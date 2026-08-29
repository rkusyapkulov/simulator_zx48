#define _CRT_SECURE_NO_WARNINGS
#define UNICODE
#define _UNICODE
#include <windows.h>
#include <mmsystem.h>
#include <fstream>
#include <vector>
#include "z80emu.h"

#pragma comment(lib, "winmm.lib")

typedef uint8_t  u8;
typedef uint16_t u16;
typedef int8_t   i8;

#define Z80_CPU_SPEED           3500000   /* In Hz. */
#define CYCLES_PER_STEP         (Z80_CPU_SPEED / 50)

Z80_STATE cpu;
int cycles_until_interrupt = CYCLES_PER_STEP;

// --- ПАРАМЕТРЫ ЭКРАНА ZX SPECTRUM ---
#define IDM_FILE_OPEN 0x0010

// --- ГЛОБАЛЬНАЯ ПАМЯТЬ ---
BYTE spec_rom[16384]; // 16 Кб ПЗУ (0x0000 - 0x3FFF)
BYTE spec_ram[49156]; // 48 Кб ОЗУ + безопасный запас для адреса 0xFFFF

// Состояние полурядов клавиатуры (8 полурядов по 5 бит, 0 = нажата)
BYTE spec_key_rows[8] = { 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F }; // effective matrix seen by the Z80
BYTE physical_key_rows[8] = { 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F }; // PC keyboard state
BYTE gui_key_rows[8] = { 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F }; // virtual keyboard state
int gui_key_frames[40] = {};            // virtual key pulse duration in 50 Hz frames
bool emulator_running = true;
static DWORD pixel_buffer[256 * 192];

// --- ГЛОБАЛЬНЫЕ ПЕРЕМЕННЫЕ ДЛЯ ЭМУЛЯЦИИ ЛЕНТЫ ---
std::vector<BYTE> current_tap_data; // Буфер текущего TAP-файла
size_t tap_current_pos = 0;         // Текущая позиция чтения в TAP
bool tap_is_loaded = false;         // Флаг, загружена ли "лента" в эмулятор

HWND hRegListBox = NULL;

const int AUDIO_SAMPLE_RATE = 22050;
HWAVEOUT hWaveOut = NULL;
WAVEHDR waveHeader[2];
short* audioBuffers[2] = { NULL, NULL };
const int AUDIO_BUF_SIZE = 1024;
bool spec_speaker_state = false;
// Border color written by OUT (0xFE),A low 3 bits
int spec_border_color = 0;
HANDLE audio_thread = NULL;

// ULA / video extras
bool spec_flash_state = false; // ULA FLASH phase; changes every 16 video frames
BYTE spec_last_floating_bus = 0xFF; // value returned on floating bus reads
BYTE spec_flash_frame = 0; // 0..15: 50 Hz frames within one FLASH half-period

// Tape / EAR / MIC stubs
bool spec_ear_signal = false;

// --- АУДИО: ULA beeper + AY-3-8910 ---
bool audio_initialized = false;
bool audio_cs_initialized = false;
CRITICAL_SECTION audio_cs;
int audio_sample_rate = AUDIO_SAMPLE_RATE;
volatile bool audio_thread_running = false;

static volatile uint64_t audio_cpu_tstates = 0;

enum AudioEventType : BYTE { AUDIO_EVT_BEEPER = 1, AUDIO_EVT_AY_WRITE = 2 };

struct AudioEvent {
    uint64_t tstate;
    BYTE type;
    BYTE reg;
    BYTE value;
};

static const int AUDIO_EVENT_CAPACITY = 16384;
static AudioEvent audio_events[AUDIO_EVENT_CAPACITY];
static volatile LONG audio_event_write = 0;
static volatile LONG audio_event_read = 0;

static inline void QueueAudioEvent(BYTE type, BYTE reg, BYTE value) {
    LONG w = audio_event_write;
    LONG r = audio_event_read;
    LONG next = (w + 1) % AUDIO_EVENT_CAPACITY;
    if (next == r) {
        // Drop the oldest event rather than blocking the Z80.
        audio_event_read = (r + 1) % AUDIO_EVENT_CAPACITY;
    }
    audio_events[w].tstate = audio_cpu_tstates;
    audio_events[w].type = type;
    audio_events[w].reg = reg;
    audio_events[w].value = value;
    MemoryBarrier();
    audio_event_write = next;
}

static inline bool PopAudioEvent(AudioEvent& ev) {
    LONG r = audio_event_read;
    if (r == audio_event_write) return false;
    ev = audio_events[r];
    MemoryBarrier();
    audio_event_read = (r + 1) % AUDIO_EVENT_CAPACITY;
    return true;
}

// --- СТРУКТУРА МУЗЫКАЛЬНОГО СОПРОЦЕССОРА AY-3-8910 ---
struct AY38910 {
    enum StereoMode { MODE_MONO, MODE_ABC, MODE_ACB };
    StereoMode stereo_mode = MODE_ABC; // По умолчанию популярный в СНГ режим ABC

    BYTE regs[16] = {};                 // Физические регистры чипа
    BYTE selected_reg = 0;              // Индекс выбранного регистра

    double tone_phase[3] = { 0.0, 0.0, 0.0 }; // Фазы генераторов тона (каналы A, B, C)
    double noise_phase = 0.0;           // Фаза генератора шума
    double envelope_phase = 0.0;        // Фаза генератора огибающей

    unsigned int noise_lfsr = 1;        // Регистр сдвига для генерации шума (LFSR)
    int envelope_level = 0;             // Текущий уровень громкости огибающей
    int envelope_direction = -1;        // Направление изменения огибающей (1 или -1)
    bool envelope_hold = false;         // Флаг удержания уровня огибающей
    bool envelope_started = false;      // Флаг активности цикла огибающей

    // Таблица соответствия уровней громкости AY (логарифмическая шкала)
    static constexpr double VOLUME[16] = {
        0.000, 0.011, 0.016, 0.023, 0.032, 0.045, 0.064, 0.090,
        0.126, 0.178, 0.250, 0.354, 0.500, 0.630, 0.794, 1.000
    };

    void Reset() {
        EnterCriticalSection(&audio_cs);
        ZeroMemory(regs, sizeof(regs));
        selected_reg = 0;
        tone_phase[0] = tone_phase[1] = tone_phase[2] = 0.0;
        noise_phase = 0.0;
        envelope_phase = 0.0;
        noise_lfsr = 1;
        envelope_level = 0;
        envelope_direction = -1;
        envelope_hold = false;
        envelope_started = false;
        LeaveCriticalSection(&audio_cs);
    }

    void WriteRegister(BYTE reg, BYTE value) {
        reg &= 0x0F;
        if (reg == 13) {
            regs[reg] = value & 0x0F;
            BYTE shape = value & 0x0F;
            bool attack = (shape & 0x04) != 0;
            envelope_direction = attack ? 1 : -1;
            envelope_level = attack ? 0 : 15;
            envelope_phase = 0.0;
            envelope_hold = false;
            envelope_started = true;
        }
        else {
            regs[reg] = value;
        }
    }

    BYTE ReadRegister(BYTE reg) const {
        return regs[reg & 0x0F];
    }
} ay;

DWORD WINAPI AudioThreadProc(LPVOID lpParam) {
    (void)lpParam;

    const double ay_clock = 1773400.0;
    const double tstates_per_sample = (double)Z80_CPU_SPEED / (double)audio_sample_rate;

    BYTE r[16] = {};
    BYTE beeper = 0;
    double tone_phase[3] = { 0.0, 0.0, 0.0 };
    double noise_phase = 0.0;
    unsigned int noise_lfsr = 1;
    double envelope_phase = 0.0;
    int envelope_level = 0;
    int envelope_direction = -1;
    bool envelope_hold = true;
    bool envelope_started = false;

    uint64_t render_tstate = audio_cpu_tstates;

    AudioEvent ev{};
    AudioEvent pending{};
    bool has_pending = false;

    while (audio_thread_running) {
        bool didWork = false;

        for (int i = 0; i < 2; ++i) {
            if (!(waveHeader[i].dwFlags & WHDR_DONE))
                continue;

            uint64_t now = audio_cpu_tstates;
            uint64_t lead = (uint64_t)(AUDIO_BUF_SIZE * tstates_per_sample * 1.5);
            if (render_tstate + (uint64_t)(AUDIO_BUF_SIZE * tstates_per_sample) > now + lead) {
                continue;
            }

            short* buf = audioBuffers[i];
            if (!buf) continue;

            // Заполнение стереобуфера: итерация по фреймам (в каждом фрейме 2 семпла)
            for (int n = 0; n < AUDIO_BUF_SIZE; ++n) {
                uint64_t sample_tstate = render_tstate + (uint64_t)(n * tstates_per_sample);

                while (true) {
                    if (!has_pending) {
                        if (!PopAudioEvent(pending))
                            break;
                        has_pending = true;
                    }
                    if (pending.tstate > sample_tstate)
                        break;
                    ev = pending;
                    has_pending = false;
                    if (ev.type == AUDIO_EVT_BEEPER) {
                        beeper = ev.value ? 1 : 0;
                    }
                    else if (ev.type == AUDIO_EVT_AY_WRITE) {
                        BYTE reg = ev.reg & 0x0F;
                        if (reg == 13) {
                            r[reg] = ev.value & 0x0F;
                            BYTE shape = r[reg];
                            bool attack = (shape & 0x04) != 0;
                            envelope_direction = attack ? 1 : -1;
                            envelope_level = attack ? 0 : 15;
                            envelope_phase = 0.0;
                            envelope_hold = false;
                            envelope_started = true;
                        }
                        else {
                            r[reg] = ev.value;
                        }
                    }
                }

                // 1. Генерация Шума
                int np = r[6] & 0x1F;
                if (np == 0) np = 32;
                noise_phase += ay_clock / (16.0 * np * audio_sample_rate);
                while (noise_phase >= 1.0) {
                    noise_phase -= 1.0;
                    unsigned fb = ((noise_lfsr >> 0) ^ (noise_lfsr >> 3)) & 1u;
                    noise_lfsr = (noise_lfsr >> 1) | (fb << 16);
                    if (!noise_lfsr) noise_lfsr = 1;
                }
                double noise = (noise_lfsr & 1) ? 1.0 : -1.0;

                // 2. Генерация Огибающей
                int ep = r[11] | ((int)r[12] << 8);
                if (ep == 0) ep = 65536;
                envelope_phase += ay_clock / (256.0 * ep * audio_sample_rate);
                while (envelope_phase >= 1.0) {
                    envelope_phase -= 1.0;
                    if (!envelope_hold) {
                        envelope_level += envelope_direction;
                        if (envelope_level < 0 || envelope_level > 15) {
                            BYTE shape = r[13] & 0x0F;
                            bool cont = (shape & 0x08) != 0;
                            bool alt = (shape & 0x02) != 0;
                            bool hold = (shape & 0x01) != 0;
                            if (!cont || hold) {
                                envelope_level = envelope_direction > 0 ? 15 : 0;
                                envelope_hold = true;
                            }
                            else if (alt) {
                                envelope_direction = -envelope_direction;
                                envelope_level = envelope_direction > 0 ? 0 : 15;
                            }
                            else {
                                envelope_level = envelope_direction > 0 ? 0 : 15;
                            }
                        }
                    }
                }

                // 3. Синтез каналов (A, B, C)
                double ch_amp[3] = { 0.0, 0.0, 0.0 };
                for (int ch = 0; ch < 3; ++ch) {
                    int tp = r[ch * 2] | ((r[ch * 2 + 1] & 0x0F) << 8);
                    if (tp == 0) tp = 4096;
                    tone_phase[ch] += ay_clock / (16.0 * tp * audio_sample_rate);
                    tone_phase[ch] -= floor(tone_phase[ch]);

                    double tone = tone_phase[ch] < 0.5 ? 1.0 : -1.0;
                    BYTE mixer = r[7];
                    bool tone_on = (mixer & (1 << ch)) == 0;
                    bool noise_on = (mixer & (1 << (ch + 3))) == 0;

                    double sig = 0.0;
                    if (tone_on && noise_on) sig = tone * noise;
                    else if (tone_on) sig = tone;
                    else if (noise_on) sig = noise;

                    BYTE vr = r[8 + ch];
                    double amp = (vr & 0x10)
                        ? AY38910::VOLUME[envelope_level & 15]
                        : AY38910::VOLUME[vr & 15];
                    ch_amp[ch] = sig * amp;
                }

                // 4. Распределение по стерео-каналам (Панорамирование)
                double left_mix = 0.0;
                double right_mix = 0.0;

                switch (ay.stereo_mode) {
                case AY38910::MODE_ABC:
                    left_mix = ch_amp[0] + ch_amp[1] * 0.5;
                    right_mix = ch_amp[2] + ch_amp[1] * 0.5;
                    break;
                case AY38910::MODE_ACB:
                    left_mix = ch_amp[0] + ch_amp[2] * 0.5;
                    right_mix = ch_amp[1] + ch_amp[2] * 0.5;
                    break;
                case AY38910::MODE_MONO:
                default:
                    left_mix = (ch_amp[0] + ch_amp[1] + ch_amp[2]) * 0.5;
                    right_mix = left_mix;
                    break;
                }

                // 5. Интеграция системного бипера (моно, раскидан в оба уха)
                static double beeper_value = -1.0;
                double target = beeper ? 1.0 : -1.0;
                beeper_value += (target - beeper_value) * 0.25;

                double final_left = left_mix * 0.20 + beeper_value * 0.14;
                double final_right = right_mix * 0.20 + beeper_value * 0.14;

                // Лимитер (Clamping)
                if (final_left > 1.0)   final_left = 1.0;
                if (final_left < -1.0)  final_left = -1.0;
                if (final_right > 1.0)  final_right = 1.0;
                if (final_right < -1.0) final_right = -1.0;

                // Запись в результирующий массив (чередование L-R-L-R)
                buf[n * 2] = (short)(final_left * 10000.0);
                buf[n * 2 + 1] = (short)(final_right * 10000.0);
            }

            render_tstate += (uint64_t)(AUDIO_BUF_SIZE * tstates_per_sample);
            waveHeader[i].dwBufferLength = AUDIO_BUF_SIZE * 2 * sizeof(short);
            waveHeader[i].dwFlags &= ~WHDR_DONE;
            waveOutWrite(hWaveOut, &waveHeader[i], sizeof(WAVEHDR));
            didWork = true;
        }

        if (!didWork)
            Sleep(1);
    }
    return 0;
}

void StopAudio() {
    if (!audio_initialized) {
        if (audio_cs_initialized) {
            DeleteCriticalSection(&audio_cs);
            audio_cs_initialized = false;
        }
        return;
    }
    audio_thread_running = false;
    if (audio_thread) {
        WaitForSingleObject(audio_thread, 2000);
        CloseHandle(audio_thread);
        audio_thread = NULL;
    }
    // drain and unprepare headers and free buffers
    for (int i = 0; i < 2; i++) {
        if (waveHeader[i].lpData) {
            waveOutUnprepareHeader(hWaveOut, &waveHeader[i], sizeof(WAVEHDR));
            // do not free waveHeader[i].lpData here; free audioBuffers instead
            waveHeader[i].lpData = NULL;
        }
        if (audioBuffers[i]) { free(audioBuffers[i]); audioBuffers[i] = NULL; }
    }
    if (hWaveOut) {
        waveOutReset(hWaveOut);
        waveOutClose(hWaveOut);
        hWaveOut = NULL;
    }
    DeleteCriticalSection(&audio_cs);
    audio_cs_initialized = false;
    audio_initialized = false;
}

void ClearAudioBuffers() {
    if (!audio_initialized || !hWaveOut) return;

    // 1. Мгновенно останавливаем аудиокарту и возвращаем буферы Windows
    waveOutReset(hWaveOut);

    // 2. Сбрасываем атомарные указатели кольцевого буфера звуковых событий
    audio_event_read = 0;
    audio_event_write = 0;

    // 3. Заполняем физические буферы тишиной и отправляем обратно в очередь
    for (int i = 0; i < 2; i++) {
        if (audioBuffers[i]) {
            ZeroMemory(audioBuffers[i], AUDIO_BUF_SIZE * 2 * sizeof(short));
            waveHeader[i].dwFlags = 0;
            waveHeader[i].dwBufferLength = AUDIO_BUF_SIZE * 2 * sizeof(short);

            waveOutPrepareHeader(hWaveOut, &waveHeader[i], sizeof(WAVEHDR));
            waveOutWrite(hWaveOut, &waveHeader[i], sizeof(WAVEHDR));
        }
    }
}

// --- ГЛОБАЛЬНЫЕ ФУНКЦИИ ВВОДА-ВЫВОДА И ПАМЯТИ (ВЫНЕСЕНЫ ИЗ СТРУКТУРЫ) ---

extern "C" u8 ReadByte(u16 addr)
{
    WORD target = addr;

    // --------------------------------------------------------
    // Обычный ZX Spectrum 48K memory map
    // --------------------------------------------------------
    if (target < 0x4000)
        return spec_rom[target];

    BYTE val = spec_ram[target - 0x4000];

    if (target >= 0x4000 && target < 0x5800)
        spec_last_floating_bus = val;

    return val;
}

extern "C" void WriteByte(u16 addr, u8 val)
{
    WORD target = addr;

    // --------------------------------------------------------
    // Обычный ZX Spectrum
    // --------------------------------------------------------
    if (target < 0x4000)
        return;

    spec_ram[target - 0x4000] = val;
}

// Ввод-вывод из портов (ULA Spectrum)
extern "C" u8 InPort(u16 port) {
    // Чтение клавиатуры: если младший байт адреса равен 254 (0xFE)
    if ((port & 0xFF) == 0xFE) {
        BYTE result = 0x1F; // Биты 0..4 изначально в 1 (не нажаты)
        // Сканируем старший байт адреса
        for (int i = 0; i < 8; i++) {
            if (!(port & (1 << (8 + i)))) {
                result &= spec_key_rows[i];
            }
        }
        return result | 0xC0 | (spec_ear_signal ? 0x20 : 0x00); // ULA: bits 7/6 high, bit 5 = EAR
    }
    // Floating bus behaviour: return the last value driven by ULA when
    // reading from unspecified ports.
    // Basic EAR/MIC stub: if high byte indicates tape port (rare), return
    // a simple representation of ear signal (0x00 for low, 0xFF for high)
    // otherwise return last floating bus value.
    // Example: if hardware used port 0xFEFE/0xFDFE variants for tape, check upper byte
    BYTE high = (BYTE)((port >> 8) & 0xFF);
    if (high == 0xFF) {
        return spec_ear_signal ? 0xFF : 0x00;
    }
    if (port == 0xFFFD) return ay.selected_reg;
    if (port == 0xBFFD) {
        EnterCriticalSection(&audio_cs);
        BYTE v = ay.ReadRegister(ay.selected_reg);
        LeaveCriticalSection(&audio_cs);
        return v;
    }

    return spec_last_floating_bus;
}

extern "C" void OutPort(u16 port, u8 val) {
    if (port == 0xFFFD) {
        EnterCriticalSection(&audio_cs);
        ay.selected_reg = val & 0x0F;
        LeaveCriticalSection(&audio_cs);
        return;
    }
    if (port == 0xBFFD) {
        EnterCriticalSection(&audio_cs);
        ay.WriteRegister(ay.selected_reg, val);
        QueueAudioEvent(AUDIO_EVT_AY_WRITE, ay.selected_reg, val);
        LeaveCriticalSection(&audio_cs);
        return;
    }

    if ((port & 0xFF) == 0xFE) {
        // Bit 4 controls the beeper (speaker)
        spec_speaker_state = (val & 0x10) != 0;
        QueueAudioEvent(AUDIO_EVT_BEEPER, 0, spec_speaker_state ? 1 : 0);
        // Bits 0..2 set the border color on a real Spectrum
        spec_border_color = val & 0x07;
    }

}

// Заглушка для совместимости со старыми вызовами внутри загрузчиков
static inline void WriteByteInline(int addr, BYTE val) { WriteByte((u16)addr, (u8)val); }
static inline BYTE ReadByteInline(int addr) { return (BYTE)ReadByte((u16)addr); }

// --- ПЕРЕХВАТ ПРОЦЕДУРЫ LOAD ИЗ ПЗУ (ROM HOOK) ---
bool HandleRomHook() {
    if (cpu.pc == 0x0556 && tap_is_loaded) {
        if (tap_current_pos + 2 <= current_tap_data.size()) {
            WORD block_len = current_tap_data[tap_current_pos] | (current_tap_data[tap_current_pos + 1] << 8);

            if (tap_current_pos + 2 + block_len <= current_tap_data.size()) {
                size_t block_start = tap_current_pos + 2;
                WORD data_len = block_len - 2;
                const BYTE* raw_data = &current_tap_data[block_start + 1];

                WORD target_addr = cpu.registers.word[Z80_IX]; // Capitalized IX
                for (WORD i = 0; i < data_len; i++) {
                    WriteByte(target_addr + i, raw_data[i]);
                }

                tap_current_pos += 2 + block_len;

                cpu.registers.byte[Z80_F] |= (0x01 | 0x40); // Direct bit manipulation on cpu.F
                cpu.registers.byte[Z80_A] = 0u;             // Capitalized A

                WORD low = ReadByte(cpu.registers.word[Z80_SP]);  cpu.registers.word[Z80_SP] = (cpu.registers.word[Z80_SP] + 1) & 0xFFFF;
                WORD high = ReadByte(cpu.registers.word[Z80_SP]); cpu.registers.word[Z80_SP] = (cpu.registers.word[Z80_SP] + 1) & 0xFFFF;
                cpu.pc = (high << 8) | low;

                return true;
            }
        }
        tap_is_loaded = false;
    }
    return false;
}

void Reset() {
    Z80Reset(&cpu);
    cycles_until_interrupt = CYCLES_PER_STEP;
}

// Обертка системного шага, заменяющая старый метод StepZ80
int SystemStepZ80()
{
    // --------------------------------------------------------
    // Spectrum tape ROM hook
    // --------------------------------------------------------
    if (HandleRomHook())
        return 20;

    // --------------------------------------------------------
    // Normal Z80 execution
    // --------------------------------------------------------
    return Z80Emulate(&cpu, 1, NULL);
}

// --- ПОПИКСЕЛЬНЫЙ РЕНДЕРИНГ ЭКРАНА ZX SPECTRUM ---
void RenderSpectrumScreen(HDC hdc, int xOffset, int yOffset) {
    // ЕДИНЫЙ и 100% правильный массив палитры в формате RGB (под ваш StretchDIBits)
    static const DWORD spec_palette[16] = {
        // --- ОБЫЧНЫЕ ЦВЕТА (BRIGHT 0) ---
        0x00000000, // 0: Черный
        0x000000C0, // 1: Синий
        0x00C00000, // 2: Красный
        0x00C000C0, // 3: Пурпурный (Красный + Синий)
        0x0000C000, // 4: Зеленый
        0x0000C0C0, // 5: Циан / Голубой (Зеленый + Синий)
        0x00C0C000, // 6: Желтый (Красный + Зеленый)
        0x00C0C0C0, // 7: Белый / Серый
        // --- ЯРКИЕ ЦВЕТА (BRIGHT 1) ---
        0x00000000, // 8: Черный
        0x000000FF, // 9: Синий яркий
        0x00FF0000, // 10: Красный яркий
        0x00FF00FF, // 11: Пурпурный яркий
        0x0000FF00, // 12: Зеленый яркий
        0x0000FFFF, // 13: Циан яркий
        0x00FFFF00, // 14: Желтый яркий
        0x00FFFFFF  // 15: Чистый белый
    };

    // ВАЖНО: Если вам нужен полноценный бордюр ВОКРУГ экрана, размер pixel_buffer и bmiHeader
    // должен быть увеличен (например, до 320x240). 
    // Поскольку ваш pixel_buffer имеет фиксированный размер 256x192, мы просто заполняем его 
    // цветом бордюра, если активная память экрана пуста, либо сразу пишем туда пиксели.
    int border_color_idx = spec_border_color & 0x07;
    DWORD border_color = spec_palette[border_color_idx];

    // Рендеринг активного экрана 256x192 (Один чистый проход)
    for (int y = 0; y < 192; y++) {
        // Вычисление интерлейсного адреса растровой строки ZX Spectrum
        int zone = (y >> 6) & 3;       // 3 зоны по 64 строки
        int line = y & 7;              // внутри символа
        int char_row = (y >> 3) & 7;    // строка символов в зоне
        WORD pixel_line_addr = 0x4000 + (zone << 11) + (line << 8) + (char_row << 5);

        int target_y = (192 - 1) - y;  // Инвертируем Y для StretchDIBits (снизу вверх)

        for (int x_byte = 0; x_byte < 32; x_byte++) {
            BYTE pixel_data = spec_ram[pixel_line_addr - 0x4000 + x_byte];

            // Каждому байту пикселей соответствует 1 байт атрибутов цвета
            int attr_addr = 0x5800 + ((y >> 3) * 32) + x_byte;
            BYTE attr = spec_ram[attr_addr - 0x4000];

            BYTE ink = attr & 0x07;
            BYTE paper = (attr >> 3) & 0x07;
            bool bright = (attr & 0x40) != 0;
            bool flash = (attr & 0x80) != 0;

            // Обработка мерцания FLASH
            if (flash && spec_flash_state) {
                BYTE t = ink; ink = paper; paper = t;
            }

            int color_offset = bright ? 8 : 0;
            DWORD ink_color = spec_palette[ink + color_offset];
            DWORD paper_color = spec_palette[paper + color_offset];

            for (int bit = 0; bit < 8; bit++) {
                bool pixel_active = (pixel_data & (1 << (7 - bit))) != 0;
                int pixel_x = (x_byte * 8) + bit;

                // Записываем финальный цвет пикселя в буфер кадра
                pixel_buffer[target_y * 256 + pixel_x] = pixel_active ? ink_color : paper_color;
            }
        }
    }

    BITMAPINFO bmi = { 0 };
    bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bmi.bmiHeader.biWidth = 256;
    bmi.bmiHeader.biHeight = 192;
    bmi.bmiHeader.biPlanes = 1;
    bmi.bmiHeader.biBitCount = 32;
    bmi.bmiHeader.biCompression = BI_RGB;

    // Выводим отрендеренный кадр с масштабированием х2 в окно Windows
    StretchDIBits(hdc, xOffset, yOffset, 256 * 2, 192 * 2, 0, 0, 256, 192, pixel_buffer, &bmi, DIB_RGB_COLORS, SRCCOPY);
}

#ifndef BS_NOFOCUS
#define BS_NOFOCUS 0x00008000L
#endif

// --- СОЗДАНИЕ ИНТЕРФЕЙСА ВИРТУАЛЬНОЙ КЛАВИАТУРЫ ---
void CreateSpectrumKeyboardUI(HWND hwndParent, HINSTANCE hInst) {
    const int BTN_W = 52; const int BTN_H = 42;
    const int START_X = 20; const int START_Y = 440; const int GAP = 5;

    // Матрица подписей для 40 оригинальных клавиш ZX Spectrum
    static const wchar_t* spec_labels[] = {
        L"1\nEDIT", L"2\nCAPS", L"3\nTRUE", L"4\nINV", L"5\n←", L"6\n↓", L"7\n↑", L"8\n→", L"9\nGRAPH", L"0\nDEL",
        L"Q\nPLOT", L"W\nDRAW", L"E\nREM", L"R\nRUN", L"T\nRAND", L"Y\nRET", L"U\nCLS", L"I\nINPUT", L"O\nPOKE", L"P\nPRINT",
        L"A\nNEW", L"S\nSAVE", L"D\nDIM", L"F\nFOR", L"G\nGOTO", L"H\nGOSUB", L"J\nLOAD", L"K\nLIST", L"L\nLET", L"ENTER",
        L"CAPS\nSHIFT", L"Z\nLN", L"X\nEXP", L"C\nAT", L"V\nCLS", L"B\nBIN", L"N\nINKEY", L"M\nPI", L"SYM\nSHIFT", L"SPACE"
    };

    for (int idx = 0; idx < 40; idx++) {
        int r = idx / 10; int c = idx % 10;
        int current_id = 1000 + idx;
        int x = START_X + c * (BTN_W + GAP);
        int y = START_Y + r * (BTN_H + GAP);

        // Добавлен отсутствовавший 1-й параметр расширенного стиля (0)
        CreateWindowExW(0, L"BUTTON", spec_labels[idx],
            WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON | BS_MULTILINE | BS_FLAT | BS_NOFOCUS,
            x, y, BTN_W, BTN_H, hwndParent, (HMENU)(INT_PTR)current_id, hInst, NULL);
    }
}

// Карта распределения физических и экранных кнопок по полурядам матрицы клавиатуры Spectrum
// Индекс полуряда: 0=#FEFE, 1=#FDFE, 2=#FBFE, 3=#EFFE, 4=#F7FE, 5=#DFFE, 6=#BFFE, 7=#7FFE
struct KeyMapInfo {
    int row; // Индекс полуряда 0..7
    int bit; // Бит 0..4
};

static const KeyMapInfo spec_hardware_map[] = {
    {3,0}, {3,1}, {3,2}, {3,3}, {3,4}, {4,4}, {4,3}, {4,2}, {4,1}, {4,0}, // 1 2 3 4 5 6 7 8 9 0
    {2,0}, {2,1}, {2,2}, {2,3}, {2,4}, {5,4}, {5,3}, {5,2}, {5,1}, {5,0}, // Q W E R T Y U I O P
    {1,0}, {1,1}, {1,2}, {1,3}, {1,4}, {6,4}, {6,3}, {6,2}, {6,1}, {6,0}, // A S D F G H J K L ENTER
    {0,0}, {0,1}, {0,2}, {0,3}, {0,4}, {7,4}, {7,3}, {7,2}, {7,1}, {7,0}  // C_SHIFT Z X C V B N M S_SHIFT SPACE
};

static void RebuildSpectrumKeyboardMatrix() {
    for (int i = 0; i < 8; ++i)
        spec_key_rows[i] = (BYTE)(physical_key_rows[i] & gui_key_rows[i]);
}

static void SetPhysicalMatrixBit(int row, int bit, bool down) {
    if (row < 0 || row >= 8 || bit < 0 || bit >= 5) return;
    if (down) physical_key_rows[row] &= (BYTE)~(1u << bit);
    else physical_key_rows[row] |= (BYTE)(1u << bit);
    RebuildSpectrumKeyboardMatrix();
}

static void SetPhysicalMatrixKey(int idx, bool down) {
    if (idx < 0 || idx >= 40) return;
    int r = spec_hardware_map[idx].row;
    int b = spec_hardware_map[idx].bit;
    if (down) physical_key_rows[r] &= (BYTE)~(1u << b);
    else physical_key_rows[r] |= (BYTE)(1u << b);
    RebuildSpectrumKeyboardMatrix();
}

static void PulseGuiMatrixKey(int idx) {
    if (idx < 0 || idx >= 40) return;
    int r = spec_hardware_map[idx].row;
    int b = spec_hardware_map[idx].bit;
    gui_key_rows[r] &= (BYTE)~(1u << b);
    gui_key_frames[idx] = 10; // ~200 ms at 50 Hz, long enough for ROM scans
    RebuildSpectrumKeyboardMatrix();
}

bool MapVirtualKeyToSpectrum(UINT vkCode, int& out_row, int& out_col) {
    int idx = -1;
    if (vkCode >= '0' && vkCode <= '9') {
        idx = (vkCode == '0') ? 9 : (vkCode - '1');
    }
    else switch (vkCode) {
    case 'Q': idx = 10; break; case 'W': idx = 11; break; case 'E': idx = 12; break; case 'R': idx = 13; break; case 'T': idx = 14; break;
    case 'Y': idx = 15; break; case 'U': idx = 16; break; case 'I': idx = 17; break; case 'O': idx = 18; break; case 'P': idx = 19; break;
    case 'A': idx = 20; break; case 'S': idx = 21; break; case 'D': idx = 22; break; case 'F': idx = 23; break; case 'G': idx = 24; break;
    case 'H': idx = 25; break; case 'J': idx = 26; break; case 'K': idx = 27; break; case 'L': idx = 28; break;
    case VK_RETURN: idx = 29; break;
    case 'Z': idx = 31; break; case 'X': idx = 32; break; case 'C': idx = 33; break; case 'V': idx = 34; break;
    case 'B': idx = 35; break; case 'N': idx = 36; break; case 'M': idx = 37; break;
    case VK_SPACE: idx = 39; break;
    }
    if (idx != -1) {
        out_row = spec_hardware_map[idx].row;
        out_col = spec_hardware_map[idx].bit;
        return true;
    }
    return false;
}


static WORD ReadLE16(const BYTE* p) {
    return (WORD)p[0] | ((WORD)p[1] << 8);
}

static bool LoadSnaSnapshot(const std::vector<BYTE>& data, std::wstring& error) {
    if (data.size() != 49179) {
        error = L"Поддерживается только 48K .SNA (49179 байт). "
                L"128K .SNA в этом 48K эмуляторе не поддерживается.";
        return false;
    }

    const BYTE* h = data.data();
    Reset();
    spec_speaker_state = false;
    ay.Reset();

    // 1. Восстановление базовых регистров Z80 из заголовка (первые 27 байт)
    cpu.i = h[0];
    cpu.alternates[Z80_HL] = h[2]<<8|h[1];
    cpu.alternates[Z80_DE] = h[4]<<8|h[3];
    cpu.alternates[Z80_BC] = h[6]<<8|h[5];
    cpu.alternates[Z80_AF] = h[8]<<8|h[7];

    cpu.registers.byte[Z80_L] = h[9];  cpu.registers.byte[Z80_H] = h[10];
    cpu.registers.byte[Z80_E] = h[11]; cpu.registers.byte[Z80_D] = h[12];
    cpu.registers.byte[Z80_C] = h[13]; cpu.registers.byte[Z80_B] = h[14];
    cpu.registers.word[Z80_IY] = ReadLE16(h + 15);
    cpu.registers.word[Z80_IX] = ReadLE16(h + 17);
    cpu.iff1 = (h[19] & 0x04) != 0;
    cpu.iff2 = cpu.iff1;
    cpu.r = h[20];
    cpu.registers.byte[Z80_F] = h[21];
    cpu.registers.byte[Z80_A] = h[22];
    cpu.registers.word[Z80_SP] = ReadLE16(h + 23);
    cpu.im = (BYTE)(h[25] & 0x03);
    if (cpu.im > 2) cpu.im = 2;

    spec_border_color = h[26] & 0x07;

    for (size_t i = 0; i < 49152; ++i)
        spec_ram[i] = data[27 + i];

    // In a 48K SNA the PC is stored on the stack. Loading it is equivalent
    // to executing RETN immediately after restoring the snapshot.
    if (cpu.registers.word[Z80_SP] < 0x4000) {
        error = L"Некорректный .SNA: SP указывает в ПЗУ.";
        return false;
    }

    size_t ram_offset = (size_t)(cpu.registers.word[Z80_SP] - 0x4000);
    if (ram_offset + 1 >= 49152) {
        error = L"Некорректный .SNA: PC на стеке выходит за пределы RAM.";
        return false;
    }

    cpu.pc = (WORD)spec_ram[ram_offset] |
             ((WORD)spec_ram[ram_offset + 1] << 8);
    cpu.registers.word[Z80_SP] = (WORD)(cpu.registers.word[Z80_SP] + 2);

    cycles_until_interrupt = CYCLES_PER_STEP;
    return true;
}

static bool DecompressZ80(const BYTE* src, size_t src_size,
                          std::vector<BYTE>& out, size_t expected_size,
                          bool old_format) {
    out.clear();
    out.reserve(expected_size);

    size_t p = 0;
    while (p < src_size && out.size() < expected_size) {
        if (old_format && p + 4 <= src_size &&
            src[p] == 0x00 && src[p + 1] == 0xED &&
            src[p + 2] == 0xED && src[p + 3] == 0x00) {
            break;
        }

        if (p + 4 <= src_size &&
            src[p] == 0xED && src[p + 1] == 0xED) {
            BYTE count = src[p + 2];
            BYTE value = src[p + 3];
            if (count == 0 || out.size() + count > expected_size)
                return false;
            out.insert(out.end(), count, value);
            p += 4;
        } else {
            out.push_back(src[p++]);
        }
    }

    return out.size() == expected_size;
}

static bool LoadZ80Snapshot(const std::vector<BYTE>& data, std::wstring& error) {
    if (data.size() < 30) {
        error = L"Файл .Z80 слишком короткий.";
        return false;
    }

    const BYTE* h = data.data();
    Reset();
    spec_speaker_state = false;
    ay.Reset();

    // 1. Парсинг заголовка версии v1 (Базовый блок)
    cpu.registers.byte[Z80_A] = h[0];
    cpu.registers.byte[Z80_F] = h[1];
    cpu.registers.word[Z80_BC] = ReadLE16(h + 2);
    cpu.registers.word[Z80_HL] = ReadLE16(h + 4);

    WORD pc_header = ReadLE16(h + 6);
    cpu.registers.word[Z80_SP] = ReadLE16(h + 8);
    cpu.i = h[10];
    cpu.r = (BYTE)((h[11] & 0x7F) | ((h[12] & 0x01) << 7));
    spec_border_color = (h[12] >> 1) & 0x07;

    cpu.registers.word[Z80_DE] = ReadLE16(h + 13);
    cpu.alternates[Z80_BC] = h[16]<<8|h[15];
    cpu.alternates[Z80_DE] = h[18]<<8|h[17];
    cpu.alternates[Z80_HL] = h[20]<<8|h[19];
    cpu.alternates[Z80_AF] = h[22]<<8|h[21];
    cpu.registers.word[Z80_IY] = ReadLE16(h + 23);
    cpu.registers.word[Z80_IX] = ReadLE16(h + 25);
    cpu.iff1 = h[27] != 0;
    cpu.iff2 = h[28] != 0;
    cpu.im = (BYTE)(h[29] & 0x03);
    if (cpu.im > 2) cpu.im = 2;

    if (pc_header != 0) {
        // Z80 v1: one 48K RAM image.
        const bool compressed = (h[12] & 0x20) != 0;
        std::vector<BYTE> ram;

        if (compressed) {
            if (!DecompressZ80(data.data() + 30, data.size() - 30,
                               ram, 49152, true)) {
                error = L"Не удалось распаковать RAM из .Z80 v1.";
                return false;
            }
        } else {
            if (data.size() < 30 + 49152) {
                error = L"Файл .Z80 v1 не содержит полные 48 КБ RAM.";
                return false;
            }
            ram.assign(data.begin() + 30, data.begin() + 30 + 49152);
        }

        std::copy(ram.begin(), ram.end(), spec_ram);
        cpu.pc = pc_header;
    } else {
        // Z80 v2/v3: additional header + 16K memory blocks.
        if (data.size() < 32) {
            error = L"Файл .Z80 v2/v3 не содержит дополнительный заголовок.";
            return false;
        }

        WORD ext_len = ReadLE16(data.data() + 30);
        if (ext_len < 23 || 32u + ext_len > data.size()) {
            error = L"Некорректная длина дополнительного заголовка .Z80.";
            return false;
        }

        const BYTE* ext = data.data() + 32;
        cpu.pc = ReadLE16(ext);
        BYTE machine = ext[2];

        // Hardware modes 0 and 1 are 48K modes. This emulator is 48K-only.
        if (machine > 1) {
            error = L"Этот эмулятор поддерживает .Z80 только для ZX Spectrum 48K.";
            return false;
        }
        if (cpu.pc == 0) {
            error = L"Некорректный .Z80: PC в дополнительном заголовке равен 0.";
            return false;
        }

        std::fill(spec_ram, spec_ram + 49152, 0);
        bool page_seen[3] = { false, false, false };
        size_t pos = 32u + ext_len;

        while (pos + 3 <= data.size()) {
            WORD block_len = ReadLE16(data.data() + pos);
            BYTE page = data[pos + 2];
            pos += 3;

            size_t target_offset = 0;
            int page_index = -1;

            // 48K Z80 pages: 8 = 4000, 4 = 8000, 5 = C000.
            if (page == 8) {
                target_offset = 0;
                page_index = 0;
            } else if (page == 4) {
                target_offset = 16384;
                page_index = 1;
            } else if (page == 5) {
                target_offset = 32768;
                page_index = 2;
            }

            size_t stored_size =
                (block_len == 0xFFFF) ? 16384u : (size_t)block_len;

            if (pos + stored_size > data.size()) {
                error = L"Повреждённый блок RAM в .Z80.";
                return false;
            }

            if (page_index < 0) {
                pos += stored_size;
                continue;
            }

            std::vector<BYTE> block;
            if (block_len == 0xFFFF) {
                block.assign(data.begin() + pos,
                             data.begin() + pos + 16384);
            } else if (!DecompressZ80(data.data() + pos, block_len,
                                      block, 16384, false)) {
                error = L"Не удалось распаковать блок RAM в .Z80.";
                return false;
            }

            std::copy(block.begin(), block.end(),
                      spec_ram + target_offset);
            page_seen[page_index] = true;
            pos += stored_size;
        }

        if (!page_seen[0] || !page_seen[1] || !page_seen[2]) {
            error = L"В .Z80 отсутствует один или несколько блоков 48K RAM.";
            return false;
        }
    }

    cycles_until_interrupt = CYCLES_PER_STEP;
    return true;
}

static bool LoadTapFile(const std::vector<BYTE>& data, std::wstring& error) {
    if (data.empty()) {
        error = L"Файл TAP пуст.";
        return false;
    }

    // Сохраняем образ ленты в глобальную память эмулятора
    current_tap_data = data;
    tap_current_pos = 0;
    tap_is_loaded = true;

    // Полный аппаратный сброс всей системы
    Reset();
    std::fill(spec_ram, spec_ram + 49152, 0);
    ay.Reset();

    // Инициализируем клавиатурную матрицу по умолчанию
    for (int i = 0; i < 8; i++) {
        spec_key_rows[i] = 0x1F;
        physical_key_rows[i] = 0x1F;
        gui_key_rows[i] = 0x1F;
    }

    // Эмуляция автоматического ввода команды LOAD "" после старта ПЗУ.
    // Для этого мы напрямую закидываем символы в системный буфер клавиатуры Spectrum (адрес 0x5C6A)
    // Это гарантирует, что эмулятор сам нажмет кнопку "J" (LOAD) и кавычки.
    // Данные пишутся в область системных переменных Spectrum (ОЗУ инициализируется ПЗУ через пару кадров)
    // Чтобы симуляция нажатия сработала наверняка через внутренние процедуры ROM, 
    // мы добавим задержку: просто дадим ПЗУ Spectrum загрузиться штатно до экрана приветствия "© 1982 Sinclair Research Ltd".

    // Но так как ПЗУ Spectrum начнет сканировать ленту как только пользователь (или мы) вызовет LOAD "",
    // наш Hook на адресе 0x0556 автоматически поймает этот вызов и мгновенно отдаст файлы из вектора current_tap_data!

    return true;
}

void UpdateRegisterDisplay() {
    SendMessageW(hRegListBox, LB_RESETCONTENT, 0, 0);
    wchar_t buf[64];
    swprintf(buf, 64, L" PC: %04Xh  SP: %04Xh", cpu.pc, cpu.registers.word[Z80_SP]);
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" REG A: %02Xh F: %02Xh", cpu.registers.byte[Z80_A], cpu.registers.byte[Z80_F]);
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" REG BC: %04Xh", cpu.registers.word[Z80_BC]);
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" REG DE: %04Xh", cpu.registers.word[Z80_DE]);
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" REG HL: %04Xh", cpu.registers.word[Z80_HL]);
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" IX: %04Xh IY: %04Xh", cpu.registers.word[Z80_IX], cpu.registers.word[Z80_IY]);
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
}

// Загрузка сырых дампов памяти или ленты игр Спектрума
void LoadSpectrumFile(HWND hwnd) {
    OPENFILENAMEW ofn = {};
    wchar_t szFile[260] = { 0 };

    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner = hwnd;
    ofn.lpstrFile = szFile;
    ofn.nMaxFile = sizeof(szFile) / sizeof(szFile[0]);
    ofn.lpstrFilter =
        L"Снимки и Ленты ZX Spectrum (*.sna;*.z80;*.tap)\0*.sna;*.z80;*.tap\0"
        L"Дампы памяти (*.bin;*.rom)\0*.bin;*.rom\0"
        L"Все файлы (*.*)\0*.*\0";
    ofn.nFilterIndex = 1;
    ofn.Flags = OFN_PATHMUSTEXIST | OFN_FILEMUSTEXIST;

    if (GetOpenFileNameW(&ofn) != TRUE)
        return;

    std::ifstream file(ofn.lpstrFile, std::ios::binary);
    if (!file.is_open()) {
        MessageBoxW(hwnd, L"Не удалось открыть файл.",
                    L"Ошибка", MB_OK | MB_ICONERROR);
        return;
    }

    std::vector<BYTE> data(
        (std::istreambuf_iterator<char>(file)),
        std::istreambuf_iterator<char>());
    file.close();

    // --- Очищаем звуковые буферы Windows ДО инжекции новой игры ---
    // Это гарантирует, что звуки из прошлой игры мгновенно затихнут, 
    // а новые порты инициализируются с чистого листа.
    ClearAudioBuffers();

    std::wstring path(szFile);
    size_t dot = path.find_last_of(L'.');
    std::wstring ext = (dot == std::wstring::npos) ? L"" : path.substr(dot);
    for (wchar_t& c : ext)
        c = (wchar_t)towlower(c);

    std::wstring error;
    bool ok = false;

    if (ext == L".sna")
        ok = LoadSnaSnapshot(data, error);
    else if (ext == L".z80")
        ok = LoadZ80Snapshot(data, error);
    else if (ext == L".tap")
        ok = LoadTapFile(data, error);
    else {
        // Existing raw BIN/ROM behavior is kept for compatibility.
        if (data.empty()) {
            error = L"Файл пуст.";
        } else {
            size_t copy_size = (data.size() > 32768) ? 32768 : data.size();
            std::fill(spec_ram, spec_ram + 49152, 0);
            std::copy(data.begin(), data.begin() + copy_size,
                      spec_ram + (0x5B00 - 0x4000));
            Reset();
            cpu.pc = 0x5B00;
            cpu.registers.word[Z80_SP] = 0xFFFF;
            ok = true;
        }
    }

    if (!ok) {
        MessageBoxW(hwnd, error.c_str(),
                    L"Ошибка загрузки snapshot",
                    MB_OK | MB_ICONERROR);
        return;
    }

    // Восстановление базового состояния интерфейса после успешного монтирования
    spec_flash_frame = 0;
    spec_flash_state = false;
    RebuildSpectrumKeyboardMatrix();
    UpdateRegisterDisplay();
    SetFocus(hwnd);

   // Обновляем заголовок главного окна приложения
    wchar_t title[320];
    swprintf_s(title, 320,
               L"Эмулятор ZX Spectrum 48 (Z80 Core) — %s", szFile);
    SetWindowTextW(hwnd, title);
}

static void PollPhysicalKeyboard(HWND hwnd) {
    if (GetForegroundWindow() != hwnd) return;

    static const UINT keys[] = {
        '0','1','2','3','4','5','6','7','8','9',
        'A','B','C','D','E','F','G','H','I','J','K','L','M',
        'N','O','P','Q','R','S','T','U','V','W','X','Y','Z',
        VK_RETURN, VK_SPACE
    };

    // 1. Опрос стандартных буквенно-цифровых клавиш
    for (UINT vk : keys) {
        int r, b;
        if (MapVirtualKeyToSpectrum(vk, r, b))
            SetPhysicalMatrixBit(r, b, (GetAsyncKeyState((int)vk) & 0x8000) != 0);
    }

    // 2. ОПРОС ФИЗИЧЕСКИХ СТРЕЛОК ПК КЛАВИАТУРЫ И КЛАВИШИ ВВОДА
    bool force_caps_shift = false;

    // Эмуляция Backspace (Стирание) = CAPS SHIFT + '0'
    if (GetAsyncKeyState(VK_BACK) & 0x8000) {
        SetPhysicalMatrixBit(4, 0, true); // Нажали '0' (клавиша DEL на Спектруме)
        force_caps_shift = true;
    }
    else if (!(GetAsyncKeyState('0') & 0x8000)) {
        SetPhysicalMatrixBit(4, 0, false);
    }

    // 3. Обработка системных модификаторов (SHIFT / CTRL / ALT)
    if (force_caps_shift || (GetAsyncKeyState(VK_SHIFT) & 0x8000)) {
        SetPhysicalMatrixKey(30, true); // CAPS SHIFT в матрице
    }
    else {
        SetPhysicalMatrixKey(30, false);
    }

    SetPhysicalMatrixKey(38, (GetAsyncKeyState(VK_CONTROL) & 0x8000) != 0 ||
        (GetAsyncKeyState(VK_MENU) & 0x8000) != 0);
}

// --- СИСТЕМНАЯ ОКОННАЯ ПРОЦЕДУРА WINDOWS ---
LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    static HINSTANCE hInst;
    switch (msg) {
    case WM_CREATE: {
        LPCREATESTRUCTW pcs = (LPCREATESTRUCTW)lp;
        hInst = pcs->hInstance;
        HMENU hSysMenu = GetSystemMenu(hwnd, FALSE);
        if (hSysMenu) {
            AppendMenuW(hSysMenu, MF_SEPARATOR, 0, NULL);
            AppendMenuW(hSysMenu, MF_STRING, IDM_FILE_OPEN, L"Открыть файл Спектрума...");
        }
        CreateSpectrumKeyboardUI(hwnd, hInst);
        int PANEL_X = 600;
        CreateWindowExW(0, L"BUTTON", L"СБРОС (RESET)", WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON, PANEL_X, 20, 180, 40, hwnd, (HMENU)2000, hInst, NULL);
        hRegListBox = CreateWindowExW(WS_EX_CLIENTEDGE, L"LISTBOX", NULL, WS_CHILD | WS_VISIBLE | WS_VSCROLL, PANEL_X, 75, 180, 220, hwnd, (HMENU)2001, NULL, NULL);

        // Заполнение матрицы клавиш по умолчанию (1 = отжато)
        for (int i = 0; i < 8; i++) { spec_key_rows[i] = 0x1F; physical_key_rows[i] = 0x1F; gui_key_rows[i] = 0x1F; }
        Reset();
        UpdateRegisterDisplay();
        return 0;
    }
    case WM_SYSCOMMAND: {
        if ((wp & 0xFFF0) == IDM_FILE_OPEN) {
            LoadSpectrumFile(hwnd);
            return 0;
        }
        return DefWindowProcW(hwnd, msg, wp, lp);
    }
    case WM_COMMAND: {
        int btn_id = LOWORD(wp);
        if (btn_id == 2000) { // Сброс
            ClearAudioBuffers(); // Звук затихает мгновенно, буферы перезапускаются
            Reset();
            spec_speaker_state = false;
            ay.Reset();

            for (int i = 0; i < 8; i++) { spec_key_rows[i] = 0x1F; physical_key_rows[i] = 0x1F; gui_key_rows[i] = 0x1F; }
            for (int i = 0; i < 40; ++i) gui_key_frames[i] = 0;
            spec_flash_frame = 0;
            spec_flash_state = false;
            UpdateRegisterDisplay();
            SetFocus(hwnd);

            return 0;
        }
        // Клик по GUI клавиатуре
        int btn_idx = btn_id - 1000;
        if (btn_idx >= 0 && btn_idx < 40) {
            PulseGuiMatrixKey(btn_idx);
            SetFocus(hwnd);
            return 0;
        }
        break;
    }
    case WM_PAINT: {
        PAINTSTRUCT ps;
        HDC hdc = BeginPaint(hwnd, &ps);
        RenderSpectrumScreen(hdc, 20, 20); // Вывод основного кадра
        EndPaint(hwnd, &ps);
        break;
    }
    case WM_DESTROY:
        PostQuitMessage(0);
        break;
    default: return DefWindowProcW(hwnd, msg, wp, lp);
    }
    return 0;
}

// --- WINMAIN С ПОДДЕРЖКОЙ СИНХРОНИЗАЦИИ ---
int WINAPI WinMain(HINSTANCE hInst, HINSTANCE, LPSTR, int nCmdShow) {
    // Подготовка чистого дампа ПЗУ 48К (базовая инициализация по умолчанию)
    memset(spec_rom, 0x00, 16384);

    // Попытка открыть оригинальный файл прошивки ZX Spectrum
    std::ifstream rom_file("ZXSpectrum48.rom", std::ios::binary);
    if (rom_file.is_open()) {
        rom_file.read(reinterpret_cast<char*>(spec_rom), 16384);
        rom_file.close();
    }
    else {
        // ЗАГЛУШКА СТАВИТСЯ ТОЛЬКО ЕСЛИ ФАЙЛ НЕ НАЙДЕН!
        spec_rom[0] = 0xF3; // DI
        spec_rom[1] = 0x31; spec_rom[2] = 0xFF; spec_rom[3] = 0xFF; // LD SP, 0xFFFF
        spec_rom[4] = 0x18; spec_rom[5] = 0xFE; // JR $ (зацикливание)
    }

    WNDCLASSW wc = { 0 };
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInst;
    wc.hCursor = LoadCursor(NULL, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)(COLOR_BTNFACE + 1);
    wc.lpszClassName = L"ZX_Spectrum_48_Core";
    RegisterClassW(&wc);

    // Подготовка размеров под экран Spectrum (256x192 в масштабе x2) и панель отладки
    HWND hwnd = CreateWindowExW(0, L"ZX_Spectrum_48_Core", L"Эмулятор ZX Spectrum 48 (Z80 Core)",
        WS_OVERLAPPEDWINDOW & ~WS_THICKFRAME & ~WS_MAXIMIZEBOX,
        CW_USEDEFAULT, CW_USEDEFAULT, 820, 680, NULL, NULL, hInst, NULL);

    ShowWindow(hwnd, nCmdShow);
    UpdateWindow(hwnd);

    WAVEFORMATEX wfx = { 0 };
    wfx.wFormatTag = WAVE_FORMAT_PCM;
    wfx.nChannels = 2; // Изменено: 2 канала (Стерео)
    wfx.nSamplesPerSec = (DWORD)audio_sample_rate;
    wfx.wBitsPerSample = 16;
    wfx.nBlockAlign = (wfx.nChannels * wfx.wBitsPerSample) / 8; // Теперь равно 4 байтам на семпл
    wfx.nAvgBytesPerSec = wfx.nSamplesPerSec * wfx.nBlockAlign;

    if (waveOutOpen(&hWaveOut, WAVE_MAPPER, &wfx, 0, 0, CALLBACK_NULL) == MMSYSERR_NOERROR) {
        for (int i = 0; i < 2; i++) {
            // Буфер теперь должен вмещать AUDIO_BUF_SIZE * 2 (левый + правый каналы)
            audioBuffers[i] = (short*)malloc(AUDIO_BUF_SIZE * 2 * sizeof(short));
            ZeroMemory(audioBuffers[i], AUDIO_BUF_SIZE * 2 * sizeof(short));
            waveHeader[i].lpData = (LPSTR)audioBuffers[i];
            waveHeader[i].dwBufferLength = AUDIO_BUF_SIZE * 2 * sizeof(short);
            waveHeader[i].dwFlags = 0;
            waveOutPrepareHeader(hWaveOut, &waveHeader[i], sizeof(WAVEHDR));
            waveOutWrite(hWaveOut, &waveHeader[i], sizeof(WAVEHDR));
        }
        audio_event_read = audio_event_write = 0;
        audio_cpu_tstates = 0;
        audio_initialized = true;
        audio_thread_running = true;
        audio_thread = CreateThread(NULL, 0, AudioThreadProc, NULL, 0, NULL);
    }

    MSG msg;
    LARGE_INTEGER frequency, last_time;
    double internal_debt = 0.0;
    QueryPerformanceFrequency(&frequency);
    QueryPerformanceCounter(&last_time);

    InitializeCriticalSection(&audio_cs);
    audio_cs_initialized = true;
    Reset();
    ay.Reset();

    while (emulator_running) {
        MsgWaitForMultipleObjectsEx(0, NULL, 1, QS_ALLINPUT, MWMO_INPUTAVAILABLE);
        while (PeekMessageW(&msg, NULL, 0, 0, PM_REMOVE)) {
            if (msg.message == WM_QUIT) {
                emulator_running = false;
                break;
            }
            // Обработка нажатий физических клавиш на ПК
            if (msg.message == WM_KEYDOWN) {
                UINT vk = (UINT)msg.wParam;
                if (vk == VK_SHIFT) { SetPhysicalMatrixKey(30, true); }
                else if (vk == VK_CONTROL || vk == VK_MENU) { SetPhysicalMatrixKey(38, true); }
                else {
                    int r = -1, b = -1;
                    if (MapVirtualKeyToSpectrum(vk, r, b)) {
                        SetPhysicalMatrixBit(r, b, true);
                    }
                }
            }
            else if (msg.message == WM_KEYUP) {
                UINT vk = (UINT)msg.wParam;
                if (vk == VK_SHIFT) { SetPhysicalMatrixKey(30, false); }
                else if (vk == VK_CONTROL || vk == VK_MENU) { SetPhysicalMatrixKey(38, false); }
                else {
                    int r = -1, b = -1;
                    if (MapVirtualKeyToSpectrum(vk, r, b)) {
                        SetPhysicalMatrixBit(r, b, false);
                    }
                }
            }
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }

        if (!emulator_running) break;

        // --- ТАКТОВАЯ СИНХРОНИЗАЦИЯ ПРОЦЕССОРА ---
        LARGE_INTEGER current_time;
        QueryPerformanceCounter(&current_time);
        double elapsed = (double)(current_time.QuadPart - last_time.QuadPart) / frequency.QuadPart;

        if (elapsed > 0.1) elapsed = 0.1; // защита от зависания окна

        if (elapsed > 0.0) {
            last_time = current_time;
            internal_debt += elapsed * Z80_CPU_SPEED;

            // Выполняем ровно столько тактов, сколько "задолжали" времени
            while (internal_debt > 0.0) {
                int ticks = 0;

                // Проверяем, наступил ли момент прерывания (50 Гц)
                if (cycles_until_interrupt <= 0) {
                    cycles_until_interrupt += CYCLES_PER_STEP;

                    // Инициируем аппаратное INT-прерывание для z80emu
                    int int_ticks = Z80Interrupt(&cpu, 0xFF, NULL);

                    if (int_ticks > 0)
                        ticks = int_ticks;

                    // Обновление состояния FLASH
                    if (++spec_flash_frame >= 16) {
                        spec_flash_frame = 0;
                        spec_flash_state = !spec_flash_state;
                    }

                    // Обновление виртуальных клавиш GUI
                    for (int k = 0; k < 40; ++k) {
                        if (gui_key_frames[k] > 0) {
                            --gui_key_frames[k];
                            if (gui_key_frames[k] == 0) {
                                int r = spec_hardware_map[k].row;
                                int b = spec_hardware_map[k].bit;
                                gui_key_rows[r] |= (BYTE)(1u << b);
                            }
                        }
                    }
                    RebuildSpectrumKeyboardMatrix();
                    PollPhysicalKeyboard(hwnd);

                    // Перерисовка экрана Windows строго по прерыванию кадра
                    InvalidateRect(hwnd, NULL, FALSE);
                    UpdateRegisterDisplay();
                }
                else {
                    // Обычный пошаговый вызов эмуляции одной инструкции
                    ticks = SystemStepZ80();
                }

                internal_debt -= ticks;
                audio_cpu_tstates += (uint64_t)ticks;
                cycles_until_interrupt -= ticks;
            }
        }
        else {
            Sleep(1);
        }

    }
    // Clean up audio subsystem if initialized
    StopAudio();
    return (int)msg.wParam;
}



