#define _CRT_SECURE_NO_WARNINGS
#define UNICODE
#define _UNICODE
#include <windows.h>
#include <mmsystem.h>
#include <fstream>
#include <vector>

#pragma comment(lib, "winmm.lib")

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
constexpr double ZX_CPU_CLOCK_HZ = 3500000.0; // Z80 clock

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
    const double tstates_per_sample = (double)ZX_CPU_CLOCK_HZ / (double)audio_sample_rate;

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

// --- СТРУКТУРА ПРОЦЕССОРА Z80 ---
#pragma pack(push, 1)
struct CPUZ80 {
    // Основные регистры (строго 8-бит)
    BYTE A, B, C, D, E, H, L;
    BYTE F; // Флаги: S(7) Z(6) X(5) H(4) X(3) P/V(2) N(1) C(0)

    // Альтернативные регистры (строго 8-бит shadow set)
    BYTE A_alt, F_alt, B_alt, C_alt, D_alt, E_alt, H_alt, L_alt;

    // Системные регистры (16-бит и 8-бит)
    WORD PC, SP;
    WORD IX, IY;
    BYTE I, R;
    // IM0 support helper: byte placed on data bus by external device when IM=0
    BYTE interrupt_vector_bus_byte = 0x00;

    bool IFF1, IFF2; // Флаги разрешения прерываний Z80
    BYTE IM;         // Режим прерываний (0, 1 или 2)
    bool halted;
    bool int_pending;
    int cycles_until_interrupt = 70000;
    int ei_delay_counter = 0; // counter to implement EI one-instruction delay (2 -> will enable after next step)

    void Reset() {
        PC = 0x0000;
        SP = 0xFFFF;
        A = B = C = D = E = H = L = F = 0;
        IX = IY = 0xFFFF;
        I = R = 0;
        A_alt = B_alt = C_alt = D_alt = E_alt = H_alt = L_alt = F_alt = 0;
        IFF1 = IFF2 = false;
        IM = 1;
        halted = false;
        int_pending = false;
        cycles_until_interrupt = 70000;
       ei_delay_counter = 0;
    }

    // Вспомогательные сеттеры/геттеры регистровых пар
    WORD GetHL() const { return ((WORD)H << 8) | L; }
    void SetHL(WORD val) { H = (BYTE)(val >> 8); L = (BYTE)(val & 0xFF); }

    WORD GetBC() const { return ((WORD)B << 8) | C; }
    void SetBC(WORD val) { B = (BYTE)(val >> 8); C = (BYTE)(val & 0xFF); }

    WORD GetDE() const { return ((WORD)D << 8) | E; }
    void SetDE(WORD val) { D = (BYTE)(val >> 8); E = (BYTE)(val & 0xFF); }

    // --- ШИНА ДАННЫХ И ПАМЯТИ ---
    inline BYTE ReadByte(int addr) {
        int target = addr & 0xFFFF; // Обрезаем до 16 бит
        if (target < 0x4000) {
            return spec_rom[target]; // Строго ROM
        }
        BYTE val = spec_ram[target - 0x4000]; // Строго RAM
        // Track floating bus: when video memory is read, the ULA would place
        // the last byte on the bus. We'll record last read from 0x4000..0x57FF
        if (target >= 0x4000 && target < 0x5800) {
            spec_last_floating_bus = val;
        }
        return val;
    }

    inline void WriteByte(int addr, BYTE val) {
        int target = addr & 0xFFFF;
        if (target < 0x4000) {
            return; // Защита ПЗУ
        }
        spec_ram[target - 0x4000] = val;
    }

    // Ввод-вывод из портов (ULA Spectrum)
    inline BYTE InPort(WORD port) {
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

    inline void OutPort(WORD port, BYTE val) {
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

    int StepZ80() {
        // Epilog helper: runs on function exit to handle EI delayed enable
        if (ei_delay_counter > 0) {
            ei_delay_counter--;
            if (ei_delay_counter == 0) {
                IFF1 = true; // enable interrupts after one instruction following EI
                IFF2 = true;
            }
        }

        // 1. Проверка маскируемого прерывания (50 Гц)
        if (int_pending && IFF1) {
            int_pending = false;
            halted = false;
            // Save previous IFF1 in IFF2 so RETN/RETI can restore it, then disable maskable interrupts
            IFF2 = IFF1;
            IFF1 = false;

            // Сохраняем текущий адрес возврата в стек
            WriteByte(--SP, PC >> 8);
            WriteByte(--SP, PC & 0xFF);

            // Обработка согласно режимам прерываний Z80
            if (IM == 1) {
                PC = 0x0038; // Стандартная обработка ZX Spectrum 48K
                return 13; // IM1: 13 T-states
            }
            else if (IM == 0) {
                // IM0: if an external device supplied a vector byte on the data bus,
                // the CPU will execute that opcode directly. We emulate a pragmatic
                // behavior: if interrupt_vector_bus_byte is non-zero and corresponds
                // to a RST n (0xC7/0xCF/.../0xFF) we jump to its vector; otherwise
                // fallback to IM1 (0x0038).
                if (interrupt_vector_bus_byte >= 0xC7 && interrupt_vector_bus_byte <= 0xFF) {
                    // RST n - compute vector
                    BYTE rst_index = (interrupt_vector_bus_byte - 0xC7) / 8;
                    WORD target = (WORD)(rst_index * 8);
                    PC = target;
                    return 13; // treat like RST timing
                }
                OutputDebugStringA("IM0: no vector byte or unsupported; treating as IM1 (0x0038)\n");
                PC = 0x0038;
                return 13;
            }
            else if (IM == 2) {
                WORD vector_addr = (I << 8) | 0xFF;
                WORD target_pc = ReadByte(vector_addr) | (ReadByte((WORD)(vector_addr + 1)) << 8);
                PC = target_pc;
                return 19; // IM2: 19 T-states (vector fetch + indirect)
            }
        }

        if (halted) return 4;

        WORD current_pc = PC;
        BYTE op = ReadByte(PC++);

        // Вставьте в StepZ80() сразу ПОСЛЕ: BYTE op = ReadByte(PC++);
        // --- ПЕРЕХВАТ ПРОЦЕДУРЫ LOAD ИЗ ПЗУ (ROM HOOK) ---
        if (current_pc == 0x0556 && tap_is_loaded) {
            // В этот момент регистры Z80 содержат:
            // A - ожидаемый тип блока (0x00 - заголовок, 0xFF - данные)
            // F - флаг переноса C (должен быть установлен для LOAD, сброшен для VERIFY)
            // DE - ожидаемая длина блока
            // IX - адрес в памяти, куда загружать данные

            if (tap_current_pos + 2 <= current_tap_data.size()) {
                // Читаем длину следующего блока из TAP файла
                WORD block_len = current_tap_data[tap_current_pos] | (current_tap_data[tap_current_pos + 1] << 8);

                if (tap_current_pos + 2 + block_len <= current_tap_data.size()) {
                    size_t block_start = tap_current_pos + 2;
                    BYTE flag = current_tap_data[block_start];

                    // Проверяем, совпадает ли тип блока с тем, что ищет система (обычно ПЗУ проверяет flag сама, но мы поможем)
                    // block_len включает 1 байт флага и 1 байт контрольной суммы. Длина чистых данных: block_len - 2
                    WORD data_len = block_len - 2;
                    const BYTE* raw_data = &current_tap_data[block_start + 1];

                    // Копируем данные напрямую в spec_ram по указателю из регистра IX процессора
                    WORD target_addr = IX;
                    for (WORD i = 0; i < data_len; i++) {
                        WriteByte(target_addr + i, raw_data[i]);
                    }

                    // Сдвигаем указатель ленты на следующий блок
                    tap_current_pos += 2 + block_len;

                    // Имитируем успешное завершение стандартной подпрограммы ПЗУ:
                    // 1. Устанавливаем флаг успешного завершения операции (регистр F: флаг C=1, флаг Z=1)
                    F |= (0x01 | 0x40); // F_C | F_Z
                    A = 0u;             // Регистр А зануляется при успешном чтении контрольной суммы

                    // 2. Имитируем выход из подпрограммы (RET). Снимаем адрес возврата со стека.
                    WORD low = ReadByte(SP);  SP = (SP + 1) & 0xFFFF;
                    WORD high = ReadByte(SP); SP = (SP + 1) & 0xFFFF;
                    PC = (high << 8) | low;

                    return 20; // Возвращаем затраченные T-states (эмуляция быстрой загрузки)
                }
            }
            // Если лента закончилась, сбрасываем флаг, чтобы ПЗУ выдало стандартную ошибку "R Tape loading error"
            tap_is_loaded = false;
        }

        R = (R & 0x80) | ((R + 1) & 0x7F);

        const BYTE F_C = 0x01; const BYTE F_N = 0x02; const BYTE F_V = 0x04;
        const BYTE F_H = 0x10; const BYTE F_Z = 0x40; const BYTE F_S = 0x80;

        static const BYTE parity_table[256] = {
            4,0,0,4,0,4,4,0,0,4,4,0,4,0,0,4,0,4,4,0,4,0,0,4,4,0,0,4,0,4,4,0,
            0,4,4,0,4,0,0,4,4,0,0,4,0,4,4,0,4,0,0,4,0,4,4,0,0,4,4,0,4,0,0,4,
            0,4,4,0,4,0,0,4,4,0,0,4,0,4,4,0,4,0,0,4,0,4,4,0,0,4,4,0,4,0,0,4,
            4,0,0,4,0,4,4,0,0,4,4,0,4,0,0,4,0,4,4,0,4,0,0,4,4,0,0,4,0,4,4,0,
            0,4,4,0,4,0,0,4,4,0,0,4,0,4,4,0,4,0,0,4,0,4,4,0,0,4,4,0,4,0,0,4,
            4,0,0,4,0,4,4,0,0,4,4,0,4,0,0,4,0,4,4,0,4,0,0,4,4,0,0,4,0,4,4,0,
            4,0,0,4,0,4,4,0,0,4,4,0,4,0,0,4,0,4,4,0,4,0,0,4,4,0,0,4,0,4,4,0,
            0,4,4,0,4,0,0,4,4,0,0,4,0,4,4,0,4,0,0,4,0,4,4,0,0,4,4,0,4,0,0,4
        };

        // --- ИСПРАВЛЕННЫЕ МАКРОСЫ АЛУ Z80 ---
#define ALU_ADD(val) { \
    BYTE operand = val; \
    DWORD res = (DWORD)A + operand; \
    F = 0; \
    if ((res & 0xFF) == 0) F |= F_Z; \
    if (res & 0x80) F |= F_S; \
    if (res & 0x100) F |= F_C; \
    if ((A ^ operand ^ res) & 0x10) F |= F_H; \
    if ((A ^ res) & (operand ^ res) & 0x80) F |= F_V; \
    A = (BYTE)res; \
}

#define ALU_ADC(val) { \
    BYTE operand = val; \
    BYTE carry = (F & F_C) ? 1 : 0; \
    DWORD res = (DWORD)A + operand + carry; \
    F = 0; \
    if ((res & 0xFF) == 0) F |= F_Z; \
    if (res & 0x80) F |= F_S; \
    if (res & 0x100) F |= F_C; \
    if ((A ^ operand ^ res) & 0x10) F |= F_H; \
    if ((A ^ res) & (operand ^ res) & 0x80) F |= F_V; \
    A = (BYTE)res; \
}

#define ALU_SUB(val) { \
    BYTE operand = val; \
    BYTE old_a = A; \
    BYTE res = A - operand; \
    F = F_N; \
    if (res == 0) F |= F_Z; \
    if (res & 0x80) F |= F_S; \
    if (old_a < operand) F |= F_C; \
    if (((old_a & 0x0F) - (operand & 0x0F)) & 0x10) F |= F_H; \
    if (((old_a ^ operand) & (old_a ^ res)) & 0x80) F |= F_V; \
    A = res; \
}

#define ALU_CP(val) { \
    BYTE operand = val; \
    BYTE old_a = A; \
    BYTE res = A - operand; \
    F = F_N; \
    if (res == 0) F |= F_Z; \
    if (res & 0x80) F |= F_S; \
    if (old_a < operand) F |= F_C; \
    if (((old_a & 0x0F) - (operand & 0x0F)) & 0x10) F |= F_H; \
    if (((old_a ^ operand) & (old_a ^ res)) & 0x80) F |= F_V; \
}

#define ALU_SBC(val) { \
    BYTE operand = val; \
    BYTE old_a = A; \
    BYTE carry = (F & F_C) ? 1 : 0; \
    int t_res = (int)A - (int)operand - (int)carry; \
    BYTE res = (BYTE)t_res; \
    F = F_N; \
    if (res == 0) F |= F_Z; \
    if (res & 0x80) F |= F_S; \
    if (t_res < 0) F |= F_C; \
    if (((old_a & 0x0F) - (operand & 0x0F) - carry) & 0x10) F |= F_H; \
    if (((old_a ^ operand) & (old_a ^ res)) & 0x80) F |= F_V; \
    A = res; \
}

#define ALU_AND(val) { \
    A &= val; \
    F = F_H | (A == 0 ? F_Z : 0) | (A & 0x80 ? F_S : 0) | (parity_table[A & 0xFF] ? F_V : 0); \
}

#define ALU_XOR(val) { \
    A ^= val; \
    F = (A == 0 ? F_Z : 0) | (A & 0x80 ? F_S : 0) | (parity_table[A & 0xFF] ? F_V : 0); \
}

#define ALU_OR(val) { \
    A |= val; \
    F = (A == 0 ? F_Z : 0) | (A & 0x80 ? F_S : 0) | (parity_table[A & 0xFF] ? F_V : 0); \
}

        switch (op) {
        case 0x00: return 4; // NOP
        case 0x06: { B = ReadByte(PC++); return 7; } // LD B, n
        case 0x0E: { C = ReadByte(PC++); return 7; } // LD C, n
        case 0x16: { D = ReadByte(PC++); return 7; } // LD D, n
        case 0x1E: { E = ReadByte(PC++); return 7; } // LD E, n
        case 0x26: { H = ReadByte(PC++); return 7; } // LD H, n
        case 0x2E: { L = ReadByte(PC++); return 7; } // LD L, n
        case 0x36: { BYTE val = ReadByte(PC++); WriteByte(GetHL(), val); return 10; } // LD (HL), n
        case 0x3E: { A = ReadByte(PC++); return 7; } // LD A, n

        case 0x27: { // --- ПОЛНАЯ АППАРАТНАЯ СИНХРОНИЗАЦИЯ DAA Z80 ---
            BYTE correction = 0; bool set_carry = false;
            if ((F & F_H) || ((A & 0x0F) > 9)) { correction |= 0x06; }
            if ((F & F_C) || (A > 0x99)) { correction |= 0x60; set_carry = true; }
            BYTE old_a = A;
            if (F & F_N) { A -= correction; }
            else { A += correction; }
            F &= ~(F_H | F_Z | F_S | F_V);
            if (F & F_N) { if ((old_a & 0x0F) < (correction & 0x0F)) F |= F_H; }
            else { if ((old_a & 0x0F) + (correction & 0x0F) > 0x0F) F |= F_H; }
            if (A == 0) F |= F_Z; if (A & 0x80) F |= F_S;
            if (parity_table[A]) F |= F_V; if (set_carry) F |= F_C;
            return 4;
        }

        case 0x01: { C = ReadByte(PC++); B = ReadByte(PC++); return 10; } // LD BC, nn
        case 0x11: { E = ReadByte(PC++); D = ReadByte(PC++); return 10; } // LD DE, nn
        case 0x21: { L = ReadByte(PC++); H = ReadByte(PC++); return 10; } // LD HL, nn
        case 0x31: { WORD l = ReadByte(PC++); WORD h = ReadByte(PC++); SP = (h << 8) | l; return 10; } // LD SP, nn

        case 0x0A: { A = ReadByte(GetBC()); return 7; } // LD A, (BC)
        case 0x1A: { A = ReadByte(GetDE()); return 7; } // LD A, (DE)
        case 0x02: { WriteByte(GetBC(), A); return 7; } // LD (BC), A
        case 0x12: { WriteByte(GetDE(), A); return 7; } // LD (DE), A
        case 0x22: { WORD l = ReadByte(PC++); WORD h = ReadByte(PC++); WORD adr = (h << 8) | l; WriteByte(adr, L); WriteByte((WORD)(adr + 1), H); return 16; } // LD (nn), HL
        case 0x2A: { WORD l = ReadByte(PC++); WORD h = ReadByte(PC++); WORD adr = (h << 8) | l; L = ReadByte(adr); H = ReadByte((WORD)(adr + 1)); return 16; } // LD HL, (nn)
        case 0x32: { WORD l = ReadByte(PC++); WORD h = ReadByte(PC++); WriteByte((h << 8) | l, A); return 13; } // LD (nn), A
        case 0x3A: { WORD l = ReadByte(PC++); WORD h = ReadByte(PC++); A = ReadByte((h << 8) | l); return 13; } // LD A, (nn)

        case 0x09: { DWORD res = GetHL() + GetBC(); F = (F & (F_Z | F_S | F_V)) | (((GetHL() & 0xFFF) + (GetBC() & 0xFFF) & 0x1000) ? F_H : 0) | ((res & 0x10000) ? F_C : 0); SetHL((WORD)res); return 11; }
        case 0x19: { DWORD res = GetHL() + GetDE(); F = (F & (F_Z | F_S | F_V)) | (((GetHL() & 0xFFF) + (GetDE() & 0xFFF) & 0x1000) ? F_H : 0) | ((res & 0x10000) ? F_C : 0); SetHL((WORD)res); return 11; }
        case 0x29: { DWORD res = GetHL() + GetHL(); F = (F & (F_Z | F_S | F_V)) | (((GetHL() & 0xFFF) + (GetHL() & 0xFFF) & 0x1000) ? F_H : 0) | ((res & 0x10000) ? F_C : 0); SetHL((WORD)res); return 11; }
        case 0x39: { DWORD res = GetHL() + SP; F = (F & (F_Z | F_S | F_V)) | (((GetHL() & 0xFFF) + (SP & 0xFFF) & 0x1000) ? F_H : 0) | ((res & 0x10000) ? F_C : 0); SetHL((WORD)res); return 11; }

        case 0x03: { WORD bc = GetBC(); bc++; SetBC(bc); return 6; } // INC BC
        case 0x0B: { WORD bc = GetBC(); bc--; SetBC(bc); return 6; } // DEC BC
        case 0x13: { WORD de = GetDE(); de++; SetDE(de); return 6; } // INC DE
        case 0x1B: { WORD de = GetDE(); de--; SetDE(de); return 6; } // DEC DE
        case 0x23: { WORD hl = GetHL(); hl++; SetHL(hl); return 6; } // INC HL
        case 0x2B: { WORD hl = ((WORD)H << 8) | L; hl--; H = (BYTE)(hl >> 8); L = (BYTE)(hl & 0xFF); return 6; } // DEC HL
        case 0x33: { SP++; return 6; } // INC SP
        case 0x3B: { SP--; return 6; } // DEC SP

        case 0x07: { BYTE c = (A & 0x80) ? 1 : 0; A = (A << 1) | c; F = (F & (F_Z | F_S | F_V)) | (c ? F_C : 0); return 4; } // RLCA
        case 0x17: { BYTE c = (A & 0x80) ? 1 : 0; BYTE old_c = F & F_C; A = (A << 1) | old_c; F = (F & (F_Z | F_S | F_V)) | (c ? F_C : 0); return 4; } // RLA
        case 0x0F: { BYTE c = A & 1; A = (A >> 1) | (c << 7); F = (F & (F_Z | F_S | F_V)) | (c ? F_C : 0); return 4; } // RRCA
        case 0x1F: { BYTE c = A & 1; BYTE old_c = F & F_C; A = (A >> 1) | (old_c << 7); F = (F & (F_Z | F_S | F_V)) | (c ? F_C : 0); return 4; } // RRA

        case 0x10: { signed char offset = (signed char)ReadByte(PC++); BYTE current_b = B; current_b--; B = current_b; if (B != 0) { PC = (WORD)((int)PC + offset); return 13; } return 8; } // DJNZ
        case 0x18: { signed char offset = (signed char)ReadByte(PC++); PC = (WORD)((int)PC + offset); return 12; } // JR e
        case 0x20: { signed char offset = (signed char)ReadByte(PC++); if (!(F & F_Z)) { PC = (WORD)((int)PC + offset); return 12; } return 7; } // JR NZ, e
        case 0x28: { signed char offset = (signed char)ReadByte(PC++); if (F & F_Z) { PC = (WORD)((int)PC + offset); return 12; } return 7; } // JR Z, e
        case 0x30: { signed char offset = (signed char)ReadByte(PC++); if (!(F & F_C)) { PC = (WORD)((int)PC + offset); return 12; } return 7; } // JR NC, e
        case 0x38: { signed char offset = (signed char)ReadByte(PC++); if (F & F_C) { PC = (WORD)((int)PC + offset); return 12; } return 7; } // JR C, e

        case 0xD3: { BYTE p = ReadByte(PC++); OutPort((WORD)(((WORD)A << 8) | p), A); return 11; } // OUT (n), A
        case 0xDB: { BYTE p = ReadByte(PC++); A = InPort((WORD)(((WORD)A << 8) | p)); F &= ~(F_N | F_H); if (A == 0) F |= F_Z; if (A & 0x80) F |= F_S; return 11; } // IN A, (n)

        case 0x76: { halted = true; return 4; } // HALT
        case 0xFB: { /* EI - enable interrupts after one instruction */ ei_delay_counter = 2; return 4; } // EI (delayed)
        case 0xF3: { IFF1 = false; IFF2 = false; ei_delay_counter = 0; return 4; } // DI

        case 0x08: { BYTE t = A; A = A_alt; A_alt = t; t = F; F = F_alt; F_alt = t; return 4; } // EX AF, AF'
        case 0xD9: { BYTE t; t = B; B = B_alt; B_alt = t; t = C; C = C_alt; C_alt = t; t = D; D = D_alt; D_alt = t; t = E; E = E_alt; E_alt = t; t = H; H = H_alt; H_alt = t; t = L; L = L_alt; L_alt = t; return 4; } // EXX
        case 0xEB: { BYTE t = D; D = H; H = t; t = E; E = L; L = t; return 4; } // EX DE, HL
        case 0xE3: { BYTE low_stack = ReadByte(SP); BYTE high_stack = ReadByte((WORD)(SP + 1)); WriteByte(SP, L); WriteByte((WORD)(SP + 1), H); L = low_stack; H = high_stack; return 19; } // EX (SP), HL
        case 0x2F: { A = ~A; F |= F_N | F_H; return 4; } // CPL
        case 0x37: { F = (F & (F_Z | F_S | F_V)) | F_C; return 4; } // SCF
        case 0x3F: { F = (F & (F_Z | F_S | F_V)) | ((F & F_C) ? F_H : F_C); return 4; } // CCF

#define INC_REG(reg) { \
    BYTE old = reg; reg++; \
    F = (F & F_C) | (reg == 0 ? F_Z : 0) | (reg & 0x80 ? F_S : 0) | ((((old & 0x0F) + 1) & 0x10) ? F_H : 0) | (old == 0x7F ? F_V : 0); \
    return 4; \
}

#define DEC_REG(reg) { \
    BYTE old = reg; reg--; \
    F = (F & F_C) | F_N | (reg == 0 ? F_Z : 0) | (reg & 0x80 ? F_S : 0) | (((old & 0x0F) < (reg & 0x0F)) ? F_H : 0) | (old == 0x80 ? F_V : 0); \
    return 4; \
}

        case 0x04: { INC_REG(B); break; }
        case 0x0C: { INC_REG(C); break; }
        case 0x14: { INC_REG(D); break; }
        case 0x1C: { INC_REG(E); break; }
        case 0x24: { INC_REG(H); break; }
        case 0x2C: { INC_REG(L); break; }
        case 0x3C: { INC_REG(A); break; }

        case 0x05: { DEC_REG(B); break; }
        case 0x0D: { DEC_REG(C); break; }
        case 0x15: { DEC_REG(D); break; }
        case 0x1D: { DEC_REG(E); break; }
        case 0x25: { DEC_REG(H); break; }
        case 0x2D: { DEC_REG(L); break; }
        case 0x3D: { DEC_REG(A); break; }

        case 0x34: { BYTE v = ReadByte(GetHL()); BYTE old = v; v++; WriteByte(GetHL(), v); F = (F & F_C) | (v == 0 ? F_Z : 0) | (v & 0x80 ? F_S : 0) | ((old & 0x0F) == 0x0F ? F_H : 0) | (old == 0x7F ? F_V : 0); return 11; }
        case 0x35: { BYTE v = ReadByte(GetHL()); BYTE old = v; v--; WriteByte(GetHL(), v); F = (F & F_C) | F_N | (v == 0 ? F_Z : 0) | (v & 0x80 ? F_S : 0) | ((old & 0x0F) == 0x00 ? F_H : 0) | (old == 0x80 ? F_V : 0); return 11; }

        case 0x80: ALU_ADD(B); return 4; case 0x81: ALU_ADD(C); return 4; case 0x82: ALU_ADD(D); return 4; case 0x83: ALU_ADD(E); return 4;
        case 0x84: ALU_ADD(H); return 4; case 0x85: ALU_ADD(L); return 4; case 0x86: ALU_ADD(ReadByte(GetHL())); return 7; case 0x87: ALU_ADD(A); return 4;
        case 0x88: ALU_ADC(B); return 4; case 0x89: ALU_ADC(C); return 4; case 0x8A: ALU_ADC(D); return 4; case 0x8B: ALU_ADC(E); return 4;
        case 0x8C: ALU_ADC(H); return 4; case 0x8D: ALU_ADC(L); return 4; case 0x8E: ALU_ADC(ReadByte(GetHL())); return 7; case 0x8F: ALU_ADC(A); return 4;
        case 0x90: ALU_SUB(B); return 4; case 0x91: ALU_SUB(C); return 4; case 0x92: ALU_SUB(D); return 4; case 0x93: ALU_SUB(E); return 4;
        case 0x94: ALU_SUB(H); return 4; case 0x95: ALU_SUB(L); return 4; case 0x96: ALU_SUB(ReadByte(GetHL())); return 7; case 0x97: ALU_SUB(A); return 4;
        case 0x98: ALU_SBC(B); return 4; case 0x99: ALU_SBC(C); return 4; case 0x9A: ALU_SBC(D); return 4; case 0x9B: ALU_SBC(E); return 4;
        case 0x9C: ALU_SBC(H); return 4; case 0x9D: ALU_SBC(L); return 4; case 0x9E: ALU_SBC(ReadByte(GetHL())); return 7; case 0x9F: ALU_SBC(A); return 4;
        case 0xA0: ALU_AND(B); return 4; case 0xA1: ALU_AND(C); return 4; case 0xA2: ALU_AND(D); return 4; case 0xA3: ALU_AND(E); return 4;
        case 0xA4: ALU_AND(H); return 4; case 0xA5: ALU_AND(L); return 4; case 0xA6: ALU_AND(ReadByte(GetHL())); return 7; case 0xA7: ALU_AND(A); return 4;
        case 0xAF: ALU_XOR(A); return 4; case 0xA8: ALU_XOR(B); return 4; case 0xA9: ALU_XOR(C); return 4; case 0xAA: ALU_XOR(D); return 4;
        case 0xAB: ALU_XOR(E); return 4; case 0xAC: ALU_XOR(H); return 4; case 0xAD: ALU_XOR(L); return 4; case 0xAE: ALU_XOR(ReadByte(GetHL())); return 7;
        case 0xB0: ALU_OR(B); return 4; case 0xB1: ALU_OR(C); return 4; case 0xB2: ALU_OR(D); return 4; case 0xB3: ALU_OR(E); return 4;
        case 0xB4: ALU_OR(H); return 4; case 0xB5: ALU_OR(L); return 4; case 0xB6: ALU_OR(ReadByte(GetHL())); return 7; case 0xB7: ALU_OR(A); return 4;
        case 0xB8: ALU_CP(B); return 4; case 0xB9: ALU_CP(C); return 4; case 0xBA: ALU_CP(D); return 4; case 0xBB: ALU_CP(E); return 4;
        case 0xBC: ALU_CP(H); return 4; case 0xBD: ALU_CP(L); return 4; case 0xBE: ALU_CP(ReadByte(GetHL())); return 7; case 0xBF: ALU_CP(A); return 4;

        case 0xC6: { ALU_ADD(ReadByte(PC++)); return 7; }
        case 0xCE: { ALU_ADC(ReadByte(PC++)); return 7; }
        case 0xD6: { ALU_SUB(ReadByte(PC++)); return 7; }
        case 0xDE: { ALU_SBC(ReadByte(PC++)); return 7; }
        case 0xE6: { ALU_AND(ReadByte(PC++)); return 7; }
        case 0xEE: { ALU_XOR(ReadByte(PC++)); return 7; }
        case 0xF6: { ALU_OR(ReadByte(PC++)); return 7; }
        case 0xFE: { ALU_CP(ReadByte(PC++)); return 7; }

        case 0xC3: { WORD l = ReadByte(PC++); WORD h = ReadByte(PC++); PC = (h << 8) | l; return 10; }
        case 0xE9: { PC = GetHL(); return 4; }
        case 0xF9: { SP = GetHL(); return 6; }
        case 0xCD: { WORD l = ReadByte(PC++); WORD h = ReadByte(PC++); WriteByte(--SP, (BYTE)(PC >> 8)); WriteByte(--SP, (BYTE)(PC & 0xFF)); PC = (h << 8) | l; return 17; }
        case 0xC9: { BYTE l = ReadByte(SP++); BYTE h = ReadByte(SP++); PC = (h << 8) | l; return 10; }

#define JP_COND(cond) { WORD l = ReadByte(PC++); WORD h = ReadByte(PC++); if (cond) PC = (h << 8) | l; return 10; }
#define CALL_COND(cond) { WORD l = ReadByte(PC++); WORD h = ReadByte(PC++); if (cond) { WriteByte(--SP, (BYTE)(PC >> 8)); WriteByte(--SP, (BYTE)(PC & 0xFF)); PC = (h << 8) | l; return 17; } return 10; }
#define RET_COND(cond) { if (cond) { BYTE l = ReadByte(SP++); BYTE h = ReadByte(SP++); PC = (h << 8) | l; return 11; } return 5; }

        case 0xC2: JP_COND(!(F & F_Z)); case 0xCA: JP_COND(F & F_Z); case 0xD2: JP_COND(!(F & F_C)); case 0xDA: JP_COND(F & F_C);
        case 0xE2: JP_COND(!(F & F_V)); case 0xEA: JP_COND(F & F_V); case 0xF2: JP_COND(!(F & F_S)); case 0xFA: JP_COND(F & F_S);
        case 0xC4: CALL_COND(!(F & F_Z)); case 0xCC: CALL_COND(F & F_Z); case 0xD4: CALL_COND(!(F & F_C)); case 0xDC: CALL_COND(F & F_C);
        case 0xE4: CALL_COND(!(F & F_V)); case 0xEC: CALL_COND(F & F_V); case 0xF4: CALL_COND(!(F & F_S)); case 0xFC: CALL_COND(F & F_S);
        case 0xC0: RET_COND(!(F & F_Z)); case 0xC8: RET_COND(F & F_Z); case 0xD0: RET_COND(!(F & F_C)); case 0xD8: RET_COND(F & F_C);
        case 0xE0: RET_COND(!(F & F_V)); case 0xE8: RET_COND(F & F_V); case 0xF0: RET_COND(!(F & F_S)); case 0xF8: RET_COND(F & F_S);

#define PUSH_REG(h, l) { WriteByte(--SP, h); WriteByte(--SP, l); return 11; }
#define POP_REG(h, l) { l = ReadByte(SP++); h = ReadByte(SP++); return 10; }
        case 0xC5: PUSH_REG(B, C); case 0xD5: PUSH_REG(D, E); case 0xE5: PUSH_REG(H, L); case 0xF5: PUSH_REG(A, F);
        case 0xC1: POP_REG(B, C); case 0xD1: POP_REG(D, E); case 0xE1: POP_REG(H, L); case 0xF1: POP_REG(A, F);

#define RST_VEC(adr) { WriteByte(--SP, (BYTE)(PC >> 8)); WriteByte(--SP, (BYTE)(PC & 0xFF)); PC = adr; return 11; }
        case 0xC7: RST_VEC(0x00); case 0xCF: RST_VEC(0x08); case 0xD7: RST_VEC(0x10); case 0xDF: RST_VEC(0x18);
        case 0xE7: RST_VEC(0x20); case 0xEF: RST_VEC(0x28); case 0xF7: RST_VEC(0x30); case 0xFF: RST_VEC(0x38);

        case 0xCB: {
            BYTE subOp = ReadByte(PC++);
            BYTE type = subOp >> 6;
            BYTE bit = (subOp >> 3) & 7;
            BYTE regIdx = subOp & 7;
            BYTE val = 0;
            if (regIdx == 0) val = B; else if (regIdx == 1) val = C;
            else if (regIdx == 2) val = D; else if (regIdx == 3) val = E;
            else if (regIdx == 4) val = H; else if (regIdx == 5) val = L;
            else if (regIdx == 6) val = ReadByte(GetHL()); else if (regIdx == 7) val = A;

            if (type == 0) {
                BYTE c = 0;
                switch (bit) {
                case 0: c = val >> 7; val = (val << 1) | c; break; // RLC
                case 1: c = val & 1; val = (val >> 1) | (c << 7); break; // RRC
                case 2: c = val >> 7; val = (val << 1) | ((F & F_C) ? 1 : 0); break; // RL
                case 3: c = val & 1; val = (val >> 1) | (((F & F_C) ? 1 : 0) << 7); break; // RR
                case 4: c = val >> 7; val <<= 1; break; // SLA
                case 5: c = val & 1; val = (signed char)val >> 1; break; // SRA
                case 6: c = val >> 7; val = (val << 1) | 1; break; // SLL
                case 7: c = val & 1; val >>= 1; break; // SRL
                }
                F = (val == 0 ? F_Z : 0) | (val & 0x80 ? F_S : 0) | (c ? F_C : 0) | (parity_table[val & 0xFF] ? F_V : 0);
            }
            else if (type == 1) {
                F = (F & F_C) | F_H | (!(val & (1 << bit)) ? F_Z : 0) | (bit == 7 && (val & 0x80) ? F_S : 0);
            }
            else if (type == 2) { val &= ~(1 << bit); }
            else if (type == 3) { val |= (1 << bit); }

            if (regIdx == 0) B = val; else if (regIdx == 1) C = val;
            else if (regIdx == 2) D = val; else if (regIdx == 3) E = val;
            else if (regIdx == 4) H = val; else if (regIdx == 5) L = val;
            else if (regIdx == 6) WriteByte(GetHL(), val); else if (regIdx == 7) A = val;
            return (regIdx == 6) ? 15 : 8;
        }

        case 0xED: {
            BYTE subOp = ReadByte(PC++);

            // 1. Команды сложения и вычитания 16-бит с переносом: ADC HL, ss / SBC HL, ss
            if ((subOp & 0xCF) == 0x42 || (subOp & 0xCF) == 0x4A) {
                DWORD hl_val = GetHL(); DWORD ss_val = 0;
                BYTE ss = (subOp >> 4) & 3;
                if (ss == 0) ss_val = GetBC(); else if (ss == 1) ss_val = GetDE();
                else if (ss == 2) ss_val = GetHL(); else if (ss == 3) ss_val = SP;
                DWORD carry = (F & F_C) ? 1 : 0;
                bool is_sbc = ((subOp & 0x0F) == 0x02);
                if (is_sbc) {
                    DWORD res = (hl_val - ss_val - carry) & 0xFFFFFFFF; F = F_N;
                    if ((res & 0xFFFF) == 0) F |= F_Z; if (res & 0x8000) F |= F_S;
                    if (hl_val < (ss_val + carry)) F |= F_C;
                    if (((hl_val & 0x0FFF) - (ss_val & 0x0FFF) - carry) & 0x1000) F |= F_H;
                    if (((hl_val ^ ss_val) & (hl_val ^ res)) & 0x8000) F |= F_V;
                    SetHL((WORD)res);
                }
                else {
                    DWORD res = hl_val + ss_val + carry; F = 0;
                    if ((res & 0xFFFF) == 0) F |= F_Z; if (res & 0x8000) F |= F_S;
                    if (res & 0x10000) F |= F_C;
                    if (((hl_val & 0x0FFF) + (ss_val & 0x0FFF) + carry) & 0x1000) F |= F_H;
                    if (((hl_val ^ ss_val ^ 0x8000) & (ss_val ^ res)) & 0x8000) F |= F_V;
                    SetHL((WORD)res);
                }
                return 15;
            }

            // 2. Команды загрузки 16-битных регистров из памяти: LD (nn), dd / LD dd, (nn)
            if ((subOp & 0xCF) == 0x43 || (subOp & 0xCF) == 0x4B) {
                WORD l = ReadByte(PC++); WORD h = ReadByte(PC++);
                WORD adr = (h << 8) | l; BYTE dd = (subOp >> 4) & 3;
                bool is_store = ((subOp & 0x0F) == 0x03);
                if (is_store) {
                    WORD val = (dd == 0) ? GetBC() : (dd == 1 ? GetDE() : (dd == 2 ? GetHL() : SP));
                    WriteByte(adr, val & 0xFF); WriteByte((WORD)(adr + 1), val >> 8);
                }
                else {
                    WORD val = ReadByte(adr) | (ReadByte((WORD)(adr + 1)) << 8);
                    if (dd == 0) SetBC(val); else if (dd == 1) SetDE(val);
                    else if (dd == 2) SetHL(val); else if (dd == 3) SP = val;
                }
                return 20;
            }

            // 3. Аппаратно точная дешифрация команд ввода-вывода: IN r, (C) / OUT (C), r
            if ((subOp & 0xC0) == 0x40 && (subOp & 0x07) <= 1) {
                BYTE regIdx = ((subOp & 0xFF) >> 3) & 7;
                bool is_out = ((subOp & 1) != 0);
                if (is_out) {
                    BYTE srcVal = 0;
                    if (regIdx == 0) srcVal = B; else if (regIdx == 1) srcVal = C;
                    else if (regIdx == 2) srcVal = D; else if (regIdx == 3) srcVal = E;
                    else if (regIdx == 4) srcVal = H; else if (regIdx == 5) srcVal = L;
                    else if (regIdx == 6) srcVal = 0; else if (regIdx == 7) srcVal = A;
                    OutPort(GetBC(), srcVal); return 12;
                }
                else {
                    BYTE inputVal = InPort(GetBC());
                    if (regIdx == 0) B = inputVal; else if (regIdx == 1) C = inputVal;
                    else if (regIdx == 2) D = inputVal; else if (regIdx == 3) E = inputVal;
                    else if (regIdx == 4) H = inputVal; else if (regIdx == 5) L = inputVal;
                    else if (regIdx == 7) A = inputVal;
                    F = (F & F_C) | (inputVal == 0 ? F_Z : 0) | (inputVal & 0x80 ? F_S : 0) | (parity_table[inputVal & 0xFF] ? F_V : 0);
                    return 12;
                }
            }

            // 4. Одиночные подкоманды префикса 0xED
            switch (subOp) {
            case 0xB0: { // LDIR
                WORD src = GetHL(); WORD dest = GetDE(); WORD len = GetBC();
                while (len > 0) { WriteByte(dest, ReadByte(src)); src++; dest++; len--; }
                SetHL(src); SetDE(dest); SetBC(0); F &= ~(F_N | F_H | F_V); return 21;
            }
            case 0xB8: { // LDDR
                WORD src = GetHL(); WORD dest = GetDE(); WORD len = GetBC();
                while (len > 0) { WriteByte(dest, ReadByte(src)); src--; dest--; len--; }
                SetHL(src); SetDE(dest); SetBC(0); F &= ~(F_N | F_H | F_V); return 21;
            }
            case 0xA0: { // LDI
                WriteByte(GetDE(), ReadByte(GetHL())); SetHL(GetHL() + 1); SetDE(GetDE() + 1); SetBC(GetBC() - 1);
                F &= ~(F_N | F_H | F_V); if (GetBC() != 0) F |= F_V; return 14;
            }
            case 0xA8: { // LDD
                WriteByte(GetDE(), ReadByte(GetHL())); SetHL(GetHL() - 1); SetDE(GetDE() - 1); SetBC(GetBC() - 1);
                F &= ~(F_N | F_H | F_V); if (GetBC() != 0) F |= F_V; return 14;
            }
            case 0xA1: case 0xB1: { // CPI / CPIR
                BYTE val = ReadByte(GetHL()); int res = A - val; SetHL(GetHL() + 1); SetBC(GetBC() - 1);
                F = (F & F_C) | F_N | (res == 0 ? F_Z : 0) | (res & 0x80 ? F_S : 0) | (((A & 0x0F) - (val & 0x0F)) & 0x10 ? F_H : 0) | (GetBC() != 0 ? F_V : 0);
                if (subOp == 0xB1 && GetBC() != 0 && res != 0) { PC -= 2; return 21; } return 16;
            }
            case 0xA2: case 0xB2: { // INI / INIR
                BYTE val = InPort(GetBC()); WriteByte(GetHL(), val); B--; SetHL(GetHL() + 1);
                F = F_N | (B == 0 ? F_Z : 0) | (B & 0x80 ? F_S : 0); if (subOp == 0xB2 && B != 0) { PC -= 2; return 21; } return 16;
            }
            case 0xA3: case 0xB3: { // OUTI / OTIR
                BYTE val = ReadByte(GetHL()); OutPort(GetBC(), val); B--; SetHL(GetHL() + 1);
                F = F_N | (B == 0 ? F_Z : 0) | (B & 0x80 ? F_S : 0); if (subOp == 0xB3 && B != 0) { PC -= 2; return 21; } return 16;
            }
            case 0x44: { A = 0 - A; F = F_N | (A == 0 ? F_Z : 0) | (A & 0x80 ? F_S : 0); return 8; } // NEG
            case 0x45: { IFF1 = IFF2; BYTE l = ReadByte(SP++); BYTE h = ReadByte(SP++); PC = (h << 8) | l; return 14; } // RETN
            case 0x4D: { IFF1 = IFF2; BYTE l = ReadByte(SP++); BYTE h = ReadByte(SP++); PC = (h << 8) | l; return 14; } // RETI
            case 0x46: { IM = 0; return 8; } case 0x56: { IM = 1; return 8; } case 0x5E: { IM = 2; return 8; }
            case 0x47: { I = A; return 9; } case 0x57: { A = I; F = (F & F_C) | (A == 0 ? F_Z : 0) | (A & 0x80 ? F_S : 0) | (IFF2 ? F_V : 0); return 9; }
            case 0x4F: { R = A; return 9; } case 0x5F: { A = R; F = (F & F_C) | (A == 0 ? F_Z : 0) | (A & 0x80 ? F_S : 0) | (IFF2 ? F_V : 0); return 9; }
            }
            return 8;
        }

        case 0xDD:
        case 0xFD: {
            const bool use_iy = (op == 0xFD);
            BYTE subOp = ReadByte(PC++);

            // DD CB d op / FD CB d op
            if (subOp == 0xCB) {
                signed char disp = (signed char)ReadByte(PC++);
                BYTE cbOp = ReadByte(PC++);
                WORD index = use_iy ? IY : IX;
                WORD addr = (WORD)(index + disp);
                BYTE val = ReadByte(addr);
                BYTE type = cbOp >> 6;
                BYTE bit = (cbOp >> 3) & 7;
                BYTE regIdx = cbOp & 7;

                if (type == 1) {
                    BYTE mask = (BYTE)(1u << bit);
                    // BIT b,(IX/IY+d): Z is set when the tested bit is zero,
                    // S is meaningful only for bit 7, H=1, N=0, C preserved.
                    F = (F & F_C) | F_H |
                        ((val & mask) ? 0 : F_Z) |
                        ((bit == 7 && (val & 0x80)) ? F_S : 0) |
                        (parity_table[val] && bit != 7 ? F_V : 0);
                    return 20;
                }

                BYTE result = val;
                BYTE carry_out = 0;
                switch (bit) {
                case 0: carry_out = (BYTE)(result >> 7); result = (BYTE)((result << 1) | carry_out); break; // RLC
                case 1: carry_out = (BYTE)(result & 1); result = (BYTE)((result >> 1) | (carry_out << 7)); break; // RRC
                case 2: carry_out = (BYTE)(result >> 7); result = (BYTE)((result << 1) | ((F & F_C) ? 1 : 0)); break; // RL
                case 3: carry_out = (BYTE)(result & 1); result = (BYTE)((result >> 1) | (((F & F_C) ? 1 : 0) << 7)); break; // RR
                case 4: carry_out = (BYTE)(result >> 7); result = (BYTE)(result << 1); break; // SLA
                case 5: carry_out = (BYTE)(result & 1); result = (BYTE)(((signed char)result) >> 1); break; // SRA
                case 6: carry_out = (BYTE)(result >> 7); result = (BYTE)((result << 1) | 1); break; // SLL
                case 7: carry_out = (BYTE)(result & 1); result = (BYTE)(result >> 1); break; // SRL
                }

                if (type == 0) {
                    F = (result == 0 ? F_Z : 0) |
                        (result & 0x80 ? F_S : 0) |
                        (parity_table[result] ? F_V : 0) |
                        (carry_out ? F_C : 0);
                }
                else if (type == 2) {
                    result = (BYTE)(val & ~(1u << bit));
                }
                else {
                    result = (BYTE)(val | (1u << bit));
                }

                WriteByte(addr, result);
                // DD/FD CB forms with r=6 are memory-only. Otherwise the
                // transformed byte is also copied into the selected register.
                if (regIdx == 0) B = result;
                else if (regIdx == 1) C = result;
                else if (regIdx == 2) D = result;
                else if (regIdx == 3) E = result;
                else if (regIdx == 4) H = result;
                else if (regIdx == 5) L = result;
                else if (regIdx == 7) A = result;
                return 23;
            }

            // --- ПОЛНАЯ ПОДДЕРЖКА ДОКУМЕНТИРОВАННЫХ И НЕДОКУМЕНТИРОВАННЫХ КОМАНД IX/IY ---
            WORD& index = use_iy ? IY : IX;

            // Выделяем ссылки на половинки регистров для недокументированных опкодов
            BYTE& index_h = use_iy ? *(BYTE*)((BYTE*)&IY + 1) : *(BYTE*)((BYTE*)&IX + 1);
            BYTE& index_l = use_iy ? *(BYTE*)((BYTE*)&IY) : *(BYTE*)((BYTE*)&IX);

            if (subOp == 0x21) {
                WORD l = ReadByte(PC++), h = ReadByte(PC++);
                index = (WORD)((h << 8) | l);
                return 14;
            }
            if (subOp == 0x22) {
                WORD l = ReadByte(PC++), h = ReadByte(PC++);
                WORD adr = (WORD)((h << 8) | l);
                WriteByte(adr, (BYTE)(index & 0xFF));
                WriteByte((WORD)(adr + 1), (BYTE)(index >> 8));
                return 20;
            }
            if (subOp == 0x2A) {
                WORD l = ReadByte(PC++), h = ReadByte(PC++);
                WORD adr = (WORD)((h << 8) | l);
                index = (WORD)(ReadByte(adr) | (ReadByte((WORD)(adr + 1)) << 8));
                return 20;
            }
            if (subOp == 0x23) { index = (WORD)(index + 1); return 10; }
            if (subOp == 0x2B) { index = (WORD)(index - 1); return 10; }

            if (subOp == 0xE5) {
                WriteByte(--SP, (BYTE)(index >> 8));
                WriteByte(--SP, (BYTE)index);
                return 15;
            }
            if (subOp == 0xE1) {
                BYTE l = ReadByte(SP); SP = (WORD)(SP + 1);
                BYTE h = ReadByte(SP); SP = (WORD)(SP + 1);
                index = (WORD)((h << 8) | l);
                return 14;
            }
            if (subOp == 0xE3) {
                BYTE low = ReadByte(SP);
                BYTE high = ReadByte((WORD)(SP + 1));
                WriteByte(SP, (BYTE)index);
                WriteByte((WORD)(SP + 1), (BYTE)(index >> 8));
                index = (WORD)(low | (high << 8));
                return 23;
            }
            if (subOp == 0xE9) { PC = index; return 8; }
            if (subOp == 0xF9) { SP = index; return 10; }

            // ADD IX/IY,rr
            if ((subOp & 0xCF) == 0x09) {
                WORD ss_val = 0;
                BYTE ss = (subOp >> 4) & 3;
                if (ss == 0) ss_val = GetBC();
                else if (ss == 1) ss_val = GetDE();
                else if (ss == 2) ss_val = index;
                else ss_val = SP;
                DWORD res = (DWORD)index + ss_val;
                F = (F & (F_Z | F_S | F_V)) |
                    ((((index & 0x0FFF) + (ss_val & 0x0FFF)) > 0x0FFF) ? F_H : 0) |
                    ((res & 0x10000) ? F_C : 0);
                index = (WORD)res;
                return 15;
            }

            // LD (IX+d),n / LD (IY+d),n -- this was the missing instruction
            // that desynchronised PC immediately after ROM 128E.
            if (subOp == 0x36) {
                signed char disp = (signed char)ReadByte(PC++);
                BYTE value = ReadByte(PC++);
                WriteByte((WORD)(index + disp), value);
                return 19;
            }

            // INC/DEC (IX+d) / (IY+d)
            if (subOp == 0x34 || subOp == 0x35) {
                signed char disp = (signed char)ReadByte(PC++);
                WORD addr = (WORD)(index + disp);
                BYTE old = ReadByte(addr);
                BYTE res = (subOp == 0x34) ? (BYTE)(old + 1) : (BYTE)(old - 1);

                BYTE old_c = F & F_C;
                if (subOp == 0x34) {
                    F = old_c |
                        (res == 0 ? F_Z : 0) |
                        (res & 0x80 ? F_S : 0) |
                        (((old & 0x0F) == 0x0F) ? F_H : 0) |
                        (old == 0x7F ? F_V : 0);
                }
                else {
                    F = old_c | F_N |
                        (res == 0 ? F_Z : 0) |
                        (res & 0x80 ? F_S : 0) |
                        (((old & 0x0F) == 0x00) ? F_H : 0) |
                        (old == 0x80 ? F_V : 0);
                }
                WriteByte(addr, res);
                return 23;
            }

            // LD r,(IX+d)/(IY+d), LD (IX+d),r
            if ((subOp & 0xC0) == 0x40 && subOp != 0x76) {
                BYTE destIdx = (subOp >> 3) & 7;
                BYTE srcIdx = subOp & 7;

                if (srcIdx == 6) {
                    signed char disp = (signed char)ReadByte(PC++);
                    BYTE memVal = ReadByte((WORD)(index + disp));
                    if (destIdx == 0) B = memVal;
                    else if (destIdx == 1) C = memVal;
                    else if (destIdx == 2) D = memVal;
                    else if (destIdx == 3) E = memVal;
                    else if (destIdx == 4) H = memVal;
                    else if (destIdx == 5) L = memVal;
                    else if (destIdx == 7) A = memVal;
                    return 19;
                }

                if (destIdx == 6) {
                    signed char disp = (signed char)ReadByte(PC++);
                    BYTE srcVal = 0;
                    if (srcIdx == 0) srcVal = B;
                    else if (srcIdx == 1) srcVal = C;
                    else if (srcIdx == 2) srcVal = D;
                    else if (srcIdx == 3) srcVal = E;
                    else if (srcIdx == 4) srcVal = H;
                    else if (srcIdx == 5) srcVal = L;
                    else if (srcIdx == 7) srcVal = A;
                    WriteByte((WORD)(index + disp), srcVal);
                    return 19;
                }
            }

            // ALU A,(IX+d)/(IY+d): 86/8E/96/9E/A6/AE/B6/BE
            if ((subOp & 0xC7) == 0x86) {
                signed char disp = (signed char)ReadByte(PC++);
                BYTE value = ReadByte((WORD)(index + disp));
                switch (subOp) {
                case 0x86: ALU_ADD(value); break;
                case 0x8E: ALU_ADC(value); break;
                case 0x96: ALU_SUB(value); break;
                case 0x9E: ALU_SBC(value); break;
                case 0xA6: ALU_AND(value); break;
                case 0xAE: ALU_XOR(value); break;
                case 0xB6: ALU_OR(value); break;
                case 0xBE: ALU_CP(value); break;
                }
                return 19;
            }

            // --- ИСПРАВЛЕНО: ДЕКОДИРОВАНИЕ НЕДОКУМЕНТИРОВАННЫХ ОПКОДОВ ДЛЯ ПОЛОВИНОК IX/IY ---
            // Сюда попадает ваш опкод 0x54 (LD D, IXH) и все операции ALU над половинками регистров
            {
                BYTE destReg = (subOp >> 3) & 7;
                BYTE srcReg = subOp & 7;

                // Перенаправление обращений к H/L на половинки IXH/IXL (или IYH/IYL)
                auto get_val = [&](BYTE reg) -> BYTE {
                    if (reg == 0) return B; if (reg == 1) return C; if (reg == 2) return D; if (reg == 3) return E;
                    if (reg == 4) return index_h; // Вместо H читаем старшую половинку индекса
                    if (reg == 5) return index_l; // Вместо L читаем младшую половинку индекса
                    if (reg == 7) return A;
                    return 0;
                    };

                // Одиночные операции INC/DEC над половинками регистров (0x24, 0x25, 0x2C, 0x2D)
                if ((subOp & 0xC7) == 0x04) {
                    BYTE r = (subOp >> 3) & 7;
                    if (r == 4) { INC_REG(index_h); } if (r == 5) { INC_REG(index_l); }
                }
                if ((subOp & 0xC7) == 0x05) {
                    BYTE r = (subOp >> 3) & 7;
                    if (r == 4) { DEC_REG(index_h); } if (r == 5) { DEC_REG(index_l); }
                }

                // Команды типа LD r, r' над половинками регистров
                if ((subOp & 0xC0) == 0x40) {
                    BYTE val = get_val(srcReg);
                    if (destReg == 0) B = val; else if (destReg == 1) C = val;
                    else if (destReg == 2) D = val; else if (destReg == 3) E = val;
                    else if (destReg == 4) index_h = val; else if (destReg == 5) index_l = val;
                    else if (destReg == 7) A = val;
                    return 4;
                }

                // Операции ALU над половинками регистров (ADD, SUB, AND, CP и т.д.)
                if ((subOp & 0xC0) == 0x80) {
                    BYTE val = get_val(srcReg);
                    switch ((subOp >> 3) & 7) {
                    case 0: ALU_ADD(val); break; case 1: ALU_ADC(val); break;
                    case 2: ALU_SUB(val); break; case 3: ALU_SBC(val); break;
                    case 4: ALU_AND(val); break; case 5: ALU_XOR(val); break;
                    case 6: ALU_OR(val); break;  case 7: ALU_CP(val); break;
                    }
                    return 4;
                }

                // Опкоды загрузки непосредственного значения типа LD IXH, n
                if (subOp == 0x26) { index_h = ReadByte(PC++); return 7; }
                if (subOp == 0x2E) { index_l = ReadByte(PC++); return 7; }
            }

            return 4;
        }

        default:
            if ((op & 0xC0) == 0x40 && op != 0x76) {
                BYTE srcIdx = op & 7; BYTE destIdx = (op >> 3) & 7; BYTE srcVal = 0;
                if (srcIdx == 0) srcVal = B; else if (srcIdx == 1) srcVal = C; else if (srcIdx == 2) srcVal = D; else if (srcIdx == 3) srcVal = E;
                else if (srcIdx == 4) srcVal = H; else if (srcIdx == 5) srcVal = L; else if (srcIdx == 6) srcVal = ReadByte(GetHL()); else if (srcIdx == 7) srcVal = A;

                if (destIdx == 0) B = srcVal; else if (destIdx == 1) C = srcVal; else if (destIdx == 2) D = srcVal; else if (destIdx == 3) E = srcVal;
                else if (destIdx == 4) H = srcVal; else if (destIdx == 5) L = srcVal; else if (destIdx == 6) WriteByte(GetHL(), srcVal); else if (destIdx == 7) A = srcVal;
                return (srcIdx == 6 || destIdx == 6) ? 7 : 4;
            }
            {
                // Безопасное чтение байт через ReadByte вместо прямого выхода за границы spec_rom
                wchar_t errBuf[512];
                swprintf_s(errBuf, 512,
                    L"CRITICAL ERROR: Unimplemented Z80 opcode!\n"
                    L"Op: 0x%02X PC: 0x%04X\n"
                    L"Regs: A:0x%02X F:0x%02X HL:0x%04X SP:0x%04X\n"
                    L"ROM bytes: %02X %02X %02X %02X\n",
                    op, current_pc, A, F, GetHL(), SP,
                    ReadByte(current_pc), ReadByte(current_pc + 1), ReadByte(current_pc + 2), ReadByte(current_pc + 3));

                // Запись лога ошибок в кодировке UTF-8
                FILE* fErr = NULL;
                if (_wfopen_s(&fErr, L"z80_error_log.txt", L"a") == 0 && fErr) {
                    fwprintf(fErr, L"%s", errBuf);
                    fclose(fErr);
                }

                // Вывод сообщения в отладчик Visual Studio
                char outBuf[512];
                int n = WideCharToMultiByte(CP_UTF8, 0, errBuf, -1, outBuf, sizeof(outBuf), NULL, NULL);
                if (n > 0) OutputDebugStringA(outBuf);

                // Грациозная остановка бесконечного цикла симулятора
                emulator_running = false;
                return 4;
            }
        }
    }
};
#pragma pack(pop)

CPUZ80 cpu;

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
    cpu.Reset();
    spec_speaker_state = false;
    ay.Reset();

    cpu.I = h[0];
    cpu.L_alt = h[1]; cpu.H_alt = h[2];
    cpu.E_alt = h[3]; cpu.D_alt = h[4];
    cpu.C_alt = h[5]; cpu.B_alt = h[6];
    cpu.F_alt = h[7]; cpu.A_alt = h[8];

    cpu.L = h[9];  cpu.H = h[10];
    cpu.E = h[11]; cpu.D = h[12];
    cpu.C = h[13]; cpu.B = h[14];
    cpu.IY = ReadLE16(h + 15);
    cpu.IX = ReadLE16(h + 17);
    cpu.IFF1 = (h[19] & 0x04) != 0;
    cpu.IFF2 = cpu.IFF1;
    cpu.R = h[20];
    cpu.F = h[21];
    cpu.A = h[22];
    cpu.SP = ReadLE16(h + 23);
    cpu.IM = (BYTE)(h[25] & 0x03);
    if (cpu.IM > 2) cpu.IM = 2;

    spec_border_color = h[26] & 0x07;

    for (size_t i = 0; i < 49152; ++i)
        spec_ram[i] = data[27 + i];

    // In a 48K SNA the PC is stored on the stack. Loading it is equivalent
    // to executing RETN immediately after restoring the snapshot.
    if (cpu.SP < 0x4000) {
        error = L"Некорректный .SNA: SP указывает в ПЗУ.";
        return false;
    }

    size_t ram_offset = (size_t)(cpu.SP - 0x4000);
    if (ram_offset + 1 >= 49152) {
        error = L"Некорректный .SNA: PC на стеке выходит за пределы RAM.";
        return false;
    }

    cpu.PC = (WORD)spec_ram[ram_offset] |
             ((WORD)spec_ram[ram_offset + 1] << 8);
    cpu.SP = (WORD)(cpu.SP + 2);

    cpu.halted = false;
    cpu.int_pending = false;
    cpu.ei_delay_counter = 0;
    cpu.cycles_until_interrupt = 70000;
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
    cpu.Reset();
    spec_speaker_state = false;
    ay.Reset();

    cpu.A = h[0];
    cpu.F = h[1];
    cpu.SetBC(ReadLE16(h + 2));
    cpu.SetHL(ReadLE16(h + 4));

    WORD pc_header = ReadLE16(h + 6);
    cpu.SP = ReadLE16(h + 8);
    cpu.I = h[10];
    cpu.R = (BYTE)((h[11] & 0x7F) | ((h[12] & 0x01) << 7));
    spec_border_color = (h[12] >> 1) & 0x07;

    cpu.SetDE(ReadLE16(h + 13));
    cpu.C_alt = h[15]; cpu.B_alt = h[16];
    cpu.E_alt = h[17]; cpu.D_alt = h[18];
    cpu.L_alt = h[19]; cpu.H_alt = h[20];
    cpu.A_alt = h[21]; cpu.F_alt = h[22];
    cpu.IY = ReadLE16(h + 23);
    cpu.IX = ReadLE16(h + 25);
    cpu.IFF1 = h[27] != 0;
    cpu.IFF2 = h[28] != 0;
    cpu.IM = (BYTE)(h[29] & 0x03);
    if (cpu.IM > 2) cpu.IM = 2;

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
        cpu.PC = pc_header;
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
        cpu.PC = ReadLE16(ext);
        BYTE machine = ext[2];

        // Hardware modes 0 and 1 are 48K modes. This emulator is 48K-only.
        if (machine > 1) {
            error = L"Этот эмулятор поддерживает .Z80 только для ZX Spectrum 48K.";
            return false;
        }
        if (cpu.PC == 0) {
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

    cpu.halted = false;
    cpu.int_pending = false;
    cpu.ei_delay_counter = 0;
    cpu.cycles_until_interrupt = 70000;
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
    cpu.Reset();
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
    swprintf(buf, 64, L" PC: %04Xh  SP: %04Xh", cpu.PC, cpu.SP);
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" REG A: %02Xh F: %02Xh", cpu.A, cpu.F);
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" REG BC: %04Xh", cpu.GetBC());
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" REG DE: %04Xh", cpu.GetDE());
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" REG HL: %04Xh", cpu.GetHL());
    SendMessageW(hRegListBox, LB_ADDSTRING, 0, (LPARAM)buf);
    swprintf(buf, 64, L" IX: %04Xh IY: %04Xh", cpu.IX, cpu.IY);
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
            cpu.Reset();
            cpu.PC = 0x5B00;
            cpu.SP = 0xFFFF;
            ok = true;
        }
    }

    if (!ok) {
        MessageBoxW(hwnd, error.c_str(),
                    L"Ошибка загрузки snapshot",
                    MB_OK | MB_ICONERROR);
        return;
    }

    spec_flash_frame = 0;
    spec_flash_state = false;
    RebuildSpectrumKeyboardMatrix();
    UpdateRegisterDisplay();
    SetFocus(hwnd);

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
        cpu.Reset();
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
            cpu.Reset();
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
            internal_debt += elapsed * ZX_CPU_CLOCK_HZ;

            // Выполняем ровно столько тактов, сколько "задолжали" времени
            while (internal_debt > 0.0) {
                int ticks = cpu.StepZ80();
                if (ticks <= 0) { // guard against faulty opcode handling returning 0 and locking the loop
                    // Critical error inside CPU emulation; stop emulator to avoid infinite loop
                    emulator_running = false;
                    break;
                }
                internal_debt -= ticks;
                audio_cpu_tstates += (uint64_t)ticks;

                // Декрементируем такты до прихода прерывания
                cpu.cycles_until_interrupt -= ticks;
                if (cpu.cycles_until_interrupt <= 0) {
                    cpu.int_pending = true;
                    cpu.cycles_until_interrupt += 70000; // 50 Гц прерывания

                    // ZX Spectrum FLASH changes phase every 16 video frames.
                    // At 50 Hz this gives ~320 ms ON and ~320 ms OFF.
                    if (++spec_flash_frame >= 16) {
                        spec_flash_frame = 0;
                        spec_flash_state = !spec_flash_state;
                    }

                    // Release virtual GUI keys independently, without touching
                    // physical keys that may still be held down.
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
// Обновляем экран строго по прерыванию (50 кадров в секунду)
                    InvalidateRect(hwnd, NULL, FALSE);
                    UpdateRegisterDisplay();

                }
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



