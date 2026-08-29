#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h> // Обеспечивает полную совместимость bool между C и C++

// ---------------------------------------
// ABBREVIATIONS & TYPES

typedef int8_t i8;
typedef uint8_t u8;
typedef uint16_t u16;
typedef bool bv;

#define SI static inline
#define R return

// Defining a single-expression function body.
// Equivalent declarations:
// u8 f(u8 a)_(a * 2)
// u8 f(u8 a) { return a * 2; }
#define _(...) { return (__VA_ARGS__); }

// ---------------------------------------
// GLOBAL CPU STRUCTURE DEFINITION

struct CPUZ80 {
    u16 PC, SP, IX, IY;
    u16 wz;
    u8 A, B, C, D, E, H, L;
    u8 A_alt, B_alt, C_alt, D_alt, E_alt, H_alt, L_alt, F_alt;
    u8 I, RR;
    u8 F;
    u8 iff_set;
    bool IFF1, IFF2;
    u8 IM;
    u8 int_vec;
    bool int_pending, nmi_pending;
    bool halted;
};

// Выделение глобального экземпляра, сопоставимого с extern в C++
struct CPUZ80 cpu;

// ---------------------------------------
// EXTERNAL PERIPHERAL CALLBACKS

extern u8 ReadByte(u16 addr);
extern void WriteByte(u16 addr, u8 val);
extern u8 InPort(u16 port);
extern void OutPort(u16 port, u8 val);

// Прототипы методов
void init(void);
int step(void);
void gen_nmi(void);
void gen_int(u8 data);

// ---------------------------------------
// BIT FLAG BITMASK HELPERS (F REGISTER)

#define CF_MASK (1u << 0)
#define NF_MASK (1u << 1)
#define PF_MASK (1u << 2)
#define XF_MASK (1u << 3)
#define HF_MASK (1u << 4)
#define YF_MASK (1u << 5)
#define ZF_MASK (1u << 6)
#define SF_MASK (1u << 7)

#define GET_SF() ((cpu.F & SF_MASK) != 0)
#define GET_ZF() ((cpu.F & ZF_MASK) != 0)
#define GET_YF() ((cpu.F & YF_MASK) != 0)
#define GET_HF() ((cpu.F & HF_MASK) != 0)
#define GET_XF() ((cpu.F & XF_MASK) != 0)
#define GET_PF() ((cpu.F & PF_MASK) != 0)
#define GET_NF() ((cpu.F & NF_MASK) != 0)
#define GET_CF() ((cpu.F & CF_MASK) != 0)

#define SET_FLAG_BIT(mask, cond) cpu.F = (cond) ? (cpu.F | (mask)) : (cpu.F & ~(mask))

// ---------------------------------------
// MEMORY / PROCESSOR STATE OPERATIONS

#define bit(n, val) (((val) >> (n)) & 1)
#define r8(a) ReadByte(a)
#define w8(a, v) WriteByte(a, v)

#define HI(a) ((a) >> 8)
#define LO(a) ((a) & 0xFF)

SI u16 r16(u16 a) _((r8(a + 1) << 8) | r8(a))
SI void w16(u16 a, u16 v) { w8(a, LO(v)); w8(a + 1, HI(v)); }

SI void psh(u16 v) { w16(cpu.SP -= 2, v); }
SI u16 pop(void) _(r16((cpu.SP += 2) - 2))

SI u8 p8(void) _(r8(cpu.PC++))
SI u16 p16(void) _(r16((cpu.PC += 2) - 2))

SI void set_bc(u16 v) { cpu.B = HI(v); cpu.C = LO(v); }
SI void set_hl(u16 v) { cpu.H = HI(v); cpu.L = LO(v); }
SI void set_de(u16 v) { cpu.D = HI(v); cpu.E = LO(v); }

SI u16 get_bc(void) _((cpu.B << 8) | cpu.C)
SI u16 get_hl(void) _((cpu.H << 8) | cpu.L)
SI u16 get_de(void) _((cpu.D << 8) | cpu.E)
SI u16 get_af(void) _((cpu.A << 8) | cpu.F)

// ---------------------------------------
// INSTRUCTION IMPLEMENTATIONS

SI void inc_r(void) { cpu.RR = (cpu.RR & 0x80) | ((cpu.RR + 1) & 0x7f); }
SI bv carry(int n, u16 a, u16 b, bv cy) _(bit(n, (a + b + cy) ^ a^ b))

SI bv parity(u8 x) {
    x ^= x >> 4; x ^= x >> 2; x ^= x >> 1;
    R(~x) & 1;
}

SI void jmp(u16 a) { cpu.wz = cpu.PC = a; }
SI void call(u16 dest) { psh(cpu.PC); jmp(dest); }

SI bv cjmp(bv c) { u16 t = p16(); if (c) { jmp(t); R 1; } cpu.wz = t; R 0; }
SI bv ccall(bv c) { u16 t = p16(); if (c) { call(t); R 1; } cpu.wz = t; R 0; }
SI void ret(void) { jmp(pop()); }
SI bv cret(bv c) { if (c) { ret(); R 1; } R 0; }
SI void jr(i8 disp) { cpu.wz = cpu.PC += disp; }
SI bv cjr(bv c) { if (c) { jr(p8()); R 1; } else { cpu.PC++; R 0; } }

SI void xyf1(u8 x) { SET_FLAG_BIT(XF_MASK, bit(3, x)); SET_FLAG_BIT(YF_MASK, bit(5, x)); }
SI void xyf2(u8 x) { SET_FLAG_BIT(XF_MASK, bit(3, x)); SET_FLAG_BIT(YF_MASK, bit(1, x)); }
SI void szf8(u8 x) { SET_FLAG_BIT(ZF_MASK, x == 0); SET_FLAG_BIT(SF_MASK, x >> 7); }
SI void szf16(u16 x) { SET_FLAG_BIT(ZF_MASK, x == 0); SET_FLAG_BIT(SF_MASK, x >> 15); }

SI u8 add8(u8 a, u8 b, bv cy) {
    u8 res = a + b + cy;
    SET_FLAG_BIT(HF_MASK, carry(4, a, b, cy));
    SET_FLAG_BIT(PF_MASK, carry(7, a, b, cy) != carry(8, a, b, cy));
    SET_FLAG_BIT(CF_MASK, carry(8, a, b, cy));
    SET_FLAG_BIT(NF_MASK, 0);
    szf8(res); xyf1(res);
    R res;
}

SI u8 sub8(u8 a, u8 b, bv cy) {
    u8 v = add8(a, ~b, !cy);
    SET_FLAG_BIT(HF_MASK, bit(4, (a - b - cy) ^ a ^ b));
    SET_FLAG_BIT(CF_MASK, bit(8, (a - b - cy) ^ a ^ b));
    SET_FLAG_BIT(NF_MASK, 1);
    R v;
}

SI u16 add16(u16 a, u16 b, bv cy) {
    u8 lo = add8((u8)a, (u8)b, cy);
    u16 res = (add8((u8)HI(a), (u8)HI(b), GET_CF()) << 8) | lo;
    SET_FLAG_BIT(ZF_MASK, res == 0); cpu.wz = a + 1; R res;
}

SI u16 sub16(u16 a, u16 b, bv cy) {
    u8 lo = sub8((u8)a, (u8)b, cy);
    u16 res = (sub8((u8)HI(a), (u8)HI(b), GET_CF()) << 8) | lo;
    SET_FLAG_BIT(ZF_MASK, res == 0); cpu.wz = a + 1; R res;
}

SI void addhl(u16 val) {
    bv nsf = GET_SF(), nzf = GET_ZF(), npf = GET_PF();
    set_hl(add16(get_hl(), val, 0));
    SET_FLAG_BIT(SF_MASK, nsf); SET_FLAG_BIT(ZF_MASK, nzf); SET_FLAG_BIT(PF_MASK, npf);
}

SI void addiz(u16* reg, u16 val) {
    bv nsf = GET_SF(), nzf = GET_ZF(), npf = GET_PF();
    *reg = add16(*reg, val, 0);
    SET_FLAG_BIT(SF_MASK, nsf); SET_FLAG_BIT(ZF_MASK, nzf); SET_FLAG_BIT(PF_MASK, npf);
}

SI void adchl(u16 v) { u16 q = add16(get_hl(), v, GET_CF()); szf16(q); set_hl(q); }
SI void sbchl(u16 v) { u16 q = sub16(get_hl(), v, GET_CF()); szf16(q); set_hl(q); }
SI u8 inc(u8 a) { bv ncf = GET_CF(); u8 q = add8(a, 1, 0); SET_FLAG_BIT(CF_MASK, ncf); R q; }
SI u8 dec(u8 a) { bv ncf = GET_CF(); u8 q = sub8(a, 1, 0); SET_FLAG_BIT(CF_MASK, ncf); R q; }

#define bit_op(name, op, halfcarry) \
  SI void name(u8 val) { \
    u8 res = cpu.A op val; \
    szf8(res); xyf1(res); \
    SET_FLAG_BIT(HF_MASK, halfcarry); \
    SET_FLAG_BIT(PF_MASK, parity(res)); \
    SET_FLAG_BIT(NF_MASK, 0); SET_FLAG_BIT(CF_MASK, 0); \
    cpu.A = res; \
  }

bit_op(land, &, 1)
bit_op(lor, | , 0)
bit_op(lxor, ^, 0)
#undef bit_op

SI void cmpa(u8 val) { sub8(cpu.A, val, 0); xyf1(val); }

#define op_cbh(name, ...) \
  SI u8 name(u8 val) { \
    __VA_ARGS__ \
    szf8(val); xyf1(val); \
    SET_FLAG_BIT(PF_MASK, parity(val)); \
    SET_FLAG_BIT(NF_MASK, 0); SET_FLAG_BIT(HF_MASK, 0); \
    R val; \
  }

op_cbh(rlc, bv old = val >> 7; val = (val << 1) | old; SET_FLAG_BIT(CF_MASK, old);)
op_cbh(rrc, bv old = val & 1; val = (val >> 1) | (old << 7); SET_FLAG_BIT(CF_MASK, old);)
op_cbh(rl, bv ncf = GET_CF(); SET_FLAG_BIT(CF_MASK, val >> 7); val = (val << 1) | ncf;)
op_cbh(rr, bv nc = GET_CF(); SET_FLAG_BIT(CF_MASK, val & 1); val = (val >> 1) | (nc << 7);)
op_cbh(sla, SET_FLAG_BIT(CF_MASK, val >> 7); val <<= 1;)
op_cbh(sll, SET_FLAG_BIT(CF_MASK, val >> 7); val <<= 1; val |= 1;)
op_cbh(sra, SET_FLAG_BIT(CF_MASK, val & 1); val = (val >> 1) | (val & 0x80);)
op_cbh(srl, SET_FLAG_BIT(CF_MASK, val & 1); val >>= 1;)

SI u8 bt(u8 val, u8 n) {
    u8 res = val & (1 << n);
    szf8(res); xyf1(val);
    SET_FLAG_BIT(HF_MASK, 1); SET_FLAG_BIT(PF_MASK, GET_ZF()); SET_FLAG_BIT(NF_MASK, 0); R res;
}

#define dbc(n) set_bc(get_bc() + (n))
#define dhl(n) set_hl(get_hl() + (n))
#define dde(n) set_de(get_de() + (n))

SI void ldi(void) {
    u8 val = r8(get_hl());
    w8(get_de(), val);
    dhl(1); dde(1); dbc(-1);
    xyf2(val + cpu.A);
    SET_FLAG_BIT(NF_MASK, 0); SET_FLAG_BIT(HF_MASK, 0);
    SET_FLAG_BIT(PF_MASK, get_bc() > 0);
}

SI void ldd(void) { ldi(); dhl(-2); dde(-2); }

SI void cpi(void) {
    bv ncf = GET_CF();
    u8 v = sub8(cpu.A, r8(get_hl()), 0);
    dhl(1); dbc(-1);
    xyf2(v - GET_HF());
    SET_FLAG_BIT(PF_MASK, get_bc() != 0);
    SET_FLAG_BIT(CF_MASK, ncf);
    cpu.wz += 1;
}

SI void cpd(void) { cpi(); dhl(-2); cpu.wz -= 2; }

SI void inr(u8* r_reg) {
    *r_reg = InPort(get_bc());
    szf8(*r_reg);
    SET_FLAG_BIT(PF_MASK, parity(*r_reg));
    SET_FLAG_BIT(NF_MASK, 0); SET_FLAG_BIT(HF_MASK, 0);
}

SI void adji(void) {
    dhl(1);
    SET_FLAG_BIT(ZF_MASK, --cpu.B == 0);
    SET_FLAG_BIT(NF_MASK, 1);
    cpu.wz = get_bc() + 1;
}

SI void ini(void) { w8(get_hl(), InPort(get_bc())); adji(); }
SI void outi(void) { OutPort(get_bc(), r8(get_hl())); adji(); }
SI void ind(void) { ini(); dhl(-2); cpu.wz = get_bc() - 2; }
SI void outd(void) { outi(); dhl(-2); cpu.wz = get_bc() - 2; }

SI void daa(void) {
    u8 bcd = 0;
    if ((cpu.A & 0x0F) > 0x09 || GET_HF()) bcd += 0x06;
    if (cpu.A > 0x99 || GET_CF()) bcd += 0x60, SET_FLAG_BIT(CF_MASK, 1);
    if (GET_NF()) {
        SET_FLAG_BIT(HF_MASK, GET_HF() && (cpu.A & 0x0F) < 0x06);
        bcd = -bcd;
    }
    else {
        SET_FLAG_BIT(HF_MASK, (cpu.A & 0x0F) > 0x09);
    }
    cpu.A += bcd;
    SET_FLAG_BIT(PF_MASK, parity(cpu.A));
    xyf1(cpu.A); szf8(cpu.A);
}

SI u16 dp(u16 b_val, i8 d_val) _(cpu.wz = b_val + d_val)

// ---------------------------------------
// EXECUTION DECODER PROTOTYPES

int exec(u8 opc);
int exec_cb(u8 opc);
int exec_cb2(u8 opc, u16 addr);
int exec_ed(u8 opc);
int exec_ind(u8 opc, u16* ir);

void init(void) {
    cpu.PC = cpu.IX = cpu.IY = cpu.wz = 0;
    cpu.SP = 0xFFFF;
    cpu.A = 0xFF; cpu.F = 0xFF;
    cpu.B = cpu.C = cpu.D = cpu.E = cpu.H = cpu.L = 0;
    cpu.A_alt = cpu.B_alt = cpu.C_alt = cpu.D_alt = cpu.E_alt = cpu.H_alt = cpu.L_alt = cpu.F_alt = 0;
    cpu.I = cpu.RR = 0;
    cpu.iff_set = 0;
    cpu.IM = 0;
    cpu.IFF1 = cpu.IFF2 = 0;
    cpu.halted = 0;
    cpu.int_pending = cpu.nmi_pending = 0;
    cpu.int_vec = 0;
}

// ---------------------------------------
// T-STATE (CYCLE) TABLES
//
// exec()/exec_ind()/exec_ed() below are built out of H(...) groups that
// share ONE trailing "R n;" placed after the group. Because H() expands
// to "case n: ...; break;", every one of those cases exits the switch
// BEFORE reaching that trailing R -- it is dead code. Rather than
// rewrite every group (very easy to get wrong by hand), each dispatch
// function below looks its opcode's correct cost up in one of these
// tables *before* running the switch, and returns that looked-up value
// at the very end (replacing the function's old always-taken "R 4;"
// fallback). Cases that already return their own value inline
// (conditionals, IN/OUT, block instructions) are untouched and simply
// return before ever reaching that fallback.
//
// Every table entry is the COMPLETE T-state cost of the instruction,
// prefix byte(s) included. A 0 in dd_cycles/ed_cycles marks an opcode
// that's handled by a dynamic/inline path instead (see exec_ind's
// "default" case and exec_cb2's DDCB dispatch), so the exact value
// there is irrelevant.

static const u16 main_cycles[256] = {
    4,10,7,6,4,4,7,4,   4,11,7,6,4,4,7,4,
    8,10,7,6,4,4,7,4,   12,11,7,6,4,4,7,4,
    7,10,16,6,4,4,7,4,  7,11,16,6,4,4,7,4,
    7,10,13,6,11,11,10,4, 7,11,13,6,4,4,7,4,
    4,4,4,4,4,4,7,4,    4,4,4,4,4,4,7,4,
    4,4,4,4,4,4,7,4,    4,4,4,4,4,4,7,4,
    4,4,4,4,4,4,7,4,    4,4,4,4,4,4,7,4,
    7,7,7,7,7,7,4,7,    4,4,4,4,4,4,7,4,
    4,4,4,4,4,4,7,4,    4,4,4,4,4,4,7,4,
    4,4,4,4,4,4,7,4,    4,4,4,4,4,4,7,4,
    4,4,4,4,4,4,7,4,    4,4,4,4,4,4,7,4,
    4,4,4,4,4,4,7,4,    4,4,4,4,4,4,7,4,
    5,10,10,10,10,11,7,11, 5,10,10,0,10,17,7,11,
    5,10,10,11,10,11,7,11, 5,4,10,11,10,0,7,11,
    5,10,10,19,10,11,7,11, 5,4,10,4,10,0,7,11,
    5,10,10,4,10,11,7,11,  5,6,10,4,10,0,7,11,
};

static const u16 dd_cycles[256] = {
    [0x09]=15, [0x19]=15, [0x29]=15, [0x39]=15,
    [0x21]=14, [0x22]=20, [0x2A]=20,
    [0x23]=10, [0x2B]=10,
    [0x24]=8, [0x25]=8, [0x2C]=8, [0x2D]=8,
    [0x26]=11, [0x2E]=11,
    [0x34]=23, [0x35]=23, [0x36]=19,
    [0x44]=8, [0x45]=8, [0x4C]=8, [0x4D]=8,
    [0x54]=8, [0x55]=8, [0x5C]=8, [0x5D]=8,
    [0x60]=8, [0x61]=8, [0x62]=8, [0x63]=8, [0x64]=8, [0x65]=8, [0x67]=8,
    [0x68]=8, [0x69]=8, [0x6A]=8, [0x6B]=8, [0x6C]=8, [0x6D]=8, [0x6F]=8,
    [0x7C]=8, [0x7D]=8,
    [0x46]=19, [0x4E]=19, [0x56]=19, [0x5E]=19, [0x66]=19, [0x6E]=19, [0x7E]=19,
    [0x70]=19, [0x71]=19, [0x72]=19, [0x73]=19, [0x74]=19, [0x75]=19, [0x77]=19,
    [0x84]=8, [0x85]=8, [0x8C]=8, [0x8D]=8,
    [0x86]=19, [0x8E]=19, [0x96]=19, [0x9E]=19,
    [0x94]=8, [0x95]=8, [0x9C]=8, [0x9D]=8,
    [0xA4]=8, [0xA5]=8, [0xA6]=19,
    [0xAC]=8, [0xAD]=8, [0xAE]=19,
    [0xB4]=8, [0xB5]=8, [0xB6]=19,
    [0xBC]=8, [0xBD]=8, [0xBE]=19,
    [0xE1]=14, [0xE5]=15, [0xE9]=8, [0xE3]=23, [0xF9]=10,
};

static const u16 ed_cycles[256] = {
    [0x40]=12, [0x48]=12, [0x50]=12, [0x58]=12, [0x60]=12, [0x68]=12, [0x70]=12, [0x78]=12,
    [0x41]=12, [0x49]=12, [0x51]=12, [0x59]=12, [0x61]=12, [0x69]=12, [0x71]=12, [0x79]=12,
    [0x42]=15, [0x52]=15, [0x62]=15, [0x72]=15,
    [0x4A]=15, [0x5A]=15, [0x6A]=15, [0x7A]=15,
    [0x43]=20, [0x53]=20, [0x63]=20, [0x73]=20,
    [0x4B]=20, [0x5B]=20, [0x6B]=20, [0x7B]=20,
    [0x44]=8, [0x4C]=8, [0x54]=8, [0x5C]=8, [0x64]=8, [0x6C]=8, [0x74]=8, [0x7C]=8,
    [0x45]=14, [0x55]=14, [0x65]=14, [0x75]=14, [0x5D]=14, [0x6D]=14, [0x7D]=14, [0x4D]=14,
    [0x46]=8, [0x66]=8, [0x56]=8, [0x76]=8, [0x5E]=8, [0x7E]=8,
    [0x47]=9, [0x4F]=9, [0x57]=9, [0x5F]=9,
    [0x67]=18, [0x6F]=18,
    [0xA0]=16, [0xA8]=16, [0xA1]=16, [0xA9]=16,
    [0xB0]=16, [0xB8]=16, [0xB1]=16, [0xB9]=16,
    [0xA2]=16, [0xAA]=16, [0xA3]=16, [0xAB]=16,
    [0xB2]=16, [0xBA]=16, [0xB3]=16, [0xBB]=16,
};

int step(void) {
    int cycles = 0;
    if (cpu.halted) {
        cycles += exec(0x00);
    }
    else {
        cycles += exec(p8());
    }

    if (cpu.iff_set) {
        cpu.iff_set = 0;
        cpu.IFF1 = cpu.IFF2 = 1;
        R cycles;
    }

    if (cpu.nmi_pending) {
        cpu.nmi_pending = cpu.halted = cpu.IFF1 = 0;
        inc_r(); call(0x66);
        R cycles + 11;
    }

    if (cpu.int_pending && cpu.IFF1) {
        cpu.int_pending = cpu.halted = 0;
        cpu.IFF1 = cpu.IFF2 = 0;
        inc_r();
        switch (cpu.IM) {
        case 0:
            cycles += exec(cpu.int_vec);
            R cycles + 2;
        case 1:
            call(0x38); R cycles + 13;
        case 2:

            call(r16((cpu.I << 8) | cpu.int_vec)); R cycles + 19;
        }
    }
    R cycles;
}

void gen_nmi(void) { cpu.nmi_pending = 1; }
void gen_int(u8 data) { cpu.int_pending = 1; cpu.int_vec = data; }

// ---------------------------------------
// DECODER BLOCKS

#define H(n, ...) case n: __VA_ARGS__; break;

SI void awz1(u16 val) { cpu.wz = (cpu.A << 8) | LO(val + 1); }

int exec(u8 opc) {
    u16 t1; bv t2; u8 t3;
    u16 cyc = main_cycles[opc];
    inc_r();
    switch (opc) {
    H(0x47, cpu.B=cpu.A) H(0x40, cpu.B=cpu.B) H(0x41, cpu.B=cpu.C) H(0x42, cpu.B=cpu.D) H(0x43, cpu.B=cpu.E) H(0x44, cpu.B=cpu.H) H(0x45, cpu.B=cpu.L)
    H(0x57, cpu.D=cpu.A) H(0x50, cpu.D=cpu.B) H(0x51, cpu.D=cpu.C) H(0x52, cpu.D=cpu.D) H(0x53, cpu.D=cpu.E) H(0x54, cpu.D=cpu.H) H(0x55, cpu.D=cpu.L)
    H(0x67, cpu.H=cpu.A) H(0x60, cpu.H=cpu.B) H(0x61, cpu.H=cpu.C) H(0x62, cpu.H=cpu.D) H(0x63, cpu.H=cpu.E) H(0x64, cpu.H=cpu.H) H(0x65, cpu.H=cpu.L)
    H(0x4F, cpu.C=cpu.A) H(0x48, cpu.C=cpu.B) H(0x49, cpu.C=cpu.C) H(0x4A, cpu.C=cpu.D) H(0x4B, cpu.C=cpu.E) H(0x4C, cpu.C=cpu.H) H(0x4D, cpu.C=cpu.L)
    H(0x5F, cpu.E=cpu.A) H(0x58, cpu.E=cpu.B) H(0x59, cpu.E=cpu.C) H(0x5A, cpu.E=cpu.D) H(0x5B, cpu.E=cpu.E) H(0x5C, cpu.E=cpu.H) H(0x5D, cpu.E=cpu.L)
    H(0x6F, cpu.L=cpu.A) H(0x68, cpu.L=cpu.B) H(0x69, cpu.L=cpu.C) H(0x6A, cpu.L=cpu.D) H(0x6B, cpu.L=cpu.E) H(0x6C, cpu.L=cpu.H) H(0x6D, cpu.L=cpu.L)
    H(0x7F, cpu.A=cpu.A) H(0x78, cpu.A=cpu.B) H(0x79, cpu.A=cpu.C) H(0x7A, cpu.A=cpu.D) H(0x7B, cpu.A=cpu.E) H(0x7C, cpu.A=cpu.H) H(0x7D, cpu.A=cpu.L)
        R 4;
    
    H(0x0E, cpu.C=p8()) H(0x06, cpu.B=p8()) H(0x1E, cpu.E=p8()) H(0x16, cpu.D=p8())
    H(0x2E, cpu.L=p8()) H(0x26, cpu.H=p8()) H(0x3E, cpu.A=p8()) 
        R 7;
    
    H(0x36, w8(get_hl(),p8())) R 10;
    
    H(0x6E, cpu.L=r8(get_hl())) H(0x7E, cpu.A=r8(get_hl())) H(0x46, cpu.B=r8(get_hl()))
    H(0x4E, cpu.C=r8(get_hl())) H(0x56, cpu.D=r8(get_hl())) H(0x5E, cpu.E=r8(get_hl())) H(0x66, cpu.H=r8(get_hl()))
        R 7;
    
    H(0x77, w8(get_hl(),cpu.A)) H(0x70, w8(get_hl(),cpu.B)) H(0x71, w8(get_hl(),cpu.C))
    H(0x72, w8(get_hl(),cpu.D)) H(0x73, w8(get_hl(),cpu.E)) H(0x74, w8(get_hl(),cpu.H)) H(0x75, w8(get_hl(),cpu.L))
        R 7;
    
    H(0x02, w8(get_bc(),cpu.A);awz1(get_bc())) H(0x12, w8(get_de(),cpu.A);awz1(get_de()))
    H(0x0A, cpu.A=r8(get_bc());cpu.wz=get_bc()+1) H(0x1A, cpu.A=r8(get_de());cpu.wz=get_de()+1)
        R 7;
        
    H(0x32, t1=p16();w8(t1,cpu.A);awz1(t1)) H(0x3A, cpu.wz=p16()+1;cpu.A=r8(cpu.wz-1))
        R 13;
    
    H(0x01, set_bc(p16())) H(0x11, set_de(p16())) H(0x21, set_hl(p16())) H(0x31, cpu.SP=p16())
        R 10;
    
    H(0x2A, set_hl(r16(t1=p16()));cpu.wz=t1+1) H(0x22, w16(t1=p16(),get_hl());cpu.wz=t1+1)
        R 16;
    
    H(0xF9, cpu.SP=get_hl()) R 6;
    H(0xEB, t1=get_de();set_de(get_hl());set_hl(t1)) R 4;
    H(0xE3, t1=r16(cpu.SP);w16(cpu.SP,get_hl());set_hl(cpu.wz=t1)) R 19;
  
    #define op(opc, src) case opc: cpu.A = add8(cpu.A, src, 0); break;
    op(0x87, cpu.A) op(0x80, cpu.B) op(0x81, cpu.C) op(0x82, cpu.D) op(0x83, cpu.E) op(0x84, cpu.H) op(0x85, cpu.L)
    #undef op
    #define op(opc, src) case opc: cpu.A = add8(cpu.A, src, GET_CF()); break;
    op(0x8F, cpu.A) op(0x88, cpu.B) op(0x89, cpu.C) op(0x8A, cpu.D) op(0x8B, cpu.E) op(0x8C, cpu.H) op(0x8D, cpu.L)
    #undef op
    #define op(opc, src) case opc: cpu.A = sub8(cpu.A, src, 0); break;
    op(0x97, cpu.A) op(0x90, cpu.B) op(0x91, cpu.C) op(0x92, cpu.D) op(0x93, cpu.E) op(0x94, cpu.H) op(0x95, cpu.L)
    #undef op
    #define op(opc, src) case opc: cpu.A = sub8(cpu.A, src, GET_CF()); break;
    op(0x9F, cpu.A) op(0x98, cpu.B) op(0x99, cpu.C) op(0x9A, cpu.D) op(0x9B, cpu.E) op(0x9C, cpu.H) op(0x9D, cpu.L)
    #undef op
    #define op(opA, opB, opC, opD, opE, opH, opL, name) \
        case opA: name(cpu.A); break; case opB: name(cpu.B); break; case opC: name(cpu.C); break; \
        case opD: name(cpu.D); break; case opE: name(cpu.E); break; case opH: name(cpu.H); break; \
        case opL: name(cpu.L); break;
    op(0xA7, 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, land)
    op(0xB7, 0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, lor)
    op(0xAF, 0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, lxor)
    op(0xBF, 0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, cmpa)
    #undef op
        R 4;

    case 0x86: cpu.A = add8(cpu.A, r8(get_hl()), 0); R 7;
    case 0x8E: cpu.A = add8(cpu.A, r8(get_hl()), GET_CF()); R 7;
    case 0x96: cpu.A = sub8(cpu.A, r8(get_hl()), 0); R 7;
    case 0x9E: cpu.A = sub8(cpu.A, r8(get_hl()), GET_CF()); R 7;
    case 0xA6: land(r8(get_hl())); R 7;
    case 0xB6: lor(r8(get_hl())); R 7;
    case 0xAE: lxor(r8(get_hl())); R 7;
    case 0xBE: cmpa(r8(get_hl())); R 7;

    case 0xC6: cpu.A = add8(cpu.A, p8(), 0); R 7;
    case 0xCE: cpu.A = add8(cpu.A, p8(), GET_CF()); R 7;
    case 0xD6: cpu.A = sub8(cpu.A, p8(), 0); R 7;
    case 0xDE: cpu.A = sub8(cpu.A, p8(), GET_CF()); R 7;
    case 0xE6: land(p8()); R 7;
    case 0xF6: lor(p8()); R 7;
    case 0xEE: lxor(p8()); R 7;
    case 0xFE: cmpa(p8()); R 7;
  
    H(0x09, addhl(get_bc())) H(0x19, addhl(get_de())) H(0x29, addhl(get_hl())) H(0x39, addhl(cpu.SP))
        R 11;
  
    H(0xF3, cpu.IFF1=cpu.IFF2=0) H(0xFB, cpu.iff_set=1) H(0x00, ) H(0x76, cpu.halted=1)
        R 4;
  
    H(0x3C, cpu.A=inc(cpu.A)) H(0x04, cpu.B=inc(cpu.B)) H(0x0C, cpu.C=inc(cpu.C)) H(0x14, cpu.D=inc(cpu.D))
    H(0x1C, cpu.E=inc(cpu.E)) H(0x24, cpu.H=inc(cpu.H)) H(0x2C, cpu.L=inc(cpu.L))
    H(0x3D, cpu.A=dec(cpu.A)) H(0x05, cpu.B=dec(cpu.B)) H(0x0D, cpu.C=dec(cpu.C)) H(0x15, cpu.D=dec(cpu.D))
    H(0x1D, cpu.E=dec(cpu.E)) H(0x25, cpu.H=dec(cpu.H)) H(0x2D, cpu.L=dec(cpu.L))
        R 4;
  
    H(0x34, w8(get_hl(),inc(r8(get_hl())))) H(0x35, w8(get_hl(),dec(r8(get_hl()))))
        R 11;
  
    H(0x03, dbc(1)) H(0x13, dde(1)) H(0x23, dhl(1)) H(0x33, ++cpu.SP)
    H(0x0B, dbc(-1)) H(0x1B, dde(-1)) H(0x2B, dhl(-1)) H(0x3B, --cpu.SP)
        R 6;
  
    H(0x27, daa())
    H(0x2F, cpu.A=~cpu.A; SET_FLAG_BIT(NF_MASK, 1); SET_FLAG_BIT(HF_MASK, 1); xyf1(cpu.A);)
    H(0x37, SET_FLAG_BIT(CF_MASK, 1); SET_FLAG_BIT(NF_MASK, 0); SET_FLAG_BIT(HF_MASK, 0); xyf1(cpu.A);)
    H(0x3F, SET_FLAG_BIT(HF_MASK, GET_CF()); SET_FLAG_BIT(CF_MASK, !GET_CF()); SET_FLAG_BIT(NF_MASK, 0); xyf1(cpu.A);)
        R 4;
  
    H(0x07, t2=cpu.A>>7; cpu.A=(cpu.A<<1)|t2; SET_FLAG_BIT(CF_MASK, t2); SET_FLAG_BIT(NF_MASK,0); SET_FLAG_BIT(HF_MASK,0); xyf1(cpu.A);)
    H(0x17, t2=GET_CF(); SET_FLAG_BIT(CF_MASK, cpu.A>>7); cpu.A=(cpu.A<<1)|t2; SET_FLAG_BIT(NF_MASK,0); SET_FLAG_BIT(HF_MASK,0); xyf1(cpu.A);)
    H(0x0F, t2=cpu.A&1; cpu.A=(cpu.A>>1)|(t2<<7); SET_FLAG_BIT(CF_MASK, t2); SET_FLAG_BIT(NF_MASK,0); SET_FLAG_BIT(HF_MASK,0); xyf1(cpu.A);)
    H(0x1F, t2=GET_CF(); SET_FLAG_BIT(CF_MASK, cpu.A&1); cpu.A=(cpu.A>>1)|(t2<<7); SET_FLAG_BIT(NF_MASK,0); SET_FLAG_BIT(HF_MASK,0); xyf1(cpu.A);)
        R 4;
  
    H(0xC3, jmp(p16())) R 10;
  
    H(0xC2, cjmp(!GET_ZF())) H(0xCA, cjmp(GET_ZF()))
    H(0xD2, cjmp(!GET_CF())) H(0xDA, cjmp(GET_CF()))
    H(0xE2, cjmp(!GET_PF())) H(0xEA, cjmp(GET_PF()))
    H(0xF2, cjmp(!GET_SF())) H(0xFA, cjmp(GET_SF()))
        R 10;
  
    H(0x10, R cjr(--cpu.B) ? 13 : 8)
    H(0x18, cpu.PC+=(i8)p8(); R 12)
  
    H(0x20, R cjr(!GET_ZF()) ? 12 : 7) H(0x28, R cjr(GET_ZF()) ? 12 : 7)
    H(0x30, R cjr(!GET_CF()) ? 12 : 7) H(0x38, R cjr(GET_CF()) ? 12 : 7)
  
    H(0xE9, cpu.PC=get_hl()) R 4;
    H(0xCD, call(p16())) R 17;
  
    H(0xC4, R ccall(!GET_ZF()) ? 17 : 10) H(0xCC, R ccall(GET_ZF()) ? 17 : 10)
    H(0xD4, R ccall(!GET_CF()) ? 17 : 10) H(0xDC, R ccall(GET_CF()) ? 17 : 10)
    H(0xE4, R ccall(!GET_PF()) ? 17 : 10) H(0xEC, R ccall(GET_PF()) ? 17 : 10)
    H(0xF4, R ccall(!GET_SF()) ? 17 : 10) H(0xFC, R ccall(GET_SF()) ? 17 : 10)
  
    H(0xC9, ret()) R 10;
  
    H(0xC0, R cret(!GET_ZF()) ? 11 : 5) H(0xC8, R cret(GET_ZF()) ? 11 : 5)
    H(0xD0, R cret(!GET_CF()) ? 11 : 5) H(0xD8, R cret(GET_CF()) ? 11 : 5)
    H(0xE0, R cret(!GET_PF()) ? 11 : 5) H(0xE8, R cret(GET_PF()) ? 11 : 5)
    H(0xF0, R cret(!GET_SF()) ? 11 : 5) H(0xF8, R cret(GET_SF()) ? 11 : 5)
  
    H(0xC7, call(0x00)) H(0xCF, call(0x08)) H(0xD7, call(0x10)) H(0xDF, call(0x18))
    H(0xE7, call(0x20)) H(0xEF, call(0x28)) H(0xF7, call(0x30)) H(0xFF, call(0x38))
        R 11;
  
    H(0xC5, psh(get_bc())) H(0xD5, psh(get_de())) H(0xE5, psh(get_hl())) H(0xF5, psh(get_af()))
        R 11;
  
    H(0xC1, set_bc(pop())) H(0xD1, set_de(pop())) H(0xE1, set_hl(pop())) R 10;
    H(0xF1, t1=pop(); cpu.A=t1>>8; cpu.F=t1&0xFF;) R 10;
  
    H(0xDB, {
        t3 = p8(); // Сначала читаем immediate-байт n из памяти
        u16 full_port_addr = (cpu.A << 8) | t3; // Склеиваем порт: верхний байт = A, нижний = n
        cpu.A = InPort(full_port_addr);
        cpu.wz = (cpu.A << 8) | (t3 + 1);
        R 11;
    })
    H(0xD3, {
        t3 = p8(); // Читаем байт порта n из памяти
        u16 full_port_addr = (cpu.A << 8) | t3; // Верхний байт = A, нижний = n
        OutPort(full_port_addr, cpu.A);
        cpu.wz = ((t3 + 1) & 0xFF) | (cpu.A << 8);
        R 11;
        })

    case 0x08: {
        u8 na = cpu.A, nf = cpu.F;
        cpu.A = cpu.A_alt; cpu.F = cpu.F_alt;
        cpu.A_alt = na; cpu.F_alt = nf;
        R 4;
    }
    case 0xD9: {
        u8 nb = cpu.B, nc = cpu.C, nd = cpu.D, ne = cpu.E, nh = cpu.H, nl = cpu.L;
        cpu.B = cpu.B_alt; cpu.C = cpu.C_alt; cpu.D = cpu.D_alt; cpu.E = cpu.E_alt; cpu.H = cpu.H_alt; cpu.L = cpu.L_alt;
        cpu.B_alt = nb; cpu.C_alt = nc; cpu.D_alt = nd; cpu.E_alt = ne; cpu.H_alt = nh; cpu.L_alt = nl;
        R 4;
    }
  
    H(0xCB, R exec_cb(p8())) H(0xDD, R exec_ind(p8(), &cpu.IX))
    H(0xED, R exec_ed(p8())) H(0xFD, R exec_ind(p8(), &cpu.IY))
  
    default: 
        fprintf(stderr, "Unknown opcode: 0x%02X\n", opc);
        R cyc;
    }
    R cyc;
}

int exec_ind(u8 opc, u16 * ir) {
    u16 t1; u16 cyc = dd_cycles[opc]; inc_r();
    #define IHI HI(*ir)
    #define ILO LO(*ir)
    #define IDP dp(*ir, p8())
  
    switch (opc) {
    H(0xE1, *ir = pop(); R 14) H(0xE5, psh(*ir); R 15) H(0xE9, jmp(*ir); R 8) H(0xF9, cpu.SP=*ir; R 10)
    H(0xE3, t1=r16(cpu.SP); w16(cpu.SP,*ir); cpu.wz=*ir=t1; R 23)
  
    H(0x09, addiz(ir, get_bc())) H(0x19, addiz(ir, get_de()))
    H(0x29, addiz(ir, *ir)) H(0x39, addiz(ir, cpu.SP))
        R 15;
  
    H(0x84, cpu.A = add8(cpu.A, IHI, 0)) H(0x85, cpu.A = add8(cpu.A, ILO, 0))
    H(0x8C, cpu.A = add8(cpu.A, IHI, GET_CF())) H(0x8D, cpu.A = add8(cpu.A, ILO, GET_CF()))
    H(0x94, cpu.A = sub8(cpu.A, IHI, 0)) H(0x95, cpu.A = sub8(cpu.A, ILO, 0))
    H(0x9C, cpu.A = sub8(cpu.A, IHI, GET_CF())) H(0x9D, cpu.A = sub8(cpu.A, ILO, GET_CF()))
    #define op3(opA, opB, opC, f) H(opB, f(IHI)) H(opC, f(ILO))
    op3(0xA6, 0xA4, 0xA5, land) op3(0xAE, 0xAC, 0xAD, lxor)
    op3(0xB6, 0xB4, 0xB5, lor) op3(0xBE, 0xBC, 0xBD, cmpa)
    #undef op3
        R 8;
  
    H(0x86, cpu.A = add8(cpu.A, r8(IDP), 0)) H(0x8E, cpu.A = add8(cpu.A, r8(IDP), GET_CF()))
    H(0x96, cpu.A = sub8(cpu.A, r8(IDP), 0)) H(0x9E, cpu.A = sub8(cpu.A, r8(IDP), GET_CF()))
    case 0xA6: land(r8(IDP)); R 19;
    case 0xAE: lxor(r8(IDP)); R 19;
    case 0xB6: lor(r8(IDP)); R 19;
    case 0xBE: cmpa(r8(IDP)); R 19;
  
    H(0x23, ++*ir) H(0x2B, --*ir) R 10;
  
    H(0x34, t1=IDP; w8(t1,inc(r8(t1)))) H(0x35, t1=IDP; w8(t1,dec(r8(t1))))
        R 23;
  
    H(0x24, *ir=ILO|(inc(IHI)<<8)) H(0x25, *ir=ILO|(dec(IHI)<<8))
    H(0x2C, *ir=(IHI<<8)|inc(ILO)) H(0x2D, *ir=(IHI<<8)|dec(ILO))
        R 8;
  
    H(0x2A, *ir=r16(p16())) H(0x22, w16(p16(),*ir)) R 20;
    H(0x21, *ir=p16()) R 14;
    H(0x36, t1=IDP; w8(t1,p8())) R 19;
  
    H(0x70, w8(IDP,cpu.B)) H(0x71, w8(IDP,cpu.C)) H(0x72, w8(IDP,cpu.D))
    H(0x73, w8(IDP,cpu.E)) H(0x74, w8(IDP,cpu.H)) H(0x75, w8(IDP,cpu.L))
    H(0x77, w8(IDP,cpu.A))
        R 19;
  
    H(0x46, cpu.B = r8(IDP)) H(0x4E, cpu.C = r8(IDP)) H(0x56, cpu.D = r8(IDP))
    H(0x5E, cpu.E = r8(IDP)) H(0x66, cpu.H = r8(IDP)) H(0x6E, cpu.L = r8(IDP))
    H(0x7E, cpu.A = r8(IDP))
        R 19;
    
    #define op2(ob, oc, od, oe, oa, var) \
        H(ob, cpu.B = var) H(oc, cpu.C = var) H(od, cpu.D = var) H(oe, cpu.E = var) H(oa, cpu.A = var)
    op2(0x44, 0x4C, 0x54, 0x5C, 0x7C, IHI)
    op2(0x45, 0x4D, 0x55, 0x5D, 0x7D, ILO)
    #undef op2
        R 8;
  
    H(0x67, *ir=ILO|(cpu.A<<8)) H(0x60, *ir=ILO|(cpu.B<<8)) H(0x61, *ir=ILO|(cpu.C<<8))
    H(0x62, *ir=ILO|(cpu.D<<8)) H(0x63, *ir=ILO|(cpu.E<<8)) H(0x26, *ir=ILO|(p8()<<8))
    H(0x64, ) H(0x65, *ir=(ILO<<8)|ILO)
    H(0x6F, *ir=(IHI<<8)|cpu.A) H(0x68, *ir=(IHI<<8)|cpu.B) H(0x69, *ir=(IHI<<8)|cpu.C)
    H(0x6A, *ir=(IHI<<8)|cpu.D) H(0x6B, *ir=(IHI<<8)|cpu.E) H(0x2E, *ir=(IHI<<8)|p8())
    H(0x6D, ) H(0x6C, *ir=(IHI<<8)|IHI)
        R 8;
  
    H(0xCB, t1=IDP; R exec_cb2(p8(),t1))
  
    default:
        cpu.RR = (cpu.RR & 0x80) | ((cpu.RR - 1) & 0x7f);
        R 4 + exec(opc);
    }
    #undef IDP
    #undef ILO
    #undef IHI
    R cyc;
}

int exec_cb(u8 opc) {
    inc_r();
    u8 dk = (opc >> 6) & 0b11; u8 da = (opc >> 3) & 0b111; u8 dr = opc & 0b111; 
    u8 hlr = 0; u8* reg = 0;
  
    switch (dr) {
    H(0,reg=&cpu.B) H(1,reg=&cpu.C) H(2,reg=&cpu.D) H(3,reg=&cpu.E) H(4,reg=&cpu.H)
    H(5,reg=&cpu.L) H(6, hlr=r8(get_hl());reg=&hlr) H(7,reg=&cpu.A)
    }
  
    switch (dk) {
    case 0:
        switch (da) {
        #define op(n,f) case n: *reg = f(*reg); break;
        op(0, rlc) op(1, rrc) op(2, rl) op(3, rr)
        op(4, sla) op(5, sra) op(6, sll) op(7, srl)
        #undef op
        }
        break;
    case 1:
        bt(*reg, da); if (dr == 6) xyf1(HI(cpu.wz));
        break;
    H(2, *reg&=~(1<<da)) H(3, *reg|=1<<da)
    }
  
    if (reg == &hlr) { w8(get_hl(), hlr); R (dk == 1) ? 12 : 15; }
    R 8;
}

int exec_cb2(u8 opc, u16 addr) {
    u8 val = r8(addr); u8 res = 0;
    u8 dk = (opc >> 6) & 0b11; u8 da = (opc >> 3) & 0b111; u8 dr = opc & 0b111; 
  
    switch (dk) {
    case 0:
        switch (da) {
        #define op(n,f) case n: res = f(val); break;
        op(0, rlc) op(1, rrc) op(2, rl) op(3, rr)
        op(4, sla) op(5, sra) op(6, sll) op(7, srl)
        #undef op
        }
        break;
    case 1:
        res = bt(val, da); xyf1(HI(addr));
        break;
    H(2, res=val&~(1<<da)) H(3, res=val|(1<<da))
    default: fprintf(stderr, "Invalid IX/IY CB-prefixed opcode: %02X\n", opc);
    }
  
    if (dk != 1 && dr != 6)
        switch (dr) {
        H(0, cpu.B=res) H(1, cpu.C=res) H(2, cpu.D=res) H(3, cpu.E=res)
        H(4, cpu.H=res) H(5, cpu.L=res) H(6, w8(get_hl(), res)) H(7, cpu.A=res)
        }
    if (dk != 1) w8(addr, res);
    R (dk == 1) ? 20 : 23;
}

SI void rot_ep(void) {
    SET_FLAG_BIT(NF_MASK, 0); SET_FLAG_BIT(HF_MASK, 0);
    xyf1(cpu.A); szf8(cpu.A);
    SET_FLAG_BIT(PF_MASK, parity(cpu.A));
    cpu.wz = get_hl() + 1;
}

int exec_ed(u8 opc) {
    u8 t1; u16 t2; u16 cyc = ed_cycles[opc]; inc_r();
    switch (opc) {
    H(0x47, cpu.I=cpu.A) H(0x4F, cpu.RR=cpu.A)
    H(0x57, cpu.A=cpu.I; szf8(cpu.A); SET_FLAG_BIT(HF_MASK,0); SET_FLAG_BIT(NF_MASK,0); SET_FLAG_BIT(PF_MASK,cpu.IFF2);)
    H(0x5F, cpu.A=cpu.RR; szf8(cpu.A); SET_FLAG_BIT(HF_MASK,0); SET_FLAG_BIT(NF_MASK,0); SET_FLAG_BIT(PF_MASK,cpu.IFF2);)
        R 9;
  
    case 0x45: case 0x55: case 0x65: case 0x75:
    case 0x5D: case 0x6D: case 0x7D:
        cpu.IFF1 = cpu.IFF2; ret(); R 14;
    H(0x4D, ret()) R 14;
  
    case 0xA0: ldi(); R 16;
    case 0xA8: ldd(); R 16;
    case 0xA1: cpi(); R 16;
    case 0xA9: cpd(); R 16;
  
    case 0xB0: ldi(); if(get_bc()) { cpu.wz=--cpu.PC; --cpu.PC; R 21; } R 16;
    case 0xB8: ldd(); if(get_bc()) { cpu.wz=--cpu.PC; --cpu.PC; R 21; } R 16;
    case 0xB1: cpi(); if(get_bc()&&!GET_ZF()) { cpu.wz=--cpu.PC; --cpu.PC; R 21; } else { ++cpu.wz; R 16; }
    case 0xB9: cpd(); if(get_bc()&&!GET_ZF()) { cpu.PC-=2; R 21; } else { ++cpu.wz; R 16; }
  
    H(0x40, inr(&cpu.B)) H(0x48, inr(&cpu.C)) H(0x50, inr(&cpu.D)) H(0x58, inr(&cpu.E))
    H(0x60, inr(&cpu.H)) H(0x68, inr(&cpu.L)) H(0x70, inr(&t1)) H(0x78, inr(&cpu.A); cpu.wz=get_bc()+1)
    H(0x41, OutPort(get_bc(), cpu.B)) H(0x49, OutPort(get_bc(), cpu.C)) H(0x51, OutPort(get_bc(), cpu.D))
    H(0x59, OutPort(get_bc(), cpu.E)) H(0x61, OutPort(get_bc(), cpu.H)) H(0x69, OutPort(get_bc(), cpu.L))
    H(0x71, OutPort(get_bc(), 0)) H(0x79, OutPort(get_bc(),cpu.A); cpu.wz=get_bc()+1)
        R 12;
  
    case 0xA2: ini(); R 16;
    case 0xAA: ind(); R 16;
    case 0xA3: outi(); R 16;
    case 0xAB: outd(); R 16;
  
    case 0xB2: ini(); if(cpu.B) { cpu.PC-=2; R 21; } R 16;
    case 0xBA: ind(); if(cpu.B) { cpu.PC-=2; R 21; } R 16;
    case 0xB3: outi(); if(cpu.B) { cpu.PC-=2; R 21; } R 16;
    case 0xBB: outd(); if(cpu.B) { cpu.PC-=2; R 21; } R 16;
  
    H(0x42, sbchl(get_bc())) H(0x52, sbchl(get_de())) H(0x62, sbchl(get_hl())) H(0x72, sbchl(cpu.SP))
    H(0x4A, adchl(get_bc())) H(0x5A, adchl(get_de())) H(0x6A, adchl(get_hl())) H(0x7A, adchl(cpu.SP))
        R 15;
  
    H(0x43, w16(t2=p16(),get_bc());cpu.wz=t2+1) H(0x53, w16(t2=p16(),get_de());cpu.wz=t2+1)
    H(0x63, w16(t2=p16(),get_hl());cpu.wz=t2+1) H(0x73, w16(t2=p16(),cpu.SP);cpu.wz=t2+1)
    H(0x4B, set_bc(r16(t2=p16()));cpu.wz=t2+1) H(0x5B, set_de(r16(t2=p16()));cpu.wz=t2+1)
    H(0x6B, set_hl(r16(t2=p16()));cpu.wz=t2+1) H(0x7B, cpu.SP = r16(t2=p16());cpu.wz=t2+1)
        R 20;
  
    case 0x44: case 0x54: case 0x64: case 0x74:
    case 0x4C: case 0x5C: case 0x6C: case 0x7C:
        cpu.A = sub8(0, cpu.A, 0); R 8;
  
    case 0x46: case 0x66: cpu.IM = 0; R 8;
    case 0x56: case 0x76: cpu.IM = 1; R 8;
    case 0x5E: case 0x7E: cpu.IM = 2; R 8;
  
    case 0x67: {
        u8 na = cpu.A, val = r8(get_hl());
        cpu.A = (na & 0xF0) | (val & 0xF); w8(get_hl(), (val >> 4) | (na << 4));
        rot_ep(); R 18;
    }
    case 0x6F: {
        u8 na = cpu.A, val = r8(get_hl());
        cpu.A = (na & 0xF0) | (val >> 4); w8(get_hl(), (val << 4) | (na & 0xF));
        rot_ep(); R 18;
    }
  
    default:
        // Все недокументированные opc в диапазонах 0x00-0x3F и 0x80-0xFF 
        // работают как NOP, длятся 8 тактов. Регистр R уже инкрементирован 
        // функцией inc_r() в начале exec_ed.
        if (opc <= 0x3F || opc >= 0x80) {
            R 8;
        }

        // На случай, если пропущена какая-то редкая недокументированная команда из диапазона 0x40-0x7F
        fprintf(stderr, "unknown ED opcode: %02X\n", opc);
        R cyc;
    }
    R cyc;
}


#undef bit
#undef H
#undef HI
#undef LO
