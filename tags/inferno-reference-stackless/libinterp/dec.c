/* Machine generated by decgen.c */

#include "lib9.h"
#include "isa.h"
#include "interp.h"

#define DIND(reg, xxx) (uchar*)((*(ulong*)(R.reg+R.PC->xxx.i.f))+R.PC->xxx.i.s)
static void
D00(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = R.MP+R.PC->d.ind;
	R.m = R.d;
}
static void
D01(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = R.FP+R.PC->d.ind;
	R.m = R.d;
}
static void
D02(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.d;
}
static void
D03(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
D04(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = DIND(MP, d);
	R.m = R.d;
}
static void
D05(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = DIND(FP, d);
	R.m = R.d;
}
static void
D06(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
D07(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
D08(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = R.MP+R.PC->d.ind;
	R.m = R.d;
}
static void
D09(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = R.FP+R.PC->d.ind;
	R.m = R.d;
}
static void
D0A(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.d;
}
static void
D0B(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
D0C(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = DIND(MP, d);
	R.m = R.d;
}
static void
D0D(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = DIND(FP, d);
	R.m = R.d;
}
static void
D0E(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
D0F(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
D10(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = R.MP+R.PC->d.ind;
	R.m = R.d;
}
static void
D11(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = R.FP+R.PC->d.ind;
	R.m = R.d;
}
static void
D12(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.d;
}
static void
D13(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
D14(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = DIND(MP, d);
	R.m = R.d;
}
static void
D15(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = DIND(FP, d);
	R.m = R.d;
}
static void
D16(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
D17(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
D18(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.m = R.d;
}
static void
D19(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.m = R.d;
}
static void
D1A(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.d;
}
static void
D1B(void)
{
}
static void
D1C(void)
{
	R.d = DIND(MP, d);
	R.m = R.d;
}
static void
D1D(void)
{
	R.d = DIND(FP, d);
	R.m = R.d;
}
static void
D1E(void)
{
}
static void
D1F(void)
{
}
static void
D20(void)
{
	R.s = DIND(MP, s);
	R.d = R.MP+R.PC->d.ind;
	R.m = R.d;
}
static void
D21(void)
{
	R.s = DIND(MP, s);
	R.d = R.FP+R.PC->d.ind;
	R.m = R.d;
}
static void
D22(void)
{
	R.s = DIND(MP, s);
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.d;
}
static void
D23(void)
{
	R.s = DIND(MP, s);
}
static void
D24(void)
{
	R.s = DIND(MP, s);
	R.d = DIND(MP, d);
	R.m = R.d;
}
static void
D25(void)
{
	R.s = DIND(MP, s);
	R.d = DIND(FP, d);
	R.m = R.d;
}
static void
D26(void)
{
	R.s = DIND(MP, s);
}
static void
D27(void)
{
	R.s = DIND(MP, s);
}
static void
D28(void)
{
	R.s = DIND(FP, s);
	R.d = R.MP+R.PC->d.ind;
	R.m = R.d;
}
static void
D29(void)
{
	R.s = DIND(FP, s);
	R.d = R.FP+R.PC->d.ind;
	R.m = R.d;
}
static void
D2A(void)
{
	R.s = DIND(FP, s);
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.d;
}
static void
D2B(void)
{
	R.s = DIND(FP, s);
}
static void
D2C(void)
{
	R.s = DIND(FP, s);
	R.d = DIND(MP, d);
	R.m = R.d;
}
static void
D2D(void)
{
	R.s = DIND(FP, s);
	R.d = DIND(FP, d);
	R.m = R.d;
}
static void
D2E(void)
{
	R.s = DIND(FP, s);
}
static void
D2F(void)
{
	R.s = DIND(FP, s);
}
static void
D30(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.m = R.d;
}
static void
D31(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.m = R.d;
}
static void
D32(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.d;
}
static void
D33(void)
{
}
static void
D34(void)
{
	R.d = DIND(MP, d);
	R.m = R.d;
}
static void
D35(void)
{
	R.d = DIND(FP, d);
	R.m = R.d;
}
static void
D36(void)
{
}
static void
D37(void)
{
}
static void
D38(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.m = R.d;
}
static void
D39(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.m = R.d;
}
static void
D3A(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.d;
}
static void
D3B(void)
{
}
static void
D3C(void)
{
	R.d = DIND(MP, d);
	R.m = R.d;
}
static void
D3D(void)
{
	R.d = DIND(FP, d);
	R.m = R.d;
}
static void
D3E(void)
{
}
static void
D3F(void)
{
}
static void
D40(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = R.MP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D41(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = R.FP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D42(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = (uchar*)&R.PC->d.imm;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D43(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
D44(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = DIND(MP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D45(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = DIND(FP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D46(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
D47(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
D48(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = R.MP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D49(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = R.FP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D4A(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = (uchar*)&R.PC->d.imm;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D4B(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
D4C(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = DIND(MP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D4D(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = DIND(FP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D4E(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
D4F(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
D50(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = R.MP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D51(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = R.FP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D52(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = (uchar*)&R.PC->d.imm;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D53(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
D54(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = DIND(MP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D55(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = DIND(FP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D56(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
D57(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
D58(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D59(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D5A(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D5B(void)
{
}
static void
D5C(void)
{
	R.d = DIND(MP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D5D(void)
{
	R.d = DIND(FP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D5E(void)
{
}
static void
D5F(void)
{
}
static void
D60(void)
{
	R.s = DIND(MP, s);
	R.d = R.MP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D61(void)
{
	R.s = DIND(MP, s);
	R.d = R.FP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D62(void)
{
	R.s = DIND(MP, s);
	R.d = (uchar*)&R.PC->d.imm;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D63(void)
{
	R.s = DIND(MP, s);
}
static void
D64(void)
{
	R.s = DIND(MP, s);
	R.d = DIND(MP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D65(void)
{
	R.s = DIND(MP, s);
	R.d = DIND(FP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D66(void)
{
	R.s = DIND(MP, s);
}
static void
D67(void)
{
	R.s = DIND(MP, s);
}
static void
D68(void)
{
	R.s = DIND(FP, s);
	R.d = R.MP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D69(void)
{
	R.s = DIND(FP, s);
	R.d = R.FP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D6A(void)
{
	R.s = DIND(FP, s);
	R.d = (uchar*)&R.PC->d.imm;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D6B(void)
{
	R.s = DIND(FP, s);
}
static void
D6C(void)
{
	R.s = DIND(FP, s);
	R.d = DIND(MP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D6D(void)
{
	R.s = DIND(FP, s);
	R.d = DIND(FP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D6E(void)
{
	R.s = DIND(FP, s);
}
static void
D6F(void)
{
	R.s = DIND(FP, s);
}
static void
D70(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D71(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D72(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D73(void)
{
}
static void
D74(void)
{
	R.d = DIND(MP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D75(void)
{
	R.d = DIND(FP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D76(void)
{
}
static void
D77(void)
{
}
static void
D78(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D79(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D7A(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D7B(void)
{
}
static void
D7C(void)
{
	R.d = DIND(MP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D7D(void)
{
	R.d = DIND(FP, d);
	R.t = (short)R.PC->reg;
	R.m = &R.t;
}
static void
D7E(void)
{
}
static void
D7F(void)
{
}
static void
D80(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = R.MP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
D81(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = R.FP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
D82(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.FP+R.PC->reg;
}
static void
D83(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
D84(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = DIND(MP, d);
	R.m = R.FP+R.PC->reg;
}
static void
D85(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = DIND(FP, d);
	R.m = R.FP+R.PC->reg;
}
static void
D86(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
D87(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
D88(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = R.MP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
D89(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = R.FP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
D8A(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.FP+R.PC->reg;
}
static void
D8B(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
D8C(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = DIND(MP, d);
	R.m = R.FP+R.PC->reg;
}
static void
D8D(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = DIND(FP, d);
	R.m = R.FP+R.PC->reg;
}
static void
D8E(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
D8F(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
D90(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = R.MP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
D91(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = R.FP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
D92(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.FP+R.PC->reg;
}
static void
D93(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
D94(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = DIND(MP, d);
	R.m = R.FP+R.PC->reg;
}
static void
D95(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = DIND(FP, d);
	R.m = R.FP+R.PC->reg;
}
static void
D96(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
D97(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
D98(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
D99(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
D9A(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.FP+R.PC->reg;
}
static void
D9B(void)
{
}
static void
D9C(void)
{
	R.d = DIND(MP, d);
	R.m = R.FP+R.PC->reg;
}
static void
D9D(void)
{
	R.d = DIND(FP, d);
	R.m = R.FP+R.PC->reg;
}
static void
D9E(void)
{
}
static void
D9F(void)
{
}
static void
DA0(void)
{
	R.s = DIND(MP, s);
	R.d = R.MP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
DA1(void)
{
	R.s = DIND(MP, s);
	R.d = R.FP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
DA2(void)
{
	R.s = DIND(MP, s);
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.FP+R.PC->reg;
}
static void
DA3(void)
{
	R.s = DIND(MP, s);
}
static void
DA4(void)
{
	R.s = DIND(MP, s);
	R.d = DIND(MP, d);
	R.m = R.FP+R.PC->reg;
}
static void
DA5(void)
{
	R.s = DIND(MP, s);
	R.d = DIND(FP, d);
	R.m = R.FP+R.PC->reg;
}
static void
DA6(void)
{
	R.s = DIND(MP, s);
}
static void
DA7(void)
{
	R.s = DIND(MP, s);
}
static void
DA8(void)
{
	R.s = DIND(FP, s);
	R.d = R.MP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
DA9(void)
{
	R.s = DIND(FP, s);
	R.d = R.FP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
DAA(void)
{
	R.s = DIND(FP, s);
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.FP+R.PC->reg;
}
static void
DAB(void)
{
	R.s = DIND(FP, s);
}
static void
DAC(void)
{
	R.s = DIND(FP, s);
	R.d = DIND(MP, d);
	R.m = R.FP+R.PC->reg;
}
static void
DAD(void)
{
	R.s = DIND(FP, s);
	R.d = DIND(FP, d);
	R.m = R.FP+R.PC->reg;
}
static void
DAE(void)
{
	R.s = DIND(FP, s);
}
static void
DAF(void)
{
	R.s = DIND(FP, s);
}
static void
DB0(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
DB1(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
DB2(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.FP+R.PC->reg;
}
static void
DB3(void)
{
}
static void
DB4(void)
{
	R.d = DIND(MP, d);
	R.m = R.FP+R.PC->reg;
}
static void
DB5(void)
{
	R.d = DIND(FP, d);
	R.m = R.FP+R.PC->reg;
}
static void
DB6(void)
{
}
static void
DB7(void)
{
}
static void
DB8(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
DB9(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.m = R.FP+R.PC->reg;
}
static void
DBA(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.FP+R.PC->reg;
}
static void
DBB(void)
{
}
static void
DBC(void)
{
	R.d = DIND(MP, d);
	R.m = R.FP+R.PC->reg;
}
static void
DBD(void)
{
	R.d = DIND(FP, d);
	R.m = R.FP+R.PC->reg;
}
static void
DBE(void)
{
}
static void
DBF(void)
{
}
static void
DC0(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = R.MP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DC1(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = R.FP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DC2(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.MP+R.PC->reg;
}
static void
DC3(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
DC4(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = DIND(MP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DC5(void)
{
	R.s = R.MP+R.PC->s.ind;
	R.d = DIND(FP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DC6(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
DC7(void)
{
	R.s = R.MP+R.PC->s.ind;
}
static void
DC8(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = R.MP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DC9(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = R.FP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DCA(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.MP+R.PC->reg;
}
static void
DCB(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
DCC(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = DIND(MP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DCD(void)
{
	R.s = R.FP+R.PC->s.ind;
	R.d = DIND(FP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DCE(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
DCF(void)
{
	R.s = R.FP+R.PC->s.ind;
}
static void
DD0(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = R.MP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DD1(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = R.FP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DD2(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.MP+R.PC->reg;
}
static void
DD3(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
DD4(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = DIND(MP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DD5(void)
{
	R.s = (uchar*)&R.PC->s.imm;
	R.d = DIND(FP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DD6(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
DD7(void)
{
	R.s = (uchar*)&R.PC->s.imm;
}
static void
DD8(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DD9(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DDA(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.MP+R.PC->reg;
}
static void
DDB(void)
{
}
static void
DDC(void)
{
	R.d = DIND(MP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DDD(void)
{
	R.d = DIND(FP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DDE(void)
{
}
static void
DDF(void)
{
}
static void
DE0(void)
{
	R.s = DIND(MP, s);
	R.d = R.MP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DE1(void)
{
	R.s = DIND(MP, s);
	R.d = R.FP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DE2(void)
{
	R.s = DIND(MP, s);
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.MP+R.PC->reg;
}
static void
DE3(void)
{
	R.s = DIND(MP, s);
}
static void
DE4(void)
{
	R.s = DIND(MP, s);
	R.d = DIND(MP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DE5(void)
{
	R.s = DIND(MP, s);
	R.d = DIND(FP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DE6(void)
{
	R.s = DIND(MP, s);
}
static void
DE7(void)
{
	R.s = DIND(MP, s);
}
static void
DE8(void)
{
	R.s = DIND(FP, s);
	R.d = R.MP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DE9(void)
{
	R.s = DIND(FP, s);
	R.d = R.FP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DEA(void)
{
	R.s = DIND(FP, s);
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.MP+R.PC->reg;
}
static void
DEB(void)
{
	R.s = DIND(FP, s);
}
static void
DEC(void)
{
	R.s = DIND(FP, s);
	R.d = DIND(MP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DED(void)
{
	R.s = DIND(FP, s);
	R.d = DIND(FP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DEE(void)
{
	R.s = DIND(FP, s);
}
static void
DEF(void)
{
	R.s = DIND(FP, s);
}
static void
DF0(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DF1(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DF2(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.MP+R.PC->reg;
}
static void
DF3(void)
{
}
static void
DF4(void)
{
	R.d = DIND(MP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DF5(void)
{
	R.d = DIND(FP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DF6(void)
{
}
static void
DF7(void)
{
}
static void
DF8(void)
{
	R.d = R.MP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DF9(void)
{
	R.d = R.FP+R.PC->d.ind;
	R.m = R.MP+R.PC->reg;
}
static void
DFA(void)
{
	R.d = (uchar*)&R.PC->d.imm;
	R.m = R.MP+R.PC->reg;
}
static void
DFB(void)
{
}
static void
DFC(void)
{
	R.d = DIND(MP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DFD(void)
{
	R.d = DIND(FP, d);
	R.m = R.MP+R.PC->reg;
}
static void
DFE(void)
{
}
static void
DFF(void)
{
}

void	(*dec[])(void) =
{
	D00,
	D01,
	D02,
	D03,
	D04,
	D05,
	D06,
	D07,
	D08,
	D09,
	D0A,
	D0B,
	D0C,
	D0D,
	D0E,
	D0F,
	D10,
	D11,
	D12,
	D13,
	D14,
	D15,
	D16,
	D17,
	D18,
	D19,
	D1A,
	D1B,
	D1C,
	D1D,
	D1E,
	D1F,
	D20,
	D21,
	D22,
	D23,
	D24,
	D25,
	D26,
	D27,
	D28,
	D29,
	D2A,
	D2B,
	D2C,
	D2D,
	D2E,
	D2F,
	D30,
	D31,
	D32,
	D33,
	D34,
	D35,
	D36,
	D37,
	D38,
	D39,
	D3A,
	D3B,
	D3C,
	D3D,
	D3E,
	D3F,
	D40,
	D41,
	D42,
	D43,
	D44,
	D45,
	D46,
	D47,
	D48,
	D49,
	D4A,
	D4B,
	D4C,
	D4D,
	D4E,
	D4F,
	D50,
	D51,
	D52,
	D53,
	D54,
	D55,
	D56,
	D57,
	D58,
	D59,
	D5A,
	D5B,
	D5C,
	D5D,
	D5E,
	D5F,
	D60,
	D61,
	D62,
	D63,
	D64,
	D65,
	D66,
	D67,
	D68,
	D69,
	D6A,
	D6B,
	D6C,
	D6D,
	D6E,
	D6F,
	D70,
	D71,
	D72,
	D73,
	D74,
	D75,
	D76,
	D77,
	D78,
	D79,
	D7A,
	D7B,
	D7C,
	D7D,
	D7E,
	D7F,
	D80,
	D81,
	D82,
	D83,
	D84,
	D85,
	D86,
	D87,
	D88,
	D89,
	D8A,
	D8B,
	D8C,
	D8D,
	D8E,
	D8F,
	D90,
	D91,
	D92,
	D93,
	D94,
	D95,
	D96,
	D97,
	D98,
	D99,
	D9A,
	D9B,
	D9C,
	D9D,
	D9E,
	D9F,
	DA0,
	DA1,
	DA2,
	DA3,
	DA4,
	DA5,
	DA6,
	DA7,
	DA8,
	DA9,
	DAA,
	DAB,
	DAC,
	DAD,
	DAE,
	DAF,
	DB0,
	DB1,
	DB2,
	DB3,
	DB4,
	DB5,
	DB6,
	DB7,
	DB8,
	DB9,
	DBA,
	DBB,
	DBC,
	DBD,
	DBE,
	DBF,
	DC0,
	DC1,
	DC2,
	DC3,
	DC4,
	DC5,
	DC6,
	DC7,
	DC8,
	DC9,
	DCA,
	DCB,
	DCC,
	DCD,
	DCE,
	DCF,
	DD0,
	DD1,
	DD2,
	DD3,
	DD4,
	DD5,
	DD6,
	DD7,
	DD8,
	DD9,
	DDA,
	DDB,
	DDC,
	DDD,
	DDE,
	DDF,
	DE0,
	DE1,
	DE2,
	DE3,
	DE4,
	DE5,
	DE6,
	DE7,
	DE8,
	DE9,
	DEA,
	DEB,
	DEC,
	DED,
	DEE,
	DEF,
	DF0,
	DF1,
	DF2,
	DF3,
	DF4,
	DF5,
	DF6,
	DF7,
	DF8,
	DF9,
	DFA,
	DFB,
	DFC,
	DFD,
	DFE,
	DFF 
};
