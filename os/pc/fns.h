#include "../port/portfns.h"
void	aamloop(int);
Dirtab*	addarchfile(char*, int, long(*)(Chan*,void*,long,vlong), long(*)(Chan*,void*,long,vlong));
void	archinit(void);
void	bootargs(ulong);
int	cistrcmp(char*, char*);
int	cistrncmp(char*, char*, int);
#define	clearmmucache()				/* x86 doesn't have one */
void	clockintr(Ureg*, void*);
void	(*coherence)(void);
void	cpuid(char*, int*, int*);
int	cpuidentify(void);
void	cpuidprint(void);
void	(*cycles)(uvlong*);
void	delay(int);
int	dmacount(int);
int	dmadone(int);
void	dmaend(int);
int	dmainit(int, int);
long	dmasetup(int, void*, long, int);
void	dumpregs(Ureg*);
#define	evenaddr(x)				/* x86 doesn't care */
void	fpinit(void);
void	fpoff(void);
void	fprestore(FPU*);
void	fpsave(FPU*);
ulong	fpstatus(void);
ulong	getcr0(void);
ulong	getcr2(void);
ulong	getcr3(void);
ulong	getcr4(void);
char*	getconf(char*);
void	guesscpuhz(int);
int	i8042auxcmd(int);
int	i8042auxcmdval(int);
void	i8042auxenable(void (*)(int, int));
int i8042auxdetect(void);
void	i8042reset(void);
void	i8250console(void);
void	i8253enable(void);
void	i8253init(void);
void	i8253link(void);
uvlong	i8253read(uvlong*);
void	i8253timerset(uvlong);
void	i8259init(void);
int	i8259isr(int);
int	i8259enable(Vctl*);
int	i8259vecno(int);
int	i8259disable(int);
void	idle(void);
#define	idlehands()			/* nothing to do in the runproc */
int	inb(int);
void	insb(int, void*, int);
ushort	ins(int);
void	inss(int, void*, int);
ulong	inl(int);
void	insl(int, void*, int);
int	intrdisable(int, void (*)(Ureg *, void *), void*, int, char*);
void	intrenable(int, void (*)(Ureg*, void*), void*, int, char*);
void	iofree(int);
void	ioinit(void);
int	iounused(int, int);
int	ioalloc(int, int, int, char*);
int	ioreserve(int, int, int, char*);
int	iprint(char*, ...);
int	isaconfig(char*, int, ISAConf*);
int	isvalid_va(void*);
void	kbdenable(void);
void	kbdinit(void);
void	kdbenable(void);
#define	kmapinval()
void	lapicclock(Ureg*, void*);
void	lapictimerset(uvlong);
void	lgdt(ushort[3]);
void	lidt(ushort[3]);
void	links(void);
void	ltr(ulong);
void	mach0init(void);
void	machinit(void);
void	mathinit(void);
void	mb386(void);
void	mb586(void);
void	meminit(ulong);
#define mmuflushtlb(pdb) putcr3(pdb)
void	mmuinit(void);
ulong	mmukmap(ulong, ulong, int);
int	mmukmapsync(ulong);
ulong*	mmuwalk(ulong*, ulong, int, int);
uchar	nvramread(int);
void	nvramwrite(int, uchar);
void	outb(int, int);
void	outsb(int, void*, int);
void	outs(int, ushort);
void	outss(int, void*, int);
void	outl(int, ulong);
void	outsl(int, void*, int);
int	pciscan(int, Pcidev**);
ulong	pcibarsize(Pcidev*, int);
int	pcicfgr8(Pcidev*, int);
int	pcicfgr16(Pcidev*, int);
int	pcicfgr32(Pcidev*, int);
void	pcicfgw8(Pcidev*, int, int);
void	pcicfgw16(Pcidev*, int, int);
void	pcicfgw32(Pcidev*, int, int);
void	pciclrbme(Pcidev*);
void	pciclrioe(Pcidev*);
void	pciclrmwi(Pcidev*);
int	pcigetpms(Pcidev*);
void	pcihinv(Pcidev*);
uchar	pciipin(Pcidev*, uchar);
Pcidev* pcimatch(Pcidev*, int, int);
Pcidev* pcimatchtbdf(int);
void	pcireset(void);
void	pcisetbme(Pcidev*);
void	pcisetioe(Pcidev*);
int	pcisetpms(Pcidev*, int);
void	pcmcisread(PCMslot*);
int	pcmcistuple(int, int, int, void*, int);
PCMmap*	pcmmap(int, ulong, int, int);
int	pcmspecial(char*, ISAConf*);
int	(*_pcmspecial)(char *, ISAConf *);
void	pcmspecialclose(int);
void	(*_pcmspecialclose)(int);
void	pcmunmap(int, PCMmap*);
void	poolinit(void);
void	poolsizeinit(void);
void	procsave(Proc*);
void	procsetup(Proc*);
void	putcr3(ulong);
void	putcr4(ulong);
void	rdmsr(int, vlong*);
ulong rdtsc32(void);
void	screeninit(void);
int	screenprint(char*, ...);			/* debugging */
void	(*screenputs)(char*, int);
#define	segflush(a,n)
void	syncclock(void);
uvlong	tscticks(uvlong*);
void	trapenable(int, void (*)(Ureg*, void*), void*, char*);
void	trapinit(void);
ulong	_tas(ulong*);
ulong	umbmalloc(ulong, int, int);
void	umbfree(ulong, int);
ulong	umbrwmalloc(ulong, int, int);
void	umbrwfree(ulong, int);
ulong	upamalloc(ulong, int, int);
void	upafree(ulong, int);
void	upareserve(ulong, int);
void	vectortable(void);
void*	vmap(ulong, int);
void	vunmap(void*, int);
void	wrmsr(ulong, ulong);
int	xchgw(ushort*, int);
ulong	kzeromap(ulong, ulong, int);
void	nmiscreen(void);
int	kbdinready(void);

#define	waserror()	(up->nerrlab++, setlabel(&up->errlab[up->nerrlab-1]))
#define getcallerpc(x)	(((ulong*)(x))[-1])
#define KADDR(a)	((void*)((ulong)(a)|KZERO))
#define PADDR(a)	((ulong)(a)&~KZERO)

#define	dcflush(a, b)
#define	clockcheck();
#define 	dumplongs(x, y, z)
#define 	setpanic()