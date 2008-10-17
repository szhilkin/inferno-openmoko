void	(*optab[256])(Disdata*s, Disdata*m, Disdata*d, REG*rr) =
{
	badop,
	alt,
	nbalt,
	igoto,
	call,
	frame,
	spawn,
	runt,
	iload,
	mcall,
	mspawn,
	mframe,
	ret,
	jmp,
	icase,
	iexit,
	new,
	newa,
	newcb,
	newcw,
	newcf,
	newcp,
	newcm,
	newcmp,
	isend,
	irecv,
	consb,
	consw,
	consp,
	consf,
	consm,
	consmp,
	headb,
	headw,
	headp,
	headf,
	headm,
	headmp,
	tail,
	lea,
	indx,
	movp,
	movm,
	movmp,
	movb,
	movw,
	movf,
	cvtbw,
	cvtwb,
	cvtfw,
	cvtwf,
	cvtca,
	cvtac,
	cvtwc,
	cvtcw,
	cvtfc,
	cvtcf,
	addb,
	addw,
	addf,
	subb,
	subw,
	subf,
	mulb,
	mulw,
	mulf,
	divb,
	divw,
	divf,
	modw,
	modb,
	andb,
	andw,
	orb,
	orw,
	xorb,
	xorw,
	shlb,
	shlw,
	shrb,
	shrw,
	insc,
	indc,
	addc,
	lenc,
	lena,
	lenl,
	beqb,
	bneb,
	bltb,
	bleb,
	bgtb,
	bgeb,
	beqw,
	bnew,
	bltw,
	blew,
	bgtw,
	bgew,
	beqf,
	bnef,
	bltf,
	blef,
	bgtf,
	bgef,
	beqc,
	bnec,
	bltc,
	blec,
	bgtc,
	bgec,
	slicea,
	slicela,
	slicec,
	indw,
	indf,
	indb,
	negf,
	movl,
	addl,
	subl,
	divl,
	modl,
	mull,
	andl,
	orl,
	xorl,
	shll,
	shrl,
	bnel,
	bltl,
	blel,
	bgtl,
	bgel,
	beql,
	cvtlf,
	cvtfl,
	cvtlw,
	cvtwl,
	cvtlc,
	cvtcl,
	headl,
	consl,
	newcl,
	casec,
	indl,
	movpc,
	tcmp,
	mnewz,		/* j2d */
	cvtrf,		/* j2d */
	cvtfr,		/* j2d */
	cvtws,		/* j2d */
	cvtsw,		/* j2d */
	lsrw,		/* j2d */
	lsrl,		/* j2d */
	eclr,		/* unused */
	newz,		/* j2d */
	newaz,		/* j2d */
	iraise,
	casel,
	mulx,
	divx,
	cvtxx,
	mulx0,
	divx0,
	cvtxx0,
	mulx1,
	divx1,
	cvtxx1,
	cvtfx,
	cvtxf,
	iexpw,
	iexpl,
	iexpf,
	self,
	/* fix maxdis if you add opcodes */
};
