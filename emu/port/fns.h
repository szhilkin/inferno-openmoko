#if !defined(NORETURN)
#define NORETURN void
#endif
ulong		FPcontrol(ulong,ulong);
ulong		FPstatus(ulong,ulong);
void		FPsave(void*);
void		FPrestore(void*);
void		sleep9(Rendez*, int (*)(void*), void*);
int		wakeup9(Rendez*);
void		FPinit(void);
void		addprog(Proc*);
Block*		adjustblock(Block*, int);
Block*		allocb(int);
Block*		bl2mem(char*, Block*, int);
int		blocklen(Block*);
char*		c2name(Chan*);
int		canlock(Lock*);
int		canqlock(QLock*);
void		cclose(Chan*);
void		chandevinit(void);
void		chanfree(Chan*);
Dir*		chandirstat(Chan*);
void		cinit(void);
char*		clipread(void);
int		clipwrite(char*);
void		copen(Chan*);
void		cmderror(Cmdbuf*, char*);
Block*		concatblock(Block*);
int		cread(Chan*, char*, int, vlong);
void		cwrite(Chan*, char*, int, vlong);
Chan*		cunique(Chan*);
void		cupdate(Chan*, char*, int, vlong);
char*		cleanname(char*);
Chan*		cclone(Chan*);
void		closeegrp(Egrp*);
void		closefgrp(Fgrp*);
void		closepgrp(Pgrp*);
void		closesigs(Skeyset*);
int		cmount(Chan*, Chan*, int, char*);
Chan*		createdir(Chan*, Mhead*);
void		cunmount(Chan*, Chan*);
int		decref(Ref*);
long		devbwrite(Chan*, Block*, ulong);
void		devcreate(Chan*, const char*, int, ulong);
void		devdir(Chan*, Qid, const char*, long, char*, long, Dir*);
long		devdirread(Chan*, void*, long, Dirtab*, int, Devgen*);
void		devinit(void);
int		devno(int, int);
Dev*		devbyname(const char*);
void		devpermcheck(const char*, ulong, int);
void		devremove(Chan*);
int		devstat(Chan*, char*, int, Dirtab*, int, Devgen*);
int		devwstat(Chan*, char*, int);
Chan*		devattach(int, const char*);
Block*		devbread(Chan*, long, ulong);
Chan*		devclone(Chan*);
Devgen		devgen;
Chan*		devopen(Chan*, int, Dirtab*, int, Devgen*);
Walkqid*	devwalk(Chan*, Chan*, const char**, int, Dirtab*, int, Devgen*);
NORETURN	disfault(void*, __in_z const char*msg);
NORETURN	disinit(__in_z const char*initmod);
int		domount(Chan**, Mhead**);
void		drawqlock(void);
void		drawqunlock(void);
Fgrp*		dupfgrp(Fgrp*);
void		egrpcpy(Egrp*, Egrp*);
int		emptystr(const char*);
NORETURN	emuinit(__in_z const char*initmod);
int		eqchan(Chan*, Chan*, int);
int		eqqid(Qid, Qid);
NORETURN	error(__in_z const char*msg);
NORETURN	errorf(__in_z const char*fmt, ...);
#pragma varargck argpos errorf 1
void		excinit(void);
NORETURN	exhausted(const char*);
int		export(int, char*, int);
Chan*		fdtochan(Fgrp*, int, int, int, int);
int		findmount(Chan**, Mhead**, int, int, Qid);
void		freeb(Block*);
void		freeblist(Block*);
void		freeskey(Signerkey*);
/*ulong	getcallerpc(void*);*/
ulong		getFPcontrol(void);
ulong		getFPstatus(void);
void		gkbdputc(Queue*, int);
int		incref(Ref*);
int		iprint(__in_z const char*fmt, ...);
void		isdir(__in const Chan*);
int		isdotdot(__in_z const char*);
int		iseve(void);
int		kannounce(char*, char*);
int		kdial(char*, char*, char*, int*);
typedef void (*ProcFunc)(void*);
int		kproc( __in_z const char *name,
		       __in ProcFunc func,
		      void *arg,
		      KProcFlags flags);
int		kfgrpclose(Fgrp*, int);
void		ksetenv(__in_z const char*, __in_z const char*, int);
void		kstrcpy(__out_z char*, __in_z const char*, __in int);
void		kstrdup(char**, const char*);
long		latin1(uchar*, int);
NORETURN	libinit(__in_z const char*initmod);
void		links(void);
void		lock(Lock*);
Cmdtab*		lookupcmd(Cmdbuf*, Cmdtab*, int);
Block*		mem2bl(uchar*, int);
int		memusehigh(void);
int		memlow(void);
void		mkqid(Qid*, vlong, ulong, int);
Qid		mkuqid(Chan*, Uqid*);
Chan*		mntauth(Chan*, char*);
long		mntversion(Chan*, char*, int, int);
void		mountfree(Mount*);
void		mousetrack(int, int, int, int);
void		muxclose(Mnt*);
Chan*		namec(const char*, int, int, ulong);
Chan*		newchan(void);
Cname*		newcname(__in_z const char*);
Egrp*		newegrp(void);
Fgrp*		newfgrp(Fgrp*);
Mount*		newmount(Mhead*, Chan*, int, char*);
Pgrp*		newpgrp(void);
Proc*		newproc(void);
NORETURN	nexterror(void);
void		notkilled(void);
int		openmode(ulong);
void		osblock(void);
void*		oscmd(char**, int, char*, int*);
int		oscmdwait(void*, char*, int);
int		oscmdkill(void*);
void		oscmdfree(void*);
#define oserror() {print("%s:%d %s", __FILE__, __LINE__, __FUNCTION__);_oserror();}
NORETURN	_oserror(void);
void		oserrstr(char*, uint);
NORETURN	oslongjmp(void*, osjmpbuf, int);
long		osmillisec(void);
int		osmillisleep(ulong);
void		osready(Proc*);
int		limbosleep(ulong);
vlong		osusectime(void);
Block*		packblock(Block*);
Block*		padblock(Block*, int);
NORETURN 	panic(__in_z const char*, ...);
Cmdbuf*		parsecmd(const void*, int);
void		pexit(char*, int);
void		pgrpcpy(Pgrp*, Pgrp*);
int		progfdprint(Chan*, int, int, char*, int);
void		putenvq(char*, char*, int);
void		putenvqv(char*, char**, int, int);
void		putmhead(Mhead*);
Block*		pullupblock(Block*, int);
Block*		pullupqueue(Queue*, int);
void		qaddlist(Queue*, Block*);
Block*		qbread(Queue*, int);
long		qbwrite(Queue*, Block*);
Queue*		qbypass(void (*)(void*, Block*), void*);
int		qcanread(Queue*);
void		qclose(Queue*);
int		qisclosed(Queue*);
int		qconsume(Queue*, void*, int);
Block*		qcopy(Queue*, int, ulong);
int		qdiscard(Queue*, int);
void		qflush(Queue*);
void		qfree(Queue*);
int		qfull(Queue*);
Block*		qget(Queue*);
void		qhangup(Queue*, char*);
int		qiwrite(Queue*, void*, int);
int		qlen(Queue*);
void		qlock(QLock*);
void		qnoblock(Queue*, int);
Queue*		qopen(int, int, void (*)(void*), void*);
int		qpass(Queue*, Block*);
int		qproduce(Queue*, void*, int);
void		qputback(Queue*, Block*);
long		qread(Queue*, void*, int);
Block*		qremove(Queue*);
void		qreopen(Queue*);
void		qsetlimit(Queue*, int);
int		qstate(Queue*);
void		qunlock(QLock*);
int		qwindow(Queue*);
int		qwrite(Queue*, const void*, int);
ulong		randomread(char *xp, ulong n);
void		randominit(void);
int		readkbd(void);
int		readnum(ulong, void*, ulong, ulong, int);
int		readnum_vlong(ulong, char*, ulong, vlong, int);
int		readstr(ulong, void*, ulong, const char*);
#define	seconds()	(osusectime()/1000000)
void		seterror(char*, ...);
void		setid(char*, int);
void		setpointer(int, int);
const char*	skipslash(const char*);
void		srvrtinit(void);
void		swiproc(Proc*, int);
Block*		trimblock(Block*, int, int);
long		unionread(Chan*, void*, long);
void		unlock(Lock*);
Uqid*		uqidalloc(Uqidtab*, Chan*);
void		uqidinit(Uqidtab*);
void		freeuqid(Uqidtab*, Uqid*);
void		validname(const char*, int);
void		validstat(const char*, int);
void		validwstatname(const char*);
NORETURN	vmachine(void*);
int		walk(Chan**, const char**, int, int, int*);
NORETURN 	cleanexit(int);
void		oshostintr(Proc*);
void		osenter(void);
void		osleave(void);
void		oslopri(void);
NORETURN	ospause(void);
void		osyield(void);
void		osreboot(char*, char**);
ulong		poolmaxsize(void);
Pool*		poolmk(char*, int, int, int);

/*void*		smalloc(size_t);
void*		kmalloc(size_t);*/

/* Namespace Emulation */
int		kbind(char*, char*, int);
int		kclose(int);
int		kcreate(char*, int, ulong);
int		kdup(int, int);
int		kfstat(int, char*, int);
int		kfwstat(int, char*, int);
int		kmount(int, int, char*, int, char*);
int		kunmount(char*, char*);
int		kopen(const char*, int);
long		kread(int, void*, long);
int		kremove(char*);
vlong		kseek(int, vlong, int);
int		kstat(char*, char*, int);
long		kwrite(int, void*, long);
int		kwstat(char*, char*, int);
Dir*		kdirstat(char*);
Dir*		kdirfstat(int);
int		kdirwstat(char*, Dir*);
int		kdirfwstat(int, Dir*);
long		kdirread(int, Dir**);
int		klisten(char*, char*);

Cname*		addelem(Cname*, const char*);
void		cleancname(Cname*);
void		cnameclose(Cname*);

#pragma varargck argpos iprint 1
