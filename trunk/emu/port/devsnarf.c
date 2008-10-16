/*
 * host's snarf buffer
 */

#include "dat.h"
#include "fns.h"
#include "../port/error.h"

enum{
	Qdir,
	Qsnarf,

	Maxsnarf=	100*1024
};

static
Dirtab snarftab[]={
	".",		{Qdir, 0, QTDIR},	0,	0555,
	"snarf",	{Qsnarf},			0,	0666,
};

static QLock snarflock;	/* easiest to synchronise all access */

static Chan*
snarfattach(const char *spec)
{
	return devattach('^', spec);
}

static Walkqid*
snarfwalk(Chan *c, Chan *nc, char **name, int nname)
{
	return devwalk(c, nc, name, nname, snarftab, nelem(snarftab), devgen);
}

static int
snarfstat(Chan* c, char *db, int n)
{
	return devstat(c, db, n, snarftab, nelem(snarftab), devgen);
}

static Chan*
snarfopen(Chan* c, int omode)
{
	c = devopen(c, omode, snarftab, nelem(snarftab), devgen);
	if(c->qid.path == Qsnarf){
		if(c->mode == ORDWR || c->mode == OWRITE){
			qlock(&snarflock);
			free(c->aux.pchar);
			c->aux.pchar = nil;
			qunlock(&snarflock);
		}
	}
	return c;
}

static void
snarfclose(Chan* c)
{
	if((c->flag & COPEN) == 0)
		return;
	if(c->qid.path == Qsnarf){
		/* this must be the last reference: no need to lock */
		if(c->mode == ORDWR || c->mode == OWRITE){
			if(!waserror()){
				clipwrite(c->aux.pchar);
				poperror();
			}
		}
		free(c->aux.pchar);
	}
}

static long
snarfread(Chan* c, char* a, long n, vlong offset)
{
	void *p;

	switch((ulong)c->qid.path){
	case Qdir:
		return devdirread(c, a, n, snarftab, nelem(snarftab), devgen);
	case Qsnarf:
		qlock(&snarflock);
		if(waserror()){
			qunlock(&snarflock);
			nexterror();
		}
		if(offset == 0){
			p = c->aux.pchar;
			c->aux.pchar = nil;
			free(p);
			c->aux.pchar = clipread();
		}
		if(c->aux.pchar != nil)
			n = readstr(offset, a, n, c->aux.pchar);
		else
			n = 0;
		poperror();
		qunlock(&snarflock);
		break;
	default:
		n=0;
		break;
	}
	return n;
}

static long
snarfwrite(Chan* c, const char* va, long n, vlong offset)
{
	ulong l;
	char *p;

	switch((ulong)c->qid.path){
	case Qsnarf:
		/* append only */
		USED(offset);	/* not */
		qlock(&snarflock);
		if(waserror()){
			qunlock(&snarflock);
			nexterror();
		}
		if(c->aux.pchar != nil)
			l = strlen(c->aux.pchar);
		else
			l = 0;
		if(l+n > Maxsnarf)
			error(Etoobig);
		p = c->aux.pchar = (char*)realloc(c->aux.pchar, l+n+1);
		if(p == nil)
			error(Enovmem);
		memmove(p+l, va, n);
		p[l+n] = 0;
		snarftab[1].qid.vers++;
		poperror();
		qunlock(&snarflock);
		break;
	default:
		error(Ebadusefd);
	}
	return n;
}

Dev snarfdevtab = {
	'^',
	"snarf",

	devinit,
	snarfattach,
	snarfwalk,
	snarfstat,
	snarfopen,
	devcreate,
	snarfclose,
	snarfread,
	devbread,
	snarfwrite,
	devbwrite,
	devremove,
	devwstat,
};
