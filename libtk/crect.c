#include <lib9.h>
#include <draw.h>
#include <kernel.h>

#include <isa.h>
#include <interp.h>
#include <runt.h>
#include <tk.h>

#include <canvs.h>


/* Rectangle Options (+ means implemented)
	+fill
	+outline
	+stipple
	+tags
	+width
*/

typedef struct TkCrect TkCrect;
struct TkCrect
{
	int	width;
	Image*	stipple;
};

static
TkOption rectopts[] =
{
	{"width",	OPTnnfrac,	offsetof(TkCrect, width)	},
	{"stipple",	OPTbmap,	offsetof(TkCrect, stipple)	},
	{nil}
};

static
TkOption itemopts_crect[] =
{
	{"tags",	OPTctag,	offsetof(TkCitem, tags)		},
	{"fill",	OPTcolr,	offsetof(TkCitem, env),		{(TkStab*)TkCfill}},
	{"outline",	OPTcolr,	offsetof(TkCitem, env),		{(TkStab*)TkCforegnd}},
	{nil}
};

void
tkcvsrectsize(TkCitem *i)
{
	TkCrect *r;
	int w;

	r = TKobj(TkCrect, i);
	w = TKF2I(r->width)*2;

	i->p.bb = bbnil;
	tkpolybound(i->p.drawpt, i->p.npoint, &i->p.bb);
	i->p.bb = insetrect(i->p.bb, -w);
}

static void
tkmkstipple(Image *stipple)
{
	int locked;
	if (stipple != nil && !stipple->repl) {
		locked = lockdisplay(stipple->display);
		replclipr(stipple, 1, huger);
		if (locked)
			unlockdisplay(stipple->display);
	}
}

TH(tkcvsrectcreat)
{
	const char* e;
	TkCrect *r;
	TkCitem *i;
	TkCanvas *c;
	TkOptab tko[3];

	c = TKobj(TkCanvas, tk);

	i = tkcnewitem(tk, TkCVrect, sizeof(TkCitem)+sizeof(TkCrect));
	if(i == nil)
		return TkNomem;

	r = TKobj(TkCrect, i);
	r->width = TKI2F(1);

	e = tkparsepts(tk->env->top, &i->p, &arg, 0);
	if(e != nil) {
		tkcvsfreeitem(i);
		return e;
	}
	if(i->p.npoint != 2) {
		tkcvsfreeitem(i);
		return TkFewpt;
	}

	tko[0].ptr = r;
	tko[0].optab = rectopts;
	tko[1].ptr = i;
	tko[1].optab = itemopts_crect;
	tko[2].ptr = nil;
	e = tkparse(tk->env->top, arg, tko, nil);
	if(e != nil) {
		tkcvsfreeitem(i);
		return e;
	}
	tkmkstipple(r->stipple);
	e = tkcaddtag(tk, i, 1);
	if(e != nil) {
		tkcvsfreeitem(i);
		return e;
	}

	tkcvsrectsize(i);
	e = tkvalue(val, "%d", i->id);
	if(e != nil) {
		tkcvsfreeitem(i);
		return e;
	}
	tkcvsappend(c, i);

	tkbbmax(&c->update, &i->p.bb);
	tkcvssetdirty(tk);
	return nil;
}

const char*
tkcvsrectcget(TkCitem *i, __in_z const char *arg, char **val)
{
	TkOptab tko[3];
	TkCrect *r = TKobj(TkCrect, i);

	tko[0].ptr = r;
	tko[0].optab = rectopts;
	tko[1].ptr = i;
	tko[1].optab = itemopts_crect;
	tko[2].ptr = nil;

	return tkgencget(tko, arg, val, i->env->top);
}

const char*
tkcvsrectconf(Tk *tk, TkCitem *i, __in_z const char *arg)
{
	const char *e;
	TkOptab tko[3];
	TkCrect *r = TKobj(TkCrect, i);

	tko[0].ptr = r;
	tko[0].optab = rectopts;
	tko[1].ptr = i;
	tko[1].optab = itemopts_crect;
	tko[2].ptr = nil;

	e = tkparse(tk->env->top, arg, tko, nil);
	tkcvsrectsize(i);
	tkmkstipple(r->stipple);
	return e;
}

void
tkcvsrectfree(TkCitem *i)
{
	TkCrect *r;

	r = TKobj(TkCrect, i);
	if(r->stipple)
		freeimage(r->stipple);
}

void
tkcvsrectdraw(__in_ecount(1) const Image *img, TkCitem *i, TkEnv *pe)
{
	int lw, rw;
	TkEnv *e;
	TkCrect *r;
	Rectangle d, rr;
	Point tr, bl;
	Image *pen;

	USED(pe);

	d.min = i->p.drawpt[0];
	d.max = i->p.drawpt[1];

	e = i->env;
	r = TKobj(TkCrect, i);

	pen = nil;
	if((e->set & (1<<TkCfill)))
		pen = tkgc(e, TkCfill);

	if(pen != nil)
		draw(img, d, pen, r->stipple, d.min);

	tr.x = d.max.x;
	tr.y = d.min.y;
	bl.x = d.min.x;
	bl.y = d.max.y;

	rw = (TKF2I(r->width) + 1)/2;
	if(rw <= 0)
		return;
	lw = (TKF2I(r->width))/2;

	pen = tkgc(e, TkCforegnd);
	if(pen != nil) {
		/* horizontal lines first */
		rr.min.x = d.min.x - lw;
		rr.max.x = d.max.x + rw;
		rr.min.y = d.min.y - lw;
		rr.max.y = d.min.y + rw;
		draw(img, rr, pen, nil, rr.min);
		rr.min.y += Dy(d);
		rr.max.y += Dy(d);
		draw(img, rr, pen, nil, rr.min);
		/* now the vertical */
		/* horizontal lines first */
		rr.min.x = d.min.x - lw;
		rr.max.x = d.min.x + rw;
		rr.min.y = d.min.y + rw;
		rr.max.y = d.max.y - lw;
		draw(img, rr, pen, nil, rr.min);
		rr.min.x += Dx(d);
		rr.max.x += Dx(d);
		draw(img, rr, pen, nil, rr.min);
	}
}

const char*
tkcvsrectcoord(TkCitem *i, __in_z const char *arg, int x, int y)
{
	const char* e;
	TkCpoints p;

	if(arg == nil) {
		tkxlatepts(i->p.parampt, i->p.npoint, x, y);
		tkxlatepts(i->p.drawpt, i->p.npoint, TKF2I(x), TKF2I(y));
		i->p.bb = rectaddpt(i->p.bb, Pt(TKF2I(x), TKF2I(y)));
	}
	else {
		e = tkparsepts(i->env->top, &p, &arg, 0);
		if(e != nil)
			return e;
		if(p.npoint != 2) {
			tkfreepoint(&p);
			return TkFewpt;
		}
		tkfreepoint(&i->p);
		i->p = p;
		tkcvsrectsize(i);
	}
	return nil;
}
