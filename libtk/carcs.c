#include <lib9.h>
#include <draw.h>

#include <isa.h>
#include <interp.h>
#include <runt.h>
#include <tk.h>

#include <canvs.h>

//typedef void	(*Drawfn)(Image*, Point, int, int, Image*, int);

/* Arc Options (+ means implemented)
	+extent
	+fill
	+outline
	 outlinestipple
	+start
	+stipple
	+style (+pieslice chord +arc)
	+tags
	+width
*/

typedef struct TkCarc TkCarc;
struct TkCarc
{
	int	width;
	int 	start;
	int 	extent;
	int 	style;
	Image*	stipple;
	Image*	pen;
};

enum Style
{
	Pieslice,
	Chord,
	Arc
};

static
TkStab tkstyle[] =
{
	{"pieslice",	Pieslice},
	{"arc",		Arc},
	{"chord",	Arc},	/* Can't do chords */
	{nil}
};

static
TkOption arcopts[] =
{
	{"start",	OPTfrac,	offsetof(TkCarc, start) 	},
	{"extent",	OPTfrac,	offsetof(TkCarc, extent) 	},
	{"style",	OPTstab,	offsetof(TkCarc, style),	{tkstyle}},
	{"width",	OPTnnfrac,	offsetof(TkCarc, width) 	},
	{"stipple",	OPTbmap,	offsetof(TkCarc, stipple) 	},
	{nil}
};

static
TkOption itemopts_carcs[] =
{
	{"tags",	OPTctag,	offsetof(TkCitem, tags) 	},
	{"fill",	OPTcolr,	offsetof(TkCitem, env),		{(TkStab*)TkCfill}},
	{"outline",	OPTcolr,	offsetof(TkCitem, env),		{(TkStab*)TkCforegnd}},
	{nil}
};

void
tkcvsarcsize(TkCitem *i)
{
	int w;
	TkCarc *a;

	a = TKobj(TkCarc, i);
	w = TKF2I(a->width)*2;

	i->p.bb = bbnil;
	tkpolybound(i->p.drawpt, i->p.npoint, &i->p.bb);
	i->p.bb = insetrect(i->p.bb, -w);
}

TH(tkcvsarccreat)
{
	const char* e;
	TkCarc *a;
	TkCitem *i;
	TkCanvas *c;
	TkOptab tko[3];

	c = TKobj(TkCanvas, tk);

	i = tkcnewitem(tk, TkCVarc, sizeof(TkCitem)+sizeof(TkCarc));
	if(i == nil)
		return TkNomem;

	a = TKobj(TkCarc, i);
	a->width = TKI2F(1);

	e = tkparsepts(tk->env->top, &i->p, &arg, 0);
	if(e != nil) {
		tkcvsfreeitem(i);
		return e;
	}
	if(i->p.npoint != 2) {
		tkcvsfreeitem(i);
		return TkFewpt;
	}

	tko[0].ptr = a;
	tko[0].optab = arcopts;
	tko[1].ptr = i;
	tko[1].optab = itemopts_carcs;
	tko[2].ptr = nil;
	e = tkparse(tk->env->top, arg, tko, nil);
	if(e != nil) {
		tkcvsfreeitem(i);
		return e;
	}

	e = tkcaddtag(tk, i, 1);
	if(e != nil) {
		tkcvsfreeitem(i);
		return e;
	}

	tkcvsarcsize(i);
	tkmkpen(&a->pen, i->env, a->stipple);

	tkcvsappend(c, i);

	tkbbmax(&c->update, &i->p.bb);
	tkcvssetdirty(tk);
	return tkvalue(val, "%d", i->id);
}

const char*
tkcvsarccget(TkCitem *i, __in_z const char *arg, char **val)
{
	TkOptab tko[3];
	TkCarc *a = TKobj(TkCarc, i);

	tko[0].ptr = a;
	tko[0].optab = arcopts;
	tko[1].ptr = i;
	tko[1].optab = itemopts_carcs;
	tko[2].ptr = nil;

	return tkgencget(tko, arg, val, i->env->top);
}

const char*
tkcvsarcconf(Tk *tk, TkCitem *i, __in_z const char *arg)
{
	const char *e;
	TkOptab tko[3];
	TkCarc *a = TKobj(TkCarc, i);

	tko[0].ptr = a;
	tko[0].optab = arcopts;
	tko[1].ptr = i;
	tko[1].optab = itemopts_carcs;
	tko[2].ptr = nil;

	e = tkparse(tk->env->top, arg, tko, nil);
	tkcvsarcsize(i);
	tkmkpen(&a->pen, i->env, a->stipple);

	return e;
}


void
tkcvsarcfree(TkCitem *i)
{
	TkCarc *a;

	a = TKobj(TkCarc, i);
	if(a->stipple)
		freeimage(a->stipple);
	if(a->pen)
		freeimage(a->pen);
}

void
tkcvsarcdraw(__in_ecount(1) const Image *img, TkCitem *i, TkEnv *pe)
{
	TkEnv *e;
	TkCarc *a;
	Rectangle d;
	int w, dx, dy;
	int s, ext, s0, s1, e0, e1, l;
	Image *pen, *col, *tmp;
	Point p0, p1, c;
	extern void drawarc(Point,int,int,int,int,int,Image *,Image *,Image *);

	USED(pe);

	d.min = i->p.drawpt[0];
	d.max = i->p.drawpt[1];

	e = i->env;
	a = TKobj(TkCarc, i);

	pen = a->pen;
	if(pen == nil && (e->set & (1<<TkCfill)))
		pen = tkgc(e, TkCfill);

	w = TKF2I(a->width)/2;
	if(w < 0)
		return;

	d = canonrect(d);
	dx = Dx(d)/2;
	dy = Dy(d)/2;
	c.x = (d.min.x+d.max.x)/2;
	c.y = (d.min.y+d.max.y)/2;
	s = TKF2I(a->start);
	ext = TKF2I(a->extent);
/*
	if(ext == 0)
		ext = 90;
*/

	if(a->style != Arc && pen != nil)
		fillarc(img, c, dx, dy, pen, Pt(0,0), s, ext);
	col = tkgc(e, TkCforegnd);
	arc(img, c, dx, dy, w, col, Pt(0,0), s, ext);
	if(a->style == Pieslice){
		/*
		 * It is difficult to compute the intersection of the lines
		 * and the ellipse using integers, so let the draw library
		 * do it for us: use a full ellipse as the source of color
		 * for drawing the lines.
		 */
		tmp = allocimage(img->display, d, img->chan, 0, DNofill);
		if(tmp == nil)
			return;
		/* copy dest to tmp so lines don't spill beyond edge of ellipse */
		drawop(tmp, d, img, nil, d.min, S);
		fillellipse(tmp, c, dx, dy, col, Pt(0,0));
		icossin(s, &s1, &s0);
		icossin(s+ext, &e1, &e0);
		if(dx > dy)
			l = 2*dx+1;
		else
			l = 2*dy+1;
		p0 = Pt(c.x+l*s1/ICOSSCALE, c.y-l*s0/ICOSSCALE);
		p1 = Pt(c.x+l*e1/ICOSSCALE, c.y-l*e0/ICOSSCALE);
		line(img, c, p0, Endsquare, Endsquare, w, tmp, c);
		line(img, c, p1, Endsquare, Endsquare, w, tmp, c);
		freeimage(tmp);
	}
}

const char*
tkcvsarccoord(TkCitem *i, __in_z const char *arg, int x, int y)
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
		tkcvsarcsize(i);
	}
	return nil;
}
