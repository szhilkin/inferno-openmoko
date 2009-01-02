#include "dat.h"
#include "fns.h"
#include "error.h"
#include "interp.h"
#include "isa.h"
#include "runt.h"
#include "kernel.h"
#include "raise.h"

static int
ematch(char *pat, char *exp)
{
        int l;

        if(strcmp(pat, exp) == 0)
                return 1;

        l = strlen(pat);
        if(l == 0)
                return 0;
        if(pat[l-1] == '*') {
                if(l == 1)
                        return 1;
                if(strncmp(pat, exp, l-1) == 0)
                        return 1;
        }
        return 0;
}

static void
setstr(String *s, char *p)
{
        if(s == H)
                return;
        if(s->len < 0 || s->max < 4)
                return;
        kstrcpy(s->Sascii, p, s->max);  /* TO DO: we are assuming they aren't runes */
        s->len = strlen(s->Sascii);
}

static String *exstr;

void
excinit(void)
{
        exstr = newstring(ERRMAX);
        poolimmutable(D2H(exstr));
}

static String*
newestring(char *estr)
{
        String *s;

        if(waserror()){
                setstr(exstr, estr);
                D2H(exstr)->ref++;
                return exstr;
        }
        s = c2string(estr, strlen(estr));
        poperror();
        return s;
}

#define NOPC    0xffffffff

#if STACK
#define FRTYPE(f)       ((f)->t == nil ? SEXTYPE(f)->reg.TR : (f)->t)
#endif

/*
 * clear up an uncalled frame
 */
#if STACK
static void
freeframe(uchar *fp, int setsp)
{
        Frame *f;

        f = (Frame*)fp;
        if(f->t == nil)
                unextend(f);
        else if(f->t->np)
                freeptrs(f, f->t);
        if(setsp)
                R.SP = fp;
}
#endif

int
handler(char *estr)
{
        Prog *p;
        Modlink *m, *mr;
        int str, ne;
        ulong pc, newpc;
        long eoff;
        uchar **eadr;
        Frame *fp, *f;
        Type *t, *zt;
        Handler *h;
        Except *e;
        void *v;

        p = currun();

        print("handler:");
        print(" |%s|%p %d\n", estr, p, p?p->pid:0);

        if(*estr == 0 || p == nil)
                return 0;
        str = p->exval == H || D2H(p->exval)->t == &Tstring;
        m = R.M;
        if(m->compiled)
                pc = (ulong)R.PC-(ulong)m->prog;
        else
                pc = R.PC-m->prog;
        pc--;

        for(fp = R.FP; fp != H; fp = fp->parent) {              /* look for a handler */
                if((h = m->m->htab) != nil){
                        for( ; h->etab != nil; h++){
                                if(pc < h->pc1 || pc >= h->pc2)
                                        continue;
                                eoff = h->eoff;
                                zt = h->t;
                                for(e = h->etab, ne = h->ne; e->s != nil; e++, ne--){
                                        if(ematch(e->s, estr) && (str && ne <= 0 || !str && ne > 0)){
                                                newpc = e->pc;
                                                goto found;
                                        }
                                }
                                newpc = e->pc;
                                if(newpc != NOPC)
                                        goto found;
                        }
                }
                if(!str && fp != R.FP){         /* becomes a string exception in immediate caller */
                        v = p->exval;
                        p->exval = *(String**)v;
                        D2H(p->exval)->ref++;
                        destroy(v);
                        str = 1;
                        continue;
                }
                assert(fp->mr != nil);
                if(fp->mr != H)
                        m = fp->mr;
                if(m->compiled)
                        pc = (ulong)fp->lr-(ulong)m->prog;
                else
                        pc = fp->lr-m->prog;
                pc--;
        }
        destroy(p->exval);
        p->exval = H;
        return 0;
found:
        {
                int n;
                char name[3*KNAMELEN];

                pc = modstatus(&R, name, sizeof(name));
                n = 10+1+strlen(name)+1+strlen(estr)+1;
                p->exstr = realloc(p->exstr, n);
                if(p->exstr != nil)
                        snprint(p->exstr, n, "%lud %s %s", pc, name, estr);
        }

        /*
         * there may be an uncalled frame at the top of the stack
         */
        f = (Frame*)R.FP;
#if STACK
        t = FRTYPE(f);
        if(R.FP < R.EX || R.FP >= R.TS)
                freeframe(R.EX+OA(Stkext, reg.tos.fr), 0);
        else if(R.FP+t->size < R.SP)
                freeframe(R.FP+t->size, 1);
#else
        //printf("achtung: uncalled frame\n");
#endif
        m = R.M;
        while(R.FP != fp){
                f = (Frame*)R.FP;
                R.PC = f->lr;
                R.FP = f->parent;
#if STACK
                R.SP = (uchar*)f;
#endif
                mr = f->mr;
                assert(mr != nil);
#if STACK
                if(f->t == nil)
                        unextend(f);
                else if(f->t->np)
                        freeptrs(f, f->t);
#else
// can be simplified, with no loop
                if(f->mr!=H)
                        D2H(f->mr)->ref++;
                D2H(f->parent)->ref++;
                destroy(f);
#endif
                if(mr != H){
                        m = mr;
                        destroy(R.M);
                        R.M = m;
                        R.MP = m->MP;
                }
        }
        if(zt != nil){
                freeptrs(fp, zt);
                initmem(zt, fp);
        }
        eadr = (uchar**)((char*)fp+eoff);
        destroy(*eadr);
        *eadr = H;
        if(p->exval == H)
                *eadr = (uchar*)newestring(estr);       /* might fail */
        else{
                D2H(p->exval)->ref++;
                *eadr = p->exval;
        }
        if(m->compiled)
                R.PC = (Inst*)((ulong)m->prog+newpc);
        else
                R.PC = m->prog+newpc;
        memmove(&p->R, &R, sizeof(R));
        p->kill = nil;
        destroy(p->exval);
        p->exval = H;
        return 1;
}
