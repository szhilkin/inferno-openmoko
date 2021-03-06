#include <lib9.h>
#include <isa.h>
#include <interp.h>
#include <raise.h>
#include <kernel.h>
#ifdef _MSC_VER
#include <malloc.h> // alloca
#endif

#define A(r)    *((Array**)(r))

Module* modules = 0;
int dontcompile = 0;

static int
operand(const char **p)
{
    int c;
    const char *cp;

    cp = *p;
    c = GBIT8I(cp,0);
    switch(c & 0xC0) {
    case 0x00:
        *p = cp+1;
        return c;
    case 0x40:
        *p = cp+1;
        return c|~0x7F;
    case 0x80:
        *p = cp+2;
        if(c & 0x20)
            c |= ~0x3F;
        else
            c &= 0x3F;
        return (c<<8) | GBIT8I(cp,1);
    case 0xC0:
        *p = cp+4;
        if(c & 0x20)
            c |= ~0x3F;
        else
            c &= 0x3F;
        return (c<<24) | (GBIT8I(cp,1)<<16) | (GBIT8I(cp,2)<<8) | GBIT8I(cp,3);
    }
    return 0;
}

static ulong
disw(const char **p)
{
    const char *c = *p;
    ulong v = GBIT32BE(c);
    *p = c + 4;
    return v;
}

double
canontod(ulong v[2])
{
    union { double d; unsigned long ul[2]; } a;
    a.d = 1.;
    if(a.ul[0]) {
        a.ul[0] = v[0];
        a.ul[1] = v[1];
    }
    else {
        a.ul[1] = v[0];
        a.ul[0] = v[1];
    }
    return a.d;
}

Module*
load(char *path)
{
    return readmod(path, nil, 0);
}

/**
 * Type constructor
 */
Type*
dtype(void (*destructor)(Heap*, int), int size, const char *map, int mapsize, const char*comment)
{
    Type *t;

    t = (Type *)malloc(sizeof(Type)+mapsize);
    if(t != nil) {
        t->ref = 1;
        t->destructor = destructor;
        t->fnmark = markheap;
        t->size = size;
        t->np = mapsize;
        t->comment = comment;
        memcpy(t->map, map, mapsize);
    }
    return t;
}

int
brpatch(Inst *ip, Module *m)
{
    switch(ip->op) {
    case ICALL:
    case IJMP:
    case IBEQW:
    case IBNEW:
    case IBLTW:
    case IBLEW:
    case IBGTW:
    case IBGEW:
    case IBEQB:
    case IBNEB:
    case IBLTB:
    case IBLEB:
    case IBGTB:
    case IBGEB:
    case IBEQF:
    case IBNEF:
    case IBLTF:
    case IBLEF:
    case IBGTF:
    case IBGEF:
    case IBEQC:
    case IBNEC:
    case IBLTC:
    case IBLEC:
    case IBGTC:
    case IBGEC:
    case IBEQL:
    case IBNEL:
    case IBLTL:
    case IBLEL:
    case IBGTL:
    case IBGEL:
    case ISPAWN:
        if(ip->d.imm < 0 || ip->d.imm >= m->nprog)
            return 0;
        ip->d.imm = (DISINT)&m->prog[ip->d.imm]; /* DIXME: int/ptr cast */
        break;
    }
    return 1;
}

void frame_type_fix(Type* t) // TODO: must be done by limbo
{
        if(t->np==0) {t->np=1; t->map[0]=0;}
        t->map[0] |= 0x40; /* parent */
        t->map[0] |= 0x20; /* ml */
}

Module*
parsemod(const char *path, const char *code, ulong length, const Dir *dir)
{
    Heap *h;
    Inst *ip;
    Type *pt;
    String *s;
    Module *m;
    Array *ary;
    ulong ul[2];
    DISINT lo, hi;
    int lsize, id, v, entry, entryt, tnp, tsz, siglen;
    int de, pc, i, n, isize, dsize, hsize, dasp;
    const char *mod, *istream, **isp;
    char sm, *si, *addr, *dastack[DADEPTH];
    Link *l;
    char* frames;

    istream = code;
    isp = &istream;

    m = (Module*)malloc(sizeof(Module));
    if(m == nil)
        return nil;

    m->dev = dir->dev;
    m->dtype = dir->type;
    m->qid = dir->qid;
    m->mtime = dir->mtime;
    m->origmp = (char*)H;
    m->pctab = nil;

    switch(operand(isp)) {
    default:
        kwerrstr("bad magic");
        goto bad;
    case SMAGIC:
        siglen = operand(isp);
        n = length-(*isp-code);
        if(n < 0 || siglen > n){
            kwerrstr("corrupt signature");
            goto bad;
        }
        if(verifysigner(*isp, siglen, *isp+siglen, n-siglen) == 0) {
            kwerrstr("security violation");
            goto bad;
        }
        *isp += siglen;
        break;
    case XMAGIC:
        if(mustbesigned(path, code, length, dir)){
            kwerrstr("security violation: not signed");
            goto bad;
        }
        break;
    }

    m->rt = (enum ModRtFlags)operand(isp); // Runtime flags
    /*m->ss =*/ operand(isp); // stack size (deprecated)
    isize = operand(isp);   // code size (number of Dis instructions)
    dsize = operand(isp);
    hsize = operand(isp);   // number of types (adt and frames)
    lsize = operand(isp);   // number of links (exports)
    entry = operand(isp);   // entry point offset
    entryt= operand(isp);   // frame type for entry point function (-1 otherwise)

    if(isize < 0 || dsize < 0 || hsize < 0 || lsize < 0) {
        kwerrstr("implausible Dis file");
        goto bad;
    }

    frames = alloca(hsize*sizeof(char));
    memset(frames, 0, hsize*sizeof(char));

    m->nprog = isize;
    m->prog = (Inst*)mallocz(isize*sizeof(Inst), 0);
    if(m->prog == nil) {
        kwerrstr(exNomem);
        goto bad;
    }

    m->ref = 1;

    ip = m->prog;
    for(i = 0; i < isize; i++) {
        ip->op = *istream++;
        ip->add = *istream++;
        ip->reg = 0;
        ip->s.imm = 0;
        ip->d.imm = 0;
        switch(ip->add & ARM) {
        case AXIMM:
        case AXINF:
        case AXINM:
            ip->reg = operand(isp);
            break;
        }
        switch(UXSRC(ip->add)) {
        case SRC(AFP):
        case SRC(AMP):
        case SRC(AIMM):
            ip->s.ind = operand(isp);
            break;
        case SRC(AIND|AFP):
        case SRC(AIND|AMP):
            ip->s.i.f = operand(isp);
            ip->s.i.s = operand(isp);
            break;
        }
        switch(UXDST(ip->add)) {
        case DST(AFP):
        case DST(AMP):
            ip->d.ind = operand(isp);
            break;
        case DST(AIMM):
            ip->d.ind = operand(isp);
            if(brpatch(ip, m) == 0) {
                kwerrstr("bad branch addr");
                goto bad;
            }
            break;
        case DST(AIND|AFP):
        case DST(AIND|AMP):
            ip->d.i.f = operand(isp);
            ip->d.i.s = operand(isp);
            break;
        }
        if(ip->op==IFRAME)
        {
             assert(UXSRC(ip->add)==SRC(AIMM)); /* TODO: do not rely on it, split frame and adt types */
             assert((unsigned)ip->s.ind < hsize);
             frames[ip->s.ind] = 1;
        }
        ip++;
    }

    m->ntype = hsize;
    m->type = (Type**)malloc(hsize*sizeof(Type*));
    if(m->type == nil) {
        kwerrstr(exNomem);
        goto bad;
    }
    for(i = 0; i < hsize; i++) {
//        char *comment = (char *)HeapAlloc(GetProcessHeap(),0,256); /* TODO: debug, remove later */
//        char* comment = malloc(256);
        char* comment = "?";
//        sprint(comment, "%s.%d", path, i);
        id = operand(isp);
        assert(i==id); //?

        if(id > hsize) {
            kwerrstr("heap id range");
            goto bad;
        }
        tsz = operand(isp);
        tnp = operand(isp);
        if(tsz < 0 || tnp < 0 || tnp > 128*1024){
            kwerrstr("implausible Dis file");
            goto bad;
        }
        pt = dtype(freeheap, tsz, istream, tnp, comment);
        if(pt == nil) {
            kwerrstr(exNomem);
            goto bad;
        }
        istream += tnp;
        m->type[id] = pt;


        if(frames[id])
        {
            if(dsize != 0) {
                assert(id!=0); // type[0] was used for origmp
            }
            frame_type_fix(pt);
        }
    }
    if(entryt>=0)
    {
        if(dsize != 0) {
             assert(entryt!=0); // type[0] was used for origmp
        }
        frame_type_fix(m->type[entryt]);
    }

    if(dsize != 0) {
        pt = m->type[0];
        if(pt == 0 || pt->size != dsize) {
            kwerrstr("bad desc for mp");
            goto bad;
        }
        h = heapz(pt);
        m->origmp = H2D(char*, h);
    }
    addr = m->origmp;
    dasp = 0;
    for(;;) {
        sm = *istream++;
        if(sm == 0)
            break;
        n = DLEN(sm);
        if(n == 0)
            n = operand(isp);
        v = operand(isp);
        si = addr + v;
        switch(DTYPE(sm)) {
        default:
            kwerrstr("bad data item");
            goto bad;
        case DEFS:
            s = c2string(istream, n);
            istream += n;
            *(String**)si = s;
            break;
        case DEFB:
            for(i = 0; i < n; i++)
                *si++ = *istream++;
            break;
        case DEFW:
            for(i = 0; i < n; i++) {
                *(DISINT*)si = disw(isp);
                si += sizeof(DISINT);
            }
            break;
        case DEFL:
            for(i = 0; i < n; i++) {
                hi = disw(isp);
                lo = disw(isp);
                *(DISBIG*)si = (DISBIG)hi << 32 | (DISBIG)(ulong)lo;
                si += sizeof(DISBIG);
            }
            break;
        case DEFF:
            for(i = 0; i < n; i++) {
                ul[0] = disw(isp);
                ul[1] = disw(isp);
                *(DISREAL*)si = canontod(ul);
                si += sizeof(DISREAL);
            }
            break;
        case DEFA:          /* Array */
            v = disw(isp);
            if(v < 0 || v > m->ntype) {
                kwerrstr("bad array type");
                goto bad;
            }
            pt = m->type[v];
            v = disw(isp);
            h = nheap(sizeof(Array)+(pt->size*v));
            h->t = &Tarray;
            h->t->ref++;
            ary = H2D(Array*, h);
            ary->t = pt;
            ary->len = v;
            ary->root = (Array*)H;
            ary->data = (char*)ary+sizeof(Array);
            memset(ary->data, 0, pt->size*v);
            initarray(pt, ary);
            A(si) = ary;
            break;
        case DIND:          /* Set index */
            ary = A(si);
            if(ary == H || D2H(ary)->t != &Tarray) {
                kwerrstr("ind not array");
                goto bad;
            }
            v = disw(isp);
            if(v > ary->len || v < 0 || dasp >= DADEPTH) {
                kwerrstr("array init range");
                goto bad;
            }
            dastack[dasp++] = addr;
            addr = ary->data+v*ary->t->size;
            break;
        case DAPOP:
            if(dasp == 0) {
                kwerrstr("pop range");
                goto bad;
            }
            addr = dastack[--dasp];
            break;
        }
    }
    mod = istream;
    if(memchr(mod, 0, 128) == 0) {
        kwerrstr("bad module name");
        goto bad;
    }
    m->name = strdup(mod);
    if(m->name == nil) {
        kwerrstr(exNomem);
        goto bad;
    }
    while(*istream++)
        ;

    l = m->ext = (Link*)malloc((lsize+1)*sizeof(Link));
    if (l == nil) {
        kwerrstr(exNomem);
        goto bad;
    }
    for(i = 0; i < lsize; i++, l++) {
        pc = operand(isp);
        de = operand(isp);
        v  = disw(isp);
        pt = nil;
        if(de != -1) {
            pt = m->type[de]; // frame type for link

            if(dsize != 0) {
                assert(de!=0); // type[0] was used for origmp
            }
            frame_type_fix(pt);
        }
        mlink(m, l, istream, v, pc, pt);
        while(*istream++)
            ;
    }
    l->name = nil;

    if(m->rt & HASLDT0){
        kwerrstr("obsolete dis");
        goto bad;
    }

    if(m->rt & HASLDT){
        int j, nl;
        Import *i1, **i2;

        nl = operand(isp);
        i2 = m->ldt = (Import**)malloc((nl+1)*sizeof(Import*));
        if(i2 == nil){
            kwerrstr(exNomem);
            goto bad;
        }
        for(i = 0; i < nl; i++, i2++){
            n = operand(isp);
            i1 = *i2 = (Import*)malloc((n+1)*sizeof(Import));
            if(i1 == nil){
                kwerrstr(exNomem);
                goto bad;
            }
            for(j = 0; j < n; j++, i1++){
                i1->sig = disw(isp);
                i1->name = strdup((char*)istream);
                if(i1->name == nil){
                    kwerrstr(exNomem);
                    goto bad;
                }
                while(*istream++)
                    ;
            }
        }
        istream++;
    }

    if(m->rt & HASEXCEPT){
        int j, nh;
        Handler *h;
        Except *e;

        nh = operand(isp);
        m->htab = (Handler*)malloc((nh+1)*sizeof(Handler));
        if(m->htab == nil){
            kwerrstr(exNomem);
            goto bad;
        }
        h = m->htab;
        for(i = 0; i < nh; i++, h++){
            h->eoff = operand(isp);
            h->pc1 = operand(isp);
            h->pc2 = operand(isp);
            n = operand(isp);
            if(n != -1)
                h->t = m->type[n];
            n = operand(isp);
            h->ne = n>>16;
            n &= 0xffff;
            h->etab = (Except*)malloc((n+1)*sizeof(Except));
            if(h->etab == nil){
                kwerrstr(exNomem);
                goto bad;
            }
            e = h->etab;
            for(j = 0; j < n; j++, e++){
                e->s = strdup((char*)istream);
                if(e->s == nil){
                    kwerrstr(exNomem);
                    goto bad;
                }
                while(*istream++)
                    ;
                e->pc = operand(isp);
            }
            e->s = nil;
            e->pc = operand(isp);
        }
        istream++;
    }

    m->entryt = nil;
    m->entry = m->prog;
    if((ulong)entry < isize && (ulong)entryt < hsize) {
        m->entry = &m->prog[entry];
        m->entryt = m->type[entryt];
    }
#if JIT
    if (cflag) {
        if((m->rt&DONTCOMPILE) == 0 && !dontcompile)
            compile(m, isize, nil);
    }
    else
    if(m->rt & MUSTCOMPILE && !dontcompile) {
        if (compile(m, isize, nil) == 0) {
            kwerrstr("compiler required");
            goto bad;
        }
    }
#endif
    m->path = strdup(path);
    if(m->path == nil) {
        kwerrstr(exNomem);
        goto bad;
    }
    m->link = modules;
    modules = m;

    return m;
bad:
    ASSIGN(m->origmp, H);
    freemod(m);
    return nil;
}

Module*
newmod(const char *s)
{
    Module *m;

    m = (Module *)malloc(sizeof(Module));
    if(m == nil)
        error(exNomem);
    m->ref = 1;
    m->path = s;
    m->origmp = (char*)H;
    m->name = strdup(s);
    if(m->name == nil) {
        free(m);
        error(exNomem);
    }
    m->link = modules;
    modules = m;
    m->pctab = nil;
    return m;
}

/**
 * Find module by path, increment ref if found
 */
Module*
lookmod(char *s)
{
    Module *m;

    for(m = modules; m != nil; m = m->link)
        if(strcmp(s, m->path) == 0) {
            m->ref++;
            return m;
        }
    return nil;
}

void
freemod(Module *m)
{
    int i;
    Handler *h;
    Except *e;
    Import *i1, **i2;

    if(m->type != nil) {
        for(i = 0; i < m->ntype; i++)
            freetype(m->type[i]);
        free(m->type);
    }
    free(m->name); /* XXX: unconst */
    free(m->prog);
    free(m->path); /* XXX: unconst */
    free(m->pctab);
    if(m->ldt != nil){
        for(i2 = m->ldt; *i2 != nil; i2++){
            for(i1 = *i2; i1->name != nil; i1++)
                free(i1->name);
            free(*i2);
        }
        free(m->ldt);
    }
    if(m->htab != nil){
        for(h = m->htab; h->etab != nil; h++){
            for(e = h->etab; e->s != nil; e++)
                free(e->s);
            free(h->etab);
        }
        free(m->htab);
    }
    free(m);
}

void
unload(Module *m)
{
    Module **last, *mm;

    m->ref--;
    if(m->ref > 0)
        return;
    if(m->ref == -1)
        panic("unload ref==-1");

    last = &modules;
    for(mm = modules; mm != nil; mm = mm->link) {
        if(mm == m) {
            *last = m->link;
            break;
        }
        last = &mm->link;
    }

    if(m->rt == DYNMOD)
        freedyncode(m);
    else
        ASSIGN(m->origmp, H);

    destroylinks(m);

    freemod(m);
}
