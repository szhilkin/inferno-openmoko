#include <dat.h>
#include <fns.h>
#include <error.h>
#include <isa.h>
#include <interp.h>


#include "emu.root.h"

ulong ndevs = 29;

extern Dev rootdevtab;
extern Dev consdevtab;
extern Dev envdevtab;
extern Dev mntdevtab;
extern Dev pipedevtab;
extern Dev progdevtab;
extern Dev srvdevtab;
extern Dev dupdevtab;
extern Dev ssldevtab;
extern Dev capdevtab;
extern Dev fsdevtab;
extern Dev cmddevtab;
extern Dev indirdevtab;
extern Dev drawdevtab;
extern Dev ipdevtab;
extern Dev eiadevtab;
extern Dev audiodevtab;
extern Dev memdevtab;
extern Dev archdevtab;
extern Dev pointerdevtab;
extern Dev snarfdevtab;
Dev* devtab[]={
    &rootdevtab,
    &consdevtab,
    &envdevtab,
    &mntdevtab,
    &pipedevtab,
    &progdevtab,
    &srvdevtab,
    &dupdevtab,
    &ssldevtab,
    &capdevtab,
    &fsdevtab,
    &cmddevtab,
    &indirdevtab,
    &drawdevtab,
    &ipdevtab,
    &eiadevtab,
    &audiodevtab,
    &memdevtab,
    &archdevtab,
    &pointerdevtab,
    &snarfdevtab,
    nil,
    nil,
    nil,
    nil,
    nil,
    nil,
    nil,
    nil,
    nil,
};

void links(void){
}

extern void sysmodinit(void);
extern void drawmodinit(void);
extern void tkmodinit(void);
extern void mathmodinit(void);
extern void srvmodinit(void);
extern void keyringmodinit(void);
extern void loadermodinit(void);
extern void freetypemodinit(void);
void modinit(void){
    sysmodinit();
    drawmodinit();
    tkmodinit();
    mathmodinit();
    srvmodinit();
    keyringmodinit();
    loadermodinit();
    freetypemodinit();
}

char* conffile = "emu";
ulong kerndate = KERNDATE;
