#include <dat.h>
#include <fns.h>
#include <error.h>
#include <ip.h>

/*
 *  well known IP addresses
 */
uchar IPv4bcast[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff
};
uchar IPv4allsys[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0xff, 0xff,
	0xe0, 0, 0, 0x01
};
uchar IPv4allrouter[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0xff, 0xff,
	0xe0, 0, 0, 0x02
};
uchar IPallbits[IPaddrlen] = {
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff
};

uchar IPnoaddr[IPaddrlen];

/*
 *  prefix of all v4 addresses
 */
uchar v4prefix[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0xff, 0xff,
	0, 0, 0, 0
};

/*
 *  well known IPv6 addresses
 */
uchar v6Unspecified[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0
};
uchar v6loopback[IPaddrlen] = {
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0x01
};
uchar v6linklocal[IPaddrlen] = {
	0xfe, 0x80, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0
};
uchar v6linklocalmask[IPaddrlen] = {
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff,
	0, 0, 0, 0,
	0, 0, 0, 0
};
int v6linklocalprefix = 8;
uchar v6sitelocal[IPaddrlen] = {
	0xfe, 0xc0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0
};
uchar v6sitelocalmask[IPaddrlen] = {
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff,
	0, 0, 0, 0,
	0, 0, 0, 0
};
int v6sitelocalprefix = 6;
uchar v6glunicast[IPaddrlen] = {
	0x08, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0
};
uchar v6multicast[IPaddrlen] = {
	0xff, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0
};
uchar v6multicastmask[IPaddrlen] = {
	0xff, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0
};
int v6multicastprefix = 1;
uchar v6allnodesN[IPaddrlen] = {
	0xff, 0x01, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0x01
};
uchar v6allnodesNmask[IPaddrlen] = {
	0xff, 0xff, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0
};
int v6allnodesprefix = 2;
uchar v6allnodesL[IPaddrlen] = {
	0xff, 0x02, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0x01
};
uchar v6allnodesLmask[IPaddrlen] = {
	0xff, 0xff, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0
};
int v6allnodesLprefix = 2;
uchar v6allroutersN[IPaddrlen] = {
	0xff, 0x01, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0x02
};
uchar v6allroutersL[IPaddrlen] = {
	0xff, 0x02, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0x02
};
uchar v6allroutersS[IPaddrlen] = {
	0xff, 0x05, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0x02
};
uchar v6solicitednode[IPaddrlen] = {
	0xff, 0x02, 0, 0,
	0, 0, 0, 0,
	0, 0, 0, 0x01,
	0xff, 0, 0, 0
};
uchar v6solicitednodemask[IPaddrlen] = {
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff,
	0xff, 0xff, 0xff, 0xff,
	0xff, 0x0, 0x0, 0x0
};
int v6solicitednodeprefix = 13;

enum
{
	Isprefix= 16,
};

int
eipfmt(Fmt *f)
{
	char buf[5*8];
	static char *efmt = "%.2lux%.2lux%.2lux%.2lux%.2lux%.2lux";
	static char *ifmt = "%d.%d.%d.%d";
	uchar *p, ip[16];
	ulong *lp;
	ushort s;
	int i, j, n, eln, eli, m, v;

	switch(f->r) {
	case 'E':		/* Ethernet address */
		p = va_arg(f->args, uchar*);
		return fmtprint(f, efmt, p[0], p[1], p[2], p[3], p[4], p[5]);
	case 'I':		/* Ip address */
		p = va_arg(f->args, uchar*);
common:
		if(memcmp(p, v4prefix, 12) == 0)
			return fmtprint(f, ifmt, p[12], p[13], p[14], p[15]);

		/* find longest elision */
		eln = eli = -1;
		for(i = 0; i < 16; i += 2){
			for(j = i; j < 16; j += 2)
				if(p[j] != 0 || p[j+1] != 0)
					break;
			if(j > i && j - i > eln){
				eli = i;
				eln = j - i;
			}
		}

		/* print with possible elision */
		n = 0;
		for(i = 0; i < 16; i += 2){
			if(i == eli){
				n += sprint(buf+n, "::");
				i += eln;
				if(i >= 16)
					break;
			} else if(i != 0)
				n += sprint(buf+n, ":");
			s = (p[i]<<8) + p[i+1];
			n += sprint(buf+n, "%ux", s);
		}
		return fmtstrcpy(f, buf);

	case 'i':		/* v6 address as 4 longs */
		lp = va_arg(f->args, ulong*);
		PBIT32BE(ip+0, lp[0]);
        PBIT32BE(ip+4, lp[1]);
        PBIT32BE(ip+8, lp[2]);
        PBIT32BE(ip+12, lp[3]);
		p = ip;
		goto common;

	case 'V':		/* v4 ip address */
		p = va_arg(f->args, uchar*);
		return fmtprint(f, ifmt, p[0], p[1], p[2], p[3]);

	case 'M':		/* ip mask */
		p = va_arg(f->args, uchar*);

		/* look for a prefix mask */
		for(i = 0; i < 16; i++)
			if(p[i] != 0xff)
				break;
		for(j = i+1; j < 16; j++)
			if(p[j] != 0)
				goto common;
		n = 8*i;
		if(i < IPaddrlen){
			v = p[i];
			for(m = 0x80; m != 0; m >>= 1){
				if((v & m) == 0)
					break;
				v &= ~m;
				n++;
			}
			if(v != 0)
				goto common;
		}

		/* got one, use /xx format */
		return fmtprint(f, "/%d", n);

	}
	return fmtstrcpy(f, "(eipfmt)");
}

#define CLASS(p) ((*(uchar*)(p))>>6)

const char*
v4parseip(uchar to[4], const char *from)
{
	int i;
	const char *p;

	p = from;
	for(i = 0; i < 4 && *p; i++){
		to[i] = strtoul(p, (char**)&p, 0);
		if(*p == '.')
			p++;
	}
	switch(CLASS(to)){
	case 0:	/* class A - 1 uchar net */
	case 1:
		if(i == 3){
			to[3] = to[2];
			to[2] = to[1];
			to[1] = 0;
		} else if(i == 2){
			to[3] = to[1];
			to[1] = 0;
		}
		break;
	case 2:	/* class B - 2 uchar net */
		if(i == 3){
			to[3] = to[2];
			to[2] = 0;
		}
		break;
	}
	return p;
}

int
isv4(const uchar ip[16])
{
	return memcmp(ip, v4prefix, IPv4off) == 0;
}


/*
 *  the following routines are unrolled with no memset's to speed
 *  up the usual case
 */
void
v4tov6(uchar v6[16], const uchar v4[4])
{
	v6[0] = 0;
	v6[1] = 0;
	v6[2] = 0;
	v6[3] = 0;
	v6[4] = 0;
	v6[5] = 0;
	v6[6] = 0;
	v6[7] = 0;
	v6[8] = 0;
	v6[9] = 0;
	v6[10] = 0xff;
	v6[11] = 0xff;
	v6[12] = v4[0];
	v6[13] = v4[1];
	v6[14] = v4[2];
	v6[15] = v4[3];
}

int
v6tov4(uchar v4[4], const uchar v6[16])
{
	if(v6[0] == 0
	&& v6[1] == 0
	&& v6[2] == 0
	&& v6[3] == 0
	&& v6[4] == 0
	&& v6[5] == 0
	&& v6[6] == 0
	&& v6[7] == 0
	&& v6[8] == 0
	&& v6[9] == 0
	&& v6[10] == 0xff
	&& v6[11] == 0xff)
	{
		v4[0] = v6[12];
		v4[1] = v6[13];
		v4[2] = v6[14];
		v4[3] = v6[15];
		return 0;
	} else {
		memset(v4, 0, 4);
		return -1;
	}
}

ulong
parseip(uchar to[16], const char *from)
{
	int i, elipsis = 0, v4 = 1;
	ulong x;
	const char *p, *op;

	memset(to, 0, IPaddrlen);
	p = from;
	for(i = 0; i < 16 && *p; i+=2){
		op = p;
		x = strtoul(p, (char**)&p, 16);
		if(*p == '.' || (*p == 0 && i == 0)){
			p = v4parseip(to+i, op);
			i += 4;
			break;
		} else {
			to[i] = x>>8;
			to[i+1] = x;
		}
		if(*p == ':'){
			v4 = 0;
			if(*++p == ':'){
				elipsis = i+2;
				p++;
			}
		}
	}
	if(i < 16){
		memmove(&to[elipsis+16-i], &to[elipsis], i-elipsis);
		memset(&to[elipsis], 0, 16-i);
	}
	if(v4){
		to[10] = to[11] = 0xff;
		return GBIT32BE(to+12);
	} else
		return 6; /* FIXME: not a good magic */
}

/*
 *  hack to allow ip v4 masks to be entered in the old
 *  style
 */
ulong
parseipmask(uchar *to, const char *from)
{
	ulong x;
	int i;
	uchar *p;

	if(*from == '/'){
		/* as a number of prefix bits */
		i = atoi(from+1);
		if(i < 0)
			i = 0;
		if(i > 128)
			i = 128;
		memset(to, 0, IPaddrlen);
		for(p = to; i >= 8; i -= 8)
			*p++ = 0xff;
		if(i > 0)
			*p = ~((1<<(8-i))-1);
		x = GBIT32BE(to+IPv4off);
	} else {
		/* as a straight bit mask */
		x = parseip(to, from);
		if(memcmp(to, v4prefix, IPv4off) == 0)
			memset(to, 0xff, IPv4off);
	}
	return x;
}

void
maskip(const uchar *from, const uchar *mask, uchar *to)
{
	int i;

	for(i = 0; i < IPaddrlen; i++)
		to[i] = from[i] & mask[i];
}

uchar classmask[4][16] = {
	0xff,0xff,0xff,0xff,  0xff,0xff,0xff,0xff,  0xff,0xff,0xff,0xff,  0xff,0x00,0x00,0x00,
	0xff,0xff,0xff,0xff,  0xff,0xff,0xff,0xff,  0xff,0xff,0xff,0xff,  0xff,0x00,0x00,0x00,
	0xff,0xff,0xff,0xff,  0xff,0xff,0xff,0xff,  0xff,0xff,0xff,0xff,  0xff,0xff,0x00,0x00,
	0xff,0xff,0xff,0xff,  0xff,0xff,0xff,0xff,  0xff,0xff,0xff,0xff,  0xff,0xff,0xff,0x00,
};

uchar*
defmask(uchar *ip)
{
	if(isv4(ip))
		return classmask[ip[IPv4off]>>6];
	else {
		if(ipcmp(ip, v6loopback) == 0)
			return IPallbits;
		else if(memcmp(ip, v6linklocal, v6linklocalprefix) == 0)
			return v6linklocalmask;
		else if(memcmp(ip, v6sitelocal, v6sitelocalprefix) == 0)
			return v6sitelocalmask;
		else if(memcmp(ip, v6solicitednode, v6solicitednodeprefix) == 0)
			return v6solicitednodemask;
		else if(memcmp(ip, v6multicast, v6multicastprefix) == 0)
			return v6multicastmask;
		return IPallbits;
	}
}

/*
 *  parse a hex mac address
 */
size_t
parsemac(uchar *to, const char *from, size_t len)
{
	char nip[4];
	const char *p;
	int i;

	p = from;
	memset(to, 0, len);
	for(i = 0; i < len; i++){
		if(p[0] == '\0' || p[1] == '\0')
			break;

		nip[0] = p[0];
		nip[1] = p[1];
		nip[2] = '\0';
		p += 2;

		to[i] = strtoul(nip, 0, 16);
		if(*p == ':')
			p++;
	}
	return i;
}
