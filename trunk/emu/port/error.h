extern char Enoerror[];		/* no error */
extern char Emount[];		/* inconsistent mount */
extern char Eunmount[];		/* not mounted */
extern char Eunion[];		/* not in union */
extern char Emountrpc[];	/* mount rpc error */
extern char Eshutdown[];	/* mounted device shut down */
extern char Eowner[];		/* not owner */
extern char Eunknown[];		/* unknown user or group id */
extern char Enocreate[];	/* mounted directory forbids creation */
extern char Enonexist[];	/* file does not exist */
extern char Eexist[];		/* file already exists */
extern char Ebadsharp[];	/* unknown device in # filename */
extern char Enotdir[];		/* not a directory */
extern char Eisdir[];		/* file is a directory */
extern char Ebadchar[];		/* bad character in file name */
extern char Efilename[];	/* file name syntax */
extern char Eperm[];		/* permission denied */
extern char Ebadusefd[];	/* inappropriate use of fd */
extern char Ebadarg[];		/* bad arg in system call */
extern char Einuse[];		/* device or object already in use */
extern char Eio[];		/* i/o error */
extern char Etoobig[];		/* read or write too large */
extern char Etoosmall[];	/* read or write too small */
extern char Enetaddr[];		/* bad network address */
extern char Emsgsize[];		/* message is too big for protocol */
extern char Enetbusy[];		/* network device is busy or allocated */
extern char Enoproto[];		/* network protocol not supported */
extern char Enoport[];		/* network port not available */
extern char Enoifc[];		/* bad interface or no free interface slots */
extern char Enolisten[];	/* not announced */
extern char Ehungup[];		/* i/o on hungup channel */
extern char Ebadctl[];		/* bad process or channel control request */
extern char Enodev[];		/* no free devices */
extern char Enoenv[];		/* no free environment resources */
extern char Ethread[];		/* thread exited */
extern char Enochild[];		/* no living children */
extern char Eioload[];		/* i/o error in demand load */
extern char Enovmem[];		/* out of memory: virtual memory */
extern char Ebadld[];		/* illegal line discipline */
extern char Ebadfd[];		/* fd out of range or not open */
extern char Eisstream[];	/* seek on a stream */
extern char Ebadexec[];		/* exec header invalid */
extern char Etimedout[];	/* connection timed out */
extern char Econrefused[];	/* connection refused */
extern char Econinuse[];	/* connection in use */
extern char Enetunreach[];	/* network unreachable */
extern char Eintr[];		/* interrupted */
extern char Enomem[];		/* out of memory: kernel */
extern char Esfnotcached[];	/* subfont not cached */
extern char Esoverlap[];	/* segments overlap */
extern char Emouseset[];	/* mouse type already set */
extern char Eshort[];		/* i/o count too small */
extern char Enobitstore[];	/* out of screen memory */
extern char Egreg[];		/* jim'll fix it */
extern char Ebadspec[];		/* bad attach specifier */
extern char Estopped[];		/* thread must be stopped */
extern char Enoattach[];	/* mount/attach disallowed */
extern char Eshortstat[];	/* stat buffer too small */
extern char Enegoff[];	/* negative i/o offset */
extern char Ebadstat[];	/* malformed stat buffer */
extern char Ecmdargs[];		/* wrong #args in control message */
extern char	Enofd[];	/* no free file descriptors */
extern char Enoctl[];	/* unknown control request */

#if !defined(NORETURN)
#define NORETURN void
#endif
extern NORETURN	error(const char*);
