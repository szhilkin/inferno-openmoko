typedef struct Chan Chan;
extern	vlong	libseek(int, vlong, int);
extern	int	libread(int, void*, int);
extern	int	libreadn(int, void*, long);
extern	int	libwrite(int, void*, int);
extern	int	libopen(char*, int);
extern	int	libclose(int);
extern	Dir*	libdirfstat(int);
extern	int	libbind(char*, char*, int);
extern	QLock*	libqlalloc(void);
extern	void	libqlfree(QLock *q);
extern	void	libqlock(QLock *q);
extern	void	libqunlock(QLock *q);
extern	void*	libqlowner(QLock *q);
extern	void*	libfdtochan(int, int);
extern	void	libchanclose(Chan *chan);
extern	int	kbind(char*, char*, int);
extern	int	kchdir(char*);
extern	int	kclose(int);
extern	int	kcreate(char*, int, ulong);
extern	Dir*	kdirfstat(int);
extern	int	kdirfwstat(int, Dir*);
extern	long	kdirread(int, Dir**);
extern	Dir*	kdirstat(char*);
extern	int	kdirwstat(char*, Dir*);
extern	int	kdup(int, int);
extern	int	kfauth(int, char*);
extern	char*	kfd2path(int);
extern	int	kfstat(int, char*, int);
extern	int	kfversion(int, uint, char*, uint);
extern	int	kfwstat(int, char*, int);
extern	int	kmount(int, int, char*, int, char*);
extern	int	kopen(char*, int);
extern	int	kpipe(int[2]);
extern	long	kpread(int, void*, long, vlong);
extern	long	kread(int, void*, long);
extern	int	kremove(char*);
extern	vlong	kseek(int, vlong, int);
extern	int	kstat(char*, char*, int);
extern	int	kunmount(char*, char*);
extern	long	kpwrite(int, void*, long, vlong);
extern	long	kwrite(int, void*, long);
extern	int	kwstat(char*, char*, int);
extern	int	klisten(char*, char*);
extern	int	kannounce(char*, char*);
extern	int	kdial(char*, char*, char*, int*);
extern	void	kerrstr(char*, uint);
extern	int	kiounit(int);
extern	void	kwerrstr(char *, ...);
extern	void	kgerrstr(char*, uint);
extern	long	kchanio(Chan*, void*, int, int);
