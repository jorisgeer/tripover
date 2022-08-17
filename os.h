// os.h - operating system specifics

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

struct osnetadr {
  ub4 port;
  ub4 host;
};

extern ub8 gettime_usec(void);
extern int osclock_gettime(ub8 *pusec);
extern void osmillisleep(ub4 msec);

extern int ostimer(ub4 msec,bool virtual);
extern int osthtimer(ub4 tid,ub8 msec);
extern int osrmthtimer(ub4 tid);
extern int osisexpired(ub4 tid);
extern int osisalarm(void);

extern char *getoserr(void);
extern int osopen(const char *name);
extern int osappend(const char *name);
extern long osread(int fd,char *buf,size_t len);
extern long oswrite(int fd, const char *buf,size_t len);
extern int oscreate(const char *name);
extern int osfdinfo(struct myfile *mf,int fd);
extern int osfileinfo(struct myfile *mf,const char *name);
extern int osfileinfos(struct mysfile *mf,const char *name);
extern int osclose(int fd);
extern int osremove(const char *name);
extern int osmkdir(const char *dir);
extern int osexists(const char *name);
extern int osrename(const char *old,const char *new);

extern int ossetprio(int nice);
extern int osrun(const char *cmd,char *const argv[],char *const envp[]);
extern int oswaitany(ub4 *cldcnt);
extern int osbackground(void);

extern int osdup2(int oldfd,int newfd);
extern int osrewind(int fd);
extern void *osmmap(size_t len);
extern void *osmmapfd(ub8 len,int fd);
extern int osmremap(void *p,size_t oldlen,size_t newlen);
extern int osmunmap(void *p,size_t len);
extern int osmemrdonly(void *p,size_t len);
extern int osmlock(void);
extern int osmunlock(void);

extern int setsigs(void);
extern int oslimits(void);

extern int getqentry(const char *qdir,struct myfile *mf,const char *region,const char *ext);
extern int setqentry(struct myfile *mfreq,struct myfile *mfrep,const char *ext);

extern int ossocket(bool inet);
extern int osbind(int fd,ub4 port);
extern int oslisten(int fd,int backlog);
extern int osaccept(int sfd,struct osnetadr *ai);

extern ub4 osmeminfo(void);

extern void setmsginfo(char *buf,ub4 len);

extern void inios(void);
