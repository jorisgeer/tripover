// util.h

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014 Joris van der Geer.
 */

struct cmdval { // matched commandline arg
  ub4 uval;
  ub4 valcnt;
  const char *sval;
  const char *valname;
  const char *subarg;
  struct cmdarg *args;
  ub4 argndx;
  int retval;
  const char *progname;
  const char *progdesc;
};

struct cmdarg { // commandline arg defines
  const char *arg;
  const char *val;
  const char *desc;
  int (*fn)(struct cmdval *cp);
};

#define fileopen(name,must) fileopenfln(FLN,(name),(must))
#define filewrite(fd,buf,len,name) filewritefln(FLN,(fd),(buf),(len),(name))
#define fileswrite(fd,fd2,buf,len,name) fileswritefln(FLN,(fd),(fd2),(buf),(len),(name))

extern int filecreate(const char *name,int mustsucceed);
extern int fileappend(const char *name);
extern int fileopenfln(ub4 fln,const char *name,int mustexist);
extern int filewritefln(ub4 fln,int fd, const void *buf,ub8 len,const char *name);
extern int fileswritefln(ub4 fln,int fd,int fd2,const void *buf,ub8 len,const char *name);
extern int fileread(int fd,void *buf,ub4 len,const char *name);
extern int fileclose(int fd,const char *name);
extern int fileexists(const char *name);
extern int fileremove(const char *name);
extern int filerotate(const char *name,const char old,const char new);

extern int readfile(struct myfile *mf,const char *name, int mustexist,ub4 maxlen);
extern int readfile_pad(struct myfile *mf,const char *name, int mustexist,ub4 maxlen,ub4 padlen,const char *pad);
extern int writefile(const char *name,char *buf,size_t len);

extern int readpath(struct myfile *mf,const char *dir,const char *name, int mustexist,ub4 maxlen);
extern int freefile(struct myfile *mf);

extern ub4 truncutf8(const char *s,ub4 len);

extern ub4 sort8(ub8 *p,ub4 n,ub4 fln,const char *desc);
extern ub4 fsort8(ub8 *p,ub4 n,int partial,ub4 fln,const char *desc);
extern ub4 sort4(ub4 *p,ub4 n,ub4 fln,const char *desc);
extern ub4 bsearch4(ub4 *p,ub4 n,ub4 key,ub4 fln,const char *desc);
extern ub4 bsearch8(ub8 *p,ub4 n,ub8 key,ub4 fln,const char *desc);

extern int precmdline(int argc, char *argv[], const char *name,char **pval);
extern int cmdline(int argc, char *argv[], struct cmdarg *cap,const char *desc);
extern int shortusage(void);
extern void show_version(void);

#define limit(a,b,c) if ((a) > (b)) { (a) = (b); warningfln(FLN,0,"limit %s:%u to %s:%u for %s:%u",#a,(a),#b,(b),#c,(c)); }

#define m2geo(m) ((m) / (1000 / Geoscale))
#define geo2m(g) ((g) * (1000 / Geoscale))

extern int dorun(ub4 fln,enum Runlvl stage,bool silent);

extern int getwatchitems(const char *name,ub8 *list,ub4 listlen);
extern void addwatchitem(const char *name,ub4 val,ub4 fln,int hex);

#define dyncfg(name,def,sil) dyncfgfln(FLN,(name),(def),(sil))
extern int dyncfgfln(ub4 fln,const char *name,ub4 def,int silent);

extern int writeppm(const char *name,ub4 *data,ub4 nx,ub4 ny);

extern int iniutil(int pass);
extern void exiutil(void);
