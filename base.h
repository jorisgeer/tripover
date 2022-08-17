// base.h

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

#ifndef __STDC__
 #error "missing __STDC__ : expect iso c 99+"
#endif
#ifndef __STDC_VERSION__
 #error "missing __STDC_VERSION__ : expect iso c 99+"
#endif
#if __STDC_VERSION__ < 199901L
 #error "expect iso c 99+"
#endif

typedef unsigned char ub1;
typedef unsigned char bool;
typedef unsigned short ub2;
typedef unsigned int ub4;
typedef unsigned long ub8;

typedef short sb2;
typedef int sb4;
typedef long sb8;

#define Version_maj 1
#define Version_min 0
#define Version_phase "prod"
#define Program_name "tripover"
#define Program_desc "broad-search journey planner"

// handful of useful macros
#define hi16 0xffff
#define hi20 0xfffff
#define hi24 0xffffff
#define hi28 0xfffffff
#define hi32 0xffffffff
#define hi64 0xffffffffffffffff

#define Elemcnt(a) (sizeof(a) / sizeof(*a))

#ifndef max
 #define max(a,b) ((a) > (b) ? (a) : (b))
#endif
#ifndef min
 #define min(a,b) ((a) < (b) ? (a) : (b))
#endif

#ifndef NULL
 #define NULL (void*)0
#endif

#define clear(p) memset((p),0,sizeof(*(p)))
#define nclear(p,n) do_clear((p),(n) * sizeof(*(p)))
#define nsethi(p,n) do_sethi((p),(n) * sizeof(*(p)))

// c11 langage only
#if defined  __STDC_VERSION__ && __STDC_VERSION__ >= 201101
 #define sassert(expr,msg) _Static_assert((expr),msg)
 #define sassert_end ;
 #define aclear(p) { _Static_assert(sizeof(p) > 8,"need array, not pointer"); do_clear((p),sizeof(p)); }
 #define strcopy(dst,src) { _Static_assert(sizeof(dst) > 8,"need array, not pointer"); strncpyfln((dst),(src),(ub4)sizeof(dst)-1,#dst,#src,FLN); }
 #define Func __func__
 #define Noret _Noreturn

#else
 #define sassert(expr,msg)
 #define sassert_end
 #define aclear(p) do_clear((p),sizeof(p));
 #define strcopy(dst,src) strncpy((dst),(src),sizeof(dst)-1 );
 #define Func ""
 #define Noret
#endif

#if defined __clang__
 #define Attribute(name) __attribute__((name))
 #define Fallthrough
 #pragma clang diagnostic error "-Wimplicit-function-declaration"
 #pragma clang diagnostic error "-Wincompatible-pointer-types"
 #pragma clang diagnostic error "-Wconditional-uninitialized"
 #pragma clang diagnostic error "-Wuninitialized"
 #define Diagoff
 #define Diagon
 // #pragma clang diagnostic ignored "-Wunused-variable"

#elif defined __GNUC__
 #define Attribute(name) __attribute__((name))
 #define Fallthrough __attribute__ ((fallthrough));
 #pragma GCC diagnostic ignored "-Wconversion"

 #define Diagoff _Pragma ( "GCC diagnostic push" ); _Pragma ( "GCC diagnostic ignored \"-Wunsafe-loop-optimizations\"" )
 #define Diagon _Pragma ( "GCC diagnostic pop" )
#else
 #define Attribute(name)
 #define Diagoff
 #define Diagon
#endif

#define memcopy(d,s,n) { sassert(sizeof(d) == sizeof(s),"pointer size mismatch"); memcopyfln((d),(s),(n),FLN); }
extern void memcopyfln(void *dst,const void *src,size_t len,ub4 fln);

#define strcomp(a,b) strcompfln((a),(b),#a,#b,FLN)
extern int strcompfln(const char *a,const char *b,const char *sa,const char *sb,ub4 fln);

extern int strncpyfln(char *dst,const char *src,ub4 len,const char *sdst,const char *ssrcb,ub4 fln);

extern ub4 str2ub4(const char *s, ub4 *pv);
extern ub4 hex2ub4(const char *s, ub4 *pv);
extern int hex2ub8(const char *s, ub8 *pv);
extern int str2dbl(const char *s,ub4 len,double *pv);
extern ub4 bstr2ub4(const char *s, ub4 *pv);

extern ub4 strlen4(const char *s);

#define oclear(p) do_clear(&(p),sizeof(p))
extern void do_clear(void *p,size_t len);
extern void do_sethi(void *p,size_t len);

extern ub4 sat32(ub8 x,ub8 y);

extern ub4 msb(ub8 x);
extern ub4 cntbits(ub4 x);

extern int inibase(void);

enum Runlvl { Runread,Runbaseprep,Runprep,Runcompound,Runmknet,Runnet0,Runnetn,Runserver,Runend,Runcnt };
enum Mainprog { Prognil,Progto,Progprep,Progvi,Progvisv };

#define Nthread 32

// program-wide global vars go here
struct globs {
  const char *progname;
  enum Mainprog prog;

  ub1 doruns[Runcnt];
  ub2 dummy;
  enum Runlvl stopat,stopatcl;
  char stopatstr[64];

  ub4 argc;
  char args[16][1024];

  char cfgfile[1024];
  char netfile[1024];
  char osmfile[1024];
  char netdir[1024];
  char querydir[256];
  ub4 serverid;
  ub4 msglvl,msgslvl;
  ub4 vrblvl;

  ub4 strict;

  ub4 maxstops;

  ub4 maxvm;

  ub4 tidcnt;
  ub4 tids[Nthread];

  int netok;

  ub4 writext;
  ub4 writpdf;
  ub4 writgtfs;
  ub4 extdec;

  int msg_fd;
  char logname[256];
  int pid;
  int sigint,sig;
  ub4 id;
  ub4 msgfln;
  ub4 msgarg1;
  ub4 msgarg2;
  ub4 msgarg3;

  bool background;
  ub1 dummy2[3];

  ub4 testa,testb;
  ub4 testcnt;
  ub4 testset[16];

  // raw config vars
  ub4 netvars[64];   // checked for Net_cnt in cfg
  ub4 engvars[64];   // checked for Eng_cnt in cfg

  // cooked config vars
  ub4 periodt0,periodt1;
  ub4 pat0,pat1;

  ub4 mintts[256];
  ub4 walkspeed,walklimit,sumwalklimit;
  ub4 net1walklimit,net2walklimit;
  ub4 taxilimit,taxilimitgnd;
  ub4 dirconlimit;
  ub4 eventzlo;
  ub4 net1timlim,net2timlim,net3timlim;
  ub4 net2altlim,net3altlim;

  ub4 net1limit[3],net2limit[3],net3limit[3];
  ub4 net1con[3],net2con[3],net3con[3];
  ub4 net1above,net2above,net3above;

  ub4 allocrep;

  int once;
  int nomsgsum,nomergeroute;
  int noevcompress;
  int nomemsum,noreserve;
  int nowalk,notaxi;
  int nolotx,nogrid;
};
extern struct globs globs;

struct myfile {
  int exist,direxist,alloced;
  int isdir,isfile;
  ub4 basename;
  size_t len;
  unsigned long mtime;
  ub4 fln;
  char name[1024];
  char localbuf[16 * 1024];
  char *buf;
};

struct mysfile {
  int exist,direxist,alloced;
  int isdir,isfile;
  size_t len;
  unsigned long mtime;
};

// Km * scale = res: 10m
#define Geoscale 100
#define Georange 1e8

#ifndef M_PI
  #define M_PI 3.141592655
#endif

#define NVALGRIND
#ifdef NVALGRIND
 #define vg_set_undef(p,n)
 #define vg_chk_def(a,p,n)
#else
 #include <valgrind/memcheck.h>
 #define vg_set_undef(p,n) VALGRIND_MAKE_MEM_UNDEFINED((p),(n));
 #define vg_chk_def(a,p,n) (a) = VALGRIND_CHECK_MEM_IS_DEFINED((p),(n));
#endif
