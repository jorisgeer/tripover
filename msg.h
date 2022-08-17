// msg.h -messages, logging and assertions

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* Defines for console, debug and assert messages
   Most entries are macros to add file and line to the functions
   Assertions are here for trivial inlining or low-overhead calling
 */

enum Msglvl { Msglvl_nil,Fatal,Assert,Error,Warn,Info,Vrb,Nolvl,Msglvl_last };

todo msgfile as enum, name in msg.c
assert inline, no init

#define Tidmask 0x7f000000U
#define Tidshift 24
#define Tidbit 0x80000000U

enum Msgcode {
  Indent = 0x7f,
  Nopfx = 0x80,
  Exit = 0x100,   // exit program dependent on assert setting
  EXit = 0x200,   // idem, unconditional
  User = 0x400, // user-style, undecorated
  Ind  = 0x800,  // indent

  Notty  = 0x1000,
  Ret0   = 0x2000,
  Iter   = 0x4000,
  Noiter = 0x8000,
  V0     = 0x10000, V1 = 0x20000, V3 = 0x30000,
  CC0    = 0x40000,
  Emp    = 0x80000,
  Ret1   = 0x100000
};

enum Msgopts { Msg_stamp = 2, Msg_pos = 4, Msg_type = 8, Msg_ccerr = 0x10, Msg_show = 0x20, Msg_mask = 0x3f, Msg_bcklog = 0x40 };

enum Msgfileopts { Msgfile_none,Msgfile_noiter = 1 };

extern ub4 msgfile_h;

// highest file coords for iter
#define Maxmsgline 8192
#define Maxmsgfile 32

struct eta {
  ub8 now,stamp,start,limit;
  ub8 cur,end;
  ub4 showcnt;
};

// arrange file coords
#define FLN (__LINE__|msgfile)
#define caller (__LINE__|msgfile)

#ifdef Chkfmt
 #define chkfmt(f) sassert(sizeof(f) >= sizeof(void *),"fmt is not a string");
#else
 #define chkfmt(f)
#endif

#define genmsg(lvl,code,fmt,...) chkfmt(fmt) genmsgfln(FLN,(lvl),(code),(fmt),__VA_ARGS__)

#define vrb(code,fmt,...) chkfmt(fmt) if (globs.msglvl < Vrb) vrbfln(FLN,(code),(fmt),__VA_ARGS__)
#define vrb0(code,fmt,...) chkfmt(fmt) if (globs.msglvl < Vrb) vrbfln(FLN,(code),(fmt),__VA_ARGS__)

#define info(code,fmt,...) chkfmt(fmt) infofln(FLN,(code),fmt,__VA_ARGS__)
#define warning(code,fmt,...) chkfmt(fmt) warnfln(FLN,(code),fmt,__VA_ARGS__)
#define warn(code,fmt,...) chkfmt(fmt) warnfln(FLN,(code),(fmt),__VA_ARGS__)
#define error(code,fmt,...) chkfmt(fmt) errorfln(FLN,(code),0,fmt,__VA_ARGS__)
#define nilerr(code,fmt,...) chkfmt(fmt) nilerrfln(FLN,(code),0,(fmt),__VA_ARGS__)
#define oserror(code,fmt,...) chkfmt(fmt) oserrorfln(FLN,(code),fmt,__VA_ARGS__)
#define oswarning(code,fmt,...) chkfmt(fmt) oswarningfln(FLN,(code),(fmt),__VA_ARGS__)
#define osinfo(code,fmt,...) chkfmt(fmt) osinfofln(FLN,(code),(fmt),__VA_ARGS__)
#define fatal(code,fmt,...) chkfmt(fmt) fatalfln(FLN,(code),0,fmt,__VA_ARGS__)

#define ret_info(code,fmt,...) chkfmt(fmt) return infofln(FLN,(code),fmt,__VA_ARGS__)
#define ret_warn(code,fmt,...) chkfmt(fmt) return warnfln(FLN,(code),(fmt),__VA_ARGS__)
#define ret_error(code,fmt,...) chkfmt(fmt) return errorfln(FLN,(code),0,fmt,__VA_ARGS__)
#define ret_oserror(code,fmt,...) chkfmt(fmt) return oserrorfln(FLN,(code),fmt,__VA_ARGS__)

#define info0(code,s) chkfmt(s) info0fln(FLN,(code),(s))
#define warn0(code,s) chkfmt(s) warn0fln(FLN,(code),(s))
#define oswarn0(code,s) chkfmt(s) oswarn0fln(FLN,(code),(s))

#define error0(code,s) chkfmt(s) errorfln(FLN,(code),0,(s))
#define oserror0(code,s) chkfmt(s) oserrorfln(FLN,(code),(s))

#define vrbcc(cc,code,fmt,...) chkfmt(fmt) if ((cc)) vrbfln(FLN,(code),(fmt),__VA_ARGS__)
#define infocc(cc,code,fmt,...) chkfmt(fmt) if ((cc)) infofln(FLN,(code),(fmt),__VA_ARGS__)
#define warncc(cc,code,fmt,...) chkfmt(fmt) if ((cc)) warnfln(FLN,(code),(fmt),__VA_ARGS__)
#define errorcc(cc,code,fmt,...) chkfmt(fmt) if ((cc)) errorfln(FLN,(code),0,(fmt),__VA_ARGS__)
#define errorccfln(cc,code,fln,fmt,...) chkfmt(fmt) if ((cc)) errorfln(FLN,(code),(fln),(fmt),__VA_ARGS__)

#define infovrb(cc,code,fmt,...) genmsg((cc) ? Info : Vrb,(code),(fmt),__VA_ARGS__)
#define warninfo(cc,code,fmt,...) genmsg((cc) ? Warn : Info,(code),(fmt),__VA_ARGS__)

// no misprint: access first two format args
#define progress(eta,fmt,cur,end,...) progress2(0,0,(eta),FLN,(cur),(end),(fmt),(cur),(end),__VA_ARGS__)
#define tprogress(tid,tidcnt,eta,fmt,cur,end,...) progress2((tid),(tidcnt),(eta),FLN,(cur),(end),(fmt),(cur),(end),__VA_ARGS__)
#define progress0(eta,fmt,cur,end) progress2(0,0,(eta),FLN,(cur),(end),(fmt),(cur),(end))

extern int progress2(ub4 tid,ub4 tidcnt,struct eta *eta,ub4 fln,ub8 cur,ub8 end,const char *fmt, ...)
  __attribute__ ((format (printf,7,8))) Attribute(nonnull);

#define mysnprintf(dst,pos,len,fmt,...) mysnprintf_fln(FLN,(dst),(pos),(len),#pos,#len,(fmt),__VA_ARGS__)
#define mysnprintf0(dst,pos,len,fmt) mysnprintf_fln(FLN,(dst),(pos),(len),#pos,#len,(fmt))
extern ub4 mysnprintf_fln(ub4 fln,char *dst,ub4 pos,ub4 len,const char *spos,const char *slen,const char *fmt,...) __attribute__ ((format (printf,7,8)));

#ifdef va_arg
  #define myvsnprintf(d,p,n,f,a) myvsnprintf_fln(FLN,(d),(p),(n),(f),(a))
  extern ub4 myvsnprintf_fln(ub4 fln,char *dst, ub4 pos, ub4 len, const char *fmt, va_list ap);
  extern void vmsg(enum Msglvl lvl,ub4 fln,const char *fmt,va_list ap);
#endif

#define fmtstring(dst,fmt,...) mysnprintf_fln(FLN,(dst),0,sizeof(dst),"0","sizeof dst",(fmt),__VA_ARGS__)
#define fmtstringc(pos,dst,fmt,...) { sassert(sizeof(dst) > sizeof(void *),"dest is not an array"); (pos) = mysnprintf_fln(FLN,(dst),0,sizeof (dst),"0","sizeof dst",(fmt),__VA_ARGS__); }
#define fmtstring0(dst,s) mysnprintf_fln(FLN,(dst),0,sizeof (dst),"0","sizeof dst","%s",(s))

#define copystr(dst,src) mysnprintf_fln(FLN,(dst),0,sizeof(dst),"0","sizeof dst","%.*s",sizeof(dst),(src))

extern ub4 myutoa(char *dst,ub4 x);

#define nomsgpfx() msgprefix(0,NULL)
int msgprefix(int rv,const char *fmt, ...) __attribute__ ((format (printf,2,3)));

extern ub4 setmsgfile(const char *filename);
extern ub4 setmsgfile2(const char *filename,enum Msgfileopts opt);

extern ub4 msgfln(char *dst,ub4 pos,ub4 len,ub4 fln,ub4 wid);
extern void msg_write(const char *buf,ub4 len);
extern void msg_errwrite(ub4 fln,ub4 fln2,ub4 fln3,const char *buf);

extern int inimsg(char *progname, const char *logname, ub4 opts);
extern void eximsg(bool cnts);
extern void msgsum(bool warnonly);

extern void setmsglvl(enum Msglvl lvl, ub4 vlvl);
extern enum Msglvl getmsglvl(void);
extern int setmsglog(const char *dir,const char *logname,int newonly,int show);
extern void clriters(void);

// assertions: error_eq(a,b) to be read as 'error if a equals b'
// when failing, both names and values are shown
#define error_eq(a,b) if ((a) == (b)) error_eq_fln((a),(b),#a,#b,FLN,Func)
#define error_ep(a,b) if ((a) == (b)) error_ep_fln((a),(b),#a,#b,FLN)
#define error_ne(a,b) if ((a) != (b)) error_ne_fln((a),(b),#a,#b,FLN,Func)
#define error_z(a,b) if ((a) == 0) error_z_fln((a),(b),#a,#b,FLN,Func)
#define error_nz(a,b) if ((a) != 0)error_nz_fln((a),(b),#a,#b,FLN,Func)
#define error_zz(a,b) if ((a) == 0 || (b) == 0) error_zz_fln((a),(b),#a,#b,FLN)
#define error_zp(a,b) if ((a) == NULL) error_zp_fln((const void*)(a),(b),#a,#b,FLN)

#define error_gt(a,b,x) if ((a) > (b)) error_gt_fln(Exit,(a),(b),#a,#b,(x),#x,FLN,Func)
// #define Error_gt(a,b,x) if ((a) > (b)) error_gt_fln(EXit,(a),(b),#a,#b,(x),#x,FLN)

#define error_ge(a,b) if ((a) >= (b)) error_ge_fln(Exit,(a),(b),#a,#b,FLN,Func)
// #define Error_ge(a,b) if ((a) >= (b)) error_ge_fln(EXit,(a),(b),#a,#b,FLN,Func)

#define error_le(a,b) if ((a) <= (b)) error_le_fln((a),(b),#a,#b,FLN,Func)
#define error_lt(a,b) if ((a) < (b)) error_lt_fln((a),(b),#a,#b,FLN,Func)

// #define error_gt2(a1,a2,b) error_gt2_fln((a1),(a2),(b),#a1,#a2,#b,FLN)

#define error_eq_cc(a,b,fmt,...) if ((a) == (b)) error_eq_cc_fln((b),#a,#b,FLN,fmt,__VA_ARGS__)

// todo convert into error_xx_cc_fln style
#define error_ne_cc(a,b,fmt,...) if ((a) != (b)) error_cc_fln((a),(b),#a,#b,"!=",FLN,fmt,__VA_ARGS__)
#define error_z_cc(a,fmt,...) if ((a) == 0) error_cc_fln((a),0,#a,"0","==",FLN,fmt,__VA_ARGS__)
#define error_nz_cc(a,fmt,...) if ((a) != 0) error_cc_fln((a),0,#a,"0","!=",FLN,fmt,__VA_ARGS__)
#define error_le_cc(a,b,fmt,...) if ((a) <= (b)) error_cc_fln((a),(b),#a,#b,"<=",FLN,fmt,__VA_ARGS__)
#define error_lt_cc(a,b,fmt,...) if ((a) < (b)) error_cc_fln((a),(b),#a,#b,"<",FLN,fmt,__VA_ARGS__)

#define error_ge_cc(a,b,fmt,...) if ((a) >= (b)) error_ge_cc_fln((a),(b),#a,#b,FLN,fmt,__VA_ARGS__)

#define error_gt_cc(a,b,fmt,...) if ((a) > (b)) error_gt_cc_fln(Exit,(a),(b),#a,#b,FLN,fmt,__VA_ARGS__)
// #define Error_gt_cc(a,b,fmt,...) error_gt_cc_fln(EXit,(a),(b),#a,#b,FLN,fmt,__VA_ARGS__)

#define error_ovf(a,t) error_ovf_fln((a),sizeof(t),#a,#t,FLN)

#define limit_gt(x,lim,arg) (x) = limit_gt_fln((x),(lim),(arg),#x,#lim,#arg,FLN)

#define msgopt(s) msgopt_fln(FLN,(s))

extern int genmsgfln(ub4 fln,enum Msglvl lvl,ub4 code,const char *fmt,...) __attribute__ ((format (printf,4,5)));
extern int vrbfln(ub4 fln, ub4 code, const char *fmt, ...) __attribute__ ((format (printf,3,4)));
extern int infofln(ub4 fln, ub4 code, const char *fmt, ...) __attribute__ ((format (printf,3,4)));
extern int warnfln(ub4 fln, ub4 code, const char *fmt, ...) __attribute__ ((format (printf,3,4)));
extern int errorfln(ub4 fln,ub4 code,ub4 fln2,const char *fmt,...) __attribute__ ((format (printf,4,5)));
extern void *nilerrfln(ub4 fln,ub4 code,ub4 fln2,const char *fmt,...) __attribute__ ((format (printf,4,5)));
extern int oserrorfln(ub4 fln,ub4 code,const char *fmt, ...) __attribute__ ((format (printf,3,4)));
extern int oserrorfln2(ub4 fln,ub4 code,ub4 fln2,const char *fmt, ...) __attribute__ ((format (printf,4,5)));
extern int oswarningfln(ub4 fln,ub4 code,const char *fmt, ...) __attribute__ ((format (printf,3,4)));
extern int osinfofln(ub4 fln,ub4 code,const char *fmt, ...) __attribute__ ((format (printf,3,4)));
Noret extern void assertfln(ub4 fln, ub4 code, const char *fmt, ...) __attribute__ ((format (printf,3,4)));
Noret extern int fatalfln(ub4 fln,ub4 code,ub4 fln2,const char *fmt,...) __attribute__ ((format (printf,4,5)));

extern int info0fln(ub4 fln, ub4 code, const char *s);
extern int infofln2(ub4 fln,ub4 code,ub4 fln2,const char *fmt,...) __attribute__ ((format (printf,4,5)));

extern int warn0fln(ub4 fln, ub4 code, const char *s);
extern int warnfln2(ub4 fln,ub4 code,ub4 fln2,const char *fmt,...) __attribute__ ((format (printf,4,5)));
extern int oswarn0fln(ub4 line, ub4 code, const char *s);

extern ub4 limit_gt_fln(ub4 x,ub4 lim,ub4 arg,const char *sx,const char *slim,const char *sarg,ub4 fln);

Noret extern void error_cc_fln(size_t a,size_t b,const char *sa,const char *sb,const char *cc,ub4 line,const char *fmt,...) __attribute__ ((format (printf,7,8)));

Noret extern void error_eq_cc_fln(size_t b,const char *sa,const char *sb,ub4 line,const char *fmt,...) __attribute__ ((format (printf,5,6)));
Noret extern void error_ge_cc_fln(size_t a,size_t b,const char *sa,const char *sb,ub4 line,const char *fmt,...) __attribute__ ((format (printf,6,7)));

Noret extern void error_gt_cc_fln(ub4 code,size_t a,size_t b,const char *sa,const char *sb,ub4 line,const char *fmt,...) __attribute__ ((format (printf,7,8)));

extern void enter(ub4 fln);
extern void leave(ub4 fln);

extern int msgopt_fln(ub4 fln,const char *name);

static void error_eq_fln(size_t a,size_t b,const char *sa,const char *sb,ub4 line,const char *fn)
{
  if (a != b) return;

  infofln(__LINE__|msgfile_h,0,"%s: '%s' eq '%s'",fn,sa,sb);
  assertfln(line,Exit,"%s:\ah%lu == %s:\ah%lu", sa,a,sb,b);
}

static void error_ep_fln(const void *a,const void *b,const char *sa,const char *sb,ub4 line)
{
  if (a != b) return;

  assertfln(line,Exit,"%s:%p == %s:%p", sa,a,sb,b);
}

static void error_ne_fln(size_t a,size_t b,const char *sa,const char *sb,ub4 line,const char *fn)
{
  if (a == b) return;

  size_t d = (a > b ? a - b : b - a);

  infofln(__LINE__|msgfile_h,0,"%s: '%s' ne '%s'",fn,sa,sb);
  if (d < 10000) assertfln(line,Exit,"\ah%lu != \ah%lu dif %lu", a,b,d);
  else assertfln(line,Exit,"\ah%lu != \ah%lu",a,b);
}

static void error_gt_fln(ub4 code,size_t a,size_t b,const char *sa,const char *sb,size_t x,const char *sx,ub4 line,const char *fn)
{
  if (a <= b) return;

  infofln(__LINE__|msgfile_h,0,"%s: '%s' gt '%s'",fn,sa,sb);

  assertfln(line,code,"%s:\ah%lu > %s:\ah%lu dif %lu %s:%lu", sa,a,sb,b,a - b,sx,x);
}

static void error_ge_fln(ub4 code,size_t a,size_t b,const char *sa,const char *sb,ub4 line,const char *fn)
{
  if (a < b) return;

  infofln(__LINE__|msgfile_h,0,"%s: '%s' ge '%s'",fn,sa,sb);

  if (a == b) assertfln(line,code,"\ah%lu == \ah%lu",a,b);
  else if (a - b < 10000) assertfln(line,code,"%lu > %lu by %lu",a,b,a-b);
  else assertfln(line,code,"%lu > %lu",a,b);
}

static void error_lt_fln(size_t a,size_t b,const char *sa,const char *sb,ub4 line,const char *fn)
{
  if (a >= b) return;

  infofln(__LINE__|msgfile_h,0,"%s: '%s' lt '%s'",fn,sa,sb);
  assertfln(line,Exit,"%lu < %lu  dif \ah%lu",a,b,b - a);
}

static void error_le_fln(ub4 a,ub4 b,const char *sa,const char *sb,ub4 line,const char *fn)
{
  if (a > b) return;

  infofln(__LINE__|msgfile_h,0,"%s: '%s' le '%s'",fn,sa,sb);
  assertfln(line,Exit,"%s:%u <= %s:%u", sa,a,sb,b);
}

static void error_z_fln(size_t a,size_t b,const char *sa,const char *sb,ub4 line,const char *fn)
{
  if (a != 0) return;

  infofln(__LINE__|msgfile_h,0,"%s: '%s' is zero",fn,sa);
  assertfln(line,Exit,"%s = 0 at %s:%lu", sa,sb,b);
}

static void error_nz_fln(ub4 a,ub4 b,const char *sa,const char *sb,ub4 line,const char *fn)
{
  if (a == 0) return;

  infofln(__LINE__|msgfile_h,0,"%s: '%s' is not zero",fn,sa);
  assertfln(line,Exit,"%s:%u != 0 at %s:%u", sa,a,sb,b);
}

static void error_zz_fln(size_t a,size_t b,const char *sa,const char *sb,ub4 line)
{
  if (a == 0) assertfln(line,Exit,"%s = 0", sa);
  else if (b == 0) assertfln(line,Exit,"%s = 0", sb);
}

static void error_zp_fln(const void *a,ub4 b,const char *sa,const char *sb,ub4 line)
{
  if (a) return;

  assertfln(line,Exit,"%s == nil at %s:%u", sa,sb,b);
}

static ub4 ovfsizes[] = { 0, 0xff, 0xffff, 0, 0xffffffff, 0, 0, 0, 0xffffffff };

static void error_ovf_fln(ub8 a,ub4 b,const char *sa,const char *sb,ub4 line)
{
  ub8 bb;
  ub4 ak = (ub4)(a >> 10);

  if (b > 7) assertfln(line,Exit,"%s:\ah%uk overflows sizeof %s:%u", sa,ak,sb,b);

  bb = ovfsizes[b];
  if (a < bb) return;

  if (b == 1) assertfln(line,Exit,"%s:\ah%lu overflows sizeof %s:%u", sa,a,sb,b);
  else assertfln(line,Exit,"%s:\ah%uk overflows sizeof %s:%u", sa,ak,sb,b);
}

// dummy to prevent 'unused' warnings, as above are static
static void iniassert(void)
{
  error_lt(1,1);
  error_le(2,1);
  error_gt(1,1,0);
  error_ge(1,2);
  error_eq(1,2);
  error_ep((void*)1,(void*)2);
  error_ne(1,1);
  error_z(1,0);
  error_nz(0,2);
  error_zz(1,1);
  error_zp((void*)1,0);

//  error_gt2(1,0,1);

  error_ovf(1024,ub2);
}
