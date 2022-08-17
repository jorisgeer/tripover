// vis.c - cgi 'script' for network display

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015-2017 Joris van der Geer.
 */

/* if a requested tile is present on disk, return it
 * otherwise, request it from viserve
 */

#include <unistd.h>

#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#include "base.h"
struct globs globs;

#include "os.h"
#include "mem.h"
#include "util.h"

static ub4 msgfile;
#include "msg.h"

#include "time.h"

// #include "vis.h"
#include "vishare.h"

static const char basedir[] = "/home/joris/to";

static ub4 test_z = hi32,test_y = hi32,test_x = hi32;

static int testonly;

static int init0(char *progname)
{
  char *p;

  setsigs();

  p = strrchr(progname,'/');
  globs.progname = (p ? p + 1 : progname);

  if (chdir(basedir)) return oserror(0,"cannot chdir to %s",basedir);

  setmsglvl(Warn,0,0);
  inimsg(progname,"--",Msg_stamp|Msg_pos|Msg_type);
  msgfile = setmsgfile(__FILE__);
  iniassert();

  info(User,"vis %u.%u %s\n", Version_maj,Version_min,Version_phase);

  if (iniutil(0)) return 1;
  inimem();
  inios();
  globs.maxvm = 32;
  return 0;
}

extern const char *runlvlnames(enum Runlvl lvl);
const char *runlvlnames(enum Runlvl lvl) { return lvl ? "n/a" : "N/A"; }

static int dowrite(const char *p,size_t n)
{
  return (int)oswrite(1,p,(ub4)n);
}

static int writestr(const char *p)
{
  return dowrite(p,strlen(p));
}

#if 0
static int notile(void)
{
  ub4 pos;
  char cl[1024];
  ub4 len = sizeof(cl);

  if (testonly) return 0;

  writestr("Access-Control-Allow-Origin: *\r\n");
  writestr("Content-type: image/svg\r\n\r\n");

  pos = fmtstring(cl,"%s","<svg width='256' height='256' xmlns='http://www.w3.org/2000/svg' version='1.1'>\n");
  pos += mysnprintf0(cl,pos,len,"<circle cx='128' cy='128' r='32' />\n");
  pos += mysnprintf0(cl,pos,len,"</svg>\n");
  return 0;
}
#endif

static int showtile(const char *name)
{
  struct myfile img;
  ub4 pos;
  char cl[256];

  if (testonly) return 0;

  if (readfile(&img,name,1,0)) return 1;

  writestr("Access-Control-Allow-Origin: *\r\n");
  writestr("Content-type: image/bmp\r\n");
  pos = fmtstring(cl,"Content-Length: %lu\r\n\r\n",img.len);
  dowrite(cl,pos);
  return dowrite(img.buf,img.len);
}

static int query(ub4 z,ub4 y,ub4 x)
{
  char val[1024];
  char qname[1024];
  char qname_new[1024];
  char qname_sub[1024];

  ub8 msec = gettime_msec();
  ub4 pos;

  fmtstring(qname,"%s/%s_%s_%011lx_%04x",globs.querydir,"T","glob",msec,0);

  fmtstring(qname_new,"%s.new",qname);
  fmtstring(qname_sub,"%s.sub",qname);

  pos = fmtstring(val,"z i %u\ny i %u\nx i %u\n\n",z,y,x);
  info(0,"query: %s",val);
  if (writefile(qname_new,val,pos)) return 1;
  if (osrename(qname_new,qname_sub)) return 1;
  info(0,"issue query %s",qname_sub);
  return 0;
}

static int vis(char *envp[])
{
  ub4 z = 0,y = 0, x = 0;
  const char *p = envp[0];
  char path[1024];

  const char *urlpath;

  if (test_z != hi32 && test_y != hi32 && test_x != hi32) {
    z = test_z; y = test_y; x = test_x;
  } else {
    urlpath = getenv("PATH_INFO");
    if (urlpath == NULL) return 1;

    info(0,"url %s",urlpath);

    p = urlpath;
    if (*p != '/') return error(0,"unexpected char %c",*p);

    p++;
    while (*p >= '0' && *p <= '9') z = z * 10 + (*p++ - '0');
    if (*p != '/') return error(0,"unexpected char %c",*p);

    p++;
    while (*p >= '0' && *p <= '9') y = y * 10 + (*p++ - '0');
    if (*p != '/') return error(0,"unexpected char %c",*p);

    p++;
    while (*p >= '0' && *p <= '9') x = x * 10 + (*p++ - '0');
    if (*p != '.') return error(0,"unexpected char %c",*p);
  }

  fmtstring(path,"%s/%02u/%03u/%03u.bmp",Tileroot,z,y,x);

#if 0
  fmtstring(path,"%s/test.bmp",Tileroot);

  return showtile(path);
#endif

  if (osexists(path)) {
    info(0,"%s exists",path);
    return showtile(path);
  }
  info(0,"%s does not exist",path);

  if (query(z,y,x)) return 1;

  ub4 iterlim = 200;
  while (iterlim && osexists(path) == 0) {
    if (globs.sigint) return 1;
    osmillisleep(20);
    iterlim--;
  }
  if (iterlim == 0) {
    info0(0,"no response");
//    notile();
    return 1;
  }
  info(0,"%s exists",path);
  return showtile(path);
}

static int cmd_vrb(struct cmdval *cv) {
  if (cv->valcnt) globs.msglvl = cv->uval + Error;
  else globs.msglvl++;
  setmsglvl(globs.msglvl,0,globs.limassert);
  return 0;
}

static int cmd_limassert(struct cmdval *cv) {
  globs.limassert = cv->uval;
  setmsglvl(globs.msglvl,0,globs.limassert);
  return 0;
}

static int cmd_z(struct cmdval *cv) { test_z = cv->uval; return 0; }
static int cmd_y(struct cmdval *cv) { test_y = cv->uval; return 0; }
static int cmd_x(struct cmdval *cv) { test_x = cv->uval; return 0; }

static int cmd_testonly(struct cmdval *cv) { testonly = 1; return info(V0,"%s set",cv->subarg); }

static int cmd_arg(struct cmdval *cv)
{
  ub4 argc = globs.argc;
  char *dst;
  ub4 maxlen = sizeof(globs.args[0]);

  if (argc + 1 >= Elemcnt(globs.args)) return error(0,"exceeded %u arg limit",argc);

  dst = globs.args[argc];
  vrb(0,"add arg %s", cv->sval);
  strncpy(dst, cv->sval,maxlen-1);
  globs.argc = argc + 1;
  return 0;
}

static struct cmdarg cmdargs[] = {
  { "verbose|v", "[level]%u", "set or increase verbosity", cmd_vrb },
  { "assert-limit", "[limit]%u", "stop at this #assertions", cmd_limassert },
  { "z", "[z]%u", "z", cmd_z },
  { "y", "[y]%u", "y", cmd_y },
  { "x", "[x]%u", "x", cmd_x },
  { "t", NULL, "test only",cmd_testonly },
  { NULL, "dir", "netserve", cmd_arg }
};

int main(int argc, char *argv[],char *envp[])
{
  init0(argv[0]);

  if (cmdline(argc,argv,cmdargs,"vis")) return 1;

  fmtstring(globs.querydir,"%s",Querydir);

  if (vis(envp)) return 1;

  return 0;
}
