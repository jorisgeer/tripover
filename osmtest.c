// osmtest.c - test osm

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015 Joris van der Geer.
 */

#include <string.h>

#include "base.h"
struct globs globs;

#include "time.h"
#include "os.h"
#include "mem.h"
#include "util.h"
#include "math.h"
#include "cfg.h"

static ub4 msgfile;
#include "msg.h"

#include "osm.h"
#include "osmint.h"

static int streq(const char *s,const char *q) { return !strcmp(s,q); }

static int init0(char *progname)
{
  char *p;

  setsigs();

  p = strrchr(progname,'/');
  globs.progname = (p ? p + 1 : progname);

  if (inimsg(progname,"osmtest",Msg_stamp|Msg_pos|Msg_type|Msg_show|Msg_bcklog)) return 1;
  msgfile = setmsgfile(__FILE__);
  iniassert();

  inibase();
  if (iniutil(0)) return 1;
  initime(0);
  inimem();
  inios();
  inimath();
  iniosm();
  return 0;
}

static void exit0(void)
{
  exiutil();
  exitime();
//  eximem();
//  eximsg(1);
}

static int do_main(void)
{
  ub4 argc = globs.argc;
  const char *osmname;
  ub4 i,cnt = 0,dnid = hi32,anid = hi32;
  const double pi180 = M_PI / 180;
  struct osmres res;
  struct node *nodes,*pdep,*parr;

  if (argc == 0) return shortusage();

  osmname = globs.args[0];
  if (*osmname == 0) return shortusage();

  void *vosm = readosm(osmname,NULL);
  if (vosm == NULL) return 1;
  struct onet *osm = (struct onet *)vosm;

  ub4 nidcnt = osm->nidcnt;
  nodes = osm->nodes;

  // if (osmplan(vosm,5821564,8813624,hi32,Osfoot,Osm_show,&res)) return 1;
  // return 0;

  for (i = 0; i < 20000 && cnt < 200; i++) {
    dnid = rnd(nidcnt);
    pdep = nodes + dnid;
    if (pdep->wid == hi32 || pdep->jid == hi32) continue;

    anid = rnd(nidcnt);
    if (dnid == anid) continue;
    parr = nodes + anid;
    parr = nodes + anid;
    if (parr->wid == hi32 || parr->jid == hi32) continue;
    if (osmplan(vosm,dnid,anid,hi32,Osfoot,i < 3 ? Osm_show : 0,&res)) return 1;
    cnt++;
    info(0,"dist \ag%u",res.dist);
  }

  osmstats(vosm);

  // return 0;

  double lat,lon;
  struct node node1,node2;
  ub4 dist1,dist2;

  lat = -27.428306; lon = 152.935283;  // wollundry
  lat = -27.6130449; lon = 152.7608060;
  lat = -27.420111; lon = 152.937159; // cobalt

  node1.ilat = (ub4)((lat + 90) * Osmgeoscale);
  node1.ilon = (ub4)((lon + 180) * Osmgeoscale);
  node1.rlat = lat * pi180;
  node1.rlon = lon * pi180;

// lat = -27.6150149; lon = 152.7581159;
  lat = -27.441021; lon = 152.940407;  // chep
  node2.ilat = (ub4)((lat + 90) * Osmgeoscale);
  node2.ilon = (ub4)((lon + 180) * Osmgeoscale);
  node2.rlat = lat * pi180;
  node2.rlon = lon * pi180;

  ub4 n1 = lookupnid(vosm,node1.ilat,node1.ilon,Osfoot,&dist1);
  if (n1 >= nidcnt) return error(0,"n1 %u above %u",n1,nidcnt);

  ub4 n2 = lookupnid(vosm,node2.ilat,node2.ilon,Osfoot,&dist2);
  if (n2 >= nidcnt) return error(0,"n2 %u above %u",n2,nidcnt);

  info(0,"n1 %u n2 %u dist1 \ag%u dist2 \ag%u",n1,n2,dist1,dist2);
  if (osmplan(vosm,n1,n2,hi32,Osfoot,Osm_show,&res)) return error(0,"plan %u %u ",n1,n2);
  info(0,"dist \ag%u",res.dist);

  n1 = 728108; n2 = 162559;
  if (osmplan(vosm,n1,n2,hi32,Oscar,Osm_show,&res)) return error(0,"plan %u %u ",n1,n2);
  info(0,"dist \ag%u time %u min",res.dist,res.time);

  if (freeosm(vosm)) return 1;

  return 0;
}

static int cmd_vrb(struct cmdval *cv)
{
  ub4 val;
  if (cv->valcnt) {
    val = cv->uval;
    globs.msglvl = val / 2 + Error;
    globs.msgslvl = val & 1;
  } else {
    if (globs.msgslvl) {
      globs.msglvl++;
      globs.msgslvl = 0;
    } else globs.msgslvl = 1;
  }
  info(0,"msg lvl %u.%u",globs.msglvl,globs.msgslvl);
  setmsglvl(globs.msglvl,globs.msgslvl,globs.limassert);
  return 0;
}

static int cmd_limassert(struct cmdval *cv) {
  globs.limassert = cv->uval;
  setmsglvl(globs.msglvl,globs.msgslvl,globs.limassert);
  return info(0,"assert limit set to %u",cv->uval);
}

static int cmd_test(struct cmdval *cv) {
  if (streq(cv->subarg,"a")) globs.testa = cv->uval;
  else if (streq(cv->subarg,"b")) globs.testb = cv->uval;
  else if (streq(cv->subarg,"set") && globs.testcnt < Elemcnt(globs.testset)) {
    vrb(User,"test %u %u",globs.testcnt,cv->uval);
    globs.testset[globs.testcnt++] = cv->uval;
  } else info(User,"ignoring arg test-%s",cv->subarg);
  return 0;
}

static int cmd_osm(struct cmdval *cv)
{
  strcopy(globs.osmfile, cv->sval);
  return 0;
}

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
  { "osm","file","load openstreetmap file",cmd_osm },
  { ".test-a", "test%u", "test", cmd_test },
  { ".test-b", "test%u", "test", cmd_test },
  { ".test-set", "test%u", "tests", cmd_test },
  { NULL, "file...", "osmtest", cmd_arg }
};

int main(int argc, char *argv[])
{
  int rv = 1;

  // temporary defaults
  globs.msglvl = Info;
  globs.msgslvl = 0;
  globs.tidcnt = 1;

  setmsglvl(globs.msglvl,globs.msgslvl,0);
  if (init0(argv[0])) return 1;

  if (cmdline(argc,argv,cmdargs,Program_desc)) return 1;

  initime(1);

  if (globs.argc == 0) return shortusage();

  info(V0,"verbosity %u.%u",globs.msglvl,globs.msgslvl);

  iniutil(1);

  rv = do_main();

  exit0();

  errorcc(rv,0,"main returned %d",rv);

  return rv;
}
