// tripover.c - main program

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* Perform initialisation and setup
   Enter a loop processing queries
   Initially, only direct commandline queries
*/

#include <string.h>

#include "base.h"
struct globs globs;

#include "time.h"
#include "cfg.h"
#include "os.h"
#include "mem.h"
#include "util.h"
#include "math.h"
#include "thread.h"
// #include "hash.h"

static ub4 msgfile;
#include "msg.h"
ub4 msgfile_h;

#include "iadr.h"
#include "server.h"

#include "netbase.h"
#include "netio.h"
#include "osm.h"
#include "gtfs.h"
#include "event.h"
#include "net.h"
#include "net1.h"
#include "net2.h"
#include "net3.h"
#include "netev.h"
#include "netprep.h"
#include "compound.h"
#include "search.h"
#include "fare.h"

static const char copyright[] = "Copyright (C) 2014-2017 Joris van der Geer";

static int streq(const char *s,const char *q) { return !strcmp(s,q); }

static int init0(char *progname,enum Msgopts msgopts)
{
  char *p;

  setsigs();

  p = strrchr(progname,'/');
  globs.progname = (p ? p + 1 : progname);

  if (inimsg(progname,"tripover",msgopts)) return 1;
  msgfile = setmsgfile(__FILE__);
  msgfile_h = setmsgfile("msg.h");
  iniassert();

  inimem();

  show_version();
  info(User,"%s",copyright);

  inibase();
  if (iniutil(0)) return 1;
  initime(0);
  if (inicfg()) return 1;
  iniiadr();
  inios();
  iniserver();
  inimath();
  inithread();
  ininetbase();
  iniosm();
  inigtfs();
  ininet();
  ininet1();
  ininet2();
  ininet3();
  ininetio();
  ininetev();
  ininetprep();
  inievent(0);
  inicompound();
  inisearch();
  inifare();
  return 0;
}

static int do_eximsg; // enable at net init

static int background;

static void exit0(void)
{
  exiutil();
  exitime();
  eximem();
  if (do_eximsg) eximsg(1);
}

static int do_params(void)
{
  ub4 walklimit,sumwalklimit,walkspeed;

  // check params
  walklimit = globs.netvars[Net_walklimit];
  sumwalklimit = globs.netvars[Net_sumwalklimit];
  if (sumwalklimit < walklimit) {
    warn(0,"max distance for single go walk %u above summed max %u",walklimit,sumwalklimit);
    sumwalklimit = walklimit;
  }

  walkspeed = globs.netvars[Net_walkspeed];
  if (walkspeed == 0) {
    warn(0,"walk speed zero for max distance %u",walklimit);
  }
  globs.walkspeed = walkspeed;
  globs.walklimit = walklimit;
  globs.sumwalklimit = sumwalklimit;

  globs.net1walklimit = globs.netvars[Net_net1walklimit];
  globs.net2walklimit = globs.netvars[Net_net2walklimit];

  globs.taxilimit = globs.netvars[Net_taxilimit];
  globs.taxilimitgnd = globs.netvars[Net_taxilimitgnd];

  globs.dirconlimit = globs.netvars[Net_dirconlimit];

  globs.net1timlim = globs.netvars[Net_net1timlim];
  globs.net2timlim = globs.netvars[Net_net2timlim];
  globs.net3timlim = globs.netvars[Net_net3timlim];

  globs.net2altlim = globs.netvars[Net_net2altlim];
  globs.net3altlim = globs.netvars[Net_net3altlim];

  globs.net1limit[0] = globs.netvars[Net_net1limitlo];
  globs.net1limit[1] = globs.netvars[Net_net1limitmi];
  globs.net1limit[2] = globs.netvars[Net_net1limithi];

  globs.net2limit[0] = globs.netvars[Net_net2limitlo];
  globs.net2limit[1] = globs.netvars[Net_net2limitmi];
  globs.net2limit[2] = globs.netvars[Net_net2limithi];

  globs.net3limit[0] = globs.netvars[Net_net3limitlo];
  globs.net3limit[1] = globs.netvars[Net_net3limitmi];
  globs.net3limit[2] = globs.netvars[Net_net3limithi];

  globs.net1con[0] = globs.netvars[Net_net1conlo];
  globs.net1con[1] = globs.netvars[Net_net1conmi];
  globs.net1con[2] = globs.netvars[Net_net1conhi];

  globs.net2con[0] = globs.netvars[Net_net2conlo];
  globs.net2con[1] = globs.netvars[Net_net2conmi];
  globs.net2con[2] = globs.netvars[Net_net2conhi];

  globs.net3con[0] = globs.netvars[Net_net3conlo];
  globs.net3con[1] = globs.netvars[Net_net3conmi];
  globs.net3con[2] = globs.netvars[Net_net3conhi];

  globs.net1above = globs.netvars[Net_net1above];
  globs.net2above = globs.netvars[Net_net2above];
  globs.net3above = globs.netvars[Net_net3above];

  globs.eventzlo = globs.netvars[Net_eventzlo];

  globs.allocrep = globs.engvars[Eng_allocrep];

  ub4 t0_cd = globs.netvars[Net_period0];
  ub4 t1_cd = globs.netvars[Net_period1];

  ub4 t0,t1;
  t0_cd = max(t0_cd,Epoch);
  t1_cd = max(t1_cd,Epoch);
  t0_cd = min(t0_cd,Era);
  t1_cd = min(t1_cd,Era);
  t0_cd = min(t0_cd,t1_cd);
  t0 = cd2day(t0_cd);
  t1 = cd2day(t1_cd);
  globs.periodt0 = t0;
  globs.periodt1 = t1;

  ub4 st0_cd = globs.netvars[Net_tpat0];
  ub4 st1_cd = globs.netvars[Net_tpat1];

  if (st0_cd >= st1_cd) return error(0,"patternstart %u not below patternend %u",st0_cd,st1_cd);
  st0_cd = max(st0_cd,Epoch);
  st1_cd = max(st1_cd,Epoch);
  st0_cd = min(st0_cd,Era);
  st1_cd = min(st1_cd,Era);
  st0_cd = min(st0_cd,st1_cd);
  if (st0_cd >= st1_cd) return error(0,"patternstart %u not below patternend %u",st0_cd,st1_cd);
  t0 = cd2day(st0_cd);
  t1 = cd2day(st1_cd);
  globs.pat0 = t0;
  globs.pat1 = t1;
  return 0;
}

// init network
static int initnet(struct network *glnet)
{
  netbase *basenet = getnetbase();
  int rv = 0;

  if (*globs.netdir == 0) return 1;

  if (dorun(FLN,Runread,0)) rv = readextnet(basenet,globs.netdir);
  else return 0;
  if (rv) return rv;

  if (dorun(FLN,Runbaseprep,0)) rv = prepbasenet();
  else return 0;
  if (rv) return rv;

  if (globs.writgtfs) rv = writegtfs(basenet,globs.netdir);
  if (rv) return rv;

  ub4 sparsethres = globs.netvars[Net_sparsethres];

  glnet->sparsethres = sparsethres;
  glnet->gridscale = globs.netvars[Net_gridscale];

  if (dorun(FLN,Runprep,0)) rv = prepnet(basenet,glnet);
  else return 0;
  if (rv) return rv;

  rv = compound(glnet);
  if (rv) return rv;

  return rv;
}

static int do_main(void)
{
  ub4 argc = globs.argc;
  struct mysfile nd;
  const char *cmdstr;
  char logdir[1024];
  int rv;
  double lat1,lat2,lon1,lon2,dist;

  if (argc == 0) return shortusage();

  cmdstr = globs.args[0];
  if (*cmdstr == 0) return shortusage();

  if (streq(cmdstr,"run")) {
    info0(0,"command 'run'");
  } else if (streq(cmdstr,"gtfsout")) {
    info0(0,"cmd: 'gtfsout' TODO: read net, process events and write normalised gtfs");
    globs.stopat = Runprep;
    globs.writgtfs = 1;
  } else if (streq(cmdstr,"init")) {
    return 0;
  } else if (streq(cmdstr,"geo")) {
    str2dbl(globs.args[1],20,&lat1);
    str2dbl(globs.args[2],20,&lon1);
    str2dbl(globs.args[3],20,&lat2);
    str2dbl(globs.args[4],20,&lon2);
    lat1 = (lat1 * M_PI) / 180.0;
    lon1 = (lon1 * M_PI) / 180.0;
    lat2 = (lat2 * M_PI) / 180.0;
    lon2 = (lon2 * M_PI) / 180.0;
    dist = geodist(lat1,lon1,lat2,lon2,"test");
    info(0,"%f",dist);
    return 0;
  } else return error(0,"unknown command '%s': known are 'run','init'",cmdstr);

  if (argc < 2) return error0(0,"commands 'run' and 'gtfsout' need network dir arg");
  strcopy(globs.netdir,globs.args[1]);

  if (*globs.netdir) {
    oclear(nd);
    if (osfileinfos(&nd,globs.netdir)) return oserror(0,"cannot access net directory %s",globs.netdir);
    else if (nd.isdir == 0) return error(0,"net arg %s is not a directory",globs.netdir);
    if (setmsglog(globs.netdir,"tripover",0,1)) return 1;

    fmtstring(logdir,"%s/log",globs.netdir);
    rv = osexists(logdir);
    if (rv == -1) return oserror(0,"cannot access dir %s",logdir);
    else if (rv == 0) {
      if (osmkdir(logdir)) return oserror(0,"cannot create dir %s",logdir);
    }
  }

  char nowstr[64];
  ub4 now = gettime_sec();
  sec70toyymmdd(now,12,nowstr,sizeof(nowstr));
  info(0,"starting at %s utc",nowstr);

  inievent(1);

  oslimits();

  do_eximsg = 1;

  if (background) osbackground();

  if (loadplans()) return 1;

  struct network *net = getnet();

  if (initnet(net)) return 1;

  if (mknet(globs.maxstops,net)) return 1;

  if (globs.testcnt > 1 && globs.netok) {
    ub4 dep,arr,lostop = 0, histop = 3;
    static search src;

    oclear(src);

    dep = globs.testset[0];
    arr = globs.testset[1];
    if (globs.testcnt > 3) {
      lostop = globs.testset[2];
      histop = globs.testset[3];
    }
    info(0,"test plan %u to %u minstop %u maxstop %u",dep,arr,lostop,histop);

    rv = plantrip(&src,(char *)"buildin test",dep,arr,lostop,histop);
    if (rv) warning(0,"search returned error %d",rv);
    else if (src.trips[0].len) info(0,"%u to %u = \av%u%p distance %u\n",dep,arr,src.lostop+2,(void *)src.trips[0].port,src.lodist);
    else info(0,"%u to %u : no trip\n",dep,arr);
  }

  showmemsums();

  if (dyncfg("tripover.chktmp",1,1)) achktmpfree();

  if (globs.netok && dorun(FLN,Runserver,0)) {

    info(0,"overall schedule period \ad%u to \ad%u",net->tt0,net->tt1);
    info(0,"connectivity precomputed for %u transfer\as",net->histop);
    info(0,"max walking distance %u m, summed %u",geo2m(net->walklimit),geo2m(net->sumwalklimit));
    return serverloop();
  }

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
  setmsglvl(globs.msglvl,globs.msgslvl);
  return 0;
}

static int cmd_id(struct cmdval *cv) {
  globs.id = cv->uval;
  return 0;
}

static int cmd_max(struct cmdval *cv) {
  ub4 val = cv->uval | Cfgcl | Cfgdef;

  if (streq(cv->subarg,"stops")) globs.maxstops = val;
  return 0;
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

static int cmd_cfg(struct cmdval *cv)
{
  strcopy(globs.cfgfile, cv->sval);
  return 0;
}

static int cmd_osm(struct cmdval *cv)
{
  strcopy(globs.osmfile, cv->sval);
  return 0;
}

static int cmd_stopat(struct cmdval *cv)
{
  strcopy(globs.stopatstr, cv->sval);

  return 0;
}

static int cmd_bg(struct cmdval *cv)
{
  background = 1;
  return info(0,"%s set",cv->subarg);
}

static int cmd_strict(struct cmdval *cv)
{
  globs.strict = 1;
  return info(0,"%s set",cv->subarg);
}

static int cmd_once(struct cmdval *cv)
{
  globs.once = 1;
  return info(0,"%s set",cv->subarg);
}

// set beforehand in precmdline
static int cmd_msgopt(struct cmdval *cv)
{
  return info(0,"%s set to %s",cv->subarg,cv->sval);
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
  { "msgopt", "sSpP", "set message options for stamp and filepos", cmd_msgopt },
  { "max-stops", "limit%u", "limit #stops", cmd_max },
  { "strict|b",NULL,"strict mode",cmd_strict },
  { "background|b",NULL,"run in background",cmd_bg },
  { "once",NULL,"single query only",cmd_once },
  { "stopat|runto","stage","run only up to the given stage",cmd_stopat },
  { "osm","file","load openstreetmap file",cmd_osm },
  { ".test-a", "test%u", "test", cmd_test },
  { ".test-b", "test%u", "test", cmd_test },
  { ".test-set", "test%u", "tests", cmd_test },
  { "config|c", "file", "specify config file", cmd_cfg },
  { "instance|i", "[ID]%u", "set instance ID", cmd_id },
  { NULL, "nets...", "tripover", cmd_arg }
};

int main(int argc, char *argv[])
{
  int rv = 1;
  char buf[256];
  ub4 pos;
  char c,*msgstr;
  ub2 msgopts = Msg_stamp|Msg_pos|Msg_type|Msg_show;

  // temporary defaults
  globs.msglvl = Info;
  globs.msgslvl = 0;
  strcopy(globs.querydir,"queries");
  globs.tidcnt = 1;

  if (precmdline(argc,argv,"-msgopt",&msgstr)) {
    while ( (c = *msgstr++) ) {
      switch(c) {
      case 's': msgopts &= ~Msg_stamp; break;
      case 'S': msgopts |=  Msg_stamp; break;
      case 'p': msgopts &= ~Msg_pos; break;
      case 'P': msgopts |=  Msg_pos; break;
      info(User,"-msgopt: expected one of [sSpP], found '%c': ",c);
      default: break;
      }
    }
  }

  setmsglvl(globs.msglvl,globs.msgslvl);
  if (init0(argv[0],msgopts)) return 1;
  fmtstring(globs.cfgfile,"%s.cfg",globs.progname);

  if (cmdline(argc,argv,cmdargs,Program_desc)) return 1;

  if (inicfgcl()) return 1;

  if (globs.argc == 0) return shortusage();

  if (globs.netdir[0] == 0) globs.netdir[0] = '.';

  info(V0,"verbosity %u.%u",globs.msglvl,globs.msgslvl);

  const char *cfgfile = globs.cfgfile;
  if (globs.argc == 1 && streq(globs.args[0],"init")) {
    info(0,"prepare new default config in %s",cfgfile);
    osremove(cfgfile);
  }

  if (readcfg(cfgfile)) return 1;

  iniutil(1);
  initime(1);

  if (do_params()) return 1;

  memcfg(globs.maxvm,globs.allocrep);

  rv = do_main();

  exit0();

  if (rv) {
    pos = fmtstring(buf,"\nrv=%d\n",rv);
    msg_write(buf,pos);
  }
  return rv;
}
