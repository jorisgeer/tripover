// cfg.c - process configuration file

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* process config file
 */

#include <string.h>

#include "base.h"
#include "mem.h"
#include "util.h"

#define Chkfmt
static ub4 msgfile;
#include "msg.h"

#include "cfg.h"
#include "time.h"

#define Varlen 64
#define Vallen 256

static ub4 linno,colno;
static const char *cfgname;

static const char *lvlnames[Runcnt+1];
static ub4 setruns[Runcnt]; // line number where set

const char *runlvlnames(enum Runlvl lvl)
{
  return lvlnames[min(lvl,Runcnt)];
}

static int streq(const char *s,const char *q) { return !strcmp(s,q); }

int inicfgcl(void)
{
  enum Runlvl l,lvl = 0;
  ub4 pos,v;
  char buf[1024];
  char *stagename = globs.stopatstr;

  if (*stagename) {
    if (str2ub4(stagename,&v)) lvl = v;
    else { while (lvl < Runcnt && strcomp(globs.stopatstr,lvlnames[lvl])) lvl++; }

    if (lvl >= Runcnt) {
      pos = fmtstring(buf,"%u known stages:\n   ", Runcnt);
      for (l = 0; l < Runcnt; l++) pos += mysnprintf(buf,pos,sizeof(buf),"%s ",lvlnames[l]);
      info0(0,buf);
      ret_error(0,"unknown stage for cmdline '-stopat=%s'",globs.stopatstr);
    }
    info(0,"stop at stage %s:%u (commandline)",lvlnames[lvl],lvl);
    globs.stopatcl = lvl;
  } else globs.stopatcl = Runcnt;
  return 0;
}

enum Cfgvar {
  Maxstops,
  Maxvm,
  Threads,
  Querydir,
  Stopat,Enable,Disable,
  Net_gen,
  Net2pdf,Net2ext,
  Section,
  Eng_gen,
  Eng_opt,
  Cfgcnt
 };

enum Cfgcnv { String,Uint,EnumRunlvl,Bool,None };

static struct cfgvar {
  const char *name;
  enum Cfgcnv cnv;
  enum Cfgvar var;
  ub4 subvar;
  ub4 lo,hi,def,errlim;
  const char *desc;
} cfgvars[] = {

  {"limits",Bool,Section,0,0,0,0,0,"limits"},

  // Netn
  {"maxstops",Uint,Maxstops,0,0,2,1,1,"max transfers to precompute"},

  {"maxvm",Uint,Maxvm,0,1,hi24,hi24,0,"virtual memory limit in GB"},

  {"threads",Uint,Threads,0,1,Nthread / 2,2,0,"Number of threads"},

  {"run",Bool,Section,0,0,0,0,0,"determines which stages to run"},
  {"stopat",EnumRunlvl,Stopat,0,0,Runcnt,Runcnt,0,"stop at given stage"},
  {"enable",EnumRunlvl,Enable,0,0,1,1,0,"enable a given stage"},
  {"disable",EnumRunlvl,Disable,0,0,1,1,0,"disable a given stage"},

  {"network",Bool,Section,0,0,0,0,0,"network settings"},
  {"net.sparsethres",Uint,Net_gen,Net_sparsethres,0,100000,10000,0,"sparse address threshold"},

  {"net.walklimit",Uint,Net_gen,Net_walklimit,0,10000,2000,0,"maximum walk distance in meters for a single go"},
  {"net.walkspeed",Uint,Net_gen,Net_walkspeed,0,10000,5000,0,"walk speed in meters per hour"},
  {"net.sumwalklimit",Uint,Net_gen,Net_sumwalklimit,0,10000,3000,0,"maximum summed up walk distance in meters"},

  {"net.taxilimit",Uint,Net_gen,Net_taxilimit,0,100,8,0,"maximum taxi links per airport"},
  {"net.taxilimitgnd",Uint,Net_gen,Net_taxilimitgnd,0,100,4,0,"idem, ground hub"},

  {"net.gridscale",Uint,Net_gen,Net_gridscale,1,255,4,0,"grid scale"},

  {"net.eventzlo",Uint,Net_gen,Net_eventzlo,2,1024,8,0,"event compression threshold"},

  {"net.periodstart",Uint,Net_gen,Net_period0,20100101,20191231,20100101,0,"start day of schedule period"},
  {"net.periodend",Uint,Net_gen,Net_period1,20100101,20191231,20191231,0,"end day of schedule period"},
  {"net.patternstart",Uint,Net_gen,Net_tpat0,20100101,20191231,20160101,1,"start day of transfer pattern base"},
  {"net.patternend",Uint,Net_gen,Net_tpat1,20100101,20191231,20160121,1,"end day of transfer pattern base"},
  {"net.dirconlimit",Uint,Net_gen,Net_dirconlimit,1,65530,1024,0,"maximum direct connections per port pair"},

  {"net.net1timlim",Uint,Net_gen,Net_net1timlim,2,65536,100,0,"1-stop time limit in msec per port pair"},
  {"net.net2timlim",Uint,Net_gen,Net_net2timlim,2,65536,100,0,"2-stop time limit in msec per port pair"},
  {"net.net3timlim",Uint,Net_gen,Net_net3timlim,2,65536,100,0,"3-stop time limit in msec per port pair"},

  {"net.net2altlim",Uint,Net_gen,Net_net2altlim,2,hi32,4096,0,"combinations to assess per port pair"},
  {"net.net3altlim",Uint,Net_gen,Net_net3altlim,2,hi32,256,0,"combinations to assess per port pair"},

  {"net.net1walklimit",Uint,Net_gen,Net_net1walklimit,0,10000,1000,0,"maximum 1-stop walk distance in meters for a single go"},
  {"net.net2walklimit",Uint,Net_gen,Net_net2walklimit,0,10000,800,0,"maximum 2-stop walk distance in meters for a single go"},

  {"net.net1limitlo",Uint,Net_gen,Net_net1limitlo,0,4096,4,0,"maximum 1-stop connections per low-con port pair"},
  {"net.net1limitmi",Uint,Net_gen,Net_net1limitmi,0,4096,8,0,"maximum 1-stop connections per mid-con port pair"},
  {"net.net1limithi",Uint,Net_gen,Net_net1limithi,0,4096,16,0,"maximum 1-stop connections per hi-con port pair"},

  {"net.net2limitlo",Uint,Net_gen,Net_net2limitlo,0,4096,2,0,"maximum 2-stop connections per low-con port pair"},
  {"net.net2limitmi",Uint,Net_gen,Net_net2limitmi,0,4096,4,0,"maximum 2-stop connections per mid-con port pair"},
  {"net.net2limithi",Uint,Net_gen,Net_net2limithi,0,4096,8,0,"maximum 2-stop connections per hi-con port pair"},

  {"net.net3limitlo",Uint,Net_gen,Net_net3limitlo,0,4096,2,0,"maximum 3-stop connections per low-con port pair"},
  {"net.net3limitmi",Uint,Net_gen,Net_net3limitmi,0,4096,4,0,"maximum 3-stop connections per mid-con port pair"},
  {"net.net3limithi",Uint,Net_gen,Net_net3limithi,0,4096,6,0,"maximum 3-stop connections per hi-con port pair"},

  {"net.net1conlo",Uint,Net_gen,Net_net1conlo,0,4096,1,0,"minimum 1-stop connectivity for low inclusion"},
  {"net.net1conmi",Uint,Net_gen,Net_net1conmi,0,4096,1,0,"minimum 1-stop connectivity for mid inclusion"},
  {"net.net1conhi",Uint,Net_gen,Net_net1conhi,0,4096,13,0,"minimum 1-stop connectivity for hi inclusion"},

  {"net.net2conlo",Uint,Net_gen,Net_net2conlo,0,4096,5,0,"minimum 2-stop connectivity for low inclusion"},
  {"net.net2conmi",Uint,Net_gen,Net_net2conmi,0,4096,9,0,"minimum 2-stop connectivity for mid inclusion"},
  {"net.net2conhi",Uint,Net_gen,Net_net2conhi,0,4096,13,0,"minimum 2-stop connectivity for hi inclusion"},

  {"net.net3conlo",Uint,Net_gen,Net_net3conlo,0,4096,13,0,"minimum 3-stop connectivity for low inclusion"},
  {"net.net3conmi",Uint,Net_gen,Net_net3conmi,0,4096,25,0,"minimum 3-stop connectivity for mid inclusion"},
  {"net.net3conhi",Uint,Net_gen,Net_net3conhi,0,4096,55,0,"minimum 3-stop connectivity for hi inclusion"},

  {"net.net1above",Uint,Net_gen,Net_net1above,0,4096,50,0,"minimum distance for 1-stop connection"},
  {"net.net2above",Uint,Net_gen,Net_net2above,0,4096,100,0,"minimum distance for 2-stop connection"},
  {"net.net3above",Uint,Net_gen,Net_net3above,0,4096,200,0,"minimum distance for 3-stop connection"},

  // interface
  {"interface",Bool,Section,0,0,0,0,0,"configure client-server interface"},
  {"querydir",String,Querydir,0,0,0,0,0,"client query queue directory"},

  {"files",Bool,Section,0,0,0,0,0,"determines which files to generate"},
  {"net.pdf",Bool,Net2pdf,0,0,1,0,0,"write network to pdf"},
  {"net.ext",Bool,Net2ext,0,0,1,0,0,"write network to ext"},

  {"engineering",Bool,Section,0,0,0,0,0,"engineering settings"},
  {"eng.periodlim",Uint,Eng_gen,Eng_periodlim,0,365 * 20,365 * 10,0,"schedule period limit"},
  {"eng.conncheck",Uint,Eng_gen,Eng_conchk,0,256,1,0,"check connectivity"},
  {"eng.allocrep",Uint,Eng_gen,Eng_allocrep,0,8192,64,0,"alloc reporting limit in MB"},
  {"eng.options",String,Eng_opt,0,0,0,0,0,"engineering options"},
  {NULL,0,0,0,0,0,0,0,NULL}
};

int inicfg(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();

  lvlnames[Runread] = "readnet";
  lvlnames[Runbaseprep] = "prepbase";
  lvlnames[Runprep] = "prepnet";
  lvlnames[Runmknet] = "mknet";
  lvlnames[Runnet0] = "mknet0";
  lvlnames[Runcompound] = "compound";
  lvlnames[Runnetn] = "mknetn";
  lvlnames[Runserver] = "server";
  lvlnames[Runend] = "end";
  lvlnames[Runcnt] = "end";

  struct cfgvar *vp;
  ub4 now;

  // determine some defaults at runtime
  for (vp = cfgvars; vp->name; vp++) {
    if (vp->var != Net_gen) continue;
    switch(vp->subvar) {
    case Net_tpat0:
      now = nix2min(gettime_sec() / 60);
      vp->def = day2cd(now / 1440);
      break;
    case Net_tpat1:
      now = nix2min(gettime_sec() / 60);
      vp->def = day2cd(now / 1440 + 30);
      break;

    default: break;
    }
  }

  return 0;
}

static int varseen[Cfgcnt];

static int memeq(const char *s,const char *q,ub4 n) { return !memcmp(s,q,n); }

static int writecfg(int havecfg,const char *cname)
{
  struct cfgvar *vp = cfgvars;
  ub4 uval,pos;
  ub4 now;
  int fd;
  char fname[1024];
  char buf[4096];
  char nowstr[64];
  const char *name;
  const char *desc;
  char *sval;
  enum Runlvl lvl;
  const char *origin;

  if (havecfg) {
    fmtstring(fname,"%s/%s-%u.cur",globs.netdir,cname,globs.id);
  } else {
    fmtstring(fname,"%s/%s",globs.netdir,cname);
  }
  fd = filecreate(fname,1);
  if (fd == -1) return 1;

  now = gettime_sec();
  sec70toyymmdd(now,10,nowstr,sizeof(nowstr));
  if (havecfg) {
    pos = fmtstring(buf,"# tripover %u.%u config in effect at %s\n\n",Version_maj,Version_min,nowstr);
    pos += mysnprintf0(buf,pos,sizeof(buf),"# name value  '#' origin description default\n\n");
  } else {
    pos = fmtstring(buf,"# tripover %u.%u config created at %s\n\n",Version_maj,Version_min,nowstr);
    pos += mysnprintf0(buf,pos,sizeof(buf),"# name value  '#' description default\n\n");
  }
  if (filewrite(fd,buf,pos,fname)) return 1;

  ub4 showcfg = dyncfg("cfg.showcfg",1,0);

  if (showcfg) { info0(0,"config in effect:\n"); }

  for (vp = cfgvars; vp->name; vp++) {
    name = vp->name;
    if (*name == '.') continue; // hidden
    desc = vp->desc;

    if (vp->var == Enable || vp->var == Disable) continue;
    else if (vp->var == Section) {
      pos = fmtstring(buf,"\n[%s] - %s\n",name,desc);
      if (filewrite(fd,buf,pos,fname)) return 1;
      continue;
    }

    uval = 0;
    sval = (char *)"";
    switch(vp->var) {
    case Maxstops: uval = globs.maxstops; break;
    case Maxvm:    uval = globs.maxvm; break;
    case Threads:  uval = globs.tidcnt; break;
    case Querydir: sval = globs.querydir; break;
    case Stopat:   uval = globs.stopat; break;
    case Enable: case Disable: break;
    case Net2pdf:  uval = globs.writpdf; break;
    case Net2ext:  uval = globs.writext; break;
    case Eng_gen:  uval = globs.engvars[vp->subvar]; break;
    case Net_gen:  uval = globs.netvars[vp->subvar]; break;
    case Eng_opt: break;
    case Cfgcnt: case Section: break;
    }

    if (havecfg == 0) origin = "";
    else if (uval & Cfgcl) origin = "cmdln ";
    else if (uval & Cfgdef) origin = ".cfg ";
    else origin = "def  ";
    uval &= ~(Cfgcl | Cfgdef);

    switch(vp->cnv) {
    case Uint:       pos = fmtstring(buf,"%s %u\t# %s%s [%u]\n",name,uval,origin,desc,vp->def); break;
    case Bool:       pos = fmtstring(buf,"%s %u\t# %s%s [%u]\n",name,uval,origin,desc,vp->def); break;
    case EnumRunlvl: if (uval <= Runcnt) pos = fmtstring(buf,"%s %s=%u\t# %s%s\n",name,lvlnames[uval],uval,origin,desc);
                     else pos = fmtstring(buf,"%s unknown-%u\t# %s%s\n",name,uval,origin,desc);
                     break;
    case String:     pos = fmtstring(buf,"%s %s\t# %s%s\n",name,sval,origin,desc);break;
    case None:       pos = fmtstring(buf,"%s\t# %s%s\n",name,origin,desc);break;
    }
    if (showcfg) msg_write(buf,pos);
    if (filewrite(fd,buf,pos,fname)) return 1;
  }
  if (showcfg) msg_write("\n",1);
  if (filewrite(fd,"\n",1,fname)) return 1;

  for (lvl = 0; lvl < Runcnt; lvl++) {
    if (globs.doruns[lvl]) pos = fmtstring(buf,"enable %s\n",lvlnames[lvl]);
    else pos = fmtstring(buf,"disable %s\n",lvlnames[lvl]);
    if (filewrite(fd,buf,pos,fname)) return 1;
  }

  fileclose(fd,fname);
  info(0,"wrote config to %s",fname);
  return 0;
}

static int limitval(struct cfgvar *vp,ub4 *puval)
{
  ub4 newval,defcl;

  defcl = *puval & (Cfgdef | Cfgcl);
  if (*puval & Cfgdef) newval = *puval & ~(Cfgcl | Cfgdef);
  else newval = vp->def;
  if (newval < vp->lo) {
    if (vp->errlim) { ret_error(0,"config var %s below %u",vp->name,vp->lo); }
    newval = vp->lo;
    warning(0,"config var %s below %u",vp->name,vp->lo);
  } else if (newval > vp->hi) {
    if (vp->errlim) { ret_error(0,"config var %s above %u",vp->name,vp->hi); }
    newval = vp->hi;
    warning(0,"config var %s above \ah%u",vp->name,vp->hi);
  }
  *puval = newval | defcl;
  return 0;
}

static int limitvals(void)
{
  struct cfgvar *vp;
  int rv = 0;

  for (vp = cfgvars; vp->name; vp++) {
    switch(vp->var) {
    case Maxstops: rv = limitval(vp,&globs.maxstops); break;
    case Maxvm:    rv = limitval(vp,&globs.maxvm); break;
    case Threads:  rv = limitval(vp,&globs.tidcnt); break;
    case Stopat: rv = limitval(vp,&globs.stopat); break;
    case Enable: case Disable: break;
    case Net2pdf: rv = limitval(vp,&globs.writpdf); break;
    case Net2ext: rv = limitval(vp,&globs.writext); break;
    case Querydir: break;
    case Eng_gen:  rv = limitval(vp,globs.engvars + vp->subvar); break;
    case Net_gen:  rv = limitval(vp,globs.netvars + vp->subvar); break;
    case Eng_opt: break;
    case Cfgcnt: case Section: break;
    }
    if (rv) return 1;
  }
  return rv;
}

static void finalval(ub4 *puval)
{
  *puval &= ~(Cfgcl | Cfgdef);
}

static void finalize(void)
{
  struct cfgvar *vp;

  for (vp = cfgvars; vp->name; vp++) {
    switch(vp->var) {
    case Maxstops: finalval(&globs.maxstops); break;
    case Maxvm:    finalval(&globs.maxvm); break;
    case Threads:  finalval(&globs.tidcnt); break;
    case Stopat: finalval(&globs.stopat); break;
    case Enable: case Disable: break;
    case Net2pdf: finalval(&globs.writpdf); break;
    case Net2ext: finalval(&globs.writext); break;
    case Eng_gen:  finalval(globs.engvars + vp->subvar); break;
    case Net_gen:  finalval(globs.netvars + vp->subvar); break;
    case Querydir: break;
    case Eng_opt: break;
    case Cfgcnt: case Section: break;
    }
  }
}

static void setval(struct cfgvar *vp,ub4 *puval,ub4 newval)
{
  if (*puval & Cfgcl) { info(0,"config var %s set on commandline",vp->name); }
  else *puval = newval | Cfgdef;
}

static void eng_opt(const char *val,ub4 len)
{
  if (len == 9 && memeq(val,"no-msgsum",len)) globs.nomsgsum = 1;
  else if (len == 13 && memeq(val,"no-mergeroute",len)) globs.nomergeroute = 1;
  else if (len == 13 && memeq(val,"no-evcompress",len)) globs.noevcompress = 1;
  else if (len == 9 && memeq(val,"no-memsum",len)) globs.nomemsum = 1;
  else if (len == 10 && memeq(val,"no-reserve",len)) globs.noreserve = 1;
  else if (len == 7 && memeq(val,"no-walk",len)) globs.nowalk = 1;
  else if (len == 7 && memeq(val,"no-taxi",len)) globs.notaxi = 1;
  else if (len == 7 && memeq(val,"no-lotx",len)) globs.nolotx = 1;
  else if (len == 7 && memeq(val,"no-grid",len)) globs.nogrid = 1;
  else if (len) { warn(0,"line %u: ignoring unknown option %s",linno,val); }
}

static int addvar(char *varname,char *val,ub4 varlen,ub4 vallen)
{
  struct cfgvar *vp = cfgvars;
  ub4 n,prvline,len,uval = 0;
  const char *name,*eq;
  enum Cfgvar var;
  char fln[1024];

  varname[varlen] = 0;
  val[vallen] = 0;

  fmtstring(fln,"%s ln %u col %u var '%s': ",cfgname,linno,colno,varname);

  if (varlen == 0) { ret_warn(0,"%s: empty var",fln); }

  varname[varlen] = 0;
  while (vp->name) {
    name = vp->name;
    n = (ub4)strlen(name);
    if (n == varlen && memeq(name,varname,n)) break;
    vp++;
  }
  if (vp->name == NULL) { ret_warn(0,"%s: unknown config var",fln); }
  var = vp->var;
  error_ge(var,Cfgcnt);

  if (var != Enable && var != Disable && var != Eng_opt && var != Eng_gen && var != Net_gen) {
    prvline = varseen[var];
    if (prvline) { ret_warn(0,"%s: previously defined at line %u",fln,prvline); }
  }
  varseen[var] = linno;

  if (var != Enable && var != Disable && var != Eng_opt && var != Eng_gen) {
    if (vallen == 0) { ret_error(0,"%s: needs arg",fln); }
  } else if (vallen == 0) return 0;

  switch(vp->cnv) {

  case Uint: val[vallen] = 0;
             len = str2ub4(val,&uval);
             if (len == 0) { ret_error(0,"%s: needs numerical arg, has '%s'",fln,val); }
             if (len + 1 < vallen && val[len+1] >= '0' && val[len+1] <= '9') { ret_error(0,"%s: numerical arg '%s' appears as %u",fln,val,uval); }
             break;

  case Bool: if (vallen) {
               if (*val == '0' || *val == 'n' || *val == 'f') uval = 0;
               else if (*val == '1' || *val == 'y' || *val == 't') uval = 1;
             }
             break;

  case EnumRunlvl:
             eq = strchr(val,'=');
             if (eq) vallen = (ub4)(eq - val);
             val[vallen] = 0;
             uval = 0;
             while (uval < Runcnt && strcmp(lvlnames[uval],val)) uval++;
             if (uval >= Runcnt) { ret_error(0,"%s: unknown option '%s'",fln,val); }
             vrb(0,"%s: stage %s",varname,lvlnames[uval]);
             break;

  case String: break;
  case None: break;
  }

  switch(var) {
  case Maxstops: setval(vp,&globs.maxstops,uval); break;
  case Maxvm:    setval(vp,&globs.maxvm,uval); break;
  case Threads:  setval(vp,&globs.tidcnt,uval); break;
  case Querydir: memcpy(globs.querydir,val,min(vallen,sizeof(globs.querydir)-1)); break;
  case Stopat:   setval(vp,&globs.stopat,uval); break;
  case Enable:   if (setruns[uval]) { ret_error(0,"%s: previously set at line %u",val,setruns[uval]); }
                 globs.doruns[uval] = 1; setruns[uval] = linno;
                 break;
  case Disable:  if (setruns[uval]) { ret_error(0,"%s: previously set at line %u",val,setruns[uval]); }
                 globs.doruns[uval] = 0; setruns[uval] = linno;
                 break;
  case Net2pdf:  setval(vp,&globs.writpdf,uval); break;
  case Net2ext:  setval(vp,&globs.writext,uval); break;
  case Net_gen:  setval(vp,globs.netvars + vp->subvar,uval); break;
  case Eng_gen:  setval(vp,globs.engvars + vp->subvar,uval); break;
  case Eng_opt:  eng_opt(val,vallen); break;
  case Cfgcnt: case Section: break;
  }
  return 0;
}

static int rdcfg(const char *name,int *havecfg)
{
  struct myfile cfg;
  char fname[1024];
  enum states { Out,Var,Val0,Val,Val9,Fls } state;
  ub4 pos,len,varlen,vallen;
  char var[Varlen];
  char val[Vallen];
  int rv = 0;
  char *buf,c;

  fmtstring(fname,"%s/%s",globs.netdir,name);
  info(0,"check config in %s",fname);
  rv = readfile(&cfg,fname,0,65536);
  if (rv) return 1;

  if (cfg.exist == 0) {
    if (streq(globs.netdir,".")) return 0;
    info(0,"check config in %s",name);
    rv = readfile(&cfg,name,0,65536);
    if (rv) return 1;
    if (cfg.exist == 0) return 0;
  }

  *havecfg = 1;

  len = (ub4)cfg.len;
  vrb(0,"parse config in %s",fname);

  if (len == 0) return 0;

  buf = cfg.buf;

  cfgname = name;
  state = Out;
  pos = 0;
  linno = 1; colno = 1;
  varlen = vallen = 0;
  while(pos < len && rv == 0) {
    c = buf[pos++];
    if (c == '\n') { linno++; colno = 1; }
    else colno++;

    vrb(1,"state %u varlen %u",state,varlen);

    switch(state) {
    case Out:
      switch(c) {
      case '#': state = Fls; break;
      case '[': state = Fls; break;
      case '\n': break;
      case ' ': case '\t': break;
      default: var[0] = c; varlen = 1; state = Var;
      } break;

    case Var:
      if (varlen >= Varlen-1) { ret_error(0,"%s.%u: variable name exceeds %u chars",cfgname,linno, Varlen); }
      switch(c) {
      case '#': state = Val9; break;
      case '\n': rv = addvar(var,val,varlen,vallen); state = Out; break;
      case ' ': case '\t': case '=': vallen = 0; state = Val0; break;
      default: var[varlen++] = c;
      } break;

    case Val0:
      switch(c) {
      case '#': state = Val9; break;
      case '\n': rv = addvar(var,val,varlen,vallen); state = Out; break;
      case ' ': case '\t': case '=': break;
      default: val[0] = c; vallen = 1; state = Val;
      } break;

    case Val:
      if (vallen >= Vallen-1) { ret_error(0,"%s.%u: variable exceeds %u chars",cfgname,linno, Vallen); }
      switch(c) {
      case '#': state = Val9; break;
      case '\n': rv = addvar(var,val,varlen,vallen); state = Out; break;
      case ' ': case '\t': state = Val9; break;
      default: val[vallen++] = c;
      } break;

    case Val9:
      if (c == '\n') state = Out;
      else state = Fls;
      if (varlen) rv = addvar(var,val,varlen,vallen);
      break;

    case Fls:
      if (c == '\n') state = Out;
      break;
    } // switch state

    if (rv) return rv;

  } // each char
  switch(state) {
  case Var: case Val0: case Val: case Val9: rv = addvar(var,val,varlen,vallen); break;
  case Out: case Fls: break;
  }

  if (rv) return rv;

  return 0;
}

int readcfg(const char *name)
{
  int havecfg = 0;

  error_ge(Eng_cnt,Elemcnt(globs.engvars));

  if (rdcfg(name,&havecfg)) return 1;
  if (limitvals()) return 1;
  writecfg(havecfg,name);
  finalize();
  globs.stopat = min(globs.stopat,globs.stopatcl);
  vrb(0,"done config file %s",name);
  infocc(globs.stopat < Runend,0,"stop at %s",lvlnames[globs.stopat]);
  return 0;
}
