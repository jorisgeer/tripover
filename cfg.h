// cfg.h

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

// search limits: practical

// max stops aka transfers supported (=15), plus a few for srcinf
#define Nstop 20

// not yet
#define Nvia 16

#define Maxquerysize (1024 * 64)

// time in seconds to accept a query
#define Queryage 3

// end of limits

enum Engvars { Eng_periodlim,Eng_conchk,Eng_allocrep,Eng_cnt };
enum Netvars {
  Net_sparsethres,
  Net_sumwalklimit,
  Net_walklimit,
  Net_walkspeed,
  Net_taxilimit,
  Net_taxilimitgnd,
  Net_gridscale,
  Net_eventzlo,
  Net_period0,
  Net_period1,
  Net_tpat0,
  Net_tpat1,
  Net_dirconlimit,
  Net_net1walklimit,
  Net_net2walklimit,
  Net_net1timlim,
  Net_net2timlim,
  Net_net3timlim,
  Net_net2altlim,
  Net_net3altlim,
  Net_net1limitlo,
  Net_net1limitmi,
  Net_net1limithi,
  Net_net2limitlo,
  Net_net2limitmi,
  Net_net2limithi,
  Net_net3limitlo,
  Net_net3limitmi,
  Net_net3limithi,
  Net_net1conlo,
  Net_net1conmi,
  Net_net1conhi,
  Net_net2conlo,
  Net_net2conmi,
  Net_net2conhi,
  Net_net3conlo,
  Net_net3conmi,
  Net_net3conhi,
  Net_net1above,
  Net_net2above,
  Net_net3above,
  Net_cnt
};

sassert(Net_cnt < sizeof(globs.netvars),"globs.netvars < Net_cnt") sassert_end
sassert(Net_cnt < Elemcnt(globs.netvars),"globs.netvars < Net_cnt") sassert_end
sassert(Eng_cnt < sizeof(globs.engvars),"globs.engvars < Eng_cnt") sassert_end

#define Cfgcl (1U << 31)
#define Cfgdef (1U << 30)

extern int readcfg(const char *name);
extern int inicfg(void);
extern int inicfgcl(void);
extern const char *runlvlnames(enum Runlvl lvl);
