// fare.c - handle fare/seat availiability for reserved transport

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2017 Joris van der Geer.
 */

/* reserved transport - like long-distance trains and planes -  have fares available on
  an individual trip basis. Whether reserved is determined on a per-route basis.
  If so, a list of fare positions per fare group per expanded departure is maintained.
  The entries contain the price. This list is accessed in parallel to time events.
 */

#include <string.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "math.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "util.h"
#include "time.h"
#include "net.h"
#include "fare.h"

#undef hdrstop

static ub4 taxifare(ub4 dist)
{
  ub4 fare = 2;
  ub4 km = dist / 100;

  if (dist < 100) fare += 5;
  else if (dist < 10 * 100) fare += 4 * km;
  else if (dist < 50 * 100) fare += 2 * km;
  else if (dist < 100 * 100) fare += 1 * km;
  else fare += dist / 300; // assume private transport
  return fare;
}

static ub4 airfare(ub4 dist,bool dom)
{
  ub4 fare;

  if (dom) fare = 30 + dist / 1000;
  else fare = 50 + dist / 1000;

  return fare;
}

ub4 mkfare(struct chop *hp)
{
  ub4 dist = hp->dist;
  switch (hp->kind) {
  case Taxi: return taxifare(dist);
  case Rail: return 2 + dist / 300;
  case Bus: return 1 + dist / 500;
  case Airdom: return airfare(dist,1);
  case Airint: return airfare(dist,0);
  case Ferry: case Walk: case Unknown: case Kindcnt: break;
  }
  return 0;
}

int fareupd(gnet *net,ub4 rid,ub4 hop1,ub4 hop2,ub4 chop,ub4 t,ub4 mask,ub4 nfare,ub4 *fares)
{
  ub4 *fhopofs = net->fhopofs;
  struct timepat *tp;
  struct hop *hp,*hops = net->hops;
  ub4 f,fi,gndx,ofs;
  ub4 nilmask;
  ub2 *farepos,*fareposbase = net->fareposbase;
  block *faremem = &net->faremem;
  ub8 *ev,*events = net->events;
  ub4 rt,tt,prvt;

  if (fhopofs == NULL || fareposbase == NULL) return info(0,"no reserved routes for %u",hop1);

  hp = hops + hop1;
  tp = &hp->tp;

  info(0,"rid %u chop %u hop2 %u mask %x",rid,chop,hop2,mask);
  if (nfare > Faregrp) return error(0,"farecnt %u above %u",nfare,Faregrp);

  ub4 evcnt = hp->evcnt;

  ub4 gt0 = tp->gt0;

  if (evcnt == 0) return info(0,"no events for %u",hop1);
  ev = events + tp->evofs;

  ofs = fhopofs[chop];

  farepos = fareposbase + ofs * Faregrp;
  bound(faremem,(ofs + nfare) * Faregrp,ub2);

  gndx = 0; tt = prvt = 0;
  while (gndx < evcnt) {
    prvt = tt;
    rt = (ub4)ev[gndx * 2];
    tt = rt + gt0;
    if (tt >= t) break;
    gndx++;
  }
  if (gndx == evcnt) return info(0,"\ad%u after \ad%u",t,tt);

  if (gndx && tt > t) {
    info(0,"found \ad%u before \ad%u",t,tt);
    gndx--; rt = (ub4)ev[gndx * 2]; tt = rt + gt0;
  }
  info(0,"found \ad%u as \ad%u after \ad%u",t,tt,prvt);

  bound(faremem,(ofs + gndx + (Faregrp-1)) * Faregrp,ub2);

  farepos += gndx * Faregrp;

  // upper bits indicate entries to clear
  if (mask & 0xf0) {
    nilmask = mask >> 4; f = 0;
    while (nilmask && f < Faregrp) {
      farepos[f] = hi16;
      info(0,"fare %u set to n/a at %p",f,(void *)farepos);
      nilmask >>= 1; f++;
    }
  }
  f = fi = 0; mask &= 0xf;
  info(0,"mask %x nfare %u",mask,nfare);
  while (mask && fi < nfare && f < Faregrp) {
    if (mask & 1) {
      farepos[f] = (ub2)fares[fi];
      info(0,"fare %u set to %u",f,fares[fi]);
      fi++;
    }
    mask >>= 1; f++;
  }

  return 0;
}

void inifare(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
}
