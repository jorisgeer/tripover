// net3.c - precompute 3-stop connections
-*- emka: skip -*-
/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

/* Initialize the network once at startup :

   create a pre-computed 3-stop connectivity network used in search

   Build connectivity matrix between any 3 full ports

   each matrix contains a list of possible trips from port A to port B
   the list is limited to a top-n on average trip duration, and trimmed on heuristics such as distance, cost, timing

   this 3-stop network is constructed from the previously computed 1-stop net

   base matrix for direct (non-stop) hops is prepared in net.c
 */

#include <string.h>
#include <pthread.h>

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
#include "net3.h"
#include "netev.h"

#undef hdrstop

static int vrbena;

void ininet3(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
  vrbena = (getmsglvl() >= Vrb);
}

// max number of alternatives per dep,arr pair to consider
#define Durcnt 256

static const ub8 sumreach = 1000 * 200;

// heuristic limit for over-route net3 versus direct
static ub4 geodistlim(ub4 dir)
{
  ub4 lim = 0;

  if (dir <= 100) return dir * 80;
  if (dir > 100) { lim += 100 * 80; dir -= 100; }
  if (dir > 1000) { lim += 1000 * 4; dir -= 1000; }
  if (dir > 10000) { lim += 10000 * 4; dir -= 10000; }
  if (dir > 100000) { lim += 100000 * 4; dir -= 100000; }
  if (dir > 500000) { lim += 500000 * 3; dir -= 500000; }
  lim += dir * 2;
  return lim;
}

static ub4 getvarlim(struct port *pdep,struct port *parr)
{
  ub4 nda = max(pdep->nda,parr->nda);

  if (nda < globs.net3con[0]) {
    if (nda > 4 && pdep->sumreach > sumreach) return globs.net3limit[0];
    else return 0;
  }
  else if (nda < globs.net3con[1]) return globs.net3limit[0];
  else if (nda < globs.net3con[2]) return globs.net3limit[1];
  else return globs.net3limit[2];
}

/*
  mid1:12
  v1:10
  v2:10
  dur:16
*/

#define Lst1midbit 12
#define Lst1midcnt (1 << Lst1midbit)
#define Lst1midmask (Lst1midcnt - 1)
#define Lst1vbit 10
#define Lst1vcnt (1 << Lst1vbit)
#define Lst1vmask (Lst1vcnt - 1)
#define Lst1v1shift Lst1midbit
#define Lst1v2shift (Lst1v1shift + Lst1vbit)
#define Lst1durshift (Lst1v2shift + Lst1vbit)
#if Lst1durshift > (64 - 16)
#error "Lst1durshift too large"
#endif
#define Lst1durcnt 65536

#define Viacnt1 Lst1midcnt

struct net3_args {
// in
  ub4 tid,tidcnt;
  struct network *net;
  ub4 depfrom,depto;

  ub4 varlimit,var12limit,altlimit,lowcon,cntonly;

  ub4 darrcnt;
  ub4 *darrs;
  ub4 *depmid1s;
  ub4 *depmid1ds;
  ub4 *depmid1cnts;
  ub4 *dmid1cnts;

  ub4 *portdst;

 // out
  int rv;
  ub8 lstlen;
};

static int net3_pas1(struct net3_args *argp)
{
  ub4 tid = argp->tid;
  ub4 tidcnt = argp->tidcnt;
  ub4 msgtid;

  ub4 darrcnt = argp->darrcnt;
  ub4 darr,*darrs = argp->darrs;

  ub4 *depmid1s = argp->depmid1s;
  ub4 *dmid1ds,*depmid1ds = argp->depmid1ds;
  ub4 *depmid1cnts = argp->depmid1cnts;
  ub4 *dmid1cnts  = argp->dmid1cnts;

  ub4 *dmid1s;
  ub4 *dmid1acnt;
  ub4 dmid1cnt;

  ub4 varlimlh;
  ub4 varlimit = argp->varlimit;
  ub4 var12limit = argp->var12limit;
  ub4 lowcon = argp->lowcon;
  ub4 cntonly = argp->cntonly;
  ub4 distabove = globs.net3above;

  struct network *net = argp->net;

  ub4 portcnt = net->portcnt;
  struct port *pdep,*pmid,*parr,*ports = net->ports;
  iadrbase *cnts1,*precnts;
  ub4 dep,mid,arr;
  ub4 dmid1;
  ub4 cnt,n1,n2,n12;
  ub8 lstlen;
  ub4 cntlim;
  ub4 dirdist,dirdistdm,dirdistma,gdistlim;

  ub8 stat_var12lim = 0,stat_distlim1 = 0,stat_distlim2 = 0,stat_abvdist = 0;

  struct eta eta;

  lstlen = 0;
  ub4 depfrom = argp->depfrom;
  ub4 depto = argp->depto;
  ub4 showdep = depfrom;

  ports = net->ports;

  precnts = &net->conipos;

  cnts1 = net->concnt + 1;

  iadrbase *lstitems = &net->lst1items;

  if (tidcnt > 1) {
    msgtid = (tid << Tidshift) | Tidbit;
    info(msgtid,"start in thread %u",tid);
  } else msgtid = 0;

  // for each departure port
  for (dep = depfrom; dep < depto; dep++) {

    pdep = ports + showdep;
    if (tprogress(tid,tidcnt,&eta,"p1 port %u of %u  \ah%lu conns %.32s",dep - depfrom,depto - depfrom,lstlen,pdep->iname)) return 1;

    pdep = ports + dep;
    if (pdep->nda < lowcon) {
      if (pdep->nda < 3 || pdep->sumreach < sumreach) continue;
    }
    if (pdep->valid == 0) continue;

    dmid1s = depmid1s + dep * Viacnt1;
    dmid1ds = depmid1ds + dep * Viacnt1;
    dmid1acnt = depmid1cnts + dep * Viacnt1;
    dmid1cnt = dmid1cnts[dep];

    if (dmid1cnt == 0) continue;

    // for each arrival port
    for (darr = 0; darr < darrcnt; darr++) {
      arr = darrs[darr];
      if (arr == dep) continue;

      if (cntonly < 256) { // todo
        n1 = rdiadr2(cnts1,dep,arr);
        if (n1 > cntonly) continue;
      }

      parr = ports + arr;

      varlimlh = getvarlim(pdep,parr);
      error_gt(varlimlh,varlimit,0);
      if (varlimlh == 0) continue;

      dirdist = fgeodist(pdep,parr,1);
      if (dirdist < distabove) { stat_abvdist++; continue; }

      gdistlim = geodistlim(dirdist);

      cnt = cntlim = 0;

      error_ovf(lstlen + varlimit * portcnt,ub4);

      // for each via
      for (dmid1 = 0; cnt < varlimlh && dmid1 < dmid1cnt; dmid1++) {
        dirdistdm = dmid1ds[dmid1];
        if (dirdistdm > gdistlim) { stat_distlim1++; continue; }

        mid = dmid1s[dmid1];
        if (mid == arr) continue;

        n2 = rdiadr2(cnts1,mid,arr);
        if (n2 == 0) continue;

        pmid = ports + mid;
        dirdistma = fgeodist(pmid,parr,1);
        if (dirdistdm + dirdistma > gdistlim) { stat_distlim2++; continue; }

        n2 = min(n2,Lst1vcnt);

        n1 = dmid1acnt[dmid1];
        error_z(n1,dmid1);

        n12 = n1 * n2;
        if (n12 > var12limit) { n12 = var12limit; stat_var12lim++; }
        cnt += n12;
      } // each mid stopover port
      cntlim = min(cnt,varlimlh);

      if (cntlim) {
        iadrinc(precnts,dep,arr,tid);
        iadrincn(lstitems,dep,arr * varlimit,cntlim,tid);
        lstlen += cntlim;
        showdep = dep;
      }

    } // each arr

  } // each dep
  argp->lstlen = lstlen;
  info(msgtid,"limits dist \ah%lu \ah%lu \ah%lu  var \ah%lu",stat_abvdist,stat_distlim1,stat_distlim2,stat_var12lim);
  return info(msgtid,"tid %u pass 1 \ah%lu tentative triplets",tid,lstlen);
} // pass 1

static void *net3_pass1(void *vp)
{
  struct net3_args *argp = (struct net3_args *)vp;
  ub4 tid = argp->tid;
  globs.tids[tid] = 1;
  int rv = net3_pas1(argp);
  argp->rv = rv;
  globs.tids[tid] = 0;
  return vp;
}

static int net3_pas2(struct net3_args *argp)
{
  ub4 tid = argp->tid;
  ub4 tidcnt = argp->tidcnt;
  ub4 msgtid;

  ub4 nstop = 3;

  ub4 darrcnt = argp->darrcnt;
  ub4 darr,*darrs = argp->darrs;

  ub4 *dmid1s,*depmid1s = argp->depmid1s;
  ub4 *dmid1ds,*depmid1ds = argp->depmid1ds;
  ub4 *depmid1cnts = argp->depmid1cnts;
  ub4 *dmid1cnts  = argp->dmid1cnts;

  ub4 *dmid1acnt;
  ub4 dmid1cnt;

  ub4 varlimlh;
  ub4 varlimit = argp->varlimit;
  ub4 var12limit = argp->var12limit;
  ub4 altlimit = argp->altlimit;
  ub4 lowcon = argp->lowcon;
  ub4 cntonly = argp->cntonly;
  ub4 distabove = globs.net3above;
  ub4 da_timlim = globs.net3timlim;

  ub4 *portdst = argp->portdst;

  struct network *net = argp->net;

  ub4 portcnt = net->portcnt;
  ub4 chopcnt = net->chopcnt;
  ub4 whopcnt = net->whopcnt;
  struct port *pdep,*parr,*pmid,*ports = net->ports;
  struct chop *hops = net->chops;
  block *lstblk1;
  ub4 *portsbyhop;
  iadrbase *cnts1,*precnts,*cnts;
  iadrbase *conofs1;
  ub8 ofs1,ofs2;
  ub4 *conlst1,*lst1,*lst2;
  ub4 *hopdist = net->hopdist;
  ub1 leg12mode;
  ub4 air,aircnt;
  ub4 lodur1,lodur2,lodur22;
  ub4 rid1,rid2;
  ub4 dep,mid,arr,mid1,mid2;
  ub4 dmid1;
  ub4 n,n0,n1,n2,n12,altcnt,v1,v2,leg1,leg12,leg2,leg22;
  ub8 lstlen;
  ub4 dirdist,dirdistdm;
  ub4 dist1,dist2,gdistlim;
  ub4 sumwalkdist1,sumwalkdist2;
  ub4 cntlimdur,gen,outcnt;

  ub4 midur,midur2,midur3,durndx,durcnt,durlim,durcntgnd,durlimgnd;
  ub4 dtlo,dthi,typdt,dtcnt;
  ub4 midurs[Durcnt],midursgnd[Durcnt];
  ub4 sortdurs[Durcnt];
  ub4 tmpmodes[Durcnt];
  ub8 tmpitem,tmpitems[Durcnt],tmpitemsgnd[Durcnt];

  ub4 sumwalklimit = net->sumwalklimit;
  ub8 stat_cntlim = 0,stat_partlimdur = 0,stat_timlim = 0;
  ub8 stat_altlim = 0,stat_var12limit = 0,stat_flt = 0;
  ub8 stat_noestdur = 0,stat_estdur = 0;
  ub4 hicnt = 0;
  ub8 nogen = 0,sumoutcnt = 0;

  struct eta eta;
  int cmd;

  lstlen = 0;
  ub4 depfrom = argp->depfrom;
  ub4 depto = argp->depto;
  ub4 showdep = depfrom;

  ports = net->ports;

  portsbyhop = net->portsbyhop;

  precnts = &net->conipos;
  conofs1 = net->conofs + 1;

  cnts1 = net->concnt + 1;
  cnts = net->concnt + nstop;

  lstblk1 = net->conlst + 1;
  conlst1 = blkdata(lstblk1,0,ub4);

  iadrbase *lstitems = &net->lst1items;
  ub4 hindx,hidur;

  ub1 mode1,*modes1 = net->modes[1];

  if (tidcnt > 1) {
    msgtid = (tid << Tidshift) | Tidbit;
    info(msgtid,"start in thread %u",tid);
  } else msgtid = 0;

  for (dep = depfrom; dep < depto; dep++) {

    pdep = ports + showdep;
    cmd = tprogress(tid,tidcnt,&eta,"p2 port %u of %u  \ah%lu conns %.32s",dep - depfrom,depto - depfrom,lstlen,pdep->iname);
    switch(cmd) {
    case 0: break;
    case 1: return 1;
    case 2: info(0,"time limit from %u to %u",da_timlim,da_timlim / 10);
            da_timlim /= 10;
            break;
    default: break;
    }

    pdep = ports + dep;
    if (pdep->nda < lowcon) {
      if (pdep->nda < 3 || pdep->sumreach < sumreach) continue;
    }
    if (pdep->valid == 0) continue;

    dmid1s = depmid1s + dep * Viacnt1;
    dmid1ds = depmid1ds + dep * Viacnt1;
    dmid1acnt = depmid1cnts + dep * Viacnt1;
    dmid1cnt = dmid1cnts[dep];

    if (dmid1cnt == 0) continue;

    if (sumoutcnt + portcnt >= hi32) {
      warn(msgtid,"limiting pairs to \ah%lu at dep %u of %u",sumoutcnt,dep,portcnt);
      break;
    }

    outcnt = 0;

    // for each arrival port
    for (darr = 0; darr < darrcnt; darr++) {
      arr = darrs[darr];
      if (arr == dep) continue;

      if (cntonly < 256) {
        n0 = rdiadr2(cnts1,dep,arr);
        if (n0 > cntonly) continue;
      }

      ofs1 = rdiadr8(conofs1,dep,arr);
      lst1 = conlst1 + ofs1;

      parr = ports + arr;

      varlimlh = getvarlim(pdep,parr);
      if (varlimlh == 0) continue;

      dirdist = fgeodist(pdep,parr,1);
      if (dirdist < distabove) continue;

      gdistlim = geodistlim(dirdist);

      setthtimer(tid,(ub4)da_timlim);

      gen = 0;

      // todo: start with limits derived from previous nstop
      // e.g. lodists[da] * 2

      // initial heuristic distance-based limit
      if (dirdist < 10) durlim = 60;
      else if (dirdist < 1 * 100) durlim = 2 * 60;
      else if (dirdist < 10 * 100) durlim = 12 * 60;
      else if (dirdist < 100 * 100) durlim = 1 * 1440;
      else if (dirdist < 1000 * 100) durlim = 4 * 1440;
      else if (dirdist < 10000 * 100) durlim = 8 * 1440;
      else durlim = 14 * 1440;
      durlimgnd = durlim;

      cntlimdur = min(varlimlh,Durcnt-1);

      nsethi(midurs,cntlimdur);
      nsethi(midursgnd,cntlimdur);

      // create time top-n list, derive threshold
      altcnt = 0;
      durcnt = 0;
      durcntgnd = 0;

      // for each via
      for (dmid1 = 0; dmid1 < dmid1cnt && altcnt < altlimit; dmid1++) {
        dirdistdm = dmid1ds[dmid1];
        if (dirdistdm > gdistlim) continue;
        mid = dmid1s[dmid1];
        if (mid == arr) continue;

        n1 = dmid1acnt[dmid1];

        n2 = rdiadr2(cnts1,mid,arr);
        if (n2 == 0) continue;

        if (isexpired(tid)) {
          stat_timlim++;
          info(msgtid,"timeout at dep %u arr %u %s - %s",dep,arr,pdep->iname,parr->iname);
          break;
        }

        pmid = ports + mid;

        n2 = min(n2,Lst1vcnt);

        n12 = 0;

        ofs1 = rdiadr8(conofs1,dep,mid);
        ofs2 = rdiadr8(conofs1,mid,arr);

        error_eq(ofs1,hi32);
        error_eq(ofs2,hi32);

        lst1 = conlst1 + ofs1 * 2;
        lst2 = conlst1 + ofs2 * 2;

        bound(lstblk1,ofs1 * 2,ub4);
        bound(lstblk1,ofs2 * 2,ub4);

        // each dep-via-arr alternative
        for (v1 = 0; v1 < n1 && altcnt < altlimit && n12 < var12limit; v1++) {
          sumwalkdist1 = 0; // sumwalks1[ofs1 + v1];
          leg1 = lst1[v1 * 2];
          if (leg1 == hi32) {
            error(msgtid,"invalid trip %u-%u-%u",dep,mid,arr);
            break;
          }
          error_ge(leg1,whopcnt);

          if (portsbyhop[leg1 * 2] != dep) {
            warn(msgtid,"hop %u %u-%u vs %u-%u",leg1,portsbyhop[leg1 * 2],portsbyhop[leg1 * 2 + 1],dep,mid);
            continue;
          }
          mid1 = portsbyhop[leg1 * 2 + 1];
          if (mid1 == arr) continue;

          leg12 = lst1[v1 * 2 + 1];
          if (leg12 == hi32) {
            error(msgtid,"invalid trip %u-%u-%u",dep,mid,arr);
            break;
          }
          error_ge(leg12,whopcnt);

          if (portsbyhop[leg12 * 2 + 1] != mid) {
            warn(msgtid,"hop %u %u-%u vs %u-%u",leg1,portsbyhop[leg1 * 2],portsbyhop[leg1 * 2 + 1],dep,mid);
            continue;
          }

          lodur1 = hops[leg1].lodur + hops[leg12].lodur;

          dist1 = hopdist[leg1] + hopdist[leg12];
          if (dist1 > gdistlim) continue;

          rid1 = hops[leg1].rid;
          mode1 = modes1[ofs1+v1];

          air = (mode1 & Airbit);
          if (lodur1 > (air ? durlim : durlimgnd)) continue;

          for (v2 = 0; v2 < n2 && n12 < var12limit; v2++) {
            n12++;
            leg2 = lst2[v2 * 2];
            error_ge(leg2,whopcnt);
            leg22 = lst2[v2 * 2 + 1];
            error_ge(leg2,whopcnt);

            mid2 = portsbyhop[leg2 * 2 + 1];
            if (mid2 == dep || mid2 == mid1) continue;

            dist2 = dist1 + hopdist[leg2] + hopdist[leg22];
            if (dist2 > gdistlim) continue;

#if 0
            tmpv1[0] = leg1;
            tmpv1[1] = leg12;
            tmpv1[2] = leg2;
            tmpv1[3] = leg22;

            if (checktrip3(net,tmpv1,4,dep,arr,mid,dist2)) info(0,"dep %u arr %u gen %u ofs %lu",dep,arr,gen,lstlen); // return 1 todo dbg;
#endif

            rid2 = hops[leg2].rid;
            if (pmid->loop == 0 && rid1 != hi32 && rid1 == rid2) continue;

            sumwalkdist2 = sumwalkdist1; // + sumwalks1[ofs2+v2];

            if (sumwalkdist2 > sumwalklimit) continue;

            if (leg12 >= chopcnt && leg2 >= chopcnt) continue;

            leg12mode = mode1 | modes1[ofs2+v2];
            air = (leg12mode & Airbit);

            lodur2 = hops[leg2].lodur;
            lodur22 = hops[leg22].lodur;

            if (lodur1 + lodur2 + lodur22 > (air ? durlim : durlimgnd)) continue;

            if (altcnt >= altlimit) { stat_altlim++; break; }

            // maintain top-n list as insertion sort
            // approximate estdur4 by estdur3 between ABCd minus dur(C) plus estdur2 CD
            dtcnt = estdur_3(net,leg1,leg12,leg2,&dtlo,&dthi,&typdt);
            midur3 = typdt;
            if (dtcnt == 0) {
              stat_noestdur++;
              // warn(0,"no estdur for %u-%u",leg1,leg2);
              continue;
            } else if (midur3 > Lst1durcnt) {
              warn(msgtid,"durlim %u exceeds %u %s - %s",midur3,Lst1durcnt,pdep->iname,parr->iname);
              continue;
            } else if (midur3 < lodur1 + lodur2) {
              warn(msgtid,"hop %u-%u-%u dur %u below min %u+%u",leg1,leg12,leg2,midur3,lodur1,lodur2);
              continue;
            }
            if (midur3 + lodur22 > (air ? durlim : durlimgnd)) continue;

            dtcnt = estdur_2(net,leg2,leg22,&dtlo,&dthi,&typdt);
            midur2 = typdt;
            if (dtcnt == 0) {
              stat_noestdur++;
              // warn(0,"no estdur for %u-%u",leg1,leg2);
              continue;
            } else if (midur2 > Lst1durcnt) {
              warn(msgtid,"durlim %u exceeds %u",midur2,Lst1durcnt);
              continue;
            } else if (midur2 < lodur2 + lodur22) {
              estdur_2(net,leg2,leg22,&dtlo,&dthi,&typdt);
              warn(msgtid,"hop %u-%u dur %u below min %u+%u",leg2,leg22,midur2,lodur2,lodur22);
              continue;
            }
            midur = midur3 - lodur2 + midur2;

            altcnt++;
            stat_estdur++;
            if (midur > (air ? durlim : durlimgnd)) continue;

            error_gt(durcnt,varlimlh,arr);
            error_gt(durcntgnd,varlimlh,arr);

            tmpitem = (ub8)dmid1 | ((ub8)v1 << Lst1v1shift) | ((ub8)v2 << Lst1v2shift) | ((ub8)midur << Lst1durshift);

            // store in both mixed mode and ground-only. select part of each if needed lateron
            if (durcnt == 0) { // first item
              midurs[0] = midur;
              tmpitems[0] = tmpitem;
              tmpmodes[0] = leg12mode;
              warncc(midur != hi32 && midur > 65534,Exit|msgtid,"durlim %u at 0 of %u exceeds 64k",midur,cntlimdur);
              durcnt = 1;
            } else if (durcnt < cntlimdur) { // next items
              warncc(midur != hi32 && midur > 65534,Exit|msgtid,"durlim %u at %u of %u exceeds 64k",midur,durcnt,cntlimdur);
              tmpitems[durcnt] = tmpitem;
              tmpmodes[durcnt] = leg12mode;
              midurs[durcnt++] = midur;
            } else { // full: eventually replace slower entry
              hidur = hindx = 0;
              for (durndx = 0; durndx < cntlimdur; durndx++) {
                if (midurs[durndx] > hidur) { hidur = midurs[durndx]; hindx = durndx; }
                warncc(midurs[durndx] != hi32 && midurs[durndx] > 65534,Exit|msgtid,"durlim %u at %u of %u exceeds 64k",midurs[durndx],durndx,cntlimdur);
              }
              durlim = hidur;
              warncc(durlim != hi32 && durlim > 65534,Exit|msgtid,"durlim %u at %u exceeds 64k",durlim,cntlimdur);
              error_eq(durlim,hi32);
              if (midur < hidur) {
                midurs[hindx] = midur;
                tmpitems[hindx] = tmpitem;
                tmpmodes[hindx] = leg12mode;
              }
            }

            if (air) continue;

            // ground-only
            if (durcntgnd == 0) {
              midursgnd[0] = midur;
              tmpitemsgnd[0] = tmpitem;
              durcntgnd = 1;
            } else if (durcntgnd < cntlimdur) {
              tmpitemsgnd[durcntgnd] = tmpitem;
              midursgnd[durcntgnd++] = midur;
            } else {
              hidur = hindx = 0;
              for (durndx = 0; durndx < cntlimdur; durndx++) {
                if (midursgnd[durndx] > hidur) { hidur = midursgnd[durndx]; hindx = durndx; }
              }
              durlimgnd = hidur;
              error_eq(durlimgnd,hi32);
              if (midur < hidur) {
                midursgnd[hindx] = midur;
                tmpitemsgnd[hindx] = tmpitem;
              }
            }

          } // each v2
        } // each v1

        if (n12 == var12limit) stat_var12limit++;
      } // each mid

      if (durcnt == cntlimdur) stat_partlimdur++;
      warncc(durlim != hi32 && durlim > 65534,Exit|msgtid,"durlim %u exceeds 64k",durlim);

      if (durcnt == 0) { nogen++; continue; }

      // emit mixed tmpitems only, or best half of tmpitems and -gnd if needed
      iadrinc(cnts,dep,arr,tid);
      outcnt++;

      aircnt = 0;
      for (n = 0; n < durcnt; n++) {
        if (tmpmodes[n] & Airbit) aircnt++;
      }
      if (aircnt * 2 <= cntlimdur) { // mixed only

        gen = durcnt;

        for (n = 0; n < durcnt; n++) {
          tmpitem = tmpitems[n];
          if (wriadr8(lstitems,dep,arr * varlimit + n,tmpitem)) break;
        }
        if (n < durcnt) continue;
        if (wriadr2(precnts,dep,arr,(ub2)gen)) return 1;
        lstlen += gen;
        continue;
      }

      // best half of each
      for (n = 0; n < durcnt; n++) sortdurs[n] = (midurs[n] << 16) | n;
      sort4(sortdurs,durcnt,FLN,"net1 midurs");
      n = gen = 0;
      while (n < durcnt && gen < cntlimdur / 2) {
        hindx = sortdurs[gen] & hi16;
        error_ge(hindx,durcnt);
        tmpitem = tmpitems[hindx];
        if (wriadr8(lstitems,dep,arr * varlimit + gen,tmpitem)) { n = 0; break; }
        gen++;
      }
      if (n == 0) continue;
      lstlen += gen;

      if (durcntgnd == 0) {
        wriadr2(precnts,dep,arr,(ub2)gen);
        continue;
      }

      for (n = 0; n < durcntgnd; n++) sortdurs[n] = (midursgnd[n] << 16) | n;
      sort4(sortdurs,durcntgnd,FLN,"net1 midurs");

      n = 0;
      while (n < durcntgnd && gen < cntlimdur) {
        hindx = sortdurs[n] & hi16;
        error_ge(hindx,durcntgnd);
        tmpitem = tmpitemsgnd[hindx];
        if (wriadr8(lstitems,dep,arr * varlimit + gen,tmpitem)) { n = 0; break; }
        gen++;
      }
      if (n == 0) continue;
      lstlen += gen;
      wriadr2(precnts,dep,arr,(ub2)gen);
    } // each arrival port

    portdst[dep] = outcnt;
    if (outcnt) showdep = dep;

    sumoutcnt += outcnt;
  } // each departure port

  ub8 allestdur = stat_estdur + stat_noestdur;
  info(msgtid|CC0,"no estdur \ah%lu of \ah%lu = \ap%lu%lu",stat_noestdur,allestdur,stat_noestdur,allestdur);

  estdur3_stats(tid);

  info(msgtid,"limits hicnt %u cntlim \ah%lu partlim dur \ah%lu altlim \ah%lu time \ah%lu var12 \ah%lu",hicnt,stat_cntlim,stat_partlimdur,stat_altlim,stat_timlim,stat_var12limit);

  info(msgtid,"tid %u pass 2 %u stop done, \ah%lu triplets in \ah%lu pairs, \ah%lu filtered \ah%lu nogen",tid,nstop,lstlen,sumoutcnt,stat_flt,nogen);

  argp->lstlen = lstlen;

  return 0;
}

static void *net3_pass2(void *vp)
{
  struct net3_args *argp = (struct net3_args *)vp;
  ub4 tid = argp->tid;
  globs.tids[tid] = 1;
  int rv = net3_pas2(argp);
  argp->rv = rv;
  rmthtimer(argp->tid);
  globs.tids[tid] = 0;
  return vp;
}

// create 3-stop connectivity matrix and derived info
// uses 1 via from 1-stop net
int mknet3(struct network *net,ub4 varlimit,ub4 var12limit,ub4 altlimit,ub4 cntonly,ub4 netstop)
{
  ub4 nstop = 3;
  ub4 portcnt = net->portcnt;
  ub4 hopcnt = net->hopcnt;
  ub4 chopcnt = net->chopcnt;
  ub4 whopcnt = net->whopcnt;
  struct port *ports,*pmid,*pdep,*parr;
  block *lstblk,*lstblk1;
  ub4 *portsbyhop;
  iadrbase *cnts,*cnts0,*cnts1,*cnts2,*precnts;
  iadrbase *conofs,*conofs1;
  ub4 *portdst;
  ub8 ofs,ofs1,ofs2,endofs,lstlen,tlstlen,newlstlen;
  ub4 *lst,*newlst,*conlst1,*lst1,*lst2,*lstv1;
  ub4 *hopdist = net->hopdist;
  ub4 dep,mid,arr,dep2,arr2;
  ub4 dmid1;
  ub4 iv;
  ub4 cnt,n,n1,n2,v1,v2,leg,leg1,leg12,leg2,leg22,nleg;
  ub4 dist1,dist2,sumwalkdist2,walkdist2,walkdist12,maxwalk;
  ub4 gen;
  ub4 midur,durlim;
  ub8 lstitem;
  ub4 stat_nocon = 0,stat_partcnt = 0,stat_cntlim = 0,stat_partlimdur = 0;

//  sassert(nstop < Netn,"Netn does not support net3");
  if (nstop >= Netn) ret_error(0,"nstop %u above %u",nstop,Netn);
  struct eta eta;

  error_zz(portcnt,hopcnt);

  if (varlimit == 0) return warn0(0,"skip 3-stop net on zero limit");
  if (net->lstlen[1] == 0) return warn0(0,"skip 3-stop net on no 1-stop net");

  info(0,"init %u/%u stop connections for %u port \ah%u hop network",nstop,netstop,portcnt,whopcnt);

  info(0,"limits: var %u var12 %u alt %u",varlimit,var12limit,altlimit);

  ports = net->ports;

  portsbyhop = net->portsbyhop;

  precnts = &net->conipos;
  clear(precnts);
  cnts = net->concnt + nstop;
  conofs = net->conofs + nstop;

  ub4 sparsethres = net->sparsethres;

  ub4 lowcon = globs.net3con[0];

  iadrbase *lstitems = &net->lst1items;

  error_lt(varlimit,globs.net3limit[0]);
  error_lt(varlimit,globs.net3limit[1]);
  error_ne(varlimit,globs.net3limit[2]);

  if (mkiadr0(lstitems,portcnt,portcnt * varlimit,ub8,sparsethres,32,"net3 lstitems")) return 1;
  if (setiadropts(lstitems,Iadr_append | Iadr_softlim)) return 1;

  // main netn structure
  if (mkiadr0(precnts,portcnt,portcnt,ub2,sparsethres,10,"net3 precnts")) return 1;
  if (setiadropts(precnts,Iadr_softlim)) return 1;

  if (mkiadr0(cnts,portcnt,portcnt,ub2,sparsethres,10,"net3 cnts")) return 1;
  if (mkiadr0(conofs,portcnt,portcnt,ub8,sparsethres,10,"net3 ofs")) return 1;

  iadrbase *durlims = net->durlims + 3;

  if (mkiadr0(durlims,portcnt,portcnt,ub2,sparsethres,10,"net2 durlims")) return 1;

  portdst = alloc(portcnt, ub4,0,"net portdst",portcnt);  // outbound conn stats

  error_zp(hopdist,0);

  nleg = nstop + 1;

/* Essentially we do for each (departure,arrival) pair:
   Search for a 'via' port such that trip (dep,via) and (via2,arr) exist
   Trim list of alternatives based on typical trip duration
   Store result by value. This is memory-intensive but keeps code simple

   In short:
   foreach dep
     foreach arr
       foreach mid with [dep,mid]
           ...

*/

/*
  pass 1 : foreach (dep,arr) pair at this #stops:
  bound overall best and worst
  create histogram and derive threshold to use as filter in next pass
  estimate size of trip list matrix
  obtain basic stats
*/

  ub8 dupstats[16];

  lstlen = 0;

  aclear(dupstats);

  ub4 darr,darrcnt = 0,*darrs = alloc(portcnt,ub4,0,"net darrs",0);

  // prepare arrs
  for (arr = 0; arr < portcnt; arr++) {
    parr = ports + arr;
    if (parr->valid == 0) continue;
    if (parr->nda < lowcon) {
      if (parr->nda < 3 || parr->sumreach < sumreach) continue;
    }
    darrs[darrcnt++] = arr;
  }
  if (darrcnt == 0) return warn(Emp,"skip 3-stop net on no arrs from %u",portcnt);

  // prepare mid lookup info
  ub4 *dmid1s,*depmid1s = alloc(portcnt * Viacnt1,ub4,0,"net depdmid",Viacnt1);
  ub4 dir,*dmid1ds,*depmid1ds = alloc(portcnt * Viacnt1,ub4,0,"net depdmidd",Viacnt1);
  ub4 *dmid1acnt,*depmid1cnts = alloc(portcnt * Viacnt1,ub4,0,"net depdmid",Viacnt1);

  ub4 *dmid1cnts = alloc(portcnt,ub4,0,"net depdmidcnt",portcnt);

  cnts0 = net->concnt + 0;
  cnts1 = net->concnt + 1;
  cnts2 = net->concnt + 2;

  lstblk1 = net->conlst + 1;
  conlst1 = blkdata(lstblk1,0,ub4);
  conofs1 = net->conofs + 1;

  ub4 dmidbins[Viacnt1];
  ub4 dmidivs = Elemcnt(dmidbins) - 1;

  aclear(dmidbins);
  ub4 fltdepcnt = 0;

  // prepare vias
  for (dep = 0; dep < portcnt; dep++) {

    if (progress0(&eta,"3-stop pass 0 dep %u of %u",dep,portcnt)) return 1;

    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    if (pdep->nda < lowcon) {
      if (pdep->nda < 3 || pdep->sumreach < sumreach) continue;
    }
    dmid1s = depmid1s + dep * Viacnt1;
    dmid1ds = depmid1ds + dep * Viacnt1;
    dmid1acnt = depmid1cnts + dep * Viacnt1;
    dmid1 = 0;
    for (mid = 0; mid < portcnt && dmid1 < Viacnt1; mid++) {
      if (mid == dep) continue;
      pmid = ports + mid;
      if (pmid->valid == 0 || pmid->oneroute) continue;

      n1 = rdiadr2(cnts1,dep,mid);
      if (n1 == 0) continue;
      n1 = min(n1,Lst1vcnt);
      dmid1acnt[dmid1] = n1;

      dir = fgeodist(pdep,pmid,1);
      dmid1ds[dmid1] = dir;
      dmid1s[dmid1++] = mid;
    }
    dmid1cnts[dep] = dmid1;
    dmidbins[min(dmid1,dmidivs)]++;
    if (dmid1 == Viacnt1) {
      info(Iter,"dep %u limiting mid to %u %s",dep,dmid1,pdep->iname);
      fltdepcnt++;
    }
  }
  for (iv = 0; iv <= dmidivs; iv++) { dmid1 = dmidbins[iv]; infocc(dmid1,Notty,"dmids %u: \ah%u",iv,dmid1); }
  info(CC0|Emp,"%u dep limited on %u vias",fltdepcnt,Viacnt1);

  ub4 depfrom,depchunk;
  int rv;
  void *trv;

  struct net3_args *argp,*argp0,*argp1,*targs = alloc(Nthread+1,struct net3_args,0,"net3 tidargs",0);
  pthread_t ptids[Nthread];
  pthread_attr_t thrattr;

  argp0 = targs;
  argp1 = targs + Nthread; // last partial

  ub4 tid = 0;
  ub4 tidcnt,btidcnt;

  if (portcnt > 5000) {
    btidcnt = globs.tidcnt;
    tidcnt = btidcnt * 2;
  } else tidcnt = btidcnt = 1;

  argp0->tid = 0;
  argp0->tidcnt = tidcnt;
  argp0->net = net;
  argp0->depfrom = 0;
  argp0->depto = portcnt;

  argp0->varlimit = varlimit;
  argp0->var12limit = var12limit;
  argp0->altlimit = altlimit;
  argp0->lowcon = lowcon;
  argp0->cntonly = cntonly;

  argp0->portdst = portdst;

  argp0->darrcnt = darrcnt;
  argp0->darrs = darrs;
  argp0->depmid1s = depmid1s;
  argp0->depmid1ds = depmid1ds;
  argp0->depmid1cnts = depmid1cnts;
  argp0->dmid1cnts = dmid1cnts;

  if (tidcnt == 1) {
    argp0->tidcnt = 1;
    rv = net3_pas1(argp0);
    if (rv) return rv;
  } else {
    depchunk = (portcnt / tidcnt) & (~Maxmask);
    info(0,"%u threads, %u ports in chunks of %u",tidcnt,portcnt,depchunk);

    argp0->depto = min(depchunk,portcnt);
    depfrom = depchunk;

    for (tid = 1; tid < tidcnt && depfrom < portcnt - 1; tid++) {
      argp = targs + tid;
      *argp = *argp0;
      argp->tid = tid;
      argp->depfrom = depfrom;
      argp->depto = min(depfrom + depchunk,portcnt);
      depfrom += depchunk;
    }

    if (depfrom < portcnt - 1) {  // last partial chunk
      *argp1 = *argp0;
      argp1->depfrom = depfrom;
      argp1->depto = portcnt;
      info(0,"running ports %u-%u",argp1->depfrom,argp1->depto);
      if (net3_pas1(argp1)) return error(0,"net1 pass 1 partial chunk %u-%u failed",depfrom,portcnt);
    }

    // todo: move to system header/module
    if (pthread_attr_init(&thrattr)) return oserror0(0,"cannot init pthread attrs");
    if (pthread_attr_setinheritsched(&thrattr,PTHREAD_EXPLICIT_SCHED)) oswarn0(0,"cannot init pthread attrs");

#ifdef SCHED_BATCH
    if (pthread_attr_setschedpolicy(&thrattr,SCHED_BATCH)) oswarn0(0,"cannot init pthread attrs");
#endif

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;

#ifdef SCHED_IDLE
      if (tid == btidcnt) {
        if (pthread_attr_setschedpolicy(&thrattr,SCHED_IDLE)) oswarn0(0,"cannot init pthread attrs");
      }
#endif

      info(0,"creating thread %u: ports %u-%u",tid,argp->depfrom,argp->depto);
      rv = pthread_create(ptids + tid,&thrattr,&net3_pass1,argp);
      if (rv) return oserror(0,"cannot create thread %u",tid);
      info(0,"created thread %u",tid);
    }

    // first chunk in main thread
    info(0,"running ports %u-%u",argp0->depfrom,argp0->depto);
    if (net3_pas1(argp0)) return error(0,"net3 pass 1 chunk %u-%u failed",0,depchunk);
    tlstlen = targs->lstlen;

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;
      info(0,"joining thread %u",tid);
      if (pthread_join(ptids[tid],&trv)) return oserror(0,"cannot join thread %u",tid);
      if (trv == NULL) return error(0,"thread %u returned nil error",tid);
      argp = (struct net3_args *)trv;
      rv = argp->rv;
      if (rv) return error(0,"thread %u returned error %d",tid,rv);
      info(0,"joined thread %u",tid);
      tlstlen += argp->lstlen;
    }
    info(Emp,"3-stop pass 1 \ah%lu tentative triplets",tlstlen);
  }

 // pass 2
  mkiadr1(precnts);
  mkiadr1(lstitems);

  if (tidcnt == 1) {
    rv = net3_pas2(argp0);
    if (rv) return rv;
  } else {

    if (argp1->depto) {  // last partial chunk
      if (net3_pas2(argp1)) return error(0,"net3 pass 2 partial chunk %u-%u failed",argp1->depfrom,portcnt);
    }

#ifdef SCHED_BATCH
    if (pthread_attr_setschedpolicy(&thrattr,SCHED_BATCH)) oswarn0(0,"cannot init pthread attrs");
#endif

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;

#ifdef SCHED_IDLE
      if (tid == btidcnt) {
        if (pthread_attr_setschedpolicy(&thrattr,SCHED_IDLE)) oswarn0(0,"cannot init pthread attrs");
      }
#endif

      info(0,"creating thread %u: ports %u-%u",tid,argp->depfrom,argp->depto);
      rv = pthread_create(ptids + tid,&thrattr,&net3_pass2,argp);
      if (rv) return oserror(0,"cannot create thread %u",tid);
      info(0,"created thread %u",tid);
    }

    // first chunk in main thread
    if (net3_pas2(argp0)) return error(0,"net3 pass 2 chunk %u-%u failed",0,argp0->depto);

    for (tid = 1; tid < tidcnt; tid++) {
      argp = targs + tid;
      if (argp->depto == 0) continue;
      info(0,"joining thread %u",tid);
      if (pthread_join(ptids[tid],&trv)) return oserror(0,"cannot join thread %u",tid);
      if (trv == NULL) return error(0,"thread %u returned nil error",tid);
      argp = (struct net3_args *)trv;
      rv = argp->rv;
      if (rv) warn(0,"thread %u returned error %d",tid,rv);
      info(0,"joined thread %u",tid);
    }
    pthread_attr_destroy(&thrattr);
  }

  ofs = 0;

  for (dep = 0; dep < portcnt; dep++) {

    if (progress(&eta,"3-stop pass 2b port %u of %u  \ah%lu conns",dep,portcnt,ofs)) return 1;

    for (darr = 0; darr < darrcnt; darr++) {
      arr = darrs[darr];
      if (arr == dep) continue;

      gen = rdiadr2(precnts,dep,arr);
      if (gen == 0) continue;

      ofs += gen;
    }
  }
  lstlen = ofs;
  info(Emp,"pass 2 %u stop done, \ah%lu triplets",nstop,lstlen);

  struct range portdr;
  ub4 ivportdst[32];

  mkhist(caller,portdst,portcnt,&portdr,Elemcnt(ivportdst),ivportdst,"outbounds by port",Info);

  warncc(lstlen == 0,0,"no connections at %u-stop for %u ports",nstop,portcnt);
  if (lstlen == 0) return 0;

  mkiadr1(cnts);

  cpiadr(durlims,cnts);
  mkiadr1(durlims);

  cpiadr(conofs,cnts);
  mkiadr1(conofs);

  ub4 cnt0,newcnt;

  ub4 genstats[64];
  ub4 cntstats[64];
  ub4 geniv = 63;

  aclear(cntstats);
  aclear(genstats);

  // prepare list matrix

  lstblk = net->conlst + nstop;

  lst = mkblock(lstblk,(ub8)lstlen * nleg,ub4,Noinit,"net3 %u-stop conlst",nstop);

  ub1 *modes = alloc(lstlen,ub1,0,"net3 modes",lstlen);
  ub1 *hopmode = net->hopmodes;

  ofs = newcnt = 0;

  if (portcnt < 20000) {
    for (dep = 0; dep < portcnt; dep++) {
      for (arr = 0; arr < portcnt; arr++) {
        if (dep == arr) continue;
        cnt = rdiadr2(precnts,dep,arr);
        cnt0 = rdiadr2(cnts0,dep,arr);
        cnt0 += rdiadr2(cnts1,dep,arr);
        if (net->lstlen[2]) cnt0 += rdiadr2(cnts2,dep,arr);
        if (cnt) {
          ofs += cnt;
          if (cnt0 == 0) newcnt++;
        }
      }
    }
    info(0,"\ah%u new connections %lu%%",newcnt, (100UL * newcnt) / ((ub8)portcnt * portcnt));
    error_ne(ofs,lstlen);
  }

  aclear(dupstats);

  ub8 dursort[Durcnt];
  ub4 *tmpv1,tmplst[Durcnt * 4];
  ub1 tmpmodes[Durcnt];
  ub4 idx,idx2;
  ub4 pairs = 0;

  // pass 3: fill based on triplets determined above
  ofs = 0;
  for (dep = 0; dep < portcnt && ofs < lstlen; dep++) {

    if (progress(&eta,"3-stop pass 3 port %u of %u  \ah%lu conns",dep,portcnt,ofs)) return 1;

    pdep = ports + dep;

    if (pdep->valid == 0) continue;

    dmid1s = depmid1s + dep * Viacnt1;
    dmid1acnt = depmid1cnts + dep * Viacnt1;

    for (darr = 0; darr < darrcnt && ofs < lstlen; darr++) {
      arr = darrs[darr];
      if (arr == dep) continue;

      cnt = rdiadr2(precnts,dep,arr);
      if (cnt == 0) continue;

      cnt = min(cnt,Durcnt);
      parr = ports + arr;

      error_z(parr->valid,arr);

      gen = 0; // generate final count

      if (wriadr8(conofs,dep,arr,ofs)) return 1;

      lstv1 = lst + ofs * nleg;
      error_ge(ofs,lstlen);
      tmpv1 = tmplst;

      endofs = ofs + cnt - 1;

      error_ge(endofs,lstlen);

      for (n = 0; n < cnt; n++) {
        lstitem = rdiadr8(lstitems,dep,arr * varlimit + n);
        dmid1 = lstitem & Lst1midmask;
        mid = dmid1s[dmid1];

        v1 = (lstitem >> Lst1v1shift) & Lst1vmask;
        v2 = (lstitem >> Lst1v2shift) & Lst1vmask;

        midur = (ub2)(lstitem >> Lst1durshift);

        if (midur == 0) {
          warn(0,"port %u-%u var %u dur 0",dep,arr,n);
          continue;
        }
        n1 = dmid1acnt[dmid1];
        error_ge(v1,n1);

        ofs1 = rdiadr8(conofs1,dep,mid);
        lst1 = conlst1 + ofs1 * 2;

        n2 = rdiadr2(cnts1,mid,arr);
        error_z(n2,mid);
        error_ge(v2,n2);

        ofs2 = rdiadr8(conofs1,mid,arr);

        lst2 = conlst1 + ofs2 * 2;

        bound(lstblk1,ofs1 * 2,ub4);
        bound(lstblk1,ofs2 * 2,ub4);

        leg1 = lst1[v1 * 2];
        error_ge(leg1,whopcnt);

        if (portsbyhop[leg1 * 2] != dep) {
          error(Exit,"hop %u %u-%u vs %u-%u",leg1,portsbyhop[leg1 * 2],portsbyhop[leg1 * 2 + 1],dep,mid);
        }

        leg12 = lst1[v1 * 2 + 1];
        error_ge(leg1,whopcnt);

        if (portsbyhop[leg12 * 2 + 1] != mid) {
          info(0,"dmid1 %u mid1 %u n %u of %u",dmid1,mid,v1,n1);
          error(Exit,"arr %u hop %u %u-%u vs %u-%u",arr,leg1,portsbyhop[leg1 * 2],portsbyhop[leg1 * 2 + 1],dep,mid);
        }

        leg2 = lst2[v2 * 2];
        error_ge(leg2,whopcnt);
        dep2 = portsbyhop[leg2 * 2];

        if (dep2 != mid) {
          error(Exit,"hop %u %u-%u vs %u-%u",leg2,dep2,portsbyhop[leg2 * 2 + 1],mid,arr);
        }
        if (dep2 == dep) {
          error(Exit,"hop %u %u-%u vs %u-%u",leg2,dep2,portsbyhop[leg2 * 2 + 1],mid,arr);
        }

        leg22 = lst2[v2 * 2 + 1];
        error_ge(leg22,whopcnt);
        arr2 = portsbyhop[leg22 * 2 + 1];

        if (arr2 != arr) {
          error(Exit,"hop %u %u-%u vs %u",leg22,portsbyhop[leg22 * 2],arr2,arr);
        }

        dist1 = hopdist[leg1] + hopdist[leg12];
        dist2 = hopdist[leg2] + hopdist[leg22];
        walkdist12 = (leg12 >= chopcnt) ? hopdist[leg12] : 0;
        walkdist2 = (leg2 >= chopcnt) ? hopdist[leg2] : 0;
        sumwalkdist2 = 0;
        maxwalk = walkdist12 + walkdist2;

        error_ge(gen,Elemcnt(dursort));
        dursort[gen] = (ub8)midur << 32 | gen;

        tmpmodes[gen] = hopmode[leg1] | hopmode[leg12] | hopmode[leg2] | hopmode[leg22];

        error_ovf(maxwalk,ub2);
        error_ovf(sumwalkdist2,ub2);

        error_gt((ub8)(tmpv1 + 4),(ub8)(tmplst + Elemcnt(tmplst)),gen);

        tmpv1[0] = leg1;
        tmpv1[1] = leg12;
        tmpv1[2] = leg2;
        tmpv1[3] = leg22;

        if (checktrip3(net,tmpv1,nleg,dep,arr,mid,dist1 + dist2)) info(0,"dep %u arr %u gen %u ofs %lu",dep,arr,gen,ofs); // return 1 todo dbg;
        gen++;

        tmpv1 += nleg;

      } // each alt

      if (gen < cnt) stat_partcnt++;

      genstats[min(gen,geniv)]++;
      cntstats[min(cnt,geniv)]++;

      // none found for any dep-Mid-arr, but mid exists : no events
      if (cnt && gen == 0) stat_nocon++;

      if (gen == 0 || cnt == 0) continue;

      pairs++;

      error_gt(gen,cnt,arr);

      if (gen > 1) sort8(dursort,gen,FLN,"nstop durlist");
      durlim = (ub4)(dursort[0] >> 32);
      for (idx = 0; idx < gen; idx++) {
        idx2 = dursort[idx] & hi32;
        error_ge(idx2,gen);
        memcpy(lstv1,tmplst + idx2 * nleg,nleg * sizeof(ub4));
        modes[ofs + idx] = tmpmodes[idx2];
        lstv1 += nleg;
      }

      ofs += gen;
      wriadr2(cnts,dep,arr,(ub2)gen);
      wriadr2(durlims,dep,arr,(ub2)durlim);

    } // each arrival port
  } // each departure port

  afree(depmid1s,"net");
  afree(depmid1ds,"net");
  afree(depmid1cnts,"net");

  newlstlen = (ub4)ofs;
  error_gt(newlstlen,lstlen,0);

  rmiadr(lstitems);
  rmiadr(precnts);

  finiadr(cnts);
  finiadr(conofs);
  info(Emp,"pass 3 net %u done, \ah%lu from \ah%lu triplets in \ah%u pairs",nstop,newlstlen,lstlen,pairs);

  if (lstlen - newlstlen > 1024 * 1024 * 64) {
    newlst = trimblock(lstblk,newlstlen * nleg,ub4);
  } else newlst = lst;

  net->lstlen[nstop] = newlstlen;
  net->pairs[nstop] = pairs;

  info(0,"verify \ah%lu hops",newlstlen);
  for (ofs = 0; ofs < newlstlen * nleg; ofs++) {
    leg = newlst[ofs];
    error_ge(leg,whopcnt);
  }
  for (ofs = 0; ofs < newlstlen; ofs++) {
    error_z(modes[ofs],ofs);
  }

  for (iv = 0; iv < Elemcnt(dupstats); iv++) if (dupstats[iv]) info(0,"dup %u: \ah%lu",iv,dupstats[iv]);

  info(0,"no conn %u  partcnt %u  cntlim %u partlim1 %u",stat_nocon,stat_partcnt,stat_cntlim,stat_partlimdur);

  for (iv = 0; iv <= geniv; iv++) infocc(cntstats[iv],V0,"%u: gen \ah%u cnt \ah%u",iv,genstats[iv],cntstats[iv]);

  net->modes[nstop] = modes;

  // verify all triplets
  // if (portcnt > 40000) return 0;

  for (dep = 0; dep < portcnt; dep++) {
    pdep = ports + dep;
    for (arr = 0; arr < portcnt; arr++) {
      n1 = rdiadr2(cnts,dep,arr);
      if (n1 == 0) continue;
      parr = ports + arr;
      error_z(pdep->valid,dep);
      error_z(parr->valid,arr);
    }
  }

  for (dep = 0; dep < portcnt; dep++) {
    if (progress0(&eta,"verify trips port %u of %u",dep,portcnt)) return 1;
    pdep = ports + dep;
    for (darr = 0; darr < darrcnt; darr++) {
      arr = darrs[darr];
      if (dep == arr) continue;
      n1 = rdiadr2(cnts,dep,arr);
      if (n1 == 0) continue;
      parr = ports + arr;

      ofs = rdiadr8(conofs,dep,arr);
      lstv1 = newlst + ofs * nleg;
      for (v1 = 0; v1 < n1; v1++) {
        if (checktrip(net,lstv1,nleg,dep,arr,hi32)) {
          wriadr2(cnts,dep,arr,0);
          break;
        }
        lstv1 += nleg;
      }
    }
  }

  // prepare sorted outbounds and inbounds per port for search
  ub4 depcnt,arrcnt,ddep;
  ub4 *deplst = alloc(pairs,ub4,0,"net3 deplst",0);
  ub4 *arrlst = alloc(pairs,ub4,0,"net3 arrlst",0);
  ub4 *depdurlst = alloc(pairs,ub4,0,"net3 deplst",0);
  ub4 *arrdurlst = alloc(pairs,ub4,0,"net3 deplst",0);

  ub8 *dasort = alloc(portcnt,ub8,0,"net0 depsort",0);

  ofs = 0;

  for (dep = 0; dep < portcnt; dep++) {
    if (progress0(&eta,"dep conlst port %u of %u",dep,portcnt)) return 1;
    pdep = ports + dep;
    if (pdep->valid == 0) continue;
    if (pdep->nda < lowcon) {
      if (pdep->nda < 3 || pdep->sumreach < sumreach) continue;
    }
    if (ofs >= pairs) {
      warn(0,"skip port %u on ofs %lu above pairs \ah%u",dep,ofs,pairs);
      break;
    }
    pdep->depofs[nstop] = (ub4)ofs;
    depcnt = 0;
    for (darr = 0; darr < darrcnt; darr++) {
      arr = darrs[darr];
      if (dep == arr) continue;
      parr = ports + arr;
      if (parr->valid == 0) continue;
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      midur = rdiadr2(durlims,dep,arr);
      dasort[depcnt] = (ub8)midur << 32 | arr;
      depcnt++;
    }
    pdep->depcnt[nstop] = depcnt;

    if (depcnt > 1) fsort8(dasort,depcnt,0,FLN,"net3 deplst");
    else if (depcnt == 0) continue;
    error_gt(ofs + depcnt,pairs,depcnt);
    for (darr = 0; darr < depcnt; darr++) {
      arr = dasort[darr] & hi32;
      midur = (ub4)(dasort[darr] >> 32);
      deplst[ofs+darr] = arr;
      depdurlst[ofs+darr] = midur;
    }
    ofs += depcnt;
  }

  ofs = 0;
  for (darr = 0; darr < darrcnt; darr++) {
    arr = darrs[darr];
    if (progress0(&eta,"arr conn port %u of %u",arr,portcnt)) return 1;
    parr = ports + arr;
    if (parr->valid == 0) continue;
    if (parr->nda < lowcon) {
      if (parr->nda < 3 || parr->sumreach < sumreach) continue;
    }
    if (ofs >= pairs) {
      warn(0,"skip port %u on ofs %lu above pairs \ah%u",arr,ofs,pairs);
      continue;
    }
    parr->arrofs[nstop] = (ub4)ofs;
    arrcnt = 0;
    for (dep = 0; dep < portcnt; dep++) {
      if (dep == arr) continue;
      pdep = ports + dep;
      if (pdep->valid == 0) continue;
      if (pdep->nda < lowcon) {
        if (pdep->nda < 3 || pdep->sumreach < sumreach) continue;
      }
      cnt = rdiadr2(cnts,dep,arr);
      if (cnt == 0) continue;
      midur = rdiadr2(durlims,dep,arr);
      dasort[arrcnt] = (ub8)midur << 32 | dep;
      arrcnt++;
    }
    parr->arrcnt[nstop] = arrcnt;

    if (arrcnt > 1) fsort8(dasort,arrcnt,0,FLN,"net3 arrlst");
    else if (arrcnt == 0) continue;
    error_gt(ofs + arrcnt,pairs,arrcnt);
    for (ddep = 0; ddep < arrcnt; ddep++) {
      dep = dasort[ddep] & hi32;
      midur = (ub4)(dasort[ddep] >> 32);
      arrlst[ofs+ddep] = dep;
      arrdurlst[ofs+ddep] = midur;
    }
    ofs += arrcnt;
  }

  net->deplst[nstop] = deplst;
  net->arrlst[nstop] = arrlst;
  net->depdurlst[nstop] = depdurlst;
  net->arrdurlst[nstop] = arrdurlst;

  rmiadr(durlims);

  return 0;
}
