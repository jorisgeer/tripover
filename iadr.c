// iadr.c - indirect addressing for 2D arrays

/*
  A compact representation for relatively sparse 2D arrays
  16 x 16 cells are grouped into a tile
  each tile has a total cell count and a list of <offset,value>
  the offset is the coordinate within the tile
  if count is relatively large, the tile is filled completely and no search is done
 */

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2017 Joris van der Geer.
 */

#include <string.h>

#include "base.h"
#include "mem.h"

#ifdef __clang__
 #pragma clang diagnostic error "-Wconversion"
#endif

static ub4 msgfile;
#include "msg.h"
#include "iadr.h"

// prepare iadr before count
int mkiadr0fln(ub4 fln,iadrbase *ia,ub4 ny,ub4 nx,ub2 elsize,ub4 ylim,ub2 clim,const char *desc)
{
  error_zp(desc,0);
  ub4 desclen = sizeof(ia->desc);

  ub4 pos = fmtstring(ia->desc,"%s ",desc);
  pos += msgfln(ia->desc,pos,desclen,fln,9);

  errorccfln(ia->state != Iadr_none,EXit,fln,"iadr %s state %u not %u",desc,ia->state,Iadr_none);
  errorccfln(ia->shift,EXit,fln,"iadr %s shift previously set",desc);
  error_ge(ylim,hi32 / 8);

  ub4 shift,mask;

  if (ny > ylim * 8) {
    shift = 5;
    mask = 0x1f;
  } else {
    shift = 4;
    mask = 0xf;
  }
  error_ge(shift,8);
  error_gt(mask,Maxmask,ylim);
  ia->mask = mask;
  ia->shift = shift;
  ub2 maxcnt = (ub2)(1 << (2 * shift));
  error_gt(clim,maxcnt,shift);

  ub4 mx = nx >> shift;
  ub4 my = ny >> shift;
  if (nx & mask) mx++;
  if (ny & mask) my++;
  error_ovf( (ub8)mx * (ub8)my,ub4);

  ub4 mxy = mx * my;
  ub8 nxy = (ub8)nx * ny;

#ifdef Tidchk
  ia->tid = alloc(mxy,ub1,0xff,ia->desc,sizeof(ub1) * mxy);
#endif

  ia->cnt = alloc(mxy,ub2,0,ia->desc,sizeof(ub2) * mxy);
  ia->pos = alloc(mxy,ub2,0,ia->desc,sizeof(ub2) * mxy);
  ia->ofs = alloc(mxy,ub8,0,ia->desc,sizeof(ub8) * mxy);
  ia->lofs = alloc(mxy,ub4,0,ia->desc,sizeof(ub4) * mxy);

  ia->mx = mx;
  ia->my = my;
  ia->mxy = mxy;
  ia->nxy = nxy;
  ia->nx = nx;
  ia->ny = ny;
  ia->elsize = elsize;
  ia->ylim = ylim;
  ia->cntlim = clim;
  ia->maxcnt = maxcnt;
  ia->fln = fln;
  ia->state = Iadr_init;
  ia->def  = 0;
  ia->def8 = 0;

  if (ny > ylim) return info(0,"sparse alloc for %u,%u above %u, cell %u for %s",ny,nx,ylim,clim,desc);

  if (nxy >= hi32) return errorfln(FLN,0,fln,"%u * %u = \ah%lu ylim %u",ny,nx,nxy,ylim);
  ia->havexy = 1;
  ub1 fill = (ub1)ia->def;

  switch(elsize) {
  case 2: ia->xy2 = alloc(nxy,ub2,fill,"net xy",ny); break;
  case 4: ia->xy4 = alloc(nxy,ub4,fill,"net xy",ny); break;
  case 8: ia->xy8 = alloc(nxy,ub8,fill,"net xy",ny); break;
  default: return error(Exit,"unknown elsize %u",elsize);
  }
  return info(0,"xy alloc of %u below %u for %s",ny,ylim,desc);
}

int setiadropts(iadrbase *ia,ub4 opts)
{
  ub8 nxy = ia->nxy;
  ub4 elsize = ia->elsize;

  error_zp(ia,0);
  if (ia->state >= Iadr_cnt) return errorfln(FLN,0,0,"%s in state %u",ia->desc,ia->state);
  ia->opts = opts;
  if ((opts & Iadr_defhi) == 0) return 0;

  ia->def = hi32;
  ia->def8 = hi64;
  if (ia->havexy == 0) return 0;
  switch(elsize) {
    case 2: memset(ia->xy2,0xff,nxy * elsize); break;
    case 4: memset(ia->xy4,0xff,nxy * elsize); break;
    case 8: memset(ia->xy8,0xff,nxy * elsize); break;
  }

  return 0;
}

static void dofree(void *p)
{
  afree(p,"net");
}

void rmiadrfln(ub4 fln,iadrbase *ia)
{
  if (ia->fln == 0) { errorfln(FLN,Exit,fln,"rm for uninited iadr"); return; }
  if (ia->state < Iadr_init) errorfln(FLN,Exit,fln,"%s in state %u",ia->desc,ia->state);

  if (ia->xy2) dofree(ia->xy2);
  if (ia->xy4) dofree(ia->xy4);
  if (ia->xy8) dofree(ia->xy8);

  if (ia->dlst) dofree(ia->dlst);
  if (ia->xymap) dofree(ia->xymap);

  if (ia->lst2) dofree(ia->lst2);
  if (ia->lst4) dofree(ia->lst4);
  if (ia->lst8) dofree(ia->lst8);

  if (ia->cnt) dofree(ia->cnt);
  if (ia->pos) dofree(ia->pos);
  if (ia->ofs) dofree(ia->ofs);
  if (ia->lofs) dofree(ia->lofs);
  clear(ia);
}

// access iadr pages
void acciadr(iadrbase *ia)
{
  if (ia->state < Iadr_cnt) return;
  ub4 n,mxy = ia->mxy;
  ub2 x = 0,*cp = ia->cnt;
  if (cp == NULL) return;
  for (n = 0; n < mxy; n += 2048) x ^= cp[n];
  ub8 xo = 0,*op = ia->ofs;
  if (op == NULL) return;
  for (n = 0; n < mxy; n += 1024) xo ^= op[n];
  info(0,"%s sum cnt %x ofs %lx",ia->desc,x,xo);
  warncc(ia->pos,0,"iadr %s not finalised",ia->desc);
}

int mkiadrmap(iadrbase *ia,const char *desc)
{
  errorccfln(ia->state != Iadr_init,Exit,ia->fln,"%s in state %u, not in init state",ia->desc,ia->state);
  ub8 nxy = ia->nxy;
  ub8 bxy = (nxy >> 6)+1;
  ia->xymap = alloc(bxy,ub8,0,desc,ia->ny);
  return 0;
}

int cpiadr(iadrbase *ia,iadrbase *iasrc)
{
  const char *desc = ia->desc;
  const char *sdesc = iasrc->desc;
  errorccfln(ia->state != Iadr_init,Exit,ia->fln,"%s state %u not in init state",desc,ia->state);
  errorccfln(iasrc->state != Iadr_cnt,Exit,iasrc->fln,"%s state %u not cnt",sdesc,iasrc->state);

  errorccfln(ia->nx != iasrc->nx,Exit,ia->fln,"%s has x %u, %s has %u",desc,ia->nx,sdesc,iasrc->nx);
  errorccfln(ia->ny != iasrc->ny,Exit,ia->fln,"%s has x %u, %s has %u",desc,ia->ny,sdesc,iasrc->ny);
  errorccfln(ia->shift != iasrc->shift,Exit,ia->fln,"%s has shift %u, %s has %u",desc,ia->shift,sdesc,iasrc->shift);

  memcopy(ia->cnt,iasrc->cnt,ia->mxy * sizeof(*ia->cnt));
  ia->inicnt = iasrc->inicnt;
  return 0;
}

// increment count for indirect adr list x,y
int iadrincnfln(iadrbase *ia,ub4 y,ub4 x,ub4 n,ub4 tid,ub4 fln)
{
  const char *desc = ia->desc;
  ub4 ny = ia->ny;
  ub4 nx = ia->nx;

  errorccfln(x >= nx,EXit,fln,"x:%u >= nx:%u %s",x,nx,desc);
  errorccfln(x + n > nx,Exit,fln,"x:%u + n:%u > nx:%u %s",x,n,nx,desc);
  errorccfln(y >= ny,EXit,fln,"y:%u >= ny:%u %s",y,ny,desc);
  errorccfln(ia->xymap,Exit,ia->fln,"xymap for %s not supported",desc);

  if (n == 0) return warn(0,"nil range for %s at %u,%u",ia->desc,y,x);

  ub4 shift = ia->shift;
  ub4 maxcnt = ia->maxcnt;

  ub4 ym = y >> shift;

  ub4 xm,xym,xe = x + n;
  ub2 cnt;

#ifdef Tidchk
  ub1 t,*tids = ia->tid;
#endif

  ia->tidset |= (1 << tid);

  do {
    xm = x >> shift;
    xym = ym * ia->mx + xm;

#ifdef Tidchk
    t = tids[xym];
    if (t != 0xff) {
      if (t != tid) return errorfln(FLN,0,fln,"%s tid %u cel %u written by tid %u",ia->desc,tid,xym,t);
    } else tids[xym] = (ub1)tid;
#endif

    cnt = ia->cnt[xym];

    error_eq(cnt,maxcnt);
    ia->cnt[xym] = (ub2)(cnt + 1);

    ia->inicnt++;
    x++;
  } while(x < xe);
  return 0;
}

// prepare iadr after count, before fill
int mkiadr1fln(iadrbase *ia,ub4 fln)
{
  ub8 sumcnt = 0;
  ub4 mx = ia->mx;
  ub4 my = ia->my;
  ub4 x,xy,mxy = mx * my;
  ub4 fulcnt = 0,mapcnt = 0,partcnt = 0;
  ub4 def = ia->def;
  ub8 def8 = ia->def8;
  ub4 shift = ia->shift;
  error_ge(shift,8);
  ub2 maxcnt = ia->maxcnt;

  error_zp(ia,0);

  ub2 cnt,*pcnt = ia->cnt;
  ub8 *pofs = ia->ofs;
  ub4 *plofs = ia->lofs;
  const char *desc = ia->desc;
  ub4 ifln = ia->fln;
  error_z(fln,0);

  errorccfln(ia->state != Iadr_init,Exit,fln,"%s state %u not in init state",desc,ia->state);

  if (ia->xymap) { afree(ia->xymap,"net"); ia->xymap = NULL; }

  for (xy = 0; xy < mxy; xy++) {
    plofs[xy] = partcnt;
    pofs[xy] = sumcnt;
    cnt = pcnt[xy];
    if (cnt > ia->cntlim) cnt = pcnt[xy] = maxcnt;
    if (cnt == maxcnt) {
      error_ovf(fulcnt,ub4);
      fulcnt++;
      mapcnt++;
    } else if (cnt) {
      error_ovf(mapcnt,ub4);
      mapcnt++;
      error_ge_cc(partcnt,hi32 - cnt,"xy \ah%u of \ah%u %s",xy,mxy,desc);
      partcnt += cnt;
    }
    sumcnt += cnt;
  }
  if (sumcnt == 0) {
    warnfln2(FLN,0,fln,"iadr %s is empty",desc);
    sumcnt = 1;
  }
  ia->sumcnt = sumcnt;
  ia->mapcnt = mapcnt;
  ub1 fill = (ub1)ia->def;

  switch(ia->elsize) {
  case 2: ia->lst2 = alloc(sumcnt,ub2,fill,desc,sumcnt);
          if (def == 0) break;
          for (x = 0; x < sumcnt; x++) ia->lst2[x] = (ub2)def;
          break;
  case 4: ia->lst4 = alloc(sumcnt,ub4,fill,desc,sumcnt);
          if (def == 0) break;
          for (x = 0; x < sumcnt; x++) ia->lst4[x] = def;
          break;
  case 8: ia->lst8 = alloc(sumcnt,ub8,fill,desc,sumcnt);
          if (def8 == 0) break;
          for (x = 0; x < sumcnt; x++) ia->lst8[x] = def8;
          break;
  default: return error(Exit,"unknown elsize %u",ia->elsize);
  }

  if (partcnt == 0) infofln2(FLN,0,fln,"no parts for %s",desc);
  else ia->dlst = alloc(partcnt,ub2,0,desc,partcnt);

  infofln2(FLN,0,ifln,"iadr %u,%u \ah%u items in \ah%u cels \ah%u full sum \ah%lu,\ah%u %s",ia->nx,ia->ny,ia->inicnt,mapcnt,fulcnt,sumcnt,partcnt,desc);
  ia->state = Iadr_cnt;
  return 0;
}

// write a value to indirect adr x,y
int wriadr2fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x,ub2 val)
{
  ub4 xm,ym,dx,dy,dxy,xy;
  ub8 ofs;
  ub4 n,lofs;
  ub2 *pdxy;
  ub2 pos,cnt,*ppos;
  ub2 *pmap;
  ub4 nx = ia->nx;
  ub2 *pxy = ia->xy2;
  const char *desc = ia->desc;

  errorccfln(ia->state != Iadr_cnt,Exit,fln,"%s state %u not in write state",desc,ia->state);
  if (ia->elsize != 2) errorfln(FLN,Exit,fln,"%s size %u not 2",desc,ia->elsize);

  if (ia->havexy) {
    if (pxy) {
      pxy[y * nx + x] = val;
      return 0;
    }
  }
  ub4 shift = ia->shift;
  ub4 mask = ia->mask;
  ub4 maxcnt = ia->maxcnt;

  ym = y >> shift;
  xm = x >> shift;
  dy = y & mask;
  dx = x & mask;

  xy = ym * ia->mx + xm;
  dxy = (dy << shift) | dx;

  ppos = ia->pos;
  cnt = ia->cnt[xy];
  if (cnt == 0) return errorfln(FLN,Exit,fln,"%s no cnt at y %u x %u",desc,y,x);
  ofs = ia->ofs[xy];

  if (ia->lst2 == NULL) return errorfln(FLN,Exit,fln,"%s write %u,%u on empty indir",desc,x,y);
  pmap = ia->lst2 + ofs;

  if (cnt == maxcnt) {  // full mode
    pmap[dxy] = val;
    return 0;
  }

  pos = ppos[xy];

  lofs = ia->lofs[xy];
  pdxy = ia->dlst + lofs;
  n = 0;
  while (n < pos) {
    if (pdxy[n] == dxy) {
      pmap[n] = val;
      return 0;
    }
    n++;
  }

  error_eq(pos,maxcnt);
  if (pos >= cnt) return errorfln(FLN,Exit,fln,"%s pos %u > cnt %u at y %u x %u",desc,pos,cnt,y,x);

  // new value
  ppos[xy] = (ub2)(pos + 1);
  pmap[pos] = val;
  pdxy[pos] = (ub2)dxy;

 return 0;
}

// write a value to indirect adr x,y
int wriadr4fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x,ub4 val)
{
  ub4 xm,ym,dx,dy,dxy,xy;
  ub8 ofs;
  ub4 n,lofs;
  ub2 *pdxy;
  ub2 pos,cnt,*ppos;
  ub4 *pmap;
  ub4 nx = ia->nx;
  ub4 *pxy = ia->xy4;
  const char *desc = ia->desc;

  errorccfln(ia->state != Iadr_cnt,Exit,fln,"%s state %u not in write state",desc,ia->state);
  if (ia->elsize != 4) errorfln(FLN,Exit,fln,"%s size %u not 4",desc,ia->elsize);

  if (ia->havexy) {
    if (pxy) {
      pxy[y * nx + x] = val;
      return 0;
    }
  }

  ub4 shift = ia->shift;
  ub4 mask = ia->mask;
  ub4 maxcnt = ia->maxcnt;

  ym = y >> shift;
  xm = x >> shift;
  dy = y & mask;
  dx = x & mask;

  xy = ym * ia->mx + xm;
  dxy = (dy << shift) | dx;

  ppos = ia->pos;
  cnt = ia->cnt[xy];
  if (cnt == 0) return errorfln(FLN,Exit,fln,"%s no cnt at y %u x %u",desc,y,x);
  ofs = ia->ofs[xy];

  if (ia->lst4 == NULL) return errorfln(FLN,Exit,fln,"%s write %u,%u on empty indir",desc,x,y);
  pmap = ia->lst4 + ofs;

  if (cnt == maxcnt) {  // full mode
    pmap[dxy] = val;
    return 0;
  }

  pos = ppos[xy];
  lofs = ia->lofs[xy];
  pdxy = ia->dlst + lofs;
  n = 0;
  while (n < pos) {
    if (pdxy[n] == dxy) {
      pmap[n] = val;
      return 0;
    }
    n++;
  }

  error_eq(pos,maxcnt);
  if (pos >= cnt) return errorfln(FLN,Exit,fln,"%s pos %u > cnt %u at y %u x %u",desc,pos,cnt,y,x);

  // new value
  ppos[xy] = (ub2)(pos + 1);
  pmap[pos] = val;
  pdxy[pos] = (ub2)dxy;

 return 0;
}

// write a value to indirect adr x,y
int wriadr8fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x,ub8 val)
{
  ub4 xm,ym,dx,dy,dxy,xy;
  ub8 ofs;
  ub4 n,lofs;
  ub2 *pdxy;
  ub2 pos,cnt,*ppos;
  ub8 *pmap;
  ub4 nx = ia->nx;
  ub8 *pxy = ia->xy8;
  const char *desc = ia->desc;

  errorccfln(ia->state != Iadr_cnt,Exit,fln,"%s state %u not in write state",desc,ia->state);
  if (ia->elsize != 8) errorfln(FLN,Exit,fln,"%s size %u not 8",desc,ia->elsize);

  if (ia->havexy) {
    if (pxy) {
      pxy[y * nx + x] = val;
      return 0;
    }
  }

  ub4 shift = ia->shift;
  ub4 mask = ia->mask;
  ub4 maxcnt = ia->maxcnt;

  ym = y >> shift;
  xm = x >> shift;
  dy = y & mask;
  dx = x & mask;

  xy = ym * ia->mx + xm;
  dxy = (dy << shift) | dx;

  ppos = ia->pos;
  cnt = ia->cnt[xy];

  if (cnt == 0) {
    if (ia->opts & Iadr_softlim) return warnfln2(FLN,Ret1,fln,"%s no cnt at y %u x %u",desc,y,x);
    else return errorfln(FLN,Exit,fln,"%s no cnt at y %u x %u",desc,y,x);
  }
  ofs = ia->ofs[xy];

  if (ia->lst8 == NULL) return errorfln(FLN,Exit,fln,"%s write %u,%u on empty indir",desc,x,y);
  pmap = ia->lst8 + ofs;

  if (cnt == maxcnt) {  // full mode
    pmap[dxy] = val;
    return 0;
  }

  pos = ppos[xy];
  lofs = ia->lofs[xy];
  pdxy = ia->dlst + lofs;

  if ((ia->opts & Iadr_append) == 0) {
    n = 0;
    while (n < pos) {
      if (pdxy[n] == dxy) {
        pmap[n] = val;
        return 0;
      }
      n++;
    }
#if 0
  } else {
    n = 0;
    while (n < pos) {
      if (pdxy[n] == dxy) return warnfln2(FLN,Ret1,fln,"%s duplicate at pos %u n %u at y %u x %u ym %u xm %u",desc,n,pos,y,x,ym,xm);
      n++;
    }
#endif
  }

  error_eq(pos,maxcnt);
  if (pos >= cnt) {
    if (ia->opts & Iadr_softlim) return warnfln2(FLN,Ret1,fln,"%s pos %u > cnt %u at y %u x %u ym %u xm %u",desc,pos,cnt,y,x,ym,xm);
    else return errorfln(FLN,0,fln,"%s pos %u > cnt %u at %u,%u = %u,%u",desc,pos,cnt,y,x,ym,xm);
  }

  // new value
  ppos[xy] = (ub2)(pos + 1);
  pmap[pos] = val;
  pdxy[pos] = (ub2)dxy;

 return 0;
}

// finalize indir, no new values to be added
int finiadr(iadrbase *ia)
{
  errorccfln(ia->state != Iadr_cnt,Exit,ia->fln,"%s state %u not in write state",ia->desc,ia->state);
  ia->state = Iadr_fin;
  if (ia->pos) { dofree(ia->pos); ia->pos = NULL; }
  return 0;
}

// read a value from indirect adr x,y
ub4 rdiadr4fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x)
{
  ub4 xm,ym,dx,dy,dxy,xy;
  ub8 ofs;
  ub4 n,cnt,lofs;
  ub2 *pdxy;
  ub4 *pmap;
  ub4 *lst;
  ub4 *pxy = ia->xy4;
  ub4 val,chkval;
  const char *desc = ia->desc;

  if (*desc == 0) errorfln(FLN,EXit,fln,"uninitialised iadr for read %u,%u",y,x);
  if (ia->state < Iadr_cnt) errorfln(FLN,EXit,ia->fln,"%s not in read state",desc);
  if (ia->elsize != 4) errorfln(fln,EXit,ia->fln,"%s read size %u not 4",desc,ia->elsize);
  if (y >= ia->ny) errorfln(fln,EXit,ia->fln,"%s y %u out of range %u",desc,y,ia->ny);
  if (x >= ia->nx) errorfln(fln,EXit,ia->fln,"%s y %u out of range %u",desc,x,ia->nx);

  if (pxy) {
    chkval = pxy[y * ia->nx + x];  // original 2d case
    return chkval;
  }

  ub4 shift = ia->shift;
  ub4 mask = ia->mask;
  ub4 maxcnt = ia->maxcnt;

  ym = y >> shift;
  xm = x >> shift;

  xy = ym * ia->mx + xm;
  cnt = ia->cnt[xy];
  if (cnt == 0) return ia->def;

  dy = y & mask;
  dx = x & mask;
  dxy = (dy << shift) | dx;

  ofs = ia->ofs[xy];
  lst = ia->lst4;

  error_zp(lst,y);
  pmap = lst + ofs;

  if (cnt == maxcnt) {
    val = pmap[dxy];
//    error_ne(val,chkval);
    return val;
  }

  lofs = ia->lofs[xy];
  pdxy = ia->dlst + lofs;
  n = 0;
  while (n < cnt) {
    if (pdxy[n] == dxy) {
      val = pmap[n];
//      error_ne(val,chkval);
      return val;
    }
    n++;
  }
  val = ia->def;
//  error_ne(val,chkval);
  return val;
}

ub8 rdiadr8fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x)
{
  ub4 xm,ym,dx,dy,dxy,xy;
  ub8 ofs;
  ub4 n,cnt,lofs;
  ub2 *pdxy;
  ub8 *pmap;
  ub8 *lst;
  ub8 *pxy = ia->xy8;
  ub8 val,chkval;
  const char *desc = ia->desc;

  globs.msgfln = fln;
  globs.msgarg1 = y;
  globs.msgarg2 = x;

  if (*desc == 0) errorfln(FLN,EXit,fln,"uninitialised iadr for read %u,%u",y,x);
  if (ia->state < Iadr_cnt) errorfln(FLN,EXit,ia->fln,"%s not in read state",desc);
  if (ia->elsize != 8) errorfln(fln,EXit,ia->fln,"%s read size %u not 8",desc,ia->elsize);
  if (y >= ia->ny) errorfln(fln,EXit,ia->fln,"%s y %u out of range %u",desc,y,ia->ny);
  if (x >= ia->nx) errorfln(fln,EXit,ia->fln,"%s y %u out of range %u",desc,x,ia->nx);

  if (pxy) {
    chkval = pxy[y * ia->nx + x];  // original 2d case
    return chkval;
  }

  ub4 shift = ia->shift;
  ub4 mask = ia->mask;
  ub4 maxcnt = ia->maxcnt;

  ym = y >> shift;
  xm = x >> shift;

  xy = ym * ia->mx + xm;
  cnt = ia->cnt[xy];
  if (cnt == 0) return ia->def8;

  globs.msgarg3 = cnt;

  dy = y & mask;
  dx = x & mask;
  dxy = (dy << shift) | dx;

  ofs = ia->ofs[xy];
  lst = ia->lst8;

  error_zp(lst,y);
  pmap = lst + ofs;

  if (cnt == maxcnt) {
    val = pmap[dxy];
//    error_ne(val,chkval);
    return val;
  }

  lofs = ia->lofs[xy];
  pdxy = ia->dlst;
  if (pdxy == NULL) errorfln(FLN,EXit,fln,"pdxy 0 for ofs %u cnt %u %u,%u %s",lofs,cnt,y,x,desc);
  pdxy += lofs;
  n = 0;
  while (n < cnt) {
    if (pdxy[n] == dxy) {
      val = pmap[n];
//      error_ne(val,chkval);
      return val;
    }
    n++;
  }
  val = ia->def8;
//  error_ne(val,chkval);
  return val;
}

ub2 rdiadr2fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x)
{
  ub4 xm,ym,dx,dy,dxy,xy;
  ub8 ofs;
  ub4 n,cnt,lofs;
  ub2 *pdxy;
  ub2 *pmap;
  ub2 *lst;
  ub2 *pxy = ia->xy2;
  ub2 val,chkval;

  // if (*desc == 0) errorfln(FLN,EXit,fln,"uninitialised iadr for read %u,%u",y,x);
  // if (ia->state < Iadr_cnt) errorfln(FLN,EXit,ia->fln,"%s state %u not in read",desc,ia->state);
  // if (ia->elsize != 2) errorfln(fln,EXit,ia->fln,"%s read size %u not 2",desc,ia->elsize);
  if (y >= ia->ny) errorfln(fln,EXit,ia->fln,"%s y %u out of range %u",ia->desc,y,ia->ny);
  if (x >= ia->nx) errorfln(fln,EXit,ia->fln,"%s y %u out of range %u",ia->desc,x,ia->nx);

  if (pxy) {
    chkval = pxy[y * ia->nx + x];  // original 2d case
    return chkval;
  }

  ub4 shift = ia->shift;

  ym = y >> shift;
  xm = x >> shift;
  xy = ym * ia->mx + xm;

  cnt = ia->cnt[xy];
  if (cnt == 0) return (ub2)ia->def;

  ub4 mask = ia->mask;

  dy = y & mask;
  dx = x & mask;
  dxy = (dy << shift) | dx;

  ofs = ia->ofs[xy];
  lst = ia->lst2;
  // error_zp(lst,y);
  pmap = lst + ofs;

  ub4 maxcnt = ia->maxcnt;

  if (cnt == maxcnt) {
    val = pmap[dxy];
//    error_ne(val,chkval);
    return val;
  }

  lofs = ia->lofs[xy];
  pdxy = ia->dlst + lofs;
  n = 0;
  while (n < cnt) {
    if (pdxy[n] == dxy) {
      val = pmap[n];
//      error_ne(val,chkval);
      return val;
    }
    n++;
  }
  val = (ub2)ia->def;
//  error_ne(val,chkval);
  return val;
}

// get count for indirect adr x,y
ub2 iadrcntfln(iadrbase *ia,ub4 y,ub4 x,ub4 fln)
{
  error_ge(x,ia->nx);
  error_ge(y,ia->ny);

  if (ia->state != Iadr_cnt) errorfln(FLN,EXit,fln,"%s state %u not in count",ia->desc,ia->state);

  ub4 shift = ia->shift;

  ub8 xy,bit,bmask,*xymap = ia->xymap;

  if (xymap) {
    xy = (ub8)y * ia->nx + x;
    bit = 1UL << (xy & 0x3f);
    bmask = xymap[xy >> 6];
    if (bmask & bit) return 1;
  }

  ub4 ym = y >> shift;
  ub4 xm = x >> shift;
  ub4 xym = ym * ia->mx + xm;
  ub2 cnt = ia->cnt[xym];

  return cnt;
}

void iniiadr(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
}
