// mem.c - memory allocation wrappers and provisions

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/* Memory allocation:
   wrappers, pool allocators
 */

#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

#include "base.h"
#include "os.h"
#include "mem.h"

static ub4 msgfile;
#include "msg.h"

// soft limit for wrappers only, from config
static ub4 Maxmem_mb;

static ub4 allocrep = 1; // report threshold in mb

static const ub4 mmap_from_mb = 16;

#define Ablocks 4096

static ub4 totalMB;

struct sumbyuse {
  char id[16];
  ub4 idlen;
  ub4 sum;
  ub4 hi,hicnt;
  char hidesc[128];
  ub4 fln,hifln;
};

struct ainfo {
  char *base;
  size_t len,kb;
  ub4 mb;
  ub4 allocfln;
  ub4 freefln;
  ub4 alloced;
  ub4 istmp;
  ub4 mmap;
  char desc[64];
};

static struct sumbyuse usesums[32];

static block lrupool[256];

static block *lruhead = lrupool;

static struct ainfo ainfos[Ablocks];
static ub4 curainfo;

static const ub4 blkmagic = 0x3751455d;

static void addsum(ub4 fln,const char *desc,ub4 mbcnt)
{
  ub4 idlen = 0;
  struct sumbyuse *up = usesums;

  totalMB += mbcnt;

  while (desc[idlen] && desc[idlen] != ' ' && idlen < sizeof(up->id)-1) idlen++;
  if (idlen == 0) return;

  while (up < usesums + Elemcnt(usesums) && up->idlen && (up->idlen != idlen || memcmp(up->id,desc,idlen))) up++;
  if (up == usesums + Elemcnt(usesums)) return;
  up->idlen = idlen;
  memcpy(up->id,desc,idlen);
  up->fln = fln;
  up->sum += mbcnt;
  if (mbcnt > 512) infofln2(up->fln,V0,FLN,"category %s memuse %u MB adding %u for %s",up->id,up->sum,mbcnt,desc);
  if (mbcnt > up->hi) {
    up->hi = mbcnt;
    if (up->hifln == fln) up->hicnt++;
    else up->hicnt = 1;
    up->hifln = fln;
    strcopy(up->hidesc,desc);
  }
}

static void subsum(const char *desc,ub4 mbcnt)
{
  ub4 idlen = 0;
  struct sumbyuse *up = usesums;

  totalMB -= min(mbcnt,totalMB);

  while (desc[idlen] && desc[idlen] != ' ' && idlen < sizeof(up->id)-1) idlen++;
  if (idlen == 0) return;

  while (up < usesums + Elemcnt(usesums) && up->idlen && (up->idlen != idlen || memcmp(up->id,desc,idlen))) up++;
  if (up == usesums + Elemcnt(usesums)) return;
  up->sum -= min(mbcnt,up->sum);
}

static int showedmemsums;

void showmemsums(void)
{
  struct sumbyuse *up = usesums;

  if (globs.nomemsum) return;

  infocc(totalMB > 16,0,"total memuse %u MB",totalMB);
  while (up < usesums + Elemcnt(usesums) && up->idlen) {
    if (up->sum > 16) {
      infofln(up->fln,0,"category %s memuse %u MB",up->id,up->sum);
      infofln(up->hifln,0,"  hi %u MB * %u for %s",up->hi,up->hicnt,up->hidesc);
    }
    up++;
  }
  showedmemsums = 1;
}

static int isasan(void)
{
#if defined(__clang__) && defined(__clang_major__) && defined(__clang_minor__)

 #ifdef __has_feature
  #if __has_feature(address_sanitizer)
   return 1;
  #else
   return 0;
  #endif
 #endif

#elif defined(__GNUC__) && defined(__GNUC_MINOR__)

  #ifdef __SANITIZE_ADDRESS__
   return 1;
  #else
   return 0;
  #endif
#else
  return 0;
#endif
}

void *alloc_fln(size_t elems,ub4 elsize,const char *slen,const char *sel,ub1 fill,ub4 tmp,const char *desc,const char *sarg,size_t arg,ub4 fln)
{
  ub8 n8 = elems * elsize;
  size_t n,nk;
  ub4 nm;
  ub4 andx;
  void *p;
  struct ainfo *ai = ainfos + curainfo;
  char descstr[128];
  char infostr[256];
  char memstr[64];
  char tmpind = tmp ? 'm' : 'M';

  if (desc && *desc) {
    if (arg && arg == elems && !strcmp(sarg,slen)) arg = 0;
    if (arg) { fmtstring(descstr," - %.64s %.32s:\ah%lu",desc,sarg,arg); }
    else { fmtstring(descstr," - %.64s",desc); }
  } else *descstr = 0;

  if (curainfo + 1 == Ablocks) errorfln(fln,EXit,FLN,"exceeding limit of %u memblocks allocating %s",Ablocks,descstr);

  n = (size_t)n8;
  nk = n >> 10;
  nm = (ub4)(n8 >> 20);
  if (n8 != n) errorfln(fln,Exit,FLN,"wraparound allocating %u MB %s", nm, descstr);

  if (nm > 4096) fmtstring(memstr,"%lu GB",n >> 30);
  else if (nk > 4096) fmtstring(memstr,"%lu MB",n >> 20);
  else if (n > 4096) fmtstring(memstr,"%lu KB",n >> 10);
  else fmtstring(memstr,"%lu B",n);

  fmtstring(infostr,"%.32s:\ah%lu * %.32s:\ah%u = %s %s",slen,elems,sel,elsize,memstr,descstr);

  // check for zero and overflow
  if (elems == 0) {
    errorfln(fln,Exit,FLN,"%s = 0 %s",slen,descstr);
    return NULL;
  }
  if (elsize == 0) fatalfln(fln,0,FLN,"elsize 0 for %s",desc);

  if (fill != 0 && fill != 0xff) infofln(fln,0,"fill with %u",fill);

  if (Maxmem_mb && nm >= Maxmem_mb) {
    showmemsums();
    errorfln(fln,Exit,FLN,"exceeding %u MB limit by %s %s",Maxmem_mb,memstr,infostr);
  }
  if (Maxmem_mb && totalMB + nm >= Maxmem_mb) {
    showmemsums();
    errorfln(fln,Exit,FLN,"exceeding %u MB limit by %u+%u=%u MB %s",Maxmem_mb,totalMB,nm,nm + totalMB,infostr);
  }

  ub4 mcode = (nm < allocrep ? V0 : 0);
  if (nm >= mmap_from_mb) {
    infofln(fln,mcode,"mem.%u %calloc %u MB.%s",__LINE__,tmpind,nm,infostr);
    p = osmmap(n);
    if (!p) { warnfln2(fln,EXit,FLN,"cannot alloc %s, total %u",infostr,totalMB); return NULL; } // osmmap() already errors
    if (fill) {
      infofln(fln,mcode,"mem.%u fill %s with 0x%x %s",__LINE__,memstr,(ub4)fill,infostr);
      memset(p,fill,n);
    }
  } else {
    infofln(fln,mcode,"mem.%u %calloc %u MB %s",__LINE__,tmpind,nm,infostr);
    p = malloc(n);
    if (!p) { errorfln(fln,EXit,FLN,"cannot allocate %s for %s, total %u MB", memstr,infostr,totalMB); return NULL; }
    else if (globs.sigint) { errorfln(fln,EXit,FLN,"interupted allocating %s for %s, total %u MB", memstr,infostr,totalMB); return NULL; }
    memset(p,fill,n);
  }
  if (globs.sigint) return NULL;

  addsum(fln,desc,nm);

  for (andx = 0; andx < curainfo; andx++) {
    ai = ainfos + andx;
    if (p == ai->base) break;
  }
  if (curainfo && andx < curainfo) {
    if (ai->alloced) {
      errorfln(fln,Exit,ai->allocfln,"mem.%u previously allocated %s",__LINE__,descstr);
    }
  } else ai = ainfos + curainfo++;

  ai->base = p;
  ai->allocfln = fln;
  ai->freefln = 0;
  ai->alloced = 1;
  ai->mmap = (nm >= mmap_from_mb);
  ai->mb = nm;
  ai->kb = nk;
  ai->len = n;
  ai->istmp = tmp;
  strncpy(ai->desc,desc,sizeof(ai->desc)-1);
  if (nm > 1024) infofln2(fln,0,FLN,"mem.%u alloced %s for %s, total %u MB",__LINE__,memstr,descstr,totalMB);
  return p;
}

int afree_fln(void *p,ub4 fln, const char *desc)
{
  block *b = lrupool;
  struct ainfo *ai = ainfos;
  ub4 andx;
  ub4 nm;

  vrbfln(fln,0,"free %p",p);
  if (!p) return errorfln(fln,0,FLN,"free nil pointer for %s",desc);

  // check if allocated with mkblock
  for (b = lrupool; b < lrupool + Elemcnt(lrupool); b++) {
    if (b->seq == 0) continue;
    if (p == b->base) return errorfln(fln,Exit,FLN,"free pointer '%s' allocated with '%s'",desc,b->desc);
  }

  // check if previously allocated
  for (andx = 0; andx < curainfo; andx++) {
    ai = ainfos + andx;
    if (p == ai->base) break;
  }
  if (andx == curainfo) return errorfln(fln,Exit,FLN,"free pointer %p '%s' was not allocated with alloc",p,desc);
  if (ai->freefln) {
    errorfln(fln,0,FLN,"double free of pointer %p '%s'",p,desc);
    return errorfln(ai->freefln,Exit,ai->allocfln,"allocated and previously freed %s",desc);
  }

  ai->freefln = fln;
  ai->alloced = 0;
  nm = ai->mb;
  subsum(desc,nm);
  ub4 mcode = (nm < allocrep ? V0 : 0);

  if (ai->mmap) {
    infofln2(ai->allocfln,mcode,fln,"mem.%u Free %u mb from %s",__LINE__,ai->mb,desc);
    if (osmunmap(p,ai->len)) return oserror(EXit,"cannot free %u MB at %p",nm,p);
  } else {
    infofln2(ai->allocfln,mcode,fln,"mem.%u free %u mb from %s",__LINE__,ai->mb,desc);
    free(p);
  }
  return globs.sigint;
}

void achktmpfree(void)
{
  struct ainfo *ai = ainfos;
  ub4 andx,n = 0,mb = 0;
  ub8 kb = 0;

  for (andx = 0; andx < curainfo; andx++) {
    ai = ainfos + andx;
    if (ai->alloced && ai->istmp) {
      n++;
      mb += ai->mb;
      kb += ai->kb;
    }
  }
  if (n == 0) return;

  info(0,"\ah%lu in %u tmp block\as not freed",kb << 10,n);

  for (andx = 0; andx < curainfo; andx++) {
    ai = ainfos + andx;
    if (ai->alloced == 0 || ai->istmp == 0) continue;
    if (ai->mb) warnfln(ai->allocfln,0,"mem.%u tmp block not freed %s %u MB",__LINE__,ai->desc,ai->mb);
    else if (ai->kb >= 64) infofln(ai->allocfln,0,"mem.%u tmp block not freed %s %lu KB",__LINE__,ai->desc,ai->kb);
  }
}

// static block *lrutail = lrupool;
static ub4 blockseq = 1;

void * trimblock_fln(block *blk,size_t elems,ub4 elsize,const char *selems,const char *selsize,ub4 fln)
{
  void *p;
  char *desc;
  char buf[64];

  error_zp(blk,fln);

  if (blkmagic != blk->magic) errorfln(fln,Exit,FLN,"uninitialised block for trim %s:\ah%lu elems",selems,elems);
  desc = blk->desc;

  if (elsize == 0) errorfln(fln,Exit,FLN,"zero element size %s",desc);
  if (elsize != blk->elsize) errorfln(fln,Exit,FLN,"size mismatch: %s size %u on %s size %u block '%s'",selsize,elsize,blk->selsize,blk->elsize,desc);

  if (elems == 0 && blk->elems == 0) {
    msgfln(buf,0,sizeof(buf),blk->fln,12);
    errorfln(fln,Exit,FLN,"%s previously freed at %s",desc,buf);
  }
  if (elems >= blk->elems) errorfln(fln,Exit,FLN,"%s:\ah%lu above %s:\ah%lu block '%s'",selems,elems,blk->selems,blk->elems,desc);

  p = blk->base;
  ub8 len = blk->elems * blk->elsize;
  ub8 newlen = elems * blk->elsize;
  ub4 nm = (ub4)(len >> 20);
  ub4 newnm = (ub4)(newlen >> 20);

  ub4 mcode = (nm < allocrep ? V0 : 0);

  if (elems == 0) {
    if (blk->mmap) {
      infofln(fln,mcode,"mem.%u Free \ah%u MB for %s",__LINE__,nm,desc);
      if (osmunmap(p,len)) oserror(Ret0,"cannot free %u MB at %p for %s",nm,p,desc);
    } else {
      infofln(fln,mcode,"mem.%u free \ah%u MB for %s",__LINE__,nm,desc);
      free(p);
    }
    p = NULL;
  } else {
    if (blk->mmap) {
      infofln(fln,mcode,"mem.%u Realloc from \ah%u to \ah%u MB for %s",__LINE__,nm,newnm,desc);
      osmremap(blk->base,blk->elems * elsize,elems * elsize);
      return p;
    } else {
      infofln(fln,mcode,"mem.%u realloc from \ah%u to \ah%u MB for %s",__LINE__,nm,newnm,desc);
      p = realloc(blk->base,elems * elsize);
      if (!p) errorfln(fln,Exit,FLN,"cannot reallocate to \ah%lu for %s",elems * elsize,desc);
    }
  }
  blk->base = p;
  blk->elems = elems;
  blk->elsize = elsize;
  blk->selems = selems;
  blk->selsize = selsize;
  blk->fln = fln;
  subsum(desc,nm - newnm);
  return p;
}

void * __attribute__ ((format (printf,8,9))) mkblock_fln(
  block *blk,
  size_t elems,
  ub4 elsize,
  enum Blkopts opts,
  const char *selems,const char *selsize,
  ub4 fln,
  const char *fmt,...)
{
  va_list ap;
  char *desc;
  ub4 descpos,descpos2,desclen;
  ub8 n8 = (ub8)elems * (ub8)elsize;
   size_t n;
  ub4 nm;
  void *p;

  error_zp(blk,fln);

  desc = blk->desc;
  desclen = sizeof(blk->desc);
  descpos = 0;

  if (blkmagic == blk->magic) errorfln(fln,Exit,FLN,"reusing block %s",desc);

  if (fmt && *fmt) {
    va_start(ap,fmt);
    descpos = myvsnprintf(desc,0,desclen,fmt,ap);
    va_end(ap);
  } else *desc = 0;

  // check for zero and overflow
  if (elems == 0) errorfln(fln,Exit,FLN,"0 %s elems for %s for block %s",selsize,selems,desc);
  if (elsize == 0) errorfln(fln,Exit,FLN,"element %s has zero size for block %s",selsize,desc);

  blk->magic = blkmagic;

  descpos += mysnprintf(desc,descpos,desclen," \ah%lu %s of %u %s ",(unsigned long)elems,selems,elsize,selsize);
  descpos2 = descpos + msgfln(desc,descpos,desclen,fln,8);

  blk->desclen = descpos2;
  blk->seq = blockseq++;

  vrbfln(fln,V0,"block '%s' ",desc);

  // check for overflow

  n = (size_t)n8;
  nm = (ub4)(n8 >> 20);
  if (n8 != n) errorfln(fln,Exit,FLN,"wraparound allocating %u MB for %s",nm,desc);

  if (nm >= Maxmem_mb) errorfln(fln,Exit,FLN,"exceeding %u MB limit by %u MB for %s",Maxmem_mb,nm,desc);
  if (totalMB + nm >= Maxmem_mb) errorfln(fln,Exit,FLN,"exceeding %u MB limit by %u MB for %s",Maxmem_mb,nm,desc);

  ub4 mcode = (nm < allocrep ? V0 : 0);

  if (nm >= mmap_from_mb) {
    infofln(fln,mcode,"mem.%u Alloc %u MB.%.*s",__LINE__,nm,descpos,desc);
    p = osmmap(n);
    if (!p) errorfln(fln,EXit,FLN,"cannot allocate %u MB for %s, total %u",nm,desc,totalMB);
    blk->mmap = 1;
    if (opts & Init1) {
      if (nm > 512) infofln(fln,0,"mem.%u preset %u MB",__LINE__,nm);
      memset(p, 0xff, n);
    }
  } else {
    infofln(fln,mcode,"mem.%u alloc %u MB for %s",__LINE__,nm,desc);
    p = malloc(n);
    if (!p) errorfln(fln,EXit,FLN,"cannot allocate %u MB for %s",nm,desc);
    blk->mmap = 0;

    if (nm > 512 && (opts & (Init0|Init1) ) ) infofln(fln,0,"mem.%u preset %u MB",__LINE__,nm);
    if (opts & Init0) memset(p, 0, n);
    else if (opts & Init1) memset(p, 0xff, n);
  }

  blk->base = p;
  blk->elems = elems;
  blk->elsize = elsize;
  blk->selems = selems;
  blk->selsize = selsize;
  blk->fln = fln;

  infofln(fln,nm > 1024 ? 0 : V0,"mem.%u alloced %u MB for %s, total %u",__LINE__,nm,desc,totalMB);

  addsum(fln,desc,nm);

  if (lruhead >= lrupool + Elemcnt(lrupool)) lruhead = lrupool;
  memcpy(lruhead,blk,sizeof(block));

  return p;
}

size_t nearblock(size_t adr)
{
  block *b = lrupool,*blklo,*blkhi;
  size_t base,top,nearlo,nearhi;
  ub4 pos;
  char buf[1024];

  nearlo = nearhi = hi32;
  blklo = blkhi = b;

  for (b = lrupool; b < lrupool + Elemcnt(lrupool); b++) {
   if (b->seq == 0) continue;
    base = (size_t)b->base;
    top = base + b->elems * b->elsize;
    if (adr < base) {
      if (base - adr < nearlo) { nearlo = base - adr; blklo = b; }
    } else if (adr >= top - 16) {
      if (adr - top < nearhi) { nearhi = adr - top; blkhi = b; }
    } else {
      return base;
    }
  }
  if (nearhi < 4096) {
    pos = mysnprintf(buf,0,sizeof buf,"%lx %u above block '%s'\n", (unsigned long)adr,(ub4)nearhi,blkhi->desc);
    oswrite(1,buf,pos);
    return (size_t)(blkhi->base);
  }
  if (nearlo < 4096) {
    pos = mysnprintf(buf,0,sizeof buf,"%lx %u below block '%s'\n", (unsigned long)adr,(ub4)nearlo,blklo->desc);
    oswrite(1,buf,pos);
    return (size_t)(blklo->base);
  }
  return adr;
}

void bound_fln(block *blk,size_t pos,ub4 elsize,const char *spos,const char *selsize,ub4 fln)
{
  if (blkmagic != blk->magic) errorfln(fln,Exit,FLN,"uninitialised block in bounds check pos '%s':%lu of %s:%u",spos,(unsigned long)pos,selsize,elsize);

  if (elsize != blk->elsize) errorfln(fln,Exit,FLN,"size mismatch: %s size %u on %s size %u block '%s'",selsize,elsize,blk->selsize,blk->elsize,blk->desc);
  if (pos >= blk->elems) errorfln(fln,Exit,FLN,"%s pos %lu %u above %s len %lu block '%s'",spos,pos,(ub4)(pos - blk->elems),blk->selems,blk->elems,blk->desc);
}

int memrdonly(void *p,size_t len)
{
  if ((size_t)p & 4095) return 0;
  return osmemrdonly(p,len);
}

ub4 meminfo(void) { return osmeminfo(); }

int mempgin(void)
{
  if (osmlock() == 0) return osmunlock();
  else return 1;
}

void memcfg(ub4 maxvm,ub4 rep)
{
  if (isasan()) info0(Emp,"no soft VM limit in asan");

  info(Emp,"setting soft VM limit to %u GB",maxvm);
  Maxmem_mb = (maxvm == hi24 ? hi32 : maxvm * 1024);
  allocrep = rep;
  info(0,"setting allocation report threshold to %u MB",rep);
}

void inimem(void)
{
  msgfile = setmsgfile2(__FILE__,Msgfile_noiter);
  iniassert();
}

void eximem(void)
{
  if (showedmemsums == 0) showmemsums();
}
