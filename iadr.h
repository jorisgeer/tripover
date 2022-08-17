// iadr.h - indirect addressing for 2D arrays

/*
  A compact representation for relatively sparse 2D arrays
  16 x 16 cells are grouped into a tile
  each tile has a total cell count and a list of <offset,value>
  the offset is the coordinate within the tile
  if count is relatively large, the tile is filled completely and no search is done
 */

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2015 Joris van der Geer.
 */

enum iadrstate { Iadr_none,Iadr_init,Iadr_cnt,Iadr_fin };

enum iadropts { Iadr_append = 1,Iadr_softlim = 2,Iadr_defhi = 4,Iadr_okdup = 8 };

#define Maxmask 0x1f

#undef Tidchk

#ifdef __clang__
 #pragma clang diagnostic push
 #pragma clang diagnostic error "-Wconversion"
#endif

struct siadrbase {
  char desc[128];
  enum iadrstate state;
  ub4 fln;
  ub2 vrb;
  ub2 havexy;
  ub4 opts;

  ub4 shift,mask;

  ub4 nx,ny,mx,my,mxy;
  ub4 ylim;   // use orig xy if y below lim
  ub8 nxy;
  ub2 cntlim; // use full cell map if cnt above lim
  ub2 elsize;
  ub2 maxcnt;
  ub4 def;    // value for n/a
  ub8 def8;

  ub8 sumcnt;
  ub4 mapcnt;
  ub4 cntovf;

  ub1 *tid;   // [ nx * ny / 256 ] (dx,dy) tid owners
  ub2 *cnt;   // [ nx * ny / 256 ] (dx,dy) items counts
  ub2 *pos;   // [ nx * ny / 256 ] (dx,dy) items counts at fill
  ub8 *ofs;   // [ nx * ny / 256 ] start of [dx * dy] map
  ub4 *lofs;  // [ nx * ny / 256 ] start of [dx * dy] lst

  ub4 *lst4;   // value maps at offset above
  ub2 *lst2;
  ub8 *lst8;

  ub2 *dlst;  // (dx,dy) tuples for each map at offset above
  ub8 *xymap; // [ nx * ny / 64 ] tmp bitmap

  ub2 *xy2;   // [nx * ny] original 2d
  ub4 *xy4;
  ub8 *xy8;

  ub4 inicnt,filcnt;
  ub8 tidset;
};
typedef struct siadrbase iadrbase;

#define iadrinc(ia,y,x,t) iadrincfln((ia),(y),(x),(t),FLN)

static inline int iadrinmap(iadrbase *ia,ub4 y,ub4 x)
{
  ub8 xy,bit,bmask,*xymap = ia->xymap;
  if (xymap == NULL) return 0;

  xy = (ub8)y * ia->nx + x;
  bit = 1UL << (xy & 0x3f);
  bmask = xymap[xy >> 6];
  if (bmask & bit) return 1;
  else return 0;
}

// increment count for indirect adr x,y
static inline int iadrincfln(iadrbase *ia,ub4 y,ub4 x,ub4 tid,ub4 fln)
{
  error_ge(x,ia->nx);
  error_ge(y,ia->ny);
  char *desc = ia->desc;

  if (ia->state != Iadr_init) errorfln(fln,EXit,ia->fln,"iadr.h:%u: %s state %u not in count",__LINE__,desc,ia->state);

  ub4 shift = ia->shift;
  ub4 maxcnt = ia->maxcnt;

  ub8 xy,bit,bmask,*xymap = ia->xymap;

  if (xymap) {
    xy = (ub8)y * ia->nx + x;
    bit = 1UL << (xy & 0x3f);
    bmask = xymap[xy >> 6];
    if (bmask & bit) return 0;
    xymap[xy >> 6] = bmask | bit;
  }
  ub4 ym = y >> shift;
  ub4 xm = x >> shift;
  ub4 xym = ym * ia->mx + xm;
  ub2 cnt = ia->cnt[xym];

  if (cnt == maxcnt) {
    ia->cntovf++;
    if (ia->opts & Iadr_okdup) {
      // infofln(fln,0,"iadr.h:%u %s: %u,%u cnt %u == max shift %u",__LINE__,desc,y,x,cnt,shift);
      return 0;
    }
    return errorfln(fln,0,0,"iadr.h:%u %s: cnt %u == max shift %u",__LINE__,desc,cnt,shift);
  }

  ia->tidset |= (1 << tid);
#ifdef Tidchk
  ub1 t,*tids = ia->tid;
  t = tids[xym];
  if (t != 0xff) {
    if (t != tid) return errorfln(fln,0,ia->fln,"iadr.h:%u %s tid %u cel %u written by tid %u",__LINE__,desc,tid,xym,t);
  } else tids[xym] = (ub1)tid;
#endif

  ia->cnt[xym] = (ub2)(cnt + 1);
  ia->inicnt++;
  return 0;
}

#define mkiadr0(ia,ny,nx,t,ylim,clim,desc) mkiadr0fln(FLN,(ia),(ny),(nx),sizeof(t),(ylim),(clim),(desc))

extern int mkiadr0fln(ub4 fln,iadrbase *ia,ub4 ny,ub4 nx,ub2 elsize,ub4 xylim,ub2 clim,const char *desc);
extern int mkiadrmap(iadrbase *ia,const char *desc);

#define mkiadr1(ia) mkiadr1fln((ia),FLN)

extern int mkiadr1fln(iadrbase *ia,ub4 fln);
extern int finiadr(iadrbase *ia);

extern int setiadropts(iadrbase *ia,ub4 opts);

extern int cpiadr(iadrbase *ia,iadrbase *iasrc);

#define iadrincn(ia,y,x,n,t) iadrincnfln((ia),(y),(x),(n),(t),FLN)

extern int iadrincnfln(iadrbase *ia,ub4 y,ub4 x,ub4 n,ub4 t,ub4 fln);

#define iadrcnt(ia,y,x) iadrcntfln(FLN,(ia),(y),(x))

extern ub2 iadrcntfln(iadrbase *ia,ub4 y,ub4 x,ub4 fln);

#define rdiadr2(ia,y,x) rdiadr2fln(FLN,(ia),(y),(x))
#define rdiadr4(ia,y,x) rdiadr4fln(FLN,(ia),(y),(x))
#define rdiadr8(ia,y,x) rdiadr8fln(FLN,(ia),(y),(x))

#define wriadr2(ia,y,x,v) wriadr2fln(FLN,(ia),(y),(x),(v))
#define wriadr4(ia,y,x,v) wriadr4fln(FLN,(ia),(y),(x),(v))
#define wriadr8(ia,y,x,v) wriadr8fln(FLN,(ia),(y),(x),(v))
extern int wriadr2fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x,ub2 val);
extern int wriadr4fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x,ub4 val);
extern int wriadr8fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x,ub8 val);

extern ub2 rdiadr2fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x);
extern ub8 rdiadr8fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x);
extern ub4 rdiadr4fln(ub4 fln,iadrbase *ia,ub4 y,ub4 x);

#define rmiadr(ia) rmiadrfln(FLN,(ia))
extern void rmiadrfln(ub4 fln,iadrbase *ia);
extern void acciadr(iadrbase *ia);

extern void iniiadr(void);

#ifdef __clang__
 #pragma clang diagnostic pop
#endif
