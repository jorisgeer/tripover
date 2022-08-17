// osmprep.c - prepare openstreetmap data

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015-2016 Joris van der Geer.
 */

/*
  Superficial parsing and tidyup of osm feeds as first pass.

  input is uncompressed .o5m as produced by osmconvert : wiki.openstreetmap.org/wiki/Osmconvert

  output is a binary, uncompressed list of
  - nodes
  - ways
  - waynodes
  - cum distances
  prefixed with a header

 */

#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#include "base.h"
struct globs globs;

#include "os.h"
#include "mem.h"
#include "util.h"
#include "time.h"

static ub4 msgfile;
#include "msg.h"
ub4 msgfile_h;

#include "math.h"

#include "osmprep.h"
#include "osmnet.h"

// defaults for commandline options

static bool strict;

static bool testonly;

static bool cntonly;

static const char osmname[] = "osmnet.bin";

static ub4 hashdepth = 10;

enum runtos { Run_time,Run_route,Run_trip,Run_stop,Run_all };
static ub4 runto = Run_all;

static bool verbose;

// defaults for config items
static ub4 nodemax = 32U * 1024 * 1024;   // max #nodes
static ub4 waymax = 2U * 1024 * 1024;    // max #ways
static ub4 relmax = 256U * 1024;    // max #relations

static ub4 nidmax = 3800U * 1024 * 1024;  // highest node ID
static ub4 widmax = 380U * 1024 * 1024;   // highest way ID

static ub4 nlstmax;
static ub4 nodecnt,waycnt,relcnt,nlstlen;


static struct node *nodes;
static struct way *ways;
static ub4 *nrid2nid,*wid2way;
static ub4 *nid2nrid;
static ub4 *nodelst,*nodeway;

static ub4 geoscale = 1000 * 1000 * 10;

static ub4 msgrep[8192];
#define Msgrep (msgrep[min(__LINE__,8191)]++ < 100)

static int init0(char *progname)
{
  char mtimestr[64];
  char *p;

  globs.msglvl = Info;
  globs.msgslvl = 0;
  globs.tidcnt = 1;

  setmsglvl(globs.msglvl,globs.msgslvl,0);

  info(V0,"verbosity %u.%u",globs.msglvl,globs.msgslvl);

  setsigs();

  p = strrchr(progname,'/');
  globs.progname = (p ? p + 1 : progname);

  setmsglvl(Info,0,0);
  if (inimsg(progname,"osmprep",Msg_stamp|Msg_pos|Msg_type|Msg_bcklog)) return 1;
  msgfile = setmsgfile(__FILE__);
  iniassert();

#ifdef NOW
  sec70toyymmdd(NOW,10,mtimestr,sizeof(mtimestr));
#else
  strcopy(mtimestr,__DATE__);
#endif

  info(User,"osmprep %u.%u %s %s\n", Version_maj,Version_min,Version_phase,mtimestr);

  if (iniutil(0)) return 1;
  inimem();
  initime(0);
  inimath();
  inios();
  globs.maxvm = 12;
  initime(1);

  return 0;
}

extern const char *runlvlnames(enum Runlvl lvl);
const char *runlvlnames(enum Runlvl lvl) { return lvl ? "n/a" : "N/A"; }

static int streq(const char *s,const char *q) { return !strcmp(s,q); }

static int memeq(const ub1 *s,const char *q,ub4 n) { return !memcmp(s,q,n); }

enum extresult { Next, Newitem, Newcmd, Exteof, Parserr };

static enum extresult __attribute__ ((format (printf,5,6))) parserr(ub4 fln,const char *fname,ub4 linno,ub4 colno,const char *fmt, ...)
{
  va_list ap;
  char buf[1024];
  ub4 pos,len = sizeof(buf);

  pos = fmtstring(buf,"%s.%u.%u: parse error: ",fname,linno,colno);
  if (fmt) {
    va_start(ap,fmt);
    myvsnprintf(buf,pos,len,fmt,ap);
    va_end(ap);
  }
  errorfln(fln,0,FLN,"%s",buf);
  return Parserr;
}

static int __attribute__ ((format (printf,5,6))) parsewarn(ub4 fln,const char *fname,ub4 linno,ub4 colno,const char *fmt, ...)
{
  va_list ap;
  char buf[1024];
  ub4 pos,len = sizeof(buf);

  pos = fmtstring(buf,"%s.%u.%u: ",fname,linno,colno);
  if (fmt) {
    va_start(ap,fmt);
    myvsnprintf(buf,pos,len,fmt,ap);
    va_end(ap);
  }
  return warnfln(fln,Iter,"%s",buf);
}

/* parse comma-separated file, e.g. gtfs.
   first line has colunm names, rest are values
   values can be quoted and if so can contain commas
   quote within quoted strings are doubled
 */

#define Valcnt 64
#define Collen 256

enum extstates {Init,Val0,Val1,Val2,Cmd0,Cmd1,Cmd2,Cfls,Fls};

struct extfmt {
  struct myfile mf;
  ub8 pos;
  enum extstates state;
  ub4 linno,colno;
  ub4 valndx,valcnt;
  ub4 ivals[Valcnt];
  ub4 vallens[Valcnt];
  ub4 uvals[Valcnt];
  ub4 valtypes[Valcnt];
  char vals[Valcnt * Collen];
};

static enum extresult nextchar(struct extfmt *ef)
{
  char *fname;
  ub1 c;
  ub8 pos,len;
  ub4 linno,colno,valndx,valno;
  char *val,*vals;
  ub4 *vallens,vallen;
  ub4 uval;
  int newitem,iscmd;

  enum extstates state;

  len = ef->mf.len;
  pos = ef->pos;
  if (pos >= len) return Exteof;

  // state
  state = ef->state;
  valndx = ef->valndx;
  linno = ef->linno + 1;
  colno = ef->colno;

  // convenience
  fname = ef->mf.name;
  vals = ef->vals;
  vallens = ef->vallens;
  ub4 *uvals = ef->uvals;

  c = ef->mf.buf[pos];
  ef->pos = pos + 1;

  newitem = iscmd = 0;
  uval = uvals[valndx];

//    info(0,"state %u c %c",state,c);

    if (c == '\r') return parserr(FLN,fname,linno,colno,"unexpected char %x",c);

    switch(state) {

    case Init:
      if (c == 0xef) { // utf8 can have byte order mark
        if (len < 3 || (ub1)ef->mf.buf[pos+1] != 0xbb || (ub1)ef->mf.buf[pos+2] != 0xbf) {
          return parserr(FLN,fname,linno,colno,"headline has unexpected char 0x%x %x %x",c,ef->mf.buf[pos+1],ef->mf.buf[pos+2]);
        }
        pos += 3;
        ef->pos = pos + 1;
        c = ef->mf.buf[pos];
      }
      linno = 1; __attribute__ ((fallthrough));

    case Cmd0:
      switch (c) {
        case '#': valndx = 0; state = Cfls; break;
        case '\t': return parserr(FLN,fname,linno,colno,"empty column name");
        case '\n': valndx = 0; break;
        default:
          if (c != '_' && !(c >= 'a' && c <= 'z')) return parserr(FLN,fname,linno,colno,"headline has unexpected char '%c'",c);
          valndx = 0;
          val = vals;
          val[0] = c; vallens[0] = 1;
          state = Cmd1;
      }
      break;

    case Cmd1:
      switch (c) {
        case '\t': vrb0(0,"col %u %.*s",valndx,vallens[valndx],vals + valndx * Collen); valndx++; vallens[valndx] = 0; state = Cmd2; break;
        case '\n': newitem = iscmd = 1; state = Val0; break;
        default:
          val = vals + valndx * Collen;
          vallen = vallens[valndx]; val[vallen] = c; vallens[valndx] = vallen + 1;
      }
      break;

    case Cmd2:
      switch (c) {
        case '\t': return parserr(FLN,fname,linno,colno,"empty column name");
        case '\n': newitem = iscmd = 1; state = Val0; break;
        default:
          val = vals + valndx * Collen;
          vallen = vallens[valndx]; val[vallen] = c; vallens[valndx] = vallen + 1;
          state = Cmd1;
      }
      break;

    case Val0:
      valndx = 0; uval = 0;
      switch (c) {
        case '#': state = Fls; break;
        case '\t': vallens[0] = 0; uvals[0] = uval; valndx = 1; vallens[1] = 0; uvals[1] = 0; state = Val1; break;
        case '\n': break;
        default:
          val = vals;
          val[0] = c; vallens[0] = 1;
          if (c >= '0' && c <= '9') uval = c - '0';
          else uval = hi32;
          state = Val1;
      }
      break;

    case Val1:
      switch(c) {
        case '\t': uvals[valndx++] = uval; vallens[valndx] = 0; state = Val2; uvals[valndx] = 0; break;
        case '\n': newitem = 1; state = Val0; break;
        default:
          val = vals + valndx * Collen;
          vallen = vallens[valndx]; val[vallen] = c; vallens[valndx] = vallen + 1;
          if (uval != hi32) {
            if (c >= '0' && c <= '9' && uval < (hi32 / 10)) uval = uval * 10 + (c - '0');
            else if ( (c == 'm' || c == 'M') && uval < 4096) uval <<= 20;
            else if ( (c == 'k' || c == 'K') && uval < 4096 * 1024) uval <<= 10;
            else uval = uvals[valndx] = hi32;
          }
      }
      break;

    case Val2:
      switch (c) {
        case '\t': uvals[valndx++] = uval; vallens[valndx] = 0; uvals[valndx] = 0; break;
        case '\n': newitem = 1; state = Val0; break;
        default:
          val = vals + valndx * Collen;
          val[0] = c; vallens[valndx] = 1;
          if (c >= '0' && c <= '9') uval = c - '0';
          else uval = hi32;
          state = Val1;
      }
      break;

    case Fls: if (c == '\n') state = Val0; break;
    case Cfls: if (c == '\n') state = Cmd0; break;

    } // end switch state

  if (c == '\n') { linno++; colno = 1; }
  else colno++;

  ef->state = state;

  ef->valndx = valndx;
  ef->linno = linno - 1;
  ef->colno = colno;

  uvals[valndx] = uval;

  if (newitem) {
    for (valno = 0; valno <= valndx; valno++) {
      val = vals + valno * Collen;
      vallen = vallens[valno];
      if (vallen == 0) uvals[valno] = hi32;
      val[vallen] = 0;
    }
    ef->valcnt = valndx + 1;
    vallens[valndx+1] = 0;
    return iscmd ? Newcmd : Newitem;
  } else return Next;
}

enum memitem { Item_node,Item_way,Item_rel,Item_count};
static const char *itemnames[Item_count] = { "node","way","rel" };

static struct memcfg {
  ub4 hicnt,hirid;
} memcfgs[Item_count];

enum hashitem { Hsh_names, Hsh_count };

static int rdcfg(const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  int rv;
  ub4 len,linno,colno;
  char *val,*vals,*itemval;
  ub4 itemvlen,*vallens;
  ub4 valcnt,valno;
  ub4 i,n;
  enum memitem item;

  oclear(eft);

  memcfgs[Item_node].hicnt = nodemax;
  memcfgs[Item_way].hicnt = waymax;
  memcfgs[Item_rel].hicnt = relmax;

  memcfgs[Item_node].hirid = nidmax;
  memcfgs[Item_way].hirid = widmax;

  fmtstring(eft.mf.name,"%s/osmprep.cfg",dir);
  fname = eft.mf.name;

  if (osfileinfo(&eft.mf,fname)) return info(0,"optional %s not present or empty",fname);
  len = (ub4)eft.mf.len;
  if (len == 0) return info(0,"optional %s not present or empty",fname);

  rv = readfile(&eft.mf,fname,0,0);
  if (rv) return 1;

  len = (ub4)eft.mf.len;
  if (len == 0) return info(0,"optional %s not present or empty",fname);

  ub4 itempos,cntpos,ridpos;
  itempos=cntpos=ridpos = hi32;

  ub4 cnt,rid;

  ub4 *uvals = eft.uvals;

  do {

    res = nextchar(&eft);
    vals = eft.vals;

    switch(res) {

    case Newcmd:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 2) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"item")) itempos = valno;
        else if (streq(val,"hicnt")) cntpos = valno;
        else if (streq(val,"hirid")) ridpos = valno;
        else return error(0,"unnown column %s",val);
      }
      if (itempos == hi32) return error(0,"%s: missing required column item",fname);
      if (cntpos == hi32) return error(0,"%s: missing required column hicnt",fname);
      if (ridpos == hi32) return error(0,"%s: missing required column hirid",fname);
      break;

    case Newitem:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);

// item
      itemval = vals + itempos * Collen;
      itemvlen = vallens[itempos];

      if (itemvlen == 0) return error(0,"line %u: missing item name",linno);

      i = 0; item = Item_count;
      while (i < Item_count && item == Item_count) {
        n = (ub4)strlen(itemnames[i]);
        if (itemvlen == n && memeq((ub1 *)itemval,itemnames[i],n)) item = i;
        i++;
      }
      if (item == Item_count) {
        parserr(FLN,fname,linno,colno,"unknown item name %s: choose one of:",itemval);
        for (i = 0; i < Item_count; i++) info(0,"  %s",itemnames[i]);
        return 1;
      }

// hicnt
      val = vals + cntpos * Collen;
      cnt = uvals[cntpos];

      if (cnt == hi32) parserr(FLN,fname,linno,colno,"expected integer value for %s, found '%s'",itemval,val);
      else if (cnt < 1024) {
        parsewarn(FLN,fname,linno,colno,"hicnt for %s: %u below 1024",itemval,cnt);
      }
      memcfgs[item].hicnt = cnt;

// hirid
      if (ridpos != hi32) {
        val = vals + ridpos * Collen;
        rid = uvals[ridpos];

        if (rid == hi32) return parserr(FLN,fname,linno,colno,"expected integer value for %s, found '%s'",itemval,val);
        if (rid < 1000) {
          parsewarn(FLN,fname,linno,colno,"hirid for %s: %u below 1000",itemval,rid);
        }
        memcfgs[item].hirid = rid;
      }

      break;

    case Next: break;
    case Exteof: break;
    case Parserr: return 1;
    }

  } while (res < Exteof);  // each input char

  nodemax = memcfgs[Item_node].hicnt;
  waymax = memcfgs[Item_way].hicnt;
  relmax = memcfgs[Item_rel].hicnt;

  nidmax = memcfgs[Item_node].hirid;
  widmax = memcfgs[Item_way].hirid;

  return 0;
}

// read a 64-bit signed Varint
static sb8 varsb8(const ub1 *buf,ub8 *ppos,ub8 len,ub4 cnt,const char *desc)
{
  ub8 pos = *ppos;
  ub8 u,cc;
  ub1 c;
  ub4 shift = 7;

  // info(0,"pos %lu varint sb8 %s",pos,desc);

  error_ge(pos,len);
  c = buf[pos++];
  u = c & 0x7f;

  while ((c & 0x80) && pos < len) {
    error_gt_cc(u,hi64 >> 8,"node %u pos \ah%lu %s",cnt,pos,desc);
    c = buf[pos++];
    cc = c & 0x7f;
    u |= cc << shift;
    // infocc(cnt == 0,0,"u %lx c %lu",u,cc);
    shift += 7;
  }
  *ppos = pos;
  // info(0,"pos %lu x %lu ",pos,u);
  if (u & 1) {
    return -1L - (u >> 1);
  } else return (u >> 1);
}

// read a 32-bit signed Varint
static sb4 varsb4(const ub1 *buf,ub8 *ppos,ub8 len,ub4 cnt,const char *desc)
{
  ub8 pos = *ppos;
  ub4 u,cc;
  ub1 c;
  ub4 shift = 7;

  error_ge(pos,len);
  c = buf[pos++];
  u = c & 0x7f;

  while ((c & 0x80) && pos < len) {
    c = buf[pos++];
    cc = c & 0x7f;
    error_gt_cc((ub8)cc << shift,hi32,"node %u pos \ah%lu %s",cnt,pos,desc);
    u |= cc << shift;
    shift += 7;
  }
  *ppos = pos;
  if (u & 1) {
    return -1 - (u >> 1);
  } else return (u >> 1);
}

// read a 32-bit Varint
static ub4 varub4(const ub1 *buf,ub8 *ppos,ub8 len,ub4 cnt,const char *desc)
{
  ub8 pos = *ppos;
  ub4 u,cc;
  ub1 c;
  ub4 shift = 7;

  error_ge(pos,len);
  c = buf[pos++];
  u = c & 0x7f;

  while ((c & 0x80) && pos < len) {
    c = buf[pos++];
    cc = c & 0x7f;
    error_gt_cc((ub8)cc << shift,hi32,"node %u pos \ah%lu %s",cnt,pos,desc);
    u |= cc << shift;
    shift += 7;
  }
  *ppos = pos;
  return u;
}

#if 0
// read a 64-bit Varint
static ub8 varub8(const ub1 *buf,ub8 *ppos,ub8 len,ub4 cnt,const char *desc)
{
  ub8 pos = *ppos;
  ub8 u,cc;
  ub1 c;
  ub4 shift = 7;

  error_ge(pos,len);
  c = buf[pos++];
  u = c & 0x7f;

  while ((c & 0x80) && pos < len) {
    c = buf[pos++];
    cc = c & 0x7f;
    error_gt_cc(cc,hi64 >> 8,"node %u pos \ah%lu %s",cnt,pos,desc);
    u |= cc << shift;
    shift += 7;
  }
  *ppos = pos;
  return u;
}
#endif

enum Tag { Tag_unknown, Tag_area, Tag_highway, Tag_junction, Tag_access, Tag_name };
enum Waytype {
  Way_none,Way_unknown,
  Way_res,Way_livstr,
  Way_unclass,Way_road,Way_lane,Way_turn,Way_acc,
  Way_prim,Way_sec,Way_ter,Way_primlnk,Way_seclnk,Way_terlnk,
  Way_mot,Way_motlnk,Way_trunk,Way_trunklnk,
  Way_cycle,
  Way_foot,Way_track,Way_path,Way_steps,Way_ped,
  Way_svc,Way_dw,Way_msc,
  Way_elevator,Way_minor,Way_unsurfaced
};

static enum Tag str2tag(ub4 len,const ub1 *s)
{
  switch (len) {
  case 4: if (*s == 'a' && memeq(s+1,"rea",3)) return Tag_area;
    else if (*s == 'n' && memeq(s+1,"ame",3)) return Tag_name;
    else return Tag_unknown;
  case 6: if (*s == 'a' && memeq(s+1,"ccess",5)) return Tag_access; else return Tag_unknown;
  case 7: if (*s == 'h' && memeq(s+1,"ighway",6)) return Tag_highway; else return Tag_unknown;
  case 8: if (*s == 'j' && memeq(s+1,"unction",7)) return Tag_junction; else return Tag_unknown;
  default: return Tag_unknown;
  }
}

static int markway(struct way *w,enum Waytype t,ub4 *pcar,ub4 *pfoot)
{
  ub1 c = 0,f = 0;
  ub2 speed = 50;

  switch (t) {
  case Way_none: return 0;
  case Way_unknown: f = 1; break;
  case Way_res: c = f = 1; break;
  case Way_livstr: c = f = 1; speed = 30; break;
  case Way_unclass: c = f = 1; break;
  case Way_road: c = f = 1; break;
  case Way_lane: c = f = 1; break;
  case Way_turn: c = f = 1; break;
  case Way_acc: c = f = 1; break;
  case Way_prim: c = f = 1; speed = 80; break;
  case Way_sec: c = f = 1; speed = 70; break;
  case Way_ter: c = f = 1; speed = 60; break;
  case Way_primlnk: c = f = 1; speed = 70; break;
  case Way_seclnk: c = f = 1; speed = 60; break;
  case Way_terlnk: c = f = 1; speed = 50; break;
  case Way_mot: c = 1; speed = 100; break;
  case Way_motlnk: c = 1; speed = 90; break;
  case Way_trunk: c = f = 1; speed = 90; break;
  case Way_trunklnk: c = f = 1; speed = 90; break;
  case Way_cycle: f = 1; break;
  case Way_foot: f = 1; break;
  case Way_track: f = 1; break;
  case Way_path: f = 1; break;
  case Way_steps: f = 1; break;
  case Way_ped: f = 1; break;
  case Way_svc: return 0;
  case Way_dw: f = 1; break;
  case Way_msc: return 0;
  case Way_elevator: f = 1; break;
  case Way_minor: f = c = 1; speed = 60; break;
  case Way_unsurfaced: f = c = 1; speed = 40; break;
  }
  w->car = c;
  w->foot = f;
  if (c) (*pcar)++;
  if (f) (*pfoot)++;
  w->speed = speed;
  return 1;
}

static enum Waytype str2way(ub4 len,const ub1 *s)
{
  ub1 c = *s;
  const ub1 *p = s + 1;

  switch(len) {
  case 2: if (c == 'n' && s[1] == 'o') return Way_none;
    else return Way_unknown;
  case 3: if (c == 'y' && memeq(p,"es",2)) return Way_road;
    else return Way_unknown;
  case 4: if (c == 'p' && memeq(p,"ath",3)) return Way_path;
    else if (c == 'r' && memeq(p,"oad",3)) return Way_road;
    else if (c == 'l' && memeq(p,"ane",3)) return Way_lane;
    else return Way_unknown;
  case 5: if (c == 't') {
      if (memeq(p,"runk",4)) return Way_trunk;
      else if (memeq(p,"rack",4)) return Way_track;
      else if (memeq(p,"rail",4)) return Way_track;
      else return Way_unknown;
    } else if (c == 's' && memeq(p,"teps",4)) return Way_steps;
    else if (c == 'a' && memeq(p,"lley",4)) return Way_road;
    else if (c == 'm' && memeq(p,"inor",4)) return Way_minor;
    else return Way_unknown;
  case 6: if (c == 'e' && memeq(p,"scape",5)) return Way_msc;
    else if (c == 'a' && memeq(p,"ccess",5)) return Way_acc;
    else return Way_unknown;
  case 7: if (c == 'p') {
      if (memeq(p,"rimary",6)) return Way_prim;
      else if (memeq(p,"lanned",6)) return Way_msc;
      else return Way_unknown;
    } else if (*s == 'f' && memeq(p,"ootway",6)) return Way_foot;
    else if (c == 'd' && memeq(p,"isused",6)) return Way_ped;
    else if (c == 's' && memeq(p,"ervice",6)) return Way_svc;
    else if (c == 'r' && memeq(p,"aceway",6)) return Way_msc;
    else return Way_unknown;
  case 8: if (c == 't' && memeq(p,"ertiary",7)) return Way_ter;
    else if (c == 'b' && memeq(p,"us_stop",7)) return Way_msc;
    else if (c == 'm' && memeq(p,"otorway",7)) return Way_mot;
    else if (c == 'e' && memeq(p,"levator",7)) return Way_elevator;
    else if (c == 'c') {
      if (memeq(p,"ycleway",7)) return Way_cycle;
      else if (memeq(p,"orridor",7)) return Way_road;
      else return Way_unknown;
    } else if (c == 's' && memeq(p,"ervices",7)) return Way_svc;
    else if (c == 'd') {
      if (memeq(p,"isuseds",7)) return Way_ped;
      else if (memeq(p,"riveway",7)) return Way_dw;
      else if (memeq(p,"eclared",7)) return Way_msc;
      else return Way_unknown;
    } else if (c == 'p') {
      if (memeq(p,"roposed",7)) return Way_msc;
      if (memeq(p,"latform",7)) return Way_ped;
      else return Way_unknown;
    } else return Way_unknown;
  case 9: if (c == 's' && memeq(p,"econdary",8)) return Way_sec;
    else if (c == 'b' && memeq(p,"ridleway",8)) return Way_msc;
    else if (c == 'r' && memeq(p,"est_area",8)) return Way_msc;
    else if (c == 'a' && memeq(p,"bandoned",8)) return Way_ped;
    else return Way_unknown;
  case 10: if (c == 'p') {
      if(memeq(p,"edestrian",9)) return Way_ped;
      else if (memeq(p,"ath;track",9)) return Way_track;
      else return Way_unknown;
    } else if (c == 't' && memeq(p,"runk_link",9)) return Way_trunklnk;
      else if (c == 'u' && memeq(p,"nsurfaced",9)) return Way_unsurfaced;
    else return Way_unknown;
  case 11: if (c == 'r' && memeq(p,"esidential",10)) return Way_res;
    else return Way_unknown;
  case 12: if (c == 'u' && memeq(p,"nclassified",11)) return Way_unclass;
    else if (c == 'p' && memeq(p,"rimary_link",11)) return Way_primlnk;
    else if (c == 'c' && memeq(p,"onstruction",11)) return Way_msc;
    else if (c == 'b' && memeq(p,"us_guideway",11)) return Way_msc;
    else return Way_unknown;
  case 13: if (c == 'm' && memeq(p,"otorway_link",12)) return Way_motlnk;
    else if (c == 't' && memeq(p,"ertiary_link",12)) return Way_terlnk;
    else if (c == 'l' && memeq(p,"iving_street",12)) return Way_livstr;
    else return Way_unknown;
  case 14: if (c == 's' && memeq(p,"econdary_link",13)) return Way_seclnk;
    else if (c == 't' && memeq(p,"urning_circle",13)) return Way_turn;
    else if (c == 'u' && memeq(p,"nmarked_route",13)) return Way_road;
    else return Way_unknown;
  case 16: if (c == 'r' && memeq(p,"esidential_link",15)) return Way_res; break;
  case 17: if (c == 'u' && memeq(p,"nclassified;road",16)) return Way_road;
    else return Way_unknown;
  case 18: if (memeq(p,"rack;unclassified",17)) return Way_track;
    else return Way_unknown;
  case 19: if (c == 'r' && memeq(p,"esidential;service",10)) return Way_dw;
    else return Way_unknown;

  default: return Way_unknown;
  }
  return Way_unknown;
}

#define Refstrcnt 16384
static ub4 refklens[Refstrcnt];
static ub4 refvlens[Refstrcnt];
static enum Tag reftags[Refstrcnt];

static ub1 *refstrs;

static ub4 refpos;

static int rdosm(const char *name)
{
  enum states { Out,Node0,Node1,Node2,Node3,Way0,Way1,Way2,Way3,Rel0,Rel1,Rel2,Rel3,Rel4,Hdr0,Hdr1,Hdr2,Stamp0,Stamp1,Stamp2,Box0,Box1,Box2,Eof} state;
  struct myfile mf;
  ub8 pos,len,epos,erpos;
  ub4 dlen;
  ub1 c,*buf;
  // ub4 stamp;
  sb8 drid,nrid,rid,prvnrid = 0,prvwrid = 0;
  sb4 lat,lon,prvlat = 0,prvlon = 0;
  double flat,flon,pi180 = M_PI / 180;
  sb4 dlat,dlon;
  struct node *np;
  struct way *wp;
  ub4 nid;
  ub4 nilnodecnt = 0;
  ub4 nilwaycnt = 0,ntwaycnt = 0,nowaycnt = 0,carwaycnt = 0,footwaycnt = 0,areawaycnt = 0;
  ub4 jctcnt = 0;

  ub4 klen,vlen,kvlen;
  ub4 ref,refrpos;
  ub8 kpos,vpos;
  ub1 *refp;
  const ub1 *vp;
  enum Tag tag;
  enum Waytype waytype;

  ub4 nref,nreflen;
  ub4 namlen;

  ub4 nlstofs = 0;

  sb8 hinrid = 0,hiwrid = 0;
  sb8 lonrid = hi32,lowrid = hi32;

  int keepway = 0;
  int dbg1 = 0;
  ub4 nodedbg = 0;
  ub4 waydbg = 0;
  struct eta eta;

  info(0,"reading %s",name);
  if (readfile(&mf,name,1,0)) return 1;

  len = mf.len;
  if (len < 2) return error(0,"%s is empty",name);

  ub4 xpos = 1;
  pos = 0;
  buf = (ub1 *)mf.buf;
  dlen = 0;

  state = Out;

  do {
    if (--xpos == 0) {
      if (progress(&eta,"\ah%lu of \ah%lu  nodes \ah%u ways \ah%u",pos,len,nodecnt,waycnt)) return 1;
      xpos = 0xffff;
    }
    c = buf[pos];

    switch (state) {
    case Out:
      switch (c) {
      case 0x10: infocc(dbg1,Noiter,"%03lu node",pos); state = Node0; break;
      case 0x11: infocc(dbg1,Noiter,"%03lu way",pos); state = Way0; break;
      case 0x12: infocc(dbg1,Noiter,"%03lu rel",pos); state = Rel0; break;
      case 0xdb: info(0,"%03lu bbox",pos); state = Box0; break;
      case 0xdc: info(0,"%03lu timestamp",pos); state = Stamp0; break;
      case 0xe0: info(0,"%03lu header",pos); state = Hdr0; break;
      case 0xfe: info(0,"%03lu eof",pos); state = Eof; break;

      case 0xff: info(0,"%03lu reset",pos);
      prvnrid = prvwrid = 0; prvlat = prvlon = 0;
      break;

      default: return error(0,"%03lu unknown type %02x at node %u way %u",pos,c,nodecnt,waycnt);
      }
      pos++;

      break;

    case Eof: pos = len; break;

    case Hdr0: pos++; if (c == 0) state = Out; else { dlen = c & 0x7f; state = (c & 0x80) ? Hdr1 : Hdr2; } break;
    case Hdr1: pos++; dlen |= (c & 0x7f) << 7; error_ge(c,0x80); break;
    case Hdr2: pos += dlen; info(0,"skip %u-byte hdr",dlen); state = Out; break;

    case Node0: pos++; if (c == 0) state = Out; else { dlen = c & 0x7f; state = (c & 0x80) ? Node1 : Node3; } break;
    case Node1: pos++; dlen |= (c & 0x7f) << 7; state = (c & 0x80) ? Node2 : Node3; break;
    case Node2: pos++; dlen |= (c & 0x7f) << 14; info(Exit,"len %u",dlen); error_ge(c,0x80); break;
    case Node3: state = Out;
      infocc(dbg1,0,"node %u: %u bytes",nodecnt,dlen);
      error_z(dlen,pos);
      epos = pos + dlen;
      error_gt(epos,len,0);

      // id
      drid = varsb8(buf,&pos,len,nodecnt,"node.id");
      rid = prvnrid + drid;
      prvnrid = rid;
      if (pos >= epos) { nilnodecnt++; break; }

      hinrid = max(hinrid,rid);
      lonrid = min(lonrid,rid);
      if (cntonly) {
        nodecnt++;
        pos = epos;
        break;
      } else if (nodecnt + 1 >= nodemax) return error(0,"exceeding max nodes \ah%u defined in osmprep.cfg",nodecnt);

      error_gt(rid,nidmax,0);

      if (rid >= 0) {
        error_nz(nrid2nid[rid],(ub4)rid);
        nrid2nid[rid] = nodecnt;
        nid2nrid[nodecnt] = (ub4)rid;
        // info(Iter,"r.nid %ld.%u",rid,nodecnt);
      }

      // version, stamp, author
      c = buf[pos++];
      if (c) return error0(0,"version not supported");

      // lon
      if (pos >= epos) { nilnodecnt++; break; }
      dlon = varsb4(buf,&pos,len,nodecnt,"node.lon");
      lon = prvlon + dlon;
      prvlon = lon;
      if (lon >= 180 * (sb4)geoscale) lon = 180 * geoscale - 10;
      if (lon <= -180 * (sb4)geoscale) lon = -180 * geoscale + 10;

      // lat
      if (pos >= epos) { nilnodecnt++; break; }
      dlat = varsb4(buf,&pos,len,nodecnt,"node.lat");
      lat = prvlat + dlat;
      prvlat = lat;
      if (lat >= 90 * (sb4)geoscale) lat = 90 * geoscale - 10;
      if (lat <= -90 * (sb4)geoscale) lat = -90 * geoscale + 10;

      np = nodes + nodecnt;
      np->ilat = lat;
      np->ilon = lon;
      flat = (double)lat / geoscale;
      flon = (double)lon / geoscale;
      if (flat > 90) return error(0,"node %u: lat %f from %u",nodecnt,flat,lat);
      if (flat < -90) return error(0,"node %u: lat %f from %u",nodecnt,flat,lat);
      if (flon > 180) return error(0,"node %u: lon %f from %u",nodecnt,flon,lon);
      if (flon < -180) return error(0,"node %u: lon %f from %u",nodecnt,flon,lon);
      np->rlat = flat * pi180;
      np->rlon = flon * pi180;
      infocc(nodecnt < nodedbg,Noiter,"node %u: rid %ld lat %f lon %f",nodecnt,(long)rid,flat,flon);

      if (rid >= 0) nodecnt++;
      if (pos >= epos) break;

      // tags
      while (pos < epos) {
        ref = varub4(buf,&pos,len,nodecnt,"node.tag");
        if (ref) { // indexed
          error_ge(ref,Refstrcnt);
          if (ref > refpos) refrpos = Refstrcnt - (ref - refpos);
          else refrpos = refpos - ref;
          klen = refklens[refrpos];
          vlen = refvlens[refrpos];
          refp = refstrs + refrpos * 256;
          infocc(nodecnt < nodedbg,0,"ref %u=%u pair %u:'%.*s' / %u:'%.*s'",ref,refrpos,klen,klen,refp,vlen,vlen,refp + klen + 1);
        } else { // store
          kpos = pos;
          while(buf[pos] && pos < epos) pos++;
          klen = (ub4)(pos - kpos);
          error_ge(klen,65535);
          vpos = ++pos;
          while(buf[pos] && pos < epos) pos++;
          vlen = (ub4)(pos - vpos);
          error_ge(vlen,65535);
          pos++;
          infocc(nodecnt < nodedbg,0,"new %u pair %u:'%.*s' / %u:'%.*s'",refpos,klen,klen,buf + kpos,vlen,vlen,buf + vpos);
          kvlen = klen + vlen;
          if (kvlen > 250) continue;
          error_ge(refpos,Refstrcnt);
          refp = refstrs + refpos * 256;
          refklens[refpos] = klen;
          refvlens[refpos] = vlen;
          memcpy(refp,buf + kpos,kvlen + 2);
          if (refpos == Refstrcnt - 1) refpos = 0;
          else refpos++;
        }
      }
      break;

    case Way0: pos++; if (c == 0) state = Out; else { dlen = c & 0x7f; state = (c & 0x80) ? Way1 : Way3; } break;
    case Way1: pos++; dlen |= (c & 0x7f) << 7; state = (c & 0x80) ? Way2 : Way3; break;
    case Way2: pos++; dlen |= (c & 0x7f) << 14; error_ge(c,0x80); break;
    case Way3: state = Out;
      infocc(dbg1,0,"way %u: %u bytes",waycnt,dlen);
      error_z(dlen,pos);
      epos = pos + dlen;
      error_gt(epos,len,0);
      keepway = 0;

      // id
      drid = varsb8(buf,&pos,len,waycnt,"way.id");
      rid = prvwrid + drid;
      prvwrid = rid;
      if (pos >= epos) { nilwaycnt++; break; }

      hiwrid = max(hiwrid,rid);
      lowrid = min(lowrid,rid);
      if (cntonly) {
        waycnt++;
        pos = epos;
        break;
      } else if (waycnt + 1 >= waymax) return error(0,"exceeding max ways \ah%u defined in osmprep.cfg",waycnt);

      error_gt(rid,widmax,0);

      if (rid >= 0) {
        error_nz(wid2way[rid],(ub4)rid);
        wid2way[rid] = waycnt;
      }

      // version, stamp, author
      c = buf[pos++];
      if (c) return error0(0,"version not supported");

      nreflen = varub4(buf,&pos,len,waycnt,"way.reflen");
      if (nreflen == 0) { nilwaycnt++; pos = epos; break; }

      infocc(dbg1 || waycnt < 5,0,"way %u id %ld len %u",waycnt,rid,nreflen);

      erpos = pos + nreflen;
      error_gt(erpos,epos,waycnt);
      nref = 0;
      while (pos < erpos) {
        drid = varsb8(buf,&pos,len,waycnt,"way.nodes");
        // infocc(Msgrep,0,"drid %lx %ld",drid,drid);
        nrid = prvnrid + drid;
        error_gt_cc(nrid,nidmax,"ref %u rid %ld nrid %lx + %lx = %lx",nref,rid,drid,prvnrid,nrid);
        prvnrid = nrid;
        nid = nrid2nid[nrid];
        // error_z(nid,nrid);
        error_ge(nref+1+nlstofs,nlstmax);
        error_ovf(nref,ub2);
        nodelst[nlstofs + nref] = nid;
        nodeway[nlstofs + nref] = waycnt;
        if (nlstofs + nref == 48) {
          info(0,"r.nid %lu.%u wid %u nref %u",nrid,nid,waycnt,nref);
        }
        nref++;
        infocc(dbg1 || waycnt < 5,0,"  r.nid %lu %u",nrid,nid);
      }
      // info(Iter,"wid %u nref %u at %u",waycnt,nref,nlstofs);

      wp = ways + waycnt;
      wp->nofs = nlstofs;
      wp->nodecnt = (ub2)nref;
      // wp->closed = (nodelst[0] == nodelst[nref - 1]);
      wp->access = 1;

      if (pos >= epos) { ntwaycnt++; break; }

      // tags
      while (pos < epos) {
        ref = varub4(buf,&pos,len,waycnt,"node.tag");
        if (ref) { // indexed
          error_ge(ref,Refstrcnt);
          if (ref > refpos) refrpos = Refstrcnt - (ref - refpos);
          else refrpos = refpos - ref;
          klen = refklens[refrpos];
          vlen = refvlens[refrpos];
          tag = reftags[refrpos];
          refp = refstrs + refrpos * 256;
          vp = refp + klen + 1;
          infocc(waycnt < waydbg,0,"ref %u=%u pair %u:'%.*s' / %u:'%.*s'",ref,refrpos,klen,klen,refp,vlen,vlen,refp + klen + 1);
        } else { // store
          kpos = pos;
          while(buf[pos] && pos < epos) pos++;
          klen = (ub4)(pos - kpos);
          error_ge(klen,65535);
          vpos = ++pos;
          while(buf[pos] && pos < epos) pos++;
          vlen = (ub4)(pos - vpos);
          error_ge(vlen,65535);
          pos++;
          infocc(waycnt < waydbg,0,"new %u pair %u:'%.*s' / %u:'%.*s'",refpos,klen,klen,buf + kpos,vlen,vlen,buf + vpos);
          tag = str2tag(klen,buf + kpos);
          kvlen = klen + vlen;
          vp = buf + vpos;
          if (kvlen <= 250) {
            error_ge(refpos,Refstrcnt);
            refp = refstrs + refpos * 256;
            refklens[refpos] = klen;
            refvlens[refpos] = vlen;
            reftags[refpos] = tag;
            memcpy(refp,buf + kpos,kvlen + 2);
            if (refpos == Refstrcnt - 1) refpos = 0;
            else refpos++;
          }
        }
        switch(tag) {
        case Tag_name:
          namlen = min(vlen,sizeof(wp->name)-1);
          memcpy(wp->name,vp,namlen);
          break;
        case Tag_highway:
          waytype = str2way(vlen,vp);
          infocc(waytype == Way_unknown,0,"highway %s",vp);
          if (wp->closed == 0 && nref > 1 && markway(wp,waytype,&carwaycnt,&footwaycnt)) keepway = 1;
          break;
        case Tag_junction:
          if (strcmp((const char *)vp,"roundabout")) info(0,"junction %s",vp);
          if (nref > 1) {
            keepway = 1;
            jctcnt++;
          }
          break;
        case Tag_area:
          info(V0,"area %s",vp);
          wp->area = 1;
          areawaycnt++;
          break;
        case Tag_access:
          if (streq((const char *)vp,"private")) wp->access = 0;
          break;
        case Tag_unknown: break;
        }
      }
      if (keepway && wp->access) {
        if (wp->speed == 0) wp->speed = 40;
        error_z(wp->speed,waycnt);
        nlstofs += nref;
        waycnt++;
        if (wp->car == 0 && wp->foot == 0) wp->car = wp->foot = 1;
      } else nowaycnt++;

      // infocc(*wp->name,0,"way %u name %s",waycnt,wp->name);
      break;

    case Rel0: pos++; if (c == 0) state = Out; else { dlen = c & 0x7f; state = (c & 0x80) ? Rel1 : Rel4; } break;
    case Rel1: pos++; dlen |= (c & 0x7f) << 7; state = (c & 0x80) ? Rel2 : Rel4; break;
    case Rel2: pos++; dlen |= (c & 0x7f) << 14; state = (c & 0x80) ? Rel3 : Rel4; break;
    case Rel3: pos++; dlen |= (c & 0x7f) << 21; error_ge(c,0x80); state = Rel4; break;
    case Rel4: pos += dlen;
      infocc(relcnt < 10,Noiter,"rel %u: %u bytes",relcnt,dlen);
      relcnt++;
      state = Out; break;

    case Stamp0: pos++; if (c == 0) state = Out; else { dlen = c & 0x7f; state = (c & 0x80) ? Stamp1 : Stamp2; } break;
    case Stamp1: pos++; dlen |= (c & 0x7f) << 7; error_ge(c,0x80); break;
    case Stamp2: pos += dlen; info(0,"skip %u-byte stamp",dlen); state = Out; break;

    case Box0: pos++; if (c == 0) state = Out; else { dlen = c & 0x7f; state = (c & 0x80) ? Box1 : Box2; } break;
    case Box1: pos++; dlen |= (c & 0x7f) << 7; error_ge(c,0x80); break;
    case Box2: pos += dlen; info(0,"skip %u-byte box",dlen); state = Out; break;

    }

  } while (pos < len && globs.sigint == 0);

  nlstlen = nlstofs;

  info(CC0,"\ah%u empty nodes",nilnodecnt);
  info(CC0,"\ah%u empty ways",nilwaycnt);

  info(0,"\ah%u nodes, id \ah%ld-\ah%ld",nodecnt,lonrid,hinrid);
  info(0,"\ah%u+\ah%u+\ah%u+\ah%u ways, id \ah%ld-\ah%ld",waycnt,nowaycnt,ntwaycnt,areawaycnt,lowrid,hiwrid);

  if (cntonly == 0) {
    info(0,"  \ah%u car ways, \ah%u foot ways",carwaycnt,footwaycnt);
    info(0,"  \ah%u way nodes",nlstlen);
    info(CC0,"  \ah%u junctions",jctcnt);
  }

  info(0,"\ah%u rels",relcnt);

  freefile(&mf);

  afree(nrid2nid,"node");
  nrid2nid = NULL;

  return 0;
}

static int mkjoins(const char *outdir)
{
  struct node *np,*prvnp;
  struct way *wp;
  ub4 nid,wid,wnid,tnid;
  ub4 rnid;
  ub4 n,nofs;
  ub4 cnt,c,sumcnt = 0;
  double fdist;
  ub4 dist,cdist;
static ub4 joinstat[65536];
  char osmfile[256];
  struct eta eta;

  error_z(nodecnt,waycnt);
  error_z(waycnt,nodecnt);

  info(0,"allocating \ah%u nodes",nodecnt);

  ub4 *nid2tnid = alloc(nodecnt,ub4,0xff,"nid",0);
  ub4 tnidcnt = 0;

  info(0,"allocating \ah%u nodelist",nlstlen);
  ub4 *tnidlst = alloc(nlstlen,ub4,0,"nid",0);
  ub4 *tnidgeo = alloc0(nlstlen,ub4,0);

  // get distance between nodes
  for (wid = 0; wid < waycnt; wid++) {
    if (progress(&eta,"distance for way %u of %u  \ah%u nodes",wid,waycnt,sumcnt)) return 1;
    wp = ways + wid;
    cnt = wp->nodecnt;
    if (cnt < 2) continue;
    nofs = wp->nofs;
    nid = nodelst[nofs];
    prvnp = nodes + nid;
    cdist = 0;
    for (n = 1; n < cnt; n++) {
      nid = nodelst[nofs + n];
      np = nodes + nid;
      fdist = geodist(prvnp->rlat,prvnp->rlon,np->rlat,np->rlon,"ways");
      dist = (ub4)(fdist * 10.0 + 0.5);
      infocc(dist > 400 * 1000,0,"wid %u pos %u dist \ag%u \ar%f,\ar%f \ar%f,\ar%f %s",
        wid,n,dist,prvnp->rlat,prvnp->rlon,np->rlat,np->rlon,wp->name);
      cdist += dist;
      infocc(cdist > 800 * 1000,0,"wid %u pos %u dist \ag%u \ag%u",wid,n,dist,cdist);
      tnidgeo[nofs + n] = cdist;
      prvnp = np;
    }
    sumcnt += cnt;
  }

  // resequence into tripover nodes
  info(0,"resequence 1 \ah%u waynodes",nlstlen);
  for (wnid = 0; wnid < nlstlen; wnid++) {
    nid = nodelst[wnid];
    rnid = nid2nrid[nid];
    tnid = nid2tnid[nid];
    if (tnid == hi32) nid2tnid[nid] = tnidcnt++;
    // info(0,"wnid %u r.nid %u.%u tnid %u",wnid,rnid,nid,nid2tnid[nid]);
  }
  info(0,"\ah%u from \ah%u nodes",tnidcnt,nodecnt);

  ub4 *tnid2nid = alloc0(tnidcnt,ub4,0);

  info(0,"resequence 2 \ah%u waynodes",nlstlen);
  for (wnid = 0; wnid < nlstlen; wnid++) {
    nid = nodelst[wnid];
    tnid = nid2tnid[nid];
    if (tnid == 45) {
      wid = nodeway[wnid];
      rnid = nid2nrid[nid];
      infocc(Msgrep,0,"wnid %u r.nid %u.%u tnid %u wid %u",wnid,rnid,nid,tnid,wid);
    }
    error_eq(tnid,hi32);
    tnidlst[wnid] = tnid;
    tnid2nid[tnid] = nid;
  }
  info(0,"\ah%u net nodes",tnidcnt);

  ub2 *joincnts = alloc(tnidcnt,ub2,0,"join cnts",0);
  ub4 *nid2jid = alloc(tnidcnt,ub4,0,"joins",0);
  ub4 joincnt = 0,joinlstlen = 0;

  // count joins
  info(0,"count joins in \ah%u waynodes",nlstlen);
  for (wnid = 0; wnid < nlstlen; wnid++) {
    tnid = tnidlst[wnid];
    cnt = joincnts[tnid];
    if (cnt == hi16) {
      error(0,"wnid %u tnid %u cnt %u",wnid,tnid,cnt);
      continue;
    }
    cnt++;
    joincnts[tnid] = (ub2)cnt;
    joinstat[cnt]++;
  }

  for (wnid = 0; wnid < nlstlen; wnid++) {
    tnid = tnidlst[wnid];
    wid = nodeway[wnid];
    cnt = joincnts[tnid];
    if (cnt < 2) continue;
    wp = ways + wid;
    wp->joined = 1;
  }

  ub4 w,ofs,jid = 0;

  for (tnid = 0; tnid < tnidcnt; tnid++) {
    cnt = joincnts[tnid];
    if (cnt < 2) continue;
    nid2jid[tnid] = jid;
    jid++;
  }
  joincnt = jid;
  info(0,"\ah%u joins",joincnt);

  for (cnt = 2; cnt < 65536; cnt++) {
    c = joinstat[cnt];
    if (c == 0) continue;
    info(0,"%u node\as with %u join\as",c,cnt);
    joinlstlen += c;
  }
  info(0,"join lst %u",joinlstlen);

  ub4 twid = 0,twaycnt;
  ub4 *wid2twid = alloc0(waycnt,ub4,0);

  // resequence ways
  for (wid = 0; wid < waycnt; wid++) {
    wp = ways + wid;
    if (wp->joined == 0) continue;
    wid2twid[wid] = twid++;
  }
  twaycnt = twid;
  info(0,"\ah%u from \ah%u ways",twaycnt,waycnt);

  struct tjoin *jp,*joins = alloc(joincnt,struct tjoin,0,"joins",0);
  ub4 jlstlen = 0;

  info(0,"create joins for \ah%u waynodes",nlstlen);
  for (wnid = 0; wnid < nlstlen; wnid++) {
    tnid = tnidlst[wnid];
    cnt = joincnts[tnid];
    if (cnt < 2) continue;
    jid = nid2jid[tnid];
    wid = nodeway[wnid];
    wp = ways + wid;
    error_z(wp->joined,wid);
    twid = wid2twid[wid];
    jp = joins + jid;
    jp->nid = tnid;
    w = jp->wcnt;
    if (w+2 == TNjoin) {
      jp->wcnt = w + 1;
      error(0,"jid %u waycnt exceeds %u",jid,w);
      continue;
    }
    else if (w+1 >= TNjoin) continue;

    jp->wcnt = w + 1;
    jp->ways[w] = twid;
    // info(Iter,"wnid %u jid %u cnt %u wid %u",wnid,jid,w,wid);
    ofs = wp->nofs;
    error_lt(wnid,ofs);
    if (wnid >= ofs + wp->nodecnt) return error(0,"wid %u wnid %u ofs %u cnt %u",wid,wnid,ofs,wp->nodecnt);
    jp->waypos[w] = (ub2)(wnid - ofs);
  }

  for (jid = 0; jid < joincnt; jid++) {
    jp = joins + jid;
    w = jp->wcnt;
    error_z(w,jid);
    // info(Iter,"jid %u cnt %u",jid,w);
    // infocc(w != 2,Iter,"jid %u cnt %u",jid,w);
    jlstlen += w;
  }
  info(0,"%u join list",jlstlen);

  // convert to file format
  struct tnode *tnodes = alloc(tnidcnt,struct tnode,0,"nid",0);

  for (tnid = 0; tnid < tnidcnt; tnid++) {
    if (progress0(&eta,"resequence node %u of %u",tnid,tnidcnt)) return 1;
    nid = tnid2nid[tnid];
    np = nodes + nid;
    tnodes[tnid].ilat = np->ilat;
    tnodes[tnid].ilon = np->ilon;
  }

  info0(0,"convert ways to tripover format");
  struct tway *twp,*tways = alloc0(waycnt,struct tway,0);
  twid = 0;

  for (wid = 0; wid < waycnt; wid++) {
    wp = ways + wid;
    if (wp->joined == 0) continue;
    twp = tways + twid++;
    twp->ncnt = wp->nodecnt;
    twp->nofs = wp->nofs;
    if (wp->foot) twp->modes |= Twfoot;
    if (wp->car) twp->modes |= Twcar;
    twp->speed = wp->speed;
    memcpy(twp->name,wp->name,min(sizeof(twp->name),sizeof(wp->name)));
  }

  if (testonly) return 0;

  if (outdir && *outdir && strcmp(outdir,".") ) {
    fmtstring(osmfile,"%s/%s",outdir,osmname);
  } else strcopy(osmfile,osmname);

  if (filerotate(osmfile,0,'0')) return 1;

  info(0,"write to %s",osmfile);

  struct osmhdr hdr;
  ub8 len;
  hdr.magic = Omagic1;
  hdr.nodecnt = tnidcnt;
  hdr.waycnt = twaycnt;
  hdr.joincnt = joincnt;
  hdr.nlstlen = nlstlen;

  int fd = filecreate(osmfile,1);
  if (fd == -1) return 1;

  if (filewrite(fd,&hdr,sizeof(hdr),osmfile)) return 1;

  if (filewrite(fd,&Omagic2,sizeof(ub4),osmfile)) return 1;

  // nodes
  len = tnidcnt * sizeof(*tnodes);
  info(0,"write \ah%u nodes len \ah%lu",tnidcnt,len);
  if (filewrite(fd,tnodes,tnidcnt * sizeof(*tnodes),osmfile)) return 1;

  if (filewrite(fd,&Omagic3,sizeof(ub4),osmfile)) return 1;

  // waynodes
  len = nlstlen * sizeof(*tnidlst);
  info(0,"write \ah%u waynodes 1 len \ah%lu",nlstlen,len);
  if (filewrite(fd,tnidlst,len,osmfile)) return 1;

  len = nlstlen * sizeof(*tnidgeo);
  info(0,"write \ah%u waynodes 2 len \ah%lu",nlstlen,len);
  if (filewrite(fd,tnidgeo,len,osmfile)) return 1;

  if (filewrite(fd,&Omagic4,sizeof(ub4),osmfile)) return 1;

  // ways
  len = twaycnt * sizeof(*tways);
  info(0,"write \ah%u ways len \ah%lu",twaycnt,len);
  if (filewrite(fd,tways,len,osmfile)) return 1;

  fileclose(fd,osmfile);

  return 0;
}

static int readosm(const char *file)
{
  info0(0,"allocating structures");

  nodes = alloc(nodemax,struct node,0,"nodes",0);
  nid2nrid = alloc(nodemax,ub4,0,"nodes",0);

  ways = alloc(waymax,struct way,0,"ways",0);

  refstrs = alloc(Refstrcnt * 256,ub1,0,"string refs",Refstrcnt);

  nlstmax = nodemax * 2;
  nodelst = alloc(nlstmax,ub4,0,"node list",nodemax);
  nodeway = alloc(nlstmax,ub4,0,"node ways",nodemax);

  nrid2nid = alloc(nidmax + 1,ub4,0,"node ids",0);
  wid2way = alloc(widmax + 1,ub4,0,"way ids",0);

  nodecnt = 1;

  info(0,"reading osm file from %s",file);

  if (rdosm(file) || globs.sigint) return 1;

  return info0(0,"done reading osm file");
}

static int cmd_test(struct cmdval *cv) {
  testonly = 1;
  info(0,"%s set",cv->subarg);
  return 0;
}

static int cmd_strict(struct cmdval *cv) { strict = 1; return info(0,"%s set",cv->subarg); }

static int cmd_cntonly(struct cmdval *cv) { cntonly = 1; return vrb0(0,"%s set",cv->subarg); }

static int cmd_runto(struct cmdval *cv) {
  const char *s = cv->sval;
  if (streq(s,"time")) runto = Run_time;
  else if (streq(s,"route")) runto = Run_route;
  else if (streq(s,"stop")) runto = Run_stop;
  else if (streq(s,"trip")) runto = Run_trip;
  else return warn(0,"unknown step %s for %s",s,cv->subarg);
  return 0;
}

static int cmd_hash(struct cmdval *cv) {
  hashdepth = max(cv->uval,1);
  hashdepth = min(hashdepth,1024);
  return vrb0(0,"%s set",cv->subarg);
}

static int cmd_vrb(struct cmdval *cv) {
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
  setmsglvl(globs.msglvl,0,globs.limassert);
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
  { "test|t", NULL, "test only, no output", cmd_test },
  { "strict|s", NULL, "strict mode", cmd_strict },
  { "runto", "[step]", "run to given step: time,route,stop,trip,seq", cmd_runto },
  { "countonly|c", NULL, "count only", cmd_cntonly },
  { "hashcap", "[depth]%u", "hash table capacity", cmd_hash },
  { "verbose|v", "[level]%u", "set or increase verbosity", cmd_vrb },
  { "assert-limit", "[limit]%u", "stop at this #assertions", cmd_limassert },
  { NULL, "outdir infile", "osmprep", cmd_arg }
};

int main(int argc, char *argv[])
{
  const char *infile,*outdir;
  struct myfile mf;
  int rv;

  init0(argv[0]);

  if (cmdline(argc,argv,cmdargs,"openstreetmap prep tool")) return 1;

  verbose = (getmsglvl() > Info);

  if (strict) {
  }

  if (globs.argc < 2) return shortusage();
  outdir = globs.args[0];
  infile = globs.args[1];

  oclear(mf);
  if (osfileinfo(&mf,infile)) return oserror(0,"cannot access %s",infile);
  else if (mf.isdir == 1) return error(0,"arg %s is a directory",infile);
  if (setmsglog("osm","osmprep",0,0)) return 1;

  globs.maxvm = 128;

  rv = rdcfg(".");
  if (rv) return 1;

  rv = readosm(infile);
  if (rv || cntonly) return rv;

  if (mkjoins(outdir) || globs.sigint) return 1;

  eximsg(1);

  return globs.sigint;
}
