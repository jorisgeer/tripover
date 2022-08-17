// gtfsprep.c - prepare gtfs feeds

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2016 Joris van der Geer.
 */

/*
  parsing and tidyup of gtfs feeds as first pass.
  input is uncompressed feed
  output is a variant of gtfs : tab-separated, unquoted and in a canonical column order
  only columns tripover uses
  this simplifies and speeds up subsequent processing by gtfstool

  additional processing:
  - filtering on transport mode
  - merge duplicate or nearby stops by inferring common parent

  for manual entry support, a few syntax variations are understood :

- blank lines are allowed and skipped

  stop_times.txt:
  - departure time, if omitted, is equal to arrival time
  - seconds, if omitted, are 0
  - . or no separator at all instead of : as time separator
  - sequence_number  if first after blank line is 1, and rest upto next blank line omitted, auto-increment
    otherwise, if higher than zero, autodecrement
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

#include "iadr.h"
#include "math.h"

#include "gtfsprep.h"

// defaults for commandline options
static ub4 stnlimit = 2;
static double stnlimit_f,stnlimit3;

static double grplinkbelow = 5;

static ub4 grouplimit = 20;
static ub4 iterlimit = 2000;

static bool useparentname = 0;

static const char *fileext = "txt";
static const char inferpat[] = "%08x-%08x-%016lx";

static bool canonin;

static bool do_join = 0;
static bool do_chkdup = 0;
static bool do_ridinfer = 0;
static bool no_grplink = 1;
static bool nounkroute = 1;

static bool mergeduproutes = 0;

static int write_stoptimes = 0;
static int write_stopseqs = 1;

static bool strict;
static bool airmode;

static bool intid;
static bool testonly;
static ub4 dateshift = 0;

static bool noportnet = 0;

static ub4 stamp,lostamp;

static char prefix[64];
static ub4 prefixlen1,prefixlen = 0;

static char netsuffix[64];

static char seqprefix[64];
static ub4 seqpfxlen;

static ub4 hidate = 20000101;
static ub4 lodate = 20201231;
static ub4 orghidate = 20000101;
static ub4 orglodate = 20201231;
static ub4 maxdays = 120;

static double minlat = 90,maxlat = -90,minlon = 180,maxlon = -180;

static ub4 poplimit = hi32;

static ub4 okdates;

static ub4 havestartdate,startdate = 20000101;
static ub4 haveenddate,enddate = 20201231;
static ub4 planstopcnt,userstopcnt;
static ub4 tzmin = 0;

static char mergedir[256];
static bool mergefirst;

static char geonamedb[256];

static ub4 hashdepth = 10;

static ub4 netgrid = 600;

static ub4 sampleratio;

static int nobus,norail,notram,nometro,noferry,noair,notaxi,noany;

static bool show_omitstop = 1;
static bool show_coloc = 1;

static bool fix_plusday = 0;   // warn, but assume +24h if trips jump back in time

static bool patch_tz = 0; // write patch script for tz mismatches

enum runtos { Run_time,Run_route,Run_trip,Run_stop,Run_all };
static ub4 runto = Run_all;

static bool verbose;

static ub4 errcnt;

// lat: 111 km / deg unit -> ~1cm / unit
static ub4 geoscale = 1000 * 1000 * 10;
static const ub4 maxdurday = 10; // longest duration

static const ub4 Hiseq = 4000 * 1000;

static const char geomagic[] = "geo-JBKScycH"; // sync with gtfstool

static ub2 defagencytzlen;
static char defagencytz[64];
static ub4 defaid;

static int init0(char *progname)
{
  char mtimestr[64];
  char *p;

  setsigs();

  p = strrchr(progname,'/');
  globs.progname = (p ? p + 1 : progname);

  setmsglvl(Info,0);
  inimsg(progname,"gtfsprep",Msg_stamp|Msg_pos|Msg_type);
//  inimsg(progname,"gtfsprep",0);
  msgfile = setmsgfile(__FILE__);
  msgfile_h = setmsgfile("msg.h");
  iniassert();

#ifdef NOW
  sec70toyymmdd(NOW,10,mtimestr,sizeof(mtimestr));
#else
  strcopy(mtimestr,__DATE__);
#endif

  info(User,"gtfsprep %u.%u %s %s\n", Version_maj,Version_min,Version_phase,mtimestr);

  if (iniutil(0)) return 1;
  inimem();
  initime(0);
  inimath();
  inios();
  return 0;
}

static int init1(void)
{
  globs.maxvm = 7;
  initime(1);
  iniiadr();
  return 0;
}

extern const char *runlvlnames(enum Runlvl lvl);
const char *runlvlnames(enum Runlvl lvl) { return lvl ? "n/a" : "N/A"; }

static int streq(const char *s,const char *q) { return !strcmp(s,q); }

static int memeq(const char *s,const char *q,ub4 n) { return !memcmp(s,q,n); }

// Bob Jenkin one-at-a-time, from Wikipedia
static ub4 hashcode(const char *str,ub4 slen,ub4 len)
{
  ub4 h = 0, i;

  for (i = 0; i < slen; i++) {
    h += str[i];
    h += (h << 10);
    h ^= (h >> 6);
  }
  h += (h << 3);
  h ^= (h >> 11);
  h += (h << 15);
  return h % len;
}

static hash *mkhash(ub4 fln,ub4 len,ub4 eqlen,ub4 slen,const char *desc)
{
  hash *ht = alloc(1,hash,0,"hash",len);
  ht->len = len;
  ht->eqlen = eqlen;
  ht->desc = desc;
  ht->fln = fln & hi16;

  infocc(len > 1024 * 1024,0,"create \ah%u * %u entry hash table with \ah%u string pool",len,eqlen,slen);

  ub4 bktlen = len * eqlen;
  ub4 spoollen = ht->spoollen = slen;
  ht->bkts = mkblock(&ht->bktmem,bktlen,struct bucket,Init0,"hash %s len %u",desc,len);
  ht->strpool = mkblock(&ht->strmem,spoollen,char,Noinit,"hash %s string pool",desc);
  return ht;
}

#define gethash(ht,str,len,code) gethashfln(FLN,(ht),(str),(len),(code))

static ub4 gethashfln(ub4 fln,hash *ht,const char *str,ub4 slen,ub4 ucode)
{
  error_zp(ht,slen);
  if (slen == 0) errorfln(fln,Exit,FLN,"slen 0 hash %u for %s",ucode,ht->desc);
  ub4 len = ht->len;
  ub4 code;
  ub4 eqlen = ht->eqlen;
  struct bucket *bkt,*bkts = ht->bkts;
  char *spool = ht->strpool;
  ub4 eq = 0;

  if (ucode == hi32 || (ucode && *str == '0')) code = hashcode(str,slen,len);
  else code = ucode % len;
  bkt = bkts + code * eqlen;
  while (bkt->slen && eq++ < eqlen) {
    if (bkt->slen == slen && memcmp(spool + bkt->sofs,str,slen) == 0) {
      return bkt->data;
    }
    bkt++;
  }
  return hi32;
}

#define addhash(ht,str,len,code,data) addhashfln(FLN,(ht),(str),(len),(code),(data))

static ub4 addhashfln(ub4 fln,hash *ht,const char *str,ub4 slen,ub4 ucode,ub4 data)
{
  error_zp(ht,slen);
  ub4 len = ht->len;
  ub4 code;
  ub4 eqlen = ht->eqlen;
  struct bucket *bkt,*bkts = ht->bkts;
  char *spool = ht->strpool;
  ub4 eq = 0;
  ub4 sofs = ht->sofs;
  ub4 cnt = ht->itemcnt;
  ub4 iter = 0;

  if (ucode == hi32 || (ucode && *str == '0')) code = hashcode(str,slen,len);
  else code = ucode % len;

  error_z(slen,data);
  if (sofs + slen >= ht->spoollen) {
    errorfln(FLN,0,fln,"hash table %s.%u spool full for %u, %u of %u.%u items spool \ah%u",ht->desc,ht->fln,slen,cnt,ht->len,ht->eqlen,ht->spoollen);
    return hi32;
  }
  bkt = bkts + code * eqlen;
  while (bkt->slen && eq < eqlen) { bkt++; eq++; iter++; }
  infocc(iter > 100,0,"addhash %.*s took %u iters",slen,str,iter);
  if (eq == eqlen) {
    errorfln(FLN,0,fln,"hash %s.%u entry %u at %u %u for %.*s exceeds %u entry limit",ht->desc,ht->fln,cnt,code,ucode,slen,str,eqlen);
    return hi32;
  }
  error_ge_cc(slen,512,"hash %s s %.128ss",ht->desc,str);
  memcpy(spool + sofs,str,slen);
  bkt->slen = slen;
  bkt->sofs = sofs;
  bkt->data = data;

  ht->sofs = sofs + slen;
  if (eq > ht->maxeq) {
    ht->maxeq = eq;
    infocc(eq > eqlen / 2,0,"hash %s.%u has load %u at %u entries for %s",ht->desc,ht->fln,eq,cnt,str);
  }
  ht->itemcnt = cnt + 1;

  return code * eqlen + eq;
}

enum extresult { Next, Newitem, Newcmd, Eof, Parserr };

// count non-empty lines
static ub4 linecnt(const char *name,const char *buf, ub8 len,ub4 head)
{
  ub8 pos = 0;
  ub4 cnt = 0;
  const char nl = '\n';

  while (pos < len) {
    if (buf[pos] == nl) pos++;
    else {
      cnt++;
      while (pos < len && buf[pos] != nl) pos++;
    }
  }
  if (len && buf[len-1] != nl) {
    warn(0,"%s has unterminated last line",name);
    cnt++;
  }
  if (cnt >= head) cnt -= head;
  info(cnt > hi16 ? 0 : V0,"%s: \ah%u data lines", name,cnt);
  return cnt;
}

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
sassert(Collen < 65536,"collen > ub2");

enum extstates {Init,Val0,Val1,Val1a,Val1f,Val2,Val2q,Val3q,Cmd0,Cmd1,Cmd2,Cfls,Fls};

struct extfmt {
  struct myfile mf;
  ub8 pos;
  enum extstates state;
  ub4 linno,colno;
  int skip0;
  ub4 valndx,valcnt;
  ub4 ivals[Valcnt];
  ub2 vallens[Valcnt];
  ub4 uvals[Valcnt];
  ub4 valtypes[Valcnt];
  char vals[Valcnt * Collen];
  const char *colnames[Valcnt];
};

static enum extresult nextchar_csv(struct extfmt *ef)
{
  char *fname;
  ub1 c;
  ub8 pos,len;
  ub4 linno,colno,valndx,valno;
  ub4 uval;
  char *val,*vals;
  ub2 *vallens,vallen;
  int newitem,iscmd;

  enum extstates state;

  len = ef->mf.len;
  pos = ef->pos;

  if (pos >= len) return Eof;

  // state
  state = ef->state;
  valndx = ef->valndx;
  linno = ef->linno + 1;
  colno = ef->colno;
  error_ge(valndx,Valcnt);

  // convenience
  fname = ef->mf.name;
  vals = ef->vals;
  vallens = ef->vallens;
  ub4 *valtypes = ef->valtypes;
  ub4 *uvals = ef->uvals;
  const char *cname = ef->colnames[valndx];

  c = ef->mf.buf[pos];
  ef->pos = pos + 1;

  newitem = iscmd = 0;
  uval = uvals[valndx];

  warncc(c == 0,0,"state %u zero char",state);
  int neweof = 0;

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
      linno = 1; Fallthrough

    case Cmd0:
      switch (c) {
        case ',': return parserr(FLN,fname,linno,colno,"empty column name");
        case '\n': return parserr(FLN,fname,linno,colno,"unexpected newline");
        case ' ': break; // ignore leading ws
        case '"': break; // simple quote handling
        default:
          if (c != '_' && !(c >= 'a' && c <= 'z')) parserr(FLN,fname,linno,colno,"headline has unexpected char '%c'",c);
          valndx = 0;
          val = vals;
          val[0] = c; vallens[0] = 1;
          state = Cmd1;
      }
      break;

    case Cmd1: // in col header
      switch (c) {
        case '\t': parsewarn(FLN,fname,linno,colno,"assuming tab-separated csv at col %u",valndx); Fallthrough
        case ',':
          if (valndx + 2 > Valcnt) return parserr(FLN,fname,linno,colno,"number of cols exceeds %u",valndx);
          valndx++;
          vallens[valndx] = 0;
          state = Cmd2;
          break;
        case '\r': break;
        case '"': break; // simple quote handling
        case '\n': newitem = iscmd = 1; state = Val0; break;
        default:
          val = vals + valndx * Collen;
          vallen = vallens[valndx];
          if (vallen + 2 > Collen) return parserr(FLN,fname,linno,colno,"col %u exceeds len %u",valndx,vallen);
          val[vallen] = c;
          vallens[valndx] = vallen + 1;
          neweof = 1;
      }
      break;

    case Cmd2:  // start of next col header
      switch (c) {
        case ',':
          parsewarn(FLN,fname,linno,colno,"empty column name");
          if (valndx + 2 > Valcnt) return parserr(FLN,fname,linno,colno,"number of cols exceeds %u",valndx);
          valndx++;
          vallens[valndx] = 0;
          state = Cmd2;
          break;
        case '\r': break;
        case '\n': newitem = iscmd = 1; state = Val0; break;
        case ' ': break;
        case '"': break; // simple quote handling
        default:
          if (valndx + 2 > Valcnt) return parserr(FLN,fname,linno,colno,"number of cols exceeds %u",valndx);
          val = vals + valndx * Collen;
          vallen = vallens[valndx];
          if (vallen + 2 > Collen) return parserr(FLN,fname,linno,colno,"col %u exceeds len %u",valndx,vallen);
          val[vallen] = c; vallens[valndx] = vallen + 1;
          state = Cmd1;
          neweof = 1;
      }
      break;

    case Val0:  // start of first col
      valndx = 0; uval = 0;
      switch (c) {
        case '\t':
        case ',': vallens[0] = 0; uvals[0] = uval; valndx = 1;  vallens[1] = 0; state = Val1; break;
        case '\r': case ' ': break;
        case '\n': vrb0(0,"skipping empty line at %u",linno); break;
        case '"': vallens[0] = 0; state = Val2q; break;
        default:
          val = vals;
          val[0] = c; vallens[0] = 1;
          state = Val1;
          if (c >= '0' && c <= '9') uval = c - '0';
          else uval = hi32;
      }
      break;

    case Val1: // within col
      switch(c) {
//        case '\t':
        case ',':
          if (valndx + 2 > Valcnt) return parserr(FLN,fname,linno,colno,"number of cols exceeds %u",valndx);
          uvals[valndx++] = uval;
          vallens[valndx] = 0;
          state = Val2;
          break;
        case '\r': break;
        case '\n': uvals[valndx] = uval; newitem = 1; state = Val0; break;
        default:
          val = vals + valndx * Collen;
          vallen = vallens[valndx];
          if (vallen + 2 >= Collen) {
            parsewarn(FLN,fname,linno,colno,"truncating col %u %s at %u",valndx,cname,vallen);
            vallen = (ub2)truncutf8(val,vallen);
            vallens[valndx] = vallen;
            state = Val1f;
            break;
          }
          if (c != '\t') { val[vallen] = c; vallens[valndx] = vallen + 1; }
          if (uval != hi32) {
            if (c >= '0' && c <= '9' && uval < (hi32 / 10)) uval = uval * 10 + (c - '0');
            else if (c == ' ' || c == '\t') state = Val1a;
            else uval = hi32;
          }
          neweof = 1;
      }
      break;

    // flush at trunc
    case Val1f:
      switch(c) {
        case ',':
          if (valndx + 2 > Valcnt) return parserr(FLN,fname,linno,colno,"number of cols exceeds %u",valndx);
          uvals[valndx++] = uval;
          vallens[valndx] = 0;
          state = Val2;
          break;
        case '\r': break;
        case '\n': uvals[valndx] = uval; newitem = 1; state = Val0; break;
      }
      break;

    case Val1a:
      switch(c) {
        case '\t': break;
        case ',': uvals[valndx++] = uval; vallens[valndx] = 0; state = Val2; break;
        case '\r': break;
        case '\n': uvals[valndx] = uval; newitem = 1; state = Val0; break;
        default:
          val = vals + valndx * Collen;
          vallen = vallens[valndx];
          if (vallen + 2 > Collen) {
            parsewarn(FLN,fname,linno,colno,"truncating col %u %s at %u",valndx,cname,vallen);
            vallen = (ub2)truncutf8(val,vallen);
            vallens[valndx] = vallen;
            state = Val1a;
            break;
          }
          val[vallen] = c; vallens[valndx] = vallen + 1;
          if (uval != hi32 && c != ' ') uval = hi32;
          neweof = 1;
      }
      break;

    case Val2: // start of subsequent cols
      switch (c) {
        case '\t': break;
        case ',': uvals[valndx++] = uval; vallens[valndx] = 0; break;
        case '\r': case ' ': break;
        case '\n': newitem = 1; state = Val0; break;
        case '"': state = Val2q; uval = 0; break;
        default:
          val = vals + valndx * Collen;
          val[0] = c; vallens[valndx] = 1;
          state = Val1;
          if (c >= '0' && c <= '9') uval = c - '0';
          else if (c != ' ') uval = hi32;
          neweof = 1;
      }
      break;

    case Val2q:
      switch(c) {
        case '"': state = Val3q; break;
        case '\r': break;
        case '\n': return parserr(FLN,fname,linno,colno,"unexpected newline in quoted string");
        case '\t': c = ' '; Fallthrough
        default:
          val = vals + valndx * Collen;
          vallen = vallens[valndx];
          if (vallen + 2 > Collen) {
            parsewarn(FLN,fname,linno,colno,"truncating col %u %s at %u",valndx,cname,vallen);
            vallen = (ub2)truncutf8(val,vallen);
            vallens[valndx] = vallen;
            break;
          }
          val[vallen] = c; vallens[valndx] = vallen + 1;

          if (uval != hi32) {
            if (c >= '0' && c <= '9' && uval < (hi32 / 10)) uval = uval * 10 + (c - '0');
            else uval = hi32;
          }
      }
      break;

    case Val3q:
      switch(c) {
        case '"': // escaped quote
          val = vals + valndx * Collen;
          vallen = vallens[valndx]; val[vallen] = c; vallens[valndx] = vallen + 1;
          uval = hi32;
          state = Val2q;
          break;
        case ',': uvals[valndx++] = uval; vallens[valndx] = 0; state = Val2; break;
        case '\r': break;
        case '\n': newitem = 1; state = Val0; break;
        default:
          val = vals + valndx * Collen;
          vallen = vallens[valndx]; val[vallen] = '"'; val[vallen+1] = c; vallens[valndx] = vallen + 2;
          parsewarn(FLN,fname,linno,colno,"col %u %s unexpected char '%c' after quote",valndx,cname,c);
          state = Val1;
      }
      break;

    case Cfls: case Fls: break;
    } // end switch state

  if (c == '\n') { linno++; colno = 1; }
  else colno++;

  ef->state = state;

  ef->valndx = valndx;
  ef->linno = linno - 1;
  ef->colno = colno;
  uvals[valndx] = uval;

  if (pos >= len && neweof) newitem = 1;

  if (newitem) {
    for (valno = 0; valno <= valndx; valno++) {
      val = vals + valno * Collen;
      vallen = vallens[valno];
      cname = ef->colnames[valno];
      if (vallen == 0) uvals[valno] = hi32;
      while (vallen) {
        c = val[vallen-1];
        if (c == ' ' || c == '\t') vallens[valno] = --vallen; // strip trailing ws
        else break;
      }
      val[vallen] = 0;
      uval = uvals[valno];
      if (uval == hi32 && valtypes[valno]) {
        if (vallen) parsewarn(FLN,fname,linno,colno,"expected numerical value for column %u.%s, found '%s'",valno+1,cname,val);
        else parsewarn(FLN,fname,linno,colno,"expected numerical value for empty column %u.%s",valno+1,cname);
      }
    }
    for (valno = valndx + 1; valno < Valcnt; valno++) vallens[valno] = 0;

    ef->valcnt = valndx + 1;

    return iscmd ? Newcmd : Newitem;
  } else return Next;
}

// similar to above, tab-separated canonical
static enum extresult nextchar_canon(struct extfmt *ef)
{
  char *fname;
  ub1 c;
  ub8 pos,len;
  ub4 linno,colno,valndx,valno;
  char *val,*vals;
  ub2 *vallens,vallen;
  ub4 uval;
  int newitem,iscmd;

  enum extstates state;

  len = ef->mf.len;
  pos = ef->pos;
  if (pos >= len) return Eof;

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

  if (c == 0 && ef->skip0) return Next;

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
      linno = 1; Fallthrough

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
            else if (c == ' ') state = Val1a;
            else uval = uvals[valndx] = hi32;
          }
      }
      break;

    case Val1a:
      switch(c) {
        case '\t': uvals[valndx++] = uval; vallens[valndx] = 0; state = Val2; uvals[valndx] = 0; break;
        case '\n': newitem = 1; state = Val0; break;
        default:
          val = vals + valndx * Collen;
          vallen = vallens[valndx]; val[vallen] = c; vallens[valndx] = vallen + 1;
          if (uval != hi32 && c != ' ') uval = uvals[valndx] = hi32;
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

    case Val2q:
    case Val1f:
    case Val3q: break;

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
    for (valno = valndx + 1; valno < Valcnt; valno++) vallens[valno] = 0;
    ef->valcnt = valndx + 1;

    return iscmd ? Newcmd : Newitem;
  } else return Next;
}

static enum extresult nextchar(struct extfmt *ef)
{
  if (canonin) return nextchar_canon(ef);
  else return nextchar_csv(ef);
}

enum memitem { Item_stop,Item_route,Item_cal,Item_date,Item_trip,Item_time,Item_freq,Item_agency,Item_count};
static const char *itemnames[Item_count] = { "stop","route","cal","caldate","trip","time","freq","agency" };

static struct memcfg {
  ub4 factor,offset,poolfac;
} memcfgs[Item_count];

#define newhash(item,ref,spool) newhashfln(FLN,(item),(ref),(spool))

static hash *newhashfln(ub4 fln,enum memitem item,ub4 reflen,ub4 spoollen)
{
  struct memcfg *mc = memcfgs + item;
  ub4 len = reflen * mc->factor + mc->offset;
  ub4 slen = spoollen * mc->poolfac;
  ub4 eqlen = hashdepth;
  hash *h = mkhash(fln,len,eqlen,slen,itemnames[item]);

  return h;
}

static int rdcfg(const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  int rv;
  ub4 len,vlen,linno,colno;
  char *val,*vals,*itemval;
  ub2 itemvlen,*vallens;
  ub4 valcnt,valno;
  ub4 i,n;
  enum memitem item;

  for (i = 0; i < Item_count; i++) {
    memcfgs[i].factor = 5;
    memcfgs[i].offset = 1024;
    memcfgs[i].poolfac = 1;
  }

  oclear(eft);

  fmtstring(eft.mf.name,"%s/gtfsprep.cfg",dir);
  fname = eft.mf.name;

  if (osfileinfo(&eft.mf,fname)) return info(V0,"optional %s not present",fname);
  len = (ub4)eft.mf.len;
  if (len == 0) return info(0,"optional %s empty",fname);

  rv = readfile(&eft.mf,fname,0,0);
  if (rv) return 1;

  len = (ub4)eft.mf.len;
  if (len == 0) return info(0,"optional %s empty",fname);

  ub4 itempos,factorpos,offsetpos,poolfacpos;
  itempos=factorpos=offsetpos=poolfacpos = hi32;

  ub4 factor,offset,poolfac;

  ub4 *uvals = eft.uvals;

  do {

    res = nextchar_canon(&eft);
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
        else if (streq(val,"factor")) factorpos = valno;
        else if (streq(val,"offset")) offsetpos = valno;
        else if (streq(val,"poolfac")) poolfacpos = valno;
        else info(0,"skipping column %s",val);
      }
      if (itempos == hi32) return error(0,"%s: missing required column item",fname);
      if (factorpos == hi32) return error(0,"%s: missing required column factor",fname);
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
        if (itemvlen == n && memeq(itemval,itemnames[i],n)) item = i;
        i++;
      }
      if (item == Item_count) {
        parsewarn(FLN,fname,linno,colno,"unknown item name %s: choose one of:",itemval);
        for (i = 0; i < Item_count; i++) info(0,"  %s",itemnames[i]);
        break;
      }

// factor
      val = vals + factorpos * Collen;
      vlen = vallens[factorpos];

      if (vlen == 0) return parserr(FLN,fname,linno,colno,"empty value for %s",itemval);

      factor = uvals[factorpos];

      if (factor == hi32) return parserr(FLN,fname,linno,colno,"expected integer value for %s, found '%s'",itemval,val);
      else if (factor < 3) {
        parsewarn(FLN,fname,linno,colno,"factor for %s: %u below 3",itemval,factor);
        factor = 3;
      } else if (factor > 1000) {
        parsewarn(FLN,fname,linno,colno,"factor for %s: %u above 1000",itemval,factor);
        factor = 1000;
      }
      memcfgs[item].factor = factor;

// offset
      if (offsetpos != hi32) {
        val = vals + offsetpos * Collen;
        vlen = vallens[offsetpos];

        if (vlen == 0) return parserr(FLN,fname,linno,colno,"missing value for %s",itemval);

        offset = uvals[offsetpos];

        if (offset == hi32) return parserr(FLN,fname,linno,colno,"expected integer value for %s, found '%s'",itemval,val);
        if (offset > 1000) {
          parsewarn(FLN,fname,linno,colno,"offset for %s: %u above 1000",itemval,offset);
          offset = 1000;
        }
        memcfgs[item].offset = offset;
      }

// poolfac
      if (poolfacpos != hi32) {
        val = vals + poolfacpos * Collen;
        vlen = vallens[poolfacpos];

        if (vlen == 0) return parserr(FLN,fname,linno,colno,"missing value for %s",itemval);

        poolfac = uvals[poolfacpos];

        if (poolfac == hi32) return parserr(FLN,fname,linno,colno,"expected integer value for %s, found '%s'",itemval,val);
        if (poolfac < 1) {
          parsewarn(FLN,fname,linno,colno,"pool factor for %s: %u below 1",itemval,poolfac);
          poolfac = 1;
        } else if (poolfac > 1000) {
          parsewarn(FLN,fname,linno,colno,"pool factor for %s: %u above 1000",itemval,poolfac);
          poolfac = 1000;
        }
        memcfgs[item].poolfac = poolfac;
      }

      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  return 0;
}

#define addcol(line,pos,col,clen,c,pfx) addcolfln(FLN,(line),(pos),(col),(clen),(c),(pfx))

// add single column to output buffer with optional prefix
static ub8 addcolfln(ub4 fln,char *lines,ub8 pos,char *col,ub4 collen,char c,bool addpfx)
{
  if (lines == NULL) errorfln(FLN,Exit,fln,"nil lines");

  if (addpfx && collen && prefixlen) {
    memcpy(lines + pos,prefix,prefixlen);
    pos += prefixlen;
    lines[pos++] = '/';
  }
  if (collen) {
    memcpy(lines + pos,col,collen);
    pos += collen;
  }
  lines[pos++] = c;
  return pos;
}

#define addmcol(mem,line,pos,col,clen,c,pfx) addmcolfln(FLN,(mem),(line),(pos),(col),(clen),(c),(pfx))

static ub8 addmcolfln(ub4 fln,block *mem,char *lines,ub8 pos,char *col,ub4 clen,char c,bool pfx)
{
  if (lines == NULL) errorfln(FLN,Exit,fln,"nil lines");
  boundfln(fln,mem,pos,char);
  boundfln(fln,mem,pos + clen + 1,char);
  if (clen && *col == 0) infofln(fln,0,"empty string for len %u",clen);
  return addcol(lines,pos,col,clen,c,pfx);
}

#define addint(line,pos,val,c,pfx) addintfln(FLN,(line),(pos),(val),(c),(pfx))

static ub8 addintfln(ub4 fln,char *lines,ub8 pos,ub4 val,char c,bool addpfx)
{
  char buf[64];
  ub4 len = myutoa(buf,val);

  if (lines == NULL) errorfln(FLN,Exit,fln,"nil lines");

  return addcol(lines,pos,buf,len,c,addpfx);
}

#define addmint(mem,line,pos,val,c,pfx) addmintfln(FLN,(mem),(line),(pos),(val),(c),(pfx))

static ub8 addmintfln(ub4 fln,block *mem,char *lines,ub8 pos,ub4 val,char c,bool addpfx)
{
  char buf[64];
  ub4 len = myutoa(buf,val);

  if (lines == NULL) errorfln(FLN,Exit,fln,"nil lines");
  return addmcolfln(fln,mem,lines,pos,buf,len,c,addpfx);
}

#define addicol(mem,line,pos,col,clen) addicolfln(FLN,(mem),(line),(pos),(col),(clen))

// internal use buffer write
static ub4 addicolfln(ub4 fln,block *mem,char *lines,ub4 pos,char *col,ub4 clen)
{
  boundfln(fln,mem,pos,char);
  boundfln(fln,mem,pos + clen + 1,char);
  if (clen) memcpy(lines + pos,col,clen);
  pos += clen;
  lines[pos++] = 0;
  return pos;
}

enum Txmode { Tram,Metro,Rail,Bus,Ferry,Cabcar,Gondola,Funicular,Plane_int,Plane_dom,Taxi,Modecnt };
static const char *modenames[] = { "tram","metro","rail","bus","ferry","cable car","gondola","funicular","air-dom","air-int","taxi","unknown" };
static ub4 rmodecnts[Modecnt + 1];
static ub4 modecnts[Modecnt + 1];

static ub4 rtype2gtfs(enum Txmode x)
{
  switch(x) {
  case Tram: case Metro: case Rail: case Bus: case Ferry: case Cabcar: case Gondola: case Funicular: return x;

  case Plane_int: return 1101;
  case Plane_dom: return 1102;
  case Taxi: return 1500;
  case Modecnt: return x;
  }
  return x;
}

// extended types from support.google.com/transitpartners/answer/3520902
static ub4 xrtype2rtype(ub4 x,ub4 linno)
{
  error_eq(x,hi32);
  if (x >= 100 && x < 118) return Rail;
  if (x >= 200 && x < 210) return Bus;
  if (x >= 700 && x < 717) return Bus;
  if (x >= 900 && x < 907) return Rail;
  if (x >= 1000 && x < 1022) return Ferry;

  switch(x) {
  case 300: case 400: case 403: case 404: return Rail;
  case 401: case 402: case 405: case 500: case 600: return Metro;
  case 800: return Bus;
  case 1101: case 1103: case 1106: case 1107: case 1112: case 1114: return Plane_int;
  case 1102: case 1104: case 1105: case 1108: case 1109: case 1110: case 1111: case 1113: return Plane_dom;
  case 1200: return Ferry;
  case 1500: return Taxi;

  case 0: return Tram;
  case 1: return Metro;
  case 2: return Rail;
  case 3: return Bus;
  case 4: return Ferry;
  case 5: return Cabcar;
  case 6: return Gondola;
  case 7: return Funicular;

  case 11: // us/or/tilla
  default: warn(0,"line %u: unknown route type %u",linno,x); return Bus;
  }
}

static int filter(ub4 rtype)
{
  switch(rtype) {
  case Tram: return notram;
  case Taxi: return notaxi;
  case Metro: return nometro;
  case Rail: return norail;
  case Bus: return nobus;
  case Ferry: return noferry;
  case Plane_int: return noair;
  case Plane_dom: return noair;
  default: return 0;
  }
}

static ub4 geo2int(double g,double ofs,const char *name)
{
  double x = (g + ofs) * geoscale;
  ub4 i;

  errorcc(x > 4e9,Exit,"coord %f exceeds scale %u for %s",g,geoscale,name);

  i = (ub4)(x + 0.5);
  return i;
}

#define readfile_gtfs(mf,name,opt,len) readfile_gtfs_fln(FLN,(mf),(name),(opt),(len))
static int readfile_gtfs_fln(ub4 fln,struct myfile *mf,const char *name, int mustexist,ub4 maxlen)
{
  mf->fln = fln;
  return readfile_pad(mf,name,mustexist,maxlen,1,"\n");
}

static int rdagency(gtfsnet *net,const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawcnt,cnt = 0;
  int rv;
  char *buf;
  ub4 len,linno,colno;
  char *val,*vals,*idval,*nval,*urlval;
  ub2 idvlen,vlen,*vallens;
  ub4 valcnt,valno;
  ub4 aid,arid;
  ub8 linepos = 0,linelen;
  block *mem = &net->agencymem;

  oclear(eft);

  fmtstring(eft.mf.name,"%s/agency.%s",dir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,1,hi24);
  if (rv) return 1 + 256;

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  rawcnt = linecnt(fname,buf,len,1);

  if (rawcnt == 0) return error(0,"%s is empty",fname);

  hash *agencyids = net->agencyids = newhash(Item_agency,rawcnt,len);

  linelen = len + (rawcnt + 2) * prefixlen1 + rawcnt * 32;
  char *lines = net->agencylines = mkblock(mem,linelen,char,Noinit,"gtfs %u agency, len %u",rawcnt-1,(ub4)linelen);

  const char tab = '\t';
  ub4 agency_idpos,agency_namepos,agency_tzpos,agency_urlpos,agency_regionpos;
  agency_idpos=agency_namepos=agency_tzpos=agency_urlpos = agency_regionpos = hi32;

  ub4 *uvals = eft.uvals;

  do {

    res = nextchar(&eft);
    vals = eft.vals;

    switch(res) {

    case Newcmd:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"agency_id")) agency_idpos = valno;
        else if (streq(val,"agency_name")) agency_namepos = valno;
        else if (streq(val,"agency_timezone")) agency_tzpos = valno;
        else if (streq(val,"agency_url")) agency_urlpos = valno;
        else vrb0(0,"skipping column %s",val);
      }
      if (agency_namepos == hi32) return error(0,"%s: missing required column agency_name",fname);
      if (agency_urlpos == hi32) return error(0,"%s: missing required column agency_url",fname);
      if (agency_tzpos == hi32) info(0,"%s: no column agency_timezone",fname);
      if (agency_idpos == hi32) info(0,"%s: no column agency_id",fname);
      break;

    case Newitem:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      error_ge(cnt,rawcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        vrb0(0,"col %u val '%s'",valno,val);
      }
      if (valcnt < 2) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);

      urlval = vals + agency_urlpos * Collen;

      if (agency_idpos != hi32) {
        idval = vals + agency_idpos * Collen;
        idvlen = vallens[agency_idpos];
      } else idvlen = 0;

// name
      nval = vals + agency_namepos * Collen;
      nvlen = vallens[agency_namepos];

      if (nvlen == 0) return parserr(FLN,fname,linno,colno,"missing name for agency %s",idval);

      if (idvlen == 0) {
        if (cnt) return parserr(FLN,fname,linno,colno,"missing ID for agency %s",nval);
        idval = nval;
        idvlen = nvlen;
      }

      info(V0,"agency %s",nval);

      bound(mem,linepos + nvlen + idvlen + 1,char);

      linepos = addcol(lines,linepos,idval,idvlen,tab,1);
      linepos = addcol(lines,linepos,nval,vlen,tab,0);

      if (cnt < 10 && strict == 0) info(0,"agency: %s %s",nval,urlval);

// id
      aid = gethash(agencyids,idval,idvlen,arid);
      if (aid != hi32) return parserr(FLN,fname,linno,colno,"aid %s redefined as %u",idval,aid);
      aid = cnt;

      if (addhash(agencyids,idval,idvlen,arid,aid) == hi32) return 1;

// tz
      if (agency_tzpos != hi32) {
        val = vals + agency_tzpos * Collen;
        vlen = vallens[agency_tzpos];
      } else vlen = 0;

      bound(mem,linepos + vlen + 1,char);
      linepos = addcol(lines,linepos,val,vlen,tab,0);

// url
      val = vals + agency_urlpos * Collen;
      vlen = vallens[agency_urlpos];

      bound(mem,linepos + vlen + 1,char);
      linepos = addcol(lines,linepos,val,vlen,tab,0);

      cnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  if (cnt == 0) return parserr(FLN,fname,linno,0,"no agencies in %u lines",rawcnt);
  else if (cnt == 1) {
    idvlen = min(idvlen,sizeof(defagencyid));
    memcopy(defagencyid,idval,idvlen);
    defagencyidlen = idvlen;
  }
  infocc(cnt != rawcnt,0,"%u from %u entries",cnt,rawcnt);
  net->agencycnt = cnt;
  net->agencylinepos = (ub4)linepos;

  return 0;
}

static int rdcalendar(gtfsnet *net,const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawcnt,cnt = 0,caldatelen;
  int rv;
  char *buf;
  ub4 len,linno,colno,spoollen;
  char *val,*vals;
  ub2 vlen,*vallens;
  ub4 valcnt,valno;
  ub4 dow,date_cd,startdate_cd,enddate_cd,date;
  ub8 linepos = 0,linelen;
  block *mem = &net->calendarmem;
  char datestr[64];
  char caldatename[256];

  oclear(eft);

  fmtstring(caldatename,"%s/calendar_dates.%s",dir,fileext);
  if (osfileinfo(&eft.mf,caldatename)) caldatelen = 0;
  else caldatelen = (ub4)eft.mf.len;
  oclear(eft);
  fmtstring(eft.mf.name,"%s/calendar.%s",dir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,0,hi32 / 4);
  if (rv) return 1;
  if (eft.mf.exist == 0) return 0;

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  rawcnt = linecnt(fname,buf,len,1);

  if (rawcnt == 0) return warning(0,"%s is empty",fname);

  spoollen = max(caldatelen,(ub4)eft.mf.len);
  hash *serviceids = net->serviceids = newhash(Item_cal,max(rawcnt,spoollen / 32),spoollen);
  ub4 rsid,sid;

  linelen = len + rawcnt * (prefixlen1 + 16);
  char *lines = net->calendarlines = mkblock(mem,linelen,char,Noinit,"gtfs %u calendar, len %u",rawcnt-1,(ub4)linelen);

  const char tab = '\t';

  ub4 service_idpos = hi32,startpos = hi32,endpos = hi32;
  ub4 dowpos[7] = {hi32,hi32,hi32,hi32,hi32,hi32,hi32};

  vals = eft.vals;
  ub4 *uvals = eft.uvals;

  do {

    res = nextchar(&eft);

    switch(res) {

    case Newcmd:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"service_id")) service_idpos = valno;
        else if (streq(val,"monday")) dowpos[0] = valno;
        else if (streq(val,"tuesday")) dowpos[1] = valno;
        else if (streq(val,"wednesday")) dowpos[2] = valno;
        else if (streq(val,"thursday")) dowpos[3] = valno;
        else if (streq(val,"friday")) dowpos[4] = valno;
        else if (streq(val,"saturday")) dowpos[5] = valno;
        else if (streq(val,"sunday")) dowpos[6] = valno;
        else if (streq(val,"start_date")) startpos = valno;
        else if (streq(val,"end_date")) endpos = valno;
        else vrb0(0,"skipping column '%s'",val);
      }
      if (service_idpos == hi32) return error(0,"%s: missing required column service_id",fname);
      if (startpos == hi32) return error(0,"%s: missing required column start_date",fname);
      if (endpos == hi32) return error(0,"%s: missing required column end_date",fname);
      for (dow = 0; dow < 7; dow++) if (dowpos[dow] == hi32) return error(0,"%s: not all of required monday .. sunday columns present",fname);

      break;

    case Newitem:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      error_ge(cnt,rawcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        vrb0(0,"col %u val '%s'",valno,val);
      }
      if (valcnt < 4) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);

// id
      val = vals + service_idpos * Collen;
      vlen = vallens[service_idpos];
      rsid = uvals[service_idpos];

      sid = gethash(serviceids,val,vlen,rsid);
      if (sid != hi32) return parserr(FLN,fname,linno,colno,"sid %s redefined from line %u",val,sid);

      sid = cnt;
      if (addhash(serviceids,val,vlen,rsid,sid) == hi32) return 1;
      vrb0(0,"add sid %s %u as %u",val,rsid,sid);

      bound(mem,linepos + vlen + 1,char);
      linepos = addcol(lines,linepos,val,vlen,tab,1);

// monday .. sunday
      for (dow = 0; dow < 7; dow++) {
        val = vals + dowpos[dow] * Collen;
        vlen = vallens[dowpos[dow]];

        bound(mem,linepos + vlen + 1,char);
        linepos = addcol(lines,linepos,val,vlen,tab,0);
      }

// start
      val = vals + startpos * Collen;
      vlen = vallens[startpos];
      date_cd = uvals[startpos];

      if (date_cd == hi32) return parserr(FLN,fname,linno,colno,"invalid date %s",val);

      if (date_cd) { // zero signals out of range
        date_cd = min(date_cd,Era);
        date_cd = max(date_cd,Epoch);

        orglodate = min(orglodate,date_cd);
        orghidate = max(orghidate,date_cd);

        if (dateshift && date_cd != hi32) {
          date = cd2day(date_cd);
          date += dateshift;
          date = epochlim(date);
          date_cd = day2cd(date);
        }
        if (date_cd == hi32) return parserr(FLN,fname,linno,colno,"invalid date %s",val);
        lodate = min(lodate,date_cd);
      }

      startdate_cd = date_cd;

// end
      val = vals + endpos * Collen;
      vlen = vallens[endpos];
      date_cd = uvals[endpos];

      if (date_cd == hi32) return parserr(FLN,fname,linno,colno,"invalid date %s",val);

      if (date_cd) {

        if (date_cd < Epoch) {
          if (date_cd < 19000101) return parserr(FLN,fname,linno,colno,"invalid date %s",val);
          parsewarn(FLN,fname,linno,colno,"date %s before %u",val,Epoch);
          date_cd = Epoch;
        }

        orglodate = min(orglodate,date_cd);
        orghidate = max(orghidate,date_cd);

        if (dateshift && date_cd < Era) {
          date = cd2day(date_cd);
          date += dateshift;
          date = epochlim(date);
          date_cd = day2cd(date);
        } else if (date_cd >= Era) date_cd = (Erayear - 1) * 10000 + 1231;

        hidate = max(hidate,date_cd);
      }

      enddate_cd = date_cd;

      if (enddate_cd < startdate || startdate_cd > enddate) startdate_cd = enddate_cd = 0; // suppress
      else {
        startdate_cd = max(startdate_cd,startdate);
        if (haveenddate == 1) enddate_cd = min(enddate_cd,enddate);
        else if (haveenddate == 2) enddate_cd = enddate;
      }

      vlen = (ub2)fmtstring(datestr,"%u",startdate_cd);
      val = datestr;
      bound(mem,linepos + vlen + 1,char);
      linepos = addcol(lines,linepos,val,vlen,tab,0);

      vlen = (ub2)fmtstring(datestr,"%u",enddate_cd);
      val = datestr;
      bound(mem,linepos + vlen + 1,char);
      linepos = addcol(lines,linepos,val,vlen,'\n',0);

      cnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  net->calendarcnt = cnt;
  net->calendarlinepos = (ub4)linepos;

  if (cnt == 0) return 0;

  if (cnt == rawcnt) info(0,"%u calendar entr%s  timebox %u - %u org %u - %u",cnt,cnt == 1 ? "y" : "ies",lodate,hidate,orglodate,orghidate);
  else info(0,"%u from %u calendar entries  timebox %u - %u org %u - %u",cnt,rawcnt,lodate,hidate,orglodate,orghidate);

  if (hidate < startdate || lodate > enddate) error0(0,"no time range for calendar");

  if (hidate < startdate || lodate > enddate) {
    return 2;
  }
  if (enddate) hidate = min(hidate,enddate);
  if (startdate) lodate = max(lodate,startdate);
  info(0,"  net timebox %u - %u",lodate,hidate);

  ub4 hiday = cd2day(hidate);
  ub4 loday = cd2day(lodate);
  if (hiday - loday > maxdays) {
    genmsg(okdates ? Warn : Error,0,"time range of %u days exceeds max %u",hiday - loday,maxdays);
    return (okdates == 0);
  }

  return 0;
}

static int rdcaldates(gtfsnet *net,const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawcnt,cnt = 0,rcnt = 0,sidcnt = 0;
  int rv;
  char *buf;
  ub4 len,linno,colno;
  char *val,*vals;
  ub2 vlen,*vallens;
  ub4 valcnt,valno;
  ub4 date,date_cd;
  ub8 linepos = 0,linelen;
  block *mem = &net->caldatesmem;

  hash *serviceids = net->serviceids;
  ub4 rsid,sid;

  oclear(eft);

  fmtstring(eft.mf.name,"%s/calendar_dates.%s",dir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,0,hi32 / 4);
  if (rv) return 1;
  if (eft.mf.exist == 0) return 0;

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  rawcnt = linecnt(fname,buf,len,1);

  if (rawcnt == 0) return info(V0,"%s is empty",fname);

  if (serviceids == NULL) serviceids = net->serviceids = newhash(Item_date,rawcnt,len);

  linelen = len + rawcnt * prefixlen1;
  char *lines = net->caldateslines = mkblock(mem,linelen,char,Noinit,"gtfs %u calendar dates, len \ah%lu",rawcnt-1,linelen);

  const char tab = '\t';
  ub4 service_idpos = hi32,extype_pos = hi32,datepos = hi32;

  ub4 *uvals = eft.uvals;
  vals = eft.vals;
  struct eta eta;

  do {

    res = nextchar(&eft);

    switch(res) {

    case Newcmd:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"service_id")) service_idpos = valno;
        else if (streq(val,"date")) datepos = valno;
        else if (streq(val,"exception_type")) extype_pos = valno;
        else vrb0(0,"skipping column %s",val);
      }
      if (service_idpos == hi32) return error(0,"%s: missing required column service_id",fname);
      if (datepos == hi32) return error(0,"%s: missing required column date",fname);
      if (extype_pos == hi32) return error(0,"%s: missing required column exception_type",fname);
      break;

    case Newitem:

      if (rawcnt > 100000 && progress(&eta,"reading item %u of %u in %s",rcnt,rawcnt,fname)) return 1;

      rcnt++;
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      error_ge(cnt,rawcnt);

#if 0
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        vrb0(0,"col %u val '%s'",valno,val);
      }
#endif
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);

// date
      val = vals + datepos * Collen;
      vlen = vallens[datepos];
      date_cd = uvals[datepos];

      orglodate = min(orglodate,date_cd);
      orghidate = max(orghidate,date_cd);

      if (dateshift && date_cd != hi32) {
        date = cd2day(date_cd);
        date += dateshift;
        date = epochlim(date);
        date_cd = day2cd(date);
      }
      lodate = min(lodate,date_cd);
      hidate = max(hidate,date_cd);
      if (date_cd != hi32) {
        if (date_cd < startdate) continue;
        else if (date_cd > enddate) continue;
      }

// id
      val = vals + service_idpos * Collen;
      vlen = vallens[service_idpos];
      rsid = uvals[service_idpos];

      sid = gethash(serviceids,val,vlen,rsid);
      if (sid == hi32) {
        sid = sidcnt++ + net->calendarcnt;
        vrb0(Notty|Noiter,"add sid %s %u as %u",val,rsid,sid);
        if (addhash(serviceids,val,vlen,rsid,sid) == hi32) return 1;
      }

      bound(mem,linepos + vlen + 1,char);
      linepos = addcol(lines,linepos,val,vlen,tab,1);

// extype
      val = vals + extype_pos * Collen;
      vlen = vallens[extype_pos];

      bound(mem,linepos + vlen + 1,char);
      linepos = addcol(lines,linepos,val,vlen,tab,0);

      linepos = addint(lines,linepos,date_cd,'\n',0);

      cnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  if (cnt && hidate >= lodate && lodate < enddate && hidate > startdate) {
    lodate = max(lodate,startdate);
    hidate = min(hidate,enddate);
  }

  info(0,"%u from %u calendar_dates entries %u sids timebox %u - %u org %u - %u",cnt,rawcnt,sidcnt,lodate,hidate,orglodate,orghidate);
  net->caldatescnt = cnt;
  net->caldateslinepos = (ub4)linepos;

  freefile(&eft.mf);

  if (cnt && (lodate >= enddate || hidate < startdate)) return error0(0,"no time range");

  if (enddate) hidate = min(hidate,enddate);
  if (startdate) lodate = max(lodate,startdate);
  info(0,"  net timebox %u - %u",lodate,hidate);

  ub4 hiday = cd2day(hidate);
  ub4 loday = cd2day(lodate);
  if (hiday <= loday) {
    genmsg(okdates == 2 ? Warn : Error,0,"no time range %u - %u",loday,hiday);
    if (okdates < 2) return 1;
  }
  if (hiday - loday > maxdays) {
    genmsg(okdates ? Warn : Error,0,"time range of %u days exceeds max %u",hiday - loday,maxdays);
    return (okdates != 0);
  }

  return 0;
}

static ub4 mkfare(struct route *rp)
{
  if (rp->type == 9999) return 0;
  return hi32;
}

static int rdroutes(gtfsnet *net,const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawcnt,tcnt,cnt = 0,fltcnt = 0;
  int rv;
  char *buf;
  ub4 len,linno,colno;
  char *val,*vals;
  ub2 vlen,*vallens;
  ub4 *uvals;
  ub4 *valtypes;
  ub4 rrid,rtype,xrtype;
  ub4 valcnt,valno;
  ub8 linepos = 0,linelen;
  block *mem = &net->routemem;
  ub4 rid,arid,aid,eqid;
  char *idval,*agval;
  ub4 idvlen,agvlen;
  ub4 fare,farecnt = 0,ifarecnt = 0;
  ub4 agcnt = net->agencycnt;

  oclear(eft);

  fmtstring(eft.mf.name,"%s/routes.%s",dir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,1,hi32 / 16);
  if (rv) return 1;

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  rawcnt = linecnt(fname,buf,len,1);

  if (rawcnt == 0) return error(0,"%s is empty",fname);
  vrb0(0,"read %u entries from %s",rawcnt,fname);

  hash *routeids = net->routeids = newhash(Item_route,rawcnt,rawcnt * 64);
  hash *norouteids = net->norouteids = newhash(Item_route,rawcnt,rawcnt * 64);

  hash *eqroutes = newhash(Item_route,rawcnt,len * 2 + rawcnt * 64);

  hash *agencyids = net->agencyids;

  struct route *rp,*rp2,*routes = net->routes = alloc((rawcnt+20),struct route,0,"routes",rawcnt);

  char eqname[1024];
  ub4 eqnampos,eqnamlen = (ub4)sizeof(eqname);
  ub4 duprids = 0;

  linelen = len * 2 + 4 * rawcnt + (3 * rawcnt) * prefixlen1 + rawcnt * defagencylen; // optional agency_id
  char *lines = net->routelines = mkblock(mem,linelen,char,Noinit,"gtfs %u routes, len \ah%lu",rawcnt-1,linelen);

  const char tab = '\t';
  ub4 route_idpos,agencypos,snamepos,lnamepos,descpos,rtypepos,farepos;
  route_idpos=agencypos=snamepos=lnamepos=descpos=rtypepos=farepos = hi32;

  vals = eft.vals;
  uvals = eft.uvals;
  valtypes = eft.valtypes;

  do {

    res = nextchar(&eft);

    switch(res) {

    case Newcmd:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"route_id")) { route_idpos = valno; eft.colnames[valno] = "route_id"; }
        else if (streq(val,"agency_id")) { agencypos = valno; eft.colnames[valno] = "agency_id"; }
        else if (streq(val,"route_short_name")) { snamepos = valno; eft.colnames[valno] = "route_short_name"; }
        else if (streq(val,"route_long_name")) { lnamepos = valno; eft.colnames[valno] = "route_long_name"; }
        else if (streq(val,"route_desc")) { descpos = valno; eft.colnames[valno] = "route_desc"; }
        else if (streq(val,"route_type")) { rtypepos = valno; valtypes[valno] = 1; eft.colnames[valno] = "route_type"; }
        else if (streq(val,"fare")) { farepos = valno; eft.colnames[valno] = "fare"; }
        else vrb0(0,"skipping column %s",val);
      }
      if (route_idpos == hi32) return error(0,"%s: missing required column route_id",fname);
      if (rtypepos == hi32) return error(0,"%s: missing required column route_type",fname);
      if (agencypos == hi32) {
        if (agcnt == 1) info(0,"%s: no optional column agency_id",fname);
        else return error(0,"%s: missing required column agency_id for %u agencies",fname,agcnt);
      }
      break;

    case Newitem:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      error_ge(cnt,rawcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        vrb0(0,"col %u val '%s'",valno,val);
        error_gt_cc(vallens[valno],256,"col %u '%.64s'",valno,val);
      }
      if (valcnt < 4) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);

// id = rrid
      idval = vals + route_idpos * Collen;
      idvlen = vallens[route_idpos];
      error_ge(idvlen,sizeof(rp->rrid));
      rrid = uvals[route_idpos];
      if (idvlen == 0) return parserr(FLN,fname,linno,colno,"empty route id");

// agencyid
      if (agencypos != hi32) {
        agval = vals + agencypos * Collen;
        agvlen = vallens[agencypos];
        arid = uvals[agencypos];
      } else if (agcnt == 1) {
        agval = defagencyid;
        agvlen = defagencyidlen;
        aid = defaid;
      } else agvlen = 0;

      if (agvlen) {
        aid = gethash(agencyids,agval,agvlen,arid);
        if (aid == hi32) return parserr(FLN,fname,linno,colno,"unknown agency %s",agval);
      } else return parserr(FLN,fname,linno,colno,"empty agency for route %s",idval);

// type
      val = vals + rtypepos * Collen;
      vlen = vallens[rtypepos];

      error_gt_cc(vlen,16,"col %u",rtypepos);

      eqnampos = fmtstring(eqname,"aid=%s_type=%s",agval,val);

      xrtype = uvals[rtypepos];
      if (xrtype == hi32) {
        parsewarn(FLN,fname,linno,colno,"substitute 3 for missing numerical rtype '%s'",val);
        xrtype = 3;
      }
      rtype = xrtype2rtype(xrtype,linno);
      rmodecnts[min(rtype,Modecnt)]++;
      vrb0(0,"route id '%s' %u type '%s' %u",idval,rrid,val,rtype);

      if (filter(rtype)) {
        fltcnt++;
        vrb0(0,"filter route %s line %u on type '%s' %u",idval,linno,val,rtype);
        if (addhash(norouteids,idval,idvlen,rrid,cnt+1) == hi32) return 1;
        break;
      }

      rid = gethash(routeids,idval,idvlen,rrid);
      if (rid != hi32) {
        rp = routes + rid;
        if (airmode == 0 || rtype != Taxi) return parserr(FLN,fname,linno,colno,"route %s already defined on line %u",idval,rp->linno);
        else {
          fltcnt++;
          info(0,"filtering duplicate route %s",idval);
          if (addhash(norouteids,idval,idvlen,rrid,cnt+1) == hi32) return 1;
        }
      }

      if (strict && *idval == '#') {
        fltcnt++;
        if (addhash(norouteids,idval+1,idvlen-1,rrid,cnt+1) == hi32) return 1;
        break;
      }

      modecnts[min(rtype,Modecnt)]++;

      bound(mem,linepos + idvlen + 1,char);
      linepos = addcol(lines,linepos,idval,idvlen,tab,1);

      bound(mem,linepos + agvlen + 1,char);
      linepos = addcol(lines,linepos,agval,agvlen,tab,1);

      bound(mem,linepos + vlen + 1,char);
      linepos += myutoa(lines + linepos,rtype2gtfs(rtype));
      lines[linepos++] = tab;

      if (addhash(routeids,idval,idvlen,rrid,cnt+1) == hi32) return 1;
      rid = gethash(routeids,idval,idvlen,rrid);
      if (rid == hi32 || rid != cnt + 1) return error(0,"stored %s not found",idval);
      error_ge(rid,rawcnt + 16);

      rp = routes + rid;
      rp->type = rtype;
      rp->linno = linno;
      rp->aid = aid;
      rp->eqid = hi32;
      strcopy(rp->agency,agval);
      strcopy(rp->rrid,idval);

// sname
      if (snamepos != hi32) {
        val = vals + snamepos * Collen;
        vlen = vallens[snamepos];

        if (vlen && *val) eqnampos += mysnprintf(eqname,eqnampos,eqnamlen,"_%s",val);

        bound(mem,linepos + vlen + 1,char);
        linepos = addcol(lines,linepos,val,vlen,tab,0);
      } else lines[linepos++] = tab;

// lname
      if (lnamepos != hi32) {
        val = vals + lnamepos * Collen;
        vlen = vallens[lnamepos];

        if (vlen && *val) eqnampos += mysnprintf(eqname,eqnampos,eqnamlen,"_%s",val);

        bound(mem,linepos + vlen + 1,char);
        linepos = addcol(lines,linepos,val,vlen,tab,0);
        strcopy(rp->name,val);
      } else lines[linepos++] = tab;

// desc
      if (descpos != hi32) {
        val = vals + descpos * Collen;
        vlen = vallens[descpos];

        bound(mem,linepos + vlen + 1,char);
        linepos = addcol(lines,linepos,val,vlen,tab,0);
      } else lines[linepos++] = tab;

// fare
      fare = hi32;
      if (farepos != hi32) {
        val = vals + farepos * Collen;
        vlen = vallens[farepos];
        fare = uvals[farepos];
        if (fare != hi32) farecnt++;
        else if (vlen) parsewarn(FLN,fname,linno,colno,"ignore non-numerical fare %s",val);
      }
      if (fare == hi32) fare = mkfare(rp);
      bound(mem,linepos + vlen + 4,char);
      if (fare == hi32) lines[linepos++] = '\n';
      else {
        ifarecnt++;
//      info(0,"add fare %s",val);
        linepos = addint(lines,linepos,fare,'\n',0);
      }

// merge duplicates
      error_ge(eqnampos,512);

      eqid = gethash(eqroutes,eqname,eqnampos,hi32);
      if (eqid == hi32) {
        if (addhash(eqroutes,eqname,eqnampos,hi32,rid) == hi32) return 1;
      } else {
        error_ge(eqid,rid);
        rp2 = routes + eqid;
        if (mergeduproutes) {
          rp2->eqcnt++;
          rp->eqid = eqid;
          if (strict) return error(0,"%s.%u: duplicate route %s, first ln %u",fname,linno,eqname,rp2->linno);
          else info(Iter,"line %u: merge duplicate route %s, first ln %u",linno,eqname,rp2->linno);
          duprids++;
        } else {
          info(Iter,"line %u: duplicate route %s, first ln %u",linno,eqname,rp2->linno);
        }
        duprids++;
      }
      cnt++;

      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  if (fltcnt) info(0,"%u from %u routes",cnt,cnt + fltcnt);
  else info(0,"%u routes",cnt);
  info(CC0," %u of %u duplicate routes",duprids,cnt);
  infocc(farecnt,0," %u with fares, %u inferred",farecnt,ifarecnt);

  ub4 ncnt,fmtpos = 0;
  char fmtbuf[1024];
  ub4 buflen = sizeof(fmtbuf);
  for (rtype = 0; rtype <= Modecnt; rtype++) {
    ncnt = modecnts[rtype];
    if (ncnt == 0) continue;
    fmtpos += mysnprintf(fmtbuf,fmtpos,buflen,"  %s %u",modenames[rtype],ncnt);
  }
  infocc(fmtpos,0,"route modes:%s",fmtbuf);

  for (rtype = 0; rtype <= Modecnt; rtype++) {
    ncnt = modecnts[rtype];
    tcnt = rmodecnts[rtype];
    infocc(ncnt != tcnt,0,"%u from %u %s routes",ncnt,tcnt,modenames[rtype]);
  }

  net->routecnt = cnt;
  net->routelinepos = (ub4)linepos;

  if (noany) {
    infocc(cnt == 0,0,"no routes from %u",rawcnt);
    return 0;
  } else if (cnt) return 0;
  return error(0,"no routes from %u",rawcnt);
}

static int rdprestops(gtfsnet *net,const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawstopcnt,stopcnt,stop = 0;
  int rv;
  char *buf;
  ub4 len,linno,colno;
  char *val,*idval,*nameval,*intnval,*vals;
  ub2 vlen,idvlen,intnlen,*vallens;
  ub4 *uvals;
  ub4 valcnt,colcnt,valno;
  ub4 stopid,rstopid;

  double d2r = M_PI / 180;
  double lat,lon;
  double lolat = 90,hilat = -90,lolon = 180,hilon = -180;

  struct eta eta;

  oclear(eft);

  fmtstring(eft.mf.name,"%s/stops.%s",dir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,1,hi28);
  if (rv) return 1;

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  rawstopcnt = linecnt(fname,buf,len,1);

  if (rawstopcnt == 0) return warning(0,"%s is empty",fname);

  hash *prestopids = net->prestopids = newhash(Item_stop,rawstopcnt,len);

  struct gtstop *sp,*presp,*stops = net->prestops = alloc(rawstopcnt,struct gtstop,0,"ext ports",rawstopcnt);
  struct gtstop *lolatsp,*hilatsp,*lolonsp,*hilonsp;
  ub4 stop_idpos,stop_codepos,stop_namepos,stop_descpos,stop_latpos,stop_lonpos,stop_locpos,parent_stapos,stop_intnamepos;
  stop_idpos=stop_codepos=stop_namepos=stop_descpos=stop_latpos=stop_lonpos=stop_locpos=parent_stapos=stop_intnamepos = hi32;

  sp = stops;
  lolatsp = hilatsp = lolonsp = hilonsp = stops;

  vals = eft.vals;
  uvals = eft.uvals;

  sassert(sizeof(sp->name) > 16,"name[>16]");
  sassert(sizeof(sp->name) == sizeof(sp->iname),"name[] == iname[]");
  ub4 namemax = sizeof(sp->name) - 1;
  ub4 inamemax = sizeof(sp->iname) - 1;

  colcnt = 0;

  do {

    res = nextchar(&eft);

    switch(res) {
    case Newcmd:
      valcnt = colcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"stop_id")) stop_idpos = valno;
        else if (streq(val,"stop_name")) stop_namepos = valno;
        else if (streq(val,"stop_name_int")) stop_intnamepos = valno;
        else if (streq(val,"stop_lat")) stop_latpos = valno;
        else if (streq(val,"stop_lon")) stop_lonpos = valno;
        else vrb0(0,"skipping column '%s'",val);
      }
      if (stop_idpos == hi32) return error(0,"%s: missing required column stopid",fname);
      if (stop_namepos == hi32) return error(0,"%s: missing required column stop_name",fname);
      if (stop_latpos == hi32) return error(0,"%s: missing required column stop_lat",fname);
      if (stop_lonpos == hi32) return error(0,"%s: missing required column stop_lon",fname);
      break;

    case Newitem:

      if (progress(&eta,"reading stop %u of %u in %s",stop,rawstopcnt,fname)) return 1;

      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      if (valcnt < 4 || valcnt + 2 < colcnt) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);
      else if (valcnt != colcnt) infocc(stop == 0,0,"row has %u cols, header %u",valcnt,colcnt);

      sp->id = stop;
      sp->linno = linno;

      nameval = vals + stop_namepos * Collen;

// id
      idval = vals + stop_idpos * Collen;
      idvlen = vallens[stop_idpos];

      if (idvlen == 0 || *idval == 0) return parserr(FLN,fname,linno,colno,"empty id for %s",nameval);

// name
      vlen = vallens[stop_namepos];
      if (vlen > namemax) {
        parsewarn(FLN,fname,linno,colno,"truncating name %u.'%s' to %u",vlen,nameval,namemax);
        vlen = (ub2)truncutf8(nameval,namemax);
      }

      if (stop_intnamepos != hi32) {
        intnval = vals + stop_intnamepos * Collen;
        intnlen = vallens[stop_intnamepos];
        if (intnlen > inamemax) {
          parsewarn(FLN,fname,linno,colno,"truncating name '%s' to %u",intnval,inamemax);
          intnlen = (ub2)truncutf8(intnval,inamemax);
        }
        if (*intnval == 0) intnlen = 0;
      } else {
        intnlen = vlen;
        intnval = nameval;
      }
      if (vlen == 0 || *nameval == 0) {
        if (intnlen == 0) {
          parsewarn(FLN,fname,linno,colno,"missing stop name for id %s",idval);
          nameval = idval;
        }
        nameval = intnval;
      }
      sp->namelen = vlen;
      if (vlen) memcpy(sp->name,nameval,vlen);

      sp->inamelen = intnlen;
      if (intnlen) memcpy(sp->iname,intnval,min(intnlen,inamemax));

// lat
      val = vals + stop_latpos * Collen;
      vlen = vallens[stop_latpos];
      if (vlen && *val == ' ') { val++; vlen--; }

      if (vlen == 0) {
        parserr(FLN,fname,linno,colno,"stop %s has no lat coordinate",nameval);
        break;
      } else if (vlen == 1 && *val == '0') {
        parsewarn(FLN,fname,linno,colno,"stop %s has zero latitude %s",nameval,val);
      } else if (vlen == 3 && memcmp(val,"0.0",3) == 0) {
        parsewarn(FLN,fname,linno,colno,"stop %s has zero latitude %s",nameval,val);
      }

      if (str2dbl(val,vlen,&lat)) {
        parserr(FLN,fname,linno,colno,"cannot convert coord '%.*s' for %s %s",vlen,val,idval,nameval);
        break;
      }
      if (lat <= -90.0 || lat >= 90.0) {
        parsewarn(FLN,fname,linno,colno,"stop %s has invalid latitude %s",nameval,val);
        lat = 0;
      }

      if (vlen == 0) {
        parserr(FLN,fname,linno,colno,"stop %s has no coordinates",nameval);
        break;
      }

      sp->lat = lat;
      if (lat < lolat) { lolat = lat; lolatsp = sp; };
      if (lat > hilat) { hilat = lat; hilatsp = sp; };

// lon
      val = vals + stop_lonpos * Collen;
      vlen = vallens[stop_lonpos];
      if (vlen && *val == ' ') { val++; vlen--; }

      if (vlen == 0) {
        parserr(FLN,fname,linno,colno,"stop %s has no lon coordinate",nameval);
        break;
      } else if (vlen == 1 && *val == '0') {
        parsewarn(FLN,fname,linno,colno,"stop %s has zero longitude %s",nameval,val);
      } else if (vlen == 3 && memcmp(val,"0.0",3) == 0) {
        parsewarn(FLN,fname,linno,colno,"stop %s has zero longitude %s",nameval,val);
      }

      if (str2dbl(val,vlen,&lon)) {
        parserr(FLN,fname,linno,colno,"cannot convert coord '%.*s' for %s",vlen,val,nameval);
        break;
      }
      if (lon <= -180.0 || lat >= 180.0) {
        parsewarn(FLN,fname,linno,colno,"stop %s has invalid longitude %s",nameval,val);
        lon = 0;
      }

      sp->lon = lon;
      if (lon < lolon) { lolon = lon; lolonsp = sp; };
      if (lon > hilon) { hilon = lon; hilonsp = sp; };

      sp->rlat = sp->lat * d2r;
      sp->rlon = sp->lon * d2r;
      sp->ilat = geo2int(sp->lat,90,nameval);
      sp->ilon = geo2int(sp->lon,180,nameval);

// id
      rstopid = uvals[stop_idpos];

      stopid = gethash(prestopids,idval,idvlen,rstopid);
      if (stopid != hi32) {
        error_ge(stopid,rawstopcnt);
        presp = stops + stopid;
        parsewarn(FLN,fname,linno,colno,"stop ID %s previously defined as %u on line %u",idval,stopid,presp->linno);
        if (strict) return 1;
        break;
      }
      if (addhash(prestopids,idval,idvlen,rstopid,stop) == hi32) return 1;

      sp->geondx = hi32;

      sp++;
      stop++;
      error_gt(stop,rawstopcnt,0);
      break;  // newitem

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  info(0,"min lat %f %f %s",lolat,lolatsp->lon,lolatsp->name);
  info(0,"max lat %f %f %s",hilat,hilatsp->lon,hilatsp->name);
  info(0,"min lon %f %f %s",lolon,lolonsp->lat,lolonsp->name);
  info(0,"max lon %f %f %s",hilon,hilonsp->lat,hilonsp->name);

  stopcnt = net->prestopcnt = stop;
  warncc(net->routecnt >= stopcnt,0,"%u routes on %u stops",net->routecnt,stopcnt);
  return info(0,"%u stops\a= from %u lines",stopcnt,rawstopcnt);
}

static int rdtransfers(gtfsnet *net,const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawcnt,xfercnt,xfer = 0;
  int rv;
  char *buf;
  ub4 len,linno,colno;
  char *val,*fidval,*tidval,*vals;
  ub2 vlen,fidvlen,tidvlen,*vallens;
  ub4 type,mintt;
  ub4 *uvals;
  ub4 valcnt,colcnt,valno;
  ub4 fstopid,tstopid,rstopid;
  struct eta eta;

  oclear(eft);

  fmtstring(eft.mf.name,"%s/transfers.%s",dir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,0,hi24);
  if (rv) return 1;
  if (eft.mf.exist == 0) return 0;

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  rawcnt = linecnt(fname,buf,len,1);

  if (rawcnt == 0) return warning(0,"%s is empty",fname);
  else if (rawcnt > 1000 * 1000) return error(0,"%s of \ah%u lines too large",fname,rawcnt);
  hash *stopids = net->stopids;
  hash *prestopids = net->prestopids;

  struct gtstop *fsp,*tsp,*prestops = net->prestops;
  ub4 prestopcnt = net->prestopcnt;
  ub4 stopcnt = net->stopcnt;
  ub4 filtercnt = 0;

  ub8 linelen = len + 4 * rawcnt + (2 * rawcnt) * prefixlen1;
  block *mem = &net->xfermem;
  char *lines = net->xferlines = mkblock(mem,linelen,char,Noinit,"gtfs %u transfers, len \ah%lu",rawcnt-1,linelen);
  ub8 linepos = 0;
  const char tab = '\t';

  ub4 from_stop_pos,to_stop_pos,type_pos,min_time_pos;
  from_stop_pos = to_stop_pos = type_pos = min_time_pos = hi32;

  vals = eft.vals;
  uvals = eft.uvals;

  colcnt = 0;

  do {

    res = nextchar(&eft);

    switch(res) {
    case Newcmd:
      valcnt = colcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"from_stop_id")) from_stop_pos = valno;
        else if (streq(val,"to_stop_id")) to_stop_pos = valno;
        else if (streq(val,"transfer_type")) type_pos = valno;
        else if (streq(val,"min_transfer_time")) min_time_pos = valno;
        else vrb0(0,"skipping column '%s'",val);
      }
      if (from_stop_pos == hi32) return error(0,"%s: missing required column from_stop_id",fname);
      if (to_stop_pos == hi32) return error(0,"%s: missing required column to_stop_id",fname);
      if (type_pos == hi32) return error(0,"%s: missing required column transfer_type",fname);
      if (min_time_pos == hi32) info(0,"%s: no column min_transfer_time",fname);
      break;

    case Newitem:

      if (progress(&eta,"reading stop %u of %u in %s",xfer,rawcnt,fname)) return 1;

      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      if (valcnt < 3 || valcnt + 2 < colcnt) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);
      else if (valcnt != colcnt) infocc(xfer == 0,0,"row has %u cols, header %u",valcnt,colcnt);

// from id
      fidval = vals + from_stop_pos * Collen;
      fidvlen = vallens[from_stop_pos];
      if (fidvlen == 0 || *fidval == 0) return parserr(FLN,fname,linno,colno,"empty from id");

      rstopid = uvals[from_stop_pos];

      fstopid = gethash(prestopids,fidval,fidvlen,rstopid);
      if (fstopid == hi32) return parserr(FLN,fname,linno,colno,"unknown stop ID %s",fidval);
      error_ge(fstopid,prestopcnt);

      fsp = prestops + fstopid;

      fstopid = gethash(stopids,fidval,fidvlen,rstopid);
      if (fstopid == hi32) { filtercnt++; break; }
      error_ge(fstopid,stopcnt);

// to id
      tidval = vals + to_stop_pos * Collen;
      tidvlen = vallens[to_stop_pos];
      if (tidvlen == 0 || *tidval == 0) return parserr(FLN,fname,linno,colno,"empty to id");

      rstopid = uvals[to_stop_pos];

      tstopid = gethash(prestopids,tidval,tidvlen,rstopid);
      if (tstopid == hi32) return parserr(FLN,fname,linno,colno,"unknown stop ID %s",tidval);
      error_ge(tstopid,prestopcnt);

      tsp = prestops + tstopid;

      tstopid = gethash(stopids,tidval,tidvlen,rstopid);
      if (tstopid == hi32) { filtercnt++; break; }
      error_ge(tstopid,stopcnt);

// type
      val = vals + type_pos * Collen;
      vlen = vallens[type_pos];
      type = uvals[type_pos];

      if (vlen == 0) { parsewarn(FLN,fname,linno,colno,"empty type for %s-%s",fidval,tidval); type = 0; }
      if (type == hi32) return parserr(FLN,fname,linno,colno,"non-numerical type '%s'",val);

// mintt
      if (min_time_pos != hi32) {

        val = vals + min_time_pos * Collen;
        vlen = vallens[min_time_pos];
        mintt = uvals[min_time_pos];

        if (vlen == 0) mintt = 0;
        if (mintt == hi32) return parserr(FLN,fname,linno,colno,"non-numerical transfer time '%s'",val);
      } else mintt = 0;

      bound(mem,linepos + fidvlen + tidvlen + 2 * prefixlen1 + 4 + 4,char);

      linepos = addcol(lines,linepos,fidval,fidvlen,tab,1);
      linepos = addcol(lines,linepos,tidval,tidvlen,tab,1);

      linepos = addint(lines,linepos,type,tab,0);

      linepos = addint(lines,linepos,mintt,'\n',0);

      error_ge(linepos,hi32);

      xfer++;
      error_gt(xfer,rawcnt,0);
      break;  // newitem

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  xfercnt = net->xfercnt = xfer;
  net->xferlinepos = (ub4)linepos;
  return info(0,"%u xfers from %u lines %u filtered",xfercnt,rawcnt,filtercnt);
}

static int rdgeonames(gtfsnet *net)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawstopcnt,stopcnt,stop = 0;
  int rv;
  char *buf;
  ub4 len,linno,colno;
  char *val,*idval,*nameval,*vals,*orgval;
  ub2 vlen,orgvlen,idvlen,*vallens;
  ub4 *uvals;
  ub4 valcnt,colcnt,valno;
  ub4 rstopid,pop;

  double d2r = M_PI / 180;
  double lat,lon;

  struct eta eta;

  oclear(eft);

  fmtstring(eft.mf.name,"geo/%s.tab",geonamedb);
  fname = eft.mf.name;
  eft.skip0 = 1;

  rv = readfile_gtfs(&eft.mf,fname,0,hi32 / 2);
  if (rv) return 1;
  if (eft.mf.exist == 0) return info(0,"skip nonexistent %s",fname);

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  if (len == 0) return info(0,"skipping empty %s",fname);
  rawstopcnt = linecnt(fname,buf,len,1);

  if (rawstopcnt == 0) return warning(0,"%s is empty",fname);

  struct geostop *sp,*stops = net->geostops = alloc(rawstopcnt,struct geostop,0,"geonames",rawstopcnt);

  ub4 idpos,tzpos,namepos,latpos,lonpos,ccpos,poppos,classpos;
  idpos=tzpos=namepos=latpos=lonpos=ccpos=poppos=classpos = hi32;

  ub4 notz = 0,nocoord = 0,popcnt = 0;

  sp = stops;

  vals = eft.vals;
  uvals = eft.uvals;

  colcnt = 0;

  do {

    res = nextchar_canon(&eft);

    switch(res) {
    case Newcmd:
      valcnt = colcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"id")) idpos = valno;
        else if (streq(val,"name")) namepos = valno;
        else if (streq(val,"lat")) latpos = valno;
        else if (streq(val,"lon")) lonpos = valno;
        else if (streq(val,"tz")) tzpos = valno;
        else if (streq(val,"pop")) poppos = valno;
        else if (streq(val,"class")) classpos = valno;
        else vrb0(0,"skipping column '%s'",val);
      }
      if (idpos == hi32) return error(0,"%s: missing required column id",fname);
      if (namepos == hi32) return error(0,"%s: missing required column name",fname);
      if (latpos == hi32) return error(0,"%s: missing required column lat",fname);
      if (lonpos == hi32) return error(0,"%s: missing required column lon",fname);
      if (tzpos == hi32) return error(0,"%s: missing required column tz",fname);
      if (poppos == hi32) return error(0,"%s: missing required column population",fname);
      if (classpos == hi32) return error(0,"%s: missing required column class",fname);
      break;

    case Newitem:

      if (progress(&eta,"reading poi %u of %u in %s",stop,rawstopcnt,fname)) return 1;

      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      if (valcnt < 4 || valcnt + 2 < colcnt) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);
      else if (valcnt != colcnt) infocc(stop == 0,0,"row has %u cols, header %u",valcnt,colcnt);

      sp->id = stop;

      nameval = vals + namepos * Collen;
      vlen = vallens[namepos];
      if (vlen == 0 || *nameval == 0) return parserr(FLN,fname,linno,colno,"missing poi name");

//lat
      val = orgval = vals + latpos * Collen;
      vlen = orgvlen = vallens[latpos];

      if (vlen == 0) { nocoord++; break; }
      if (*val == ' ' || *val == 0) { val++; vlen--; }
      if (vlen == 0) { nocoord++; break; }
      if (vlen == 1 && *val == '-') { nocoord++; break; }

      if (str2dbl(val,vlen,&lat)) {
        info(Iter,"%s.%u: invalid lat coord '%.*s' %x len %u for %s",fname,linno,orgvlen,orgval,*orgval,orgvlen,nameval);
        break;
      }
      if (lat < -89 || lat > 89) break;

      sp->lat = lat;
      sp->ilat = geo2int(lat,90,nameval);
      sp->rlat = lat * d2r;

//lon
      val = orgval = vals + lonpos * Collen;
      vlen = orgvlen = vallens[lonpos];

      if (vlen == 0) { nocoord++; break; }
      if (*val == ' ' || *val == 0) { val++; vlen--; }
      if (vlen == 0) { nocoord++; break; }
      if (vlen == 1 && *val == '-') { nocoord++; break; }

      if (str2dbl(val,vlen,&lon)) {
        info(Iter,"%s.%u: invalid lon coord '%.*s' for %s",fname,linno,orgvlen,orgval,nameval);
        break;
      }
      sp->lon = lon;
      sp->ilon = geo2int(lon,180,nameval);
      sp->rlon = sp->lon * d2r;

// id
      idval = vals + idpos * Collen;
      idvlen = vallens[idpos];

      if (idvlen) {
        rstopid = uvals[idpos];
        sp->id = rstopid;
      }

// name
      val = vals + namepos * Collen;
      vlen = vallens[namepos];

      if (vlen == 0) return parserr(FLN,fname,linno,colno,"poi ID %s has no name",idval);

      sp->namelen = vlen;
      memcpy(sp->name,val,min(vlen,sizeof(sp->name)-1));

// class
      val = vals + classpos * Collen;
      vlen = vallens[classpos];

      if (vlen && *val == 'P') sp->isplace = 1;

// population
      val = vals + poppos * Collen;
      vlen = vallens[poppos];
      pop = uvals[poppos];
      if (sp->isplace && sp->namelen && vlen && pop && pop != hi32) {
        sp->pop = pop;
        if (pop >= poplimit) {
          info(0,"%s pop. \ah%u %f,%f",sp->name,pop,sp->lat,sp->lon);
          popcnt++;
        }
      }

// tz
      val = vals + tzpos * Collen;
      vlen = vallens[tzpos];

      if (vlen == 0) {
        notz++;
        // parsewarn(FLN,fname,linno,colno,"stop ID %s has no tz",idval);
        break;
      }

      sp->tzlen = vlen;
      memcpy(sp->tzname,val,min(vlen,sizeof(sp->tzname)-1));

      sp++;
      stop++;
      error_gt(stop,rawstopcnt,0);
      break;  // newitem

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  freefile(&eft.mf);

  stopcnt = net->geostopcnt = stop;
  net->geopopcnt = popcnt;
  info(CC0,"\ah%u pois without timezone",notz);
  info(CC0,"\ah%u pois without coords",nocoord);
  info(CC0,"\ah%u pois with pop above %u",popcnt,poplimit);
  return info(0,"\ah%u pois from \ah%u lines",stopcnt,rawstopcnt);
}

static void mkgeosort(gtfsnet *net,ub4 cnt,struct gtstop *cstops)
{
  ub4 dep,idx;
  struct gtstop *sp;

  if (cnt < 2) return;

  info(0,"sorting \ah%u geo items",cnt);

  ub8 xlat,*latxsort = alloc(cnt,ub8,0,"geo lat",cnt);
  ub8 xlon,*lonxsort = alloc(cnt,ub8,0,"geo lon",cnt);

  ub4 lat,*latsort = net->latsort = alloc(cnt,ub4,0,"geo lat",cnt);
  ub4 lon,*lonsort = net->lonsort = alloc(cnt,ub4,0,"geo lon",cnt);
  ub4 *latsortidx = net->latsortidx = alloc(cnt,ub4,0,"geo latidx",cnt);
  ub4 *lonsortidx = net->lonsortidx = alloc(cnt,ub4,0,"geo lonidx",cnt);

  // prepare bsearch for geo lookup
  for (dep = 0; dep < cnt; dep++) {
    sp = cstops + dep;
    lat = sp->ilat; lon = sp->ilon;
    xlat = (ub8)lat << 32 | dep;
    xlon = (ub8)lon << 32 | dep;
    latxsort[dep] = xlat;
    lonxsort[dep] = xlon;
  }
  sort8(latxsort,cnt,FLN,"latsort");
  sort8(lonxsort,cnt,FLN,"lonsort");

  // separate sorted list into coord and index
  for (idx = 0; idx < cnt; idx++) {
    xlat = latxsort[idx];
    xlon = lonxsort[idx];
    lat = (ub4)(xlat >> 32);
    lon = (ub4)(xlon >> 32);
    dep = (ub4)xlat & hi32;
    latsort[idx] = lat;
    latsortidx[idx] = dep;
    dep = (ub4)xlon & hi32;
    lonsort[idx] = lon;
    lonsortidx[idx] = dep;
  }
  afree(latxsort,"geo lat");
  afree(lonxsort,"geo lon");
}

static void mknamgeosort(gtfsnet *net,ub4 cnt,struct geostop *cstops)
{
  ub4 dep,idx;
  struct geostop *sp;

  if (cnt < 2) return;

  info(0,"sorting \ah%u geo items",cnt);

  ub8 xlat,*latxsort = alloc(cnt,ub8,0,"geo lat",cnt);
  ub8 xlon,*lonxsort = alloc(cnt,ub8,0,"geo lon",cnt);

  ub4 lat,*latsort = net->namlatsort = alloc(cnt,ub4,0,"geo lat",cnt);
  ub4 lon,*lonsort = net->namlonsort = alloc(cnt,ub4,0,"geo lon",cnt);
  ub4 *latsortidx = net->namlatsortidx = alloc(cnt,ub4,0,"geo latidx",cnt);
  ub4 *lonsortidx = net->namlonsortidx = alloc(cnt,ub4,0,"geo lonidx",cnt);

  // prepare bsearch for geo lookup
  for (dep = 0; dep < cnt; dep++) {
    sp = cstops + dep;
    lat = sp->ilat; lon = sp->ilon;
    xlat = (ub8)lat << 32 | dep;
    xlon = (ub8)lon << 32 | dep;
    latxsort[dep] = xlat;
    lonxsort[dep] = xlon;
  }
  sort8(latxsort,cnt,FLN,"latsort");
  sort8(lonxsort,cnt,FLN,"lonsort");

  // separate sorted list into coord and index
  for (idx = 0; idx < cnt; idx++) {
    xlat = latxsort[idx];
    xlon = lonxsort[idx];
    lat = (ub4)(xlat >> 32);
    lon = (ub4)(xlon >> 32);
    dep = (ub4)xlat & hi32;
    latsort[idx] = lat;
    latsortidx[idx] = dep;
    dep = (ub4)xlon & hi32;
    lonsort[idx] = lon;
    lonsortidx[idx] = dep;
  }
  afree(latxsort,"geo lat");
  afree(lonxsort,"geo lon");
}

static int lookupstops(gtfsnet *net,struct gtstop *cstops,ub4 stopcnt)
{
  struct gtstop *sp;
  struct geostop *pp,*gstops = net->geostops;
  ub4 geostopcnt = net->geostopcnt;

  if (geostopcnt == 0) return 0;

  ub4 *latsort = net->namlatsort;
  ub4 *lonsort = net->namlonsort;
  ub4 *latsortidx = net->namlatsortidx;
  ub4 *lonsortidx = net->namlonsortidx;
  ub4 ilat,ilon;
  double rlat,rlon;
  double dist,vdist,hdist,lodist;

  ub4 dep;

  ub4 dir = 1;
  ub4 a,o,ar,or,ai,oi,al,ol,loid;

  ub4 iter,iterlim = max(geostopcnt / 4,20);
  ub4 nogeo = 0;
  struct eta eta;

  error_zp(latsort,stopcnt);

  for (dep = 0; dep < stopcnt; dep++) {

    if (stopcnt > 10000 && progress(&eta,"lookup stop %u of %u nogeo %u",dep,stopcnt,nogeo)) return 1;

    sp = cstops + dep;

    ilat = sp->ilat;
    ilon = sp->ilon;
    rlat = sp->rlat; rlon = sp->rlon;

    a = bsearch4(latsort,geostopcnt,ilat,FLN,"lat");
    o = bsearch4(lonsort,geostopcnt,ilon,FLN,"lon");
    a = min(a,geostopcnt-1);
    o = min(o,geostopcnt-1);
    info(V0,"%s initial pos %u,%u of %u",sp->name,a,o,geostopcnt);

    ar = al = a;
    or = ol = o;

    dist = vdist = hdist = lodist = 1e10;
    loid = hi32;
    pp = gstops;

    iter = 0;
    while (iter < iterlim) {

      iter++;

      if (a < geostopcnt) {
        ai = latsortidx[a];
        pp = gstops + ai;
        dist = geodist(rlat,rlon,pp->rlat,pp->rlon,sp->name);
        if (dist < lodist) { lodist = dist; loid = ai; }
        else if (dist > Georange - 1) warn(0,"geo poi %u %s",ai,pp->name);
        else {
          vdist = geodist(rlat,rlon,pp->rlat,rlon,sp->name);
          if (vdist >= lodist) {
            if (dir) al = geostopcnt; else ar = geostopcnt;
          } else if (vdist > Georange - 1) warn(0,"geo poi %u %s",ai,pp->name);
        }
      }

      if (o < geostopcnt) {
        oi = lonsortidx[o];
        pp = gstops + oi;
        dist = geodist(rlat,rlon,pp->rlat,pp->rlon,sp->name);
        if (dist < lodist) { lodist = dist; loid = oi; }
        else if (dist > Georange - 1) warn(0,"geo poi %u %s",oi,pp->name);
        else {
          hdist = geodist(rlat,rlon,rlat,pp->rlon,sp->name);
          if (hdist >= lodist) {
            if (dir) ol = geostopcnt; else or = geostopcnt;
          } else if (hdist > Georange - 1) warn(0,"geo poi %u %s",oi,pp->name);
        }
      }

    // info(0,"iter %u dir %u lodist %e vdist %e hdist %e al %u ar %u ol %u or %u",iter,dir,lodist,vdist,hdist,al,ar,ol,or);

      if (dir) {
        if (ar + 1 < geostopcnt) a = ++ar;
        else a = geostopcnt;
        if (or + 1 < geostopcnt) o = ++or;
        else o = geostopcnt;
      } else {
        if (al && al < geostopcnt) a = --al; else a = al = geostopcnt;
        if (ol && ol < geostopcnt) o = --ol; else o = ol = geostopcnt;
      }
      if ( (ar == geostopcnt && al == geostopcnt) || (or == geostopcnt && ol == geostopcnt) ) break;
      dir ^= 1;
    } // each iter

    if (loid == hi32) {
      nogeo++;
      warn(Iter,"no geocode match for %s in %u iters",sp->name,iter);
      continue;
    }
    pp = gstops + loid;
    sp->geondx = loid;
    if (*pp->tzname == 0) nogeo++;
    info(Iter|V0,"%s -> %s at %u %s",sp->name,pp->tzname,pp->id,pp->name);
  }
  info(CC0|Emp,"\ah%u from \ah%u stops without coords",nogeo,stopcnt);
  return 0;
}

static int samename(struct gtstop *sp1,struct gtstop *sp2)
{
  return (sp1->namelen == sp2->namelen && *sp1->name == *sp2->name && memeq(sp1->name,sp2->name,sp1->namelen));
}

static int chk4grp(struct gtstop *cstops,iadrbase *net0,struct gtstop *sp,ub4 ni,ub4 cntlim,double grplim,double axislim,int islat)
{
  double dist;
  ub4 nn,cnt = sp->nearcnt;
  struct gtstop *sp2,*spn;
  ub4 coloc = 0;
  int havelim = (grplim > 0.5);
  sp2 = cstops + ni;
  error_ne(sp2->group,hi32);

  if (cnt + 1 >= cntlim) return 1;

  ub4 pid = sp->pid;
  ub4 stn = 0;

  // tentative member if original parent, coloc or nearby
  if (pid == hi32 || pid != sp2->pid) {
    if (sp->ilat > sp2->ilat + 1 || sp->ilat + 1 < sp2->ilat
     || sp->ilon > sp2->ilon + 1 || sp->ilon + 1 < sp2->ilon) {
      if (no_grplink && rdiadr2(net0,sp->stopid,sp2->stopid)) return 0; // connected
      if (havelim) dist = geodist(sp->rlat,sp->rlon,sp2->rlat,sp2->rlon,sp->name);
      else dist = 1;
      if (dist > grplim) {
        if (islat) dist = geodist(sp->rlat,sp->rlon,sp2->rlat,sp->rlon,sp->name);
        else dist = geodist(sp->rlat,sp->rlon,sp->rlat,sp2->rlon,sp->name);
        return (dist > axislim);
      }
    } else coloc = 1;
  } else if (no_grplink && pid != hi32 && sp2->pid != hi32 && pid != sp2->pid) return 0; // different parent
  else if (pid != hi32 && pid == sp2->pid) stn = 1;

  ub4 nearpos;
  stn |= coloc;
  for (nearpos = 0; nearpos < cnt; nearpos++) { // add except dups
    nn = sp->nears[nearpos];
    if (nn == ni) return 0;
    if (no_grplink == 0) continue;
    spn = cstops + nn;
    if (stn == 0 && rdiadr2(net0,sp2->stopid,spn->stopid)) return 0; // connected
    if (havelim && stn == 0) {
      dist = geodist(sp->rlat,sp->rlon,spn->rlat,spn->rlon,sp->name);
      if (dist < stnlimit_f || ((samename(sp,spn) && dist < stnlimit3))) stn = 1;
    }
  }
  sp->nears[cnt++] = ni;
  sp->nears[cnt] = hi32;
  sp->nearcnt = cnt;
  sp->stncnt += stn;
  return 0;
}

static int mknearparents(struct gtstop *stops,ub4 stopcnt)
{
  struct gtstop *sp,*sp2;
  ub4 stop,stop2,pid = stopcnt,mrgcnt = 0;
  struct eta eta;
  double dist,rlat,rlon;
  ub4 ilat,ilon;
  ub4 istnlim = stnlimit * 100 * 10 * 10;

  info(0,"merging %u stops on nearlim %u",stopcnt,istnlim);

  for (stop = 0; stop < stopcnt; stop++) {
    sp = stops + stop;
    if (progress(&eta,"stop %u of %u merged %u %s",stop,stopcnt,mrgcnt,sp->name)) return 1;
    if (sp->isparent || sp->hasparent) continue;
    rlat = sp->rlat;
    rlon = sp->rlon;
    ilat = sp->ilat;
    ilon = sp->ilon;

    for (stop2 = 0; stop2 < stopcnt; stop2++) {
      if (stop == stop2) continue;
      sp2 = stops + stop2;
      if (sp2->isparent || sp2->hasparent) continue;

      if (ilat + istnlim < sp2->ilat || sp2->ilat + istnlim < ilat) continue;
      if (ilon + istnlim < sp2->ilon || sp2->ilon + istnlim < ilon) continue;

      dist = geodist(rlat,rlon,sp2->rlat,sp2->rlon,sp->name);
      if (dist > stnlimit_f) continue;
      // info(Noiter,"merge %s to %s",sp->name,sp2->name);
      mrgcnt++;
      sp->pid = sp2->pid = pid++;
      sp->hasparent = sp2->hasparent = 1;
      break;
    }
  }
  info(Emp|CC0,"%u stops merged on distance",mrgcnt);
  return 0;
}

static int rdstops(gtfsnet *net,const char *indir,const char *outdir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawstopcnt,stopcnt,stop2,stop = 0,rawstop = 0,plainstopcnt = 0;
  ub4 popcnt = net->geopopcnt;
  ub4 pstopcnt = 0;
  int rv;
  char *buf;
  ub4 len,linno,colno;
  ub4 n;
  char *val,*vals,*idval,*nameval,*inameval,*pfval,*tzval;
  ub2 nlen,inlen,idvlen,vlen,pfvlen,tzvlen,*vallens;
  ub4 *uvals,uval;
  ub4 valcnt,colcnt,valno;
  double lat,lon;
  ub4 stopid,rstopid,prestopid,prepstopid;
  ub4 linelen;
  ub4 linepos = 0;
  block *mem = &net->stopmem;
  block *emem = &net->estopmem;

  hash *hstops = net->stopids;
  hash *prestops = net->prestopids;

  double d2r = M_PI / 180;

  struct eta eta,eta2;

  oclear(eft);

  fmtstring(eft.mf.name,"%s/stops.%s",indir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,1,hi28);
  if (rv) return 1;

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  rawstopcnt = linecnt(fname,buf,len,1);

  if (rawstopcnt == 0) return warning(0,"%s is empty",fname);

  struct gtstop *sp,*sp2,*psp,*stops = alloc(rawstopcnt,struct gtstop,0,"ext ports",rawstopcnt);

  ub4 namemax = sizeof(sp->name) - 1;

  linelen = len;
  linelen += popcnt * (32 + prefixlen1); // gids
  error_ge(linelen,hi32);
  char *lines = mkblock(mem,linelen,char,Noinit,"gtfs tmp %u+%u stops, len \ah%u",rawstopcnt-1,popcnt,linelen);

  const char tab = '\t';

  ub4 stop_idpos,stop_codepos,stop_namepos,stop_descpos,stop_latpos,stop_lonpos,stop_locpos,parent_stapos,stop_platpos,stop_tzpos,stop_intnamepos;
  stop_idpos=stop_codepos=stop_namepos=stop_descpos=stop_latpos=stop_lonpos=stop_locpos=parent_stapos=stop_platpos=stop_tzpos=stop_intnamepos = hi32;

  sp = stops;

  vals = eft.vals;
  uvals = eft.uvals;

  colcnt = 0;
  ub4 uncons = 0;

  do {

    res = nextchar(&eft);

    switch(res) {
    case Newcmd:
      valcnt = colcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"stop_id")) stop_idpos = valno;
        else if (streq(val,"stop_code")) stop_codepos = valno;
        else if (streq(val,"stop_name")) stop_namepos = valno;
        else if (streq(val,"stop_name_int")) stop_intnamepos = valno;
        else if (streq(val,"stop_desc")) stop_descpos = valno;
        else if (streq(val,"stop_lat")) stop_latpos = valno;
        else if (streq(val,"stop_lon")) stop_lonpos = valno;
        else if (streq(val,"location_type")) stop_locpos = valno;
        else if (streq(val,"parent_station")) parent_stapos = valno;
        else if (streq(val,"platform_code")) stop_platpos = valno;
        else if (streq(val,"stop_timezone")) stop_tzpos = valno;
        else vrb0(0,"skipping column '%s'",val);
      }
      if (stop_idpos == hi32) return error(0,"%s: missing required column stopid",fname);
      if (stop_namepos == hi32) return error(0,"%s: missing required column stop_name",fname);
      if (stop_latpos == hi32) return error(0,"%s: missing required column stop_lat",fname);
      if (stop_lonpos == hi32) return error(0,"%s: missing required column stop_lon",fname);
      if (stop_locpos == hi32) info(0,"%s: no column location_type",fname);
      if (parent_stapos == hi32) info(0,"%s: no column parent_station",fname);
      break;

    case Newitem:

      if (progress(&eta,"reading stop %u of %u in %s",rawstop,rawstopcnt,fname)) return 1;
      rawstop++;

      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        vrb0(0,"line %u col %u val '%s'",linno,valno,val);
      }
      if (valcnt < 4 || valcnt + 2 < colcnt) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);
      else if (valcnt != colcnt) infocc(stop == 0,0,"row has %u cols, header %u",valcnt,colcnt);

      sp->id = stop;

// check parent first
      sp->isparent = 0;
      if (stop_locpos != hi32) {
        val = vals + stop_locpos * Collen;
        uval = uvals[stop_locpos];
        if (uval == 1) sp->isparent = 1;
      }

      idval = vals + stop_idpos * Collen;
      idvlen = vallens[stop_idpos];

//name
      nameval = vals + stop_namepos * Collen;
      nlen = vallens[stop_namepos];

      if (nlen > namemax) nlen = (ub2)truncutf8(nameval,namemax);

      if (stop_intnamepos != hi32) {
        inameval = vals + stop_intnamepos * Collen;
        inlen = vallens[stop_intnamepos];
        if (inlen > namemax) inlen = (ub2)truncutf8(inameval,namemax);

        if (nlen == 0) {
          nameval = inameval;
          nlen = inlen;
        }
      } else {
        inameval = nameval;
        inlen = 0;
      }
      if (nlen == 0 || *nameval == 0) {
        nameval = idval;
        nlen = idvlen;
      }
      if (nlen > namemax) nlen = (ub2)truncutf8(nameval,namemax);

// id
      val = vals + stop_idpos * Collen;
      vlen = vallens[stop_idpos];

      if (vlen == 0) return parserr(FLN,fname,linno,colno,"no id for stop %s",nameval);

      rstopid = uvals[stop_idpos];

      prestopid = gethash(prestops,val,vlen,rstopid);
      if (prestopid == hi32) {
        if (strict) return parserr(FLN,fname,linno,colno,"unknown stop %s %s",val,nameval);
        else info(Iter,"line %u: omitting filtered stop %s %s",linno,val,nameval);
        break;
      }
      stopid = gethash(hstops,val,vlen,rstopid);
      if (sp->isparent == 0 && stopid == hi32) {
        if (strict) parsewarn(FLN,fname,linno,colno,"unknown stop %s %s",val,nameval);
        uncons++;
        infocc(show_omitstop,Iter,"line %u: omitting unreferenced stop %s %u %s",linno,val,rstopid,nameval);
        break;
      } else if (sp->isparent == 1 && stopid != hi32) {
        warn(0,"line %u: parent stop %s is referenced",linno,val);
      }

      sp->gidofs = linepos;

      bound(mem,linepos + vlen + 1,char);
      linepos = (ub4)addcol(lines,linepos,val,vlen,tab,1);
      sp->gidlen = linepos - sp->gidofs - 1;

      sp->stopid = stopid;
      sp->prestopid = prestopid;

// code
      if (stop_codepos != hi32) {
        val = vals + stop_codepos * Collen;
        vlen = vallens[stop_codepos];
        sp->codeofs = linepos;
        sp->codelen = vlen;
        bound(mem,linepos + vlen + 1,char);
        linepos = (ub4)addcol(lines,linepos,val,vlen,tab,0);
      }

// loc
      if (stop_locpos != hi32) {
        val = vals + stop_locpos * Collen;
        vlen = vallens[stop_locpos];
        if (vlen == 0) uval = 0;
        else if (vlen == 4 && streq(val,"NULL")) uval = 0;
        else uval = uvals[stop_locpos];
        if (uval == hi32) return parserr(FLN,fname,linno,colno,"location_type %s not numerical",val);
        else if (uval > 1) parsewarn(FLN,fname,linno,colno,"location_type %u not 0 or 1",uval);

        if (uval) {
          sp->isparent = 1;
          pstopcnt++;
        }
      }

// parent
      if (parent_stapos != hi32) {
        val = vals + parent_stapos * Collen;
        vlen = vallens[parent_stapos];
        rstopid = uvals[parent_stapos];

        if (vlen) {
          prepstopid = gethash(prestops,val,vlen,rstopid);
          if (prepstopid == hi32) {
            parsewarn(FLN,fname,linno,colno,"stop %s has unknown parent %s",nameval,val);
            vlen = 0;
          }
        } else prepstopid = hi32;
        if (vlen) {
          if (sp->isparent) parsewarn(FLN,fname,linno,colno,"parent stop with parent");
          sp->hasparent = 1;
          sp->parentofs = linepos;
          sp->parentlen = vlen;
          sp->prepstopid = prepstopid;
          bound(mem,linepos + vlen + 1,char);
          linepos = (ub4)addcol(lines,linepos,val,vlen,tab,1);
        }
      }
      if (sp->hasparent == 0 && sp->isparent == 0) plainstopcnt++;

// platform: concat to name
      if (stop_platpos != hi32) {
        pfval = vals + stop_platpos * Collen;
        pfvlen = vallens[stop_platpos];
      } else { pfvlen = 0; pfval = NULL; }

//name
      if (nlen && pfvlen && strstr(nameval,pfval) == NULL) {
        vlen = (ub2)fmtstring(sp->name,"%.256s %.32s",nameval,pfval);
        nameval = sp->name;
      } else if (nlen) {
        memcpy(sp->name,nameval,nlen);
      }
      sp->namelen = nlen;

      if (inlen && pfvlen && strstr(inameval,pfval) == NULL) {
        vlen = (ub2)fmtstring(sp->iname,"%.256s %.32s",inameval,pfval);
        inameval = sp->iname;
      } else if (inlen) {
        memcpy(sp->iname,inameval,inlen);
      }
      sp->inamelen = inlen;

//lat
      val = vals + stop_latpos * Collen;
      vlen = vallens[stop_latpos];
      if (vlen && *val == ' ') { val++; vlen--; }

      if (vlen == 0 || str2dbl(val,vlen,&lat)) return parserr(FLN,fname,linno,colno,"stop %s cannot convert lat coord '%.*s'",sp->name,vlen,val);

      if (lat <= -90.0 || lat >= 90.0) {
        parsewarn(FLN,fname,linno,colno,"stop %s has invalid latitude %s",sp->name,val);
        lat = 0;
      }

      sp->lat = lat;
      sp->rlat = lat * d2r;
      sp->ilat = geo2int(lat,90,nameval);
      minlat = min(minlat,lat);
      maxlat = max(maxlat,lat);

//lon
      val = vals + stop_lonpos * Collen;
      vlen = vallens[stop_lonpos];
      if (vlen && *val == ' ') { val++; vlen--; }

      if (vlen == 0 || str2dbl(val,vlen,&lon)) return parserr(FLN,fname,linno,colno,"stop %s cannot convert lon coord '%.*s'",sp->name,vlen,val);

      if (lon <= -180.0 || lon >= 180.0) {
        parsewarn(FLN,fname,linno,colno,"stop %s has invalid longitude %s",sp->name,val);
        lon = 0;
      }

      sp->lon = lon;
      sp->ilon = geo2int(lon,180,nameval);
      sp->rlon = lon * d2r;
      minlon = min(minlon,lon);
      maxlon = max(maxlon,lon);

// desc
      if (stop_descpos != hi32) {
        val = vals + stop_descpos * Collen;
        vlen = vallens[stop_descpos];

        sp->descofs = linepos;
        sp->desclen = vlen;
        bound(mem,linepos + vlen + 1,char);
        linepos = (ub4)addcol(lines,linepos,val,vlen,'\n',0);
      }

// timezone todo
      if (stop_tzpos != hi32) {
        tzval = vals + stop_tzpos * Collen;
        tzvlen = vallens[stop_tzpos];
      } else { tzvlen = 0; tzval = NULL; }

      if (tzvlen == 0) {
      x  tzvlen = defagencytzlen;
        tzval = defagencytz;
        // info(0,"%s tz '%.*s'",nameval,tzvlen,tzval);
      }
      tzvlen = min(tzvlen,sizeof(sp->tzname) - 1);
      sp->tznamlen = tzvlen;
      if (tzvlen) memcpy(sp->tzname,tzval,tzvlen);
      sp->geondx = hi32;
      sp->valid = 1;
      sp++;
      stop++;
      error_gt(stop,rawstopcnt,0);

     break;  // newitem

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  stopcnt = stop;
  userstopcnt = plainstopcnt + pstopcnt;
  info(0,"%u stops from %u lines %u parents",stopcnt,rawstopcnt,pstopcnt);
  infocc(uncons,0,"%u unconnected stop\as omitted",uncons);

  if (stopcnt == 0) return error(0,"0 stops from %u lines",rawstopcnt);

  error_ge(pstopcnt,stopcnt);

  ub4 *preids2stop = alloc(rawstopcnt,ub4,0,"ext map",stopcnt);
  ub4 pstop;

  // mark original parents
  for (stop = 0; stop < stopcnt; stop++) {
    sp = stops + stop;
    prestopid = sp->prestopid;
    error_ge(prestopid,rawstopcnt);
    preids2stop[prestopid] = stop;
  }
  for (stop = 0; stop < stopcnt; stop++) {
    sp = stops + stop;
    sp->pid = hi32;
    if (sp->hasparent == 0) continue;
    prepstopid = sp->prepstopid;
    error_ge(prepstopid,rawstopcnt);
    pstop = preids2stop[prepstopid];
    vrb0(0,"stop %s parent %u->%u",sp->name,prepstopid,pstop);
    sp->pid = pstop;
  }

  if (grouplimit && stnlimit && mknearparents(stops,stopcnt)) return 1;

  // set parents aside
  struct gtstop *pstops = NULL;
  if (pstopcnt) pstops = alloc(pstopcnt,struct gtstop,0,"ext pports",pstopcnt);
  ub4 pid,*s2pstop = alloc(stopcnt,ub4,0,"ext pports",stopcnt);

  psp = pstops;
  pid = 0;
  for (stop = 0; stop < stopcnt; stop++) {
    sp = stops + stop;
    pstop = sp->pid;
    if (sp->isparent == 0) continue;
    errorcc(psp >= pstops + pstopcnt,Exit,"pstopcnt %u overflow",pstopcnt);
    if (pstop < stopcnt) s2pstop[pstop] = pid;
    *psp++ = *sp;
    pid++;
  }

  // optionally let child stops inherit parent name
  for (stop = 0; stop < stopcnt; stop++) {
    sp = stops + stop;
    if (useparentname == 0 || (sp->isparent == 0 && sp->hasparent == 0)) continue;

    if (sp->hasparent) {
      pid = sp->pid;
      if (pid == hi32) { warn(0,"missing parent for %s",sp->name); continue; }
      if (pid >= stopcnt) continue;
      pstop = s2pstop[pid];
      error_ge(pstop,pstopcnt);
      psp = pstops + pstop;
      sp->pnameref = psp->name;
      sp->pnamelen = psp->namelen;
    }
  }

  ub4 cstopcnt_feed = stopcnt - pstopcnt;
  ub4 cstopcnt = cstopcnt_feed + popcnt;
  info(0,"prepare grouping for %u+%u stops within \ag%u",cstopcnt_feed,popcnt,grouplimit);

  struct gtstop *csp,*cstops = alloc(cstopcnt,struct gtstop,0,"ext cports",cstopcnt);
  struct geostop *gp,*gstops = net->geostops;
  ub4 geostopcnt = net->geostopcnt;

  ub4 cstop = 0;
  csp = cstops;
  for (stop = 0; stop < stopcnt; stop++) {
    sp = stops + stop;
    if (sp->isparent) continue;
    error_ge(cstop,cstopcnt_feed);
    *csp = *sp;
    csp->id = cstop;
    csp++;
    cstop++;
  }
  error_ne(cstop,cstopcnt_feed);

  sassert(sizeof(csp->name) >= sizeof(gp->name),"csp.name >= gp.name");
  char tmpbuf[128];

  // add geo stops if any
  for (stop = 0; stop < geostopcnt; stop++) {
    gp = gstops + stop;
    if (gp->isplace == 0 || gp->pop < poplimit) continue;
    error_ge(cstop - cstopcnt_feed,popcnt);
    memcpy(csp->name,gp->name,gp->namelen);
    csp->namelen = gp->namelen;
    csp->tznamlen = min(gp->tzlen,sizeof(csp->tzname)-1);
    memcpy(csp->tzname,gp->tzname,csp->tznamlen);

    csp->ilat = gp->ilat;
    csp->lat = gp->lat;
    csp->rlat = gp->rlat;
    csp->ilon = gp->ilon;
    csp->lon = gp->lon;
    csp->rlon = gp->rlon;

    csp->gidofs = linepos;

    bound(mem,linepos + csp->gidlen + 1,char);
    vlen = (ub2)fmtstring(tmpbuf,"%s-%u-%u",geomagic,cstop,gp->pop);
    linepos = (ub4)addcol(lines,linepos,tmpbuf,vlen,tab,1);
    csp->gidlen = linepos - csp->gidofs - 1;

    csp->id = cstop++;
    csp->pid = hi32;
    csp->valid = 1;
    csp->geondx = stop;
    csp++;
  }
  error_ne(cstop,cstopcnt);

  ub4 cnt,hicnt2 = 0,hicnt = 0,histncnt,histop = 0,histnstop = hi32,sumcnt = 0,colocnt = 0;
  double grplim = grouplimit;
  ub4 ilatmax = 0,ilonmax = 0;
  ub4 ilatmin = hi32,ilonmin = hi32;

  for (stop = 0; stop < cstopcnt; stop++) {
    sp = cstops + stop;
    error_z(sp->valid,stop);
    sp->group = hi32;
    sp->iparent = hi32;
    ilatmin = min(ilatmin,sp->ilat);
    ilatmax = max(ilatmax,sp->ilat);
    ilonmin = min(ilonmin,sp->ilon);
    ilonmax = max(ilonmax,sp->ilon);
    sp->rlat = sp->lat * d2r;
    sp->rlon = sp->lon * d2r;
  }

  info(V0,"prepare %u stop clustering",cstopcnt);

  mkgeosort(net,cstopcnt,cstops);

  ub4 ilat,*latsort = net->latsort;
  ub4 ilon,*lonsort = net->lonsort;
  ub4 a,*latsortidx = net->latsortidx;
  ub4 o,*lonsortidx = net->lonsortidx;
  ub4 ar,or,al,ol,ni,nearpos,cntlim;
  ub4 iparentcnt,iparent = 0,prviparent;

  ub4 *himap = alloc(cstopcnt,ub4,0,"ext map",cstopcnt);

  infocc(grouplimit,0,"cluster %u stops on limit %.2f",cstopcnt,grplim);

  cntlim = min(Nearstop-1,cstopcnt) - 1;

  ub4 *as = alloc(cstopcnt,ub4,0,"grp",cstopcnt);
  ub4 *os = alloc(cstopcnt,ub4,0,"grp",cstopcnt);

  for (stop = 0; stop < cstopcnt; stop++) {
    sp = cstops + stop;
    ilat = sp->ilat; ilon = sp->ilon;

    a = bsearch4(latsort,cstopcnt,ilat,FLN,"lat");
    o = bsearch4(lonsort,cstopcnt,ilon,FLN,"lon");
    error_ge(a,cstopcnt);
    error_ge(o,cstopcnt);
    as[stop] = a;
    os[stop] = o;
  }

  iadrbase *net0 = &net->net0;

  ub8 *subsort = alloc(cstopcnt,ub8,0,"subsort",0);

  double axislim = max(grplim,20) * 1.5;
  ub4 grp,subndx,subcnt = 0;
  ub4 iter = 0;

  do {

    if (progress(&eta,"group %u of max %u cur %u sum %u iters %u",iparent,cstopcnt,hicnt2,sumcnt,iter++)) return 1;

    hicnt = 1; histncnt = 0; histop = histnstop = hi32;

    info(0,"iter %u group %u of max %u cur %u sum %u done %u",iter,iparent,cstopcnt,hicnt2,sumcnt,subcnt);

    for (stop = 0; stop < cstopcnt; stop++) {
      sp = cstops + stop;
    }
    for (stop = 0; stop < cstopcnt; stop++) {

      if (grplim > 40 && progress(&eta2,"  stop %u of %u cur %u",stop,cstopcnt,hicnt)) return 1;

      if (himap[stop]) continue;
      sp = cstops + stop;
      error_ne(sp->iparent,hi32);

      a = as[stop];
      o = os[stop];

      ar = a;
      or = o;
      al = a + 1;
      ol = o + 1;
      cnt = sp->nearcnt = 1;
      sp->stncnt = 0;
      sp->nears[0] = stop;

      // determine range
      while (ar < cstopcnt) {
        ni = latsortidx[ar++];
        error_ge(ni,cstopcnt);
        if (himap[ni]) continue;
        if (chk4grp(cstops,net0,sp,ni,cntlim,grplim,axislim,1)) break;
      }

      while (al) {
        ni = latsortidx[--al];
        if (himap[ni]) continue;
        if (chk4grp(cstops,net0,sp,ni,cntlim,grplim,axislim,1)) break;
      }

      while (or < cstopcnt) {
        ni = lonsortidx[or++];
        error_ge(ni,cstopcnt);
        if (himap[ni]) continue;
        if (chk4grp(cstops,net0,sp,ni,cntlim,grplim,axislim,0)) break;
      }

      while (ol) {
        ni = lonsortidx[--ol];
        error_ge(ni,cstopcnt);
        if (himap[ni]) continue;
        if (chk4grp(cstops,net0,sp,ni,cntlim,grplim,axislim,0)) break;
      }

      cnt = sp->nearcnt;

      // mark colocs
      if (iter == 1) {
        for (nearpos = 1; nearpos < cnt; nearpos++) {
          ni = sp->nears[nearpos];
          error_gt(ni,cstopcnt,stop);
          sp2 = cstops + ni;
          if (sp->coloc == 0 && sp->ilat < sp2->ilat + 2 && sp->ilat + 2 > sp2->ilat
              && sp->ilon < sp2->ilon + 2 && sp->ilon + 2 > sp2->ilon) {
            infocc(sp->coloc == 0 && show_coloc && !canonin && strcmp(sp->name,sp2->name),Iter,"%s and %s colocated",sp->name,sp2->name);
            error_ge(colocnt,cstopcnt);
            if (sp2->coloc == 0) { sp->coloc = 1; colocnt++; }
          }
        }
        if (cnt == 1) himap[stop] = __LINE__;
      }

      if (cnt > hicnt) { hicnt = cnt; histop = stop; }
      if (sp->stncnt > histncnt) { histncnt = sp->stncnt; histnstop = stop; }

      if (cnt + 1 >= cntlim) {
        warncc(iter == 1 && cntlim > 3,Iter|Emp,"stop %u group size limit %u reached %s %f,%f",stop,cnt,sp->iname,sp->lat,sp->lon);
      }

    } // each stop

    infocc(iter == 1,CC0,"coloc %u",colocnt);

    if (histop == hi32 && (histncnt == hi32 || histncnt < 2)) break;
    hicnt2 = hicnt;

    // remove largest station group or plain group from set
    if (no_grplink && histnstop < hi32 && histncnt > 1) {
      histop = histnstop;
      error_ge(histop,cstopcnt);
      error_nz(himap[histop],histop);
      sp = cstops + histop;
    } else {
      error_ge(histop,cstopcnt);
      error_nz(himap[histop],histop);
      sp = cstops + histop;
    }
    cnt = sp->nearcnt;
    info(Iter,"assign group %u cnt %u stncnt %u %s",iparent,cnt,sp->stncnt,sp->name);

    warncc(sp->enearcnt,0,"stop %u group %u iter %u.%u",histop,sp->group,sp->iter,sp->subiter);
    error_nz(sp->enearcnt,histop);

    error_ne(sp->iparent,hi32);

    sp->iparent = iparent;
    sp->group = histop;
    sp->iter = iter;
    sp->subiter = hi32;
    himap[histop] = __LINE__;
    for (nearpos = 1; nearpos < cnt; nearpos++) {
      stop2 = sp->nears[nearpos];
      error_ge(stop2,cstopcnt);
      sp2 = cstops + stop2;
      error_nz(himap[stop2],stop2); // todo vbb  m=30 sample=20
      if (himap[stop2]) {
        warn(0,"line %u iparent %u grp %u stop2 %u already in %u at %u.%u",himap[stop2],iparent,histop,stop2,sp2->group,sp2->iter,sp2->subiter);
        continue;
      }
      error_ne(sp2->iparent,hi32);
      himap[stop2] = __LINE__;
      sp2->group = histop;
      sp2->iter = iter;
      sp2->subiter = hi32;
      error_nz(sp2->enearcnt,stop2);
      sp2->enearcnt = cnt;
    }
    sp->enearcnt = cnt;
    sumcnt += cnt;
    iparent++;

    // remove 2-member groups if no shared members
    prviparent = iparent;
    for (stop = 0; stop < cstopcnt; stop++) {
      if (himap[stop]) continue;
      sp = cstops + stop;
      cnt = sp->nearcnt;
      if (cnt != 2) continue;
      // if (sp->stncnt) continue;
      stop2 = sp->nears[1];
      error_eq(stop2,hi32);
      error_eq(stop,stop2);
      if (himap[stop2]) continue;
      sp2 = cstops + stop2;
      if (sp2->nearcnt != 2) continue;
      if (sp2->iparent != hi32) continue;
      if (sp2->nears[1] != stop) continue;
      sp->iparent = iparent++;
      sp->group = sp2->group = stop;
      error_nz(sp->enearcnt,stop);
      error_nz(sp2->enearcnt,stop2);
      sp->enearcnt = sp2->enearcnt = 2;
      sp->iter = sp2->iter = iter;
      sp->subiter = sp2->subiter = __LINE__;
      himap[stop] = himap[stop2] = __LINE__;
      sumcnt += 2;
    }
    if (iparent != prviparent) continue;

    // remove subsequent groups if no shared members
    // proceed on sorted by station / coloc first, then on plain size
    histncnt = 0;
    for (stop = 0; no_grplink && stop < cstopcnt; stop++) {
      if (himap[stop]) continue;
      sp = cstops + stop;
      cnt = sp->nearcnt;
      if (cnt < 3) continue;
      histncnt = max(histncnt,sp->stncnt);
    }

    subcnt = 0;
    for (stop = 0; stop < cstopcnt; stop++) {

      // if (progress(&eta2,"stop %u of %u sum %u iter %u",stop,cstopcnt,sumcnt,iter)) return 1;

      if (himap[stop]) continue;
      sp = cstops + stop;
      cnt = sp->nearcnt;
      if (cnt < 3) continue;
      if (histncnt && sp->stncnt == 0) continue;

      for (nearpos = 0; nearpos < cnt; nearpos++) {
        stop2 = sp->nears[nearpos];
        error_ge(stop2,cstopcnt);
        if (himap[stop2])  break;
      }
      if (nearpos < cnt) continue; // shared
      if (histncnt) cnt = sp->stncnt;
      subsort[subcnt++] = ((ub8)cnt << 32) | stop;
    }

    if (subcnt == 0) continue;

    if (subcnt > 1) sort8(subsort,subcnt,FLN,"sub");

    for (subndx = 1; subndx <= subcnt; subndx++) {

      stop = subsort[subcnt - subndx] & hi32;
      error_ge(stop,cstopcnt);

      // if (progress(&eta2,"stop %u of %u sum %u iter %u",stop,cstopcnt,sumcnt,iter)) return 1;

      if (himap[stop]) continue;
      sp = cstops + stop;
      cnt = sp->nearcnt;
      if (cnt < 3) continue;

      for (nearpos = 0; nearpos < cnt; nearpos++) {
        stop2 = sp->nears[nearpos];
        error_ge(stop2,cstopcnt);
        if (himap[stop2])  break;
      }
      if (nearpos < cnt) continue; // shared

      sp->iparent = iparent;
      sp->group = stop;
      sp->iter = iter;
      sp->subiter = __LINE__;
      himap[stop] = __LINE__;
      for (nearpos = 1; nearpos < cnt; nearpos++) {
        stop2 = sp->nears[nearpos];
        sp2 = cstops + stop2;
        error_nz(himap[stop2],stop2);
        himap[stop2] = __LINE__;
        sp2->group = stop;
        sp2->iter = iter;
        sp2->subiter = sp->subiter;
        sp2->enearcnt = cnt;
      }
      sp->enearcnt = cnt;
      sumcnt += cnt;
      iparent++;
    }

    error_ge(iparent,cstopcnt);

    // check
    for (stop = 0; stop < cstopcnt && cstopcnt < 50000; stop++) {
      sp = cstops + stop;
      grp = sp->group;
      if (grp == hi32) continue;
      psp = cstops + grp;
      error_eq_cc(psp->iparent,hi32,"stop %u grp %u line %u %u",stop,grp,himap[grp],himap[stop]);
    }
    for (stop = 0; stop < cstopcnt && cstopcnt < 50000; stop++) {
      psp = cstops + stop;
      if (psp->iparent == hi32) continue;
      cnt = psp->enearcnt;
      if (cnt < 2) continue;
      for (nearpos = 0; nearpos < cnt; nearpos++) {
        stop2 = psp->nears[nearpos];

        if (stop2 == hi32) return error(0,"stop %u no item at %u of %u",stop,nearpos,cnt);
        sp2 = cstops + stop2;
        if (sp2->group == hi32) {
          return error(0,"no group for stop %u grp %u member %u %u %u",stop,psp->group,stop2,himap[stop2],psp->subiter); // todo toscana m=40
        }
        if (himap[stop2] == 0) return error(0,"grp %u stop %u not marked %u",psp->group,stop2,psp->subiter);
      }
    }

  } while (iter < iterlimit);

  warncc(iter == iterlimit,Emp,"group limit %u reached",iterlimit);

  iparentcnt = iparent;
  info(0,"done cluster %u stops, %u groups %u iters",cstopcnt,iparent,iter);

  colocnt /= 2; // counted in both directions

  plainstopcnt = cstopcnt - sumcnt;
  planstopcnt = plainstopcnt + iparentcnt;
  ub4 estopcnt = cstopcnt + iparentcnt;
  userstopcnt -= min(colocnt,userstopcnt);
  info(0,"stops %u plain %u parent %u total %u planning %u user %u coloc",plainstopcnt,iparentcnt,estopcnt,planstopcnt,userstopcnt,colocnt);

  lookupstops(net,cstops,cstopcnt_feed);

  ub4 elinelen = 0;
  ub4 iparentlen = 8 + 6 + 6;
  ub4 geopreclen = 6 + 1 + 1 + 4;
  ub4 pos,group;

  infocc(plainstopcnt > 2000,0,"writing %u plain stops",plainstopcnt);

  for (stop = 0; stop < cstopcnt; stop++) {
    sp = cstops + stop;
    len = sp->gidlen + sp->codelen + sp->namelen + sp->inamelen + sp->desclen;
    len += geopreclen * 2;
    if (sp->group != hi32) len += iparentlen;
    len += 32; // tz
    len += 20;
    if (sp->iparent != hi32) len += (len + iparentlen);
    elinelen += (len + 8);
  }

  char *elines = net->stoplines = mkblock(emem,elinelen,char,Noinit,"gtfs %u stops, len %u",estopcnt,elinelen);

  // stops
  pos = 0;
  char *pfxend;
  ub4 pfxlen,geondx,patchlen;
  char idbuf[256];

  char patbuf[256];
  int patchfd = -1;

  if (patch_tz) patchfd = filecreate("patch.sed",1);

  for (stop = 0; stop < cstopcnt; stop++) {
    sp = cstops + stop;

    geondx = sp->geondx;
    gp = (geondx == hi32 ? NULL : gstops + geondx);

    error_z_cc(sp->gidlen,"empty id for stop %s",sp->name);

    fmtstring(idbuf,"%.*s",sp->gidlen,lines + sp->gidofs);

    // id,code,loctype
    n = mysnprintf(elines,pos,elinelen,"%s\t%.*s\t0\t",idbuf,sp->codelen,lines + sp->codeofs);
    pos += n;
    error_ge(pos,elinelen);

    pfxend = strrchr(idbuf,'/');
    if (pfxend) pfxlen = (ub4)(pfxend - idbuf);
    else pfxlen = 0;
    error_ge(pfxlen,64);

    // parent
    group = sp->group;
    if (group != hi32) {
      psp = cstops + group;
      if (*psp->parentname == 0) {
        if (prefixlen) fmtstring(psp->parentname,"%s/%u-%u-%u-%u-c8gaTX73",prefix,group,psp->nearcnt,psp->stncnt,psp->subiter);
        else fmtstring(psp->parentname,"%.*s/%u-%u-%u-%u-c8gaTX73",pfxlen,idbuf,group,psp->nearcnt,psp->stncnt,psp->subiter);
      }
      n = mysnprintf(elines,pos,elinelen,"%s",psp->parentname);
      error_z(n,stop);
      pos += n;
    } else {
      error_ne(sp->iparent,hi32);
    }
    elines[pos++] = '\t';
    error_ge(pos,elinelen);

    // name
    pos += mysnprintf(elines,pos,elinelen,"%.*s\t",sp->namelen,sp->name);
    pos += mysnprintf(elines,pos,elinelen,"%.*s\t",sp->inamelen,sp->iname);

    // lat,lon
    pos += mysnprintf(elines,pos,elinelen,"%f\t%f\t",sp->lat,sp->lon);

    // desc
    if (sp->desclen) {
      pos += mysnprintf(elines,pos,elinelen,"%.*s\t",sp->desclen,lines + sp->descofs);
      bound(emem,pos,char);
      error_ge(pos + 2,elinelen);
    } else elines[pos++] = '\t';

    // timezone
    n = sp->tznamlen;
    if (gp && gp->tzlen) {
      if (n) {
        if (n != gp->tzlen || memcmp(sp->tzname,gp->tzname,n)) {
          warn(0,"stop %u %s timezone %s, geonames %s %f,%f",stop,sp->name,sp->tzname,gp->tzname,sp->lat,sp->lon);
          if (patchfd != -1) {
            patchlen = fmtstring(patbuf,"/%.*s/ s,\\t%s$,\\t%s,\n",sp->codelen,lines + sp->codeofs,sp->tzname,gp->tzname);
            filewrite(patchfd,patbuf,patchlen,"patch.sed");
          }
        }
      }
      pos += mysnprintf(elines,pos,elinelen,"%.*s\n",gp->tzlen,gp->tzname);
    } else if (n) {
      pos += mysnprintf(elines,pos,elinelen,"%.*s\n",n,sp->tzname);
    }
    bound(emem,pos,char);
    error_ge(pos + 2,elinelen);
  }
  if (patchfd != -1) fileclose(patchfd,"patch.sed");

  // center parent into members
#if 0
  info(0,"center %u parents",iparentcnt);
  double maxdist,lomax;
  ub4 lomaxstop,nearpos2;
  for (stop = 0; stop < cstopcnt; stop++) {
    sp = cstops + stop;
    if (sp->iparent == hi32) continue;
    cnt = sp->enearcnt;
    if (cnt < 2) continue;
    lomax = 1e+10; lomaxstop = hi32;
    for (nearpos = 0; nearpos < cnt; nearpos++) {
      stop2 = sp->nears[nearpos];
      maxdist = -1;
      warncc(stop2 == hi32,0,"stop %u cnt %u,%u hi at %u",stop,cnt,sp->nearcnt,nearpos);
      if (stop2 == hi32) continue;
      sp2 = cstops + stop2;
      if (sp2->iter != sp->iter || sp2->subiter != sp->subiter) {
        warn(0,"parent %u grp %u cnt %u iter %u.%u stop %u %u.%u",sp->iparent,sp->group,cnt,sp->iter,sp->subiter,stop2,sp2->iter,sp2->subiter); // todo
        continue;
      }
      if (sp2->group != sp->group) {
        warn(0,"parent %u grp %u cnt %u stop %u has grp %u",sp->iparent,sp->group,cnt,stop2,sp2->group);
        continue;
      }
      if (sp2->latlen == 0 || sp2->lonlen == 0) continue;

      for (nearpos2 = 0; nearpos2 < cnt; nearpos2++) {
        if (nearpos2 == nearpos) continue;
        stop3 = sp->nears[nearpos2];
        error_eq(stop2,stop3);
        sp3 = cstops + stop3;
        if (sp2->ilat == sp3->ilat && sp2->ilon == sp3->ilon) continue;
        dist = geodist(sp2->rlat,sp2->rlon,sp3->rlat,sp3->rlon,sp2->name);
        warncc(dist > 1e7,0,"%s to %s",sp2->name,sp3->name);
        maxdist = max(maxdist,dist);
      }
      if (maxdist > 0 && maxdist < lomax) { lomax = maxdist; lomaxstop = stop2; }
    }
    if (lomaxstop != hi32) {
      sp2 = cstops + lomaxstop;
      sp->lat = sp2->lat;
      sp->lon = sp2->lon;
    }
  }
#endif

  infocc(iparentcnt > 2000,0,"writing %u parent stops",iparentcnt);

  // inferred parents
  for (stop = 0; stop < cstopcnt; stop++) {
    sp = cstops + stop;
    if (sp->iparent == hi32) continue;
    geondx = sp->geondx;
    gp = (geondx == hi32 ? NULL : gstops + geondx);

    error_z_cc(*sp->parentname,"stop %u grp %u iparent %u",stop,sp->group,sp->iparent);

    pos += mysnprintf(elines,pos,elinelen,"%s\t%.*s\t1\t\t",sp->parentname,sp->codelen,lines + sp->codeofs);

    if (sp->pnamelen == 0) pos += mysnprintf(elines,pos,elinelen,"%.*s\t",sp->namelen,sp->name);
    else pos += mysnprintf(elines,pos,elinelen,"%.*s\t",sp->pnamelen,sp->pnameref);
    pos += mysnprintf(elines,pos,elinelen,"%.*s\t",sp->inamelen,sp->iname);

    pos += mysnprintf(elines,pos,elinelen,"%f\t%f\t",sp->lat,sp->lon);
    if (sp->desclen) pos += mysnprintf(elines,pos,elinelen,"%.*s\t",sp->desclen,lines + sp->descofs);
    else elines[pos++] = '\t';
    if (gp && gp->tzlen) pos += mysnprintf(elines,pos,elinelen,"%.*s\n",gp->tzlen,gp->tzname);
    else pos += mysnprintf(elines,pos,elinelen,"%.*s\n",defagencytzlen,defagencytz);
    bound(emem,pos,char);
    error_ge(pos + 20,elinelen);
  }

  net->stopcnt = estopcnt;
  net->stoplinepos = pos;

  if (noportnet) return 0;

  // network map
  char netname[256];

  ub4 bspos,binstoplen = cstopcnt * 2 + 2;
  ub4 *binstops = alloc(binstoplen,ub4,0,"net",0);

  binstops[0] = cstopcnt;
  binstops[1] = geoscale;
  bspos = 2;

  for (stop = 0; stop < cstopcnt; stop++) {
    sp = cstops + stop;
    binstops[bspos++] = sp->ilat;
    binstops[bspos++] = sp->ilon;
  }

  fmtstring(netname,"%s/network-ports.bin",outdir);

  info(0,"writing %u stops to %s",cstopcnt,netname);
  if (writefile(netname,(char *)binstops,binstoplen * sizeof(ub4))) return 1;

  if (*netsuffix == 0) return info(0,"no network map for %s",outdir);

  // original single json
  elinelen = (plainstopcnt + iparentcnt) * 14 + 6;
  elinelen += 64;

  char *latlines = alloc(elinelen,char,0,"network",plainstopcnt + iparentcnt);
  char *lonlines = alloc(elinelen,char,0,"network",plainstopcnt + iparentcnt);
  char *cntlines = alloc(elinelen,char,0,"network",plainstopcnt + iparentcnt);

  ub4 latpos = 0,lonpos = 0,cntpos = 0;
  char *nlsepa,*sepa = (char *)"";
  ub4 itemcnt = 0;

  ub4 ilatrange = max(ilatmax - ilatmin,1);
  ub4 ilonrange = max(ilonmax - ilonmin,1);
  ub8 igridlat,igridlon;

  ub8 igeogridlen,igridpos,grid2 = netgrid * netgrid;
  ub8 igeoscale = 0;
  ub4 netskiprng = 0,netskipgrid = 0;

  do {
    igeoscale++;
    igeogridlen = ((ub8)ilatrange * ilonrange) / (igeoscale * igeoscale);
    vrb0(0,"grid \ah%lu scale %lu",igeogridlen,igeoscale);
  } while (igeogridlen > grid2);

  ub4 *igeogrid = alloc(igeogridlen,ub4,0,"network",(ub4)igeogridlen);

  for (stop = 0; stop < cstopcnt && itemcnt < 10000; stop++) {
    sp = cstops + stop;
    if (sp->iparent == hi32 && sp->group != hi32) continue; // only plains and inferreds

    igridlat = (sp->ilat - ilatmin) / igeoscale;
    igridlon = (sp->ilon - ilonmin) / igeoscale;
    igridpos = igridlat * (ilonrange / igeoscale) + igridlon;
    if (igridpos >= igeogridlen) { netskiprng++; continue; }
    if (igeogrid[igridpos] > 4) { netskipgrid++; continue; }
    igeogrid[igridpos]++;

    itemcnt++;
    nlsepa = (itemcnt & 0xf) ? (char *)"" : (char *)"\n ";

    // lat
    n = mysnprintf(latlines,latpos,elinelen,"%s%f%s",sepa,sp->lat,nlsepa);
    latpos += n;
    error_ge(latpos,elinelen);

    // lon
    n = mysnprintf(lonlines,lonpos,elinelen,"%s%f%s",sepa,sp->lon,nlsepa);
    lonpos += n;
    error_ge(lonpos,elinelen);

    // cnt
    if (sp->iparent != hi32) {
      cnt = sp->enearcnt;
    } else cnt = 1;
    n = mysnprintf(cntlines,cntpos,elinelen,"%s%u%s",sepa,cnt,nlsepa);
    cntpos += n;
    sepa = (char *)",";
  }

  info(0,"%u items, %u gridded, %u ranged",itemcnt,netskipgrid,netskiprng);

  elinelen = latpos + lonpos + cntpos + 256;
  char *netlines = alloc(elinelen,char,0,"network",plainstopcnt + iparentcnt);

  n = mysnprintf(netlines,0,elinelen,"{\n \"lats\":[%s],\n",latlines);
  pos = n;
  n = mysnprintf(netlines,pos,elinelen," \"lons\":[%s],\n ",lonlines);
  pos += n;
  n = mysnprintf(netlines,pos,elinelen," \"cnts\":[%s]\n}\n",cntlines);
  pos += n;

  fmtstring(netname,"%s/network-%s.txt",outdir,netsuffix);

  info(0,"writing %u stops to %s",itemcnt,netname);
  if (writefile(netname,netlines,pos)) return 1;
  return 0;
}

todo parse all into struct, write at end

static int rdtrips(gtfsnet *net,const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawcnt,cnt = 0;
  int rv;
  char *buf;
  ub4 len,linno,colno;
  char *val,*vals,*sidval,*rridval,*orgridval,*orgtidval;
  ub2 vlen,sidvlen,rridvlen,orgridvlen,orgtidvlen,*vallens;
  ub4 *uvals;
  ub4 rrid,rtid,tid,eqid;
  ub4 valcnt,valno;
  ub4 linepos = 0;
  block *mem = &net->tripmem;
  int watch = 0,dbg = 0;
  char rridstr[128];

  oclear(eft);

  fmtstring(eft.mf.name,"%s/trips.%s",dir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,1,hi32 / 4);
  if (rv) return 1;

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  rawcnt = linecnt(fname,buf,len,1);

  if (rawcnt == 0) return warning(0,"%s is empty",fname);
  else if (rawcnt >= (1 << 23)) return error(0,"%s has %u trips, max %u",fname,rawcnt,1 << 23);

  hash *tripids = net->tripids = newhash(Item_trip,rawcnt,len);
  hash *notripids = net->notripids = newhash(Item_trip,rawcnt,len);

  hash *blockids = NULL;
  if (do_join) blockids = net->blockids = newhash(Item_trip,rawcnt,rawcnt * 32);

  hash *routeids = net->routeids;
  hash *norouteids = net->norouteids;
  hash *serviceids = net->serviceids;

  ub4 rid,bid,sid,rsid,type;
  char block_id[64];

  struct route *rp,*routes = net->routes;
  struct trip *tp,*trips = net->trips = alloc((rawcnt+2),struct trip,0,"trips",rawcnt);

  ub8 linelen = len + rawcnt + 4 * rawcnt * prefixlen1 + 16 + rawcnt * 36 + len;
  error_ge(linelen,hi32);
  char *lines = net->triplines = mkblock(mem,linelen,char,Noinit,"gtfs %u trips, len \ah%lu",rawcnt-1,linelen);

  ub4 route_idpos,service_idpos,trip_idpos,trip_orgidpos,headsignpos,block_idpos;
  route_idpos=service_idpos=trip_idpos=trip_orgidpos=headsignpos=block_idpos = hi32;

  vals = eft.vals;
  uvals = eft.uvals;

  do {

    res = nextchar(&eft);

    switch(res) {

    case Newcmd:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"route_id")) route_idpos = valno;
        else if (streq(val,"service_id")) service_idpos = valno;
        else if (streq(val,"trip_id")) trip_idpos = valno;
        else if (streq(val,"org_tripid")) trip_orgidpos = valno;
        else if (streq(val,"trip_headsign")) headsignpos = valno;
        else if (streq(val,"block_id")) block_idpos = valno;
        else vrb0(0,"skipping column %s",val);
      }
      if (route_idpos == hi32) return error(0,"%s: missing required column route_id",fname);
      if (service_idpos == hi32) return error(0,"%s: missing required column service_id",fname);
      if (trip_idpos == hi32) return error(0,"%s: missing required column trip_id",fname);
      break;

    case Newitem:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      error_ge(cnt,rawcnt);

      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        vlen = vallens[valno];
        vrbcc(dbg,0,"col %u val %u.'%s'",valno,vlen,val);
      }
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);

// trip id
      val = vals + trip_idpos * Collen;
      vlen = vallens[trip_idpos];
      rtid = uvals[trip_idpos];

// route id
      rridval = vals + route_idpos * Collen;
      rridvlen = vallens[route_idpos];
      rrid = uvals[route_idpos];

      infocc(watch,0,"watch route %s",rridval);
      rid = gethash(routeids,rridval,rridvlen,rrid); // filtered ?
      if (rid == hi32) {
        rid = gethash(norouteids,rridval,rridvlen,rrid); // disabled ?
        if (rid != hi32) {
          info(V0,"add trip %s for filtered route",val);
          if (addhash(notripids,val,vlen,rtid,cnt) == hi32) return 1;
          break;
        }
        if (strict || nounkroute) return parserr(FLN,fname,linno,colno,"unknown route %s",rridval);
        if (noany == 0) parsewarn(FLN,fname,linno,colno,"unknown route %s",rridval);
        parsewarn(FLN,fname,linno,colno,"unknown route %s",rridval);
        break;
      }

      rp = routes + rid;
      eqid = rp->eqid;
      if (eqid != hi32) {
        error_ge(eqid,rid);
        rp = routes + eqid;
        rridval = rp->rrid;
        rridvlen = (ub2)strlen(rridval);
      }
      type = rp->type;

      rp->tripcnt++;
      if (sampleratio && rp->tripcnt > 2) {
        if (rp->tripcnt >= rp->skipto) rp->skipto = rp->tripcnt + rnd(sampleratio);
        else {
          if (addhash(notripids,val,vlen,rtid,cnt) == hi32) return 1;
          break;
        }
      }

      if (do_ridinfer) { // placeholder filled lateron
        orgridvlen = rridvlen;
        orgridval = rridval;
        rridvlen = (ub2)fmtstring(rridstr,inferpat,0,0,0UL);
        rridval = rridstr;
      } else { orgridvlen = 0; orgridval = rridval; }

// service id
      sidval = vals + service_idpos * Collen;
      sidvlen = vallens[service_idpos];
      rsid = uvals[service_idpos];

      if (sidvlen == 0) return parserr(FLN,fname,linno,colno,"empty service for trip %s",val);

      sid = gethash(serviceids,sidval,sidvlen,rsid);
      if (sid == hi32) {
        if (strict) return parserr(FLN,fname,linno,colno,"unknown service %s",sidval);
//      warncc(sid == hi32,Noiter,"line %u: unknown sid %s",linno,sidval);  can be filtered on date
      }

// org_trip id
      if (trip_orgidpos != hi32) {
        orgtidval = vals + trip_orgidpos * Collen;
        orgtidvlen = vallens[trip_orgidpos];
      } else { orgtidvlen = 0; orgtidval = NULL; }

// trip id
      val = vals + trip_idpos * Collen;
      vlen = vallens[trip_idpos];
      rtid = uvals[trip_idpos];
      tid = gethash(tripids,val,vlen,rtid);
      if (tid != hi32) {
        tp = trips + tid;
        parsewarn(FLN,fname,linno,colno,"trip %s %.*s previously defined on line %u",val,orgtidvlen,orgtidval,tp->linno);
        if (strict) return 1;
        break;
      }
      tid = cnt;
      if (addhash(tripids,val,vlen,rtid,tid) == hi32) return 1;
      tid = gethash(tripids,val,vlen,rtid);
      if (tid == hi32 || tid != cnt) return error(0,"stored trip %s not present, expect %u got %u",val,cnt,tid);

      tp = trips + tid;
      error_nz(tp->tid,tid);
      tp->tid = tid;
      tp->watch = watch;
      tp->rid = rid;
      tp->sid = sid;
      tp->type = type;
      tp->loseq = hi32; tp->hiseq = 0;
      tp->linno = linno;
      tp->join = tp->join2 = hi32;

      strcopy(tp->name,val);

// write org trip id
      if (canonin == 0 || orgtidvlen == 0) {
        orgtidval = val;
        orgtidvlen = vlen;
      }

      tp->orgtidpos = linepos;
      linepos = addicol(mem,lines,linepos,orgtidval,orgtidvlen);
      tp->orgtidlen = orgtidvlen;

// route_id
      tp->rridpos = linepos;
      linepos = addicol(mem,lines,linepos,rridval,rridvlen);
      tp->rridlen = rridvlen;

// org route_id
      if (do_ridinfer) { // keep org route_id here
        tp->orgridpos = linepos;
        linepos = addicol(mem,lines,linepos,orgridval,orgridvlen);
        tp->orgridlen = orgridvlen;
      }

// sid
      tp->sidpos = linepos;
      linepos = addicol(mem,lines,linepos,sidval,sidvlen);
      tp->sidlen = sidvlen;
      error_z(lines[tp->sidpos],tid);

// block_id
      if (block_idpos != hi32 && blockids) {
        val = vals + block_idpos * Collen;
        vlen = vallens[block_idpos];
        if (vlen == 0) bid = hi32;
        else {
          len = fmtstring(block_id,"%s\t%s",sidval,val);
          bid = gethash(blockids,block_id,len,hi32);
          if (bid == hi32) {
            bid = linno;
            if (addhash(blockids,block_id,len,hi32,bid) == hi32) return 1;
          }
        }
      } else bid = hi32;
      tp->bid = bid;

// headsign
      if (headsignpos != hi32) {
        val = vals + headsignpos * Collen;
        vlen = vallens[headsignpos];

        if (rp->type == 1101 || rp->type == 1102) {
          if (vlen < 3 || vlen > 7 || val[0] < 'A' || val[0] > 'Z' || val[1] < 'A' || val[1] > 'Z') return error(0,"line %u: unrecognisable flightno %s",linno,val);
          memcpy(tp->flno,val,min(vlen,sizeof(tp->flno)));
        }

        bound(mem,linepos + vlen + 1,char);
        tp->headsignpos = linepos;
        linepos = addicol(mem,lines,linepos,val,vlen);
        tp->headsignlen = vlen;
      }
      error_ovf(linepos,ub4);
      cnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  infocc(cnt != rawcnt,0,"%u from %u entries",cnt,rawcnt);
  net->tripcnt = cnt;
  error_ge(linepos,hi32);
  net->triplinepos = (ub4)linepos;
  net->striplinepos = linepos + cnt * 3 * (prefixlen + 1) + cnt * 8;
  freefile(&eft.mf);

  if (cnt == 0) return error(0,"nil from %u trips",rawcnt);

  return 0;
}

// recognise 06:24  06.24  0624  0624+2
static ub4 hhmm2sec(ub4 linno,char *p,ub4 len)
{
  ub4 u,d,h,m,s,res;
  ub4 c,prvstate = 0,pos = 0,state = 0,hdig = 0,umin = 0;

  h = m = s = hi32;
  d = u = 0;
  if (len == 0) return hi32;
  bool sepa = 0;

  while (pos < len) {
    if (p[pos++] == ':') { sepa = 1; break; }
  }
  pos = 0;

  while (pos < len) {
    c = p[pos++];

    prvstate = state;
    switch(state) {

    case 0: if (c == '.' || c == ':') state = 2;
    else if (c >= '0' && c <= '9') {
      h = c - '0';
      hdig = 1;
      state = 1;
    } else state = 99;
    break;

    case 1: if (c == '.' || c == ':') state = 2;
    else if (c >= '0' && c <= '9') {
      if (hdig == 2 && sepa == 0) { m = c - '0'; state = 3; }
      else { h = h * 10 + c - '0'; hdig++; }
      if (h > 240) state = 99;
    } else state = 99;
    break;

    case 2:
    switch(c) {
    case '.': case ':': state = 4; break;
    case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9': m = c - '0'; state = 3; break;
    default: return state = 99;
    }
    break;

    case 3:
    switch(c) {
      case '.': case ':': state = 4; break;
      case '+': d = hi32; state = 6; break;
      case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9':
        m = m * 10 + c - '0';
        if (m >= 60) state = 99;
        break;
      default: state = 99;
    }
    break;

    case 4: if (c >= '0' && c <= '9') { s = c - '0'; state = 5; }
    else state = 99;
    break;

    case 5: if (c >= '0' && c <= '9') {
      s = s * 10 + c - '0';
      if (s >= 60) state = 99;
    } else if (c == '+') { d = hi32; state = 6; }
    else state = 99;
    break;

    case 6:
    if (c >= '0' && c <= '9') { d = c - '0'; state = 7; }
    else state = 99;
    break;

    case 7:
    switch(c) {
      case '+': u = hi32; state = 8; break;
      case '-': u = hi32; umin = 1; state = 8; break;
      case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9':
        d = d * 10 + c - '0';
        if (d >= 30) state = 99;
      break;
      default: state = 99;
    }
    break;

    case 8:
    if (c >= '0' && c <= '9') { u = c - '0'; state = 9; }
    break;

    case 9:
    if (c >= '0' && c <= '9') {
      u = u * 10 + c - '0';
      if (u > 1400) state = 99;
    } else state = 99;
    break;

    case 99: break;

    }

  }

  switch(state) {
    case 99: return error(Exit,"line %u.%u: unrecognisable time '%s' state %u",linno,pos,p,prvstate);
    case 1: m = h; h = 0; break;  // 2-digit only
  }

  if (s == hi32) s = 0;
  if (u == hi32 || d == hi32 || h == hi32 || m == hi32) return error(Exit,"line %u: unrecognisable time %s",linno,p);

  if (d > maxdurday) return error(Exit,"line %u.%u: unrecognisable time '%s', days %u",linno,pos,p,d);
  if (h > maxdurday * 24) return error(Exit,"line %u.%u: unrecognisable time '%s', days %u",linno,pos,p,h);
  if (m > 59) return error(Exit,"line %u.%u: unrecognisable time '%s', days %u",linno,pos,p,m);
  if (s > 59) return error(Exit,"line %u.%u: unrecognisable time '%s', days %u",linno,pos,p,s);
  res = d * 1440  + h * 60 + m;
  if (umin) {
    errorcc(umin > res,Exit,"line %u.%u: utcdelta %u > tmin %u",linno,pos,u,res);
    res -= u;
  } else res += u;

  return res * 60 + s;
}

static ub8 addtime(char *lines,ub4 tarr,ub4 tdep,ub8 linepos)
{
  ub4 clen;
  char c;
  char cval[64];

  if (tdep != tarr) c = '\t'; else c = '\n';

  if (tdep != hi32) clen = fmtstring(cval,"%02u:%02u:%02u",tarr / 3600,(tarr % 3600) / 60,tarr % 60);
  else clen = 0;
  linepos = addcol(lines,linepos,cval,clen,c,0);

  if (tdep != tarr) {
    if (tarr != hi32) clen = fmtstring(cval,"%02u:%02u:%02u",tdep / 3600,(tdep % 3600) / 60,tdep % 60);
    else clen = 0;
    linepos = addcol(lines,linepos,cval,clen,'\n',0);
  }
  return linepos;
}

static int rdfreqs(gtfsnet *net,const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawcnt,cnt = 0;
  int rv;
  char *buf;
  ub4 len,linno,colno;
  char *val,*vals,*idval,*val0,*val1;
  ub2 vlen,idvlen,*vallens,vlen0,vlen1;
  ub4 uval,*uvals;
  ub4 starttime,endtime,repiv;
  ub4 rtid,tid;
  ub4 valcnt,valno;
  ub8 orglinepos,linepos = 0,linelen;
  block *mem = &net->freqmem;

  oclear(eft);

  fmtstring(eft.mf.name,"%s/frequencies.%s",dir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,0,hi24);
  if (rv) return 1;
  if (eft.mf.exist == 0) return 0;

  buf = eft.mf.buf;
  len = (ub4)eft.mf.len;
  rawcnt = linecnt(fname,buf,len,1);

  if (rawcnt == 0) return info(0,"%s is empty",fname);

  hash *tripids = net->tripids;
  hash *notripids = net->notripids;

  struct trip *tp,*trips = net->trips;
  ub4 tripcnt = net->tripcnt;

  linelen = len + rawcnt + 4 * rawcnt * prefixlen1 + 16 + rawcnt * 36 + rawcnt * 64;
  char *lines = net->freqlines = mkblock(mem,linelen,char,Noinit,"gtfs %u trips, len \ah%lu",rawcnt-1,linelen);

  const char tab = '\t';
  ub4 trip_idpos,starttime_idpos,endtime_idpos,headway_idpos;
  trip_idpos=starttime_idpos=endtime_idpos=headway_idpos = hi32;

  vals = eft.vals;
  uvals = eft.uvals;

  do {

    res = nextchar(&eft);

    switch(res) {

    case Newcmd:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"start_time")) starttime_idpos = valno;
        else if (streq(val,"end_time")) endtime_idpos = valno;
        else if (streq(val,"trip_id")) trip_idpos = valno;
        else if (streq(val,"headway_secs")) headway_idpos = valno;
        else vrb0(0,"skipping column %s",val);
      }
      if (starttime_idpos == hi32) return error(0,"%s: missing required column start_time",fname);
      if (endtime_idpos == hi32) return error(0,"%s: missing required column end_time",fname);
      if (trip_idpos == hi32) return error(0,"%s: missing required column trip_id",fname);
      if (headway_idpos == hi32) return error(0,"%s: missing required column headway_secs",fname);
      break;

    case Newitem:
      valcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      vallens = eft.vallens;
      error_ge(cnt,rawcnt);
      orglinepos = linepos;

      if (valcnt < 4) return parserr(FLN,fname,linno,colno,"missing required columns, only %u",valcnt);

// trip id
      idval = vals + trip_idpos * Collen;
      idvlen = vallens[trip_idpos];
      rtid = uvals[trip_idpos];
      tid = gethash(tripids,idval,idvlen,rtid);
      if (tid == hi32) {
        tid = gethash(notripids,idval,idvlen,rtid);
        if (tid != hi32) break;
        parsewarn(FLN,fname,linno,colno,"undefined trip '%s'",idval);
        // return 1;
        if (strict) return 1;
        break;
      }
      error_ge(tid,tripcnt);
      tp = trips + tid;

      bound(mem,linepos + 12,char);
      linepos = addint(lines,linepos,tid,tab,1);

// org tripid
      bound(mem,linepos + idvlen,char);
      linepos = addcol(lines,linepos,idval,idvlen,tab,0);

// headway
      val = vals + headway_idpos * Collen;
      vlen = vallens[headway_idpos];
      uval = uvals[headway_idpos];

      if (vlen == 0) return parserr(FLN,fname,linno,colno,"missing headway for trip %s",idval);
      else if (uval == hi32) return parserr(FLN,fname,linno,colno,"expected numerical headway for trip %s, found %s",idval,val);
      else if (uval == 0) {
        if (strict) return parserr(FLN,fname,linno,colno,"zero headway for trip %s",idval);
        parsewarn(FLN,fname,linno,colno,"zero headway for trip %s",idval);
        linepos = orglinepos;
        break;
      } else if (uval < 60) {
        if (strict) return parserr(FLN,fname,linno,colno,"headway %u sec for trip %s",uval,idval);
        parsewarn(FLN,fname,linno,colno,"headway %u sec for trip %s",uval,idval);
        uval = 60;
      }
      repiv = uval;

      linepos = addint(lines,linepos,uval,tab,0);

// starttime
      val0 = vals + starttime_idpos * Collen;
      vlen0 = vallens[starttime_idpos];

      starttime = hhmm2sec(linno,val0,vlen0);

      if (starttime > 2 * 86400) return parserr(FLN,fname,linno,colno,"unexpected start_time %s",val0);

// endtime
      val1 = vals + endtime_idpos * Collen;
      vlen1 = vallens[endtime_idpos];

      endtime = hhmm2sec(linno,val1,vlen1);

      if (endtime > 2 * 86400) return parserr(FLN,fname,linno,colno,"unexpected end_time %s",val1);
      if (endtime < starttime) {
        parsewarn(FLN,fname,linno,colno,"end time %s before start %s",val1,val0);
        endtime += 86400;
      }
      if (endtime == starttime) repiv = 0;

      if (tp->repiv == 0) tp->repstart = starttime;
//      tp->repend = endtime;
      tp->repiv = repiv;

      linepos = addtime(lines,starttime,endtime,linepos);

      cnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  infocc(cnt != rawcnt,0,"%u from %u entries",cnt,rawcnt);
  net->freqlinepos = (ub4)linepos;
  net->freqcnt = cnt;

  return 0;
}

static int rdstoptimes(gtfsnet *net,const char *dir)
{
  enum extresult res;
  struct extfmt eft;
  const char *fname;

  ub4 rawcnt,timescnt = 0;
  ub4 tripcnt = net->tripcnt;
  ub4 prestopcnt = net->prestopcnt;
  int rv;
  char *buf;
  ub4 linno = 0,colno;
  char *val,*taval,*tdval,*vals;
  ub4 rtid,*uvals;
  ub2 vlen,tavlen,tdvlen,*vallens;
  ub4 valcnt,colcnt,valno;
  ub4 prestopid,stopid,rstopid;
  ub8 len,linepos = 0,linelen,slinelen,slinepos = 0;
  block *mem = &net->stoptimesmem;
  block *smem = &net->stopseqmem;
  int dbg;

  struct eta eta;

  oclear(eft);

  fmtstring(eft.mf.name,"%s/stop_times.%s",dir,fileext);
  fname = eft.mf.name;

  rv = readfile_gtfs(&eft.mf,fname,1,0);
  if (rv) return 1;

  buf = eft.mf.buf;
  len = eft.mf.len;
  rawcnt = linecnt(fname,buf,len,1);

  if (rawcnt == 0) return warning(0,"%s is empty",fname);

  hash *stopids = net->stopids = newhash(Item_stop,net->prestopcnt,net->prestopcnt * 64);
  hash *prestopids = net->prestopids;

  const char tab = '\t';
  ub4 trip_idpos,stop_idpos,stop_seqpos,tarr_pos,tdep_pos,pick_pos,drop_pos;
  trip_idpos=stop_idpos=stop_seqpos=tarr_pos=tdep_pos=pick_pos=drop_pos = hi32;

  struct route *rp,*rp2,*routes = net->routes;

  hash *tripids = net->tripids;
  hash *notripids = net->notripids;
  struct trip *tp,*tp2,*trips = net->trips;

  struct stoptime *st,*prvst,*stoptimes = alloc(rawcnt+2,struct stoptime,0,"stoptimes",rawcnt);

  char *stop_ids = alloc(prestopcnt * (Stop_idlen+2),char,0,"stop_ids",prestopcnt);

  char *triplines = net->triplines;
  error_zp(triplines,0);

  ub4 tid,rid,pick,drop;
  ub4 nilhops = 0;
  ub4 triplen = 1;

  ub4 seq = 0,seqline = 0;
  bool seqinc = 1;
  ub4 stopcnt = 0;
  ub4 ecnt = 0;

  ub4 tarr,tdep;
  ub4 nostopcnt = 0;
  int havepickdrop = 0;

  vals = eft.vals;
  uvals = eft.uvals;

  colcnt = 0;

  if (progress(&eta,"reading stop_time %u of %u in %s",0,rawcnt,fname)) return 1;

  do {

    res = nextchar(&eft);

    switch(res) {
    case Newcmd:
      valcnt = colcnt = eft.valcnt;
      linno = eft.linno;
      colno = eft.colno;
      if (valcnt < 3) return parserr(FLN,fname,linno,colno,"missing columns, only %u",valcnt);
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        if (streq(val,"trip_id")) trip_idpos = valno;
        else if (streq(val,"stop_id")) stop_idpos = valno;
        else if (streq(val,"stop_sequence")) stop_seqpos = valno;
        else if (streq(val,"arrival_time")) tarr_pos = valno;
        else if (streq(val,"departure_time")) tdep_pos = valno;
        else if (streq(val,"pickup_type")) pick_pos = valno;
        else if (streq(val,"drop_off_type")) drop_pos = valno;
        else vrb0(0,"skipping column %s",val);
      }
      if (trip_idpos == hi32) return error(0,"%s: missing required column trip_id",fname);
      if (stop_idpos == hi32) return error(0,"%s: missing required column stop_id",fname);
      if (stop_seqpos == hi32) return error(0,"%s: missing required column sequence_id",fname);
      if (tdep_pos == hi32) return error(0,"%s: missing required column departure_time",fname);
      if (tarr_pos == hi32) warning(0,"%s: missing column arrival_time",fname);
      havepickdrop = (pick_pos != hi32 && drop_pos != hi32);
      break;

    case Newitem:

      linno = eft.linno;
      if (progress(&eta,"reading stop_time %u of %u in %s",linno,rawcnt,fname)) return 1;

      valcnt = eft.valcnt;
      colno = eft.colno;
      vallens = eft.vallens;
      error_ge(timescnt,rawcnt);

#if 0
      for (valno = 0; valno < valcnt; valno++) {
        val = vals + valno * Collen;
        info(0,"col %u val '%s'",valno,val);
      }
#endif

      if (valcnt < 4 || valcnt < colcnt - 1) return parserr(FLN,fname,linno,colno,"require 4 columns, has %u, header %u",valcnt,colcnt);
      else if (valcnt != colcnt && timescnt == 0) {
        parsewarn(FLN,fname,linno,colno,"row has %u columns, header %u",valcnt,colcnt);
      }

// pickup / dropoff
      if (havepickdrop) {
        val = vals + pick_pos * Collen;
        vlen = vallens[pick_pos];
        if (vlen == 0) pick = 0;
        else pick = uvals[pick_pos];
        if (pick == hi32) { parsewarn(FLN,fname,linno,colno,"invalid value %s for pickup_type, expect integer",val); pick = 0; }
        val = vals + drop_pos * Collen;
        vlen = vallens[drop_pos];
        if (vlen == 0) drop = 0;
        else drop = uvals[drop_pos];
        if (drop == hi32) { parsewarn(FLN,fname,linno,colno,"invalid value %s for drop_off_type, expect integer",val); drop = 0; }
        if (pick == 1 && drop == 1) { nostopcnt++; break; }
      }

// tripid
      val = vals + trip_idpos * Collen;
      vlen = vallens[trip_idpos];
      rtid = uvals[trip_idpos];

      tid = gethash(tripids,val,vlen,rtid);
      if (tid == hi32) {
        tid = gethash(notripids,val,vlen,rtid);
        if (tid != hi32) break; // filtered
        if (strict) return parserr(FLN,fname,linno,colno,"unknown tripid %s",val);
        infocc(sampleratio == 0 && (canonin || noany == 0),0,"unknown tripid %s %u",val,rtid); // route filtered
        break;
      }
      error_ge(tid,tripcnt);
      tp = trips + tid;

      if (tp->sid == hi32) {
        info(Iter,"tripid %s has no sid",val);
        break;
      }

      dbg = tp->watch;

      st = stoptimes + timescnt;
      st->tid = tid;

// stopid
      val = vals + stop_idpos * Collen;
      vlen = vallens[stop_idpos];

      error_ge(vlen,Stop_idlen);
      if (vlen == 0) return parserr(FLN,fname,linno,colno,"empty stop id");

      rstopid = uvals[stop_idpos];

      prestopid = gethash(prestopids,val,vlen,rstopid);
      if (prestopid == hi32) {
        if (strict) return parserr(FLN,fname,linno,colno,"unknown stop %s",val);
        info(Iter,"line %u: skip filtered stop %s",linno,val);
        break;
      }

      stopid = gethash(stopids,val,vlen,rstopid);
      if (stopid == hi32) {
        // vrb0(0,"adding new stop %u:%s hash %u",vlen,val,rstopid);
        stopid = stopcnt;
        if (addhash(stopids,val,vlen,rstopid,stopid) == hi32) return 1;
        memcpy(stop_ids + stopid * Stop_idlen,val,vlen);
        stopcnt++;
      } // else info(0,"line %u: existing stop %s",linno,val);

      st->prestopid = prestopid;
      st->stopid = stopid;
      st->rstopid = rstopid;
      st->stop_id = stop_ids + stopid * Stop_idlen;

// seq
      val = vals + stop_seqpos * Collen;
      vlen = vallens[stop_seqpos];

      if (vlen) {
        seq = uvals[stop_seqpos];
        if (seq == hi32) {
          parserr(FLN,fname,linno,colno,"non-numerical sequence '%s'",val);
          if (strict) return 1;
          break;
        }
        if (seqpfxlen) {
          if (vlen < seqpfxlen || memcmp(val,seqprefix,seqpfxlen)) return parserr(FLN,fname,linno,colno,"non-constant sequence prefix %s in '%s'",seqprefix,val);
          if (str2ub4(val + seqpfxlen,&seq) == 0) return parserr(FLN,fname,linno,colno,"invalid sequence '%s' from '%s'",val + seqpfxlen,val);
        }
        if (linno > seqline + 1) seqinc = (seq == 1);
        seqline = linno;
        error_gt(seq,Hiseq,linno);
      } else if (canonin) return parserr(FLN,fname,linno,colno,"missing sequence");
      else { // autofill to support manual feeds
        if (seqinc) seq++; else seq--;
        if (seq == 0) return parserr(FLN,fname,linno,colno,"sequence zero, set at line %u",seqline);
      }
      if (seq < tp->loseq) { tp->loseq = seq; tp->lostop = stopid; }
      if (seq > tp->hiseq) { tp->hiseq = seq; tp->histop = stopid; }
      st->seq = (ub2)seq;
      error_gt(seq,Hiseq,linno);
      tp->len++;

// tarr,tdep
      tdval = vals + tdep_pos * Collen;
      tdvlen = vallens[tdep_pos];

      if (tarr_pos != hi32) {
        taval = vals + tarr_pos * Collen;
        tavlen = vallens[tarr_pos];
      } else {
        tavlen = 0;
        taval = (char *)"(n/a)";
      }

      // support tarr only for manual feed entry
      if (tdvlen && tavlen == 0) { tavlen = tdvlen; taval = tdval; }
      else if (tavlen && tdvlen == 0) { tdvlen = tavlen; tdval = taval; }

      tarr = hhmm2sec(linno,taval,tavlen);
      tdep = hhmm2sec(linno,tdval,tdvlen);

      if (tarr == hi32 && tdep != hi32) tarr = tdep;
      else if (tdep == hi32 && tarr != hi32) tdep = tarr;

//      info(Notty,"dep %s arr %s -> %u %u",tdval,taval,tdep / 60,tarr / 60);

      if (tarr == hi32 && tavlen) return parserr(FLN,fname,linno,colno,"invalid arr time for %s",taval);
      if (tdep == hi32 && tdvlen) return parserr(FLN,fname,linno,colno,"invalid dep time for %s",tdval);

      st->tarr = tarr;
      st->tdep = tdep;

      st->linno = linno;

      timescnt++;
      break;  // newitem

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  info(0,"\ah%u from \ah%u lines %u stops",timescnt,rawcnt,stopcnt);
  info(CC0,"\ah%u lines without pickup/dropoff",nostopcnt);
  if (timescnt == 0) return error(0,"0 from \ah%u lines",rawcnt);

  net->stoptimescnt = timescnt;
  net->stopcnt = stopcnt;

  freefile(&eft.mf);

  ub4 si,stopofs,sumtriplen = 0;
  ub4 loseq,loseq1,prvseq,seq1,span,ivdep,ivarr,prvtdep,prvtarr;
  ub4 notime = 0;

  for (tid = 0; tid < tripcnt; tid++) {
    tp = trips + tid;
    if (tp->len == 0 || tp->loseq == hi32) { // leftover from joined trips
      warncc(tp->sid != hi32,Iter,"trip %u line %u '%s' empty",tid,tp->linno,tp->name);
      continue;
    }
    if (tp->len == 1) warn(Iter,"trip %u line %u '%s' single entry",tid,tp->linno,tp->name);
    else {
      error_ge(tp->loseq,tp->hiseq);
      triplen = tp->hiseq - tp->loseq + 1;
      if (triplen > 10000) {
        warn(0,"trip %u line %u len %u %u .. %u",tid,tp->linno,triplen,tp->loseq,tp->hiseq);
        tp->len = 0;
        triplen = 0;
      }
    }
//    info(0,"%u %u",tp->loseq,tp->hiseq);
    sumtriplen += triplen;
  }
  struct tripstop *tsp,*tsp1,*tripstops = alloc(sumtriplen,struct tripstop,0,"trips",sumtriplen);

  for (si = 0; si < sumtriplen; si++) {
    tsp = tripstops + si;
    tsp->seq = hi16;
  }
  tsp = tripstops;
  stopofs = 0;
  for (tid = 0; tid < tripcnt; tid++) {
    tp = trips + tid;
    if (tp->len == 0 || tp->loseq == hi32) continue;
    triplen = tp->hiseq - tp->loseq + 1;
    tp->stopofs = stopofs;
    stopofs += triplen;
  }

  // arrange stops and seq in order
  info(0,"sort \ah%u times",timescnt);
  for (si = 0; si < timescnt; si++) {
    st = stoptimes + si;
    tid = st->tid;
    error_ge(tid,tripcnt);
    tp = trips + tid;
    if (progress(&eta,"sort \ah%u of \ah%u\a0, %u nilhop\as",si,timescnt,nilhops)) return 1;
    loseq = tp->loseq;
    if (tp->len == 0 || loseq >= hi16) continue;
    triplen = tp->hiseq - loseq + 1;
    error_gt(seq,Hiseq,si);
    seq = st->seq;
    error_lt(seq,loseq);
    error_gt(seq,tp->hiseq,si);
    error_ge(tp->stopofs,sumtriplen);
    error_ge(tp->stopofs + seq - loseq,sumtriplen);
    tsp = tripstops + tp->stopofs + seq - loseq; // insert sorted
    tdep = st->tdep;
    tarr = st->tarr;
    if (tsp->seq == seq) { // duplicate. join can create these
      error_ne_cc(tsp->stopid,st->stopid,"line %u %s",st->linno,st->stop_id);
      tsp->tarr = min(tsp->tarr,tarr);
      tsp->tdep = max(tsp->tdep,tdep);
      if (strict) return error(0,"null hop at line %u trip %s",st->linno,tp->name);
      else info(0,"null hop at line %u trip %s",st->linno,tp->name);
      nilhops++;
      continue;
    }
    error_ne(tsp->seq,hi16);
    tsp->seq = (ub2)seq;
    tsp->tdep = tdep;
    tsp->tarr = tarr;
    tsp->stopid = st->stopid;
    tsp->stid = si;
    tsp->linno = st->linno;
  }
  info(CC0,"%u null hop\as",nilhops);

  struct gtstop *presp,*presplo,*presp2,*presp3,*prestops = net->prestops;
  struct gtstop *pdep,*parr;
  ub4 fillcnt = 0;
  ub4 adj24,repiv,lotdep;
  ub8 seqsum1,seqsum2,timesum1,timesum2;
  ub4 nodurcnt = 0;

  // interpolate missing times and check increase
  for (tid = 0; tid < tripcnt; tid++) {
    if (progress(&eta,"trip %u of %u\a0 %u time interpol\as",tid,tripcnt,fillcnt)) return 1;
    tp = trips + tid;
    if (tp->len == 0 || tp->loseq >= hi16) continue;

    ecnt = 0;

    triplen = tp->hiseq - tp->loseq;
    tsp = tripstops + tp->stopofs;
    loseq = tp->loseq;
    tdep = tarr = prvseq = prvtdep = prvtarr = hi32;
    span = 0;
//    info(0,"trip %u line %u seq %u-%u '%s'",tid,tp->linno,loseq,tp->hiseq,tp->name);
    for (seq = loseq; seq <= tp->hiseq; seq++) {
      tsp = tripstops + tp->stopofs + seq - loseq;
      if (tsp->seq == hi16) continue;
      if (tsp->tdep == hi32) {
        notime++;
        span++;
        continue;
      }
      st = stoptimes + tsp->stid;
      tdep = tsp->tdep;
      tarr = tsp->tarr;

      if (prvtdep != hi32 && tdep < prvtdep && fix_plusday == 0) {
        error_eq(seq,loseq);
        error(0,"%s.%u: tdep \ad%u < preceding \ad%u seq %u %s",fname,tsp->linno,tdep / 60,prvtdep / 60,seq,st->stop_id);
        tp->hiseq = seq - 1;
        ecnt++;
        break;
      } else if (prvtarr != hi32 && tarr < prvtarr && fix_plusday == 0) {
        error_eq(seq,loseq);
        error(0,"%s.%u: tarr \ad%u < preceding \ad%u seq %u %s",fname,tsp->linno,tarr / 60,prvtarr / 60,seq,st->stop_id);
        tp->hiseq = seq - 1;
        ecnt++;
        break;
      }

      if (span && prvseq != hi32) {
        error_gt_cc(prvtdep,tarr,"tid %u seq %u line %u",tid,seq,tsp->linno);
        error_eq(prvtdep,hi32);
        error_eq(prvtarr,hi32);
        if (tdep == prvtdep) {
          info(Iter,"%s.%u: zero duration for tdep %u",fname,tsp->linno,tdep);
          nodurcnt++;
        }
        ivdep = (tdep - prvtdep) / (span + 1);
        ivarr = (tarr - prvtarr) / (span + 1);
        for (seq1 = prvseq + 1; seq1 < seq; seq1++) {
          tsp1 = tripstops + tp->stopofs + seq1 - loseq;
          if (tsp1->seq == hi16) continue;
          error_eq_cc(tsp1->seq,hi16,"line %u,%u seq %u/%u",tsp1->linno,tsp->linno,seq1,seq); // todo us/or/rvtd
          error_ne(tsp1->tdep,hi32);
          prvtdep += ivdep;
          tsp1->tdep = prvtdep;
          prvtarr += ivarr;
          tsp1->tarr = prvtarr;
          fillcnt++;
        }
      }
      span = 0;
      prvseq = seq;
      prvtdep = tdep;
      prvtarr = tarr;
    }

    // check
    prvtdep = prvtarr = hi32;
    adj24 = 0;
    for (seq = loseq; seq <= tp->hiseq; seq++) {
      tsp = tripstops + tp->stopofs + seq - loseq;
      if (tsp->seq == hi16) continue;
      st = stoptimes + tsp->stid;
      if (tsp->tdep == hi32) {
        notime++;
        warn(0,"line %u no time %s",tsp->linno,st->stop_id);
        continue;
      }
      tdep = tsp->tdep;
      tarr = tsp->tarr;
      if (tdep == hi32 && tarr == hi32) return error(0,"line %u no time %s",tsp->linno,st->stop_id);
      else if (tdep == hi32) tdep = tsp->tdep = tarr;
      else if (tarr == hi32) tarr = tsp->tarr = tdep;
      tdep += adj24;
      tarr += adj24;
      if (prvtdep != hi32) {
        st = stoptimes + tsp->stid;

        if(tarr < prvtarr) {
          if (fix_plusday) {
            warn(0,"line %u tarr \ad%u < preceding \ad%u %s",tsp->linno,tarr / 60,prvtarr / 60,st->stop_id);
            adj24 += 24 * 3600;
            tdep += 24 * 3600;
            tarr += 24 * 3600;
          } else ecnt += error(0,"trip %s line %u tarr \ad%u < preceding \ad%u %s",tp->name,tsp->linno,tarr / 60,prvtarr / 60,st->stop_id);

        }
        if (tdep < prvtdep) {
          if (fix_plusday) {
            warn(0,"line %u tdep \ad%u < preceding \ad%u %s",tsp->linno,tdep / 60,prvtdep / 60,st->stop_id);
            adj24 += 24 * 3600;
            tdep += 24 * 3600;
          } else ecnt += error(0,"trip %s line %u seq %u tdep \ad%u < preceding \ad%u seq %u %s",tp->name,tsp->linno,tsp->seq,tdep / 60,prvtdep / 60,prvseq,st->stop_id);
        }
        if (tdep < tarr) {
          ecnt += error(0,"line %u tdep \ad%u < tarr \ad%u %s",tsp->linno,tdep / 60,tarr / 60,st->stop_id);
          tarr = tdep;
        }
        tsp->tdep = tdep;
        tsp->tarr = tarr;
        if (tdep > maxdurday * 24 * 3600) ecnt += error(0,"line %u tdep \ad%u %s",tsp->linno,tdep / 60,st->stop_id);
        if (tarr > maxdurday * 24 * 3600) ecnt += error(0,"line %u tarr \ad%u %s",tsp->linno,tarr / 60,st->stop_id);
      }
      prvtdep = tdep;
      prvtarr = tarr;
      prvseq = tsp->seq;
    }
    if (strict && ecnt) return 1;
    errcnt += ecnt;

    // prepare start and end points
    seqsum1 = seqsum2 = timesum1 = timesum2 = 0;
    repiv = tp->repiv;  // interval if frequency-based
    lotdep = hi32;

    for (seq = loseq; seq <= tp->hiseq; seq++) {
      tsp = tripstops + tp->stopofs + seq - loseq;
      if (tsp->seq == hi16) continue;

      st = stoptimes + tsp->stid;
      prestopid = gethash(prestopids,st->stop_id,(ub4)strlen(st->stop_id),st->rstopid);
      error_eq_cc(prestopid,hi32,"unknown stopid '%s' line %u",st->stop_id,st->linno);
      seqsum1 = (seqsum1 + prestopid) & hi32;  // checksum on stop sequence for route inference
      seqsum2 = (seqsum2 + seqsum1) & hi32;
      error_ne(st->prestopid,prestopid);
      tsp->prestopid = prestopid;
      timesum1 = (timesum1 + tsp->tdep) & hi32; // checksum on time for duplicate detection
      timesum2 = (timesum2 + timesum1) & hi32;
      if (seq == loseq) {
        tp->loprestopid = tsp->prestopid;
        tp->lotarr = tsp->tarr;
        lotdep = tsp->tdep;
//        infocc(repiv,0,"rep iv %u tdep %u",repiv,lotdep);
      } else if (seq == tp->hiseq) {
        tp->hiprestopid = tsp->prestopid;
        tp->hitdep = tsp->tdep;
      }
    }
    tp->seqsum = seqsum1 | (seqsum2 << 32);
    tp->timesum = timesum1 | (timesum2 << 32);

//    infocc(repiv,0,"rep iv %u tdep %u",repiv,lotdep);
    if (repiv == 0 || lotdep == hi32) continue;

    // info(0,"line %u: adjust %u to 0",0,lotdep);
    for (seq = loseq; seq <= tp->hiseq; seq++) {
      tsp = tripstops + tp->stopofs + seq - loseq;
      if (tsp->seq == hi16) continue;
      error_lt(tsp->tdep,lotdep);
      tsp->tdep -= lotdep;
      tsp->tarr -= min(tsp->tarr,lotdep);
    }
  }
  info(CC0,"\ah%u/\ah%u of \ah%u entries without time",notime,fillcnt,timescnt);
  info(CC0,"\ah%u of \ah%u entries without duration",nodurcnt,timescnt);

  ub4 tid2;
  ub4 joincnt = 0;
  double dist;
  ub4 dupcnt = 0;

  // check duplicates
  for (tid = 0; do_chkdup && tid < tripcnt - 1; tid++) {

    if (progress(&eta,"checking trip %u of %u, %u dups",tid,tripcnt,dupcnt)) return 1;

    tp = trips + tid;
    if (tp->len < 2 || tp->loseq == hi32) continue;
    for (tid2 = tid + 1; tid2 < tripcnt; tid2++) {
      if (tid2 == tid) continue;
      tp2 = trips + tid2;
      if (tp2->len < 2 || tp2->loseq >= hi16) continue;
      if (tp->seqsum != tp2->seqsum) continue;
      if (tp->sid != tp2->sid) continue;
      if (tp->timesum != tp2->timesum) continue;
      info(Noiter,"identical trip lines %u and %u %s %s",tp->linno,tp2->linno,tp->name,tp2->name);
      tp->loseq = hi32;
      dupcnt++;
    }
  }

  hash *irouteids = NULL;
  ub4 irid,rridvlen = 0,iroutecnt = 0,noiridcnt = 0;

  if (do_ridinfer) irouteids = mkhash(FLN,tripcnt * 10,10,tripcnt * 36,"inferred routes");

  // infer routes
  for (tid = 0; do_ridinfer && tid < tripcnt; tid++) {
    tp = trips + tid;
    if (tp->len < 2 || tp->loseq == hi32) { noiridcnt++; continue; }
    triplen = tp->hiseq - tp->loseq;
    loseq = tp->loseq;

    rridvlen = fmtstring(tp->iroute,inferpat,tp->loprestopid,tp->hiprestopid,tp->seqsum);
    error_ne(rridvlen,8+8+16+2);
    irid = gethash(irouteids,tp->iroute,rridvlen,hi32);
    if (irid == hi32) {
      irid = iroutecnt++;
      if (addhash(irouteids,tp->iroute,rridvlen,hi32,irid) == hi32) return 1;
    }
    tp->irid = irid;
  }

  infocc(do_ridinfer,0,"%u inferred routes, %u from %u trips",iroutecnt,tripcnt - noiridcnt,tripcnt);
  net->iroutecnt = iroutecnt;

  struct iroute *irp, *iroutes = NULL;

  if (do_ridinfer) iroutes = net->iroutes = alloc(iroutecnt,struct iroute,0,"iroutes",iroutecnt);

  for (tid = 0; do_ridinfer && tid < tripcnt; tid++) {
    tp = trips + tid;
    if (tp->len < 2 || tp->loseq == hi32) continue;
    triplen = tp->hiseq - tp->loseq;
    loseq = tp->loseq;
    rid = tp->rid;
    irid = tp->irid;
    irp = iroutes + irid;
    memcpy(triplines + tp->rridpos,tp->iroute,rridvlen);   // overwrite routeid as filled before
    if (*irp->id) continue;
    strcopy(irp->id,tp->iroute);
    irp->type = tp->type;
    irp->rid = rid;

    presp = prestops + tp->hiprestopid;
    presplo = prestops + tp->loprestopid;
    fmtstring(irp->name,"%s to %s",presplo->name,presp->name);
  }

  linelen = len + iroutecnt * 13 + 2 * iroutecnt * prefixlen1;
  char *iridlines = NULL;
  block *imem = &net->iroutemem;
  if (iroutecnt) iridlines = net->iroutelines = mkblock(imem,linelen,char,Noinit,"gtfs %u ridinfer, len \ah%lu",iroutecnt-1,linelen);

  // write inferred routes
  linepos = 0;
  for (irid = 0; irid < iroutecnt; irid++) {
    irp = iroutes + irid;
    if (*irp->id == 0) continue;

    // route_id  agency_id  route_type  route_short_name  route_long_name  route_desc"
    bound(imem,linepos + rridvlen + 1,char);
    linepos = addcol(iridlines,linepos,irp->id,rridvlen,tab,1);

    rid = irp->rid;
    rp = routes + rid;

    vlen = (ub2)strlen(rp->agency);
    bound(imem,linepos + vlen + 1,char);
    linepos = addcol(iridlines,linepos,rp->agency,vlen,tab,1);

    linepos = addint(iridlines,linepos,irp->type,tab,0);

    vlen = (ub2)strlen(irp->name);
    bound(imem,linepos + vlen + 1,char);
    linepos = addcol(iridlines,linepos,irp->name,vlen,tab,0);

    iridlines[linepos++] = tab;
    iridlines[linepos++] = tab;
    iridlines[linepos++] = tab;
    iridlines[linepos++] = '\n';
  }
  net->iroutelinepos = (ub4)linepos;
  linepos = 0;

  // join eligible trips
  for (tid = 0; tid < tripcnt && do_join; tid++) {

    if (progress(&eta,"processing trip %u of %u joins %u",tid,tripcnt,joincnt)) return 1;

    dbg = (tid == 0);

    tp = trips + tid;
    if (tp->len < 2 || tp->loseq == hi32 || tp->bid == hi32) continue;

    rid = tp->rid;
    rp = routes + rid;

    triplen = tp->hiseq - tp->loseq;
    loseq = tp->loseq;

    presp = prestops + tp->hiprestopid;
    presplo = prestops + tp->loprestopid;

    // scan for concatenations:
    // same sid,(rid?),blockid, different stop sequence, matching time
    for (tid2 = 0; tid2 < tripcnt; tid2++) {
      if (tid2 == tid) continue;
      tp2 = trips + tid2;
      if (tp2->len < 2 || tp2->loseq >= hi16 || tp2->join != hi32) continue;
      if (tp2->bid == hi32 || tp->bid != tp2->bid) continue;
      if (tp2->hitdep > tp->lotarr || tp2->lotarr >= tp->lotarr) {
        continue;  // rename only if tid1 after tid2
      }

      if (tp->lotarr - tp2->hitdep > 10) continue;
      if (tp->lostop != tp2->histop) continue;

      if (tp->histop == tp2->lostop) continue;  // typical case of shuttle with same block id

      presp2 = prestops + tp2->loprestopid;
      rp2 = routes + tp2->rid;

      // check end of t1 near start of t2
      dist = geodist(presp->rlat,presp->rlon,presp2->rlat,presp2->rlon,presp->name);
      if (dist < 30) {
        infocc(dbg,Notty,"not join trip %u line %u to %u line %u route %s,%s t %u,%u",tid,tp->linno,tid2,tp2->linno,rp->name,rp2->name,tp->lotarr / 60,tp2->hitdep / 60);
        infocc(dbg,Notty,"dist %f at %s to %s %f,%f %f,%f",dist,presp->name,presp2->name,presp->lat,presp->lon,presp2->lat,presp2->lon);
        continue;
      }

      // check any of t2 near end of t1
      dist = 10000;
      for (seq = loseq; seq <= tp2->hiseq; seq++) {
        tsp = tripstops + tp2->stopofs + seq - loseq;
        if (tsp->seq == 0) continue;
        presp2 = prestops + tsp->prestopid;
        if (tp->histop == tsp->stopid) {
          dist = 0;
          break;
        }
        dist = geodist(presp->rlat,presp->rlon,presp2->rlat,presp2->rlon,presp->name);
        if (dist < 30) {
          break;
        }
      }
      if (dist < 30) continue;

      // check any of t1 near start of t2
      dist = 10000;
      tsp = tripstops + tp2->stopofs;
      presp3 = prestops + tsp->prestopid;
      for (seq = loseq; seq <= tp->hiseq; seq++) {
        tsp = tripstops + tp->stopofs + seq - loseq;
        if (tsp->seq == hi16) continue;
        presp2 = prestops + tsp->prestopid;
        if (tp2->lostop == tsp->stopid) {
          dist = 0;
          break;
        }
        dist = geodist(presp3->rlat,presp3->rlon,presp2->rlat,presp2->rlon,presp3->name);
        if (dist < 30) {
          break;
        }
      }
      if (dist < 30) continue;

      tp->join = tid2;
      tp2->join2 = tid;
      infocc(dbg,0,"join trip %u line %u to %u line %u route %s,%s t %u,%u",tid,tp->linno,tid2,tp2->linno,rp->name,rp2->name,tp->lotarr / 60,tp2->hitdep / 60);
      infocc(dbg,0,"%s %s %s",presp3->name,presplo->name,presp->name);
      joincnt++;
      break;
    }
  }
  info(CC0,"\ah%u of \ah%u trips joined",joincnt,tripcnt);

  if (testonly) return 0;

  ub4 wrlines = 0,wrslines = 0;
  ub4 seqadj,seqndx;
  char *stopval;
  ub4 stopvlen;
  ub8 cnt = timescnt;
  linelen = len + cnt * 16 + 2 * cnt * prefixlen1;
  slinelen = len + cnt * 16 + 3 * cnt * prefixlen1;
  char *lines,*slines;

  if (write_stoptimes) lines = net->stoptimeslines = mkblock(mem,linelen,char,Noinit,"gtfs %u stoptimes, len \ah%lu",timescnt-1,linelen);
  else lines = NULL;
  if (write_stopseqs) slines = net->stopseqlines = mkblock(smem,slinelen,char,Noinit,"gtfs %u stopseqs, len \ah%lu",timescnt-1,slinelen);
  else slines = NULL;

  iadrbase *net0 = &net->net0;

  if (no_grplink) {
    if (mkiadr0(net0,prestopcnt,prestopcnt,ub2,10000,8,"net0")) return 1;
    if (mkiadrmap(net0,"net0 `")) return 1;
  }

  // sort on route
  infovrb(tripcnt > 1024 * 16,0,"sorting %u trips",tripcnt);
  ub8 rs,*ridsort = talloc0(tripcnt,ub8,0);
  ub4 stid,prvrid = 0;

  for (tid = 0; tid < tripcnt; tid++) {

    tp = trips + tid;
    rid = tp->rid;

    ridsort[tid] = ((ub8)rid << 32) | tid;
  }
  sort8(ridsort,tripcnt,FLN,"ridsort");

  block *tmem = &net->stripmem;
  char *striplines = net->striplines = mkblock(tmem,net->striplinepos,char,Noinit,"gtfs %u trips",tripcnt);
  ub8 stpos = 0;
  ub4 nolinecnt = 0;
  error_zp(striplines,0);

  // write
  for (stid = 0; stid < tripcnt; stid++) {

    if (progress(&eta,"writing trip %u of %u  lines \ah%u",stid,tripcnt,wrlines)) return 1;

    rs = ridsort[stid];
    tid = rs & hi32;

    error_ge(tid,tripcnt);
    tp = trips + tid;
    error_ne(tp->tid,tid);
    rid = tp->rid;
    error_ne(rid,rs >> 32);
    error_lt(rid,prvrid);
    rp = routes + rid;
    infocc(rid != prvrid,V0,"tid %u rid %u %s",tid,rid,rp->rrid);
    prvrid = rid;

    if (tp->len < 2 || tp->loseq == hi32) continue;
    if (tp->join2 != hi32) continue;

    // write trip
    bound(&net->tripmem,0,char);
    bound(&net->tripmem,tp->rridpos,char);

    // route id
    stpos = addmcol(tmem,striplines,stpos,triplines + tp->rridpos,tp->rridlen,tab,1);

    // service id
    stpos = addmcol(tmem,striplines,stpos,triplines + tp->sidpos,tp->sidlen,tab,1);

    // trip id
    stpos = addmint(tmem,striplines,stpos,tid,tab,1);

    // org trip id
    stpos = addmcol(tmem,striplines,stpos,triplines + tp->orgtidpos,tp->orgtidlen,tab,0);

    // org route id
    stpos = addmcol(tmem,striplines,stpos,triplines + tp->orgridpos,tp->orgridlen,tab,0);

    // headsign
    stpos = addmcol(tmem,striplines,stpos,triplines + tp->headsignpos,tp->headsignlen,'\n',0);

    error_gt(stpos,net->striplinepos,tid);

    prvtdep = prvtarr = hi32;
    prvst = NULL;
    prvseq = hi32;

    if (tp->join == hi32) {
      rp = routes + rid;

      triplen = tp->hiseq - tp->loseq;
      loseq = tp->loseq;
      seqadj = (loseq ? 0: 1);
      seqndx = 0;
      tdep = tarr = 0;
      st = NULL;
      for (seq = loseq; seq <= tp->hiseq; seq++) {
        tsp = tripstops + tp->stopofs + seq - loseq;
        if (tsp->seq == hi16) continue;

        prvtdep = tdep; prvtarr = tarr; prvst = st;

        st = stoptimes + tsp->stid;
        tarr = tsp->tarr;
        tdep = tsp->tdep;

        if (tdep == prvtdep && tarr == prvtarr && st == prvst) {
          nolinecnt++;
          continue; // skip dummy lines
        }

        if (write_stoptimes) linepos = addint(lines,linepos,tid,tab,1);  // tripid

        stopval = st->stop_id;
        stopvlen = (ub4)strlen(stopval);

        if (write_stoptimes) {
          bound(mem,linepos + stopvlen + 1,char);
          linepos = addcol(lines,linepos,stopval,stopvlen,tab,1);  // stopid
          linepos = addint(lines,linepos,seq + seqadj,tab,0);  // seq
        }

        if (tdep != hi32 && tdep > maxdurday * 24 * 3600) fatal(0,"line %u tdep %u above max days %u %s",tsp->linno,tdep,maxdurday,st->stop_id);
        if (tarr != hi32 && tarr > maxdurday * 24 * 3600) fatal(0,"line %u tarr %u above max days %u %s",tsp->linno,tarr,maxdurday,st->stop_id);

        if (write_stoptimes) {
          bound(mem,linepos + 32,char);
          linepos = addtime(lines,tarr,tdep,linepos);  // tarr,tdep
        }

        seqndx++;
        wrlines++;

        if (seqndx == 1) continue;

        if (prvtdep == hi32 || tarr == hi32) {
          warn(Iter,"line %u tdep %u tarr %u %s",tsp->linno,tdep,tarr,stoptimes[tsp->stid].stop_id);
          continue;
        }
        if (prvtdep == tarr) { // au/qld/seq
          info(Iter|V0,"line %u tdep %u equals tarr %u %s",tsp->linno,tdep,tarr,stoptimes[tsp->stid].stop_id);
          tarr++;
        }
        if (write_stopseqs) {
          slinepos = addint(slines,slinepos,tid,tab,1);  // tripid

          val = prvst->stop_id;
          vlen = (ub2)strlen(val);
          boundcc(write_stopseqs,smem,slinepos + vlen + 1,char);
          slinepos = addcol(slines,slinepos,val,vlen,tab,1);  // dep

          boundcc(write_stopseqs,smem,slinepos + stopvlen + 1,char);
          slinepos = addcol(slines,slinepos,stopval,stopvlen,tab,1);  // arr

          slinepos = addint(slines,slinepos,seqndx - 2,tab,0);  // resequenced seq 0..n

          boundcc(write_stopseqs,smem,slinepos + 64,char);
          slinepos = addint(slines,slinepos,prvtdep,tab,0); // tdep
          slinepos = addint(slines,slinepos,tarr,'\n',0);   // tarr
        }

        if (no_grplink) iadrinc(net0,prvst->stopid,st->stopid,0);
        wrslines++;
      }
    } else {
      tid2 = tp->join;
      tp2 = trips + tid2;

      rid = tp2->rid;
      rp = routes + rid;

      triplen = tp2->hiseq - tp2->loseq;
      loseq = tp2->loseq;
      seqadj = (loseq ? 0: 1);
      info(Iter,"joined trip %u line %u seq %u-%u route %s",tid2,tp2->linno,loseq,tp2->hiseq,rp->name);

      // orig trip 1
      for (seq = loseq; seq <= tp2->hiseq; seq++) {
        tsp = tripstops + tp2->stopofs + seq - loseq;
        if (tsp->seq == hi16) continue;

        st = stoptimes + tsp->stid;
        tarr = tsp->tarr;
        tdep = tsp->tdep;

        if (tdep == prvtdep && tarr == prvtarr && st == prvst && seq == prvseq) continue;
        prvtdep = tdep; prvtarr = tarr; prvst = st; prvseq = seq;

        linepos = addint(lines,linepos,tid2,tab,1);

        val = st->stop_id;
        vlen = (ub2)strlen(val);
        boundcc(write_stoptimes,mem,linepos + vlen + 1,char);
        linepos = addcol(lines,linepos,val,vlen,tab,1);

        linepos = addint(lines,linepos,seq + seqadj,tab,0);

        linepos = addtime(lines,tarr,tdep,linepos);

        wrlines++;
      }
      tp2->len = 0;
      loseq1 = tp->loseq;

      // orig trip 2
      for (seq = loseq1; seq <= tp->hiseq; seq++) {
        tsp = tripstops + tp->stopofs + seq - loseq1;
        if (tsp->seq == hi16) continue;

        st = stoptimes + tsp->stid;
        tarr = tsp->tarr;
        tdep = tsp->tdep;

        if (tdep == prvtdep && tarr == prvtarr && st == prvst && seq == prvseq) continue;
        prvtdep = tdep; prvtarr = tarr; prvst = st; prvseq = seq;

        linepos = addint(lines,linepos,tid2,tab,1);

        val = st->stop_id;
        vlen = (ub2)strlen(val);
        bound(mem,linepos + vlen + 1,char);
        linepos = addcol(lines,linepos,val,vlen,tab,1);

        linepos = addint(lines,linepos,seq + tp2->hiseq + seqadj,tab,0);

        linepos = addtime(lines,tarr,tdep,linepos);

        wrlines++;
      }
    }
  }
  info(0,"%u trips",tripcnt);
  info(CC0,"%u empty line\as",nolinecnt);

  if (no_grplink) mkiadr1(net0); // todo br/belo

  for (tid = 0; tid < tripcnt && no_grplink; tid++) {

    if (progress0(&eta,"marking trip %u of %u",tid,tripcnt)) return 1;

    tp = trips + tid;
    if (tp->len < 2 || tp->loseq == hi32) continue;

    prvtdep = prvtarr = hi32;
    prvst = NULL;
    prvseq = hi32;

    rid = tp->rid;
    rp = routes + rid;

    triplen = tp->hiseq - tp->loseq;
    loseq = tp->loseq;
    seqadj = (loseq ? 0: 1);
    seqndx = 0;
    tdep = tarr = 0; st = NULL;
    for (seq = loseq; seq <= tp->hiseq; seq++) {
      tsp = tripstops + tp->stopofs + seq - loseq;
      if (tsp->seq == hi16) continue;

      prvtdep = tdep; prvtarr = tarr; prvst = st;

      st = stoptimes + tsp->stid;
      tarr = tsp->tarr;
      tdep = tsp->tdep;

      if (tdep == prvtdep && tarr == prvtarr && st == prvst) continue; // skip dummy lines

      seqndx++;

      if (seqndx == 1) continue;

      if (prvtdep == hi32 || tarr == hi32) continue;

      pdep = prestops + prvst->prestopid;
      parr = prestops + st->prestopid;
      error_ne(pdep->id,prvst->prestopid);
      error_ne(parr->id,st->prestopid);
      dist = geodist(pdep->rlat,pdep->rlon,parr->rlat,parr->rlon,"");
      if (dist > 3 * grplinkbelow || (!samename(pdep,parr) && dist > grplinkbelow)) {
        if (wriadr2(net0,prvst->stopid,st->stopid,1)) return 1;
      }
    }
  }
  if (no_grplink) finiadr(net0);

  net->stoptimeslinepos = linepos;
  net->stopseqlinepos = slinepos;
  net->striplinepos = (ub4)stpos;

  net->stopseqcnt = wrslines;

  afree(tripstops,"trips");
  afree(stoptimes,"stoptimes");

  return 0;
}

static ub4 wrhdr(const char *fname,char *buf,ub4 buflen)
{
  char cnowstr[64];
  char nowstr[64];
  const char *tz;
  ub4 pos;
  ub4 now = gettime_sec();

#ifdef NOW
  sec70toyymmdd(NOW,10,cnowstr,sizeof(cnowstr));
  tz = "utc";
#else
  strcopy(cnowstr,__DATE__);
  tz = "localtime";
#endif

  sec70toyymmdd(now,12,nowstr,sizeof(nowstr));

  pos = mysnprintf(buf,0,buflen,"# %s - variant gtfs feed for tripover\n\n",fname);
  pos += mysnprintf(buf,pos,buflen,"# written at %s utc by gtfsprep version %u.%u  %s %s\n\n",nowstr,Version_maj,Version_min,cnowstr,tz);
  return pos;
}

enum writeopts { Opt_nil = 0, Opt_needcnt = 1, Opt_nohdr = 2, Opt_nobck = 4 };

static int mayclose(int fd1,int fd2,const char *n1,const char *n2)
{
  if (fd1 != -1) fileclose(fd1,n1);
  if (fd2 != -1) fileclose(fd2,n2);
  return 1;
}

static int wrfeedfile(const char *dir,const char *name,const char *cols,ub4 cnt,ub4 opts,const char *data,ub8 len,const char *cmt)
{
  char fname[1024];
  char mrgfname[1024];
  char buf[1024];
  ub4 buflen = sizeof(buf);
  ub4 pos = 0;
  int fd,mrgfd,first = mergefirst;

  fmtstring(fname,"%s/%s.tab",dir,name);

  if (cnt == 0 || len == 0) {
    if (opts & Opt_needcnt) return error(0,"no items for %s",name);
    if (filerotate(fname,0,'0')) return 1;
    if (fileexists(fname) == 1) {
      if (fileremove(fname)) return 1;
    }
    return info(V0,"no items for %s",name);
  }

  fmtstring(mrgfname,"%s/%s.tab",mergedir,name);

  if (*mergedir) {
    if (fileexists(mrgfname) != 1) {
      info(0,"set first merge for nonexisting %s",mrgfname);
      first = 1;
    }
    mrgfd = first ? filecreate(mrgfname,1) : fileappend(mrgfname);
    if (mrgfd == -1) *mergedir = 0;
  } else mrgfd = -1;

  info(0,"writing %u item\as to %s/%s",cnt,dir,name);

  if ( (opts & Opt_nobck) == 0 && filerotate(fname,0,'0')) return 1;

  fd = filecreate(fname,1);
  if (fd == -1) {
    if (mrgfd != -1) fileclose(mrgfd,mrgfname);
    return 1;
  }

  if ( (opts & Opt_nohdr) == 0) pos = wrhdr(fname,buf,buflen);
  if (cnt > 1) pos += mysnprintf(buf,pos,buflen,"# %u entries\n\n",cnt);
  if (cmt) pos += mysnprintf(buf,pos,buflen,"## %s\n\n",cmt);

  if (pos && fileswrite(fd,mrgfd,buf,pos,fname)) return 1;

  pos = fmtstring(buf,"# %s\n",cols);
  if (first) {
    if (fileswrite(fd,mrgfd,buf+2,pos-2,fname)) return 1;
  } else {
    if (filewrite(fd,buf+2,pos-2,fname)) return mayclose(-1,mrgfd,fname,mrgfname);
    if (mrgfd != -1 && filewrite(mrgfd,buf,pos,fname)) return 1;
  }
  if (fileswrite(fd,mrgfd,data,len,fname)) return 1;

  if (mrgfd != -1 && fileclose(mrgfd,mrgfname)) return mayclose(fd,-1,fname,mrgfname);
  if (fileclose(fd,fname)) return 1;
  return globs.sigint;
}

static int wrsummary(gtfsnet *net,const char *dir)
{
  const char cols[] = "region\tname\tagencies\tstops\troutes\tstart\tend\trange\tminlat\tmaxlat\tminlon\tmaxlon";
  return wrfeedfile(dir,"summary",cols,1,Opt_needcnt | Opt_nohdr,net->summarylines,net->summarylinepos,NULL);
}

static int wragency(gtfsnet *net,const char *dir)
{
  const char cols[] = "agency_id\tagency_name\tagency_timezone\tagency_url\tagency_region";

  return wrfeedfile(dir,"agency",cols,net->agencycnt,Opt_needcnt,net->agencylines,net->agencylinepos,NULL);
}

static int wrcalendar(gtfsnet *net,const char *dir)
{
  const char cols[] = "service_id\tmonday\ttuesday\twednesday\tthursday\tfriday\tsaturday\tsunday\tstart_date\tend_date";

  char cmt[256];

  fmtstring(cmt,"feedstamp\t%u",stamp);
  fmtstring(cmt,"feedlostamp\t%u",lostamp);

  return wrfeedfile(dir,"calendar",cols,net->calendarcnt,Opt_nil,net->calendarlines,net->calendarlinepos,cmt);
}

static int wrcaldates(gtfsnet *net,const char *dir)
{
  const char cols[] = "service_id\texception_type\tdate";

  return wrfeedfile(dir,"calendar_dates",cols,net->caldatescnt,Opt_nil,net->caldateslines,net->caldateslinepos,NULL);
}

static int wrroutes(gtfsnet *net,const char *dir)
{
  char name[1024];

  fmtstring(name,"%sroutes",net->iroutelinepos ? "org_" : "");

  const char cols[] = "route_id\tagency_id\troute_type\troute_short_name\troute_long_name\troute_desc\tfare";

  return wrfeedfile(dir,name,cols,net->routecnt,Opt_needcnt,net->routelines,net->routelinepos,NULL);
}

static int wrxfers(gtfsnet *net,const char *dir)
{
  const char cols[] = "from_stop_id\tto_stop_id\ttransfer_type\tmin_transfer_time";

  return wrfeedfile(dir,"transfers",cols,net->xfercnt,Opt_nil,net->xferlines,net->xferlinepos,NULL);
}

static int wriroutes(gtfsnet *net,const char *dir)
{
  ub4 len = net->iroutelinepos;
  if (len == 0) return 0;

  const char cols[] = "route_id\tagency_id\troute_type\troute_short_name\troute_long_name\troute_desc\tfare";

  return wrfeedfile(dir,"routes",cols,net->iroutecnt,Opt_needcnt,net->iroutelines,len,NULL);
}

static int wrstops(gtfsnet *net,const char *dir)
{
  const char cols[] = "stop_id\tstop_code\tlocation_type\tparent_station\tstop_name\tstop_name_int\tstop_lat\tstop_lon\tstop_desc\tstop_timezone";

  char cmt[256];

  fmtstring(cmt,"cluster %u%s userstops %u",grouplimit,no_grplink ? "" : " linked",userstopcnt);

  return wrfeedfile(dir,"stops",cols,net->stopcnt,Opt_needcnt,net->stoplines,net->stoplinepos,cmt);
}

static int wrtrips(gtfsnet *net,const char *dir)
{
  const char cols[] = "route_id\tservice_id\ttrip_id\torg_tripid\torg_routeid\ttrip_headsign";

  return wrfeedfile(dir,"trips",cols,net->tripcnt,Opt_needcnt,net->striplines,net->striplinepos,NULL);
}

static int wrfreqs(gtfsnet *net,const char *dir)
{
  const char cols[] = "trip_id\torg_tripid\theadway_secs\tstart_time\tend_time";

  return wrfeedfile(dir,"frequencies",cols,net->freqcnt,Opt_nil,net->freqlines,net->freqlinepos,NULL);
}

static int wrstoptimes(gtfsnet *net,const char *dir)
{
  const char cols[] = "trip_id\tstop_id\tstop_sequence\tarrival_time\tdeparture_time";
  ub4 opt = write_stoptimes ? Opt_needcnt : Opt_nil;
  opt |= Opt_nobck;
  return wrfeedfile(dir,"stop_times",cols,net->stoptimescnt,opt,net->stoptimeslines,net->stoptimeslinepos,NULL);
}

static int wrstopseqs(gtfsnet *net,const char *dir)
{
  const char cols[] = "trip_id\tdep_stop_id\tarr_stop_id\tstop_sequence\tdeparture_time\tarrival_time";
  ub4 opt = write_stopseqs ? Opt_needcnt : Opt_nil;
  opt |= Opt_nobck;
  return wrfeedfile(dir,"stop_sequences",cols,net->stopseqcnt,opt,net->stopseqlines,net->stopseqlinepos,NULL);
}

static int readgtfs(gtfsnet *net,const char *dir,const char *outdir)
{
  int rv;

  info(0,"reading gtfs files from dir %s",dir);

  rv = rdagency(net,dir);
  if (rv) return rv;
  if (globs.sigint) return 1;

  rv = rdcalendar(net,dir);
  if (rv == 2) return 2 + 256;
  if (globs.sigint) return 2;

  if (net->calendarcnt) {
    if (havestartdate && lodate > startdate) {
      if (okdates) warn(0,"start date %u after specified %u",lodate,startdate);
      else {
        error(0,"start date %u after specified %u",lodate,startdate);
        return 2 + 256;
      }
    }
    if (haveenddate == 1 && hidate < enddate) {
      if (okdates) warn(0,"end date %u before specified %u",hidate,enddate);
      else {
        error(0,"end date %u before specified %u",hidate,enddate);
        return 2 + 256;
      }
    }
  }

  if (rdcaldates(net,dir) || globs.sigint) return 3 + 256;

  if (net->calendarcnt == 0 && net->caldatescnt == 0) {
    error0(0,"no valid calendar entries");
    return 4;
  }
  if (havestartdate && lodate > startdate) {
    if (okdates) warn(0,"start date %u after specified %u",lodate,startdate);
    else return error(0,"start date %u after specified %u",lodate,startdate);
  }
  if (haveenddate == 1 && hidate < enddate) {
    if (okdates) warn(0,"end date %u before specified %u",hidate,enddate);
    else return error(0,"end date %u before specified %u",hidate,enddate);
  }
  if (runto <= Run_time) return 0;
  if (rdroutes(net,dir) || globs.sigint) return 5;
  if (runto <= Run_route) return 0;
  if (net->routecnt == 0) return info0(0,"no routes");
  if (rdtrips(net,dir) || globs.sigint) return 6;
  if (runto <= Run_trip) return 0;
  if (rdfreqs(net,dir) || globs.sigint) return 7;

  if (*geonamedb) {
    rv = rdgeonames(net);
    if (rv) return error(0,"reading geo names failed, code %d",rv);
    else if (globs.sigint) return error0(0,"geo names interrupted");
    mknamgeosort(net,net->geostopcnt,net->geostops);
  }

  if (rdprestops(net,dir) || globs.sigint) return 8;
  if (runto <= Run_stop) return 0;

  if (rdstoptimes(net,dir) || globs.sigint) return 9;

  if (rdtransfers(net,dir) || globs.sigint) return 8;

  if (rdstops(net,dir,outdir) || globs.sigint) return 10;

  return info0(0,"done reading gtfs files");
}

static int writegtfs(gtfsnet *net,const char *dir)
{
  if (testonly) return info0(0,"test mode: no gtfs output");
  if (net->routecnt == 0 && noany) return info0(0,"no routes: skip gtfs output");
  if (wragency(net,dir)) return 1;
  if (net->routecnt == 0) {
    return runto < Run_route ? info0(0,"no routes") : error0(0,"no routes");;
  }
  if (wrcalendar(net,dir)) return 2;
  if (wrcaldates(net,dir)) return 3;
  if (wrroutes(net,dir)) return 4;
  if (wrxfers(net,dir)) return 4;
  if (wriroutes(net,dir)) return 5;
  if (wrstops(net,dir)) return 6;
  if (wrtrips(net,dir)) return 7;
  if (wrfreqs(net,dir)) return 8;
  if (wrstoptimes(net,dir)) return 9;
  if (wrstopseqs(net,dir)) return 10;
  if (wrsummary(net,dir)) return 11;
  return 0;
}

static int cmd_mergelim(struct cmdval *cv) {
  if (cv->valcnt) grouplimit = cv->uval;
  return info(0,"%s set to %u",cv->subarg,grouplimit);
}

static int cmd_stnlim(struct cmdval *cv) {
  if (cv->valcnt) stnlimit = cv->uval;
  return info(V0,"%s set to %u",cv->subarg,stnlimit);
}

static int cmd_dateshift(struct cmdval *cv) {
  ub4 prv = dateshift;
  if (cv->valcnt) dateshift = cv->uval * 7;
  return infovrb(prv != dateshift,0,"dateshift %u day\as",dateshift);
}

static int cmd_stamp(struct cmdval *cv) {
  if (cv->valcnt) stamp = cv->uval;
  return info(V0,"stamp %u",stamp);
}

static int cmd_lostamp(struct cmdval *cv) {
  if (cv->valcnt) lostamp = cv->uval;
  return info(V0,"lostamp %u",lostamp);
}

static int cmd_startdate(struct cmdval *cv) {
  if (cv->valcnt) { startdate = cv->uval; havestartdate = 1; }
  return info(V0,"startdate %u",startdate);
}
static int cmd_enddate(struct cmdval *cv) {
  if (cv->valcnt) { enddate = cv->uval; haveenddate = 1; }
  return info(V0,"enddate %u",enddate);
}
static int cmd_Enddate(struct cmdval *cv) {
  if (cv->valcnt) { enddate = cv->uval; haveenddate = 2; }
  return info(V0,"enddate %u",enddate);
}

static int cmd_tzmin(struct cmdval *cv) {
  tzmin = cv->uval;
  return info(V0,"%s set to %u",cv->subarg,tzmin);
}

static int cmd_parentname(struct cmdval *cv) {
  useparentname = 1;
  info(0,"%s set",cv->subarg);
  return 0;
}

static int cmd_test(struct cmdval *cv) {
  testonly = 1;
  info(0,"%s set",cv->subarg);
  return 0;
}

static int cmd_canonin(struct cmdval *cv) {
  canonin = 1;
  fileext = "tab";
  return info(V0,"%s set",cv->subarg);
}

static int cmd_intid(struct cmdval *cv) { intid = 1; return info(0,"%s set",cv->subarg); }
static int cmd_nojoin(struct cmdval *cv) { do_join = 0; return info(0,"%s set",cv->subarg); }
static int cmd_join(struct cmdval *cv) { do_join = 1; return info(0,"%s set",cv->subarg); }
static int cmd_chkdup(struct cmdval *cv) { do_chkdup = 1; return info(0,"%s set",cv->subarg); }
static int cmd_ridinfer(struct cmdval *cv) { do_ridinfer = 1; return info(0,"%s set",cv->subarg); }

static int cmd_okdates(struct cmdval *cv) { okdates = 1; return info(0,"%s set",cv->subarg); }
static int cmd_Okdates(struct cmdval *cv) { okdates = 2; return info(0,"%s set",cv->subarg); }

static int cmd_notram(struct cmdval *cv) { notram = 1; return info(0,"%s set",cv->subarg); }
static int cmd_notaxi(struct cmdval *cv) { notaxi = 1; return info(0,"%s set",cv->subarg); }
static int cmd_nometro(struct cmdval *cv) { nometro = 1; return info(0,"%s set",cv->subarg); }
static int cmd_norail(struct cmdval *cv) { norail = 1; return info(0,"%s set",cv->subarg); }
static int cmd_nobus(struct cmdval *cv) { nobus = 1; show_omitstop = 0; return info(0,"%s set",cv->subarg); }
static int cmd_bus(struct cmdval *cv) { nobus = 0; return info(0,"%s set",cv->subarg); }
static int cmd_noferry(struct cmdval *cv) { noferry = 1; return info(0,"%s set",cv->subarg); }
static int cmd_noair(struct cmdval *cv) { noair = 1; return info(0,"%s set",cv->subarg); }

static int cmd_seqprefix(struct cmdval *cv) {
  const char *s = cv->sval;
  seqpfxlen = fmtstring(seqprefix,"%s",s);
  return info(0,"%s set to %s",cv->subarg,s);
}

static int cmd_mergedir(struct cmdval *cv) {
  fmtstring(mergedir,"%s",cv->sval);
  return info(V0,"%s set to %s",cv->subarg,mergedir);
}

static int userprefix;

static int cmd_noprefix(struct cmdval *cv) {
  *prefix = 0;
  userprefix = 1;
  return info(V0,"%s unset",cv->subarg);
}

static int cmd_prefix(struct cmdval *cv) {
  fmtstring(prefix,"%s",cv->sval);
  userprefix = 1;
  return info(V0,"%s set to %s",cv->subarg,prefix);
}

static int cmd_dummy(struct cmdval *cv) { return info(V0,"%s set",cv->subarg); }

static int cmd_stoptimes(struct cmdval *cv) { write_stoptimes = cv->uval; return info(V0,"%s set",cv->subarg); }
static int cmd_stopseqs(struct cmdval *cv) { write_stopseqs = cv->uval; return info(V0,"%s set",cv->subarg); }

static int cmd_mergefirst(struct cmdval *cv) { mergefirst = 1; return info(V0,"%s set",cv->subarg); }

static int cmd_grplink(struct cmdval *cv) { no_grplink = 0; return info(V0,"%s set",cv->subarg); }

static int cmd_air(struct cmdval *cv) { airmode = 1; return info(V0,"%s set",cv->subarg); }

static int cmd_mergeroutes(struct cmdval *cv) { mergeduproutes = 1; return info(0,"%s set",cv->subarg); }

static int cmd_plusday(struct cmdval *cv) { fix_plusday = 1; return info(V0,"%s set",cv->subarg); }

static int cmd_strict(struct cmdval *cv) { strict = 1; return info(0,"%s set",cv->subarg); }

static int cmd_sample(struct cmdval *cv) {
  sampleratio = cv->uval;
  return info(0,"%s set to %u",cv->subarg,sampleratio);
}

static int cmd_runto(struct cmdval *cv) {
  const char *s = cv->sval;
  if (streq(s,"time")) runto = Run_time;
  else if (streq(s,"route")) runto = Run_route;
  else if (streq(s,"stop")) runto = Run_stop;
  else if (streq(s,"trip")) runto = Run_trip;
  else return warn(0,"unknown step %s for %s",s,cv->subarg);
  return 0;
}

static int cmd_modes(struct cmdval *cv) {
  notram = nometro = norail = nobus = noferry = noair = 1;
  const char *s = cv->sval;
  if (strstr(s,"tram")) notram = 0;
  if (strstr(s,"metro")) nometro = 0;
  if (strstr(s,"rail")) norail = 0;
  if (strstr(s,"bus")) nobus = 0;
  if (strstr(s,"ferry")) noferry = 0;
  if (strstr(s,"air")) noair = 0;
  return 0;
}

static int cmd_net(struct cmdval *cv) {
  strcopy(netsuffix,cv->sval);
  return 0;
}

static int cmd_geonames(struct cmdval *cv) {
  const char *s = cv->sval;
  if (*s == 0) return error(0,"missing arg for %s",cv->subarg);
  strcopy(geonamedb,cv->sval);
  return info(0,"%s set to %s",cv->subarg,cv->sval);
}

static int cmd_poplimit(struct cmdval *cv) {
  poplimit = cv->uval;
  return info(V0,"%s set",cv->subarg);
}

static int cmd_hash(struct cmdval *cv) {
  hashdepth = max(cv->uval,1);
  hashdepth = min(hashdepth,1024);
  return info(0,"%s set",cv->subarg);
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
  setmsglvl(globs.msglvl,globs.msgslvl);

  return 0;
}

static int cmd_arg(struct cmdval *cv)
{
  ub4 argc = globs.argc;
  char *dst;
  ub4 maxlen = sizeof(globs.args[0]);

  if (argc + 1 >= Elemcnt(globs.args)) return error(0,"exceeded %u arg limit",argc);

  dst = globs.args[argc];
  info(V0,"add arg %s", cv->sval);
  strncpy(dst, cv->sval,maxlen-1);
  globs.argc = argc + 1;
  return 0;
}

static struct cmdarg cmdargs[] = {
  { "mergelimit|m", "[limit]%u", "merge stops within given distance", cmd_mergelim },
  { "stnlimit", "[limit]%u", "threshold for station members", cmd_stnlim },
  { "startdate", "[date]%u", "start date of period", cmd_startdate },
  { "enddate", "[date]%u", "end date of period", cmd_enddate },
  { "Enddate", "[date]%u", "unconditional end date of period", cmd_Enddate },
  { "stamp", "[date]%u", "timestamp for annotation", cmd_stamp },
  { "lostamp", "[date]%u", "low timestamp for annotation", cmd_lostamp },
  { "okdates", NULL, "accept date range outside specified", cmd_okdates },
  { "Okdates", NULL, "accept date range outside specified", cmd_Okdates },
  { "dateshift", "[limit]%u", "shift dates by given weeks", cmd_dateshift },
  { "tzmin", "[days]%u", "adjust dates down by given days", cmd_tzmin },
  { "sample", "[ratio]%u", "sample trips", cmd_sample },
  { "test|t", NULL, "test only, no output", cmd_test },
  { "strict|s", NULL, "strict mode", cmd_strict },
  { "nostrict", NULL, "no strict mode", cmd_dummy },
  { "mknet", "[suffix]", "generate network for map", cmd_net },
  { "poplimit", "[limit]%u", "population limit for geo places", cmd_poplimit },
  { "modes", "[mode,mode]", "only specified transport modes", cmd_modes },
  { "runto", "[step]", "run to given step: time,route,stop,trip,seq", cmd_runto },
  { "nobus", NULL, "exclude bus routes", cmd_nobus },
  { "bus", NULL, "include bus routes", cmd_bus },
  { "norail", NULL, "exclude rail routes", cmd_norail },
  { "noferry", NULL, "exclude ferry routes", cmd_noferry },
  { "notram", NULL, "exclude tram routes", cmd_notram },
  { "notaxi", NULL, "exclude taxi routes", cmd_notaxi },
  { "nometro", NULL, "exclude metro routes", cmd_nometro },
  { "noair", NULL, "exclude air routes", cmd_noair },
  { "air", NULL, "air mode", cmd_air },
  { "nojoin", NULL, "do not join trips", cmd_nojoin },
  { "join", NULL, "join trips", cmd_join },
  { "grouplinked", NULL, "group connected stops", cmd_grplink },
  { "stoptimes", "[bool]%u", "write stoptimes", cmd_stoptimes },
  { "stopseqs", "[bool]%u", "write stopseqs", cmd_stopseqs },
  { "plusday", NULL, "assume +1day from 24 to 0", cmd_plusday },
  { "routeinfer", NULL, "infer routes", cmd_ridinfer },
  { "chkdup", NULL, "check for duplicate trips", cmd_chkdup },
  { "mrgroutes", NULL, "merge duplicate routes", cmd_mergeroutes },
  { "nopfx",NULL,"specify no ID prefix", cmd_noprefix },
  { "pfx","[prefix]","specify ID prefix", cmd_prefix },
  { "seqprefix","[prefix]","specify trip sequence prefix", cmd_seqprefix },
  { "geonames", "[file]", "read geonames from file", cmd_geonames },
  { "mergedir","[dir]","merge (=append) in addition", cmd_mergedir },
  { "mergefirst",NULL,"first merge item", cmd_mergefirst },
  { "parentname", NULL, "use parent name for stops", cmd_parentname },
  { "canonin", NULL, "use canonical input", cmd_canonin },
  { "intid", NULL, "use integer ID", cmd_intid },
  { "hashcap", "[depth]%u", "hash table capacity", cmd_hash },
  { "verbose|v", "[level]%u", "set or increase verbosity", cmd_vrb },
  { NULL, "dir or outdir indir", "gtfsprep", cmd_arg }
};

int main(int argc, char *argv[])
{
  gtfsnet net;
  const char *indir,*outdir;
  struct myfile mf;
  char buf[256];
  ub4 x;
  int rv;

  oclear(net);

  init0(argv[0]);

  if (cmdline(argc,argv,cmdargs,"gtfs prep tool")) return 1;
  if (globs.argc == 0) return shortusage();

  init1();

  if (userprefix) msgprefix(0,"%s ",prefix);

  verbose = (getmsglvl() > Info);

  ub4 maxvm = 64;
  memcfg(maxvm,8);

  if (canonin) { do_join = 0; do_ridinfer = 0; }

  if (enddate > lodate) return error(0,"end date %u above %u",enddate,lodate);
  else if (enddate < hidate) return error(0,"end date %u below %u",enddate,hidate);
  if (startdate > lodate) return error(0,"start date %u above %u",startdate,lodate);
  else if (startdate < hidate) return error(0,"start date %u below %u",startdate,hidate);
  if (enddate <= startdate) return error(0,"end date %u before start %u",enddate,startdate);

  if (tzmin) {
    x = cd2day(startdate) - tzmin;
    startdate = day2cd(x);
    x = cd2day(enddate) - tzmin;
    enddate = day2cd(x);
  }

  if (startdate > hidate && enddate < lodate) info(0,"period set to %u - %u",startdate,enddate);
  else if (startdate > hidate) info(0,"lower period date set to %u",startdate);
  else if (enddate < lodate) info(0,"upper period date set to %u",enddate);

  if (grouplimit) info(0,"-m=%u %s",grouplimit,no_grplink ? "" : "grplinked");

  noany = nobus | norail | notram | nometro | noferry | noair;

  if (strict) {
    fix_plusday = 0;
    sampleratio = 0;
    do_chkdup = 1;
  }

  if (testonly) {
    no_grplink = 0;
  }

  indir = outdir = globs.args[0];
  if (globs.argc > 1) indir = globs.args[1];
  if (canonin && testonly == 0 && streq(indir,outdir)) return error(0,"attempt to overwrite indir %s",indir);

  oclear(mf);
  if (osfileinfo(&mf,indir)) return oserror(0,"cannot access net directory %s",indir);
  else if (mf.isdir == 0) return error(0,"net arg %s is not a directory",indir);
  if (setmsglog(outdir,"gtfsprep",0,0)) return 1;

  if (canonin == 0) {
    if (*prefix == 0 && userprefix == 0) {
      if (globs.argc > 2) {
        strcopy(prefix,globs.args[2]);
        } else {
        strcopy(prefix,globs.args[0]);
      }
    }
  }

  prefixlen = (ub4)strlen(prefix);
  prefixlen1 = prefixlen + 1;
  if (prefixlen) info(V0,"using prefix %s",prefix);

  rv = rdcfg(".");
  if (rv) return 1;

  stnlimit_f = stnlimit;
  stnlimit3 = stnlimit * 3;

  rv = readgtfs(&net,indir,outdir);
  if (rv) {
    if (globs.sigint) { info0(0,"interrupted"); return 1; }
    else if (rv & 256) return 1;
    else return error(0,"gtfs read failed, code %d",rv);
  }

  ub4 lodays = cd2day(orglodate);
  ub4 hidays = cd2day(orghidate);

  int datespan = hidays - lodays;

  net.summarylinepos = fmtstring(net.summarylines,"%s\t%s\t%u\t%u\t%u\t%u\t%u\t%d\t%f\t%f\t%f\t%f\n",
    gen_region,prefix,net.agencycnt,userstopcnt,net.routecnt,orglodate,orghidate,datespan,minlat,maxlat,minlon,maxlon);

  if (runto == Run_all) {
    rv = writegtfs(&net,outdir);
    if (rv) {
      if (globs.sigint) { info0(0,"interrupted"); return 1; }
      else if (rv & 256) return 1;
      else return error(0,"gtfs write failed, code %d",rv);
    }
  }

  msgprefix(0,NULL);
  if (errcnt) {
    fmtstring(buf,"E %u ",errcnt);
  } else *buf = 0;

  char latlonbuf[128];

  fmtstring(latlonbuf,"%f,%f %f,%f",minlat,maxlat,minlon,maxlon);

  info(User,"I\\ %17s %sstop %4u > %4u %u-%u > %u-%u+%u %s",
    prefixlen ? prefix : outdir,buf,userstopcnt,planstopcnt,
    orglodate,orghidate,lodate,hidate,dateshift,
    runto == Run_all ? latlonbuf : "");

  eximsg(1);

  return globs.sigint;
}
