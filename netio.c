// netio.c - networks to and from file

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2014-2017 Joris van der Geer.
 */

/*
  Functions to read and write tripover internal networks, utility functions to write diagnostics
 */

#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#include "base.h"
#include "cfg.h"
#include "mem.h"
#include "math.h"
#include "util.h"
#include "time.h"

static ub4 msgfile;
#include "msg.h"

#include "iadr.h"
#include "netbase.h"
#include "netio.h"

static ub4 pdfscale_lat = 1200;
static ub4 pdfscale_lon = 1200;

static ub4 lat2pdf(ub4 lat,ub4 lolat,ub4 dlat) { return (lat - lolat) * pdfscale_lat / dlat; }
static ub4 lon2pdf(ub4 lon,ub4 lolon,ub4 dlon) { return (lon - lolon) * pdfscale_lon / dlon; }

static const ub4 pdfmaxports = 1000;
static const ub4 pdfmaxhops = 1000;
static const ub4 daymin = 60 * 24;
static const ub4 maxtripdur = 10; // in days

static ub4 timecntlimit = hi32;

// static const ub4 hop2watch = hi32;
// static const ub4 rtid2watch = hi32;

#include "watch.h"

/* tripover external format: easy manual editing, typical from single gtfs

files contain tab-separated columns

file ports.txt:

# starts comment
letters introduce commands:
  s <latlon scale,ofs>  scale and offset for lat and lon

numbers start a regular 'port' line:
 id name lat lon

numbers default to hexadecimal. prefix . for decimal.

file hops.txt
  patterned after ports.txt

commands:
# starts comment
tab introduces commands:
 t from to   # overal time validity of following block

any char except tab and newline introduce a regular hop line:
 name id dport aport route.seq dow.hhmm.rep.t0.t1.dur dow.hhmm.rep ...  # mm implies rep=60min
   dport,aport refers to port.id above
   route refers to route.id below
   seq  = hops from route start
   dow = days of week
   hhmm = hour:min
   rep = repetition interval
   t0,t1 is start and end of repetition
   dur = duration


routes.txt  todo
 id name hopcnt
 ...

  tripover internal format todo: meant for larger nets. typ combine sets of external

 */

enum stopopts { Stopopt_child = 1, Stopopt_parent = 2, Stopopt_geo = 4 };

static const char *kindnames[Kindcntb] = { "unknown","air int","air dom","rail","bus","ferry","taxi","walk" };

enum extresult { Next, Newitem, Newcmd, Eof, Parserr };

static int memeq(const char *s,const char *q,ub4 n) { return !memcmp(s,q,n); }

// count non-empty and non-comment lines
static ub4 linecnt(const char *name,const char *buf, ub8 len)
{
  ub8 pos = 0;
  ub4 cnt = 0;
  const char nl = '\n';

  while (pos < len) {
    if (buf[pos] == '#' || (pos + 1 < len && buf[pos] == '.' && buf[pos+1] != '.')  ) { while (pos < len && buf[pos] != nl) pos++; }
    else if (buf[pos] == nl) pos++;
    else {
      cnt++;
      while (pos < len && buf[pos] != nl) pos++;
    }
  }
  if (len && buf[len-1] != nl) warning(0,"%s has unterminated last line",name);
  info(0,"%s: %u data lines", name,cnt);
  return cnt;
}

static ub1 hexmap[256];

static void mkhexmap(void)
{
  char c;

  memset(hexmap,0xff,256);
  for (c = '0'; c <= '9'; c++) hexmap[(ub4)c] = (ub1)(c - '0');
  for (c = 'a'; c <= 'f'; c++) hexmap[(ub4)c] = (ub1)(c + 10 - 'a');
  for (c = 'A'; c <= 'F'; c++) hexmap[(ub4)c] = (ub1)(c + 10 - 'A');
  hexmap[9] = 0x20;
  hexmap[0x0a] = 0xfe;
  hexmap[0x20] = 0x20;
}

#define Maxval (64 * 1024)
#define Maxsval (16 * 1024)
#define Maxname 256

enum extstates { Init,Out,Val0,Hex1,Dec0,Dec1,Val1,Name,Cmd0,Fls};

struct extfmt {
  struct myfile mf;
  ub8 pos;
  enum extstates state;
  ub4 linno,colno;
  int iscmd;
  char name[Maxname];
  char prvname[Maxname];
  ub4 namelen;
  ub4 radix;
  ub4 val,xval,valndx,vals[Maxval];
  ub4 svalndx,svalpos;
  char svals[Maxval * Maxname];
  ub4 svallens[Maxval];
};

static enum extresult __attribute__ ((format (printf,6,7))) parserr(ub4 fln,const char *fname,ub4 linno,ub4 colno,struct extfmt *ef,const char *fmt, ...)
{
  va_list ap;
  char buf[1024];
  ub4 pos,len = sizeof(buf);

  if (ef) info(0,"after '%s'",ef->prvname);
  pos = fmtstring(buf,"%s.%u.%u: parse error: ",fname,linno,colno);
  if (fmt) {
    va_start(ap,fmt);
    myvsnprintf(buf,pos,len,fmt,ap);
    va_end(ap);
  }
  errorfln(fln,0,FLN,"%s",buf);

  nomsgpfx();

  return Parserr;
}

static int __attribute__ ((format (printf,5,6))) inerr(ub4 fln,const char *fname,ub4 linno,ub4 colno,const char *fmt, ...)
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
  errorfln(fln,0,FLN,"%s",buf);
  return msgprefix(1,NULL);
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

/* basic tab-separated ints parser.
   first item is name, rest are integers
   string starting with . is a command, double dot to escape a dot
   # is comment
   . prefix for decimal
   no prefix to use default radix
   .. switch radix to dec
   x switch radix to hex
 */

static enum extresult nextchar(struct extfmt *ef)
{
  char *fname,*name,c;
  ub8 pos,len;
  ub4 linno,colno,x,valndx,svalndx,svalpos,namelen;
  ub4 val,xval,*vals;
  ub4 namemax = Maxname - 2;
  ub4 maxval = Maxval - 1;
  int newitem,iscmd;
  ub4 radix;
  enum extstates state;
  char *sp;

  if (globs.sigint) return Parserr;

  len = ef->mf.len;
  pos = ef->pos;
  if (pos >= len) return Eof;

  // state
  state = ef->state;
  valndx = ef->valndx;
  svalndx = ef->svalndx;
  svalpos = ef->svalpos;
  val = ef->val;
  xval = ef->xval;
  linno = ef->linno + 1;
  colno = ef->colno;
  namelen = ef->namelen;
  iscmd = ef->iscmd;
  radix = ef->radix;

  // convenience
  name = ef->name;
  fname = ef->mf.name;
  vals = ef->vals;

  c = ef->mf.buf[pos];
  ef->pos = pos + 1;

  newitem = 0;

//    infocc(linno == 135,Noiter,"state %u c %c",state,c);

    switch(state) {

    case Init:
      linno = 1;
      radix = 16; Fallthrough
    case Out:
      valndx = svalndx = svalpos = 0;
      iscmd = 0;
      switch (c) {
        case '#': state = Fls; break;
        case '\t': valndx = namelen = 0; vals[0] = hi32; state = Val0; break;
        case '\n': break;
        case ' ': break;
        case '.': iscmd = 1; state = Cmd0; break;
        default: name[0] = c; namelen = 1; state = Name;
      }
      break;

    case Cmd0:
      switch (c) {
        case '#': state = Fls; break;
        case '\t': valndx = namelen = 0; vals[0] = hi32; state = Val0; break;
        case '\n': return parserr(FLN,fname,linno,colno,ef,"unexpected newline");
        case '.': iscmd = 0; name[0] = '.'; namelen = 1; state = Name; break;
        case '\\': state = Name; namelen = 0; break;
        default: name[0] = c; namelen = 1; state = Name;
      }
      break;

    case Name:
      if (c == '\t') {
        if (namelen + 2 < namemax) name[namelen] = 0;
        valndx = svalndx = svalpos = 0; state = Val0;
        vals[0] = hi32;
      }
      else if (c == '\n') return parserr(FLN,fname,linno,colno,ef,"missing args");
      else if (namelen + 2 < namemax) name[namelen++] = c;
      else if (name[namemax] != '!') {
        parsewarn(FLN,fname,linno,colno,"name exceeds %u",namemax);
        namelen = truncutf8(name,namelen);
        name[namemax] = '!';
      }
      break;

    case Val0:
      switch(c) {
        case '#': newitem = 1; state = Fls; break;
        case '\n': newitem = 1; state = Out; break;
        case '\t': case ' ': break;
        case '.': state = Dec0; break;
        case 'x': radix = 16; break;
        case '\'':
          if (svalndx + 1 >= Maxsval) return parserr(FLN,fname,linno,colno,ef,"exceeded %u strings",Maxsval);
          ef->svallens[svalndx] = 0;
          sp = ef->svals + svalndx * Maxname;
          svalpos = 0;
          *sp = 0;
          state = Val1;
          break;
        case '0': case '1': case '2': case '3': case '4': case '5': case '6': case '7': case '8': case '9':
          if (radix == 16) {
            val = hexmap[(ub4)c];
            state = Hex1;
          } else {
            val = c - '0';
            state = Dec1;
          }
          break;
        case 'a': case 'b': case 'c': case 'd': case 'e': case 'f':
          val = hexmap[(ub4)c];
          state = Hex1;
          break;
        default: return parserr(FLN,fname,linno,colno,ef,"expected digit, found '%c'",c);
      }
      break;

    case Val1:    // generic string
      switch(c) {
//        case '#': newitem = 1; state = Fls; break;
        case '\n':
          newitem = 1; state = Out;
          ef->svallens[svalndx] = svalpos;
          svalndx++; svalpos = 0;
          break;
        case '\t':
          ef->svallens[svalndx] = svalpos;
          svalndx++; svalpos = 0;
          state = Val0;
          break;
        default:
          if (svalpos + 1 >= Maxname) return parserr(FLN,fname,linno,colno,ef,"exceeding %u string len",svalpos);
          sp = ef->svals + svalndx * Maxname;
          sp[svalpos++] = c;
          sp[svalpos] = 0;
          break;
      }
      break;

    case Hex1:  // hex number
      if (valndx + 1 >= maxval) return parserr(FLN,fname,linno,colno,ef,"exceeding %u values",valndx);
      x = hexmap[(ub4)c];
      if (x < 16) val = (val << 4) | x;
      else if (x == 0x20) {
        vals[valndx++] = val;
        vals[valndx] = hi32;
        state = Val0;
      } else if (x == 0xfe) { // newline
        vals[valndx++] = val;
        vals[valndx] = hi32;
        newitem = 1;
        state = Out;
      } else return parserr(FLN,fname,linno,colno,ef,"expected whitespace after number, found %c",c);
      break;

    case Dec0:  // dec number
      if (c == '\t') {
        if (valndx >= maxval) return parserr(FLN,fname,linno,colno,ef,"exceeding %u values",valndx);
        vals[valndx++] = 0;
        vals[valndx] = hi32;
        state = Val0;
      } else if (c == '.') radix = 10;
//      else if (c >= 'A' && c <= 'Z') { val = 0; xval = (ub4)c << 24; state = Dec1; }
      else if (c < '0' || c > '9') return parserr(FLN,fname,linno,colno,ef,"expected decimal digit or letter, found '%c'",c);
      else { val = c - '0'; xval = 0; state = Dec1; }
      break;

    case Dec1:  // dec number
      if (c == '\t' || c == ' ') {
        if (valndx >= maxval) return parserr(FLN,fname,linno,colno,ef,"exceeding %u values",valndx);
        vals[valndx++] = val | xval;
        vals[valndx] = hi32;
        state = Val0;
      }
//      else if (c >= 'A' && c <= 'Z') xval |= (ub4)c << 16;
      else if (c >= '0' && c <= '9') {
        if (val > 400 * 1000 * 1000) parsewarn(FLN,fname,linno,colno,"decimal digit overflow at %u",val);
        else val = (val * 10) + (c - '0');
      } else if (c == '\n') {
        vals[valndx++] = val | xval;
        vals[valndx] = hi32;
        newitem = 1;
        state = Out;
      } else return parserr(FLN,fname,linno,colno,ef,"col %u: expected decimal digit or letter, found '%c' radix %u",valndx,c,radix);
      break;

    case Fls:
      if (c == '\n') { state = Out; } break;

    }

  if (c == '\n') { linno++; colno = 1; }
  else colno++;

  ef->state = state;

  ef->valndx = valndx;
  ef->svalndx = svalndx;
  ef->svalpos = svalpos;
  ef->val = val;
  ef->xval = xval;
  ef->linno = linno - 1;
  ef->colno = colno;
  ef->namelen = namelen;
  ef->iscmd = iscmd;
  ef->radix = radix;

  if (namelen) strcpy(ef->prvname,ef->name);
  else *ef->prvname = 0;

  if (newitem) return iscmd ? Newcmd : Newitem;
  else return Next;
}

struct cmdvars {
  const char *name;
  ub4 namelen;
  ub4 nval;
  ub4 *pval;
  char *sval;
  ub4 linno;
};

static ub4 sumtimes;
static ub4 rawtripcnt;
static ub4 hitripid;
static ub4 feedstamp,feedlostamp;

static struct cmdvars hopvars[] = {
  {"sumtimes",8,1,&sumtimes,NULL,0},
  {"trips",5,1,&rawtripcnt,NULL,0},
  {"hitrip",6,1,&hitripid,NULL,0},
  {"",0,0,NULL,NULL,0}
};

static ub4 timebox[2];  // coded decimal local yyyymmdd inclusive todo timezone
static ub4 dummy;
static ub4 sidrange[2];

static struct cmdvars timevars[] = {
  {"timebox",7,2,timebox,NULL,0},
  {"dowstart",8,0,&dummy,NULL,0},
  {"feedstamp",9,1,&feedstamp,NULL,hi32},
  {"feedlostamp",11,1,&feedlostamp,NULL,hi32},
  {"sidrange",8,2,sidrange,NULL,0},
  {"",0,0,NULL,NULL,0}
};

static ub4 ridrange[2];

static struct cmdvars routevars[] = {
  {"ridrange",8,2,ridrange,NULL,0},  // ridcnt, hirrid
  {"",0,0,NULL,NULL,0}
};

static ub4 tidrange[2];
static struct cmdvars ridevars[] = {
  {"tidrange",8,2,tidrange,NULL,0},  // tidcnt, hirtid
  {"",0,0,NULL,NULL,0}
};

static char portcmt[Maxname];
static ub4 pc_max = Maxname;
static ub4 latscale,lonscale;

static struct cmdvars portvars[] = {
  {"comment",7,1,&pc_max,portcmt,hi32},
  {"latscale",8,1,&latscale,NULL,0},
  {"lonscale",8,1,&lonscale,NULL,0},
  {"",0,0,NULL,NULL,0}
};

static int docmd(struct cmdvars *cvs,struct extfmt *ef,const char *fname)
{
  struct cmdvars *cv = cvs;
  ub4 namelen = ef->namelen;
  ub4 valcnt = ef->valndx;
  ub4 svalcnt = ef->svalndx;
  ub4 linno = ef->linno;
  ub4 *vals = ef->vals;
  char *svals = ef->svals;
  char *name = ef->name;

  ub4 nval,n,maxlen;

  while (cv->namelen) {
    if (namelen == cv->namelen && memeq(name,cv->name,namelen)) {
      if (cv->linno && cv->linno != hi32) return parsewarn(FLN,fname,linno,0,"ignore %s previously defined at %u",name,cv->linno);
      nval = cv->nval;
      if (valcnt + svalcnt < nval) return parserr(FLN,fname,linno,0,ef,"%s needs %u arg\as, has %u",name,nval,valcnt);
      cv->linno = linno;
      if (cv->sval) {
        if (svalcnt == 0 || ef->svallens[0] == 0) return parserr(FLN,fname,linno,0,ef,"missing value for cmd %s",name);
        maxlen = min(*cv->pval,ef->svallens[0]);
        maxlen = min(maxlen,Maxname);
        info(Emp,"%s '%.*s'",name,Maxname,svals);
        strncpy(cv->sval,svals,maxlen);
        return 0;
      }

      if (valcnt < nval) return parserr(FLN,fname,linno,0,ef,"%s needs %u arg\as, has %u",name,nval,valcnt);
      for (n = 0; n < nval; n++) {
        error_eq(vals[n],hi32);
        cv->pval[n] = vals[n];
      }
      if (nval == 1) info(0,"%s : %u",name,vals[0]);
      else if (nval > 1) info(0,"%s : %u %u",name,vals[0],vals[1]);
      return 0;
    }
    cv++;
  }
  return parsewarn(FLN,fname,linno,0,"unknown cmd %s ignored",name);
}

static void chkcmd(struct cmdvars *cvs,const char *desc)
{
  struct cmdvars *cv = cvs;

  while (cv->namelen) {
    if (cv->linno == 0) error(Exit,"missing required var %s for %s",cv->name,desc);
    cv++;
  }
}

#define Conshift 6
#define Conmax 1024

// manage constats for this step only. netbase needs to reconnect
static int doconstats(struct portbase *ports,ub4 portcnt)
{
  struct portbase *pp;
  ub4 nodep,noarr,nodeparr,udeparr1;
  ub4 hidep,hiarr,hidport,hiaport;
  ub4 port,ndep,narr,i,cnt,pos,pos1;
  char *name;
  char buf[256];
  char buf1[256];
  ub4 buflen = sizeof(buf);
  ub4 maxcon = (1 << Conshift) - 1;

static ub4 constats[1 << (Conshift * 2)];
static ub4 depstats[Conmax];
static ub4 arrstats[Conmax];
static ub4 dastats[Conmax];

  ub4 depivs = Elemcnt(depstats) - 1;
  ub4 arrivs = Elemcnt(arrstats) - 1;

  nodep = noarr = nodeparr = udeparr1 = 0;
  hidep = hiarr = hidport = hiaport = 0;

  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    name = pp->iname;
    ndep = pp->ndep; narr = pp->narr;
    if (ndep == 0 && narr == 0) {
      if (pp->geo == 0) {
        warn(Iter,"port %u %u has no connections - %s",port,pp->id,name);
        nodeparr++;
      }
    }
    else if (ndep == 0) { info(Iter,"port %u has no deps, %u arr\as %s",port,narr,name); nodep++; }
    else if (narr == 0) { info(Iter,"port %u has no arrs, %u dep\as %s",port,ndep,name); noarr++; }
    if (ndep > hidep) { hidep = ndep; hidport = port; }
    if (narr > hiarr) { hiarr = narr; hiaport = port; }
    depstats[min(ndep,depivs)]++;
    arrstats[min(narr,arrivs)]++;
    dastats[min(ndep + narr,arrivs)]++;
    ndep = min(ndep,maxcon);
    narr = min(narr,maxcon);
    constats[(ndep << Conshift) | narr]++;
  }
  if (nodeparr) warn(0,"%u of %u ports without connection",nodeparr,portcnt);
  if (nodep) info(0,"%u of %u ports without departures",nodep,portcnt);
  if (noarr) info(0,"%u of %u ports without arrivals",noarr,portcnt);

  ub4 showda = dyncfg("netio.showda",1,0);

  if (showda) {
    info0(User,"");
    info0(0,"ports with h deps and v arrs ");
    info0(0,"        0     1     2     3     4     5     6     7     8     9    10    11    12    13    14    15");
    for (i = 0; i < 16; i++) {
      ndep = i << Conshift;
      info(0,"%2u  %5u %5u %5u %5u %5u %5u %5u %5u %5u %5u %5u %5u %5u %5u %5u %5u",i,
        constats[ndep],constats[ndep+1],constats[ndep+2],constats[ndep+3],constats[ndep+4],constats[ndep+5],constats[ndep+6],constats[ndep+7],
        constats[ndep+8],constats[ndep+9],constats[ndep+10],constats[ndep+11],constats[ndep+12],constats[ndep+13],constats[ndep+14],constats[ndep+15]);
    }

    info0(User,"");
    info0(0,"ports with n deps");
    pos = pos1 = 0;
    for (ndep = 0; ndep <= min(depivs,127); ndep++) {
      pos1 += mysnprintf(buf1,pos1,buflen," %5u",ndep);
      pos += mysnprintf(buf,pos,buflen," %5u",depstats[ndep]);
      if ( (ndep % 16) == 15) {
        info0(User,"");
        info(0,"%s",buf1);
        info(0,"%s",buf);
        pos = pos1 = 0;
      }
    }
    if (pos) {
      info0(User,"");
      info(0,"%s",buf1);
      info(0,"%s",buf);
    }

    info0(User,"");
    info0(0,"ports with n arrs");
    pos = pos1 = 0;
    for (narr = 0; narr <= min(arrivs,127); narr++) {
      pos1 += mysnprintf(buf1,pos1,buflen," %5u",narr);
      pos += mysnprintf(buf,pos,buflen," %5u",arrstats[narr]);
      if ( (narr % 16) == 15) {
        info0(User,"");
        info(0,"%s",buf1);
        info(0,"%s",buf);
        pos = pos1 = 0;
      }
    }
    if (pos) {
      info0(User,"");
      info(0,"%s",buf1);
      info(0,"%s",buf);
    }

    info0(User,"");
  }

  pp = ports + hidport;
  info(0,"port %u deps %u arrs %u %s",hidport,hidep,pp->narr,pp->iname);
  pp = ports + hiaport;
  info(0,"port %u deps %u arrs %u %s",hiaport,pp->ndep,hiarr,pp->iname);

  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    ndep = pp->ndep; narr = pp->narr;
    if (ndep > hidep / 2 || narr > hiarr / 2) info(Iter,"port %u deps %u arrs %u %s", port,ndep,narr,pp->iname);
    pp->ndep = pp->narr = 0;
  }

  ub8 sumcnt = 0;
  for (narr = 0; narr <= arrivs; narr++) {
    cnt = dastats[narr];
    sumcnt += cnt;
    msgopt("dastats"); infocc(cnt,0,"%u deps + arrs : %u = \ap%lu%lu",narr,cnt,sumcnt,(ub8)portcnt);
  }

  return 0;
}

static ub4 portmodes(struct portbase *pp)
{
  ub4 m = 0;

  if (pp->air) m |= 1;
  if (pp->rail) m |= 2;
  if (pp->bus) m |= 4;
  if (pp->ferry) m |= 8;
  return m;
}
static ub4 sportmodes(struct subportbase *pp)
{
  ub4 m = 0;

  if (pp->air) m |= 1;
  if (pp->rail) m |= 2;
  if (pp->bus) m |= 4;
  if (pp->ferry) m |= 8;
  return m;
}

// name iname pfx id subid lat lon [opts stopid utcofs dstonof]
// opts: parent, child, geo
static int rdextports(netbase *net,const char *dir)
{
  enum extresult res;
  struct extfmt *eft = talloc0(1,struct extfmt,0);
  const char *fname;

  ub4 rawportcnt,extportcnt,portcnt,port;
  struct portbase *ports,*pp;
  int rv;
  char *buf;
  ub4 len,linno,colno,namelen,inamelen,prefixlen,idlo,idhi,subidhi,mapidlen,maxid;
  ub4 lat,lon,id,subid,stopid,opts;
  ub4 utcofs12,dstonof;
  ub4 dup2;
  ub4 lolon,lolat,hilon,hilat;
  char *name,*iname;
  ub4 valndx,svalndx,*vals;
  ub8 x8;

  struct extport {
    char name[Portnamelen];
    char iname[Portnamelen];
    char prefix[64];
    ub4 namelen,inamelen;
    ub4 prefixlen;
    ub4 id,subid,stopid,linno;
    ub4 opts;
    bool parent,child;
    ub4 subcnt,subofs,seq;
    ub4 lat,lon;
    ub4 utcofs12,dstonof;
  };
  struct extport *extports,*ep,*pep,*ep2;
  ub4 namemax = sizeof(extports->name) - 1;

  fmtstring(eft->mf.name,"%s/ports.txt",dir);
  fname = eft->mf.name;

  info0(User,"");
  info(0,"reading %s",fname);

  rv = readfile(&eft->mf,fname,1,0);
  if (rv) return 1;

  buf = eft->mf.buf;
  len = (ub4)eft->mf.len;
  rawportcnt = linecnt(fname,buf, len);

  if (rawportcnt == 0) return error(0,"%s is empty",fname);

  extportcnt = 0;
  extports = ep = talloc(rawportcnt,struct extport,0,"ext ports",rawportcnt);

  // vg_set_undef(ep,rawportcnt * sizeof(struct extport));
  //  vg_chk_def(ep,sizeof(struct extport));

  idhi = subidhi = maxid = 0;
  idlo = hi32;

  lolat = lolon = hi32;
  hilat = hilon = 0;

  vals = eft->vals;
  name = eft->name;

  do {
    res = nextchar(eft);

    switch(res) {
    case Newcmd:
      if (docmd(portvars,eft,fname)) return 1;
    break;

    case Newitem:
      if (extportcnt == 0) {
        chkcmd(portvars,"ports");
        error_zz(latscale,lonscale);
        error_eq(latscale,hi32);
        error_eq(lonscale,hi32);
        x8 = (ub8)latscale / 180;
        error_gt(x8,1<<30,0);
        x8 = (ub8)lonscale / 360;
        error_gt(x8,1<<30,0);
      }
      namelen = eft->namelen;
      valndx = eft->valndx;
      svalndx = eft->svalndx;
      linno = eft->linno;
      colno = eft->colno;
      error_ge(extportcnt,rawportcnt);
      if (valndx < 4) return parserr(FLN,fname,linno,colno,eft,"missing id,subid,lat,lon args, only %u",valndx);

      id = vals[0];
      subid = vals[1];

      msgprefix(0,"r.port %u.%u",id,extportcnt);

      lat = vals[2];
      lon = vals[3];
      if (valndx > 3) opts = vals[4];
      else opts = 0;
      if (valndx > 4) stopid = vals[5];
      else stopid = 0;
      utcofs12 = (valndx > 5 ? vals[6] : 2600);
      dstonof = (valndx > 6 ? vals[7] : 0);

      error_eq(id,hi32);
      error_eq(subid,hi32);
      error_eq(lat,hi32);
      error_eq(lon,hi32);
      error_eq(opts,hi32);
      error_eq(stopid,hi32);

      vrb(0,"port %u id %u sub %u opts %x",extportcnt,id,subid,opts);

      for (dup2 = 0; dup2 < extportcnt; dup2++) {
        ep2 = extports + dup2;
        if (ep2->lat != lat || ep2->lon != lon || ep2->namelen != namelen) break;
        if (memcmp(ep2->name,name,namelen)) break;
        if (ep2->id == id && ep2->subid == subid) parsewarn(FLN,fname,linno,colno,"duplicate port id %u subid %u %s",id,subid,name);
        else parsewarn(FLN,fname,linno,colno,"port name %s lat %u lon %u for both id %u subid %u and %u %u",name,lat,lon,id,subid,ep2->id,ep2->subid);
      }
      if (id > idhi) idhi = id;
      if (id < idlo) idlo = id;
      if (subid > subidhi) subidhi = subid;

      ep->id = id;
      ep->stopid = stopid;
      ep->subid = subid;
      ep->linno = linno;
      // infocc(id > 300000,Iter,"port %u id %u %x hi %u",extportcnt,id,id,idhi);
      ep->opts = opts;
      ep->parent = (opts & Stopopt_parent);
      ep->child  = (opts & Stopopt_child);
      if (id != subid && ep->parent) parsewarn(FLN,fname,linno,colno,"parent port %u has parent %u",subid,id);
      if (id == subid && ep->child) parsewarn(FLN,fname,linno,colno,"child port %u %s has no parent",id,name);

      if (lat >= 180 * latscale) { parsewarn(FLN,fname,linno,colno,"port %u lat %u out of range",id,lat); lat = 0; }
      if (lon >= 360 * lonscale) { parsewarn(FLN,fname,linno,colno,"port %u lon %u out of range",id,lon); lon = 0; }
      ep->lat = lat;
      ep->lon = lon;
      lolat = min(lolat,lat);
      hilat = max(hilat,lat);
      lolon = min(lolon,lon);
      hilon = max(hilon,lon);

      ep->utcofs12 = utc12ofs(utcofs12);
      ep->dstonof = dstonof;

      if (namelen > namemax) parsewarn(FLN,fname,linno,colno,"name length %u exceeds max %u",namelen,namemax);
      else if (namelen == 0) return parserr(FLN,fname,linno,colno,"port %u has no name",id);
      else {
        ep->namelen = copystr(ep->name,name);
        memset(ep->iname,0,sizeof(ep->iname));
      }

      if (svalndx > 1) {
        prefixlen = eft->svallens[1];
        prefixlen = min(prefixlen,sizeof(ep->prefix)-1);
        if (prefixlen) memcpy(ep->prefix,eft->svals + Maxname,prefixlen);
        ep->prefixlen = prefixlen;
        ep->prefix[prefixlen] = 0;
      } else ep->prefixlen = 0;

      if (svalndx) {
        inamelen = eft->svallens[0];
        iname = eft->svals;
        if (inamelen > namemax) {
          parsewarn(FLN,fname,linno,colno,"name length %u exceeds max %u",inamelen,namemax);
        }
        info(V1,"port %u name '%s'",extportcnt,iname);
      } else { inamelen = 0; iname = name; }

      ep->inamelen = copystr(ep->Liname,iname);

      extportcnt++;
      ep++;

      msgprefix(0,NULL);

      break;  // newitem

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  info(0,"read %u ports, id in %u..%u",extportcnt,idlo,idhi);

  freefile(&eft->mf);
  afree0(eft);

  if (extportcnt == 0) return error(0,"no ports from %u",rawportcnt);

  ub4 pid,subofs,seq,pos;
  ub4 cnt,extport,extport2,subport,subportcnt;
  ub8 vgadr = 0;
  struct subportbase *subports,*sp;

  // create mappings
  if (idhi > 100 * 1000 * 1000) warning(0,"max port id %u",idhi);
  if (subidhi > 100 * 1000 * 1000) warning(0,"max subport id %u",subidhi);

  mapidlen = max(idhi,subidhi) + 1;
  ub4 *id2ports = talloc(mapidlen,ub4,0xff,"ext id2port",idhi);
  ub4 *subid2ports = talloc(mapidlen,ub4,0xff,"ext subid2port",subidhi);

  port = 0;
  for (extport = 0; extport < extportcnt; extport++) {
    ep = extports + extport;
    id = ep->id;
    subid = ep->subid;
    error_gt_cc(id,idhi,"port %u",extport);
    error_gt(subid,subidhi,extport);
    ep->subcnt = 0;

    if (id == subid) { // parent or plain port
      if (id2ports[id] != hi32) warning(0,"port ID %u doubly defined as %x", id,id2ports[id]);
      else id2ports[id] = extport;
      infocc(id == 1696,0,"port %u ext %u %s",id,extport,ep->name);
      if (subid2ports[id] != hi32) warning(0,"port subID %u doubly defined as %x", subid,subid2ports[subid]);
      else { subid2ports[id] = extport; if (extport == 0) info(0,"id %u port 0 %s",id,ep->namelen ? ep->name : "(no name)"); port++; }
    } else {
      if (subid2ports[subid] != hi32) warning(0,"port subID %u doubly defined as %x", subid,subid2ports[subid]);
      else { subid2ports[subid] = extport; if (extport == 0) info(0,"subid %u",subid); }
    }
  }
  portcnt = port;

  for (extport = 0; extport < extportcnt; extport++) {
    ep = extports + extport;
    id = ep->id;
    if (subid2ports[id] == 0) info(0,"port %u id %u map 0 %s",extport,id,ep->name);
   }

  // check station assignment
  for (extport = 0; extport < extportcnt; extport++) {
    ep = extports + extport;
    id = ep->id;
    subid = ep->subid;
    if (id == subid) continue;

    extport2 = subid2ports[id];
    if (extport2 == hi32) return parserr(FLN,fname,ep->linno,0,eft,"port ID %u has nonexisting parent %u %s",subid,id,ep->name);
    ep2 = extports + extport2;
    if (ep2->parent == 0) warning(0,"line %u: port ID %u has plain %u as parent %s",ep->linno,subid,id,ep->name);
  }

  // count members

  subportcnt = 0;
  for (extport = 0; extport < extportcnt; extport++) {
    ep = extports + extport;
    id = ep->id;
    subid = ep->subid;
    if (id == subid) continue;

    pid = id2ports[id];
    error_ge_cc(pid,extportcnt,"id %u",id);
    error_eq(pid,extport);
    pep = extports + pid;
    cnt = pep->subcnt;
    if (cnt > 253) {
      warning(0,"drop subport %u for %u %s %s",subid,pid,ep->name,pep->name);
      ep->id = hi32;
      continue;
    }
    pep->subcnt = cnt + 1;
    ep->seq = cnt;
    vrb(0,"port %u has parent %u %s %s",subid,id,ep->name,pep->name);
    subportcnt++;
  }

  info(Emp,"%u ports, %u subports", portcnt, subportcnt);
  error_gt(portcnt,extportcnt,0);
  error_ge(subportcnt,extportcnt);

  if (portcnt == 0) return 0;

  ports = mkblock(&net->portmem,portcnt,struct portbase,Init0,"ext ports");
  net->ports = ports;

  if (subportcnt) {
    subports = mkblock(&net->subportmem,subportcnt,struct subportbase,Init0,"ext subports");
    net->subports = subports;
  } else subports = NULL;

  // assign subport ofs
  subofs = 0;
  for (extport = 0; extport < extportcnt; extport++) {
    ep = extports + extport;
    id = ep->id;
    if (id == hi32) continue;
    subid = ep->subid;
    if (id != subid) continue;
    cnt = ep->subcnt;
    ep->subofs = subofs;
    if (cnt == 0) continue;
    vrb(0,"port %u subcnt %u %s",extport,cnt,ep->name);
    subofs += cnt;
  }
  error_ne(subofs,subportcnt);

  // fill
  port = subport = 0;
  for (extport = 0; extport < extportcnt; extport++) {
    ep = extports + extport;
    vg_chk_def(vgadr,ep,sizeof(struct extport))
    id = ep->id;
    if (id == hi32) continue;
    subid = ep->subid;
    namelen = ep->namelen;
    inamelen = ep->inamelen;
    prefixlen = ep->prefixlen;
    lat = ep->lat;
    lon = ep->lon;
    if (id == subid) {
      pp = ports + port;
      pp->id = pp->cid = id;
      pp->stopid = ep->stopid;
      pp->parentsta = ep->parent;
      pp->lat = lat;
      pp->lon = lon;
      pp->utcofs = ep->utcofs12;
      pp->dstonof = ep->dstonof;
      pp->geo = (ep->opts & Stopopt_geo);
      pp->namelen = namelen;
      pp->intnamelen = inamelen;
      if (namelen) memcpy(pp->name,ep->name,namelen);
      if (inamelen) memcpy(pp->intname,ep->iname,inamelen);
      prefixlen = min(prefixlen,sizeof(pp->prefix)-1);
      pp->prefixlen = prefixlen;
      if (prefixlen) {
        memcpy(pp->prefix,ep->prefix,prefixlen);
        pos = fmtstring(pp->iname,"%s/",pp->prefix);
      } else pos = 0;
      pos += mysnprintf(pp->iname,pos,sizeof(pp->iname),"%.128s %.128s",pp->name,strcmp(ep->name,ep->iname) ? ep->iname : "");
      if (sizeof(pp->iname) - pos < 32) return error(0,"name %s %s",pp->name,ep->iname);
      cnt = ep->subcnt;
      if (cnt) { // station with members
        subofs = ep->subofs;
        error_ge(subofs,subportcnt);
        pp->subcnt = cnt;
        pp->subofs = subofs;
      } else if (ep->parent) vrb(0,"parent station %u has no member stops %s",id,ep->name);
      port++;
    } else { // sub
      pid = id2ports[id];
      error_ge(pid,extportcnt);
      pep = extports + pid;
      vg_chk_def(vgadr,pep,sizeof(struct extport))
      cnt = pep->subcnt;
      subofs = pep->subofs;
      error_ge(subofs,subportcnt);
      seq = ep->seq;
      error_gt(seq,hi16,id);
      vrb0(0,"seq %u cnt %u",seq,cnt);
      error_z(cnt,pid);
      subport = subofs + seq;
      error_ge(subport,subportcnt);
      sp = subports + subport;
      error_nz(sp->id,subport);
      sp->id = id;
      sp->subid = subid;
      sp->seq = (ub2)seq;
      sp->lat = lat;
      sp->lon = lon;
      sp->namelen = namelen;
      sp->intnamelen = inamelen;
      sp->stopid = ep->stopid;
      vg_chk_def(vgadr,ep,sizeof(struct extport)-1)
      infocc(vgadr != 0,0,"port %u ep undefined at ofs %ld",extport,(char *)vgadr - (char *)ep);
      vg_chk_def(vgadr,sp,sizeof(struct subportbase)-1)
      infocc(vgadr != 0,0,"port %u sp undefined at ofs %ld",subport,(char *)vgadr - (char *)sp);
      if (namelen) memcpy(sp->name,ep->name,namelen);
      if (inamelen) memcpy(sp->intname,ep->iname,inamelen);
    }
  }
  afree(extports,"ext");

  // resequence and arrange
  for (id = 0; id <= idhi; id++) id2ports[id] = hi32;

  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    id = pp->id;
    id2ports[id] = port;
    pp->rlat = lat2rad(pp->lat,latscale);
    pp->rlon = lon2rad(pp->lon,lonscale);
    for (subport = 0; subport < pp->subcnt; subport++) {
      sp = subports + pp->subofs + subport;
      sp->parent = port;
    }
  }
  for (subid = 0; subid <= subidhi; subid++) subid2ports[subid] = hi32;
  for (port = 0; port < subportcnt; port++) {
    sp = subports + port;
    subid = sp->subid;
    subid2ports[subid] = port;
    sp->rlat = lat2rad(sp->lat,latscale);
    sp->rlon = lon2rad(sp->lon,lonscale);
  }

  info(0,"read %u stops into %u ports", extportcnt,portcnt);
  info(0,"bbox lat %u - %u = %u scale %u",lolat,hilat,hilat-lolat,latscale);
  info(0,"bbox lon %u - %u = %u scale %u",lolon,hilon,hilon-lolon,lonscale);
  net->portcnt = portcnt;
  net->subportcnt = subportcnt;
  net->id2ports = id2ports;
  net->subid2ports = subid2ports;
  net->maxportid = idhi;
  net->maxsubportid = subidhi;
  net->latscale = latscale;
  net->lonscale = lonscale;
  net->latrange[0] = lolat;
  net->latrange[1] = hilat;
  net->lonrange[0] = lolon;
  net->lonrange[1] = hilon;
  return 0;
}

// expand regular sid part into localtime day map. times in days
static void expandsid(ub4 rsid,ub1 *map,ub4 maplen,ub4 t00,ub4 t0,ub4 t1,ub4 dstonof,ub4 dow,ub4 t0day)
{
  error_ge(t0day,7);
  ub4 tday = 0,t = t0 - t00;
  ub4 daymask = (1 << t0day);
  ub1 x,rs6 = rsid & 0x3f;

  vrb0(0,"rsid %u map %p base %u \ad%u start %u len %u",rsid,(void *)(map + t0),t00,t00,t0,t1 - t0);
  while (tday < t1 - t00 && tday < maplen) {
    error_nz_cc(map[tday],"rsid %x t %u/%u",rsid,tday,t1 - t00);
    x = rs6;
    if (tday >= t && (daymask & dow)) {
      if (dstonof && indst(t + t00,dstonof)) x |= 0xc0;
      else x |= 0x80;
    }
    map[tday] = x;
    // info(0,"t %u",t);
    if (daymask == (1 << 6)) daymask = 1;
    else daymask <<= 1;
    tday++;
  }
}

// service_id sid dow utcofs dst start end
static int rdexttimes(netbase *net,const char *dir)
{
  enum extresult res;
  struct extfmt *eft = talloc0(1,struct extfmt,0);
  const char *fname;

  ub4 rawsidcnt,sidcnt,vsidcnt;
  struct sidbase *sids,*sp;
  ub4 rsid,sid;
  int rv;
  char *buf,*p;
  ub4 len,linno,colno,namelen,valndx,valcnt,maxsid = 0;
  ub4 dow,t0,t1,t0_cd,t1_cd,t_cd,tbox0,tbox1,dtbox,t0wday = 0,tday0,tday1;
  ub4 daybox0,daybox1,t0days,t1days,tday,cnt,daycnt;
  ub4 hh,mm;
  ub4 utcofs12,utcofs,dstonof;
  ub4 t0lo = hi32,t1hi = 0;
  char *name;
  ub4 *vals;
  ub1 *sidmaps,*map,x,rs6;
  ub4 *rsidmap = NULL;
  ub4 maplen,allmaplen = 0,mapofs,addcnt,subcnt,addndx,subndx;
  ub4 namemax = sizeof(sids->name) - 1;
  ub4 timespanlimit = globs.engvars[Eng_periodlim];
  int initvars = 0;

  error_z(timespanlimit,0);

  fmtstring(eft->mf.name,"%s/times.txt",dir);
  fname = eft->mf.name;

  info0(User,"");
  info(0,"reading %s",fname);
  rv = readfile(&eft->mf,fname,1,0);
  if (rv) return 1;

  buf = eft->mf.buf;
  len = (ub4)eft->mf.len;
  rawsidcnt = linecnt(fname,buf,len);

  if (rawsidcnt == 0) return warning(0,"%s is empty",fname);
  error_ge(rawsidcnt,hi24);
  sidcnt = vsidcnt = 0;

  rawsidcnt++;
  sids = sp = mkblock(&net->sidmem,rawsidcnt,struct sidbase,Init0,"%u sids",rawsidcnt);

  maxsid = 0;
  tbox0 = tbox1 = dtbox = daybox0 = daybox1 = 0;
  sidmaps = NULL;
  mapofs = 0;

  net->timespanlimit = timespanlimit;

  vals = eft->vals;
  name = eft->name;

  do {
    res = nextchar(eft);

    switch(res) {

    case Newcmd:
      if (docmd(timevars,eft,fname)) return 1;
      if (feedstamp) net->feedstamp = feedstamp;
      if (feedlostamp) net->feedlostamp = feedlostamp;
      break;

    case Newitem:
      if (initvars == 0) {

        chkcmd(timevars,"times");

        if (timebox[1] < timebox[0]) {
          warning(0,"negative timebox from %u to %u",timebox[0],timebox[1]);
          timebox[1] = timebox[0] + 1;
        }
        tbox0 = timebox[0]; tbox1 = timebox[1];
        daybox0 = cd2day(tbox0);
        if (daybox0 >= 2) daybox0 -= 2; // account for max utcofs
        daybox1 = cd2day(tbox1) + 2 + maxtripdur;
        dtbox = daybox1 - daybox0;

        if (daybox0 > daybox1) {
          warn(0,"period start \ad%u after end \ad%u",daybox0,daybox1);
          daybox1 = daybox0 + maxtripdur + 1;
        }
        if (daybox1 - daybox0 < dtbox) timespanlimit = daybox1 - daybox0 + maxtripdur;
        dtbox = daybox1 - daybox0;
        tbox0 = timebox[0] = day2cd(daybox0);
        tbox1 = timebox[1] = day2cd(daybox1);
        info(0,"period start \ad%u end \ad%u %u days",daybox0,daybox1,dtbox);
        if (dtbox > timespanlimit) {
          warn(0,"timebox %u-%u limited to %u days",tbox0,tbox1,timespanlimit);
          daybox1 = daybox0 + timespanlimit;
          tbox1 = timebox[1] = day2cd(daybox1);
          dtbox = daybox1 - daybox0;
        }
        t0wday = cdday2wday(tbox0);
        error_ge_cc(t0wday,7,"startday %u",tbox0);
        info(Emp,"gross timebox %u-%u = %u days startday %u",tbox0,tbox1,daybox1 - daybox0,t0wday);
        info(0,"rsid range %u .. %u",sidrange[0],sidrange[1]);
        error_ge(sidrange[1],hi24);
        error_ge(dtbox,365 * 2);
        error_z(dtbox,0);
        error_ge((ub8)rawsidcnt * dtbox,hi32);
        allmaplen = rawsidcnt * dtbox;
        sidmaps = talloc(allmaplen,ub1,0,"time sidmap",dtbox);
        rsidmap = talloc0(sidrange[1] + 1,ub4,0xff);
        initvars = 1;
      }
      namelen = eft->namelen;
      valcnt = eft->valndx;
      linno = eft->linno;
      colno = eft->colno;
      error_gt(sidcnt+1,rawsidcnt,linno);
      if (valcnt < 7) return parserr(FLN,fname,linno,colno,eft,"expect svcid,sid,dow,utcofs,start,end,n+,n- args, found only %u args",valcnt);

      rsid = vals[0];
      dow = vals[1];
      utcofs12 = vals[2];
      dstonof = vals[3];
      t0_cd = vals[4];
      t1_cd = vals[5];
      addcnt = vals[6];
      subcnt = vals[7];

      error_eq(rsid,hi32);
      error_eq(dow,hi32);
      error_eq(utcofs12,hi32);
      error_eq(dstonof,hi32);
      error_eq(t0_cd,hi32);
      error_eq(t1_cd,hi32);
      error_z(t0_cd,rsid);
      error_z(t1_cd,rsid);
      error_gt(t0_cd,t1_cd,rsid);
      error_eq(addcnt,hi32);
      error_eq(subcnt,hi32);

      if (rsid > sidrange[1]) return parserr(FLN,fname,linno,colno,eft,"sid %u above range %us",rsid,sidrange[1]);
      if (rsid < sidrange[0]) return parserr(FLN,fname,linno,colno,eft,"sid %u below range %us",rsid,sidrange[0]);
      maxsid = max(maxsid,rsid);
      rs6 = rsid & 0x3f;

      valndx = 8;

      if (dow == 0 && addcnt == 0) {
        info(Iter|V0,"skip empty rsid %u delcnt %u",rsid,subcnt);
        rsidmap[rsid] = hi32 - 1;
        continue;
      }

      // overall date range in localtime days is daybox0 .. daybox1
      // sids are based on this
      vrb0(0,"rsid %u dow %x %u..%u +%u -%u",rsid,dow,t0_cd,t1_cd,addcnt,subcnt);

      if (utcofs12 < 100) { parsewarn(FLN,fname,linno,colno,"UTCoffset %d below lowest -1100", utcofs12 - 1200); utcofs12 = 1200; }
      else if (utcofs12 > 1400 + 1200) { parsewarn(FLN,fname,linno,colno,"UTCoffset %u above highest +1400", utcofs12 - 1200); utcofs12 = 1200; }
      hh = utcofs12 / 100;
      mm = utcofs12 % 100;
      utcofs = hh * 60 + mm;
      vrb0(0,"UTC offset %d from %u:%u - 12:00 dst %u",(int)utcofs - 12 * 60,hh,mm,dstonof);
      net->utcofs12_def = utcofs12;

      if (dstonof > 12311231) { parsewarn(FLN,fname,linno,colno,"dst %u above 1231.1231",dstonof); dstonof = 0; }
      if (dstonof && dstonof < 1010101) { parsewarn(FLN,fname,linno,colno,"dst %u below 0101.0101",dstonof); dstonof = 0; }

      if (addcnt > dtbox) {
        infovrb(timespanlimit > 356,0,"line %u sid %u has %u calendar entries, time range %u",linno,rsid,addcnt,dtbox);
      }
      if (subcnt > dtbox) {
        infovrb(timespanlimit > 356,0,"line %u sid %u has %u calendar entries, time range %u",linno,rsid,subcnt,dtbox);
      }
      if (timespanlimit == hi32 && valndx + addcnt + subcnt != valcnt) {
        parsewarn(FLN,fname,linno,colno,"expected 6 + %u + %u args, found %u",addcnt,subcnt,valcnt);
      }

      if (dow > 0x7f) return inerr(FLN,fname,linno,colno,"invalid dayofweek mask %x",dow);

      if (t0_cd < tbox0) {
        warninfo(timespanlimit == hi32,0,"line %u: sid %u has start date %u before %u",linno,rsid,t0_cd,tbox0);
        t0_cd = tbox0;
      }
      if (t1_cd > tbox1) {
        warninfo(timespanlimit == hi32,0,"line %u: sid %u has end date %u after %u",linno,rsid,t1_cd,tbox1);
        t1_cd = tbox1;
      }

      map = sidmaps + mapofs;
      error_ge(mapofs,allmaplen);
      error_ge(mapofs + dtbox,allmaplen);

      // expand the regular calendar
      maplen = dtbox;
      if (dow) {
        t0days = cd2day(t0_cd);
        t1days = cd2day(t1_cd) + 1; // make exclusive
        maplen = min(maplen,t1days - daybox0);
        info(V0,"expand at %u len %u",mapofs,maplen);
        if (t1days > t0days) expandsid(rsid,map,dtbox,daybox0,t0days,t1days,dstonof,dow,t0wday);
      } else {
        memset(map,rs6,maplen);
      }

      // add and remove individual items
      addndx = 0;
      while (addndx++ < addcnt && valndx < valcnt) {
        t_cd = vals[valndx++];
        if (t_cd < tbox0) {
          warninfo(timespanlimit == hi32,0,"line %u: sid %u has date %u before %u",linno,rsid,t0_cd,tbox0);
          continue;
        }
        else if (t_cd > tbox1) {
          warninfo(timespanlimit == hi32,0,"line %u: sid %u has end date %u after %u",linno,rsid,t1_cd,tbox1);
          continue;
        }
        tday = cd2day(t_cd);
        error_lt(tday,daybox0);
        error_ge(tday,daybox1);
        error_ge(tday - daybox0,maplen);
        vrb0(0,"rsid %x add %u - %u = %u at %u %lx",rsid,t_cd,tbox0,tday - daybox0,mapofs + tday - daybox0,(ub8)(map + tday - daybox0));
        x = map[tday - daybox0];
        error_ne(rs6,x & 0x3f);
        infocc(x & 0x80,Iter,"rsid %x dup add day %u",rsid,t_cd);
        x |= 0x80;
        if (dstonof && indst(tday,dstonof)) x |= 0x40;
        map[tday - daybox0] = x;
      }

      subndx = 0;
      while (subndx++ < subcnt && valndx < valcnt) {
        t_cd = vals[valndx++];
        if (t_cd < tbox0) {
          warninfo(timespanlimit == hi32,0,"line %u: sid %u has date %u before %u",linno,rsid,t_cd,tbox0);
          continue;
        }
        if (t_cd > tbox1) {
          warninfo(timespanlimit == hi32,0,"line %u: sid %u has end date %u before %u",linno,rsid,t1_cd,tbox1);
          continue;
        }
        tday = cd2day(t_cd);
        error_lt(tday,daybox0);
        error_gt(tday,daybox1,0);
        error_ge(tday - daybox0,maplen);
        x = map[tday - daybox0];
        error_ne(rs6,x & 0x3f);
        if (x & 0x80) {
          // infocc(rsid == 14,V0,"line %u rsid %x del day %u",linno,rsid,t_cd);
          map[tday - daybox0] = rs6;
        } else info(Iter|V0,"line %u rsid %x dup del day %u",linno,rsid,t_cd);
      }

      // determine range
      daycnt = 0;
      for (tday = 0; tday < maplen; tday++) {
        cnt = map[tday];
        error_ne_cc(rs6,cnt & 0x3f,"tday %u/%u rsid %x",tday,dtbox,rsid);
        if (cnt & 0x80) daycnt++;
      }
      tday0 = 0;
      while (tday0 < maplen && (map[tday0] & 0x80) == 0) tday0++;
      if (tday0 == maplen) {
        warninfo(globs.strict,0,"line %u: r.sid %u.%u has no service days %s",linno,rsid,sidcnt,name);
        rsidmap[rsid] = hi32 - 2;
        memset(map,0,maplen);
        continue;
      } else {
        t0_cd = day2cd(tday0 + daybox0);
        tday1 = maplen - 1;
        while (tday1 > tday0 && (map[tday1] & 0x80) == 0) tday1--;
        maplen = sp->maplen = tday1 + 1;
        sp->lt1day = maplen + daybox0;
        if (dtbox > maplen) memset(map + maplen,0,dtbox - maplen);
        t1_cd = day2cd(tday1 + daybox0 + 1);
        error_le(t1_cd,t0_cd);
        vsidcnt++;
        sp->daycnt = daycnt;
        sp->valid = 1;
        rsidmap[rsid] = sidcnt;
      }

      p = sp->dowstr;
      memcpy(p,".......",7);
      if (dow & 1) p[0] = 'm';
      if (dow & 2) p[1] = 't';
      if (dow & 4) p[2] = 'w';
      if (dow & 8) p[3] = 't';
      if (dow & 16) p[4] = 'f';
      if (dow & 32) p[5] = 's';
      if (dow & 64) p[6] = 's';

      t0 = yymmdd2min(t0_cd,utcofs);
      t1 = yymmdd2min(t1_cd,utcofs);

      t0lo = min(t0lo,t0);
      t1hi = max(t1hi,t1);

      rsidlog(rsid,"rsid \ax%u %u day\as in dow %x %u..%u \ad%u-\ad%u",rsid,daycnt,dow,t0_cd,t1_cd,t0,t1);
      info(V0,"line %u r.sid %u.%u start %u=%u %u day\as in dow %x %s len %u map %u %u..%u \ad%u-\ad%u name %s",
        linno,rsid,sidcnt,daybox0,day2cd(daybox0),daycnt,dow,sp->dowstr,maplen,mapofs,t0_cd,t1_cd,t0,t1,name);

      error_le(t1,t0);

      error_lt(t0,daybox0);

      sp->sid = sidcnt;
      sp->rsid = rsid;
      sp->t0 = t0;
      sp->t1 = t1;
      sp->dow = dow;
      sp->utcofs = utcofs;
      sp->lt0day = daybox0;
      sp->lt1day = daybox0 + maplen;
      sp->maplen = maplen;
      error_gt(t0,t1,linno);
      error_z(t1,t0);

      if (namelen > namemax) {
        parsewarn(FLN,fname,linno,colno,"name length %u exceeds max %u",namelen,namemax);
      }
      sp->namelen = fmtstring(sp->name,"%.*s",name,sizeof();
      if (namelen) memcpy(sp->name,name,namelen);
      sp->mapofs = mapofs;
      mapofs += maplen;
      sp++;
      sidcnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  freefile(&eft->mf);
  afree0(eft);

  if (sidcnt == 0) return error(0,"no sids from %u entries",rawsidcnt);

  if (maxsid > 100 * 1000 * 1000) warning(0,"max service id %u",maxsid);
  info(0,"max service id %u",maxsid);

  ub4 *rsid2sids = talloc(maxsid+1,ub4,0xff,"io rsid2sids",maxsid);
  ub4 *rsiddiag = talloc(maxsid+1,ub4,0,"io rsiddiag",maxsid);

  for (sid = 0; sid < sidcnt; sid++) {
    sp = sids + sid;
    rsid = sp->rsid;
    error_z(rsid,sid);
    error_gt(rsid,maxsid,0);
    if (rsid2sids[rsid] != hi32) warning(0,"service ID %u doubly defined", rsid);
    else rsid2sids[rsid] = sid;
  }
  net->rsid2sids = rsid2sids;
  net->rsiddiag = rsiddiag;
  net->rsidmap = rsidmap;
  error_zp(rsidmap,0);

  info(0,"read %u sids, %u valid, range \ad%u to \ad%u", sidcnt,vsidcnt,t0lo,t1hi);
  net->sidcnt = sidcnt;
  net->sids = sids;
  net->sidmaps = sidmaps;
  net->maxsid = maxsid;

  ub4 gt0,gt1;

  if (tbox0 && tbox1) {
    info(0,"overall gross day period %u - %u",tbox0,tbox1);
    gt0 = daybox0 * daymin;
    gt1 = daybox1 * daymin;
    if (gt0 > t0lo) { warning(0,"overall start \ad%u > \ad%u",gt0,t0lo); gt0 = t0lo; }
    if (gt1 < t1hi) { warninfo(timespanlimit > 365,0,"overall end \ad%u != \ad%u",gt1,t1hi); gt1 = t1hi; }
    if (gt1 <= gt0) { warning(0,"overall start %u beyond end %u",gt0,gt1); gt1 = gt0 + daymin; }
  } else { gt0 = t0lo; gt1 = t1hi; }
  net->t0 = gt0; net->t1 = gt1;
  msgopt("readsid"); info(0,"overall gross period \ad%u - \ad%u",gt0,gt1);

  return 0;
}

static int rdextagencies(netbase *net,const char *dir)
{
  enum extresult res;
  struct extfmt *eft = talloc0(1,struct extfmt,0);
  const char *fname;

  ub4 rawaidcnt,aidcnt;
  struct agencybase *routes,*rp;
  ub4 rrid,hirrid = 0,*rrid2rid = 0;
  int rv;
  char *buf;
  ub4 len,linno = 0,colno = 0,namelen,valcnt;
  ub4 rtype,reserve,fare,aid,hiaid = 0,rsvcnt = 0;
  char *name;
  ub4 *vals;
  enum txbkind tx;
  ub4 namemax = sizeof(rp->name) - 1;
  int initvars = 0;

  fmtstring(eft->mf.name,"%s/to-agencies.txt",dir);
  fname = eft->mf.name;

  info0(User,"");
  info(0,"reading %s",fname);

  rv = readfile(&eft->mf,fname,1,0);
  if (rv) return 1;

  buf = eft->mf.buf;
  len = (ub4)eft->mf.len;
  rawaidcnt = linecnt(fname,buf, len);

  if (rawaidcnt == 0) return warning(0,"%s is empty",fname);
  aidcnt = 0;

  rawridcnt++;
  routes = rp = mkblock(&net->ridmem,rawridcnt,struct agencybase,Init0,"%u routes",rawridcnt);

  vals = eft->vals;
  name = eft->name;

  do {
    res = nextchar(eft);

    switch(res) {

    case Newcmd:
      if (docmd(agencyvars,eft,fname)) return 1;
      break;

    case Newitem:
      if (initvars == 0) {
        chkcmd(agencyvars,"routes");

        hiraid = aidrange[1];
        if (rawaidcnt > hiraid) {
          parsewarn(FLN,fname,linno,colno,"hi raid %u < aidcnt %u",hiraid,rawaidcnt);
          hiraid = rawaidcnt;
        }
        error_eq(hiraid,hi32);
        raid2aid = talloc(hiraid+1,ub4,0xff,"net raid2aid",hiraid);
        initvars = 1;
      }
      namelen = eft->namelen;
      valcnt = eft->valndx;
      linno = eft->linno;
      colno = eft->colno;
      error_gt(ridcnt+1,rawridcnt,linno);
      if (valcnt < 5) return parserr(FLN,fname,linno,colno,eft,"expect rrid,rtype,res,aid,fare args, found only %u args",valcnt);

      raid = vals[0];

      utcofs12 = vals[2];
      dstonof = vals[3];

      tzname = svals[0];
      tznlen = svallens[0];

      error_eq(utcofs12,hi32);
      error_eq(dstonof,hi32);

      if (tznlen) {
        if (utcofs12 < 100) { parsewarn(FLN,fname,linno,colno,"UTCoffset %d below lowest -1100", utcofs12 - 1200); utcofs12 = 1200; }
        else if (utcofs12 > 1400 + 1200) { parsewarn(FLN,fname,linno,colno,"UTCoffset %u above highest +1400", utcofs12 - 1200); utcofs12 = 1200; }
        hh = utcofs12 / 100;
        mm = utcofs12 % 100;
        utcofs = hh * 60 + mm;
        info(0,"UTC offset %d from %u:%u - 12:00 dst %u",(int)utcofs - 12 * 60,hh,mm,dstonof);

        if (dstonof > 12311231) { parsewarn(FLN,fname,linno,colno,"dst %u above 1231.1231",dstonof); dstonof = 0; }
        if (dstonof && dstonof < 1010101) { parsewarn(FLN,fname,linno,colno,"dst %u below 0101.0101",dstonof); dstonof = 0; }

        ap->tzlen = copystr(ap->tzname,tzname);
      }

      if (namelen > namemax) {
        parsewarn(FLN,fname,linno,colno,"name length %u exceeds max %u",namelen,namemax);
      } else if (namelen == 0) {
        strcopy(ap->name,"(unnamed)");
        ap->namelen = 9;
      } else ap->namelen = copystr(ap->name,name);

      if (raid > hiraid) return parserr(FLN,fname,linno,colno,"raid %u > hiraid %u",raid,hiraid);
      else if (raid2aid[raid] != hi32) return parserr(FLN,fname,linno,colno,"duplicate raid %u",raid);
      raid2aid[raid] = aidcnt;
      ap->rrid = rrid;
      ap->aid = aid;
      ap->utcofs = utcofs12;
      ap->dstonof = dstonof;
      ap++;
      aidcnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  freefile(&eft->mf);
  afree0(eft);

  info(Emp,"%u agencies\as, %u reserved",ridcnt,rsvcnt);

  net->routes = routes;
  net->ridcnt = ridcnt;
  net->rrid2rid = rrid2rid;
  net->hirrid = hirrid;
  net->agencycnt = hiaid + 1;

  return 0;
}

// todo generalise
static enum txbkind rt2tx(ub4 rtype)
{
  switch(rtype) {
  case 0: case 1: case 2: case 5: case 6: case 7: return Railb;
  case 3: return Busb;
  case 4: return Ferryb;
  case 711: return Busb;    // shuttle
  case 1101: return Airintb;
  case 1102: return Airdomb;
  case 1500: return Taxib;
  default: return Unknownb;
  }
}

static int rdextroutes(netbase *net,const char *dir)
{
  enum extresult res;
  struct extfmt *eft = talloc0(1,struct extfmt,0);
  const char *fname;

  ub4 rawridcnt,ridcnt;
  struct routebase *routes,*rp;
  ub4 rrid,hirrid = 0,*rrid2rid = 0;
  int rv;
  char *buf;
  ub4 len,linno = 0,colno = 0,namelen,valcnt;
  ub4 rtype,reserve,fare,aid,hiaid = 0,rsvcnt = 0;
  char *name;
  ub4 *vals;
  enum txbkind tx;
  ub4 namemax = sizeof(rp->name) - 1;
  int initvars = 0;

  fmtstring(eft->mf.name,"%s/to-routes.txt",dir);
  fname = eft->mf.name;

  info0(User,"");
  info(0,"reading %s",fname);

  rv = readfile(&eft->mf,fname,1,0);
  if (rv) return 1;

  buf = eft->mf.buf;
  len = (ub4)eft->mf.len;
  rawridcnt = linecnt(fname,buf, len);

  if (rawridcnt == 0) return warning(0,"%s is empty",fname);
  ridcnt = 0;

  rawridcnt++;
  routes = rp = mkblock(&net->ridmem,rawridcnt,struct routebase,Init0,"%u routes",rawridcnt);

  vals = eft->vals;
  name = eft->name;

  do {
    res = nextchar(eft);

    switch(res) {

    case Newcmd:
      if (docmd(routevars,eft,fname)) return 1;
      break;

    case Newitem:
      if (initvars == 0) {
        chkcmd(routevars,"routes");

        hirrid = ridrange[1];
        if (rawridcnt > hirrid) {
          parsewarn(FLN,fname,linno,colno,"hi rrid %u < ridcnt %u",hirrid,rawridcnt);
          hirrid = rawridcnt;
        }
        error_eq(hirrid,hi32);
        rrid2rid = talloc(hirrid+1,ub4,0xff,"net rrid2rid",hirrid);
        initvars = 1;
      }
      namelen = eft->namelen;
      valcnt = eft->valndx;
      linno = eft->linno;
      colno = eft->colno;
      error_gt(ridcnt+1,rawridcnt,linno);
      if (valcnt < 5) return parserr(FLN,fname,linno,colno,eft,"expect rrid,rtype,res,aid,fare args, found only %u args",valcnt);

      rrid = vals[0];
      rtype = vals[1];
      reserve = vals[2];
      raid = vals[3];
      fare = vals[4];

      agency_id = svals[1];
      agency_idlen = svallens[1];

      error_eq(rrid,hi32);
      error_eq(rtype,hi32);
      error_eq(reserve,hi32);
      error_eq(raid,hi32);
      error_eq(fare,hi32);

      if (raid > hiraid) return parserr(FLN,fname,linno,colno,eft,"invalid raid %u above %u",raid,hiraid);
      aid = raid2aid[raid];
      if (aid == hi32) return parserr(FLN,fname,linno,colno,eft,"invalid raid %u",raid);

      if (reserve) rsvcnt++;

      if (namelen > namemax) {
        parsewarn(FLN,fname,linno,colno,"name length %u exceeds max %u",namelen,namemax);
      } else if (namelen == 0) {
        strcopy(rp->name,"(unnamed)");
        rp->namelen = 9;
      } else rp->namelen = copystr(rp->name,name);

      if (agency_idlen) copystr(rp->agency_id,agency_id);

      if (rrid > hirrid) return parserr(FLN,fname,linno,colno,"rrid %u > hirrid %u",rrid,hirrid);
      else if (rrid2rid[rrid] != hi32) return parserr(FLN,fname,linno,colno,"duplicate rrid %u",rrid);
      rrid2rid[rrid] = ridcnt;
      tx = rt2tx(rtype);
      rp->rrid = rrid;
      rp->rtype = rtype;
      rp->kind = tx;
      rp->reserve = (ub2)reserve;
      rp->fare = (ub2)fare;
      rp->aid = aid;
      rp++;
      ridcnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  freefile(&eft->mf);
  afree0(eft);

  info(Emp,"%u route\as, %u reserved",ridcnt,rsvcnt);

  net->routes = routes;
  net->ridcnt = ridcnt;
  net->rrid2rid = rrid2rid;
  net->hirrid = hirrid;
  net->agencycnt = hiaid + 1;

  return 0;
}

static int rdextxfers(netbase *net,const char *dir)
{
  enum extresult res;
  struct extfmt *eft = talloc(1,struct extfmt,0,"transfers",0);
  const char *fname;
  struct portbase *pdep,*ports = net->ports;
  ub4 *id2ports = net->id2ports;
  ub4 idcnt = net->maxportid;
  ub4 portcnt = net->portcnt;
  ub4 rawcnt,cnt;
  int rv;
  char *buf;
  ub4 len,linno = 0,colno = 0,namelen,valcnt;
  ub4 fromid,toid,fromport,toport,type,mintt;
  char *name;
  ub4 *vals;
  int initvars = 0;

  fmtstring(eft->mf.name,"%s/xfers.txt",dir);
  fname = eft->mf.name;

  info0(User,"");
  info(0,"reading %s",fname);

  rv = readfile(&eft->mf,fname,0,0);
  if (rv) return 1;

  len = (ub4)eft->mf.len;
  if (len == 0) {
    info(0,"optional %s not present or empty",fname);
    freefile(&eft->mf);
    afree0(eft);
    return 0;
  }

  buf = eft->mf.buf;
  rawcnt = linecnt(fname,buf, len);

  if (rawcnt == 0) {
    info(0,"%s is empty",fname);
    freefile(&eft->mf);
    afree0(eft);
    return 0;
  }
  cnt = 0;

  rawcnt++;
  struct xferbase *xp, *xfers = mkblock(&net->xfermem,rawcnt,struct xferbase,Init0,"%u transfers",rawcnt);
  xp = xfers;

  vals = eft->vals;
  name = eft->name;

  do {
    res = nextchar(eft);

    switch(res) {

    case Newcmd:
//      if (docmd(routevars,eft,fname)) return 1;
      break;

    case Newitem:
      if (initvars == 0) {
//        chkcmd(routevars,"routes");

        initvars = 1;
      }
      namelen = eft->namelen;
      valcnt = eft->valndx;
      linno = eft->linno;
      colno = eft->colno;
      error_gt(cnt+1,rawcnt,linno);
      if (valcnt < 4) return parserr(FLN,fname,linno,colno,eft,"expect from,to,type,mintt, found only %u args",valcnt);

      fromid = vals[0];
      toid = vals[1];
      type = vals[2];
      mintt = vals[3];

      error_gt_cc(fromid,idcnt,"line %u %s",linno,name);
      error_gt_cc(toid,idcnt,"line %u %s",linno,name);

      fromport = id2ports[fromid];
      toport = id2ports[toid];
      error_ge_cc(fromport,portcnt,"line %u %s",linno,name);
      error_ge_cc(toport,portcnt,"line %u %s",linno,name);

      pdep = ports + fromport;

      infocc(mintt,Iter,"%s %s %u-%u %u %u",pdep->name,name,fromport,toport,type,mintt);

      xp->fromport = fromport;
      xp->toport = toport;
      xp->type = (ub2)type;
      xp->mintt = (ub2)mintt;

      xp++;
      cnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  freefile(&eft->mf);
  afree0(eft);

  info(Emp,"%u transfer\as",cnt);

  net->xfers = xfers;
  net->xfercnt = cnt;

  return 0;
}

// equivalent to gtfs trips
static int rdextrides(netbase *net,const char *dir)
{
  enum extresult res;
  struct extfmt *eft = talloc0(1,struct extfmt,0);
  const char *fname;

  ub4 rawtidcnt,tidcnt;
  struct ridebase *rides,*rp;
  ub4 rtid,hirtid = 0,*rtid2tid = 0;
  ub4 cnt;
  int rv;
  char *buf;
  ub4 len,linno = 0,colno = 0,namelen,valcnt;
  char *name;
  ub4 *vals;
  ub4 namemax = sizeof(rp->name) - 1;
  int initvars = 0;

  fmtstring(eft->mf.name,"%s/rides.txt",dir);
  fname = eft->mf.name;

  info0(User,"");
  info(0,"reading %s",fname);

  rv = readfile(&eft->mf,fname,1,0);
  if (rv) return 1;

  buf = eft->mf.buf;
  len = (ub4)eft->mf.len;
  rawtidcnt = linecnt(fname,buf, len);

  if (rawtidcnt == 0) return warning(0,"%s is empty",fname);
  tidcnt = 0;

  rides = rp = alloc(rawtidcnt,struct ridebase,0,"rides",rawtidcnt);

  vals = eft->vals;
  name = eft->name;

  do {
    res = nextchar(eft);

    switch(res) {

    case Newcmd:
      // if (docmd(ridevars,eft,fname)) return 1;
      break;

    case Newitem:
      if (initvars == 0) {
        chkcmd(ridevars,"rides");

        hirtid = tidrange[1];
        if (rawtidcnt > hirtid) {
          parsewarn(FLN,fname,linno,colno,"hi rtid %u < tidcnt %u",hirtid,rawtidcnt);
          hirtid = rawtidcnt;
        }
        error_eq(hirtid,hi32);
        rtid2tid = talloc(hirtid+1,ub4,0xff,"net rtid2rid",hirtid);
        initvars = 1;
      }
      namelen = eft->namelen;
      valcnt = eft->valndx;
      linno = eft->linno;
      colno = eft->colno;
      error_gt(tidcnt+1,rawtidcnt,linno);
      if (valcnt < 2) return parserr(FLN,fname,linno,colno,eft,"expect rtid,cnt, found only %u arg\as",valcnt);

      rtid = vals[0];
      cnt = vals[1];

      error_eq(rtid,hi32);
      error_ge(cnt,hi16);

      if (namelen > namemax) {
        parsewarn(FLN,fname,linno,colno,"name length %u exceeds max %u",namelen,namemax);
      } else if (namelen == 0) {
        strcopy(rp->name,"(unnamed)");
        rp->namelen = 9;
      } else {
        rp->namelen = (ub2)namelen;
        memcpy(rp->name,name,namelen);
      }
      if (rtid > hirtid) { parsewarn(FLN,fname,linno,colno,"rtid %u > hirtid %u",rtid,hirtid); continue; }
      else if (rtid2tid[rtid] != hi32) { parsewarn(FLN,fname,linno,colno,"duplicate rtid %u",rtid); continue; }
      rtid2tid[rtid] = tidcnt;
      rp->rtid = rtid;
      rp->cnt = (ub2)cnt;
      rp++;
      tidcnt++;
      break;

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);  // each input char

  freefile(&eft->mf);
  afree0(eft);

  info(Emp,"%u ride\as",tidcnt);

  net->rides = rides;
  net->tidcnt = tidcnt;
  // net->rtid2tid = rtid2tid;
  // net->hirtid = hirtid;

  return 0;
}

// match with gtfstool
enum Zformat { Fmt_prvsid=1,Fmt_diftid=2,Fmt_diftdep=4,Fmt_diftarr=8,Fmt_prvdep=16,Fmt_prvarr=32,Fmt_rep=64 };

static int rdexthops(netbase *net,const char *dir)
{
  enum extresult res;
  struct extfmt *eft = talloc0(1,struct extfmt,0);
  const char *fname;

  ub4 hop,rawhop,rawhopcnt,hopcnt;
  ub4 portcnt,subportcnt;
  ub4 rid,rrid,ridcnt;
  ub4 chain,chaincnt;
  struct hopbase *hops,*hp;
  struct portbase *ports,*pdep,*parr;
  struct subportbase *subports,*psdep,*psarr;
  struct sidbase *sids,*sp;
  struct chainbase *chains = NULL,*cp;
  struct routebase *rp,*routes;
  ub4 *rtid2tid = NULL,*tid2rtid = NULL,*rtidrefs = NULL,*tidrrid = NULL,*tidhops = NULL;
  ub4 *id2ports, *subid2ports;
  ub4 rsid,sid,sidcnt,*rsid2sids,*rsiddiag;
  ub4 *rsidmap;
  int rv;
  char *buf;
  ub8 len;
  ub4 linno,colno,val,namelen,valcnt,id,maxid,hirrid,maxsid;
  ub4 depid,arrid,sdepid,sarrid,dep,arr,sdep,sarr,srdep,srarr,prvsdep,prvsarr,pid;
  ub4 trepivsec,trepstartsec,trependsec;
  ub4 tripno,tripnum,carrier,striplen;
  char *stripno;
  ub4 rtype,prvrrid = hi32,timecnt,fare;
  char *name,*dname,*aname;
  ub4 *vals;
  char *svals;
  ub4 *svallens;
  ub4 sndx = 0;
  ub4 namemax = sizeof(hops->name) - 1;
  ub4 kinds[Kindcntb];
  enum txbkind tx;

  ub4 *tbp,*tbp2,*timesbase = NULL;
  ub4 timespos = 0;
  ub4 rtid,tid,tdep,tarr,tripseq,tdepsec,tarrsec,prvsid,prvtid,prvtdep,prvtarr;
  ub4 t0,t1,ht0,ht1;
  ub4 fmt,vndx,tndx,tndx2;

  struct eta eta;

  aclear(kinds);

  fmtstring(eft->mf.name,"%s/hops.txt",dir);
  fname = eft->mf.name;

  info0(User,"");
  info(0,"reading %s",fname);
  rv = readfile(&eft->mf,fname,1,0);
  if (rv) return 1;

  buf = eft->mf.buf;
  len = eft->mf.len;
  rawhopcnt = linecnt(fname,buf,len);

  if (rawhopcnt == 0) return warning(0,"%s is empty",fname);
  hop = rawhop = chain = 0;

  hops = hp = mkblock(&net->hopmem,rawhopcnt,struct hopbase,Init0,"net hops");

  portcnt = net->portcnt;
  subportcnt = net->subportcnt;
  ports = net->ports;
  subports = net->subports;
  id2ports = net->id2ports;
  subid2ports = net->subid2ports;

  ub4 maxportid = net->maxportid;
  ub4 maxsubportid = net->maxsubportid;

  ub4 *rrid2rid = net->rrid2rid;

  rsidmap = net->rsidmap;
  rsid2sids = net->rsid2sids;
  rsiddiag = net->rsiddiag;
  sids = net->sids;
  sidcnt = net->sidcnt;
  maxsid = net->maxsid;

  routes = net->routes;
  ridcnt = net->ridcnt;

  maxid = hirrid = 0;

  vals = eft->vals;
  svals = eft->svals;
  svallens = eft->svallens;
  name = eft->name;

  int inited = 0;
  int isair;
  ub4 cumhoprefs = 0;
  chaincnt = 0;
  ub4 dupcnt,duptndx,duptcnt = 0,nominiv = 0 ;
  ub4 nosidcnt,nosidtcnt = 0;
  ub4 arrltdep = 0;

  int varsda;
  ub4 varsdacnt = 0;
  ub4 prvsdepid = 0,prvsarrid = 0;

  ub4 prvrid = 0;
  prvrrid = 0;

  do {

    res = nextchar(eft);
    switch(res) {

    case Newcmd:
      if (docmd(hopvars,eft,fname)) return msgprefix(1,NULL);
    break;

    case Newitem:
      if (inited == 0) {
        chkcmd(hopvars,"hops");
        error_z(rawtripcnt,0);

        if (sumtimes) {
          timesbase = net->timesbase = mkblock(&net->timesmem,sumtimes * Tentries,ub4,Init0,"time timebase %u",sumtimes);
        }
        chaincnt = 0;
        rtid2tid = talloc(hitripid + 1,ub4,0xff,"chain rtid2tid",hitripid);
        tid2rtid = talloc(rawtripcnt,ub4,0xff,"chain tid2rtid",rawtripcnt);
        tidhops  = talloc(rawtripcnt,ub4,0xff,"chain tidhops",rawtripcnt);
        rtidrefs = talloc(hitripid + 1,ub4,0,"chain triprefs",hitripid);
        tidrrid  = talloc(rawtripcnt,ub4,0,"chain triproutes",rawtripcnt);
        inited = 1;
      }
      error_zp(rtid2tid,hitripid);
      if (progress(&eta,"reading hop %u of %u, \ah%u time entries",rawhop,rawhopcnt,timespos)) return msgprefix(1,NULL);
      msgprefix(0,"hop %u ",rawhop);

      rawhop++;

      namelen = eft->namelen;
      valcnt = eft->valndx;

//      vrb(0,"%u values",valcnt);
      linno = eft->linno;
      colno = eft->colno;

      if (namelen > namemax) {
        parsewarn(FLN,fname,linno,colno,"name length %u exceeds max %u",namelen,namemax);
      } else if (namelen) hp->namelen = copystr(hp->name,name);

      error_gt(hop+1,rawhopcnt,linno);
      if (valcnt < 7) return parserr(FLN,fname,linno,colno,eft,"missing dep,arr,type,id,fare,cnt args, only %u",valcnt);
      id = vals[0];
      depid = vals[1];
      arrid = vals[2];
      rtype = vals[3];
      rrid  = vals[4];
      fare  = vals[5];
      timecnt = vals[6];

      error_eq(id,hi32);
      error_eq(depid,hi32);
      error_eq(arrid,hi32);
      error_eq(rtype,hi32);
      error_eq(timecnt,hi32);

      if (rrid == hi32) return inerr(FLN,fname,linno,colno,"hop %u has no route id",hop);
      else if (rrid > ridrange[1]) return inerr(FLN,fname,linno,colno,"hop %u has invalid route id",hop);

      if (hop && rrid < prvrrid) return inerr(FLN,fname,linno,colno,"unsorted route %u after %u",rrid,prvrrid);
      prvrrid = rrid;
      rid = rrid2rid[rrid];
      if (rid == hi32) return inerr(FLN,fname,linno,colno,"invalid route id %u",rrid);
      rp = routes + rid;
      aid = rp->aid;
      agp = agencies + aid;
      agtime = agp->tznlen;

      if (depid == arrid) return inerr(FLN,fname,linno,colno,"dep id %u,%x equal to arr id",depid,depid);
      if (depid > maxportid) return inerr(FLN,fname,linno,colno,"dep id %u above highest port id %u",depid,maxportid);
      else if (arrid > maxportid) return inerr(FLN,fname,linno,colno,"arr id %u above highest port id %u",arrid,maxportid);

      dep = id2ports[depid];
      if (dep == hi32) {
        sdep = subid2ports[depid];
        if (sdep >= subportcnt) return inerr(FLN,fname,linno,colno,"dep %u id %u above highest subport %u",sdep,depid,subportcnt);
        psdep = subports + sdep;
        hoplog(hop,0,"sdep %s",psdep->name);
        pid = psdep->id;
        dep = id2ports[pid];
        psdep->pid = dep;
        warn(0,"parent %u for %u %s",dep,sdep,psdep->name);
      } else { sdep = hi32; psdep = NULL; }
      if (dep >= portcnt) return inerr(FLN,fname,linno,colno,"dep %u id %u above highest port %u",dep,depid,portcnt);

      arr = id2ports[arrid];
      if (arr == hi32) {
        sarr = subid2ports[arrid];
        if (sarr == hi32) return inerr(FLN,fname,linno,colno,"unknwon arr for id %u name %s",arrid,name);
        if (sarr >= subportcnt) return inerr(FLN,fname,linno,colno,"arr %u above highest subport %u for %s",sarr,subportcnt,name);
        psarr = subports + sarr;
        hoplog(hop,0,"sarr %s",psarr->name);
        pid = psarr->id;
        arr = id2ports[pid];
        psarr->pid = arr;
        warn(0,"parent %u for %u %s",arr,sarr,psarr->name);
      } else { sarr = hi32; psarr = NULL; }
      if (arr >= portcnt) return inerr(FLN,fname,linno,colno,"arr %u above highest port %u",arr,portcnt);

      pdep = ports + dep;
      parr = ports + arr;
      dname = pdep->iname; aname = parr->name;

      fmtstring(hp->iname,"%.48s - %.48s",dname,aname);
      hoplog(hop,0,"%s - %s",dname,aname);

      if (dep == arr) return inerr(FLN,fname,linno,colno,"dep \ax%u id %u equal to arr %s",dep,depid,dname);

      if (agtime) {
        utcofsd = utcofsa = agp->utcofs;
        dstonofd = dstonofa = agp->dstonof;
      } else {
        utcofsd = pdep->utcofs;
        utcofsa = parr->utcofs;
        dstonofd = pdep->dstonof;
        dstonofa = parr->dstonof;
      }

//      hirrid = max(hirrid,hirrid);
      infocc(hop > 7188 && hop < 7192,0,"rrid %u",hirrid);

      tx = rt2tx(rtype);
      hp->kind = tx; kinds[tx]++;
      hp->carrier = hi32;

      if (timecnt && !sumtimes) return inerr(FLN,fname,linno,colno,"hop %u-%u has %u times, sumtimes var zero",depid,arrid,timecnt);
      if (timespos + timecnt > sumtimes) return inerr(FLN,fname,linno,colno,"hop %u has %u time entries, sum %u",hop,timecnt,sumtimes);

      error_zp(timesbase,0);
      if (timesbase == NULL) return msgprefix(1,NULL);
      if (timecnt * 4 > valcnt - 6) return parserr(FLN,fname,linno,colno,eft,"%u time entries, but only %u args",timecnt,valcnt);

      error_zp(timesbase,timecnt);
      tbp = timesbase + timespos * Tentries;

      if (timecntlimit != hi32 && timecnt > timecntlimit) {
        warn(Iter,"%s.%u: hop %u has %u time entries, max %u",fname,linno,hop,timecnt,timecntlimit);
        timecnt = timecntlimit;
      }

      tndx = 0; vndx = 7; sndx = 0;
      rsid = rtid = tdep = tarr = tdepsec = tarrsec = trepivsec = 0;
      sdepid = sarrid = 0;
      ht0 = hi32; ht1 = 0;
      dupcnt = 0;
      trepstartsec = trependsec = 0;

      varsda = 0;

      nosidcnt = 0;
      vrb0(0,"%u time entries, %u vals",timecnt,valcnt);

      if (timecnt == 0 || vndx + 6 >= valcnt) {
        warn(0,"line %u hop id %x no time entries %u-%u rrid %u %s to %s",linno,id,dep,arr,rrid,dname,aname);
        info(0,"timecnt %u vndx %u valcnt %u",timecnt,vndx,valcnt);
      }
      hoplog(hop,0,"%u time entries %u-%u rrid %u %s to %s",timecnt,dep,arr,rrid,dname,aname);

      while (vndx < valcnt && tndx < timecnt) {
        prvsid = rsid; prvtid = rtid; prvtdep = tdepsec; prvtarr = tarrsec;
        prvsdep = sdepid; prvsarr = sarrid;

        // first entry is not compressed
        fmt = vals[vndx++];
        error_eq(fmt,hi32);

        if (fmt & Fmt_prvdep) sdepid = prvsdep;
        else { if (vndx >= valcnt) break; sdepid = vals[vndx++]; error_eq(sdepid,hi32); }
        if (fmt & Fmt_prvarr) sarrid = prvsarr;
        else { if (vndx >= valcnt) break; sarrid = vals[vndx++]; error_eq(sarrid,hi32); }
        if (fmt & Fmt_prvsid) rsid = prvsid;
        else { if (vndx >= valcnt) break; rsid = vals[vndx++]; error_eq(rsid,hi32); }
        if (fmt & Fmt_rep) {
          if (vndx >= valcnt) break;
          trepivsec = vals[vndx++];
          error_eq(trepivsec,hi32);
          if (trepivsec < 60) {
            error(0,"hop %u freq rep %u %s - %s",hop,trepivsec,dname,aname);
            trepivsec = 0;
          }
          warncc(trepivsec > 86400 * 7,0,"hop %u headway %u",hop,trepivsec);
          if (vndx >= valcnt) break;
          trepstartsec = vals[vndx++];
          error_eq(trepstartsec,hi32);
          warncc(trepstartsec > 86400 + 3600,Iter,"hop %u interval start %u %s to %s",hop,trepstartsec,dname,aname);
          if (vndx >= valcnt) break;
          trependsec = vals[vndx++];
          error_eq(trependsec,hi32);
          warncc(trependsec > 86400 + 3600,Iter,"hop %u interval end %u %s to %s",hop,trepstartsec,dname,aname);
          info(V0,"hop %u tdep %u+%u freq %u end %u sid %u",hop,tdepsec,trepstartsec,trepivsec,trependsec,rsid);
          infocc(rawhopcnt < 500000,V0,"hop %u tdep \ad%u freq \at%u end \at%u sid %u",hop,tdepsec / 60,trepivsec / 60,trependsec / 60,rsid);
        } else trepivsec = 0;

        if (vndx + 3 >= valcnt) { warn(0,"vndx %u",vndx); break; }
        rtid = vals[vndx];

        stripno = svals + sndx * Maxname;
        striplen = svallens[sndx++];
        tdepsec = vals[vndx+1];
        tarrsec = vals[vndx+2];
        tripseq = vals[vndx+3];

        error_eq(rtid,hi32);
        error_eq(tdepsec,hi32);
        error_eq(tarrsec,hi32);
        error_eq(tripseq,hi32);

        vndx += 4;

        if (fmt & Fmt_diftid) rtid += prvtid;

        if (fmt & Fmt_diftdep) tdepsec += prvtdep;
        if (fmt & Fmt_diftarr) tarrsec += prvtarr;

        if ( (tdepsec % 60) || (tarrsec % 60) ) nominiv++;

        if (rsid > sidrange[1]) { nosidcnt++; warning(0,"skip service id %u above highest %u",rsid,sidrange[1]); continue; }
        error_gt(rsid,maxsid,0);
        sid = rsidmap[rsid];
        if (sid == hi32) { nosidcnt++; warning(0,"skip invalid service id %u",rsid); continue; }
        else if (sid == hi32 - 1) { nosidcnt++; info(V0,"skip empty service id %u",rsid); continue; }
        else if (sid == hi32 - 2) { nosidcnt++; info(V0,"skip empty service id %u",rsid); continue; }

        error_ne(sid,rsid2sids[rsid]);
        if (sid == hi32) {
          nosidcnt++;
          infocc(rsiddiag[rsid] == 0,0,"empty rsid %u skipped %s",rsid,hp->name);
          rsiddiag[rsid] = 1;
          continue;
        }

        error_ge(sid,sidcnt);
        sp = sids + sid;
        if (sp->valid == 0) { nosidcnt++; info(0,"sid %u skipped %s",sid,sp->name); continue; }

        sp->refcnt++;
        daycnt = sp->daycnt;

        lt0day = sp->lt0day;
        lt1day = sp->lt1day;
        lolt0day = min(lolt0day,lt0day);
        hilt1day = max(hilt1day,lt1day);

        hp->evcnt += daycnt; // tentative
        hoplog(hop,0,"rtid %u rsid %u dow %x.%u t \ad%u %s",rtid,rsid,sp->dow,daycnt,tdepsec / 60,sp->name);

        srdep = srarr = hi32;
        if (sdepid > maxsubportid) return inerr(FLN,fname,linno,colno,"dep id %u above highest port id %u",sdepid,maxsubportid);
        sdep = subid2ports[sdepid];
        if (sdep != hi32) {
          if (sdep >= subportcnt) return inerr(FLN,fname,linno,colno,"dep %u id %u above highest subport %u",sdep,sdepid,subportcnt);
          psdep = subports + sdep;
          hoplog(hop,0,"sdep %s",psdep->name);
          pid = psdep->id;
          if (id2ports[pid] != dep) return inerr(FLN,fname,linno,colno,"parent %u for sub %u differs from dep %u",id2ports[pid],sdep,dep);
          srdep = psdep->seq;
          if (srdep >= pdep->subcnt) return inerr(FLN,fname,linno,colno,"sub %u rsub %u not in %u subs",sdep,srdep,pdep->subcnt);

        } else psdep = NULL;

        if (sarrid > maxsubportid) return inerr(FLN,fname,linno,colno,"arr id %u above highest port id %u",sarrid,maxsubportid);
        sarr = subid2ports[sarrid];
        if (sarr != hi32) {
          if (sarr >= subportcnt) return inerr(FLN,fname,linno,colno,"arr %u id %u above highest subport %u",sarr,sarrid,subportcnt);
          psarr = subports + sarr;
          hoplog(hop,0,"sarr %s",psarr->name);
          pid = psarr->id;
          if (id2ports[pid] != arr) return inerr(FLN,fname,linno,colno,"parent %u for sub %u differss from arr %u",id2ports[pid],sarr,arr);
          srarr = psarr->seq;
          if (srarr >= parr->subcnt) return inerr(FLN,fname,linno,colno,"sub %u rsub %u not in %u subs",sarr,srarr,parr->subcnt);

        } else psarr = NULL;

        isair = 0;
        switch(tx) {
        case Unknownb: case Kindcntb: break;
        case Airintb: case Airdomb: isair = 1; if (psdep) psdep->air = 1; if (psarr) psarr->air = 1; break;
        case Railb: if (psdep) psdep->rail = 1; if (psarr) psarr->rail = 1; break;
        case Ferryb: if (psdep) psdep->ferry = 1; if (psarr) psarr->ferry = 1; break;
        case Busb: if (psdep) psdep->bus = 1; if (psarr) psarr->bus = 1; break;
        case Taxib: if (psdep) psdep->taxi = 1; if (psarr) psarr->taxi = 1; break;
        case Walkb: break;
        }

        if (isair && striplen < 3) { parsewarn(FLN,fname,linno,colno,"hop %u unknown flightno %s len %u pos %u %s %s",hop,stripno,striplen,sndx,dname,aname); striplen = 0; }
        if (isair && striplen > 2) {
          carrier = ((ub4)stripno[0]) << 8 | stripno[1];
          if (hp->carrier == hi32) hp->carrier = carrier;
          else if (hp->carrier != carrier) parsewarn(FLN,fname,linno,colno,"hop %u carrier %c%c vs %c%c %s %s",hop,hp->carrier >> 8,hp->carrier & 0xff,stripno[0],stripno[1],dname,aname);
          tripnum = 0;
          if (str2ub4(stripno + 2,&tripnum) == 0) parsewarn(FLN,fname,linno,colno,"hop %u unrecognised flightno %s %s %s",hop,stripno + 2,dname,aname);
          else if (tripnum >= hi24) parsewarn(FLN,fname,linno,colno,"hop %u unrecognised flightno %s %s %s",hop,stripno,dname,aname);
          tripno = (carrier << 16) | tripnum;
          // info(0,"line %u.%u %.2s %u",linno,colno,stripno,tripnum);
        } else {
          tripno = 0;
        }

        if (tarrsec < tdepsec) {
          parsewarn(FLN,fname,linno,colno,"hop %u arr %u before dep %u %s %s",hop,tarrsec,tdep,dname,aname);
          tarrsec = tdepsec;
          arrltdep++;
        } else if (tarrsec == tdepsec) {
          parsewarn(FLN,fname,linno,colno,"hop %u arr time %u equals dep %s %s",hop,tarrsec,dname,aname);
        }

        t0 = sp->t0;
        t1 = sp->t1;

        ht0 = min(ht0,t0);
        ht1 = max(ht1,t1);

        tbp2 = timesbase + timespos * Tentries;
        duptndx = 0;
        for (tndx2 = 0; tndx2 < tndx; tndx2++) { // check for duplicates
          if (tbp2[Tesid] == sid
//            && tbp2[Tetid] == tid
            && tbp2[Tetdep] == tdepsec
            && tbp2[Tetarr] == tarrsec) {
            duptndx = 1;
            break;
          }
          tbp2 += Tentries;
        }

        // tentative
        error_gt(rtid,hitripid,hop);
        tid = rtid2tid[rtid];
        if (tid == hi32) {
          error_ge(chaincnt,rawtripcnt);
          tid = chaincnt;
        }

        if (duptndx) {
          dupcnt++;
          info(Iter|V0,"line %u hop id %x dup time sid %u tid %u and %u %s to %s",linno,id,sid,tid,tbp2[Tetid],dname,aname);
          info(Iter|V0,"index.seq %u.%u and %u.%u tdep %x %u tarr %x %u",
            tndx,tripseq,tndx2,tbp2[Teseq],tdepsec,tdepsec / 60,tarrsec,tarrsec / 60);
          continue;
        }

        // prepare chains
        error_gt(rtid,hitripid,hop);
        tid = rtid2tid[rtid];
        if (tid == hi32) {
          error_ge(chaincnt,rawtripcnt);
          tid = chaincnt++;
          rtid2tid[rtid] = tid;
          tid2rtid[tid] = rtid;
          tidhops[tid] = hop;
          vrb0(Notty|Noiter,"new r.tid %u.%u",rtid,tid);
        }
        rtidrefs[rtid]++;
        tidrrid[tid] = rrid;
        cumhoprefs++;

        if (tndx) {
          if (sdepid != prvsdepid || sarrid != prvsarrid) varsda = 1;
        } else {
          hp->srdep = (ub2)srdep;
          hp->srarr = (ub2)srarr;
        }
        prvsdepid = sdepid;
        prvsarrid = sarrid;

        tbp[Tesid] = sid;
        tbp[Tetid] = tid;
        tbp[Tetripno] = tripno;

        tbp[Tetdep] = tdepsec;
        tbp[Tetarr] = tarrsec;
        tbp[Terepiv] = trepivsec;
        tbp[Terepstart] = trepstartsec;
        tbp[Terepend] = trependsec;

        tbp[Teseq] = tripseq;
        tbp[Tesdep] = srdep;
        tbp[Tesarr] = srarr;

        tbp += Tentries;
        tndx++;
      } // each time entry

      if (tndx == 0) {
        warn(0,"line %u hop id %x none from %u time entries %u dups %u nosid %u-%u rrid %u %s to %s",linno,id,timecnt,dupcnt,nosidcnt,dep,arr,rrid,dname,aname);
        continue;
      }

      if (tndx + dupcnt + nosidcnt != timecnt) {
        warn(0,"hop %u %u from %u time entries %u dups %u nosid",hop,tndx,timecnt,dupcnt,nosidcnt);
        info(0,"vndx %u valcnt %u",vndx,valcnt);
      }
      if (tndx != timecnt) {
        info(Iter|V0,"hop %u %u from %u time entries %u dups %u nosid",hop,tndx,timecnt,dupcnt,nosidcnt);
      }
      timecnt = tndx;
      duptcnt += dupcnt;
      nosidtcnt += nosidcnt;
      info(Iter|V0|CC0,"%u dup times",dupcnt);

      error_le(ht1,ht0);

      hp->t0 = ht0;
      hp->t1 = ht1 + 1440; // tdep can be above 24h
      hoplog(hop,0,"t range %u-%u \ad%u \ad%u",ht0,ht1,ht0,ht1);

      pdep->ndep++;
      parr->narr++;

      if (psdep) psdep->ndep++;
      if (psarr) psarr->narr++;

      if (pdep->parentsta) vrb(0,"hop %u dport %u %u %s",id,dep,pdep->id,dname);
      if (parr->parentsta) vrb(0,"hop %u aport %u %u %s",id,arr,parr->id,aname);

      hp->id  = id;  // = gtfstool seqno
      hp->dep = dep;
      hp->arr = arr;

      hp->fare = (ub2)fare;

// todo generalise
      switch(tx) {
      case Unknownb: case Kindcntb: parsewarn(FLN,fname,linno,colno,"unknown route type %u for %s",rtype,name); break;
      case Airintb: case Airdomb: pdep->air = parr->air = 1; if (psdep) psdep->air = 1; if (psarr) psarr->air = 1; break;
      case Railb: pdep->rail = parr->rail = 1; if (psdep) psdep->rail = 1; if (psarr) psarr->rail = 1; break;
      case Ferryb: pdep->ferry = parr->ferry = 1; if (psdep) psdep->ferry = 1; if (psarr) psarr->ferry = 1; break;
      case Busb: pdep->bus = parr->bus = 1; if (psdep) psdep->bus = 1; if (psarr) psarr->bus = 1; break;
      case Taxib: pdep->taxi = parr->taxi = 1; break;
      case Walkb: parsewarn(FLN,fname,linno,colno,"unsupported route type %u for %s",rtype,name); break;
      }

      hp->rrid = rrid;

      rid = rrid2rid[rrid];
      error_eq(rid,hi32);
      hp->rid = rid;
      error_lt_cc(rid,prvrid,"hop %u rrid %u/%u",hop,rrid,prvrrid);
      prvrid = rid;

      maxid = max(maxid,id);
      hp->timespos = timespos;
      hp->timecnt = timecnt;
      hp->varsda = (ub2)varsda;
      timespos += timecnt;
      if (varsda) {
        info(V0|Iter,"rid %u var sda %s",rid,hp->name);
        varsdacnt++;
      }
      hp++;
      hop++;
      msgprefix(0,NULL);

    break;  // newitem

    case Next: break;
    case Eof: break;
    case Parserr: return 1;
    }

  } while (res < Eof);

  hopcnt = hop;
  info(0,"\ah%u time entries, \ah%u duplicate \ah%u nosid",timespos,duptcnt,nosidtcnt);
  info(CC0,"\ah%u of \ah%u hops with arrival before departure",arrltdep,hopcnt);
  info(CC0,"\ah%u of \ah%u hops with variable sub dep,arr \ap%lu%lu",varsdacnt,hopcnt,(ub8)varsdacnt,(ub8)hopcnt);
  info(CC0,"\ah%u time entries not on minute boundary",nominiv);

  freefile(&eft->mf);
  afree0(eft);

  if (hopcnt == 0) return error(0,"0 hops from %u",rawhopcnt);

  if (hirrid != net->hirrid) {
    warninfo(hirrid > net->hirrid,0,"hi rrid %u vs %u",hirrid,net->hirrid);
    hirrid = net->hirrid;
  }

  ub4 cnt,ridhicnt = 0,ridhihop = hi32;

  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    rid = hp->rid;
    rp = routes + rid;
    hp->fare += rp->fare;
    cnt = rp->hopcnt + 1;
    rp->hopcnt = cnt;
    hoplog(hop,0,"r.rid %u.%u %s",hp->rrid,rid,rp->name);

    if (cnt > ridhicnt) { ridhicnt = cnt; ridhihop = hop; }
  }
  if (ridhihop != hi32) {
    hp = hops + ridhihop;
    rp = routes + hp->rid;
    info(0,"r.rid %u.%u has %u hop\as on route %s",hp->rrid,hp->rid,ridhicnt,rp->name);
  }

  for (rid = 0; rid < ridcnt; rid++) {
    rp = routes + rid;
    cnt = rp->hopcnt;
    rrid = rp->rrid;
    if (cnt == 0) info(Iter,"r.rid %u.%u has no hops %s",rrid,rid,rp->name);
    else if (cnt == 1) {
      vrb0(0,"r.rid %u.%u has 1 hop %s",rrid,rid,rp->name);
    } else infovrb(cnt > 150,Iter|V0,"r.rid %u.%u has %u hops %s",rrid,rid,cnt,rp->name);
  }

// check for duplicates
  ub4 hop2,rid2,hdupcnt = 0,hduprcnt = 0;
  ub8 x8;
  iadrbase danet;

  oclear(danet);
  if (mkiadr0(&danet,portcnt,portcnt,ub8,10000,8,"netio danet")) return 1;
  setiadropts(&danet,Iadr_defhi|Iadr_okdup);

  for (hop = 0; hop < hopcnt; hop++) {
    if (progress(&eta,"p1 check hop %u of %u, %u dups",hop,hopcnt,hdupcnt)) return 1;

    hp = hops + hop;
    dep = hp->dep;
    arr = hp->arr;
    if (iadrinc(&danet,dep,arr,0)) return 1;
  }
  info(CC0,"\ah%u count overflows",danet.cntovf);
  if (mkiadr1(&danet)) return 1;

  for (hop = 0; hop < hopcnt; hop++) {
    if (progress(&eta,"p2 check hop %u of %u, %u dups",hop,hopcnt,hdupcnt)) return 1;

    hp = hops + hop;
    dep = hp->dep;
    arr = hp->arr;
    rid = hp->rid;
    x8 = rdiadr8(&danet,dep,arr);
    rid2 = (ub4)x8;
    if (rid2 == hi32) wriadr8(&danet,dep,arr,((ub8)hop << 32) | rid);
    else if (rid == rid2) {
      hdupcnt++;
      hop2 = (ub4)(x8 >> 32);
      warn(0,"duplicate hop %u,%u da %u-%u r.rid %u.%u",hop,hop2,hp->dep,hp->arr,hp->rrid,rid);
    } else hduprcnt++;
  }

  warn(CC0,"%u duplicate hop\as",hdupcnt);
  info(CC0,"\ah%u of \ah%u hop\as with identical dep,arr",hduprcnt,hopcnt);

  net->timescnt = timespos;

  for (tx = 0; tx < Kindcntb; tx++) {
    val = kinds[tx];
    if (val) info(0,"%u %s hop\as",val,kindnames[tx]);
  }

  info(Emp,"%u hops, %u time entries",hopcnt,sumtimes);

  ub4 sidrefs = 0;

  for (sid = 0; sid < sidcnt; sid++) {
    sp = sids + sid;
    if (sp->refcnt) sidrefs++;
    else warninfo(net->timespanlimit > 365,Iter,"sid %x not referenced %s",sp->sid,sp->name);
  }
  if (sidrefs < sidcnt) info(0,"%u sid\as not referenced",sidcnt - sidrefs); // todo filter ?

  if (maxid > 100 * 1000 * 1000) warning(0,"max hop id %u",maxid);
  ub4 *id2hops = talloc0(maxid+1,ub4,0xff);
  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    id = hp->id;
    error_gt(id,maxid,hop);
    if (id2hops[id] != hi32) warning(0,"hop ID %u doubly defined", id);
    else id2hops[id] = hop;
  }
  afree0(id2hops);

  doconstats(ports,portcnt);

  info(0,"read %u hops",hopcnt);
  net->hopcnt = hopcnt;
  net->hops = hops;
  net->hirrid = hirrid;

  net->tid2rtid = tid2rtid;

  net->hitripid = hitripid;

  if (chaincnt == 0) {
    afree(rtid2tid,"rtid2tid");
    return info0(0,"0 chains");
  }

  ub4 nilchains = 0;
  chains = alloc(chaincnt,struct chainbase,0,"chain",chaincnt);
  for (rtid = 0; rtid <= hitripid; rtid++) {
    tid = rtid2tid[rtid];
    if (tid == hi32) continue;
    rrid = tidrrid[tid];
    cp = chains + tid;
    cp->hoprefs = rtidrefs[rtid];
    if (cp->hoprefs == 0) nilchains++;
    error_nz(cp->rtid,rtid);
    cp->rtid = rtid;
    // info(Noiter|Notty,"r.tid %u.%u",rtid,tid);
    cp->rid = rrid2rid[rrid];
    cp->firsthop = tidhops[tid];
  }
  for (tid = 0; tid < chaincnt; tid++) {
    cp = chains + tid;
    error_z(cp->rtid,rtid);
  }

  afree0(rtid2tid);
  afree0(rtidrefs);
  afree0(tidhops);

  info(CC0,"\ah%u of \ah%u chains without hops",nilchains,chaincnt);
  info(0,"%u chain\as",chaincnt);

  ub4 sport,port,sportcnt = net->subportcnt;
  ub4 portsair = 0,portsrail = 0,portsbus = 0,portsferry = 0,portstaxi = 0;
  struct portbase *pp;
  struct subportbase *spp,*sports = net->subports;
  for (sport = 0; sport < sportcnt; sport++) {
    spp = sports + sport;
    spp->modes = sportmodes(spp);
//    if (spp->air) portsair++;
//    if (spp->rail) portsrail++;
//    if (spp->bus) portsbus++;
//    if (spp->ferry) portsferry++;
//    if (spp->taxi) portstaxi++;
  }
  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    pp->modes = portmodes(pp);
    if (pp->air) portsair++;
    if (pp->rail) portsrail++;
    if (pp->bus) portsbus++;
    if (pp->ferry) portsferry++;
    if (pp->taxi) portstaxi++;
  }
  info(0,"ports air \ah%u  rail \ah%u  bus \ah%u  ferry \ah%u  taxi \ah%u",portsair,portsrail,portsbus,portsferry,portstaxi);

  net->rawchaincnt = chaincnt;
  net->chainhopcnt = cumhoprefs;
  net->chains = chains;

  return 0;
}

int readextnet(netbase *net,const char *dir)
{
  int rv;

  info(0,"reading base net in tripover external format from dir %s",dir);

  rsid2logcnt = getwatchitems("rsid",rsids2log,Elemcnt(rsids2log));
  hop2logcnt = getwatchitems("hop",hops2log,Elemcnt(hops2log));

  hoplog(hi32,1,"%c",0);

  rv = rdextagencies(net,dir);
  if (rv) return rv;

  rv = rdextports(net,dir);
  if (rv) return rv;

  rv = rdexttimes(net,dir);
  if (rv) return rv;

  rv = rdextroutes(net,dir);
  if (rv) return rv;

  rv = rdextrides(net,dir);
  if (rv) return rv;

  rv = rdextxfers(net,dir);
  if (rv) return rv;

  rv = rdexthops(net,dir);
  infocc(rv != 1 && rv != Parserr,0,"done reading base net in external format, status %d",rv);
  if (rv) return rv;

  info(Emp,"\ah%u ports \ah%u routes \ah%u chains",net->portcnt,net->ridcnt,net->rawchaincnt);

  if (globs.writext) rv = net2ext(net);
  if (globs.writpdf) net2pdf(net);
  return rv;
}

static int closefds(int rv,int fd1,int fd2,const char *name1,const char *name2)
{
  if (fd1 != -1) fileclose(fd1,name1);
  if (fd2 != -1) fileclose(fd2,name2);
  return rv;
}

static ub4 lat2ext(ub4 lat) { return lat; }
static ub4 lon2ext(ub4 lon) { return lon; }

// write port reference for name and lat/lon lookup
int wrportrefs(netbase *net,ub4 *bbox)
{
  int fd,fd2;
  char buf[4096];
  ub4 pos,x,y;
  ub4 scnt,sofs;
  ub4 buflen = sizeof(buf);

  struct portbase *pp,*ports = net->ports;
  struct subportbase *spp,*sports = net->subports;

  ub4 port,sport,wportcnt = 0,portcnt = net->portcnt;
  const char *portsname = "portrefs.txt"; // user ports
  const char *pportsname = "pportrefs.txt"; // planning ports

  char nowstr[64];
  const char *tz;

#ifdef NOW
  sec70toyymmdd(NOW,10,nowstr,sizeof(nowstr));
  tz = "utc";
#else
  strcopy(nowstr,__DATE__);
  tz = "localtime";
#endif

  info(0,"writing %u-ports reference ",portcnt);

  fd = filecreate(portsname,1);
  if (fd == -1) return 1;
  fd2 = filecreate(pportsname,1);
  if (fd2 == -1) return closefds(1,fd,-1,portsname,pportsname);

  pos = fmtstring(buf,"# %s - tripover port name and lat/lon lookup table\n\n",portsname);

  pos += mysnprintf(buf,pos,buflen,"# written by tripover version %u.%u  %s %s\n\n", Version_maj,Version_min,nowstr,tz);
  pos += mysnprintf(buf,pos,buflen,"# %u ports\n\n",portcnt);

  pos += mysnprintf(buf,pos,buflen,".utcofs\t%u\n\n",net->utcofs12_def);

  pos += mysnprintf(buf,pos,buflen,".latscale\t%u\n",net->latscale);
  pos += mysnprintf(buf,pos,buflen,".lonscale\t%u\n\n",net->lonscale);

  pos += mysnprintf(buf,pos,buflen,".minlat\t%u\n",bbox[Minlat]);
  pos += mysnprintf(buf,pos,buflen,".maxlat\t%u\n",bbox[Maxlat]);
  pos += mysnprintf(buf,pos,buflen,".minlon\t%u\n",bbox[Minlon]);
  pos += mysnprintf(buf,pos,buflen,".maxlon\t%u\n\n",bbox[Maxlon]);

  pos += mysnprintf0(buf,pos,buflen,"# gid\tname\tlat\tlon\tmodes\n\n");

  if (fileswrite(fd,fd2,buf,pos,portsname)) return 1;

  // write plain ports as-is, members only for parents
  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    if (pp->ndep == 0 && pp->narr == 0) continue;

    y = lat2ext(pp->lat);
    x = lon2ext(pp->lon);

    scnt = pp->subcnt;
    pos = fmtstring(buf,"%u\t%u\t%s\t%u\t%u\t%u\t%u\n", port,port,pp->name,y,x,portmodes(pp),pp->stopid);
    if (scnt == 0) {
      if (fileswrite(fd,fd2,buf,pos,portsname)) return 1;
      wportcnt++;
      continue;
    }
    if (filewrite(fd2,buf,pos,portsname)) return closefds(1,fd,-1,portsname,pportsname); // parent only for pports, subs otherwise

    sofs = pp->subofs;
    for (sport = 0; sport < scnt; sport++) {
      spp = sports + sofs + sport;
      y = lat2ext(spp->lat);
      x = lon2ext(spp->lon);
      pos = fmtstring(buf,"%u\t%u\t%s\t%u\t%u\t%u\t%u\n",port,sofs + sport + portcnt,spp->name,y,x,sportmodes(spp),spp->stopid); // use parent port to make alias
      if (filewrite(fd,buf,pos,portsname)) return closefds(1,-1,fd2,portsname,pportsname);
      wportcnt++;
    }
  }
  closefds(0,fd,fd2,portsname,pportsname);
  return info(0,"wrote %u ports+subports to %s",wportcnt,portsname);
}

int net2ext(netbase *net)
{
  int fd;
  char buf[1024];
  ub4 pos,x,y;
  ub4 dec = globs.extdec;

  struct hopbase *hp,*hops = net->hops;
  struct portbase *pp,*ports = net->ports;

  ub4 hop,hopcnt = net->hopcnt;
  ub4 port,portcnt = net->portcnt;
  const char *portsname = "ports.txt";
  const char *hopsname = "hops.txt";

  info(0,"writing %u-ports %u-hops base net to dir '.' in external format",portcnt,hopcnt);

  fd = filecreate(portsname,1);
  if (fd == -1) return 1;

  pos = fmtstring(buf,"# hops %u ports %u\n# id name lat lon\n",hopcnt,portcnt);
  if (filewrite(fd,buf,pos,portsname)) return 1;

  // temporary: port as number
  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    y = lat2ext(pp->lat);
    x = lon2ext(pp->lon);
    if (dec) pos = fmtstring(buf,"D%u\t%s\tD%u\t%u\n", pp->id,pp->name,y,x);
    else pos = fmtstring(buf,"%x\t%s\t%x\t%x\n", pp->id,pp->name,y,x);
    if (filewrite(fd,buf,pos,portsname)) return 1;
  }
  fileclose(fd,portsname);
  info(0,"wrote %u ports to %s",portcnt,portsname);

  fd = filecreate(hopsname,1);
  if (fd == -1) return 1;

  pos = fmtstring(buf,"# hops %u ports %u\n# id dep arr\n",hopcnt,portcnt);
  if (filewrite(fd,buf,pos,hopsname)) return 1;

  for(hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    if (dec) pos = fmtstring(buf,"%s\tD%u\tD%u\tD%u\n",hp->name,hop,hp->dep,hp->arr);
    else pos = fmtstring(buf,"%s\t%x\t%x\t%x\n",hp->name,hop,hp->dep,hp->arr);
    if (filewrite(fd,buf,pos,hopsname)) return 1;
  }
  fileclose(fd,hopsname);
  info(0,"wrote %u hops to %s",hopcnt,hopsname);

  info(0,"done writing %u-ports %u-hops base net to dir '.' in external format",portcnt,hopcnt);

  return 0;
}

// write network as page content
static ub4 addnetpdf(netbase *net, char *buf, ub4 len)
{
  struct portbase *pp,*pdep,*parr,*ports = net->ports;
  struct hopbase *hp,*hops = net->hops;
  ub4 port,portcnt = net->portcnt;
  ub4 hop,hopcnt = net->hopcnt;
  ub4 x,y,x0,y0,x1,y1,arr,dep;
  ub4 lolon,lolat,hilon,hilat,dlon,dlat;
  ub4 pos,n;

  pos = mysnprintf0(buf,0,len,"BT /F1 18 Tf 25 25 Td (title) Tj ET\n");

  pos += mysnprintf0(buf,pos,len,"BT /F1 16 Tf\n");

  lolon = net->lonrange[0];
  hilon = net->lonrange[1];
  lolat = net->latrange[0];
  hilat = net->latrange[1];
  dlon = max(1,hilon - lolon);
  dlat = max(1,hilat - lolat);

  if (portcnt > pdfmaxports) {
    info(0,"limiting %u ports to %u for pdf",portcnt,pdfmaxports);
    portcnt = pdfmaxports;
  }
  if (hopcnt > pdfmaxhops) {
    info(0,"limiting %u hops to %u for pdf",hopcnt,pdfmaxhops);
   hopcnt = pdfmaxhops;
  }

  // temporary: port as number
  for (port = 0; port < portcnt; port++) {
    pp = ports + port;
    y = lat2pdf(pp->lat,lolat,dlat);
    x = lon2pdf(pp->lon,lolon,dlon);
    n = mysnprintf(buf,pos,len,"1 0 0 1 %u %u Tm (%u) Tj ", x,y,port);
    if (n == 0) break;
    pos += n;
  }
  pos += mysnprintf0(buf,pos,len,"ET\n");

  pos += mysnprintf0(buf,pos,len,"1 w\n");

  // draw direct connection as straight line
  for (hop = 0; hop < hopcnt; hop++) {
    hp = hops + hop;
    dep = hp->dep;
    arr = hp->arr;
    pdep = ports + dep;
    parr = ports + arr;
    y0 = lat2pdf(pdep->lat,lolat,dlat);
    x0 = lon2pdf(pdep->lon,lolon,dlon);
    y1 = lat2pdf(parr->lat,lolat,dlat);
    x1 = lon2pdf(parr->lon,lolon,dlon);
    n = mysnprintf(buf,pos,len,"%u %u m %u %u l s\n",x0,y0,x1,y1);
    if (n == 0) break;
    pos += n;
  }
  error_gt(pos,len,0);
  if (pos == len) warning(0,"pdf output buffer limit \ah%u reached: truncated", len);
  return pos;
}

/* write graphic representation of network:
  ports, hops
  currently single page only
 */
static ub4 maxcontent = 64 * 1024 * 1024;

int net2pdf(netbase *net)
{
static char pagebuf[64 * 1024];

  int fd;
  ub4 pos,xpos,cpos,xrefpos,obj;
  ub4 plen = sizeof pagebuf;
  ub4 xref[16];
  block contentblk;
  char *content;
  enum objnos { pdfnil, pdfcat, pdftree,pdfnode,pdfcontent, pdflast };
  const char *name = "net.pdf";

  info(0,"writing %u-ports %u-hops base net to %s in pdf format",net->portcnt,net->hopcnt,name);

  fd = filecreate("net.pdf",1);
  if (fd == -1) return 1;

  pos = mysnprintf0(pagebuf,0,plen,"%%PDF-1.4\n");

  // patterned after simple examples in PDF reference
  xref[pdfcat] = pos;
  pos += mysnprintf(pagebuf,pos,plen,"%u 0 obj\n << /Type /Catalog /Pages %u 0 R >>\nendobj\n",pdfcat,pdftree);

  xref[pdftree] = pos;
  pos += mysnprintf(pagebuf,pos,plen,"%u 0 obj\n << /Type /Pages /Kids [%u 0 R] /Count 1 >>\nendobj\n", pdftree,pdfnode);

  xref[pdfnode] = pos;
  pos += mysnprintf(pagebuf,pos,plen,"%u 0 obj\n << /Type /Page /Parent %u 0 R "
    "/MediaBox [0 0 %u %u] /Contents %u 0 R /Resources"
    " << /Font << /F1 << /Type /Font /Subtype /Type1 /BaseFont /Helvetica >> >> >> >>\n"
    "endobj\n", pdfnode,pdftree,pdfscale_lon, pdfscale_lat,pdfcontent);

  xref[pdfcontent] = pos;

  xpos = pos;
  if (filewrite(fd,pagebuf,pos,name)) return 1;

  content = mkblock(&contentblk,maxcontent,char,Noinit,"pdf content buffer");

  cpos = addnetpdf(net,content,maxcontent);

  pos = mysnprintf(pagebuf,0, plen,"%u 0 obj\n << /Length %u >>\nstream\n", pdfcontent, cpos);
  if (filewrite(fd,pagebuf,pos,name)) return 1;
  xpos += pos + cpos;

  if (filewrite(fd,content,cpos,name)) return 1;

  pos = mysnprintf0(pagebuf,0,plen,"endstream\nendobj\n");

  xrefpos = xpos + pos;
  pos += mysnprintf(pagebuf,pos,plen,"xref\n0 %u\n",pdflast);

  pos += mysnprintf(pagebuf,pos,plen,"%010u 65535 f \n", 0);
  for (obj = 1; obj <= pdfcontent; obj++) pos += mysnprintf(pagebuf,pos,plen,"%010u 00000 n \n", xref[obj]);

  pos += mysnprintf(pagebuf,pos,plen,"trailer\n << /Size %u /Root %u 0 R >>\n", pdflast, pdfcat);

  pos += mysnprintf(pagebuf,pos,plen,"startxref\n%u\n%s\n", xrefpos,"%%EOF");

  if (filewrite(fd,pagebuf,pos,name)) return 1;

  fileclose(fd,name);

  info(0,"done writing base net to %s in pdf format: \ah%u bytes",name,xrefpos + pos);

  return 0;
}

void ininetio(void)
{
  msgfile = setmsgfile(__FILE__);
  iniassert();
  mkhexmap();
}
