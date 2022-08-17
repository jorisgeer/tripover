// viserve.c - network visualisation server

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015 Joris van der Geer.
 */

/*
 network is meant to be visualised as a tiled layer. cgi script request tiles given tile/pixel coordinates
 this server runs in the background and provides them as file.
 using the current network data.
 Initially, only stop locations.
*/

#include <unistd.h>

#include <string.h>
#include <stdlib.h>
#include <math.h>

#include "base.h"
struct globs globs;

#include "os.h"
#include "mem.h"
#include "util.h"

static ub4 msgfile;
#include "msg.h"

#include "time.h"

#include "viserve.h"
#include "vishare.h"

#define Tile 256

static char *svgbuf;
static const ub4 svglen = 1024 * 1024 * 16;

static ub4 test_z = hi32,test_y = hi32,test_x = hi32;

static int init0(char *progname)
{
  char *p;
  ub2 bom = 0x1234;
  ub1 *bomp = (ub1 *)&bom;
  if (*bomp == 0x12) { msg_write("unsupported byte order\n",24); return 1; }

  setsigs();

  p = strrchr(progname,'/');
  globs.progname = (p ? p + 1 : progname);

  setmsglvl(Info,0,0);
  if (inimsg(progname,"viserve",Msg_stamp|Msg_pos|Msg_type|Msg_bcklog)) return 1;
  msgfile = setmsgfile(__FILE__);
  iniassert();

  info(User,"viserve %u.%u %s\n", Version_maj,Version_min,Version_phase);

  if (iniutil(0)) return 1;
  inimem();
  inios();
  initime(0);
  globs.maxvm = 32;

  svgbuf = alloc(svglen,char,0,"svg",0);

  return 0;
}

extern const char *runlvlnames(enum Runlvl lvl);
const char *runlvlnames(enum Runlvl lvl) { return lvl ? "n/a" : "N/A"; }

#define Bmphdr 14
#define Bmphdr2 40
static ub2 bmpfile[(Bmphdr + Bmphdr2 + 256 * 4 + Tile * Tile) / 2];
static ub4 bmplen = sizeof(bmpfile);

#define Tile4 (Tile / 4)

static ub1 map[Tile * Tile];
static ub1 gmap[Tile * Tile];
static ub4 map4[Tile4 * Tile4];

static int mkbmp(void)
{
  ub2 *fp = bmpfile;
  ub1 *bp,*bpend;
  ub4 ofs = Bmphdr + Bmphdr2 + 256 * 4;
  ub1 r,g,b;
  ub4 ndx,y;

  aclear(bmpfile);

  // bmp file header
  *fp++ = 0x4d << 8 | 0x42;
  *fp++ = bmplen & hi16;
  *fp++ = bmplen >> 16;
  fp += 2;
  *fp++ = ofs & hi16;
  *fp++ = ofs >> 16;

  // dib header
  *fp++ = Bmphdr2;
  fp++;

  *fp++ = Tile;
  fp++;

  *fp++ = Tile;
  fp++;

  *fp++ = 1; // color planes

  *fp++ = 8; // bpp

  *fp++ = 0; // no compression : 1 = rle8 3 = bi_bitfields
  fp++;

  *fp++ = (Tile * Tile) & hi16;
  *fp++ = (Tile * Tile) >> 16;

  *fp++ = 1; // xres
  fp++;
  *fp++ = 1; // yres
  fp++;

  fp += 2; // palette size, 0 = def

  fp += 2;

#if 0
  fp += 2;   // redmask

  fp += 2;   // greenmask

  fp += 2; // bluemask

  fp += 2; // alpha mask

  fp += (9 + 4) * 2;
#endif

  bp = (ub1 *)fp;

#if 1
  // palette
  b = r = g = 0xff;  // 0 = white
  *bp++ = b;
  *bp++ = g;
  *bp++ = r;
  *bp++ = 0;

  b = 0; r = 0xff; g = 0;  // 1 = red
  *bp++ = b;
  *bp++ = g;
  *bp++ = r;
  *bp++ = 0;

  for (ndx = 2; ndx < 256; ndx++) {
    b = (ub1)ndx;
    r = (ub1)(256 - ndx);
    g = b + r / 2;
    *bp++ = b;
    *bp++ = g;
    *bp++ = r;
    *bp++ = 0;
  }
#endif

  warncc(ofs != bp - (ub1 *)bmpfile,0,"offset %u mismatch",ofs);
  bpend = (ub1 *)bmpfile + bmplen;
  for (y = 1; y <= Tile; y++) {
    if (bp + Tile > bpend) return error(0,"bitmap buffer overflows at y = %u",y);
    memcpy(bp,gmap + (Tile - y) * Tile,Tile);

#if 0
    if (y > 20 && y < 80) memset(bp,0xff,Tile);
    else for (c = 0; c != 255; c++) {
      bp[c] = y;
    }
    *bp = 5;
#endif
    bp += Tile;
  }
  return 0;
}

static ub4 geoscale;

static double ilat2lat(ub4 lat)
{
  double x = (double)lat / geoscale;
  return x - 90;
}

#if 0
static ub4 lat2ilat(double lat)
{
  double x = (lat + 90) * geoscale;
  return (ub4)(x + 0.5);
}
#endif

static ub4 lon2ilon(double lon)
{
  double x = (lon + 180) * geoscale;
  return (ub4)(x + 0.5);
}

static double ilon2lon(ub4 lon)
{
  double x = (double)lon / geoscale;
  return x - 180;
}

struct port {
  ub4 ilat,ilon;
//  double lat,lon;
};
static ub4 portcnt;
static struct port *ports;

static ub4 *latsort,*lonsort;
static ub4 *latsortidx,*lonsortidx;

// prepare bsearch for geo lookup
static int mkgeosort(void)
{
  ub4 dep,idx,cnt = portcnt;
  struct port *sp;

  info(0,"sorting \ah%u geo items",cnt);

  ub8 xlat,*latxsort = alloc(cnt,ub8,0,"geo lat",cnt);
  ub8 xlon,*lonxsort = alloc(cnt,ub8,0,"geo lon",cnt);

  ub4 lat,lon;
  latsort = alloc(cnt,ub4,0,"geo lat",cnt);
  lonsort = alloc(cnt,ub4,0,"geo lon",cnt);
  latsortidx = alloc(cnt,ub4,0,"geo latidx",cnt);
  lonsortidx = alloc(cnt,ub4,0,"geo lonidx",cnt);

  for (dep = 0; dep < cnt; dep++) {
    sp = ports + dep;
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
  info(0,"lat range %u-%u",latsort[0],latsort[cnt-1]);
  info(0,"lon range %u-%u",lonsort[0],lonsort[cnt-1]);

  afree(latxsort,"geo lat");
  afree(lonxsort,"geo lon");
  return 0;
}

static int readnet(const char *netdir)
{
  struct myfile bin;
  ub4 i,cnt,*up;
  struct port *pp;
  char name[1024];

  fmtstring(name,"%s/network-ports.bin",netdir);
  info(0,"reading net %s",name);
  if (readfile(&bin,name,1,0)) return 1;

  if (bin.len & 7) return error(0,"%s network size mismatch for %lu",name,bin.len);
  else if (bin.len > hi32) return error(0,"%s network size mismatch for %lu",name,bin.len);
  else if (bin.len < 3 * sizeof(ub4)) return error(0,"%s network size mismatch for %lu",name,bin.len);

  void *vp = (void *)bin.buf;
  up = (ub4 *)vp;
  cnt = *up++;
  geoscale = *up++;

  portcnt = cnt;

  pp = ports = alloc(portcnt,struct port,0,"net",0);
  for (i = 0; i < portcnt; i++) {
    pp->ilat = *up++;
    pp->ilon = *up++;
    pp++;
  }

  mkgeosort();

  return 0;
}

static int mk_dir(const char *path)
{
  if (osexists(path)) return 0;
  if (osmkdir(path)) return oserror(0,"cannot create %s",path);
  else return 0;
}

static void drawdot(ub4 xc,ub4 yc,ub4 r,ub4 wid,ub1 val)
{
  ub1 *my = gmap + yc * Tile;
  ub4 y,x,xx,yy,rr = r * r;

  if (r == 1) {
    my[xc] = val;
    if (wid == 2) {
      if (xc < Tile - 1) my[xc+1] = val;
      if (yc < Tile - 1) {
        my = gmap + (yc+1) * Tile;
        my[xc] = val;
        if (xc < Tile - 1) my[xc+1] = val;
      }
    }
    return;
  }

  ub4 yl = yc - min(yc,r);
  ub4 yh = min(yc + r, Tile - 1);
  ub4 xl = xc - min(xc,r);
  ub4 xh = min(xc + r, Tile - 1);

  for (y = yl; y <= yh; y++) {
    if (y < yc) yy = (yc - y) * (yc - y);
    else yy = (y - yc) * (y - yc);
    for (x = xl; x <= xh; x++) {
      if (x < xc) xx = (xc - x) * (xc - x);
      else xx = (x - xc) * (x - xc);
      if (xx + yy <= rr) gmap[y * Tile + x] = val;
    }
  }
}

static void writepoint(ub4 z,ub4 x,ub4 y,ub1 val)
{
  if (y >= Tile || x >= Tile) return;

  ub1 *my = map + y * Tile;
  ub4 *my4 = map4 + (y / 4) * Tile4;
  ub4 r;
  ub4 wid;

  my[x] = val;
  my4[x / 4]++;

  switch (z) {
  case 0: case 1: case 2: case 3: case 4: case 5: case 6: case 7:  // handled by densepoints()
//    gmap[y * Tile + x] = val;
    return;

  case 8: r = 1; wid = 1; break;
  case 9: r = 1; wid = 1; break;
  case 10: r = 1; wid = 2; break;
  case 11: r = 2; wid = 2; break;
  case 12: r = 2; wid = 2; break;
  case 13: r = 2; wid = 3; break;
  case 14: r = 3; wid = 3; break;
  case 15: r = 4; wid = 3; break;
  case 16: r = 4; wid = 3; break;
  case 17: r = 5; wid = 3; break;
  default: r = 4; wid = 4; break;
  }

  drawdot(x,y,r,wid,val);
}

static void densepoints(ub4 z)
{
  ub1 val = 2;
  ub4 r,wid = 1;
  ub4 cnt,i;
  ub4 x,y,xx,yy,x4,y4;
  int found;
  ub1 *mp;
  ub1 *gmp;

  if (z > 10) return;

  for (y4 = 0; y4 < Tile4; y4++) {
    for (x4 = 0; x4 < Tile4; x4++) {
      cnt = map4[y4 * Tile4 + x4];
      if (cnt == 0) continue;
      else if (cnt > 1) {    // dense area: leave as single pixel
        for (y = 0; y < 4; y++) {
          yy = y4 * 4 + y;
          gmp = gmap + yy * Tile + x4 * 4;
          mp = map + yy * Tile + x4 * 4;
          for (i = 0; i < 4; i++) if (gmp[i] == 0) gmp[i] = mp[i];
        }
        continue;
      }

      // individual : draw extended
      found = 0; yy = y4 * 4; xx = x4 * 4;
      for (y = 0; y < 4; y++) {
        yy = y4 * 4 + y;
        for (x = 0; x < 4; x++) {
          xx = x4 * 4 + x;
          val = map[yy * Tile + xx];
          if (val) { found = 1; break; }
        }
      }
      if (found == 0) continue;

      switch(z) {
      case 0: case 1: case 2: r = 3;
      case 10: r = 2; break;
      default: r = 3;
      }
      drawdot(xx,yy,r,wid,val);

    }
  }
}

/*
  ground resolution = cos(latitude * pi/180) * earth circumference / map width

  sinLatitude = sin(latitude * pi/180)

  pixelX = ((longitude + 180) / 360) * 256 * 2 level

  pixelY = (0.5 – log( (1 + sinLatitude) / (1 – sinLatitude)) / (4 * pi)) * 256 * 2 ^ level
*/

static int mktile(ub8 tz,ub8 ty,ub8 tx)
{
  struct port *sp;
  ub4 ol,oh,o,oi;
  char path[1024];
  char npath[1024];
  double lat,lon;

  info(0,"mktile %lu %lu %lu",tz,ty,tx);
  aclear(map);
  aclear(map4);
  aclear(gmap);

  if (tz > 20) tz = 20;
  ub8 zpixlen = Tile * (1 << tz);
  ub8 xpixlo = tx * Tile;
  ub8 xpixhi = xpixlo + Tile;
  ub8 ypixlo = ty * Tile;
  ub8 ypixhi = ypixlo + Tile;
  double fzpixlen = zpixlen;
  double sinlat,fpx,fpy,a,b;
  double pi4 = M_PI * 4;
  double pi2 = M_PI * 2;

  double c = (double)xpixlo / fzpixlen - 0.5;
  double lolon = c * 360;

  c = (double)(xpixhi) / fzpixlen - 0.5;
  double hilon = c * 360;

  c = 0.5 - (double)ypixlo / fzpixlen;
  double hilat = 90 - 360 * atan(exp(-c * pi2)) / M_PI;

  c = 0.5 - (double)ypixhi / fzpixlen;
  double lolat = 90 - 360 * atan(exp(-c * pi2)) / M_PI;

  info(0,"lat range %f - %f  pix %lu - %lu",lolat,hilat,xpixlo,xpixhi);
  info(0,"lon range %f - %f  pix %lu - %lu",lolon,hilon,ypixlo,ypixhi);

  ub4 loilon = lon2ilon(lolon);
  ub4 hiilon = lon2ilon(hilon);
  ub8 px,py,lpx,lpy;

  ol = bsearch4(lonsort,portcnt,loilon,FLN,"lon");
  oh = bsearch4(lonsort,portcnt,hiilon,FLN,"lon");
  if (ol >= portcnt) return info(0,"lo lon %u out of range for hi %u",loilon,hiilon);
  oh = min(oh,portcnt);
  if (ol > oh) return 1;

  info(0,"lon portrange %u-%u",ol,oh);

  ub4 outcnt = 0;

// ub4 pos = mysnprintf(svgbuf,0,svglen,"<svg width='256' height='256' xmlns='http://www.w3.org/2000/svg' version='1.1'>\n");

//  sinLatitude = sin(latitude * pi/180)

//  pixelX = ((longitude + 180) / 360) * 256 * 2 level

//  pixelY = (0.5 – log( (1 + sinLatitude) / (1 – sinLatitude)) / (4 * pi)) * 256 * 2 ^ level

  for (o = ol; o < oh; o++) {
    oi = lonsortidx[o];
    sp = ports + oi;
    lat = ilat2lat(sp->ilat);
    lon = ilon2lon(sp->ilon);
    // info(Iter,"%f %f",lat,lon);
    if (lat <= lolat || lat >= hilat) continue;
    if (lon <= lolon || lon >= hilon) continue;

    sinlat = sin(lat * M_PI / 180);
    fpx = ((lon + 180) / 360) * fzpixlen;
    fpx = max(fpx,0);

    a = (1 + sinlat) / (1 - sinlat);
    b = 0.5 - log(a) / pi4;
    fpy = b * fzpixlen;

    px = (ub8)(fpx + 0.5);
    py = (ub8)(fpy + 0.5);
    // info(Iter|V0,"px %lu from %lu  py %lu from %lu,%lu",px,xpixlo,py,ypixlo,ypixhi);
    if (px <= xpixlo || px >= xpixhi) continue;
    lpx = px - xpixlo;

    if (py <= ypixlo || py >= ypixhi) continue;
    lpy = py - ypixlo;
    error_gt(lpx,Tile,tx);
    error_gt(lpy,Tile,ty);
    outcnt++;
    writepoint((ub4)tz,(ub4)lpx,(ub4)lpy,1);
    // pos += mysnprintf(svgbuf,pos,svglen,"<circle cx='%lu' cy='%lu' r='1' />\n",lpx,lpy);
  }
  // pos += mysnprintf(svgbuf,pos,svglen,"</svg>\n");

  info(0,"generated %u items",outcnt);

  densepoints((ub4)tz);

  fmtstring(path,"%s/%02lu",Tileroot,tz);
  if (mk_dir(path)) return 1;
  fmtstring(path,"%s/%02lu/%03lu",Tileroot,tz,ty);
  if (mk_dir(path)) return 1;

  if (mkbmp()) return 1;

  fmtstring(path,"%s/%02lu/%03lu/%03lu.bmp",Tileroot,tz,ty,tx);

  fmtstring(npath,"%s.new",path);
  if (writefile(npath,(char *)bmpfile,bmplen)) return 1;
  osrename(npath,path);
  info(0,"wrote %s",path);

#if 0
  fmtstring(path,"%s/%02lu/%03lu/%03lu.svg",Tileroot,tz,ty,tx);
  if (writefile(path,svgbuf,pos)) return 1;
  info(0,"wrote %s",path);
#endif

  return 0;
}

static int cmd_tile(struct myfile *req)
{
  struct myfile rep;
  char *vp,*lp = req->buf;
  ub4 n,pos = 0,len = (ub4)req->len;
  ub4 ival,z = 0,y = 0,x = 0;
  ub4 varstart,varend,varlen,valstart,valend,type;

  if (len == 0) return 1;

  oclear(rep);

  while (pos < len && lp[pos] >= 'a' && lp[pos] <= 'z') {
    ival = 0;
    varstart = varend = pos;
    while (varend < len && lp[varend] >= 'a' && lp[varend] <= 'z') varend++;
    varlen = varend - varstart; pos = varend;
    if (varlen == 0) break;
    while (pos < len && lp[pos] == ' ') pos++;
    if (pos == len) break;
    type = lp[pos++];
    if (type == '\n' || pos == len) break;
    while (pos < len && lp[pos] == ' ') pos++;
    lp[varend] = 0;

    valstart = valend = pos;
    while (valend < len && lp[valend] != '\n') valend++;
    if (valend == len) break;
    pos = valend;
    while (pos < len && lp[pos] != '\n') pos++;
    if (lp[pos] == '\n') pos++;
    if (pos == len) break;
    lp[valend] = 0;

    if (type == 'i') {
      n = str2ub4(lp + valstart,&ival);
      if (n == 0) {
        warn(0,"expected integer for %s, found '%.*s'",lp + varstart,valend - valstart,lp + valstart);
        continue;
      }
    } else if (type == 'x') {
      n = hex2ub4(lp + valstart,&ival);
      if (n == 0) {
        warn(0,"expected hex integer for %s, found '%.*s'",lp + varstart,valend - valstart,lp + valstart);
        continue;
      }
    } else if (type == 'b') {
      n = bstr2ub4(lp + valstart,&ival);
      if (n == 0) {
        warn(0,"expected integer for %s, found '%.*s'",lp + varstart,valend - valstart,lp + valstart);
        continue;
      }
    } else {
      warn(0,"skip unknown type %c for %s '%.*s'",type,lp + varstart,valend - valstart,lp + valstart);
      continue;
    }
    vp = lp + varstart;
    if (varlen == 1 && *vp == 'z') z = ival;
    else if (varlen == 1 && *vp == 'y') y = ival;
    else if (varlen == 1 && *vp == 'x') x = ival;
    else {
      warn(0,"ignoring unknown var '%s'",vp);
    }
  }
  info(V0,"z %u y %u x %u",z,y,x);
  if (mktile(z,y,x)) return 1;

  return 0;
}

// wrapper around cmd_tileplan, fork here
static int start_tile(struct myfile *req,int do_fork)
{
  int rv;
  char logname[1024];
  char filename[1024];
  char *file,*ext;
  int pid;

  file = strrchr(req->name,'/');
  if (file) file++; else file = req->name;
  ext = strrchr(req->name,'.');
  if (ext) fmtstring(filename,"%.*s",(ub4)(ext - file),file);
  else strcopy(filename,file);

  if (do_fork) {
    pid = fork();
    if (pid == -1) { oserror(0,"Cannot fork from %u for %s",globs.pid,filename); return -1; }
    else if (pid) { info(0,"create process %u for %s",pid,filename); return pid; }

    globs.pid = getpid();
    fmtstring(logname,"log/%s-%u-%u",filename,globs.id,globs.pid);
    setmsglog(globs.netdir,logname,1,1);
  }

  rv = cmd_tile(req);
  if (rv) info(0,"tiler returned %d",rv);
  if (do_fork) {
    eximsg(0);
    osremove(globs.logname);
    exit(rv);
  } else return rv;
}

static int serverloop(void)
{
  const char *querydir = globs.querydir;
  struct myfile req;
  int prv,rv = 1;
  enum Cmds { Cmd_nil, Cmd_stop, Cmd_tile } cmd = Cmd_nil;
  ub4 prvseq = 0,seq = 0;
  char c;
  const char *region = "glob";
  int cpid;
  int do_fork;
  ub4 cldcnt = 0;

  info(Emp,"entering server loop for id %u",globs.serverid);

  do {
    infovrb(seq > prvseq,0,"wait for new cmd %u",seq);
    rv = getqentry(querydir,&req,region,".sub");
    if (rv) break;

    prvseq = seq;

    if (req.direxist == 0) osmillisleep(2000);
    else if (req.exist == 0) {
      if (cldcnt) {
        prv = oswaitany(&cldcnt);
        if (prv) return 1;
      }
      osmillisleep(10);  // for linux only we may use inotify instead
    } else {
      info(0,"new client entry %s",req.name);
      if (osremove(req.name)) oswarning(0,"cannot remove %s",req.name);
      do_fork = 0;
      c = req.name[req.basename];
      switch(c) {
      case 's': cmd = Cmd_stop; break;
      case 't': cmd = Cmd_tile; break;
      case 'T': cmd = Cmd_tile; do_fork = 1; break;
      default: info(0,"unknown command '%c'",c);
      }
      if (cmd == Cmd_tile) {
        seq++;
        if (do_fork) {
          cpid = start_tile(&req,1);
          if (cpid > 0) cldcnt++;
        } else {
          clriters();
          rv = start_tile(&req,do_fork);
        }
        if (req.alloced) afree(req.buf,"client request");
      }
    }
  } while (cmd != Cmd_stop && globs.sigint == 0);

  info(0,"leaving server loop for id %u",globs.serverid);

  return rv;
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

static int cmd_z(struct cmdval *cv) { test_z = cv->uval; return 0; }
static int cmd_y(struct cmdval *cv) { test_y = cv->uval; return 0; }
static int cmd_x(struct cmdval *cv) { test_x = cv->uval; return 0; }

static int background;

static int cmd_bg(struct cmdval *cv)
{
  background = 1;
  return info(V0,"%s set",cv->subarg);
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
  { "verbose|v", "[level]%u", "set or increase verbosity", cmd_vrb },
  { "assert-limit", "[limit]%u", "stop at this #assertions", cmd_limassert },
  { "z", "[z]%u", "z", cmd_z },
  { "y", "[y]%u", "y", cmd_y },
  { "x", "[x]%u", "x", cmd_x },
  { "background|b",NULL,"run in background",cmd_bg },
  { NULL, "dir", "viserve", cmd_arg }
};

int main(int argc, char *argv[],char *envp[])
{
  int rv;

  globs.msglvl = Info;
  globs.msgslvl = 0;
  strcopy(globs.querydir,"queries");
  globs.tidcnt = 1;

  setmsglvl(globs.msglvl,globs.msgslvl,0);

  init0(argv[0]);

  vrbcc(envp,0,"env: %s",envp[0]);

  if (cmdline(argc,argv,cmdargs,"viserve")) return 1;

  if (globs.argc == 0) return shortusage();

  const char *netdir = globs.args[0];
  if (*netdir == 0) return shortusage();

  if (readnet(netdir)) return 1;

  fmtstring(globs.querydir,"%s",Querydir);

  if (background) osbackground();

  if (test_z != hi32 && test_y != hi32 && test_x != hi32) {
    rv = mktile(test_z,test_y,test_x);
    return rv;
  }

  rv = serverloop();

  return rv;
}
