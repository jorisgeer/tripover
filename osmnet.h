// osmnet.h - openstreetmap network, internal file structure

/*
   This file is part of Tripover, a broad-search journey planner.

   Copyright (C) 2015-2016 Joris van der Geer.
 */

struct tnode {
  sb4 ilat,ilon;  // in original osm units
};

enum Twmodes { Twfoot = 1,Twbike = 2,Twcar = 4,Twmodecnt = 8 };
enum Twtypes { Twtrack,Twfootpath };
struct tway {
  ub4 nofs;
  ub2 ncnt;
  ub1 modes;
  ub1 type;
  ub2 speed;
  char name[32];
};

static const ub4 Omagic1 = 0xcd1a4b0d;
static const ub4 Omagic2 = 0xd86640ab;
static const ub4 Omagic3 = 0xbb944ce4;
static const ub4 Omagic4 = 0xd409643b;

struct osmhdr {
  ub4 magic;
  ub4 nodecnt;
  ub4 waycnt;
  ub4 joincnt;
  ub4 nlstlen;
  ub4 x;
};
