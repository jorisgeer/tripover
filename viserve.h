// viserve.h - network visualisation server

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

struct bmphdr {
  ub2 sig;
  ub4 len;
  ub4 res;
  ub4 ofs;
};

// https://msdn.microsoft.com/en-us/library/dd183376%28v=vs.85%29.aspx
struct bmphdr4 {
  ub4        bV4Size;
  ub4         bV4Width;
  ub4         bV4Height;
  ub2        bV4Planes;
  ub2         bV4BitCount;
  ub4        bV4V4Compression; // bi_rle8 = 1
  ub4        bV4SizeImage;
  ub4        bV4XPelsPerMeter;
  ub4         bV4YPelsPerMeter;
  ub4        bV4ClrUsed;
  ub4        bV4ClrImportant;
  ub4        bV4RedMask;
  ub4        bV4GreenMask;
  ub4        bV4BlueMask;
  ub4        bV4AlphaMask;
  ub4        bV4CSType;
  ub4        bV4Endpoints[9]; // 3 * 3 * ub4
  ub4        bV4GammaRed;
  ub4        bV4GammaGreen;
  ub4        bV4GammaBlue;
};
