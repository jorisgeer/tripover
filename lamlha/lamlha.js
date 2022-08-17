// lamlha.js - Lam Lha journey planner website

/*
  author: Joris van der Geer

 */

"use strict";

var version = '1.0';
var lastchanged = '15 Apr 2016';

var region = 'au';

var geocode_region = region;

var maintenance = 0;

var local_proxy_adr = 'http://192.168.1.4/';

var remote_proxy_adr = ''; // use relative path
var proxy_adr;

var geocode_url = 'http://maps.googleapis.com/maps/api/geocode/json';

// ui elems
var map;
var statuspane,dirpane,progresspane;
var depnamepane,arrnamepane,depfulnampane,arrfulnampane;
var srcoptform,advoptform,optCform,optHform,dohopsrc;

var deplatlng = [0,0];
var arrlatlng = [0,0];
var depmark = null,arrmark = null;
var depmark_stop = null,arrmark_stop = null;

var depname,arrname,depfulnam = '',arrfulnam = '';
var dep_to_id = 0;
var arr_to_id = 0;
var depdist,arrdist;
var depstopdist = 0,arrstopdist = 0;

var geodres_name = '',geoares_name = '';

var visnet;
var Esri_WorldTopoMap;
var OSM_map;

var routeset;

// state
var havedep = 0;
var havearr = 0;
var plan_iter = 0;
var deparr_iter = 0;

var reqtype_plan = false;
var reqtype_geo = false;

var havedepgeo = false;
var havearrgeo = false;
var haveplan = false;
var geonolim = false;

var arrdesc = '',depdesc = '';

var dblclick = false;

var plantstamp = 0;

var toproxy,codedep,codearr,netloader;

// icons
var mopts_air = {
  title:'airport',
  className:'depmark',
  clickable:false,
  draggable:true,
  opacity:0.8
};
var mopts_train = {
  title:'train station',
  className:'depmark',
  clickable:false,
  draggable:true,
  opacity:0.8
};
var mopts_bus = {
  title:'bus stop',
  className:'depmark',
  clickable:false,
  draggable:true,
  opacity:0.8
};
var mopts_ferry = {
  title:'ferry',
  className:'depmark',
  clickable:false,
  draggable:true,
  opacity:0.8
};

var depmopts = {
  title:'start',
  className:'depmark',
  clickable:false,
  draggable:true,
  opacity:0.8
};
var arrmopts = {
  title:'end',
  className:'depmark',
  clickable:false,
  draggable:true,
  opacity:0.8
};

// smaller utility functions
function log(m)
{
  console.log(m);
}

function hide(e) { e.style.visibility = 'hidden'; }
function show(e) { e.style.visibility = 'visible'; }

function hidex(e) { e.style.display = 'none'; }
function showx(e) { e.style.display = 'initial'; }

function eid(n) { return document.getElementById(n); }

function tooltip(e,s)
{
  var x = eid(e);
  if (x != null) eid(e).setAttribute("title",s);
}

function showprogresspane() { show(progresspane); }
var delayedprogress;

function plural(n,s)
{
  var f = n + ' ' + s;
  if (n != 1) f += 's';
  return f;
}

function truncate(s,lim)
{
  if (s.length <= lim) return s;
  return s.substr(0,lim) + '&hellip;';
}

function toint(x) { return Math.floor(x); }
function mkint(x) { return parseInt(x,10); }

function fmtdist(d)
{
  var dd,prec;

  if (d < 1500) return d + ' m';

  dd = d / 1000;
  if (dd < 10) prec = 2;
  else if (dd < 100) prec = 1;
  else prec = 0;
  return dd.toFixed(prec) + ' Km';
}
function fmtloc(loc)
{
  return loc[0].toFixed(5) + ' , ' + loc[1].toFixed(5);
}

// functions handling start and end points
function cancelreq()
{
  toproxy.onreadystatechange = null;
  clearTimeout(delayedprogress);
  hide(progresspane);
}

function setdep(latlon,boundmap,replace)
{
  var bounds = map.getBounds();
  var s = truncate(depfulnam,64) + ' out of range at ' + fmtloc(latlon);
  if (boundmap === true && bounds.contains(latlon) !== true) {
    console.log(s);
    return status(s);
  }
  depmopts.title = 'start at ' + fmtloc(latlon) + '\n' + depfulnam;
  if (depmark !== null) map.removeLayer(depmark);
  depmark = L.marker(latlon,depmopts);
  depmark.addTo(map);

  havedep = true;
  havedepgeo = false;
  if (replace === true && depmark_stop !== null) map.removeLayer(depmark_stop);
  show(eid('rmdep'));
}

function setidep(latlon)
{
  depmopts.title = 'start at ' + fmtloc(latlon) + '\n' + depfulnam;
  if (depmark !== null) map.removeLayer(depmark);
  depmark = L.marker(latlon,depmopts);
  depmark.addTo(map);
  havedep = true;
}

function setarr(latlon,boundmap,replace)
{
  var bounds = map.getBounds();
  if (boundmap === true && bounds.contains(latlon) !== true) {
    status(truncate(arrfulnam,64) + ' out of range at ' + fmtloc(latlon));
    return;
  }
  arrmopts.title = 'end at ' + fmtloc(latlon) + '\n' + arrfulnam;
  if (arrmark !== null) map.removeLayer(arrmark);
  arrmark = L.marker(latlon,arrmopts);
  arrmark.addTo(map);
  havearr = true;
  havearrgeo = false;
  if (replace === true && arrmark_stop !== null) map.removeLayer(arrmark_stop);
  show(eid('rmarr'));
}

function setiarr(latlon)
{
  arrmopts.title = 'end at ' + fmtloc(latlon) + '\n' + arrfulnam;
  if (arrmark !== null) map.removeLayer(arrmark);
  arrmark = L.marker(latlon,arrmopts);
  arrmark.addTo(map);
  havearr = true;
}

// click in map: set or toggle depart or arrive points
function ongenclick(e)
{
  var lat = e.latlng.lat;
  var lon = e.latlng.lng;

  log('lat ' + lat + ' lon ' + lon);

  geonolim = e.originalEvent.shiftKey;
  status('');
  cancelreq();
  haveplan = false;
  routeset.clearLayers();

  if (havedep) {  // place new arr or modify existing
    arrfulnam = '';
    arrnamepane.value = '';
    geoares_name = '';
    arrlatlng = [lat,lon];
    setarr(arrlatlng,true,true);
    deparr_iter++;
    geoicode(arrlatlng,false);
    reqplan();  // schedule geo lookup
    arrdesc = 'map.' + map.getZoom();
  } else { // place new dep or modify existing
    depfulnam = '';
    geodres_name = '';
    depnamepane.value = '';
    deplatlng = [lat,lon];
    setdep(deplatlng,true,true);
    if (havearr) {
      deparr_iter++;
    }
    geoicode(deplatlng,true);
    reqplan();
    depdesc = 'map.' + map.getZoom();
  }
}

function onclick(e)
{
  dblclick = false;
  ongenclick(e);
}

function ondblclick(e)
{
  dblclick = true;
}

// search option form
function onoptchange()
{
  if (havedep && havearr) {
    routeset.clearLayers();
    haveplan = false;
    reqplan();
  }
}

// right click in map: set or toggle depart point only
function onrtclick(e)
{
  var lat = e.latlng.lat;
  var lon = e.latlng.lng;

  geodres_name = '';
  depnamepane.value = '';

  status('');
  cancelreq();
  haveplan = false;

  deplatlng = [lat,lon];
  setdep(deplatlng,true,true);

  if (havedep == false) {
    show(eid('rmdep'));
    depmark.addTo(map);
    havedep = true;
  }
  geoicode(deplatlng,true);
  reqplan();
}

// functions handling geo results
var geodres_status,geodres_fuladr,geodres_lat,geodres_lng;
var geodres_loc = [];
var geoares_status,geoares_fuladr,geoares_lat,geoares_lng;
var geoares_loc = [];

function parsegeodres(key,val)
{
  if (key === 'status') geodres_status = val;
  else if (key === 'formatted_address' && geodres_fuladr == '') geodres_fuladr = val;
  else if (key === 'lat') geodres_lat = val;
  else if (key === 'lng') geodres_lng = val;
  else if (key === 'location' && geodres_loc.length == 0) {
    geodres_loc = [geodres_lat,geodres_lng];
  }
  return null;
}
function parsegeoares(key,val)
{
  if (key === 'status') geoares_status = val;
  else if (key === 'formatted_address' && geoares_fuladr == '') geoares_fuladr = val;
  else if (key === 'lat') geoares_lat = val;
  else if (key === 'lng') geoares_lng = val;
  else if (key === 'location' && geoares_loc.length == 0) {
    geoares_loc = [geoares_lat,geoares_lng];
  }
  return null;
}

function parsegeodires(key,val)
{
  if (key === 'status') geodres_status = val;
  else if (key === 'formatted_address' && geodres_fuladr == '') geodres_fuladr = val;
  else if (key === 'lat') geodres_lat = val;
  else if (key === 'lng') geodres_lng = val;
  else if (key === 'location' && geodres_loc.length == 0) {
    geodres_loc = [geodres_lat,geodres_lng];
  }
  return null;
}
function parsegeoaires(key,val)
{
  if (key === 'status') geoares_status = val;
  else if (key === 'formatted_address' && geoares_fuladr == '') geoares_fuladr = val;
  else if (key === 'lat') geoares_lat = val;
  else if (key === 'lng') geoares_lng = val;
  else if (key === 'location' && geoares_loc.length == 0) {
    geoares_loc = [geoares_lat,geoares_lng];
  }
  return null;
}

function ongeodstate(e)
{
  var state = codedep.readyState;
  log('state ' + state);
  if (state != 4) return;

  log('status ' + codedep.status);
  var s = 'geocode service for ' + depname;
  if (codedep.status != 200) return status(s + ' returned ' + codedep.status);

  var txt = codedep.responseText;
  if (txt === false || txt.length < 10) return status(s + ' returned empty result');
  var obj;
  geodres_status = geodres_fuladr = '';
  geodres_loc = [];

  try {
    obj = JSON.parse(txt,parsegeodres);
  }
  catch(e) { return status(s + 'returned invalid result'); }

  var gstatus = geodres_status;
  var fuladr = geodres_fuladr;
  var loc = geodres_loc;

  log('status ' + gstatus);
  log('fuladr ' + fuladr);
  log('loc ' + loc);

  if (gstatus !== 'OK') return status(s + 'returned status ' + gstatus);
  if (loc.length == 0) return status(s + 'returned no location');

  if (fuladr.length == 0) fuladr = '(no name)';

  depfulnam = fuladr;
  deplatlng = loc;

  s = truncate(fuladr,64);
  depfulnampane.innerHTML = '<span style="color:green">&xcirc;</span>&ensp;' + s;
  status(geodres_name + ' resolved into ' + s + ' at ' + fmtloc(loc));
  setdep(deplatlng,false,true);
  reqplan();
}

function ongeoastate(e)
{
  var state = codearr.readyState;
  log('state ' + state);
  if (state != 4) return;

  log('status ' + codearr.status);
  var s = 'geocode service for ' + arrname;
  if (codearr.status != 200) return status(s + ' returned ' + codearr.status);

  var txt = codearr.responseText;
  if (txt == false || txt.length < 10) return status(s + ' returned empty result');
  var obj;
  geoares_status = geoares_fuladr = '';
  geoares_loc = [];

  try {
    obj = JSON.parse(txt,parsegeoares);
  }
  catch(e) { return status(s + 'returned invalid result'); }

  var gstatus = geoares_status;
  var fuladr = geoares_fuladr;
  var loc = geoares_loc;

  log('status ' + gstatus);
  log('fuladr ' + fuladr);
  log('loc ' + loc);

  if (gstatus !== 'OK') return status(s + 'returned status ' + gstatus);
  if (loc.length == 0) return status(s + 'returned no location');

  if (fuladr.length == 0) fuladr = '(no name)';

  arrfulnam = fuladr;
  arrlatlng = loc;

  s = truncate(fuladr,64);

  arrfulnampane.innerHTML = '<span style="color:blue">&xcirc;</span>&ensp;' + s;
  status(geoares_name + ' resolved into ' + s + ' at ' + fmtloc(loc));
  setarr(arrlatlng,false,true);
  reqplan();
}

function ongeodistate(e)
{
  var state = codedep.readyState;
  log('state ' + state);
  if (state != 4) return;
  log('status ' + codedep.status);
  if (codedep.status != 200) return;

  var txt = codedep.responseText;
  if (txt == false || txt.length < 10) return;
  var obj;
  geodres_status = geodres_fuladr = '';
  geodres_loc = [];

  try {
    obj = JSON.parse(txt,parsegeodires);
  }
  catch(e) { return; }

  var gstatus = geodres_status;
  var fuladr = geodres_fuladr;
  var loc = geodres_loc;

  log('status ' + gstatus);
  log('fuladr ' + fuladr);
  log('loc ' + loc);

  if (gstatus !== 'OK' || loc.length == 0 || fuladr.length == 0) return;

  depfulnam = fuladr;
  setidep(loc);
  var s = truncate(fuladr,64);

  depfulnampane.innerHTML = '<span style="color:green">&xcirc;</span>&ensp;start ' + s;
//  status('found ' + s + ' at ' + fmtloc(loc));
}
function ongeoaistate(e)
{
  var state = codearr.readyState;
  log('state ' + state);
  if (state != 4) return;
  log('status ' + codearr.status);
  if (codearr.status != 200) return;

  var txt = codearr.responseText;
  if (txt == false || txt.length < 10) return;
  var obj;
  geoares_status = geoares_fuladr = '';
  geoares_loc = [];

  try {
    obj = JSON.parse(txt,parsegeoaires);
  }
  catch(e) { return; }

  var gstatus = geoares_status;
  var fuladr = geoares_fuladr;
  var loc = geoares_loc;

  log('status ' + gstatus);
  log('fuladr ' + fuladr);
  log('loc ' + loc);

  if (gstatus !== 'OK' || loc.length == 0 || fuladr.length == 0) return;
  arrfulnam = fuladr;
  setiarr(arrlatlng);

  var s = truncate(fuladr,64);

  arrfulnampane.innerHTML = '<span style="color:blue">&xcirc;</span>&ensp;end&emsp;' + s;
//  status('found ' + s + ' at ' + fmtloc(loc));
}

function geocode(name,isdep)
{
  if (name === null || name.length == 0) return;
  var url = geocode_url + '?address=' + name;

  var bounds = map.getBounds();
  var ne = bounds.getNorthEast();
  var sw = bounds.getSouthWest();
  var n = ne.lat.toFixed(6);
  var e = ne.lng.toFixed(6);
  var s = sw.lat.toFixed(6);
  var w = sw.lng.toFixed(6);
  url += '&bounds=' + n + ',' + e + '|' + s + ',' + w;
  url += '&region=' + geocode_region;
  log(url);

  if (isdep) {
    if (geodres_name === name) return;
    geodres_name = name;
    codedep.open('GET',url);
    codedep.onreadystatechange = ongeodstate;
    codedep.timeout = 2000;
    codedep.ontimeout = function(e) { status('no response from geocode service'); }
    codedep.onerror = function(e) { status('error contacting geocode service'); }
    codedep.send();
    log('send dep geo req');
  } else {
    if (geoares_name === name) return;
    geoares_name = name;
    codearr.open('GET',url);
    codearr.onreadystatechange = ongeoastate;
    codearr.timeout = 2000;
    codearr.ontimeout = function(e) { status('no response from geocode service'); }
    codearr.onerror = function(e) { status('error contacting geocode service'); }
    codearr.send();
    log('send arr geo req');
  }
}

function geoicode(latlon,isdep)
{
  var url = geocode_url + '?latlng=' + latlon[0] + ',' + latlon[1];

  log(url);

  if (isdep) {
//    depfulnam = '(unknown)';
    codedep.open('GET',url);
    codedep.onreadystatechange = ongeodistate;
    codedep.timeout = 3000;
    codedep.ontimeout = function(e) { status('no response from geocode service'); }
    codedep.onerror = function(e) { status('error contacting geocode service'); }
    codedep.send();
  } else {
//    arrfulnam = '(unknown)';
    codearr.open('GET',url);
    codearr.onreadystatechange = ongeoaistate;
    codearr.timeout = 3000;
    codearr.ontimeout = function(e) { status('no response from geocode service'); }
    codearr.onerror = function(e) { status('error contacting geocode service'); }
    codearr.send();
  }
}

function ondepchange()
{
  plantstamp = Date.now();
  log('ondepchange');
  var name = depnamepane.value;
  if (name == null) return;
  if (name.length < 3) return;
  depfulnam = '';
  geocode(name,true);
  depdesc = 'name.' + map.getZoom();
}
function onarrchange()
{
  plantstamp = Date.now();
  var name = arrnamepane.value;
  if (name == null) return;
  if (name.length < 3) return;
  arrfulnam = '';
  geocode(name,false);
  arrdesc = 'name.' + map.getZoom();
}

function rmdep()
{
  havedep = false;
  status('');
  if (depmark !== null) map.removeLayer(depmark);
  if (depmark_stop !== null) map.removeLayer(depmark_stop);
  hide(eid('rmdep'));
  depnamepane.value = '';
  depfulnampane.innerHTML = '';
  geodres_name = '';
  depfulnam = '';
}

function onrmdep()
{
  routeset.clearLayers();
  havedepgeo = false; haveplan = false;
  cancelreq();
  toproxy.abort();
  dep_to_id = 0;
  rmdep();
}

function rmarr()
{
  havearr = false;
  status('');
  map.removeLayer(arrmark);
  if (arrmark_stop !== null) map.removeLayer(arrmark_stop);
  hide(eid('rmarr'));
  arrnamepane.value = '';
  arrfulnampane.innerHTML = '';
  geoares_name = '';
  arrfulnam = '';
}

function onrmarr()
{
  routeset.clearLayers();
  havearrgeo = false; haveplan = false;
  cancelreq();
  toproxy.abort();
  arr_to_id = 0;
  rmarr();
}

function srcopt(v) { return document.forms["srcopt"][v].value; }
function advopt(v) { return document.forms["advopt"][v].value; }
function optC(v) { return document.forms["optC"][v].value; }

function advopt_cb(v) { return document.forms["advopt"][v].checked; }

var state_reqtmo = false;
var state_reqok = false;

function status(msg)
{
  if (maintenance) msg = 'Server is currently under maintenance';
  statuspane.innerHTML = msg;
  if (msg.length) console.log(msg);
  return true;
}

function onreqtmo()
{
  state_reqtmo = true;
  cancelreq();
  var s = 'no response in ' + toproxy.timeout / 1000 + ' seconds';
  status(s);
  log(s);
}

// get tripover id and name from reply
// reqid	dist  lat	lon	id	pid	modes name	pname
function showdepgeo(res)
{
//  console.log('dep geocode result ' + res + ' . ');
  if (res === null) {
    depnamepane.value = '(no stop found)';
    status('no stop found: no result' );
    return false;
  }
  if (res.indexOf('error') >= 0 || res.indexOf('\n') === -1) {
    depnamepane.value = '(no stop found)';
    status('no stop found: ' + res);
    return false;
  }

  var lines = res.split("\n");
  var dist,i = 0;
  var lat,lon,modes;

  while (i < lines.length && (lines[i].charAt(0) === '#' || lines[i].indexOf('.geo') !== 0)) i++;

  if (i >= lines.length) return false;

  console.log(lines[i]);

  var args = lines[i].split("\t");
  if (args.length > 2 && args[2].indexOf('no reply') >= 0) {
    status(args[1]);
    return false;
  }
  if (args.length < 8) {
    depnamepane.value = '(no stop found)';
    console.log(args);
    return false;
  }
  dist = args[2];
  depname = args[8];
  console.log(dist);

  lat = args[3]; lon = args[4];
//  if (lon < 0) lon = 360 + lon;
  lon = Math.max(lon,lon);

  var latlon = new L.LatLng(lat,lon);
  var mapview = map.getBounds();

  var s = '';

  if (mapview.contains(latlon) === false) {
    s = '(out of view) ' + lon;
//    if (depnamepane.value == '') depnamepane.value = '(out of range)';
//    status('nearest stop ' + depname + ' ' + fmtdist(dist) + ' away');
//    rmdep();
//    console.log(dist);
//    return false;
  }
  if (havearrgeo == true && arr_to_id == args[5]) {
    status("start and end stop identical");
    rmdep();
    console.log(dist);
    return false;
  }

  dep_to_id = args[5]; // id
  modes = args[7];

  depdist = dist;

  s += 'start ' + fmtdist(dist) + ' from ';

  if (depnamepane.value == '') depnamepane.value = depname;

  var s2 = ' ' + depname + ' at ' + fmtdist(dist) + ' from start';
  if (modes & 3) {
    s += 'airport';
    mopts_air.title = 'airport' + s2;
    depmark_stop = L.marker(latlon,mopts_air);
  } else if (modes & 16) {
    s += 'ferry';
    mopts_ferry.title = 'ferry' + s2;
    depmark_stop = L.marker(latlon,mopts_ferry);
  } else if (modes & 4) {
    s += 'station';
    mopts_train.title = 'station' + s2;
    depmark_stop = L.marker(latlon,mopts_train);
  } else if (modes & 8) {
    s += 'bus stop';
    mopts_bus.title = 'bus stop' + s2;
    depmark_stop = L.marker(latlon,mopts_bus);
  } else {
    s += 'bus stop';
    mopts_bus.title = 'bus stop' + s2;
    depmark_stop = L.marker(latlon,mopts_bus);
  }

  depmark_stop.addTo(map);

  s += ' ' + depname;

  status(s);
  log(s);

  return true;
}
function showarrgeo(res)
{
//  log('arr geocode result ' + res + ' . ');
  if (res === null || res.indexOf('\n') === -1) {
    arrnamepane.value = '(no stop found)';
    return false;
  }
  var lines = res.split("\n");
  if (lines.length == 0) return false;

  var dist,i = 0;
  var lat,lon,modes;

  while (lines[i].charAt(0) === '#' || lines[i].indexOf('.geo') !== 0) i++;
  if (i >= lines.length) return false;

  var args = lines[i].split("\t");
  if (args.length < 8) {
    arrnamepane.value = '(no stop found)';
    return true;
  }
  dist = args[2];
  arrname = args[8];

  lat = args[3]; lon = args[4];
  var latlon = new L.LatLng(lat,lon);
  var mapview = map.getBounds();

  var s = '';

  if (mapview.contains(latlon) === false) {
    s = '(out of view) ';
//  if (arrnamepane.value == '') arrnamepane.value = '(out of range)';
//  status('nearest stop ' + arrname + ' ' + fmtdist(dist) + ' away');
//  rmarr();
//  return false;
  }
  if (havedepgeo == true && dep_to_id == args[5]) {
    status("start and end stop identical");
    rmarr();
    return false;
  }

  arr_to_id = args[5];
  modes = args[7];

  arrdist = dist;

  s += 'end ' + fmtdist(dist) + ' from ';

  if (arrnamepane.value == '') arrnamepane.value = arrname;

  var s2 = ' ' + arrname + ' at ' + fmtdist(dist) + ' from end';

  if (modes & 3) {
    s += 'airport';
    mopts_air.title = 'air' + s2;
    arrmark_stop = L.marker(latlon,mopts_air);
  } else if (modes & 16) {
    s += 'ferry';
    mopts_ferry.title = 'ferry' + s2;
    arrmark_stop = L.marker(latlon,mopts_ferry);
  } else if (modes & 4) {
    s += 'station';
    mopts_train.title = 'train' + s2;
    arrmark_stop = L.marker(latlon,mopts_train);
  } else if (modes & 8) {
    s += 'bus stop';
    mopts_bus.title = 'bus' + s2;
    arrmark_stop = L.marker(latlon,mopts_bus);
  } else {
    s += 'bus stop';
    mopts_bus.title = 'bus stop' + s2;
    depmark_stop = L.marker(latlon,mopts_bus);
  }
  s += ' ' + arrname;

  status(s);
  log(s);

  arrmark_stop.addTo(map);
}

// callback for proxy call in progress
function onreqstate()
{
  if (havedep == false && havearr == false) { // canceled search
    toproxy.onreadystatechange = null;
    clearTimeout(delayedprogress);
    hide(progresspane);
    status('');
    return;
  }
  if (toproxy.readyState != 4) return;
  cancelreq();
  var hs = toproxy.status;
  log('proxy result status ' + hs);
  if (hs !== 200) {
    if (hs === 0) status("no response from server");
    else if (hs === 500) status("server returned internal error");
    else status("server returned error code " + hs);
    return;
  }
  if (toproxy.responseText == null || toproxy.responseText === '') {
    status('no response from proxy');
    return;
  }
//  console.log('proxy result ' + toproxy.responseText);
  if (state_reqtmo == true) {
    status('no response from Tripover server');
    return;
  }
  state_reqok = true;

  if (havedepgeo === true && havearrgeo === true && haveplan === false) {
    haveplan = true;
    showres(toproxy.responseText);
  } else if (havedep === true && havedepgeo === false) {
    if (showdepgeo(toproxy.responseText) == false) return;
    havedepgeo = true;
    if (havedep && havearr) reqplan(); // start plan cmd now
  } else if (havearr === true && havearrgeo === false) {
    if (showarrgeo(toproxy.responseText)) return false;
    havearrgeo = true;
    if (havedep && havearr) reqplan();
  }
}

var geoscale = 1000000;  // ~10 cm

function lat2to(l) {
  if (l == undefined) return 0;
  return Math.round((l + 90) * geoscale);
}
function lon2to(l) {
  if (l == undefined) return 0;
  if (l > 180) l = -360 + l;
  return Math.round((l + 180) * geoscale);
}

var minttAA = 60;
var minttAa = 90;
var minttaa = 45;
var minttaA = 90;
var minttAx = 45;
var minttxA = 120;
var minttax = 30;
var minttxa = 60;
var minttbx = 5;
var minttxb = 5;
var mintttt = 3;
var minttxf = 10;
var minttfx = 10;

var xminttAA;
var xminttAa;
var xminttaa;
var xminttaA;
var xminttAx;
var xminttxA;
var xminttax;
var xminttxa;
var xminttbx;
var xminttxb;
var xmintttt;
var xminttxf;
var xminttfx;

/* send request to tripover proxy
  geo lookup, in latlon out (name, id)
  plan in id,id out result

  cmdline : aver,ver,id,cmd,dlat,dlon,alat,alon,dep,arr,date,hh,pmday,utcofs,walklim,srcmode,delay
 */
function reqplan()
{
  var deplat = lat2to(deplatlng[0]);
  var deplon = lon2to(deplatlng[1]);
  var arrlat = lat2to(arrlatlng[0]);
  var arrlon = lon2to(arrlatlng[1]);
  var dep,arr;
  var desc;

  plan_iter = deparr_iter;

  var args = '/0/0/' + plan_iter + '/';
  var statline;

  // determine what call to make from dep,arr state
  if (havedepgeo === true && havearrgeo === true && haveplan === false) {
    args += '0/'; dep = dep_to_id; arr = arr_to_id;
    desc = 'plan ' + depdesc + ' ' + arrdesc + ' ' + plan_iter;
    statline = 'planning trip';
  } else if (havedep === true && havedepgeo === false) {
    args += '2/'; dep = arr = 0; arrlat = arrlon = 0;
    desc = 'geo dep ' + depdesc + ' ' + plan_iter;
    statline = 'finding nearest departure stop';
  } else if (havearr === true && havearrgeo === false) {
    args += '2/'; dep = arr = 0; deplat = arrlat; deplon = arrlon;
    desc = 'geo arr ' + arrdesc + ' ' + plan_iter;
    statline = 'finding nearest arrival stop';
  } else {
    log('reqplan');
    return;
  }

  var hh = mkint(srcopt("deptime"));

  var plusday = mkint(srcopt("plusday"));
  var minday = mkint(srcopt("minday"));

  var srcmode = mkint(advopt("srcmode"));

  var walklim = mkint(advopt("maxwalk"));

  var date = mkint(srcopt('depdate'));

  var pmday = toint((plusday * 1000) + minday);

  var utcofs = mkint(srcopt('timezone'));
  var dsputcofs = mkint(advopt('dsptimezone'));

  var mintts = xminttAA + xminttAa + xminttaa + xminttaA + xminttAx + xminttxA + xminttax + xminttxa;
  mintts += xminttbx + xminttxb + xmintttt + xminttxf + xminttfx;

  var effort = mkint(optC('effort'));

  var txmode = 0;
  var opts = 0;
  var ntop = 1;

  if (advopt_cb('plane') == true) txmode += 11;
  if (advopt_cb('train') == true) txmode += 100;
  if (advopt_cb('bus') == true) txmode += 1000;
  if (advopt_cb('ferry') == true) txmode += 10000;
  if (advopt_cb('taxi') == true) txmode += 100000;
  if (advopt_cb('walk') == true) txmode += 1000000;

  console.log('tx mode ' + txmode);

  args += deplat + '/' + deplon;
  args += '/' + arrlat + '/' + arrlon;
  args += '/' + dep;
  args += '/' + arr;
  args += '/' + date;
  args += '/' + hh;
  args += '/' + pmday;
  args += '/' + utcofs;
  args += '/' + dsputcofs;
  args += '/' + walklim;
  args += '/' + srcmode;
  args += '/' + txmode;
  args += '/' + mintts;
  args += '/' + effort;
  args += '/' + ntop;
  args += '/' + opts;
  args += '/';
  var url = proxy_adr + 'cgi/plantrip.pl' + args + '?' + desc.replace(/ /g,'_');

  console.log('sending ' + desc + ' ' + url);
  status(statline + ' &hellip;');
  progresspane.setAttribute("title",'sending ' + desc + ' to Tripover');

  delayedprogress = setTimeout(showprogresspane,300);

  state_reqok = false;
  state_reqtmo = false;

  toproxy.timeout = 1500 * effort + 2000;
  toproxy.ontimeout = onreqtmo;
  toproxy.open("GET",url,true);
  toproxy.onreadystatechange = onreqstate;
  toproxy.send();
}

var months = ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"];
var dows = ["Sun","Mon","Tue","Wed","Thu","Fri","Sat"];

// 20141225 from 20141225.1125
function getday(t)
{
  var dot = t.indexOf('.');
  if (dot == -1) return parseInt(t,10);
  return t.substr(0,dot);
}
// 1125 from 20141225.1125
function gethm(t)
{
  var dot = t.indexOf('.');
  if (dot == -1) return 0;
  return parseInt(t.substr(dot+1),10);
}

function fmtdhdate(t)
{
  return t.getDate() + '.' + t.getMonth() + 1 + '.' + t.getFullYear();
}

function fmtdate(t,full)
{
  var mon = months[t.getMonth()];
  var dow = dows[t.getDay()];
  var s = dow + ' ' + t.getDate() + ' ' + mon;
  if (full) s += ' ' + t.getFullYear();
  return s;
}
function fmttime(t)
{
  var hh = toint(t / 100);
  var mm = toint(t % 100);
  var s = '';

  if (hh < 10) s = ' ';
  s += hh + ':';
  if (mm < 10) s += '0';
  return s + mm;
}

function cd2str(cd)
{
  var s = '';
  var yy = toint(cd / 10000);
  var mm = toint((cd % 10000) / 100);
  var dd = toint(cd % 100);

  s = yy + '-';
  if (mm < 10) s += '0';
  s += mm + '-';
  if (dd < 10) s += '0';
  s += dd;
  return s;
}

// days between cd1 and cd2
function daydif(cd1,cd2)
{
  var d1 = new Date(cd2str(cd1));
  var d2 = new Date(cd2str(cd2));
  var dtms = d2.getTime() - d1.getTime();
  return toint(dtms / (3600 * 1000 * 24));
}

var faredep,farearr,faredate;

function onfarereq()
{
  dohopsrc.setAttribute('action','http://whitelabel.dohop.com/w/timenwheel');
  dohopsrc['a1'].value = faredep;
  dohopsrc['a2'].value = farearr;
  dohopsrc['d1'].value = faredate;
  dohopsrc.submit();
}

var trip_txt,trip_title;

// format and show plan result
function showres(txt)
{
  // console.log(txt);

  var fmt = '';
  var sum = '';
  var sumtxt = '';
  var poptxt = '';
  var errtxt = '';
  var inftxt = '';

  var lines = txt.split("\n");
  var line;
  var i;
  var cols;
  var ncol;
  var leg = 0;
  var row = 0;
  var tdep,tarr,txtime,thop;
  var mode,route,name,dist,sdist,fare;
  var sumtime,sumdist,sumstops,sumnext,sumref;
  var cdday,cdhm,prvcdday = 0,prvcdhm = 0,startcdday = 0;
  var td,ta,plusday;
  var ntrip = 0;
  var nleg = 0;
  var imgatr;
  var aname = '',asname;
  var stamp,lostamp,feedstamp = 0,feedlostamp = 0;

  var nline = lines.length;
  if (nline == 0) errtxt = 'no reply from Tripover server';

  for (i = 0; i < nline; i++) {
    line = lines[i];
    if (line.length < 1 || line.charAt(0) === '#' || line.indexOf('.planres') !== 0) continue;

    cols = line.split("\t");

    if (cols[1].indexOf('no reply') != -1) {
      errtxt = cols[1];
      break;
    }

    if (cols.length < 2) continue;

    if (cols[1] == 'result') {
      if (cols[2].indexOf('no trip found') != -1) {
        errtxt = cols[2];
        break;
      }
      if (cols[2].indexOf('no reply') != -1) {
        errtxt = cols[2];
        break;
      }
    } else if (cols[1] === 'sum') {  // summary: time dist fare [ref]
      if (sum.length) continue;
//      fmt = '<p class="tripsum">' + '<b>trip summary</b>' + '<br></span>';
      sum = '<p class="tripsum">' + '<b>At a glance</b>' + '<br></span>';
      if (cols[2] == '-') sumtime = '(no time)';
      else sumtime = cols[2];
      sumdist = cols[3];
      sumstops = cols[4];
      sumref = cols[7];
      if (cols[6] == '-') sumnext = '';
      else sumnext = ' next in ' + cols[6];
      nleg = parseInt(sumstops,10) + 1;
//      fmt += sumtime + '  ' + sumdist + '  ' + plural(sumstops,'stop') + sumnext + '</p>';
      sumtxt = sumtime + '  ' + plural(sumstops,'stop') + ' ' + sumdist + ' ' + sumnext;
      sum += sumtime + '  ' + sumdist + '<br>' + plural(sumstops,'stop') + '</p>';

    } else if (cols[1] == 'stat') {
      console.log(cols[2]);
      inftxt = cols[2];
      if (cols.length > 3) feedlostamp = cols[3];
      if (cols.length > 4) feedstamp = cols[4];
      console.log(feedlostamp);
      console.log(feedstamp);
    }
  }
  ntrip = 0;

  status(errtxt);

  var currow = 0;
  var dsprows;
  var flows = new Array();
  var descs = new Array();
  var space = new Array();
  var s;

  var deplat,deplon,arrlat,arrlon;
  var pointlst = new Array();

  flows[currow] = '';
  space[currow] = ' ';
  descs[currow++] = sumtxt;
  space[currow] = ' ';
  flows[currow] = '';

  if (errtxt.length) {
    nline = 0;
    flows[currow] = '';
    space[currow] = ' ';
    descs[currow++] = errtxt;
  }

  if (depdist && depfulnam.length > 0 && errtxt.length === 0) {
    space[currow] = '';
    flows[currow] = '';
    descs[currow++] = fmtdist(depdist) + ' from ' + depfulnam;
  }

  for (i = 0; i < nline; i++) {
    line = lines[i];
    if (line.length < 1 || line.charAt(0) === '#' || line.indexOf('.planres') !== 0) continue;
    cols = line.split("\t");
    if (cols.length < 3) continue;

    if (cols[1].indexOf('trip') !== 0) continue;

    if (ntrip) continue; // currently only one trip with time

    ncol = cols.length;
    txtime = 0;

    // depart
    if (cols[1] == 'trip-dep') {  // tdep,name

      if (leg == nleg) {
        ntrip++; leg = 0;
      }

      if (ncol < 4 || ntrip > 0) continue;

      space[currow] = ' ';

      tdep = cols[2]; name = cols[3]; sdist = cols[4];
      if (leg != 0 && name != aname && sdist !== '0 m') {
        flows[currow] = '';
        descs[currow++] = name + ' within ' + sdist;
      }
      if (tdep) {
        cdday = getday(tdep); cdhm = gethm(tdep);
        faredep = name.replace(/^[A-Za-z]/g,'');
        faredep = 'BNE';
        if (leg == 0) {
          startcdday = prvcdday = cdday;
          prvcdhm = cdhm;
          td = new Date(cd2str(cdday));
          flows[currow] = '';
          space[currow] = '';
          descs[currow++] = 'leave ' + fmtdate(td,true);
          space[currow] = '';
          flows[currow] = '';
        }
        td = new Date(cd2str(cdday));
        faredate = fmtdhdate(td);
        if (prvcdday < cdday) {
          plusday = daydif(prvcdday,cdday);
          flows[currow] = fmttime(cdhm) + '&ensp;+' + plusday;
          descs[currow++] = fmtdate(td,false);
          flows[currow] = '&thinsp;&boxv;';
          space[currow] = '';
        } else if (prvcdday > cdday) {
          plusday = daydif(cdday,prvcdday);
          flows[currow] = fmttime(cdhm) + '&ensp;-' + plusday;
          descs[currow++] = fmtdate(td,false);
          flows[currow] = '&thinsp;&boxv;';
          space[currow] = '';
        } else {
          flows[currow] = fmttime(cdhm);
        }
        prvcdday = cdday; prvcdhm = cdhm;
      } else flows[currow] = '';

      if (leg != 0) {
        s = 'continue';
        if (ncol > 5 && cols[5] !== false) {
          txtime = cols[5];
          if (txtime) s += ', ' + txtime + ' transfer time';
        }
      } else s = name;
      if (ncol > 7 && cols[6] !== false && cols[7] !== false) {
        deplat = cols[6]; deplon = cols[7];
        console.log('dep ' + deplat + ',' + deplon);
        pointlst.push(L.latLng(deplat,deplon));
      }
      descs[currow++] = s;

    // route
    } else if (cols[1] == 'trip-rou') {  //  mode,route
      if (ncol < 5) { cols[3] = cols[4] = cols[5] = cols[6] = 'n/a'; }
      mode = cols[2]; route = cols[3]; thop = cols[4]; fare = cols[5]; dist = cols[6];
      s = '&thinsp;&boxv;';
      imgatr = ' height="18" width="18" '
      if (mode == 'plane-dom' || mode == 'plane-int') {
        s += '  <img src="img/xs-icon-plane.png"' + imgatr + 'alt="plane" title="plane">';
      } else if (mode == 'train') {
        s += '  <img src="img/icon_train.png"' + imgatr + 'alt="train" title="train">';
      } else if (mode == 'bus') {
        s += '  <img src="img/icon-bus.png"' + imgatr + 'alt="bus" title="bus">';
      } else if (mode == 'walk') {
        s += '  <img src="img/icon-walk.gif"' + imgatr + 'alt="walk" title="walk">';
      } else if (mode == 'ferry') {
        s += '  <img src="img/icon_boat_white.gif"' + imgatr + 'alt="ferry" title="ferry">';
      } else if (mode == 'taxi') {
        s += '  <img src="img/aiga-taxi_20.png"' + 'alt="taxi" title="taxi">';
      } else s += mode;
      flows[currow] = s;
      space[currow] = '';
      descs[currow] = truncate(route,60) + '  ' + thop + ' ' + dist;
      // descs[currow] += '<input type="button" value="check fares" onclick="onfarereq()"></input>';
      currow++;

    // arrive
    } else if (cols[1] == 'trip-arr') {
      if (ncol < 4) continue;
      tarr = cols[2]; aname = cols[3];
      if (tarr) {
        farearr = aname.replace(/^[A-Za-z]/g,'');
        farearr = 'IRK';
        cdday = getday(tarr); cdhm = gethm(tarr);
        s = fmttime(cdhm);
        if (prvcdday < cdday) {
          plusday = daydif(prvcdday,cdday);
          td = new Date(cd2str(cdday));
          flows[currow] = s + '&ensp;+' + plusday;
          space[currow] = '';
          descs[currow++] = fmtdate(td,false);
          flows[currow] = '';
          descs[currow] = aname;
        } else if (prvcdday > cdday) {
          plusday = daydif(cdday,prvcdday);
          td = new Date(cd2str(cdday));
          flows[currow] = s + '&ensp;-' + plusday;
          space[currow] = '';
          descs[currow++] = fmtdate(td,false);
          flows[currow] = '';
          descs[currow] = aname;
        } else {
          flows[currow] = s
          descs[currow] = aname;
        }
        prvcdday = cdday; prvcdhm = cdhm;
      } else {
        flows[currow] = '';
        descs[currow] = aname;
      }
      if (ncol > 5 && cols[4] !== false && cols[5] !== false) {
        arrlat = cols[4]; arrlon = cols[5];
        console.log('arr ' + arrlat + ',' + arrlon);
        pointlst.push(L.latLng(arrlat,arrlon));
      }

      space[currow++] = '';

      leg++;

    } else if (cols[1] == 'trip-xar') {
      if (ncol < 4) continue;
      asname = cols[3]; dist = cols[4];
      if (asname === aname && dist === '0 m') continue;
      flows[currow] = '';
      descs[currow++] = asname + ' at ' + dist;
    }

  }
  if (arrdist && errtxt.length === 0) {
//  if (arrdist && arrfulnam.length > 0 && errtxt.length === 0) {
    space[currow] = '';
    flows[currow] = '';
    descs[currow++] = arrfulnam + ' at ' + fmtdist(arrdist);
  }

  var routepath = L.polyline(pointlst,{smoothFactor:0.5});
  routeset.addLayer(routepath);
  routeset.addTo(map);

  if (feedstamp != 0 && feedlostamp != 0) {
    stamp = new Date(cd2str(feedstamp));
    lostamp = new Date(cd2str(feedlostamp));
    space[currow] = '';
    flows[currow] = '';
    descs[currow++] = ' timetable data obtained ' + fmtdate(stamp,false) + ' - ' + fmtdate(lostamp,false);
  }

  dsprows = currow;

  fmt += '<span id="triplines">';

  var flow,desc;

  for (currow = 0; currow < dsprows; currow++) {

    flow = flows[currow];
    desc = descs[currow];

    if (space[currow] === ' ') fmt += '<span id="tripeline"><span id="tripflow"></span><span id="tripdesc"></span></span>';

    fmt += '<span id="tripline">';

    fmt += '<span id="tripflow">' + flow + '</span>';
    fmt += '<span id="tripdesc">' + desc + '</span>';

    fmt += '</span>'; // each line
  }

  fmt += '</span>'; // table

  trip_txt = fmt;
  trip_title = depname + ' to ' + arrname;

  if (sum.length == 0) sum = '(no summary)';
  if (fmt.length == 0) {
    fmt = 'no response from Tripover';
  }

  if (errtxt.length !== 0) {
    return;
  }

  poptxt = '<span onclick="onpopout()" style="color:blue">&rarr; open in separate window &larr;</span><br>';
  status(sumtxt);
  statuspane.setAttribute('title',inftxt + ' ' + sumref);

  poptxt += fmt;

  var mapsize = map.getSize();

  var wid = toint(mapsize.x * 0.75);
  var hgh = toint(mapsize.y * 0.75);

  var bounds = map.getBounds();
  var mapy0 = bounds.getNorth();
  var mapy1 = bounds.getSouth();

  var arry,arrx = arrlatlng[1];

  var latofs;
  if (mapy1 > mapy0) {
    latofs = (mapy1 - mapy0) * 0.45;
    arry = arrlatlng.lat + latofs;
  } else {
    latofs = (mapy1 - mapy0) * 0.45;
    arry = arrlatlng[0] - latofs;
  }

  var curzoom = map.getZoom();

  map.setView([arry,arrx],curzoom,{animate:false});

  var trip_popup = L.popup({
    minWidth: Math.min(100,wid),
    maxWidth: wid,
    maxHeight: hgh,
    offset:[0,-30],
    autoPan: false,
//    autoPanPaddingTopLeft:[42,10],
    closeOnClick: false,
    className:"trip",
    zoomAnimation: false
  })
  .setLatLng(arrlatlng)
  .setContent(poptxt)
  .openOn(map);
}

function onpopout()
{
  var popwin = window.open('',trip_title,'height=350,width=450,menubar=0,statusbar=0,toolbar=0,location=0,personalbar=0,dialog=0');

  var h = '<!DOCTYPE html>\n';
  h += '<html>\n';
  h += '<head>\n';
  h += '<title>' + trip_title + '</title>\n';
  h += '<link rel="stylesheet" href="lamlha.css" />\n';
  h += '</head>\n'

  var html = h + '<body>\n' + trip_txt + '</body></html>';
  if (popwin != null) popwin.document.write(html);
}

function showpopup(txt,wid,hgh)
{
  var view = map.getBounds();
  var y = view.getSouth();
  var x = map.getCenter().lng;

  var p = L.popup({
   maxWidth: wid,
   maxHeight: hgh,
   autoPan: false,
   closeOnClick: false,
   zoomAnimation: false,
   className:'helptxt'
   });
  p.setContent(txt);
  p.setLatLng([y,x]);
  p.openOn(map);
}

function addoption(selectbox,text,value,sel,id) {
  var opt = document.createElement("option");
  opt.text = text;
  opt.value = value;
  if (sel) opt.selected = 'selected';
  if (id.length) {
    opt.id = id;
    console.log('id ' + id + ' for ' + text);
  }

  selectbox.add(opt);
}

function addoption2(selbox1,selbox2,text,value,sel1,sel2) {
  addoption(selbox1,text,value,sel1,'');
  addoption(selbox2,text,value,sel2,'');
}

var mintts = [1,2,3,4,5,6,8,10,15,20,30,45,60,90,120,150,180];

var minttcat = 'AA';

function setmintt(def)
{
  var id,d,hhmm,opt;

  for (d = 0; d < mintts.length; d++) {
    hhmm = mintts[d];
    id = 'mintt_' + hhmm.toString();
    opt = eid(id);
    if (opt === null) {
      console.log('cannot find id ' + id + ' for ' + def);
      return;
    }
    if (def === hhmm) opt.selected = 'selected';
    else opt.removeAttribute('selected');
  }
}

function ttinit(cat,val)
{
  var xval = val.toString(16);
  if (xval.length === 1) xval = '0' + xval;
  switch(cat) {
  case 'AA': xminttAA = xval; break;
  case 'Aa': xminttAa = xval; break;
  case 'aA': xminttaA = xval; break;
  case 'aa': xminttaa = xval; break;
  case 'Ax': xminttAx = xval; break;
  case 'ax': xminttax = xval; break;
  case 'xA': xminttxA = xval; break;
  case 'xa': xminttxa = xval; break;
  case 'bx': xminttbx = xval; break;
  case 'xb': xminttxb = xval; break;
  case 'tt': xmintttt = xval; break;
  case 'xf': xminttxf = xval; break;
  case 'fx': xminttfx = xval; break;
  }
}

function onminttvalchg()
{
  var sval = optC('minttval');
  var val = parseInt(sval,10);
  var xval = val.toString(16);
  if (xval.length === 1) xval = '0' + xval;
  switch(minttcat) {
  case 'AA': minttAA = val; xminttAA = xval; break;
  case 'Aa': minttAa = val; xminttAa = xval; break;
  case 'aA': minttaA = val; xminttaA = xval; break;
  case 'aa': minttaa = val; xminttaa = xval; break;
  case 'Ax': minttAx = val; xminttAx = xval; break;
  case 'ax': minttax = val; xminttax = xval; break;
  case 'xA': minttxA = val; xminttxA = xval; break;
  case 'xa': minttxa = val; xminttxa = xval; break;
  case 'bx': minttbx = val; xminttbx = xval; break;
  case 'xb': minttxb = val; xminttxb = xval; break;
  case 'tt': mintttt = val; xmintttt = xval; break;
  case 'xf': minttxf = val; xminttxf = xval; break;
  case 'fx': minttfx = val; xminttfx = xval; break;
  }
  console.log('mintt AA ' + minttAA + ' ' + xminttAA);
  console.log('mintt tt ' + mintttt + ' ' + xmintttt);
  onoptchange();
}

function onminttcatchg()
{
  minttcat = optC('minttcat');

  switch(minttcat) {
  case 'AA': setmintt(minttAA); break;
  case 'Aa': setmintt(minttAa); break;
  case 'aa': setmintt(minttaa); break;
  case 'aA': setmintt(minttaA); break;
  case 'Ax': setmintt(minttAx); break;
  case 'ax': setmintt(minttax); break;
  case 'xA': setmintt(minttxA); break;
  case 'xa': setmintt(minttxa); break;
  case 'bx': setmintt(minttbx); break;
  case 'xb': setmintt(mintttb); break;
  case 'tt': setmintt(mintttt); break;
  case 'xf': setmintt(minttxf); break;
  case 'fx': setmintt(minttfx); break;
  }
}

function init2()
{
  var dists = [0,50,100,200,250,500,750,1000,1500,2000,2500,3000,4000,5000];
  var dist,hh,mm,hhmm,id;
  var day,mon,d;
  var now = new Date();
  var depdate = new Date(2016,2,10); // month from 0
  var ddend = new Date(2016,3,5);
  var s,v;

  var selelem = eid("depdate");
  var selelem2;

  now.setMilliseconds(0);
  now.setSeconds(0);
  now.setMinutes(0);
  now.setHours(0);
  while (depdate < ddend) {
    day = depdate.getDate();
    mon = depdate.getMonth();
    s = dows[depdate.getDay()] + ' ' + day + ' ' + months[mon];
    v = toint(20160000 + ((mon + 1) * 100) + day);
    addoption(selelem,s,v,depdate.getTime() === now.getTime(),'');
    depdate.setDate(day + 1);
  }

  selelem = eid("deptime");
  addoption(selelem,'anytime',0,0,'');
  addoption(selelem,'daytime',600,1,'');
  addoption(selelem,'morning',800,0,'');
  addoption(selelem,'afternoon',1300,0,'');
  addoption(selelem,'evening',1900,0,'');

  for (hh = 0; hh < 24; hh++) {
    addoption(selelem, hh.toString() + ':00',toint(hh * 100),0,'');
  }

  selelem = eid("plusday");
  selelem2 = eid("minday");
  addoption2(selelem,selelem2, "auto",0,1,1);
  addoption2(selelem,selelem2, "+ 2 hours",2,0,0);
  addoption2(selelem,selelem2, "+ 4 hours",4,0,0);
  addoption2(selelem,selelem2, "+ 8 hours",8,0,0);
  addoption2(selelem,selelem2, "+ 12 hours",12,0,0);
  addoption2(selelem,selelem2, "+ 18 hours",18,0,0);
  addoption2(selelem,selelem2, "+ 1 day",24,0,0);
  addoption2(selelem,selelem2, "+ 2 days",48,0,0);
  addoption2(selelem,selelem2, "+ 3 days",72,0,0);
  addoption2(selelem,selelem2, "+ 4 days",96,0,0);
  addoption2(selelem,selelem2, "+ 5 days",120,0,0);
  addoption2(selelem,selelem2, "+ 6 days",144,0,0);
  addoption2(selelem,selelem2, "+ 8 days",196,0,0);
  addoption2(selelem,selelem2, "+ 10 days",240,0,0);
  addoption2(selelem,selelem2, "+ 12 days",264,0,0);
  addoption2(selelem,selelem2, "+ 14 days",288,0,0);

  selelem = eid("srcmode");
  addoption(selelem,"fewest transfers",0,0,'');
  addoption(selelem,"balance time / transfers",1,1,'');
  addoption(selelem,"fastest trip",2,0,'');

  selelem = eid("effort");
  addoption(selelem,"lowest",1,0,'');
  addoption(selelem,"low",2,0,'');
  addoption(selelem,"medium",3,1,'');
  addoption(selelem,"higher",4,0,'');
  addoption(selelem,"highest",8,0,'');

  selelem = eid("maxwalk");
  for (d = 0; d < dists.length; d++) {
    dist = dists[d];
    if (dist < 1000) addoption(selelem, dist.toString() + ' m',dist,dist == 1500,'');
    else addoption(selelem, (dist / 1000).toString() + ' Km',dist,dist == 1500,'');
  }

  selelem = eid("minttcat");
  addoption(selelem,'int. air transfer','AA',0,'');
  addoption(selelem,'int. to dom. air transfer','Aa',0,'');
  addoption(selelem,'dom. air transfer','aa',0,'');
  addoption(selelem,'dom. to int. air transfer','aA',0,'');
  addoption(selelem,'int. air to arrival','Ax',0,'');
  addoption(selelem,'dom. air to arrival','ax',0,'');
  addoption(selelem,'checkin to int. air','xA',0,'');
  addoption(selelem,'checkin to dom. air','xa',0,'');
  addoption(selelem,'bus to bus/train','bx',1,'');
  addoption(selelem,'bus/train to bus','xb',0,'');
  addoption(selelem,'train to train','tt',0,'');
  addoption(selelem,'train/bus to ferry','xf',0,'');
  addoption(selelem,'ferry to train/bus','fx',0,'');

  selelem = eid("minttval");
  for (d = 0; d < mintts.length; d++) {
    hhmm = mintts[d];
    mm = toint(hhmm % 60); hh = toint(hhmm / 60);
    if (hh > 0) s = hh.toString() + ' hr '; else s = '';
    if (mm) s += mm.toString() + ' min';
    id = 'mintt_' + hhmm.toString();
    addoption(selelem,s,hhmm,hhmm == 5,id);
  }

  ttinit('AA',minttAA);
  ttinit('Aa',minttAa);
  ttinit('aA',minttaA);
  ttinit('aa',minttaa);
  ttinit('Ax',minttAx);
  ttinit('ax',minttax);
  ttinit('xA',minttxA);
  ttinit('xa',minttxa);
  ttinit('bx',minttbx);
  ttinit('xb',minttxb);
  ttinit('tt',mintttt);
  ttinit('xf',minttxf);
  ttinit('fx',minttfx);

  // onminttcatchg();

  var utcofs = now.getTimezoneOffset();
  log('UTC offset'+ utcofs);

  selelem = eid("timezone");
  selelem2 = eid("dsptimezone");

  addoption(selelem2,'local time',2600,1,'');

  addoption2(selelem,selelem2,'-10:00 Hawai',200,utcofs === 800,0);
  addoption2(selelem,selelem2,'-9:00 Alaska',300,utcofs === 700,0);
  addoption2(selelem,selelem2,'-8:00 California',400,utcofs === 600,0);
  addoption2(selelem,selelem2,'-7:00 Denver',500,utcofs === 500,0);
  addoption2(selelem,selelem2,'-6:00 Mexico',600,utcofs === 400,0);
  addoption2(selelem,selelem2,'-5:00 New York',700,utcofs === 300,0);
  addoption2(selelem,selelem2,'-4:30 Caracas',730,utcofs === 270,0);
  addoption2(selelem,selelem2,'-4:00 La Paz',800,utcofs === 240,0);
  addoption2(selelem,selelem2,'-3:30 Newfoundland',830,utcofs === 210,0);
  addoption2(selelem,selelem2,'-3:00 Brasilia',900,utcofs === 180,0);
  addoption2(selelem,selelem2,'-2:00 Trinidad',1000,utcofs === 120,0);
  addoption2(selelem,selelem2,'-1:00 Azores',1100,utcofs === 60,0);
  addoption2(selelem,selelem2,'-0:00 London',1200,utcofs === 0,0);
  addoption2(selelem,selelem2,'+1:00 Paris',1300,utcofs === -60,0);
  addoption2(selelem,selelem2,'+2:00 Cairo',1400,utcofs === -120,0);
  addoption2(selelem,selelem2,'+3:00 Moscow',1500,utcofs === -180,0);
  addoption2(selelem,selelem2,'+3:30 Tehran',1530,utcofs === -210,0);
  addoption2(selelem,selelem2,'+4:00 Oman',1600,utcofs === -240,0);
  addoption2(selelem,selelem2,'+4:30 Kaboul',1630,utcofs === -270,0);
  addoption2(selelem,selelem2,'+5:00 Lahore',1700,utcofs === -300,0);
  addoption2(selelem,selelem2,'+5:30 Kolkata',1730,utcofs === -330,0);
  addoption2(selelem,selelem2,'+5:45 Kathmandu',1745,utcofs === -345,0);
  addoption2(selelem,selelem2,'+6:00 Dhaka',1800,utcofs === -360,0);
  addoption2(selelem,selelem2,'+6:30 Rangoon',1830,utcofs === -390,0);
  addoption2(selelem,selelem2,'+7:00 Bangkok',1900,utcofs === -420,0);
  addoption2(selelem,selelem2,'+8:00 China',2000,utcofs === -480,0);
  addoption2(selelem,selelem2,'+9:00 Japan',2100,utcofs === -540,0);
  addoption2(selelem,selelem2,'+9:30 Adelaide',2130,utcofs === -570,0);
  addoption2(selelem,selelem2,'+10:00 Sydney',2200,utcofs === -600,0);
  addoption2(selelem,selelem2,'+11:00 Siberia',2300,utcofs === -660,0);
  addoption2(selelem,selelem2,'+12:00 Auckland',2400,utcofs === -720,0);
  addoption2(selelem,selelem2,'+13:00 Samoa',2500,utcofs === -780,0);

  selelem=eid('mapstyle');

  addoption(selelem,'ESRI topographic',0,0,0);
  addoption(selelem,'Openstreetmap',1,1,0);

  toproxy = new XMLHttpRequest();

  codedep = new XMLHttpRequest();
  codearr = new XMLHttpRequest();

  netloader = new XMLHttpRequest();

  log("using proxy " + proxy_adr);

  var ismaint = eid('head').getAttribute('maintenance');
  log(ismaint);
  if (ismaint == 1) maintenance = 1;
}

var optactivetab = 0;
var tabA,tabB,tabC,tabH;

function activetab(t)
{
  var ea,e0,e1,e2;
  if (t === 0) { ea = tabA; e0 = tabB; e1 = tabC; e2 = tabH; }
  else if (t === 1) { ea = tabB; e0 = tabA; e1 = tabC; e2 = tabH; }
  else if (t === 2)  { ea = tabC; e0 = tabA; e1 = tabB; e2 = tabH; }
  else { ea = tabH; e0 = tabA; e1 = tabB; e2 = tabC; }
  ea.style.borderWidth = "2px 2px 0px 2px";  /* trbl */
  e0.style.borderWidth = "1px 1px 2px 1px";
  e1.style.borderWidth = "1px 1px 2px 1px";
  e2.style.borderWidth = "1px 1px 2px 1px";
  ea.style.color = 'blue';
  e0.style.color = 'black';
  e1.style.color = 'black';
  e2.style.color = 'black';
}

function onsetAclick()
{
  hidex(advoptform);
  hidex(optCform);
  hidex(optHform);
  showx(srcoptform);
  activetab(0);
}
function onsetBclick()
{
  hidex(srcoptform);
  hidex(optCform);
  hidex(optHform);
  showx(advoptform);
  activetab(1);
}
function onsetCclick()
{
  hidex(srcoptform);
  hidex(advoptform);
  hidex(optHform);
  showx(optCform);
  activetab(2);
}

function onsetHclick()
{
  hidex(srcoptform);
  hidex(advoptform);
  hidex(optCform);
  showx(optHform);
  activetab(3);
}

var netshown = false;

function shownet()
{
  netshown = true;
}

var netopts = {
  weight:1,
  fill:false,
  radius:1,
  color:'#700',
  clickable:false
};

// read from external data: { lats[], lons[], cnts[] }
var network;

var netitems = []
var netitemgrp;

var netloaded = false;
var netloading = false;

var netext = 'all';

function havenet()
{
  log('havenet ');
  netloaded = true;
}

function mknet()
{
  var i,r,lat,lon;
  var len = network.lats.length;

  netitems = [];
  netitems.length = len;

  log('mknet ' + len);
  for (i = 0; i < len; i++) {
    lat = network.lats[i];
    lon = network.lons[i];
    netitems[i] = [lat,lon];
  }

  netitemgrp.clearLayers();

  var curzoom = map.getZoom();

  for (i = 0; i < len; i++) {
    r = Math.max(network.cnts[i],1) * 2;
    r = Math.round(Math.log(r)) + 1;
    netopts.radius = r;
    netitemgrp.addLayer(L.circleMarker(netitems[i],netopts));
  }
}

function loadnet()
{
  var net = 'net/network-' + netext + '.txt';
  log('reading ' + net);
  netloader.open("GET",net,true);
  netloader.onreadystatechange = onnetstate;
  netloader.send();
}


function togglenet()
{
  var now = Date.now();

  if (map.hasLayer(visnet) === true) map.removeLayer(visnet);
  else visnet.addTo(map);
}

function onmapchange()
{
  var style = srcopt("mapstyle");

  if (style === '0') {
    if (map.hasLayer(OSM_map) === true) map.removeLayer(OSM_map);
    Esri_WorldTopoMap.addTo(map);
  } else if (style === '1') {
    if (map.hasLayer(Esri_WorldTopoMap) === true) map.removeLayer(Esri_WorldTopoMap);
    OSM_map.addTo(map);
  }
}

function parsenet(s)
{
  console.log('parse net');
  network = JSON.parse(s);
  if (network === false) {
    console.log("cannot parse");
    return true;
  }
  return false;
}

// callback for netload
function onnetstate()
{
  if (netloader.readyState != 4) return;
  var hs = netloader.status;
  console.log('proxy result status ' + hs);
  if (hs !== 200) {
    if (hs === 0) status("no response from server");
    else if (hs === 500) status("server returned internal error");
    else status("server returned error code " + hs);
    return;
  }
  if (netloader.responseText == null || netloader.responseText === '') {
    status('empty network');
    return;
  }
  if (parsenet(netloader.responseText)) return;
  netloading = false;
  netloaded = true;
  mknet();
}

function init()
{
  statuspane = eid("status");
  dirpane = eid("dirtxt");
  srcoptform = eid("srcopt");
  advoptform = eid("advopt");
  optCform = eid("optC");
  optHform = eid("optH");
  progresspane = eid('progress');
  depnamepane = eid('depname');
  arrnamepane = eid('arrname');
  depfulnampane = eid('depfulnam');
  arrfulnampane = eid('arrfulnam');
  tabA = eid('setA');
  tabB = eid('setB');
  tabC = eid('setC');
  tabH = eid('setH');
  dohopsrc = eid('dohopsrc');

  onsetAclick();

  depnamepane.value = '';
  arrnamepane.value = '';

  map = new L.Map('map',{
   closePopupOnClick:false,
   bounceAtZoomLimits:false,
   inertia:false,
   attributionControl:false,
   fadeAnimation:false,
   zoomAnimation:false,
   markerZoomAnimation:false
  });

  tooltip("sitecopy","javascript, html, css version " + version + '  last changed ' + lastchanged);

  if (location.protocol == 'file:') proxy_adr = local_proxy_adr;
  else proxy_adr = remote_proxy_adr;

  Esri_WorldTopoMap = L.tileLayer('http://server.arcgisonline.com/ArcGIS/rest/services/World_Topo_Map/MapServer/tile/{z}/{y}/{x}',{zIndex: '0'});

  OSM_map = L.tileLayer('http://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {zIndex: '0'});

  visnet = L.tileLayer(proxy_adr + 'vcgi/vis.x/{z}/{y}/{x}.bmp',{zIndex: '1',opacity:'0.3'});

  // Esri_WorldTopoMap.addTo(map);
  OSM_map.addTo(map);

//  visnet.addTo(map);

//  map.attributionControl.setPrefix(''); // Don't show the 'Powered by Leaflet' text.

  var london = new L.LatLng(51.505, -0.09);
  var brisbane = new L.LatLng(-27.5, 153.0);
  var melbourne = new L.LatLng(-37.67,144.85);
  var utrecht = new L.LatLng(52.09, 5.11);
  var au = new L.LatLng(-27.07, 135.96);
  var us = new L.LatLng(40.0, -96.0);
  var eu = new L.LatLng(49.34,11.28);
  var cn = new L.LatLng(34.0,108.0);
  var bd = new L.LatLng(24.1,90.0);

  if (region === 'au') map.setView(au, 5);
  else if (region === 'nl') map.setView(utrecht, 8);
  else if (region === 'us') map.setView(us, 5);
  else if (region === 'eu') map.setView(eu, 5);
  else if (region === 'cn') map.setView(cn, 5);
  else if (region === 'bd') map.setView(bd, 7);

  else map.setView(brisbane,9);

  arrlatlng = brisbane;

  // markers for nearby stops
  mopts_air.icon = new L.Icon({
    iconUrl: 'img/red-plane-dep.png',
    iconSize: [20,20],
    iconAnchor: [26,26]
  });
  mopts_train.icon = new L.Icon({
    iconUrl: 'img/icon_train.png',
    iconSize: [20,20],
    iconAnchor: [26,26]
  });
  mopts_bus.icon = new L.Icon({
    iconUrl: 'img/icon-bus.png',
    iconSize: [20,20],
    iconAnchor: [26,26]
  });
  mopts_ferry.icon = new L.Icon({
    iconUrl: 'img/icon_boat_white.gif',
    iconSize: [20,20],
    iconAnchor: [26,26]
  });

  // markers for dep,arr
  depmopts.icon = new L.Icon({
    iconUrl: 'img/icon-ios7-circle-outline-32-green.png',
    iconSize: [32,32]
  });
  arrmopts.icon = new L.Icon({
    iconUrl: 'img/icon-ios7-circle-outline-32-blue.png',
    iconSize: [32,32]
  });

  map.on('click', onclick);
  map.on('dblclick', ondblclick);
  map.on('contextmenu', onrtclick);

  routeset = L.layerGroup();

  init2();
  status('');
  if (window.location.href.indexOf('coverage=1') > 0) {
    eid('netshow').checked='checked';
    togglenet();
  }
}

var mysite = 'lamlha.net';
console.log(window.location.hostname);

/*
if (window.location.hostname != mysite && window.location.hostname != '192.168.1.4' && window.location.hostname != 'localhost') {
  console.log('ll');
  window.location = 'http://' + mysite;
} else */ window.onload = init;

/*
http://leaflet-extras.github.io/leaflet-providers/preview/
var Esri_WorldStreetMap = L.tileLayer('http://server.arcgisonline.com/ArcGIS/rest/services/World_Street_Map/MapServer/tile/{z}/{y}/{x}', {
	attribution: 'Tiles &copy; Esri &mdash; Source: Esri, DeLorme, NAVTEQ, USGS, Intermap, iPC, NRCAN, Esri Japan, METI, Esri China (Hong Kong), Esri (Thailand), TomTom, 2012'
});
var Esri_WorldImagery = L.tileLayer('http://server.arcgisonline.com/ArcGIS/rest/services/World_Imagery/MapServer/tile/{z}/{y}/{x}', {
	attribution: 'Tiles &copy; Esri &mdash; Source: Esri, i-cubed, USDA, USGS, AEX, GeoEye, Getmapping, Aerogrid, IGN, IGP, UPR-EGP, and the GIS User Community'
});

var OpenStreetMap_Mapnik = L.tileLayer('http://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
	attribution: '&copy; <a href="http://www.openstreetmap.org/copyright">OpenStreetMap</a>'
});
var Esri_NatGeoWorldMap = L.tileLayer('http://server.arcgisonline.com/ArcGIS/rest/services/NatGeo_World_Map/MapServer/tile/{z}/{y}/{x}', {
	attribution: 'Tiles &copy; Esri &mdash; National Geographic, Esri, DeLorme, NAVTEQ, UNEP-WCMC, USGS, NASA, ESA, METI, NRCAN, GEBCO, NOAA, iPC',
	maxZoom: 16
});
var HERE_normalDayCustom = L.tileLayer('http://{s}.{base}.maps.cit.api.here.com/maptile/2.1/maptile/{mapID}/normal.day.custom/{z}/{x}/{y}/256/png8?app_id={app_id}&app_code={app_code}', {
	attribution: 'Map &copy; 1987-2014 <a href="http://developer.here.com">HERE</a>',
	subdomains: '1234',
	mapID: 'newest',
	app_id: '<insert your app_id here>',
	app_code: '<insert your app_code here>',
	base: 'base',
	minZoom: 0,
	maxZoom: 20
});
var HERE_hybridDay = L.tileLayer('http://{s}.{base}.maps.cit.api.here.com/maptile/2.1/maptile/{mapID}/hybrid.day/{z}/{x}/{y}/256/png8?app_id={app_id}&app_code={app_code}', {
	attribution: 'Map &copy; 1987-2014 <a href="http://developer.here.com">HERE</a>',
	subdomains: '1234',
	mapID: 'newest',
	app_id: '<insert your app_id here>',
	app_code: '<insert your app_code here>',
	base: 'aerial',
	minZoom: 0,
	maxZoom: 20
});

 */
