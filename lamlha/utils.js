// utils.js - Time & Wheel journey planner js utilities

/*
  author: Joris van der Geer

 */

"use strict";

var version = 1.0;
var lastchanged = '23 Jan 2016';

var feedbackurl = 'fedback.html';

// ui elems
var cmtloader;

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
  eid(e).setAttribute("title",s);
}

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

function fbfld(f)
{
  log(f);
  return document.forms['feedback'][f].value;
}

function onfbsubmit()
{
  var name = fbfld('name');
  var email = fbfld('email');
  var cmt = truncate(fbfld('comment'),2048);
  var url = feedbackurl + '?name=';
  url += encodeURIComponent(name);
  url += '&email=';
  url += encodeURIComponent(email);
  url += '&cmt=';
  url += encodeURIComponent(cmt);

  console.log(url);

  cmtloader.open("GET",url,true);
  cmtloader.send();
  show(eid('fbreceived'));
}

function init()
{
  cmtloader = new XMLHttpRequest();

  tooltip("sitecopy","javascript, html, css version " + version.toString() + '  last changed ' + lastchanged);
}

window.onload = init;
