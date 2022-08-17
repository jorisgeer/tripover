#!/usr/bin/perl -W

# mkfeed.pl - manage gtfs feeds

# This file is part of Tripover, a broad-search journey planner.

#  Copyright (C) 2015-2017 Joris van der Geer.

# fetch,prepare,process and merge feeds according to a config file.

use 5.012;
use strict;
use utf8;
use POSIX qw(strftime);

my $version_maj = 1;
my $version_min = 1;
my $lastchanged = "10 Feb 2017";

my $glinno = 0;

# stop at compile-time warnings
local $SIG{__WARN__} = sub { print "$_[0] input line $glinno\n"; exit 1; };

# defaults for commandline options
my $verbose = 0;
my $dryrun = 0;
my $docheck = 0;
my $dozip = 0;

my $stopat = 'x';
my $feeds = 'feeds';

my $feedcfg = 'feeds.cfg';

my $mergefirst = 1;
my $mergedir;

my $distlimit=20;

my $startdate=20170101;
my $enddate=20170121;

my $getafter=20191231;

my $lostamp;
my $histamp = 0;

my $startat = '';
my $stopat1 = '';
my $histate = '';
my $lostate = '';
my $gprepopt = '';
my $gprepopt2 = '';
my $feedset = '';

my $feedlst = '';

my $do_patch = 0;
my $do_updcheck = 0;
my $do_xinfo = 0;
my $stopatcfg = 0;
my $showtf = 0;

my @feedfiles = ('agency','stops','routes','trips','stop_times','transfers','calendar','calendar_dates');

binmode(STDOUT,':utf8');

my $logfd;

open($logfd,'>:encoding(UTF-8)','mkfeed.log') or print("cannot create mkfeed:$!");

sub msg($) {
  my ($m) = @_;

  print("$m\n");
  print($logfd "$m\n");
  return 1;
}

sub vrb($)     { msg("$_[0]") if $verbose; return 1; }
sub info($)    { return msg("$_[0]"); }
sub warning($) { return msg("warning: $_[0]"); }

sub error($)
{
  my ($package,$filename,$line) = caller(0);

  msg("$line  error: $_[0]"); return 0;
}

sub serror($)
{
  msg("$_[0]"); return 0;
}

sub error_exit($) {
  my ($package,$filename,$line) = caller(0);

  msg("$line  error: $_[0]"); exit 1;
}

sub trimws($) {
  my ($s) = @_;
  $s =~ s/[ \r\n]+/ /g;
  $s =~ s/^ //g;
  $s =~ s/ $//g;
  return $s;
}

# action:
# g get
# u unzip
# p prep
# m merge
# a air

# p2 prep2
# t tool

# set name  startstate  endstate    dateshift   url

my (@feednos,@names,@state0s,@state1s,@orgstate0s,@prepopts,@urls,@regions,@feedprops);
my %feedbyname;
my $feedcnt = 0;

my (%names,%urls,%plainurls,%alturls,%agurls,%lcurls,%lcplainurls);

my $pi = 3.141592655;
my $geolow = $pi * 2.0e-6;  # ~50m
my $geolimit = $pi * 1.0e-8;
my $mean_earth_radius = 6371.0;
my $approx_surface = sqrt($mean_earth_radius * $mean_earth_radius + $mean_earth_radius * $mean_earth_radius);

sub acos { atan2( sqrt(1 - $_[0] * $_[0]), $_[0] ) }

# Adapted from Tripover:math.c which in turn is adapted from Wikipedia article
sub geodist($$$$)
{
  my ($slat,$slon,$lat,$lon) = @_;

  my ($dist,$dlat,$dlon);

  my $phi1 = ($slat * $pi) / 180;
  my $lam1 = ($slon * $pi) / 180;
  my $phi2 = ($lat * $pi) / 180;
  my $lam2 = ($lon * $pi) / 180;

  my $dlam = $lam2 - $lam1;
  my $dphi = $phi2 - $phi1;

  return 0 if abs($dlam) < $geolimit and abs($dphi) < $geolimit; # flush to zero

  if (abs($dlam) < $geolow and abs($dphi) < $geolow) { # trivial case: assume flat
    $dlat = $dlam * $approx_surface * 2 / $pi;
    $dlon = ($dphi * $approx_surface * 2) / $pi;
    $dist = sqrt( ($dlat * $dlat) + ($dlon * $dlon));
    return $dist;
  }

  my ($d,$dsig);

  $d = sin($phi1) * sin($phi2) + cos($phi1) * cos($phi2) * cos($dlam);
  if ($d >= 1.0) { error("geodist d $d for $phi1 $phi2 $lam1 $lam2"); return 0; }
  elsif ($d <= -1.0) { error("geodist d $d for $phi1 $phi2 $lam1 $lam2"); return 0; }

  $dsig = acos($d);

  $dist = $dsig * $mean_earth_radius;
  return $dist;
}

sub readcfg($)
{
  my $cfgname = shift;

  my ($cfg,$tfurl,$plainurl,$agurl,$c,$val,$ena2,$cnt);
  my ($line,$feednos,$ena,$name,$state0,$state1,$orgstate0,$prepopt,$url,$region,$feedprop);
  my ($user,$pwd,$neturl,$xtra);
  my %cmpurls;
  my $rawfeedcnt = 0;
  my $webfeedcnt = 0;
  my (%setcnts,%enacnts);
  my %lstfeeds;

  my $linno = 0;

  if (length($feedlst)) {
    open(my $lst,'<',$feedlst) or error_exit("cannot open $feedlst: $!");
    my @lstlines = readline($lst);
    close($lst);
    foreach $line (@lstlines) {
      $linno++;
      $line = trimws($line);
      next unless length($line);
      $c = substr($line,0,1);
      next if $c eq '#';
      $lstfeeds{$line} = $linno;
    }
  }

  my $tfurlname = 'tfurls.json';
  open($tfurl,'<:encoding(UTF-8)',$tfurlname) or error_exit("cannot open $tfurlname: $!");

  my @tflines = readline($tfurl);
  close($tfurl);

  my ($xurl,$title);
  my $tfcnt = 0;
  my $ndx = 0;
  my @tfurlset;
  my (%tfurls,%tftitles);

  my $urlpati = qr/"i":"([-_.A-Za-z0-9:\/\\?=&%]+)"/;
  my $urlpatd = qr/"d":"([-_.A-Za-z0-9:\/\\?=&%]+)"/;

  foreach $line (@tflines) {
    $line = trimws($line);
    next unless length($line);
    @tfurlset = ($line =~ /"ty":"gtfs","t":"([-.,&_\/\\A-Za-z0-9 %]+)","l":\{[^}]+?\},"u":\{([^}]+?)\}/g);

    $cnt = scalar(@tfurlset);
    $ndx = 0;
    while ($ndx < $cnt) {
      $title = $tfurlset[$ndx];
      $xurl = $tfurlset[$ndx+1];
      $ndx += 2;
      $title = '' unless defined $title;
      unless (defined $xurl and length $xurl) {
        warning("item '$title' has no urls");
        next;
      }
      ($agurl) = ($xurl =~ $urlpati);
      ($url) = ($xurl =~ $urlpatd);
#      info("  xurl '$xurl'");
#      info("");
      $agurl = '' unless defined $agurl;

      $title =~ tr/\\//d;
      $agurl =~ tr/\\//d;

      unless (defined $url and length $url) {
#        warning("item '$title' has no url");
#        info("  agurl '$agurl'\n") if length $agurl;
#        info("  xurl '$xurl'\n");
        next;
      }

      $url =~ tr/\\//d;
#      info("  url '$url'");

      # info(" $title url $url ag $agurl");
      if (exists($tfurls{$url})) {
#        warning("duplicate TF url $url");
        next;
      }
      $tfcnt++;
      $tfurls{$url} = $agurl;
      $tftitles{$url} = $title;
#      info("$title");
#      info("  url '$url'");
#      info("  ag  '$agurl'");
#      info("");
    }
  }
  info("$tfcnt TF urls");
#  return 0;

  my $tlurlname = 'tlurls.json';
  open(my $tlurl,'<:encoding(UTF-8)',$tlurlname) or error_exit("cannot open $tlurlname: $!");

  $line = readline($tlurl);
  close($tfurl);

  my $tlcnt = 0;
  my $tldup = 0;
  $ndx = 0;
  my (%tlurls,%tltitles);
  my $onestop;

  my @tlurlset = ($line =~ /\{"onestop_id":"[^"]+","url":"([-.,&?=_\/:A-Za-z0-9%#\(\)]+)","feed_format":"gtfs"/g);

  foreach $url (@tlurlset) {

    unless (defined $url and length $url) {
      warning("empty url #$tlcnt");
      next;
    }

    if (exists($tlurls{$url})) {
      warning("duplicate TL url $url #$tlcnt");
      $tldup++;
      next;
    }
    $tlcnt++;
    $tlurls{$url} = $tlcnt;
    $tltitles{$url} = '';
#      info("$title");
#      info('"url":"' . "$url");
#      info("");
  }
  info("$tlcnt TL urls $tldup dups");

#  return 0;

  open($cfg,'<:encoding(UTF-8)',$cfgname) or error_exit("cannot open $cfgname: $!");

  my @cfglines = readline($cfg);
  error_exit("$cfgname is empty") unless @cfglines > 0;
  close($cfg);

  my $beforestart = 0;
  $beforestart = 1 if length $startat;

  $linno = 0;
  my $regprepopt = '';
  my %options;
  my $intf = 0;

  info("start at $startat") if length $startat;
  foreach $line (@cfglines) {
    $linno++;
    $line = trimws($line);
    unless (length($line)) {
      $url = '';
      $agurl = '';
      next;
    }
    $c = substr($line,0,1);
    if ($c eq '#') {
      $url = '';
      next;
    }

    if ($c eq '.') {  # options
      ($name,$val) = split("\t",$line);
      next unless defined $name and length $name > 1;
      $name = substr($name,1);
      next unless length $name;
      return error("$cfgname.$linno: $name previously defined at $options{$name}") if exists($options{$name});
      $options{$name} = $linno;
      $val = '' unless defined $val;
      if ($name eq 'startdate') { $startdate = $val; }
      elsif ($name eq 'enddate') { $enddate = $val; }
      elsif ($name eq 'distlimit') { $distlimit = $val; }
      elsif ($name eq 'prepopts') { $gprepopt = $val; }
      elsif ($name eq 'prepopts2') { $gprepopt2 = $val; }
      elsif ($name eq 'regprepopts') { $regprepopt = $val; }
      elsif ($name eq 'set') {
         $feedset = $val unless length($feedset);
      } else { warning("skip unknown var $name"); }
      next;
    } elsif ($c eq '~') {  # skipped
      $name = substr($line,2);
      warning("line $linno: $name skipped");
      # info("store $name");
      if (exists($cmpurls{$name})) {
        warning("line $linno: $name previously defined at $cmpurls{$name}");
        next;
      }
      $cmpurls{$name} = $linno;
      next;
    } elsif ($c eq '=') {  # metadata
      $line = trimws(substr($line,1));
      $intf = (index($line,'tf') >= 0);
      next;
    } elsif (length($line) > 7 and ($line =~ '^/?https?://') or $line =~ '^/?ftps?://') { # plain url
      $plainurl = trimws($line);
      error_exit("line $linno malformed url $plainurl") if (index($plainurl,' ') > 0) or (index($plainurl,"\t") > 0);
      if (substr($plainurl,0,1) eq '/') {
        $plainurl = substr($plainurl,1);
      } else {
        error_exit("line $linno url $plainurl previously defined at $plainurls{$plainurl}") if exists $plainurls{$plainurl};
      }
      error_exit("line $linno alt url $plainurl identical to base") if defined $url and length $url and $url eq $plainurl;
      error_exit("line $linno malformed url '$plainurl'") unless ($plainurl =~ '^(ht|f)tps?://[-_/A-Zöa-z0-9.?&=%#]+$');

      $plainurls{$plainurl} = $linno;
      $alturls{$url} .= "$plainurl\t" if defined $url and length $url; # and $url ne 'manual';
      $agurl = $plainurl;
      next;
    } elsif ($c eq '[') {  # section
      info("processing $line");
      $url = '';
      $agurl = '';
      next;
    }

    return error("line $linno unknown code '$c'") unless $c =~ /[a-zA-z]/;
    ($ena,$name,$region,$state0,$state1,$prepopt,$url,$xtra) = split("\t",$line);

    error_exit("line $linno empty name") unless defined $name and length $name;
    error_exit("line $linno name $name previously defined at $names{$name}") if exists $names{$name};

    error_exit("line $linno name malformed $name") if $name =~ /[,:?& %*]/;

    error_exit("line $linno empty region") unless defined $region and length $region;
    error_exit("line $linno empty state0") unless defined $state0 and length $state0;
    error_exit("line $linno empty state1") unless defined $state1 and length $state1;
    error_exit("line $linno empty popt") unless defined $prepopt and length $prepopt;

    error_exit("line $linno incomplete line") unless defined $url and length $url;
    error_exit("line $linno incorrect line") if $url eq '0';

    error_exit("line $linno spurious arg") if defined $xtra;

#    warning("$name '$region'") unless index($region,' ') < 0;

    if (substr($url,0,6) ne 'manual' and $url ne 'a') {
      if ($state0 eq 'g') {
        ($user,$pwd,$neturl) = ($url =~ '^user=([A-Za-z0-9.@]+) pwd=([A-Za-z0-9.])+ ((?:ft|htt)ps?://[-_/A-Za-z0-9.?&=]+)$');
        $neturl = $url unless defined $neturl and length $neturl;
#        error_exit("line $linno malformed url $url") unless ($neturl =~ '^https?://' or $neturl =~ '^ftps?://');
        error_exit("line $linno malformed url '$neturl'") unless ($neturl =~ '^(ht|f)tps?://[-_/A-Za-z0-9.?&=%:@#]+$');
      } else { $neturl = $url; }
      error_exit("line $linno url $url previously defined at $plainurls{$neturl}") if exists $plainurls{$neturl};
      if ($state0 ne 's') {
        error_exit("line $linno $name url $neturl previously defined at $urls{$neturl}") if exists $urls{$neturl};
        $urls{$neturl} = $linno . ' ' . $name;
        $agurls{$neturl} = $agurl if length $agurl;
      }
    }
    return error("line $linno url $url from $cmpurls{$url}") if substr($url,0,6) ne 'manual' and exists $cmpurls{$url};
    $agurl = '';

    $names{$name} = $linno;
    $ena = '' unless defined $ena;
    $ena2 = '';
    $ena2 = chop($ena) if length($ena) > 1;

    last if $name eq $stopat1 and $startat ne $stopat1;

    $orgstate0 = $state0;

    if ($beforestart) {
      if ($name eq $startat) { $beforestart = 0; }
      else {
        $state0 = 'm' if $state0 eq 'g' or $state0 eq 'u' or $state0 eq 'p' or $state0 eq 's' or $state0 eq 'n' or $state0 eq 'a';
      }
    }
    if (length($histate)) {
      if ($histate eq 'a' or $histate eq 's') {
        if ($state0 eq 'g' or $state0 eq 'u' or $state0 eq 'p') { $state0 = 'm'; }
      } else {
        if ($state0 eq 'g') { $state0 = $histate; }
        elsif ($state0 eq 's' and $histate ne 's' and $histate ne 'g' and $histate ne 'u') { $state0 = 'x'; }
        elsif ($state0 eq 'u' and $histate ne 'g') { $state0 = $histate; }
        elsif ($state0 eq 'p' and $histate eq 'm') { $state0 = $histate; }
        elsif ($state0 eq 'a' and $histate eq 'm') { $state0 = $histate; }
        elsif ($state0 eq 'n' and $histate eq 'm') { $state0 = $histate; }
      }
    }
    if (length($lostate)) {
      if ($state1 eq 'm') { $state1 = $lostate; }
      elsif ($state1 eq 'p' and $lostate ne 'm') { $state1 = $lostate; }
    }

    next if length($ena) == 0;
    $rawfeedcnt++;
    $webfeedcnt++ if $histate eq 'g' and $ena ne '-' and $ena ne 'x';
    $setcnts{$ena}++;
    $enacnts{$ena} = 0 unless exists $enacnts{$ena};
    if (length($ena2)) {
      next if index($feedset,$ena) < 0 and index($feedset,$ena2) < 0;
    }
    next if index($feedset,$ena) < 0;

    next unless defined $state1;

    next if length($feedlst) and not exists $lstfeeds{$name};

    $enacnts{$ena}++;
#    info("'$name' $state0");
    $prepopt = '' unless defined $prepopt;
    $prepopt = '' if $prepopt eq '0';
    $prepopt .= ' ' . $regprepopt if length $regprepopt;
    $url = '' unless defined $url;
    $feedprop = '';
    $feedprop .= 'TF' if $intf;
    push @names,$name;
    push @state0s,$state0;
    push @orgstate0s,$orgstate0;
    push @state1s,$state1;
    push @prepopts,$prepopt;
    push @urls,$url;
    push @feednos,$feedcnt;
    push @regions,$region;
    push @feedprops,$feedprop;
    $feedbyname{$name} = $feedcnt;
    $feedcnt++;
    last if $name eq $stopat1;
    $intf = 0;
  }
  info("$feedcnt from $rawfeedcnt feeds $webfeedcnt web");

  return error("$startat not encountered") if $beforestart;

  while (($url,$linno) = each %urls) {
#   info("new url '$url'");
    $lcurls{lc($url)} = $linno;
  }
  while (($url,$linno) = each %plainurls) {
    $lcplainurls{lc($url)} = $linno;
  }

  my $ntfcnt = 0;
  my $havealt = 0;
  my ($agfname,$agfh,$keypos,$prvurl,$sumfname,$sumfh);
  my ($country,$state,$city,$dist);
  my @aglines;
  my @agcols;

  my ($sumregion,$sumname,$agcnt,$stopcnt,$routecnt,$start,$end,$days,$minlat,$maxlat,$minlon,$maxlon);

  info("feed urls not in TF:") if $showtf;
  for my $feedno (@feednos) {
    $state0 = $orgstate0s[$feedno];
    $state1 = $state1s[$feedno];
    next unless $state0 eq 'g';
    next unless $state1 eq 'm';
    $name = $names[$feedno];
    $url = $urls[$feedno];
    $agurl = $agurls{$url};
    next unless index($url,'gtfs.s3.amazonaws.com') < 0;
    next unless index($url,'transitfeeds.com') < 0;

    my ($xurl) = ($url =~ '^user=.+? pwd=.+? (.+)$');
    $url = $xurl if defined $xurl and length $xurl;
    next if exists $tfurls{$url};
    if (exists($alturls{$url})) {
      $havealt = 0;
      foreach my $alt (split("\t",$alturls{$url})) {
        next unless defined $alt and length $alt;
        $havealt = 1 if exists $tfurls{$alt};
      }
      next if $havealt;
    }
    $ntfcnt++;
    if ($showtf) {

      ($country,$state,$city) = split(",",$regions[$feedno]);

      ($country,$state,$city) = split('/',$name) unless defined $country and length $country;

      info("Country\t\t$country") if defined $country and length $country;

      if (defined($city) and length($city)) {
        info("Region\t\t$state") if defined $state and length $state;
        info("City\t\t$city") if defined $city and length $city;
      } else {
        info("Region/city\t$state") if defined $state and length $state;
      }

      $keypos = index($url,'?key=');
      $url = substr($url,0,$keypos) if $keypos > 0;

      info("ID\t\t$name");
      info("Feed URL\t$url");
      info("Landing page\t$agurl") if defined $agurl and length $agurl;

#      next;

      $sumfname = "$name/in/summary.tab";

      open($sumfh,'<:encoding(UTF-8)',$sumfname) or error_exit("cannot open $sumfname: $!");
      $line = readline($sumfh);
      error_exit("$sumfname is empty") unless defined $line and length $line;
      $line = readline($sumfh);
      error_exit("$sumfname is empty") unless defined $line and length $line;
      close($sumfh);
      $line = trimws($line);
      ($sumregion,$sumname,$agcnt,$stopcnt,$routecnt,$start,$end,$days,$minlat,$maxlat,$minlon,$maxlon) = split("\t",$line);

      $dist = geodist($minlat,$minlon,$minlat,$maxlon);
      $dist += geodist($minlat,$minlon,$maxlat,$minlon);
      $dist += geodist($maxlat,$minlon,$maxlat,$maxlon);
      $dist += geodist($minlat,$maxlon,$maxlat,$maxlon);
      $dist = sprintf("%.0f",$dist);
      info("routes\t\t$routecnt");
      info("stops\t\t$stopcnt");
      info("valid\t\t$start .. $end  $days days");
      info('');
      info("area\t\t$minlat, $minlon .. $maxlat, $maxlon  $dist Km");

#      info('');
#      next;

      info("agencies");

      $agfname = "$name/in/agency.tab";

      open($agfh,'<:encoding(UTF-8)',$agfname) or error_exit("cannot open $agfname: $!");
      @aglines = readline($agfh);
      error_exit("$agfname is empty") unless @aglines > 1;
      close($agfh);

      $prvurl = '';
      foreach $line (@aglines) {
        $line = trimws($line);
        next unless length $line;
        next if substr($line,0,1) eq '#';
        next if index($line,'agency_id') == 0;
        @agcols = split("\t",$line);
        $agurl = $agcols[3];
        if ($agurl eq $prvurl) { printf("  %-25s\n",$agcols[1]); }
        else { printf("  %-25s \t%s\n",$agcols[1],$agurl); }
        $prvurl = $agurl;
      }

      info("");
      info("");
#      info("  $agurl") if defined $agurl and length $agurl;
#      info("");
    }
  }
  info("$ntfcnt of $feedcnt not in TF") if $ntfcnt;
#  return 0;

  $showtf = 0;
  my $nfcnt = 0;
  # info("TF urls not in feeds:");
  foreach $url (sort keys %tfurls) {
    next if exists($urls{$url});
    next if exists($plainurls{$url});
    $agurl = $tfurls{$url};
    $title = $tftitles{$url};
    if ($showtf) {
      info("TF $title not in feeds");
      info("$url");
      info(" agurl $agurl") if length $agurl;
      info('');
    }
    $nfcnt++;
  }
  info("$nfcnt of $tfcnt TF not in feeds") if $nfcnt;
#  return 0;

  $showtf = 0;

  my $nlcnt = 0;
  my ($lcurl,$suburl);
  # info("TL urls not in feeds:");
  foreach $url (sort keys %tlurls) {
    next if exists($urls{$url});
    next if exists($plainurls{$url});

    $lcurl = lc($url);
    next if exists($lcurls{$lcurl});
    next if exists($lcplainurls{$lcurl});

    next if index($lcurl,'http://') == 0 and (exists $lcurls{'https://' . substr($lcurl,7)} or exists $lcplainurls{'https://' . substr($lcurl,7)});

    next if index($lcurl,'https://') == 0 and (exists $lcurls{'http://' . substr($lcurl,8)} or exists $lcurls{'http://' . substr($lcurl,8)});

    $agurl = $tlurls{$url};
    if ($showtf) {
      foreach $suburl (keys %lcurls) {
        info(" F $suburl\n contains TL $lcurl") unless index($suburl,$lcurl) < 0;
        info(" TL $lcurl\n contains F $suburl") unless index($lcurl,$suburl) < 0;
      }

      info("$url");
#      info(" agurl $agurl") if length $agurl;
#      info('');
    }
    $nlcnt++;
  }
  info("$nlcnt of $tlcnt TL not in feeds") if $nlcnt;

  return 0 if $stopatcfg;

  while (($ena,$cnt) = each %setcnts) { info("$ena: $cnt $enacnts{$ena}"); }
  return 1;
}

sub run($$$$$)
{
  my ($dir,$cmd,$arglst,$silent,$xexit) = @_;

  my ($orgdir,$arg);
  my $rv = 0;

  my (@args,@rawargs);
  push(@args,$cmd);

  push(@rawargs,split("\t",$arglst));
  for $arg (@rawargs) { push(@args,$arg) if defined $arg and length $arg; }

  if ($dir ne $ENV{PWD} and $dir ne '.') {
    $orgdir = $ENV{PWD};
    vrb("cd $dir");
    chdir($dir);
    info("[$dir] " . join(' ',@args));
  } else {
    info(join(' ',@args));
  }

  $rv = system(@args) unless $dryrun;
  if (defined $orgdir) {
    vrb("cd $orgdir");
    chdir($orgdir);
  }

  if ($rv == -1) {
    return error("failed to run $cmd: $!");
  }
  elsif ($rv & 127) {
    my $sig = $rv & 127;
    return error("$cmd received signal $sig");
  }
  my $rc = ($rv >> 8);
  $arglst =~ tr/\t/ /;
  if ($rc) {
    return warning("$cmd returned $rc\n\n$arglst\n") if $rc == $xexit and $silent == 0;
    return error("$cmd returned $rc\n\n$arglst\n") if $silent == 0;
    return 0;
  }
  return 1;
}

# mkdir -p
sub mkpdir($)
{
  my $fuldir = shift;

  my ($dir,$dir1,$a);

  return 1 if -d $fuldir;

  $dir = $fuldir;
  $dir1 = '';
  while (length($dir) > 0) {
    $a = index($dir,'/');
    if ($a < 0) {
      $dir1 .= $dir;
      $dir = '';
    } elsif ($a == 0) {
      $dir1 = '/';
      $dir = substr($dir,$a + 1);
      next;
    } else {
      $dir1 .= substr($dir,0,$a);
      $dir = substr($dir,$a + 1);
    }
    unless (-d $dir1) {
      mkdir($dir1) or return error("cannot create dir1 '$dir1' for $fuldir: $!");
    }
    $dir1 .= '/';
  }
  return error("dir $fuldir does not exist: $!") unless -d $fuldir;
  return 1;
}

sub yymmdd2fmt($)
{
  my $x = shift;
  my $d = int($x % 100);
  $x /= 100;
  my $m = int($x % 100);
  $x /= 100;
  my $y = int($x);
#  return strftime('%a&nbsp;%e&nbsp;%b&nbsp;%Y',0, 0, 0, $d, $m - 1, $y - 1900);
  return strftime('%e&nbsp;%b&nbsp;%Y',0, 0, 0, $d, $m - 1, $y - 1900);
}

sub kmg($$)
{
  my ($x,$u) = @_;
  my $f;

  if ($x >= 1024 * 1024 * 1024 * 2) { $f = sprintf('%.2f G',$x / (1024 * 1024 * 1024)); }
  if ($x >= 1024 * 1024 * 2) { $f = sprintf('%.2f M',$x / (1024 * 1024)); }
  elsif ($x >= 1024 * 2) { $f = sprintf('%.2f K',$x / 1024); }
  else { $f = $; }
  return $f . $u;
}

sub str2reg($$)
{
  my ($str,$feed) = @_;

  my ($c,$r,$x) = split(',',$str);
  return error("unrecognised region $str") if defined $x;
  $r = 'n/a' unless defined $r and length $r;
  error_exit("unhandled country abbrev '$c' in $feed") if length($c) < 3;
  return ($c,$r);
}

sub readsum($$)
{
  my ($dir,$ext) = @_;
  my $sumdir = "$dir/$ext";
  my $sumname = $sumdir . '/summary.tab';
  my $agcname = $sumdir . '/agency.tab';

  my $header = '<th>country</th><th>Region</th>';
  $header .= '<th>feed</th>';
  $header .= '<th>repository</th>';
  $header .= '<th>agency</th>';
  $header .= '<th>#routes</th>';
  $header .= '<th>#stops</th>';
  $header .= '<th>coverage</th>';
  $header .= '<th>&emsp;validity&emsp;</th>';
  $header .= '<th>updated</th>';
  $header .= '<th>accessed</th>';
  $header .= '<th>size</th>';
  $header .= '<th>props</th>';

  my ($line,$c,$i,$feedno,$feedurl,$feedprop);
  my ($regstr,$country,$region,$name,$agen,$stops,$routes,$start,$end,$range,$fstart,$fend,$minlat,$maxlat,$minlon,$maxlon);
  my ($agid,$agname,$agtz,$agurl,$agregion);

  my (%xfeedlns,%xfeeds,%xfeedags,%xfeedagurls,@agnames,@agurls);
  my (%stoptab);
  my ($fln,$pfx,$indir,$infoname,$infofh,$zipname,$anyname,$fmtime,$fatime,$fsize);
  my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$filesize,$atime,$mtime);

  my ($sec,$min,$hour,$mday,$mon,$year);

  info("reading summary $sumname");
  open(my $sum,'<',$sumname) or return error("cannot open $sumname: $!");

  my @lines = readline($sum);
  return error("$sumname is empty") unless @lines > 1;
  close($sum);

  my $linno = 0;
  my $xfeedcnt = 0;

  # read summary
  foreach my $line (@lines) {
    $linno++;
    $line = trimws($line);
    next unless length($line);
    $c = substr($line,0,1);
    next if $c eq '#';
    next if index($line,'region') == 0;

    $fln = "$sumname.$linno: ";
    ($regstr,$name,$agen,$stops,$routes,$start,$end,$range,$minlat,$maxlat,$minlon,$maxlon) = split("\t",$line);
    info("$fln name $name  stops $stops");
    return error("$fln $name already defined on line $linno") if exists($xfeedlns{$name});
    return error("$fln $name incomplete line $line") unless defined $maxlon;
    $xfeedlns{$name} = $linno;

    $indir = $name . '/in';
    -d $indir or return error("$fln directory $indir not found for $name");

    $anyname = $indir . '/stop_times.txt';
    ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$filesize,$atime,$mtime) = stat $anyname;
    return error("cannot open $anyname: $!") unless defined $dev and length $dev;

    $infoname = $indir . '/info.txt';
    open($infofh,'<:encoding(UTF-8)',$infoname) or return error("cannot open $infoname: $!");
    $line = readline($infofh);
    return error("$infoname is empty") unless defined $line and length $line;
    close($infofh);
    $zipname = trimws($line);

    ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$filesize,$atime) = stat($indir .  '/' . $zipname);
    return error("cannot open $zipname: $!") unless defined $dev and length $dev;

    $fstart = yymmdd2fmt($start);
    $fend = yymmdd2fmt($end);
    $xfeeds{$name} = join("\t",$regstr,$agen,$stops,$routes,$minlat,$maxlat,$minlon,$maxlon,$fstart,$fend,$range,$zipname,$mtime,$atime,$filesize);
    $stoptab{$stops} = $name;
    $xfeedcnt++;
  }
  return error("no items in $sumname") unless $xfeedcnt > 0;

  info("$fln $xfeedcnt feeds");

  # sort on various keys
  my (@bystop,@byname);
  foreach $stops (sort {$a <=> $b} keys %stoptab) {
    $name = $stoptab{$stops};
    push @bystop,$name;
  }
  foreach $name (sort keys %xfeeds) {
    push @byname,$name;
  }

  open(my $agc,'<:encoding(UTF-8)',$agcname) or return error("cannot open $agcname: $!");

  @lines = readline($agc);
  return error("$agcname is empty") unless @lines > 1;
  close($agc);

  $linno = 0;
  my $itemcnt = 0;

  foreach $line (@lines) {
    $linno++;
    $line = trimws($line);
    next unless length($line);
    $c = substr($line,0,1);
    next if $c eq '#';
    next if index($line,'agency_id') == 0;
    $itemcnt++;

    $fln = "$agcname.$linno: ";
    ($agid,$agname,$agtz,$agurl,$agregion) = split("\t",$line);
    $a = rindex($agid,'/');
    return error("$fln no prefix for $agid") unless $a > 1;
    $pfx = substr($agid,0,$a);
    $agname = '' unless defined $agname and length $agname;
    $agurl = '' unless defined $agurl and length $agurl;
    $agurl = '' if $agurl eq 'http:///' or $agurl eq 'http://';
    # info("  id $agid name $agname $agurl feed $pfx");
    return error("$fln unknown feed $pfx for $agid $linno") unless exists($xfeedlns{$pfx});

    if (exists($xfeedags{$pfx})) {
      $xfeedags{$pfx} .= "\t" . $agname;
      $xfeedagurls{$pfx} .= "\t" . $agurl;
    } else {
      $xfeedags{$pfx} = $agname;
      $xfeedagurls{$pfx} = $agurl;
    }
  }
  return error("no items in $agcname") unless $itemcnt > 0;

  info("$fln $itemcnt agencies");

  # write html
  my $inhdr = 0;
  my ($ziplink,$tdclass);
  my $itemndx = 0;
  my $rowcnt = 0;
  my $htmlname = "$dir/feeds.html";
  my $bboxurl;
  info("writing $htmlname");
  open(my $html,'>:encoding(UTF-8)',$htmlname) or return error("cannot create $htmlname: $!");
  print($html "<html>\n <head>\n");
  print($html "  <meta charset='utf-8' />\n");
  print($html "  <title>feeds</title>\n");

  print($html "  <meta http-equiv=refresh content=60 />\n");

  print($html "<link rel=stylesheet href=feeds.css />");

  print($html " </head>\n <body>\n");

#  print($html "  <table border=1 cellpadding=5>\n<tr>\n");
#  print($html "  <div id=maintab>\n");

#  print($html '  <div id=colgroup>');

#  print($html '  <div id=country></div>');
#  print($html '  <div id=region></div>');
#  print($html '  <div id=feed></div>');
#  print($html '  <div id=repos></div>');
#  print($html '  <div id=routes></div>');
#  print($html '  <div id=stops></div>');
#  print($html '  <div id=coverage></div>');
#  print($html '  <div id=validity></div>');
#  print($html '  <div id=updated></div>');
#  print($html '  <div id=accessed></div>');
#  print($html '  <div id=size></div>');
#  print($html '  <div id=flags></div>');

#  print($html "  </div>\n");

  $itemndx = 0;

  while ($itemndx < $xfeedcnt) {

    print($html "  <div class=hline></div>\n");

    if ( ($inhdr == 0 && $xfeedcnt > 20 && $itemndx + 1 == $xfeedcnt) or ($rowcnt % 15) == 0) {
      print($html "<div class=hr>\n");
      $inhdr = 1;
      $country = 'country';
      $region = 'region';
      $name = 'feed';
      $feedurl = '';
      $zipname = 'repos';
      $ziplink = '';
      $routes = 'routes';
      $stops = 'stops';
      $fmtime = 'updated';
      $fatime = 'accessed';
      $fsize = 'size';
      $feedprop = 'props';
      $tdclass = ' th thdr';
    } else {
      print($html "<div class=tr>\n");
      $inhdr = 0;

      if ($itemndx & 1) {
        $tdclass = ' td';
      } else {
        $tdclass = ' td altrow';
      }

      $name = $byname[$itemndx];
      $itemndx++;

      ($regstr,$agen,$stops,$routes,$minlat,$maxlat,$minlon,$maxlon,$fstart,$fend,$range,$zipname,$mtime,$atime,$filesize) = split("\t",$xfeeds{$name});
      $ziplink = $zipname;

      ($sec,$min,$hour,$mday,$mon,$year) = gmtime $mtime;
      $fmtime = yymmdd2fmt(sprintf('%04u%02u%02u',$year+1900,$mon+1,$mday));

      ($sec,$min,$hour,$mday,$mon,$year) = gmtime $atime;
      $fatime = yymmdd2fmt(sprintf('%04u%02u%02u',$year+1900,$mon+1,$mday));

      $fsize = kmg($filesize,'B');

      info("$regstr $name  agc $agen  stops $stops  routes $routes $start $end");
      return error("unknown feed $name") unless exists($xfeedags{$name}) and exists($feedbyname{$name});
      $feedno = $feedbyname{$name};
      $feedurl = $urls[$feedno];
      $feedurl = '' unless defined $feedurl and length $feedurl;
      $feedprop = $feedprops[$feedno];

      return error("empty feedno") unless defined $feedno and length $feedno;

      unless (defined($feedurl) and length($feedurl)) {
        warning("empty feedurl for $name");
        $feedurl = '';
      }

      return error("empty feedurl") unless defined $feedurl and length $feedurl;
      $feedprop = ' ' unless defined $feedprop and length $feedprop;

      @agnames = ();
      @agurls = ();
      @agnames = split("\t",$xfeedags{$name});
      @agurls = split("\t",$xfeedagurls{$name});

      ($country,$region) = str2reg($regstr,$name);
    }

    return error("unrecognised country/region $regstr in $name") unless defined $country and length $country and defined $region;
    $rowcnt++;

    # country,region
    print($html "<div class='country$tdclass'>$country</div><div class='region$tdclass'>$region</div>");

#    info("$xfeedags{$name}");
#    info("$xfeedagurls{$name}");

    # agencies
    print($html "<div class='agency$tdclass'>");
    if ($inhdr != 0) {
      print($html 'agency')
    } else {
#      print($html "<div class=agtxt>");
      for ($i = 0; $i < @agnames; $i++) {
        print($html "<br>") unless $i == 0;
        $agname = $agnames[$i];
        $agurl = $agurls[$i];
        $agname = '' unless defined $agname and length $agname;
        $agurl = '' unless defined $agurl and length $agurl;
        info("  agency $agname  url $agurl");
        if (length($agurl)) { print($html '<a href="' . $agurl . '">' . $agname . '</a>'); }
        else { print($html "$agname"); }
      }
#      print($html '</div>');
    }
    print($html '</div>');

    # routes, stops
    print($html "<div class='routes$tdclass'>$routes</div><div class='td stops$tdclass'>$stops</div>");

    # feed
    print($html "<div class='feed$tdclass'>");
    if (length($feedurl)) {
      print($html '<a href="' . $feedurl . '">' . $name . '</a>');
    } else {
      print($html "$name");
    }
    print($html '</div>');

    # repos
    print($html "<div class='repos$tdclass'>");
    if (length($ziplink)) {
      print($html '<a href="' . $ziplink . '">' . $zipname . '</a>');
    } else {
      print($html "$zipname");
    }
    print($html '</div>');

    # coverage
    $bboxurl = 'http://www.openstreetmap.org/?';
    $bboxurl .= "minlon=$minlon&minlat=$minlat&maxlon=$maxlon&maxlat=$maxlat";

    print($html "<div class='coverage$tdclass'>");
    if ($inhdr != 0) {
      print($html 'coverage');
    } else {
      print($html "<div class=minlatlon>");
      print($html "<a class=link href='" . $bboxurl . "'>" . sprintf('%.4f',$minlat) . ',' . sprintf('%.4f',$minlon) . '</a>');
      print($html "</div>");
      print($html "<div class=maxlatlon>");
      print($html "<a class=link href='" . $bboxurl . "'>" . sprintf('%.4f',$maxlat) . ',' . sprintf('%.4f',$maxlon) . '</a>');
      print($html "</div>");
    }
    print($html "</div>");

    # validity
    print($html "<div class='validity$tdclass'>");
    if ($inhdr != 0) {
      print($html 'validity');
    } else {
      print($html "<div class=validfrom>$fstart</div>");
      print($html "<div class=validcnt>|</div>");
      print($html "<div class=validto>$fend</div>");
      # print($html "<div class=validlen>$range days</div>");
    }
    print($html "</div>");

    # updated
    print($html "<div class='updated$tdclass'>$fmtime</div>");

    # accessed
    print($html "<div class='accessed$tdclass'>$fatime</div>");

    # size
    print($html "<div class='size$tdclass'>$fsize</div>");

    #props
    print($html "<div class='flags$tdclass'>$feedprop</div>");

    # end row
    print($html "</div>\n");

#    last if $itemcnt == 4;
  }

  print($html "  <div class=hline></div>\n");

#  print($html "</div>\n");

  print($html "\n </body>\n</html>");
  close $html;
  return info("wrote $itemndx items to $htmlname");
}

sub script($$)
{
  my ($name,$url) = @_;

  my $script = 'mkfeed.sh';

  return error("$name/$script not found") unless -f "$name/$script";

  run($name,$script,$url,1,0) or return 0;
}

sub get($$)
{
  my ($name,$url) = @_;

  my ($bckname,$user,$pwd,$xurl,$args,$dir1,$a);
  my $havezip = 0;

  my $indir = $name . '/in';

  my $stampname = 'wget.stamp';

  mkpdir($indir) or return 0;

  my ($dh,$zipname);
  opendir($dh,$indir) or return error("cannot access $indir: $!");
  my @names = readdir($dh);
  closedir($dh);

# check if refresh needed
  foreach my $name (@names) {
    next if substr($name,0,1) eq ".";
    $havezip = 1 if lc(substr($name,-4)) eq '.zip';
  }

  if (-f $indir . '/' . $stampname) {
    open(my $stampfh,'<',"$indir/$stampname") or return error("cannot open $indir/$stampname: $!");
    my $stamp = readline($stampfh);
    return error("cannot read $indir/$stampname: $!") unless defined $stamp and length $stamp;
    $lostamp = $stamp if $stamp < $lostamp;
    $histamp = $stamp if $stamp > $histamp;

    return info("skip $indir on last got $stamp after $getafter") if $havezip == 1 and $stamp > $getafter;
    info("get $indir on last got $stamp before $getafter") if $havezip == 1 and $stamp < $getafter;
  } elsif ($havezip) {
    info("get $indir on no stamp");
  }

  foreach my $name (@names) {
    next if substr($name,0,1) eq ".";
    next unless lc(substr($name,-4)) eq '.zip';
    $bckname = $indir . '/' . $name . '.bak';
    unless ($dryrun) {
      unlink($bckname) if -f $bckname;
      rename($indir . '/' . $name,$bckname) or return 0;
      rename($indir . '/' . $stampname,$indir . '/' . $stampname . 'bak');
   }
  }

  ($user,$pwd,$xurl) = ($url =~ qr'^user=([-A-Za-z0-9.@/]+) pwd=([-A-Za-z0-9.@/]+) ([-_A-Za-z0-9.:/]+)');

  vrb("url '$url'");

  if (defined($user)) {
    $args = join("\t",'--backups=0','--no-use-server-timestamps','--no-check-certificate','--user=' . $user,'--password=' . $pwd,$xurl);
  } else {
    $args = join("\t",'--backups=0','--no-use-server-timestamps','--no-check-certificate',$url);
  }
  info("get feed $name");
  run($indir,'wget',$args,0,0) or return 0;

  my $now = time();
  my ($sec,$min,$hour,$mday,$mon,$year) = gmtime($now);
  $stampname = "$indir/wget.stamp";
  open(my $stampfd,'>',"$stampname") or return error("cannot create $stampname");
  my $stamp = sprintf("%04u%02u%02u",$year + 1900,$mon + 1,$mday);
  print($stampfd $stamp);
  close $stampfd;

  $lostamp = $stamp if $stamp < $lostamp;
  $histamp = $stamp if $stamp > $histamp;
  return 1;
}

sub chkupd($$)
{
  my ($name,$url) = @_;

  my $cmd = "wget -S --method=HEAD '$url' 2>wget.stderr";

  my $rv = system($cmd);
  error("cannot run $cmd:$!") if $rv == -1;

  if ($rv & 127) {
    my $sig = $rv & 127;
    return error("$cmd received signal $sig");
  }
  my $rc = ($rv >> 8);
  return error("$cmd returned $rc") if $rc;

  open(my $fd,'<','wget.stderr') or return error('cannot open wget.stderr');
  my @lines = readline($fd);
  close $fd;
  return error("could not run $cmd") unless @lines > 0;

  my ($line,$mtime,$pos);
  for $line (@lines) {
    $line = trimws($line);
    $pos = index($line ,'Last-Modified:');
    next if $pos < 0;
    $mtime = substr($line,$pos + 14);
    info(sprintf("%-18s %s",$name,$mtime));
    last;
  }
  info("no mtime for $name") unless defined $mtime;
  return 1;
}

sub patchfile($$)
{
  my ($section,$indir) = @_;

  my ($c,$i,$line,$fline,$match,$pat,$rep,$ln1,$ln2);

  my $modname = $indir . '/' . $section . '.patch';
  my $feedname = $indir . '/' . $section . '.txt';
  return 1 unless -f $modname;

  info("patching $section in $indir");
  open(my $updfh,'<:encoding(UTF-8)',$modname) or error_exit("cannot open $modname: $!");

  my @modlines = readline($updfh);
  close $updfh;
  return 1 unless @modlines > 0;

  open(my $feedfh,'<:encoding(UTF-8)',$feedname) or error_exit("cannot open $feedname: $!");
  my @feedlines = readline($feedfh);
  close $feedfh;
  return 1 unless @feedlines > 0;
  my $linecnt = scalar(@feedlines);
  my $change = 0;

  foreach my $line (@modlines) {
    next unless length($line);
    $c = chop $line;
    $line .= $c if $c ne "\n";
    next unless length($line);
    $c = substr($line,0,1);
    next if $c eq '#';
    ($match,$pat,$rep) = split("\t",$line);
    $rep = '' unless defined $rep;
    next unless defined $pat;
    for $i (0 .. $linecnt-1) {
      $fline = $feedlines[$i];
      next if index($fline,$match) < 0;
      next if index($fline,$pat) < 0;
      $fline =~ s/$pat/$rep/;
      if ($fline ne $feedlines[$i]) {
        $ln1 = trimws($feedlines[$i]);
        $ln2 = trimws($fline);
        info("< $ln1");
        info("> $ln2");
        info("");
        $feedlines[$i] = $fline;
        $change++;
      }
    }
  }
  return 1 if $change == 0;

  info("$change lines patched");
  my $nfeedname = $indir . '/' . $section . '.txt.new';

  open($feedfh,'>:encoding(UTF-8)',$nfeedname) or error_exit("cannot create $nfeedname: $!");
  for $fline (@feedlines) {
    print($feedfh $fline);
  }
  close $feedfh;
  rename($feedname,$feedname . '.0') or error_exit("cannot rename $nfeedname: $!");
  rename($nfeedname,$feedname) or error_exit("cannot rename $nfeedname: $!");
  return 1;
}

sub patch($)
{
  my $name = shift;

  my $indir = $name . '/in';

  for my $section (@feedfiles) {
    patchfile($section,$indir) or return 0;
  }
  return 1;
}

sub unzip($$$)
{
  my ($feed,$url,$state1) = @_;

  my $indir = $feed . '/in';

  my @txtnames = ('agency.txt','calendar.txt','calendar_dates.txt','routes.txt','stop_times.txt','stops.txt','trips.txt');

  unless (-d $indir) {
    mkpdir($indir) or return 0;
    return error("no archives in $indir dryrun $dryrun");
  }

  my ($dh,$updfh,$feedfh,$zipname,$extpos,$qpos,$path,$himtime,$hiname,$name);
  my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksize,$blocks);

  # take newest non-feed file as zip
  opendir($dh,$indir) or return error("cannot access $indir: $!");
  my @names = readdir($dh);
  closedir($dh);
  $himtime = 0;
  foreach $name (@names) {
    next if substr($name,0,1) eq ".";
    $path = $indir . '/' . $name;
    stat $path || error_exit("cannot access $path: $!");
    ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksize,$blocks) = stat _;
    if ($size > 10 and $mtime > $himtime and $name ne 'gtfsprep-0.log' and $name ne 'wget.stamp') { $himtime = $mtime; $hiname = $name; }

    $extpos = index($name,'.zip');
    $qpos = index($name,'?');
    if ($extpos > 0 and $qpos > $extpos) {
      rename($indir . '/' . $name,$indir . '/' . substr($name,0,$qpos)) or error_exit("cannot rename $name:$!");
      return error("multiple archives $name and $zipname") if defined $zipname;
      $zipname = substr($name,0,$qpos);
      last;
    }

    next unless lc(substr($name,-4)) eq '.zip';
    info("found $name");
    return error("multiple archives $name and $zipname") if defined $zipname;
    $zipname = $name;
  }
  if ($dryrun) {
    $zipname = "dryrun.zip" unless defined $zipname;
  } elsif (defined $hiname and not defined $zipname) {
    $zipname = 'gtfs.zip';
    run($indir,"cp","-p\t$hiname\t$zipname",0,0) or return 0;
  }
  return error("no archives in $indir dryrun $dryrun") unless defined $zipname;

  my $infoname = $indir . '/info.txt';
  open(my $infofh,'>:encoding(UTF-8)',$infoname) or error_exit("cannot create $infoname: $!");
  print($infofh "$zipname");
  close $infofh;

  my $opts = '-jo';

  if (-f $indir . '/routes.txt') {
    ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime) = stat($indir . '/routes.txt');
    $opts .= 'u' if $do_patch < 1 and $mtime > 1451570400;
    vrb("timestamp $mtime");
    warning("timestamp at or below 1980") unless $mtime > 315532800;
  }

  unlink($indir . 'calendar.txt');
  unlink($indir . 'calendar_dates.txt');
  unlink($indir . 'transfers.txt');
#  my $arglst = join("\t",'-u','-jo',$zipname,'-x','shapes.txt');

  #my $arglst = join("\t",$opts,$zipname,'*.txt','-x','shapes.txt');
  my $arglst = join("\t",$opts,$zipname,'feed_info.txt');
  foreach my $feedfile (@feedfiles) {
    $arglst .= "\t" . $feedfile . '.txt';
  }

#  info("$arglst");

  run($indir,'unzip',$arglst,0,11) or return 0;

  return 1 if $dryrun;

  # check for nested zip with 1 member
  my $zipcnt = 0;
  my $nestedname = '';
  opendir($dh,$indir) or return error("cannot access $indir: $!");
  @names = readdir($dh);
  closedir($dh);
  foreach $name (@names) {
    next if substr($name,0,1) eq ".";

    next if $name eq $zipname;
    next unless length($name) > 4 and lc(substr($name,-4)) eq '.zip';
    $nestedname = $name;
    $zipcnt++;
  }

  $path = $indir . '/' . $zipname;
  my $bckpath = $path . '.bak';

  if ($zipcnt == 1) {

    $zipname = $nestedname;
    $arglst = join("\t",'-jo',$zipname,'-x','shapes.txt');

    run($indir,'unzip',$arglst,0,0) or return 0;

    unlink($bckpath) if -f $bckpath;
    rename($path,$bckpath) or return 0;
  }

  $path = $indir . '/' . $zipname;
  $bckpath = $path . '.bak';

#  if (index($url,'manual') != 0) {
#    unlink($bckpath) if -f $bckpath;
#    rename($path,$bckpath) or return 0;
#  }

  my $agname = $indir . '/agency.txt';
  return error("$agname not found in archive") unless -f $agname or $state1 eq 'u';

  return 1 if $do_patch < 0;

  patch($feed) or return 0;

  return 1;
}

sub prep($$$)
{
  my ($name,$prepopt,$region) = @_;

  if ($do_patch == 1) {
    patch($name) or return 0;
  }

  my $stamp = '';
  my $stampname = "$name/in/wget.stamp";
  if (-f $stampname) {
    open(my $fd,'<',$stampname) or error_exit("cannot open $stampname: $!");
    $stamp = readline($fd);
    close $fd;
    $lostamp = $stamp if $stamp < $lostamp;
    $histamp = $stamp if $stamp > $histamp;
  }

  my $opts = trimws($gprepopt);
  my $popt = trimws($prepopt);
  $opts =~ tr/ /\t/s;
  $popt =~ tr/ /\t/s;
  if (length($popt)) {
    $opts .= "\t" if length($opts);
    $opts .= $popt;
  }
  if (length($mergedir)) {
    $opts .= "\t" if length $opts;
    $opts .= '-mergedir=' . $mergedir;
    $opts .= "\t-mergefirst" if $mergefirst;
    $mergefirst = 0;
  }
  if (length($stamp)) {
    $opts .= "\t" if length $opts;
    $opts .= '-stamp=' . $stamp;
  }
  my $arglst;

  if ($docheck) {
    $arglst = join("\t",'-m=' . $distlimit,'-stoptimes=0','-stopseqs=1','-pfx=' . $name,'-startdate=' . $startdate,'-enddate=' . $enddate,$opts,$name . '/in');
    run('.','./gtfsprep',$arglst,0,0) or return 0;

    $arglst = join("\t",'import',$name,$name . '/in');
    run('.','./gtfstool',$arglst,1,0) or return 0;

    $arglst = join("\t",'-stopat=8','run',$name);
    run('.','./tripover',$arglst,0,0) or return 0;
  }

  $arglst = join("\t",'-m=0','-stoptimes=1','-stopseqs=0','-pfx=' . $name,'-region=' . $region,'-startdate=' . $startdate,'-enddate=' . $enddate,$opts,$name . '/in');

  run('.','./gtfsprep',$arglst,1,0) or return 0;
  return 1 unless $docheck;

  return 1;
}

sub air($$$$)
{
  my ($name,$prepopt,$url,$region) = @_;

  my $opts = trimws($prepopt);
  $opts =~ tr/ /\t/s;

  my $namein = $name . '/in';

  my ($mode,$startdate_air,$enddate_air) = ($url =~ '^([a-z]+) ([0-9]+) ([0-9]+)$');

  $mode = $url unless defined $mode and length $mode;
  return error("unknown mode in $url") unless defined $mode and length $mode;

  info("url $url");

  $startdate_air = $startdate unless defined $startdate_air and length $startdate_air;
  $enddate_air = $enddate unless defined $enddate_air and length $enddate_air;

  my $arglst = join("\t",'air2gtfs',$opts,$mode,$namein,$namein,$startdate_air,$enddate_air);

  run('.','gtfstool',$arglst,0,0) or return 0;

  my $gopts = trimws($gprepopt);
  $gopts =~ tr/ /\t/s;
  $opts = $gopts;
  if (length($mergedir)) {
    $opts .= "\t" if length $opts;
    $opts .= '-mergedir=' . $mergedir;
    $opts .= "\t-mergefirst" if $mergefirst;
    $mergefirst = 0;
  }
  $arglst = join("\t",'-canonin','-m=0','-stoptimes=1','-stopseqs=0','-pfx=' . $name,'-region=' . $region,'-startdate=' . $startdate,'-enddate=' . $enddate,$opts,$name,$name . '/in');

  run('.','gtfsprep',$arglst,1,0) or return 0;
  return 1 unless $docheck;

  $arglst = join("\t",'-t','import',$name,$name . '/in');
  run('.','gtfstool',$arglst,0,0) or return 0;

  return 1;
}

sub manual($$$$)
{
  my ($name,$prepopt,$mode,$region) = @_;

  my $opts = trimws($prepopt);
  $opts =~ tr/ /\t/s;

  my $namein = $name . '/in';

  my $arglst = join("\t",'tt2gtfs',$opts,$mode,$namein,$namein,$startdate,$enddate);

  run('.','gtfstool',$arglst,0,0) or return 0;

  my $gopts = trimws($gprepopt);
  $gopts =~ tr/ /\t/s;
  $opts = $gopts;
  if (length($mergedir)) {
    $opts .= "\t" if length $opts;
    $opts .= '-mergedir=' . $mergedir;
    $opts .= "\t-mergefirst" if $mergefirst;
    $mergefirst = 0;
  }
  $arglst = join("\t",'-canonin','-m=0','-stoptimes=1','-stopseqs=0','-nopfx','-region=' . $region,'-startdate=' . $startdate,'-enddate=' . $enddate,$opts,$name,$name . '/in');

  run('.','gtfsprep',$arglst,1,0) or return 0;
  return 1 unless $docheck;

  $arglst = join("\t",'-t','import',$name,$name . '/in');
  run('.','gtfstool',$arglst,0,0) or return 0;

  return 1;
}

sub prepfeed($)
{
  my $feed = shift;

  my $state0 = $state0s[$feed];
  my $state1 = $state1s[$feed];
  my $name = $names[$feed];
  my $prepopt = $prepopts[$feed];
  my $url = $urls[$feed];
  my $region = $regions[$feed];

  vrb("$name $state0 $state1");

  return 1 if $lostate eq 'g' and $state0 ne 'g';

  if ($state0 eq 's' and $state1 ne 'x') {
    return 0 unless script($name,$url);
  }

  if ($state0 eq 'g' and $state1 ne 'x') {
    if ($do_updcheck) {
      return chkupd($name,$url);
    } else {
      return 0 unless get($name,$url);
    }
    $state0 = 'u';
  }

  if ($state0 eq 'u' and $state1 ne 'x' and $state1 ne 'g') {
    return 0 unless unzip($name,$url,$state1);
    $state0 = 'p';
  }

  if ($state0 eq 'p' and ($state1 eq 'p' or $state1 eq 'm' or $state1 eq 'i')) {
    return 0 unless prep($name,$prepopt,$region);
    $state0 = 'm';
  }

  if ($state0 eq 'a' and $state1 ne 'x' and $state1 ne 'u' and $state1 ne 'p') {
    return 0 unless air($name,$prepopt,$url,$region);
    $state0 = 'm';
  }
  if ($state0 eq 'n' and $state1 ne 'x' and $state1 ne 'u' and $state1 ne 'p') {
    return 0 unless manual($name,$prepopt,$url,$region);
    $state0 = 'm';
  }

  $state0s[$feed] = $state0;
}

# run steps according to config
# per feed all steps in order
sub prepfeeds()
{
  my $now = time();
  my ($sec,$min,$hour,$mday,$mon,$year) = gmtime($now);
  $lostamp = sprintf("%04u%02u%02u",$year + 1900,$mon + 1,$mday);

  for my $feed (@feednos) {
    my $name = $names[$feed];
    open(my $fh,'>','lastfeed') or return error("cannot create lastfeed:$!");
    print $fh $name;
    close $fh;
    prepfeed($feed) or return serror("feed $name line $names{$name} not processed");
  }
  return 1 unless $do_xinfo;
  readsum($feeds,'/in') or return error("cannot read summary in $feeds");
  return 1;
}

sub merge()
{
  my $feedlst = '';
  my $mfeedcnt = 0;

  for my $feed (@feednos) {
    next unless $state1s[$feed] eq 'm';
    next unless $state0s[$feed] eq 'm';
    $mfeedcnt++;
    $feedlst .= "\t" if length($feedlst);
    $feedlst .= $names[$feed] . '/in';
  }
  info("$mfeedcnt feeds mergable");
  return 0 unless length $feedlst;
  info("expect $feedlst");

  return 1;
}

# run prep after merge
sub mergeprep()
{
  my $opts = trimws($gprepopt2);
  $opts =~ tr/ /\t/s;

  mkpdir($feeds) or return 0;

  my $arglst = join("\t",'-canonin','-m=' . $distlimit,'-stamp=' . $histamp,'-lostamp=' . $lostamp,$opts,$feeds,$feeds . '/in');

  run('.','gtfsprep',$arglst,1,0) or return 0;

  return 1;
}

# gtfstool import
sub import()
{
  my $arglst = 'import' . "\t" . $feeds . "\t" . $feeds;

  run('.','gtfstool',$arglst,0,0) or return 0;
  return 1;
}

# main

sub showhelp()
{
  info("usage: mkfeed.pl [options]\n");
  info("-n\tdryrun: do not act");
  info("-c\tcheck: add checks after each stage");
  info("-p\tpatch: patch input");
  info("-u\tupdate check instead of regular get\n");
  info("-np\tno patch: skip patching input");
  info("histate=[gupm]\tstart at this stage");
  info("lostate=[gupm]\tstop after this stage");
  info("start=<feed>\tstart at this feed");
  info("stop=<feed>\tstop at this feed");
  info("only=<feed>\tadd only this feed");
  info("after=yyyymmdd\tget only if last got before date");
  info("set=[a-z]>\tinclude feeds for this set");
  info("start=<feed>\tstart at this feed");
  info("merges=<dir>\tgenerate merged feeds in this dir");
  info("feedcfg=<file>\tuse this feed config\n");

  info("feed config:\n");
  info(".startdate\t20160101");
  info(".enddate\t20160101");
  info("#set\tdir\tregion\tstart\tend\topts\turl");
  info("u	us/or/port	US,OR	g	m	0	http://developer.trimet.org/schedule/gtfs.zip\n");

  info("stages:");
  info("g\tget from url");
  info("u\tunpack / unzip");
  info("p\tpreprocess");
  info("m\tmerge");
  info("s\trun mkfeed.sh script in feed dir, passing url as arg");
}

foreach my $arg (@ARGV) {
  my $opt = $arg;
  if ($opt eq '-?' or $opt eq '-h') { showhelp(); exit 1; }
  if ($opt eq '-m') { $stopat='m'; }
  elsif ($opt eq '-2') { $stopat='2'; }
  elsif ($opt eq '-i') { $stopat='i'; }
  elsif ($opt eq '-z') { $dozip=1; }
  elsif ($opt eq '-n') { $dryrun=1; }
  elsif ($opt eq '-c') { $docheck=1; }
  elsif ($opt eq '-C') { $stopat='c'; }
  elsif ($opt eq '-p') { $do_patch=1; }
  elsif ($opt eq '-u') { $do_updcheck=1; }
  elsif ($opt eq '-x') { $do_xinfo=1; }
  elsif ($opt eq '-cfg') { $stopatcfg=1; }
  elsif ($opt eq '-np') { $do_patch=-1; }
  elsif ($opt eq '-tf') { $showtf=-1; }
  elsif (index($opt,'start=') == 0) { $mergefirst = 0; $startat = substr($opt,6); }
  elsif (index($opt,'stop=') == 0) { $stopat1 = substr($opt,5); }
  elsif (index($opt,'only=') == 0) { $mergefirst = 0; $startat = substr($opt,5); $stopat1 = $startat; $stopat = 'm'; }
  elsif (index($opt,'histate=') == 0) { $histate = substr($opt,8); }
  elsif (index($opt,'lostate=') == 0) { $lostate = substr($opt,8); }
  elsif (index($opt,'after=') == 0) { $getafter = substr($opt,6); }
  elsif (index($opt,'set=') == 0) { $feedset = substr($opt,4); }
  elsif (index($opt,'merges=') == 0) { $feeds = substr($opt,7); }
  elsif (index($opt,'cfg=') == 0) { $feedcfg = substr($opt,4); }
  elsif (index($opt,'feedlst=') == 0) { $feedlst = substr($opt,8); }
  else { warning("unknown option '$opt': use -h for help"); exit 1; }
}

$stopat = 'm' if length $startat and length $stopat1 and $stopat eq 'x';

readcfg($feedcfg) or exit 1;

exit 0 if $stopat eq 'c';

if ($do_updcheck) {
  $histate = 'g';
  $lostate = 'g';
}

$mergedir = $feeds . '/in';
$mergedir = '' if $stopat eq 'm';

unless (-d $feeds) { mkpdir($feeds) or exit 1; }

if (length($mergedir)) {
  mkpdir($mergedir) or exit 1;
  if ($mergefirst and not $dryrun) {
    if (-f "$mergedir/calendar.tab") { unlink("$mergedir/calendar.tab"); info("delete $mergedir/calendar.tab"); }
    if (-f "$mergedir/frequencies.tab") { unlink("$mergedir/frequencies.tab"); info("delete $mergedir/frequencies.tab"); }
    if (-f "$mergedir/calendar_dates.tab") { unlink("$mergedir/calendar_dates.tab"); info("delete $mergedir/calendar_dates.tab"); }
  }
}

prepfeeds() or exit 1;

exit 0 if $stopat eq 'm';

merge() or exit 1;

exit 0 if $stopat eq '2';

mergeprep() or exit 1;

exit 0 if $stopat eq 'i';

import() or exit 1;

exit 0 unless $dozip;

my $arglst = "-zcf\t$feeds.tar.gz\t";
$arglst .= join("\t","$feeds/ports.txt","$feeds/hops.txt","$feeds/times.txt","$feeds/to_routes.txt","$feeds/to-agencies.txt");
run('.','tar',$arglst,0,0);

exit 0;
