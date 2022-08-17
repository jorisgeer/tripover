#!/usr/bin/perl -W

# genbits.pl - generate bit field defines from regular declarations

# This file is part of Tripover, a broad-search journey planner.

#  Copyright (C) 2014 Joris van der Geer.

#  This work is licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International License.
#  To view a copy of this license, visit http://creativecommons.org/licenses/by-nc-nd/4.0/

# bit fields allow more compact data store, yet some compilers produce less efficient code
# when both memory and cpu use counts, macros can be used to access fields using shifts and masks
# this tool reads a regular bitfield declaration and generates such macros
# example :
#
# struct tt_flight {
#  int dayofweek:7;
#  int hhmm_1440:11;  // departure time in minutes utc per 24h
#  int dur_1440:11;   // duration  in minutes max 24h
#  int t0_365:9;      // t0 days relative to plan t0
#  int t1_365:9;      // t1 days relative to t0
# };
#
# the embedded digit holds the maximum value needed
# the resulting type is sized to fit the fields
#
# output:
#
#  # define tt_flight_dayofweek_(x)     ((x) & 0x7f)
#  # define pack_tt_flight_dayofweek(x) (x)
#  # define tt_flight_hhmm_(x)          (((x) >> 7) & 0x7ff)
#  # define pack_tt_flight_hhmm(x)      ((tt_flightpack)(x) << 7)
#  typedef ub8 tt_flight; // 58 bits

use 5.008;
use integer;
use strict;

my $verbose = 0;

sub vrb($)     { print("$_[0]\n") if $verbose; return 1; }
sub info($)    { print("$_[0]\n"); return 1; }
sub warning($) { print("warning: $_[0]\n"); return 1; }
sub error($)   { print("error: $_[0]\n"); return 0; }

sub error_exit($) { print ("error: $_[0]\n"); exit 1; }

sub filetime2yyyymmddhhmm($) {
  my ($nixsec) = @_;

  my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst);

  ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = gmtime($nixsec);
  return sprintf('%04u-%02u-%02u %02u:%02u',($year + 1900,$mon + 1,$mday,$hour,$min));
}

# main

error_exit("usage: genbits in out") unless (@ARGV > 1);

my ($in,$out,$infh,$outfh,$line,$linno,$fieldpos,$fieldname,$fieldbits,$fieldmax,$packname);
my ($fln);

$in  = $ARGV[0];
$out = $ARGV[1];

open($infh, "<",$in)  or error_exit("cannot open $in: $!");
open($outfh,">",$out) or error_exit("cannot open $out: $!");

printf($outfh "// %s - bit field defines\n\n", $out);
printf($outfh "// generated from %s by %s at %s utc\n\n", $in, 'genbits.pl', filetime2yyyymmddhhmm(($^T)));

# int deptime_1440:12;
my $fullfield = qr?^\s*([a-z ]+) ([a-zA-Z0-9_]+)_([0-9]+)\s*:\s*([0-9]+)\s*;?;

# int hhmm:12;
my $halffield = qr?^\s*([a-z ]+) ([a-zA-Z0-9_]+)\s*:\s*([0-9]+)\s*;?;

$linno = 0;
while($line = readline $infh) {
  $linno++;
  next unless length($line);
  next if index($line,'//') == 0;
  next if index($line,"\n") == 0;

  $fln = $in . ':' . $linno . ': ';
  vrb("$line");

  $fieldbits = 0;
  if ($line =~ /struct\s+([a-zA-Z_]+)\s+{/) {
    $packname = $1;
    $fieldpos = 0;
  } elsif ($line =~ $fullfield) {
    $fieldname = $2;
    $fieldmax = $3;
    $fieldbits = $4;
    if ((1 << $fieldbits) < $fieldmax) {
      close $outfh;
      unlink $out;
      error_exit("$fln $packname.$fieldname overflows $fieldmax");
    }
    warning("$fln $packname.$fieldname oversizes $fieldmax") if (1 << ($fieldbits-1)) > $fieldmax;
  } elsif ($line =~ $halffield) {
    $fieldname = $2;
    $fieldmax = 0;
    $fieldbits = $3;
  } elsif (index($line,'};') == 0) {
    printf($outfh "typedef %s %s; // %u bits\n\n", $fieldpos > 32 ? 'ub8' : 'ub4', $packname,$fieldpos);
  } else { warning("$fln skipping unknown $line"); }

  if ($fieldbits) {
# TODO   printf('#define %s_%s_mask 0x%x\n',$packname,$fieldname,(1 << $fieldbits) - 1);
    if ($fieldpos == 0) {
      printf($outfh "#define %s_%s_(x) ((x) & 0x%x)\n",$packname,$fieldname,(1 << $fieldbits) - 1);
      printf($outfh "#define pack_%s_%s(x) (x)\n",$packname,$fieldname);
    } else {
      printf($outfh "#define %s_%s_(x) (((x) >> %u) & 0x%x)\n",$packname,$fieldname,$fieldpos,(1 << $fieldbits) - 1);
      printf($outfh "#define pack_%s_%s(x) ((%spack)(x) << %u)\n",$packname,$fieldname,$packname,$fieldpos);
    }
    $fieldpos += $fieldbits; 
  }
}
close $infh;
close $outfh;
