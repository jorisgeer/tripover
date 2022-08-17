#!/usr/bin/perl -W

# emka - build tool with emphasis on self-configuring

# This file is part of Tripover, a broad-search journey planner.

#  Copyright (C) 2014-2017 Joris van der Geer.

#  This work is licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International License.
#  To view a copy of this license, visit http://creativecommons.org/licenses/by-nc-nd/4.0/

#  Project home is at https://github.com/joriswu/tripover

# author: Joris van der Geer

# last changed:  27 Feb 2017

# derive most build instructions and dependencies from the project sources.
# It does require some conventions and project organisation style.
# Currently only c is supported.
#
# The only minimal config is in a file 'config', specifying compile and link settings
#
# Header dependencies are obtained by scanning for includes.
# Targets are obtained by checking for sources defining a 'main' function.
#
# Compile and link steps use a single set of options for each file.
# List of dependant objects derives from this convention:
#
#   'main_app.c' includes headers 'time.h', 'net.h, 'base.h.
#   'time.c' and 'net.c' do exist.  -> link main_app with time.o and net.o
#
# This is taken to imply main_app uses functions exported in
# those two files, thus main_app is linked with net.o and time.o
#
# Generated sources are recognised with a per-source configuration:
#
# 'generated.c' has a corresponding 'generate.c.generate' file showing the commandline and dependencies.
#
# emka works over an entire project tree, visiting each file in turn.
# compiland sources are bundled in one action.
#
# Target up-to-date-ness is based on timestamps, update is done in forward steps :
#
# 1 update generated sources ( run )
# 2 update objects ( compile )
# 3 update executables ( link )
#
# Optionally this is done in a loop.
#

# limitations:
# - no indirect dependencies yet
# - content hashes excluding comments is a better indicator than timestamp
# - executables used to generate sources are not updated automatically

use 5.012;
use integer;
use strict;

use POSIX ();
use POSIX qw(tmpnam);

use Fcntl ':mode';

my $progname = 'emka';
my $verstr = '1.0';

my $norecurse = 1;

sub cmd_help() {
  print("Usage: $progname [options] [command] [dir]\n");
  print("Options:\n");
  print("-h, -help, -?       Show help and quit\n");
  print("-n, -dryrun         No action mode\n");
  print("-s, -static         Add static analysis pass\n");
  print("-u, -unconditional  Unconditional build\n");
  print("-x, -nolink         Skip linking step\n");
  print("-v, -verbose        Verbose mode\n");
  print("-V, -version        Show version and quit\n\n");
  print("Commands:\n");
  print("clean               Delete intermediates\n");
  print("config, setup       Configure\n");
  print("loop                Continuous build\n");
  print("build               Build ( default)\n");
}

local $SIG{__WARN__} = sub { print $_[0]; exit 1;  };

my $cfgname = 'config';

my %config;
my %cfglines;

# defaults for config. Only items in this list are read from config
my %defconfig = (
  compiler => 'clang',
    cdef => '',
    cinc => '',
    copt => '-O',
    cdiag => '-Weverything',
    csyn => '-w -fsyntax-only',
    cfmt => '',
    cdbg => '',
    cextra => '',
    cdia => '',
    cana => '',
    csan => '',

# standard .c.o rule
  _c_o => '%compiler -c -o %.o %copt %cdiag %cextra %.c',

# initial syntax-check only for .c
  _c_ => '%compiler -fsyntax_only -w %.c',

  _c_s => '',

  linker => 'clang',
    lopt => '-O',
    ldiag => '-Weverything',
    ldbg => '',
    lextra => '',
    lana => '',
    lsan => '',

# standard .o.x rule
  _o_x => '%linker -o %.x %lopt %ldiag %lextra %.o',

  ignoredir => 'data doc queries',
  ignoresrc => ''
);

my @filelist;
my %files;
my %ifconds;

# file namings:
# sfile = source
# ofile = obj  typical compile s into o
# xfile = app binary
# afile = main app obj. has depobjs

my (@ignoredirs,@ignoresrcs);

my ($static_ana,$do_clean);

my ($starttime,$itertime);

my $newlimit = 0;

my $prjroot = '.';

my $endtime = 600;
my $configtime = 0;

my $verbose = 0;
my $unconditional = 0;
my $dryrun = 0;
my $do_sca = 0;
my $loop = 0;
my $nolink = 0;
my $showcmd = 0;

my $logfh;

sub init() {
  return 1;
}

sub vrb($) { print($_[0],"\n") if $verbose; return 1; }
sub info($) { print($_[0],"\n"); return 1; }
sub warning($) { print("warning: ",$_[0],"\n"); return 1; }
sub error($) { print("error: ",$_[0],"\n"); sleep 1; return 0; }

sub error_exit($) { print ($_[0],"\n"); exit 1; }

sub substitute($$$$) {
  my ($val,$arg,$from,$to) = @_;

  $arg = substr $arg,1;
  return substr($val,0,$from) . $config{$arg} . substr($val,$to) if exists $config{$arg};

#  info("empty substution for '$arg'");
  return substr($val,0,$from) . substr($val,$to);
}

sub unquote($) {
  my ($s) = @_;

  if ( (substr($s,0,1) eq "'" and substr($s,-1,1) eq "'") or (substr($s,0,1) eq '"' and substr($s,-1,1) eq '"') ) {
    chop $s;
    return substr($s,1);
  }
  return $s;
}

sub trimws($) {
  my ($s) = @_;
  $s =~ s/[ \t\n]+/ /g;
  $s =~ s/^ //;
  $s =~ s/ $//;
  return $s;
}

sub which($) {
  my ($name) = @_;

  my $path = $ENV{PATH};
  foreach my $dir (split(':',$path)) {
    if (-x $dir . '/' . $name) {
      info("$name is in $dir");
      return 1;
    }
  }
  return 0;
}

sub inarray($@) {
  my ($a,@arr) = @_;

  foreach my $b (@arr) { return 1 if $a eq $b; }
  return 0;
}

sub cmd_config($) {
  my ($cfgname) = @_;

  my $varcnt = 0;
  my ($fh,$line,$cfg,$tpl,$tplname,$name);
  my $linno = 0;
  my ($var,$val,$varline,$cclist,$ldlist,$cc,$ccdef,$ld,$lddef);
  my @ccs;
  my @lds;

  $tplname = $cfgname . '.in';
  vrb("reading config template in '$tplname'");
  open($tpl,"<",$tplname) || error_exit("cannot open $tplname: $!");

  my $pat = qr?^\s*\[\s*([a-z_]+)\s*=\s*(.+)\s*\]?;  # var = value
  while($line = readline $tpl) {
    $linno++;
    next if index($line,'##') == 0;
    ($var,$val) = ($line =~ $pat);
    next unless defined $var and length $var;
    $val = '' unless defined $val;
    $val =~ tr/\t/ /;
    $val = unquote(trimws($val));
    next if $val eq 'all';
    if ($var eq 'compiler') {
      push (@ccs,$val)  if (not inarray($val,@ccs)) and (not inarray($val,@lds)) and which($val);
    } elsif ($var eq 'linker') {
      push (@lds,$val) if (not inarray($val,@lds)) and (not inarray($val,@ccs)) and which($val);
    }
  }
  $cclist = join(',',@ccs);
  $ldlist = join(',',@lds);

  info('compilers in $PATH: ' . $cclist);
  $cclist = join("\n",@ccs);

  if (hasname($cclist,'clang')) { $ccdef = 'clang'; }
  elsif (hasname($cclist,'gcc')) { $ccdef = 'gcc'; }
  else { $ccdef = 'cc'; }

  print ("compiler [$ccdef] ? ");

  $cc = <STDIN>;
  $cc = $ccdef unless defined $cc;
  $cc = trimws($cc);
  $cc = $ccdef if length($cc) < 1;
  info("cc '$cc'");
  if (which($cc)) { $ccdef = $cc; }
  else { info("note: '$cc' is not in PATH"); }

  print ("linker [$ccdef] ? ");

  $ld = <STDIN>;
  $ld = $ccdef unless defined $ld;
  $ld = trimws($ld);
  $ld = $ccdef if length($ld) < 1;
  info("'$ld' is not in PATH") unless which($ld);

  my ($ccdir,$ccname) = splitpath($cc);
  my ($lddir,$ldname) = splitpath($ld);

  seek($tpl,0,0);

  my $ccpart = '';
  my $ldpart = '';
  my $now = time2yyyymmdd(time(),'min');
  open($cfg,">",$cfgname) or error_exit("cannot open $cfgname: $!");
  print($cfg "# config - emka config file\n\n");
  print($cfg "# generated from '$tplname' by '$progname' at $now utc\n\n");
  $linno = 0;
  while($line = readline $tpl) {
    $linno++;
    next if index($line,'##') == 0;

    if (substr($line,0,1) eq '#') {
      print($cfg $line);
      next;
    } elsif (substr($line,0,1) eq "\n") {
      print($cfg $line);
      next;
    }
    ($var,$val) = ($line =~ $pat);
    if (defined $val and $var eq 'compiler') {
      $ccpart = trimws($val);
      $ldpart='';
      print($cfg "compiler = $cc\n") if $ccpart eq $ccname;
    } elsif (defined $val and $var eq 'linker') {
      $ldpart = trimws($val);
      $ccpart='';
      print($cfg "linker = $ld\n") if $ldpart eq $ldname;
    } elsif ($ccpart eq $ccname or $ccpart eq 'all') {
      print($cfg "$line");
    } elsif ($ldpart eq $ldname or $ldpart eq 'all') {
      print($cfg "$line");
    }
  }
  close $cfg;
  close $tpl;
  info("wrote $cfgname - you may tailor it to your needs");
}

sub readconfig($) {
  my ($name) = @_;

  my $varcnt = 0;
  my ($fh,$line);
  my $linno = 0;
  my ($var,$op,$val,$varline,$cmtpos,$ifcond);
  my $skip = 0;

  my $varisval = qr/^([a-z_.]+)\s*(\+?=)\s*(.*)/;  # var [+]= value
  my $ifline = qr'^@if ([-a-zA-Z_.]+)';  # @if ident
  vrb("reading config in '$name'");
  open($fh,"<",$name) || error_exit("cannot open $name: $!\nconsider running 'emka config'");

  while($line = readline $fh) {
    $linno++;
    if ($skip) { $skip = 0; next; }
    $line = trimws($line);
    $cmtpos = index($line,'#');
    next if $cmtpos == 0;
    $line = substr($line,0,$cmtpos) if $cmtpos > 0 and index($line,'##') != $cmtpos;
    next if length($line) < 1;

    ($ifcond) = ($line =~ $ifline);
    if (defined $ifcond and length $ifcond) {
      $skip = (not exists $ifconds{$ifcond});
      next;
    }
    ($var,$op,$val) = ($line =~ $varisval);
    if (defined $var and defined $op) {
      $var =~ tr/./_/;
      $val = '' unless defined $val;
      $val =~ tr/\t/ /;

      $val = trimws($val);

      if ($op eq '=') {
        if (exists $defconfig{$var}) {
          if (exists $config{$var}) {
            $varline = $cfglines{$var};
            info("$name.$linno skip duplicate '$var = $val' at line $varline");
          } else {
            $config{$var} = $val;
            $cfglines{$var} = $linno;
          }
          $varcnt++;
        } else {
          warning("$name.$linno skip unknown '$var = $val'");
        }
      } elsif ($op eq '+=') {

        if (exists $defconfig{$var}) {
          if (exists $config{$var}) {
            $config{$var} .= ' ' . $val;
          } else {
            warning("$name.$linno skip undefined '$var' for $op");
          }
        } else {
          warning("$name.$linno skip unknown '$var $op $val'");
        }

      } else { warning("$name.$linno unknown op '$op'"); }
    } else { warning("$name.$linno skip unknown '$line'"); }
  }

  vrb("read config in '$name': $varcnt variables");
  foreach $var (keys %defconfig) {
    if (not exists $config{$var}) {
      $config{$var} = $defconfig{$var};
    }
  }

  foreach $var (keys %config) {
    $val = $config{$var};
    my $limit = 0;
    while ($limit < 256 and $val =~ /(%[a-z]+)/) {
      $limit++;
      $val = substitute($val,$1,$-[1],$+[1]);
    }
    vrb("'$var' = '$val'");
    $config{$var} = $val;
  }
  if (exists($config{ignoredir})) {
    @ignoredirs = split(' ',$config{ignoredir});
  }
  if (exists($config{ignoresrc})) {
    @ignoresrcs = split(' ',$config{ignoresrc});
  }
  return $varcnt;
}

sub hasname($$) {
  my ($list,$name) = @_;
  my $elem;

  return 0 if length($list) == 0;
  foreach $elem (split("\n",$list)) {
    return 1 if ($elem eq $name);
  }
  return 0;
}

sub max($$) {
  my ($a,$b) = @_;
  return ($a > $b ? $a : $b);
}

sub time2yyyymmdd($$) {
  my ($nixsec,$res) = @_;

  my ($fmt,$sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst);

  ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = gmtime($nixsec);
  return sprintf('%04u-%02u-%02u %02u:%02u:%02u',($year + 1900,$mon + 1,$mday,$hour,$min,$sec)) if $res eq 'sec';
  return sprintf('%04u-%02u-%02u %02u:%02u',($year + 1900,$mon + 1,$mday,$hour,$min)) if $res eq 'min';
  return sprintf('%04u-%02u-%02u %02u:%02u',($year + 1900,$mon + 1,$mday));
}

sub splitpath($) {
  my ($path) = @_;

  my $pos = rindex $path, '/';
  return ('',$path) if $pos < 0;
  return (substr($path,0,$pos),substr($path,$pos+1));
}

sub run($$$$$) {
  my ($dir,$cmd,$argstr,$show,$okname) = @_;

  my ($rv,$orgdir);
  my @args = ($cmd, split ' ',$argstr);

  if (open(my $logfd,'>>:encoding(UTF-8)','emka.log')) {
    print($logfd "$cmd $argstr\n");
    close($logfd);
  } else {
    warning("cannot write to emka.log:$!");
  }

  if ($dir ne $ENV{PWD} and $dir ne '.') {
    $orgdir = $ENV{PWD};
    info("cd $dir && $show");
    chdir($dir) unless $dryrun;
  } elsif ($loop == 0) { info("$show"); }
  info("\n'$cmd' '$argstr'\n") if $showcmd;
  vrb("'$cmd' '$argstr'");
  $rv = system(@args) unless $dryrun;
  if (defined $orgdir) {
    info("cd $orgdir");
    chdir($orgdir) unless $dryrun;
  }

  return 1 if $dryrun;

  if ($rv == -1) {
    error_exit("failed to run $cmd: $!");
  }
  elsif ($rv & 127) {
    my $sig = $rv & 127;
    error_exit("$cmd received signal $sig");
  }
  my $rc = ($rv >> 8);
  if ($rc) {
    if ($loop) {
      return 0;
    } else {
      error_exit("$cmd returned $rc");
    }
  }
  info("$okname OK") if $loop and length $okname;
  return 1;
}

# read file.x.generate. store src, dst, cmd and hashes in .generate info
sub readgen($$$) {
  my ($dir,$gname,$ginfo) = @_;

  my ($gpath,$genre,$optre,$fh,$line,$linno,$fln,$dstname,$srcname,$binname,$mark);
  my ($cmd,$args,$srcpath,$sinfo);

  $gpath = mkpath($dir,$gname);
  $mark = '#';

  if (not open($fh,"<",$gpath)) {
    warning("cannot open $gpath");
    return ('','','');
  }
  $linno = 0;

          # generate 'bits.h' from 'bitdefs.h' with 'genpack -X .in .out'
          # input is optional
  $genre = qr?^\s*generate\s+([A-Za-z0-9_./\'\" ]+)\s+from\s+([A-Za-z0-9_./\'\" ]+)\s+with\s+(.+)?;
  $optre = qr?^\s*mark\s+(.+)\s*?;
  while($line = readline $fh) {
    $linno++;
    last if $linno > 1000;
    $fln = $gpath . ':' . $linno . ' ';
    if (defined $cmd) {
      warning("$fln ignoring duplicate generate line") if ($line =~ qr?^\s*generate\s+?);
    } elsif ($line =~ $genre) {
      $dstname = unquote($1);
      $srcname = unquote($2);
      $cmd = unquote(trimws($3));
      vrb("generate $dstname from $srcname with $cmd");
    } elsif ($line =~ $optre) {
      $mark = unquote($1);
    }
  }
  close $fh;
  if (not defined $cmd) {
    info(">  generate 'gen.h' from 'gen.h.in' with 'genhdr .in .out'");
    warning("no 'generate' line like above in $gname");
    return ();
  }

  $ginfo->{cmd} = $cmd;

  $ginfo->{srcname} = $srcname;
  if (length($srcname)) {
    $srcpath = mkpath($dir,$srcname);
    if (exists $files{$srcpath}) {
      $sinfo = $files{$srcpath};
      $sinfo->{gendst} = $dstname;
      $sinfo->{role} = 'gensrc';
    } else { warning("$gname: $srcpath not found"); }
  }
  my $pos = index($cmd,' ');
  if ($pos > 0) {
    $binname = substr($cmd,0,$pos);
    $args = substr($cmd,$pos);
  } else {
    $binname = $cmd;
    $args = '';
  }
  vrb("generate $dstname from $srcname with $binname $args");
  $args =~ s?%\.in?$srcname?g;
  $args =~ s?%\.out?$dstname?g;

  vrb("generate $dstname from $srcname with $binname $args");

  return ($dstname,$srcname,$binname,$args);
}

sub filetype($) {
  my ($name) = @_;

  return ('cfg',$name) if $name eq $cfgname;
  my $dotpos = rindex $name,'.';
  return ('x',$name) if $dotpos < 0;

  my $ext = substr($name,$dotpos + 1);
  my $base = substr($name,0,$dotpos);
  return ('c',$base) if $ext eq 'c';
  return ('h',$base) if $ext eq 'h';
  return ('o',$base) if $ext eq 'o';
  return ('gen',$base) if $ext eq 'generate';
  return ('in',$base) if $ext eq 'in';
  return ('x',$base) if $ext eq 'pl';
  vrb "unknown type for '$name' '$ext'";
  return ('unknown',$base);
}

sub basename($) {
  my ($name) = @_;

  my $dot = rindex $name,'.';
  return ('x',$name) if $dot < 0;
  substr($name,0,$dot);
}

sub read_dir_recurse($) {

  return read_dir($_[0]);
}

sub read_dir($) {
  my ($dir) = @_;

  my ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksize,$blocks);
  my ($path,$type,$gtype,$base,$gbase,$basedir,$dh);

  my $pos = rindex($dir,'/');
  if ($pos >= 0) {
    $basedir = substr($dir, $pos+1);
  } else { $basedir = $dir; }

  vrb("read dir $dir");
  opendir($dh,$dir) || error_exit("cannot access $dir: $!");
  my @names = readdir($dh);
  foreach my $name (@names) {
    next if substr($name,0,1) eq ".";
    $path = $dir . "/" . $name;
    stat $path || error_exit("cannot access $path: $!");
    ($dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,$atime,$mtime,$ctime,$blksize,$blocks) = stat _;

    if (S_ISDIR($mode)) {
      if ($norecurse or inarray($name,@ignoredirs)) { next; }
      info("recurse into $name");
      return 0 unless read_dir_recurse($path);
      next;
    }
    if (S_ISREG($mode)) {
      next if inarray($name,@ignoresrcs);

      my $info = {};
      $info = $files{$path} if exists $files{$path};

      ($type,$base) = filetype($name);

      vrb("add $name in $basedir");

      if ($type eq "o") {
        $info->{role} = 'obj';
        $files{$path} = $info;
      } elsif ($type eq "x") {
        $info->{role} = 'exe';
      } elsif ($type eq "c") {
        $info->{obj} = $base . '.o';
        $info->{role} = 'src';
      } elsif ($type eq "h") {
        $info->{role} = 'inc';
      } elsif ($type eq "in") {
        $info->{role} = 'in';
      } elsif ($type eq "gen") {
        ($gtype,$gbase) = filetype($base);
        $info->{gendst} = $base;
        $info->{type} = $gtype;
        $info->{role} = 'gen';
      } elsif ($type eq "cfg") {
        $configtime = $mtime;
        next;
      } else {
        vrb("skip unknown $name");
        next;
      }
      if ($size == 0) {
        info("skip empty $path");
        next;
      }

      vrb("add $name in $dir $mtime $itertime");
      warning("$name is in the future") if $mtime > $itertime;
      if ($itertime - $mtime < $newlimit) {
        info("skip $mtime within $newlimit of $itertime");
        sleep 1; return 0;
      }

      $files{$path} = $info;

      $info->{name} = $name;
      $info->{dir} = $dir;
      $info->{type} = $type;
      $info->{size} = $size;
      $info->{mtime} = $mtime;
      $info->{mode} = $mode;
      $info->{isapp} = 0;
      $info->{srcs} = '';

      $info->{gensrc} = '' if not exists $info->{gensrc};
      $info->{isgen} = 0 if not exists $info->{isgen};

      push (@filelist, $info) if ($type ne "unknown");
    }
  }
  closedir $dh;
  return 1;
}

sub timebyname($$) {
  my ($dir,$name) = @_;

  my $path;
  $path = mkpath($dir,$name);
  return 0 unless exists $files{$path};
  return $files{$path}->{mtime};
}

sub cmd_static() {

  my ($path,$info,$dir,$name,$type,$out,$binname,$args,$line);
  my @out;

  my $perlunused = qr?\s+i[0-9]+$?;

  $itertime = time();
  read_dir($prjroot) or return 0;

  foreach $path (sort keys %files) {
    $info = $files{$path};
    $type = $info->{type};
    $dir = $info->{dir};
    $name = $info->{name};
    if ($type eq 'pl') {
      $binname = 'perl';
      $args = '-W -MO=Xref ' . $name;
      info("run $binname $args");
      @out = qx?$binname $args?;
      foreach $line (@out) { info($line) if $line =~ $perlunused; }
    } elsif ($type eq 'c') {
      info("TODO - run static analysis for $name");
    } else { vrb("no static analysis for $name"); }
  }
  return 0;
}

sub gen() {

  my ($gpath,$ginfo,$dir,$gname,$dtime,$btime,$stime);

  foreach $gpath (sort keys %files) {
    $ginfo = $files{$gpath};
    next unless $ginfo->{role} eq 'gen';
    vrb("generate $gpath");
    $dir = $ginfo->{dir};
    $gname = $ginfo->{name};

    my ($dstname,$srcname,$binname,$genline) = readgen($dir,$gname,$ginfo);
    next unless length($binname);

    $dtime = timebyname($dir,$dstname);
    $btime = timebyname($dir,$binname);
    $stime = timebyname($dir,$srcname);
    vrb("btime $btime dtime $dtime  stime $stime");
    next unless $stime > $dtime or $btime > $dtime;

    run($dir,$binname,$genline,$binname . ' ' . $genline,'');
    return 0;
  }
  return 1;
}

sub src2obj($) {
  my ($mode) = @_;

  my ($dir,$name,$path,$opath,$info,$oinfo,$fh,$gen,$fresh,$retval);
  my ($cmd,$arg,$pos,$line,$incname,$htime,$now);

  my $inc_dq = qr'^\s*#\s*include\s+\"([a-z0-9_/.]+)\"';
  my $inc_last = qr'^\s*#\s*undef\s*hdrstop';

# compile if needed
  my $srclist = '';
  foreach $path (sort keys %files) {
    $info = $files{$path};
    next unless $info->{role} eq 'src';

    $dir = $info->{dir};
    $name = $info->{name};
    $gen = length($info->{gensrc});
    next if ($mode eq 'nogen' and $gen);

# determine includees and directives
    my $skip = 0;
    my $hitime = $info->{mtime};
    open($fh,'<',$path) or error_exit("cannot open $path: $!");
    while ($line = readline($fh)) {
      last if $line =~ $inc_last;
      if (index($line,"-*- emka: skip -*-") == 0) {
        $skip = 1;
        last;
      }
      if ($line =~ $inc_dq) {
        $incname = $1;
        $htime = timebyname($dir,$incname);
        vrb("$name inc $dir / $incname $htime " . time2yyyymmdd($htime,'sec'));
        $hitime = max($hitime,$htime);
      }
    }
    close $fh;

    $hitime = max($hitime,$configtime);
    next if $skip;

    $opath = mkpath($dir,$info->{obj});
    if (exists $files{$opath}) {
      $oinfo = $files{$opath};

      $fresh = $oinfo->{mtime} >= $hitime;
      vrb("$opath $oinfo->{mtime} hi $hitime");
    } else { vrb("no $opath"); $fresh = 0; }

    $fresh = 0 if $unconditional;
    $srclist .= ' ' . $name unless $fresh;
    vrb("srclist $srclist");
  }

  return 1 unless length $srclist;
  $unconditional = 0;
  $now = time();

  $cmd = $config{compiler};

  my $dianame = '';
  my ($diafh,$dialine);

  # first pass syntax only
  $arg = $config{_c_};
  if (length($arg) > 1 and not $dryrun) {
    $pos = index($arg, $cmd);
    $arg = substr($arg, length($cmd)) if $pos == 0;
    if (index($arg,'%.dia') >= 0) {
      $dianame = tmpnam();
      $arg =~ s?%.dia?$dianame?;
    }
    $arg =~ s?%.now?$now?;
    $arg =~ s?%\.c?$srclist?g;
    $retval = run($dir,$cmd,$arg,$cmd . ' syntax  ' . $srclist,'');
    if (length($dianame) and -f $dianame and -s $dianame and -r $dianame and open($diafh,'<',$dianame)) {
      while ($dialine = readline($diafh)) {
        print(' xxx ' . $dialine) unless index($dialine,'note: ') > 0;
      }
      close($diafh);
    }
    return 0 unless $retval;
  }

  $arg = $config{_c_o};
  $pos = index($arg, $cmd);
  $arg = substr($arg, length($cmd)) if $pos == 0;
  if (index($arg,'%.dia') >= 0) {
    $dianame = tmpnam();
    $arg =~ s?%.dia?$dianame?;
    open($diafh,'>',$dianame);
    close($diafh);
  }
  $arg =~ s?%.now?$now?;
  vrb("arg $arg now %now");
  $arg =~ s?%\.c?$srclist?g;

  return 0 unless run($dir,$cmd,$arg,$cmd . ' compile ' . $srclist,'');
  return 0 unless $do_sca;

  $arg = $config{_c_s};
  return 0 unless length($arg);
  $pos = index($arg, $cmd);
  $arg = substr($arg, length($cmd)) if $pos == 0;
  $arg =~ s?%.now?$now?;
  $arg =~ s?%\.c?$srclist?g;

  return 0 unless run($dir,$cmd,$arg,$cmd . ' static ' . $srclist,'');
  return 0;
}

sub obj2exe($) {
  my ($mode) = @_;

  my ($dir,$odir,$oname,$o2name,$spath,$opath,$info,$objlist,$gen,$fresh);
  my ($cmd,$arg,$pos,$fh,$line,$incname,$o2path,$xpath,$xname,$xtime);

  my $hasmain1 = qr'int\s+main\s*\(\s*int\s+argc\s*,\s*char\s*\*\s*argv\s*\[\s*\]';
  my $hasmain2 = qr'int\s+main\s*\(\s*int\s+argc\s*,\s*char\s*\*\s*\*\s*argv';
  my $inc_dq = qr'^\s*#\s*include\s+\"([a-z0-9_/.]+)\"';

  my $library = qr'^//\s*-l\s+([-a-zA-Z0-9_/.]+)';

# determine apps
  foreach $spath (sort keys %files) {
    $info = $files{$spath};
    next unless $info->{role} eq 'src';

    $dir = $info->{dir};
    $gen = length($info->{gensrc});
    next if ($mode eq 'nogen' and $gen);

# determine app and objs to link
    $opath = mkpath($dir,$info->{obj});
    ($odir,$oname) = splitpath($opath);
    my $ismain = 0;
    my $hitime = timebyname($dir,$oname);
    my $objlist = $opath;
    my $libs = '';
    open($fh,'<',$spath) or error_exit("cannot open $spath: $!");
    while ($line = readline($fh)) {
      $ismain = 1 if $line =~ $hasmain1 or $line =~ $hasmain2;
      if ($line =~ $library) {
        info("add lib $1");
        $libs .= $1 . ' ';
      }

      if ($line =~ $inc_dq) {
        $incname = $1;
        vrb("$spath inc $incname");
        $o2name = basename($incname) . '.o';
        $o2path = mkpath($dir,$o2name);
        if (exists $files{$o2path} and $o2path ne $opath) {
          $o2path = substr($o2path,2) if substr($o2path,0,2) eq './';
          $objlist .= ' ' . $o2path;
          $hitime = max($hitime,timebyname($dir,$o2name));
        } else { vrb("no $o2path"); }
      }
    }
    close $fh;
    $info->{isapp} = $ismain;
    next unless $ismain;
    vrb("main $spath hitime $hitime");
    $hitime = max($hitime,$configtime);

    $xname = basename($oname);
    $xpath = mkpath($dir,$xname);
    if (exists $files{$xpath}) {
      $xtime = timebyname($dir,$xname);
      vrb("main $spath $xtime hitime $hitime");
      $fresh = ($xtime >= $hitime);
    } else { info("no $xpath"); $fresh = 0; }

    $fresh = 0 if $unconditional;
    next if $fresh;

    $cmd = $config{linker};
    $arg = $config{_o_x};
    $pos = index($arg, $cmd);
    $arg = substr($arg, length($cmd)) if $pos == 0;
    $arg =~ s?%\.o?$objlist?;
    $arg .= ' ' . $libs if length $libs;
    $arg =~ s?%\.x?$xpath?;

    return 0 unless run($dir,$cmd,$arg,$cmd . $xpath . ' <- ' . $objlist,$xname);
  }
}

sub mkpath($$) { $_[0] . '/' . $_[1]; }

sub cmd_version() {
  print("$progname version $verstr\n");
}

sub cmd_clean() {
  my ($path,$info);

  $itertime = time();
  read_dir($prjroot) or return 0;

  foreach $path (sort keys %files) {
    $info = $files{$path};
    next unless $info->{role} eq 'obj';
    next unless -f $path;
    unlink($path);
  }
}

# continuous build
sub cmd_loop() {
  $starttime = $itertime = time();
  $loop = 1;

  while ($itertime < $starttime + $endtime) {
    sleep 1;
    $itertime = time();

    read_dir($prjroot) or redo;

    vrb('g ');
    gen() or redo;

    vrb('c ');
    src2obj('nogen') or next;

    vrb('l ');
    obj2exe('nogen') unless $nolink;
#    sleep 2;
  }
}

# standard build: make tagets up to date
sub cmd_build() {
  my $changed = 1;

  while ($changed) {
    $itertime = time();
    read_dir($prjroot) or redo;
    gen() or redo;
    src2obj('nogen') or redo;

    obj2exe('nogen') unless $nolink;
    $changed = 0;
  }
}

# main

my ($arg,$opt,$retval);

foreach $arg (@ARGV) {
  next if substr($arg,0,1) ne '-';
  $opt = $arg;
  $opt =~ s/^-+//;
  if ($opt eq 'h' or $opt eq '?' or $opt eq 'help') {
    cmd_help(); exit 0;
  }
}

my $cmd = 'build';

foreach $arg (@ARGV) {
  if (substr($arg,0,1) eq '-') {
    $opt = $arg;
    $opt =~ s/^-+//;
    if ($opt eq 'v') { info('verbose'); $verbose = 1; }
    elsif ($opt eq 'n') { info('dryrun'); $dryrun = 1; }
    elsif ($opt eq 's') { info('+static'); $do_sca = 1; }
    elsif ($opt eq 'x') { info('nolink'); $nolink = 1; }
    elsif ($opt eq 'u') { info('unconditional build'); $unconditional = 1; }
    elsif (index($opt,'t') == 0) { $endtime = int(substr($opt,2)); }
    elsif (index($opt,'d=') == 0) { $ifconds{substr($opt,2)} = 1; }
    else { info("ignoring unknown option -$opt"); }
  } else {
    if ($arg eq 'static') { $cmd = 'static'; }
    elsif ($arg eq 'clean') { $cmd = 'clean'; }
    elsif ($arg eq 'loop') { $cmd = 'loop'; }
    elsif ($arg eq 'config') { $cmd = 'config'; }
    elsif ($arg eq 'build' or $arg eq 'all') { $cmd = 'build'; }
    elsif (-d $arg) { $prjroot = $arg; }
    else { error_exit("$arg is not a directory or known command"); }
  }
}

init() or exit 1;

if ($cmd eq 'config') {
  cmd_config($cfgname) or exit 1;
  exit 0;
}

readconfig("config") or exit 1;

if ($cmd eq 'loop') { cmd_loop(); }
elsif ($cmd eq 'build') { cmd_build(); }
elsif ($cmd eq 'static') { cmd_static(); }
elsif ($cmd eq 'clean') { cmd_clean(); }
exit 0;
