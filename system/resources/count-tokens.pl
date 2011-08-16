#!/usr/bin/perl
#
# Public domain. Initially written by Michal Moskal.
#
# Counts number of tokens in source file.
# By default lines are treated as ghost code (annotations).
# Add "// R" (with no quotes) at the end of the line to treat it as real code.
# Add "// A" the have the line ignored by the script.
#
# Please check with http://vacid.codeplex.com/SourceControl/list/changesets
# for the latest version of this script.
#
# Revision history:
# 
# July 21, 2010    Initial revision
# January 5, 2011  Fix bug in keyword detection
#                  allow identifiers to start with \
#                  (by Mark Hillebrand).
#

$verbose = 0;

if ($ARGV[0] eq "-v") {
  $verbose = 1;
  shift;
}

$toks{"A"} = 0;
$toks{"G"} = 0;
$toks{"R"} = 0;

while (<>) {
  s/\r//;
  s/\n//;

  $kind = "G";
  /\/\/\s*([RA])\s*$/ and $kind = $1;

  # don't treat JML style specs as comments
  s/\/\/\s*\@//;
  s/\/\*\s*\@//;
  # remove single-line comments
  s/\/\/.*//;
  # remove one-line /* */ comments
  s/\/\*.*?\*\///g;

  # remove multi-line comments
  if (s/\/\*.*//) {
    $l = $_;
    while (<>) {
      if (s/^.*?\*\///) {
        $l .= " $_";
	last;
      }
    }
    $_ = $l;
  }

  while (1) {
    s/^\s*//;
    if (s/^(\\?[0-9a-zA-Z_]+)//) {
      $toks{$kind}++;
    } elsif (s/^([!@#\$%\^&*:<>\/?~`|+=-]+)//) {
      $toks{$kind}++;
    } elsif (s/^(.)//) {
      $toks{$kind}++;
    } else {
      last;
    }
    print " $1" if $verbose;
  }
  print "\n" if $verbose;
}

$r = $toks{"R"}; 
$g = $toks{"G"}; 

if ($r > 0) {
  printf "%d real tokens, %d ghost tokens, ratio: %.2f, %.3f points (+%d aux tokens)\n", 
    $r, $g, $g/$r, 6 - 2 * log ($g/$r), $toks{"A"};
} else {
  print "$g tokens\n";
}

