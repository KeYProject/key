#!/usr/bin/perl -w
#
# This script can be used to generate plots on the runtimes of KeY
# examples.
# 
# As arguments it expects one or more statistics files generated by
# runAllProofs.pl (using command line option -p).
#
# This script creates some .svg files in the current directory. It
# expects the gnuplot tool to be installed.
#
# written by Mattias Ulbrich
# (modified by Christoph Scheben)

use strict;
use Getopt::Long;

# Command line options
my %option = ();
GetOptions(\%option, 'help|h', 'verbose|v', 'silent|s', 'nologscale|n', 'fullproblemnames|f','withLables|l');

if ($option{'help'}) {
  print "Use '-h' or '--help' to get this text (very necessary this line).\n";
  print "Use '-v' or '--verbose' to increase verbosity.\n";
  print "Use '-s' or '--silent' to reduce verbosity (only final results are displayed).\n";
  print "Use '-n' or '--nologscale' to set the y axis to normal scale (default is log scale).\n";
  print "Use '-f' or '--fullproblemnames' to display the full problem names including the path to the examples.\n";
  print "Use '-l' or '--withLables' to display the hight of the bars over the bars of the diagram.\n";
  exit;
}

# the arguments
my @filenames = @ARGV;

die "There were no file arguments" unless(@filenames);

# use this string as a prefix to the generated image files; later to
# be definable in a commandline option
my $prefix = "";

# List the names for columns in the statistics files.
# These are read from the first line of the first file.
my @columns = &extractColumnNames;

# Reads the column names from the first line of the first file.
sub extractColumnNames {
    # read first line
    open IN, $filenames[0] or die "cannot open ".$filenames[0];
    my $line = <IN>;
    close IN;
    # remove "\n"
    chomp $line;
    # split at delimiter
    my @columns = split(/\s*\|\s*/, $line);
    # remove first entry because it is the example name column
    shift @columns;
    
    return @columns;
}

# make a unique key from a set of strings.
# we assume that '%' does not occurr in the strings.
sub makeKey {
    return join("%", @_);
}

# extract the problem name from a descriptin which may contain path
# and extension
sub extractProblemName {
    $a = $_[0];
    if($a =~ m#(?:^|/)([^/\.]*)\.[^/]+$#) {
	# print $1 . " " . $a ."\n";
	return $1;
    } else {
	print "Warning: cannot extract short name from '$a'\n" unless ($option{'silent'});;
	return $a;
    }
}

# the collection of all found proof names
my %problemnames = ();

# the data table
my %data = ();

foreach my $filename (@filenames) {
    open IN, $filename or die "cannot open $filename";
    <IN>;  # skip over first line
    while(<IN>) {
	# remove "\n"
	chomp;
	# ignore line if it is a comment or if it is empty
	next if /^#/ or ($_ eq "");
	my @elems = split /\s*\|\s*/, $_;
	my $problem = shift @elems;
	$problemnames{$problem} = 1;
	my $colNo = 0;
	while (my $entry = shift @elems) {
	    $data{&makeKey($filename, $problem, $colNo)} = $entry;
	    # print &makeKey($filename, $problem, $colNo) . " -> " . $entry . "\n";
	    $colNo ++;
	}
    }
    close IN;
}

#foreach my $k (keys %data) {
#    print "$k -> ". $data{$k} ."\n";
#}

foreach (@filenames) {
    print "Checking $_\n" unless ($option{'silent'});
}

my $colNo = 0;
my $width = 150 + ((values %data) * (2 + 0.1*@filenames));
my $hight = 1000;
foreach my $col (@columns) {
    open GP, "| gnuplot" or die "cannot launch gnuplot";
    print GP "set title 'Plot for $col'\n";
    print GP "set style data histogram\n";
    print GP "set style histogram gap 1\n";
    print GP "set style fill solid border -1\n";
    print GP "set xtic rotate by -45\n";
    print GP "set out '$prefix$col.svg'\n";
    print GP "set logscale y\n" unless ($option{'nologscale'});
    print GP "set yrange [0.1:]\n" unless ($option{'nologscale'});
    print GP "set yrange [0:]\n" if ($option{'nologscale'});
    print GP "set terminal svg size $width,$hight\n";

    print GP "plot";
    my $first = 1;
    foreach my $filename (@filenames) {
	if($first) {
	    $first = 0;
	} else {
	    print GP ",";
	}
	print GP " '-' using 2:xtic(1)" ;
	print GP ", '-' using 0:2:3 with labels" if ($option{'withLables'});
	print GP " title '$filename'" ;
    }
    print GP "\n";
    
    foreach my $filename (@filenames) {
	foreach my $problem (sort (keys %problemnames)) {
	    my $prettyproblem = &extractProblemName($problem);	    
	    my $key = &makeKey($filename, $problem, $colNo);
	    my $data = "0";
	    if(exists $data{$key}) {
		$data = $data{$key};
	    }
	    if ($option{'fullproblemnames'}) {
		print GP "\"$problem\" $data\n";
		print "added \"$problem\" $data (file $filename)\n" if ($option{'verbose'});
	    } else {
		print GP "\"$prettyproblem\" $data\n";
		print "added \"$prettyproblem\" $data (file $filename)\n" if ($option{'verbose'});
	    }
	}
	print GP "e\n";
	if ($option{'withLables'}) {
	    foreach my $problem (sort (keys %problemnames)) {
		my $prettyproblem = &extractProblemName($problem);	    
		my $key = &makeKey($filename, $problem, $colNo);
		my $data = "0";
		if(exists $data{$key}) {
		    $data = $data{$key};
		}
		my $ypos;
		if (not $option{'nologscale'}) {
		    $ypos = 1.5 * $data;
		} else {
		    $ypos = 2 + $data;
		}
		print GP "\"$problem\" $ypos $data\n";
	    }
	    print GP "e\n";
	}
    }
    close GP;
    $colNo ++;
}
