#! /usr/bin/perl

use strict;
use Getopt::Long;

# see http://www.somacon.com/p114.php
sub trim($) {
    my $string = shift;
    chomp $string;
    $string =~ s/^\s+//;
    $string =~ s/\s+$//;
    return $string;
}

my $targetDir = ".";
my $projectName = "";

GetOptions ('directory|d=s' => \$targetDir,
	    'project|p=s' => \$projectName);

my @sum;
my @columnNames;
my $countExamples = 0;
while (<>) {
    chomp;
    my @line = split /\s*\|\s*/, &trim($_);
    # remove the name of the example (can not be summed up)
    shift(@line);
print $_."\n";
    if ($. == 1) {
	# first line with column names
	@columnNames = @line;
    } elsif (not /^--- SUM ---/) {
	# skip comments
	next if /^#/ or ($_ eq "");
	# check and count line
	die "wrong number of fields in line $." 
	    unless scalar(@line) == scalar(@columnNames);
	$countExamples ++;
    } else {
	# the line with the summas
	die "wrong number of fields in line $." 
	    unless scalar(@line) == scalar(@columnNames);
	@sum = @line;
    }
}

# generate files for the columns
foreach (@columnNames) {
    print "creating $targetDir/$_.sum.properties\n";
    open (OUT, ">", "$targetDir/$_.sum.properties") or die $!;
    print OUT "YVALUE=" . shift(@sum) . "\n";
    print OUT "URL=http://abu.se.informatik.tu-darmstadt.de:8080/hudson/userContent/$projectName\n";
    close OUT;
}

# and finally for the total number of examples
print "creating $targetDir/count.sum.properties\n";
open OUT, ">", "$targetDir/count.sum.properties" or die $!;
print OUT "YVALUE=$countExamples\n";
print OUT "URL=http://abu.se.informatik.tu-darmstadt.de:8080/hudson/userContent/$projectName\n";
close OUT;

