#!/usr/bin/perl -w
#
# This script can be used to check whether all proofs in a directory are still loadable.
# 
# As argument it expects the directory in which the proofs are located.
#
# written by Christoph Scheben

use strict;
use Cwd 'getcwd', 'realpath';
use File::Find;
use File::Basename;
use Getopt::Long;


die "There was no directory argument" unless(@ARGV);

# the path to the key directory
my $path_to_key = &realpath(&dirname($0) . "/../..");

# the directory to be checked
my $dir = $ARGV[0];

# the collection of all found proof names
opendir(DIR, $dir) or die "$dir couldn't be opened.";
my @filenames = readdir(DIR);
closedir(DIR);

# subrutine to call key
sub runAuto {
  my $filename = pop @_;
  my $command = "'" . $path_to_key . "/bin/key' --K-headless --auto-loadonly '$filename'";
   print "Command is: $command\n";
  my $result = system($command);
  return $result;
}


# load each proof file in key and print the result
my $numOfFiles = 0;
my $numOfLoadableFiles = 0;
my @failedFiles = ();
my @successfulFiles = ();
foreach my $filename (@filenames) {
    $filename = $dir.$filename;
    next if (-d $filename); # skip directories (like ..)
    
    $numOfFiles++;
    my $result = &runAuto($filename);
    
    if ($result == 0) {
	print "Loading was successful.\n\n";
	$numOfLoadableFiles++;
	push(@successfulFiles, $filename);
    } else {
	print "Loading failed!\n\n";
	push(@failedFiles, $filename);
    }
}

# print overall result
if ($numOfLoadableFiles == $numOfFiles) {
    print "All files could be loaded successfully.\n";
} else {
    print "Failed to load ".($numOfFiles-$numOfLoadableFiles)." files out of ".$numOfFiles.".\n";
    print "successful:\n";
    foreach my $filename (@successfulFiles) {
	print "  $filename\n";
    }
    print "failed:\n";
    foreach my $filename (@failedFiles) {
	print "  $filename\n";
    }
}

