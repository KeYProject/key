#!/usr/bin/perl -w
use strict;
use Cwd 'getcwd', 'realpath';
use File::Find;
use File::Basename;
use Getopt::Long;
use POSIX qw(strftime);
# use File::Copy;
# use Net::SMTP;

#
# Configuration variables
my $orig_path = &getcwd;
my $path_to_key = realpath(dirname($0) . "/..");
my $path_to_examples = $path_to_key . "/examples/";
my $path_to_automated = "index/";
my $path_to_header = $path_to_examples . $path_to_automated . "headerJavaDL.txt";
my $path_to_index = $path_to_examples . $path_to_automated . "automaticJAVADL.txt";

# time out set to 30 minutes
my $time_limit = 30*60; 

# use the time command to print out runtime info
#my $time_executable = "/usr/bin/time";
# output of the time command
#my $time_format = '   user %U sec\n system %S sec\nelapsed %E sec\nMax. size %M kB\nAvg. size %t kB';


# see http://www.somacon.com/p114.php
sub trim($) {
    my $string = shift;
    chomp $string;
    $string =~ s/^\s+//;
    $string =~ s/\s+$//;
    return $string;
}

#
# Command line options
my %option = ();
GetOptions(\%option, 'help|h', 'verbose|v', 'silent|z', 'delete|d', 'reload|l', 'stopfail|t', 'storefailed|s=s', 'file|f=s', 'xml-junit|x=s', 'printStatistics|p=s');

if ($option{'help'}) {
  print "Runs all proofs listed in the file \'$path_to_index\'.\n";
#  print "\'$path_to_index\' can be found in the directory \'$key_path/$path_to_examples$path_to_automated\'.\n\n";
  print "Use '-h' or '--help' to get this text (very necessary this line).\n";
  print "Use '-v' or '--verbose' to increase verbosity.\n";
  print "Use '-z' or '--silent' to reduce verbosity (only final results are displayed).\n";
  print "Use '-l' or '--reload' to save proofs and reload them directly afterwards. (Test cases for proof loading.)\n";
  print "Use '-d' or '--delete' to delete all files created automatically by a run of this script.\n";
  print "Use '-t' or '--stopfail' to stop immediately upon a failure.\n";
  print "Use '-s <filename>' or '--storefailed <filename>' to store the file names of failures in file <filename>.\n";
  print "Use '-f <filename>' or '--file <filename>' to load the problems from <filename>.\n";
  print "Use '-x <filename>' or '--xml-junit <filename>' to store the results in junit's xml result format to <filename>.\n";
  print "Use '-p <filename>' or '--printStatistics <filename>' to generate a statistics file. The file is overridden in case it already exists.\n";
#  print "[DEFUNCT] Use '-m email\@address.com' to send the report as an email to the specified address.\n";
#  print "[DEFUNCT] Use '-c' to get the debug messages from the smtp part if there are email problems.\n";
  exit;
}

my $reloadTests = $option{'reload'};

if($option{'delete'}) {
    &cleanDirectories ($path_to_examples);
    exit 0;
}

if ($option{'printStatistics'}) {
    $option{'printStatistics'} = realpath($option{'printStatistics'});
    unlink($option{'printStatistics'}) 
	if $option{'printStatistics'} && -e $option{'printStatistics'};
}

#
# read in the configuration files and store them in arrays.

open (HEADER_JAVADL, $path_to_header) or die $path_to_header . " couldn't be opened.";
binmode(HEADER_JAVADL);
my @headerJavaDL = <HEADER_JAVADL>;
close HEADER_JAVADL;

my $testFile;
if (not $option{'file'}) {
  $testFile = $path_to_index;
} else {
  $testFile = $option{'file'};
}

print "Reading from $testFile.\n\n" unless $option{'silent'};

my @automatic_JAVADL;
open (AUTOMATIC, $testFile) or die $testFile . " couldn't be opened.";
@automatic_JAVADL = <AUTOMATIC>;
close AUTOMATIC;

my $counter = 0;
my $total = trim(`grep provable "$path_to_index" | grep -v "\#" | wc -l`);
my $correct = 0;
my $failures = 0;
my $errors = 0;
my @reloadFailed;
my @reloadSuccesses;
my %successes;
my %failing;
my %erroneous;

#
# go through automatic files
#
chdir $path_to_examples;
foreach my $dotkey (@automatic_JAVADL) {
   if ($option{'stopfail'} && 
		($failures + $errors + scalar(@reloadFailed) > 0)) {
      print "Bailing out due to error\n";
      last;
   }

   # ignore empty lines and comments
   next if $dotkey =~ /^\s*#/;
   next if $dotkey =~ /^\s*$/;
 
   (my $provable, $dotkey) = &fileline($dotkey);

   print "Now running $dotkey ...\n" unless $option{'silent'};

   &prepare_file($dotkey);

   my $success = &runAuto ($dotkey . ".auto.key");

   if ($provable and $success == 0) {
       &processReturn (0, "indeed provable", $dotkey);
   } elsif ($provable and $success == 256) {
       &processReturn (1, "proof failed", $dotkey);
   } elsif ((not $provable) and $success == 0) {
       &processReturn (1, "should not be provable", $dotkey);
   } elsif ((not $provable) and $success == 256) {
       &processReturn (0, "indeed not provable", $dotkey);
   } else {
       &processReturn (2, "error in proof/timed out (" . 
 		    "Error code $success)", $dotkey);
   }

   # replace trailing .key by .auto.proof
   $dotkey =~ s/\.key$/.auto.proof/;

   &reloadFile($dotkey) if ($reloadTests and $provable);
    
   unless($option{'silent'}) {
      print "\nStatus: $counter / $total examples tested. $failures failures and $errors errors occurred.\n";
      print "Reload-Tests: " . 
         (($reloadTests and $provable) ? (scalar(@reloadFailed) . 
					  " failures") : "disabled") 
         . "\n\n";
   }
}

chdir $orig_path;

print "\n$counter / $total prover runs according to spec.\n".
     "$failures failures and $errors errors occurred.\n";

if($reloadTests) {
    print "Failing reload attempts: " . scalar(@reloadFailed) . "\n\n";
} else {
    print "Reload tests were disabled\n\n";
}

print &produceResultText;

if($option{'storefailed'}) {
  &storeFailedProofs
}

if($option{'xml-junit'}) {
    &writeXmlReport($option{'xml-junit'});
}

if ($option{'printStatistics'}) {
    # calculate Summas
    my @sum = &calculateSummas($option{'printStatistics'});
    
    # append summas 
    my $line = "--- SUM ---";
    foreach my $s (@sum) {
	$line = $line." | ".$s;
    }
    open OUT, ">>", $option{'printStatistics'} or die $!;
    print OUT $line."\n";
    
    # append git commit hash
    my $gitHash = `git rev-parse HEAD`;
    print OUT "\n";
    print OUT "# git commit $gitHash\n";
    close OUT;
}

if($failures + $errors + scalar(@reloadFailed) > 0) {
    if($option{'stopfail'}) {
        print "Tests stopped after first failure.\n";
    }
    exit -1;
} else {
    exit 0;
}

# Sub routines
# ------------------------------------------------------------

sub prepare_file {

    my $dotkey = $_[0];

    open (IN, $dotkey) or 
	die $dotkey. " couldn't be opened for reading.";
    open (OUT, "> " . $dotkey . ".auto.key") or 
	die $dotkey. ".auto.key couldn't be opened for writing.";
    
    my $has_settings = grep /\\settings/, <IN>;
    
    seek IN, 0, 0;

    print OUT @headerJavaDL unless $has_settings;

    while(<IN>) {
	print OUT $_;
    }

    close OUT;
    close IN;
}

sub fileline {
    chop $_[0];
    (my $result, my $file) = split(/: */, $_[0]);
    return (($result eq 'provable'), $file);
}

sub produceResultText {
    my $result = "";

    if (%failing) {
	$result .= "++The following files did not behave as expected:\n";
	foreach my $key (keys %failing) {
	    $result .= "$key \t :  $failing{$key}\n"
	}
    }
    
    if (%erroneous) {
	$result .= "++The following files produced unexpected errors:\n";
	foreach my $key (keys %erroneous) {
	    $result .= "$key \t :  $erroneous{$key}\n"
	}
    }

    if (@reloadFailed) {
	$result .= "++The following files could not have their proof reloaded:\n";
	foreach (@reloadFailed) {
	    $result .= "$_\n";
	}
    }
    
    return $result."\n";
}

sub storeFailedProofs {
    open (OUT, "> ".$option{'storefailed'}) or 
        die $option{'storefailed'}." couldn't be opened for writing.";

    if (%failing) {
# 	++The following files did not behave as expected:
	foreach my $key (keys %failing) {
	    print OUT ($failing{$key} eq 'proof failed' ? 'provable: ' : 'notprovable: ');
	    print OUT "$key\n";
	}
    }
    
    if (%erroneous) {
# 	++The following files produced unexpected errors:
	foreach my $key (keys %erroneous) {
	    print OUT ($erroneous{$key} eq 'proof failed' ? 'provable: ' : 'notprovable: ');
	    print OUT "$key\n";
	}
    }

    if (@reloadFailed) {
# 	++The following files could not have their proof reloaded:
	foreach (@reloadFailed) {
	    # reload is done only in case the problem is provable
	    print OUT 'provable: ';
	    print OUT "$_\n";
	}
    }
    close OUT;
    print "Failed proof attempts stored in \'".$option{'storefailed'}."\'.\n\n";
}

sub iso8601now {
    # ISO8601
    return strftime("%Y-%m-%dT%H:%M:%S", localtime(time()));
}

sub writeXmlReport {
    my $filename = $_[0];
    open OUT, "> $filename" or die "cannot open $filename for writing.";

    my $errors    = scalar(keys(%erroneous));
    my $failures  = scalar(keys(%failing)) + scalar(@reloadFailed);
    my $successes = scalar(keys(%successes)) + scalar(@reloadSuccesses);
    my $tests     = $errors + $failures + $successes;
    my $timestamp = &iso8601now;

    print OUT <<HEADER;
<?xml version="1.0" encoding="UTF-8" ?>
<testsuite errors="$errors" failures="$failures" name="runAllProofs" tests="$counter" timestamp="$timestamp" host="localhost" time="0.0">
  <properties>
    <property name="reload" value="$reloadTests" />
    <property name="directory" value="$path_to_key" />
  </properties>
HEADER
    foreach (keys(%successes)) {
	print OUT '  <testcase classname="runallproofs.run" name="' . 
	    $_ . '" time="0.0" />'  . "\n";
    }
    foreach (@reloadSuccesses) {
	print OUT '  <testcase classname="runallproofs.reload" name="' . 
	    $_ . '" time="0.0" />'  . "\n";
    }
    foreach (keys(%erroneous)) {
	print OUT '  <testcase classname="runallproofs.run" name="' . 
	    $_ . '" time="0.0">'  . "\n";
	print OUT '     <error type="ERR">error during proof for ' .
	    $_ . "</error>\n  </testcase>\n";
    }
    foreach (keys(%failing)) {
	print OUT '  <testcase classname="runallproofs.run" name="' . 
	    $_ . '" time="0.0">'  . "\n";
	print OUT '     <failure type="FAIL">proof for ' .
	    $_ . " failed</failure>\n  </testcase>\n";
    }
    foreach (@reloadFailed) {
	print OUT '  <testcase classname="runallproofs.reload" name="' . 
	    $_ . '" time="0.0">'  . "\n";
	print OUT '     <failure type="FAIL">could not reload proof for ' .
	    $_ . "</failure>\n  </testcase>\n";
    }

    print OUT "</testsuite>";
    close OUT;
    print "JUnit XML report written to $filename.\n\n";
}

# first argument: timeout in seconds
# following arguments: used to call exec.
# returns error code with user error code shifted to the left by 8.
# user exit code 1 ==> 256
sub system_timeout {
    my $child = fork();
    if($child == 0) {
	# child process: call process, with alarm set
	alarm shift @_;
	exec @_;
	exit 127;
    } elsif($child > 0) {
	# parent process, waiting for child
	waitpid $child, 0;
	my $result = ${^CHILD_ERROR_NATIVE};
        # this waitpid call makes the result value (of KeY) shift by 8 to the left
	# in case of a time out - wait a little for the process to finish
	sleep 10 if $result & 0xff;
	return $result;
    } else {
	die "Error while forking!";
    }
}
 
sub runAuto {
  my $dk = &getcwd . "/$_[0]";
  my $statisticsCmd = "";
  if ($option{'printStatistics'}) {
    $statisticsCmd = "--print-statistics '$option{'printStatistics'}'";
  }
  my $verbosity = "";
  if ($option{'silent'}) { $verbosity = "--verbose 0"; }
  if ($option{'verbose'}) { $verbosity = "--verbose 2"; }
  my $command = "'" . $path_to_key . "/bin/key' --K-headless --auto $verbosity $statisticsCmd '$dk'";
  print "Command is: $command\n" unless $option{'silent'};
  my $starttime = time();
  my $result = &system_timeout($time_limit, $command);
  print "Total time elapsed: " . (time() - $starttime) . " sec\n" unless $option{'silent'};
  return $result;
}

sub processReturn {
    print "$_[1] : $_[2]\n";
    $counter++;
    if ($_[0] == 0) {
	$successes{"$_[2]"} = $_[1];
	$correct++;
    } elsif ($_[0] == 1) {
	$failing{"$_[2]"} = $_[1];
	$failures++;
    } elsif ($_[0] == 2) {
	$erroneous{"$_[2]"} = $_[1];
	$errors++;
    }
}

sub reloadFile {
    my $file = $_[0];
    if (not $option{'silent'}) {print "\nTry to reload proof result $file:\n";}

    my $dk = &getcwd . "/$file";
    unless(-r $dk) {
	if (not $option{'silent'}) {print "$dk cannot be read!";}
	push @reloadFailed, $file;
	return;
    }

    my $command = "'" . $path_to_key . "/bin/key' --K-headless --auto-loadonly '$dk'";
    # print "Command is: $command\n";
    my $result = &system_timeout($time_limit, $command);
#    print "\nReturn value: $result\n";

    if($result != 0) {
	if (not $option{'silent'}) {
	    print "\nCould not reload saved file $file\n";
        }
	push @reloadFailed, $file;
    } else {
	push @reloadSuccesses, $file;
    }
}

sub cleanDirectories {
    print @_;
    find(\&wanted, @_);
    sub wanted {
	# $_ holds filename and $File::Find::name the full path
	# print $_ . "\n";
	if(/auto\.key$/ || /auto(\.[0-9]+)?\.proof$/) {
	    if (not $option{'silent'}){print "Remove file $File::Find::name\n";}
	    unlink($_) or die "Cannot remove $_ in " . `pwd` . ": $!"; 
	}
    }

}

sub calculateSummas {
    my $filename = shift @_;
    my @sum;
    my @columnNames;
    my $countExamples = 0;
    open IN, "<", $filename or die $!;
    while (<IN>) {
	my @line = split /\s*\|\s*/, &trim($_);
	# remove the name of the example (can not be summed up)
	shift(@line);
	if ($. == 1) {
	    # first line with column names
	    @columnNames = @line;
	} elsif ($. == 2) {
	    # second line: init sum
	    die "wrong number of fields in line $." 
		unless scalar(@line) == scalar(@columnNames);
	    @sum = @line;
	    $countExamples ++;
	} else {
	    # remaining lines: adding up
	    die "wrong number of fields in line $." 
		unless scalar(@line) == scalar(@columnNames);
	    for (@sum) {
		$_ = $_ + shift(@line);
	    }
	    $countExamples ++;
	}
    }
    close IN;
    
    # compute averages instead of sums
    # extra handling of the average time per step and memory consumption 
    # (which should be in the last two columns)
    $sum[@sum-2] = $sum[@sum-2] / $countExamples;
    $sum[@sum-1] = $sum[@sum-1] / $countExamples;
    return @sum;
}


