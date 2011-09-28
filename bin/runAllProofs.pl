#!/usr/bin/perl -w
use strict;
use Cwd;
use File::Find;
use File::Basename;
use Getopt::Std;
# use File::Copy;
# use Net::SMTP;

#
# Configuration variables
my $bin_path = dirname($0);
my $path_to_examples = "../system/proofExamples/";
my $path_to_automated = "index/";
my $automaticjavadl_txt = "automaticJAVADL.txt";
my $not_provablejavadl_txt = "notProvableJavaDL.txt";
# time out set to 30 minutes
my $time_limit = 30*60; 

# use the time command to print out runtime info
my $time_command = "/usr/bin/time";
# output of the time command
my $time_format = '   user %U sec\n system %S sec\nelapsed %E sec\nMax. size %M kB\nAvg. size %t kB';


chdir $bin_path;
my $absolute_bin_path = &getcwd;

chdir $path_to_examples;

#
# Command line
my %option = ();
getopts("hdl", \%option);

if ($option{h}) {
  print "runs all proofs listed in the files: $automaticjavadl_txt and $not_provablejavadl_txt .\n";
  print "They can be found in " . $bin_path . "/" . $path_to_examples . "/" . $path_to_automated .  "\n\n";
  print "Use '-h' to get this text (very necessary this line).\n";
  print "Use '-l' to save proofs and reload them directly afterwards. (Test cases for proof loading)\n";
  print "Use '-d' to delete all files created automatically by a run of this script.\n";
#  print "[DEFUNCT] Use '-m email\@address.com' to send the report as an email to the specified address.\n";
#  print "[DEFUNCT] Use '-c' to get the debug messages from the smtp part if there are email problems.\n";
  exit;
}

my $reloadTests = $option{l};

if($option{d}) {
    &cleanDirectories (".");
    exit 0;
}

#
# read in the configuration files and store them in arrays.

open (HEADER_JAVADL, $path_to_automated . "headerJavaDL.txt") or
  die $path_to_automated . "headerJavaDL.txt" . " couldn't be opened.";
binmode(HEADER_JAVADL);
my @headerJavaDL = <HEADER_JAVADL>;
close HEADER_JAVADL;

open (AUTOMATIC, $path_to_automated . $automaticjavadl_txt) or
  die $path_to_automated . $automaticjavadl_txt . " couldn't be opened.";
my @automatic_JAVADL = <AUTOMATIC>;
close AUTOMATIC;

open (NOT_PROVABLE, $path_to_automated . $not_provablejavadl_txt) or
  die $path_to_automated . $not_provablejavadl_txt . " couldn't be opened.";
my @not_provableJavaDL = <NOT_PROVABLE>;
close NOT_PROVABLE;

my $counter = 0;
my $correct = 0;
my $failures = 0;
my $errors = 0;
my @reloadFailed;
my %successes;
my %failing;
my %erroneous;

#
# go through automatic files
#

foreach my $dotkey (@automatic_JAVADL) {

   # ignore empty lines and comments
   next if $dotkey =~ /^\s*#/;
   next if $dotkey =~ /^\s*$/;
 
   $dotkey = &fileline($dotkey);
   print "now running $dotkey ...\n";

   &prepare_file($dotkey);

   my $success = &runAuto ($dotkey . ".auto.key");
   if ( $success == 0) {
       &processReturn (0, "indeed provable", $dotkey);
   } elsif ($success == 256) {
       &processReturn (1, "proof failed", $dotkey);
   } else {
       &processReturn (2, "error in proof/timed out (" . 
		       "Error code $success)", $dotkey);
   }

   # replace trailing .key by .auto.proof
   $dotkey =~ s/\.key$/.auto.proof/;

   &reloadFile($dotkey) if $reloadTests;
    
   print "\nStatus: $counter examples tested. $failures failures and $errors errors occurred.\n";
   print "Reload-Tests: " . 
       ($reloadTests ? (scalar(@reloadFailed) . " failures") : "disabled") 
       . "\n\n";
}

#
# go through unprovable files
#

foreach my $dotkey (@not_provableJavaDL) {

    # ignore empty lines and comments
    next if $dotkey =~ /^\s*#/;
    next if $dotkey =~ /^\s*$/;

    $dotkey = &fileline($dotkey);
    print "now running $dotkey ...\n";

    &prepare_file($dotkey);
    
    my $success = &runAuto ($dotkey . ".auto.key");
    if ( $success == 0) {
        &processReturn (1, "should not be provable", $dotkey);
    } elsif ($success == 256) {
        &processReturn (0, "indeed not provable", $dotkey);
    } else {
	&processReturn (2, "error in proof/timed out (" . 
		       "Error code $success)", $dotkey);
    }

    # unlink($dotkey.".auto.key");
    # unlink($dotkey."auto.0.proof"); 

    print "\nStatus: $counter examples tested. $failures failures and $errors errors occurred.\n\n";
}

print "\n$correct/$counter prover runs according to spec.\n".
     "$failures failures and $errors errors occurred.\n";

if($reloadTests) {
    print "Failing reload attempts: " . scalar(@reloadFailed) . "\n\n";
} else {
    print "Reload tests were disabled\n\n";
}

print &produceResultText;

if($failures + $errors > 0) {
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
    return $_[0];
#  if ($_[0] =~ /\w*#/) {
#    '';
#  } else {
#    $_[0];
#  }
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
    
    return $result;
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
	# in case of a time out - wait a little for the process to finish
	sleep 10 if $result & 0xff;
	return $result;
    } else {
	die "Error while forking!";
    }
}
 
sub runAuto {
  my $dk = &getcwd . "/$_[0]";
  my $command = "$time_command -f '$time_format' " . $absolute_bin_path . "/runProver $dk auto";
  # print "Command is: $command\n";
  my $result = &system_timeout($time_limit, $command);
#  print "\nReturn value: $result\n";
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
    print "Try to reload proof result $file:\n";

    my $dk = &getcwd . "/$file";
    unless(-r $dk) {
	print "$dk cannot be read!";
	push @reloadFailed, $file;
	return;
    }

    my $command = "$time_command -f '$time_format' " . $absolute_bin_path . "/runProver $dk auto_loadonly";
    # print "Command is: $command\n";
    my $result = &system_timeout($time_limit, $command);
#    print "\nReturn value: $result\n";

    if($result != 0) {
	print "\nCould not reload saved file $file\n";
	push @reloadFailed, $file;
    }
}

sub cleanDirectories {
    print @_;
    find(\&wanted, @_);
    sub wanted {
	# $_ holds filename and $File::Find::name the full path
	# print $_ . "\n";
	if(/auto\.key$/ || /auto(\.[0-9]+)?\.proof$/) {
	    print "Remove file $File::Find::name\n";
	    unlink($_) or die "Cannot remove $_ in " . `pwd` . ": $!"; 
	}
    }

}
