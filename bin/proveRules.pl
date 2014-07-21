#!/usr/bin/perl -w
#
# // This file is part of KeY - Integrated Deductive Software Design 
# //
# // Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
# //                         Universitaet Koblenz-Landau, Germany
# //                         Chalmers University of Technology, Sweden
# // Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
# //                         Technical University Darmstadt, Germany
# //                         Chalmers University of Technology, Sweden
# //
# // The KeY system is protected by the GNU General 
# // Public License. See LICENSE.TXT for details.
# // 

#
# This script is used to check proofs for KeY's rules by rerunning
# them.  It ensures that all rules which are tagged "proved" have
# indeed a loadable proof.
#
# This script is called in the course of the regression tests.
#
# The steps are: 
#      1. scan the examples/taclets directory for proofs.
#      2. run these proofs.
#      3. check for taclets in the rules directory which are tagged
#         proof
#      4. Fail if there is a tagged rule without proof.
#
# The proof files may be arbitrarily nested under the tacelts
# directory.
#
# The program has no timeout set on the invocations of KeY. 
# We advise you to run the tool within a timeout environment

use strict;
use warnings;
use File::Find qw(finddepth);
use File::Temp qw(tempfile);
use POSIX qw(strftime);
use File::Basename;
use File::Glob qw(bsd_glob);
use Cwd 'realpath';
use Getopt::Long;

#
# Configuration variables
my $path_to_key = realpath(dirname($0) . "/..");
my $path_to_examples = $path_to_key . "/examples/";
my $path_to_proofs = $path_to_examples . "taclets/";
my $path_to_rules = $path_to_key . "/system/resources/de/uka/ilkd/key/proof/rules";
my $iso8601now = strftime("%Y-%m-%dT%H:%M:%S", localtime(time()));
# time out set to 30 minutes
my $time_limit = 30*60; 

#                                                                               |
my $helptext = <<DOC;
Check the proofs for taclets in KeY.

The proof files are stored in directory 'examples/taclets' under your
KeY top directory.

To mark a rule amongst your KeY system rules as a proved rule, add the
comment 
  '// proved:' 
to the line DIRECTLY BEFORE the declaration of the rule. 

If no proof for this rule is found during checking of rules, an error
is raised.

Command line options:
  -h  --help                  to get this help message
  -x  --xml-junit <filename>  to store the result of the tests in an xml-format
                              which can be understood by Jenkins.
  -p  --prove-only            to only rerun the proofs w/o checking annotations
  -q  --quick-check           to only check the annotations w/o running the proofs.
DOC

my (undef, $log_file) = tempfile();
my @successes = ();
my @failures = ();
my @errors = ();
my @missing_proofs = ();
my %proved_taclets = ();

sub check_annotations {
    print "Checking proved annotations in directory $path_to_rules...\n";
 
    my @files = bsd_glob("$path_to_rules/*.key");
    foreach my $ruleFile (@files) {
	open IN, "$ruleFile" or die "cannot read $ruleFile";
	my $tagFound = 0;
	while(<IN>) {
	    if($tagFound) {
		if(/\s*([a-zA-Z_0-9]+)\s*{/) {
		    if($proved_taclets{$1}) {
			$proved_taclets{$1} = 2;
			print "  Proof for annotated rule '$1' is present.\n";
		    } else {
			print "  ERROR: Proof for annotated rule '$1' is MISSING!\n";
			push @missing_proofs, $1;
		    }
		} else {
		    print "  Warning: spurious 'proved' annotation in $ruleFile:$.\n";
		}
		$tagFound = 0;
	    }
		    
	    $tagFound = 1 if m#^\s*//\s*proved:?#;
	}
	close IN;
    }

    foreach (keys(%proved_taclets)) {
	if($proved_taclets{$_} == 1) {
	    print "  Warning: The rule '$_' is proved, however its definition is NOT annotated.\n";
	}
    }

}

sub grep_proof_files {
    my @files;
    finddepth(sub {
	my $f = $File::Find::name;
	push @files, $f if /\.proof$/;
    }, $path_to_proofs);

    my $count = 0;

    print "Note: KeY is NOT actually run. Only the names of proved taclets are extracted from proof files.\n";
    
    my $inPO = 0;
    foreach my $proofName (@files) {
	open IN, "<", $proofName or die "cannot read $proofName";;
	while(<IN>) {
	    $inPO=1 if /^\\proofObligation/;
            if($inPO && /^name=(.*)$/) {
                print "  Found proof obligation for $1 in file $proofName\n";
                $proved_taclets{$1}=1;
            }
	    $inPO=0 if /^";/;
	}
    }
}

# This is without timeout :-(
# Compare runAllProofs.pl to see how to do it WITH timeout
# Capturing the output is difficult then, however!
sub runAuto {
    my $file = $_[0];
    my $command = "'" . $path_to_key . "/bin/key' --auto-loadonly '$file'";
    print "Command is: $command\n";
    my $starttime = time();
    my @output = `$command`;
    my $result = $?;

    print "Time elapsed: " . (time() - $starttime) . " sec\n";
#    print "Return value: $result\n";

    my $taclet = "$file";
    my $open_goals = 0;
    foreach (@output) {
	print $_;
	$taclet = $1 if /^Proof obligation for taclet: (.*)$/;
	$open_goals = $1 if /^Number of open goals after loading: (.*)$/;	
    }

    return ($result, $taclet, $open_goals);
}

sub rerun_proof_obligations {

    my @files;
    finddepth(sub {
	my $f = $File::Find::name;
	push @files, $f if /\.proof$/;
    }, $path_to_proofs);

    my $count = 0;

    print "Note: KeY output is delayed in this script. Please be patient ...\n";

    foreach my $proofName (@files) {

	my ($result, $taclet, $open_goals) = &runAuto($proofName, "auto-loadonly");
	my $shortName = substr $proofName, length($path_to_proofs);

	$proved_taclets{$taclet} = 1;
	
	if ($result == 256 || $open_goals > 0) {
	    print "Proof failed\n";
	    push @failures, $shortName;
	} elsif ($result == 0) {
	    print "Indeed proved\n";
	    push @successes, $shortName;
	} else {
	    print "Error in proof / time out. Error code: $result\n";
	    push @errors, $shortName;
	}
    }

    print "\nSUMMARY:\n";
    print "From the taclet proofs considered\n";
    print scalar(@successes) . " were successfully proved\n";
    print scalar(@failures) . " proofs failed\n";
    print scalar(@errors) . " errors occured\n";
    
    if(scalar(@failures)) {
	print "\nThe failures occurred in the proofs of:\n";
	foreach (@failures) {
	    print "  " . $_ . "\n";
	}
    }

    if(scalar(@errors)) {
	print "\nThe errors occurred in the proofs of:\n";
	foreach (@errors) {
	    print "  " . $_ . "\n";
	}
    }

}

sub write_xml_report {
    my $filename = $_[0];
    open OUT, ">", $filename or die "cannot open $filename for writing.";

    my $errors    = scalar(@errors);
    my $failures  = scalar(@failures);
    my $successes = scalar(@successes);
    my $tests     = $errors + $failures + $successes + 1;
    my $timestamp = $iso8601now;

    $failures++ if scalar(@missing_proofs) > 0;

    print OUT <<HEADER ;
<?xml version="1.0" encoding="UTF-8" ?>
<testsuite errors="$errors" failures="$failures" name="proveRules" tests="$tests" timestamp="$timestamp" host="localhost" time="0.0">
  <properties>
    <property name="directory" value="$path_to_key" />
  </properties>
HEADER

    foreach (@successes) {
	print OUT '  <testcase classname="proveRules.run" name="' . 
	    $_ . '" time="0.0" />'  . "\n";
    }
    foreach (@errors) {
	print OUT '  <testcase classname="proveRules.run" name="' . 
	    $_ . '" time="0.0">'  . "\n";
	print OUT '     <error type="ERR">error during proof for ' .
	    $_ . "</error>\n  </testcase>\n";
    }
    foreach (@failures) {
	print OUT '  <testcase classname="proveRules.run" name="' . 
	    $_ . '" time="0.0">'  . "\n";
	print OUT '     <failure type="FAIL">proof for ' .
	    $_ . " failed</failure>\n  </testcase>\n";
    }
    print OUT '  <testcase classname="proveRules.run" name="ruleAnnotations" time="0.0">' . "\n";
    if(scalar(@missing_proofs) > 0) {
	print OUT '     <failure type="FAIL">Missing proofs for the following annotated rule(s): '  .
	    join(", ", @missing_proofs) . "</failure>\n";
    }
    print OUT "  </testcase>\n";
    
    print OUT "</testsuite>";
    close OUT;
    print "JUnit XML report written to $filename.\n\n";
}
    
#
# Command line options
my %option = ();
GetOptions(\%option, 'help|h', 'xml-junit|x=s', 'prove-only|p', 'quick-check|q');
if($option{'help'}) {
    print $helptext;
    exit 0;
}

if($option{'quick-check'}) {
    &grep_proof_files;
} else {
    &rerun_proof_obligations;
}

unless($option{'prove-only'}) {
    &check_annotations;
}

my $xml = $option{'xml-junit'};
&write_xml_report($xml) if $xml;

# reaching this point everything is fine!
# Failures are reported to xml file
exit 0;
