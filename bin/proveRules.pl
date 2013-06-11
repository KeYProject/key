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
# This script is used to generate / run the proof obligations for KeY's rules
# which are tagges as derived and have to be proved as regression tests
#
# The steps are: 
#      1. scan the sysem .key files and generate proof obligations if
#         they do not exist
#
#      2. run KeY on these proof obligations, proving the PO or replaying
#         the proofs.
#

use strict;
use File::Basename;
use Cwd 'realpath';
use Getopt::Long;

#
# Configuration variables
my $path_to_key = realpath(dirname($0) . "/..");
my $path_to_examples = $path_to_key . "/examples/";
my $path_to_obligs = $path_to_examples . "taclets/";
my $path_to_rules = $path_to_key . "/system/resources/de/uka/ilkd/key/proof/rules";
my $now=localtime(time);
# time out set to 30 minutes
my $time_limit = 30*60; 

#                                                                               |
my $helptext = <<DOC;
Create and run/reload proofs for taclets in KeY.

The proof obligation files are stored in directory 'examples/taclets' under your
KeY top directory.

To enable the creation of a proof obligation for a rule, add the comment
  '//proved'
to the line DIRECTLY BEFORE the declaration of the rule. The proof obligation
will then be created by the next call to this script.

Command line options:
  -h  --help                  to get this help message
  -x  --xml-junit <filename>  to store the result of the tests in an xml-format
                              which can be understood by Jenkins.
  -c  --create-only           only create proof obligation files, no proofs
  -p  --proof-only            only run the proofs, do create proof obl. files.
  -d  --delete-old            remove proof obligation or proof files for rules
                              which are no longer annotated in the rules file.

DOC

#
# the template file for new proof obligations:
sub file_as_string {
    local $/ = undef;
    my $file = $_[0];
    open my $fh, "<", $file or die "could not open $file: $!";
    <$fh>;
};
my $path_to_template = $path_to_obligs . "tacletPO.template";
my $template = &file_as_string($path_to_template);

sub ensure_proof_obligation_present {
    my $rulename = $_[1];
    my $ruleset = "unknown";
    $ruleset = $1 if $_[0] =~ m#/([^/]+)\.key$#;

    my $dir = $path_to_obligs . $ruleset;
    my $target = "$dir/$rulename.key";

    mkdir $dir or die unless(-d $dir);

    if(-r $target) {
	print "Proof obligation for rule $rulename in $ruleset already present.\n";
    } else {
	open OUT, "> $target";
	my $s = $template;
	$s =~ s/%RULENAME%/$rulename/g;
	$s =~ s/%RULESET%/$ruleset/g;
	$s =~ s/%DATE%/$now/g;
	print OUT $s;
	print "Proof obligation for rule $rulename in $ruleset CREATED.\n";
	close OUT;
    }
}

sub scan_for_proof_obligations {
    foreach my $ruleFile (<$path_to_rules/*.key>) {
	open IN, "$ruleFile";
	my $tagFound = 0;
	while(<IN>) {
	    if($tagFound) {
		if(/\s*([a-zA-Z_0-9]+)\s*{/) {
		    &ensure_proof_obligation_present($ruleFile, $1);
		} else {
		    print "WARNING: spurious 'proved' annotations in $ruleFile:$.\n";
		}
		$tagFound = 0;
	    }
		    
	    $tagFound = 1 if m#^\s*//\s*proved:#;
	}
	close IN;
    }

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
    my $file = $_[0];
    my $mode = $_[1];  # either auto or auto-loadonly
    my $command = "'" . $path_to_key . "/bin/runProver' --$mode '$file'";
    print "Command is: $command\n";
    my $starttime = time();
    my $result = &system_timeout($time_limit, $command);
    print "Time elapsed: " . (time() - $starttime) . " sec\n";
#  print "\nReturn value: $result\n";
    return $result;
}

sub run_proof_obligations {

    my @successes;
    my @failures;
    my @errors;
    my $count = 0;

    foreach (<$path_to_obligs/*/*.key>) {
	my $proofName = $_;
	$proofName =~ s/.key$/.proof/;

	my $result;
	if(-r "$proofName") {
	    $result = &runAuto($proofName, "auto-loadonly");
	} else {
	    $result = &runAuto($_, "auto");
	}

	if ($result == 0) {
	    print "Indeed proved\n";
	    push @successes, $_;
	} elsif ($result == 256) {
	    print "Proof failed\n";
	    push @failures, $_;
	} else {
	    print "Error in proof / time out. Error code: $result\n";
	    push @errors, $_;
	}
    }

    print "\nSUMMARY:\n";
    print $count . " taclet proof obligations considered\n";
    print scalar(@successes) . " were successfully proved or reloaded\n";
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

sub remove_stale_files {
    my %taggedrules = ();
    foreach my $ruleFile (<$path_to_rules/*.key>) {
	open IN, "$ruleFile";
	my $ruleset = $1 if $ruleFile =~ m#/([^/]+)\.key$#;
	my $tagFound = 0;
	while(<IN>) {
	    if($tagFound) {
		if(/\s*([a-zA-Z_0-9]+)\s*{/) {		    
		    $taggedrules{"$path_to_obligs/$ruleset/$1"} = 1;
		} else {
		    print "WARNING: spurious 'proved' annotations in $ruleFile:$.\n";
		}
		$tagFound = 0;
	    }
		    
	    $tagFound = 1 if m#^\s*//\s*proved:#;
	}
	close IN;
    }

    # print join("\n", %taggedrules);

    foreach (<$path_to_obligs/*/*.key $path_to_obligs/*/*.proof>) {
	my $base = $_;
	$base =~ s/.[^\.]*$//;
	if($taggedrules{$base}) {
	    print "$_ is still valid.\n";
	} else {
	    print "$_ is a stale proof obligation/proof. It will be removed.\n";
	    unlink($_);
	}
    }



}

#
# Command line options
my %option = ();
GetOptions(\%option, 'help|h', 'xml-junit|x=s', 'prove-only|p', 'create-only|c', 
                     'delete-old|d');
if($option{'help'}) {
    print $helptext;
    exit 0;
}

&remove_stale_files if $option{'delete-old'};
&scan_for_proof_obligations unless $option{'prove-only'};
&run_proof_obligations unless $option{'create-only'};
