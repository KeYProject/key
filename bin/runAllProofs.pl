#!/usr/bin/perl -w
use File::Find;
use File::Copy;
use File::Basename;
use Cwd;
use strict;
use Net::SMTP;
use Getopt::Std;

my %option = ();
getopts("hcm:", \%option);


my $bin_path = dirname($0);
my $path_to_pe = "../system/proofExamples/";
my $path_to_automated = "index/";
my $automaticjavadl_txt = "automaticJAVADL.txt";
my $not_provablejavadl_txt = "notProvableJavaDL.txt";
chdir $bin_path;
my $absolute_bin_path = &getcwd;
print "$absolute_bin_path\n";
chdir $path_to_pe;

if ($option{h}) {
  print "runs all proofs listed in the files: $automaticjavadl_txt and $not_provablejavadl_txt .\n";
  print "They can be found in " .  $bin_path . "/" . $path_to_pe .  "\n\n";
  print "Use '-m email\@address.com' to send the report as an email to the specified address.\n";
  print "Use '-h' to get this text (very necessary this line).\n";
  print "Use '-c' to get the debug messages from the smtp part if there are email problems.\n";
  exit;
}


open (HEADER_JAVADL, $path_to_automated . "headerJavaDL.txt") or
  die $bin_path . "/" . $path_to_pe . "headerJavaDL.txt" . " couldn't be opened.";
binmode(HEADER_JAVADL);
my @headerJavaDL = <HEADER_JAVADL>;
close HEADER_JAVADL;

open (AUTOMATIC, $path_to_automated . $automaticjavadl_txt) or
  die $bin_path . "/" . $path_to_pe . $automaticjavadl_txt . " couldn't be opened.";
my @automatic_JAVADL = <AUTOMATIC>;
close AUTOMATIC;

open (NOT_PROVABLE, $path_to_automated . $not_provablejavadl_txt) or
  die  $bin_path . "/" . $path_to_pe . $not_provablejavadl_txt . " couldn't be opened.";
my @not_provableJavaDL = <NOT_PROVABLE>;
close NOT_PROVABLE;



my $counter = 0;
my $correct = 0;
my $failures = 0;
my $errors = 0;
my %successes;
my %failures;
my %erroneous;


 foreach my $dotkey (@automatic_JAVADL) {
   $dotkey = &fileline($dotkey);

   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my $cnt=grep /\\settings/, <HANDLE>;
   close HANDLE;

   #the following should be put in a sub routine
   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my @old = <HANDLE>;
   close HANDLE;
   open (HANDLE, ">".$dotkey.".auto.key");
   if (!$cnt) {
       foreach my $line (@headerJavaDL) {
	   print HANDLE $line;
       }
   }
   foreach my $line (@old) {
     print HANDLE $line;
   }
   close HANDLE;

   if ($dotkey.".auto.key") {
     my $success = runAuto ($dotkey.".auto.key");
     if ( $success == 0) {
       &processReturn (0, "indeed provable", $dotkey);
     } elsif ($success == 1) {
       &processReturn (1, "proof failed", $dotkey);
     } else {
       &processReturn (2, "error in proof", $dotkey);
     }
     unlink($dotkey.".auto.key");
     chop($dotkey);
     chop($dotkey);
     chop($dotkey);
     unlink($dotkey."auto.0.proof")
   }
   print "\nStatus: $counter examples tested. $errors errors occurred.\n\n";
 }



  foreach my $dotkey (@not_provableJavaDL) {
    $dotkey = &fileline($dotkey);

   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my $cnt=grep /\\settings/, <HANDLE>;
   close HANDLE;

   #the following should be put in a sub routine
   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my @old = <HANDLE>;
   close HANDLE;
   open (HANDLE, ">".$dotkey.".auto.key");
   if (!$cnt) {
       foreach my $line (@headerJavaDL) {
	   print HANDLE $line;
       }
   }
   foreach my $line (@old) {
     print HANDLE $line;
   }
   close HANDLE;

    if ($dotkey.".auto.key") {
      my $success = runAuto ($dotkey.".auto.key");
      if ( $success == 0) {
        &processReturn (1, "should not be provable", $dotkey);
      } elsif ($success == 1) {
        &processReturn (0, "indeed not provable", $dotkey);
      } else {
        &processReturn (2, "error in proof", $dotkey);
      }
    }
    unlink($dotkey.".auto.key");
    chop($dotkey);
    chop($dotkey);
    chop($dotkey);
    unlink($dotkey."auto.0.proof");
    print "\nStatus: $counter examples tested. $errors errors occurred.\n";
  }


print "\n$correct/$counter prover runs according to spec. $errors errors occurred.\n\n";
my $text = &produceResultText;
if ($text) {
  print $text;
}

# ------------------------------------------------------------


sub fileline {
  chop $_[0];
  if ($_[0] =~ /\w*#/) {
    '';
  } else {
    $_[0];
  }
}

sub produceResultText {
  my $result;
  if (%failures) {
    $result .= "++The following files did not behave as expected:\n";
    foreach my $key (keys %failures) {
      $result .= "$key \t :  $failures{$key}\n"
    }
  }
  if (%erroneous) {
    $result .= "++The following files produced unexpected errors:\n";
    foreach my $key (keys %erroneous) {
      $result .= "$key \t :  $erroneous{$key}\n"
    }
  }

  if (%failures || %erroneous) {
      exit -1;
  }

}

sub runAuto {
  #  system "ls -l $_[0]";
  #  system $bin_path . "/runProver $_[0] auto";
  my $dk = &getcwd . "/$_[0]";
  #  print "$dk .-. ";
  sleep(1);
  my $result = system $absolute_bin_path . "/runProver $dk auto ";
  #chdir "/home/daniels/programme/kruscht/";
  #my $result = system 'java RetVal';
  #print "\n Return value if: $result\n";
  $result / 256; #exit code from system is multiplied by 256
}

sub processReturn { 
  $counter++;
  if ($_[0] == 0) {
    print "$_[1] : $_[2]\n";
    $successes{"$_[2]"} = $_[1];
    $correct++;
  } elsif ($_[0] == 1) {
    print "$_[1] : $_[2]\n";
    $failures{"$_[2]"} = $_[1];
    $failures++;
  } elsif ($_[0] == 2) {
    print "$_[1] : $_[2]\n";
    $erroneous{"$_[2]"} = $_[1];
    $errors++;
  }
}
