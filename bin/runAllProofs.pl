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
my $automaticfol_txt = "automaticFOL.txt";
my $automaticjavadl_txt = "automaticJAVADL.txt";
my $not_provablefol_txt = "notProvableFOL.txt";
my $not_provablejavadl_txt = "notProvableJavaDL.txt";
my $interactive_txt = "interactive.txt";
my $quit_with_error_txt = "quitWithError.txt";
chdir $bin_path;
my $absolute_bin_path = &getcwd;
print "$absolute_bin_path\n";
chdir $path_to_pe;

if ($option{h}) {
  print "runs all proofs listed in the files: $automaticfol_txt, $automaticjavadl_txt, $interactive_txt, $not_provablefol_txt, $not_provablejavadl and $quit_with_error_txt .\n";
  print "They can be found in " .  $bin_path . "/" . $path_to_pe .  "\n\n";
  print "Use '-m email\@address.com' to send the report as an email to the specified address.\n";
  print "Use '-h' to get this text (very necessary this line).\n";
  print "Use '-c' to get the debug messages from the smtp part if there are email problems.\n";
  exit;
}


open (HEADER_FOL, $path_to_automated . "headerFOL.txt") or
  die $bin_path . "/" . $path_to_pe . "headerFOL.txt" . " couldn't be opened.";
binmode(HEADER_FOL);
my @headerFOL = <HEADER_FOL>;
close HEADER_FOL;

open (HEADER_JAVADL, $path_to_automated . "headerJava_DL.txt") or
  die $bin_path . "/" . $path_to_pe . "headerJava_DL.txt" . " couldn't be opened.";
binmode(HEADER_JAVADL);
my @headerJavaDL = <HEADER_JAVADL>;
close HEADER_JAVADL;

open (AUTOMATIC, $path_to_automated . $automaticfol_txt) or
  die $bin_path . "/" . $path_to_pe . $automaticfol_txt . " couldn't be opened.";
my @automatic_FOL = <AUTOMATIC>;
close AUTOMATIC;

open (AUTOMATIC, $path_to_automated . $automaticjavadl_txt) or
  die $bin_path . "/" . $path_to_pe . $automaticjavadl_txt . " couldn't be opened.";
my @automatic_JAVADL = <AUTOMATIC>;
close AUTOMATIC;

open (NOT_PROVABLE, $path_to_automated . $not_provablefol_txt) or
  die  $bin_path . "/" . $path_to_pe . $not_provablefol_txt . " couldn't be opened.";
my @not_provableFOL = <NOT_PROVABLE>;
close NOT_PROVABLE;

open (NOT_PROVABLE, $path_to_automated . $not_provablejavadl_txt) or
  die  $bin_path . "/" . $path_to_pe . $not_provablejavadl_txt . " couldn't be opened.";
my @not_provableJavaDL = <NOT_PROVABLE>;
close NOT_PROVABLE;


open (INTERACTIVE, $path_to_automated . $interactive_txt) or
  die  $bin_path . "/" . $path_to_pe . $interactive_txt . " couldn't be opened.";
my @interactive = <INTERACTIVE>;
close INTERACTIVE;



#open (QUIT_WITH_ERROR, $path_to_automated . $quit_with_error_txt) or die  $bin_path . "/" . $path_to_pe . $quit_with_error_txt . " couldn't be opened.";
#my @quit_with_error = <QUIT_WITH_ERROR>;
#close QUIT_WITH_ERROR;


my $counter = 0;
my $correct = 0;
my $failures = 0;
my $errors = 0;
my %successes;
my %failures;
my %erroneous;

 foreach my $dotkey (@automatic_FOL) {
   $dotkey = &fileline($dotkey);

   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my $cnt=grep /\\settings/, <HANDLE>;
   close HANDLE;

   #the following should be put in a sub routine
   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my @old = <HANDLE>;
   close HANDLE;

   open (HANDLE, ">".$dotkey);
   if (!$cnt) {
       foreach my $line (@headerFOL) {
	   print HANDLE $line;
       }
   }
   foreach my $line (@old) {
     print HANDLE $line;
   }
   close HANDLE;

   if ($dotkey) {
     my $success = runAuto ($dotkey);
     if ( $success == 0) {
       &processReturn (0, "indeed provable", $dotkey);
     } elsif ($success == 1) {
       &processReturn (1, "proof failed", $dotkey);
     } else {
       &processReturn (2, "error in proof", $dotkey);
     }
   }
 }

 foreach my $dotkey (@automatic_JAVADL) {
   $dotkey = &fileline($dotkey);

   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my $cnt=grep /\\settings/, <HANDLE>;
   close HANDLE;

   #the following should be put in a sub routine
   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my @old = <HANDLE>;
   close HANDLE;
   open (HANDLE, ">".$dotkey);
   if (!$cnt) {
       foreach my $line (@headerJavaDL) {
	   print HANDLE $line;
       }
   }
   foreach my $line (@old) {
     print HANDLE $line;
   }
   close HANDLE;

   if ($dotkey) {
     my $success = runAuto ($dotkey);
     if ( $success == 0) {
       &processReturn (0, "indeed provable", $dotkey);
     } elsif ($success == 1) {
       &processReturn (1, "proof failed", $dotkey);
     } else {
       &processReturn (2, "error in proof", $dotkey);
     }
   }
 }



  foreach my $dotkey (@not_provableFOL) {
    $dotkey = &fileline($dotkey);

   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my $cnt=grep /\\settings/, <HANDLE>;
   close HANDLE;

   #the following should be put in a sub routine
   open (HANDLE, $dotkey) or die  $dotkey. " couldn't be opened.";
   my @old = <HANDLE>;
   close HANDLE;
   open (HANDLE, ">".$dotkey);
   if (!$cnt) {
       foreach my $line (@headerFOL) {
	   print HANDLE $line;
       }
   }
   foreach my $line (@old) {
     print HANDLE $line;
   }
   close HANDLE;

    if ($dotkey) {
      my $success = runAuto ($dotkey);
      if ( $success == 0) {
        &processReturn (1, "should not be provable", $dotkey);
      } elsif ($success == 1) {
        &processReturn (0, "indeed not provable", $dotkey);
      } else {
        &processReturn (2, "error in proof", $dotkey);
      }
    }
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
   open (HANDLE, ">".$dotkey);
   if (!$cnt) {
       foreach my $line (@headerJavaDL) {
	   print HANDLE $line;
       }
   }
   foreach my $line (@old) {
     print HANDLE $line;
   }
   close HANDLE;

    if ($dotkey) {
      my $success = runAuto ($dotkey);
      if ( $success == 0) {
        &processReturn (1, "should not be provable", $dotkey);
      } elsif ($success == 1) {
        &processReturn (0, "indeed not provable", $dotkey);
      } else {
        &processReturn (2, "error in proof", $dotkey);
      }
    }
  }


  foreach my $dotkey (@interactive) {
    $dotkey = &fileline($dotkey);

    if ($dotkey) {
      my $success = runAuto ($dotkey);
     if ( $success == 0) {
       &processReturn (0, "indeed provable with interaction", $dotkey);
     } elsif ($success == 1) {
       &processReturn (1, "proof failed", $dotkey);
     } else {
       &processReturn (2, "error in proof", $dotkey);
     }
   }
  }

# foreach my $dotkey (@quit_with_error) {
#   $dotkey = &fileline($dotkey);
#   if ($dotkey) {
#     my $success = runAuto ($dotkey);
#     if ( $success == 0) {
#       &processReturn (1, "should not be provable", $dotkey);
#     } elsif ($success == 1) {
#       &processReturn (1, "should not be not provable", $dotkey);
#     } else {
#       &processReturn (0, "indeed error in proof", $dotkey);
#     }
#   }
# }

print "\n$correct/$counter prover runs according to spec. $errors errors occured.\n";
my $text = &produceResultText;
if ($text) {
  print $text;
  &mailResults ( $text ) if $option{m};
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

  $result;

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
  my $result = system $absolute_bin_path . "/runProver $dk auto print_statistics " . $absolute_bin_path . "/../examples/statistics.csv";
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

sub mailResults {
  # This debug flag will print debugging code to your browser, 
  # depending on its value  
  # Set this to 1 to send debug code to your browser.  
  # Set it to 0 to turn it off.  

  my $DEBUG = $option{h};

  if ($DEBUG) {  
    $| = 1;  
    open(STDERR, ">&STDOUT");  
  }

  my $ServerName = 'smtp.ira.uni-karlsruhe.de';


  # Connect to the server
  my $smtp = Net::SMTP->new($ServerName, Debug => $DEBUG);
  #die "Couldn't connect to server" unless $smtp;
  print "Couldn't connect to server" unless $smtp;


  my $MailFrom = "daniels\@ira.uka.de";
  my $MailFromText = "Reporting cronjob for KeY";
#  my $MailTo = "schlager\@ira.uka.de";
  my $MailTo = $option{m};


  $smtp->mail( $MailFrom );
  $smtp->to( $MailTo );

  # Start the mail
  $smtp->data();

  # Send the header.
  $smtp->datasend("To: $MailTo\n");
  $smtp->datasend("From: $MailFromText <$MailFrom>\n");
  $smtp->datasend("Subject: Problems with automated proof runs\n");
  $smtp->datasend("\n");

  # Send the message
  $smtp->datasend("$_[0]\n\n");

  # Send the termination string
  $smtp->dataend();

  $smtp->quit();

}
