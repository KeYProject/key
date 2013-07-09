#! /usr/bin/perl

# see http://www.somacon.com/p114.php
sub trim($) {
    my $string = shift;
    chomp $string;
    $string =~ s/^\s+//;
    $string =~ s/\s+$//;
    return $string;
}


my $statisticsFile = shift @ARGV;

my @sum;
my @columnNames;
while (<>) {
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
    } else {
	# remaining lines: adding up
	die "wrong number of fields in line $." 
	    unless scalar(@line) == scalar(@columnNames);
	for (@sum) {
	    $_ = $_ + shift(@line);
	}
    }
}

foreach (@columnNames) {
    open (OUT, ">", $_ . ".sum.properties") or die $!;
    print OUT "YVALUE=" . shift(@sum) . "\n";
    print OUT "URL=http://abu.se.informatik.tu-darmstadt.de:8080/hudson/userContent\n";
    close OUT;
}


