#!/usr/bin/perl -w


#
# THIS PROGRAM IS OUTDATED.
# 
# Please refer to the python program publishAudit.py
# composed by Alexander Weigl.
#
#



# workflow:
#  - runIncrementalCheckstyle.sh | tee report.txt
#  - publishAudit.pl report.txt

use LWP::UserAgent;
use Data::Dumper;
use HTTP::Request::Common;

$rawReport = shift @ARGV;
$server = "https://git.key-project.org/";
$url = $ENV{"CI_PROJECT_URL"};
$pid = $ENV{"CI_PROJECT_ID"};
$token = $ENV{"CI_COMMENT_TOKEN"};
$sha = $ENV{"CI_COMMIT_SHA"};
$bid = $ENV{"CI_BUILD_ID"};

open(my $raw, "<", $rawReport);
my $URL = "hhh";
my %report = ();
while(<$raw>) {

    if(/\[(.*?)\] (.*\/(.*?)):(\d+)(?::\d+)?: (.*)/) {
	$report{$1} .=  "* [$3:$4](../blob/$sha/$2#L$4): $5\n";
    }
}
close($raw);

sub report {
    (my $type, my $msg) = @_;

    my $result = "";
    if($msg) {
        $result .= "#" unless $type eq "ERROR"; # Errors have a larger heading ...
        $result .=  "## $type messages\n\n";
        $result .= $msg . "\n";
    }
    return $result;
}

my $note = "Checkstyle has been run on this commit in [job $bid]($url/builds/$bid).  ";
$note .= "Here is its report:\n\n";
if(%report) {
    $note .= "<details>";
    $note .= &report("ERROR", $report{"ERROR"});
    $note .= &report("WARNING", $report{"WARN"});
    $note .= &report("INFO", $report{"INFO"});
    $note .= "</details>";
} else {
    $note .= "*No issues. Good.*";
}

my $ua = LWP::UserAgent->new();
my $response = $ua->post(
    "$server/api/v4/projects/$pid/repository/commits/$sha/comments",
    { private_token => $token, note => $note });
my $content = $response->as_string();

print Dumper($content);

if($report{"ERROR"}) {
    exit 1;
} else {
    exit 0;
}
