#!/usr/bin/python3

import sys, os, re, urllib

# workflow:
#  - runIncrementalCheckstyle.sh | tee report.txt
#  - publishAudit.pl report.txt


def getenv(*args):
    "relaxed access to environment"
    return map(lambda x: os.environ.get(x, ""), args)

rawReport = sys.argv[1]
SERVER = "https://git.key-project.org/"
URL, PID, TOKEN, SHA, BID = getenv("CI_PROJECT_URL", "CI_PROJECT_ID",
                                   "CI_COMMENT_TOKEN", "CI_COMMIT_SHA","CI_BUILD_ID")

everythingIsFine = True

with open(rawReport) as raw:
    report = {'ERROR':[], 'WARN':[], 'INFO':[]}

    regex = re.compile(r'\[(?P<level>.*?)\] (?P<path>.*\/(?P<file>.*?)):(?P<line>\d+)(:\d+)?: (?P<msg>.*)')

    for line in raw:
        m = regex.match(line)
        if m:
            everythingIsFine = False
            markdown = "* [%s:%s](../blob/%s/%s#L%s): %s" % (
                m.group('file'), m.group('line'),
                SHA, m.group('path'), m.group('line'), m.group('msg'))
            report[m.group('level')].append( markdown )
            #"* [$3:$4](../blob/$sha/$2#L$4): $5\n";

def r2s(header, msgs, level=2):
    "report to string"
    if msgs:
        return ("#"*level) + " " + header + "\n\n" + "\n".join(msgs)
    else:
        return ""

if everythingIsFine:
    note = """Checkstyle has been run on this commit in [job %s](%s/builds/%s).
    *Good job. No issues.*
    """ % (BID, URL, BID)
else:
    note = """Checkstyle has been run on this commit in [job %s](%s/builds/%s).

Here is its report:

%s

%s

%s

""" % (BID, URL, BID,
       r2s("Error messages", report['ERROR'], level=1),
       r2s("Warning messages", report['WARN']),
       r2s("Info messages", report['INFO']))

import requests
reportUrl = "%s/api/v4/projects/%s/repository/commits/%s/comments" % (SERVER,PID,SHA)
print("Send report to", reportUrl)
resp = requests.post(reportUrl, data={ b'private_token': TOKEN, b'note':note })
print(note)
sys.exit(int(bool(report["ERROR"])))
