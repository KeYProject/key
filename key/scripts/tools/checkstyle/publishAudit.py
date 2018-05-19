#!/usr/bin/python3

import sys, os, re, urllib

# workflow:
#  - runIncrementalCheckstyle.sh | tee report.txt
#  - publishAudit.py report.txt

# The original was written in perl and is available under publishAudit.pl

# Written by Alexander Weigl
# Refactored in May 2018, by Mattias Ulbrich

def getenv(*args):
    "relaxed access to environment"
    return map(lambda x: os.environ.get(x, ""), args)

rawReport = sys.argv[1]
SERVER = "https://git.key-project.org/"
URL, PID, TOKEN, SHA, BID, JID = getenv("CI_PROJECT_URL", "CI_PROJECT_ID",
                                        "CI_COMMENT_TOKEN", "CI_COMMIT_SHA",
                                        "CI_BUILD_ID", "CI_JOB_ID")

everythingIsFine = True

with open(rawReport) as raw:
    report = {'ERROR':0, 'WARN':0, 'INFO':0}

    regex = re.compile(r'\[(?P<level>.*?)\] (?P<path>.*\/(?P<file>.*?)):(?P<line>\d+)(:\d+)?: (?P<msg>.*)')

    for line in raw:
        m = regex.match(line)
        if m:
            everythingIsFine = False
            old = report[m.group('level')]
            report[m.group('level')] = old + 1

def r2s(header, count, red=False):
    "report to string"
    if count > 0:
        markup = "**" if red else ""
        return "- " + markup + str(count) + " " + header + markup + "\n"
    else:
        return ""

if everythingIsFine:
    note = """Checkstyle has been run on this commit in [job %s](%s/builds/%s).
    *No issues. Good job*
    """ % (BID, URL, BID)
else:
    note = """Checkstyle has been run on this commit in [job %s](%s/builds/%s).

It found the following issues:
%s

Its report can be [downloaded here](%s/-/jobs/%s/artifacts/raw/report.txt).  
*Please* resolve as many issues as possible before merging the code back into the master branch.  
You can produce a report locally by executing `key/key/scripts/tools/checkstyle/runIncrementalCheckstyle.sh` in your local repository
""" % (BID, URL, BID,
       r2s("ERROR messages", report['ERROR'], red=True) + 
       r2s("warning messages", report['WARN']) +
       r2s("info messages", report['INFO']),
       URL, BID)

print(note)

import requests
reportUrl = "%s/api/v4/projects/%s/repository/commits/%s/comments" % (SERVER,PID,SHA)
print("Send report to", reportUrl)
resp = requests.post(reportUrl, data={ b'private_token': TOKEN, b'note':note })
print(note)
sys.exit(int(bool(report["ERROR"])))
