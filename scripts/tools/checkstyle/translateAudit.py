#!/usr/bin/python3

import sys
import os
import re
import json

from hashlib import sha224

# workflow:
#  - runIncrementalCheckstyle.sh | tee report.txt
#  - publishAudit.py report.txt

# The original was written in perl and is available under publishAudit.pl

# Written by Alexander Weigl
# Refactored in May 2018, by Mattias Ulbrich

def getenv(*args):
    "relaxed access to environment"
    return map(lambda x: os.environ.get(x, ""), args)


                
REGEX = re.compile(r'\[(?P<level>.*?)\] (?P<path>.*\/(?P<file>.*?)):(?P<line>\d+)(:\d+)?: (?P<msg>.*)')

#info, minor, major, blocker,critical
LEVEL_TO_SEVERITY = {
    'INFO': 'info', 
    'WARN': 'minor',
    'ERROR': 'major'
}

def main(filename):
    with open(filename) as raw:
        statistics = {'ERROR':0, 'WARN':0, 'INFO':0}
        reports = list()

        for line in raw:
            m = REGEX.match(line)
            if m:
                old = statistics[m.group('level')]
                statistics[m.group('level')] = old + 1

                fingerprint = sha224(line.encode()).hexdigest()
                
                #see https://docs.gitlab.com/ee/user/project/merge_requests/code_quality.html#implementing-a-custom-tool
                entry = {
                    'description':  m.group('msg'),
                    'fingerprint': fingerprint,
                    'severity': LEVEL_TO_SEVERITY[m.group('level')],
                    'location.path': os.path.join(m.group('path'),m.group('file')),
                    'location.lines.begin': m.group('line')
                }
                reports.append(entry)

        json.dump(reports, sys.stdout, indent=4)
        
        everythingIsFine = statistics['ERROR'] > 0 or statistics['WARN'] > 0

        sys.exit(statistics["ERROR"])
        
######################################################
if __name__=='__main__':
    main(sys.argv[1])
    


