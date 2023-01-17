#!/usr/bin/python3

import sys
import os
import re
import urllib
import json
import pprint
import requests


HOST = "https://git.key-project.org/api/v4"
URL = os.environ["CI_PROJECT_URL"]
PROJECT_ID = os.environ["CI_PROJECT_ID"]
MR_IID = os.environ["CI_MERGE_REQUEST_IID"]
TOKEN = os.environ["CI_COMMENT_TOKEN"]

note = "SonarQube analysis was triggered.  The [:beetle: results will appear on SonarCloud](https://sonarcloud.io/dashboard?id=key-main&pullRequest=%s) soon." % MR_IID


def isSonarQubeComment(obj):
    return obj['body'].startswith("SonarQube analysis was triggered.")

checkUrl = "%s/projects/%s/merge_requests/%s/notes" % (HOST, PROJECT_ID, MR_IID)
print("Check For Hint at: ", checkUrl)
resp = requests.get(checkUrl, headers={"Private-Token": TOKEN})

if resp.status_code != 200:
    print(resp.content)
    sys.exit(0)

notesOnMr = resp.json()


print("Founds %s comments" % len(notesOnMr))
print("Check for comment on SonarQube.")

if not any(map(isSonarQubeComment, notesOnMr)):
    reportUrl = "%s/projects/%s/merge_requests/%s/notes"% (HOST, PROJECT_ID, MR_IID)
    print("Send report to", reportUrl)
    resp = requests.post(reportUrl, data={ b'private_token': TOKEN, b'body': note })

    if resp.status_code >=400:
        sys.exit(1)
