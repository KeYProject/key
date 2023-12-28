#!/usr/bin/python3

import sys
import re

REGEX = re.compile(r'\\proofObligation\s*"(.*?)";', re.DOTALL)

def replace(matcher):
    orig = matcher.group(1)
    translated = ""
    for line in orig.split("\n"):
        if line == "": continue
        if line.startswith("#"): continue
        k,v = line.split("=", 1)
        v = v.replace(r'\\','')

        if not(v == 'false' or v == 'true'):
            v = f'"{v}"'

        translated += f"\t\"{k}\": {v},\n"
    return '\\proofObligation {\n%s }' % translated


def rewrite(filename):
    with open(filename) as fh:
        text = fh.read()

    with open(f"{filename}.orig", 'w') as fh:
        fh.write(text)

    new_text = REGEX.sub(replace, text, 1)
    print(new_text)

    with open(filename, 'w') as fh:
        fh.write(new_text)

if __name__=="__main__":
    for a in sys.argv[1:]:
        rewrite(a)
