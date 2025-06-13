#!/usr/bin/python

import sys
import xml.etree.ElementTree as ET
from pathlib import Path


def main():
  path = Path(r".") # path to the root dir from where you want to start searching

  for t in path.glob("**/TEST-*xml"):
    print(t)
    tree = ET.parse(t)
    root = tree.getroot()

    for c in root:
      failure = c.find("failure") # failure in test case
      if failure is not None:
	# ::error file={name},line={line},endLine={endLine},title={title}::{message}
        case_name = c.attrib['name']
        classname = c.attrib['classname']
        message = failure.attrib['message'][0:80]
        print(f"::error title=Testcase-missed,file={classname}::Error in test case '{case_name}' and {message}")

if __name__=='__main__': main()
