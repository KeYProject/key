#!/usr/bin/env sh

## This file reformats each commit in a branch using "git rebase".
##
## If you are are unsure, you can of course apply on a copy.
##
## Branch should be linear, i.e. free of merges.
##
## https://stackoverflow.com/questions/76945493/how-do-i-format-all-commits-in-a-branch

git rebase \
  --strategy-option=theirs \
  --exec 'gradle --parallel spotlessApply; git add --update; git commit --amend --no-edit' \
  $1 
