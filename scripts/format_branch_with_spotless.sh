#!/usr/bin/env bash

# Script for reformatting a whole branch to avoid unnecessary complicated intermediate commits.
# https://stackoverflow.com/questions/1885525/how-do-i-prompt-a-user-for-confirmation-in-bash-script

FIRST_COMMIT=$(git rev-list --ancestry-path origin/main..HEAD | tail -n 1)

read -p "Reformat every commit from $FIRST_COMMIT to HEAD " -n 1 -r
echo    # (optional) move to a new line
if [[ $REPLY =~ ^[Yy]$ ]]
then
  git filter-branch --tree-filter 'gradle --parallel spotlessApply' -- $FIRST_COMMIT..HEAD
fi

