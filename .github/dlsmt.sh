# No shebang!

## Weigl's little helper to download SMT-solvers.
# SPDX-License-Identifier: GPL-2.0-or-later

# This script is meant to be executed inside an Github Action to download the SMT-solver. 
# It uses the Github cli tool "gh", which allows an easy access to the releases of a
# repository, and to download it artifacts. 
#
# This script will always the latest uploaded artifact.
#
#
# For performance, you should consider caching. This script skips downloading if files are present.


## Github workflow commands
#  Please have a look at https://docs.github.com/en/actions/using-workflows/workflow-commands-for-github-actions
#  which explains a lot of workflow commands and special files in Github Actions. 


## TODO 
# It would be nice to convert it into a real! Github action, which can also exploit 
# the API library of Github. A manual/tutorial is here:
#
# https://docs.github.com/en/actions/creating-actions/developing-a-third-party-cli-action

mkdir smt-solvers
cd smt-solvers

set -x # exit on error

#################################################
echo "::group::{install z3}"
echo "Check for Z3, if present skip installation"

if readlink -f */bin/z3; then 
  echo "::notice::{Z3 found. Caching works! Skip installation}"
else 
  echo "Download Z3"
  rm z3-*.zip
  # gh release download --skip-existing -p 'z3-*-x64-glibc-2.35.zip' -R Z3Prover/z3
  ## pin to a release
  wget -q https://github.com/Z3Prover/z3/releases/download/z3-4.13.0/z3-4.13.0-x64-glibc-2.35.zip
  unzip -n z3*.zip
  rm z3-*-x64-glibc-*.zip  
fi

Z3=$(readlink -f */bin/z3)
chmod u+x $Z3
echo "Z3 added to path: $Z3"
echo $(dirname $Z3) >> $GITHUB_PATH

echo "::endgroup::"
#################################################

#################################################
echo "::group::{install cvc5}"
if -f cvc5-Linux-static/bin/cvc5; then
  echo "::notice::{CVC5 found. Caching works! Skip installation}"
else 
  echo "Install CVC5"
  # does not work anymore
  # gh release download --skip-existing -p 'cvc5-Linux' -R cvc5/cvc5

  wget -q https://github.com/cvc5/cvc5/releases/download/cvc5-1.1.2/cvc5-Linux-static.zip
  unzip cvc5-Linux-static.zip
  rm cvc5-Linux-static.zip
fi 

CVC5=$(readlink -f cvc5-Linux-static/bin/cvc5)
echo "CVC5 installed and added to path: CVC5"
chmod u+x $CVC5
echo $(dirname $CVC5) >> $GITHUB_PATH

echo "::endgroup::"
#################################################

echo "::group::{check installation/versions}"
$Z3 --version

$CVC5 --version
echo "::endgroup::"
