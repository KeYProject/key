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


#################################################
echo "::group::{install z3}"
echo "Check for Z3, if present skip installation"

if readlink -f */bin/z3; then 
  echo "::notice::{Z3 found. Caching works! Skip installation}"
else 
  echo "Download Z3"
  gh release download --skip-existing -p 'z3-*-x64-glibc-*.zip' -R Z3Prover/z3
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
if -f cvc5-Linux; then 
  echo "::notice::{Z3 found. Caching works! Skip installation}"
else 
  echo "Install CVC5"
  gh release download --skip-existing -p 'cvc5-Linux' -R cvc5/cvc5  
fi 

CVC5=$(readlink -f cvc5-Linux)
echo "CVC5 installed and added to path: CVC5"
chmod u+x $CVC5
echo $(dirname $CVC5) >> $GITHUB_PATH

echo "::endgroup::"
#################################################

echo "::group::{check installation/versions}"
$Z3 --version

$CVC5 --version
echo "::endgroup::"
