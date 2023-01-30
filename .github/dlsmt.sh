#!/usr/bin/sh

# https://docs.github.com/en/actions/creating-actions/developing-a-third-party-cli-action
#

echo "Install Z3"
mkdir smt-solvers
cd smt-solvers

gh release download --skip-existing -p 'z3-*-x64-glibc-*.zip' -R Z3Prover/z3
unzip -n z3*.zip

Z3=$(readlink -f */bin/z3)
chmod u+x $Z3
echo "Z3 installed and added to path: $Z3"
echo $(dirname $Z3) >> $GITHUB_PATH


echo "Install CVC5"
gh release download --skip-existing -p 'cvc5-Linux' -R cvc5/cvc5
CVC5=$(readlink -f cvc5-Linux)
chmod u+x $CVC5
echo "CVC5 installed and added to path: CVC5"
echo $(dirname $CVC5) >> $GITHUB_PATH

echo "Check installation!"

$Z3 --version

$CVC5 --version
