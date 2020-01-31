#!/bin/bash -x

# stop on error
set -e

rm -rf build/libs/
(cd ..;
 gradle :keyext.citool:shadowJar --parallel)


cat >build/index.html <<eof
<html>
<head>
<style>body {width:60em; margin:auto;}</style>
<title>ci-tool</title></head>
<body>
eof

markdown2 -x code-friendly -x fenced-code-blocks -x header-ids -x smarty-pants \
          README.md >> build/index.html
#curl https://api.github.com/markdown/raw \
#     -X "POST" -H "Content-Type: text/plain" --data "@README.md"\
#     >> build/index.html
echo "</body></html>" >> build/index.html


rsync -v build/libs/*citool-*-all.jar \
    build/index.html\
    i57adm.ira.uka.de:/misc/HomePages/UserHomePages/i57/weigl/ci-tool/