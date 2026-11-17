#!/usr/bin/env bash
# Runs every Matched/Replaced pair of this example with `java` (single-file source launch)
# and compares the visible results (stdout and exit status).
set -u
here=$(cd "$(dirname "$0")" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
fail=0
for dir in "$here"/case-*/; do
    name=$(basename "$dir")
    ( cd "$dir" && java Matched.java > "$out/matched" 2>&1; echo "exit=$?" >> "$out/matched" )
    ( cd "$dir" && java Replaced.java > "$out/replaced" 2>&1; echo "exit=$?" >> "$out/replaced" )
    if diff -u "$out/matched" "$out/replaced" > /dev/null; then
        echo "OK   $name"
    else
        echo "FAIL $name"
        diff -u "$out/matched" "$out/replaced"
        fail=1
    fi
done
exit $fail
