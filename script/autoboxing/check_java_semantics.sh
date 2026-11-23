#!/usr/bin/env bash
#
# Compiles and runs the autoboxing corpus with javac/java 21 and compares the
# observed behaviour against the committed expectations.
#
# Corpus layout (key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus):
#   cases.tsv                 one row per case: id<TAB>kind<TAB>class<TAB>method
#   <id>/<Class>.java         valid Java 21, also loadable by KeY
#   <id>/expected.txt         exact stdout, or a single line "THROWS <exception>"
#
# Exit status is non-zero if any case fails to compile or deviates.

set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
CORPUS="$ROOT/key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

fail=0
count=0

while IFS=$'\t' read -r caseId kind class method; do
    [ -z "${caseId:-}" ] && continue
    case "$caseId" in \#*) continue ;; esac
    count=$((count + 1))

    src="$CORPUS/$caseId/$class.java"
    outDir="$TMP/$caseId"
    mkdir -p "$outDir"

    if ! javac --release 21 -d "$outDir" "$src" >"$TMP/$caseId.compile.log" 2>&1; then
        echo "FAIL $caseId (compile)"
        sed 's/^/    /' "$TMP/$caseId.compile.log"
        fail=1
        continue
    fi

    stdout="$TMP/$caseId.stdout"
    stderr="$TMP/$caseId.stderr"
    java -cp "$outDir" "$class" >"$stdout" 2>"$stderr"
    status=$?

    expectedFile="$CORPUS/$caseId/expected.txt"
    if [ ! -f "$expectedFile" ]; then
        echo "FAIL $caseId (missing expected.txt)"
        fail=1
        continue
    fi

    first="$(head -n 1 "$expectedFile")"
    case "$first" in
        THROWS\ *)
            exception="${first#THROWS }"
            if [ "$status" -ne 0 ] && grep -q "$exception" "$stderr"; then
                echo "PASS $caseId ($kind, throws $exception)"
            else
                echo "FAIL $caseId (expected $exception, exit status $status)"
                sed 's/^/    /' "$stderr"
                fail=1
            fi
            ;;
        *)
            if [ "$status" -ne 0 ]; then
                echo "FAIL $caseId (unexpected exit status $status)"
                sed 's/^/    /' "$stderr"
                fail=1
            elif diff -u "$expectedFile" "$stdout" >"$TMP/$caseId.diff"; then
                echo "PASS $caseId ($kind)"
            else
                echo "FAIL $caseId (output mismatch)"
                sed 's/^/    /' "$TMP/$caseId.diff"
                fail=1
            fi
            ;;
    esac
done < "$CORPUS/cases.tsv"

echo "$count case(s) checked"
exit "$fail"
