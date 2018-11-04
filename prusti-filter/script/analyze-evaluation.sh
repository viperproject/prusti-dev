#!/bin/bash

set -uo pipefail

space() { echo ""; }
title() { space; echo -e "${*}"; space; }
inlineinfo() { echo -ne "[-] ${*}: "; }
info() { echo -e "[-] ${*}"; }
error() { echo -e "[!] ${*}"; }

# Get the directory in which this script is contained
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null && pwd )"

# Get the folder in which all the crates has been downloaded
CRATE_DOWNLOAD_DIR="$(cd "${1:-.}" && pwd)"

if [[ ! -d "$CRATE_DOWNLOAD_DIR/000_libc" ]]; then
	echo "It looks like CRATE_DOWNLOAD_DIR is wrong: '$CRATE_DOWNLOAD_DIR'"
	exit 1
fi

title "=== Evaluation ==="

inlineinfo "Start of evaluation"
egrep -ho "\(2018-[^)]+\)" "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | sort | head -n 1

inlineinfo "End of evaluation"
egrep -ho "\(2018-[^)]+\)" "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | sort | tail -n 1

inlineinfo "Crates for which the evaluation is in progress"
for f in "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log; do grep "Summary" $f >/dev/null || echo $f; done | wc -l
for f in "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log; do grep "Summary" $f >/dev/null || echo " - $(basename "$(dirname "$f")")"; done

inlineinfo "Crates for which standard compilation failed or timed out"
cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 42" | wc -l

inlineinfo "Crates for which standard compilation succeeded"
cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep -v "exit status 42" | wc -l

inlineinfo "Crates for which standard compilation succeeded, but the filtering failed"
cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 43" | wc -l
cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 43"

inlineinfo "Crates for which standard compilation and the filtering succeeded"
cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep -v "exit status 42" | grep -v "exit status 43" | wc -l

inlineinfo "Verifiable items from crates for which standard compilation and the filtering succeeded"
echo "$(cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep -v "exit status 42" | grep -v "exit status 43" | sed 's/^.*of \([0-9]*\) in the whitelist.*$/\1/;s/^$/0/' | tr "\n" '+')" 0 | bc

inlineinfo "Crates for which Prusti succeeded"
cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 0" | wc -l

inlineinfo "Verifiable items from crates for which Prusti succeeded"
echo "$(cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 0" | sed 's/^.*of \([0-9]*\) in the whitelist.*$/\1/;s/^$/0/' | tr "\n" '+')" 0 | bc

inlineinfo "Verified items from crates for which Prusti succeeded"
echo "$(cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 0" | sed 's/^.* \([0-9]*\) verified items.*$/\1/;s/^$/0/' | tr "\n" '+')" 0 | bc


inlineinfo "Crates for which Prusti timed out"
cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 124" | wc -l

inlineinfo "Verifiable items from crates for which Prusti timed out"
echo "$(cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 124" | sed 's/^.*of \([0-9]*\) in the whitelist.*$/\1/;s/^$/0/' | tr "\n" '+')" 0 | bc

cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 124"


inlineinfo "Crates for which Prusti failed"
cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep -v "exit status 42" | grep -v "exit status 0" | grep -v "exit status 124" | wc -l

inlineinfo "Verifiable items from crates for which Prusti failed"
echo "$(cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep -v "exit status 42" | grep -v "exit status 0"  | sed 's/^.*of \([0-9]*\) in the whitelist.*$/\1/;s/^$/0/' | tr "\n" '+')" 0 | bc

cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep -v "exit status 42" | grep -v "exit status 0" | grep -v "exit status 124"


#title "=== Legend of exit status ==="
#echo "   42: Standard compilation failed or timed out"
#echo "   43: Automatic filtering failed or timed out"
#echo "    0: Prusti succeeded"
#echo "  124: Prusti timed out"
#echo " else: Prusti failed (bug)"

title "=== Filtering ==="

inlineinfo "Approximate number of functions from all the crates"
egrep '^[[:space:]]*fn[[:space:]]+(.*[^;]$|.*{)' -r "$CRATE_DOWNLOAD_DIR"/*/source/src/ | wc -l

inlineinfo "Number of functions from all the crates"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | .node_path' | wc -l

info "Functions from all the crates: distribution by lines of code"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | .lines_of_code' | sort | uniq -c | sort -k 2 -n | head -n 15
echo "..."
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | .lines_of_code' | sort | uniq -c | sort -k 2 -n | tail -n 3

space

inlineinfo "Number of functions from all the crates that have a reference in the return type"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.procedure.interestings | length > 0) | .node_path' | wc -l

space

inlineinfo "Number of functions from all the crates, excluded macro expansions"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.from_macro_expansion == false) | .node_path' | wc -l

info "Functions from all the crates (excluded macro expansions): distribution by lines of code"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.from_macro_expansion == false) | .lines_of_code' | sort | uniq -c | sort -k 2 -n | head -n 15
echo "..."
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.from_macro_expansion == false) | .lines_of_code' | sort | uniq -c | sort -k 2 -n | tail -n 3

space

inlineinfo "Number of supported functions from all the crates"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.procedure.restrictions | length == 0) | .node_path' | wc -l

inlineinfo "Number of supported functions with loops"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.procedure.restrictions | length == 0) | select(.num_loop_heads > 0) | .node_path' | wc -l

inlineinfo "Number of supported functions that have a reference in the return type"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.procedure.restrictions | length == 0) | select(.procedure.interestings | length > 0) | .node_path' | wc -l

info "Supported functions: distribution by lines of code"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.procedure.restrictions | length == 0)| .lines_of_code' | sort | uniq -c | sort -k 2 -n

info "Supported functions: distribution by number of encoded basic blocks"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.procedure.restrictions | length == 0)| .num_encoded_basic_blocks' | sort | uniq -c | sort -k 2 -n

info "Source code of supported functions with >= 13 lines of code"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.procedure.restrictions | length == 0) | select(.lines_of_code >= 13) | .source_code' | sed 's/^"//;s/"$/\n/;s/\\n/\n/g;s/\\"/"/g;s/\\t/\t/g'

info "Source code of supported functions with >= 12 encoded basic blocks"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.procedure.restrictions | length == 0) | select(.num_encoded_basic_blocks >= 12) | .source_code' | sed 's/^"//;s/"$/\n/;s/\\n/\n/g;s/\\"/"/g;s/\\t/\t/g'

info "Source code of supported functions with a reference in the return type"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.procedure.restrictions | length == 0) | select(.procedure.interestings | length > 0) | .source_code' | sed 's/^"//;s/"$/\n/;s/\\n/\n/g;s/\\"/"/g;s/\\t/\t/g'

space

inlineinfo "Number of supported functions from all the crates (excluded macro expansions)"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.from_macro_expansion == false) | select(.procedure.restrictions | length == 0) | .node_path' | wc -l

info "Supported functions (excluded macro expansions): distribution by lines of code"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.from_macro_expansion == false) | select(.procedure.restrictions | length == 0)| .lines_of_code' | sort | uniq -c | sort -k 2 -n

info "Supported functions (excluded macro expansions): distribution by number of encoded basic blocks"
cat "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json | jq '.functions[] | select(.from_macro_expansion == false) | select(.procedure.restrictions | length == 0)| .num_encoded_basic_blocks' | sort | uniq -c | sort -k 2 -n
