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

inlineinfo "Start of first crate evaluation"
jq --raw-output '.start_date | values' "$CRATE_DOWNLOAD_DIR"/*/report.json | sort | head -n 1

inlineinfo "End of latest crate evaluation"
jq --raw-output '.end_date | values' "$CRATE_DOWNLOAD_DIR"/*/report.json | sort | tail -n 1

inlineinfo "Crates for which the evaluation is in progress"
jq --raw-output 'select(.in_progress) | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | wc -l
jq --raw-output 'select(.in_progress) | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | sed 's/^/ - /'

inlineinfo "Crates for which standard compilation failed or timed out"
jq --raw-output 'select(.exit_status == "42") | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | wc -l

inlineinfo "Crates for which standard compilation succeeded"
jq --raw-output 'select(.exit_status != "42") | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | wc -l

inlineinfo "Crates for which standard compilation succeeded, but the filtering failed"
jq --raw-output 'select(.exit_status == "43") | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | wc -l
jq --raw-output 'select(.exit_status == "43") | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | sed 's/^/ - /'
cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 43"


inlineinfo "Crates for which standard compilation and the filtering succeeded"
jq --raw-output 'select(.exit_status != "42" and .exit_status != "43") | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | wc -l

inlineinfo "Function items from crates for which standard compilation and the filtering succeeded"
(jq '.functions | length' "$CRATE_DOWNLOAD_DIR"/*/source/prusti-filter-results.json 2> /dev/null | tr '\n' '+'; echo "0") | bc

inlineinfo "Verifiable items from crates for which standard compilation and the filtering succeeded"
(jq --raw-output 'select(.exit_status != "42" and .exit_status != "43") | .whitelist_items | values' "$CRATE_DOWNLOAD_DIR"/*/report.json | sed 's/^$/0/' | tr "\n" '+'; echo "0") | bc

inlineinfo "Crates for which Prusti succeeded"
jq --raw-output 'select(.exit_status == "0") | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | wc -l

inlineinfo "Verifiable items from crates for which Prusti succeeded"
(jq --raw-output 'select(.exit_status == "0") | .whitelist_items | values' "$CRATE_DOWNLOAD_DIR"/*/report.json | sed 's/^$/0/' | tr "\n" '+'; echo "0") | bc

inlineinfo "Verified items from crates for which Prusti succeeded"
(jq --raw-output 'select(.exit_status == "0") | .verified_items | values' "$CRATE_DOWNLOAD_DIR"/*/report.json | sed 's/^$/0/' | tr "\n" '+'; echo "0") | bc

inlineinfo "Successfully verified items"
(jq --raw-output '.successful_items | values' "$CRATE_DOWNLOAD_DIR"/*/report.json | sed 's/^$/0/' | tr "\n" '+'; echo "0") | bc


inlineinfo "Crates for which Prusti timed out"
jq --raw-output 'select(.exit_status == "124") | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | wc -l

inlineinfo "Verifiable items from crates for which Prusti timed out"
(jq --raw-output 'select(.exit_status == "124") | .whitelist_items | values' "$CRATE_DOWNLOAD_DIR"/*/report.json | sed 's/^$/0/' | tr "\n" '+'; echo "0") | bc

cat "$CRATE_DOWNLOAD_DIR"/*/evaluate-crate.log | grep Summary | grep "exit status 124"


inlineinfo "Crates for which Prusti failed"
jq --raw-output 'select(.exit_status != null and .exit_status != "42" and .exit_status != "0" and .exit_status != "124") | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | wc -l

inlineinfo "Verifiable items from crates for which Prusti failed"
(jq --raw-output 'select(.exit_status != null and .exit_status != "42" and .exit_status != "0" and .exit_status != "124") | .whitelist_items | values' "$CRATE_DOWNLOAD_DIR"/*/report.json | sed 's/^$/0/' | tr "\n" '+'; echo "0") | bc

jq --raw-output 'select(.exit_status != null and .exit_status != "42" and .exit_status != "0" and .exit_status != "124") | .crate_name' "$CRATE_DOWNLOAD_DIR"/*/report.json | sed 's/^/ - /'
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
