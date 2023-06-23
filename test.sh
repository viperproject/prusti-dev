#!/bin/bash

# ANSI escape codes for colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Initialize or clear the files
> passing.txt
> failing.txt
> panicking.txt

# Initialize counters
passed=0
failed=0
panicked=0

for i in prusti-tests/tests/verify/pass/**/*.rs; do
    echo -n "Testing file: $i"

    # Run the test
    output=$(PRUSTI_FULL_COMPILATION=false target/release/prusti-rustc --edition=2021 $i -Pcheck_overflows=false 2>&1)

    # Check the exit status of the test
    if [ $? -eq 0 ]; then
        # Test passed, append to passing.txt
        echo "$i" >> passing.txt
        echo -e " ...${GREEN}ok${NC}"
        ((passed++))
    else
        # Test failed
        if echo "$output" | grep -q "^thread 'rustc' panicked at"; then
            # There was a panic, append output to panicking.txt
            echo -e "\n---- $i ----\n$output" >> panicking.txt
            echo -e " ...${YELLOW}PANICKED${NC}"
            ((panicked++))
        else
            # Other error, append output to failing.txt
            echo -e "\n---- $i ----\n$output" >> failing.txt
            echo -e " ...${RED}FAILED${NC}"
            ((failed++))
        fi
    fi
done

# Print test statistics
echo -e "${GREEN}$passed tests passed${NC}"
echo -e "${RED}$failed tests failed${NC}"
echo -e "${YELLOW}$panicked tests panicked${NC}"
