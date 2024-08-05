#!/bin/bash
if [ $# -lt 2 ]; then
    >&2 echo "Not enough arguments provided. Specify two integers, the first is the number of headers to be verified per step and the second is the number of steps"
    exit 1
fi

echo "Generating logs for ${2} steps each verifying ${1} headers."
command time -v --output=./logs/arecibo_time_output_${1}_${2}.txt ./target/release/examples/validate_btc_header_batch scripts/headers_100000.txt $1 $2 > ./logs/arecibo_output_${1}_${2}.txt
echo "See logs directory for output files"
