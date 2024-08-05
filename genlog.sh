#!/bin/bash
if [ $# -eq 0 ]; then
    >&2 echo "No arguments provided. Specify an integer argument n for the number of headers to be verified"
    exit 1
fi

echo "Generating logs for verifying ${1} headers."
command time -v --output=./logs/arecibo_time_output_${1}.txt ./target/release/examples/validate_btc_headers scripts/headers_100000.txt $1 > ./logs/arecibo_output_${1}.txt
echo "See logs directory for output files"
