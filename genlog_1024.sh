#!/bin/bash

SLEEP=60s

for i in {0..7}
do
    HDRS_PER_STEP=$(echo "2 ^ $i" | bc)
    NUM_STEPS=$(echo "2^ (10 - $i)" | bc)
    if [ $HDRS_PER_STEP -ne 1 ]; then
        S="s"
    else
        S="" 
    fi
    echo "Generating logs for ${NUM_STEPS} steps with ${HDRS_PER_STEP} header${S} per step."
    command time -v --output=./logs/arecibo_time_output_${HDRS_PER_STEP}_${NUM_STEPS}.txt ./target/release/examples/validate_btc_header_batch scripts/headers_100000.txt $HDRS_PER_STEP $NUM_STEPS > ./logs/arecibo_output_${HDRS_PER_STEP}_${NUM_STEPS}.txt
    if [ $i -ne 7 ]; then
        echo "Sleeping for 60 seconds to give the CPU a break"
        sleep $SLEEP
    fi
done
echo "See logs directory for output files"
