#!/bin/bash

# The first argument is the timeout duration in seconds
# if it is a number
TIMEOUT_SECONDS="$1"
if ! [[ "$TIMEOUT_SECONDS" =~ ^[0-9]+$ ]]; then
    TIMEOUT_SECONDS=0
else
    shift # Removes the first argument, so $@ now contains the original arguments for twee
fi

# start a new neuralcoder/twee container for each run
RUN_CMD="docker run --rm -i neuralcoder/twee:latest"

# Execute 'twee' inside the container, but wrapped with the 'timeout' command.
if [ "$TIMEOUT_SECONDS" -eq 0 ]; then
    # If timeout is 0, run without timeout
    exec time $RUN_CMD twee "$@"
else
    OUTER_TIMEOUT_SECONDS=$((TIMEOUT_SECONDS + 1))
    exec time $RUN_CMD timeout "$OUTER_TIMEOUT_SECONDS" twee "$@" --max-time "$TIMEOUT_SECONDS"
fi

# ./twee.sh [1] - < file.p