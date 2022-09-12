#!/bin/bash

iocdir="$1"
exec "$(dirname "$0")"/analyze.sh summarize "$iocdir" | \
    grep '^[^ ]' | sed -e 's/ .*//' | sort | uniq -c | sort -nr
