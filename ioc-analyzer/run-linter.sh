#!/bin/bash

# This is the exact script used to produce the broken links table in our
# FSE paper.

# This might be better as an awk script, but my awk-fu is lacking...

function abspath {
  pushd "$1" >/dev/null && pwd && popd >/dev/null
}

DIR="$(abspath "$(dirname "$0")")"

./analyze.sh lint ../therapyControl/opIOC "$DIR/ca-records.txt" | {

  CA=0
  OUT=0
  INP=0

  while read line; do
    echo "$line"
    if grep -q "^Missing channel access annotation" <<<"$line"; then
      let CA=CA+1
    else
      FIELD="$(python -c "import sys,re; print(re.search(r'\.([^\.]+) links to', sys.stdin.read()).group(1))" <<<"$line")"
      case "$FIELD" in
        INP*) let INP=INP+1 ;;
        OUT*) let OUT=OUT+1 ;;
        *) echo "UNKNOWN FIELD: $FIELD" ;;
      esac
    fi
  done

  echo "---------------------------------------------------------------"
  echo "# unmarked channel access links:   $CA"
  echo "# broken input links:              $INP"
  echo "# broken output links:             $OUT"

}
