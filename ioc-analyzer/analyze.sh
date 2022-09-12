#!/bin/bash

set -e # stop straight away if any command fails

function usage {
    echo "usage: $0 <command> .../path/to/therapyControl/opIOC [arg [...]]" 1>&2
    echo "(see Main.hs for a list of commands)" 1>&2
    exit 2
}

cmd="$1"
iocdir="$2"
if [[ ! -d "$iocdir" ]]; then
    usage
fi
shift 2

# This pushd/pwd/popd trick gives us an absolute path, where dirname alone
# would give us a relative one.
code_dir="$(pushd "$(dirname "$0")" >/dev/null && pwd && popd >/dev/null)"
cd "$iocdir"
exec "$code_dir/Main" "$cmd" "$@" <iocBoot/iocisoconsole/st.cmd
