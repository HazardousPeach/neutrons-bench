#!/bin/sh
set -e
set -x
curl -LO https://gforge.inria.fr/frs/download.php/file/35430/flocq-2.5.1.tar.gz
tar -xf flocq-2.5.1.tar.gz
cd flocq-2.5.1
./configure
./remake
