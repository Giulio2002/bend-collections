#!/bin/zsh
# Dev helper: check a templated proof module together with instance checks.
# usage: tools/dev/inst_check.sh proofs/<id>/<module>.bend instances.bend
src=$1; inst=$2
out=build/scratch/_inst_$(basename $src)
sed -e 's#import \.\./lib/#import ../../proofs/lib/#; s#import \./#import ../../'"$(dirname $src)"'/#' $src > $out
cat $inst >> $out
bend $out
