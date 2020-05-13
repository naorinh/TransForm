#!/bin/bash
if [ -z $3 ]; then
  echo "Usage: ./perturb.sh <file> <scope bound> <tests>"
  exec /bin/false
fi

TESTSFILE=$1
DEDUPLICATER="./deduplicate.py"
TIMESTAMP=`date +'%Y%m%d-%H%M%S'`
ALLOYPATH=.
#echo "# Tests file: $TESTSFILE"

time java $JAVAFLAGS -classpath $ALLOYPATH:$ALLOYPATH/alloy4.2.jar MainClass -f $TESTSFILE -b ${@:2} | $DEDUPLICATER $TIMESTAMP-$3-$2
