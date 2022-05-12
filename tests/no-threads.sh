#!/bin/sh

: ${CC:="gcc"}

LISP="tmp/bare-$$.scm"
FASL="tmp/bare-$$.fasl"
C="tmp/bare-$$.c"
OBJ="tmp/bare-$$"

echo '(lambda (args) 42)' > $LISP # <- to be dumped as such, so program exits with return value 42

# check that all compile silently and produce equal code
$@ --run $LISP   # interpret and run
RINT=$?
echo "interpret: $RINT"

$@ --mode plain -o $FASL $LISP
$@ --load $FASL
RFASL=$?
echo "fasl: $RFASL"

$@ --mode plain -o $C $LISP
$CC -o $OBJ $C 2>/dev/null
$OBJ
RBIN=$?
echo "binary: $RBIN"

# don't remove files if there were differences in return values
test "$RBIN" = "$RFASL" && test "$RFASL" = "$RINT" || exit 1

rm $LISP $FASL $C $OBJ

