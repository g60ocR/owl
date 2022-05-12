#!/bin/sh

echo '(lambda (x) 42)' | $@ --mode plain -o tmp/a.fasl
$@ -e '(vector->file (list->vector (fasl-encode (lambda (x) 42))) "tmp/b.fasl")'

cmp tmp/a.fasl tmp/b.fasl

rm tmp/[ab].fasl
