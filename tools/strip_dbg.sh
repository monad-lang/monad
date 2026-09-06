#!/bin/sh
# Strip everything --debug adds to an .ll, leaving only what the compiler
# DECIDED. What survives here must be byte-identical to a non-debug build:
# any difference is a location wrapper that changed a compiler decision, not
# just an annotation.
#
#   1. the trailing metadata block, and the blank line emit_module puts
#      before it ("\n; === Debug Info ===\n")
#   2. `, !dbg !N` on instructions and ` !dbg !N` on `define` lines
sed -e '/^; === Debug Info ===$/,$d' \
    -e 's/,[[:space:]]*!dbg ![0-9]\{1,\}//g' \
    -e 's/[[:space:]]*!dbg ![0-9]\{1,\}//g' "$1" \
  | awk 'BEGIN{n=0} {lines[n++]=$0} END{while(n>0 && lines[n-1]=="") n--; for(i=0;i<n;i++) print lines[i]}'
