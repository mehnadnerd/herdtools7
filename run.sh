#!/bin/bash
_build/install/default/bin/herd7 -set-libdir herd/libdir -show cond -cat herd/libdir/riscv.cat -o out -conf catalogue/riscv/cfgs/finalproj.cfg $1 #catalogue/riscv/tests/zicondallow.litmus 
# -through invalid