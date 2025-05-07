import «ProjetoConformance».ConformanceTests


------------------------------

def memoryadd :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progadd : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 2
add32 %r0, 1
add32 %r0, %r1
add32 %r0, %r0
add32 %r0, -3
exit
result
0x3
}

--#eval exeConformanceCompareResult progadd memoryadd
--#eval exeConformanceDebug progadd memoryadd


------------------------------------------------------------

def memoryadd64 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progadd64 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
mov %r1, 2
add %r0, 1
add %r0, %r1
add %r0, %r0
add %r0, -3
exit
result
0x3
}

-- #eval exeConformanceCompareResult progadd64 memoryadd64
-- #eval exeConformanceDebug progadd64 memoryadd64


------------------------------------------------------------

def memoryalu_arith :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progalu_arith : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 10
sub32 %r0, %r0
mov32 %r1, 1
mov32 %r2, 2
mov32 %r3, 3
mov32 %r4, 4
mov32 %r5, 5
mov32 %r6, 6
mov32 %r7, 7
mov32 %r8, 8
mov32 %r9, 9
jne %r0, 0, exit
add32 %r0, 23
add32 %r0, %r7
jne %r0, 30, exit
sub32 %r0, 13
sub32 %r0, %r1
jne %r0, 16, exit
mul32 %r0, 7
mul32 %r0, %r3
jne %r0, 336, exit
div32 %r0, 2
div32 %r0, %r4
jne %r0, 42, exit
exit
result
0x2a
}

--#eval exeConformanceCompareResult progalu_arith memoryalu_arith
--#eval exeConformanceDebug progalu_arith memoryalu_arith


------------------------------------------------------------

def memoryalu_bit :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progalu_bit : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 1
mov32 %r2, 2
mov32 %r3, 3
mov32 %r4, 4
mov32 %r5, 5
mov32 %r6, 6
mov32 %r7, 7
mov32 %r8, 8
jne %r0, 0, exit
or32 %r0, %r5
or32 %r0, 0xa0
or32 %r0, %r0 -- 165
jne %r0, 0xa5, exit
and32 %r0, 0xa3
mov32 %r9, 0x91
and32 %r0, %r9
and32 %r0, %r0
jne %r0, 0x81, exit --129
lsh32 %r0, 22
lsh32 %r0, %r8
jne %r0, 0x40000000, exit
rsh32 %r0, 19
rsh32 %r0, %r7
jne %r0, 0x10, exit
xor32 %r0, 0x03
xor32 %r0, %r2
exit
result
0x11
}

--#eval exeConformanceCompareResult progalu_bit memoryalu_bit
--#eval exeConformanceDebug progalu_bit memoryalu_bit

------------------------------------------------------------

def memoryalu64_arith :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progalu64_arith : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 10
sub %r0, %r0
mov %r1, 1
mov %r2, 2
mov %r3, 3
mov %r4, 4
mov %r5, 5
mov %r6, 6
mov %r7, 7
mov %r8, 8
mov %r9, 9
jne %r0, 0, exit
add %r0, 23
add %r0, %r7
jne %r0, 30, exit
sub %r0, 13
sub %r0, %r1
jne %r0, 16, exit
mul %r0, 7
mul %r0, %r3
jne %r0, 336, exit
div %r0, 2
div %r0, %r4
exit
result
0x2a
}

-- #eval exeConformanceCompareResult progalu64_arith memoryalu64_arith
-- #eval exeConformanceDebug progalu64_arith memoryalu64_arith


------------------------------------------------------------

def memoryalu64_bit :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progalu64_bit : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
mov %r1, 1
mov %r2, 2
mov %r3, 3
mov %r4, 4
mov %r5, 5
mov %r6, 6
mov %r7, 7
mov %r8, 8
jne %r0, 0, exit
or %r0, %r5
or %r0, 0xa0
or %r0, %r0
jne %r0, 0xa5, exit
and %r0, 0xa3
mov %r9, 0x91
and %r0, %r9
and %r0, %r0
jne %r0, 0x81, exit
lsh %r0, 32
lsh %r0, 22
lsh %r0, %r8
rsh %r0, 32
rsh %r0, 19
rsh %r0, %r7
jne %r0, 0x10, exit
xor %r0, 0x03
xor %r0, %r2
exit
result
0x11
}

-- #eval exeConformanceCompareResult progalu64_bit memoryalu64_bit
-- #eval exeConformanceDebug progalu64_bit memoryalu64_bit


------------------------------------------------------------

def memoryarsh32_imm_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh32_imm_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0xf8
lsh32 %r0, 28
arsh32 %r0, 48
exit
result
0xffff8000
}

-- #eval exeConformanceCompareResult progarsh32_imm_high memoryarsh32_imm_high
-- #eval exeConformanceDebug progarsh32_imm_high memoryarsh32_imm_high

------------------------------------------------------------

def memoryarsh32_imm_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh32_imm_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0xf8
lsh32 %r0, 28
arsh32 %r0, -16
exit
result
0xffff8000
}

-- #eval exeConformanceCompareResult progarsh32_imm_neg memoryarsh32_imm_neg
-- #eval exeConformanceDebug progarsh32_imm_neg memoryarsh32_imm_neg


------------------------------------------------------------

def memoryarsh32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0xf8
lsh32 %r0, 28
arsh32 %r0, 16
exit
result
0xffff8000
}

-- #eval exeConformanceCompareResult progarsh32_imm memoryarsh32_imm
-- #eval exeConformanceDebug progarsh32_imm memoryarsh32_imm


------------------------------------------------------------

def memoryarsh32_reg_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh32_reg_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0xf8
mov32 %r1, 48
lsh32 %r0, 28
arsh32 %r0, %r1
exit
result
0xffff8000
}

-- #eval exeConformanceCompareResult progarsh32_reg_high memoryarsh32_reg_high
-- #eval exeConformanceDebug progarsh32_reg_high memoryarsh32_reg_high


------------------------------------------------------------

def memoryarsh32_reg_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh32_reg_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0xf8
mov32 %r1, -16
lsh32 %r0, 28
arsh32 %r0, %r1
exit
result
0xffff8000
}

-- #eval exeConformanceCompareResult progarsh32_reg_neg memoryarsh32_reg_neg
-- #eval exeConformanceDebug progarsh32_reg_neg memoryarsh32_reg_neg


------------------------------------------------------------

def memoryarsh32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0xf8
mov32 %r1, 16
lsh32 %r0, 28
arsh32 %r0, %r1
exit
result
0xffff8000
}

-- #eval exeConformanceCompareResult progarsh32_reg memoryarsh32_reg
-- #eval exeConformanceDebug progarsh32_reg memoryarsh32_reg


------------------------------------------------------------

def memoryarsh64_imm_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh64_imm_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
lsh %r0, 63
arsh %r0, 124
exit
result
0xfffffffffffffff8
}


-- #eval exeConformanceCompareResult progarsh64_imm_high memoryarsh64_imm_high
-- #eval exeConformanceDebug progarsh64_imm_high memoryarsh64_imm_high

------------------------------------------------------------

def memoryarsh64_imm_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh64_imm_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
lsh %r0, 63
arsh %r0, -4
exit
result
0xfffffffffffffff8
}

-- #eval exeConformanceCompareResult progarsh64_imm_neg memoryarsh64_imm_neg
-- #eval exeConformanceDebug progarsh64_imm_neg memoryarsh64_imm_neg


------------------------------------------------------------

def memoryarsh64_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh64_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
lsh %r0, 63
arsh %r0, 60
exit
result
0xfffffffffffffff8
}

-- #eval exeConformanceCompareResult progarsh64_imm memoryarsh64_imm
-- #eval exeConformanceDebug progarsh64_imm memoryarsh64_imm


------------------------------------------------------------

def memoryarsh64_reg_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh64_reg_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
lsh %r0, 63
mov32 %r1, 124
arsh %r0, %r1
exit
result
0xfffffffffffffff8
}

-- #eval exeConformanceCompareResult progarsh64_reg_high memoryarsh64_reg_high
-- #eval exeConformanceDebug progarsh64_reg_high memoryarsh64_reg_high


------------------------------------------------------------

def memoryarsh64_reg_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh64_reg_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
lsh %r0, 63
mov32 %r1, -4
arsh %r0, %r1
exit
result
0xfffffffffffffff8
}

-- #eval exeConformanceCompareResult progarsh64_reg_neg memoryarsh64_reg_neg
-- #eval exeConformanceDebug progarsh64_reg_neg memoryarsh64_reg_neg


------------------------------------------------------------

def memoryarsh64_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progarsh64_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
lsh %r0, 63
mov32 %r1, 60
arsh %r0, %r1
exit
result
0xfffffffffffffff8
}

-- #eval exeConformanceCompareResult progarsh64_reg memoryarsh64_reg
-- #eval exeConformanceDebug progarsh64_reg memoryarsh64_reg


------------------------------------------------------------

def memorybe16_high :=
    createStackMemory 0 emptyMemory
{mem|
'1' '1' '2' '2' '3' '3' '4' '4' '5' '5' '6' '6' '7' '7' '8' '8' }

def progbe16_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
be16 %r0
exit
result
0x1122
}

-- #eval exeConformanceCompareResult progbe16_high memorybe16_high
-- #eval exeConformanceDebug progbe16_high memorybe16_high

------------------------------------------------------------

def memorybe16 :=
    createStackMemory 0 emptyMemory
{mem|
'1' '1' '2' '2' }

def progbe16 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxh %r0, [%r1]
be16 %r0
exit
result
0x1122
}

-- #eval exeConformanceCompareResult progbe16 memorybe16
-- #eval exeConformanceDebug progbe16 memorybe16

------------------------------------------------------------

def memorybe32_high :=
    createStackMemory 0 emptyMemory
{mem|
'1' '1' '2' '2' '3' '3' '4' '4' '5' '5' '6' '6' '7' '7' '8' '8' }

def progbe32_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
ldxdw %r1, [%r1]
be32 %r0
exit
result
0x11223344
}

-- #eval exeConformanceCompareResult progbe32_high memorybe32_high
-- #eval exeConformanceDebug progbe32_high memorybe32_high

------------------------------------------------------------

def memorybe32 :=
    createStackMemory 0 emptyMemory
{mem|
'1' '1' '2' '2' '3' '3' '4' '4' }

def progbe32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxw %r0, [%r1]
be32 %r0
exit
result
0x11223344
}

-- #eval exeConformanceCompareResult progbe32 memorybe32
-- #eval exeConformanceDebug progbe32 memorybe32


------------------------------------------------------------

def memorybe64 :=
    createStackMemory 0 emptyMemory
{mem|
'1' '1' '2' '2' '3' '3' '4' '4' '5' '5' '6' '6' '7' '7' '8' '8' }

def progbe64 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
be64 %r0
exit
result
0x1122334455667788
}

-- #eval exeConformanceCompareResult progbe64 memorybe64
-- #eval exeConformanceDebug progbe64 memorybe64

------------------------------------------------------------

def memorycallx :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progcallx : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r1, -1
mov %r2, 5
call %r2
mov %r0, 2
exit
result
0x2
}

-- #eval exeConformanceCompareResult progcallx memorycallx
-- #eval exeConformanceDebug progcallx memorycallx


------------------------------------------------------------

def memorycall_local :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progcall_local : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
mov %r1, 1
mov %r2, 2
mov %r3, 3
mov %r4, 4
mov %r5, 5
mov %r6, 6
mov %r7, 7
mov %r8, 8
mov %r9, 9
call_local 10
jne %r0, 15, 6
jne %r6, 6, 5
jne %r7, 7, 4
jne %r8, 8, 3
jne %r9, 9, 2
mov %r0, 1
exit
mov %r0, -1
exit
mov %r0, 0
add %r0, %r1
add %r0, %r2
add %r0, %r3
add %r0, %r4
add %r0, %r5
mov %r6, 0
mov %r7, 0
mov %r8, 0
mov %r9, 0
exit
result
0x1
}

-- #eval exeConformanceCompareResult progcall_local memorycall_local
-- #eval exeConformanceDebug progcall_local memorycall_local


------------------------------------------------------------

def memorycall_unwind_fail :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progcall_unwind_fail : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r1, -1
--call 5
mov %r0, 2
exit
result
0x2
}

-- #eval exeConformanceCompareResult progcall_unwind_fail memorycall_unwind_fail
-- #eval exeConformanceDebug progcall_unwind_fail memorycall_unwind_fail


------------------------------------------------------------

def memorydiv32_zero_reg_2 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv32_zero_reg_2 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
lddw %r1, 0x100000000
div32 %r0, %r1
exit
result
0x0
}

-- #eval exeConformanceCompareResult progdiv32_zero_reg_2 memorydiv32_zero_reg_2
-- #eval exeConformanceDebug progdiv32_zero_reg_2 memorydiv32_zero_reg_2


------------------------------------------------------------

def memorydiv32_zero_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv32_zero_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
mov32 %r1, 0
div32 %r0, %r1
exit
result
0x0
}

-- #eval exeConformanceCompareResult progdiv32_zero_reg memorydiv32_zero_reg
-- #eval exeConformanceDebug progdiv32_zero_reg memorydiv32_zero_reg


------------------------------------------------------------

def memorydiv32_high_divisor :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv32_high_divisor : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 12
lddw %r1, 0x100000004
div32 %r0, %r1
exit
result
0x3
}

-- #eval exeConformanceCompareResult progdiv32_high_divisor memorydiv32_high_divisor
-- #eval exeConformanceDebug progdiv32_high_divisor memorydiv32_high_divisor

------------------------------------------------------------

def memorydiv32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x10000000c
div32 %r0, 4
exit
result
0x3
}

-- #eval exeConformanceCompareResult progdiv32_imm memorydiv32_imm
-- #eval exeConformanceDebug progdiv32_imm memorydiv32_imm


------------------------------------------------------------

def memorydiv32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x10000000c
mov %r1, 4
div32 %r0, %r1
exit
result
0x3
}

-- #eval exeConformanceCompareResult progdiv32_reg memorydiv32_reg
-- #eval exeConformanceDebug progdiv32_reg memorydiv32_reg


------------------------------------------------------------

def memorydiv64_zero_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv64_zero_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
mov32 %r1, 0
div %r0, %r1
exit
result
0x0
}

-- #eval exeConformanceCompareResult progdiv64_zero_reg memorydiv64_zero_reg
-- #eval exeConformanceDebug progdiv64_zero_reg memorydiv64_zero_reg


------------------------------------------------------------

def memorydiv64_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv64_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0xc
lsh %r0, 32
div %r0, 4
exit
result
0x300000000
}

-- #eval exeConformanceCompareResult progdiv64_imm memorydiv64_imm
-- #eval exeConformanceDebug progdiv64_imm memorydiv64_imm


------------------------------------------------------------

def memorydiv64_negative_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv64_negative_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0xFFFFFFFFFFFFFFFF
div %r0, -10
exit
result
0x1
}

-- #eval exeConformanceCompareResult progdiv64_negative_imm memorydiv64_negative_imm
-- #eval exeConformanceDebug progdiv64_negative_imm memorydiv64_negative_imm


------------------------------------------------------------

def memorydiv64_negative_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv64_negative_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0xFFFFFFFFFFFFFFFF
mov32 %r1, -10
div %r0, %r1
exit
result
0x10000000A
}

-- #eval exeConformanceCompareResult progdiv64_negative_reg memorydiv64_negative_reg
-- #eval exeConformanceDebug progdiv64_negative_reg memorydiv64_negative_reg


------------------------------------------------------------

def memorydiv64_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progdiv64_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0xc
lsh %r0, 32
mov %r1, 4
div %r0, %r1
exit
result
0x300000000
}

-- #eval exeConformanceCompareResult progdiv64_reg memorydiv64_reg
-- #eval exeConformanceDebug progdiv64_reg memorydiv64_reg


------------------------------------------------------------

def memoryexit_not_last :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progexit_not_last : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r1, 0
ja 3
mov %r2, 0
exit
mov %r0, 0
ja -6
result
0x0
}

-- #eval exeConformanceCompareResult progexit_not_last memoryexit_not_last
-- #eval exeConformanceDebug progexit_not_last memoryexit_not_last


------------------------------------------------------------

def memoryexit :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progexit : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult progexit memoryexit
-- #eval exeConformanceDebug progexit memoryexit

------------------------------------------------------------

def memoryj_signed_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progj_signed_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 2
lddw %r1, 0xFFFFFFFF80000000
jeq %r1, 0x80000000, +1
exit
lddw %r1, 0xFFFFFFFF80000000
jlt %r1, 0x80000001, +1
exit
lddw %r1, 0xFFFFFFFF80000001
jgt %r1, 0x80000000, +1
exit
lddw %r1, 0x80000000
jne %r1, 0x80000000, +1
exit
lddw %r1, 0xFFFFFFFF00000000
jset %r1, 0x80000000, +1
exit
mov32 %r0, 1
exit
result
0x1
}

 #eval exeConformanceCompareResult progj_signed_imm memoryj_signed_imm
-- #eval exeConformanceDebug progj_signed_imm memoryj_signed_imm

#eval (evalSigned 0xFFFFFFFF80000000 64) == 0x80000000                           -- jeq
#eval (evalSigned 0xFFFFFFFF80000000 64) == (evalSigned 0x80000000 64)           -- jeq
#eval (evalSigned 0xFFFFFFFF80000000 64) == (makeSigned 0x80000000 32)           -- jeq
#eval 0xFFFFFFFF80000000 == (makeSigned 0x80000000 64)           -- jeq
#eval (evalSigned 0xFFFFFFFF80000000 64) < 0x80000001                            -- jlt
#eval (evalSigned 0xFFFFFFFF80000000 64) < (evalSigned 0x80000001 64)            -- jlt
#eval (evalSigned 0xFFFFFFFF80000000 64) < (makeSigned 0x80000001 32)            -- jlt
#eval 0xFFFFFFFF80000000 < (makeSigned 0x80000001 64)            -- jlt
#eval (evalSigned 0xFFFFFFFF80000001 64) > 0x80000000                            -- jgt
#eval (evalSigned 0xFFFFFFFF80000001 64) > (evalSigned 0x80000000 64)            -- jgt
#eval (evalSigned 0xFFFFFFFF80000001 64) > (makeSigned 0x80000000 64)            -- jgt
#eval (evalSigned 0x80000000 64) != 0x80000000                                   -- jne
#eval (evalSigned 0x80000000 64) != (evalSigned 0x80000000 64)                   -- jne
#eval (evalSigned 0x80000000 64) != (makeSigned 0x80000000 32)                   -- jne
#eval (andLogical (evalSigned 0xFFFFFFFF00000000 64) 0x80000000) != 0                    -- Jset
#eval (andLogical (evalSigned 0xFFFFFFFF00000000 64) (evalSigned 0x80000000 64)) != 0    -- Jset
#eval (andLogical (evalSigned 0xFFFFFFFF00000000 64) (makeSigned 0x80000000 32)) != 0    -- Jset
#eval andLogical 0xFFFFFFFF00000000 0x80000000

#eval (makeSigned 0x80000001 64)
#eval 0xFFFFFFFF80000000
#eval natToBin 0xFFFFFFFF80000001
#eval evalSigned 0xFFFFFFFF80000001 64
#eval returnSigned 0xFFFFFFFF80000001 64
#eval makeSigned 0x80000000 32
#eval evalSigned 0x80000000 32

#eval evalSigned 0xFFFFFFFF80000001 64
#eval 0x80000000

#eval (natToBin 0x80000000).length

#eval andLogical (evalSigned 0xFFFFFFFF00000000 64) 5
#eval (evalSigned 0xFFFFFFFF00000000 64)
#eval 0x80000000
#eval (natToBin 0xFFFFFFFF80000000).length
#eval (natToBin 0x80000001).length
#eval (natToBin 0xFFFFFFFF80000001)
#eval (returnSigned 0xFFFFFFFF80000000 64)
#eval (returnSigned 0xFFFFFFFF80000001 64)
#eval 0x80000000
#eval (natToBin 0x80000001)
#eval 0xFFFFFFFF80000000
#eval 0x80000001

#eval (evalSigned 0x80000000 64)

#eval evalSigned 0x80000000 32
#eval evalSigned 0xFFFFFFFF00000000 0

#eval natToBin (evalSigned 0x80000000 32)
#eval natToBin (evalSigned 0xFFFFFFFF00000000 32)
#eval (natToBin 0xFFFFFFFF00000000).length
#eval (natToBin (evalSigned 0xFFFFFFFF00000000 32)).length

#eval (natToBin 0xFFFFFFFF00000000)
#eval (natToBin 0x80000000)
#eval (natToBin 0xFFFFFFFF00000000).length
#eval (natToBin 0x80000000).length
------------------------------------------------------------

def memoryja32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progja32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r1, 0
ja32 3
mov %r2, 0
exit
mov %r0, 0
ja32 -6
result
0x0
}

-- #eval exeConformanceCompareResult progja32 memoryja32
-- #eval exeConformanceDebug progja32 memoryja32


------------------------------------------------------------

def memoryjeq_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjeq_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 0xa
jeq %r1, 0xb, exit
mov32 %r0, 1
mov32 %r1, 0xb
jeq %r1, 0xb, exit
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjeq_imm memoryjeq_imm
-- #eval exeConformanceDebug progjeq_imm memoryjeq_imm


------------------------------------------------------------

def memoryjeq_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjeq_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 0xa
mov32 %r2, 0xb
jeq %r1, %r2, exit
jeq %r1, %r1, +1
exit
mov32 %r0, 1
mov32 %r1, 0xb
jeq %r1, %r2, exit
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjeq_reg memoryjeq_reg
-- #eval exeConformanceDebug progjeq_reg memoryjeq_reg


------------------------------------------------------------

def memoryjeq32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjeq32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0x0
mov32 %r1, 0xa
jeq32 %r1, 0xb, exit
mov32 %r0, 1
mov %r1, 0xb
or %r1, %r9
jeq32 %r1, 0xb, exit
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjeq32_imm memoryjeq32_imm
-- #eval exeConformanceDebug progjeq32_imm memoryjeq32_imm


------------------------------------------------------------

def memoryjeq32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjeq32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xa
mov32 %r2, 0xb
jeq32 %r1, %r2, exit
jeq32 %r1, %r1, +1
exit
mov32 %r0, 1
mov32 %r1, 0xb
or %r1, %r9
jeq32 %r1, %r2, exit
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjeq32_reg memoryjeq32_reg
-- #eval exeConformanceDebug progjeq32_reg memoryjeq32_reg


------------------------------------------------------------

def memoryjge_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjge_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 0xa
jge %r1, 0xb, exit
mov32 %r0, 1
mov32 %r1, 0xc
jge %r1, 0xb, exit
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjge_imm memoryjge_imm
-- #eval exeConformanceDebug progjge_imm memoryjge_imm


------------------------------------------------------------

def memoryjge_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjge_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 0xa
mov32 %r2, 0x0b
jge %r1, %r2, exit
jge %r1, %r1, +1
exit
mov32 %r0, 1
mov32 %r1, 0xc
jge %r1, %r2, exit
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjge_reg memoryjge_reg
-- #eval exeConformanceDebug progjge_reg memoryjge_reg


------------------------------------------------------------

def memoryjge32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjge32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xa
jge32 %r1, 0xb, exit
mov32 %r0, 1
mov32 %r1, 0xc
or %r1, %r9
jge32 %r1, 0xb, exit
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjge32_imm memoryjge32_imm
-- #eval exeConformanceDebug progjge32_imm memoryjge32_imm


------------------------------------------------------------

def memoryjge32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjge32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xa
mov32 %r2, 0xb
jge32 %r1, %r2, exit
jge32 %r1, %r1, +1
exit
mov32 %r0, 1
mov32 %r1, 0xc
or %r1, %r9
jge32 %r1, %r2, exit
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjge32_reg memoryjge32_reg
-- #eval exeConformanceDebug progjge32_reg memoryjge32_reg


------------------------------------------------------------

def memoryjgt_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjgt_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 5
jgt %r1, 6, exit
jgt %r1, 5, exit
jgt %r1, 4, 1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjgt_imm memoryjgt_imm
-- #eval exeConformanceDebug progjgt_imm memoryjgt_imm


------------------------------------------------------------

def memoryjgt_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjgt_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
mov %r1, 5
mov %r2, 6
mov %r3, 4
jgt %r1, %r2, exit
jgt %r1, %r1, exit
jgt %r1, %r3, 1
exit
mov %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjgt_reg memoryjgt_reg
-- #eval exeConformanceDebug progjgt_reg memoryjgt_reg


------------------------------------------------------------

def memoryjgt32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjgt32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 5
or %r1, %r9
jgt32 %r1, 6, exit
jgt32 %r1, 5, exit
jgt32 %r1, 4, 1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjgt32_imm memoryjgt32_imm
-- #eval exeConformanceDebug progjgt32_imm memoryjgt32_imm


------------------------------------------------------------

def memoryjgt32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjgt32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov %r0, 0
mov %r1, 5
mov32 %r1, 5
or %r1, %r9
mov %r2, 6
mov %r3, 4
jgt32 %r1, %r2, exit
jgt32 %r1, %r1, exit
jgt32 %r1, %r3, 1
exit
mov %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjgt32_reg memoryjgt32_reg
-- #eval exeConformanceDebug progjgt32_reg memoryjgt32_reg


------------------------------------------------------------

def memoryjit_bounce :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjit_bounce : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 1
mov %r6, %r0
mov %r7, %r6
mov %r8, %r7
mov %r9, %r8
mov %r0, %r9
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjit_bounce memoryjit_bounce
-- #eval exeConformanceDebug progjit_bounce memoryjit_bounce


------------------------------------------------------------

def memoryjle_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjle_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 5
jle %r1, 4, exit
jle %r1, 6, +1
exit
jle %r1, 5, +1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjle_imm memoryjle_imm
-- #eval exeConformanceDebug progjle_imm memoryjle_imm


------------------------------------------------------------

def memoryjle_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjle_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
mov %r1, 5
mov %r2, 4
mov %r3, 6
jle %r1, %r2, exit
jle %r1, %r1, +1
exit
jle %r1, %r3, +1
exit
mov %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjle_reg memoryjle_reg
-- #eval exeConformanceDebug progjle_reg memoryjle_reg


------------------------------------------------------------

def memoryjle32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjle32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 5
or %r1, %r9
jle32 %r1, 4, exit
jle32 %r1, 6, +1
exit
jle32 %r1, 5, +1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjle32_imm memoryjle32_imm
-- #eval exeConformanceDebug progjle32_imm memoryjle32_imm


------------------------------------------------------------

def memoryjle32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjle32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov %r0, 0
mov %r1, 5
mov %r2, 4
mov %r3, 6
or %r1, %r9
jle32 %r1, %r2, exit
jle32 %r1, %r1, +1
exit
jle32 %r1, %r3, +1
exit
mov %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjle32_reg memoryjle32_reg
-- #eval exeConformanceDebug progjle32_reg memoryjle32_reg


------------------------------------------------------------

def memoryjlt_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjlt_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 5
jlt %r1, 4, exit
jlt %r1, 5, exit
jlt %r1, 6, +1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjlt_imm memoryjlt_imm
-- #eval exeConformanceDebug progjlt_imm memoryjlt_imm


------------------------------------------------------------

def memoryjlt_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjlt_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
mov %r1, 5
mov %r2, 4
mov %r3, 6
jlt %r1, %r2, exit
jlt %r1, %r1, exit
jlt %r1, %r3, +1
exit
mov %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjlt_reg memoryjlt_reg
-- #eval exeConformanceDebug progjlt_reg memoryjlt_reg


------------------------------------------------------------

def memoryjlt32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjlt32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 5
or %r1, %r9
jlt32 %r1, 4, exit
jlt32 %r1, 5, exit
jlt32 %r1, 6, +1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjlt32_imm memoryjlt32_imm
-- #eval exeConformanceDebug progjlt32_imm memoryjlt32_imm


------------------------------------------------------------

def memoryjlt32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjlt32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov %r0, 0
mov %r1, 5
mov %r2, 4
mov %r3, 6
or %r1, %r9
jlt32 %r1, %r2, exit
jlt32 %r1, %r1, exit
jlt32 %r1, %r3, +1
exit
mov %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjlt32_reg memoryjlt32_reg
-- #eval exeConformanceDebug progjlt32_reg memoryjlt32_reg


------------------------------------------------------------

def memoryjne_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjne_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 0xb
mov32 %r2, 0xb
jne %r1, %r2, exit
jne %r1, %r1, exit
mov32 %r0, 1
mov32 %r1, 0xa
jne %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjne_reg memoryjne_reg
-- #eval exeConformanceDebug progjne_reg memoryjne_reg


------------------------------------------------------------

def memoryjne32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjne32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xb
or %r1, %r9
jne32 %r1, 0xb, +4
mov32 %r0, 1
mov32 %r1, 0xa
or %r1, %r9
jne32 %r1, 0xb, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjne32_imm memoryjne32_imm
-- #eval exeConformanceDebug progjne32_imm memoryjne32_imm


------------------------------------------------------------

def memoryjne32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjne32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xb
or %r1, %r9
mov32 %r2, 0xb
jne32 %r1, %r2, +5
jne32 %r1, %r1, +4
mov32 %r0, 1
mov32 %r1, 0xa
or %r1, %r9
jne32 %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjne32_reg memoryjne32_reg
-- #eval exeConformanceDebug progjne32_reg memoryjne32_reg


------------------------------------------------------------

def memoryjset_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjset_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 0x7
jset %r1, 0x8, exit
mov32 %r0, 1
mov32 %r1, 0x9
jset %r1, 0x8, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjset_imm memoryjset_imm
-- #eval exeConformanceDebug progjset_imm memoryjset_imm

------------------------------------------------------------

def memoryjset_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjset_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 0x7
mov32 %r2, 0x8
jset %r1, %r2, exit
jset %r1, %r1, +1
exit
mov32 %r0, 1
mov32 %r1, 0x9
jset %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjset_reg memoryjset_reg
-- #eval exeConformanceDebug progjset_reg memoryjset_reg


------------------------------------------------------------

def memoryjset32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjset32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0x7
or %r1, %r9
jset32 %r1, 0x8, exit
mov32 %r0, 1
mov32 %r1, 0x9
jset32 %r1, 0x8, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjset32_imm memoryjset32_imm
-- #eval exeConformanceDebug progjset32_imm memoryjset32_imm


------------------------------------------------------------

def memoryjset32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjset32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0x7
or %r1, %r9
mov32 %r2, 0x8
jset32 %r1, %r2, exit
jset32 %r1, %r1, +1
exit
mov32 %r0, 1
mov32 %r1, 0x9
jset32 %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjset32_reg memoryjset32_reg
-- #eval exeConformanceDebug progjset32_reg memoryjset32_reg


------------------------------------------------------------

def memoryjsge_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsge_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov %r1, 0xfffffffe
jsge %r1, 0xffffffff, exit
jsge %r1, 0, +4
mov32 %r0, 1
mov %r1, 0xffffffff
jsge %r1, 0xffffffff, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsge_imm memoryjsge_imm
-- #eval exeConformanceDebug progjsge_imm memoryjsge_imm


------------------------------------------------------------

def memoryjsge_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsge_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov %r1, 0xfffffffe
mov %r2, 0xffffffff
mov32 %r3, 0
jsge %r1, %r2, exit
jsge %r1, %r3, exit
jsge %r1, %r1, +1
exit
mov32 %r0, 1
mov %r1, %r2
jsge %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsge_reg memoryjsge_reg
-- #eval exeConformanceDebug progjsge_reg memoryjsge_reg


------------------------------------------------------------

def memoryjsge32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsge32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xfffffffe
or %r1, %r9
jsge32 %r1, 0xffffffff, exit
jsge32 %r1, 0, exit
mov32 %r0, 1
mov %r1, 0xffffffff
jsge32 %r1, 0xffffffff, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsge32_imm memoryjsge32_imm
-- #eval exeConformanceDebug progjsge32_imm memoryjsge32_imm


------------------------------------------------------------

def memoryjsge32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsge32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xfffffffe
or %r1, %r9
mov %r2, 0xffffffff
mov32 %r3, 0
jsge32 %r1, %r2, exit
jsge32 %r1, %r3, exit
jsge32 %r1, %r1, +1
exit
mov32 %r0, 1
mov %r1, %r2
jsge32 %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsge32_reg memoryjsge32_reg
-- #eval exeConformanceDebug progjsge32_reg memoryjsge32_reg


------------------------------------------------------------

def memoryjsgt_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsgt_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov %r1, 0xfffffffe
jsgt %r1, 0xffffffff, exit
mov32 %r0, 1
mov32 %r1, 0
jsgt %r1, 0xffffffff, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsgt_imm memoryjsgt_imm
-- #eval exeConformanceDebug progjsgt_imm memoryjsgt_imm


------------------------------------------------------------

def memoryjsgt_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsgt_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov %r1, 0xfffffffe
mov %r2, 0xffffffff
jsgt %r1, %r2, exit
jsgt %r1, %r1, exit
mov32 %r0, 1
mov32 %r1, 0
jsgt %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}


-- #eval exeConformanceCompareResult progjsgt_reg memoryjsgt_reg
-- #eval exeConformanceDebug progjsgt_reg memoryjsgt_reg


------------------------------------------------------------

def memoryjsgt32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsgt32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xfffffffe
or %r1, %r9
jsgt32 %r1, 0xffffffff, exit
mov32 %r0, 1
mov32 %r1, 0
jsgt32 %r1, 0xffffffff, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsgt32_imm memoryjsgt32_imm
-- #eval exeConformanceDebug progjsgt32_imm memoryjsgt32_imm


------------------------------------------------------------

def memoryjsgt32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsgt32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xfffffffe
or %r1, %r9
mov %r2, 0xffffffff
jsgt32 %r1, %r2, exit
jsgt32 %r1, %r1, exit
mov32 %r0, 1
mov32 %r1, 0
jsgt32 %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsgt32_reg memoryjsgt32_reg
-- #eval exeConformanceDebug progjsgt32_reg memoryjsgt32_reg


------------------------------------------------------------

def memoryjsle_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsle_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov %r1, 0xfffffffe
jsle %r1, 0xfffffffd, exit
jsle %r1, 0xffffffff, +1
exit
mov32 %r0, 1
jsle %r1, 0xfffffffe, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsle_imm memoryjsle_imm
-- #eval exeConformanceDebug progjsle_imm memoryjsle_imm


------------------------------------------------------------

def memoryjsle_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsle_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov %r1, 0xffffffff
mov %r2, 0xfffffffe
mov32 %r3, 0
jsle %r1, %r2, exit
jsle %r1, %r3, +1
exit
jsle %r1, %r1, +1
exit
mov32 %r0, 1
mov %r1, %r2
jsle %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsle_reg memoryjsle_reg
-- #eval exeConformanceDebug progjsle_reg memoryjsle_reg


------------------------------------------------------------

def memoryjsle32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsle32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xfffffffe
or %r1, %r9
jsle32 %r1, 0xfffffffd, exit
jsle32 %r1, 0xffffffff, +1
exit
mov32 %r0, 1
jsle32 %r1, 0xfffffffe, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsle32_imm memoryjsle32_imm
-- #eval exeConformanceDebug progjsle32_imm memoryjsle32_imm


------------------------------------------------------------

def memoryjsle32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjsle32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xffffffff
or %r1, %r9
mov %r2, 0xfffffffe
mov32 %r3, 0
jsle32 %r1, %r2, exit
jsle32 %r1, %r3, +1
exit
jsle32 %r1, %r1, +1
exit
mov32 %r0, 1
mov %r1, %r2
jsle32 %r1, %r2, +1
mov32 %r0, 2
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjsle32_reg memoryjsle32_reg
-- #eval exeConformanceDebug progjsle32_reg memoryjsle32_reg


------------------------------------------------------------

def memoryjslt_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjslt_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov %r1, 0xfffffffe
jslt %r1, 0xfffffffd, exit
jslt %r1, 0xfffffffe, exit
jslt %r1, 0xffffffff, +1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjslt_imm memoryjslt_imm
-- #eval exeConformanceDebug progjslt_imm memoryjslt_imm


------------------------------------------------------------

def memoryjslt_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjslt_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov %r1, 0xfffffffe
mov %r2, 0xfffffffd
mov %r3, 0xffffffff
jslt %r1, %r1, exit
jslt %r1, %r2, exit
jslt %r1, %r3, +1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjslt_reg memoryjslt_reg
-- #eval exeConformanceDebug progjslt_reg memoryjslt_reg


------------------------------------------------------------

def memoryjslt32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjslt32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xfffffffe
or %r1, %r9
jslt32 %r1, 0xfffffffd, exit
jslt32 %r1, 0xfffffffe, exit
jslt32 %r1, 0xffffffff, +1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjslt32_imm memoryjslt32_imm
-- #eval exeConformanceDebug progjslt32_imm memoryjslt32_imm


------------------------------------------------------------

def memoryjslt32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progjslt32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r9, 1
lsh %r9, 32
mov32 %r0, 0
mov32 %r1, 0xfffffffe
or %r1, %r9
mov %r2, 0xfffffffd
mov %r3, 0xffffffff
jslt32 %r1, %r1, exit
jslt32 %r1, %r2, exit
jslt32 %r1, %r3, +1
exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progjslt32_reg memoryjslt32_reg
-- #eval exeConformanceDebug progjslt32_reg memoryjslt32_reg


------------------------------------------------------------

def memorylddw :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglddw : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x1122334455667788
exit
result
0x1122334455667788
}

-- #eval exeConformanceCompareResult proglddw memorylddw
-- #eval exeConformanceDebug proglddw memorylddw


------------------------------------------------------------

def memorylddw2 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglddw2 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 2147483648
exit
result
0x0000000080000000
}

-- #eval exeConformanceCompareResult proglddw2 memorylddw2
-- #eval exeConformanceDebug proglddw2 memorylddw2


------------------------------------------------------------

def memoryldxb_all :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '1' '0' '2' '0' '3' '0' '4' '0' '5' '0' '6' '0' '7' '0' '8' '0' '9' }

def progldxb_all : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, %r1
ldxb %r9, [%r0+0]
lsh %r9, 0
ldxb %r8, [%r0+0x1]
lsh %r8, 4
ldxb %r7, [%r0+2]
lsh %r7, 8
ldxb %r6, [%r0+3]
lsh %r6, 12
ldxb %r5, [%r0+4]
lsh %r5, 16
ldxb %r4, [%r0+5]
lsh %r4, 20
ldxb %r3, [%r0+6]
lsh %r3, 24
ldxb %r2, [%r0+7]
lsh %r2, 28
ldxb %r1, [%r0+8]
lsh %r1, 32
ldxb %r0, [%r0+9]
lsh %r0, 36
or %r0, %r1
or %r0, %r2
or %r0, %r3
or %r0, %r4
or %r0, %r5
or %r0, %r6
or %r0, %r7
or %r0, %r8
or %r0, %r9
exit
result
0x9876543210
}

-- #eval exeConformanceCompareResult progldxb_all memoryldxb_all
-- #eval exeConformanceDebug progldxb_all memoryldxb_all


------------------------------------------------------------

def memoryldxb :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' '1' '1' 'c' 'c' 'd' 'd' }

def progldxb : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxb %r0, [%r1+0x2]
exit
result
0x11
}

-- #eval exeConformanceCompareResult progldxb memoryldxb
-- #eval exeConformanceDebug progldxb memoryldxb


------------------------------------------------------------

def memoryldxdw :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' '1' '1' '2' '2' '3' '3' '4' '4' '5' '5' '6' '6' '7' '7' '8' '8' 'c' 'c' 'd' 'd' }

def progldxdw : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1+2]
exit
result
0x8877665544332211
}

-- #eval exeConformanceCompareResult progldxdw memoryldxdw
-- #eval exeConformanceDebug progldxdw memoryldxdw


------------------------------------------------------------

def memoryldxh_all :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '1' '0' '0' '0' '2' '0' '0' '0' '3' '0' '0' '0' '4' '0' '0' '0' '5' '0' '0' '0' '6' '0' '0' '0' '7' '0' '0' '0' '8' '0' '0' '0' '9' }

def progldxh_all : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, %r1
ldxh %r9, [%r0+0]
be16 %r9
lsh %r9, 0
ldxh %r8, [%r0+2]
be16 %r8
lsh %r8, 4
ldxh %r7, [%r0+4]
be16 %r7
lsh %r7, 8
ldxh %r6, [%r0+6]
be16 %r6
lsh %r6, 12
ldxh %r5, [%r0+8]
be16 %r5
lsh %r5, 16
ldxh %r4, [%r0+10]
be16 %r4
lsh %r4, 20
ldxh %r3, [%r0+12]
be16 %r3
lsh %r3, 24
ldxh %r2, [%r0+14]
be16 %r2
lsh %r2, 28
ldxh %r1, [%r0+16]
be16 %r1
lsh %r1, 32
ldxh %r0, [%r0+18]
be16 %r0
lsh %r0, 36
or %r0, %r1
or %r0, %r2
or %r0, %r3
or %r0, %r4
or %r0, %r5
or %r0, %r6
or %r0, %r7
or %r0, %r8
or %r0, %r9
exit
result
0x9876543210
}

-- #eval exeConformanceCompareResult progldxh_all memoryldxh_all
-- #eval exeConformanceDebug progldxh_all memoryldxh_all

------------------------------------------------------------

def memoryldxh_all2 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '1'
'0' '0' '0' '2'
'0' '0' '0' '4'
'0' '0' '0' '8'
'0' '0' '1' '0'
'0' '0' '2' '0'
'0' '0' '4' '0'
'0' '0' '8' '0'
'0' '1' '0' '0'
'0' '2' '0' '0' }

def progldxh_all2 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, %r1
ldxh %r9, [%r0+0]
be16 %r9
ldxh %r8, [%r0+2]
be16 %r8
ldxh %r7, [%r0+4]
be16 %r7
ldxh %r6, [%r0+6]
be16 %r6
ldxh %r5, [%r0+8]
be16 %r5
ldxh %r4, [%r0+10]
be16 %r4
ldxh %r3, [%r0+12]
be16 %r3
ldxh %r2, [%r0+14]
be16 %r2
ldxh %r1, [%r0+16]
be16 %r1
ldxh %r0, [%r0+18]
be16 %r0
or %r0, %r1
or %r0, %r2
or %r0, %r3
or %r0, %r4
or %r0, %r5
or %r0, %r6
or %r0, %r7
or %r0, %r8
or %r0, %r9
exit
result
0x3ff
}


-- #eval exeConformanceCompareResult progldxh_all2 memoryldxh_all2
-- #eval exeConformanceDebug progldxh_all2 memoryldxh_all2

------------------------------------------------------------

def memoryldxh_same_reg :=
    createStackMemory 0 emptyMemory
{mem|
'f' 'f' 'f' 'f' }

def progldxh_same_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, %r1
sth [%r0], 0x1234
ldxh %r0, [%r0]
exit
result
0x1234
}

-- #eval exeConformanceCompareResult progldxh_same_reg memoryldxh_same_reg
-- #eval exeConformanceDebug progldxh_same_reg memoryldxh_same_reg


------------------------------------------------------------

def memoryldxh :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' '1' '1' '2' '2' 'c' 'c' 'd' 'd' }

def progldxh : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxh %r0, [%r1+2]
exit
result
0x2211
}

-- #eval exeConformanceCompareResult progldxh memoryldxh
-- #eval exeConformanceDebug progldxh memoryldxh


------------------------------------------------------------

def memoryldxw_all :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '1'
'0' '0' '0' '0' '0' '0' '0' '2'
'0' '0' '0' '0' '0' '0' '0' '4'
'0' '0' '0' '0' '0' '0' '0' '8'
'0' '0' '0' '0' '0' '1' '0' '0'
'0' '0' '0' '0' '0' '2' '0' '0'
'0' '0' '0' '0' '0' '4' '0' '0'
'0' '0' '0' '0' '0' '8' '0' '0'
'0' '0' '0' '1' '0' '0' '0' '0'
'0' '0' '0' '2' '0' '0' '0' '0' }

def progldxw_all : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, %r1
ldxw %r9, [%r0+0]
be32 %r9
ldxw %r8, [%r0+4]
be32 %r8
ldxw %r7, [%r0+8]
be32 %r7
ldxw %r6, [%r0+12]
be32 %r6
ldxw %r5, [%r0+16]
be32 %r5
ldxw %r4, [%r0+20]
be32 %r4
ldxw %r3, [%r0+24]
be32 %r3
ldxw %r2, [%r0+28]
be32 %r2
ldxw %r1, [%r0+32]
be32 %r1
ldxw %r0, [%r0+36]
be32 %r0
or %r0, %r1
or %r0, %r2
or %r0, %r3
or %r0, %r4
or %r0, %r5
or %r0, %r6
or %r0, %r7
or %r0, %r8
or %r0, %r9
exit
result
0x030f0f
}

-- #eval exeConformanceCompareResult progldxw_all memoryldxw_all
-- #eval exeConformanceDebug progldxw_all memoryldxw_all


------------------------------------------------------------

def memoryldxw :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' '1' '1' '2' '2' '3' '3' '4' '4' 'c' 'c' 'd' 'd' }

def progldxw : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxw %r0, [%r1+2]
exit
result
0x44332211
}

-- #eval exeConformanceCompareResult progldxw memoryldxw
-- #eval exeConformanceDebug progldxw memoryldxw


------------------------------------------------------------

def memoryle16_high :=
    createStackMemory 0 emptyMemory
{mem|
'2' '2' '1' '1' '0' '0' 'F' 'F' 'E' 'E' 'D' 'D' 'C' 'C' 'B' 'B' 'A' 'A' }

def progle16_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
le16 %r0
exit
result
0x1122
}

-- #eval exeConformanceCompareResult progle16_high memoryle16_high
-- #eval exeConformanceDebug progle16_high memoryle16_high



------------------------------------------------------------

def memoryle16 :=
    createStackMemory 0 emptyMemory
{mem|
'2' '2' '1' '1' }

def progle16 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxh %r0, [%r1]
le16 %r0
exit
result
0x1122
}

-- #eval exeConformanceCompareResult progle16 memoryle16
-- #eval exeConformanceDebug progle16 memoryle16


------------------------------------------------------------

def memoryle32_high :=
    createStackMemory 0 emptyMemory
{mem|
'4' '4' '3' '3' '2' '2' '1' '1' '0' '0' 'F' 'F' 'E' 'E' 'D' 'D' }

def progle32_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
le32 %r0
exit
result
0x11223344
}

-- #eval exeConformanceCompareResult progle32_high memoryle32_high
-- #eval exeConformanceDebug progle32_high memoryle32_high


------------------------------------------------------------

def memoryle32 :=
    createStackMemory 0 emptyMemory
{mem|
'4' '4' '3' '3' '2' '2' '1' '1' }

def progle32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxw %r0, [%r1]
le32 %r0
exit
result
0x11223344
}

-- #eval exeConformanceCompareResult progle32 memoryle32
-- #eval exeConformanceDebug progle32 memoryle32


------------------------------------------------------------

def memoryle64 :=
    createStackMemory 0 emptyMemory
{mem|
'8' '8' '7' '7' '6' '6' '5' '5' '4' '4' '3' '3' '2' '2' '1' '1' }

def progle64 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
le64 %r0
exit
result
0x1122334455667788
}

-- #eval exeConformanceCompareResult progle64 memoryle64
-- #eval exeConformanceDebug progle64 memoryle64


------------------------------------------------------------

def memorylock_add :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_add : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
mov %r1, 1
lock add [%r10-8], %r1
ldxdw %r1, [%r10-8]
lddw %r0, 0x123456789abcdef1
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_add memorylock_add
-- #eval exeConformanceDebug proglock_add memorylock_add


------------------------------------------------------------

def memorylock_add32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_add32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
mov %r1, 1
lock add32 [%r10-8], %r1
ldxdw %r1, [%r10-8]
lddw %r0, 0x123456789abcdef1
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_add32 memorylock_add32
-- #eval exeConformanceDebug proglock_add32 memorylock_add32


------------------------------------------------------------

def memorylock_and :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_and : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
lddw %r1, 0x00ff00ff00ff00ff
lock and [%r10-8], %r1
ldxdw %r0, [%r10-8]
lddw %r1, 0x0034007800bc00f0
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_and memorylock_and
-- #eval exeConformanceDebug proglock_and memorylock_and


------------------------------------------------------------

def memorylock_and32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_and32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
lddw %r1, 0x00ff00ff00ff00ff
lock and32 [%r10-8], %r1
ldxdw %r0, [%r10-8]
lddw %r1, 0x1234567800bc00f0
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_and32 memorylock_and32
-- #eval exeConformanceDebug proglock_and32 memorylock_and32


------------------------------------------------------------

def memorylock_cmpxchg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_cmpxchg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
lddw %r1, 0x1122334455667788
lddw %r0, 0xfedcba987654321
lock cmpxchg [%r10-8], %r1
lddw %r1, 0x123456789abcdef0
jne %r0, %r1, exit
ldxdw %r0, [%r10-8]
jne %r0, %r1, exit
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
lddw %r1, 0x1122334455667788
lock cmpxchg [%r10-8], %r1
lddw %r1, 0x123456789abcdef0
jne %r0, %r1, exit
ldxdw %r0, [%r10-8]
lddw %r1, 0x1122334455667788
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_cmpxchg memorylock_cmpxchg
-- #eval exeConformanceDebug proglock_cmpxchg memorylock_cmpxchg


------------------------------------------------------------

def memorylock_cmpxchg32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_cmpxchg32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
mov32 %r1, 0x876543210
mov32 %r0, 0x12345678
lock cmpxchg32 [%r10-8], %r1
mov32 %r1, 0x9abcdef0
jne %r0, %r1, exit
ldxdw %r0, [%r10-8]
lddw %r1, 0x123456789abcdef0
jne %r0, %r1, exit
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
mov32 %r1, 0x11223344
lock cmpxchg32 [%r10-8], %r1
mov32 %r1, 0x9abcdef0
jne %r0, %r1, exit
ldxdw %r0, [%r10-8]
lddw %r1, 0x1234567811223344
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_cmpxchg32 memorylock_cmpxchg32
-- #eval exeConformanceDebug proglock_cmpxchg32 memorylock_cmpxchg32


------------------------------------------------------------

def memorylock_fetch_add :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_fetch_add : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
mov %r1, 1
lock fetch add [%r10-8], %r1
jne %r1, %r0, exit
ldxdw %r1, [%r10-8]
lddw %r0, 0x123456789abcdef1
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_fetch_add memorylock_fetch_add
-- #eval exeConformanceDebug proglock_fetch_add memorylock_fetch_add


------------------------------------------------------------

def memorylock_fetch_add32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_fetch_add32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
mov %r1, 1
lock fetch add32 [%r10-8], %r1
jne32 %r1, %r0, exit
ldxdw %r1, [%r10-8]
lddw %r0, 0x123456789abcdef1
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_fetch_add32 memorylock_fetch_add32
-- #eval exeConformanceDebug proglock_fetch_add32 memorylock_fetch_add32


------------------------------------------------------------

def memorylock_fetch_and :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_fetch_and : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
lddw %r1, 0x00ff00ff00ff00ff
lock fetch and [%r10-8], %r1
jne %r1, %r0, exit
ldxdw %r0, [%r10-8]
lddw %r1, 0x0034007800bc00f0
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_fetch_and memorylock_fetch_and
-- #eval exeConformanceDebug proglock_fetch_and memorylock_fetch_and


------------------------------------------------------------

def memorylock_fetch_and32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_fetch_and32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x123456789abcdef0
stxdw [%r10-8], %r0
lddw %r1, 0x00ff00ff00ff00ff
lock fetch and32 [%r10-8], %r1
jne32 %r1, %r0, exit
ldxdw %r0, [%r10-8]
lddw %r1, 0x1234567800bc00f0
jne %r0, %r1, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_fetch_and32 memorylock_fetch_and32
-- #eval exeConformanceDebug proglock_fetch_and32 memorylock_fetch_and32


------------------------------------------------------------

def memorylock_fetch_or :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_fetch_or : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x1100110011001100
lddw %r1, 0x0011001100110011
stxdw [%r10-8], %r0
lock fetch or [%r10-8], %r1
jne %r1, %r0, exit
ldxdw %r0, [%r10-8]
lddw %r1, 0x1111111111111111
jne %r0, %r1, exit
mov %r0, 0
exit
result
0
}

-- #eval exeConformanceCompareResult proglock_fetch_or memorylock_fetch_or
-- #eval exeConformanceDebug proglock_fetch_or memorylock_fetch_or


------------------------------------------------------------

def memorylock_fetch_or32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_fetch_or32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x1100110011001100
lddw %r1, 0x0011001100110011
stxdw [%r10-8], %r0
lock fetch or32 [%r10-8], %r1
jne32 %r1, %r0, exit
ldxdw %r0, [%r10-8]
lddw %r1, 0x1100110011111111
jne %r0, %r1, exit
mov %r0, 0
exit
result
0
}

-- #eval exeConformanceCompareResult proglock_fetch_or32 memorylock_fetch_or32
-- #eval exeConformanceDebug proglock_fetch_or32 memorylock_fetch_or32


------------------------------------------------------------

def memorylock_fetch_xor :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_fetch_xor : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0xcccccccccccccccc
lddw %r1, 0xffffffffffffffff
stxdw [%r10-8], %r0
lock fetch xor [%r10-8], %r1
jne %r1, %r0, exit
ldxdw %r0, [%r10-8]
lddw %r1, 0x3333333333333333
jne %r0, %r1, exit
mov %r0, 0
exit
result
0
}

-- #eval exeConformanceCompareResult proglock_fetch_xor memorylock_fetch_xor
-- #eval exeConformanceDebug proglock_fetch_xor memorylock_fetch_xor


------------------------------------------------------------

def memorylock_fetch_xor32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_fetch_xor32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0xcccccccccccccccc
lddw %r1, 0xffffffffffffffff
stxdw [%r10-8], %r0
lock fetch xor32 [%r10-8], %r1
jne32 %r1, %r0, exit
ldxdw %r0, [%r10-8]
lddw %r1, 0xcccccccc33333333
jne %r0, %r1, exit
mov %r0, 0
exit
result
0
}

-- #eval exeConformanceCompareResult proglock_fetch_xor32 memorylock_fetch_xor32
-- #eval exeConformanceDebug proglock_fetch_xor32 memorylock_fetch_xor32


------------------------------------------------------------

def memorylock_or :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_or : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x1100110011001100
lddw %r1, 0x0011001100110011
stxdw [%r10-8], %r0
lock or [%r10-8], %r1
ldxdw %r0, [%r10-8]
lddw %r1, 0x1111111111111111
jne %r0, %r1, exit
mov %r0, 0
exit
result
0
}

-- #eval exeConformanceCompareResult proglock_or memorylock_or
-- #eval exeConformanceDebug proglock_or memorylock_or


------------------------------------------------------------

def memorylock_or32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_or32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x1100110011001100
lddw %r1, 0x0011001100110011
stxdw [%r10-8], %r0
lock or32 [%r10-8], %r1
ldxdw %r0, [%r10-8]
lddw %r1, 0x1100110011111111
jne %r0, %r1, exit
mov %r0, 0
exit
result
0
}

-- #eval exeConformanceCompareResult proglock_or32 memorylock_or32
-- #eval exeConformanceDebug proglock_or32 memorylock_or32


------------------------------------------------------------

def memorylock_xchg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_xchg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 1
lddw %r1, 0x1111111111111111
stxdw [%r10-8], %r1
lddw %r1, 0x2222222222222222
lock xchg [%r10-8], %r1
ldxdw %r2, [%r10-8]
lddw %r0, 0x2222222222222222
jne %r2, %r0, exit
lddw %r0, 0x1111111111111111
jne %r1, %r0, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_xchg memorylock_xchg
-- #eval exeConformanceDebug proglock_xchg memorylock_xchg


------------------------------------------------------------

def memorylock_xchg32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_xchg32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 1
lddw %r1, 0x1111111111111111
stxdw [%r10-8], %r1
lddw %r1, 0x2222222222222222
lock xchg32 [%r10-8], %r1
ldxdw %r2, [%r10-8]
lddw %r0, 0x1111111122222222
jne %r2, %r0, exit
lddw %r0, 0x11111111
jne %r1, %r0, exit
mov %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult proglock_xchg32 memorylock_xchg32
-- #eval exeConformanceDebug proglock_xchg32 memorylock_xchg32


------------------------------------------------------------

def memorylock_xor :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_xor : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0xcccccccccccccccc
lddw %r1, 0xffffffffffffffff
stxdw [%r10-8], %r0
lock xor [%r10-8], %r1
ldxdw %r0, [%r10-8]
lddw %r1, 0x3333333333333333
jne %r0, %r1, exit
mov %r0, 0
exit
result
0
}

-- #eval exeConformanceCompareResult proglock_xor memorylock_xor
-- #eval exeConformanceDebug proglock_xor memorylock_xor


------------------------------------------------------------

def memorylock_xor32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglock_xor32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0xcccccccccccccccc
lddw %r1, 0xffffffffffffffff
stxdw [%r10-8], %r0
lock xor32 [%r10-8], %r1
ldxdw %r0, [%r10-8]
lddw %r1, 0xcccccccc33333333
jne %r0, %r1, exit
mov %r0, 0
exit
result
0
}

-- #eval exeConformanceCompareResult proglock_xor32 memorylock_xor32
-- #eval exeConformanceDebug proglock_xor32 memorylock_xor32


------------------------------------------------------------

def memorylsh32_imm_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh32_imm_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x11
lsh32 %r0, 60
exit
result
0x10000000
}

-- #eval exeConformanceCompareResult proglsh32_imm_high memorylsh32_imm_high
-- #eval exeConformanceDebug proglsh32_imm_high memorylsh32_imm_high


------------------------------------------------------------

def memorylsh32_imm_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh32_imm_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x11
lsh32 %r0, -4
exit
result
0x10000000
}

-- #eval exeConformanceCompareResult proglsh32_imm_neg memorylsh32_imm_neg
-- #eval exeConformanceDebug proglsh32_imm_neg memorylsh32_imm_neg


------------------------------------------------------------

def memorylsh32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x11
lsh32 %r0, 28
exit
result
0x10000000
}

-- #eval exeConformanceCompareResult proglsh32_imm memorylsh32_imm
-- #eval exeConformanceDebug proglsh32_imm memorylsh32_imm


------------------------------------------------------------

def memorylsh32_reg_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh32_reg_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x11
mov %r7, 60
lsh32 %r0, %r7
exit
result
0x10000000
}

-- #eval exeConformanceCompareResult proglsh32_reg_high memorylsh32_reg_high
-- #eval exeConformanceDebug proglsh32_reg_high memorylsh32_reg_high


------------------------------------------------------------

def memorylsh32_reg_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh32_reg_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x11
mov %r7, -4
lsh32 %r0, %r7
exit
result
0x10000000
}

-- #eval exeConformanceCompareResult proglsh32_reg_neg memorylsh32_reg_neg
-- #eval exeConformanceDebug proglsh32_reg_neg memorylsh32_reg_neg


------------------------------------------------------------

def memorylsh32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x11
mov %r7, 28
lsh32 %r0, %r7
exit
result
0x10000000
}

-- #eval exeConformanceCompareResult proglsh32_reg memorylsh32_reg
-- #eval exeConformanceDebug proglsh32_reg memorylsh32_reg


------------------------------------------------------------

def memorylsh64_imm_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh64_imm_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x1
lsh %r0, 68
exit
result
0x10
}

-- #eval exeConformanceCompareResult proglsh64_imm_high memorylsh64_imm_high
-- #eval exeConformanceDebug proglsh64_imm_high memorylsh64_imm_high


------------------------------------------------------------

def memorylsh64_imm_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh64_imm_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x1
lsh %r0, -60
exit
result
0x10
}

-- #eval exeConformanceCompareResult proglsh64_imm_neg memorylsh64_imm_neg
-- #eval exeConformanceDebug proglsh64_imm_neg memorylsh64_imm_neg


------------------------------------------------------------

def memorylsh64_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh64_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x1
lsh %r0, 4
exit
result
0x10
}

-- #eval exeConformanceCompareResult proglsh64_imm memorylsh64_imm
-- #eval exeConformanceDebug proglsh64_imm memorylsh64_imm


------------------------------------------------------------

def memorylsh64_reg_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh64_reg_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x1
mov %r7, 68
lsh %r0, %r7
exit
result
0x10
}

-- #eval exeConformanceCompareResult proglsh64_reg_high memorylsh64_reg_high
-- #eval exeConformanceDebug proglsh64_reg_high memorylsh64_reg_high


------------------------------------------------------------

def memorylsh64_reg_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh64_reg_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x1
mov %r7, -60
lsh %r0, %r7
exit
result
0x10
}

-- #eval exeConformanceCompareResult proglsh64_reg_neg memorylsh64_reg_neg
-- #eval exeConformanceDebug proglsh64_reg_neg memorylsh64_reg_neg


------------------------------------------------------------

def memorylsh64_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def proglsh64_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x1
mov %r7, 4
lsh %r0, %r7
exit
result
0x10
}

-- #eval exeConformanceCompareResult proglsh64_reg memorylsh64_reg
-- #eval exeConformanceDebug proglsh64_reg memorylsh64_reg


------------------------------------------------------------

def memorymem_len :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '1'
'0' '0' '0' '0' '0' '0' '0' '2' }

def progmem_len : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, %r2
exit
result
0x8
}

 #eval exeConformanceCompareResult progmem_len memorymem_len
 #eval exeConformanceDebug progmem_len memorymem_len

#eval hexToNatList ['0','2'] 0
#eval 0x8

------------------------------------------------------------

def memorymod_zero_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmod_zero_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
mov32 %r1, 0
mod32 %r0, %r1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progmod_zero_reg memorymod_zero_reg
-- #eval exeConformanceDebug progmod_zero_reg memorymod_zero_reg


------------------------------------------------------------

def memorymod :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmod : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 5748
mod32 %r0, 92
jne %r0, 44, exit
mov32 %r1, 13
mod32 %r0, %r1
exit
result
0x5
}

-- #eval exeConformanceCompareResult progmod memorymod
-- #eval exeConformanceDebug progmod memorymod


------------------------------------------------------------

def memorymod32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmod32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x100000003
mod32 %r0, 3
exit
result
0x0
}

-- #eval exeConformanceCompareResult progmod32 memorymod32
-- #eval exeConformanceDebug progmod32 memorymod32


------------------------------------------------------------

def memorymod64_zero_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmod64_zero_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
mov32 %r1, 0
mod %r0, %r1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progmod64_zero_reg memorymod64_zero_reg
-- #eval exeConformanceDebug progmod64_zero_reg memorymod64_zero_reg


------------------------------------------------------------

def memorymod64 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmod64 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0xb1858436
lsh %r0, 32
or %r0, 0x100dc5c8
mov32 %r1, 0xdde263e
lsh %r1, 32
or %r1, 0x3cbef7f3
mod %r0, %r1
mod %r0, 0x658f1778
exit
result
0x30ba5a04
}

-- #eval exeConformanceCompareResult progmod64 memorymod64
-- #eval exeConformanceDebug progmod64 memorymod64


------------------------------------------------------------

def memorymov :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmov : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r1, 2
mov32 %r0, %r1
jne %r0, 2, exit
lddw %r2, 0xFFFFFF00000002
mov32 %r0, %r2
jne %r0, 2, exit
mov32 %r0, 1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progmov memorymov
-- #eval exeConformanceDebug progmov memorymov


------------------------------------------------------------

def memorymov64_sign_extend :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmov64_sign_extend : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, -10
exit
result
0xFFFFFFFFFFFFFFF6
}

-- #eval exeConformanceCompareResult progmov64_sign_extend memorymov64_sign_extend
-- #eval exeConformanceDebug progmov64_sign_extend memorymov64_sign_extend


------------------------------------------------------------

def memorymov64 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmov64 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r1, 1
mov %r0, %r1
mov %r0, %r0
exit
result
0x1
}

-- #eval exeConformanceCompareResult progmov64 memorymov64
-- #eval exeConformanceDebug progmov64 memorymov64


------------------------------------------------------------

def memorymovsx1632_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmovsx1632_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r1, 0x0123456789abcdef
movsx1632 %r0, %r1
exit
result
0xffffcdef
}

-- #eval exeConformanceCompareResult progmovsx1632_reg memorymovsx1632_reg
-- #eval exeConformanceDebug progmovsx1632_reg memorymovsx1632_reg


------------------------------------------------------------

def memorymovsx1664_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmovsx1664_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r1, 0x0123456789abcdef
movsx1664 %r0, %r1
exit
result
0xffffffffffffcdef
}

-- #eval exeConformanceCompareResult progmovsx1664_reg memorymovsx1664_reg
-- #eval exeConformanceDebug progmovsx1664_reg memorymovsx1664_reg


------------------------------------------------------------

def memorymovsx3264_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmovsx3264_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r1, 0x0123456789abcdef
movsx3264 %r0, %r1
exit
result
0xffffffff89abcdef
}

--- #eval exeConformanceCompareResult progmovsx3264_reg memorymovsx3264_reg
-- #eval exeConformanceDebug progmovsx3264_reg memorymovsx3264_reg


------------------------------------------------------------

def memorymovsx832_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmovsx832_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r1, 0x0123456789abcdef
movsx832 %r0, %r1
exit
result
0xffffffef
}

-- #eval exeConformanceCompareResult progmovsx832_reg memorymovsx832_reg
-- #eval exeConformanceDebug progmovsx832_reg memorymovsx832_reg


------------------------------------------------------------

def memorymovsx864_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmovsx864_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r1, 0x0123456789abcdef
movsx864 %r0, %r1
exit
result
0xffffffffffffffef
}

-- #eval exeConformanceCompareResult progmovsx864_reg memorymovsx864_reg
-- #eval exeConformanceDebug progmovsx864_reg memorymovsx864_reg


------------------------------------------------------------

def memorymul32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmul32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 3
mul32 %r0, 4
exit
result
0xc
}

-- #eval exeConformanceCompareResult progmul32_imm memorymul32_imm
-- #eval exeConformanceDebug progmul32_imm memorymul32_imm


------------------------------------------------------------

def memorymul32_intmin_negone_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmul32_intmin_negone_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x80000000
mul32 %r0, -1
exit
result
0x80000000
}

-- #eval exeConformanceCompareResult progmul32_intmin_negone_imm memorymul32_intmin_negone_imm
-- #eval exeConformanceDebug progmul32_intmin_negone_imm memorymul32_intmin_negone_imm


------------------------------------------------------------

def memorymul32_intmin_negone_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmul32_intmin_negone_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x80000000
mov %r1, -1
mul32 %r0, %r1
exit
result
0x80000000
}

-- #eval exeConformanceCompareResult progmul32_intmin_negone_reg memorymul32_intmin_negone_reg
-- #eval exeConformanceDebug progmul32_intmin_negone_reg memorymul32_intmin_negone_reg


------------------------------------------------------------

def memorymul32_reg_overflow :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmul32_reg_overflow : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x40000001
mov %r1, 4
mul32 %r0, %r1
exit
result
0x4
}

-- #eval exeConformanceCompareResult progmul32_reg_overflow memorymul32_reg_overflow
-- #eval exeConformanceDebug progmul32_reg_overflow memorymul32_reg_overflow


------------------------------------------------------------

def memorymul32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmul32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 3
mov %r1, 4
mul32 %r0, %r1
exit
result
0xc
}

-- #eval exeConformanceCompareResult progmul32_reg memorymul32_reg
-- #eval exeConformanceDebug progmul32_reg memorymul32_reg


------------------------------------------------------------

def memorymul64_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmul64_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x40000001
mul %r0, 4
exit
result
0x100000004
}

-- #eval exeConformanceCompareResult progmul64_imm memorymul64_imm
-- #eval exeConformanceDebug progmul64_imm memorymul64_imm


------------------------------------------------------------

def memorymul64_intmin_negone_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '8' '0' }

def progmul64_intmin_negone_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
mul %r0, -1
exit
result
0x8000000000000000
}

-- #eval exeConformanceCompareResult progmul64_intmin_negone_imm memorymul64_intmin_negone_imm
-- #eval exeConformanceDebug progmul64_intmin_negone_imm memorymul64_intmin_negone_imm


------------------------------------------------------------

def memorymul64_intmin_negone_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '8' '0' }

def progmul64_intmin_negone_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
mov %r1, -1
mul %r0, %r1
exit
result
0x8000000000000000
}

-- #eval exeConformanceCompareResult progmul64_intmin_negone_reg memorymul64_intmin_negone_reg
-- #eval exeConformanceDebug progmul64_intmin_negone_reg memorymul64_intmin_negone_reg


------------------------------------------------------------

def memorymul64_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progmul64_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x40000001
mov %r1, 4
mul %r0, %r1
exit
result
0x100000004
}

-- #eval exeConformanceCompareResult progmul64_reg memorymul64_reg
-- #eval exeConformanceDebug progmul64_reg memorymul64_reg


------------------------------------------------------------

def memoryneg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progneg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x100000002
neg32 %r0
exit
result
0xfffffffe
}

-- #eval exeConformanceCompareResult progneg memoryneg
-- #eval exeConformanceDebug progneg memoryneg

------------------------------------------------------------

def memoryneg32_intmin_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progneg32_intmin_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x80000000
neg32 %r0
exit
result
0x80000000
}

-- #eval exeConformanceCompareResult progneg32_intmin_imm memoryneg32_intmin_imm
-- #eval exeConformanceDebug progneg32_intmin_imm memoryneg32_intmin_imm


------------------------------------------------------------

def memoryneg32_intmin_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progneg32_intmin_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x80000000
neg32 %r0
exit
result
0x80000000
}

-- #eval exeConformanceCompareResult progneg32_intmin_reg memoryneg32_intmin_reg
-- #eval exeConformanceDebug progneg32_intmin_reg memoryneg32_intmin_reg


------------------------------------------------------------

def memoryneg64_intmin_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '8' '0' }

def progneg64_intmin_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
neg %r0
exit
result
0x8000000000000000
}

-- #eval exeConformanceCompareResult progneg64_intmin_imm memoryneg64_intmin_imm
-- #eval exeConformanceDebug progneg64_intmin_imm memoryneg64_intmin_imm

------------------------------------------------------------

def memoryneg64_intmin_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '8' '0' }

def progneg64_intmin_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
mov %r1, -1
neg %r0
exit
result
0x8000000000000000
}

-- #eval exeConformanceCompareResult progneg64_intmin_reg memoryneg64_intmin_reg
-- #eval exeConformanceDebug progneg64_intmin_reg memoryneg64_intmin_reg


------------------------------------------------------------

def memoryneg64 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progneg64 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 2
neg %r0
exit
result
0xfffffffffffffffe
}

-- #eval exeConformanceCompareResult progneg64 memoryneg64
-- #eval exeConformanceDebug progneg64 memoryneg64


------------------------------------------------------------

def memoryprime :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progprime : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r1, 67
mov %r0, 0x1
mov %r2, 0x2
jgt %r1, 0x2, 6
ja exit
add %r2, 0x1
mov %r0, 0x1
jge %r2, %r1, exit
mov %r3, %r1
div %r3, %r2
mul %r3, %r2
mov %r4, %r1
sub %r4, %r3
mov %r0, 0x0
jne %r4, 0x0, -12
exit
result
0x1
}

-- #eval exeConformanceCompareResult progprime memoryprime
-- #eval exeConformanceDebug progprime memoryprime


------------------------------------------------------------

def memoryrsh32_imm_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh32_imm_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
sub %r0, 1
rsh32 %r0, 40
exit
result
0x00ffffff
}

-- #eval exeConformanceCompareResult progrsh32_imm_high memoryrsh32_imm_high
-- #eval exeConformanceDebug progrsh32_imm_high memoryrsh32_imm_high


------------------------------------------------------------

def memoryrsh32_imm_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh32_imm_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
sub %r0, 1
rsh32 %r0, -24
exit
result
0x00ffffff
}

-- #eval exeConformanceCompareResult progrsh32_imm_neg memoryrsh32_imm_neg
-- #eval exeConformanceDebug progrsh32_imm_neg memoryrsh32_imm_neg


------------------------------------------------------------

def memoryrsh32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
sub %r0, 1
rsh32 %r0, 8
exit
result
0x00ffffff
}

-- #eval exeConformanceCompareResult progrsh32_imm memoryrsh32_imm
-- #eval exeConformanceDebug progrsh32_imm memoryrsh32_imm


------------------------------------------------------------

def memoryrsh32_reg_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh32_reg_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
sub %r0, 1
mov %r7, 40
rsh32 %r0, %r7
exit
result
0x00ffffff
}

-- #eval exeConformanceCompareResult progrsh32_reg_high memoryrsh32_reg_high
-- #eval exeConformanceDebug progrsh32_reg_high memoryrsh32_reg_high


------------------------------------------------------------

def memoryrsh32_reg_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh32_reg_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
sub %r0, 1
mov %r7, -24
rsh32 %r0, %r7
exit
result
0x00ffffff
}

-- #eval exeConformanceCompareResult progrsh32_reg_neg memoryrsh32_reg_neg
-- #eval exeConformanceDebug progrsh32_reg_neg memoryrsh32_reg_neg


------------------------------------------------------------

def memoryrsh32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0
sub %r0, 1
mov %r7, 8
rsh32 %r0, %r7
exit
result
0x00ffffff
}

-- #eval exeConformanceCompareResult progrsh32_reg memoryrsh32_reg
-- #eval exeConformanceDebug progrsh32_reg memoryrsh32_reg


------------------------------------------------------------

def memoryrsh64_imm_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh64_imm_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x10
rsh %r0, 68
exit
result
0x1
}

-- #eval exeConformanceCompareResult progrsh64_imm_high memoryrsh64_imm_high
-- #eval exeConformanceDebug progrsh64_imm_high memoryrsh64_imm_high


------------------------------------------------------------

def memoryrsh64_imm_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh64_imm_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x10
rsh %r0, -60
exit
result
0x1
}

-- #eval exeConformanceCompareResult progrsh64_imm_neg memoryrsh64_imm_neg
-- #eval exeConformanceDebug progrsh64_imm_neg memoryrsh64_imm_neg


------------------------------------------------------------

def memoryrsh64_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh64_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x10
rsh %r0, 4
exit
result
0x1
}

-- #eval exeConformanceCompareResult progrsh64_imm memoryrsh64_imm
-- #eval exeConformanceDebug progrsh64_imm memoryrsh64_imm


------------------------------------------------------------

def memoryrsh64_reg_high :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh64_reg_high : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x10
mov %r7, 68
rsh %r0, %r7
exit
result
0x1
}

-- #eval exeConformanceCompareResult progrsh64_reg_high memoryrsh64_reg_high
-- #eval exeConformanceDebug progrsh64_reg_high memoryrsh64_reg_high


------------------------------------------------------------

def memoryrsh64_reg_neg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh64_reg_neg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x10
mov %r7, -60
rsh %r0, %r7
exit
result
0x1
}

-- #eval exeConformanceCompareResult progrsh64_reg_neg memoryrsh64_reg_neg
-- #eval exeConformanceDebug progrsh64_reg_neg memoryrsh64_reg_neg


------------------------------------------------------------

def memoryrsh64_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progrsh64_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0x10
mov %r7, 4
rsh %r0, %r7
exit
result
0x1
}

-- #eval exeConformanceCompareResult progrsh64_reg memoryrsh64_reg
-- #eval exeConformanceDebug progrsh64_reg memoryrsh64_reg


------------------------------------------------------------

def memorysdiv32_zero_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv32_zero_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
sdiv32 %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult progsdiv32_zero_imm memorysdiv32_zero_imm
-- #eval exeConformanceDebug progsdiv32_zero_imm memorysdiv32_zero_imm


------------------------------------------------------------

def memorysdiv32_zero_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv32_zero_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
mov32 %r1, 0
sdiv32 %r0, %r1
exit
result
0x0
}

-- #eval exeConformanceCompareResult progsdiv32_zero_reg memorysdiv32_zero_reg
-- #eval exeConformanceDebug progsdiv32_zero_reg memorysdiv32_zero_reg


------------------------------------------------------------

def memorysdiv32_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv32_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x10000000c
sdiv32 %r0, -4
exit
result
0xfffffffd
}

-- #eval exeConformanceCompareResult progsdiv32_imm memorysdiv32_imm
-- #eval exeConformanceDebug progsdiv32_imm memorysdiv32_imm



------------------------------------------------------------

def memorysdiv32_intmin_negone_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv32_intmin_negone_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0x80000000
sdiv32 %r0, -1
exit
result
0x80000000
}

-- #eval exeConformanceCompareResult progsdiv32_intmin_negone_imm memorysdiv32_intmin_negone_imm
-- #eval exeConformanceDebug progsdiv32_intmin_negone_imm memorysdiv32_intmin_negone_imm


------------------------------------------------------------

def memorysdiv32_intmin_negone_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv32_intmin_negone_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0x80000000
mov32 %r1, -1
sdiv32 %r0, %r1
exit
result
0x80000000
}

-- #eval exeConformanceCompareResult progsdiv32_intmin_negone_reg memorysdiv32_intmin_negone_reg
-- #eval exeConformanceDebug progsdiv32_intmin_negone_reg memorysdiv32_intmin_negone_reg


------------------------------------------------------------

def memorysdiv32_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv32_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x10000000c
mov %r1, -4
sdiv32 %r0, %r1
exit
result
0xfffffffd
}

-- #eval exeConformanceCompareResult progsdiv32_reg memorysdiv32_reg
-- #eval exeConformanceDebug progsdiv32_reg memorysdiv32_reg

------------------------------------------------------------

def memorysdiv64_zero_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv64_zero_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
sdiv %r0, 0
exit
result
0x0
}

-- #eval exeConformanceCompareResult progsdiv64_zero_imm memorysdiv64_zero_imm
-- #eval exeConformanceDebug progsdiv64_zero_imm memorysdiv64_zero_imm


------------------------------------------------------------

def memorysdiv64_zero_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv64_zero_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 1
mov32 %r1, 0
sdiv %r0, %r1
exit
result
0x0
}

-- #eval exeConformanceCompareResult progsdiv64_zero_reg memorysdiv64_zero_reg
-- #eval exeConformanceDebug progsdiv64_zero_reg memorysdiv64_zero_reg


------------------------------------------------------------

def memorysdiv64_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv64_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0xc
lsh %r0, 32
sdiv %r0, -4
exit
result
0xfffffffd00000000
}

-- #eval exeConformanceCompareResult progsdiv64_imm memorysdiv64_imm
-- #eval exeConformanceDebug progsdiv64_imm memorysdiv64_imm

------------------------------------------------------------

def memorysdiv64_intmin_negone_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '8' '0' }

def progsdiv64_intmin_negone_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
sdiv %r0, -1
exit
result
0x8000000000000000
}

-- #eval exeConformanceCompareResult progsdiv64_intmin_negone_imm memorysdiv64_intmin_negone_imm
-- #eval exeConformanceDebug progsdiv64_intmin_negone_imm memorysdiv64_intmin_negone_imm

------------------------------------------------------------

def memorysdiv64_intmin_negone_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '8' '0' }

def progsdiv64_intmin_negone_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
mov %r1, -1
sdiv %r0, %r1
exit
result
0x8000000000000000
}

-- #eval exeConformanceCompareResult progsdiv64_intmin_negone_reg memorysdiv64_intmin_negone_reg
-- #eval exeConformanceDebug progsdiv64_intmin_negone_reg memorysdiv64_intmin_negone_reg


------------------------------------------------------------

def memorysdiv64_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsdiv64_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0xc
lsh %r0, 32
mov %r1, -4
sdiv %r0, %r1
exit
result
0xfffffffd00000000
}

-- #eval exeConformanceCompareResult progsdiv64_reg memorysdiv64_reg
-- #eval exeConformanceDebug progsdiv64_reg memorysdiv64_reg


------------------------------------------------------------

def memorysmod32_intmin_negone_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_intmin_negone_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0x80000000
smod32 %r0, -1
exit
result
0x0
}

-- #eval exeConformanceCompareResult progsmod32_intmin_negone_imm memorysmod32_intmin_negone_imm
-- #eval exeConformanceDebug progsmod32_intmin_negone_imm memorysmod32_intmin_negone_imm


------------------------------------------------------------

def memorysmod32_intmin_negone_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_intmin_negone_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0x80000000
mov32 %r1, -1
smod32 %r0, %r1
exit
result
0x0
}

-- #eval exeConformanceCompareResult progsmod32_intmin_negone_reg memorysmod32_intmin_negone_reg
-- #eval exeConformanceDebug progsmod32_intmin_negone_reg memorysmod32_intmin_negone_reg
------------------------------------------------------------

def memorysmod32_neg_neg_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_neg_neg_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, -13
smod32 %r0, -3
exit
result
0xffffffff
}

-- #eval exeConformanceCompareResult progsmod32_neg_neg_imm memorysmod32_neg_neg_imm
-- #eval exeConformanceDebug progsmod32_neg_neg_imm memorysmod32_neg_neg_imm



------------------------------------------------------------

def memorysmod32_neg_neg_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_neg_neg_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, -13
mov32 %r1, -3
smod32 %r0, %r1
exit
result
0xffffffff
}

-- #eval exeConformanceCompareResult progsmod32_neg_neg_reg memorysmod32_neg_neg_reg
-- #eval exeConformanceDebug progsmod32_neg_neg_reg memorysmod32_neg_neg_reg


------------------------------------------------------------

def memorysmod32_neg_pos_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_neg_pos_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, -13
smod32 %r0, 4
exit
result
0xffffffff
}

-- #eval exeConformanceCompareResult progsmod32_neg_pos_imm memorysmod32_neg_pos_imm
-- #eval exeConformanceDebug progsmod32_neg_pos_imm memorysmod32_neg_pos_imm


------------------------------------------------------------

def memorysmod32_neg_pos_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_neg_pos_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, -13
mov32 %r1, 4
smod32 %r0, %r1
exit
result
0xffffffff
}

-- #eval exeConformanceCompareResult progsmod32_neg_pos_reg memorysmod32_neg_pos_reg
-- #eval exeConformanceDebug progsmod32_neg_pos_reg memorysmod32_neg_pos_reg



------------------------------------------------------------

def memorysmod32_neg_zero_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_neg_zero_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, -10
smod32 %r0, 0
exit
result
0xFFFFFFF6
}

-- #eval exeConformanceCompareResult progsmod32_neg_zero_imm memorysmod32_neg_zero_imm
-- #eval exeConformanceDebug progsmod32_neg_zero_imm memorysmod32_neg_zero_imm

------------------------------------------------------------

def memorysmod32_neg_zero_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_neg_zero_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, -10
mov32 %r1, 0
smod32 %r0, %r1
exit
result
0xFFFFFFF6
}

-- #eval exeConformanceCompareResult progsmod32_neg_zero_reg memorysmod32_neg_zero_reg
-- #eval exeConformanceDebug progsmod32_neg_zero_reg memorysmod32_neg_zero_reg

------------------------------------------------------------

def memorysmod32_pos_neg_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_pos_neg_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 13
smod32 %r0, -3
exit
result
0x1
}

-- #eval exeConformanceCompareResult progsmod32_pos_neg_imm memorysmod32_pos_neg_imm
-- #eval exeConformanceDebug progsmod32_pos_neg_imm memorysmod32_pos_neg_imm

------------------------------------------------------------

def memorysmod32_pos_neg_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod32_pos_neg_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 13
mov32 %r1, -3
smod32 %r0, %r1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progsmod32_pos_neg_reg memorysmod32_pos_neg_reg
-- #eval exeConformanceDebug progsmod32_pos_neg_reg memorysmod32_pos_neg_reg


------------------------------------------------------------

def memorysmod64_intmin_negone_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '8' '0' }

def progsmod64_intmin_negone_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
smod %r0, -1
exit
result
0x0
}

-- #eval exeConformanceCompareResult progsmod64_intmin_negone_imm memorysmod64_intmin_negone_imm
-- #eval exeConformanceDebug progsmod64_intmin_negone_imm memorysmod64_intmin_negone_imm


------------------------------------------------------------

def memorysmod64_intmin_negone_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '8' '0' }

def progsmod64_intmin_negone_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldxdw %r0, [%r1]
mov %r1, -1
smod %r0, %r1
exit
result
0x0
}

-- #eval exeConformanceCompareResult progsmod64_intmin_negone_reg memorysmod64_intmin_negone_reg
-- #eval exeConformanceDebug progsmod64_intmin_negone_reg memorysmod64_intmin_negone_reg


------------------------------------------------------------

def memorysmod64_neg_neg_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod64_neg_neg_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, -13
smod %r0, -3
exit
result
0xffffffffffffffff
}

-- #eval exeConformanceCompareResult progsmod64_neg_neg_imm memorysmod64_neg_neg_imm
-- #eval exeConformanceDebug progsmod64_neg_neg_imm memorysmod64_neg_neg_imm


------------------------------------------------------------

def memorysmod64_neg_neg_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod64_neg_neg_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, -13
mov %r1, -3
smod %r0, %r1
exit
result
0xffffffffffffffff
}

-- #eval exeConformanceCompareResult progsmod64_neg_neg_reg memorysmod64_neg_neg_reg
-- #eval exeConformanceDebug progsmod64_neg_neg_reg memorysmod64_neg_neg_reg


------------------------------------------------------------

def memorysmod64_neg_pos_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod64_neg_pos_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, -13
smod %r0, 4
exit
result
0xffffffffffffffff
}

-- #eval exeConformanceCompareResult progsmod64_neg_pos_imm memorysmod64_neg_pos_imm
-- #eval exeConformanceDebug progsmod64_neg_pos_imm memorysmod64_neg_pos_imm


------------------------------------------------------------

def memorysmod64_neg_pos_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod64_neg_pos_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, -13
mov %r1, 4
smod %r0, %r1
exit
result
0xffffffffffffffff
}

-- #eval exeConformanceCompareResult progsmod64_neg_pos_reg memorysmod64_neg_pos_reg
-- #eval exeConformanceDebug progsmod64_neg_pos_reg memorysmod64_neg_pos_reg


------------------------------------------------------------

def memorysmod64_neg_zero_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod64_neg_zero_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, -10
smod %r0, 0
exit
result
0xFFFFFFFFFFFFFFF6
}

-- #eval exeConformanceCompareResult progsmod64_neg_zero_imm memorysmod64_neg_zero_imm
-- #eval exeConformanceDebug progsmod64_neg_zero_imm memorysmod64_neg_zero_imm


------------------------------------------------------------

def memorysmod64_neg_zero_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod64_neg_zero_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, -10
mov %r1, 0
smod %r0, %r1
exit
result
0xFFFFFFFFFFFFFFF6
}

-- #eval exeConformanceCompareResult progsmod64_neg_zero_reg memorysmod64_neg_zero_reg
-- #eval exeConformanceDebug progsmod64_neg_zero_reg memorysmod64_neg_zero_reg


------------------------------------------------------------

def memorysmod64_pos_neg_imm :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod64_pos_neg_imm : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 13
smod %r0, -3
exit
result
0x1
}

-- #eval exeConformanceCompareResult progsmod64_pos_neg_imm memorysmod64_pos_neg_imm
-- #eval exeConformanceDebug progsmod64_pos_neg_imm memorysmod64_pos_neg_imm


------------------------------------------------------------

def memorysmod64_pos_neg_reg :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progsmod64_pos_neg_reg : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 13
mov %r1, -3
smod %r0, %r1
exit
result
0x1
}

-- #eval exeConformanceCompareResult progsmod64_pos_neg_reg memorysmod64_pos_neg_reg
-- #eval exeConformanceDebug progsmod64_pos_neg_reg memorysmod64_pos_neg_reg


------------------------------------------------------------

def memorystack :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progstack : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r1, 51
stdw [%r10-16], 0xab --%r10-16 == 0
stdw [%r10-8], 0xcd --%r10-8 == 8
and %r1, 1
lsh %r1, 3
mov %r2, %r10
mov %r5, %r10
add %r2, %r1
ldxdw %r0, [%r2-16] -- 16 + 8 -16
exit
result
0xcd
}

-- #eval exeConformanceCompareResult progstack memorystack
-- #eval exeConformanceDebug progstack memorystack

------------------------------------------------------------

def memorystb :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' 'f' 'f' 'c' 'c' 'd' 'd' }

def progstb : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
stb [%r1+2], 0x11
ldxb %r0, [%r1+2]
exit
result
0x11
}

-- #eval exeConformanceCompareResult progstb memorystb
-- #eval exeConformanceDebug progstb memorystb

------------------------------------------------------------

def memorystdw :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'c' 'c' 'd' 'd' }

def progstdw : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
stdw [%r1+2], 0x44332211
ldxdw %r0, [%r1+2]
exit
result
0x0000000044332211
}

-- #eval exeConformanceCompareResult progstdw memorystdw
-- #eval exeConformanceDebug progstdw memorystdw

------------------------------------------------------------

def memorysth :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' 'f' 'f' 'f' 'f' 'c' 'c' 'd' 'd' }

def progsth : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
sth [%r1+2], 0x2211
ldxh %r0, [%r1+2]
exit
result
0x2211
}

-- #eval exeConformanceCompareResult progsth memorysth
-- #eval exeConformanceDebug progsth memorysth


------------------------------------------------------------

def memorystw :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'c' 'c' 'd' 'd' }

def progstw : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
stw [%r1+2], 0x44332211
ldxw %r0, [%r1+2]
exit
result
0x44332211
}

-- #eval exeConformanceCompareResult progstw memorystw
-- #eval exeConformanceDebug progstw memorystw


------------------------------------------------------------

def memorystxb_all :=
    createStackMemory 0 emptyMemory
{mem|
'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' }

def progstxb_all : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, 0xf0
mov %r2, 0xf2
mov %r3, 0xf3
mov %r4, 0xf4
mov %r5, 0xf5
mov %r6, 0xf6
mov %r7, 0xf7
mov %r8, 0xf8
stxb [%r1], %r0
stxb [%r1+1], %r2
stxb [%r1+2], %r3
stxb [%r1+3], %r4
stxb [%r1+4], %r5
stxb [%r1+5], %r6
stxb [%r1+6], %r7
stxb [%r1+7], %r8
ldxdw %r0, [%r1]
be64 %r0
exit
result
0xf0f2f3f4f5f6f7f8
}

-- #eval exeConformanceCompareResult progstxb_all memorystxb_all
-- #eval exeConformanceDebug progstxb_all memorystxb_all


------------------------------------------------------------

def memorystxb_all2 :=
    createStackMemory 0 emptyMemory
{mem|
'f' 'f' 'f' 'f' }

def progstxb_all2 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, %r1
mov %r1, 0xf1
mov %r9, 0xf9
stxb [%r0], %r1
stxb [%r0+1], %r9
ldxh %r0, [0]
ldxh %r3, [%r0]
be16 %r0
exit
result
0xf1f9
}

-- #eval exeConformanceCompareResult progstxb_all2 memorystxb_all2
-- #eval exeConformanceDebug progstxb_all2 memorystxb_all2


--Problema com o calculo do Offset de algumas operaçoes
-- O Be16 funciona com pares de hexadecimal
------------------------------------------------------------

def memorystxb_chain :=
    createStackMemory 0 emptyMemory
{mem|
'2' 'a' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progstxb_chain : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r0, %r1
ldxb %r9, [%r0+0]
stxb [%r0+1], %r9
ldxb %r8, [%r0+1]
stxb [%r0+2], %r8
ldxb %r7, [%r0+2]
stxb [%r0+3], %r7
ldxb %r6, [%r0+3]
stxb [%r0+4], %r6
ldxb %r5, [%r0+4]
stxb [%r0+5], %r5
ldxb %r4, [%r0+5]
stxb [%r0+6], %r4
ldxb %r3, [%r0+6]
stxb [%r0+7], %r3
ldxb %r2, [%r0+7]
stxb [%r0+8], %r2
ldxb %r1, [%r0+8]
stxb [%r0+9], %r1
ldxb %r0, [%r0+9]
exit
result
0x2a
}

-- #eval exeConformanceCompareResult progstxb_chain memorystxb_chain
-- #eval exeConformanceDebug progstxb_chain memorystxb_chain


------------------------------------------------------------

def memorystxb :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' 'f' 'f' 'c' 'c' 'd' 'd' }

def progstxb : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r2, 0x11
stxb [%r1+2], %r2
ldxb %r0, [%r1+2]
exit
result
0x11
}

-- #eval exeConformanceCompareResult progstxb memorystxb
-- #eval exeConformanceDebug progstxb memorystxb


------------------------------------------------------------

def memorystxdw :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'c' 'c' 'd' 'd' }

def progstxdw : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r2, 0x88776655
lsh %r2, 32
or %r2, 0x44332211
stxdw [%r1+2], %r2
ldxdw %r0, [%r1+2]
exit
result
0x8877665544332211
}

-- #eval exeConformanceCompareResult progstxdw memorystxdw
-- #eval exeConformanceDebug progstxdw memorystxdw


------------------------------------------------------------

def memorystxh :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' 'f' 'f' 'f' 'f' 'c' 'c' 'd' 'd' }

def progstxh : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r2, 0x2211
stxh [%r1+2], %r2
ldxh %r0, [%r1+2]
exit
result
0x2211
}

-- #eval exeConformanceCompareResult progstxh memorystxh
-- #eval exeConformanceDebug progstxh memorystxh


------------------------------------------------------------

def memorystxw :=
    createStackMemory 0 emptyMemory
{mem|
'a' 'a' 'b' 'b' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'f' 'c' 'c' 'd' 'd' }

def progstxw : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r2, 0x44332211
stxw [%r1+2], %r2
ldxw %r0, [%r1+2]
exit
result
0x44332211
}

-- #eval exeConformanceCompareResult progstxw memorystxw
-- #eval exeConformanceDebug progstxw memorystxw


------------------------------------------------------------

def memorysubnet :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' 'c' '0' '9' 'f' 'a' '0' '9' '7' '0' '0' 'a' '0'
'c' 'c' '3' 'b' 'b' 'f' 'f' 'a' '0' '8' '0' '0' '4' '5' '1' '0'
'0' '0' '3' 'c' '4' '6' '3' 'c' '4' '0' '0' '0' '4' '0' '0' '6'
'7' '3' '1' 'c' 'c' '0' 'a' '8' '0' '1' '0' '2' 'c' '0' 'a' '8'
'0' '1' '0' '1' '0' '6' '0' 'e' '0' '0' '1' '7' '9' '9' 'c' '5'
'a' '0' 'e' 'c' '0' '0' '0' '0' '0' '0' '0' '0' 'a' '0' '0' '2'
'7' 'd' '7' '8' 'e' '0' 'a' '3' '0' '0' '0' '0' '0' '2' '0' '4'
'0' '5' 'b' '4' '0' '4' '0' '2' '0' '8' '0' 'a' '0' '0' '9' 'c'
'2' '7' '2' '4' '0' '0' '0' '0' '0' '0' '0' '0' '0' '1' '0' '3'
'0' '3' '0' '0' }

def progsubnet : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov %r2, 0xe
ldxh %r3, [%r1+12]
jne %r3, 0x81, 3
mov %r2, 0x12
ldxh %r3, [%r1+16]
and %r3, 0xffff
jne %r3, 0x8, 5
add %r1, %r2
mov %r0, 0x1
ldxw %r1, [%r1+16]
and %r1, 0xffffff
jeq %r1, 0x1a8c0, exit
mov %r0, 0x0
exit
result
0x1
}

-- #eval exeConformanceCompareResult progsubnet memorysubnet
-- #eval exeConformanceDebug progsubnet memorysubnet


------------------------------------------------------------

def memoryswap16 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progswap16 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x8877665544332211
swap16 %r0
exit
result
0x1122
}

-- #eval exeConformanceCompareResult progswap16 memoryswap16
-- #eval exeConformanceDebug progswap16 memoryswap16


------------------------------------------------------------

def memoryswap32 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progswap32 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x8877665544332211
swap32 %r0
exit
result
0x11223344
}

-- #eval exeConformanceCompareResult progswap32 memoryswap32
-- #eval exeConformanceDebug progswap32 memoryswap32


------------------------------------------------------------

def memoryswap64 :=
    createStackMemory 0 emptyMemory
{mem|
'0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' '0' }

def progswap64 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
lddw %r0, 0x8877665544332211
swap64 %r0
exit
result
0x1122334455667788
}

-- #eval exeConformanceCompareResult progswap64 memoryswap64
-- #eval exeConformanceDebug progswap64 memoryswap64


------------------------------
