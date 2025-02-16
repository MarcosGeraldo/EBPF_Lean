-- Projeto proposto da formalização do eBPF em Lean

import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Defs
import Aesop
import Lean.Elab.Tactic
import Init.System.IO
open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Term
open Lean.Syntax

open Lean Elab  Meta

-- Inicio da semantica

inductive Immediate : Type
| mk : ℕ → Immediate
deriving Repr

inductive Pc : Type
| mk : ℕ → Pc
deriving Repr

inductive Offset: Type
| mk : ℕ → Offset
| Exit : Offset
deriving Repr

inductive RegisterCode : Type
| r0  : RegisterCode
| r1  : RegisterCode
| r2  : RegisterCode
| r3  : RegisterCode
| r4  : RegisterCode
| r5  : RegisterCode
| r6  : RegisterCode
| r7  : RegisterCode
| r8  : RegisterCode
| r9  : RegisterCode
| r10 : RegisterCode
| rP  : RegisterCode
deriving Repr

inductive Content : Type
| mk: ℕ → Content
deriving Repr

inductive Register : Type
| mk : RegisterCode → Content → Register
deriving Repr

inductive Registers : Type -- Trocar para Mapeamento Finito
| Nil : Register → Registers
| Cons : Register → Registers → Registers
deriving Repr

inductive Lsb: Type
| bpf_ld : Lsb
| bpf_ldx : Lsb
| bpf_st : Lsb
| bpf_stx : Lsb
| bpf_alu : Lsb
| bpf_jmp : Lsb
| bpf_jmp32 : Lsb
| bpf_alu64 : Lsb
deriving Repr

inductive Msb : Type
| bpf_add : Msb
| bpf_sub : Msb
| bpf_mul : Msb
| bpf_div : Msb
| bpf_end : Msb
| bpf_mov : Msb
deriving Repr
/-
| bpf_ : Msb
| bpf_ : Msb
-/

inductive Source : Type
| bpf_k : Source
| bpf_x : Source
deriving Repr

inductive SourceReg: Type
| mk : RegisterCode →  SourceReg
deriving Repr

inductive DestinationReg: Type
| mk : RegisterCode → DestinationReg
deriving Repr

inductive OpCode: Type
| Eof : OpCode
| mk : Msb → Source → Lsb → OpCode
deriving Repr

inductive Word : Type
| mk : Immediate → Offset → SourceReg → DestinationReg → OpCode → Word
deriving Repr

inductive Instructions : Type
| Nil : Word → Instructions
| Cons : Word → Instructions → Instructions
deriving Repr

inductive Program: Type
| mk : Registers → Instructions → Pc → Program
deriving Repr

inductive ProgramList: Type
| mk : List Register → List Word → Pc → ProgramList
deriving Repr

#eval Content.mk 1


def Ex_Content := Content.mk 5
def Ex_Immediate := Immediate.mk 25
def Ex_Pc := Pc.mk 0
def Ex_Offset := Offset.mk 0
def Ex_Register := Register.mk RegisterCode.r1 Ex_Content
def Ex_Register1 := Register.mk RegisterCode.r1 (Content.mk 7)
def Ex_Registers := Registers.Cons Ex_Register (Registers.Cons Ex_Register1 (Registers.Nil Ex_Register1))
def Ex_OpCode : OpCode := OpCode.mk Msb.bpf_add Source.bpf_k Lsb.bpf_alu
def Ex_Word : Word := Word.mk Ex_Immediate Ex_Offset (SourceReg.mk RegisterCode.r2) (DestinationReg.mk RegisterCode.r3) Ex_OpCode
def Ex_Instructions := Instructions.Cons Ex_Word (Instructions.Cons Ex_Word (Instructions.Nil Ex_Word))


def Ex_Program : Program :=
  Program.mk Ex_Registers Ex_Instructions Ex_Pc

def Ex_ProgramList : ProgramList :=
  ProgramList.mk [Ex_Register] [Ex_Word] Ex_Pc


#eval Ex_Content
#eval Ex_Immediate
#eval Ex_Pc
#eval Ex_Offset
#eval Ex_Register
#eval Ex_Register1
#eval Ex_Registers
#eval Ex_OpCode
#eval Ex_Word
#eval Ex_Instructions
#eval Ex_Program
#eval Ex_ProgramList

-------$$$$$$$$$$$$$$$$$$$$$$$$$
-------$$$$$$$$$$$$$$$$$$$$$$$$$
-------$$$$$$$$$$$$$$$$$$$$$$$$$
-------$$$$$$$$$$$$$$$$$$$$$$$$$
---- Inicio do parser para ler o padrão de entrada do Racket

declare_syntax_cat imp_Immediate

syntax num : imp_Immediate

def elabImmediate : Syntax → MetaM Expr
| `(imp_Immediate| $n:num) => mkAppM ``Immediate.mk #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

elab "test_elabImmediate" l:imp_Immediate : term => elabImmediate l

#reduce test_elabImmediate 3

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Pc

syntax num : imp_Pc

def elabPc : Syntax → MetaM Expr
| `(imp_Pc| $n:num) => mkAppM ``Pc.mk #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

elab "test_elabPc" l:imp_Pc : term => elabPc l

#reduce test_elabPc 3

declare_syntax_cat imp_Content

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

syntax num : imp_Content

def elabContent : Syntax → MetaM Expr
| `(imp_Content| $n:num) => mkAppM ``Content.mk #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

elab "test_elabContent" l:imp_Content : term => elabContent l

#reduce test_elabContent 3

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Offset

syntax num : imp_Offset

def elabOffset : Syntax → MetaM Expr
| `(imp_Offset| $n:num) => mkAppM ``Offset.mk #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

elab "test_elabOffset" l:imp_Offset : term => elabOffset l

#reduce test_elabOffset 3

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_RegisterCode

syntax "%r0" : imp_RegisterCode
syntax "%r1" : imp_RegisterCode
syntax "%r2" : imp_RegisterCode
syntax "%r3" : imp_RegisterCode
syntax "%r4" : imp_RegisterCode
syntax "%r5" : imp_RegisterCode
syntax "%r6" : imp_RegisterCode
syntax "%r7" : imp_RegisterCode
syntax "%r8" : imp_RegisterCode
syntax "%r9" : imp_RegisterCode
syntax "%r10" : imp_RegisterCode

def elabRegisterCode : Syntax → MetaM Expr
| `(imp_RegisterCode| %r0) => return .const ``RegisterCode.r0 []
| `(imp_RegisterCode| %r1) => return .const ``RegisterCode.r1 []
| `(imp_RegisterCode| %r2) => return .const ``RegisterCode.r2 []
| `(imp_RegisterCode| %r3) => return .const ``RegisterCode.r3 []
| `(imp_RegisterCode| %r4) => return .const ``RegisterCode.r4 []
| `(imp_RegisterCode| %r5) => return .const ``RegisterCode.r5 []
| `(imp_RegisterCode| %r6) => return .const ``RegisterCode.r6 []
| `(imp_RegisterCode| %r7) => return .const ``RegisterCode.r7 []
| `(imp_RegisterCode| %r8) => return .const ``RegisterCode.r8 []
| `(imp_RegisterCode| %r9) => return .const ``RegisterCode.r9 []
| `(imp_RegisterCode| %r10) => return .const ``RegisterCode.r10 []
| _ => throwUnsupportedSyntax

elab "test_elabRegisterCode" l:imp_RegisterCode : term => elabRegisterCode l

#reduce test_elabRegisterCode %r3

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Register

syntax imp_RegisterCode imp_Content : imp_Register

def elabRegister : Syntax → MetaM Expr
| `(imp_Register| $l:imp_RegisterCode $b:imp_Content) => do
  let l ← elabRegisterCode l
  let b ← elabContent b
  mkAppM ``Register.mk #[l, b]

| _ => throwUnsupportedSyntax

elab "test_elabRegister" l:imp_Register : term => elabRegister l

#reduce test_elabRegister %r1 9

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Registers

syntax imp_Register imp_Registers : imp_Registers
syntax imp_Register : imp_Registers

partial def elabRegisters : Syntax → MetaM Expr
| `(imp_Registers| $l:imp_Register) => do
  let l ← elabRegister l
  mkAppM ``Registers.Nil #[l]
| `(imp_Registers| $l:imp_Register $b:imp_Registers) => do
  let l ← elabRegister l
  let b ← elabRegisters b
  mkAppM ``Registers.Cons #[l, b]
| _ => throwUnsupportedSyntax

elab "test_elabRegisters" l:imp_Registers : term => elabRegisters l

#reduce test_elabRegisters %r1 7 %r2 8 %r3 9

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Lsb

syntax "bpf_ld" : imp_Lsb
syntax "bpf_ldx" : imp_Lsb
syntax "bpf_st" : imp_Lsb
syntax "bpf_stx" : imp_Lsb
syntax "bpf_alu" : imp_Lsb
syntax "bpf_jmp" : imp_Lsb
syntax "bpf_jmp32" : imp_Lsb
syntax "bpf_alu64" : imp_Lsb

def elabLsb : Syntax → MetaM Expr
| `(imp_Lsb| bpf_ld) => return .const ``Lsb.bpf_ld []
| `(imp_Lsb| bpf_ldx) => return .const ``Lsb.bpf_ldx []
| `(imp_Lsb| bpf_st) => return .const ``Lsb.bpf_st []
| `(imp_Lsb| bpf_stx) => return .const ``Lsb.bpf_stx []
| `(imp_Lsb| bpf_alu) => return .const ``Lsb.bpf_alu []
| `(imp_Lsb| bpf_jmp) => return .const ``Lsb.bpf_jmp []
| `(imp_Lsb| bpf_jmp32) => return .const ``Lsb.bpf_jmp32 []
| `(imp_Lsb| bpf_alu64) => return .const ``Lsb.bpf_alu64 []
| _ => throwUnsupportedSyntax

elab "test_elabLsb" l:imp_Lsb : term => elabLsb l

#reduce test_elabLsb bpf_ld

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Msb

syntax "bpf_add" : imp_Msb
syntax "bpf_sub" : imp_Msb
syntax "bpf_mul" : imp_Msb
syntax "bpf_div" : imp_Msb
syntax "bpf_end" : imp_Msb
syntax "bpf_mov" : imp_Msb


def elabMsb : Syntax → MetaM Expr
| `(imp_Msb| bpf_add) => return .const ``Msb.bpf_add []
| `(imp_Msb| bpf_sub) => return .const ``Msb.bpf_sub []
| `(imp_Msb| bpf_mul) => return .const ``Msb.bpf_mul []
| `(imp_Msb| bpf_div) => return .const ``Msb.bpf_div []
| `(imp_Msb| bpf_end) => return .const ``Msb.bpf_end []
| `(imp_Msb| bpf_mov) => return .const ``Msb.bpf_mov []

| _ => throwUnsupportedSyntax

elab "test_elabMsb" l:imp_Msb : term => elabMsb l

#reduce test_elabMsb bpf_add

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Source

syntax "bpf_k" : imp_Source
syntax "bpf_x" : imp_Source

def elabSource : Syntax → MetaM Expr
| `(imp_Source| bpf_k) => return .const ``Source.bpf_k []
| `(imp_Source| bpf_x) => return .const ``Source.bpf_x []
| _ => throwUnsupportedSyntax

elab "test_elabSource" l:imp_Source : term => elabSource l

#reduce test_elabSource bpf_k

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_SourceReg

syntax imp_RegisterCode : imp_SourceReg

def elabSourceReg : Syntax → MetaM Expr
| `(imp_SourceReg| $l:imp_RegisterCode) => do
  let l ← elabRegisterCode l
  mkAppM ``SourceReg.mk #[l]
| _ => throwUnsupportedSyntax

elab "test_elabSourceReg" l:imp_SourceReg : term => elabSourceReg l

#reduce test_elabSourceReg %r1

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_DestinationReg

syntax imp_RegisterCode : imp_DestinationReg

def elabDestinationReg : Syntax → MetaM Expr
| `(imp_DestinationReg| $l:imp_RegisterCode) => do
  let l ← elabRegisterCode l
  mkAppM ``DestinationReg.mk #[l]
| _ => throwUnsupportedSyntax

elab "test_elabDestinationReg" l:imp_DestinationReg : term => elabDestinationReg l

#reduce test_elabDestinationReg %r1

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_OpCode

syntax "exit" : imp_OpCode
syntax imp_Msb imp_Source imp_Lsb : imp_OpCode

partial def elabOpCode : Syntax → MetaM Expr
| `(imp_OpCode| exit) => return .const ``OpCode.Eof []
| `(imp_OpCode| $l:imp_Msb $b:imp_Source $r:imp_Lsb) => do
  let l ← elabMsb l
  let b ← elabSource b
  let r ← elabLsb r
  mkAppM ``OpCode.mk #[l, b, r]
| _ => throwUnsupportedSyntax

elab "test_elabOpCode" e:imp_OpCode : term => elabOpCode e

#reduce test_elabOpCode bpf_add bpf_x bpf_alu

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Word

syntax imp_Immediate imp_Offset imp_SourceReg imp_DestinationReg imp_OpCode : imp_Word

def elabWord : Syntax → MetaM Expr
| `(imp_Word| $a:imp_Immediate $b:imp_Offset $c:imp_SourceReg $d:imp_DestinationReg $e:imp_OpCode ) => do
  let a ← elabImmediate a
  let b ← elabOffset b
  let c ← elabSourceReg c
  let d ← elabDestinationReg d
  let e ← elabOpCode e
  mkAppM ``Word.mk #[a, b, c, d, e]
| _ => throwUnsupportedSyntax

elab "test_elabWord" e:imp_Word : term => elabWord e

#reduce test_elabWord 5 0 %r1 %r5 bpf_add bpf_x bpf_alu

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Instructions

syntax imp_Word : imp_Instructions
syntax imp_Word imp_Instructions : imp_Instructions
syntax "(" imp_Word imp_Instructions ")" : imp_Instructions

partial def elabInstructions : Syntax → MetaM Expr
| `(imp_Instructions| $l:imp_Word) => do
  let l ← elabWord l
  mkAppM ``Instructions.Nil #[l]
| `(imp_Instructions| $l:imp_Word $b:imp_Instructions) => do
  let l ← elabWord l
  let b ← elabInstructions b
  mkAppM ``Instructions.Cons #[l, b]
| `(imp_Instructions| ($l:imp_Word $b:imp_Instructions)) => do
  let l ← elabWord l
  let b ← elabInstructions b
  mkAppM ``Instructions.Cons #[l, b]
| _ => throwUnsupportedSyntax

elab "test_elabInstructions" e:imp_Instructions : term => elabInstructions e

#reduce test_elabInstructions ( 5 0 %r1 %r5 bpf_add bpf_x bpf_alu 15 10 %r2 %r8 bpf_sub bpf_k bpf_alu )

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Program

syntax imp_Registers imp_Instructions  imp_Pc : imp_Program

def elabProgram : Syntax → MetaM Expr
| `(imp_Program| $a:imp_Registers $b:imp_Instructions $c:imp_Pc) => do
  let a ← elabRegisters a
  let b ← elabInstructions b
  let c ← elabPc c
  mkAppM ``Program.mk #[a, b, c]
| _ => throwUnsupportedSyntax

elab "test_elabProgram" l:imp_Program : term => elabProgram l

#reduce test_elabProgram %r1 7 %r2 8 %r3 9  (5 0 %r1 %r5 bpf_add bpf_x bpf_alu 15 10 %r2 %r8 bpf_sub bpf_k bpf_alu ) 0


elab "{exe|" p: imp_Program "}" : term => elabProgram p

#reduce {exe|
  %r1 7 %r2 8 %r3 9
  (5 0 %r1 %r2 bpf_add bpf_x bpf_alu 15 10 %r1 %r3 bpf_sub bpf_k bpf_alu 15 10 %r1 %r3 bpf_sub bpf_k bpf_alu)
  0
}


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
---- Inicio do parser para ler o padrão dos Testes de Conformidade


inductive Comment: Type
| Nil : String → Comment
| Cons : String → Comment → Comment
deriving Repr

inductive Result: Type
| mk : ℕ → Result
deriving Repr

inductive TestEval: Type
| mk : Instructions → ℕ → TestEval
deriving Repr

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_OpCodeT

syntax "exit" : imp_OpCodeT
syntax "mov32" : imp_OpCodeT
syntax "add32" : imp_OpCodeT
syntax "sub32" : imp_OpCodeT
syntax "mul32" : imp_OpCodeT
syntax "div32" : imp_OpCodeT

partial def elabOpCodeT : Syntax → MetaM Expr
| `(imp_OpCodeT| add32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_add [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeT| sub32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sub [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeT| mul32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mul [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeT| div32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_div [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeT| exit) => return .const ``OpCode.Eof []
| `(imp_OpCodeT| mov32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mov [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]

| _ => throwUnsupportedSyntax

elab "test_elabOpCodeT" e:imp_OpCodeT : term => elabOpCodeT e

#reduce test_elabOpCodeT add32

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_WordT

syntax imp_OpCodeT imp_SourceReg "," imp_DestinationReg: imp_WordT
syntax imp_OpCodeT imp_SourceReg "," imp_Immediate: imp_WordT
syntax "exit" : imp_WordT
-- Adequar para as possiveis diferentes classes
def elabWordT : Syntax → MetaM Expr
| `(imp_WordT| $a:imp_OpCodeT $b:imp_SourceReg , $c:imp_DestinationReg) => do
  let a ← elabOpCodeT a
  let b ← elabSourceReg b
  let c ← elabDestinationReg c
  return mkAppN (Expr.const ``Word.mk []) #[Expr.const ``Immediate.mk [0], Expr.const ``Offset.mk [0], b, c, a]
| `(imp_WordT| $a:imp_OpCodeT $b:imp_SourceReg , $c:imp_Immediate) => do
  let a ← elabOpCodeT a
  let b ← elabSourceReg b
  let c ← elabImmediate c
  let offsetExpr := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  let contentExpr := mkApp (Expr.const ``Content.mk []) (mkNatLit 0)
  let regExpr := mkAppN (Expr.const ``Register.mk []) #[Expr.const ``RegisterCode.r0 [], contentExpr]
  return mkAppN (Expr.const ``Word.mk []) #[c, offsetExpr, b, regExpr, a]
| `(imp_WordT| exit) => do
  let immExpr := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let offsetExpr := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  let contentExpr := mkApp (Expr.const ``Content.mk []) (mkNatLit 0)
  let regExpr := mkAppN (Expr.const ``Register.mk []) #[Expr.const ``RegisterCode.r0 [], contentExpr]
  let extExpr := Expr.const ``OpCode.Eof []
  return mkAppN (Expr.const ``Word.mk []) #[immExpr, offsetExpr, regExpr, regExpr, extExpr]
| _ => throwUnsupportedSyntax

elab "test_elabWordT" e:imp_WordT : term => elabWordT e

#reduce test_elabWordT mov32 %r0, 0

#reduce test_elabWordT add32 %r0, %r1
#reduce test_elabWordT exit


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_InstructionsT

syntax imp_WordT : imp_InstructionsT
syntax imp_WordT imp_InstructionsT : imp_InstructionsT

partial def elabInstructionsT : Syntax → MetaM Expr
| `(imp_InstructionsT| $l:imp_WordT $b:imp_InstructionsT) => do
  let l ← elabWordT l
  let b ← elabInstructionsT b
  mkAppM ``Instructions.Cons #[l, b]
| `(imp_InstructionsT| $l:imp_WordT) => do
  let l ← elabWordT l
  mkAppM ``Instructions.Nil #[l]
| _ => throwUnsupportedSyntax

elab "test_elabInstructionsT" e:imp_InstructionsT : term => elabInstructionsT e

#reduce test_elabInstructionsT
mov32 %r0, 0
add32 %r0, %r1
add32 %r0, %r1
mov32 %r0, 0
mov32 %r1, 2
add32 %r0, 1
add32 %r0, %r1
add32 %r0, %r0
add32 %r0, 3
exit


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
declare_syntax_cat newline  -- Define uma categoria de sintaxe para nova linha
syntax "\\n" : newline       -- Define o símbolo de nova linha como uma sintaxe


declare_syntax_cat imp_Comment

syntax "#" ident* : imp_Comment

def elabComment : Syntax → MetaM Expr
| `(imp_Comment| # $a*) => do
  let comment_str := String.join (List.map (fun id => id.getId.toString) (a.toList))   -- Converte todos os identificadores após # em uma string
  return mkStrLit comment_str
| _ => throwUnsupportedSyntax

elab "test_elabComment" e:imp_Comment : term => elabComment e

#reduce test_elabComment
# Este e um comentario com varios espacos
data


declare_syntax_cat imp_TestEval

syntax "#" ident* "#" ident* "asm" imp_InstructionsT "result" num : imp_TestEval


def elabTestEval : Syntax → MetaM Expr
| `(imp_TestEval| # $_* # $_* asm $b:imp_InstructionsT result $c:num) => do
  --let a : Expr := mkStrLit (String.join (List.map (fun id => id.getId.toString) (a.toList)))   -- Converte o identificador em uma string
  let b ← elabInstructionsT b  -- Usa a função já existente para elaborar as instruções
  let c : Expr := mkNatLit c.getNat  -- Converte o número para um literal de número
  mkAppM ``TestEval.mk #[ b, c]  -- Cria uma instância do construtor TestEval
| _ => throwUnsupportedSyntax

elab "test_elabTestEval" e:imp_TestEval : term => elabTestEval e

#reduce test_elabTestEval
#Comentario com espacos
#Comentario com espacos
asm
mov32 %r0, 0
add32 %r0, %r1
add32 %r0, %r1
mov32 %r0, 0
mov32 %r1, 2
add32 %r0, 1
add32 %r0, %r1
add32 %r0, %r0
add32 %r0, 3
exit
result
0x10

#reduce test_elabTestEval
#Comentario com espacos
#Comentario com espacos
asm
mov32 %r0, 0
mov32 %r1, 0
add32 %r0, %r1
add32 %r0, %r1
mov32 %r0, 0
mov32 %r1, 2
add32 %r0, 1
add32 %r0, %r1
add32 %r0, %r0
add32 %r0, 3
exit
result
0x10

def readFile (filePath : String) : IO String := do
  let handle ← IO.FS.Handle.mk filePath IO.FS.Mode.read
  let content ← handle.readToEnd
  return content

def main : IO Unit := do
  let fileContent ← readFile "add.data"
  IO.println fileContent

#eval main
#eval readFile "add.data"

def readFileContent (filePath : String) : IO String := do
  IO.FS.readFile filePath

def testExample : IO Unit := do
  let content ← readFileContent "add.data"
  -- Aqui você deve manipular `content` como `String`
  IO.println s!"Conteúdo do arquivo: {content}"

def prog := readFile "add.data"

#eval readFileContent "add.data"


-- Define a função para ler o conteúdo do arquivo
def readFileContentB (filePath : String) : IO String := do
  IO.FS.readFile filePath

-- Processa o conteúdo do arquivo como `imp_TestEval` assumindo que o conteúdo segue o formato apropriado
def parseAndEvaluate (content : String) : String :=
  -- Suponha que 'content' tenha a forma correta para ser interpretado
  -- como um termo Lean que começa com "#test" (exemplo)
  -- Isso deve ser adaptado conforme a necessidade para usar `test_elabTestEval`
  let trimmed := content.trim
  s!"Test case loaded: {trimmed}"

-- Função para integrar leitura e processamento
def runTestEvalFromFile (filePath : String) : IO Unit := do
  let content ← readFileContentB filePath
  IO.println s!"{parseAndEvaluate content}"

def readFileContentA (filePath : String) : IO String := do
  let handle ← IO.FS.Handle.mk filePath IO.FS.Mode.read -- Abre o arquivo em modo de leitura
  let content ← handle.readToEnd -- Lê todo o conteúdo do arquivo
  return content

#eval readFileContentA "add.data"




-- Função para ler um arquivo e retornar como uma string
def readFileAsString (filePath : String) : IO String := do
  IO.FS.readFile filePath

-- Função de parsing que toma uma string de entrada e tenta analisá-la
def parseImpTestEval (input : String) : IO (Option Syntax) := do
  -- Tenta analisar o código com a categoria 'imp_TestEval'
  let parser := Lean.Parser.term
  match parser input with
  | except.ok result => return some result
  | except.error _ => return none

-- Função principal que lê o arquivo e tenta fazer o parsing
def processFile (filePath : String) : IO Unit := do
  -- Lê o conteúdo do arquivo
  let content ← readFileAsString filePath
  -- Tenta fazer o parsing do conteúdo
  let result ← parseImpTestEval content
  match result with
  | some stx => IO.println s!"Parsing success: {stx}"
  | none => IO.println "Parsing failed."

-- Exemplo de uso
#eval processFile "add.data"


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
---- Inicio da Sintaxe
def regComp (reg : Register) (regCode : RegisterCode) : Bool :=
  match reg with
  | Register.mk regCode' _cont =>
  match regCode', regCode with
  | RegisterCode.r0, RegisterCode.r0 => true
  | RegisterCode.r1, RegisterCode.r1 => true
  | RegisterCode.r2, RegisterCode.r2 => true
  | RegisterCode.r3, RegisterCode.r3 => true
  | RegisterCode.r4, RegisterCode.r4 => true
  | RegisterCode.r5, RegisterCode.r5 => true
  | RegisterCode.r6, RegisterCode.r6 => true
  | RegisterCode.r7, RegisterCode.r7 => true
  | RegisterCode.r8, RegisterCode.r8 => true
  | RegisterCode.r9, RegisterCode.r9 => true
  | RegisterCode.r10, RegisterCode.r10 => true
  | _ , _=> false


def getDestCode (destReg : DestinationReg) :  RegisterCode  :=
  match destReg with
    | DestinationReg.mk x => x

def getSrcCode (srcReg : SourceReg) :  RegisterCode  :=
  match srcReg with
    | SourceReg.mk x => x

def getNatCont (cont : Content) :  ℕ  :=
  match cont with
    | Content.mk nat => nat

def getCont (reg : Register) :  ℕ  :=
  match reg with
    | Register.mk _ cont => (getNatCont cont)


def getReg (regs : Registers) (regCode : RegisterCode) : ℕ  :=
  match regs with
  | Registers.Nil reg' => (getCont reg')
  | Registers.Cons reg' regs' =>
    match (regComp reg' regCode) with
    | true => (getCont reg')
    | false => (getReg regs' regCode)

def getNatImm (imm : Immediate) :  ℕ  :=
  match imm with
    | Immediate.mk nat => nat

def saveAtReg (reg : Register) (regCode : RegisterCode) (val : ℕ ) : Register :=
  match (regComp reg regCode) with
  | true =>
    match reg with
    | Register.mk rCode _ => Register.mk rCode (Content.mk val)
  | false => reg

partial def saveAtRegs (regs : Registers) (regCode : RegisterCode) (val : ℕ ) : Registers :=
  match regs with
  | Registers.Nil r => Registers.Nil (saveAtReg r regCode val )
  | Registers.Cons r rs => Registers.Cons (saveAtReg r regCode val ) (saveAtRegs rs regCode val)

def execMsb (msb : Msb) (x y : ℕ ) : ℕ  :=
  match msb with
  | Msb.bpf_add => x + y
  | Msb.bpf_sub => x - y
  | Msb.bpf_mul => x * y
  | Msb.bpf_div => x / y
  | Msb.bpf_mov => y
  | _ => 0



def applyWord (regs : Registers) (word : Word) : Registers :=
  match word with
  | Word.mk imm _offset srcReg destReg opCode =>
    match opCode with
        | OpCode.Eof => regs
        | OpCode.mk msb source _lsb => -- (saveAtReg regs (execWord msb source ) )
          match msb with
          | Msb.bpf_end => regs
          | _ =>
            match source with
            | Source.bpf_x => (saveAtRegs regs (getDestCode destReg) (execMsb msb (getReg regs (getDestCode destReg)) (getReg regs (getSrcCode srcReg))  ) )
            | Source.bpf_k => (saveAtRegs regs (getDestCode destReg) (execMsb msb (getReg regs (getDestCode destReg)) (getNatImm imm)  ) )


def applyWordJmp (instr : Instructions) (word : Word) : Instructions :=
  match word with
  | Word.mk imm offset srcReg destReg opCode =>
  match instr, offset with
    | Instructions.Nil _w, Offset.mk _ => Instructions.Nil (Word.mk imm offset srcReg destReg OpCode.Eof)
    | Instructions.Cons _w ws, Offset.mk off => applyWordJmp ws (Word.mk imm (Offset.mk (off-1)) srcReg destReg opCode)
    | _, Offset.Exit => Instructions.Nil (Word.mk imm offset srcReg destReg OpCode.Eof)

def exeMainFuel (prog : Program) (fuel : ℕ ) : Program :=
  match fuel with
  | 0 => prog
  | fuel' + 1 =>
    match prog with
    | Program.mk regs instr (Pc.mk pc)=>
      match instr with
      | Instructions.Nil _word => prog
      | Instructions.Cons word instr' =>
        match word with
        | Word.mk _imm _offser _srcReg _destReg opCode =>
          match opCode with
          | OpCode.Eof => prog
          | OpCode.mk _msb _source lsb =>
            let pc' := (Pc.mk (pc+1))
            match lsb with
            | Lsb.bpf_ld => exeMainFuel (Program.mk (applyWord regs word) instr' pc') fuel'
            | Lsb.bpf_ldx => exeMainFuel (Program.mk (applyWord regs word) instr' pc') fuel'
            | Lsb.bpf_st => exeMainFuel (Program.mk (applyWord regs word) instr' pc') fuel'
            | Lsb.bpf_stx => exeMainFuel (Program.mk (applyWord regs word) instr' pc') fuel'
            | Lsb.bpf_alu => exeMainFuel (Program.mk (applyWord regs word) instr' pc') fuel'
            | Lsb.bpf_jmp => exeMainFuel (Program.mk regs (applyWordJmp instr' word)  pc') fuel'
            | Lsb.bpf_jmp32 => exeMainFuel (Program.mk regs (applyWordJmp instr' word)  pc') fuel'
            | Lsb.bpf_alu64 => exeMainFuel (Program.mk (applyWord regs word) instr' pc') fuel'




#eval exeMainFuel {exe|
  %r1 7 %r2 8 %r3 9
  (5 0 %r1 %r2 bpf_add bpf_x bpf_alu 5 0 %r1 %r2 bpf_add bpf_x bpf_alu 15 10 %r1 %r3 bpf_end bpf_k bpf_alu)
  0
} 10

#eval exeMainFuel {exe|
  %r0 0 %r1 0 %r2 0 %r3 0
  (
  2 0 %r2 %r1 bpf_mov bpf_k bpf_alu
  6 0 %r1 %r2 bpf_mov bpf_k bpf_alu
  5 0 %r1 %r2 bpf_add bpf_x bpf_alu
  5 0 %r1 %r2 bpf_add bpf_x bpf_alu
  15 10 %r1 %r3 bpf_end bpf_k bpf_alu)
  0
} 10
