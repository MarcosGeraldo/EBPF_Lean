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

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
-- Inicio da semantica do Ebpf

-------Memoria de registradores do eBPF
structure Registers where
  r0 : Nat
  r1 : Nat
  r2 : Nat
  r3 : Nat
  r4 : Nat
  r5 : Nat
  r6 : Nat
  r7 : Nat
  r8 : Nat
  r9 : Nat
deriving Repr

-------------------Definição da Pilha de Memoria
structure MemorySpace where
  data : Fin 512 → Nat

inductive StackWord
  | nil : StackWord
  | mk : Char → Char → StackWord → StackWord
deriving Repr

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
| bpf_ja : Msb
| bpf_jeq : Msb
| bpf_jne : Msb
| bpf_jneq : Msb
| bpf_ldh : Msb
| bpf_ldb : Msb
| bpf_ldxh : Msb
| bpf_ldxw : Msb
| bpf_and : Msb
| bpf_or : Msb

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

-----Testes da Semantica

def Ex_Content := Content.mk 5
def Ex_Immediate := Immediate.mk 25
def Ex_Pc := Pc.mk 0
def Ex_Offset := Offset.mk 0
def Ex_OpCode : OpCode := OpCode.mk Msb.bpf_add Source.bpf_k Lsb.bpf_alu
def Ex_Word : Word := Word.mk Ex_Immediate Ex_Offset (SourceReg.mk RegisterCode.r2) (DestinationReg.mk RegisterCode.r3) Ex_OpCode
def Ex_Instructions := Instructions.Cons Ex_Word (Instructions.Cons Ex_Word (Instructions.Nil Ex_Word))




#eval Ex_Content
#eval Ex_Immediate
#eval Ex_Pc
#eval Ex_Offset
#eval Ex_OpCode
#eval Ex_Word
#eval Ex_Instructions

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
---- Inicio da semantica para ler o padrão dos Testes de Conformidade


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
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
----- Inicio do parser para ler os testes de conformidade

declare_syntax_cat imp_StackWord

syntax char char : imp_StackWord  -- Caso base
syntax char char imp_StackWord : imp_StackWord


partial def elabStackWord : Syntax → TermElabM Expr
  | `(imp_StackWord| $a:char $b:char) => do
      let aExpr ← mkAppM ``Char.ofNat #[mkRawNatLit a.getChar.toNat]
      let bExpr ← mkAppM ``Char.ofNat #[mkRawNatLit b.getChar.toNat]
      mkAppM ``StackWord.mk #[aExpr, bExpr, mkConst ``StackWord.nil]
  | `(imp_StackWord| $a:char $b:char $rest:imp_StackWord) => do
      let restExpr ← elabStackWord rest
      let aExpr ← mkAppM ``Char.ofNat #[mkRawNatLit a.getChar.toNat]
      let bExpr ← mkAppM ``Char.ofNat #[mkRawNatLit b.getChar.toNat]
      mkAppM ``StackWord.mk #[aExpr, bExpr, restExpr]
  | _ => throwUnsupportedSyntax

elab "test_elabStackWord" l:imp_StackWord : term => elabStackWord l

#eval test_elabStackWord 'a' 'b' 'c' 'd' 'e' 'f' '0' '0'

elab "{mem|" p: imp_StackWord "}" : term => elabStackWord p


--#reduce test_elabStackWord 'a' 'b' 'c' 'd' 'e' 'f'

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


declare_syntax_cat imp_Offset
syntax num : imp_Offset
syntax "exit" : imp_Offset


def elabOffset : Syntax → MetaM Expr
| `(imp_Offset| $n:num) => mkAppM ``Offset.mk #[mkNatLit n.getNat]
| `(imp_Offset| exit) => mkAppM ``Offset.Exit #[]
| _ => throwUnsupportedSyntax

elab "test_elabOffset" l:imp_Offset : term => elabOffset l
#reduce test_elabOffset 3

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Content
syntax num : imp_Content

def elabContent : Syntax → MetaM Expr
| `(imp_Content| $n:num) => mkAppM ``Content.mk #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

elab "test_elabContent" l:imp_Content : term => elabContent l
#reduce test_elabContent 3

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


declare_syntax_cat imp_Immediate
syntax num : imp_Immediate

def elabImmediate : Syntax → MetaM Expr
| `(imp_Immediate| $n:num) => mkAppM ``Immediate.mk #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

elab "test_elabImmediate" l:imp_Immediate : term => elabImmediate l
#reduce test_elabImmediate 3


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


declare_syntax_cat imp_OpCodeK
syntax "exit" : imp_OpCodeK
syntax "mov32" : imp_OpCodeK
syntax "add32" : imp_OpCodeK
syntax "sub32" : imp_OpCodeK
syntax "mul32" : imp_OpCodeK
syntax "div32" : imp_OpCodeK
syntax "jne" : imp_OpCodeK
syntax "ja" : imp_OpCodeK
syntax "jeq" : imp_OpCodeK
syntax "jneq" : imp_OpCodeK
syntax "ldh" : imp_OpCodeK
syntax "ldb" : imp_OpCodeK
syntax "ldxh" : imp_OpCodeK
syntax "ldxw" : imp_OpCodeK
syntax "and" : imp_OpCodeK
syntax "or" : imp_OpCodeK

partial def elabOpCodeK : Syntax → MetaM Expr
| `(imp_OpCodeK| add32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_add [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| sub32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sub [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| mul32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mul [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| div32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_div [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| exit) => return .const ``OpCode.Eof []
| `(imp_OpCodeK| mov32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mov [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| ja) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ja [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jeq) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jeq [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jne) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jne [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jneq) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jneq [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| ldh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ld []]
| `(imp_OpCodeK| ldb) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldb [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ld []]
| `(imp_OpCodeK| and) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_and [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| or) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_or [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| ldxh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeK| ldxw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxw [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ldx []]
| _ => throwUnsupportedSyntax

elab "test_elabOpCodeK" e:imp_OpCodeK : term => elabOpCodeK e
#reduce test_elabOpCodeK add32
#reduce test_elabOpCodeK ldxw



--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


declare_syntax_cat imp_OpCodeX
syntax "exit" : imp_OpCodeX
syntax "mov32" : imp_OpCodeX
syntax "add32" : imp_OpCodeX
syntax "sub32" : imp_OpCodeX
syntax "mul32" : imp_OpCodeX
syntax "div32" : imp_OpCodeX
syntax "ja" : imp_OpCodeX
syntax "jeq" : imp_OpCodeX
syntax "jne" : imp_OpCodeX
syntax "jneq" : imp_OpCodeX
syntax "ldh" : imp_OpCodeX
syntax "ldb" : imp_OpCodeX
syntax "ldxh" : imp_OpCodeX
syntax "ldxw" : imp_OpCodeX
syntax "and" : imp_OpCodeX
syntax "or" : imp_OpCodeX

partial def elabOpCodeX : Syntax → MetaM Expr
| `(imp_OpCodeX| add32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_add [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| sub32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sub [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| mul32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mul [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| div32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_div [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| exit) => return .const ``OpCode.Eof []
| `(imp_OpCodeX| mov32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mov [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| jeq) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jeq [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jne) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jne [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jneq) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jneq [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| ldh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ld []]
| `(imp_OpCodeX| ldb) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldb [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ld []]
| `(imp_OpCodeX| and) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_and [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| or) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_or [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| ldxh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeX| ldxw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxw [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ldx []]

| _ => throwUnsupportedSyntax

elab "test_elabOpCodeX" e:imp_OpCodeX : term => elabOpCodeX e
#reduce test_elabOpCodeK add32


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Word

syntax imp_OpCodeX imp_DestinationReg "," imp_SourceReg : imp_Word
syntax imp_OpCodeK imp_DestinationReg "," imp_Immediate : imp_Word
syntax imp_OpCodeK imp_DestinationReg "," imp_Immediate "," imp_Offset : imp_Word
syntax imp_OpCodeX imp_DestinationReg "," imp_SourceReg "," imp_Offset : imp_Word
syntax imp_OpCodeK imp_DestinationReg "," " [" imp_Offset "]" : imp_Word
syntax imp_OpCodeX imp_DestinationReg "," " [" imp_SourceReg "+" imp_Offset "]" : imp_Word
syntax imp_OpCodeK imp_Offset : imp_Word
syntax "exit" : imp_Word

-- Adequar para as possiveis diferentes classes
def elabWord : Syntax → MetaM Expr
-- add %r1 , %r2
| `(imp_Word| $a:imp_OpCodeX $b:imp_DestinationReg , $c:imp_SourceReg) => do
  let opCode ← elabOpCodeX a
  let destReg ← elabDestinationReg b
  let srcReg ← elabSourceReg c
  let offsetExpr := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  let immExpr := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  return mkAppN (Expr.const ``Word.mk []) #[immExpr, offsetExpr, srcReg, destReg, opCode]
-- add %r1 , 5
| `(imp_Word| $a:imp_OpCodeK $b:imp_DestinationReg , $c:imp_Immediate) => do
  let opCode ← elabOpCodeK a
  let dstReg ← elabDestinationReg b
  let imm ← elabImmediate c
  let offsetExpr := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  let regExpr := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, regExpr , dstReg, opCode]
-- jne %r1 , 22, 10
| `(imp_Word| $a:imp_OpCodeK $b:imp_DestinationReg , $c:imp_Immediate , $d:imp_Offset  ) => do
  let opCode ← elabOpCodeK a
  let dstReg ← elabDestinationReg b
  let imm ← elabImmediate c
  let offsetExpr ← elabOffset d
  let regExpr := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, regExpr , dstReg, opCode]
-- jne %r1 , %r2, 10
| `(imp_Word| $a:imp_OpCodeX $b:imp_DestinationReg , $c:imp_SourceReg , $d:imp_Offset ) => do
  let opCode ← elabOpCodeX a
  let srcReg ← elabSourceReg c
  let dstReg ← elabDestinationReg b
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let offsetExpr ← elabOffset d
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, srcReg , dstReg, opCode]
-- ldxh %r1 , [10]
| `(imp_Word| $a:imp_OpCodeK $b:imp_DestinationReg , [ $c:imp_Offset ] ) => do
  let opCode ← elabOpCodeK a
  let dstReg ← elabDestinationReg b
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let offsetExpr ← elabOffset c
  let regExpr := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, regExpr , dstReg, opCode]
-- ldxh %r2 , [%r1 + 10]
| `(imp_Word| $a:imp_OpCodeX $b:imp_DestinationReg , [ $c:imp_SourceReg + $d:imp_Offset ] ) => do
  let opCode ← elabOpCodeX a
  let srcReg ← elabSourceReg c
  let dstReg ← elabDestinationReg b
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let offsetExpr ← elabOffset d
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, srcReg , dstReg, opCode]
-- ja 5
| `(imp_Word| $a:imp_OpCodeK $b:imp_Offset ) => do
  let opCode ← elabOpCodeK a
  let offsetExpr ← elabOffset b
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let regExprSrc := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  let regExprDst := mkAppN (Expr.const ``DestinationReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, regExprSrc , regExprDst, opCode]

| `(imp_Word| exit) => do
  let immExpr := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let offsetExpr := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  let regExprS := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  let regExprD := mkAppN (Expr.const ``DestinationReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  let extExpr := Expr.const ``OpCode.Eof []
  return mkAppN (Expr.const ``Word.mk []) #[immExpr, offsetExpr, regExprS, regExprD, extExpr]

| _ => throwUnsupportedSyntax

elab "test_elabWord" e:imp_Word : term => elabWord e
#reduce test_elabWord mov32 %r3, 0
#reduce test_elabWord add32 %r3, %r4
#reduce test_elabWord ldh %r1, [10]
#reduce test_elabWord ldh %r1, [%r1+ 10]
#reduce test_elabWord jne %r1, 5, 10
#reduce test_elabWord ldh %r1, %r2, 10

#reduce test_elabWord exit


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


declare_syntax_cat imp_Instructions
syntax imp_Word : imp_Instructions
syntax imp_Word imp_Instructions : imp_Instructions

partial def elabInstructions : Syntax → MetaM Expr
| `(imp_Instructions| $l:imp_Word $b:imp_Instructions) => do
  let l ← elabWord l
  let b ← elabInstructions b
  mkAppM ``Instructions.Cons #[l, b]
| `(imp_Instructions| $l:imp_Word) => do
  let l ← elabWord l
  mkAppM ``Instructions.Nil #[l]
| _ => throwUnsupportedSyntax

elab "test_elabInstructions" e:imp_Instructions : term => elabInstructions e
#reduce test_elabInstructions
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


declare_syntax_cat imp_Pc
syntax num : imp_Pc

def elabPc : Syntax → MetaM Expr
| `(imp_Pc| $n:num) => mkAppM ``Pc.mk #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

elab "test_elabPc" l:imp_Pc : term => elabPc l
#reduce test_elabPc 3


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

instance : Repr Registers where
  reprPrec regs _ :=
    s!"Registers(r0 := {regs.r0}, r1 := {regs.r1}, r2 := {regs.r2}, r3 := {regs.r3}, r4 := {regs.r4}, " ++
    s!"r5 := {regs.r5}, r6 := {regs.r6}, r7 := {regs.r7}, r8 := {regs.r8}, r9 := {regs.r9})"

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

instance : Repr MemorySpace where
  reprPrec mem _ :=
    let contents := List.filterMap (fun i =>
      if h : i < 512 then
        let idx : Fin 512 := ⟨i, h⟩  -- Converte ℕ para Fin 512 com prova explícita
        let val := mem.data idx
        if val ≠ 0 then some s!"{idx} -> {val}" else none
      else none) (List.range 512)  -- Garante que os índices estão dentro do limite
    let memStr := String.intercalate ", " contents
    s!"MemorySpace({memStr})"

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

instance : Repr Instructions where
  reprPrec ins _ :=
    let rec aux (instrs : Instructions) : List String :=
      match instrs with
      | Instructions.Nil w => [reprStr w]  -- Usa `reprStr` para obter um String
      | Instructions.Cons w rest => (reprStr w) :: aux rest
    let instrList := aux ins
    let instrStr := String.intercalate ", " instrList
    s!"Instructions([{instrStr}])"

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
#reduce test_elabComment # Este e um comentario com varios espacos data

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


declare_syntax_cat imp_TestEval
syntax "#" ident* "#" ident* "asm" imp_Instructions "result" num : imp_TestEval

def elabTestEval : Syntax → MetaM Expr
| `(imp_TestEval| # $_* # $_* asm $b:imp_Instructions result $c:num) => do
  --let a : Expr := mkStrLit (String.join (List.map (fun id => id.getId.toString) (a.toList)))   -- Converte o identificador em uma string
  let b ← elabInstructions b  -- Usa a função já existente para elaborar as instruções
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


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<
---- Inicio da Sintaxe de eBPF

-- Converte um número natural para uma lista de bits (binário)
def natToBinAux (n : Nat) (fuel : Nat) : List Bool :=
match fuel with
| 0 => []
| fuel' + 1 =>
  match n with
  | 0 => []
  | _ => (n % 2 == 1) :: (natToBinAux (n / 2) fuel')

#eval 15/2
#eval 15%2



def natToBin (n : Nat) (fuel : Nat) : List Bool :=
  List.reverse ( natToBinAux n fuel)

#eval List.reverse (0 :: 1 :: 1 :: 1 :: [])



-- Realiza a operação AND bit a bit entre duas listas de bits
def bitwiseAnd (a b : List Bool) : List Bool :=
  let len := max a.length b.length
  let aPadded := List.replicate (len - a.length) false ++ a
  let bPadded := List.replicate (len - b.length) false ++ b
  List.zipWith (· && ·) aPadded bPadded


-- Converte uma lista de bits de volta para um número natural
def binToNat (bits : List Bool) : Nat :=
  bits.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0

#eval binToNat (natToBin 15879454 1000000) --ok

#eval bitwiseAnd [true,true,true,true] [true,true,true,false,false,true,true]
#eval (natToBin 9 9)
#eval (natToBin 17 17)
#eval binToNat (bitwiseAnd (natToBin 9 9) (natToBin 17 17))

-- Função principal que faz a operação AND lógica bit a bit
def andLogical (x y : Nat) : Nat :=
  let fuel := max x y + 1  -- Define um limite para evitar loops infinitos
  let binX := natToBin x fuel
  let binY := natToBin y fuel
  let resultBin := bitwiseAnd binX binY
  binToNat resultBin

-- Testes
#eval andLogical 5 3  -- 5 = 101, 3 = 011 → AND = 001 (1)
#eval andLogical 12 6 -- 12 = 1100, 6 = 0110 → AND = 0100 (4)
#eval andLogical 7 14 -- 7 = 0111, 14 = 1110 → AND = 0110 (6)


def bitwiseOr (a b : List Bool) : List Bool :=
  let len := max a.length b.length
  let aPadded := List.replicate (len - a.length) false ++ a
  let bPadded := List.replicate (len - b.length) false ++ b
  List.zipWith (· || ·) aPadded bPadded

-- Função principal que faz a operação OR lógica bit a bit
def orLogical (x y : Nat) : Nat :=
  let fuel := max x y + 1  -- Define um limite para evitar loops infinitos
  let binX := natToBin x fuel
  let binY := natToBin y fuel
  let resultBin := bitwiseOr binX binY
  binToNat resultBin

#eval bitwiseAnd [true,true,true,true,true ] [true,false]
-- Testes
#eval orLogical 5 3  -- 5 = 101, 3 = 011 → OR = 111 (7)
#eval orLogical 12 6 -- 12 = 1100, 6 = 0110 → OR = 1110 (14)
#eval orLogical 7 14 -- 7 = 0111, 14 = 1110 → OR = 1111 (15)

def emptyMemory : MemorySpace :=
  { data := fun _ => 0 }

def readReg (regs : Registers) (r : RegisterCode) : Nat :=
  match r with
  | RegisterCode.r0 => regs.r0
  | RegisterCode.r1 => regs.r1
  | RegisterCode.r2 => regs.r2
  | RegisterCode.r3 => regs.r3
  | RegisterCode.r4 => regs.r4
  | RegisterCode.r5 => regs.r5
  | RegisterCode.r6 => regs.r6
  | RegisterCode.r7 => regs.r7
  | RegisterCode.r8 => regs.r8
  | RegisterCode.r9 => regs.r9
  | _ => 0

def writeReg (regs : Registers) (r : RegisterCode) (val : Nat) : Registers :=
  match r with
  | RegisterCode.r0 => { regs with r0 := val }
  | RegisterCode.r1 => { regs with r1 := val }
  | RegisterCode.r2 => { regs with r2 := val }
  | RegisterCode.r3 => { regs with r3 := val }
  | RegisterCode.r4 => { regs with r4 := val }
  | RegisterCode.r5 => { regs with r5 := val }
  | RegisterCode.r6 => { regs with r6 := val }
  | RegisterCode.r7 => { regs with r7 := val }
  | RegisterCode.r8 => { regs with r8 := val }
  | RegisterCode.r9 => { regs with r9 := val }
  | _ => regs

def writeMem (mem : MemorySpace) (addr : Fin 512) (val : Nat) : MemorySpace :=
  { data := fun i => if i = addr then val else mem.data i }

def readMem (mem : MemorySpace) (addr : Fin 512) : Nat :=
  mem.data addr

-- Le o espaço de memoria retornando o valor natural contido no indice index
def readMemNat (mem : MemorySpace) (index : Nat) : Nat :=
  mem.data (⟨ index % 512, by {
  have h : index % 512 < 512 := Nat.mod_lt index (by decide)
  exact h
}⟩)

-- Convert a hexadecimal character to a natural number
def hexCharToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    Char.toNat c - Char.toNat '0'
  else if 'a' ≤ c ∧ c ≤ 'f' then
    10 + Char.toNat c - Char.toNat 'a'
  else if 'A' ≤ c ∧ c ≤ 'F' then
    10 + Char.toNat c - Char.toNat 'A'
  else
    panic! s!"Invalid hexadecimal character: {c}"

-- Convert a list of hexadecimal characters to a natural number
def hexToNatList (s : List Char) (acc : Nat) : Nat :=
  match s with
  | [] => acc
  | c :: rest =>
    let n := hexCharToNat c
    hexToNatList rest (16 * acc + n)

-- Convert a hexadecimal string to a natural number
def hexToNat (s : String) : Nat :=
  hexToNatList s.toList 0

-- Example usage
#check hexToNat "a246dadf4"  -- Output: 43494831220
#eval hexToNat "0"          -- Output: 0
#eval hexToNat "A1F"        -- Output: 2591

-- Converte um número (0-15) para o caractere hexadecimal correspondente
def natToHexChar (n : ℕ) : Char :=
  if n < 10 then
    Char.ofNat (n + 48)  -- '0' é representado por 48 na tabela ASCII
  else
    Char.ofNat (n - 10 + 97)  -- 'a' é representado por 97 na tabela ASCII

-- Função recursiva para gerar a representação hexadecimal como uma lista de caracteres
def natToHexRec (n : ℕ) : List Char :=
  if n = 0 then []
  else natToHexRec (n / 16) ++ [natToHexChar (n % 16)]

-- Função principal que lida com o caso em que n = 0
def natToHexCharList (n : ℕ) : List Char :=
  if n = 0 then ['0']
  else natToHexRec n

def natToHexString (n : ℕ) : String :=
  if n = 0 then String.mk ['0']
  else String.mk (natToHexRec n)

#eval natToHexCharList 255  -- Saída esperada: ['f', 'f']
#eval natToHexString 255  -- Saída esperada: ['f', 'f']

#check hexToNat "a246dadf4"  -- Output: 43494831220
#eval hexToNat "0"          -- Output: 0
#eval hexToNat "A1F"        -- Output: 2591
#eval natToHexCharList 255  -- Saída esperada: ['f', 'f']
#eval natToHexString 255  -- Saída esperada: "ff"

theorem provaFin (index : Nat) : index % 512 < 512 := by
  -- Introduce the fact using `have`
  have h : index % 512 < 512 := Nat.mod_lt index (by decide)
  -- Use the fact to prove the goal
  exact h

def createStackMemory (index : ℕ )(stack : MemorySpace) (input : StackWord) : MemorySpace :=
  match input with
  | StackWord.mk charA charB rest =>
    let value := hexToNatList [charA,charB] 0
    createStackMemory (index + 1) (writeMem stack ⟨ index % 512, provaFin index⟩ value) rest
  | StackWord.nil => stack

#check ['a', 'a']

#eval createStackMemory 0 emptyMemory {mem| '0' '0' '0''0' 'c''0' '9''f' 'a''0' '9''7' '0''0' 'a' '0' }

def getDestCode (destReg : DestinationReg) :  RegisterCode  :=
  match destReg with
    | DestinationReg.mk x => x

def getSrcCode (srcReg : SourceReg) :  RegisterCode  :=
  match srcReg with
    | SourceReg.mk x => x

def getNatCont (cont : Content) :  ℕ  :=
  match cont with
    | Content.mk nat => nat

def getNatImm (imm : Immediate) :  ℕ  :=
  match imm with
    | Immediate.mk nat => nat

def execMsb (msb : Msb) (x y : ℕ ) : ℕ  :=
  match msb with
  | Msb.bpf_add => x + y
  | Msb.bpf_sub => x - y
  | Msb.bpf_mul => x * y
  | Msb.bpf_div => x / y
  | Msb.bpf_mov => y
  | Msb.bpf_and => andLogical x y
  | Msb.bpf_or => orLogical x y
  | _ => 0


def applyWordAlu (regs : Registers) (word : Word) : Registers :=
  match word with
  | Word.mk imm _offset srcReg destReg opCode =>
    match opCode with
        | OpCode.Eof => regs
        | OpCode.mk msb source _lsb => -- (saveAtReg regs (execWord msb source ) )
          match msb with
          | Msb.bpf_end => regs
          | _ =>
            match source with
            | Source.bpf_x => (writeReg regs (getDestCode destReg) (execMsb msb (readReg regs (getDestCode destReg)) (readReg regs (getSrcCode srcReg))  ) )
            | Source.bpf_k => (writeReg regs (getDestCode destReg) (execMsb msb (readReg regs (getDestCode destReg)) (getNatImm imm)  ) )


--Criar função que dado stack indice e tamanho retorna o valor desejado

#eval (toString 10).toList

--Passar tamanho da palavra -1
--Começa a obter os valores a partir do indice passado e guarda a palavra de forma inversa igual ao subnet
def returnMemoryBlockChar ( stack : MemorySpace ) ( index: ℕ ) ( size : ℕ ) : List Char  :=
  match size with
  | 0 =>
    let n := natToHexCharList (readMemNat stack index)
    match n.length with
    | 1 => '0' :: n
    | _ => n
  | size' + 1 =>
    let valRet:= (returnMemoryBlockChar stack (index+1) size')
    ---let valRetChar := natToHexCharList valRet
    let valChar := natToHexCharList (readMemNat stack index)
    match valChar.length with
    | 1 => valRet ++ ('0' :: valChar)
    | _ => valRet ++ valChar

#eval '0' :: ['1']
#eval ['0'].length
#eval natToHexCharList 16885952
#eval hexToNatList ['1', '0'] 0
#eval 0x0101a8c0
#eval hexToNat "0101a8c0"
--Tratar de sempre retornar uma dupla de valores

#eval Char.ofNat 11

def returnMemoryBlockNat ( stack : MemorySpace ) ( index: ℕ ) ( size : ℕ ) : ℕ  :=
  hexToNatList (returnMemoryBlockChar stack index size) 0

def inputMemo :=
  let mem1 := emptyMemory
  let mem2 := writeMem mem1 ⟨1, by decide⟩ 1  -- Escreve 42 na posição 10
  let mem3 := writeMem mem2 ⟨2, by decide⟩ 2 -- Escreve 100 na posição 20
  let mem4 := writeMem mem3 ⟨3, by decide⟩ 3 -- Escreve 100 na posição 20
  let mem5 := writeMem mem4 ⟨4, by decide⟩ 4 -- Escreve 100 na posição 20
  let mem6 := writeMem mem5 ⟨5, by decide⟩ 11 -- Escreve 100 na posição 20
  let mem7 := writeMem mem6 ⟨6, by decide⟩ 12 -- Escreve 100 na posição 20
  let mem8 := writeMem mem7 ⟨7, by decide⟩ 13 -- Escreve 100 na posição 20
  let mem9 := writeMem mem8 ⟨8, by decide⟩ 14 -- Escreve 100 na posição 20
  let mem10 := writeMem mem9 ⟨0, by decide⟩ 3 -- Escreve 100 na posição 20
  mem10

--           cc 3b bf fa 08 00 45 10
--Val size   -  1  0
--Val index  0  1  2   3  4  5  6  7

--           3  1  2  3  4  11 12 13 14
--Val size   -  1  0
--Val index  0  1  2  3  4  5  6  7  8
#eval returnMemoryBlockNat inputMemo 4 1  -- '4' '2'

#eval (natToHexCharList 14)
#eval hexToNatList ((natToHexCharList 12) ++ (natToHexCharList 11) ++ (natToHexCharList 4)) 0

#eval inputMemo

def returnMemoryBlock (regs : Registers) (dstReg : DestinationReg) (stack : MemorySpace) (index:Nat) (msb : Msb) : Registers :=
  match msb with
  | Msb.bpf_ldh => writeReg regs (getDestCode dstReg) (returnMemoryBlockNat stack index 0)
  | Msb.bpf_ldb => writeReg regs (getDestCode dstReg) (returnMemoryBlockNat stack index 0)
  | Msb.bpf_ldxh => writeReg regs (getDestCode dstReg) (returnMemoryBlockNat stack index 1)
  | Msb.bpf_ldxw => writeReg regs (getDestCode dstReg) (returnMemoryBlockNat stack index 3)
  | _ => regs

def applyWordMemoryLD (regs : Registers)(stack : MemorySpace) (word : Word) : Registers :=
  match word with
  | Word.mk _imm offset srcReg destReg opCode =>
    match opCode with
        | OpCode.Eof => regs
        | OpCode.mk msb source _lsb =>
          match offset with
          | Offset.Exit => regs
          | Offset.mk offVal =>
            match source with
            | Source.bpf_k =>
              let index := offVal
              returnMemoryBlock regs destReg stack index msb
            | Source.bpf_x =>
              let index := offVal + readReg regs (getSrcCode srcReg)
              returnMemoryBlock regs destReg stack index msb

def applyWordMemorySK (_regs : Registers)(stack : MemorySpace) (word : Word) : MemorySpace :=
  match word with
  | Word.mk _imm _offset _srcReg _destReg _opCode => stack

def evalJmpCond (regs : Registers) (word : Word) : Bool :=
  match word with
    | Word.mk imm _offset srcReg destReg opCode =>
    match opCode with
      |OpCode.Eof => false
      |OpCode.mk msb source _lsb =>
        match msb with
        | Msb.bpf_ja => true
        | _ =>
          match source with
          | Source.bpf_k =>
            match msb with
            | Msb.bpf_jne=> (getNatImm imm) != readReg regs (getDestCode destReg)
            --| Msb.bpf_jneq=> (getNatImm imm) != readReg regs (getDestCode destReg)
            | Msb.bpf_jeq=> (getNatImm imm) == readReg regs (getDestCode destReg)

            | _ => false
          | Source.bpf_x =>
            match msb with
            | Msb.bpf_jne=> readReg regs (getSrcCode srcReg) != readReg regs (getDestCode destReg)
            --| Msb.bpf_jneq=> readReg regs (getSrcCode srcReg) != readReg regs (getDestCode destReg)
            | Msb.bpf_jeq=> readReg regs (getSrcCode srcReg) == readReg regs (getDestCode destReg)

            | _ => false


def execJmp (instr : Instructions) (word : Word) : Instructions :=
  match word with
  | Word.mk imm offset srcReg destReg opCode =>
    match instr, offset with
     | Instructions.Cons _ _, Offset.mk 0 => instr
     | Instructions.Cons _w ws, Offset.mk off => execJmp ws (Word.mk imm (Offset.mk (off-1)) srcReg destReg opCode)
     | Instructions.Nil _w, Offset.mk _ => Instructions.Nil (Word.mk imm offset srcReg destReg OpCode.Eof)
     | _, Offset.Exit => Instructions.Nil (Word.mk imm offset srcReg destReg OpCode.Eof)

def applyWordJmp (regs : Registers) (instr : Instructions) (word : Word) : Instructions :=
  match word with
  | Word.mk _imm _offset _srcReg _destReg opCode =>
    match opCode with
      |OpCode.Eof => instr
      |OpCode.mk msb _source _lsb =>
        match msb with
        | Msb.bpf_ja => execJmp instr word
        | _ =>
          match (evalJmpCond regs word) with
          | true => execJmp instr word
          | false => instr

def exeMain (stack : MemorySpace) (regs : Registers) (instr : Instructions) (fuel : ℕ) : MemorySpace × Registers × Instructions :=
  match fuel with
  | 0 => (stack, regs, instr)  -- Retorna o estado atual sem executar mais instruções
  | fuel' + 1 =>
      match instr with
      | Instructions.Nil _word => (stack, regs, instr)  -- Programa terminou
      | Instructions.Cons word instr' =>
        match word with
        | Word.mk _imm _offset _srcReg _destReg opCode =>
          match opCode with
          | OpCode.Eof => (stack, regs, instr)  -- Parar execução no EOF
          | OpCode.mk _msb _source lsb =>
            match lsb with
            | Lsb.bpf_alu64 | Lsb.bpf_alu =>
              -- Operações que alteram os registradores
              let regs' := applyWordAlu regs word
              exeMain stack regs' instr' fuel'

            | Lsb.bpf_ld | Lsb.bpf_ldx =>
              -- Operações que alteram a memória
              let regs' := applyWordMemoryLD regs stack word
              exeMain stack regs' instr' fuel'

            | Lsb.bpf_st | Lsb.bpf_stx =>
              -- Operações que alteram a memória
              let stack' := applyWordMemorySK regs stack word
              exeMain stack' regs instr' fuel'

            | Lsb.bpf_jmp | Lsb.bpf_jmp32 =>
              -- Operações de salto que alteram as instruções
              let instr'' := applyWordJmp regs instr' word
              exeMain stack regs instr'' fuel'


def initialRegisters : Registers :=
  { r0 := 0, r1 := 0, r2 := 0, r3 := 0, r4 := 0
  , r5 := 0, r6 := 0, r7 := 0, r8 := 0, r9 := 0 }

-- Criar função que recebe test eval, cria a lista vazia de registradores e chama exeMainFuel

def exeConformance ( input : TestEval ) (stack : MemorySpace) : MemorySpace × Registers × Instructions :=
  match input with
  | TestEval.mk instructions _expectedResult =>
    --let program := emptyMemory initialRegisters instructions
    let fuel := 10000
    let returnedResult := exeMain stack initialRegisters instructions fuel
    returnedResult

elab "{exe|" p: imp_TestEval "}" : term => elabTestEval p


def inputMem :=
  let mem1 := emptyMemory
  let mem2 := writeMem mem1 ⟨1, by decide⟩ 11  -- Escreve 42 na posição 10
  let mem3 := writeMem mem2 ⟨2, by decide⟩ 12 -- Escreve 100 na posição 20
  let mem4 := writeMem mem3 ⟨3, by decide⟩ 13 -- Escreve 100 na posição 20
  let mem5 := writeMem mem4 ⟨4, by decide⟩ 14 -- Escreve 100 na posição 20
  let mem6 := writeMem mem5 ⟨5, by decide⟩ 15 -- Escreve 100 na posição 20
  let mem7 := writeMem mem6 ⟨6, by decide⟩ 16 -- Escreve 100 na posição 20
  let mem8 := writeMem mem7 ⟨7, by decide⟩ 17 -- Escreve 100 na posição 20
  let mem9 := writeMem mem8 ⟨8, by decide⟩ 18 -- Escreve 100 na posição 20
  mem9

#eval exeConformance {exe|
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
ldh %r4, [6]
exit
result
0x10
} inputMem

#eval exeConformance {exe|
#Comentario com espacos
#Comentario com espacos
asm
mov32 %r0, 0xa
mov32 %r1, 0
--add32 %r0, 10
--add32 %r1, 5
ldh %r4, [%r1+2]
exit
result
0x10
} inputMem

#eval exeConformance {exe|
#Comentario com espacos
#Comentario com espacos
asm
mov32 %r0, 0
mov32 %r1, 1
add32 %r0, %r1
add32 %r0, %r1
add32 %r0, %r1
jeq %r1, 1, 0
add32 %r0, %r1
add32 %r0, %r1
add32 %r0, %r1
add32 %r0, %r1
result
0x10
} inputMem

def subnetMem :=
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

'2' '7' '2' '4' '0' '0' '0' '0' '0' '1' '0' '3' '0' '3' '0' '0' }

--Subnet
/-

mov %r2, 0xe
ldxh %r3, [%r1+12]
jne %r3, 0x81, L1
mov %r2, 0x12
ldxh %r3, [%r1+16]
and %r3, 0xffff
L1:
jne %r3, 0x8, L2
add %r1, %r2
mov %r0, 0x1
ldxw %r1, [%r1+16]
and %r1, 0xffffff
jeq %r1, 0x1a8c0, exit
L2:
mov %r0, 0x0
exit
-- mem
00 00 c0 9f a0 97 00 a0
cc 3b bf fa 08 00 45 10
00 3c 46 3c 40 00 40 06
73 1c c0 a8 01 02 c0 a8
01 01 06 0e 00 17 99 c5
a0 ec 00 00 00 00 a0 02
7d 78 e0 a3 00 00 02 04
05 b4 04 02 08 0a 00 9c
27 24 00 00 00 00 01 03
03 00

-/
--Offset == ao numero de linhas que se deseja pular
#eval exeConformance {exe|
#Comentario com espacos
#Comentario com espacos
asm
mov32 %r2, 0xe
ldxh %r3, [%r1+12]
jne %r3, 0x81, 3
mov32 %r2, 0x12
ldxh %r3, [%r1+16]
and %r3, 0xffff
jne %r3, 0x8, 4
add32 %r1, %r2
mov32 %r0, 0x1
ldxw %r1, [%r1+16]
mov32 %r5, %r1
and %r1, 0xffffff
jeq %r1, 0x1a8c0, 2
mov32 %r0, 0x0
exit
result
0x1
} subnetMem

def listCharBool (input : List Bool) : String :=
  match input with
  | [] => ""
  | x :: xs =>
   match x with
   | false => "0" ++ listCharBool xs
   | true =>  "1" ++ listCharBool xs

#eval returnMemoryBlockNat subnetMem 30 3 --16885952
#eval returnMemoryBlockChar subnetMem 30 3 --16885952

#eval natToHexCharList 1157312
#eval 0x0101a8c0
#eval natToBin 16777215 16777215 --0xffffff
#eval natToBin 16885952 16885952 --0x0101a8c0
#eval binToNat (natToBin 16885952 16885952)
#eval binToNat (natToBin 16777215 16777215)
#eval listCharBool (natToBin 0xffffff 0xffffff) --0xffffff
#eval listCharBool (natToBin 0x0101a8c0 0x0101a8c0) --0x0101a8c0
#eval binToNat (bitwiseAnd (natToBin 0xffffff 0xffffff) (natToBin 0x0101a8c0 0x0101a8c0))
#eval andLogical 0x0101a8c0 0xffffff

--"111111111111111111111111"
--"1000000011010100011000000"
--"1000000011010100011000000"
--"'000000'10000000'0'11010100011000000"
--  000000 10000000 0 11010100011000000 OrdemTrocada
--         111111111111111111111111
#eval andLogical 0x0101a8c0 0xffffff -- Corrigir
#eval 0x0101a8c0
#eval 0xffffff --16777215
#eval 0x1a8c0 --108736
#eval natToHexString 404225
#eval natToHexString 808450
-- r5 := 1157312, r6 := 50530
#eval natToHexString 1157312 --r5
#eval 0x11a8c0
#eval natToHexString 50530 --r6

--Testes de conformidade para ldxh e ldxw Passando
#eval exeConformance {exe|
#Comentario com espacos
#Comentario com espacos
asm
ldxh %r3, [%r1+2]
exit
result
0x1
}
(createStackMemory 0 emptyMemory
{mem|
 'a''a' 'b''b' '1''1' '2''2' 'c''c' 'd''d'
})
#eval 0x2211

#eval exeConformance {exe|
#Comentario com espacos
#Comentario com espacos
asm
ldxw %r3, [%r1+2]
exit
result
0x1
}
(createStackMemory 0 emptyMemory
{mem|
 'a''a' 'b''b' '1''1' '2''2' '3' '3' '4' '4' 'c''c' 'd' 'd'
})

#eval 0x44332211


-- Usar arquivos Lean para representar os programas eBPF
-- Testes de conformidade
-- Organizar os arquivos
-- Pesquisar um pouco dos pacotes Ipv4
-- Dia 28/03 ^^^^^^^^^^^^^
-- Doctum JM
-- Criar pacotes utilizando o slimCheck
-- Definir matematicamente a semantica que temos em Lean(V2)



/-
 Only allow IPv4 TCP packets:

         ldh [12] --Load half-word into A where A = 32 bit wide accumulator
         jne #0x800, drop
         ldb [23]
         jneq #6, drop
         ret #-1
         drop: ret #0
-/

/-
Only allow IPv4 TCP SSH traffic:

         ldh [12]
         jne #0x800, drop
         ldb [23]
         jneq #6, drop
         ldh [20]
         jset #0x1fff, drop
         ldxb 4 * ([14] & 0xf)
         ldh [x + 14]
         jeq #0x16, pass
         ldh [x + 16]
         jne #0x16, drop
         pass: ret #-1
         drop: ret #0
-/

/-

Pacote IPv4 + TCP (Permitido ✅)
Representação do Pacote (Hexadecimal)

Dest MAC   | Src MAC    | EtherType | IP Header ... | Protocol | TCP Header ...
FF:FF:FF:FF:FF:FF  11:22:33:44:55:66  08 00   45 00 00 3C ...  06   00 14 00 50 ...

Pacote IPv6 + TCP (Descartado ❌)
Dest MAC   | Src MAC    | EtherType | IPv6 Header ... | Protocol | TCP Header ...
FF:FF:FF:FF:FF:FF  11:22:33:44:55:66  86 DD   60 00 00 00 ...  06   00 14 00 50 ...

Pacote IPv4 + UDP (Descartado ❌)
Dest MAC   | Src MAC    | EtherType | IP Header ... | Protocol | UDP Header ...
FF:FF:FF:FF:FF:FF  11:22:33:44:55:66  08 00   45 00 00 3C ...  11   00 14 00 50 ...

Pacote Ethernet com ARP (Descartado ❌)
Dest MAC   | Src MAC    | EtherType | ARP Header ...
FF:FF:FF:FF:FF:FF  11:22:33:44:55:66  08 06   00 01 08 00 ...

-/


-- Tarefas Semana
-- Rodar os exemplos praticos de programas eBPF
-- Rodar os testes de conformidade

-- Compilar codigo em c para gerar os codigos eBPF






--Leio a entrada em Hexa -> Guardo na memoria como decimal
--> transformo para Hexa na hora de construir a palavra -> Armazeno no registrador como natural
