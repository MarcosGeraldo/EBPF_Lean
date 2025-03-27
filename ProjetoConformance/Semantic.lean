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
