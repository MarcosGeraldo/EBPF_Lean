import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Defs
import Aesop
import Lean.Elab.Tactic
import Mathlib.Tactic.SlimCheck
import Init.System.IO
open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Term
open Lean.Syntax
open Lean Elab  Meta

set_option maxRecDepth 1000

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
  r10 : Nat
deriving Repr

-------------------Definição da Pilha de Memoria
structure MemorySpace where
  data : Fin 513 → Nat

inductive StackWord
  | nil : StackWord
  | mk : Char → Char → StackWord → StackWord
deriving Repr

inductive Immediate : Type
| mk : ℕ  → Immediate
| mkN : ℕ → Immediate
deriving Repr, DecidableEq

inductive Pc : Type
| mk : ℕ → Pc
deriving Repr

inductive Offset: Type
| mk : ℕ → Offset
| mkN : ℕ → Offset
| Exit : Offset
deriving Repr, DecidableEq

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
deriving Repr, DecidableEq

inductive Msb : Type
| bpf_add : Msb
| bpf_sub : Msb
| bpf_mul : Msb
| bpf_div : Msb
| bpf_sdiv : Msb
| bpf_end : Msb
| bpf_mod : Msb
| bpf_smod : Msb
| bpf_neg : Msb
| bpf_mov : Msb
| bpf_movsx1632 : Msb
| bpf_movsx1664 : Msb
| bpf_movsx3264 : Msb
| bpf_movsx832 : Msb
| bpf_movsx864 : Msb
| bpf_call_local : Msb
| bpf_ja : Msb
| bpf_jeq : Msb
| bpf_jge : Msb
| bpf_jle : Msb
| bpf_jne : Msb
| bpf_jlt : Msb
| bpf_jgt : Msb
| bpf_jset : Msb
| bpf_jsge : Msb
| bpf_jsgt : Msb
| bpf_jsle : Msb
| bpf_jslt : Msb
| bpf_jneq : Msb
| bpf_ldh : Msb
| bpf_ldxb : Msb
| bpf_ldxh : Msb
| bpf_ldxw : Msb
| bpf_lddw : Msb
| bpf_ldxdw : Msb
| bpf_ldxdh : Msb
| bpf_and : Msb
| bpf_or : Msb
| bpf_xor : Msb
| bpf_rsh : Msb
| bpf_lsh : Msb
| bpf_arsh : Msb
| bpf_be16 : Msb
| bpf_be32 : Msb
| bpf_be64 : Msb
| bpf_le16 : Msb
| bpf_le32 : Msb
| bpf_le64 : Msb
| bpf_swap16 : Msb
| bpf_swap32 : Msb
| bpf_swap64 : Msb
| bpf_stw : Msb
| bpf_sth : Msb
| bpf_stb : Msb
| bpf_stdw : Msb
| bpf_stxw : Msb
| bpf_stxh : Msb
| bpf_stxb : Msb
| bpf_stxdw : Msb
deriving Repr
/-
| bpf_ : Msb
| bpf_ : Msb
-/

inductive Source : Type
| bpf_k : Source
| bpf_x : Source
deriving Repr, DecidableEq

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



/-
#eval Ex_Content
#eval Ex_Immediate
#eval Ex_Pc
#eval Ex_Offset
#eval Ex_OpCode
#eval Ex_Word
#eval Ex_Instructions
-/
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
--#reduce test_elabRegisterCode %r3


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
--#reduce test_elabSourceReg %r1


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
--#reduce test_elabDestinationReg %r1

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


declare_syntax_cat imp_Offset
syntax "+"? num : imp_Offset
syntax "-"? num : imp_Offset
syntax "exit" : imp_Offset


def elabOffset : Syntax → MetaM Expr
| `(imp_Offset| $n:num) => mkAppM ``Offset.mk #[mkNatLit n.getNat]
| `(imp_Offset| + $n:num) => mkAppM ``Offset.mk #[mkNatLit n.getNat]
| `(imp_Offset| - $n:num) => mkAppM ``Offset.mkN #[mkNatLit n.getNat]
| `(imp_Offset| exit) => mkAppM ``Offset.Exit #[]
| _ => throwUnsupportedSyntax

elab "test_elabOffset" l:imp_Offset : term => elabOffset l
--#reduce test_elabOffset 3

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Content
syntax num : imp_Content

def elabContent : Syntax → MetaM Expr
| `(imp_Content| $n:num) => mkAppM ``Content.mk #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

elab "test_elabContent" l:imp_Content : term => elabContent l
--#reduce test_elabContent 3

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Immediate
syntax "-"? num : imp_Immediate

def elabImmediate : Syntax → MetaM Expr
| `(imp_Immediate| - $n:num) => do
    let i := n.getNat
    mkAppM ``Immediate.mkN #[mkNatLit i]
| `(imp_Immediate| $n:num) =>do
    let i := n.getNat
    mkAppM ``Immediate.mk #[mkNatLit i]
| _ => throwUnsupportedSyntax

elab "test_elabImmediate" l:imp_Immediate : term => elabImmediate l
--#reduce test_elabImmediate 3
--#reduce test_elabImmediate -3

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


declare_syntax_cat imp_OpCodeK
syntax "exit" : imp_OpCodeK
syntax "mov32" : imp_OpCodeK
syntax "add32" : imp_OpCodeK
syntax "sub32" : imp_OpCodeK
syntax "mul32" : imp_OpCodeK
syntax "div32" : imp_OpCodeK
syntax "mov" : imp_OpCodeK
syntax "movsx1632" : imp_OpCodeK
syntax "movsx1664" : imp_OpCodeK
syntax "movsx3264" : imp_OpCodeK
syntax "movsx832" : imp_OpCodeK
syntax "movsx864" : imp_OpCodeK
syntax "mod" : imp_OpCodeK
syntax "mod32" : imp_OpCodeK
syntax "smod" : imp_OpCodeK
syntax "smod32" : imp_OpCodeK
syntax "neg" : imp_OpCodeK
syntax "neg32" : imp_OpCodeK
syntax "add" : imp_OpCodeK
syntax "sub" : imp_OpCodeK
syntax "mul" : imp_OpCodeK
syntax "div" : imp_OpCodeK
syntax "sdiv" : imp_OpCodeK
syntax "sdiv32" : imp_OpCodeK
syntax "jne" : imp_OpCodeK
syntax "jne32" : imp_OpCodeK
syntax "call_local" : imp_OpCodeK
syntax "ja" : imp_OpCodeK
syntax "ja32" : imp_OpCodeK
syntax "jeq" : imp_OpCodeK
syntax "jeq32" : imp_OpCodeK
syntax "jlt" : imp_OpCodeK
syntax "jlt32" : imp_OpCodeK
syntax "jle" : imp_OpCodeK
syntax "jle32" : imp_OpCodeK
syntax "jge" : imp_OpCodeK
syntax "jge32" : imp_OpCodeK
syntax "jgt" : imp_OpCodeK
syntax "jgt32" : imp_OpCodeK
syntax "jneq" : imp_OpCodeK
syntax "jset" : imp_OpCodeK
syntax "jset32" : imp_OpCodeK

syntax "jsgt" : imp_OpCodeK
syntax "jsgt32" : imp_OpCodeK
syntax "jsge" : imp_OpCodeK
syntax "jsge32" : imp_OpCodeK

syntax "jslt" : imp_OpCodeK
syntax "jslt32" : imp_OpCodeK
syntax "jsle" : imp_OpCodeK
syntax "jsle32" : imp_OpCodeK

syntax "ldh" : imp_OpCodeK
syntax "ldxb" : imp_OpCodeK
syntax "ldxh" : imp_OpCodeK
syntax "ldxw" : imp_OpCodeK
syntax "lddw" : imp_OpCodeK
syntax "ldxdh" : imp_OpCodeK
syntax "ldxdw" : imp_OpCodeK
syntax "and" : imp_OpCodeK
syntax "or" : imp_OpCodeK
syntax "and32" : imp_OpCodeK
syntax "or32" : imp_OpCodeK
syntax "rsh32" : imp_OpCodeK
syntax "lsh32" : imp_OpCodeK
syntax "xor32" : imp_OpCodeK
syntax "arsh" : imp_OpCodeK
syntax "arsh32" : imp_OpCodeK
syntax "rsh" : imp_OpCodeK
syntax "lsh" : imp_OpCodeK
syntax "xor" : imp_OpCodeK
syntax "be16" : imp_OpCodeK
syntax "be32" : imp_OpCodeK
syntax "be64" : imp_OpCodeK
syntax "le16" : imp_OpCodeK
syntax "le32" : imp_OpCodeK
syntax "le64" : imp_OpCodeK
syntax "swap16" : imp_OpCodeK
syntax "swap32" : imp_OpCodeK
syntax "swap64" : imp_OpCodeK

syntax "stw" : imp_OpCodeK
syntax "sth" : imp_OpCodeK
syntax "stb" : imp_OpCodeK
syntax "stdw" : imp_OpCodeK
syntax "stxw" : imp_OpCodeK
syntax "stxh" : imp_OpCodeK
syntax "stxb" : imp_OpCodeK
syntax "stxdw" : imp_OpCodeK


partial def elabOpCodeK : Syntax → MetaM Expr
| `(imp_OpCodeK| add32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_add [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| sub32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sub [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| mul32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mul [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| div32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_div [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| exit) => return .const ``OpCode.Eof []
| `(imp_OpCodeK| mov32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mov [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| movsx1632) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx1632 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| movsx1664) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx1664 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| movsx3264) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx3264 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| movsx832) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx832 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| movsx864) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx864 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| mod32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mod [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| mod) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mod [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| smod32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_smod [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| smod) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_smod [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| neg32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_neg [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| neg) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_neg [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| sdiv32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sdiv [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| sdiv) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sdiv [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| add) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_add [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| sub) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sub [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| mul) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mul [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| div) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_div [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| mov) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mov [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| call_local) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_call_local [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| ja) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ja [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| ja32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ja [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jle) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jle [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jle32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jle [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jeq) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jeq [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jeq32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jeq [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jsge) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsge [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jsge32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsge [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jsgt) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsgt [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jsgt32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsgt [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jsle) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsle [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jsle32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsle [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jslt) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jslt [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jslt32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jslt [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jge) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jge [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jge32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jge [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jne) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jne [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jne32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jne [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jlt) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jlt [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jlt32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jlt [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jgt) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jgt [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jgt32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jgt [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jset) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jset [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| jset32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jset [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeK| jneq) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jneq [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeK| ldh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ld []]
| `(imp_OpCodeK| ldxb) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxb [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ld []]
| `(imp_OpCodeK| and) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_and [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| or) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_or [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| ldxh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeK| ldxdh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxdh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeK| and32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_and [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| or32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_or [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| ldxw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxw [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeK| lddw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_lddw [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeK| ldxdw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxdw [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeK| xor32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_xor [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| xor) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_xor [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| rsh32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_rsh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| lsh32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_lsh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| rsh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_rsh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| lsh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_lsh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| arsh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_arsh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| arsh32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_arsh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeK| be16) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_be16 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| be32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_be32 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| be64) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_be64 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| le16) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_le16 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| le32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_le32 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| le64) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_le64 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| swap16) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_swap16 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| swap32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_swap32 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| swap64) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_swap64 [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeK| stw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stw [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_st []]
| `(imp_OpCodeK| sth) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sth [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_st []]
| `(imp_OpCodeK| stb) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stb [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_st []]
| `(imp_OpCodeK| stdw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stdw [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_st []]
| `(imp_OpCodeK| stxw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stxw [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_stx []]
| `(imp_OpCodeK| stxh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stxh [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_stx []]
| `(imp_OpCodeK| stxb) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stxb [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_stx []]
| `(imp_OpCodeK| stxdw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stxdw [], Expr.const ``Source.bpf_k [], Expr.const ``Lsb.bpf_stx []]
| _ => throwUnsupportedSyntax

elab "test_elabOpCodeK" e:imp_OpCodeK : term => elabOpCodeK e
/-
#reduce test_elabOpCodeK add32
#reduce test_elabOpCodeK ldxw
-/


--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


declare_syntax_cat imp_OpCodeX
syntax "exit" : imp_OpCodeX
syntax "mov32" : imp_OpCodeX
syntax "add32" : imp_OpCodeX
syntax "sub32" : imp_OpCodeX
syntax "mul32" : imp_OpCodeX
syntax "div32" : imp_OpCodeX
syntax "mov" : imp_OpCodeX
syntax "movsx1632" : imp_OpCodeX
syntax "movsx1664" : imp_OpCodeX
syntax "movsx3264" : imp_OpCodeX
syntax "movsx832" : imp_OpCodeX
syntax "movsx864" : imp_OpCodeX
syntax "mod" : imp_OpCodeX
syntax "mod32" : imp_OpCodeX
syntax "smod" : imp_OpCodeX
syntax "smod32" : imp_OpCodeX
syntax "sdiv" : imp_OpCodeX
syntax "sdiv32" : imp_OpCodeX
syntax "neg" : imp_OpCodeX
syntax "neg32" : imp_OpCodeX
syntax "add" : imp_OpCodeX
syntax "sub" : imp_OpCodeX
syntax "mul" : imp_OpCodeX
syntax "div" : imp_OpCodeX
syntax "call_local" : imp_OpCodeX
syntax "ja" : imp_OpCodeX
syntax "ja32" : imp_OpCodeX
syntax "jeq" : imp_OpCodeX
syntax "jeq32" : imp_OpCodeX
syntax "jle" : imp_OpCodeX
syntax "jle32" : imp_OpCodeX
syntax "jge" : imp_OpCodeX
syntax "jge32" : imp_OpCodeX
syntax "jne" : imp_OpCodeX
syntax "jne32" : imp_OpCodeX

syntax "jsgt" : imp_OpCodeX
syntax "jsgt32" : imp_OpCodeX
syntax "jsge" : imp_OpCodeX
syntax "jsge32" : imp_OpCodeX

syntax "jslt" : imp_OpCodeX
syntax "jslt32" : imp_OpCodeX
syntax "jsle" : imp_OpCodeX
syntax "jsle32" : imp_OpCodeX

syntax "jlt" : imp_OpCodeX
syntax "jlt32" : imp_OpCodeX
syntax "jset" : imp_OpCodeX
syntax "jset32" : imp_OpCodeX
syntax "jgt" : imp_OpCodeX
syntax "jgt32" : imp_OpCodeX
syntax "jneq" : imp_OpCodeX
syntax "ldh" : imp_OpCodeX
syntax "ldxb" : imp_OpCodeX
syntax "ldxh" : imp_OpCodeX
syntax "ldxw" : imp_OpCodeX
syntax "lddw" : imp_OpCodeX
syntax "ldxdh" : imp_OpCodeX
syntax "ldxdw" : imp_OpCodeX
syntax "and" : imp_OpCodeX
syntax "or" : imp_OpCodeX
syntax "and32" : imp_OpCodeX
syntax "or32" : imp_OpCodeX
syntax "rsh32" : imp_OpCodeX
syntax "lsh32" : imp_OpCodeX
syntax "xor32" : imp_OpCodeX
syntax "arsh" : imp_OpCodeX
syntax "arsh32" : imp_OpCodeX
syntax "rsh" : imp_OpCodeX
syntax "lsh" : imp_OpCodeX
syntax "xor" : imp_OpCodeX
syntax "be16" : imp_OpCodeX
syntax "be32" : imp_OpCodeX
syntax "be64" : imp_OpCodeX
syntax "le16" : imp_OpCodeX
syntax "le32" : imp_OpCodeX
syntax "le64" : imp_OpCodeX
syntax "swap16" : imp_OpCodeX
syntax "swap32" : imp_OpCodeX
syntax "swap64" : imp_OpCodeX
syntax "stw" : imp_OpCodeX
syntax "sth" : imp_OpCodeX
syntax "stb" : imp_OpCodeX
syntax "stdw" : imp_OpCodeX
syntax "stxw" : imp_OpCodeX
syntax "stxh" : imp_OpCodeX
syntax "stxb" : imp_OpCodeX
syntax "stxdw" : imp_OpCodeX
--Adicionar Call

partial def elabOpCodeX : Syntax → MetaM Expr
| `(imp_OpCodeX| add32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_add [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| sub32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sub [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| mul32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mul [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| div32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_div [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| exit) => return .const ``OpCode.Eof []
| `(imp_OpCodeX| mov32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mov [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| movsx1632) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx1632 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| movsx1664) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx1664 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| movsx3264) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx3264 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| movsx832) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx832 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| movsx864) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_movsx864 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| mod32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mod [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| mod) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mod [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| smod32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_smod [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| smod) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_smod [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| sdiv32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sdiv [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| sdiv) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sdiv [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| neg32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_neg [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| neg) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_neg [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| add) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_add [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| sub) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sub [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| mul) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mul [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| div) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_div [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| mov) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_mov [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| call_local) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_call_local [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jeq) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jeq [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jeq32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jeq [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jne) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jne [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jne32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jne [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jlt) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jlt [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jlt32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jlt [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jslt) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jslt [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jslt32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jslt [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jsle) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsle [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jsle32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsle [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jle) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jle [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jle32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jle [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jge) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jge [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jge32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jge [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jsge) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsge [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jsge32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsge [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jsgt) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsgt [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jsgt32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jsgt [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jset) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jset [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jset32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jset [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jgt) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jgt [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| jgt32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jgt [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp32 []]
| `(imp_OpCodeX| jneq) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_jneq [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_jmp []]
| `(imp_OpCodeX| ldh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ld []]
| `(imp_OpCodeX| and32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_and [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| or32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_or [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| and) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_and [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| or) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_or [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| ldxb) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxb [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeX| ldxh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeX| ldxw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxw [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeX| lddw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_lddw [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeX| ldxdh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxdh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeX| ldxdw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_ldxdw [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_ldx []]
| `(imp_OpCodeX| xor) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_xor [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| xor32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_xor [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| lsh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_lsh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| rsh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_rsh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| lsh32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_lsh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| rsh32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_rsh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| arsh32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_arsh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu []]
| `(imp_OpCodeX| arsh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_arsh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| be16) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_be16 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| be32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_be32 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| be64) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_be64 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| le16) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_le16 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| le32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_le32 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| le64) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_le64 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| swap16) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_swap16 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| swap32) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_swap32 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| swap64) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_swap64 [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_alu64 []]
| `(imp_OpCodeX| stw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stw [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_st []]
| `(imp_OpCodeX| sth) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_sth [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_st []]
| `(imp_OpCodeX| stb) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stb [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_st []]
| `(imp_OpCodeX| stdw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stdw [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_st []]
| `(imp_OpCodeX| stxw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stxw [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_stx []]
| `(imp_OpCodeX| stxh) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stxh [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_stx []]
| `(imp_OpCodeX| stxb) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stxb [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_stx []]
| `(imp_OpCodeX| stxdw) => return mkAppN (Expr.const ``OpCode.mk []) #[Expr.const ``Msb.bpf_stxdw [], Expr.const ``Source.bpf_x [], Expr.const ``Lsb.bpf_stx []]

| _ => throwUnsupportedSyntax

elab "test_elabOpCodeX" e:imp_OpCodeX : term => elabOpCodeX e
/-
#reduce test_elabOpCodeK add32
#reduce test_elabOpCodeK arsh
#reduce test_elabOpCodeK be16
-/



--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

declare_syntax_cat imp_Word
syntax imp_OpCodeX imp_DestinationReg : imp_Word
syntax imp_OpCodeX imp_DestinationReg "," imp_SourceReg : imp_Word
syntax imp_OpCodeK imp_DestinationReg "," imp_Immediate : imp_Word
syntax imp_OpCodeK imp_DestinationReg "," imp_Immediate "," imp_Offset : imp_Word
syntax imp_OpCodeX imp_DestinationReg "," imp_SourceReg "," imp_Offset : imp_Word
syntax imp_OpCodeK imp_DestinationReg "," " [" imp_Offset "]" : imp_Word
syntax imp_OpCodeX imp_DestinationReg "," " [" imp_SourceReg  imp_Offset "]" : imp_Word
syntax imp_OpCodeX imp_DestinationReg "," " [" imp_SourceReg "]" : imp_Word
syntax imp_OpCodeK imp_Offset : imp_Word

syntax imp_OpCodeK "[" imp_Offset "]" ","  imp_Immediate  : imp_Word
syntax imp_OpCodeX "[" imp_DestinationReg  imp_Offset "]" ","  imp_Immediate  : imp_Word
syntax imp_OpCodeX "[" imp_DestinationReg "]" ","  imp_Immediate  : imp_Word

syntax imp_OpCodeK "[" imp_Offset "]" ","  imp_SourceReg  : imp_Word
syntax imp_OpCodeX "[" imp_DestinationReg  imp_Offset "]" ","  imp_SourceReg  : imp_Word
syntax imp_OpCodeX "[" imp_DestinationReg "]" ","  imp_SourceReg  : imp_Word

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
| `(imp_Word| $a:imp_OpCodeX $b:imp_DestinationReg , [ $c:imp_SourceReg  $d:imp_Offset ] ) => do
  let opCode ← elabOpCodeX a
  let srcReg ← elabSourceReg c
  let dstReg ← elabDestinationReg b
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let offsetExpr ← elabOffset d
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, srcReg , dstReg, opCode]
-- ldxh %r2 , [%r1]
| `(imp_Word| $a:imp_OpCodeX $b:imp_DestinationReg , [ $c:imp_SourceReg] ) => do
  let opCode ← elabOpCodeX a
  let srcReg ← elabSourceReg c
  let dstReg ← elabDestinationReg b
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let offsetExpr := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, srcReg , dstReg, opCode]
-- ja 5
| `(imp_Word| $a:imp_OpCodeK $b:imp_Offset ) => do
  let opCode ← elabOpCodeK a
  let offsetExpr ← elabOffset b
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let regExprSrc := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  let regExprDst := mkAppN (Expr.const ``DestinationReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, regExprSrc , regExprDst, opCode]
-- be16 %r1
| `(imp_Word| $a:imp_OpCodeX $b:imp_RegisterCode ) => do
  let opCode ← elabOpCodeX a
  let offsetExpr := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  --let regExprSrc := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  let reg ← elabRegisterCode b
  --let regExprDst ← elabRegisterCode reg
  --let regExprSrc ← elabRegisterCode reg
  let regExprSrc := mkAppN (Expr.const ``SourceReg.mk []) #[reg]
  let regExprDst := mkAppN (Expr.const ``DestinationReg.mk []) #[reg]
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, regExprSrc , regExprDst, opCode]



/-
syntax imp_OpCodeK "[" imp_Offset "]" ","  imp_Immediate  : imp_Word
syntax imp_OpCodeK "[" imp_DestinationReg "+" imp_Offset "]" ","  imp_Immediate  : imp_Word
syntax imp_OpCodeK "[" imp_Offset "]" ","  imp_Immediate  : imp_Word
syntax imp_OpCodeK "[" imp_DestinationReg "+" imp_Offset "]" ","  imp_Immediate  : imp_Word
-/
  -- sth [10], 0x1234 OK
| `(imp_Word| $a:imp_OpCodeK [ $b:imp_Offset ] , $c:imp_Immediate ) => do
  let opCode ← elabOpCodeK a
  let offset ← elabOffset b
  let imm ← elabImmediate c
  let regExprSrc := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  let regExprDst := mkAppN (Expr.const ``DestinationReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  return mkAppN (Expr.const ``Word.mk []) #[imm, offset, regExprSrc , regExprDst, opCode]
-- sth [%r0 + 10 ], 0x1234
| `(imp_Word| $a:imp_OpCodeX [ $b:imp_DestinationReg $c:imp_Offset ] , $d:imp_Immediate ) => do
  let opCode ← elabOpCodeX a
  let dst ← elabDestinationReg b
  let offset ← elabOffset c
  let imm ← elabImmediate d
  let regExprSrc := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  return mkAppN (Expr.const ``Word.mk []) #[imm, offset, regExprSrc , dst, opCode]
-- sth [%r0], 0x1234
| `(imp_Word| $a:imp_OpCodeX [ $b:imp_DestinationReg ] , $d:imp_Immediate ) => do
  let opCode ← elabOpCodeX a
  let dst ← elabDestinationReg b
  let offsetExpr := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  let imm ← elabImmediate d
  let regExprSrc := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  return mkAppN (Expr.const ``Word.mk []) #[imm, offsetExpr, regExprSrc , dst, opCode]

-- stxh [10], %r1
| `(imp_Word| $a:imp_OpCodeK [ $b:imp_Offset ] , $c:imp_SourceReg ) => do
  let opCode ← elabOpCodeK a
  let offset ← elabOffset b
  let src ← elabSourceReg c
  let regExprDst := mkAppN (Expr.const ``DestinationReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  return mkAppN (Expr.const ``Word.mk []) #[imm, offset, src , regExprDst, opCode]

-- stxh [%r0 + 10 ], %r1
| `(imp_Word| $a:imp_OpCodeX [ $b:imp_DestinationReg $c:imp_Offset ] , $d:imp_SourceReg ) => do
  let opCode ← elabOpCodeX a
  let dst ← elabDestinationReg b
  let offset ← elabOffset c
  let src ← elabSourceReg d
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  return mkAppN (Expr.const ``Word.mk []) #[imm, offset, src , dst, opCode]

-- stxh [%r0], %r1
| `(imp_Word| $a:imp_OpCodeX [ $b:imp_DestinationReg ] , $c:imp_SourceReg ) => do
  let opCode ← elabOpCodeX a
  let dst ← elabDestinationReg b
  let offset := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  let src ← elabSourceReg c
  let imm := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  return mkAppN (Expr.const ``Word.mk []) #[imm, offset, src , dst, opCode]

| `(imp_Word| exit) => do
  let immExpr := mkApp (Expr.const ``Immediate.mk []) (mkNatLit 0)
  let offsetExpr := mkApp (Expr.const ``Offset.mk []) (mkNatLit 0)
  let regExprS := mkAppN (Expr.const ``SourceReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  let regExprD := mkAppN (Expr.const ``DestinationReg.mk []) #[Expr.const ``RegisterCode.r0 []]
  let extExpr := Expr.const ``OpCode.Eof []
  return mkAppN (Expr.const ``Word.mk []) #[immExpr, offsetExpr, regExprS, regExprD, extExpr]

| _ => throwUnsupportedSyntax

elab "test_elabWord" e:imp_Word : term => elabWord e

#reduce test_elabWord neg32 %r1
#reduce test_elabWord ldh %r1, [%r1-10]
#reduce test_elabWord ldxdw %r0, [%r1]


/-
#reduce test_elabWord mov32 %r3, 0
#reduce test_elabWord add32 %r3, %r4
#reduce test_elabWord ldh %r1, [10]
#reduce test_elabWord ldxw %r1, [%r3]
#reduce test_elabWord ldh %r1, [%r1+ 10]
#reduce test_elabWord jne %r1, 5, 10
#reduce test_elabWord ldh %r1, %r2, 10
#reduce test_elabWord be16 %r1
#reduce test_elabWord exit
-/
/-
#reduce test_elabWord ldh %r1, [10]

#reduce test_elabWord stxh [10], 0x1234
#reduce test_elabWord stxh [10], 0x1234
#reduce test_elabWord sth [%r0 + 10], 0x1234
#reduce test_elabWord sth [%r0], 0x1234

#reduce test_elabWord stxh [10], %r0
-/

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<

#reduce test_elabWord stb [%r0 + 10 ], 0x1234

#reduce test_elabWord stb [%r1+2], 0x11

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
/-
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
-/

--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<
--------->>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<<<<<


declare_syntax_cat imp_Pc
syntax num : imp_Pc

def elabPc : Syntax → MetaM Expr
| `(imp_Pc| $n:num) => mkAppM ``Pc.mk #[mkNatLit n.getNat]
| _ => throwUnsupportedSyntax

elab "test_elabPc" l:imp_Pc : term => elabPc l
--#reduce test_elabPc 3


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
      if h : i < 513 then
        let idx : Fin 513 := ⟨i, h⟩  -- Converte ℕ para Fin 512 com prova explícita
        let val := mem.data idx
        --some s!"{idx} -> {val}" --Imprime todos os valores
        if val ≠ 0 then some s!"{idx} -> {val}" else none --Imprime diferentes de Zero
      else none) (List.range 513)  -- Garante que os índices estão dentro do limite
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
--#reduce test_elabComment # Este e um comentario com varios espacos data

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
/-
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
-/
