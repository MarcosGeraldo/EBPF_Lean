import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Defs
import «ProjetoConformance».Methods
import Aesop
import Lean.Elab.Tactic
import Init.System.IO
open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Term
open Lean.Syntax
open Lean Elab  Meta

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
