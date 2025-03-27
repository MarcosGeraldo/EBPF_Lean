import «ProjetoConformance».Sintax


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


def progTestTerm : TestEval := --Definição de um programa como uma palavra chave
{exe|
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
}

--Definir cada teste como um def de Term
--Armazenar o nome de cada def
--Percorrer a lista de defs e obter os resultados com uma função


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

#eval exeConformance progTestTerm inputMem

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


-- Usar arquivos Lean para representar os programas eBPF ok

-- Testes de conformidade
    --Definir cada teste como um def de Term
    --Armazenar o nome de cada def
    --Percorrer a lista de defs e obter os resultados com uma função

-- Organizar os arquivos Sprint 1 OK

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
