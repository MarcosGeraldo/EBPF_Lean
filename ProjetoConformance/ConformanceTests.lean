import «ProjetoConformance».Sintax


def initialRegisters : Registers :=
  { r0 := 0, r1 := 0, r2 := 0, r3 := 0, r4 := 0
  , r5 := 0, r6 := 0, r7 := 0, r8 := 0, r9 := 0, r10 := 0 }

-- Criar função que recebe test eval, cria a lista vazia de registradores e chama exeMainFuel

def exeConformance ( input : TestEval ) (stack : MemorySpace) : MemorySpace × Registers × Instructions :=
  match input with
  | TestEval.mk instructions _expectedResult =>
    --let program := emptyMemory initialRegisters instructions
    let fuel := 1000
    let returnedResult := exeMain stack initialRegisters instructions fuel
    returnedResult

def exeConformanceDebug ( input : TestEval ) (stack : MemorySpace) : MemorySpace × Registers × Instructions × List ℕ :=
  match input with
  | TestEval.mk instructions _expectedResult =>
    --let program := emptyMemory initialRegisters instructions
    let fuel := 1000
    let returnedResult := exeMainDebug stack initialRegisters instructions fuel []
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

def nomes_defs := [progTestTerm]

def lista := [1,2,3]

--#eval lista[0]

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

/-
#eval exeConformance progTestTerm inputMem

#eval exeConformanceDebug {exe|
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
-/

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
/-
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
-/
def listCharBool (input : List Bool) : String :=
  match input with
  | [] => ""
  | x :: xs =>
   match x with
   | false => "0" ++ listCharBool xs
   | true =>  "1" ++ listCharBool xs

/-
#eval returnMemoryBlockNat subnetMem 30 3 --16885952
#eval returnMemoryBlockChar subnetMem 30 3 --16885952

#eval natToHexCharList 1157312
#eval 0x0101a8c0
#eval natToBin 16777215 --0xffffff
#eval natToBin 16885952 --0x0101a8c0
#eval binToNat (natToBin 16885952)
#eval binToNat (natToBin 16777215)
#eval listCharBool (natToBin 0xffffff) --0xffffff
#eval listCharBool (natToBin 0x0101a8c0) --0x0101a8c0
#eval binToNat (bitwiseAnd (natToBin 0xffffff) (natToBin 0x0101a8c0))
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
-/
-- Selecionar para quais exemplos que a gente vai aplicar o gerador --QuickCheck
-- Only allow ARP packets:
-- Only allow IPv4 TCP packets:

-- Usar arquivos Lean para representar os programas eBPF ok

-- Testes de conformidade
    --Definir cada teste como um def de Term
    --Armazenar o nome de cada def
    --Percorrer a lista de defs e obter os resultados com uma função


-- Organizar os arquivos Sprint 1 OK


-- Tarefas Pos 28/03
--     Gerador de pacotes IPV4 ok
--        Criar gerador de pacotes aleatorio de pacotes IPV4/IPV6 Selecionado ou não Selecionado ok
--     Implementar os testes da pagina de eBPF +/- ok
--     Executar os testes de conformidade em Lean
--     Testar os programas praticos com o gerador de pacotes ok
--     TCP Dump

-- Pesquisar um pouco dos pacotes Ipv4 *Socorro*

-- Dia 28/03 ^^^^^^^^^^^^^
-- Doctum JM
-- Criar pacotes utilizando o slimCheck ok (SlimCheck não está funcionando 100% em Lean4)
-- Definir matematicamente a semantica que temos em Lean(V2)

def subnetMem1 :=
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

--Função que cria retorna um char dado um natural
def charFromIndex (n : ℕ) : Char :=
  if n < 10 then
    Char.ofNat (n + 48)  -- '0' é ASCII 48
  else
    Char.ofNat (n - 10 + 97)  -- 'a' é ASCII 97

-- Função para "randomizar" os valore tendo uma seed como base
def generateChar (seed : ℕ) : Char :=
  charFromIndex (seed % 16)  -- 16 valores números entre 0 - 9 e a - f

--Função que dada um tanho e uma seed retorna uma lista de caracteres hexadecimal
-- Lista essa que é utilziada para popular o pacote de entrada
def generateRandomList (size : ℕ) (seed : ℕ) : List Char :=
  match size with
  | 0 => []
  | size' + 1 =>
      generateChar seed :: generateRandomList (size') (seed + 17)

--#eval generateRandomList 8 42  -- Exemplo: ['a', 'b', 'c', 'd', 'e', 'f', '0', '1']

--Função que dado uma lista de caracteres popula um espaço de memoria
def formatMemorySpace (input : List Char) : MemorySpace :=
  createStackMemoryCharList 0 emptyMemory input

--Macros do pacote, aqui posso definir qualquer valor esperado
def ipv4 := ['0','8','0','0']--0x0800
def arp := ['0','8','0','6']--0x0806

--Função que cria um pacote Arp, demais valores estão sendo randomizados
def inputPackgeGeneratorArp ( valid : Bool ) : MemorySpace :=
  let macDestino := generateRandomList 12 8
  let macOrigem := generateRandomList 12 8
  let eth_type :=  if valid then arp
    else
        generateRandomList 8 8
  let ipV4Header := generateRandomList 40 8
  let tcpHeader := generateRandomList 80 8
  formatMemorySpace (macDestino ++ macOrigem ++ eth_type ++ ipV4Header ++ tcpHeader)

--Função que cria um pacote IPv4, demais valores estão sendo randomizados
def inputPackgeGeneratorIPv4 ( valid : Bool ) : MemorySpace :=
  let macDestino := generateRandomList 12 8
  let macOrigem := generateRandomList 12 8
  let eth_type :=  if valid then ipv4
    else
        generateRandomList 8 8
  let ipV4Header := generateRandomList 40 8
  let tcpHeader := generateRandomList 80 8
  formatMemorySpace (macDestino ++ macOrigem ++ eth_type ++ ipV4Header ++ tcpHeader)

-- Função que dado uma lista de booleanos retorna uma lista de pacotes Arp
-- Onde para cada boleano da lista fica definido se o pacote deve ser aceito ou não
def inputPackgeGeneratorListArp (validList : List Bool ) : List MemorySpace:=
  match validList with
  | valid :: xs => inputPackgeGeneratorArp valid :: inputPackgeGeneratorListArp xs
  | [] => []

-- Função que dado uma lista de booleanos retorna uma lista de pacotes IPv4
-- Onde para cada boleano da lista fica definido se o pacote deve ser aceito ou não
def inputPackgeGeneratorListIPv4 (validList : List Bool ) : List MemorySpace:=
  match validList with
  | valid :: xs => inputPackgeGeneratorIPv4 valid :: inputPackgeGeneratorListIPv4 xs
  | [] => []

-- Função que dado uma contagem de pacotes validos e um tamanho total
-- Cria uma lista de boleanos definindo os valores para pacotes aceitos ou não
def createBooleanList(valid n : ℕ) : List Bool :=
  match n with
  |n' + 1 =>
    match valid with
      | valid' + 1 => true :: createBooleanList valid' n'
      | 0 => false :: createBooleanList 0 n'
  |0 => []


--#eval inputPackgeGeneratorListIPv4 (createBooleanList 5 10)

--Função que cria uma lista de pacotes ARP
--E retorna quais são validos e quais não pacote
def cratePackgesArp ( valid n : ℕ ) : List MemorySpace × List Bool :=
    let validList := createBooleanList valid n
    (inputPackgeGeneratorListArp validList, validList)

--Função que cria uma lista de pacotes IPV4
--E retorna quais são validos e quais não pacote
def cratePackgesIPV4 ( valid n : ℕ ) : List MemorySpace × List Bool :=
    let validList := createBooleanList valid n
    (inputPackgeGeneratorListIPv4 validList, validList)

-- Função que recebe um programa , uma lista de pacotes de entrada
-- E compara o resultado esperado com o obtido
def evalEbpfProg (prog : TestEval) (inputs : List MemorySpace) (validList : List Bool) : List Bool :=
  match inputs with
  | i :: is =>
    match validList with
      | v :: vs =>
        let (_retMemory, retVal, _inst) := exeConformance prog i
        match prog with
        | TestEval.mk _instr expectedVal => ((expectedVal == retVal.r0) && v) :: evalEbpfProg prog is vs
      |[]=> []
  | [] => []

def exeConformanceCompareResult (prog : TestEval) (inputs : MemorySpace) :=
  let (_retMemory, retVal, _inst) := exeConformance prog inputs
  match prog with
    | TestEval.mk _instr expectedVal => (expectedVal == retVal.r0)

-- Função para "Desembrulhar" o retorno do cratePackges
def evaluateEbpfProg (prog : TestEval) (input : List MemorySpace × List Bool) : List Bool :=
  match input with
  | (inputMemory, validList) => evalEbpfProg prog inputMemory validList

/-
#eval generateRandomList 6 8
#eval inputPackgeGeneratorArp true
#eval inputPackgeGeneratorArp false
#eval subnetMem
#eval formatMemorySpace ( generateRandomList 6 8 ++ ipv4 ++ generateRandomList 6 8)
#eval inputPackgeGeneratorArp true
#eval returnMemoryBlockNat (inputPackgeGeneratorArp true) 12 1

#eval 0x0608
-/

/-
Only allow ARP packets:

         ldh [12]
         jne #0x806, drop -- Jump Not Equal
         ret #-1
         drop: ret #0
-/
-- Usar %r1 como o Acumulador
-- Substituir o ret pelo exit
-- Trocar as labels pelo valor do Offset
-- Valor invertido devido a particularidades dos testes de Conformidade
def prog_only_arp : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldh %r1, [12]
mov32 %r0, 1
jne %r1, 0x0608, 1
exit
mov32 %r0, 0
exit
result
0x1
}

/-
#eval exeConformance prog_only_arp (inputPackgeGeneratorArp true)

#eval evaluateEbpfProg prog_only_arp (cratePackgesArp 5 10)
-/
def prog_only_IPV44 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldh %r1, [12]
mov32 %r0, 1
jne %r1, 0x0008, 1
exit
mov32 %r0, 0
exit
result
0x1
}
/-
#eval exeConformance prog_only_IPV44 (inputPackgeGeneratorIPv4 true)

#eval evaluateEbpfProg prog_only_IPV44 (cratePackgesIPV4 15 100)
-/
def isEven (n : ℕ) : Prop :=
  n % 2 = 0

example : Prop :=
  ∀ n : ℕ, isEven (n * 2)  -- Testar se o dobro de qualquer número é par

/-
 Only allow IPv4 TCP packets:

         ldh [12] --Load half-word into A where A = 32 bit wide accumulator
         jne #0x800, drop
         ldb [23]
         jneq #6, drop
         ret #-1
         drop: ret #0
-/
-- Usar %r0 como o Acumulador
-- Substituir o ret pelo exit
-- Trocar as labels pelo valor do Offset
def prog_only_IPv4 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldh %r1, [12]
jne %r1, 0x0008, 1
mov32 %r0, 0
ldh %r1, [12]
jne %r1, 0x0006, 1
mov32 %r0, 0
mov32 %r0, 1
exit
result
0x0
}



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
-- Usar %r0 como o Acumulador
-- Substituir o ret pelo exit
-- Trocar as labels pelo valor do Offset
def prog_only_IPv4_SSH : TestEval :=
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

/-
namespace SlimCheck


example : ∀ n : ℕ, n % 4 == 0 → n % 2 == 0 := by

slim_check

example : ∀ n : ℕ, n + 0 = n := by
  slim_check

example : ∀ x y : ℕ, y ≠ 0 → (x * y) / y = x := by
  slim_check
#sample ℕ

def isEven (n : ℕ) : Prop := n % 2 = 0

example : ∀ n : ℕ, (n % 2 = 0) ∨ (n % 2 = 1) := by slim_check

#eval 4%2

#eval 2%2


def List.shrink : (l : List A) -> List { y : List A // WellFoundedRelation.rel y l }
| [] => []
|x::xs =>
  let rest := List.shrink xs
  ⟨xs, by simp_wf⟩ :: rest.map (fun y => {y with property := by match y with |⟨y,h⟩ => simp_wf; sorry })


instance List.sampleableExt1 [SampleableExt A] [Repr A] [Shrinkable A] : SampleableExt (List A) :=
  SampleableExt.mkSelfContained
    (do Gen.listOf (SampleableExt.interpSample A))

example : forall x : Nat, 2 * x = x + x :=
  by slim_check -- Success

example : forall x y : Nat, x + y = y + x := by slim_check -- Success

end SlimCheck
-/

--260,59

/-
==================== Proximos Passos=======================
Adicionar tratamento para valores negativos
-- Usar complemento 2 para tratar os valores negativos
-- Lembrar que apenas o Immediato está com a flag para separar valores negativos e positivos
-- Armazenar os valores dentro dos registradores como o natural respectivo para o complemento 2 binario}

Adicionar operaçoes com variação de tamahos de palavras 32 e 64 bits
-- Criar função para transformar numero em lista de caracteres
-- Criar função para "cortar" a lista de caracteres
-- Separar as funçoes de 32 e 64 bits dentro do applyOpCode
---- Decidir entre separar por *classe* ou por opCode

Implementar mais exemplos do site do Linux
-- Usar engenharia reversa para descobrir os valores esperados

Adicionar a implementação para os operadores ainda não definidos, seguir a ordem dos testes de conformidade

Usar a função que crie que compara o resultado obtido com o esperado para avaliar todos os testes de conformidade

Alterar o parser feito em Python para reconhecer todas as labels e colocar os valores corretos
-- Se forem poucos casos fazer manualmente

Comentar, Documentar e Organizar todo o código
-- Comentar cada função, falando o que ela faz e quais são os parametros e retornos esperados
-- Comentar no inicio de cada Arquivo falando o que cada um deles contem
-- Orgazizar os pacotes de forma a garantir que os conteudos fiquem corretamente separados em cada arquivo

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


-- Implementação do Call
-- Implementar todos os Metodos do bpfc(8) — Linux manual page
-- GitHub Anonimo e Versão Estável do programa
-- Criar um Docker para facilitar a utiliziação do revisor na avaliação do Trabalho
----
