import «ProjetoConformance».Semantic

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
