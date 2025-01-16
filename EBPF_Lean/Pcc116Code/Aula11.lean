-- Aula 11: Recursão geral

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Defs

-- ∀ {e}, ∃ r, f e = r
-- funções devem ser totais
-- * Recursão estrutural.
-- * Casamento de padrão exaustivo.

-- definições parciais: uma maneira de contornar a
-- exigência de totalidade

-- n ÷ m = (q,r) tal que n = m × q + r ∧ r < m

partial def pdiv (n m : ℕ) : ℕ × ℕ :=
  match Nat.decLt n m with
  | isTrue _ => (0, n)
  | _           =>
    match pdiv (n - m) m with
    | (q,r) => (q + 1, r)

#eval pdiv 5 2

-- Lean não identifica a chamada a pdif (n - m) m
-- como seguindo uma cadeia decrescente finita de
-- chamadas. Como resolver esse dilema?

-- Estratégia 1. uso de fuel
-- dois componentes:
-- * Contador de chamadas recursivas passado como argumento.
-- * Resultado da forma Option A, em que A é o tipo do resultado.
-- ** fuel = 0, resultado .none
-- ** fuel ≠ 0, calcule o resultado fazendo chamada recursiva sobre fuel - 1
/-
inductive Decidable (P : Prop) : Type where
| isTrue : P → Decidable P
| isFalse : ¬ P → Decidable P

inductive Lt : ℕ → ℕ → Prop where
| base : ∀ {m}, Lt 0 (m + 1)
| step : ∀ {n m}, Lt n m → Lt (n + 1) (m + 1)



def blt (n m : ℕ) : Bool := ...

blt n m = true ∨  blt n m = false

def decLt (n m : ℕ) : Decidable (Lt n m) := ...

if n < m then (0, n) else let (q,r) := div (n - m) m in (q + 1, r)
-/

inductive Lt : ℕ → ℕ → Prop where
| base : ∀ {m}, Lt 0 (m + 1)
| step : ∀ {n m}, Lt n m → Lt (n + 1) (m + 1)

def blt (n m : ℕ) : Bool :=
  match n, m with
  | 0, _ + 1 => true
  | 0, 0 => false
  | _ + 1, 0 => false
  | n + 1, m + 1 => blt n m

def ltDec (n m : ℕ) : Decidable (Lt n m) :=
  match n, m with
  | 0, 0 => by
      apply Decidable.isFalse
      intros H
      cases H
  | 0, m + 1 => by
      apply Decidable.isTrue
      apply Lt.base
  | n + 1, 0 => by
    apply Decidable.isFalse
    intros H
    cases H
  | n + 1, m + 1 => by
    have R : Decidable (Lt n m) := ltDec n m
    cases R with
    | isFalse H =>
      apply Decidable.isFalse
      intros H1
      cases H1
      contradiction
    | isTrue H =>
      apply Decidable.isTrue
      apply Lt.step
      exact H

lemma test : Lt 2 5 := by
  apply Lt.step
  apply Lt.step
  apply Lt.base

def fuel_div_def (fuel : ℕ)(n m : ℕ) : Option (ℕ × ℕ) :=
  match fuel with
  | 0 => .none
  | fuel' + 1 =>
    match Nat.decLt n m with
    | isTrue _ => .some (0,n)
    | _ => match fuel_div_def fuel' (n - m) m with
           | .none => .none
           | .some (q,r) => .some (q + 1, r)

def fuel_div (n m : ℕ) : Option (ℕ × ℕ) :=
  fuel_div_def n n m

-- Problemas:
-- 1. Necessidade de usar o tipo Option para garantir totalidade
--    quando não há combustível suficiente para executar
--    chamadas recursivas.
-- 2. Presença de um parâmetro artificial, o fuel.

-- Estratégia 2. uso de relações de ordem bem formadas

-- Relações bem formadas

-- Exemplo: < sobre ℕ
-- * n > ... > 0
-- < sobre ℤ não é bem formado.

/-
Primeiro, temos que lembrar o que é uma relação de ordem.

Dizemos que R é uma relação de ordem se:

- R é irreflexiva: ∀ x, ¬ R x x
- R é transitiva: ∀ x y z, R x y → R y z → R x z

Dizemos que uma relação de ordem é bem formada se
todos os elementos desta relação são _alcançáveis_.

Para entender o conceito de alcançabilidade, é
útil recordar sobre o princípio de indução forte.
-/

-- ∀ n, P n ≃ P 0 ∧ ∀ n, P n → P (n + 1)

def strong_induction (P : ℕ → Prop)
  : (∀ m, (∀ k, k < m → P k) → P m) → ∀ n, P n  := by
  intros IH n
  have IH1 : ∀ p, p ≤ n → P p := by
    induction n with
    | zero =>
      intros p H
      cases H
      apply IH
      intros k Hk
      cases Hk
    | succ n' IHn' =>
      intros p H
      apply IH
      intros k Hk
      apply IHn'
      omega
  apply IH1
  apply Nat.le_refl

/-
Essencialmente, o uso de relações bem formadas é uma
generalização do princípio de indução forte para
tipos de dados quaisquer.
-/

--
-- Acessibilidade de uma relação de ordem

-- inductive Acc {α : Sort u} (r : α → α → Prop) : α → Prop where
-- | intro (x : α) (h : (y : α) → r y x → Acc r y) : Acc r x
-- essencialmente, isso é o princípio de indução forte.

-- inductive WellFounded {α : Sort u} (r : α → α → Prop) : Prop where
-- | intro (h : ∀ a, Acc r a) : WellFounded r

lemma div_rec {n m : ℕ} : 0 < m ∧ m ≤ n → n - m < n := by
  intros H1
  omega -- Aritmética de Presburger

-- aqui explicitamente realizamos a chamada recursiva
-- sobre um argumento menor e provamos esse fato usando
-- div_rec

def divF (n : ℕ)
         (f : (n' : Nat) → n' < n → ℕ → ℕ) (m : ℕ) : ℕ :=
  if h : 0 < m ∧ m ≤ n then
    f (n - m) (div_rec h) m + 1
  else
    0

def div1 n m := WellFounded.fix (measure id).wf divF n m

#check div1

-- outra maneira, é termos no escopo da definição
-- uma prova mostrando que o argumento é menor e,
-- partir disso, o compilador do Lean é capaz de
-- automatizar o processo de construção do uso
-- WellFounded.fix

def div2 (n m : ℕ) : ℕ :=
  if h : 0 < m ∧ m ≤ n then
    div2 (n - m) m + 1
  else 0

lemma div2_def (n m : ℕ)
  : div2 n m = if 0 < m ∧ m ≤ n then
                  div2 (n - m) m + 1 else 0 := by
  show div2 n m = _
  rw [div2]
  rfl

lemma div_induction (P : ℕ → ℕ → Prop)
  (n m : ℕ)
  (IH : ∀ n m, 0 < m ∧ m ≤ n → P (n - m) m → P n m)
  (base : ∀ n m, ¬ (0 < m ∧ m ≤ n) → P n m) : P n m :=
  if h : 0 < m ∧ m ≤ n then
    IH n m h (div_induction P (n - m) m IH base)
  else base n m h


theorem div2_correct
  : ∀ n m, ∃ q r, div2 n m = q ∧ n = m * q + r := by
    intros n m
    induction n, m using div_induction with
    | IH n m H IH =>
      rw [div2_def]
      split
      ·
        simp at *
        rcases IH with ⟨ q, Heq ⟩
        exists q
        rw [ Nat.mul_add
           , Nat.mul_one
           , Nat.add_assoc _ m
           , Nat.add_comm m q
           , ← Nat.add_assoc _ q
           , ← Heq
           , ← Nat.sub_add_comm
           , Nat.add_sub_cancel]
        omega
      ·
        contradiction
    | base n m H =>
      rw [div2_def]
      exists 0
      exists n
      split
      contradiction
      simp

-- 3. Uso de um predicado de domínio
-- Essa técnica consiste em definir um predicado que representa
-- o domínio da função e então definimos a função por recursão
-- sobre esse predicado.


inductive DivDom : ℕ → ℕ → Type where
| Base1 : ∀ m, DivDom 0 (m + 1)
| Base2 : ∀ n, DivDom (n + 1) 1
| Step : ∀ {n m}, DivDom (n - m) m → DivDom n (m + 1)

def div3F {n m} : DivDom n m → ℕ
| DivDom.Base1 _ => 0
| DivDom.Base2 n => n + 1
| DivDom.Step Hrec =>
  div3F Hrec + 1

-- tendo definido a função, o próximo passo é mostrar a totalidade do
-- predicado para o domínio.

def divDom : ∀ (n m : ℕ), m ≠ 0 → DivDom n m
| 0, 0, Heq => by
  simp at *
| 0, m + 1, _Heq => DivDom.Base1 m
| n + 1, 1, _Heq => DivDom.Base2 n
| n + 1, (m + 1) + 1, _Heq => by
  apply DivDom.Step
  apply divDom
  intros H
  rcases H

-- combinando a definição e totalidade do predicado

def div3 (n m : ℕ)(H : m ≠ 0) : ℕ :=
  div3F (divDom n m H)


-- Exercício: Defina uma função div3 que retorna o
-- quociente e o resto da divisão e prove a correção
-- desta versão.

def divR (n m: ℕ) : ℕ × ℕ :=
  if _h : 0 < m ∧ m ≤ n then
    divR (n - m) m + (1,0)
  else (0,n)

#eval divR 11 3
#eval (3,5)+(1,2)


lemma divR_def (n m : ℕ)
  : divR n m = if 0 < m ∧ m ≤ n  then
                  divR (n - m) m + (1,0) else (0,n) := by
  show divR n m = _
  rw [divR]
  rfl


lemma divR_induction (P : ℕ → ℕ → Prop)
  (n m: ℕ)
  (IH : ∀ n m, 0 < m ∧ m ≤ n → P (n - m) m → P n m)
  (base : ∀ n m, ¬ (0 < m ∧ m ≤ n) → P n m) : P n m :=
  if h : 0 < m ∧ m ≤ n then
    IH n m h (divR_induction P (n - m) m IH base)
  else base n m h


theorem divR_correct
  : ∀ n m, m ≠ 0 → ∃ q r, divR n m = (q,r) ∧ n = m * q + r ∧ r < m := by
    intros n m
    intros Hm
    induction n, m using divR_induction with
    | IH n m h IH =>
      rw [divR_def]
      simp only [if_pos h]
      rcases (IH Hm) with ⟨  q,r,HdivR,Hn,Hr ⟩
      use q+1 , r
      simp [HdivR]
      apply And.intro
      ·
        rw [Nat.mul_add]
        rw [Nat.mul_one]
        omega
      ·
        exact Hr
    | base n m IH =>
      rw [divR_def]
      split
      .
        contradiction
      .
        exists 0
        exists n
        simp
        rw [not_and_or] at IH
        rcases IH with  H1 | H2
        ·
          omega
        ·
          simp at H2
          exact H2


-- Exercício: Desenvolva uma função que realiza a
-- intercalação de duas listas previamente ordenadas e
-- prove que esta função preserva a relação de ordenação
-- das listas fornecidas como argumento.


def list_concat : List ℕ → List ℕ →  List ℕ
  | [], ys => ys
  | xs, [] => xs
  | x::xs , y::ys =>
    match Nat.decLt x y with
    | isTrue _    => x :: list_concat xs (y::ys)
    | _           => y :: list_concat (x::xs) ys

#eval list_concat [1,2,3,4] [1,2,3,5,8]
#eval list_concat [1,2,3,4] [1,27,3,5,8]



lemma list_concat_def (xs ys : List ℕ) :
  list_concat xs ys = match xs, ys with
                      | [], _ => ys
                      | _, [] => xs
                      | x::xs', y::ys' =>
                        if x < y then x :: list_concat xs' (y::ys')
                        else y :: list_concat (x::xs') ys' := by
  show list_concat xs ys = _
  cases xs with
  | nil =>
    simp [list_concat]
  | cons x xs' =>
    induction ys with
    | nil =>
      simp [list_concat]
    | cons y ys' _H' =>
      simp [list_concat]
      cases Nat.decLt x y with
      | isTrue h =>
        simp [list_concat, h]
      | isFalse h =>
        simp [list_concat, h]



lemma sort_induction (P : List ℕ → List ℕ → Prop)
  (xs ys : List ℕ)
  (BaseX : ∀ xs ys, xs = [] → P xs ys)
  (BaseY : ∀ xs ys, ys = [] → P xs ys)
  (IHX : ∀ x xs y ys, x < y → P xs (y :: ys) → P (x :: xs) (y :: ys))
  (IHY : ∀ x xs y ys, ¬(x < y) → P (x :: xs) ys → P (x :: xs) (y :: ys)) :
  P xs ys :=
if h : xs = [] then
  BaseX xs ys h
else if h1 : ys = [] then
  BaseY xs ys h1
else
  match xs, ys with
  | (x :: xs'), (y :: ys') =>
    if h2 : x < y then
      IHX x xs' y ys' h2  (sort_induction P xs' (y :: ys') BaseX BaseY IHX IHY)
    else
      IHY x xs' y ys' h2 (sort_induction P (x :: xs') ys' BaseX BaseY IHX IHY)

inductive sort_cat : List ℕ  → Prop
| Base1 : sort_cat []
| Base2 : ∀ x, sort_cat (x :: [])
| PassoIndut : ∀ x y z , x ≤ y → sort_cat (y :: z) → sort_cat (x::y::z)

lemma list_concat_empty_right : list_concat xs [] = xs := by
  induction xs with
  | nil => simp [list_concat]
  | cons x xs' _IH => simp [list_concat]

lemma list_concat_IH : x < y → sort_cat (list_concat (x :: xs) (y :: ys)) → sort_cat (x :: list_concat xs (y :: ys)) := by
  intros H1 H2
  simp [list_concat] at H2
  split at H2
  ·
    assumption
  ·
    rename_i H3
    rename_i H4
    simp [H1] at H3
    simp [Nat.decLt] at H3
    simp [Nat.decLe] at H3
    split at H3
    contradiction
    contradiction

lemma list_concat_IH2 : ¬x < y → sort_cat (list_concat (x :: xs) (y :: ys)) → sort_cat (y :: list_concat (x::xs) ys) := by
  intros H1 H2
  simp [list_concat] at H2
  split at H2
  ·
    contradiction
  ·
    assumption


  lemma sort_cat_sorted2 :
  ∀ xs ys, sort_cat xs → sort_cat ys → sort_cat (list_concat xs ys) := by
  intros xs ys H1 H2
  induction xs,ys using sort_induction with
  | BaseX xs' ys' H3=>
    simp [H3]
    simp [list_concat]
    exact H2
  | BaseY xs' ys' H3=>
    simp [H3]
    simp[list_concat_empty_right]
    exact H1
  | IHX x' xs' y' ys' H3 H4 =>
    cases H1 with
    | Base2 x =>
      rw [list_concat_def]
      simp [if_pos H3]
      simp [list_concat]
      apply sort_cat.PassoIndut
      .
        omega
      .
        exact H2
    | PassoIndut a b bs ih ih' =>
      simp [list_concat]
      split
      ·
        split
        ·
          constructor
          linarith
          apply list_concat_IH
          ·
            assumption
          ·
            aesop
        ·
          constructor
          linarith
          apply list_concat_IH2
          ·
            rename_i H3
            rename_i H4
            cases H4 with
            | isFalse h => assumption
            | isTrue h =>
              simp [h] at H3
              simp [Nat.decLt] at H3
              simp [Nat.decLe] at H3
              split at H3
              rename_i H5
              contradiction
              contradiction
          ·
            aesop
      ·
        rename_i H3
        rename_i H4
        cases H4 with
          | isFalse h => contradiction
          | isTrue h =>
            simp [h] at H3
            simp [Nat.decLt] at H3
            simp [Nat.decLe] at H3
            split at H3
            rename_i H5
            contradiction
            contradiction

  | IHY x' xs' y' ys' H1' H2'=>
    cases H2 with
    | Base2 x =>
      rw [list_concat_def]
      simp [if_pos H1]
      simp [list_concat]
      split
      .
        omega
      .
        apply sort_cat.PassoIndut
        .
          push_neg at H1'
          exact H1'
        .
          exact H1
    | PassoIndut a b bs ih ih' =>
      simp [list_concat]
      split
      ·
        contradiction
      .
        split
        ·
          constructor
          linarith
          apply list_concat_IH
          ·
            assumption
          ·
            aesop
        ·
          constructor
          linarith
          apply list_concat_IH2
          ·
            rename_i H3
            rename_i H4
            cases H4 with
            | isFalse h => assumption
            | isTrue h =>
              simp [h] at H3
              simp [Nat.decLt] at H3
              simp [Nat.decLe] at H3
              split at H3
              rename_i H5
              contradiction
              contradiction
          ·
            aesop
