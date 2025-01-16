import Mathlib.Tactic.Basic

section PropLogic

  variable (A B C : Prop)

  theorem first_theorem : (A → B) → A → B := by
    /-
     G U {H : A} |- B
     --------------      intros H
     G |- A -> B


     H : A <- G
     -----------         exact H
     G |- A
    -/
    intros H -- introdução da implicação
    exact H

  #print first_theorem

  theorem first2 : (A → B) → A → B :=
    λ H : A → B => H


-- *** Exercício 1.

  lemma ex1 : A → B → A := by
    intros H1
    intros
    exact H1


-- *** Exercício 2.

  lemma ex2 : (A → B) → (B → C) → A → C := by
    intros H1 H2 H3
    /-
      G |- B -> C     G |- B
      ----------------------- apply
          G |- C
    -/
    apply H2
    apply H1
    exact H3


-- ** Conjunção
-- par

  theorem and_comm1 : (A ∧ B) → (B ∧ A) := by
    intros H1
    apply And.intro
    ·
      exact H1.right
    ·
      rcases H1 with ⟨ H1 , _H2 ⟩
      exact H1


  theorem and_assoc1 : A ∧ (B ∧ C) → (A ∧ B) ∧ C := by
    intros H
    rcases H with ⟨ HA , HB , HC ⟩
    apply And.intro
    ·
      apply And.intro <;> assumption
    ·
      assumption


-- *** Exercício 3

  theorem ex3 : (A ∧ B) ∧ C -> A ∧ (B ∧ C) := by
    intros H
    rcases H with ⟨ HAB , HC ⟩
    apply And.intro
    .
      rcases HAB with ⟨ HA, _HB ⟩
      exact HA
    .
      apply And.intro
      .
        rcases HAB with ⟨ _HA, HB ⟩
        exact HB
      .
        exact HC

-- *** Exercício 4

  theorem ex4 : ((A ∧ B) → C) → (A → B → C) := by
  intros H1
  intros H2
  intros H3
  apply H1
  apply And.intro
  .
   exact H2
  .
   exact H3

-- *** Exercício 5

  theorem ex5 : (A → B → C) → ((A ∧ B) → C) := by
  intros H1
  intros H2
  apply H1
  rcases H2 with ⟨ HA, _HB ⟩
  .
    exact HA
  .
    rcases H2 with ⟨ _HA, HB ⟩
    exact HB

-- *** Exercício 6

  theorem ex6 : ((A → B) ∧ (A → C)) → A → (B ∧ C) := by
  intros H1
  intros H2
  rcases H1 with ⟨ HA , HB ⟩
  apply And.intro
  .
    apply HA
    exact H2
  .
    apply HB
    exact H2


  -- A ↔ B = (A → B) ∧ (B → A)

  lemma iff_demo : (A ∧ B) ↔ (B ∧ A) := by
    apply Iff.intro           <;>
    intros H                  <;>
    rcases H with ⟨ H1 , H2 ⟩ <;>
    apply And.intro           <;>
    assumption


-- Negação
-- ¬ A ≃ A → False

  lemma modus1 : ((A → B) ∧ ¬ B) → ¬ A := by
    intros H
    rcases H with ⟨ H1 , H2 ⟩
    intros HA
    have HB : B := by
      apply H1
      exact HA
    contradiction

/-
H1 : A -> B
-----------------
B

apply H1

H1 : A -> B
--------------
A



====>
A -> B          A
------------------
       B
-/


  lemma modus2 : ((A → B) ∧ ¬ B) → ¬ A := by
    intros H
    rcases H with ⟨ H1 , H2 ⟩
    intros HA
    apply H2
    apply H1
    exact HA

  lemma contraEx : A → ¬ A → B := by
    intros H H1
    contradiction


-- disjunção
  /-
  Γ |- A ∨ B    Γ ∪ {A} |- C    Γ ∪ {B} |- C
  ------------------------------------------
        Γ |- C

  -/



  lemma or_comm1 : (A ∨ B) → (B ∨ A) := by
    intros H
    rcases H with H1 | H2
    ·
      right
      exact H1
    ·
      left
      exact H2



  lemma orex2 : ((A ∨ B) ∧ ¬ A) → B := by
    intros H
    rcases H with ⟨ H1 , H2 ⟩
    rcases H1 with H3 | H4
    ·
      contradiction
    ·
      exact H4

-- Exercício 8

  lemma ex8 : (A ∨ (B ∧ C)) → (A ∨ B) ∧ (A ∨ C) := by
  intro H
  rcases H with H1 | H2
  .
    apply And.intro
    .
      left
      exact H1
    .
      left
      exact H1
  .
    rcases H2 with ⟨ HB , HC ⟩
    apply And.intro
    .
      right
      exact HB
    .
      right
      exact HC



-- Lógica clássica

open Classical

  -- excluded middle

  #check (em A)

lemma doubleNeg : ¬ (¬ A) ↔ A := by
    apply Iff.intro
    ·
      have H1 : A ∨ ¬ A := em A
      rcases H1 with H1 | H2
      ·
        intros _H3
        exact H1
      ·
        intros H3
        contradiction
    ·
      intros H H1
      contradiction



-- Exercício 9

  lemma ex9 : (¬ B → ¬ A) → (A → B) := by
  intro H
  intro HA
  by_cases H1 : B
  .
    exact H1
  .
    have not_a := H H1
    contradiction

-- Exercício 10

  lemma ex10 : ((A → B) → A) → A := by
  intro H
  by_cases H1 : A
  .
    assumption
  .
    have H2 : (A → B) := by
      intro H3
      contradiction
    exact H H2


end PropLogic
