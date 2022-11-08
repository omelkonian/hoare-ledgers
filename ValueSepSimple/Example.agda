module ValueSepSimple.Example where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.DecLists
open import Prelude.Monoid

data Part : Type where
  A B C D : Part
unquoteDecl DecEq-Part = DERIVE DecEq [ quote Part , DecEq-Part ]

open import ValueSepSimple.Maps
open import ValueSepSimple.Ledger Part hiding (A; B; C; D)
open import ValueSepSimple.HoareLogic Part
open import ValueSepSimple.HoareProperties Part
open import ValueSepSimple.SL Part
open import ValueSepSimple.CSL Part

t₁ = A —→⟨ 1 ⟩ B; t₂ = D —→⟨ 1 ⟩ C; t₃ = B —→⟨ 1 ⟩ A; t₄ = C —→⟨ 1 ⟩ D
t₁-₄ = L ∋ t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ []

open HoareReasoning

-- 1a) proof using only SL.[FRAME]
_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
    t₁-₄
    ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ~⟪ ∗↝ {A ↦ 1} {B ↦ 0} {C ↦ 0 ∗ D ↦ 1} ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟨ t₁ ∶- ℝ[FRAME] (C ↦ 0 ∗ D ↦ 1) (mkℝ A ↝⁰ B) ⟩
          (A ↦ 0 ∗ B ↦ 1) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ ∗↔ {A ↦ 0 ∗ B ↦ 1} {C ↦ 0 ∗ D ↦ 1} ⟩
          (C ↦ 0 ∗ D ↦ 1) ∗ A ↦ 0 ∗ B ↦ 1 ~⟨ t₂ ∶- ℝ[FRAME] (A ↦ 0 ∗ B ↦ 1) (mkℝ C ↜⁰ D) ⟩
          (C ↦ 1 ∗ D ↦ 0) ∗ A ↦ 0 ∗ B ↦ 1 ~⟪ ∗↔ {C ↦ 1 ∗ D ↦ 0} {A ↦ 0 ∗ B ↦ 1} ⟩
          (A ↦ 0 ∗ B ↦ 1) ∗ C ↦ 1 ∗ D ↦ 0 ~⟨ t₃ ∶- ℝ[FRAME] (C ↦ 1 ∗ D ↦ 0) (mkℝ A ↜⁰ B) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 1 ∗ D ↦ 0 ~⟪ ∗↔ {A ↦ 1 ∗ B ↦ 0} {C ↦ 1 ∗ D ↦ 0} ⟩
          (C ↦ 1 ∗ D ↦ 0) ∗ A ↦ 1 ∗ B ↦ 0 ~⟨ t₄ ∶- ℝ[FRAME] (A ↦ 1 ∗ B ↦ 0) (mkℝ C ↝⁰ D) ⟩
          (C ↦ 0 ∗ D ↦ 1) ∗ A ↦ 1 ∗ B ↦ 0 ~⟪ ∗↔ {C ↦ 0 ∗ D ↦ 1} {A ↦ 1 ∗ B ↦ 0} ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ ↜∗ {A ↦ 1} {B ↦ 0} {C ↦ 0 ∗ D ↦ 1} ⟩
          A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ∎

-- 1b) proof using CSL.[INTERLEAVE]
_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
     t₁-₄
     ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ~⟪ ∗↝ {A ↦ 1} {B ↦ 0} {C ↦ 0 ∗ D ↦ 1} ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟨ t₁-₄ ∶- ℝ[PAR] auto H₁ H₂ ⟩++
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ ↜∗ {A ↦ 1} {B ↦ 0} {C ↦ 0 ∗ D ↦ 1} ⟩
          A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ∎
  where
    H₁ : ℝ⟨ A ↦ 1 ∗ B ↦ 0 ⟩ t₁ ∷ t₃ ∷ [] ⟨ A ↦ 1 ∗ B ↦ 0 ⟩
    H₁ = A ↦ 1 ∗ B ↦ 0 ~⟨ t₁ ∶- mkℝ A ↝⁰ B ⟩
        A ↦ 0 ∗ B ↦ 1 ~⟨ t₃ ∶- mkℝ A ↜⁰ B ⟩
        A ↦ 1 ∗ B ↦ 0 ∎

    H₂ : ℝ⟨ C ↦ 0 ∗ D ↦ 1 ⟩ t₂ ∷ t₄ ∷ [] ⟨ C ↦ 0 ∗ D ↦ 1 ⟩
    H₂ = C ↦ 0 ∗ D ↦ 1 ~⟨ t₂ ∶- mkℝ C ↜⁰ D ⟩
              C ↦ 1 ∗ D ↦ 0 ~⟨ t₄ ∶- mkℝ C ↝⁰ D ⟩
              C ↦ 0 ∗ D ↦ 1 ∎

-- 2) overlapping proof
t₁′ = A —→⟨ 1 ⟩ B; t₂′ = C —→⟨ 1 ⟩ A
t₁₂ = L ∋ t₁′ ∷ t₂′ ∷ []

_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 1 ∗ A ↦ 0 ⟩
     t₁₂
     ⟨ A ↦ 0 ∗ B ↦ 1 ∗ C ↦ 0 ∗ A ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 1 ∗ A ↦ 0     ~⟪ ∗↝ {A ↦ 1} {B ↦ 0} {C ↦ 1 ∗ A ↦ 0} ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ (C ↦ 1 ∗ A ↦ 0) ~⟨ t₁₂ ∶- ℝ[PAR] auto H₁ H₂ ⟩++
          (A ↦ 0 ∗ B ↦ 1) ∗ (C ↦ 0 ∗ A ↦ 1) ~⟪ ↜∗ {A ↦ 0} {B ↦ 1} {C ↦ 0 ∗ A ↦ 1} ⟩
          A ↦ 0 ∗ B ↦ 1 ∗ C ↦ 0 ∗ A ↦ 1     ∎
  where
    H₁ : ℝ⟨ A ↦ 1 ∗ B ↦ 0 ⟩ [ t₁′ ] ⟨ A ↦ 0 ∗ B ↦ 1 ⟩
    H₁ = mkℝ A ↝⁰ B

    H₂ : ℝ⟨ C ↦ 1 ∗ A ↦ 0 ⟩ [ t₂′ ] ⟨ C ↦ 0 ∗ A ↦ 1 ⟩
    H₂ = mkℝ C ↝⁰ A
