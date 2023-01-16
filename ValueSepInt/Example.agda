module ValueSepInt.Example where

open import Prelude.Init; open SetAsType
open Integer
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists.Dec
open import Prelude.Monoid

data Part : Type where
  A B C D : Part
unquoteDecl DecEq-Part = DERIVE DecEq [ quote Part , DecEq-Part ]

open import ValueSepInt.Maps
open import ValueSepInt.Ledger Part hiding (A; B; C; D)
open import ValueSepInt.HoareLogic Part
open import ValueSepInt.HoareProperties Part
open import ValueSepInt.SL Part
open import ValueSepInt.CSL Part

t₁ = A —→⟨ 1ℤ ⟩ B; t₂ = D —→⟨ 1ℤ ⟩ C; t₃ = B —→⟨ 1ℤ ⟩ A; t₄ = C —→⟨ 1ℤ ⟩ D
t₁-₄ = L ∋ t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ []

open HoareReasoning

-- 1ℤa) proof using only SL.[FRAME]
_ : ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩
    t₁-₄
    ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩
_ = begin
  A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ   ~⟪ ∗↝ {A ↦ 1ℤ} {B ↦ 0ℤ} {C ↦ 0ℤ ∗ D ↦ 1ℤ} ⟩
  (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟨ t₁ ∶- ℝ[FRAME] (C ↦ 0ℤ ∗ D ↦ 1ℤ) (mkℝ A ↝⁰ B) ⟩
  (A ↦ 0ℤ ∗ B ↦ 1ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟪ ∗↔ {A ↦ 0ℤ ∗ B ↦ 1ℤ} {C ↦ 0ℤ ∗ D ↦ 1ℤ} ⟩
  (C ↦ 0ℤ ∗ D ↦ 1ℤ) ∗ A ↦ 0ℤ ∗ B ↦ 1ℤ ~⟨ t₂ ∶- ℝ[FRAME] (A ↦ 0ℤ ∗ B ↦ 1ℤ) (mkℝ C ↜⁰ D) ⟩
  (C ↦ 1ℤ ∗ D ↦ 0ℤ) ∗ A ↦ 0ℤ ∗ B ↦ 1ℤ ~⟪ ∗↔ {C ↦ 1ℤ ∗ D ↦ 0ℤ} {A ↦ 0ℤ ∗ B ↦ 1ℤ} ⟩
  (A ↦ 0ℤ ∗ B ↦ 1ℤ) ∗ C ↦ 1ℤ ∗ D ↦ 0ℤ ~⟨ t₃ ∶- ℝ[FRAME] (C ↦ 1ℤ ∗ D ↦ 0ℤ) (mkℝ A ↜⁰ B) ⟩
  (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 1ℤ ∗ D ↦ 0ℤ ~⟪ ∗↔ {A ↦ 1ℤ ∗ B ↦ 0ℤ} {C ↦ 1ℤ ∗ D ↦ 0ℤ} ⟩
  (C ↦ 1ℤ ∗ D ↦ 0ℤ) ∗ A ↦ 1ℤ ∗ B ↦ 0ℤ ~⟨ t₄ ∶- ℝ[FRAME] (A ↦ 1ℤ ∗ B ↦ 0ℤ) (mkℝ C ↝⁰ D) ⟩
  (C ↦ 0ℤ ∗ D ↦ 1ℤ) ∗ A ↦ 1ℤ ∗ B ↦ 0ℤ ~⟪ ∗↔ {C ↦ 0ℤ ∗ D ↦ 1ℤ} {A ↦ 1ℤ ∗ B ↦ 0ℤ} ⟩
  (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟪ ↜∗ {A ↦ 1ℤ} {B ↦ 0ℤ} {C ↦ 0ℤ ∗ D ↦ 1ℤ} ⟩
  A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ   ∎

-- 1ℤb) proof using CSL.[INTERLEAVE]
_ : ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩
     t₁-₄
     ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩
_ = begin
  A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ   ~⟪ ∗↝ {A ↦ 1ℤ} {B ↦ 0ℤ} {C ↦ 0ℤ ∗ D ↦ 1ℤ} ⟩
  (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟨ t₁-₄ ∶- ℝ[PAR] auto H₁ H₂ ⟩++
  (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟪ ↜∗ {A ↦ 1ℤ} {B ↦ 0ℤ} {C ↦ 0ℤ ∗ D ↦ 1ℤ} ⟩
  A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 0ℤ ∗ D ↦ 1ℤ   ∎
  where
    H₁ : ℝ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ⟩ t₁ ∷ t₃ ∷ [] ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ⟩
    H₁ = A ↦ 1ℤ ∗ B ↦ 0ℤ ~⟨ t₁ ∶- mkℝ A ↝⁰ B ⟩
        A ↦ 0ℤ ∗ B ↦ 1ℤ ~⟨ t₃ ∶- mkℝ A ↜⁰ B ⟩
        A ↦ 1ℤ ∗ B ↦ 0ℤ ∎

    H₂ : ℝ⟨ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩ t₂ ∷ t₄ ∷ [] ⟨ C ↦ 0ℤ ∗ D ↦ 1ℤ ⟩
    H₂ = C ↦ 0ℤ ∗ D ↦ 1ℤ ~⟨ t₂ ∶- mkℝ C ↜⁰ D ⟩
              C ↦ 1ℤ ∗ D ↦ 0ℤ ~⟨ t₄ ∶- mkℝ C ↝⁰ D ⟩
              C ↦ 0ℤ ∗ D ↦ 1ℤ ∎

-- 2ℤ) overlapping proof
t₁′ = A —→⟨ 1ℤ ⟩ B; t₂′ = C —→⟨ 1ℤ ⟩ A
t₁₂ = L ∋ t₁′ ∷ t₂′ ∷ []

_ : ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 1ℤ ∗ A ↦ 0ℤ ⟩
     t₁₂
     ⟨ A ↦ 0ℤ ∗ B ↦ 1ℤ ∗ C ↦ 0ℤ ∗ A ↦ 1ℤ ⟩
_ = begin A ↦ 1ℤ ∗ B ↦ 0ℤ ∗ C ↦ 1ℤ ∗ A ↦ 0ℤ     ~⟪ ∗↝ {A ↦ 1ℤ} {B ↦ 0ℤ} {C ↦ 1ℤ ∗ A ↦ 0ℤ} ⟩
          (A ↦ 1ℤ ∗ B ↦ 0ℤ) ∗ (C ↦ 1ℤ ∗ A ↦ 0ℤ) ~⟨ t₁₂ ∶- ℝ[PAR] auto H₁ H₂ ⟩++
          (A ↦ 0ℤ ∗ B ↦ 1ℤ) ∗ (C ↦ 0ℤ ∗ A ↦ 1ℤ) ~⟪ ↜∗ {A ↦ 0ℤ} {B ↦ 1ℤ} {C ↦ 0ℤ ∗ A ↦ 1ℤ} ⟩
          A ↦ 0ℤ ∗ B ↦ 1ℤ ∗ C ↦ 0ℤ ∗ A ↦ 1ℤ     ∎
  where
    H₁ : ℝ⟨ A ↦ 1ℤ ∗ B ↦ 0ℤ ⟩ [ t₁′ ] ⟨ A ↦ 0ℤ ∗ B ↦ 1ℤ ⟩
    H₁ = mkℝ A ↝⁰ B

    H₂ : ℝ⟨ C ↦ 1ℤ ∗ A ↦ 0ℤ ⟩ [ t₂′ ] ⟨ C ↦ 0ℤ ∗ A ↦ 1ℤ ⟩
    H₂ = mkℝ C ↝⁰ A
