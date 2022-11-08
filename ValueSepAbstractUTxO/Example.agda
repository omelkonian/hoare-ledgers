{-# OPTIONS --rewriting #-}
module ValueSepAbstractUTxO.Example where

open import Agda.Builtin.Equality.Rewrite

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists hiding (_↦_)
open import Prelude.DecLists

open import Prelude.Bags
open import ValueSepAbstractUTxO.UTxO
open import ValueSepAbstractUTxO.Ledger
open import ValueSepAbstractUTxO.HoareLogic
open import ValueSepAbstractUTxO.HoareProperties
open import ValueSepAbstractUTxO.SL
open import ValueSepAbstractUTxO.CSL

A B C D : Address
A = 111; B = 222; C = 333; D = 444

postulate t₀ : Tx
t₀₀ = (t₀ ♯) at 0
t₀₁ = (t₀ ♯) at 1

postulate
  mkValidator : TxOutput → (TxInfo → DATA → Bool)
  in₁ : (mkValidator t₀₀) ♯ ≡ A
  in₂ : (mkValidator t₀₁) ♯ ≡ D
{-# REWRITE in₁ #-}
{-# REWRITE in₂ #-}

_—→⟨_∣_⟩_ : Address → Value → TxOutput → Address → Tx
A —→⟨ v ∣ or ⟩ B = record
  { inputs  = [ record { outputRef = or ; validator = mkValidator or; redeemer = 0 } ]
  ; outputs = [ v at B ]
  ; forge   = 0
  }

t₁ t₂ t₃ t₄ : Tx
-- t₀ = record {inputs = []; outputs = 1 at A ∷ 1 at D ∷ []; forge = 2}
t₁ = A —→⟨ 1 ∣ t₀₀ ⟩ B
t₂ = D —→⟨ 1 ∣ t₀₁ ⟩ C

t₁₀ = (t₁ ♯) at 0
t₂₀ = (t₂ ♯) at 0
postulate
  in₃ : (mkValidator t₁₀) ♯ ≡ B
  in₄ : (mkValidator t₂₀) ♯ ≡ C
{-# REWRITE in₃ #-}
{-# REWRITE in₄ #-}

t₃ = B —→⟨ 1 ∣ t₁₀ ⟩ A
t₄ = C —→⟨ 1 ∣ t₂₀ ⟩ D

t₁-₄ = List Tx ∋ t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ []

open HoareReasoning
postulate
  _↝_ : ∀ A B {or} → {_ : True ¿ A ≢ B ¿} → ℝ⟨ A ↦ 1 ∗ B ↦ 0 ⟩ [ A —→⟨ 1 ∣ or ⟩ B ] ⟨ A ↦ 0 ∗ B ↦ 1 ⟩
  _↜_ : ∀ A B {or} → {_ : True ¿ A ≢ B ¿} → ℝ⟨ A ↦ 0 ∗ B ↦ 1 ⟩ [ B —→⟨ 1 ∣ or ⟩ A ] ⟨ A ↦ 1 ∗ B ↦ 0 ⟩

-- proof using only SL.[FRAME]
h : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
    t₁-₄
    ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
h = begin A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ~⟪ (λ {x} → ∗↝ {A ↦ 1} {B ↦ 0} {C ↦ 0 ∗ D ↦ 1} {x}) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟨ t₁ ∶- ℝ[FRAME] (C ↦ 0 ∗ D ↦ 1) (A ↝ B) ⟩
          (A ↦ 0 ∗ B ↦ 1) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ (λ {x} → ∗↔ {A ↦ 0 ∗ B ↦ 1} {C ↦ 0 ∗ D ↦ 1} {x}) ⟩
          (C ↦ 0 ∗ D ↦ 1) ∗ A ↦ 0 ∗ B ↦ 1 ~⟨ t₂ ∶- ℝ[FRAME] (A ↦ 0 ∗ B ↦ 1) (C ↜ D) ⟩
          (C ↦ 1 ∗ D ↦ 0) ∗ A ↦ 0 ∗ B ↦ 1 ~⟪ (λ {x} → ∗↔ {C ↦ 1 ∗ D ↦ 0} {A ↦ 0 ∗ B ↦ 1} {x}) ⟩
          (A ↦ 0 ∗ B ↦ 1) ∗ C ↦ 1 ∗ D ↦ 0 ~⟨ t₃ ∶- ℝ[FRAME] (C ↦ 1 ∗ D ↦ 0) (A ↜ B) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 1 ∗ D ↦ 0 ~⟪ (λ {x} → ∗↔ {A ↦ 1 ∗ B ↦ 0} {C ↦ 1 ∗ D ↦ 0} {x}) ⟩
          (C ↦ 1 ∗ D ↦ 0) ∗ A ↦ 1 ∗ B ↦ 0 ~⟨ t₄ ∶- ℝ[FRAME] (A ↦ 1 ∗ B ↦ 0) (C ↝ D) ⟩
          (C ↦ 0 ∗ D ↦ 1) ∗ A ↦ 1 ∗ B ↦ 0 ~⟪ (λ {x} → ∗↔ {C ↦ 0 ∗ D ↦ 1} {A ↦ 1 ∗ B ↦ 0} {x}) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ (λ {x} → ↜∗ {A ↦ 1} {B ↦ 0} {C ↦ 0 ∗ D ↦ 1} {x}) ⟩
          A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ∎

-- 1b) proof using CSL.[INTERLEAVE]
_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
     t₁-₄
     ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ~⟪ (λ {x} → ∗↝ {A ↦ 1} {B ↦ 0} {C ↦ 0 ∗ D ↦ 1} {x}) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟨ t₁-₄ ∶- ℝ[PAR] (keepˡ keepʳ keepˡ keepʳ []) H₁ H₂ ⟩++
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ (λ {x} → ↜∗ {A ↦ 1} {B ↦ 0} {C ↦ 0 ∗ D ↦ 1} {x}) ⟩
          A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ∎
  where
    H₁ : ℝ⟨ A ↦ 1 ∗ B ↦ 0 ⟩ t₁ ∷ t₃ ∷ [] ⟨ A ↦ 1 ∗ B ↦ 0 ⟩
    H₁ = A ↦ 1 ∗ B ↦ 0 ~⟨ t₁ ∶- A ↝ B ⟩
         A ↦ 0 ∗ B ↦ 1 ~⟨ t₃ ∶- A ↜ B ⟩
         A ↦ 1 ∗ B ↦ 0 ∎

    H₂ : ℝ⟨ C ↦ 0 ∗ D ↦ 1 ⟩ t₂ ∷ t₄ ∷ [] ⟨ C ↦ 0 ∗ D ↦ 1 ⟩
    H₂ = C ↦ 0 ∗ D ↦ 1 ~⟨ t₂ ∶- C ↜ D ⟩
         C ↦ 1 ∗ D ↦ 0 ~⟨ t₄ ∶- C ↝ D ⟩
         C ↦ 0 ∗ D ↦ 1 ∎
