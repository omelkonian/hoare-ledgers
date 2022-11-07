{-# OPTIONS --allow-unsolved-metas #-}
---------------------------------------
-- ** Concurrent separation logic (CSL)

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists
open import Prelude.Sets
open import Prelude.Maps
open import Prelude.Apartness

module UTxO.CSL where

open import UTxO.UTxO
open import UTxO.Ledger
open import UTxO.HoareLogic
open import UTxO.SL

-- ** Proof of CSL's [PAR] rule, which allows for modular reasoning.
[PAR] :
    l₁ ∥ l₂ ≡ l
  → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
  → l₁ ♯ P₂
  → l₂ ♯ P₁
    ---------------------------
  → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
[PAR] = {!!}

open HoareReasoning
ℝ[PAR] :
    l₁ ∥ l₂ ≡ l
  → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
  → l₁ ♯ P₂
  → l₂ ♯ P₁
    ---------------------------
  → ℝ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
ℝ[PAR] eq PlQ PlQ′ p q = mkℝ [PAR] eq PlQ PlQ′ p q
