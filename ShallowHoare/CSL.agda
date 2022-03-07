---------------------------------------
-- ** Concurrent separation logic (CSL)

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists
open import Prelude.Sets
open import Prelude.Maps

module ShallowHoare.CSL (Part : Set) ⦃ _ : DecEq Part ⦄ where

open import ShallowHoare.Ledger     Part ⦃ it ⦄
open import ShallowHoare.HoareLogic Part ⦃ it ⦄
open import ShallowHoare.SL         Part ⦃ it ⦄

-- ** Proof of CSL's [PAR] rule, which allows for modular reasoning.
postulate
  [PAR] :
      l₁ ∥ l₂ ≡ l
    → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
    → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
    → l₁ ♯♯ P₂
    → l₂ ♯♯ P₁
      ---------------------------
    → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
