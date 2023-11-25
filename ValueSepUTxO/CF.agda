{-# OPTIONS --allow-unsolved-metas #-}
module ValueSepUTxO.CF where

open import Prelude.Init; open SetAsType

open import ValueSepUTxO.UTxO
open import ValueSepUTxO.Ledger
open import ValueSepUTxO.HoareLogic

-- ** characteristic formulae

record CF (A : Type) : Type₁ where
  field pre post : A → Assertion
open CF ⦃...⦄ public

mkCF : ∀ {A} → (A → Assertion) → CF A
mkCF f = record {pre = f; post = f}

instance
  CF-Txo : CF TxOutput
  CF-Txo = mkCF λ o → o .address ↦ o .value

  CF-Tx : CF (Resolved t)
  CF-Tx {t} = λ where
    .pre  res → ∗⋯ $ map (pre ∘ proj₂) (resolveInputs t res)
    .post _   → ∗⋯ $ map pre (t .outputs)
   where
    ∗⋯ : List Assertion → Assertion
    ∗⋯ = λ where
      (p ∷ []) → p
      []       → emp
      (p ∷ ps) → p ∗ ∗⋯ ps

  CF-List : ∀ {A} → ⦃ CF A ⦄ → CF (List A)
  CF-List = λ where
    .pre  → λ where
      [] → emp
      (x ∷ xs) → pre x
    .post → λ where
      [] → emp
      (x ∷ xs) → {!!}


  CF-L : CF L
  CF-L = λ where
    .pre  → {!!}
    .post → {!!}
  -- [] = emp , emp
  -- (t ∷ l) = {!!}
