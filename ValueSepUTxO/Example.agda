{-# OPTIONS --rewriting #-}
module ValueSepUTxO.Example where

open import Agda.Builtin.Equality.Rewrite

open import Prelude.Init; open SetAsType
open Nat hiding (_≥_)
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists hiding (_↦_)
open import Prelude.Lists.Dec
open import Prelude.Ord
open import Prelude.InferenceRules

open import Prelude.Bags
open import ValueSepUTxO.UTxO
open import ValueSepUTxO.Ledger
open import ValueSepUTxO.HoareLogic
open import ValueSepUTxO.HoareProperties
open import ValueSepUTxO.SL
open import ValueSepUTxO.CSL

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

t₁-₄ = L ∋ t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ []

open HoareReasoning
module _ A B {or} {_ : auto∶ A ≢ B} where postulate
  _↝_ : ℝ⟨ A ↦ 1 ∗ B ↦ 0 ⟩ [ A —→⟨ 1 ∣ or ⟩ B ] ⟨ A ↦ 0 ∗ B ↦ 1 ⟩
  _↜_ : ℝ⟨ A ↦ 0 ∗ B ↦ 1 ⟩ [ B —→⟨ 1 ∣ or ⟩ A ] ⟨ A ↦ 1 ∗ B ↦ 0 ⟩

-- proof using only SL.[FRAME]
h : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
    t₁-₄
    ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
h = begin A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ~⟪ (λ {x} → ∗↝ {x = x}) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟨ t₁ ∶- ℝ[FRAME] (C ↦ 0 ∗ D ↦ 1) (A ↝ B) ⟩
          (A ↦ 0 ∗ B ↦ 1) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ (λ {x} → ∗↔ {x = x}) ⟩
          (C ↦ 0 ∗ D ↦ 1) ∗ A ↦ 0 ∗ B ↦ 1 ~⟨ t₂ ∶- ℝ[FRAME] (A ↦ 0 ∗ B ↦ 1) (C ↜ D) ⟩
          (C ↦ 1 ∗ D ↦ 0) ∗ A ↦ 0 ∗ B ↦ 1 ~⟪ (λ {x} → ∗↔ {x = x}) ⟩
          (A ↦ 0 ∗ B ↦ 1) ∗ C ↦ 1 ∗ D ↦ 0 ~⟨ t₃ ∶- ℝ[FRAME] (C ↦ 1 ∗ D ↦ 0) (A ↜ B) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 1 ∗ D ↦ 0 ~⟪ (λ {x} → ∗↔ {x = x}) ⟩
          (C ↦ 1 ∗ D ↦ 0) ∗ A ↦ 1 ∗ B ↦ 0 ~⟨ t₄ ∶- ℝ[FRAME] (A ↦ 1 ∗ B ↦ 0) (C ↝ D) ⟩
          (C ↦ 0 ∗ D ↦ 1) ∗ A ↦ 1 ∗ B ↦ 0 ~⟪ (λ {x} → ∗↔ {x = x}) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ (λ {x} → ↜∗ {x = x}) ⟩
          A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ∎

-- 1b) proof using CSL.[INTERLEAVE]
_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
     t₁-₄
     ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 0 ∗ D ↦ 1   ~⟪ (λ {x} → ∗↝ {x = x}) ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟨ t₁-₄ ∶- ℝ[PAR] (keepˡ keepʳ keepˡ keepʳ []) H₁ H₂ ⟩++
          (A ↦ 1 ∗ B ↦ 0) ∗ C ↦ 0 ∗ D ↦ 1 ~⟪ (λ {x} → ↜∗ {x = x}) ⟩
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


-- ** split example
module _ (A : Address) (n : Value) where postulate
  split : Tx
  split-semantics : ⟨ A ↦ n ⟩ [ split ] ⟨ A ↦ ⌊ n /2⌋ ∗ A ↦ ⌈ n /2⌉ ⟩

split-ex : ⟨ A ↦ 100 ⟩ [ split A 100 ] ⟨ A ↦ 50 ∗ A ↦ 50 ⟩
split-ex = split-semantics A 100

-- ** escrow example
module ESCROW (A B : Address) (n m : Value) where postulate
  init : Tx
  init-semantics : ℝ⟨ P ⟩ [ init ] ⟨ P ⟩

  contribute : Address → Value → Tx
  contribute-semanticsA : ∀ {v} ⦃ _ : auto∶ v ≥ m ⦄ → ℝ⟨ A ↦ v ⟩ [ contribute A m ] ⟨ A ↦ (v ∸ m) ⟩
  contribute-semanticsB : ℝ⟨ B ↦ n ⟩ [ contribute B n ] ⟨ B ↦ 0 ⟩

  payout : Tx
  payout-semantics : ∀ {v} → ℝ⟨ B ↦ v ⟩ [ payout ] ⟨ B ↦ (v + n + m) ⟩

escrow-ex : let open ESCROW A B 10 20 in
  ⟨ B ↦ 10 ∗ A ↦ 50 ⟩
  init ∷ contribute B 10 ∷ contribute A 20 ∷ payout ∷ []
  ⟨ B ↦ 30 ∗ A ↦ 30 ⟩
escrow-ex = let open ESCROW A B 10 20 in begin
  B ↦ 10 ∗ A ↦ 50 ~⟨ init ∶- init-semantics ⟩
  B ↦ 10 ∗ A ↦ 50 ~⟨ contribute B 10 ∶- ℝ[FRAME] (A ↦ 50) contribute-semanticsB ⟩
  B ↦  0 ∗ A ↦ 50 ~⟪ (λ {x} → ∗↔ {x = x}) ⟩
  A ↦ 50 ∗ B ↦  0 ~⟨ contribute A 20 ∶- ℝ[FRAME] (B ↦ 0)  contribute-semanticsA ⟩
  A ↦ 30 ∗ B ↦  0 ~⟪ (λ {x} → ∗↔ {x = x}) ⟩
  B ↦ 0  ∗ A ↦ 30 ~⟨ payout ∶- ℝ[FRAME] (A ↦ 30) payout-semantics ⟩
  B ↦ 30 ∗ A ↦ 30 ∎

-- -- ** crowdfunding example

-- -- ** final example
-- postulate
--   txs : Ledger
--   -- ≈ [split(A,100,50,50)]
--   -- ∥ ESCROW.[init(A,B,10,30), contribute(B,10), contribute(A,30), payout()]
--   -- ∥ CROWDFUNDING.[contribute(A,50), contribute(C,1000)]
--   final-ex : ⟨ B ↦ 10 ∗ A ↦ 100 ∗ C ↦ 1000 ⟩ txs ⟨ B ↦ 30 ∗ A → 0 ∗ C ↦ 0 ⟩
--            -- ∩ CROWDFUNDING.state == SUCCESS

-- ** fraud detection

VL∅ : Pred₀ L
VL∅ = VL ∅

-- utxo : L → S
-- utxo l = ⟦ l ⟧ ∅

compress :
  ∙ l₁ ∥ l₂ ≡ l
  ∙ ⟨ P ⟩ l₁ ⟨ P ⟩
  ∙ ⟨ Q ⟩ l₂ ⟨ Q′ ⟩
    ──────────────────────
    ⟨ P ∗ Q ⟩ l ⟨ P ∗ Q′ ⟩
compress = [PAR]

detect : ∀ (l₁ l₂ l : L) (vl : VL∅ l) →
  ∙ l₁ ∥ l₂ ≡ l
  ∙ ⟨ P ⟩ l₁ ⟨ P ⟩
  ∙ ⟨ Q ⟩ l₂ ⟨ Q′ ⟩
    ───────────────────────
    ⟨ P ∗ Q ⟩ l₂ ⟨ P ∗ Q′ ⟩
    -- ∙ ⟦ l₁ ⟧ ≈ ⟦ [] ⟧
    -- ∙ ⟦ l ⟧ ≈ ⟦ l₁ ∥ l₂ ⟧ ≈ ⟦ l₂ ⟧
    -- ∙ ⟨ P ∗ Q ⟩ l ⟨ P ∗ Q′ ⟩
detect {P}{Q}{Q′} l₁ l₂ l vl ≡l Pl₁ = [FRAME]˘ {l = l₂} P
