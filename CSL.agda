---------------------------------------
-- ** Concurrent separation logic (CSL)

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists
open import Prelude.Sets
open import Prelude.Maps renaming (_♯_ to _♯′_)

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Ternary.Interleaving

module CSL (Part : Set) ⦃ _ : DecEq Part ⦄ where

open import Ledger     Part ⦃ it ⦄
open import HoareLogic2 Part ⦃ it ⦄
open import SL         Part ⦃ it ⦄

-- Interleaving two ledgers is the same as interleaving their respective transation list.
_∥_≡_ : L → L → L → Set
l₁ ∥ l₂ ≡ l = Interleaving _≡_ _≡_ l₁ l₂ l

-- ** Proof of CSL's [PAR] rule, which allows for modular reasoning.
[PAR] :
    l₁ ∥ l₂ ≡ l
  → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
  → l₁ ♯♯ P₂
  → l₂ ♯♯ P₁
    ---------------------------
  → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
[PAR] {.[]} {.[]} {.[]} {P₁} {Q₁} {P₂} {Q₂} [] Pl₁Q Pl₂Q l₁♯P₂ l₂♯P₁
  = P⊢Q
  where
    P⊢Q : P₁ `∗ P₂ `⊢ Q₁ `∗ Q₂
    P⊢Q (s₁ , s₂ , s≡ , Ps₁ , Ps₂) = s₁ , s₂ , s≡ , Pl₁Q Ps₁ , Pl₂Q Ps₂
[PAR] {t ∷ l₁} {l₂} {.t ∷ l} {P₁} {Q₁} {P₂} {Q₂} (refl ∷ˡ inter) Pl₁Q Pl₂Q l₁♯P₂ l₂♯P₁
  -- = {!!}
  = qed
  where
  --   PtX : ⟨ P₁ `∘⟦ t ⟧ₜ ⟩ [ t ] ⟨ P₁ ⟩
  --   PtX = `step {P = P₁} {l = []} {R = P₁} (`base {P = P₁})

  --   rec : ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
  --   rec = [PAR] {P₁ = P₁}{Q₁}{P₂}{Q₂} inter Pl₁Q Pl₂Q (♯♯-skip {P = P₂} l₁♯P₂) l₂♯P₁

  --   -- t♯P₂ : [ t ] ♯♯ P₂
  --   -- t♯P₂ A (here A∈) = l₁♯P₂ A (here A∈)

  --   -- PtX′ : ⟨ P₁ `∗ P₂ ⟩ [ t ] ⟨ P₁ `∗ P₂ ⟩
  --   -- PtX′ = [FRAME] P₂ t♯P₂ PtX

{-

l₂♯P₁ : l₂ ♯♯ P₁
l₁♯P₂ : (t ∷ l₁) ♯♯ P₂

inter : l₁ ∥ l₂ ≡ l

Pl₁Q  : ⟨ P₁ ⟩ t ∷ l₁ ⟨ Q₁ ⟩
  ↝ l₁ ⟨ P₁ `∘⟦ t ⟧⁻¹ ⟩ l₁ ⟨ Q₁ ⟩

  ∃[ P₁′ ] (P₁ ≡ P₁′ ∘⟦ t ⟧) × ⟨ P₁′ ⟩ l ⟨ Q ⟩

Pl₂Q  : ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩

  ↝ ⟨ (P₁ `∘⟦ t ⟧⁻¹ ) `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩

———————————————————————————————————————————— -}

    qed : ⟨ P₁ `∗ P₂ ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
    qed = {!!} -- step′ PtX′ rec


  -- = qed
  -- where
  --   PtX : ⟨ P₁ `∘⟦ t ⟧ₜ ⟩ [ t ] ⟨ P₁ ⟩
  --   PtX = step base

  --   rec : ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
  --   rec = [PAR] inter Pl₁Q Pl₂Q (♯♯-skip {P = P₂} l₁♯P₂) l₂♯P₁

  --   t♯P₂ : [ t ] ♯♯ P₂
  --   t♯P₂ A (here A∈) = l₁♯P₂ A (here A∈)

  --   PtX′ : ⟨ (P₁ `∘⟦ t ⟧ₜ) `∗ P₂ ⟩ [ t ] ⟨ P₁ `∗ P₂ ⟩
  --   PtX′ = [FRAME] P₂ t♯P₂ PtX

  --   qed : ⟨ (P₁ `∘⟦ t ⟧ₜ) `∗ P₂ ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
  --   qed = step′ PtX′ rec
[PAR] {l₁} {.(_ ∷ _)} {.(_ ∷ _)} {P₁} {Q₁} {P₂} {Q₂} (x ∷ʳ p) Pl₁Q Pl₂Q l₁♯P₂ l₂♯P₁ = {!!}

-- [PAR] {l₁} {t ∷ l₂} {.t ∷ l} {P₁} {Q₁} {P₂ `∘⟦ .([ t ]) ⟧} {Q₂} (refl ∷ʳ inter) Pl₁Q (step Pl₂Q) l₁♯P₂ l₂♯P₁
--   = qed
--   where
--     PtX : ⟨ P₂ `∘⟦ t ⟧ₜ ⟩ [ t ] ⟨ P₂ ⟩
--     PtX = step base

--     rec : ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
--     rec = [PAR] inter Pl₁Q Pl₂Q l₁♯P₂ (♯♯-skip {P = P₁} l₂♯P₁)

--     t♯P₁ : [ t ] ♯♯ P₁
--     t♯P₁ A (here A∈) = l₂♯P₁ A (here A∈)

--     PtX′ : ⟨ P₁ `∗ (P₂ `∘⟦ t ⟧ₜ) ⟩ [ t ] ⟨ P₁ `∗ P₂ ⟩
--     PtX′ = begin P₁ `∗ (P₂ `∘⟦ t ⟧ₜ) ~⟪ ∗↔ {P₁} {P₂ `∘⟦ t ⟧ₜ}    ⟩
--                  (P₂ `∘⟦ t ⟧ₜ) `∗ P₁ ~⟨ t ∶- [FRAME] P₁ t♯P₁ PtX ⟩
--                  P₂ `∗ P₁            ~⟪ ∗↔ {P₂} {P₁}             ⟩
--                  P₁ `∗ P₂            ∎
--                  where open HoareReasoning

--     qed : ⟨ P₁ `∗ (P₂ `∘⟦ t ⟧ₜ) ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
--     qed = step′ PtX′ rec
