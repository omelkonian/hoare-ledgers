{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Set'

module CSL (Part : Set) {{_ : DecEq Part}} where

open import Ledger Part
open import HoareLogic Part
open import SL Part
open import Dec Part

-- ** Concurrent separation logic
open import Data.List.Relation.Ternary.Interleaving
_∥_≡_ : L → L → L → Set
l₁ ∥ l₂ ≡ l = Interleaving _≡_ _≡_ l₁ l₂ l

[INTERLEAVE] :
    l₁ ∥ l₂ ≡ l
  → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
  → mods l₁ ♯ mods l₂
  -- → fv P₁ ∪ fv Q₁ S.♯ mod l₂
  -- → fv P₂ ∪ fv Q₂ S.♯ mod l₁
    ---------------------------
  → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
[INTERLEAVE] = {!!}

-- h :
--     s₁ ♯ s₂ ← s
--   → l₁ ∥ l₂ ← l
--   → mod l₁ S.♯ mod l₂
--     -------------------------------
--   → ⟦ l₁ ⟧ s₁ ♯ ⟦ l₂ ⟧ s₂ ← ⟦ l ⟧ s
-- h {s₁}{s₂}{s}{l₁}{l₂}{l} s₁♯s₂ l₁∥l₂ l₁♯l₂ = h₁ , h₂
--   where
--     ps₁ = proj₁ (⟦ l₁ ⟧ s₁)
--     ps₂ = proj₁ (⟦ l₂ ⟧ s₂)

--     All∉ : All (_∉′ ps₂) (list ps₁)
--     All∉ = {!!}

--     h₁ : ⟦ l₁ ⟧ s₁ ♯ ⟦ l₂ ⟧ s₂
--     h₁ = let p = L.filter-none (_∈′? ps₂) {xs = list ps₁} All∉ in {!!} -- subst _ p refl

--     h₂ : ⟦ l ⟧ s ≡ᵐ union (⟦ l₁ ⟧ s₁) (⟦ l₂ ⟧ s₂)
--     h₂ = {!!}

-- [INTERLEAVE] :
--     l₁ ∥ l₂ ← l
--   → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
--   → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
--   → mod l₁ S.♯ mod l₂
--   -- → fv P₁ ∪ fv Q₁ S.♯ mod l₂
--   -- → fv P₂ ∪ fv Q₂ S.♯ mod l₁
--     ---------------------------
--   → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩

-- [INTERLEAVE] {l₁}{l₂}{l}{P₁}{Q₁}{P₂}{Q₂} l₁∥l₂ PlQ PlQ′ l₁♯l₂ = proj₂ axiom⇔denot d
--   where
--     d : (P₁ `∗ P₂) `⊢ (Q₁ `∗ Q₂) `∘ ⟦ l ⟧
--     d {s} (s₁ , s₂ , s₁♯s₂ , Ps₁ , Ps₂) = _ , _ , q , q₁ , q₂
--       where
--         q₁ : Q₁ ∙ ⟦ l₁ ⟧ s₁
--         q₁ = proj₁ axiom⇔denot PlQ Ps₁

--         q₂ : Q₂ ∙ ⟦ l₂ ⟧ s₂
--         q₂ = proj₁ axiom⇔denot PlQ′ Ps₂

--         q : ⟦ l₁ ⟧ s₁ ♯ ⟦ l₂ ⟧ s₂ ← ⟦ l ⟧ s
--         q = {!!} -- h s₁♯s₂ l₁∥l₂ l₁♯l₂
-- -}
