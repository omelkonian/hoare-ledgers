open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
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

postulate
  ♯-skipˡ : ∀ {A : Set} {{_ : DecEq A}} {xs ys zs : Set⟨ A ⟩} → (xs ∪ ys) ♯ zs → ys ♯ zs
  ♯-skipʳ : ∀ {A : Set} {{_ : DecEq A}} {xs ys zs : Set⟨ A ⟩} → (xs ∪ ys) ♯ zs → xs ♯ zs

[INTERLEAVE] :
    l₁ ∥ l₂ ≡ l
  → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
  → mods l₁ ♯ mods l₂
    ---------------------------
  → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
[INTERLEAVE] {.[]} {.[]} {.[]} {P₁}{Q₁}{P₂}{Q₂} [] Pl₁Q Pl₂Q mods♯ = {!!}
[INTERLEAVE] {t ∷ l₁} {l₂} {.t ∷ l} {P₁}{Q₁}{P₂}{Q₂} (refl ∷ˡ inter) Pl₁Q Pl₂Q mods♯
  = {!!}
  where
    postulate P₁′ : Assertion

    PtX : ⟨ P₁ ⟩ [ t ] ⟨ P₁′ ⟩
    PtX = {!!}

    Pl₁Q′ : ⟨ P₁′ ⟩ l₁ ⟨ Q₁ ⟩
    Pl₁Q′ = {!!}

    mods♯′ : mods l₁ ♯ mods l₂
    mods♯′ = ♯-skipˡ {xs = fromList (sender t ∷ receiver t ∷ [])}{mods l₁}{mods l₂} mods♯

    rec : ⟨ P₁′ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
    rec = [INTERLEAVE] inter Pl₁Q′ Pl₂Q mods♯′

    postulate P⇒l₂ : addr A P₂ → A ∈′ mods l₂

    open import Data.List.Membership.Propositional.Properties

    t♯P₂ : [ t ] ♯♯ P₂
    t♯P₂ A (here A∈) A∈′ = ♯→♯′ {xs = mods (t ∷ l₁)} {ys = mods l₂} mods♯ A (∈-++⁺ˡ $ ∈-nub⁺ A∈) (P⇒l₂ A∈′)

    PtX′ : ⟨ P₁ `∗ P₂ ⟩ [ t ] ⟨ P₁′ `∗ P₂ ⟩
    PtX′ = fr P₂ t♯P₂ PtX

    qed : ⟨ P₁ `∗ P₂ ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
    qed = step′ PtX′ rec

[INTERLEAVE] {l₁} {t ∷ l₂} {.t ∷ l} {P₁}{Q₁}{P₂}{Q₂} (refl ∷ʳ inter) Pl₁Q Pl₂Q mods♯ = {!!}

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
