open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Set'

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Ternary.Interleaving

module CSL (Part : Set) {{_ : DecEq Part}} where

open import Ledger Part
open import HoareLogic Part
open import SL Part
open import Dec Part

-- ** Concurrent separation logic
_∥_≡_ : L → L → L → Set
l₁ ∥ l₂ ≡ l = Interleaving _≡_ _≡_ l₁ l₂ l

postulate
  ♯-skipˡ : ∀ {A : Set} {{_ : DecEq A}} {xs ys zs : Set⟨ A ⟩} → (xs ∪ ys) ♯ zs → ys ♯ zs
  ♯-skipʳ : ∀ {A : Set} {{_ : DecEq A}} {xs ys zs : Set⟨ A ⟩} → xs ♯ (ys ∪ zs) → xs ♯ zs

[INTERLEAVE] :
    l₁ ∥ l₂ ≡ l
  → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
  → mods l₁ ♯ mods l₂
    ---------------------------
  → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
[INTERLEAVE] {.[]} {.[]} {.[]} {P₁}{Q₁}{P₂}{Q₂} [] Pl₁Q Pl₂Q mods♯
  = denot⇒axiom P⊢Q
  where
    P⊢Q : P₁ `∗ P₂ `⊢ Q₁ `∗ Q₂
    P⊢Q (s₁ , s₂ , s≡ , Ps₁ , Ps₂) = s₁ , s₂ , s≡ , axiom⇒denot Pl₁Q Ps₁ , axiom⇒denot Pl₂Q Ps₂

[INTERLEAVE] {t ∷ l₁} {l₂} {.t ∷ l} {P₁ `∘ .(⟦ t ⟧ₜ)} {Q₁} {P₂} {Q₂} (refl ∷ˡ inter) (step Pl₁Q) Pl₂Q mods♯
  = qed
  where
    PtX : ⟨ P₁ `∘ ⟦ t ⟧ₜ ⟩ [ t ] ⟨ P₁ ⟩
    PtX = step base

    mods♯′ : mods l₁ ♯ mods l₂
    mods♯′ = ♯-skipˡ {xs = fromList (sender t ∷ receiver t ∷ [])}{mods l₁}{mods l₂} mods♯

    rec : ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
    rec = [INTERLEAVE] inter Pl₁Q Pl₂Q mods♯′

    postulate P⇒l₂ : addr A P₂ → A ∈′ mods l₂

    t♯P₂ : [ t ] ♯♯ P₂
    t♯P₂ A (here A∈) A∈′ = ♯→♯′ {xs = mods (t ∷ l₁)} {ys = mods l₂} mods♯ A (∈-++⁺ˡ $ ∈-nub⁺ A∈) (P⇒l₂ A∈′)

    PtX′ : ⟨ (P₁ `∘ ⟦ t ⟧ₜ) `∗ P₂ ⟩ [ t ] ⟨ P₁ `∗ P₂ ⟩
    PtX′ = fr P₂ t♯P₂ PtX

    qed : ⟨ (P₁ `∘ ⟦ t ⟧ₜ) `∗ P₂ ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
    qed = step′ PtX′ rec
[INTERLEAVE] {t ∷ l₁} {l₂} {.t ∷ l} {P₁} {Q₁} {P₂} {Q₂} (refl ∷ˡ inter)
             (weaken-strengthen {P₁}{P₁′}{Q₁′}{Q₁} pre post Pl₁Q) Pl₂Q mods♯
  = qed
  where
    h : ⟨ P₁′ `∗ P₂ ⟩ t ∷ l ⟨ Q₁′ `∗ Q₂ ⟩
    h = [INTERLEAVE] (refl ∷ˡ inter) Pl₁Q Pl₂Q mods♯

    pre′ : P₁ `∗ P₂ `⊢ P₁′ `∗ P₂
    pre′ (s₁ , s₂ , s≡ , Ps₁ , Ps₂) = (s₁ , s₂ , s≡ , pre Ps₁ , Ps₂)

    post′ : Q₁′ `∗ Q₂ `⊢ Q₁ `∗ Q₂
    post′ (s₁ , s₂ , s≡ , Qs₁ , Qs₂) = (s₁ , s₂ , s≡ , post Qs₁ , Qs₂)

    qed : ⟨ P₁ `∗ P₂ ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
    qed = weaken-strengthen pre′ post′ h

[INTERLEAVE] {l₁} {t ∷ l₂} {.t ∷ l} {P₁} {Q₁} {P₂ `∘ .(⟦ t ⟧ₜ)} {Q₂} (refl ∷ʳ inter) Pl₁Q (step Pl₂Q) mods♯
  = qed
  where
    PtX : ⟨ P₂ `∘ ⟦ t ⟧ₜ ⟩ [ t ] ⟨ P₂ ⟩
    PtX = step base

    mods♯′ : mods l₁ ♯ mods l₂
    mods♯′ = ♯-skipʳ {xs = mods l₁}{fromList (sender t ∷ receiver t ∷ [])}{mods l₂} mods♯

    rec : ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
    rec = [INTERLEAVE] inter Pl₁Q Pl₂Q mods♯′

    postulate P⇒l₁ : addr A P₁ → A ∈′ mods l₁

    t♯P₁ : [ t ] ♯♯ P₁
    t♯P₁ A (here A∈) A∈′ = ♯→♯′ {xs = mods l₁} {ys = mods (t ∷ l₂)} mods♯ A (P⇒l₁ A∈′) (∈-++⁺ˡ $ ∈-nub⁺ A∈)

    PtX′ : ⟨ P₁ `∗ (P₂ `∘ ⟦ t ⟧ₜ) ⟩ [ t ] ⟨ P₁ `∗ P₂ ⟩
    PtX′ = begin P₁ `∗ (P₂ `∘ ⟦ t ⟧ₜ) ~⟨ ∗↔ {P₁} {P₂ `∘ ⟦ t ⟧ₜ} ⟩
                 (P₂ `∘ ⟦ t ⟧ₜ) `∗ P₁ ~⟨ t ∶- fr P₁ t♯P₁ PtX    ⟩
                 P₂ `∗ P₁             ~⟨ ∗↔ {P₂} {P₁}           ⟩
                 P₁ `∗ P₂             ∎
                 where open HoareReasoning

    qed : ⟨ P₁ `∗ (P₂ `∘ ⟦ t ⟧ₜ) ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
    qed = step′ PtX′ rec

[INTERLEAVE] {l₁} {t ∷ l₂} {.t ∷ l} {P₁} {Q₁} {P₂} {Q₂} (refl ∷ʳ inter) Pl₁Q
             (weaken-strengthen {P₂}{P₂′}{Q₂′}{Q₂} pre post Pl₂Q) mods♯
  = qed
  where
    h : ⟨ P₁ `∗ P₂′ ⟩ t ∷ l ⟨ Q₁ `∗ Q₂′ ⟩
    h = [INTERLEAVE] (refl ∷ʳ inter) Pl₁Q Pl₂Q mods♯

    pre′ : P₁ `∗ P₂ `⊢ P₁ `∗ P₂′
    pre′ (s₁ , s₂ , s≡ , Ps₁ , Ps₂) = (s₁ , s₂ , s≡ , Ps₁ , pre Ps₂)

    post′ : Q₁ `∗ Q₂′ `⊢ Q₁ `∗ Q₂
    post′ (s₁ , s₂ , s≡ , Qs₁ , Qs₂) = (s₁ , s₂ , s≡ , Qs₁ , post Qs₂)

    qed : ⟨ P₁ `∗ P₂ ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
    qed = weaken-strengthen pre′ post′ h
