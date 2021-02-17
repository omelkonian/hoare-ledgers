open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists
open import Prelude.Sets
open import Prelude.Maps renaming (_♯_ to _♯′_)

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Ternary.Interleaving

module CSL (Part : Set) ⦃ _ : DecEq Part ⦄ where

open import Ledger Part
open import HoareLogic Part
open import SL Part

-- ** Concurrent separation logic
_∥_≡_ : L → L → L → Set
l₁ ∥ l₂ ≡ l = Interleaving _≡_ _≡_ l₁ l₂ l

[INTERLEAVE] :
    l₁ ∥ l₂ ≡ l
  → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
  → l₁ ♯♯ P₂
  → l₂ ♯♯ P₁
    ---------------------------
  → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
[INTERLEAVE] {.[]} {.[]} {.[]} {P₁}{Q₁}{P₂}{Q₂} [] Pl₁Q Pl₂Q _ _
  = denot⇒axiom P⊢Q
  where
    P⊢Q : P₁ `∗ P₂ `⊢ Q₁ `∗ Q₂
    P⊢Q (s₁ , s₂ , s≡ , Ps₁ , Ps₂) = s₁ , s₂ , s≡ , axiom⇒denot Pl₁Q Ps₁ , axiom⇒denot Pl₂Q Ps₂

[INTERLEAVE] {t ∷ l₁} {l₂} {.t ∷ l} {P₁ `∘⟦ .([ t ]) ⟧} {Q₁} {P₂} {Q₂} (refl ∷ˡ inter) (step Pl₁Q) Pl₂Q l₁♯P₂ l₂♯P₁
  = qed
  where
    PtX : ⟨ P₁ `∘⟦ t ⟧ₜ ⟩ [ t ] ⟨ P₁ ⟩
    PtX = step base

    rec : ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
    rec = [INTERLEAVE] inter Pl₁Q Pl₂Q (♯♯-skip {P = P₂} l₁♯P₂) l₂♯P₁

    t♯P₂ : [ t ] ♯♯ P₂
    t♯P₂ A (here A∈) = l₁♯P₂ A (here A∈)

    PtX′ : ⟨ (P₁ `∘⟦ t ⟧ₜ) `∗ P₂ ⟩ [ t ] ⟨ P₁ `∗ P₂ ⟩
    PtX′ = [FRAME] P₂ t♯P₂ PtX

    qed : ⟨ (P₁ `∘⟦ t ⟧ₜ) `∗ P₂ ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
    qed = step′ PtX′ rec
[INTERLEAVE] {t ∷ l₁} {l₂} {.t ∷ l} {P₁} {Q₁} {P₂} {Q₂} (refl ∷ˡ inter)
             (consequence {P₁}{P₁′}{Q₁′}{Q₁} pre post Pl₁Q) Pl₂Q l₁♯P₂ l₂♯P₁
  = denot⇒axiom qed
  where
    pre′ : P₁ `∗ P₂ `⊢ P₁′ `∗ P₂
    pre′ (s₁ , s₂ , s≡ , Ps₁ , Ps₂) = (s₁ , s₂ , s≡ , pre Ps₁ , Ps₂)

    post′ : Q₁′ `∗ Q₂ `⊢ Q₁ `∗ Q₂
    post′ (s₁ , s₂ , s≡ , Qs₁ , Qs₂) = (s₁ , s₂ , s≡ , post Qs₁ , Qs₂)

    qed : (P₁ `∗ P₂) `⊢ (Q₁ `∗ Q₂) `∘⟦ t ∷ l ⟧
    qed {s₀} Ps₀@(s , _ , _ , Ps , _) = axiom⇒denot {P = P₁ `∗ P₂} {Q = Q₁ `∗ Q₂} (consequence pre′ post′ h) Ps₀
       where
         l₂♯P₁′ : l₂ ♯♯ P₁′
         l₂♯P₁′ A A∈l A∈P with ¿ A ∈ᵈ s ¿
         ... | yes A∈ = l₂♯P₁ A A∈l (∈⇒addr {P = P₁} A∈ Ps)
         ... | no  A∉ = ∉⇒¬addr {P = P₁′} A∉ (pre Ps) A∈P

         h : ⟨ P₁′ `∗ P₂ ⟩ t ∷ l ⟨ Q₁′ `∗ Q₂ ⟩
         h = [INTERLEAVE] (refl ∷ˡ inter) Pl₁Q Pl₂Q l₁♯P₂ l₂♯P₁′

[INTERLEAVE] {l₁} {t ∷ l₂} {.t ∷ l} {P₁} {Q₁} {P₂ `∘⟦ .([ t ]) ⟧} {Q₂} (refl ∷ʳ inter) Pl₁Q (step Pl₂Q) l₁♯P₂ l₂♯P₁
  = qed
  where
    PtX : ⟨ P₂ `∘⟦ t ⟧ₜ ⟩ [ t ] ⟨ P₂ ⟩
    PtX = step base

    rec : ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
    rec = [INTERLEAVE] inter Pl₁Q Pl₂Q l₁♯P₂ (♯♯-skip {P = P₁} l₂♯P₁)

    t♯P₁ : [ t ] ♯♯ P₁
    t♯P₁ A (here A∈) = l₂♯P₁ A (here A∈)

    PtX′ : ⟨ P₁ `∗ (P₂ `∘⟦ t ⟧ₜ) ⟩ [ t ] ⟨ P₁ `∗ P₂ ⟩
    PtX′ = begin P₁ `∗ (P₂ `∘⟦ t ⟧ₜ) ~⟨ ∗↔ {P₁} {P₂ `∘⟦ t ⟧ₜ}   ⟩
                 (P₂ `∘⟦ t ⟧ₜ) `∗ P₁ ~⟨ t ∶- [FRAME] P₁ t♯P₁ PtX ⟩
                 P₂ `∗ P₁             ~⟨ ∗↔ {P₂} {P₁}             ⟩
                 P₁ `∗ P₂             ∎
                 where open HoareReasoning

    qed : ⟨ P₁ `∗ (P₂ `∘⟦ t ⟧ₜ) ⟩ t ∷ l ⟨ Q₁ `∗ Q₂ ⟩
    qed = step′ PtX′ rec

[INTERLEAVE] {l₁} {t ∷ l₂} {.t ∷ l} {P₁} {Q₁} {P₂} {Q₂} (refl ∷ʳ inter) Pl₁Q
             (consequence {P₂}{P₂′}{Q₂′}{Q₂} pre post Pl₂Q) l₁♯P₂ l₂♯P₁
  = denot⇒axiom qed
  where
    pre′ : P₁ `∗ P₂ `⊢ P₁ `∗ P₂′
    pre′ (s₁ , s₂ , s≡ , Ps₁ , Ps₂) = (s₁ , s₂ , s≡ , Ps₁ , pre Ps₂)

    post′ : Q₁ `∗ Q₂′ `⊢ Q₁ `∗ Q₂
    post′ (s₁ , s₂ , s≡ , Qs₁ , Qs₂) = (s₁ , s₂ , s≡ , Qs₁ , post Qs₂)

    qed : (P₁ `∗ P₂) `⊢ (Q₁ `∗ Q₂) `∘⟦ t ∷ l ⟧
    qed Ps₀@(_ , s , _ , _ , Ps) = axiom⇒denot {P = P₁ `∗ P₂} {Q = Q₁ `∗ Q₂} (consequence pre′ post′ h) Ps₀
       where
         l₁♯P₂′ : l₁ ♯♯ P₂′
         l₁♯P₂′ A A∈l A∈P with ¿ A ∈ᵈ s ¿
         ... | yes A∈ = l₁♯P₂ A A∈l (∈⇒addr {P = P₂} A∈ Ps)
         ... | no  A∉ = ∉⇒¬addr {P = P₂′} A∉ (pre Ps) A∈P

         h : ⟨ P₁ `∗ P₂′ ⟩ t ∷ l ⟨ Q₁ `∗ Q₂′ ⟩
         h = [INTERLEAVE] (refl ∷ʳ inter) Pl₁Q Pl₂Q l₁♯P₂′ l₂♯P₁
