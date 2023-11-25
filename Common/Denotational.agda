module Common.Denotational where

open import Prelude.Init; open SetAsType
open import Prelude.Monad
open import Prelude.Semigroup
open import Prelude.InferenceRules

-- Types that admit denotational semantics under a certain denotational domain.
record Denote (A : Type ℓ) (Domain : Type ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  field ⟦_⟧ : A → Domain
open Denote ⦃...⦄ public

-- ** Denotational domains as a state transformers.

Domain₀ : Pred (Type ℓ) _
Domain₀ S = S → S

Domainₑ : Pred (Type ℓ) _
Domainₑ S = S → Maybe S

Denote₀ : Type ℓ → Type ℓ′ → Type _
Denote₀ A S = Denote A (Domain₀ S)

Denoteₑ : Type ℓ → Type ℓ′ → Type _
Denoteₑ A S = Denote A (Domainₑ S)

private variable A S : Type ℓ

⟦_⟧₀ : ⦃ Denote₀ A S ⦄ → A → Domain₀ S
⟦_⟧₀ = ⟦_⟧

⟦_⟧ₑ : ⦃ Denoteₑ A S ⦄ → A → Domainₑ S
⟦_⟧ₑ = ⟦_⟧

instance
  -- we denote a ledger as the composition of the denotations of its transactions,
  -- i.e. we run all transactions in sequence
  ⟦List⟧₀ : ⦃ Denote₀ A S ⦄ → Denote₀ (List A) S
  ⟦List⟧₀ .⟦_⟧ = λ where
    []       → id
    (x ∷ xs) → ⟦ xs ⟧ ∘ ⟦ x ⟧

  ⟦List⟧ₑ : ⦃ Denoteₑ A S ⦄ → Denoteₑ (List A) S
  ⟦List⟧ₑ .⟦_⟧ = λ where
    []       → return
    (x ∷ xs) → ⟦ x ⟧ >=> ⟦ xs ⟧

comp₀ : ∀ ⦃ _ : Denote₀ A S ⦄ {l l′ : List A} →
  ∀ (s : S) → ⟦ l ◇ l′ ⟧₀ s ≡ (⟦ l′ ⟧₀ ∘ ⟦ l ⟧₀) s
comp₀ {l = []}    = λ _ → refl
comp₀ {l = x ∷ l} = comp₀ {l = l} ∘ ⟦ x ⟧₀

comp : ∀ {S : Type ℓ} ⦃ _ : Denoteₑ A S ⦄ {l l′ : List A} →
  ∀ (s : S) → ⟦ l ++ l′ ⟧ₑ s ≡ (⟦ l ⟧ₑ >=> ⟦ l′ ⟧ₑ) s
comp {l = []}    _ = refl
comp {l = x ∷ l} s with ⟦ x ⟧ s
... | nothing = refl
... | just s′ = comp {l = l} s′
