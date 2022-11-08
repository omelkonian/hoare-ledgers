-------------------------
-- ** Axiomatic semantics
-- Alternative using simple predicates.

module ValueSepUTxO.SimpleHoareLogic where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Ord
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Monad
open import Prelude.Apartness

open import ValueSepUTxO.Maps
open import ValueSepUTxO.UTxO
open import ValueSepUTxO.Ledger

-- ** Shallow embedding of logic formulas/propositions.
Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

private variable K V₁ V₂ : Type

emp : Assertion
emp m = ∀ k → k ∉ᵈ m

_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ⊎ s₂ ⟩≡ s × P s₁ × Q s₂

_↦_ : TxOutputRef → TxOutput → Assertion
or ↦ o = _[ or ↦ o ]

infixr 10 _∗_
infix  11 _↦_

⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Type
⟨ P ⟩ l ⟨ Q ⟩ = P ⊢ Q ∘ ⟦ l ⟧₀

hoare-base :
  ──────────────
  ⟨ P ⟩ [] ⟨ P ⟩
hoare-base = id

hoare-step :
  ∙ ⟨ P ⟩ l ⟨ Q ⟩
  ∙ P ⊆¹ IsValidTx t
    ──────────────────────────
    ⟨ P ∘ ⟦ t ⟧₀ ⟩ t ∷ l ⟨ Q ⟩
hoare-step {t = t} PlQ P⇒ {s} Ps′ = PlQ Ps′

consequence :
  ∙ P′ ⊢ P   -- ^ weakening the pre-condition
  ∙ Q  ⊢ Q′  -- ^ strengthening the post-condition
  ∙ ⟨ P  ⟩ l ⟨ Q  ⟩
    ───────────────
    ⟨ P′ ⟩ l ⟨ Q′ ⟩
consequence ⊢P Q⊢ PlQ = Q⊢ ∘ PlQ ∘ ⊢P

-- Utilities for Hoare triples.
weaken : P′ ⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken {l = l} {Q = Q} H = consequence {Q = Q} {l = l} H id

strengthen : Q ⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen {Q = Q} {l = l} H = consequence {Q = Q} {l = l} id H

axiom-base⋆ : ⟨ P ∘ ⟦ l ⟧₀ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []} = weaken {P′ = P ∘ ⟦ [] ⟧₀} {l = []} id (hoare-base {P = P})
axiom-base⋆ {P = P} {l = t ∷ l} = id

-- Derived alternative formulation for step, using list concatenation.

hoare-step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ───────────────────
    ⟨ P ⟩ l ++ l′ ⟨ R ⟩
hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR {s}
  rewrite comp₀ {l}{l′} s = QlR ∘ PlQ

-- ** Reasoning syntax for Hoare triples.
module HoareReasoning where

  -- weakening syntax
  _~⟪_⟩_ : ∀ P′ → P′ ⊢ P → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ l ⟨ R ⟩
  _~⟪_⟩_ {l = l} {R = R} _ = weaken {l = l} {Q = R}

  -- strengthening syntax
  _~⟨_⟫_ : ∀ R′ → R ⊢ R′ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
  _~⟨_⟫_ {P = P} {l = l} _ = strengthen {l = l}

  -- step syntax
  _~⟨_∶-_⟩_ : ∀ P′ t → ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  _~⟨_∶-_⟩_ {l = l} {R = R} P′ t H PlR = PlR ∘ H

  -- step′ syntax
  _~⟨_∶-_⟩++_ : ∀ P′ → (l : L) → ⟨ P′ ⟩ l ⟨ P ⟩ → ⟨ P ⟩ l′ ⟨ R ⟩ → ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  _~⟨_∶-_⟩++_ {R = R} P′ l = hoare-step′ {l = l} {R = R}

  _∎ : ∀ P → ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = hoare-base {P = p}
