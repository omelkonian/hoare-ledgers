-------------------------
-- ** Axiomatic semantics

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Ord
open import Prelude.Monad

module ValueSepExact.HoareLogicOper (Part : Type) ⦃ _ : DecEq Part ⦄ where

open import ValueSepExact.Maps
open import ValueSepExact.Ledger Part

-- ** Shallow embedding of logic formulas/propositions.
Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

emp : Assertion
emp m = ∀ k → m k ≡ 0

_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ◇ s₂ ⟩≡ s × P s₁ × Q s₂

_↦_ : Part → ℕ → Assertion
p ↦ n = _[ p ↦ n ]∅

infixr 10 _∗_
infix  11 _↦_

-- ** Hoare triples.
⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Type
⟨ P ⟩ l ⟨ Q ⟩ =
  ∀ {s s′} →
    ∙ P s
    ∙ l  , s —→ s′
      ────────────
      Q s′

hoare-base :
  ──────────────
  ⟨ P ⟩ [] ⟨ P ⟩
hoare-base Ps base = Ps

hoare-step :
  ⟨ P ⟩ l ⟨ Q ⟩
  ──────────────────────────
  ⟨ P ∘ ⟦ t ⟧₀ ⟩ t ∷ l ⟨ Q ⟩
hoare-step {t = t} PlQ {s} Ps (step vt s→) = PlQ Ps s→

consequence :
  ∙ P′ ⊢ P   -- ^ weakening the pre-condition
  ∙ Q  ⊢ Q′  -- ^ strengthening the post-condition
  ∙ ⟨ P  ⟩ l ⟨ Q  ⟩
    ───────────────
    ⟨ P′ ⟩ l ⟨ Q′ ⟩
consequence ⊢P Q⊢ PlQ Ps = Q⊢ ∘ PlQ (⊢P Ps)

-- Utilities for Hoare triples.
weaken : P′ ⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken {l = l} H = consequence {l = l} H id

strengthen : Q ⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen {l = l} H = consequence {l = l} id H

axiom-base⋆ : ⟨ P ∘ ⟦ l ⟧₀ ⟩ l ⟨ P ⟩
axiom-base⋆ {l = []} = weaken id hoare-base
axiom-base⋆ {l = _ ∷ _} Ps (step _ s→) = axiom-base⋆ Ps s→

-- Derived alternative formulation for step, using list concatenation.

hoare-step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ───────────────────
    ⟨ P ⟩ l ++ l′ ⟨ R ⟩
hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR {s} Ps s→s′ =
  let _ , s→ , →s′ = oper-comp˘ s→s′
  in QlR (PlQ Ps s→) →s′

-- ** Reasoning syntax for Hoare triples.
module HoareReasoning where
  infix -2 begin_
  infixr -1 _~⟪_⟩_ _~⟨_⟫_ _~⟨_∶-_⟩_ _~⟨_∶-_⟩++_
  infix  0  _∎

  begin_ = id

  -- weakening syntax
  _~⟪_⟩_ : ∀ P′ → P′ ⊢ P → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ l ⟨ R ⟩
  _~⟪_⟩_ {l = l} _ H PlR = weaken {l = l} H PlR

  -- strengthening syntax
  _~⟨_⟫_ : ∀ R′ → R ⊢ R′ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
  _~⟨_⟫_ {l = l} _ H PlR = strengthen {l = l} H PlR

  -- step syntax
  _~⟨_∶-_⟩_ : ∀ P′ t → ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  _~⟨_∶-_⟩_ {l = l} {R = R} P′ t H PlR Ps (step vt s→) =
    PlR (H Ps (step vt base)) s→

  -- step′ syntax
  _~⟨_∶-_⟩++_ : ∀ P′ → (l : L) → ⟨ P′ ⟩ l ⟨ P ⟩ → ⟨ P ⟩ l′ ⟨ R ⟩ → ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩++ PlR = hoare-step′ {l = l} H PlR

  _∎ : ∀ P → ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = hoare-base {P = p}
