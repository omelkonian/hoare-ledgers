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

module ValueSepInt.HoareLogic (Part : Type) ⦃ _ : DecEq Part ⦄ where

open import ValueSepInt.Maps
open import ValueSepInt.Ledger Part

-- ** Shallow embedding of logic formulas/propositions.
Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

emp : Assertion
emp m = ∀ k → m k ≡ ε

_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ◇ s₂ ⟩≡ s × P s₁ × Q s₂

_↦_ : Part → V → Assertion
p ↦ n = _[ p ↦ n ]∅

infixr 10 _∗_
infix  11 _↦_

-- ** Hoare triples.
⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Type
⟨ P ⟩ l ⟨ Q ⟩ = P ⊢ Q ∘ ⟦ l ⟧

hoare-base :
  ──────────────
  ⟨ P ⟩ [] ⟨ P ⟩
hoare-base = id

hoare-step :
  ⟨ P ⟩ l ⟨ Q ⟩
  ──────────────────────────
  ⟨ P ∘ ⟦ t ⟧ ⟩ t ∷ l ⟨ Q ⟩
hoare-step PlQ {_} = PlQ

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

axiom-base⋆ : ⟨ P ∘ ⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []} =
  weaken {P′ = P ∘ ⟦ [] ⟧} {l = []} id (hoare-base {P = P})
axiom-base⋆ {P = P} {l = t ∷ l} = id

-- Derived alternative formulation for step, using list concatenation.

hoare-step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ───────────────────
    ⟨ P ⟩ l ++ l′ ⟨ R ⟩
hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR
  = begin
    P
  ⊢⟨ PlQ  ⟩
    Q ∘ ⟦ l ⟧
  ⊢⟨ QlR ⟩
    R ∘ (⟦ l′ ⟧ ∘ ⟦ l ⟧)
  ≗˘⟨ cong R ∘ comp {l} {l′} ⟩
    R ∘ ⟦ l ++ l′ ⟧
  ∎ where open ⊢-Reasoning

-- ** Reasoning syntax for Hoare triples.
module HoareReasoning where
  -- Reasoning newtype (for better type inference).
  record ℝ⟨_⟩_⟨_⟩ (P : Assertion) (l : L) (Q : Assertion) : Type where
    constructor mkℝ_
    field begin_ : ⟨ P ⟩ l ⟨ Q ⟩
    infix -2 begin_
  open ℝ⟨_⟩_⟨_⟩ public
  infix  -2 mkℝ_
  infixr -1 _~⟪_⟩_ _~⟨_⟫_ _~⟨_∶-_⟩_ _~⟨_∶-_⟩++_
  infix  0  _∎

  -- weakening syntax
  _~⟪_⟩_ : ∀ P′ → P′ ⊢ P → ℝ⟨ P ⟩ l ⟨ R ⟩ → ℝ⟨ P′ ⟩ l ⟨ R ⟩
  _~⟪_⟩_ {l = l}{R} _ H (mkℝ PlR) = mkℝ weaken {l = l}{R} H PlR

  -- strengthening syntax
  _~⟨_⟫_ : ∀ R′ → R ⊢ R′ → ℝ⟨ P ⟩ l ⟨ R ⟩ → ℝ⟨ P ⟩ l ⟨ R′ ⟩
  _~⟨_⟫_ {R}{l = l} _ H (mkℝ PlR) = mkℝ strengthen {R}{l = l} H PlR

  -- step syntax
  _~⟨_∶-_⟩_ : ∀ P′ t → ℝ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ℝ⟨ P ⟩ l ⟨ R ⟩ → ℝ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  _~⟨_∶-_⟩_ {l = l} {R = R} P′ t (mkℝ H) (mkℝ PlR) =
    P′ ~⟪ H ⟩ (mkℝ λ {x} Px → hoare-step {l = l}{R} {t = t} PlR {_} Px)

  -- step′ syntax
  _~⟨_∶-_⟩++_ : ∀ P′ → (l : L) → ℝ⟨ P′ ⟩ l ⟨ P ⟩ → ℝ⟨ P ⟩ l′ ⟨ R ⟩ → ℝ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  _~⟨_∶-_⟩++_ {R = R}  P′ l (mkℝ H) (mkℝ PlR) = mkℝ hoare-step′ {l = l} {R = R} H PlR

  _∎ : ∀ P → ℝ⟨ P ⟩ [] ⟨ P ⟩
  P ∎ = mkℝ hoare-base {P = P}
