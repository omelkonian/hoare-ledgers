-------------------------
-- ** Axiomatic semantics

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Ord

module ValueSep.WeakHoareLogic (Part : Set) ⦃ _ : DecEq Part ⦄ where

open import ValueSep.Maps
-- NB. ⦃ it ⦄ required due to Agda bug, reported at https://github.com/agda/agda/issues/5093
open import ValueSep.Ledger Part ⦃ it ⦄

-- ** Shallow embedding of logic formulas/propositions.
Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

emp : Assertion
emp m = ∀ k → k ∉ᵈ m

_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ◇ s₂ ⟩≡ s × P s₁ × Q s₂

_↦_ : Part → ℕ → Assertion
p ↦ n = _[ p ↦ n ]

infixr 10 _∗_
infix  11 _↦_

-- ** Hoare triples.

weak↑ strong↑ : Pred₀ S → Pred₀ (Maybe S)
weak↑   = M.All.All
strong↑ = M.Any.Any

infixl 4 _↑∘_
_↑∘_ : Pred₀ S → (S → Maybe S) → Pred₀ S
P ↑∘ f = weak↑ P ∘ f

lift↑ = weak↑
pattern ret↑ x = M.All.just x
pattern ret∅ = M.All.nothing

map↑ : P ⊆¹ Q → lift↑ P ⊆¹ lift↑ Q
map↑ = M.All.map

⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Set
⟨ P ⟩ l ⟨ Q ⟩ = P ⊢ Q ↑∘ ⟦ l ⟧

hoare-base :
  ───────────────
  ⟨ P ⟩ [] ⟨ P ⟩
hoare-base = ret↑

hoare-step :
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────────
  ⟨ P ↑∘ ⟦ t ⟧ ⟩ t ∷ l ⟨ Q ⟩
hoare-step {t = t} PlQ {s} Ps↑ with ⟦ t ⟧ s | Ps↑
... | _       | ret↑ Ps = PlQ Ps
... | nothing | ret∅    = ret∅

consequence :
  ∙ P′ ⊢ P   -- ^ weakening the pre-condition
  ∙ Q  ⊢ Q′  -- ^ strengthening the post-condition
  ∙ ⟨ P  ⟩ l ⟨ Q  ⟩
    ───────────────
    ⟨ P′ ⟩ l ⟨ Q′ ⟩
consequence ⊢P Q⊢ PlQ = map↑ Q⊢ ∘ PlQ ∘ ⊢P

-- Utilities for Hoare triples.
weaken : P′ ⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken {l = l} H = consequence {l = l} H id

strengthen : Q ⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen {l = l} H = consequence {l = l} id H

axiom-base⋆ : ⟨ P ↑∘ ⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []} = weaken {P′ = P ↑∘ ⟦ [] ⟧} {l = []} (λ where (ret↑ p) → p) hoare-base
axiom-base⋆ {P = P} {l = t ∷ l} Ps = map↑ id Ps

-- Derived alternative formulation for step, using list concatenation.
hoare-step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ───────────────────
    ⟨ P ⟩ l ++ l′ ⟨ R ⟩
hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR {s} Ps
  rewrite comp {l}{l′} s
  with ⟦ l ⟧ s | PlQ Ps
... | just _  | ret↑ Qs′ = QlR Qs′
... | nothing | ret∅     = ret∅

-- ** Reasoning syntax for Hoare triples.
module HoareReasoning where
  -- Reasoning newtype (for better type inference).
  record ℝ⟨_⟩_⟨_⟩ (P : Assertion) (l : L) (Q : Assertion) : Set where
    constructor mkℝ_
    field begin_ : ⟨ P ⟩ l ⟨ Q ⟩
    infix -2 begin_
  open ℝ⟨_⟩_⟨_⟩ public
  infix  -2 mkℝ_
  infixr -1 _~⟪_⟩_ _~⟨_⟫_ _~⟨_∶-_⟩_ _~⟨_∶-_⟩++_
  infix  0  _∎

  -- weakening syntax
  _~⟪_⟩_ : ∀ P′ → P′ ⊢ P → ℝ⟨ P ⟩ l ⟨ R ⟩ → ℝ⟨ P′ ⟩ l ⟨ R ⟩
  _~⟪_⟩_ {l = l} _ H PlR = mkℝ weaken {l = l} H (begin PlR)

  -- strengthening syntax
  _~⟨_⟫_ : ∀ R′ → R ⊢ R′ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
  _~⟨_⟫_ {l = l} _ H PlR = strengthen {l = l} H PlR

  -- step syntax
  _~⟨_∶-_⟩_ : ∀ P′ t → ℝ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ℝ⟨ P ⟩ l ⟨ R ⟩ → ℝ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  _~⟨_∶-_⟩_ {l = l} {R = R} P′ t H PlR = mkℝ go
    where
      go : P′ ⊢ R ↑∘ ⟦ t ∷ l ⟧
      go {s} P′s with ⟦ t ⟧ s | (begin H) P′s
      ... | just _  | ret↑ Ps′ = (begin PlR) Ps′
      ... | nothing | ret∅     = ret∅

  -- step′ syntax
  _~⟨_∶-_⟩++_ : ∀ P′ → (l : L) → ℝ⟨ P′ ⟩ l ⟨ P ⟩ → ℝ⟨ P ⟩ l′ ⟨ R ⟩ → ℝ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩++ PlR = mkℝ hoare-step′ {l = l} (begin H) (begin PlR)

  _∎ : ∀ P → ℝ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = mkℝ hoare-base {P = p}
