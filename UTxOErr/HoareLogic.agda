-------------------------
-- ** Axiomatic semantics

module UTxOErr.HoareLogic where

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

open import UTxOErr.Maps
open import UTxOErr.UTxO
open import UTxOErr.Ledger

-- ** Shallow embedding of logic formulas/propositions.
Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

private variable K V₁ V₂ : Type

emp : Assertion
emp m = ∀ k → k ∉ᵈ m

_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ⊎ s₂ ⟩≡ s × P s₁ × Q s₂

_↦_ : TxOutputRef → TxOutput → Assertion
or ↦ o = _[ or ↦ o ]∅

infixr 10 _∗_
infix  11 _↦_

-- ** Hoare triples.
weak↑ strong↑ : Pred₀ S → Pred₀ (Maybe S)
weak↑   = M.All.All
strong↑ = M.Any.Any

infixl 4 _↑∘_
_↑∘_ : Pred₀ S → (S → Maybe S) → Pred₀ S
P ↑∘ f = strong↑ P ∘ f

lift↑ = strong↑
pattern ret↑ x = M.Any.just x

map↑ : P ⊆¹ Q → lift↑ P ⊆¹ lift↑ Q
map↑ = M.Any.map

⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Type
⟨ P ⟩ l ⟨ Q ⟩ = P ⊢ Q ↑∘ ⟦ l ⟧

hoare-base :
  ──────────────
  ⟨ P ⟩ [] ⟨ P ⟩
hoare-base = ret↑

module _ (f : S → Maybe S) where
  lift∘>>= : ∀ {ms}
    → lift↑ (lift↑ P ∘ f) ms
    → lift↑ P (ms >>= f)
  lift∘>>= (ret↑ p) = p

  lift∘>>=˘ : ∀ {ms : Maybe S}
    → lift↑ P (ms >>= f)
    → lift↑ (lift↑ P ∘ f) ms
  lift∘>>=˘ {ms = just s} p = ret↑ p

  lift∘=<<  = lift∘>>=
  lift∘=<<˘ = lift∘>>=˘

module _ (f g : S → Maybe S) where
  lift²∘>=> : (P ↑∘ g ↑∘ f) ⊢ (P ↑∘ (f >=> g))
  lift²∘>=> = lift∘=<< _

  lift²∘>=>˘ : (P ↑∘ (f >=> g)) ⊢ (P ↑∘ g ↑∘ f)
  lift²∘>=>˘ = lift∘=<<˘ _

hoare-step :
  ⟨ P ⟩ l ⟨ Q ⟩
  ──────────────────────────
  ⟨ P ↑∘ ⟦ t ⟧ ⟩ t ∷ l ⟨ Q ⟩
hoare-step {t = t} PlQ {s} = lift²∘>=> ⟦ t ⟧ _ {x = s} ∘ map↑ PlQ

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
axiom-base⋆ {P = P} {l = t ∷ l} = map↑ id

-- Derived alternative formulation for step, using list concatenation.

hoare-step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ───────────────────
    ⟨ P ⟩ l ++ l′ ⟨ R ⟩
hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR
--   {s} Ps rewrite comp {l}{l′} s
--   with ⟦ l ⟧ s | PlQ Ps
-- ... | .(just _) | ret↑ Qs′ = QlR Qs′
  = begin
    P
  ⊢⟨ PlQ  ⟩
    Q ↑∘ ⟦ l ⟧
  ⊢⟨ map↑ QlR ⟩
    R ↑∘ ⟦ l′ ⟧ ↑∘ ⟦ l ⟧
  ⊢⟨ lift²∘>=> ⟦ l ⟧ ⟦ l′ ⟧  ⟩
    R ↑∘ (⟦ l ⟧ >=> ⟦ l′ ⟧)
  ≗˘⟨ cong (lift↑ R) ∘ comp {l}{l′} ⟩
    R ↑∘ ⟦ l ++ l′ ⟧
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
      ... | just _ | ret↑ Ps′ = (begin PlR) Ps′

  -- step′ syntax
  _~⟨_∶-_⟩++_ : ∀ P′ → (l : L) → ℝ⟨ P′ ⟩ l ⟨ P ⟩ → ℝ⟨ P ⟩ l′ ⟨ R ⟩ → ℝ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩++ PlR = mkℝ hoare-step′ {l = l} (begin H) (begin PlR)

  _∎ : ∀ P → ℝ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = mkℝ hoare-base {P = p}
