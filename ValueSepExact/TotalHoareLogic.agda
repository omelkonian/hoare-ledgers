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
open import Prelude.Bifunctor

module ValueSepExact.TotalHoareLogic (Part : Type) ⦃ _ : DecEq Part ⦄ where

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

IsValid : L → S → Type
IsValid l s = ∃ (l , s —→_)

⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Type
⟨ P ⟩ l ⟨ Q ⟩ =
  -- P Unary.∩ IsValid l ⊢ Q ∘ ⟦ l ⟧₀
  P ⊢ IsValid l Unary.∩ Q ∘ ⟦ l ⟧₀

hoare-base :
  ──────────────
  ⟨ P ⟩ [] ⟨ P ⟩
-- hoare-base (Ps , vl) = Ps
hoare-base Ps = (-, base) , Ps

-- hoare-step :
--   ⟨ P ⟩ l ⟨ Q ⟩
--   ──────────────────────────
--   ⟨ P ∘ ⟦ t ⟧₀ ⟩ t ∷ l ⟨ Q ⟩
-- hoare-step {t = t} PlQ {s} (Ps , (_ , step _ vl)) = PlQ (Ps , _ , vl)

hoare-step : let ↓P = P ∘ ⟦ t ⟧₀ in
  ∙ ↓P ⊆¹ IsValidTx t
  ∙ ⟨ P ⟩ l ⟨ Q ⟩
    ──────────────────────────
    ⟨ ↓P ⟩ t ∷ l ⟨ Q ⟩
hoare-step {t = t} P⇒ PlQ {s} Ps =
  let (_ , vl) , Qs′ = PlQ Ps
  in (-, step (P⇒ Ps) vl) , Qs′

consequence :
  ∙ P′ ⊢ P   -- ^ weakening the pre-condition
  ∙ Q  ⊢ Q′  -- ^ strengthening the post-condition
  ∙ ⟨ P  ⟩ l ⟨ Q  ⟩
    ───────────────
    ⟨ P′ ⟩ l ⟨ Q′ ⟩
consequence ⊢P Q⊢ PlQ = map₂ Q⊢ ∘ PlQ ∘ ⊢P

-- Utilities for Hoare triples.
weaken : P′ ⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken {Q = Q} = flip (consequence {Q = Q}) id

strengthen : Q ⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen = consequence id

axiom-base⋆ : let ↓P = P ∘ ⟦ l ⟧₀ in
  ↓P ⊆¹ IsValid l
  ──────────────────────
  ⟨ ↓P ⟩ l ⟨ P ⟩
axiom-base⋆ {P}{[]}    _ = hoare-base {P = P}
axiom-base⋆ {P}{t ∷ l} P⊆ = hoare-step {P = P ∘ ⟦ l ⟧₀} {!P⊆!} (axiom-base⋆ {!P⊆!})
-- axiom-base⋆ {P}{_ ∷ l} P⊆ Ps with P⊆ Ps
-- ... | _ , step vt l→
--   = hoare-step (λ Ps → Ps) (axiom-base⋆ {l = l} λ Ps → {!P⊆ Ps!}) {!!}
  -- in hoare-step (λ Ps → {!!}) (axiom-base⋆ {l = l} λ Ps → {!P⊆!}) ?

-- -- Derived alternative formulation for step, using list concatenation.

-- hoare-step′ :
--   ∙ ⟨ P ⟩ l  ⟨ Q ⟩
--   ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
--     ───────────────────
--     ⟨ P ⟩ l ++ l′ ⟨ R ⟩
-- hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR {s} Ps s→s′ =
--   let _ , s→ , →s′ = oper-comp˘ s→s′
--   in QlR (PlQ Ps s→) →s′

-- -- ** Reasoning syntax for Hoare triples.
-- module HoareReasoning where
--   infix -2 begin_
--   infixr -1 _~⟪_⟩_ _~⟨_⟫_ _~⟨_∶-_⟩_ _~⟨_∶-_⟩++_
--   infix  0  _∎

--   begin_ = id

--   -- weakening syntax
--   _~⟪_⟩_ : ∀ P′ → P′ ⊢ P → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ l ⟨ R ⟩
--   _~⟪_⟩_ {l = l} _ H PlR = weaken {l = l} H PlR

--   -- strengthening syntax
--   _~⟨_⟫_ : ∀ R′ → R ⊢ R′ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
--   _~⟨_⟫_ {l = l} _ H PlR = strengthen {l = l} H PlR

--   -- step syntax
--   _~⟨_∶-_⟩_ : ∀ P′ t → ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
--   _~⟨_∶-_⟩_ {l = l} {R = R} P′ t H PlR Ps (step vt s→) =
--     PlR (H Ps (step vt base)) s→

--   -- step′ syntax
--   _~⟨_∶-_⟩++_ : ∀ P′ → (l : L) → ⟨ P′ ⟩ l ⟨ P ⟩ → ⟨ P ⟩ l′ ⟨ R ⟩ → ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
--   P′ ~⟨ l ∶- H ⟩++ PlR = hoare-step′ {l = l} H PlR

--   _∎ : ∀ P → ⟨ P ⟩ [] ⟨ P ⟩
--   p ∎ = hoare-base {P = p}
