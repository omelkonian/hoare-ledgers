------------------------------------------
-- ** Denotational & operational semantics

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Functor
open import Prelude.InferenceRules
open import Prelude.Apartness
open import Prelude.Monad

module ValueSepInt.Ledger
  (Part : Type) -- a fixed set of participants
  ⦃ _ : DecEq Part ⦄
  where

open import ValueSepInt.Maps

V = ℤ
instance
  Sℤ  = Semigroup-ℤ-+
  Sℤ⁺ = SemigroupLaws-ℤ-+
  Mℤ  = Monoid-ℤ-+
  Mℤ⁺ = MonoidLaws-ℤ-+

variable
  A B C D : Part
  v v′ v″ : V

-- The state of a ledger is a collection of participants, along with their balance.
S : Type
S = Map⟨ Part ↦ V ⟩

-- A transaction is transferring money from one participant to another.
record Tx : Type where
  constructor _—→⟨_⟩_
  field
    sender   : Part
    value    : V
    receiver : Part
open Tx public
unquoteDecl DecEq-Tx = DERIVE DecEq [ quote Tx , DecEq-Tx ]

-- A ledger is a list of transactions.
L = List Tx

variable
  s s′ s″ s₁ s₁′ s₁″ s₂ s₂′ s₂″ s₃ s₃′ s₃″ s₂₃ s₂₃′ s₂₃″ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

  ms ms′ ms″ : Maybe S
  mls mls′ mls″ : Maybe (L × S)

-- ** Denotational semantics

-- The meaning of a transaction or a whole ledger will be denoted by state transformers,
-- i.e. a function from the current state to the updated one.
Domain = S → S

record Denotable (A : Type) : Type where
  field ⟦_⟧ : A → Domain
open Denotable ⦃...⦄ public

-- Express the action of tranferring values between keys in a map.
-- NB: a transaction goes through only when:
--   1. both participants are present in the domain
--   2. the sender holds sufficient funds
instance
  -- we denote a transaction as the map transformation that implements the transfer
  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ (A —→⟨ v ⟩ B) s = s [ A ↝ (Integer._- v) ] [ B ↝ (Integer._+ v) ]

  -- we denote a ledger as the composition of the denotations of its transactions,
  -- i.e. we run all transactions in sequence
  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      = id
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ l ⟧ ∘ ⟦ t ⟧

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l′ ⟧ ∘ ⟦ l ⟧) x
comp {l = []}    _ = refl
comp {l = t ∷ l} x = comp {l} (⟦ t ⟧ x)

-- Executing transactions never introduces new keys in the resulting map out-of-thin-air.
-- ** Operational semantics
-- We model configurations of the transition system as pairs of a ledger and its current state.

infix 0 _—→_
data _—→_ : L × S → S → Type where

  base :
    ────────────
    ε , s —→ s

  step : let t = A —→⟨ v ⟩ B in

    ∙ l , ⟦ t ⟧ s —→ s′
      ─────────────────
      t ∷ l , s —→ s′

oper-comp :
  ∙ l       , s  —→ s′
  ∙ l′      , s′ —→ s″
    ──────────────────
    l ++ l′ , s  —→ s″
oper-comp {l = []}    base        s′→s″ = s′→s″
oper-comp {l = _ ∷ _} (step s→s′) s′→s″ = step (oper-comp s→s′ s′→s″)

-- ** Relating denotational and operational semantics.
denot⇒oper :
  ⟦ l ⟧ s ≡ s′
  ────────────
  l , s —→ s′
denot⇒oper {l = []} refl = base
denot⇒oper {l = A —→⟨ v ⟩ B ∷ l}{s} l≡ = step (denot⇒oper l≡)

oper⇒denot :
  l , s —→ s′
  ────────────
  ⟦ l ⟧ s ≡ s′
oper⇒denot {l = .[]} base = refl
oper⇒denot {l = A —→⟨ v ⟩ B ∷ _}{s} (step p) = oper⇒denot p

denot⇔oper :
  ⟦ l ⟧ s ≡ s′
  ════════════
  l , s —→ s′
denot⇔oper = denot⇒oper , oper⇒denot
