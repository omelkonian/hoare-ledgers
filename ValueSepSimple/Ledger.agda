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

module ValueSepSimple.Ledger
  (Part : Type) -- a fixed set of participants
  ⦃ _ : DecEq Part ⦄
  where

variable
  A B C D : Part
  v v′ v″ : ℕ

open import ValueSepSimple.Maps

-- The state of a ledger is a collection of participants, along with their balance.
S : Type
S = Map⟨ Part ↦ℕ⟩

-- A transaction is transferring money from one participant to another.
record Tx : Type where
  constructor _—→⟨_⟩_
  field
    sender   : Part
    value    : ℕ
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
-- i.e. a function from the current state to the updated one that may produce an error.
Domain = S → Maybe S

record Denotable (A : Type) : Type where
  field ⟦_⟧ : A → Domain
open Denotable ⦃...⦄ public

-- pure fragment without error-handling
Domain₀ = S → S

record Denotable₀ (A : Type) : Type where
  field ⟦_⟧₀ : A → Domain₀
open Denotable₀ ⦃...⦄ public

IsValidTx : Tx → S → Type
IsValidTx (A —→⟨ v ⟩ _) s = v ≤ s A

data IsValidTx′ : Tx → S → Type where

  mkValid :

    v ≤ s A
    ──────────────────────────
    IsValidTx′ (A —→⟨ v ⟩ B) s

isValidTx? : Decidable² IsValidTx
isValidTx? = dec²

isValidTx : Tx → S → Bool
isValidTx t s = ⌊ isValidTx? t s ⌋

-- Express the action of tranferring values between keys in a map.
-- NB: a transaction goes through only when:
--   1. both participants are present in the domain
--   2. the sender holds sufficient funds
instance
  -- we denote a transaction as the map transformation that implements the transfer
  ⟦Tx⟧₀ : Denotable₀ Tx
  ⟦Tx⟧₀ .⟦_⟧₀ (A —→⟨ v ⟩ B) s = s [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]

  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ t s = M.when (isValidTx t s) (⟦ t ⟧₀ s)

  -- we denote a ledger as the composition of the denotations of its transactions,
  -- i.e. we run all transactions in sequence
  ⟦L⟧₀ : Denotable₀ L
  ⟦L⟧₀ .⟦_⟧₀ []      = id
  ⟦L⟧₀ .⟦_⟧₀ (t ∷ l) = ⟦ l ⟧₀ ∘ ⟦ t ⟧₀

  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      s = just s
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ t ⟧ >=> ⟦ l ⟧

comp₀ : ∀ x → ⟦ l ++ l′ ⟧₀ x ≡ (⟦ l′ ⟧₀ ∘ ⟦ l ⟧₀) x
comp₀ {l = []}    _ = refl
comp₀ {l = t ∷ l} x = comp₀ {l} (⟦ t ⟧₀ x)

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l ⟧ >=> ⟦ l′ ⟧) x
comp {l = []}    x = refl
comp {l = t ∷ l} x with ⟦ t ⟧ x
... | nothing = refl
... | just s  = comp {l} s

-- Executing transactions never introduces new keys in the resulting map out-of-thin-air.
-- ** Operational semantics
-- We model configurations of the transition system as pairs of a ledger and its current state.

infix 0 _—→_
data _—→_ : L × S → S → Type where

  base :
    ────────────
    ε , s —→ s

  step : let t = A —→⟨ v ⟩ B in

    ∙ v ≤ s A
    ∙ l , ⟦ t ⟧₀ s —→ s′
      ──────────────────
      t ∷ l , s —→ s′

oper-comp :
  ∙ l       , s  —→ s′
  ∙ l′      , s′ —→ s″
    ────────────────────
    l ++ l′ , s  —→ s″
oper-comp {l = []}    base                   s′→s″ = s′→s″
oper-comp {l = _ ∷ _} (step v≤ s→s′) s′→s″ = step v≤ (oper-comp s→s′ s′→s″)

-- ** Relating denotational and operational semantics.
denot⇒oper :
  ⟦ l ⟧ s ≡ just s′
  ─────────────────
  l , s —→ s′
denot⇒oper {l = []} refl = base
denot⇒oper {l = A —→⟨ v ⟩ B ∷ l}{s} l≡
  with yes v≤ ← v ≤? s A
  = step v≤ (denot⇒oper l≡)

oper⇒denot :
  l , s —→ s′
  ─────────────────
  ⟦ l ⟧ s ≡ just s′
oper⇒denot {l = .[]} base = refl
oper⇒denot {l = A —→⟨ v ⟩ B ∷ _}{s} (step v≤ p)
  rewrite dec-yes (v ≤? s A) v≤ .proj₂
  = oper⇒denot p

denot⇔oper :
  ⟦ l ⟧ s ≡ just s′
  ═════════════════
  l , s —→ s′
denot⇔oper = denot⇒oper , oper⇒denot
