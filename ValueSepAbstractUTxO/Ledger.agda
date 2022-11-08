------------------------------------------
-- ** Denotational & operational semantics

module ValueSepAbstractUTxO.Ledger where

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
open import Prelude.Membership

open import Prelude.Bags
open import ValueSepAbstractUTxO.UTxO

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

instance
  -- we denote a transaction as simply running the transaction based on the transfer operation above
  ⟦Tx⟧₀ : Denotable₀ Tx
  ⟦Tx⟧₀ .⟦_⟧₀ tx utxos = (utxos ─ stxoTx tx) ∪ utxoTx tx

  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ tx s = M.when (isValidTx tx s) (⟦ tx ⟧₀ s)

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


-- ** Operational semantics

infix 0 _—→_
data _—→_ : L × S → S → Type where

  base :
    ──────────
    ε , s —→ s

  step :

    ∙ IsValidTx t s
    ∙ l , (s ─ stxoTx t ∪ utxoTx t) —→ s′
      ───────────────────────────────────
      t ∷ l , s —→ s′

oper-comp :
  ∙ l       , s  —→ s′
  ∙ l′      , s′ —→ s″
    ──────────────────
    l ++ l′ , s  —→ s″
oper-comp {l = []}    base              s′→s″ = s′→s″
oper-comp {l = _ ∷ _} (step valid s→s′) s′→s″ = step valid (oper-comp s→s′ s′→s″)

-- ** Relating denotational and operational semantics.
denot⇒oper :
  ⟦ l ⟧ s ≡ just s′
  ─────────────────
  l , s —→ s′
denot⇒oper {l = []} refl = base
denot⇒oper {l = t ∷ l}{s} l≡
  with yes valid ← isValidTx? t s
  = step valid (denot⇒oper l≡)

oper⇒denot :
  l , s —→ s′
  ─────────────────
  ⟦ l ⟧ s ≡ just s′
oper⇒denot {l = .[]} base = refl
oper⇒denot {l = t ∷ _}{s} (step valid p)
  rewrite dec-yes (isValidTx? t s) valid .proj₂
  = oper⇒denot p

denot⇔oper :
  ⟦ l ⟧ s ≡ just s′
  ═════════════════
  l , s —→ s′
denot⇔oper = denot⇒oper , oper⇒denot
