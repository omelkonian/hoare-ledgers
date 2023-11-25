------------------------------------------
-- ** Denotational & operational semantics

module EUTxOErr.Ledger where

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

open import EUTxOErr.EUTxO

variable
  s s′ s″ s₁ s₁′ s₁″ s₂ s₂′ s₂″ s₃ s₃′ s₃″ s₂₃ s₂₃′ s₂₃″ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

  ms ms′ ms″ : Maybe S
  mls mls′ mls″ : Maybe (L × S)

-- ** Denotational semantics

open import Common.Denotational public

instance
  ⟦Tx⟧₀ : Denote₀ Tx S
  ⟦Tx⟧₀ .⟦_⟧ tx utxos = (utxos ─ᵏˢ outputRefs tx) ∪ utxoTx tx

  ⟦Tx⟧ : Denoteₑ Tx S
  ⟦Tx⟧ .⟦_⟧ tx s = M.when (isValidTx tx s) (⟦ tx ⟧₀ s)

-- valid ledgers w.r.t. a given initial state
data VL : S → L → Type where

  [] :
    ───────
    VL s []

  _⊣_∷_ : ∀ tx →
    ∙ IsValidTx tx s
    ∙ VL (⟦ tx ⟧₀ s) l
      ────────────────
      VL s (tx ∷ l)

infixr 5 _⊣_∷_

VL⇒Resolved : VL s l → All Resolved l
VL⇒Resolved [] = []
VL⇒Resolved (tx ⊣ p ∷ l) = resolved p ∷ VL⇒Resolved l

-- ** Operational semantics

infix 0 _—→_
data _—→_ : L × S → S → Type where

  base :
    ───────────
    [] , s —→ s

  step :
    ∙ IsValidTx t s
    ∙ l , ⟦ t ⟧₀ s —→ s′
      ──────────────────
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
