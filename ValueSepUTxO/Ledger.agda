------------------------------------------
-- ** Denotational & operational semantics

module ValueSepUTxO.Ledger where

open import Prelude.Init
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

open import ValueSepUTxO.Maps
open import ValueSepUTxO.UTxO

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

record Denotable (A : Set) : Set where
  field ⟦_⟧ : A → Domain
open Denotable ⦃...⦄ public

instance
  -- we denote a transaction as simply running the transaction based on the transfer operation above
  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ tx utxos =
    if isValidTx tx utxos then just $ (utxos ─ outputRefs tx) ∪ utxoTxS tx
                          else nothing

  -- we denote a ledger as the composition of the denotations of its transactions,
  -- i.e. we run all transactions in sequence
  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      s = just s
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ t ⟧ >=> ⟦ l ⟧

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l ⟧ >=> ⟦ l′ ⟧) x
comp {l = []}    x = refl
comp {l = t ∷ l} x with ⟦ t ⟧ x
... | nothing = refl
... | just s  = comp {l} s
