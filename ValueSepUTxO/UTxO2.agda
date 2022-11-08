----------------------------------------------
-- ** Basic definition for UTxO-based ledgers.
-- Simpler formulation without hashes.
----------------------------------------------
-- ** Basic definition for UTxO-based ledgers.
-- Simpler formulation without hashes.

module ValueSepUTxO.UTxO2 where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Functor
open import Prelude.Applicative

open import ValueSepUTxO.Maps

HashId  = ℕ
Address = HashId
postulate _♯ : ∀ {A : Type ℓ} → A → HashId

DATA = ℕ -- T0D0: more realistic data for redeemers
record Value : Type where
  constructor _at_
  field value     : ℕ
        validator : DATA → Bool
open Value public
-- unquoteDecl DecEq-Value = DERIVE DecEq [ quote Value , DecEq-Value ]

record TxRef : Type where
  constructor _indexed-at_
  field txId  : HashId
        index : ℕ
open TxRef public
unquoteDecl DecEq-TxOR = DERIVE DecEq [ quote TxRef , DecEq-TxOR ]

record TxInput : Type where
  field ref : TxRef
        redeemer  : DATA
open TxInput public

record Tx : Type where
  field
    inputs  : List TxInput
    outputs : List Value
    forge   : ℕ
open Tx public

-- A ledger is a list of transactions.
L = List Tx

-- The state of a ledger maps output references locked by a validator to a value.

S : Type
S = Map⟨ TxRef ↦ Value ⟩

refs : Tx → List TxRef
refs = map ref ∘ inputs

mkUtxo : ∀ {out} tx → out L.Mem.∈ outputs tx → TxRef × Value
mkUtxo {out} tx out∈ = (tx ♯) indexed-at toℕ (L.Any.index out∈)
                     , out

utxoTx : Tx → List (TxRef × Value)
utxoTx tx = L.Mem.mapWith∈ (tx .outputs) (mkUtxo tx)

utxoTxS : Tx → S
utxoTxS = mkMap ∘ utxoTx

getSpentOutput : S → TxInput → Maybe Value
getSpentOutput s i = s (i .ref)

∑ : ∀ {A : Type} → List A → (A → ℕ) → ℕ
∑ xs f = ∑ℕ (map f xs)

∑M : ∀ {A : Type} → List (Maybe A) → (A → ℕ) → Maybe ℕ
∑M xs f = (flip ∑ f) <$> seqM xs
  where
    -- if one fails everything fails
    seqM : ∀ {A : Type} → List (Maybe A) → Maybe (List A)
    seqM []       = just []
    seqM (x ∷ xs) = ⦇ x ∷ seqM xs ⦈

record IsValidTx (tx : Tx) (utxos : S) : Type where
  field
    validRefs :
      All (_∈ᵈ utxos) (refs tx)

    preservesValues :
      M.Any.Any (λ q → tx .forge + q ≡ ∑ (tx .outputs) value)
                (∑M (map (getSpentOutput utxos) (tx .inputs)) value)

    noDoubleSpending :
      Unique (refs tx)

    allInputsValidate :
      All (λ i → M.Any.Any (λ o → T $ o .validator (i .redeemer))
                           (getSpentOutput utxos i))
          (tx .inputs)

open IsValidTx public

isValidTx? : ∀ tx s → Dec (IsValidTx tx s)
isValidTx? tx utxos
  with all? (_∈ᵈ? utxos) (refs tx)
... | no ¬p = no (¬p ∘ validRefs )
... | yes p₁
  with M.Any.dec (λ q → tx .forge + q ≟ ∑ (tx .outputs) value)
                 (∑M (map (getSpentOutput utxos) (tx .inputs)) value)
... | no ¬p = no (¬p ∘ preservesValues)
... | yes p₂
  with unique? (refs tx)
... | no ¬p = no (¬p ∘ noDoubleSpending)
... | yes p₃
  with all? (λ i → M.Any.dec (λ o → T? $ o .validator (i .redeemer))
                             (getSpentOutput utxos i))
            (tx .inputs)
... | no ¬p = no (¬p ∘ allInputsValidate)
... | yes p₄ = yes record {validRefs = p₁; preservesValues = p₂; noDoubleSpending = p₃; allInputsValidate = p₄}

isValidTx : Tx → S → Bool
isValidTx tx s = ⌊ isValidTx? tx s ⌋
