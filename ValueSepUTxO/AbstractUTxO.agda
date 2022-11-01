----------------------------------------------
-- ** Abstract definition for UTxO-based ledgers.

module ValueSepUTxO.AbstractUTxO where

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.FromList
open import Prelude.Ord
open import Prelude.Semigroup
open import Prelude.Monoid

open import ValueSepUTxO.AbstractMaps
instance
  Sℕ  = Semigroup-ℕ-+
  Sℕ⁺ = SemigroupLaws-ℕ-+
  Mℕ  = Monoid-ℕ-+
  Mℕ⁺ = MonoidLaws-ℕ-+

Value   = ℕ
HashId  = ℕ
Address = HashId
postulate _♯ : ∀ {A : Set ℓ} → A → HashId

DATA = ℕ -- T0D0: more realistic data for redeemers

record TxOutput : Set where
  constructor _at_
  field value   : Value
        address : Address
open TxOutput public
unquoteDecl DecEq-TxO = DERIVE DecEq [ quote TxOutput , DecEq-TxO ]

TxOutputRef : Set
TxOutputRef = HashId

record InputInfo : Set where
  field outputRef     : TxOutputRef
        validatorHash : HashId
        redeemerHash  : HashId

record TxInfo : Set where
  field inputs  : List InputInfo
        outputs : List TxOutput
        forge   : Value

record TxInput : Set where
  field outputRef : TxOutput
        validator : TxInfo → DATA → Bool
        redeemer  : DATA
open TxInput public

mkInputInfo : TxInput → InputInfo
mkInputInfo i = record
  { outputRef     = i .outputRef ♯
  ; validatorHash = i .validator ♯
  ; redeemerHash  = i .redeemer ♯ }

record Tx : Set where
  field
    inputs  : List TxInput
    outputs : List TxOutput
    forge   : Value
open Tx public

mkTxInfo : Tx → TxInfo
mkTxInfo tx = record
  { inputs  = mkInputInfo <$> tx .inputs
  ; outputs = tx .outputs
  ; forge   = tx .forge }

-- A ledger is a list of transactions.
L = List Tx

-- The state of a ledger maps addresses to a value.

S : Set
S = Map⟨ Address ↦ Value ⟩

outputRefs : Tx → List TxOutput
outputRefs = map outputRef ∘ inputs

utxoTx : Tx → S
utxoTx = fromList ∘ map (λ txo → txo .address , txo .value) ∘ outputRefs

∑ : ∀ {A : Set} → List A → (A → Value) → Value
∑ xs f = ∑ℕ (map f xs)

record IsValidTx (tx : Tx) (utxos : S) : Set where
  field
    validOutputRefs :
      utxoTx tx ≤ᵐ utxos

    preservesValues :
      tx .forge + ∑ (tx .inputs) (value ∘ outputRef) ≡ ∑ (tx .outputs) value

    noDoubleSpending :
      Unique (outputRefs tx)

    allInputsValidate :
      All (λ i → T (validator i (mkTxInfo tx) (i .redeemer))) (tx .inputs)

    validateValidHashes :
      All (λ i → i .outputRef .address ≡ i .validator ♯) (tx .inputs)

open IsValidTx public

isValidTx? : ∀ tx s → Dec (IsValidTx tx s)
isValidTx? tx utxos
  with dec
... | no ¬p = no (¬p ∘ validOutputRefs)
... | yes p₁
  with dec
... | no ¬p = no (¬p ∘ preservesValues)
... | yes p₂
  with dec
... | no ¬p = no (¬p ∘ noDoubleSpending)
... | yes p₃
  with dec
... | no ¬p = no (¬p ∘ allInputsValidate)
... | yes p₄
  with dec
... | no ¬p = no (¬p ∘ validateValidHashes)
... | yes p₅ = yes record { validOutputRefs = p₁; preservesValues = p₂; noDoubleSpending = p₃
                          ; allInputsValidate = p₄; validateValidHashes = p₅ }

isValidTx : Tx → S → Bool
isValidTx tx s = ⌊ isValidTx? tx s ⌋
