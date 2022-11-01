----------------------------------------------
-- ** Abstract definition for UTxO-based ledgers.

module ValueSepUTxO.AbstractUTxO where

open import Prelude.Init; open SetAsType
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

-- open import ValueSepUTxO.AbstractMaps
open import Prelude.Bags
instance
  Sℕ  = Semigroup-ℕ-+; Sℕ⁺ = SemigroupLaws-ℕ-+
  Mℕ  = Monoid-ℕ-+;    Mℕ⁺ = MonoidLaws-ℕ-+

Value   = ℕ
HashId  = ℕ
Address = HashId
postulate _♯ : ∀ {A : Type ℓ} → A → HashId

DATA = ℕ -- T0D0: more realistic data for redeemers

record TxOutput : Type where
  constructor _at_
  field value   : Value
        address : Address
open TxOutput public
unquoteDecl DecEq-TxO = DERIVE DecEq [ quote TxOutput , DecEq-TxO ]

TxOutputRef : Type
TxOutputRef = HashId

record InputInfo : Type where
  field outputRef     : TxOutputRef
        validatorHash : HashId
        redeemerHash  : HashId

record TxInfo : Type where
  field inputs  : List InputInfo
        outputs : List TxOutput
        forge   : Value

record TxInput : Type where
  field outputRef : TxOutput
        validator : TxInfo → DATA → Bool
        redeemer  : DATA
open TxInput public

mkInputInfo : TxInput → InputInfo
mkInputInfo i = record
  { outputRef     = i .outputRef ♯
  ; validatorHash = i .validator ♯
  ; redeemerHash  = i .redeemer ♯ }

record Tx : Type where
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

S : Type
S = Bag⟨ Address × Value ⟩

instance
  FromList-S : FromList TxOutput S
  FromList-S .fromList = fromList ∘ map (λ txo → txo .address , txo .value)

outputRefs : Tx → List TxOutput
outputRefs = map outputRef ∘ inputs

stxoTx utxoTx : Tx → S
stxoTx = fromList ∘ outputRefs
utxoTx = fromList ∘ outputs

∑ : ∀ {A : Type} → List A → (A → Value) → Value
∑ xs f = ∑ℕ (map f xs)

record IsValidTx (tx : Tx) (utxos : S) : Type where
  field
    validOutputRefs :
      stxoTx tx ⊆ˢ utxos

    preservesValues :
      tx .forge + ∑ (tx .inputs) (value ∘ outputRef) ≡ ∑ (tx .outputs) value

    -- noDoubleSpending :
    --   Unique (outputRefs tx)

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
--   with dec
-- ... | no ¬p = no (¬p ∘ noDoubleSpending)
-- ... | yes p₃
  with dec
... | no ¬p = no (¬p ∘ allInputsValidate)
... | yes p₄
  with dec
... | no ¬p = no (¬p ∘ validateValidHashes)
... | yes p₅ = yes record { validOutputRefs = p₁; preservesValues = p₂
                          ; allInputsValidate = p₄; validateValidHashes = p₅ }

isValidTx : Tx → S → Bool
isValidTx tx s = ⌊ isValidTx? tx s ⌋
