----------------------------------------------
-- ** Basic definition for UTxO-based ledgers.

module ValueSepUTxO.UTxO where

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Functor
open import Prelude.Applicative

open import ValueSepUTxO.Maps

Value   = ℕ
HashId  = ℕ
Address = HashId
postulate _♯ : ∀ {A : Set ℓ} → A → HashId

DATA = ℕ -- T0D0: more realistic data for redeemers

record TxOutputRef : Set where
  constructor _indexed-at_
  field txId  : HashId
        index : ℕ
open TxOutputRef public
unquoteDecl DecEq-TxOR = DERIVE DecEq [ quote TxOutputRef , DecEq-TxOR ]

record TxOutput : Set where
  constructor _at_
  field value    : Value
        address  : Address
open TxOutput public
unquoteDecl DecEq-TxO = DERIVE DecEq [ quote TxOutput , DecEq-TxO ]

record InputInfo : Set where
  field outputRef     : TxOutputRef
        validatorHash : HashId
        redeemerHash  : HashId

record TxInfo : Set where
  field inputs  : List InputInfo
        outputs : List TxOutput
        forge   : Value

record TxInput : Set where
  field outputRef : TxOutputRef
        validator : TxInfo → DATA → Bool
        redeemer  : DATA
open TxInput public

mkInputInfo : TxInput → InputInfo
mkInputInfo i = record
  { outputRef     = i .outputRef
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

-- The state of a ledger maps output references locked by a validator to a value.

S : Set
S = Map⟨ TxOutputRef ↦ TxOutput ⟩

outputRefs : Tx → List TxOutputRef
outputRefs = map outputRef ∘ inputs

mkUtxo : ∀ {out} tx → out L.Mem.∈ outputs tx → TxOutputRef × TxOutput
mkUtxo {out} tx out∈ = (tx ♯) indexed-at toℕ (L.Any.index out∈)
                     , out

utxoTx : Tx → List (TxOutputRef × TxOutput)
utxoTx tx = L.Mem.mapWith∈ (tx .outputs) (mkUtxo tx)

utxoTxS : Tx → S
utxoTxS = mkMap ∘ utxoTx

getSpentOutput : S → TxInput → Maybe TxOutput
getSpentOutput s i = s (i .outputRef)

∑ : ∀ {A : Set} → List A → (A → Value) → Value
∑ xs f = ∑ℕ (map f xs)

∑M : ∀ {A : Set} → List (Maybe A) → (A → Value) → Maybe Value
∑M xs f = (flip ∑ f) <$> seqM xs
  where
    -- if one fails everything fails
    seqM : ∀ {A : Set} → List (Maybe A) → Maybe (List A)
    seqM []       = just []
    seqM (x ∷ xs) = ⦇ x ∷ seqM xs ⦈

record IsValidTx (tx : Tx) (utxos : S) : Set where
  field
    validOutputRefs :
      All (_∈ᵈ utxos) (outputRefs tx)

    preservesValues :
      M.Any.Any (λ q → tx .forge + q ≡ ∑ (tx .outputs) value)
                (∑M (map (getSpentOutput utxos) (tx .inputs)) value)

    noDoubleSpending :
      Unique (outputRefs tx)

    allInputsValidate :
      All (λ i → T (validator i (mkTxInfo tx) (i .redeemer)))
          (tx .inputs)

    validateValidHashes :
      All (λ i → M.Any.Any (λ o → o .address ≡ i .validator ♯) (getSpentOutput utxos i))
          (tx .inputs)

open IsValidTx public

isValidTx? : ∀ tx s → Dec (IsValidTx tx s)
isValidTx? tx utxos
  with all? (_∈ᵈ? utxos) (outputRefs tx)
... | no ¬p = no (¬p ∘ validOutputRefs )
... | yes p₁
  with M.Any.dec (λ q → tx .forge + q ≟ ∑ (tx .outputs) value)
                 (∑M (map (getSpentOutput utxos) (tx .inputs)) value)
... | no ¬p = no (¬p ∘ preservesValues)
... | yes p₂
  with unique? (outputRefs tx)
... | no ¬p = no (¬p ∘ noDoubleSpending)
... | yes p₃
  with all? (λ i → T? (validator i (mkTxInfo tx) (i .redeemer)))
            (tx .inputs)
... | no ¬p = no (¬p ∘ allInputsValidate)
... | yes p₄
  with all? (λ i → M.Any.dec (λ o → o .address ≟ i .validator ♯) (getSpentOutput utxos i))
            (tx .inputs)
... | no ¬p = no (¬p ∘ validateValidHashes)
... | yes p₅ = yes record {validOutputRefs = p₁; preservesValues = p₂; noDoubleSpending = p₃; allInputsValidate = p₄; validateValidHashes = p₅}

isValidTx : Tx → S → Bool
isValidTx tx s = ⌊ isValidTx? tx s ⌋
