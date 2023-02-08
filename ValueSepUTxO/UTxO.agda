----------------------------------------------
-- ** Abstract definition for UTxO-based ledgers.

module ValueSepUTxO.UTxO where

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.FromList; open import Prelude.ToList
open import Prelude.Ord
open import Prelude.Semigroup
open import Prelude.Monoid

open import Prelude.Bags
instance
  Sℕ  = Semigroup-ℕ-+; Sℕ⁺ = SemigroupLaws-ℕ-+
  Mℕ  = Monoid-ℕ-+;    Mℕ⁺ = MonoidLaws-ℕ-+

open import Common public
TxOutputRef = TxOutput
open CommonInfo TxOutputRef public

-- The state of a ledger maps addresses to a value.

S : Type
S = Bag⟨ TxOutput ⟩

stxoTx utxoTx : Tx → S
stxoTx = fromList ∘ outputRefs
utxoTx = fromList ∘ outputs

resolved : ∀ tx → Resolved tx
resolved _ {r} _ = r

record IsValidTx (tx : Tx) (utxos : S) : Type where
  field
    validOutputRefs :
      stxoTx tx ⊆ˢ utxos

    preservesValues :
      tx .forge + ∑ (tx .inputs) (value ∘ outputRef) ≡ ∑ (tx .outputs) value

  txInfo = mkTxInfo tx (resolved tx)

  field

    allInputsValidate :
      All (λ i → T (i .validator txInfo (i .redeemer)))
          (tx .inputs)

    validateValidHashes :
      All (λ i → i .outputRef .address ≡ i .validator ♯)
          (tx .inputs)

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
