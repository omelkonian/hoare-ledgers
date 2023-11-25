----------------------------------------------
-- ** Basic definition for EUTxO-based ledgers.

module EUTxOErr.EUTxO where

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.Maybes
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Lists hiding (_⁉_; _‼_; map↦)
open import Prelude.Lists.Dec
open import Prelude.Lists.WithK
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.FromList
open import Prelude.Membership using (_∈?_; _∉?_)
open import Prelude.Irrelevance
open import Prelude.Apartness
open import Prelude.Allable hiding (All)

open import Common.Utils public
open import Common.Hash  public
open import Common.Data  public
open import Common.Maps  public
  hiding (_⊣_)

Value   = ℕ
Address = HashId

-- Transaction context, identical to the type of transactions except where
-- validators, redeemers, and datums have been replaced with hashes.
record OutputInfo : Type where
  constructor ⦉_⦊_at_
  field datumHash : DATA
        value     : Value
        address   : Address
unquoteDecl DecEq-OutputInfo = DERIVE DecEq [ quote OutputInfo , DecEq-OutputInfo ]
pattern _at_ x y = ⦉ "" ⦊ x at y

record InputInfo : Type where
  field outputRef     : OutputInfo
        -- NB: the actual implementation also keeps references here
        validatorHash : HashId
        redeemerHash  : HashId
unquoteDecl DecEq-InputInfo = DERIVE DecEq [ quote InputInfo , DecEq-InputInfo ]

record TxInfo : Type where
  field inputs    : List InputInfo
        outputs   : List OutputInfo
        forge     : Value
unquoteDecl DecEq-TxInfo = DERIVE DecEq [ quote TxInfo , DecEq-TxInfo ]
--

record TxOutput : Type where
  constructor ⦉_⦊_at_
  field datum    : DATA
        value    : Value
        address  : Address
open TxOutput public
unquoteDecl DecEq-TxO = DERIVE DecEq [ quote TxOutput , DecEq-TxO ]
pattern _at_ x y = ⦉ "" ⦊ x at y

record TxOutputRef : Type where
  constructor _indexed-at_
  field txId  : HashId
        index : ℕ
open TxOutputRef public
unquoteDecl DecEq-TxOR = DERIVE DecEq [ quote TxOutputRef , DecEq-TxOR ]

Validator
  = HashId -- ^ self-reference to script's own hash
  → TxInfo -- ^ context
  → DATA   -- ^ redeemer
  → DATA   -- ^ datum
  → Bool

call : Validator → TxInfo → DATA → DATA → Bool
call f = f (f ♯)

record TxInput : Type where
  field outputRef : TxOutputRef
        validator : Validator
        redeemer  : DATA
open TxInput public

record Tx : Type where
  field inputs  : List TxInput
        outputs : List TxOutput
        forge   : Value
open Tx public

-- A ledger is a list of transactions.
L = List Tx

-- Auxiliary definitions.

outputRefs : Tx → List TxOutputRef
outputRefs = map outputRef ∘ inputs

Resolved : Pred₀ Tx
Resolved tx = All (const TxOutput) (outputRefs tx)

ResolvedL = Σ L (All Resolved)

ResolvedInput  = TxInput × TxOutput
ResolvedInputs = List ResolvedInput

resolveInputs : ∀ tx → Resolved tx → ResolvedInputs
resolveInputs tx resolvedTx = mapWith∈ (tx .inputs) λ {i} i∈ →
  i , L.All.lookup resolvedTx (∈-map⁺ outputRef i∈)

resolved∈⁻ : ∀ {io} tx → (resolvedTx : Resolved tx)
  → io ∈ resolveInputs tx resolvedTx
  → io .proj₁ ∈ tx .inputs
resolved∈⁻ _ _ x∈
  with _ , i∈ , refl ← ∈-mapWith∈⁻ x∈
  = i∈

mkOutputInfo : TxOutput → OutputInfo
mkOutputInfo o = record
  { TxOutput o
  ; datumHash = o .datum ♯ }

mkInputInfo : ResolvedInput → InputInfo
mkInputInfo (i , o) = record
  { outputRef     = mkOutputInfo o
  ; validatorHash = i .validator ♯
  ; redeemerHash  = i .redeemer ♯ }

mkTxInfo : ∀ (tx : Tx) → Resolved tx → TxInfo
mkTxInfo tx resolvedTx = record
  { Tx tx
  ; inputs  = mkInputInfo  <$> resolveInputs tx resolvedTx
  ; outputs = mkOutputInfo <$> tx .outputs }

-- The state of a ledger maps output references locked by a validator to a value.

S : Type
S = Map⟨ TxOutputRef ↦ TxOutput ⟩

mkUtxo : ∀ {out} tx → out L.Mem.∈ outputs tx → TxOutputRef × TxOutput
mkUtxo {out} tx out∈ = (tx ♯) indexed-at toℕ (L.Any.index out∈) , out

postulate Unique-mkUtxo : ∀ t → Unique $ map proj₁ $ mapWith∈ (t .outputs) (mkUtxo t)

utxoTx : Tx → S
utxoTx tx = fromList $ L.Mem.mapWith∈ (tx .outputs) (mkUtxo tx)

record IsValidTx (tx : Tx) (utxos : S) : Type where
  field
    noDoubleSpending :
      ·Unique (outputRefs tx)

    validOutputRefs :
      ∀[ ref ∈ outputRefs tx ]
        (ref ∈ᵈ utxos)

  resolved : Resolved tx
  resolved = L.All.map (utxos ‼_) validOutputRefs

  txInfo = mkTxInfo tx resolved
  resolvedInputs = resolveInputs tx resolved

  field
    preservesValues :
      tx .forge + ∑ resolvedInputs (value ∘ proj₂) ≡ ∑ (tx .outputs) value

    allInputsValidate :
      ∀[ (i , o) ∈ resolvedInputs ]
        T (call (i .validator) txInfo (i .redeemer) (o .datum))

    validateValidHashes :
      ∀[ (i , o) ∈ resolvedInputs ]
        (o .address ≡ i .validator ♯)

open IsValidTx public

instance
  ·Valid : ∀ {tx s} → · IsValidTx tx s
  ·Valid {s = record {uniq = ·uniq}} .∀≡
    (record { noDoubleSpending = ndp
            ; validOutputRefs = vor
            ; preservesValues = pv
            ; allInputsValidate = aiv
            ; validateValidHashes = vvh
            })
    (record { noDoubleSpending = ndp′
            ; validOutputRefs = vor′
            ; preservesValues = pv′
            ; allInputsValidate = aiv′
            ; validateValidHashes = vvh′
            })
    with uniq ← recompute dec ·uniq
    rewrite ∀≡ ndp ndp′
          | L.All.irrelevant (∈-irr uniq) vor vor′
          | ∀≡ pv pv′
          | L.All.irrelevant B.T-irrelevant aiv aiv′
          | ∀≡ vvh vvh′
          = refl

isValidTx? : ∀ tx s → Dec (IsValidTx tx s)
isValidTx? tx s@(record {uniq = ·uniq})
  with uniq ← recompute dec ·uniq
  with dec
... | no ¬p = no (¬p ∘ noDoubleSpending)
... | yes ndp with dec
... | no ¬p = no (¬p ∘ validOutputRefs)
... | yes vor with dec
... | no ¬p = no absurd
  where absurd : ¬ IsValidTx tx s
        absurd (record {validOutputRefs = vor′; preservesValues = p})
          rewrite L.All.irrelevant (∈-irr uniq) vor vor′ = ¬p p
... | yes pv with dec
... | no ¬p = no absurd
  where absurd : ¬ IsValidTx tx s
        absurd (record {validOutputRefs = vor′; allInputsValidate = p})
          rewrite L.All.irrelevant (∈-irr uniq) vor vor′ = ¬p p
... | yes aiv with dec
... | no ¬p = no absurd
  where absurd : ¬ IsValidTx tx s
        absurd (record {validOutputRefs = vor′; validateValidHashes = p})
          rewrite L.All.irrelevant (∈-irr uniq) vor vor′ = ¬p p
... | yes vvh = yes record
  { noDoubleSpending = ndp
  ; validOutputRefs = vor
  ; preservesValues = pv
  ; allInputsValidate = aiv
  ; validateValidHashes = vvh }

isValidTx : Tx → S → Bool
isValidTx tx s = ⌊ isValidTx? tx s ⌋

-- this is a property of the postulated cryptography (hashing in this case)
postulate s♯t : ∀ {t s} → IsValidTx t s → keys (s ─ᵏˢ outputRefs t) ♯ keys (utxoTx t)
