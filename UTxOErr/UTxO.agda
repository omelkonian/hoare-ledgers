----------------------------------------------
-- ** Basic definition for UTxO-based ledgers.

module UTxOErr.UTxO where

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

-- open import UTxOErr.Maps
open import Prelude.Maps

open import Common public

record TxOutputRef : Type where
  constructor _indexed-at_
  field txId  : HashId
        index : ℕ
open TxOutputRef public
unquoteDecl DecEq-TxOR = DERIVE DecEq [ quote TxOutputRef , DecEq-TxOR ]

open CommonInfo TxOutputRef public

-- The state of a ledger maps output references locked by a validator to a value.

S : Type
S = Map⟨ TxOutputRef ↦ TxOutput ⟩

mkUtxo : ∀ {out} tx → out L.Mem.∈ outputs tx → TxOutputRef × TxOutput
mkUtxo {out} tx out∈ = (tx ♯) indexed-at toℕ (L.Any.index out∈) , out

utxoTx : Tx → S
utxoTx tx = fromList $ L.Mem.mapWith∈ (tx .outputs) (mkUtxo tx)

-- open L.SubL renaming (_⊆_ to _⊑_)

module _ {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : DecEq V ⦄ where
  open import Prelude.ToList
  import Prelude.Sets as S
  import Prelude.Bags as B

  _‼_ : {k : K} (m : Map⟨ K ↦ V ⟩) → k ∈ᵈ m → V
  m ‼ k∈ = destruct-Is-just (∈ᵈ⇒⁉ m k∈) .proj₁

  _─ᵏˢ_ : Map⟨ K ↦ V ⟩ → List K → Map⟨ K ↦ V ⟩
  m ─ᵏˢ ks = filterK (_∉? ks) m

  keys : Map⟨ K ↦ V ⟩ → List K
  keys = map proj₁ ∘ toList

  keysˢ : Map⟨ K ↦ V ⟩ → B.Bag⟨ K ⟩
  keysˢ = fromList ∘ keys

  values⊑ : (m : Map⟨ K ↦ V ⟩) → ∃ $ All (_∈ᵈ m) → List V
  values⊑ m (ks , ks⊆) = mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆)

  values values′ : Map⟨ K ↦ V ⟩ → List V
  values = map proj₂ ∘ toList
  values′ m = values⊑ m (keys m , L.All.tabulate id)

  values⊑ˢ : (m : Map⟨ K ↦ V ⟩) → ∃ $ All (_∈ᵈ m) → B.Bag⟨ V ⟩
  values⊑ˢ = fromList ∘₂ values⊑

  valuesˢ valuesˢ′ : Map⟨ K ↦ V ⟩ → B.Bag⟨ V ⟩
  valuesˢ = fromList ∘ map proj₂ ∘ toList
  valuesˢ′ m = values⊑ˢ m (keys m , L.All.tabulate id)

  private variable
    m m′ : Map⟨ K ↦ V ⟩
    ks : List K; kvs : List (K × V)
  postulate
    valuesˢ-∪ : valuesˢ (m ∪ m′) ≡ valuesˢ m B.∪ valuesˢ m′
    valuesˢ∘fromList : valuesˢ (fromList kvs) ≡ fromList (proj₂ <$> kvs)
    valuesˢ-─ : ∀ m (p : ∃ $ All (_∈ᵈ m)) →
      valuesˢ (m ─ᵏˢ p .proj₁) ≡ valuesˢ m B.─ values⊑ˢ m p
    values⊆⇒⊆[bag] : ∀ m (p : ∃ $ All (_∈ᵈ m)) →
      values⊑ m p ⊆[bag] values m

  values⊆⇒⊆ˢ : ∀ m (p : ∃ $ All (_∈ᵈ m)) → values⊑ˢ m p B.⊆ˢ valuesˢ m
  values⊆⇒⊆ˢ = values⊆⇒⊆[bag]

--   values⊑ : Map⟨ K ↦ V ⟩ → List K → List V
--   values⊑ m ks = map proj₂ $ filter ((_∈? ks) ∘ proj₁) $ toList m

--   values values′ : Map⟨ K ↦ V ⟩ → List V
--   values = map proj₂ ∘ toList
--   values′ m = values⊑ m (keys m)

--   values⊑ˢ : Map⟨ K ↦ V ⟩ → List K → B.Bag⟨ V ⟩
--   values⊑ˢ m ks = fromList $ map proj₂ $ filter ((_∈? ks) ∘ proj₁) $ toList m

--   valuesˢ valuesˢ′ : Map⟨ K ↦ V ⟩ → B.Bag⟨ V ⟩
--   valuesˢ = fromList ∘ map proj₂ ∘ toList
--   valuesˢ′ m = values⊑ˢ m (keys m)

--   private variable
--     m m′ : Map⟨ K ↦ V ⟩
--     ks : List K; kvs : List (K × V)
--   postulate
--     valuesˢ-∪ : valuesˢ (m ∪ m′) ≡ valuesˢ m B.∪ valuesˢ m′
--     valuesˢ∘fromList : valuesˢ (fromList kvs) ≡ fromList (proj₂ <$> kvs)
--     valuesˢ-─ : valuesˢ (m ─ᵏˢ ks) ≡ valuesˢ m B.─ values⊑ˢ m ks
--     values⊆⇒⊆[bag] : ∀ m ks → values⊑ m ks ⊆[bag] values m

--   values⊆⇒⊆ˢ : ∀ m ks → values⊑ˢ m ks B.⊆ˢ valuesˢ m
--   values⊆⇒⊆ˢ = values⊆⇒⊆[bag]

record IsValidTx (tx : Tx) (utxos : S) : Type where
  field
    noDoubleSpending :
      ·Unique (outputRefs tx)

    validOutputRefs :
      ∀[ ref ∈ outputRefs tx ]
        (ref ∈ᵈ utxos)

  resolved : Resolved tx
  resolved = (utxos ‼_) ∘ L.All.lookup validOutputRefs

  txInfo = mkTxInfo tx resolved
  resolvedInputs = resolveInputs tx resolved

  field
    preservesValues :
      tx .forge + ∑ resolvedInputs (value ∘ proj₂) ≡ ∑ (tx .outputs) value

    allInputsValidate :
      ∀[ i ∈ tx .inputs ]
        T (i .validator txInfo (i .redeemer))

    validateValidHashes :
      ∀[ (i , o) ∈ resolvedInputs ]
        (o .address ≡ i .validator ♯)

open IsValidTx public

instance
  ·Valid : ∀ {tx s} → · IsValidTx tx s
  ·Valid {s = _ ⊣ ·uniq} .∀≡
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
isValidTx? tx s@(_ ⊣ ·uniq)
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
