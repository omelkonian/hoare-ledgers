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
open import Prelude.Apartness
open import Prelude.Allable hiding (All)

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

postulate Unique-mkUtxo : ∀ t → Unique $ map proj₁ $ mapWith∈ (t .outputs) (mkUtxo t)

utxoTx : Tx → S
utxoTx tx = fromList $ L.Mem.mapWith∈ (tx .outputs) (mkUtxo tx)

-- ** Utilities relating Prelude.Maps and Prelude.Bags.
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

  open ≡-Reasoning
  private variable
    m m′ : Map⟨ K ↦ V ⟩
    ks : List K; kvs : List (K × V)

  open import Prelude.Lists.Dec
  open import Prelude.Apartness

  -- basic list properties
  postulate
    nubBy-from∘to : ∀ {A B : Type} ⦃ _ : DecEq B ⦄ {f : A → B} {xs : List A} →
      Unique (map f xs) → nubBy f xs ≡ xs
    Unique-proj₁ : ∀ {A B : Type} {xys : List (A × B)} →
      Unique (map proj₁ xys) → Unique xys
    Disjoint-proj₁ : ∀ {A B : Type} {xys xys′ : List (A × B)} →
      map proj₁ xys ♯ map proj₁ xys′ → xys ♯ xys′

  nub∘nubBy-from∘to : ∀ {A B : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄
    {f : A → B} {xs : List A} →
    Unique (map f xs) →
      nub (nubBy f xs) ≡ xs
  nub∘nubBy-from∘to {f = f}{xs} uniq =
    begin
      nub (nubBy f xs)
    ≡⟨ nub-from∘to $ Unique-nubBy f xs ⟩
      nubBy f xs
    ≡⟨ nubBy-from∘to uniq ⟩
      xs
    ∎

  toList-∪ : keys m ♯ keys m′ →  toList (m ∪ m′) ≡ toList m ++ toList m′
  toList-∪ {m@(_ ⊣ ·uniq-m)}{m′@(_ ⊣ ·uniq-m′)} m♯m′ =
    begin
      toList (m ∪ m′)
    ≡⟨⟩
      nub (nubBy proj₁ (toList m ++ toList m′))
    ≡⟨ cong nub $ nubBy-from∘to uniq-proj₁-++ ⟩
      nub (toList m ++ toList m′)
    ≡⟨ nub-from∘to uniq-++ ⟩
      toList m ++ toList m′
    ∎
    where
      uniq-m  = recompute dec ·uniq-m
      uniq-m′ = recompute dec ·uniq-m′

      uniq-++ : Unique (toList m ++ toList m′)
      uniq-++ = L.Uniq.++⁺ (Unique-proj₁ uniq-m) (Unique-proj₁ uniq-m′)
                           (Disjoint-proj₁ m♯m′)

      uniq-proj₁-++ : Unique $ map proj₁ (toList m ++ toList m′)
      uniq-proj₁-++ rewrite L.map-++-commute proj₁ (toList m) (toList m′)
        = L.Uniq.++⁺ uniq-m uniq-m′ m♯m′

  module _ m m′ (m♯m′ : keys m ♯ keys m′) where
    valuesˢ-∪ : valuesˢ (m ∪ m′) ≡ valuesˢ m B.∪ valuesˢ m′
    valuesˢ-∪ =
      begin
        valuesˢ (m ∪ m′)
      ≡⟨⟩
        fromList (proj₂ <$> toList (m ∪ m′))
      ≡⟨ cong (fromList ∘ map proj₂) $ toList-∪ {m}{m′} m♯m′ ⟩
        fromList (proj₂ <$> (toList m ++ toList m′))
      ≡⟨ cong fromList $ L.map-++-commute proj₂ (toList m) (toList m′) ⟩
        fromList ((proj₂ <$> toList m) ++ (proj₂ <$> toList m′))
      ≡⟨⟩
        fromList (proj₂ <$> toList m) B.∪ fromList (proj₂ <$> toList m′)
      ≡⟨⟩
        valuesˢ m B.∪ valuesˢ m′
      ∎

  valuesˢ∘fromList : Unique (proj₁ <$> kvs) →
    valuesˢ (fromList kvs) ≡ fromList (proj₂ <$> kvs)
  valuesˢ∘fromList = cong (fromList ∘ map proj₂) ∘ nub∘nubBy-from∘to

  valuesˢ-─ : ∀ m (p : ∃ $ All (_∈ᵈ m)) →
    valuesˢ (m ─ᵏˢ p .proj₁) ≡ valuesˢ m B.─ values⊑ˢ m p
  valuesˢ-─ m (ks , ks⊆) =
    begin
      valuesˢ (m ─ᵏˢ ks)
    ≡⟨⟩
      fromList (proj₂ <$> toList (m ─ᵏˢ ks))
    ≡⟨⟩
      fromList (proj₂ <$> filter ((_∉? ks) ∘ proj₁) (toList m))
    ≡⟨ cong fromList H ⟩
      fromList
        (map proj₂ (toList m) ∸[bag] (mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆)))
    ≡⟨⟩
      fromList (proj₂ <$> toList m)
        B.─
      fromList (mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆))
    ≡⟨⟩
      fromList (proj₂ <$> toList m) B.─ fromList (values⊑ m (-, ks⊆))
    ≡⟨⟩
      valuesˢ m B.─ values⊑ˢ m (-, ks⊆)
    ∎
    where
      postulate
        H : map proj₂ (filter ((_∉? ks) ∘ proj₁) (toList m))
          ≡ map proj₂ (toList m) ∸[bag] (mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆))


  postulate
    values⊆⇒⊆[bag] : ∀ m (p : ∃ $ All (_∈ᵈ m)) → values⊑ m p ⊆[bag] values m

  values⊆⇒⊆ˢ : ∀ m (p : ∃ $ All (_∈ᵈ m)) → values⊑ˢ m p B.⊆ˢ valuesˢ m
  values⊆⇒⊆ˢ = values⊆⇒⊆[bag]

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

-- this is a property of the postulated cryptography (hashing in this case)
postulate s♯t : ∀ {t s} → IsValidTx t s → keys (s ─ᵏˢ outputRefs t) ♯ keys (utxoTx t)
