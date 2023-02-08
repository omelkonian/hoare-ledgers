----------------------------------------------
-- ** Basic definition for UTxO-based ledgers.

{-# OPTIONS --allow-unsolved-metas #-}
module UTxOErr.UTxO where

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.Maybes
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToN
open import Prelude.Lists hiding (_⁉_; _‼_)
open import Prelude.Lists.Dec
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.FromList
open import Prelude.Membership

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

module _ {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : DecEq V ⦄ where
  open import Prelude.ToList
  import Prelude.Sets as S
  import Prelude.Bags as B

  _─ᵏˢ_ : Map⟨ K ↦ V ⟩ → List K → Map⟨ K ↦ V ⟩
  m ─ᵏˢ ks = filterK (_∉? ks) m

  keys : Map⟨ K ↦ V ⟩ → List K
  keys m = proj₁ <$> m .Map.kvs ∙toList

  _‼_ : {k : K} (m : Map⟨ K ↦ V ⟩) → k ∈ᵈ m → V
  m ‼ k∈ = destruct-Is-just (∈ᵈ⇒⁉ m k∈) .proj₁

  open L.SubL renaming (_⊆_ to _⊑_)

  -- TODO: Unique ks → ks ⊆ keys m →

  values⊑ : (m : Map⟨ K ↦ V ⟩) → ∃ (_⊑ keys m) → List V
  values⊑ m (ks , p) = L.Mem.mapWith∈ ks λ k∈ → m ‼ L.SubL.lookup p k∈

  values⊑ˢ : (m : Map⟨ K ↦ V ⟩) → ∃ (_⊑ keys m) → B.Bag⟨ V ⟩
  values⊑ˢ = fromList ∘₂ values⊑

  values : Map⟨ K ↦ V ⟩ → List V
  values m = values⊑ m (keys m , L.SubL.⊆-refl)

  valuesˢ : Map⟨ K ↦ V ⟩ → B.Bag⟨ V ⟩
  valuesˢ = fromList ∘ values

  private variable
    m m′ : Map⟨ K ↦ V ⟩
    ks : List K; kvs : List (K × V)
  postulate
    valuesˢ-∪ : valuesˢ (m ∪ m′) ≡ valuesˢ m B.∪ valuesˢ m′
    valuesˢ∘fromList : valuesˢ (fromList kvs) ≡ fromList (proj₂ <$> kvs)
    valuesˢ-─ : (ks⊑ : ks ⊑ keys m) →
      valuesˢ (m ─ᵏˢ ks) ≡ valuesˢ m B.─ values⊑ˢ m (ks , ks⊑)

    values⊆⇒⊆[bag] : (m : Map⟨ K ↦ V ⟩) (p : ∃ $ _⊑ keys m) →
      values⊑ m p ⊆[bag] values m
  -- values⊆⇒⊆[bag] m ([] , p) = []
  -- values⊆⇒⊆[bag] (((x ∷ xs) S.⊣ _) ⊣ _) (k ∷ ks , p L.SubL.∷ʳ q) = {!!}
  -- values⊆⇒⊆[bag] (((x ∷ xs) S.⊣ _) ⊣ _) (k ∷ ks , p L.SubL.∷ q) = {!!}

  values⊆⇒⊆ˢ : (m : Map⟨ K ↦ V ⟩) (p : ∃ $ _⊑ keys m) →
    values⊑ˢ m p B.⊆ˢ valuesˢ m
  values⊆⇒⊆ˢ = values⊆⇒⊆[bag]

record IsValidTx (tx : Tx) (utxos : S) : Type where
  field
    validOutputRefs :
      outputRefs tx ⊑ keys utxos
      -- All (_∈ᵈ utxos) (outputRefs tx)
      -- Unique (outputRefs tx)

  resolved : Resolved tx
  resolved = (utxos ‼_) ∘ L.SubL.lookup validOutputRefs

  txInfo = mkTxInfo tx resolved
  resolvedInputs = resolveInputs tx resolved

  field
    preservesValues :
      tx .forge + ∑ resolvedInputs (value ∘ proj₂) ≡ ∑ (tx .outputs) value

    allInputsValidate :
      All (λ i → T $ i .validator txInfo (i .redeemer)) (tx .inputs)

    validateValidHashes :
      All (λ (i , o) → o .address ≡ i .validator ♯) resolvedInputs

open IsValidTx public

open import Prelude.Irrelevance

instance
  postulate ·⊑ : ∀ {A : Type} {xs ys : List A} → · (xs ⊑ ys)

  ·Valid : ∀ {tx s} → · IsValidTx tx s
  ·Valid .∀≡ (record { validOutputRefs = vor
                     ; preservesValues = pv
                     ; allInputsValidate = aiv
                     ; validateValidHashes = vvh
                     })
             (record { validOutputRefs = vor′
                     ; preservesValues = pv′
                     ; allInputsValidate = aiv′
                     ; validateValidHashes = vvh′
                     })
    rewrite ∀≡ vor vor′
          | ∀≡ pv pv′
          | L.All.irrelevant B.T-irrelevant aiv aiv′
          | L.All.irrelevant ∀≡ vvh vvh′
          = refl

isValidTx? : ∀ tx s → Dec (IsValidTx tx s)
isValidTx? tx utxos
  = {!!}
--   with all? (_∈ᵈ? utxos) (outputRefs tx)
-- ... | no ¬p = no (¬p ∘ validOutputRefs)
-- ... | yes p₁
--   with M.Any.dec (λ q → tx .forge + q ≟ ∑ (tx .outputs) value)
--                  (∑M (map (getSpentOutput utxos) (tx .inputs)) value)
-- ... | no ¬p = no (¬p ∘ preservesValues)
-- ... | yes p₂
--   = ?
-- --   with unique? (outputRefs tx)
-- -- ... | no ¬p = no (¬p ∘ noDoubleSpending)
-- -- ... | yes p₃
-- --   with all? (λ i →
-- --     T? $ validator i
-- --       (mkTxInfo tx $ proj₁ ∘ destruct-Is-just ∘ ∈ᵈ⇒⁉ utxos ∘ L.All.lookup p₁)
-- --       (i .redeemer)
-- --     ) (tx .inputs)
-- -- ... | no ¬p = no TODO -- (¬p ∘ allInputsValidate)
-- --   where postulate TODO : ∀ {A : Type} → A
-- -- ... | yes p₄
-- --   with all? (λ i → M.Any.dec (λ o → o .address ≟ i .validator ♯) (getSpentOutput utxos i))
-- --             (tx .inputs)
-- -- ... | no ¬p = no (¬p ∘ validateValidHashes)
-- -- ... | yes p₅ = yes record {validOutputRefs = p₁; preservesValues = p₂; noDoubleSpending = p₃; allInputsValidate = p₄; validateValidHashes = p₅}

isValidTx : Tx → S → Bool
isValidTx tx s = ⌊ isValidTx? tx s ⌋
