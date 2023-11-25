-----------------------------------------------
-- ** Common definition for UTxO-based ledgers.

module Common where

open import Prelude.Init renaming (module L to 𝕃)
open SetAsType
open 𝕃.Mem
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.Semigroup; open import Prelude.Monoid
open import Prelude.Lists.Sums
open import Prelude.Lists.Membership

Value   = ℕ
HashId  = ℕ
Address = HashId
postulate _♯ : ∀ {A : Type ℓ} → A → HashId

DATA = ℕ -- T0D0: more realistic data for redeemers

∑ : ∀ {A : Type} → List A → (A → Value) → Value
∑ xs f = ∑ℕ (map f xs)

record TxOutput : Type where
  constructor _at_
  field value    : Value
        address  : Address
open TxOutput public
unquoteDecl DecEq-TxO = DERIVE DecEq [ quote TxOutput , DecEq-TxO ]

record InputInfo : Type where
  field outputRef     : TxOutput
        -- NB: the actual implementation also keeps references here
        validatorHash : HashId
        redeemerHash  : HashId
unquoteDecl DecEq-InputInfo = DERIVE DecEq [ quote InputInfo , DecEq-InputInfo ]

record TxInfo : Type where
  field inputs  : List InputInfo
        outputs : List TxOutput
        forge   : Value
unquoteDecl DecEq-TxInfo = DERIVE DecEq [ quote TxInfo , DecEq-TxInfo ]

module CommonInfo (TxOutputRef : Type) where

  record TxInput : Type where
    field outputRef : TxOutputRef
          validator : TxInfo → DATA → Bool
          redeemer  : DATA
  open TxInput public

  record Tx : Type where
    field inputs  : List TxInput
          outputs : List TxOutput
          forge   : Value
  open Tx public

  -- A ledger is a list of transactions.
  L = List Tx
  -- data L : Type where
  --   [] : L
  --   _⨾_ : L → Tx → L

  -- _++˘_ : Op₂ L
  -- l ++˘ l′ = from (to l ++ to l′)
  -- _++˘_ : Op₂ L
  -- l ++˘ [] = l
  -- l ++˘ (l′ ⨾ t) = (l ++˘ l′) ⨾ t

  -- ++˘-identityˡ : ∀ l → [] ++˘ l ≡ l
  -- ++˘-identityˡ [] = refl
  -- ++˘-identityˡ (l ⨾ _) rewrite ++˘-identityˡ l = refl

  instance
    Semigroup-L : Semigroup L
    Semigroup-L ._◇_ = _++_

    Monoid-L : Monoid L
    Monoid-L .ε = []

  -- Auxiliary definitions.

  outputRefs : Tx → List TxOutputRef
  outputRefs = map outputRef ∘ inputs

  Resolved : Pred₀ Tx
  Resolved tx = ∀ {r} → r ∈ outputRefs tx → TxOutput

  ResolvedL = Σ L (All Resolved)

  ResolvedInput  = TxInput × TxOutput
  ResolvedInputs = List ResolvedInput

  resolveInputs : ∀ tx → Resolved tx → ResolvedInputs
  resolveInputs tx resolvedTx = mapWith∈ (tx .inputs) λ {i} i∈ →
    i , resolvedTx (∈-map⁺ outputRef i∈)

  resolved∈⁻ : ∀ {io} tx → (resolvedTx : Resolved tx)
    → io ∈ resolveInputs tx resolvedTx
    → io .proj₁ ∈ tx .inputs
  resolved∈⁻ _ _ x∈
    with _ , i∈ , refl ← ∈-mapWith∈⁻ x∈
    = i∈

  mkInputInfo : ResolvedInput → InputInfo
  mkInputInfo (i , o) = record
    { outputRef     = o
    ; validatorHash = i .validator ♯
    ; redeemerHash  = i .redeemer ♯ }

  mkTxInfo : ∀ (tx : Tx) → Resolved tx → TxInfo
  mkTxInfo tx resolvedTx = record
    { inputs  = mkInputInfo <$> resolveInputs tx resolvedTx
    ; outputs = tx .outputs
    ; forge   = tx .forge }
