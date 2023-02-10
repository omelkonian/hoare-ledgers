module AbstractToConcrete where

open import Prelude.Init; open SetAsType
open L.Mem
open Unary using (_∩_)
open import Prelude.Lists.Membership
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Functor
open import Prelude.FromList; open import Prelude.ToList
open import Prelude.DecEq
open import Prelude.Monad

import Prelude.Bags as B
import Prelude.Maps as M

open import Common
import UTxOErr.UTxO      as C
import ValueSepUTxO.UTxO as A
open import UTxOErr.Ledger      as C
  using ([]; _⊣_∷_)
open import ValueSepUTxO.Ledger as A
  using ([]; _⊣_∷_)
import ValueSepUTxO.UTxO as A
import UTxOErr.HoareLogic      as C
import ValueSepUTxO.HoareLogic as A

-- ** abstracting away implementation details
private variable
  s s′ : C.S
  l̂ : A.L
  t̂ : A.Tx

absS : C.S → A.S
absS = C.valuesˢ

open ≡-Reasoning

postulate
  map∘mapWith∈ : ∀ {A B C : Type}
     (g : B → C)  (xs : List A) (f : ∀ {x} → x ∈ xs → B)
    → map g (mapWith∈ xs f) ≡ mapWith∈ xs (g ∘ f)
  mapWith∈∘map : ∀ {A B C : Type}
    (f : A → B) (xs : List A) (g : ∀ {x} → x ∈ map f xs → C)
    → mapWith∈ (map f xs) g ≡ mapWith∈ xs (g ∘ ∈-map⁺ f)

concVT : A.IsValidTx t̂ (absS s) → ∃ (flip C.IsValidTx s)
concVT {t̂}{s} vt̂ = t , record
  { validOutputRefs     = vor′
  ; preservesValues     = pv′
  ; allInputsValidate   = L.All.tabulate aiv′
  ; validateValidHashes = L.All.tabulate vvh′ }
  where
    is = t̂ .A.inputs; os = t̂ .A.outputs; frg = t̂ .A.forge
    vor = vt̂ .A.validOutputRefs

    -- goI : A.TxInput × C.TxOutput → C.TxInput × C.TxOutput
    -- goI (record {outputRef = _; validator = f; redeemer = r} , o)
    --    = record {outputRef = o; validator = f; redeemer = r}

    -- ris = C.resolvedInputs vt
    is′ = {!!} -- map goI ris

    t = record {inputs = is′; outputs = os; forge = frg}
    ŝ = absS s

    rt : C.Resolved t
    rt = {!!}

    ris : C.ResolvedInputs
    ris = C.resolveInputs t rt

    open L.SubL renaming (_⊆_ to _⊑_)

    vor′ : C.outputRefs t ⊑ C.keys s
    vor′ = {!!}

    pv′ : frg + ∑ ris (value ∘ proj₂) ≡ ∑ os value
    pv′ = vt̂ .A.preservesValues

    aiv′ : ∀ {i} → i ∈ is′ →
      T $ i .C.validator (C.mkTxInfo t rt) (i .C.redeemer)
    aiv′ i∈ = {!L.All.lookup (vt̂ .A.allInputsValidate)  !}

    vvh′ : ∀ {io} → io ∈ ris → io .proj₂ .address ≡ io .proj₁ .C.validator ♯
    vvh′ io∈ = {!!}

concT : A.IsValidTx t̂ (absS s) → C.Tx
concT = proj₁ ∘ concVT

postulate concL : A.L → C.L

soundness : ∀ {P Q : Pred₀ A.S} →
  A.⟨ P ⟩ l̂ ⟨ Q ⟩
  ───────────────────────────────────
  C.⟨ P ∘ absS ⟩ concL l̂ ⟨ Q ∘ absS ⟩
soundness = {!!}

-- NB: conc either non-deterministic or canonical
