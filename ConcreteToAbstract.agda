module ConcreteToAbstract where

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
open import Prelude.Maybes

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
  l : C.L
  t : C.Tx
  P Q : Pred₀ A.S

absS : C.S → A.S
absS = C.valuesˢ

open ≡-Reasoning

absVT : C.IsValidTx t s → ∃ (flip A.IsValidTx (absS s))
absVT {t}{s} vt = t̂ , record
  { validOutputRefs     = vor′
  ; preservesValues     = pv′
  ; allInputsValidate   = L.All.tabulate aiv′
  ; validateValidHashes = L.All.tabulate vvh′ }
  module ∣absVT∣ where
    is = t .C.inputs; os = t .C.outputs; frg = t .C.forge
    vor = vt .C.validOutputRefs

    goI : C.TxInput × C.TxOutput → A.TxInput
    goI (record {outputRef = _; validator = f; redeemer = r} , o)
       = record {outputRef = o; validator = f; redeemer = r}

    ris = C.resolvedInputs vt
    is′ = map goI ris

    t̂ = record {inputs = is′; outputs = os; forge = frg}
    ŝ = absS s

    stxo≡ : A.stxoTx t̂ ≡ C.values⊑ˢ s (-, vor)
    stxo≡ rewrite
      begin
        A.outputRefs t̂
      ≡˘⟨ L.map-compose ris ⟩
        (A.outputRef ∘ goI) <$> ris
      ≡⟨ map∘mapWith∈ (A.outputRef ∘ goI) is _ ⟩
        mapWith∈ is _
      ≡⟨ mapWith∈-cong is _ _ (λ _ → refl) ⟩
        mapWith∈ is (C.resolved vt ∘ ∈-map⁺ C.outputRef)
      ≡˘⟨ mapWith∈∘map C.outputRef is (C.resolved vt) ⟩
        mapWith∈ (C.outputRef <$> is) (C.resolved vt)
      ≡⟨⟩
        C.values⊑ s (-, vor)
      ∎ = refl

    vor′ : A.stxoTx t̂ B.⊆ˢ ŝ
    vor′ = subst (B._⊆ˢ C.valuesˢ s) (sym stxo≡) (C.values⊆⇒⊆ˢ s (-, vor))

    pv′ =
      begin
        t̂ .A.forge + ∑ (t̂ .A.inputs) (value ∘ A.outputRef)
      ≡⟨⟩
        frg + ∑ (map goI ris) (value ∘ A.outputRef)
      ≡⟨ cong (λ ◆ → frg + ◆) $ cong sum $ sym $ L.map-compose ris ⟩
        frg + ∑ ris (value ∘ proj₂)
      ≡⟨ vt .C.preservesValues ⟩
        ∑ os value
      ≡⟨⟩
        ∑ (t̂ .A.outputs) value
      ∎

    inputInfo≡ =
      begin
        (A.mkInputInfo <$> A.resolveInputs t̂ (A.resolved t̂))
      ≡⟨ map∘mapWith∈ A.mkInputInfo is′ _ ⟩
        mapWith∈ (goI <$> ris) _
      ≡⟨ mapWith∈∘map goI ris _ ⟩
        mapWith∈ ris _
      ≡⟨ mapWith∈-cong ris _ _ (λ _ → refl) ⟩
        mapWith∈ ris _
      ≡⟨ mapWith∈≗map _ ris ⟩
        (C.mkInputInfo <$> ris)
      ∎

    aiv′ : ∀ {i} → i ∈ is′ →
      T $ i .A.validator (A.mkTxInfo t̂ $ A.resolved t̂) (i .A.redeemer)
    aiv′ i∈
      with _ , i∈ , refl ← ∈-map⁻ goI i∈
      rewrite
        begin
          A.mkTxInfo t̂ (A.resolved t̂)
        ≡⟨ cong (λ ◆ → record {inputs = ◆; outputs = os; forge = frg}) inputInfo≡ ⟩
          C.mkTxInfo t (C.resolved vt)
        ∎
      with _ , i∈ , refl ← ∈-mapWith∈⁻ i∈
      = L.All.lookup (vt .C.allInputsValidate) i∈

    vvh′ : ∀ {i} → i ∈ is′ → i .A.outputRef .address ≡ i .A.validator ♯
    vvh′ i∈
      with _ , i∈ , refl ← ∈-map⁻ goI i∈
      = L.All.lookup (vt .C.validateValidHashes) i∈

absT : C.IsValidTx t s → A.Tx
absT = proj₁ ∘ absVT

absS-∪ : absS (s M.∪ s′) ≡ absS s B.∪ absS s′
absS-∪ {s}{s′} = C.valuesˢ-∪ {m = s}{s′}

absS-utxo : ∀ (vt : C.IsValidTx t s) → absS (C.utxoTx t) ≡ A.utxoTx (absT vt)
absS-utxo {t}{s} vt =
  begin
    absS (fromList $ mapWith∈ (t .C.outputs) (C.mkUtxo t))
  ≡⟨⟩
    C.valuesˢ (fromList $ mapWith∈ (t .C.outputs) (C.mkUtxo t))
  ≡⟨ C.valuesˢ∘fromList ⟩
    fromList (proj₂ <$> mapWith∈ (t .C.outputs) (C.mkUtxo t))
  ≡⟨ cong fromList
   $ begin
        proj₂ <$> mapWith∈ (t .C.outputs) (C.mkUtxo t)
      ≡⟨ map∘mapWith∈ proj₂ _ _ ⟩
        mapWith∈ (t .C.outputs) (proj₂ ∘ C.mkUtxo t)
      ≡⟨ mapWith∈-cong _ _ _ (λ _ → refl) ⟩
        mapWith∈ (t .C.outputs) (λ {o} _ → o)
      ≡⟨ mapWith∈≗map id _ ⟩
        map id (t .C.outputs)
      ≡⟨ L.map-id _ ⟩
        t .C.outputs
      ∎
   ⟩
    fromList (t .C.outputs)
  ≡⟨⟩
    fromList (absT vt .A.outputs)
  ∎

absS-stxo : ∀ (vt : C.IsValidTx t s) →
  absS (s C.─ᵏˢ C.outputRefs t) ≡ absS s B.─ A.stxoTx (absT vt)
absS-stxo {t@record{outputs = os}}{s} vt@record{validOutputRefs = vor} =
  let t̂ = absT vt in
  begin
    absS (s C.─ᵏˢ C.outputRefs t)
  ≡⟨⟩
    C.valuesˢ (s C.─ᵏˢ C.outputRefs t)
  ≡⟨ C.valuesˢ-─ s (-, vor) ⟩
    C.valuesˢ s B.─ C.values⊑ˢ s (-, vor)
  ≡˘⟨ cong (C.valuesˢ s B.─_) $ ∣absVT∣.stxo≡ vt ⟩
    C.valuesˢ s B.─ A.stxoTx t̂
  ≡⟨⟩
    absS s B.─ A.stxoTx t̂
  ∎

denot-abs-t₀ : ∀ (vt : C.IsValidTx t s) →
  A.⟦ absT vt ⟧₀ (absS s) ≡ absS (C.⟦ t ⟧₀ s)
denot-abs-t₀ {t}{s} vt = let t̂ = absT vt in
  sym $ begin
    absS (s C.─ᵏˢ C.outputRefs t M.∪ C.utxoTx t)
  ≡⟨ absS-∪ {s C.─ᵏˢ C.outputRefs t}{C.utxoTx t} ⟩
    absS (s C.─ᵏˢ C.outputRefs t) B.∪ absS (C.utxoTx t)
  ≡⟨ cong (B._∪ _) (absS-stxo vt) ⟩
    absS s B.─ A.stxoTx t̂ B.∪ absS (C.utxoTx t)
  ≡⟨ cong (absS s B.─ A.stxoTx t̂ B.∪_) (absS-utxo vt) ⟩
    absS s B.─ A.stxoTx t̂ B.∪ A.utxoTx t̂
  ∎

denot-t : ∀ {t : C.Tx} {s : C.S} (vt : C.IsValidTx t s) →
  C.⟦ t ⟧ s ≡ just (C.⟦ t ⟧₀ s)
denot-t {t}{s} vt rewrite dec-yes (C.isValidTx? t s) vt .proj₂ = refl

denot-t̂ : ∀ {t : A.Tx} {s : A.S} (vt : A.IsValidTx t s) →
  A.⟦ t ⟧ s ≡ just (A.⟦ t ⟧₀ s)
denot-t̂ {t}{s} vt rewrite dec-yes (A.isValidTx? t s) vt .proj₂ = refl

denot-abs-t : ∀ (vt : C.IsValidTx t s) →
  A.⟦ absT vt ⟧ (absS s) ≡ (absS <$> C.⟦ t ⟧ s)
denot-abs-t {t}{s} vt =
  begin
    A.⟦ absT vt ⟧ (absS s)
  ≡⟨ denot-t̂ (absVT vt .proj₂) ⟩
    just (A.⟦ absT vt ⟧₀ $ absS s)
  ≡⟨ cong just $ denot-abs-t₀ vt ⟩
    just (absS $ C.⟦ t ⟧₀ s)
  ≡˘⟨ M.map-just $ denot-t vt ⟩
    (absS <$> C.⟦ t ⟧ s)
  ∎

absVL : C.VL s l → ∃ $ A.VL (absS s)
absVL [] = -, []
absVL {s}{.t ∷ l} (t ⊣ vt ∷ vl) =
  let
    t̂ , vt̂ = absVT {s = s} vt
    l̂  , vl̂ = absVL vl

    EQ : absS (C.⟦ t ⟧₀ s) ≡ A.⟦ t̂ ⟧₀ (absS s)
    EQ = sym $ denot-abs-t₀ vt
  in
    t̂ ∷ l̂ , t̂ ⊣ vt̂ ∷ subst (λ ◆ → A.VL ◆ l̂) EQ vl̂

absL : C.VL s l → A.L
absL = proj₁ ∘ absVL

denot-abs₀ : ∀ (vl : C.VL s l) →
  A.⟦ absL vl ⟧₀ (absS s) ≡ absS (C.⟦ l ⟧₀ s)
denot-abs₀ [] = refl
denot-abs₀ {s} {t ∷ l} (t ⊣ vt ∷ vl) = let ŝ = absS s; t̂ = absT vt; l̂ = absL vl in
  begin
    A.⟦ l̂ ⟧₀ (A.⟦ t̂ ⟧₀ ŝ)
  ≡⟨ cong A.⟦ l̂ ⟧₀ $ denot-abs-t₀ vt ⟩
    A.⟦ l̂ ⟧₀ (absS $ C.⟦ t ⟧₀ s)
  ≡⟨ denot-abs₀ {s = C.⟦ t ⟧₀ s} vl ⟩
    absS (C.⟦ l ⟧₀ $ C.⟦ t ⟧₀ s)
  ∎

denot-l : ∀ {l : C.L} {s : C.S} (vl : C.VL s l) →
  C.⟦ l ⟧ s ≡ just (C.⟦ l ⟧₀ s)
denot-l [] = refl
denot-l (_ ⊣ vt ∷ vl) rewrite denot-t vt | denot-l vl = refl

denot-l̂ : ∀ {l : A.L} {s : A.S} (vl : A.VL s l) →
  A.⟦ l ⟧ s ≡ just (A.⟦ l ⟧₀ s)
denot-l̂ [] = refl
denot-l̂ (_ ⊣ vt ∷ vl) rewrite denot-t̂ vt | denot-l̂ vl = refl

denot-abs : ∀ (vl : C.VL s l) →
  A.⟦ absL vl ⟧ (absS s) ≡ (absS <$> C.⟦ l ⟧ s)
denot-abs [] = refl
denot-abs {s} {t ∷ l} (.t ⊣ vt ∷ vl)
  rewrite denot-t vt | denot-t̂ (absVT vt .proj₂) =
  let ŝ = absS s; t̂ = absT vt; l̂ , vl̂ = absVL vl in
  begin
    A.⟦ l̂ ⟧ (A.⟦ t̂ ⟧₀ ŝ)
  ≡⟨ cong A.⟦ l̂ ⟧ $ denot-abs-t₀ vt ⟩
    A.⟦ l̂ ⟧ (absS $ C.⟦ t ⟧₀ s)
  ≡⟨ denot-l̂ vl̂ ⟩
    just (A.⟦ l̂ ⟧₀ $ absS $ C.⟦ t ⟧₀ s)
  ≡⟨ cong just $ denot-abs₀ vl ⟩
    just (absS $ C.⟦ l ⟧₀ $ C.⟦ t ⟧₀ s)
  ≡˘⟨ M.map-just $ denot-l vl ⟩
    (absS <$> C.⟦ l ⟧ (C.⟦ t ⟧₀ s))
  ∎

↑ = M.Any.Any

denot-sound : ∀ (vl : C.VL s l) →
  (P (absS s) → ↑ Q (A.⟦ absL vl ⟧ $ absS s))
  ───────────────────────────────────────────
  (P (absS s) → ↑ Q (absS <$> C.⟦ l ⟧ s))
denot-sound vl PlQ Ps = subst (↑ _) (denot-abs vl) (PlQ Ps)

denot-sound′ : ∀ (vl : C.VL s l) →
  ∙ P (absS s)
  ∙ ↑ Q (A.⟦ absL vl ⟧ $ absS s)
    ─────────────────────────────
    ↑ Q (absS <$> C.⟦ l ⟧ s)
denot-sound′ vl Ps = subst (↑ _) (denot-abs vl)

{- ** cannot formulate soundness without relating to a specific state
soundness : ∀ {P Q : Pred₀ A.S} (vl : C.VL {!!} l) →
  A.⟨ P ⟩ absL vl ⟨ Q ⟩
  ─────────────────────────────
  C.⟨ P ∘ absS ⟩ l ⟨ Q ∘ absS ⟩
soundness = {!!}
-}

-- ** universally quantifying abstract ledgers
soundness-∀l̂ : ∀ {P Q : Pred₀ A.S} →
    (∀ l̂ → A.⟨ P ⟩ l̂ ⟨ Q ⟩)
    ─────────────────────────────────────────────
    C.⟨ (P ∘ absS) ∩ flip C.VL l ⟩ l ⟨ Q ∘ absS ⟩
soundness-∀l̂ {l}{P}{Q} PlQ {s} (Ps , vl) =
  MAny-map⁻ Qs
  where
    ŝ = absS s
    l̂ = absL vl

    Qŝ : M.Any.Any Q (A.⟦ l̂ ⟧ ŝ)
    Qŝ = PlQ l̂ Ps

    Qs : M.Any.Any Q (absS <$> C.⟦ l ⟧ s)
    Qs = subst (M.Any.Any Q) (denot-abs vl) Qŝ

-- ** universally quantifying proofs of validity
soundness-∀vl : ∀ {P Q : Pred₀ A.S} →
  (∀ {s} (vl : C.VL s l) → A.⟨ P ⟩ absL vl ⟨ Q ⟩)
  ───────────────────────────────────────────────
  C.⟨ (P ∘ absS) ∩ flip C.VL l ⟩ l ⟨ Q ∘ absS ⟩
soundness-∀vl {l}{P}{Q} PlQ {s} (Ps , vl) =
  MAny-map⁻ Qs
  where
    ŝ = absS s
    l̂ = absL vl

    Qŝ : M.Any.Any Q (A.⟦ l̂ ⟧ ŝ)
    Qŝ = PlQ vl Ps

    Qs : M.Any.Any Q (absS <$> C.⟦ l ⟧ s)
    Qs = subst (M.Any.Any Q) (denot-abs vl) Qŝ

-- ** alternative formulation using "strong" abstract Hoare triples
𝔸⟨_⟩_⊣_⟨_⟩ : ∀ P l →
  (∀ s → P $ absS s → C.VL s l) → Pred₀ A.S → Type
𝔸⟨ P ⟩ l ⊣ P⇒ ⟨ Q ⟩ =
  (∀ s (p : P $ absS s) → (Q A.↑∘ A.⟦ absL (P⇒ s p) ⟧) (absS s))

semi-soundness : ∀ {P Q : Pred₀ A.S} →
  ∀ (P⇒ : ∀ s → P $ absS s → C.VL s l) →
  ∙ 𝔸⟨ P ⟩ l ⊣ P⇒ ⟨ Q ⟩
    ──────────────────────────────────
    C.⟨ P ∘ absS ⟩ l ⟨ Q ∘ absS ⟩
semi-soundness {l}{P}{Q} P⇒ PlQ {s} Ps
  = MAny-map⁻ $ subst (M.Any.Any Q) (denot-abs vl) Qs
  where
    vl = P⇒ _ Ps

    Qs : (Q A.↑∘ A.⟦ absL vl ⟧) (absS s)
    Qs = PlQ _ Ps

-- ** Reasoning on the abstract level is sound; proving an abstract Hoare triple
-- is enough to prove a concrete Hoare triple (with abstract pre-/post-conditions).
soundness :
  ∀ (vl : C.VL s l) →
  ∙ A.⟨ P ⟩ absL vl ⟨ Q ⟩＠ absS s
    ────────────────────────────────
    C.⟨ P ∘ absS ⟩ l ⟨ Q ∘ absS ⟩＠ s
soundness {s}{l}{P}{Q} vl PlQ Ps
  = MAny-map⁻ $ subst (M.Any.Any Q) (denot-abs vl) Qs
  where
    Qs : (Q A.↑∘ A.⟦ absL vl ⟧) (absS s)
    Qs = PlQ Ps
