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

{- ** USE CASE

We can compositionally reason about an *abstract* UTxO ledger,
but can we transfer the results to an actual *concrete* UTxO ledger?

Well, this would only be possible for properties that do not observe the concrete
implementation details (such as the order of transaction outputs, c.f. set/list).
This could be enforced by only considering predicates of the
form: `Pᶜ = Pᵃ ∘ concrete→abstract` for some abstract predicate Pᵃ and a
concrete→abstract translation which forgets about implementation details.

At this point, we can use our reasoning framework on concrete ledgers,
but can we prove that this procedure is sound?
Is this even possible? Seems connected to parametricity and such...

NB: might be worth just looking at the minimal example of sets/lists and figuring
out the issue at this more simplistic setting first.
-}

M-Any-∘ : ∀ {A B : Type} {P : Pred₀ B} {f : A → B} {mx : Maybe A} →
  M.Any.Any P (f <$> mx)
  ───────────────────
  M.Any.Any (P ∘ f) mx
M-Any-∘ {mx = just _} (M.Any.just p) = M.Any.just p

-- ** abstracting away implementation details
private variable
  s s′ : C.S
  l : C.L
  t : C.Tx

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

postulate to∘from : toList ∘ fromList {B = C.S} ≗ id

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
  ≡⟨ C.valuesˢ-─ vor ⟩
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

denot-abs-t : ∀ {vt : C.IsValidTx t s} →
  A.⟦ absT vt ⟧ (absS s) ≡ (absS <$> C.⟦ t ⟧ s)
denot-abs-t {t}{s}{vt} =
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

denot-abs : ∀ {vl : C.VL s l} →
  A.⟦ absL vl ⟧ (absS s) ≡ (absS <$> C.⟦ l ⟧ s)
denot-abs {s} {[]} {[]} = refl
denot-abs {s} {t ∷ l} {.t ⊣ vt ∷ vl}
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

postulate
  MAny-map⁻ : ∀ {A B : Type} {f : A → B} {mx} (P : Pred₀ B) →
    M.Any.Any P (M.map f mx)
    ────────────────────────
    M.Any.Any (P ∘ f) mx

{- ** cannot formulate soundness without relating to a specific state
soundness : ∀ {P Q : Pred₀ A.S} (vl : C.VL {!!} l) →
  A.⟨ P ⟩ absL vl ⟨ Q ⟩
  ─────────────────────────────
  C.⟨ P ∘ absS ⟩ l ⟨ Q ∘ absS ⟩
soundness = {!!}
-}

-- ** universally quantifying abstractt ledgers
soundness-∀l̂ : ∀ {P Q : Pred₀ A.S} →
    (∀ l̂ → A.⟨ P ⟩ l̂ ⟨ Q ⟩)
    ───────────────────────────────────────────────────
    C.⟨ (P ∘ absS) ∩ flip C.VL l ⟩ l ⟨ Q ∘ absS ⟩
soundness-∀l̂ {l}{P}{Q} PlQ {s} (Ps , vl) =
  MAny-map⁻ Q Qs
  where
    ŝ = absS s
    l̂ = absL vl

    Qŝ : M.Any.Any Q (A.⟦ l̂ ⟧ ŝ)
    Qŝ = PlQ l̂ Ps

    Qs : M.Any.Any Q (absS <$> C.⟦ l ⟧ s)
    Qs = subst (M.Any.Any Q) (denot-abs {vl = vl}) Qŝ

-- ** universally quantifying proofs of validity
soundness-∀vl : ∀ {P Q : Pred₀ A.S} →
  (∀ {s} (vl : C.VL s l) → A.⟨ P ⟩ absL vl ⟨ Q ⟩)
  ───────────────────────────────────────────────────
  C.⟨ (P ∘ absS) ∩ flip C.VL l ⟩ l ⟨ Q ∘ absS ⟩
soundness-∀vl {l}{P}{Q} PlQ {s} (Ps , vl) =
  MAny-map⁻ Q Qs
  where
    ŝ = absS s
    l̂ = absL vl

    Qŝ : M.Any.Any Q (A.⟦ l̂ ⟧ ŝ)
    Qŝ = PlQ vl Ps

    Qs : M.Any.Any Q (absS <$> C.⟦ l ⟧ s)
    Qs = subst (M.Any.Any Q) (denot-abs {vl = vl}) Qŝ

-- ** alternative formulation using "strong" abstract Hoare triples
𝔸⟨_⟩_⊣_⟨_⟩ : (P : Pred₀ A.S) (l : C.L) → P ∘ absS ⊆¹ flip C.VL l → Pred₀ A.S → Type
𝔸⟨ P ⟩ l ⊣ P⇒ ⟨ Q ⟩ =
  (∀ {s} (p : (P ∘ absS) s) → (Q A.↑∘ A.⟦ absL (P⇒ p) ⟧) (absS s))

semi-soundness : ∀ {P Q : Pred₀ A.S} →
  ∀ (P⇒ : (P ∘ absS) ⊆¹ flip C.VL l) →
  ∙ 𝔸⟨ P ⟩ l ⊣ P⇒ ⟨ Q ⟩
    ───────────────────────────────────────────────────
    C.⟨ P ∘ absS ⟩ l ⟨ Q ∘ absS ⟩
semi-soundness {l}{P}{Q} P⇒ PlQ {s} Ps
  = MAny-map⁻ Q $ subst (M.Any.Any Q) (denot-abs {vl = vl}) Qs
  where
    vl = P⇒ Ps

    Qs : (Q A.↑∘ A.⟦ absL vl ⟧) (absS s)
    Qs = PlQ Ps


-- {P} lᵃ {Q}
-- ─────────────────────
-- {P ∘ abs} conc lᵃ {Q ∘ abs}

-- NB: conc either non-deterministic or canonical


{- old scribbles

abs : Pred₀ A.S → Pred₀ C.S
(abs P) s = P (concrete→abstract s)

-- abstraction : ∀ {s : A.S} (P : Pred₀ A.S) →
--   P s
--   ═══════
--   abs P s
-- abstraction = ?

-- ** inverse direction (aka reification)
abstract→concrete : A.S → C.S
abstract→concrete = {!!}
  where
    goT : A.T → C.Tx
    goT = {!!}

rei : Pred₀ C.S → Pred₀ A.S
(rei P) s = P (abstract→concrete s)

-- reification : ∀ {s : C.S} (P : Pred₀ C.S) →
--   P s
--   ════════════════════════
--   P (abstract→concrete s)
-- reification = ?

-- ** connecting both directions (although with abstract∘concrete≗id it's trivial)
sound-abstraction : ∀ {s : A.S} (P : Pred₀ A.S) →
  P s
  ════════════════════════════
  abs P (abstract→concrete s)
sound-abstraction = {!!}

sound-reification : ∀ {s : C.S} (P : Pred₀ C.S) →
  P s
  ════════════════════════════
  rei P (concrete→abstract s)
sound-reification = {!!}

-- sound : ∀ {s : C.S} (P : Pred₀ A.S) →
--   P (concrete→abstract s)

-- ** non-deterministic formulation
abstract→concrete∗ : A.S → List C.S
abstract→concrete∗ = {!!}
  where
    goT : A.T → List C.Tx
    goT = {!!}

rei∗ : Pred₀ C.S → Pred₀ A.S
(rei∗ P) s = P (abstract→concrete s)

-- ** relational formulation

data _-reifies-_ : C.S → A.S → Type where

𝕣ei : Pred₀ A.S → Pred₀ C.S
(𝕣ei P) cs = ∃ λ as → (cs -reifies- as) × P as

-- reification′ : ∀ {ss : A.S} {cs : C.S} (P : Pred₀ C.S)
--   → cs -reifies- as
--   → P s ↔ (𝕣ei P) cs
-- reification′ = ?
-}
