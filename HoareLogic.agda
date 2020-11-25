-------------------------
-- ** Axiomatic semantics

open import Function using (id)
open import Prelude.Init hiding (_⇔_)
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.PartialMaps

module HoareLogic (Part : Set) {{_ : DecEq Part}} where

open import Ledger Part

Predˢ = Pred S 0ℓ

record Transformerˢ : Set where
  field
    transform : S → S
    monotone  : ∀ s → s ⊆ᵈ transform s
open Transformerˢ public

⟦_⟧ₜ : Tx → Transformerˢ
transform ⟦ t ⟧ₜ = ⟦ t ⟧
monotone ⟦ A —→⟨ v ⟩ B ⟧ₜ s p p∈ with s A
... | nothing = p∈
... | just vᵃ with v Nat.≤? vᵃ
... | no  _ = p∈
... | yes _ with p ≟ A
... | yes _ = auto
... | no  _ with p ≟ B
... | yes _ = auto
... | no  _ = p∈

⟦_⟧ₗ : L → Transformerˢ
transform ⟦ l ⟧ₗ = ⟦ l ⟧
monotone  ⟦ [] ⟧ₗ s p = id
monotone  ⟦ t ∷ l ⟧ₗ s p = monotone ⟦ l ⟧ₗ (⟦ t ⟧ s) p ∘ monotone ⟦ t ⟧ₜ s p

data Assertion : Set₁ where
  `emp : Assertion
  _`↦_ : Part → ℕ → Assertion
  _`∗_ : Assertion → Assertion → Assertion
  _`∘_ : Assertion → Transformerˢ → Assertion

infixr 9 _`∘_
infixr 10 _`∗_
infix 11 _`↦_

private
  emp : Predˢ
  emp m = ∀ k → k ∉ᵈ m

  _∗_ : Predˢ → Predˢ → Predˢ
  (P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → (s₁ ∪ s₂ ≡ s) × P s₁ × Q s₂

⟦_⟧ᵖ : Assertion → Predˢ
⟦ `emp    ⟧ᵖ = emp
⟦ p `↦ n  ⟧ᵖ s = (s [ p ↦ n ]) × (∀ p′ → p′ ≢ p → p′ ∉ᵈ s)
⟦ P `∗ Q  ⟧ᵖ = ⟦ P ⟧ᵖ ∗ ⟦ Q ⟧ᵖ
⟦ P `∘ f  ⟧ᵖ = ⟦ P ⟧ᵖ ∘ f .transform

infix 1 _`⊢_
_`⊢_ : Assertion → Assertion → Set
P `⊢ Q = ⟦ P ⟧ᵖ ⊢ ⟦ Q ⟧ᵖ

_∙_ : Assertion → S → Set
P ∙ s = ⟦ P ⟧ᵖ s

variable
  P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

data ⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Set₁ where

  base :
    ------------
    ⟨ P ⟩ [] ⟨ P ⟩

  step :
      ⟨ P ⟩ l ⟨ R ⟩
      -------------------------
    → ⟨ P `∘ ⟦ t ⟧ₜ ⟩ t ∷ l ⟨ R ⟩

  weaken-strengthen :
      P′ `⊢ P
    → Q  `⊢ Q′
    → ⟨ P  ⟩ l ⟨ Q  ⟩
      ---------------
    → ⟨ P′ ⟩ l ⟨ Q′ ⟩

data ⟨_⟩_⟨_⟩′ : Assertion → L → Assertion → Set₁ where

  base :
    ----------------------------
    ⟨ P `∘ ⟦ t ⟧ₜ ⟩ [ t ] ⟨ P ⟩′

  step :
      ⟨ P ⟩ l  ⟨ Q ⟩′
    → ⟨ Q ⟩ l′ ⟨ R ⟩′
      --------------------
    → ⟨ P ⟩ l ++ l′ ⟨ R ⟩′

  weaken-strengthen :
      P′ `⊢ P
    → Q  `⊢ Q′
    → ⟨ P  ⟩ l ⟨ Q  ⟩′
      ----------------
    → ⟨ P′ ⟩ l ⟨ Q′ ⟩′

postulate
  step′ :
      ⟨ P ⟩ l  ⟨ Q ⟩
    → ⟨ Q ⟩ l′ ⟨ R ⟩
      -------------------
    → ⟨ P ⟩ l ++ l′ ⟨ R ⟩
-- step′ {P} {[]} {Q} {l′} {R} PlQ QlR = {!weaken-strengthen QlR!}
-- step′ {P} {x ∷ l} {Q} {l′} {R} PlQ QlR = {!step!}

-- utilities
axiom-base⋆ : ⟨ P `∘ ⟦ l ⟧ₗ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []}    = weaken-strengthen {P = P} id id base
axiom-base⋆ {P = P} {l = t ∷ l} = weaken-strengthen {P = (P `∘ ⟦ l ⟧ₗ) `∘ ⟦ t ⟧ₜ} {Q = P} id id (step axiom-base⋆)

-- equivalences
axiom⇔denot : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (P `⊢ Q `∘ ⟦ l ⟧ₗ)
axiom⇔denot = axiom→denot , denot→axiom
  where
    axiom→denot : ⟨ P ⟩ l ⟨ Q ⟩ → (P `⊢ Q `∘ ⟦ l ⟧ₗ)
    axiom→denot base                              Ps = Ps
    axiom→denot (step PlQ)                        = axiom→denot PlQ
    axiom→denot (weaken-strengthen P⊢P′ Q′⊢Q PlQ) = Q′⊢Q ∘ axiom→denot PlQ ∘ P⊢P′

    denot→axiom : (P `⊢ Q `∘ ⟦ l ⟧ₗ) → ⟨ P ⟩ l ⟨ Q ⟩
    denot→axiom {P = P} {Q = Q} {l = []}    H
      = weaken-strengthen {P = P} {Q = P} {Q′ = Q} id H base
    denot→axiom {P = P} {Q = Q} {l = t ∷ l} H
      = weaken-strengthen {P′ = P} {P = Q `∘ ⟦ t ∷ l ⟧ₗ} {Q = Q} {Q′ = Q} H id (axiom-base⋆ {P = Q} {l = t ∷ l})

--

module HoareReasoning where

  infix  -2 begin_
  infixr -1 _~⟨_⟩_
  infixr -1 _~⟨_∶-_⟩_
  infixr -1 _~⟨_∶-_⟩′_
  infix  0  _∎

  begin_ : ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q ⟩
  begin p = p

  _~⟨_⟩_ : ∀ P′ → P′ `⊢ P  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ l ⟨ R ⟩
  _ ~⟨ H ⟩ PlR = weaken-strengthen H (λ x → x) PlR

  _~⟨_∶-_⟩_ : ∀ P′ → (t : Tx) → ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  P′ ~⟨ t ∶- H ⟩ PlR = P′ ~⟨ (proj₁ axiom⇔denot H) ⟩ step {t = t} PlR

  _~⟨_∶-_⟩′_ : ∀ P′ → (l : L) → ⟨ P′ ⟩ l ⟨ P ⟩ → ⟨ P ⟩ l′ ⟨ R ⟩ → ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩′ PlR = step′ H PlR

  _∎ : ∀ P → ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = base {P = p}

axiom⇔oper : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (∀ {s s′} → P ∙ s → l , s —→⋆′ s′ → Q ∙ s′)
axiom⇔oper
  {- ** 1. proving from scratch -}
  -- = axiom→oper , oper→axiom
  -- where
  --   axiom→oper : ⟨ P ⟩ l ⟨ Q ⟩ → (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′)
  --   axiom→oper base                              Ps base                   = Ps
  --   axiom→oper (step PlQ)                        Ps (step singleStep s→s′) = axiom→oper PlQ Ps s→s′
  --   axiom→oper (weaken-strengthen P⊢P′ Q′⊢Q PlQ) Ps s→s′                   = Q′⊢Q $ axiom→oper PlQ (P⊢P′ Ps) s→s′

  --   oper→axiom : (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′) → ⟨ P ⟩ l ⟨ Q ⟩
  --   oper→axiom {l = []}    H = weaken-strengthen id (flip H base) base
  --   oper→axiom {l = _ ∷ _} H = weaken-strengthen (λ Ps → H Ps oper-base⋆) id axiom-base⋆

  {- ** 2. composing axiom⇔denot ∘ denot⇔oper -}
  = (λ{ P⊢ Ps s→s′ → subst _ (proj₂ denot⇔oper s→s′) (P⊢ Ps)}) ∘ proj₁ axiom⇔denot
  , λ H → proj₂ axiom⇔denot λ Ps → H Ps oper-base⋆
