-------------------------
-- ** Axiomatic semantics

open import Prelude.Init hiding (_⇔_)
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.PartialMaps

module HoareLogic (Part : Set) {{_ : DecEq Part}} where

open import Ledger Part {{it}}

Monotone : Pred₀ (S → S)
Monotone f = ∀ s → s ⊆ᵈ f s

⟦⟧ₜ-mono : Monotone ⟦ t ⟧
⟦⟧ₜ-mono {A —→⟨ v ⟩ B} s p p∈ with s A | s B
... | nothing | _       = p∈
... | just _  | nothing = p∈
... | just vᵃ | just _  with v Nat.≤? vᵃ
... | no  _ = p∈
... | yes _ with p ≟ A
... | yes _ = auto
... | no  _ with p ≟ B
... | yes _ = auto
... | no  _ = p∈

⟦⟧ₗ-mono : Monotone ⟦ l ⟧
⟦⟧ₗ-mono {[]} _ _ = id
⟦⟧ₗ-mono {t ∷ l} s p = ⟦⟧ₗ-mono {l} (⟦ t ⟧ s) p ∘ ⟦⟧ₜ-mono {t} s p

data Assertion : Set₁ where
  `emp : Assertion
  _`↦_ : Part → ℕ → Assertion
  _`∗_ : Assertion → Assertion → Assertion
  _`∘⟦_⟧ : Assertion → L → Assertion

infixl 9 _`∘⟦_⟧
infixr 10 _`∗_
infix 11 _`↦_

private
  emp : Pred₀ S
  emp m = ∀ k → k ∉ᵈ m

  _∗_ : Pred₀ S → Pred₀ S → Pred₀ S
  (P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → (s₁ ∪ s₂ ≡ s) × P s₁ × Q s₂

⟦_⟧ᵖ : Assertion → Pred₀ S
⟦ `emp    ⟧ᵖ = emp
⟦ p `↦ n  ⟧ᵖ s = (s [ p ↦ n ]) × (∀ p′ → p′ ≢ p → p′ ∉ᵈ s)
⟦ P `∗ Q  ⟧ᵖ = ⟦ P ⟧ᵖ ∗ ⟦ Q ⟧ᵖ
⟦ P `∘⟦ l ⟧  ⟧ᵖ s = ⟦ P ⟧ᵖ $ ⟦ l ⟧ s

infixl 9 _`∘⟦_⟧ₜ
_`∘⟦_⟧ₜ : Assertion → Tx → Assertion
P `∘⟦ t ⟧ₜ = P `∘⟦ [ t ] ⟧

infix 1 _`⊢_
_`⊢_ : Assertion → Assertion → Set
P `⊢ Q = ⟦ P ⟧ᵖ ⊢ ⟦ Q ⟧ᵖ

_∙_ : Assertion → S → Set
P ∙ s = ⟦ P ⟧ᵖ s

variable
  P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

singleton′ : Part × ℕ → S
singleton′ (A , v) k with k ≟ A
... | yes refl = just v
... | no  k≢A  = nothing

singleton≡ : ⟦ A `↦ v ⟧ᵖ $ singleton′ (A , v)
singleton≡ {A}{v} = p₁ , p₂
  where
    p₁ : singleton′ (A , v) [ A ↦ v ]
    p₁ rewrite ≟-refl _≟_ A = refl

    p₂ : ∀ A′ → A′ ≢ A → A′ ∉ᵈ singleton′ (A , v)
    p₂ A′ A′≢ with A′ ≟ A
    ... | yes refl = ⊥-elim $ A′≢ refl
    ... | no  _    = M.All.nothing

data ⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Set₁ where

  base :
    ------------
    ⟨ P ⟩ [] ⟨ P ⟩

  step :
      ⟨ P ⟩ l ⟨ R ⟩
      -------------------------
    → ⟨ P `∘⟦ t ⟧ₜ ⟩ t ∷ l ⟨ R ⟩

  consequence :
      P′ `⊢ P
    → Q  `⊢ Q′
    → ⟨ P  ⟩ l ⟨ Q  ⟩
      ---------------
    → ⟨ P′ ⟩ l ⟨ Q′ ⟩

data ⟨_⟩_⟨_⟩′ : Assertion → L → Assertion → Set₁ where

  base :
    ----------------------------
    ⟨ P `∘⟦ t ⟧ₜ ⟩ [ t ] ⟨ P ⟩′

  step :
      ⟨ P ⟩ l  ⟨ Q ⟩′
    → ⟨ Q ⟩ l′ ⟨ R ⟩′
      --------------------
    → ⟨ P ⟩ l ++ l′ ⟨ R ⟩′

  consequence :
      P′ `⊢ P
    → Q  `⊢ Q′
    → ⟨ P ⟩ l ⟨ Q ⟩′
      ----------------
    → ⟨ P′ ⟩ l ⟨ Q′ ⟩′

-- utilities
weaken : P′ `⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken H = consequence H id

strengthen : Q `⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen H = consequence id H

axiom-base⋆ : ⟨ P `∘⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []}    = consequence {P = P} id id base
axiom-base⋆ {P = P} {l = t ∷ l} = consequence {P = P `∘⟦ l ⟧ `∘⟦ t ⟧ₜ} {Q = P} id id (step axiom-base⋆)

-- equivalences
axiom⇒denot : ⟨ P ⟩ l ⟨ Q ⟩ → (P `⊢ Q `∘⟦ l ⟧)
axiom⇒denot base = id
axiom⇒denot (step PlQ) = axiom⇒denot PlQ
axiom⇒denot (consequence P⊢P′ Q′⊢Q PlQ) = Q′⊢Q ∘ axiom⇒denot PlQ ∘ P⊢P′

denot⇒axiom : (P `⊢ Q `∘⟦ l ⟧) → ⟨ P ⟩ l ⟨ Q ⟩
denot⇒axiom {P = P} {Q = Q} {l = []} H =
  strengthen {Q = P} {Q′ = Q} H base
denot⇒axiom {P = P} {Q = Q} {l = t ∷ l} H =
  weaken {P′ = P} {P = Q `∘⟦ t ∷ l ⟧} H (axiom-base⋆ {P = Q} {l = t ∷ l})

axiom⇔denot : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (P `⊢ Q `∘⟦ l ⟧)
axiom⇔denot = axiom⇒denot , denot⇒axiom

axiom⇒oper : ⟨ P ⟩ l ⟨ Q ⟩ → (∀ {s s′} → P ∙ s → l , s —→⋆′ s′ → Q ∙ s′)
axiom⇒oper = (λ{ P⊢ Ps s→s′ → subst _ (proj₂ denot⇔oper s→s′) (P⊢ Ps)}) ∘ axiom⇒denot

oper⇒axiom : (∀ {s s′} → P ∙ s → l , s —→⋆′ s′ → Q ∙ s′) → ⟨ P ⟩ l ⟨ Q ⟩
oper⇒axiom = λ H → denot⇒axiom λ Ps → H Ps oper-base⋆

axiom⇔oper : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (∀ {s s′} → P ∙ s → l , s —→⋆′ s′ → Q ∙ s′)
axiom⇔oper = axiom⇒oper , oper⇒axiom

-- equational reasoning

step′ :
    ⟨ P ⟩ l  ⟨ Q ⟩
  → ⟨ Q ⟩ l′ ⟨ R ⟩
    -------------------
  → ⟨ P ⟩ l ++ l′ ⟨ R ⟩
step′ {P} {[]} {Q} {l′} {R} PlQ QlR = weaken (axiom⇒denot PlQ) QlR
step′ {.(_ `∘⟦ t ⟧ₜ)} {t ∷ l} {Q} {l′} {R} (step PlQ) QlR = step (step′ PlQ QlR)
step′ {P} {t ∷ l} {Q} {l′} {R} (consequence {P = P′}{Q = Q′} pre post PlQ) QlR = weaken pre p
  where
    p : ⟨ P′ ⟩ t ∷ l ++ l′ ⟨ R ⟩
    p = step′ PlQ (weaken post QlR)

module HoareReasoning where

  infix  -2 begin_
  infixr -1 _~⟨_⟩_
  infixr -1 _~⟨_∶-_⟩_
  infixr -1 _~⟨_∶-_⟩′_
  infix  0  _∎

  begin_ : ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q ⟩
  begin p = p

  _~⟨_⟩_ : ∀ P′ → P′ `⊢ P  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ l ⟨ R ⟩
  _ ~⟨ H ⟩ PlR = weaken H PlR

  _~⟨_⟩′_ : ∀ R′ → R `⊢ R′  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
  _ ~⟨ H ⟩′ PlR = strengthen H PlR

  _~⟨_∶-_⟩_ : ∀ P′ → (t : Tx) → ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  P′ ~⟨ t ∶- H ⟩ PlR = P′ ~⟨ (axiom⇒denot H) ⟩ step {t = t} PlR

  _~⟨_∶-_⟩′_ : ∀ P′ → (l : L) → ⟨ P′ ⟩ l ⟨ P ⟩ → ⟨ P ⟩ l′ ⟨ R ⟩ → ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩′ PlR = step′ H PlR

  _∎ : ∀ P → ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = base {P = p}
