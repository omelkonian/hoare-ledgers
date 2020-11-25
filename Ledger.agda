open import Function using (id)
open import Prelude.Init hiding (_⇔_)
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.PartialMaps as M

module Ledger
  (Part : Set) -- a fixed set of participants
  {{_ : DecEq Part}}
  where

--

variable
  ℓ ℓ′ ℓ″ : Level

  A B C D : Part
  v v′ v″ : ℕ

infix 0 _⇔_
infix 1 _⊢_

_⇔_ : Set ℓ → Set ℓ′ → Set _
A ⇔ B = (A → B) × (B → A)

_⊢_ : ∀ {A : Set ℓ} → (A → Set ℓ′) → (A → Set ℓ″) → Set _
P ⊢ Q = ∀ {x} → P x → Q x

_⊣⊢_ : ∀ {A : Set ℓ} → (A → Set ℓ′) → (A → Set ℓ″) → Set _
P ⊣⊢ Q = (P ⊢ Q) × (Q ⊢ P)

--

-- The state of a ledger is a collection of participants, along with their balance.
S : Set
S = Map⟨ Part ↦ ℕ ⟩

ex : S
ex = const nothing

-- A transaction is transferring money from one participant to another
record Tx : Set where
  constructor _—→⟨_⟩_
  field
    sender   : Part
    value    : ℕ
    receiver : Part
open Tx public

-- A ledger is a list of transactions
L = List Tx

variable
  s s′ s″ s₁ s₂ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

-- ** Denotational semantics

Domain = S → S

record Denotable (A : Set) : Set where
  field
    ⟦_⟧ : A → Domain
open Denotable {{...}} public

-- transfer
transfer : S → (Part × ℕ) → ℕ → Part → S
transfer s (A , vᵃ) v B k with k ≟ A
... | yes _ = just (vᵃ ∸ v)
... | no  _ with k ≟ B
... | yes _ = just (M.fromMaybe 0 (s B) + v)
... | no  _ = s k

_[_∣_↦_] : S → Part → ℕ → Part → S
s [ A ∣ v ↦ B ] with s A
... | nothing = s
... | just vᵃ with v Nat.≤? vᵃ
... | no _  = s
... | yes _ = transfer s (A , vᵃ) v B

--

instance
  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ (A —→⟨ v ⟩ B) = _[ A ∣ v ↦ B ]

  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      s = s
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ l ⟧ ∘ ⟦ t ⟧

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l′ ⟧ ∘ ⟦ l ⟧) x
comp {l = []}    {l′} x = refl
comp {l = t ∷ l} {l′} x rewrite comp {l}{l′} (⟦ t ⟧ x) = refl

-- ** Operational semantics

infix 0 _—→_ _—→⋆_ _—→⋆′_

data _—→_ : L × S → L × S → Set where
  singleStep :
     ------------------------
     t ∷ l , s —→ l , ⟦ t ⟧ s

data _—→′_ : L × S → S → Set where
  finalStep :
      --------------
      ([] , s) —→′ s

data _—→⋆_ : L × S → L × S → Set where
   base :
       ---------
       ls —→⋆ ls

   step :
       ls —→ ls′
     → ls′ —→⋆ ls″
       ----------
     → ls —→⋆ ls″

_—→⋆′_ : L × S → S → Set
ls —→⋆′ s = ls —→⋆ ([] , s)

comp′ :
    l       , s  —→⋆′ s′
  → l′      , s′ —→⋆′ s″
  → l ++ l′ , s  —→⋆′ s″
comp′ {l = []}    base                   s′→s″ = s′→s″
comp′ {l = _ ∷ _} (step singleStep s→s′) s′→s″ = step singleStep (comp′ s→s′ s′→s″)

oper-base⋆ : l , s —→⋆′ ⟦ l ⟧ s
oper-base⋆ {l = []}    = base
oper-base⋆ {l = _ ∷ _} = step singleStep oper-base⋆

-- ** Relating denotational and operational semantics

denot⇔oper : (⟦ l ⟧ s ≡ s′) ⇔ (l , s —→⋆′ s′)
denot⇔oper = denot→oper , oper→denot
  where
    denot→oper : (⟦ l ⟧ s ≡ s′) → (l , s —→⋆′ s′)
    denot→oper {l = []}    refl = base
    denot→oper {l = _ ∷ _} refl = step singleStep (denot→oper refl)

    oper→denot : (l , s —→⋆′ s′) → (⟦ l ⟧ s ≡ s′)
    oper→denot {l = .[]}   base                = refl
    oper→denot {l = _ ∷ _} (step singleStep p) = oper→denot p

-- ** Axiomatic semantics

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
  -- ↑_   : Predˢ → Assertion

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
-- ⟦ ↑ P     ⟧ᵖ = P

-- infixr 9 _`∘_
-- _`∘_ : Assertion → (S → S) → Assertion
-- P `∘ f = ↑ λ s → ⟦ P ⟧ᵖ (f s)

infix 1 _`⊢_
_`⊢_ : Assertion → Assertion → Set
P `⊢ Q = ⟦ P ⟧ᵖ ⊢ ⟦ Q ⟧ᵖ

_∙_ : Assertion → S → Set
P ∙ s = ⟦ P ⟧ᵖ s

variable
  P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

data ⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Set₁ where

  base :
    --
    ------------
    ⟨ P ⟩ [] ⟨ P ⟩
  --   -------------------------
  --   ⟨ P ∘ ⟦ t ⟧ ⟩ [ t ] ⟨ P ⟩

  step :
      ⟨ P ⟩ l ⟨ R ⟩
      -------------------------
    → ⟨ P `∘ ⟦ t ⟧ₜ ⟩ t ∷ l ⟨ R ⟩
  --     ⟨ P ⟩ l  ⟨ Q ⟩
  --   → ⟨ Q ⟩ l′ ⟨ R ⟩
  --     -------------------
  --   → ⟨ P ⟩ l ++ l′ ⟨ R ⟩

  weaken-strengthen :

      P′ `⊢ P
    → Q  `⊢ Q′
    → ⟨ P  ⟩ l ⟨ Q  ⟩
      ---------------
    → ⟨ P′ ⟩ l ⟨ Q′ ⟩

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

-- ** Separation logic

mod : Part → L → Set
mod A = Any λ t → A ∈ (sender t ∷ receiver t ∷ [])

addr : Part → Assertion → Set
addr A `emp     = ⊥
addr A (B `↦ _) = A ≡ B
addr A (P `∗ Q) = addr A P ⊎ addr A Q
addr A (P `∘ _) = addr A P

_ˡ♯_ : L → S → Set
l ˡ♯ s = ∀ A → mod A l → A ∉ᵈ s

_♯ˡ_ : S → L → Set
s ♯ˡ l = ∀ A → A ∈ᵈ s → ¬ mod A l

_♯♯_ : L → Assertion → Set
l ♯♯ P = ∀ A → mod A l → ¬ addr A P

_♯♯′_ : L → S → Set
l ♯♯′ s = ∀ A → mod A l → A ∉ᵈ s

-- Lemmas about separation

MAll⇒¬MAny : ∀ {A : Set} {m : Maybe A} → M.All.All (const ⊥) m → ¬ M.Any.Any (const ⊤) m
MAll⇒¬MAny {m = nothing} M.All.nothing = λ ()

∉¬ : A ∉ᵈ s → ¬ A ∈ᵈ s
∉¬ {A}{s} A∉ A∈ with s A | A∉ | A∈
... | just _  | M.All.just () | _

¬∉ : ¬ A ∈ᵈ s → A ∉ᵈ s
¬∉ {A}{s} ¬A∈ with s A
... | nothing = M.All.nothing
... | just _  = ⊥-elim $ ¬A∈ (M.Any.just tt)

∈ᵈ-∪ : s₁ ∪ s₂ ≡ s → A ∈ᵈ s → A ∈ᵈ s₁ ⊎ A ∈ᵈ s₂
∈ᵈ-∪ {s₁}{s₂}{s}{A} (s₁♯s₂ , p) A∈
  with s A | A∈ | s₁ A | s₂ A | inspect s₂ A | p A
... | nothing | () | _       | _       | _        | _
... | just _  | _  | just _  | _       | _        | _  = inj₁ $ M.Any.just tt
... | just _  | _  | _       | just _  | _        | _  = inj₂ $ M.Any.just tt
... | just v  | _  | nothing | nothing | ≡[ s₂≡ ] | pA = case subst (_≡ just v) s₂≡ pA of λ ()

∈⇒addr : A ∈ᵈ s → P ∙ s → addr A P
∈⇒addr {A}{s}{P = `emp} A∈ Ps = ⊥-elim $ ∉¬ {A}{s} (Ps A) A∈
∈⇒addr {A}{s}{P = B `↦ v} A∈ Ps with A ≟ B
... | yes A≡B = A≡B
... | no  A≢B = ⊥-elim $ ∉¬ {A}{s} (proj₂ Ps A A≢B) A∈
∈⇒addr {A}{s}{P = P `∗ Q} A∈ (s₁ , s₂ , ≡s , Ps₁ , Qs₂)
  with ∈ᵈ-∪ ≡s A∈
... | inj₁ A∈₁ = inj₁ $ ∈⇒addr {P = P} A∈₁ Ps₁
... | inj₂ A∈₂ = inj₂ $ ∈⇒addr {P = Q} A∈₂ Qs₂
∈⇒addr {A}{s}{P = P `∘ f} A∈ Ps = ∈⇒addr {P = P} (f .monotone s A A∈) Ps

♯♯-skip : (t ∷ l) ♯♯ P → l ♯♯ P
♯♯-skip p A = p A ∘ there

ˡ♯⇒♯ˡ : l ˡ♯ s → s ♯ˡ l
ˡ♯⇒♯ˡ {s = s} p A A∈s A∈l with s A | p A A∈l | A∈s
... | nothing | _             | ()
... | just _  | M.All.just () | _

∉-splits : s₁ ∪ s₂ ≡ s → A ∉ᵈ s₁ → A ∉ᵈ s₂ → A ∉ᵈ s
∉-splits {s₁ = s₁}{s₂}{s}{A} (s₁♯s₂ , p) A∉₁ A∉₂
  with s₁ A | s₂ A | inspect s₂ A | A∉₁ | A∉₂ | s A | p A
... | just _  | _       | _        | M.All.just () | _             | _       | _
... | _       | just _  | _        | _             | M.All.just () | _       | _
... | nothing | nothing | _        | _             | _             | nothing | _
    = M.All.nothing
... | nothing | nothing | ≡[ s₂≡ ] | _             | _             | just v  | pA
    = case subst (_≡ just v) s₂≡ pA of λ ()

♯♯⇒ˡ♯ : l ♯♯ R → R ∙ s → l ˡ♯ s
♯♯⇒ˡ♯ {l}{`emp}{s} l♯R s∅ A A∈ = s∅ A
♯♯⇒ˡ♯ {l}{B `↦ v}{s} l♯R B↦ A A∈
  with A ≟ B
... | yes refl = ⊥-elim $ l♯R A A∈ refl
... | no  A≢B  = proj₂ B↦ A A≢B
♯♯⇒ˡ♯ {l}{R `∗ Q}{s} l♯R (s₁ , s₂ , ≡s , Rs₁ , Qs₂) A A∈
  with s₁ A | inspect s₁ A | s₂ A | inspect s₂ A
... | just _  | ≡[ s₁≡ ] | _       | _
    = ⊥-elim $ l♯R A A∈ $ inj₁ $ ∈⇒addr {A}{s₁}{R} (subst M.Is-just (sym s₁≡) auto) Rs₁
... | _       | _        | just _  | ≡[ s₂≡ ]
    = ⊥-elim $ l♯R A A∈ $ inj₂ $ ∈⇒addr {A}{s₂}{Q} (subst M.Is-just (sym s₂≡) auto) Qs₂
... | nothing | ≡[ s₁≡ ] | nothing | ≡[ s₂≡ ]
    = ∉-splits ≡s (subst M.Is-nothing (sym s₁≡) auto) (subst M.Is-nothing (sym s₂≡) auto)

♯♯⇒ˡ♯ {l}{R `∘ f}{s} l♯R Rs A A∈ = ¬∉ {A}{s} ¬A∈
  where
    A∉ : A ∉ᵈ f .transform s
    A∉ = ♯♯⇒ˡ♯ {R = R} {s = f .transform s} l♯R Rs A A∈

    ¬A∈ : ¬ A ∈ᵈ s
    ¬A∈ = ∉¬ {A}{f .transform s} A∉ ∘ f .monotone s A

-- Helper lemmas for [FRAME]

transfer-helper :
    s₁ ♯ s₂
  → B ∉ᵈ s₂
    ---------------------
  → (s₁ [ A ∣ v ↦ B ]) ♯ s₂
transfer-helper {s₁ = s₁}{s₂}{B}{A}{v} s₁♯s₂ B∉ with s₁ A | inspect s₁ A
... | nothing | _  = s₁♯s₂
... | just vᵃ | ≡[ A∈ ] with v Nat.≤? vᵃ
... | no  _ = s₁♯s₂
... | yes _ = λ k → go k
  where
    go : transfer s₁ (A , vᵃ) v B ♯ s₂
    go k with k ≟ A
    ... | yes refl =
      let (p , p′) = s₁♯s₂ A
      in  (λ _ → p (subst (M.Any.Any (const ⊤)) (sym A∈) auto))
        , λ A∈′ → case (subst (M.All.All (const ⊥)) A∈ (p′ A∈′)) of λ{ (M.All.just ()) }
    ... | no _ with k ≟ B
    ... | yes refl =
      let (p , p′) = s₁♯s₂ B
      in  (λ _ → B∉) , ⊥-elim ∘ MAll⇒¬MAny B∉
    ... | no _ = s₁♯s₂ k

drop-[∣↦] : ∀ k → k ≢ A → k ≢ B → (s [ A ∣ v ↦ B ]) k ≡ s k
drop-[∣↦] {A = A}{B}{s}{v} k k≢A k≢B with s A
... | nothing = refl
... | just vᵃ with v Nat.≤? vᵃ
... | no _  = refl
... | yes _ with k ≟ A
... | yes eq = ⊥-elim $ k≢A eq
... | no  _ with k ≟ B
... | yes eq = ⊥-elim $ k≢B eq
... | no  _ = refl

frame-helper :
    l ♯♯ R
  → R ∙ s₂
  → s₁ ∪ s₂ ≡ s
    -----------------------
  → ⟦ l ⟧ s₁ ∪ s₂ ≡ ⟦ l ⟧ s
frame-helper {l = []} _ _ p = p
frame-helper {l = l₀@(A —→⟨ v ⟩ B ∷ l)}{R}{s₂}{s₁}{s} l♯R Rs₂ (s₁♯s₂ , ≡s) =
  frame-helper {l}{R}{s₂}{s₁ [ A ∣ v ↦ B ]} {s [ A ∣ v ↦ B ]} (♯♯-skip {P = R} l♯R) Rs₂ p′
  where
    l♯s₂ : l₀ ˡ♯ s₂
    l♯s₂ = ♯♯⇒ˡ♯ {R = R} l♯R Rs₂

    A∉ : A ∉ᵈ s₂
    A∉ = l♯s₂ A $ here (here refl)

    B∉ : B ∉ᵈ s₂
    B∉ = l♯s₂ B $ here (there (here refl))

    p₁ : (s₁ [ A ∣ v ↦ B ]) ♯ s₂
    p₁ = transfer-helper s₁♯s₂ B∉

    ∉⇒≢ : ∀ k → k ∈ᵈ s₂ → (k ≢ A) × (k ≢ B)
    ∉⇒≢ k k∈ = k≢A , k≢B
      where
        k∉ : ¬ mod k l₀
        k∉ = ˡ♯⇒♯ˡ l♯s₂ k k∈

        k≢A : k ≢ A
        k≢A refl = ⊥-elim $ k∉ (here (here refl))

        k≢B : k ≢ B
        k≢B refl = ⊥-elim $ k∉ (here (there (here refl)))

    p₂ : ∀ k → ((s₁ [ A ∣ v ↦ B ]) ∪ s₂ ∶- p₁) k ≡ (s [ A ∣ v ↦ B ]) k
    p₂ k
      with eq ← ≡s k
      with eqᵃ ← ≡s A
      with eqᵇ ← ≡s B
      with Dec (k ∈ᵈ s₂) ∋ dec
    ... | yes k∈
      with k≢A , k≢B ← ∉⇒≢ k k∈
      rewrite ∪-chooseᵣ p₁ k∈
            | ∪-chooseᵣ s₁♯s₂ k∈
            | drop-[∣↦] {s = s} {v = v} k k≢A k≢B
            = eq
    ... | no ¬k∈
      with k∉ ← ¬∉ {k}{s₂} ¬k∈
      rewrite ∪-chooseₗ p₁ k∉
            | ∪-chooseₗ s₁♯s₂ k∉
      with s₁ A | s₂ A | A∉ | inspect s₂ A | s A | eqᵃ
    ... | nothing | just _  | M.All.just () | _          | _          | _
    ... | nothing | nothing | _             | ≡[ s₂≡ ]   | just _     | eqᵃ′
        = case trans (sym s₂≡) eqᵃ′ of λ ()
    ... | nothing | nothing | _             | _          | nothing    | _
        = eq
    ... | just vᵃ | _       | _             | _          | .(just vᵃ) | refl
      with v ≤? vᵃ
    ... | no  _ = eq
    ... | yes _
      with k ≟ A
    ... | yes k≡A = refl
    ... | no  k≢A
      with k ≟ B
    ... | no  k≢b = eq
    ... | yes k≡B
      with s₁ B | s₂ B | B∉ | inspect s₂ B | s B | eqᵇ
    ... | nothing | just _  | M.All.just () | _          | _          | _
    ... | nothing | nothing | _             | ≡[ s₂≡ ]   | just _     | eqᵇ′
        = case trans (sym s₂≡) eqᵇ′ of λ ()
    ... | nothing | nothing | _             | _          | nothing    | _
        = refl
    ... | just vᵇ | _       | _             | _          | .(just vᵇ) | refl
        = refl

    p′ : (s₁ [ A ∣ v ↦ B ]) ∪ s₂ ≡ (s [ A ∣ v ↦ B ])
    p′ = p₁ , p₂

[FRAME] :
    ⟨ P ⟩ l ⟨ Q ⟩
  → l ♯♯ R
    -----------------------
  → ⟨ P `∗ R ⟩ l ⟨ Q `∗ R ⟩
[FRAME] {P}{l}{Q}{R} PlQ sep = proj₂ axiom⇔denot d
  where
    d : (P `∗ R) `⊢ (Q `∗ R) `∘ ⟦ l ⟧ₗ
    d {s} (s₁ , s₂ , s₁♯s₂ , Ps₁ , Rs₂) = ⟦ l ⟧ s₁ , s₂  , p , Qs₁′ , Rs₂
      where
        Qs₁′ : Q ∙ ⟦ l ⟧ s₁
        Qs₁′ = proj₁ axiom⇔denot PlQ Ps₁

        p : ⟦ l ⟧ s₁ ∪ s₂ ≡ ⟦ l ⟧ s
        p = frame-helper {R = R} sep Rs₂ s₁♯s₂

-- {-
-- -- ** Concurrent separation logic
-- open import Data.List.Relation.Ternary.Interleaving
-- _∥_←_ : L → L → L → Set
-- l₁ ∥ l₂ ← l = Interleaving _≡_ _≡_ l₁ l₂ l

-- h :
--     s₁ ♯ s₂ ← s
--   → l₁ ∥ l₂ ← l
--   → mod l₁ S.♯ mod l₂
--     -------------------------------
--   → ⟦ l₁ ⟧ s₁ ♯ ⟦ l₂ ⟧ s₂ ← ⟦ l ⟧ s
-- h {s₁}{s₂}{s}{l₁}{l₂}{l} s₁♯s₂ l₁∥l₂ l₁♯l₂ = h₁ , h₂
--   where
--     ps₁ = proj₁ (⟦ l₁ ⟧ s₁)
--     ps₂ = proj₁ (⟦ l₂ ⟧ s₂)

--     All∉ : All (_∉′ ps₂) (list ps₁)
--     All∉ = {!!}

--     h₁ : ⟦ l₁ ⟧ s₁ ♯ ⟦ l₂ ⟧ s₂
--     h₁ = let p = L.filter-none (_∈′? ps₂) {xs = list ps₁} All∉ in {!!} -- subst _ p refl

--     h₂ : ⟦ l ⟧ s ≡ᵐ union (⟦ l₁ ⟧ s₁) (⟦ l₂ ⟧ s₂)
--     h₂ = {!!}

-- [INTERLEAVE] :
--     l₁ ∥ l₂ ← l
--   → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
--   → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
--   → mod l₁ S.♯ mod l₂
--   -- → fv P₁ ∪ fv Q₁ S.♯ mod l₂
--   -- → fv P₂ ∪ fv Q₂ S.♯ mod l₁
--     ---------------------------
--   → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩

-- [INTERLEAVE] {l₁}{l₂}{l}{P₁}{Q₁}{P₂}{Q₂} l₁∥l₂ PlQ PlQ′ l₁♯l₂ = proj₂ axiom⇔denot d
--   where
--     d : (P₁ `∗ P₂) `⊢ (Q₁ `∗ Q₂) `∘ ⟦ l ⟧
--     d {s} (s₁ , s₂ , s₁♯s₂ , Ps₁ , Ps₂) = _ , _ , q , q₁ , q₂
--       where
--         q₁ : Q₁ ∙ ⟦ l₁ ⟧ s₁
--         q₁ = proj₁ axiom⇔denot PlQ Ps₁

--         q₂ : Q₂ ∙ ⟦ l₂ ⟧ s₂
--         q₂ = proj₁ axiom⇔denot PlQ′ Ps₂

--         q : ⟦ l₁ ⟧ s₁ ♯ ⟦ l₂ ⟧ s₂ ← ⟦ l ⟧ s
--         q = {!!} -- h s₁♯s₂ l₁∥l₂ l₁♯l₂
-- -}
