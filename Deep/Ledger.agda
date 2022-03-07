{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.General
open Integer using () renaming (_-_ to _-ℤ_; _+_ to _+ℤ_)
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Maps hiding (∅; singleton) renaming (_∪_ to _∪ᵐ_)
open import Prelude.Lists
open import Prelude.Apartness

module Deep.Ledger
  (Part : Set) -- a fixed set of participants
  ⦃ _ : DecEq Part ⦄
  where

-- The state of a ledger is a collection of participants, along with their balance.
S : Set
S = Map⟨ Part ↦ ℤ ⟩

-- A transaction is transferring money from one participant to another
data Tx : Set where
  _—→⟨_⟩_ : Part → ℤ → Part → Tx

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

instance
  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ (p₁ —→⟨ n ⟩ p₂) s = modify p₂ (_+ℤ n) $ modify p₁ (_-ℤ n) s

  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      = id
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
{-
-- the shallow embedding of predicates seems to break here..
-- ..we really need to get ahold of the actual variables, i.e. from a deeply-embedded DSL
fv : Predˢ → Set⟨ Part ⟩
fv P = {!!}
-}

data Assertion : Set where
  `emp `⊥ : Assertion
  -- _`≡_ : ℤ → ℤ → Assertion
  _`↦_ : Part → ℤ → Assertion
  _`∗_ _`—∗_ : Assertion → Assertion → Assertion
  _`∘_ : Assertion → (S → S) → Assertion

infixr 9 _`∘_

fv : Assertion → Set⟨ Part ⟩
fv `emp      = ∅
fv `⊥        = ∅
-- fv (_ `≡ _) = ∅
fv (p `↦ _)  = singleton p
fv (P `∗ Q)  = fv P ∪ fv Q
fv (P `—∗ Q) = fv P ∪ fv Q
fv (P `∘ _)  = fv P

emp : Predˢ
emp s = ∀ k → k ∉ᵈ s

_♯_←_ : S → S → S → Set
s₁ ♯ s₂ ← s = ⟨ s₁ ⊎ s₂ ⟩≡ s

_∗_ : Predˢ → Predˢ → Predˢ
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → (s₁ ♯ s₂ ← s) × P s₁ × Q s₂

_—∗_ : Predˢ → Predˢ → Predˢ
(P —∗ Q) s = ∀ s′ → s′ ♯ s → P s′ → Q (s ∪ᵐ s′)

⟦_⟧ᵖ : Assertion → Predˢ
⟦ `emp    ⟧ᵖ = emp
⟦ `⊥      ⟧ᵖ = const ⊥
-- ⟦ x `≡ y  ⟧ᵖ = {!!}
⟦ p `↦ n  ⟧ᵖ = _[ p ↦ n ]
⟦ P `∗ Q  ⟧ᵖ = ⟦ P ⟧ᵖ ∗ ⟦ Q ⟧ᵖ
⟦ P `—∗ Q ⟧ᵖ = ⟦ P ⟧ᵖ —∗ ⟦ Q ⟧ᵖ
⟦ P `∘ f  ⟧ᵖ = ⟦ P ⟧ᵖ ∘ f

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
    → ⟨ P `∘ ⟦ t ⟧ ⟩ t ∷ l ⟨ R ⟩
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
axiom-base⋆ : ⟨ P `∘ ⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []}    = weaken-strengthen {P = P} id id base
axiom-base⋆ {P = P} {l = t ∷ l} = weaken-strengthen {P = (P `∘ ⟦ l ⟧) `∘ ⟦ t ⟧} id id (step axiom-base⋆)

⟦⟧-comm : (⟦ t ⟧ ∘ ⟦ t′ ⟧) s ≡ (⟦ t′ ⟧ ∘ ⟦ t ⟧) s
⟦⟧-comm {t = A —→⟨ n ⟩ B}{t′ = A′ —→⟨ n′ ⟩ B′} = {!!}

denot-comm : (⟦ t ⟧ ∘ ⟦ l ⟧) s ≡ (⟦ l ⟧ ∘ ⟦ t ⟧) s
denot-comm {t = t}{l = []}    {s} = refl
denot-comm {t = t}{l = t′ ∷ l}{s}
  rewrite sym $ denot-comm {t′}{l}{s}
        | sym $ denot-comm {t′}{l}{⟦ t ⟧ s}
        | ⟦⟧-comm {t}{t′}{⟦ l ⟧ s}
        | denot-comm {t}{l}{s}
        | denot-comm {t}{l}{⟦ t′ ⟧ s}
        = refl

-- equivalences
axiom⇔denot : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (P `⊢ Q `∘ ⟦ l ⟧)
axiom⇔denot = axiom→denot , denot→axiom
  where
    axiom→denot : ⟨ P ⟩ l ⟨ Q ⟩ → (P `⊢ Q `∘ ⟦ l ⟧)
    axiom→denot base                              Ps = Ps
    axiom→denot (step PlQ)                        = axiom→denot PlQ
    axiom→denot (weaken-strengthen P⊢P′ Q′⊢Q PlQ) = Q′⊢Q ∘ axiom→denot PlQ ∘ P⊢P′

    denot→axiom : (P `⊢ Q `∘ ⟦ l ⟧) → ⟨ P ⟩ l ⟨ Q ⟩
    denot→axiom {P = P} {Q = Q} {l = []}    H
      = weaken-strengthen {P = P} {Q = P} {Q′ = Q} id H base
    denot→axiom {P = P} {Q = Q} {l = t ∷ l} H
      = weaken-strengthen {P′ = P} {P = Q `∘ ⟦ t ∷ l ⟧} {Q = Q} {Q′ = Q} H id (axiom-base⋆ {P = Q} {l = t ∷ l})

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

mod : L → Set⟨ Part ⟩
mod [] = ∅
mod (p₁ —→⟨ _ ⟩ p₂ ∷ l) = singleton p₁ ∪ singleton p₂ ∪ mod l

-- ⟦⟧-constᵗ : dom (⟦ t ⟧ s) ≡ dom s
-- ⟦⟧-constᵗ {t = p —→⟨ n ⟩ p′}    = refl

-- ⟦⟧-const : ∀ {s} {l : L} → dom (⟦ l ⟧ s) ≡ dom s
-- ⟦⟧-const {s = _} {l = []}    = refl
-- ⟦⟧-const {s = s} {l = t ∷ l} rewrite ⟦⟧-const {⟦ t ⟧ s}{l} = ⟦⟧-constᵗ {t}{s}

⟦⟧-union :
    ⟨ s₁ ⊎ s₂ ⟩≡ s
    --------------------------------------
  → ⟨ ⟦ l ⟧ s₁ ⊎ ⟦ l ⟧ s₂ ⟩≡ ⟦ l ⟧ s
⟦⟧-union s₁⊎s₂ = {!!} , {!!}

postulate
  ⟦⟧-♯ :
      s₁ ♯ s₂ ← s
      -----------------------------
    → ⟦ l ⟧ s₁ ♯ ⟦ l ⟧ s₂ ← ⟦ l ⟧ s

-- update-emptyᵗ : proj₁ s ≡ ∅ → ⟦ t ⟧ s ≡ s
-- update-emptyᵗ {.(⟨ [] ⟩∶- _) , snd} {x —→⟨ x₁ ⟩ x₂} refl = {!!}

-- update-empty : proj₁ s ≡ ∅ → ⟦ l ⟧ s ≡ s
-- update-empty {s}{[]}    refl = refl
-- update-empty {s}{t ∷ l} refl rewrite update-emptyᵗ {s}{t} refl = {!!}
-- rewrite update-empty {⟦ t ⟧ s}{l} (update-emptyᵗ {s}{t} refl) = refl

frame :
    mod l ♯ fv R
  → R ∙ s
    -----------
  → R ∙ ⟦ l ⟧ s
frame = {!!}
-- frame {l} {`emp}    {.(⟨ [] ⟩∶- _) , _} _ refl = subst (`emp ∙_) (sym $ update-empty {l = l} refl) refl
-- frame {l} {p `↦ v} {s} mod♯ (p∈ , p≡) = {!!}
-- frame {l} {P `∗ Q}  {s} mod♯ Rs = {!!}
-- frame {l} {P `—∗ Q} {s} mod♯ Rs = {!!}
-- frame {l} {P `∘ f}  {s} mod♯ Rs = {!!}
-- frame {[]} {R} {s} mod♯fv Rs = Rs
-- frame {(p —→⟨ n ⟩ p′) ∷ l} {R} {s} mod♯fv Rs = {!!}

-- need deeply-embedded Predˢ for fv
[FRAME] :
    ⟨ P ⟩ l ⟨ Q ⟩
  → mod l ♯ fv R
    -----------------------
  → ⟨ P `∗ R ⟩ l ⟨ Q `∗ R ⟩
[FRAME] {P}{l}{Q}{R} PlQ mod♯fv = proj₂ axiom⇔denot d
  where
    d : (P `∗ R) `⊢ (Q `∗ R) `∘ ⟦ l ⟧
    d {s} (s₁ , s₂ , s₁♯s₂ , Ps₁ , Rs₂) = ⟦ l ⟧ s₁ , ⟦ l ⟧ s₂ , p , Qs₁′ , Rs₂′
    {-
      s = s₁ ⊎ s₂
      —→ ⟦l⟧s = ⟦l⟧s₁ ⊎ ⟦l⟧s₂
      P s₁
      —→ Q ⟦l⟧s₁
      R s₂
      —→ R ⟦l⟧s₂

         ⟦l⟧s = ⟦l⟧s₁ ⊎ ⟦l⟧s₂     Q ⟦l⟧s₁      R ⟦l⟧s₂
      ----------------------------------------------------
                          (Q ∗ R) ⟦l⟧s
    -}
      where
        Qs₁′ : Q ∙ ⟦ l ⟧ s₁
        Qs₁′ = proj₁ axiom⇔denot PlQ Ps₁

        Rs₂′ : R ∙ ⟦ l ⟧ s₂
        Rs₂′ = frame {l = l} {R = R} {s = s₂} mod♯fv Rs₂

        p : ⟦ l ⟧ s₁ ♯ ⟦ l ⟧ s₂ ← ⟦ l ⟧ s
        p = ⟦⟧-♯ {s₁}{s₂}{s}{l} s₁♯s₂
{-

-- ** Concurrent separation logic
open import Data.List.Relation.Ternary.Interleaving
_∥_←_ : L → L → L → Set
l₁ ∥ l₂ ← l = Interleaving _≡_ _≡_ l₁ l₂ l

h :
    s₁ ♯ s₂ ← s
  → l₁ ∥ l₂ ← l
  → mod l₁ S.♯ mod l₂
    -------------------------------
  → ⟦ l₁ ⟧ s₁ ♯ ⟦ l₂ ⟧ s₂ ← ⟦ l ⟧ s
h {s₁}{s₂}{s}{l₁}{l₂}{l} s₁♯s₂ l₁∥l₂ l₁♯l₂ = h₁ , h₂
  where
    ps₁ = proj₁ (⟦ l₁ ⟧ s₁)
    ps₂ = proj₁ (⟦ l₂ ⟧ s₂)

    All∉ : All (_∉′ ps₂) (list ps₁)
    All∉ = {!!}

    h₁ : ⟦ l₁ ⟧ s₁ ♯ ⟦ l₂ ⟧ s₂
    h₁ = let p = L.filter-none (_∈′? ps₂) {xs = list ps₁} All∉ in {!!} -- subst _ p refl

    h₂ : ⟦ l ⟧ s ≡ᵐ union (⟦ l₁ ⟧ s₁) (⟦ l₂ ⟧ s₂)
    h₂ = {!!}

[INTERLEAVE] :
    l₁ ∥ l₂ ← l
  → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
  → mod l₁ S.♯ mod l₂
  -- → fv P₁ ∪ fv Q₁ S.♯ mod l₂
  -- → fv P₂ ∪ fv Q₂ S.♯ mod l₁
    ---------------------------
  → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩

[INTERLEAVE] {l₁}{l₂}{l}{P₁}{Q₁}{P₂}{Q₂} l₁∥l₂ PlQ PlQ′ l₁♯l₂ = proj₂ axiom⇔denot d
  where
    d : (P₁ `∗ P₂) `⊢ (Q₁ `∗ Q₂) `∘ ⟦ l ⟧
    d {s} (s₁ , s₂ , s₁♯s₂ , Ps₁ , Ps₂) = _ , _ , q , q₁ , q₂
      where
        q₁ : Q₁ ∙ ⟦ l₁ ⟧ s₁
        q₁ = proj₁ axiom⇔denot PlQ Ps₁

        q₂ : Q₂ ∙ ⟦ l₂ ⟧ s₂
        q₂ = proj₁ axiom⇔denot PlQ′ Ps₂

        q : ⟦ l₁ ⟧ s₁ ♯ ⟦ l₂ ⟧ s₂ ← ⟦ l ⟧ s
        q = {!!} -- h s₁♯s₂ l₁∥l₂ l₁♯l₂
-}
