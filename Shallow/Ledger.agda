open import Prelude.Init
open import Prelude.General
open Integer using () renaming (_-_ to _-ℤ_; _+_ to _+ℤ_)
open import Prelude.DecEq
open import Prelude.Sets

module Shallow.Ledger
  (Part : Set) -- a fixed set of participants
  ⦃ _ : DecEq Part ⦄
  where

-- The state of a ledger assigns a balance to each participant
S = Part → ℤ

-- A transaction is transferring money from one participant to another
data Tx : Set where
  _—→⟨_⟩_ : Part → ℤ → Part → Tx

-- A ledger is a list of transactions
L = List Tx

variable
  s s′ s″ : S
  t t′ t″ : Tx
  l l′ l″ : L
  ls ls′ ls″ : L × S

-- ** Denotational semantics

Domain = S → S

record Denotable (A : Set) : Set where
  field
    ⟦_⟧ : A → Domain
open Denotable {{...}} public

instance
  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ (p₁ —→⟨ n ⟩ p₂) s p =
    let prev = s p
    in  if p₁ == p₂ then
          prev
        else if p == p₁ then
          prev -ℤ n
        else if p == p₂ then
          prev +ℤ n
        else
          prev

  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      s = s
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ l ⟧ ∘ ⟦ t ⟧

lem : ∀ x → ⟦ t ∷ l ⟧ x ≡ (⟦ l ⟧ ∘ ⟦ t ⟧) x
lem _ = refl

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l′ ⟧ ∘ ⟦ l ⟧) x
comp {l = []}    {l′} x = refl
comp {l = t ∷ l} {l′} x rewrite lem {t}{l} x | comp {l}{l′} (⟦ t ⟧ x) = refl

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

comp′ : l       , s  —→⋆′ s′
      → l′      , s′ —→⋆′ s″
      → l ++ l′ , s  —→⋆′ s″
comp′ {l = []}    base                   s′→s″ = s′→s″
comp′ {l = _ ∷ _} (step singleStep s→s′) s′→s″ = step singleStep (comp′ s→s′ s′→s″)

oper-base⋆ : l , s —→⋆′ ⟦ l ⟧ s
oper-base⋆ {[]}    = base
oper-base⋆ {_ ∷ _} = step singleStep oper-base⋆

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

variable
  P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Predˢ

data ⟨_⟩_⟨_⟩ : Predˢ → L → Predˢ → Set₁ where

  base :
    --------------
    ⟨ P ⟩ [] ⟨ P ⟩
  --   -------------------------
  --   ⟨ P ∘ ⟦ t ⟧ ⟩ [ t ] ⟨ P ⟩

  step :
      ⟨ P ⟩ l ⟨ R ⟩
      -------------------------
    → ⟨ P ∘ ⟦ t ⟧ ⟩ t ∷ l ⟨ R ⟩
  --     ⟨ P ⟩ l  ⟨ Q ⟩
  --   → ⟨ Q ⟩ l′ ⟨ R ⟩
  --     -------------------
  --   → ⟨ P ⟩ l ++ l′ ⟨ R ⟩

  weaken-strengthen :

      P′ ⊢ P
    → Q  ⊢ Q′
    → ⟨ P  ⟩ l ⟨ Q  ⟩
      ---------------
    → ⟨ P′ ⟩ l ⟨ Q′ ⟩

-- utilities
axiom-base⋆ : ⟨ P ∘ ⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {l = []}    = base
axiom-base⋆ {l = _ ∷ _} = step axiom-base⋆

postulate
  ⟦⟧-comm : (⟦ t ⟧ ∘ ⟦ t′ ⟧) s ≡ (⟦ t′ ⟧ ∘ ⟦ t ⟧) s
-- ⟦⟧-comm {A —→⟨ n ⟩ B}{A′ —→⟨ n′ ⟩ B′} = {!!}

denot-comm : (⟦ t ⟧ ∘ ⟦ l ⟧) s ≡ (⟦ l ⟧ ∘ ⟦ t ⟧) s
denot-comm {t}{[]}    {s} = refl
denot-comm {t}{t′ ∷ l}{s}
  rewrite sym $ denot-comm {t′}{l}{s}
        | sym $ denot-comm {t′}{l}{⟦ t ⟧ s}
        | ⟦⟧-comm {t}{t′}{⟦ l ⟧ s}
        | denot-comm {t}{l}{s}
        | denot-comm {t}{l}{⟦ t′ ⟧ s}
        = refl

-- equivalences
axiom⇔denot : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (P ⊢ Q ∘ ⟦ l ⟧)
axiom⇔denot = axiom→denot , denot→axiom
  where
    axiom→denot : ⟨ P ⟩ l ⟨ Q ⟩ → (P ⊢ Q ∘ ⟦ l ⟧)
    axiom→denot base                              Ps = Ps
    axiom→denot (step PlQ)                        = axiom→denot PlQ
    axiom→denot (weaken-strengthen P⊢P′ Q′⊢Q PlQ) = Q′⊢Q ∘ axiom→denot PlQ ∘ P⊢P′

    denot→axiom : (P ⊢ Q ∘ ⟦ l ⟧) → ⟨ P ⟩ l ⟨ Q ⟩
    denot→axiom {l = []}    H = weaken-strengthen (λ x → x) H base
    denot→axiom {l = _ ∷ _} H = weaken-strengthen H (λ x → x) axiom-base⋆

axiom⇔oper : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′)
axiom⇔oper = (λ{ P⊢ Ps s→s′ → subst _ (proj₂ denot⇔oper s→s′) (P⊢ Ps) {-P⊢ Ps-}}) ∘ proj₁ axiom⇔denot
           , λ H → proj₂ axiom⇔denot λ Ps → H Ps oper-base⋆
-- axiom⇔oper = axiom→oper , oper→axiom
--   where
--     axiom→oper : ⟨ P ⟩ l ⟨ Q ⟩ → (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′)
--     axiom→oper base                              Ps base                   = Ps
--     axiom→oper (step PlQ)                        Ps (step singleStep s→s′) = axiom→oper PlQ Ps s→s′
--     axiom→oper (weaken-strengthen P⊢P′ Q′⊢Q PlQ) Ps s→s′                   = Q′⊢Q $ axiom→oper PlQ (P⊢P′ Ps) s→s′

--     oper→axiom : (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′) → ⟨ P ⟩ l ⟨ Q ⟩
--     oper→axiom {l = []}    H = weaken-strengthen (λ x → x) (flip H base) base
--     oper→axiom {l = _ ∷ _} H = weaken-strengthen (λ Ps → H Ps oper-base⋆) (λ x → x) axiom-base⋆

-- ** Separation logic

mod : L → Set⟨ Part ⟩
mod [] = ∅
mod (p₁ —→⟨ _ ⟩ p₂ ∷ l) = singleton p₁ ∪ singleton p₂ ∪ mod l

■_ : Set → Predˢ
■_ = const

_↦_ : Part → ℤ → Predˢ
(p ↦ z) s = s p ≡ z

_`∧_ : Predˢ → Predˢ → Predˢ
(P `∧ Q) s = P s × Q s

-- _♯_←_ : S → S → S → Set
-- s₁ ♯ s₂ ← s = {!!}
-- (s₁ ♯ s₂) × (s ≡ union s₁ s₂)
-- [STUCK] cannot express this using *shallow* Agda functions, need *deep* finite maps

-- inference rules

{-
[SEP-COMM] : P ∗ Q ⊣⊢ Q ∗ P
[SEP-COMM] = {!!} , {!!}

[SEP-ASSOC] : P ∗ (Q ∗ R) ⊣⊢ (P ∗ Q) ∗ R
[SEP-ASSOC] = {!!} , {!!}

[SEP-MONO] :
     P₁ ⊢ Q₁
   → P₂ ⊢ Q₂
     -----------------
   → P₁ ∗ P₂ ⊢ Q₁ ∗ Q₂
[SEP-MONO] P₁⊢Q₁ P₂⊢Q₂ = {!!}
-}

{-
postulate
  fv : Assertion → Set⟨ Part ⟩

[FRAME] :
    ⟨ P ⟩ l ⟨ Q ⟩
  → mod l ∩ fv R ≡ ∅
    -------------------------
  → ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
-}

-- ** Concurrent separation logic
{-
[INTERLEAVE]
    Interleaving l l′ l″
  → ⟨ P ⟩ l ⟨ Q ⟩
  → ⟨ P ⟩ l′ ⟨ Q ⟩
  → mod l ∩ mod l′ ≡ ∅
    ------------------------
  → ⟨ P ∗ P′ ⟩ l″ ⟨ Q ∗ Q′ ⟩
-}
