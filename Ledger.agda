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
