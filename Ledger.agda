open import Function using (id)
open import Prelude.Init hiding (_⇔_)
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Maps

module Ledger
  (Part : Set) -- a fixed set of participants
  ⦃ _ : DecEq Part ⦄
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
open Denotable ⦃...⦄ public

-- NB: a transaction goes through only when:
--   1. both participants are present in the domain
--   2. the sender holds sufficient funds
[_∣_↦_] : Part → ℕ → Part → Cmd
[ A ∣ v ↦ B ] =
  just? A λ vᵃ →
  just? B λ vᵇ →
  iff (v ≤? vᵃ)
  ((A ≔ vᵃ ∸ v) ∶ (B ≔ vᵇ + v))

--

instance
  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ (A —→⟨ v ⟩ B) = run [ A ∣ v ↦ B ]

  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      s = s
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ l ⟧ ∘ ⟦ t ⟧

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l′ ⟧ ∘ ⟦ l ⟧) x
comp {l = []}    {l′} x = refl
comp {l = t ∷ l} {l′} x rewrite comp {l}{l′} (⟦ t ⟧ x) = refl

transfer : ∀ {A B v v′}
  → A ≢ B
  → run [ A ∣ v ↦ B ] (singleton (A , v) ∪ singleton (B , v′))
  ≈ (singleton (A , 0) ∪ singleton (B , v′ + v))
transfer {A}{B}{v}{v′} A≢B =
  let
    m = singleton (A , v) ∪ singleton (B , v′)
  in
  begin
    run [ A ∣ v ↦ B ] m
  ≡⟨⟩
    run (just? A λ vᵃ → just? B λ vᵇ → iff (v ≤? vᵃ) ((A ≔ vᵃ ∸ v) ∶ (B ≔ vᵇ + v))) m
  ≈⟨ just?-accept (↦-∪⁺ˡ singleton-law′) ⟩
    run (just? B λ vᵇ → iff (v ≤? v) ((A ≔ v ∸ v) ∶ (B ≔ vᵇ + v))) m
  ≈⟨ just?-accept (↦-∪⁺ʳ′ (⊥-elim ∘ A≢B ∘ sym ∘ singleton∈) singleton-law′) ⟩
    run (iff (v ≤? v) ((A ≔ v ∸ v) ∶ (B ≔ v′ + v))) m
  ≈⟨ iff-accept {b = v ≤? v} (fromWitness Nat.≤-refl) ⟩
    run ((A ≔ v ∸ v) ∶ (B ≔ v′ + v)) m
  ≈⟨ ≈-cong-cmd (B ≔ v′ + v) update-update ⟩
    run (B ≔ (v′ + v)) (singleton (A , v ∸ v) ∪ singleton (B , v′))
  ≈⟨ ≈-cong-cmd (B ≔ v′ + v) (∪-comm $ singleton♯ A≢B) ⟩
    run (B ≔ (v′ + v)) (singleton (B , v′) ∪ singleton (A , v ∸ v))
  ≈⟨ update-update ⟩
    singleton (B , v′ + v) ∪ singleton (A , v ∸ v)
  ≈⟨ ∪-comm $ singleton♯ (≢-sym A≢B) ⟩
    singleton (A , v ∸ v) ∪ singleton (B , v′ + v)
  ≡⟨ cong (λ x → (singleton (A , x) ∪ singleton (B , v′ + v))) (Nat.n∸n≡0 v) ⟩
    singleton (A , 0) ∪ singleton (B , v′ + v)
  ∎ where
    open ≈-Reasoning

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
denot⇒oper : (⟦ l ⟧ s ≡ s′) → (l , s —→⋆′ s′)
denot⇒oper {l = []}    refl = base
denot⇒oper {l = _ ∷ _} refl = step singleStep (denot⇒oper refl)

oper⇒denot : (l , s —→⋆′ s′) → (⟦ l ⟧ s ≡ s′)
oper⇒denot {l = .[]}   base                = refl
oper⇒denot {l = _ ∷ _} (step singleStep p) = oper⇒denot p

denot⇔oper : (⟦ l ⟧ s ≡ s′) ⇔ (l , s —→⋆′ s′)
denot⇔oper = denot⇒oper , oper⇒denot
