-------------------------
-- ** Axiomatic semantics

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Maps
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules

module HoareLogic (Part : Set) ⦃ _ : DecEq Part ⦄ where

-- NB. ⦃ it ⦄ required due to Agda bug, reported at https://github.com/agda/agda/issues/5093
open import Ledger Part ⦃ it ⦄

-- ** Shallow embedding of logic formulas/propositions.
Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

emp : Assertion
emp m = ∀ k → k ∉ᵈ m

_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ◇ s₂ ⟩≡ s × P s₁ × Q s₂

_↦_ : Part → ℕ → Assertion
p ↦ n = _[ p ↦ n ]

infixr 10 _∗_
infix  11 _↦_

-- ** Hoare triples: both strengthening/weakening are captured by consequence.
data ⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Set₁ where

  base :

    ──────────────
    ⟨ P ⟩ [] ⟨ P ⟩

  step :
    ⟨ P ⟩ l ⟨ R ⟩
    ─────────────────────────
    ⟨ P ∘ ⟦ t ⟧ ⟩ t ∷ l ⟨ R ⟩

  consequence :
    ∙ P′ ⊢ P          -- ^ weakening the pre-condition
    ∙ Q  ⊢ Q′         -- ^ strengthening the post-condition
    ∙ ⟨ P  ⟩ l ⟨ Q  ⟩
      ───────────────
      ⟨ P′ ⟩ l ⟨ Q′ ⟩

-- Utilities for Hoare triples.
weaken : P′ ⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken H = consequence H id

strengthen : Q ⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen H = consequence id H

axiom-base⋆ : ⟨ P ∘ ⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []}    = consequence {P = P} id id base
axiom-base⋆ {P = P} {l = t ∷ l} = consequence {P = P ∘ ⟦ l ⟧ ∘ ⟦ t ⟧} {Q = P} id id (step axiom-base⋆)

-- ** Correspondence with denotational/operational semantics.
axiom⇒denot : ⟨ P ⟩ l ⟨ Q ⟩ → (P ⊢ Q ∘ ⟦ l ⟧)
axiom⇒denot base = id
axiom⇒denot (step PlQ) = axiom⇒denot PlQ
axiom⇒denot (consequence P⊢P′ Q′⊢Q PlQ) = Q′⊢Q ∘ axiom⇒denot PlQ ∘ P⊢P′

denot⇒axiom : (P ⊢ Q ∘ ⟦ l ⟧) → ⟨ P ⟩ l ⟨ Q ⟩
denot⇒axiom {P = P} {Q = Q} {l = []} H =
  strengthen {Q = P} {Q′ = Q} H base
denot⇒axiom {P = P} {Q = Q} {l = t ∷ l} H =
  weaken {P′ = P} {P = Q ∘ ⟦ t ∷ l ⟧} H (axiom-base⋆ {P = Q} {l = t ∷ l})

axiom⇔denot : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (P ⊢ Q ∘ ⟦ l ⟧)
axiom⇔denot = axiom⇒denot , denot⇒axiom

axiom⇒oper : ⟨ P ⟩ l ⟨ Q ⟩ → (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′)
axiom⇒oper = (λ{ P⊢ Ps s→s′ → subst _ (proj₂ denot⇔oper s→s′) (P⊢ Ps)}) ∘ axiom⇒denot

oper⇒axiom : (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′) → ⟨ P ⟩ l ⟨ Q ⟩
oper⇒axiom = λ H → denot⇒axiom λ Ps → H Ps oper-base⋆

axiom⇔oper : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′)
axiom⇔oper = axiom⇒oper , oper⇒axiom

-- Derived alternative formulation for step, using list concatenation.
step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ───────────────────
    ⟨ P ⟩ l ++ l′ ⟨ R ⟩
step′ {P} {[]} {Q} {l′} {R} PlQ QlR = weaken (axiom⇒denot PlQ) QlR
step′ {_} {t ∷ l} {Q} {l′} {R} (step PlQ) QlR = step (step′ PlQ QlR)
step′ {P} {t ∷ l} {Q} {l′} {R} (consequence {P = P′}{Q = Q′} pre post PlQ) QlR = weaken pre p
  where
    p : ⟨ P′ ⟩ t ∷ l ++ l′ ⟨ R ⟩
    p = step′ PlQ (weaken post QlR)

-- ** Reasoning syntax for Hoare triples.
module HoareReasoning where
  infix  -2 begin_
  infixr -1 _~⟪_⟩_ _~⟨_⟫_ _~⟨_∶-_⟩_ _~⟨_∶-_⟩′_
  infix  0  _∎

  begin_ : ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q ⟩
  begin p = p

  -- weakening syntax
  _~⟪_⟩_ : ∀ P′ → P′ ⊢ P  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ l ⟨ R ⟩
  _ ~⟪ H ⟩ PlR = weaken H PlR

  -- strengthening syntax
  _~⟨_⟫_ : ∀ R′ → R ⊢ R′  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
  _ ~⟨ H ⟫ PlR = strengthen H PlR

  -- step syntax
  _~⟨_∶-_⟩_ : ∀ P′ → (t : Tx) → ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  P′ ~⟨ t ∶- H ⟩ PlR = P′ ~⟪ axiom⇒denot H ⟩ step {t = t} PlR

  -- step′ syntax
  _~⟨_∶-_⟩′_ : ∀ P′ → (l : L) → ⟨ P′ ⟩ l ⟨ P ⟩ → ⟨ P ⟩ l′ ⟨ R ⟩ → ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩′ PlR = step′ H PlR

  _∎ : ∀ P → ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = base {P = p}

-- ** Lemmas about separating conjunction.

-- commutativity
∗↔ : P ∗ Q ⊢ Q ∗ P
∗↔ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) = s₂ , s₁ , ◇≡-comm ≡s , Qs₂ , Ps₁

-- associativity
∗↝ : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R
∗↝ {x = s} (s₁ , s₂₃ , ≡s , Ps₁ , (s₂ , s₃ , ≡s₂₃ , Qs₂ , Rs₃)) =
  (s₁ ◇ s₂) , s₃ , ◇≈-assocʳ ≡s ≡s₂₃ , (s₁ , s₂ , ≈-refl , Ps₁ , Qs₂) , Rs₃

↜∗ : (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R
↜∗ {x = s} (s₁₂ , s₃ , ≡s , (s₁ , s₂ , ≡s₁₂ , Ps₁ , Qs₂) , Rs₃) =
  s₁ , s₂ ◇ s₃ , ◇≈-assocˡ ≡s ≡s₁₂  , Ps₁ , (s₂ , s₃ , ≈-refl , Qs₂ , Rs₃)

-- ** Useful lemmas when transferring a value between participants in the minimal context.
_↝_ : ∀ A B → ⟨ A ↦ v ∗ B ↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ 0 ∗ B ↦ (v′ + v) ⟩
_↝_ {v}{v′} A B = denot⇒axiom d
  where
    tx = A —→⟨ v ⟩ B

    postulate d : A ↦ v ∗ B ↦ v′ ⊢ A ↦ 0 ∗ B ↦ (v′ + v) ∘ ⟦ tx ⟧
    {-
    d {s} (s₁ , s₂ , ≡s , As₁ , Bs₂) = s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′
      where
        s₁′ s₂′ ⟦t⟧s : S
        s₁′ = singleton (A , 0)
        s₂′ = singleton (B , v′ + v)
        s₁₂ = s₁ ◇ s₂

        ⟦t⟧s = ⟦ tx ⟧ s

        As₁′ : (A ↦ 0) s₁′
        As₁′ = singleton-law .proj₁

        Bs₂′ : (B ↦ (v′ + v)) s₂′
        Bs₂′ = singleton-law .proj₁

        ≡s′ : ⟨ s₁′ ◇ s₂′ ⟩≡ ⟦t⟧s
        ≡s′ =
          begin
            s₁′ ◇ s₂′
          ≡⟨⟩
            singleton (A , 0) ◇ singleton (B , v′ + v)
          ≈⟨ ≈-sym transfer◇ ⟩
            run [ A ∣ v ↦ B ] (singleton (A , v) ◇ singleton (B , v′))
          ≈⟨ ≈-cong-cmd [ A ∣ v ↦ B ] {!!} ⟩
            run [ A ∣ v ↦ B ] (s₁ ◇ s₂)
          ≡⟨⟩
            ⟦ tx ⟧ (s₁ ◇ s₂)
          ≈⟨ {!≡s!} ⟩
            ⟦ tx ⟧ s
          ∎ where open ≈-Reasoning
    -}

_↜_ : ∀ A B → ⟨ A ↦ v′ ∗ B ↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (v′ + v) ∗ B ↦ 0 ⟩
_↜_ {v}{v′} A B = denot⇒axiom λ where
  (s₁ , s₂ , ≡s , As₁ , Bs₂) →
    let s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′ = axiom⇒denot (B ↝ A) (s₂ , s₁ , ◇≡-comm ≡s , Bs₂ , As₁)
    in  s₂′ , s₁′ , ◇≡-comm ≡s′ , Bs₂′ , As₁′
