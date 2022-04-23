-------------------------
-- ** Axiomatic semantics

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
-- open import Prelude.Maps
open import ValueSep.Maps
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Ord

module ValueSep.HoareLogic (Part : Set) ⦃ _ : DecEq Part ⦄ where

-- NB. ⦃ it ⦄ required due to Agda bug, reported at https://github.com/agda/agda/issues/5093
open import ValueSep.Ledger Part ⦃ it ⦄

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

-- ** Hoare triples.

weak↑ strong↑ : Pred₀ S → Pred₀ (Maybe S)
weak↑   = M.All.All
strong↑ = M.Any.Any
lift↑   = strong↑ -- weak↑
-- T0D0: weak or strong?

infixl 4 _↑∘_
_↑∘_ : Pred₀ S → (S → Maybe S) → Pred₀ S
P ↑∘ f = lift↑ P ∘ f

⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Set
⟨ P ⟩ l ⟨ Q ⟩ = ∀ s → P s → lift↑ Q (⟦ l ⟧ s)

hoare-base :
  ──────────────
  ⟨ P ⟩ [] ⟨ P ⟩
hoare-base _ = M.Any.just

hoare-step :
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────────
  ⟨ P ↑∘ ⟦ t ⟧ ⟩ t ∷ l ⟨ Q ⟩
hoare-step {t = t} PlQ s Ps↑ with ⟦ t ⟧ s | Ps↑
... | just s′ | M.Any.just Ps = PlQ s′ Ps

consequence :
  ∙ P′ ⊢ P   -- ^ weakening the pre-condition
  ∙ Q  ⊢ Q′  -- ^ strengthening the post-condition
  ∙ ⟨ P  ⟩ l ⟨ Q  ⟩
    ───────────────
    ⟨ P′ ⟩ l ⟨ Q′ ⟩
consequence ⊢P Q⊢ PlQ _ = M.Any.map Q⊢ ∘ PlQ _ ∘ ⊢P

-- Utilities for Hoare triples.
weaken : P′ ⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken {l = l} H = consequence {l = l} H id

strengthen : Q ⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen {l = l} H = consequence {l = l} id H

axiom-base⋆ : ⟨ P ↑∘ ⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []} = weaken {l = []} (λ where (M.Any.just p) → p) hoare-base
axiom-base⋆ {P = P} {l = t ∷ l} s Ps
  with ⟦ t ⟧ s | Ps
... | just s′ | Ps
  with ⟦ l ⟧ s′ | Ps
... | just s′ | M.Any.just p = M.Any.just p

-- Derived alternative formulation for step, using list concatenation.
hoare-step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ───────────────────
    ⟨ P ⟩ l ++ l′ ⟨ R ⟩
hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR s Ps
  rewrite comp {l}{l′} s
  with ⟦ l ⟧ s | PlQ s Ps
... | just s′ | M.Any.just Qs′ = QlR s′ Qs′

-- ** Reasoning syntax for Hoare triples.
module HoareReasoning where
  infix  -2 begin_
  infixr -1 _~⟪_⟩_ _~⟨_⟫_ _~⟨_∶-_⟩_ _~⟨_∶-_⟩′_
  infix  0  _∎

  begin_ : ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q ⟩
  begin p = p

  -- weakening syntax
  _~⟪_⟩_ : ∀ P′ → P′ ⊢ P  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ l ⟨ R ⟩
  _~⟪_⟩_ {l = l} _ H PlR = weaken {l = l} H PlR

  -- strengthening syntax
  _~⟨_⟫_ : ∀ R′ → R ⊢ R′  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
  _~⟨_⟫_ {l = l} _ H PlR = strengthen {l = l} H PlR

  -- step syntax
  _~⟨_∶-_⟩_ : ∀ P′ → (t : Tx) → ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  -- (P′ ~⟨ t ∶- H ⟩ PlR) = hoare-step {l = l} H PlR
  (P′ ~⟨ t ∶- H ⟩ PlR) s P′s with ⟦ t ⟧ s | H s P′s
  ... | just s′ | M.Any.just Ps′ = PlR s′ Ps′

  -- step′ syntax
  _~⟨_∶-_⟩′_ : ∀ P′ → (l : L) → ⟨ P′ ⟩ l ⟨ P ⟩ → ⟨ P ⟩ l′ ⟨ R ⟩ → ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩′ PlR = hoare-step′ {l = l} H PlR

  _∎ : ∀ P → ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = hoare-base {P = p}

-- ** Correspondence with denotational/operational semantics.
axiom⇒denot : ⟨ P ⟩ l ⟨ Q ⟩ → (P ⊢ Q ↑∘ ⟦ l ⟧)
axiom⇒denot PlQ = PlQ _

denot⇒axiom : (P ⊢ Q ↑∘ ⟦ l ⟧) → ⟨ P ⟩ l ⟨ Q ⟩
denot⇒axiom P⊢Q _ = P⊢Q

axiom⇔denot : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (P ⊢ Q ↑∘ ⟦ l ⟧)
axiom⇔denot {l = l} = axiom⇒denot {l = l} , denot⇒axiom {l = l}

-- axiom⇒oper : ⟨ P ⟩ l ⟨ Q ⟩ → (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′)
-- axiom⇒oper {l = l}
--   =
-- (λ{ P⊢ Ps s→s′ → subst _ (oper⇒denot s→s′) (P⊢ Ps)})
--   ∘ axiom⇒denot {l = l}

-- oper⇒axiom : (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′) → ⟨ P ⟩ l ⟨ Q ⟩
-- oper⇒axiom = λ H → denot⇒axiom λ Ps → H Ps oper-base⋆

-- axiom⇔oper : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (∀ {s s′} → P s → l , s —→⋆′ s′ → Q s′)
-- axiom⇔oper = axiom⇒oper , oper⇒axiom

-- ** Lemmas about separating conjunction.

-- commutativity
∗↔ : P ∗ Q ⊢ Q ∗ P
∗↔ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) = s₂ , s₁ , ◇≡-comm {x = s₁}{s₂} ≡s , Qs₂ , Ps₁

-- associativity
∗↝ : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R
∗↝ {x = s} (s₁ , s₂₃ , ≡s , Ps₁ , (s₂ , s₃ , ≡s₂₃ , Qs₂ , Rs₃)) =
  (s₁ ◇ s₂) , s₃ , ◇≈-assocʳ ≡s ≡s₂₃ , (s₁ , s₂ , ≈-refl , Ps₁ , Qs₂) , Rs₃

↜∗ : (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R
↜∗ {x = s} (s₁₂ , s₃ , ≡s , (s₁ , s₂ , ≡s₁₂ , Ps₁ , Qs₂) , Rs₃) =
  s₁ , s₂ ◇ s₃ , ◇≈-assocˡ {m₁ = s₁}{s₂} ≡s ≡s₁₂  , Ps₁ , (s₂ , s₃ , ≈-refl , Qs₂ , Rs₃)

-- ** Useful lemmas when transferring a value between participants in the minimal context.
_↝⟨_⟩_ : ∀ A v B {vᵃ}{vᵇ}{v≤ : v ≤ vᵃ} → ⟨ A ↦ vᵃ ∗ B ↦ vᵇ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ (vᵃ ∸ v) ∗ B ↦ (vᵇ + v) ⟩
(A ↝⟨ v ⟩ B) {vᵃ}{vᵇ}{vᵃ≤v} s (s₁ , s₂ , ≡s , As₁ , Bs₂)
  with s₁ A | As₁ | ↦-◇ˡ {s₁ = s₁}{A}{vᵃ}{s₂} As₁ | ≡s A
... | .(just vᵃ) | refl | .(s₂ ⁉⁰ A) , refl , p | sA≡
  with s₂ B | Bs₂ | ↦-◇ʳ {s₂ = s₂}{B}{vᵇ}{s₁} Bs₂ | ≡s B
... | .(just vᵇ) | refl | .(s₁ ⁉⁰ B) , refl , q | sB≡
  with s A | trans (sym sA≡) p
... | .(just (vᵃ ◇ (s₂ ⁉⁰ A))) | refl
  with s B | trans (sym sB≡) q
... | .(just ((s₁ ⁉⁰ B) ◇ vᵇ)) | refl
  with v ≤? vᵃ ◇ (s₂ ⁉⁰ A)
... | no  v≰ = ⊥-elim $ v≰ $ Nat.≤-stepsʳ (s₂ ⁉⁰ A) $ vᵃ≤v
... | yes v≤
  = M.Any.just (_s₁′ , _s₂′ , ≡s′ , As₁′ , Bs₂′)
  where
    sA≡′ : s A ≡ just (vᵃ ◇ (s₂ ⁉⁰ A))
    sA≡′ = trans (sym sA≡) p

    sB≡′ : s B ≡ just ((s₁ ⁉⁰ B) ◇ vᵇ)
    sB≡′ = trans (sym sB≡) q

    _s₁′ = s₁ [ A ↝ (_∸ v) ]
    _s₂′ = s₂ [ B ↝ (_+ v) ]

    _s′ = s [ A ↝ (_∸ v) ]
            [ B ↝ (_+ v) ]

    As₁′ : _s₁′ A ≡ just (vᵃ ∸ v)
    As₁′ rewrite As₁ | ≟-refl A = refl

    Bs₂′ : _s₂′ B ≡ just (vᵇ + v)
    Bs₂′ rewrite Bs₂ | ≟-refl B = refl

    ≡s′ : ⟨ _s₁′ ◇ _s₂′ ⟩≡ _s′
    ≡s′ k
      rewrite sym $ ≡s k
      with k ≟ A | k ≟ B
    ≡s′ k | yes refl | yes refl -- ∙ k ≡ A ≡ B
      rewrite ≟-refl A | ≟-refl B | As₁ | Bs₂
      = cong just
      $ begin (vᵃ ∸ v) + (vᵇ + v) ≡⟨ sym $ Nat.+-∸-comm _ vᵃ≤v ⟩
              vᵃ + (vᵇ + v) ∸ v   ≡⟨ cong (_∸ v) $ sym $ Nat.+-assoc _ vᵇ v ⟩
              (vᵃ + vᵇ) + v ∸ v   ≡⟨ Nat.m+n∸n≡m _ v ⟩
              (vᵃ + vᵇ)           ≡⟨ sym $ Nat.m∸n+n≡m v≤ ⟩
              (vᵃ + vᵇ) ∸ v + v   ∎ where open ≡-Reasoning
    ≡s′ k | yes refl | no k≢B -- ∙ k ≡ A
      rewrite ≟-refl A | As₁
      with s₂ A
    ... | nothing = refl
    ... | just _  = cong just $ sym $ Nat.+-∸-comm _ vᵃ≤v
    ≡s′ k | no k≢A   | yes refl -- ∙ k ≡ B
      rewrite ≟-refl B | Bs₂
      with s₁ B
    ... | nothing  = refl
    ... | just _   = cong just $ sym $ Nat.+-assoc _ vᵇ v
    ≡s′ k | no k≢A   | no k≢B -- ∙ k ∉ {A, B}
      rewrite M.map-id (s₁ k) | M.map-id (s₂ k) | M.map-id (s₁ k ◇ s₂ k) | M.map-id (s₁ k ◇ s₂ k)
      = refl

_↝⁰_ : ∀ A B → ⟨ A ↦ v ∗ B ↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ 0 ∗ B ↦ (v′ + v) ⟩
_↝⁰_ {v = v} {v′ = v′} A B with p ← (A ↝⟨ v ⟩ B) {vᵇ = v′} {v≤ = ≤-refl {x = v}} rewrite Nat.n∸n≡0 v = p

_↜⟨_⟩_ : ∀ A v B {vᵃ}{vᵇ}{v≤ : v ≤ vᵇ} → ⟨ A ↦ vᵃ ∗ B ↦ vᵇ ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (vᵃ + v) ∗ B ↦ (vᵇ ∸ v) ⟩
(A ↜⟨ v ⟩ B) {vᵃ}{vᵇ}{v≤} s (s₁ , s₂ , ≡s , As₁ , Bs₂)
  = M.Any.map (λ where (s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′) → s₂′ , s₁′ , ◇≡-comm {x = s₁′} ≡s′ , Bs₂′ , As₁′)
              ((B ↝⟨ v ⟩ A) {v≤ = v≤} s (s₂ , s₁ , ◇≡-comm {x = s₁} ≡s , Bs₂ , As₁))

_↜⁰_ : ∀ A B → ⟨ A ↦ v′ ∗ B ↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (v′ + v) ∗ B ↦ 0 ⟩
_↜⁰_ {v′ = v′} {v = v} A B with p ← (A ↜⟨ v ⟩ B) {vᵃ = v′} {v≤ = ≤-refl {x = v}} rewrite Nat.n∸n≡0 v = p
