-- Mostly copied from Prelude.Maps.

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Applicative
open import Prelude.Decidable
open import Prelude.Apartness
open import Prelude.InferenceRules
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Functor

import Relation.Binary.Reasoning.Setoid as BinSetoid

module ValueSep.Maps {K V : Type} where

Map : Type
Map = K → Maybe V

syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

private variable
  s s₁ s₂ s₃ s₁₂ s₂₃ m m′ m₁ m₂ m₃ m₁₂ m₂₃ : Map
  k k′ : K
  v v′ : V
  f g : Map → Map

∅ : Map
∅ = const nothing

infix 3 _∈ᵈ_ _∉ᵈ_ _∈ᵈ?_ _∉ᵈ?_
_∈ᵈ_ _∉ᵈ_ : K → Map → Type
k ∈ᵈ m = Is-just (m k)
k ∉ᵈ m = ¬ (k ∈ᵈ m)

_∈ᵈ?_ : Decidable² _∈ᵈ_
k ∈ᵈ? m with m k
... | just _  = yes auto
... | nothing = no  auto
_∉ᵈ?_ : Decidable² _∉ᵈ_
k ∉ᵈ? m = ¬? (k ∈ᵈ? m)

infix 3 _⊆ᵈ_ _⊈ᵈ_
_⊆ᵈ_ _⊈ᵈ_ : Rel₀ Map
m ⊆ᵈ m′ = ∀ k → k ∈ᵈ m → k ∈ᵈ m′
k ⊈ᵈ m = ¬ (k ⊆ᵈ m)

-- ** equivalence
open import Prelude.Setoid
instance
  Setoid-Map : ISetoid Map
  Setoid-Map = λ where
    .relℓ → _
    ._≈_ m m′ → ∀ k → m k ≡ m′ k

  SetoidLaws-Map : SetoidLaws Map
  SetoidLaws-Map .isEquivalence = record
    { refl = λ _ → refl
    ; sym = λ p k → sym (p k)
    ; trans = λ p q k → trans (p k) (q k)
    }

-- infix 3 _≈_
-- _≈_ : Rel₀ Map
-- m ≈ m′ = ∀ k → m k ≡ m′ k

-- ≈-refl : Reflexive _≈_
-- ≈-refl _ = refl

-- ≈-sym : Symmetric _≈_
-- ≈-sym p k = sym (p k)

-- ≈-trans : Transitive _≈_
-- ≈-trans p q k = trans (p k) (q k)

-- ≈-equiv : IsEquivalence _≈_
-- ≈-equiv = record {refl = ≈-refl; sym = ≈-sym; trans = ≈-trans}

-- ≈-setoid : Setoid 0ℓ 0ℓ
-- ≈-setoid = record {Carrier = Map; _≈_ = _≈_; isEquivalence = ≈-equiv}

-- module ≈-Reasoning = BinSetoid ≈-setoid

≈-cong : ∀ {P : K → Maybe V → Type}
  → s₁ ≈ s₂
  → (∀ k → P k (s₁ k))
  → (∀ k → P k (s₂ k))
≈-cong {P = P} eq p k = subst (P k) (eq k) (p k)

_⁺ : ∀ {X : Type} → Pred₀ X → Pred₀ (Maybe X)
_⁺ = M.All.All

KeyMonotonic KeyPreserving : Pred₀ (Map → Map)
KeyMonotonic  f = ∀ s → s   ⊆ᵈ f s
KeyPreserving f = ∀ s → f s ⊆ᵈ s

KeyMonotonicᵐ KeyPreservingᵐ : Pred₀ (Map → Maybe Map)
KeyMonotonicᵐ  f = ∀ s → M.All.All (s ⊆ᵈ_) (f s)
KeyPreservingᵐ f = ∀ s → M.All.All (_⊆ᵈ s) (f s)

-- ** membership
∈ᵈ-cong : ∀ {k s₁ s₂} → s₁ ≈ s₂ → k ∈ᵈ s₁ → k ∈ᵈ s₂
∈ᵈ-cong {k}{s₁}{s₂} s₁≈s₂ k∈ = subst Is-just (s₁≈s₂ k) k∈

module _ {s k} where
  ∉ᵈ⁺ : Is-nothing (s k) → k ∉ᵈ s
  ∉ᵈ⁺ p k∈ with just _ ← s k = case p of λ where (M.All.just ())

  ∉ᵈ⁻ : k ∉ᵈ s → Is-nothing (s k)
  ∉ᵈ⁻ k∉ with s k
  ... | just _  = ⊥-elim $ k∉ (M.Any.just tt)
  ... | nothing = auto

∉ᵈ-cong : ∀ {k s₁ s₂} → s₁ ≈ s₂ → k ∉ᵈ s₁ → k ∉ᵈ s₂
∉ᵈ-cong s≈ k∉ = k∉ ∘ ∈ᵈ-cong (≈-sym s≈)

_[_↦∅] = _∉ᵈ_

_[_↦_] : Map → K → V → Type
m [ k ↦ v ] = m k ≡ just v

_[_↦_]∅ : Map → K → V → Type
m [ k ↦ v ]∅ = m [ k ↦ v ] × ∀ k′ → k′ ≢ k → k′ ∉ᵈ m

module _ ⦃ _ : DecEq K ⦄ where
  _[_↝_] : Map → K → (Op₁ V) → Map
  -- m [ k′ ↝ f ] = λ k → if k == k′ then f <$> m k else m k
  m [ k′ ↝ f ] = λ k → (if k == k′ then f else id) <$> m k

  [↝]-mono : ∀ k (f : Op₁ V) → KeyMonotonic (_[ k ↝ f ])
  [↝]-mono k′ f m k k∈ with k ≟ k′
  ... | no _ = subst Is-just (sym $ M.map-id (m k)) k∈
  ... | yes refl with m k′
  ... | nothing = k∈
  ... | just _  = auto

  [↝]-pre : ∀ k (f : Op₁ V) → KeyPreserving (_[ k ↝ f ])
  [↝]-pre k′ f m k k∈ with k ≟ k′
  ... | no _ = subst Is-just (M.map-id (m k)) k∈
  ... | yes refl with m k′
  ... | nothing = k∈
  ... | just _  = auto

module _ ⦃ _ : Semigroup V ⦄ ⦃ _ : Monoid V ⦄
         -- ⦃ _ : ISetoid V ⦄ ⦃ _ : SetoidLaws V ⦄
         -- ⦃ _ : SemigroupLaws V ⦄ ⦃ _ : MonoidLaws V ⦄ where
         ⦃ _ : SemigroupLaws≡ V ⦄ ⦃ _ : MonoidLaws≡ V ⦄ where
  instance
    Semigroup-Map : Semigroup Map
    Semigroup-Map ._◇_ m m′ k = m k ◇ m′ k

    Monoid-Map : Monoid Map
    Monoid-Map .ε = ∅

  open Alg (Rel₀ Map ∋ _≈_)

  ⟨_◇_⟩≡_ : 3Rel Map 0ℓ
  ⟨ m₁ ◇ m₂ ⟩≡ m = m₁ ◇ m₂ ≈ m

  instance
    SemigroupLaws-Map : SemigroupLaws Map
    SemigroupLaws-Map = λ where
      .◇-comm   → λ m m′ k   → ◇-comm≡ (m k) (m′ k)
      .◇-assocʳ → λ m₁ _ _ k → ◇-assocʳ≡ (m₁ k) _ _

    MonoidLaws-Map : MonoidLaws Map
    MonoidLaws-Map .ε-identity = λ where
      .proj₁ → λ m k → ε-identityˡ≡ (m k)
      .proj₂ → λ m k → ε-identityʳ≡ (m k)

  ◇≡-comm : Symmetric (⟨_◇_⟩≡ m)
  ◇≡-comm {x = m₁}{m₂} ≈m = ≈-trans (◇-comm m₂ m₁) ≈m

  ◇-congˡ :
    m₁ ≈ m₂
    ───────────────────
    (m₁ ◇ m₃) ≈ (m₂ ◇ m₃)
  ◇-congˡ {m₁}{m₂}{m₃} m₁≈m₂ k =
    begin
      (m₁ ◇ m₃) k
    ≡⟨⟩
      m₁ k ◇ m₃ k
    ≡⟨  cong (_◇ m₃ k) (m₁≈m₂ k) ⟩
      m₂ k ◇ m₃ k
    ≡⟨⟩
      (m₂ ◇ m₃) k
    ∎ where open ≡-Reasoning

  ◇-congʳ : m₂ ≈ m₃ → (m₁ ◇ m₂) ≈ (m₁ ◇ m₃)
  ◇-congʳ {m₂}{m₃}{m₁} m₂≈m₃ =
    begin m₁ ◇ m₂ ≈⟨ ◇-comm m₁ m₂ ⟩
          m₂ ◇ m₁ ≈⟨ ◇-congˡ m₂≈m₃ ⟩
          m₃ ◇ m₁ ≈⟨ ◇-comm m₃ m₁ ⟩
          m₁ ◇ m₃ ∎ where open ≈-Reasoning

  ◇≈-assocˡ :
    ∙ ⟨ m₁₂ ◇ m₃ ⟩≡ m
    ∙ ⟨ m₁ ◇ m₂  ⟩≡ m₁₂
      ───────────────────
      ⟨ m₁ ◇ (m₂ ◇ m₃) ⟩≡ m
  ◇≈-assocˡ {m₃ = m₃}{m₁ = m₁}{m₂ = m₂} ≡m ≡m₁₂ = ≈-trans (≈-trans (≈-sym (◇-assocʳ m₁ m₂ m₃)) (◇-congˡ ≡m₁₂)) ≡m

  ◇≈-assocʳ :
    ∙ ⟨ m₁ ◇ m₂₃ ⟩≡ m
    ∙ ⟨ m₂ ◇ m₃  ⟩≡ m₂₃
      ───────────────────
      ⟨ (m₁ ◇ m₂) ◇ m₃ ⟩≡ m
  ◇≈-assocʳ {m₁ = m₁}{m₂ = m₂}{m₃ = m₃} ≡m ≡m₂₃ = ≈-trans (≈-trans (◇-assocʳ m₁ m₂ m₃) (◇-congʳ ≡m₂₃)) ≡m

  Is-just-◇⁻ : ∀ (m m′ : Maybe V) → Is-just (m ◇ m′) → Is-just m ⊎ Is-just m′
  Is-just-◇⁻ (just _) _       _ = inj₁ auto
  Is-just-◇⁻ nothing (just _) _ = inj₂ auto

  Is-just-◇⁺ : ∀ (m m′ : Maybe V) → Is-just m ⊎ Is-just m′ → Is-just (m ◇ m′)
  Is-just-◇⁺ (just _) (just _) _        = auto
  Is-just-◇⁺ (just _) nothing  (inj₁ _) = auto
  Is-just-◇⁺ nothing  (just _) (inj₂ _) = auto

  ∈ᵈ-◇⁻ : ∀ k s₁ s₂ → k ∈ᵈ (s₁ ◇ s₂) → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
  ∈ᵈ-◇⁻ k s₁ s₂ k∈ = k∈′
    where
      p : Is-just (s₁ k ◇ s₂ k)
      p = k∈

      k∈′ : (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
      k∈′ = case Is-just-◇⁻ (s₁ k) (s₂ k) p of λ where
        (inj₁ x) → inj₁ x
        (inj₂ x) → inj₂ x

  ∈ᵈ-◇⁺ : ∀ k s₁ s₂ → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂) → k ∈ᵈ (s₁ ◇ s₂)
  ∈ᵈ-◇⁺ k s₁ s₂ k∈ = k∈′
    where
      p : Is-just (s₁ k) ⊎ Is-just (s₂ k)
      p = case k∈ of λ where
        (inj₁ x) → inj₁ x
        (inj₂ x) → inj₂ x

      k∈′ : Is-just ((s₁ ◇ s₂) k)
      k∈′ = Is-just-◇⁺ (s₁ k) (s₂ k) p

  ∈ᵈ-◇⁺ˡ : ∀ k s₁ s₂ → k ∈ᵈ s₁ → k ∈ᵈ (s₁ ◇ s₂)
  ∈ᵈ-◇⁺ˡ k s₁ s₂ = ∈ᵈ-◇⁺ k s₁ s₂ ∘ inj₁

  ∈ᵈ-◇⁺ʳ : ∀ k s₁ s₂ → k ∈ᵈ s₂ → k ∈ᵈ (s₁ ◇ s₂)
  ∈ᵈ-◇⁺ʳ k s₁ s₂ = ∈ᵈ-◇⁺ k s₁ s₂ ∘ inj₂

  _⁉⁰_ : Map → K → V
  m ⁉⁰ k = fromMaybe ε (m k)

  _[_↦⁰_] : Map → K → V → Type
  m [ k ↦⁰ v ] = m ⁉⁰ k ≡ v

  ↦⇒↦⁰ : s [ k ↦ v ] → s [ k ↦⁰ v ]
  ↦⇒↦⁰ {s}{k}{v} k∈ with s k | k∈
  ... | .(just v) | refl = refl

  ↦⁰⇒↦ : s [ k ↦⁰ v ] → (k ∉ᵈ s) ⊎ (s [ k ↦ v ])
  ↦⁰⇒↦ {s}{k}{v} k∈ with s k | k∈
  ... | nothing | refl = inj₁ λ ()
  ... | just _  | refl = inj₂ refl

  ↦-◇ˡ : s₁ [ k ↦ v ] → ∃ λ v′ → s₂ [ k ↦⁰ v′ ] × (s₁ ◇ s₂) [ k ↦ v ◇ v′ ]
  ↦-◇ˡ {s₁ = s₁} {k = k}{v} {s₂ = s₂} k∈₁
    with s₁ k | k∈₁
  ... | just _  | refl
    with s₂ k
  ... | nothing = -, refl , cong just (sym $ ε-identityʳ≡ _)
  ... | just _  = -, refl , refl

  ↦-◇ʳ : s₂ [ k ↦ v ] → ∃ λ v′ → s₁ [ k ↦⁰ v′ ] × (s₁ ◇ s₂) [ k ↦ v′ ◇ v ]
  ↦-◇ʳ {s₂ = s₂} {k = k} {s₁ = s₁} k∈₂
    with s₂ k | k∈₂ | s₁ k
  ... | just _  | refl | nothing = -, refl , cong just (sym $ ε-identityˡ≡ _)
  ... | just _  | refl | just _  = -, refl , refl

  ↦-◇⁺ˡ : k ∉ᵈ s₂ → s₁ k ≡ (s₁ ◇ s₂) k
  ↦-◇⁺ˡ {k = k}{s₂}{s₁} k∉ =
    begin
      s₁ k
    ≡⟨ sym $ ε-identity≡ .proj₂ (s₁ k) ⟩
      s₁ k ◇ nothing
    ≡⟨ cong (s₁ k ◇_) (sym (Is-nothing≡ (∉ᵈ⁻ {s = s₂} k∉))) ⟩
      s₁ k ◇ s₂ k
    ≡⟨⟩
      (s₁ ◇ s₂) k
    ∎ where open ≡-Reasoning

  ↦-◇⁺ʳ : k ∉ᵈ s₁ → s₂ k ≡ (s₁ ◇ s₂) k
  ↦-◇⁺ʳ {k = k}{s₁}{s₂} k∉ =
    begin
      s₂ k
    ≡⟨ sym $ ε-identity≡ .proj₁ (s₂ k) ⟩
      nothing ◇ s₂ k
    ≡⟨ cong (_◇ s₂ k) (sym (Is-nothing≡ (∉ᵈ⁻ {s = s₁} k∉))) ⟩
      s₁ k ◇ s₂ k
    ≡⟨⟩
      (s₁ ◇ s₂) k
    ∎ where open ≡-Reasoning
