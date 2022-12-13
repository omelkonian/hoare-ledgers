-- Mostly copied from Prelude.Maps.

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.InferenceRules
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Setoid

module ValueSepSimple.Maps {K : Type} where

Map : Type
Map = K → ℕ

syntax Map {K = K} = Map⟨ K ↦ℕ⟩

private variable
  s s₁ s₂ s₃ s₁₂ s₂₃ m m′ m₁ m₂ m₃ m₁₂ m₂₃ : Map
  k k′ : K
  v v′ : ℕ
  f g : Map → Map

∅ : Map
∅ = const 0

-- ** equivalence

instance
  Setoid-Map : ISetoid Map
  Setoid-Map = λ where
    .relℓ → _
    ._≈_ m m′ → ∀ k → m k ≡ m′ k

  SetoidLaws-Map : SetoidLaws Map
  SetoidLaws-Map .isEquivalence = record
    { refl  = λ _ → refl
    ; sym   = λ p k → sym (p k)
    ; trans = λ p q k → trans (p k) (q k)
    }

V = ℕ

≈-cong : ∀ {P : K → V → Type}
  → s₁ ≈ s₂
  → (∀ k → P k (s₁ k))
  → (∀ k → P k (s₂ k))
≈-cong {P = P} eq p k = subst (P k) (eq k) (p k)

_⁺ : ∀ {X : Type} → Pred₀ X → Pred₀ (Maybe X)
_⁺ = M.All.All

-- ** membership
_[_↦_] : Map → K → V → Type
m [ k ↦ v ] = m k ≡ v

module _ ⦃ _ : DecEq K ⦄ where
  _[_↝_] : Map → K → (Op₁ V) → Map
  m [ k′ ↝ f ] = λ k → (if k == k′ then f else id) (m k)

  _[_≔_] : Map → K → V → Map
  m [ k′ ≔ v ] = λ k → if k == k′ then v else m k

  ≔⇒↦ : (m [ k ≔ v ]) [ k ↦ v ]
  ≔⇒↦ {k = k} rewrite ≟-refl k = refl

instance
  Sℕ  = Semigroup-ℕ-+
  Sℕ⁺ = SemigroupLaws-ℕ-+
  Mℕ  = Monoid-ℕ-+
  Mℕ⁺ = MonoidLaws-ℕ-+

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
