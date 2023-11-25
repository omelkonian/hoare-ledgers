-------------------------------------
-- ** Properties for Hoare triples.

open import Prelude.Init hiding (_+_; +_); open SetAsType
open Integer using (_+_; _-_)
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Ord
open import Prelude.Setoid

module ValueSepInt.HoareProperties (Part : Type) ⦃ _ : DecEq Part ⦄ where

open import ValueSepInt.Maps {K = Part}
open import ValueSepInt.Ledger Part ⦃ it ⦄
open import ValueSepInt.HoareLogic Part ⦃ it ⦄

◇-assoc-comm : ∀ (x y z : V) → (x ◇ y) ◇ z ≡ (x ◇ z) ◇ y
◇-assoc-comm x y z rewrite ◇-assocʳ≡ x y z | ◇-comm≡ y z | ◇-assocˡ≡ x z y = refl

◇-reorder : ∀ x y z w → (x ◇ y) ◇ (z + w) ≡ ((x ◇ z) ◇ y) + w
◇-reorder x y z w =
  begin x + y + (z + w)   ≡⟨ ◇-assocʳ≡ x y (z + w) ⟩
        x + (y + (z + w)) ≡⟨ cong (x +_) $ ◇-assocˡ≡ y z w ⟩
        x + (y + z + w)   ≡⟨ cong (λ ◆ → x + (◆ + w)) $ ◇-comm≡ y z ⟩
        x + (z + y + w)   ≡⟨ cong (x +_) $ ◇-assocʳ≡ z y w ⟩
        x + (z + (y + w)) ≡⟨ ◇-assocˡ≡ x z (y + w) ⟩
        x + z + (y + w)   ≡⟨ ◇-assocˡ≡ (x + z) y w ⟩
        x + z + y + w     ∎ where open ≡-Reasoning

-- ** Lemmas about separating conjunction.

-- commutativity
∗↔ : P ∗ Q ⊢ Q ∗ P
∗↔ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) = s₂ , s₁ , ◇≡-comm {x = s₁}{s₂} ≡s , Qs₂ , Ps₁

-- associativity
∗↝ : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R
∗↝ {x = s} (s₁ , s₂₃ , ≡s , Ps₁ , (s₂ , s₃ , ≡s₂₃ , Qs₂ , Rs₃)) =
  (s₁ ◇ s₂) , s₃ , ◇≈-assocʳ {m₁ = s₁} ≡s ≡s₂₃ , (s₁ , s₂ , ≈-refl , Ps₁ , Qs₂) , Rs₃

↜∗ : (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R
↜∗ {x = s} (s₁₂ , s₃ , ≡s , (s₁ , s₂ , ≡s₁₂ , Ps₁ , Qs₂) , Rs₃) =
  s₁ , s₂ ◇ s₃ , ◇≈-assocˡ {m₁ = s₁}{s₂} ≡s ≡s₁₂  , Ps₁ , (s₂ , s₃ , ≈-refl , Qs₂ , Rs₃)

-- ** Useful lemmas when transferring a value between participants in the minimal context.
_↝⟨_⟩_ : ∀ A v B {vᵃ}{vᵇ} →
  ⟨ A ↦ vᵃ ∗ B ↦ vᵇ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ (vᵃ - v) ∗ B ↦ (vᵇ + v) ⟩
(A ↝⟨ v ⟩ B) {vᵃ}{vᵇ} {s} (s₁ , s₂ , ≡s , (As₁ , A∅) , (Bs₂ , B∅))
  = _s₁′ , _s₂′ , ≡s′ , (As₁′ , A∅′) , (Bs₂′ , B∅′)
  where
    _s₁′ = s₁ [ A ↝ (_- v) ]
    _s₂′ = s₂ [ B ↝ (_+ v) ]

    _s′ = s [ A ↝ (_- v) ]
            [ B ↝ (_+ v) ]

    As₁′ : _s₁′ A ≡ vᵃ - v
    As₁′ rewrite As₁ | ≟-refl A = refl

    A∅′ : ∀ k → k ≢ A → _s₁′ k ≡ 0ℤ
    A∅′ k k≢ rewrite dec-no (k ≟ A) k≢ .proj₂ = A∅ k k≢

    Bs₂′ : _s₂′ B ≡ vᵇ + v
    Bs₂′ rewrite Bs₂ | ≟-refl B = refl

    B∅′ : ∀ k → k ≢ B → _s₂′ k ≡ 0ℤ
    B∅′ k k≢ rewrite dec-no (k ≟ B) k≢ .proj₂ = B∅ k k≢

    ≡s′ : ⟨ _s₁′ ◇ _s₂′ ⟩≡ _s′
    ≡s′ k
      rewrite sym $ ≡s k
      with k ≟ A | k ≟ B
    ≡s′ k | yes refl | yes refl -- ∙ k ≡ A ≡ B
      rewrite ≟-refl A | ≟-refl B | As₁ | Bs₂
      = ◇-reorder vᵃ (Integer.- v) vᵇ v
    ≡s′ k | yes refl | no k≢B -- ∙ k ≡ A
      rewrite ≟-refl A | As₁
      = ◇-assoc-comm vᵃ (Integer.- v) (s₂ k)
    ≡s′ k | no k≢A   | yes refl -- ∙ k ≡ B
      rewrite ≟-refl B | Bs₂
      = ◇-assocˡ≡ (s₁ k) vᵇ v
    ≡s′ k | no k≢A   | no k≢B -- ∙ k ∉ {A, B}
      = refl

_↝⁰_ : ∀ A B → ⟨ A ↦ v ∗ B ↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ ε ∗ B ↦ (v′ + v) ⟩
_↝⁰_ {v = v} A B
  with p ← (A ↝⟨ v ⟩ B) {v}
  rewrite Integer.m≡n⇒m-n≡0 v v refl
  = p

_↜⟨_⟩_ : ∀ A v B {vᵃ}{vᵇ} →
  ⟨ A ↦ vᵃ ∗ B ↦ vᵇ ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (vᵃ + v) ∗ B ↦ (vᵇ - v) ⟩
(A ↜⟨ v ⟩ B) {vᵃ}{vᵇ}{v≤} (s₁ , s₂ , ≡s , As₁ , Bs₂)
  = let s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′ =
            (B ↝⟨ v ⟩ A) (s₂ , s₁ , ◇≡-comm {x = s₁} ≡s , Bs₂ , As₁)
    in s₂′ , s₁′ , ◇≡-comm {x = s₁′} ≡s′ , Bs₂′ , As₁′

_↜⁰_ : ∀ A B → ⟨ A ↦ v′ ∗ B ↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (v′ + v) ∗ B ↦ 0ℤ ⟩
_↜⁰_ {v′ = v′} {v = v} A B
  with p ← (A ↜⟨ v ⟩ B) {v′}{v}
  rewrite Integer.m≡n⇒m-n≡0 v v refl
  = p
