-------------------------------------
-- ** Properties for Hoare triples.

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Ord
open import Prelude.Setoid

module ValueSepExact.HoareProperties (Part : Type) ⦃ _ : DecEq Part ⦄ where

open import ValueSepExact.Maps {K = Part}
open import ValueSepExact.Ledger Part ⦃ it ⦄
open import ValueSepExact.HoareLogic Part ⦃ it ⦄

-- ** Examples
↦0 : (A ↦ 0) s
   → s ≈ ∅
↦0 {A}{s} (sA≡ , A∅) k
  with k ≟ A
... | yes refl = sA≡
... | no  k≢A  = A∅ _ k≢A

_ :  (A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 1 ∗ A ↦ 0)
  ⊣⊢ (A ↦ 1 ∗ C ↦ 1)
_ = ↝ , ↜
  where
  ↝ : (A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 1 ∗ A ↦ 0)
    ⊢ (A ↦ 1 ∗ C ↦ 1)
  ↝ {x = s} (sᵃ , sᵇᶜᵈ , ≡abcd , A↦1 , (sᵇ  , sᶜᵈ , ≡bcd , B↦0 , (sᶜ , sᵈ , ≡cd , C↦1 , A↦0)))
    = sᵃ , sᶜ
    , (let open ≈-Reasoning in
       begin sᵃ ◇ sᶜ         ≈˘⟨ ◇-congʳ {m₁ = sᵃ} $ ε-identityʳ sᶜ ⟩
             sᵃ ◇ (sᶜ ◇ ∅)   ≈˘⟨ ◇-congʳ {m₁ = sᵃ} $ ◇-congʳ {m₁ = sᶜ} $ ↦0 A↦0 ⟩
             sᵃ ◇ (sᶜ ◇ sᵈ)  ≈⟨ ◇-congʳ {m₁ = sᵃ} ≡cd ⟩
             sᵃ ◇ sᶜᵈ        ≈˘⟨ ◇-congʳ {m₁ = sᵃ} $ ε-identityˡ sᶜᵈ ⟩
             sᵃ ◇ (∅ ◇ sᶜᵈ)  ≈⟨ ◇-congʳ {m₁ = sᵃ} $ ◇-congˡ {m₃ = sᶜᵈ} $ ≈-sym $ ↦0 B↦0 ⟩
             sᵃ ◇ (sᵇ ◇ sᶜᵈ) ≈⟨ ◇-congʳ {m₁ = sᵃ} ≡bcd ⟩
             sᵃ ◇ sᵇᶜᵈ       ≈⟨ ≡abcd ⟩
             s               ∎)
    , A↦1 , C↦1

  ↜ : (A ↦ 1 ∗ C ↦ 1)
    ⊢ (A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 1 ∗ A ↦ 0)
  ↜ (sᵃ , sᶜ , ≡s , A↦1 , C↦1)
    = sᵃ , sᶜ , ≡s , A↦1 , ∅ , sᶜ , (λ _ → refl) , (refl , (λ _ _ → refl)) , sᶜ , ∅ , (λ _ → Nat.+-identityʳ _) , C↦1 , refl , λ _ _ → refl

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
_↝⟨_⟩_ : ∀ A v B {vᵃ}{vᵇ}{v≤ : v ≤ vᵃ} →
  ⟨ A ↦ vᵃ ∗ B ↦ vᵇ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ (vᵃ ∸ v) ∗ B ↦ (vᵇ + v) ⟩
(A ↝⟨ v ⟩ B) {vᵃ}{vᵇ}{v≤ᵃ} {s} (s₁ , s₂ , ≡s , (As₁ , A∅) , (Bs₂ , B∅))
  with v ≤? s A
... | no v≰
  = ⊥-elim $ v≰ $ subst (v ≤_) (≡s A)
                $ subst (λ ◆ → v ≤ ◆ + s₂ A) (sym As₁)
                $ Nat.≤-stepsʳ (s₂ A) v≤ᵃ
... | yes v≤
  = ret↑ (_s₁′ , _s₂′ , ≡s′ , (As₁′ , A∅′) , (Bs₂′ , B∅′))
  where
    _s₁′ = s₁ [ A ↝ (_∸ v) ]
    _s₂′ = s₂ [ B ↝ (_+ v) ]

    _s′ = s [ A ↝ (_∸ v) ]
            [ B ↝ (_+ v) ]

    As₁′ : _s₁′ A ≡ vᵃ ∸ v
    As₁′ rewrite As₁ | ≟-refl A = refl

    A∅′ : ∀ k → k ≢ A → _s₁′ k ≡ 0
    A∅′ k k≢ rewrite dec-no (k ≟ A) k≢ .proj₂ = A∅ k k≢

    Bs₂′ : _s₂′ B ≡ vᵇ + v
    Bs₂′ rewrite Bs₂ | ≟-refl B = refl

    B∅′ : ∀ k → k ≢ B → _s₂′ k ≡ 0
    B∅′ k k≢ rewrite dec-no (k ≟ B) k≢ .proj₂ = B∅ k k≢

    v≤′ : v ≤ vᵃ + vᵇ
    v≤′ rewrite sym As₁ | sym Bs₂ = Nat.≤-stepsʳ (s₂ B) v≤ᵃ

    ≡s′ : ⟨ _s₁′ ◇ _s₂′ ⟩≡ _s′
    ≡s′ k
      rewrite sym $ ≡s k
      with k ≟ A | k ≟ B
    ≡s′ k | yes refl | yes refl -- ∙ k ≡ A ≡ B
      rewrite ≟-refl A | ≟-refl B | As₁ | Bs₂
      = begin (vᵃ ∸ v) + (vᵇ + v) ≡˘⟨ Nat.+-∸-comm _ v≤ᵃ ⟩
              vᵃ + (vᵇ + v) ∸ v   ≡⟨ cong (_∸ v) $ sym $ Nat.+-assoc _ vᵇ v ⟩
              (vᵃ + vᵇ) + v ∸ v   ≡⟨ Nat.m+n∸n≡m _ v ⟩
              (vᵃ + vᵇ)           ≡˘⟨ Nat.m∸n+n≡m v≤′ ⟩
              (vᵃ + vᵇ) ∸ v + v   ∎ where open ≡-Reasoning
    ≡s′ k | yes refl | no k≢B -- ∙ k ≡ A
      rewrite ≟-refl A | As₁
      = sym $ Nat.+-∸-comm _ v≤ᵃ
    ≡s′ k | no k≢A   | yes refl -- ∙ k ≡ B
      rewrite ≟-refl B | Bs₂
      = sym $ Nat.+-assoc _ vᵇ v
    ≡s′ k | no k≢A   | no k≢B -- ∙ k ∉ {A, B}
      = refl

_↝⁰_ : ∀ A B → ⟨ A ↦ v ∗ B ↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ 0 ∗ B ↦ (v′ + v) ⟩
_↝⁰_ {v = v} {v′ = v′} A B with p ← (A ↝⟨ v ⟩ B) {vᵇ = v′} {v≤ = ≤-refl {x = v}} rewrite Nat.n∸n≡0 v = p

_↜⟨_⟩_ : ∀ A v B {vᵃ}{vᵇ}{v≤ : v ≤ vᵇ} → ⟨ A ↦ vᵃ ∗ B ↦ vᵇ ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (vᵃ + v) ∗ B ↦ (vᵇ ∸ v) ⟩
(A ↜⟨ v ⟩ B) {vᵃ}{vᵇ}{v≤} (s₁ , s₂ , ≡s , As₁ , Bs₂)
  = map↑ (λ where (s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′) → s₂′ , s₁′ , ◇≡-comm {x = s₁′} ≡s′ , Bs₂′ , As₁′)
         ((B ↝⟨ v ⟩ A) {v≤ = v≤} (s₂ , s₁ , ◇≡-comm {x = s₁} ≡s , Bs₂ , As₁))

_↜⁰_ : ∀ A B → ⟨ A ↦ v′ ∗ B ↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (v′ + v) ∗ B ↦ 0 ⟩
_↜⁰_ {v′ = v′} {v = v} A B with p ← (A ↜⟨ v ⟩ B) {vᵃ = v′} {v≤ = ≤-refl {x = v}} rewrite Nat.n∸n≡0 v = p
