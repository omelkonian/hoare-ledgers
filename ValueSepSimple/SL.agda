---------------------------
-- ** Separation logic (SL)

open import Prelude.Init
open L.Mem
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Semigroup
open import Prelude.Functor
open import Prelude.Monoid
open import Prelude.Setoid

module ValueSepSimple.SL (Part : Set) ⦃ _ : DecEq Part ⦄ where

open import ValueSepSimple.Maps {K = Part}
open import ValueSepSimple.Ledger Part ⦃ it ⦄
open import ValueSepSimple.HoareLogic Part ⦃ it ⦄

≈-[↝] : ∀ (A : Part) s s′ {f : Op₁ ℕ} →
  s ≈ s′
  ──────────────────────────
  s [ A ↝ f ] ≈ s′ [ A ↝ f ]
≈-[↝] A s s′ s≈ k rewrite s≈ k = refl

≈-[↝]² : ∀ (A B : Part) s s′ {f g : Op₁ ℕ} →
  s ≈ s′
  ──────────────────────────────────────────────
  s [ A ↝ f ] [ B ↝ g ] ≈ s′ [ A ↝ f ] [ B ↝ g ]
≈-[↝]² A B s s′ s≈ k rewrite s≈ k = refl

◇≡-[↝+] : ∀ A v →
  ────────────────────────────────────────────────────────
  ⟨ (s₁ [ A ↝ (_+ v) ]) ◇ s₂ ⟩≡ ((s₁ ◇ s₂) [ A ↝ (_+ v) ])
◇≡-[↝+] {s₁ = s₁} {s₂ = s₂} A v k
  with k ≟ A
... | yes refl
  with v₁ ← s₁ A
  with v₂ ← s₂ A
  rewrite Nat.+-assoc v₁ v v₂
        | Nat.+-comm v v₂
        | sym $ Nat.+-assoc v₁ v₂ v = refl
... | no _ = refl

◇≡-[↝∸] : ∀ A v vᵃ →
  ∙ (_[_↦_] s₁ A vᵃ)
  ∙ v ≤ vᵃ
    ────────────────────────────────────────────────────────
    ⟨ (s₁ [ A ↝ (_∸ v) ]) ◇ s₂ ⟩≡ ((s₁ ◇ s₂) [ A ↝ (_∸ v) ])
◇≡-[↝∸] {s₁ = s₁} {s₂ = s₂} A v vᵃ A∈ v≤ k
  with k ≟ A
◇≡-[↝∸] {s₁ = s₁} {s₂ = s₂} A v vᵃ A∈ v≤ k | yes refl
  with s₁ A | A∈
... | .vᵃ | refl
  = sym $ Nat.+-∸-comm _ v≤
◇≡-[↝∸] {s₁ = s₁} {s₂ = s₂} A v vᵃ A∈ v≤ k | no _
  = refl

◇-⟦⟧ᵗ : ∀ s₁′ →
  ∙ ⟦ t ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁′ ◇ s₂ ⟩≡_) (⟦ t ⟧ s)
◇-⟦⟧ᵗ {t@(A —→⟨ v ⟩ B)}{s₁}{s₂}{s} s₁′ ⟦t⟧s≡ ≡s
  rewrite sym $ ≡s A | sym $ ≡s B
  with vᵃ ← s₁ A in s₁≡
  with vᵇ ← s₁ B
  with v ≤? vᵃ
... | yes v≤
  rewrite sym (M.just-injective ⟦t⟧s≡)
  with v ≤? vᵃ ◇ s₂ A
... | no v≰ = ⊥-elim $ v≰ $ Nat.≤-stepsʳ (s₂ A) v≤
... | yes _ = ret↑ qed
  where
    _s₁′ = s₁ [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]
    _s′  = s  [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]

    qed : ⟨ _s₁′ ◇ s₂ ⟩≡ _s′
    qed =
      begin
        _s₁′ ◇ s₂
      ≈⟨ ◇≡-[↝+] {s₁ = s₁ [ A ↝ (_∸ v) ]} {s₂ = s₂} B v ⟩
        ((s₁ [ A ↝ (_∸ v) ]) ◇ s₂) [ B ↝ (_+ v) ]
      ≈⟨ (λ k → cong (if k == B then _+ v else id) (◇≡-[↝∸] {s₁ = s₁} {s₂ = s₂} A v _ refl (subst (v ≤_) (sym s₁≡) v≤) k)) ⟩
        (s₁ ◇ s₂) [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]
      ≈⟨ ≈-[↝]² A B (s₁ ◇ s₂) s ≡s ⟩
        _s′
      ∎ where open ≈-Reasoning

◇-⟦⟧ᵗ˘ : ∀ s₂′ →
  ∙ ⟦ t ⟧ s₂ ≡ just s₂′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁ ◇ s₂′ ⟩≡_) (⟦ t ⟧ s)
◇-⟦⟧ᵗ˘ {t@(A —→⟨ v ⟩ B)}{s₂}{s₁}{s} s₂′ ⟦t⟧s≡ ≡s
  with ⟦ t ⟧ s | ◇-⟦⟧ᵗ {t = t}{s₂}{s₁} s₂′ ⟦t⟧s≡ (◇≡-comm {x = s₁}{s₂} ≡s)
... | just _ | ret↑ ≡s′ = ret↑ (◇≡-comm {x = s₂′}{s₁} ≡s′)

◇-⟦⟧ : ∀ s₁′ →
  ∙ ⟦ l ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁′ ◇ s₂ ⟩≡_) (⟦ l ⟧ s)
◇-⟦⟧ {l = []} _ refl p = ret↑ p
◇-⟦⟧ {l = t ∷ l} {s₁ = s₁} {s₂} {s} s₁″ eq ≡s
  with ⟦ t ⟧ s₁ in ⟦t⟧s≡
... | just s₁′
  with ⟦ t ⟧ s | ◇-⟦⟧ᵗ {t = t} {s₁ = s₁} {s₂ = s₂} s₁′ ⟦t⟧s≡ ≡s
... | just s′  | ret↑ s₁′◇s₂≡s′
  with ⟦ l ⟧ s₁′ in ⟦l⟧s≡ | eq
... | just .s₁″           | refl
  = ◇-⟦⟧ {l = l} {s₁ = s₁′} {s₂ = s₂} s₁″ ⟦l⟧s≡ s₁′◇s₂≡s′

◇-⟦⟧˘ : ∀ s₂′ →
  ∙ ⟦ l ⟧ s₂ ≡ just s₂′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁ ◇ s₂′ ⟩≡_) (⟦ l ⟧ s)
◇-⟦⟧˘ {l = l} {s₂ = s₂} {s₁} {s} s₂′ eq ≡s
  with ⟦ l ⟧ s | ◇-⟦⟧ {l = l} {s₁ = s₂} {s₁} {s} s₂′ eq (◇≡-comm {x = s₁}{s₂} ≡s)
... | just _ | ret↑ ≡s′ = ret↑ (◇≡-comm {x = s₂′}{s₁} ≡s′)

-- The proof of the frame rule from separation logic, allowing us to prove formulas in minimal contexts
-- and then weaken our results to the desired context.
[FRAME] : ∀ R →
  -- l ♯ R
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
[FRAME] {P}{l}{Q} R PlQ {s} (s₁ , s₂ , ≡s , Ps₁ , Rs₂)
  with ⟦ l ⟧ s₁ in s₁≡ | PlQ Ps₁
... | .just s₁′ | ret↑ Qs₁′
  with ⟦ l ⟧ s in s≡ | ◇-⟦⟧ {l = l} {s₁ = s₁} {s₂ = s₂} s₁′ s₁≡ ≡s
... | .just s′ | ret↑ ≡s′
  = ret↑ (s₁′ , s₂ , ≡s′ , Qs₁′ , Rs₂)

open HoareReasoning
ℝ[FRAME] : ∀ R →
  ℝ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ℝ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
ℝ[FRAME] {l = l} R PlQ = mkℝ [FRAME] {l = l} R (begin PlQ)
