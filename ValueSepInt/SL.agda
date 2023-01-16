---------------------------
-- ** Separation logic (SL)

open import Prelude.Init hiding (_+_); open SetAsType
open Integer using (_+_; _-_)
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

module ValueSepInt.SL (Part : Type) ⦃ _ : DecEq Part ⦄ where

open import ValueSepInt.Maps {K = Part}
open import ValueSepInt.Ledger Part ⦃ it ⦄
open import ValueSepInt.HoareLogic Part ⦃ it ⦄
open import ValueSepInt.HoareProperties Part ⦃ it ⦄

≈-[↝] : ∀ (A : Part) s s′ {f : Op₁ V} →
  s ≈ s′
  ──────────────────────────
  s [ A ↝ f ] ≈ s′ [ A ↝ f ]
≈-[↝] A s s′ s≈ k rewrite s≈ k = refl

≈-[↝]² : ∀ (A B : Part) s s′ {f g : Op₁ V} →
  s ≈ s′
  ──────────────────────────────────────────────
  s [ A ↝ f ] [ B ↝ g ] ≈ s′ [ A ↝ f ] [ B ↝ g ]
≈-[↝]² A B s s′ s≈ k rewrite s≈ k = refl

◇≡-[↝+] : ∀ A v →
  ────────────────────────────────────────────────────────
  ⟨ (s₁ [ A ↝ (_+ v) ]) ◇ s₂ ⟩≡ ((s₁ ◇ s₂) [ A ↝ (_+ v) ])
◇≡-[↝+] {s₁ = s₁} {s₂ = s₂} A v k with k ≟ A
... | yes refl = ◇-assoc-comm (s₁ A) v (s₂ A)
... | no _ = refl

◇≡-[↝-] : ∀ A v →
  ────────────────────────────────────────────────────────
  ⟨ (s₁ [ A ↝ (_- v) ]) ◇ s₂ ⟩≡ ((s₁ ◇ s₂) [ A ↝ (_- v) ])
◇≡-[↝-] {s₁ = s₁} {s₂ = s₂} A v k with k ≟ A
... | yes refl = ◇-assoc-comm (s₁ A) (Integer.- v) (s₂ A)
... | no _ = refl

◇-⟦⟧ᵗ :
  ⟨ s₁ ◇ s₂ ⟩≡ s
  ────────────────────────────────
  ⟨ ⟦ t ⟧ s₁ ◇ s₂ ⟩≡ ⟦ t ⟧ s
◇-⟦⟧ᵗ {s₁}{s₂}{s}{t@(A —→⟨ v ⟩ B)} ≡s =
  begin
    (s₁ [ A ↝ (_- v) ] [ B ↝ (_+ v) ]) ◇ s₂
  ≈⟨ ◇≡-[↝+] {s₁ = s₁ [ A ↝ (_- v) ]} {s₂ = s₂} B v ⟩
    ((s₁ [ A ↝ (_- v) ]) ◇ s₂) [ B ↝ (_+ v) ]
  ≈⟨ (λ k → cong (if k == B then _+ v else id)
   $ ◇≡-[↝-] {s₁ = s₁} {s₂ = s₂} A v k)
   ⟩
    (s₁ ◇ s₂) [ A ↝ (_- v) ] [ B ↝ (_+ v) ]
  ≈⟨ ≈-[↝]² _ _ (s₁ ◇ s₂) s ≡s ⟩
    s [ A ↝ (_- v) ] [ B ↝ (_+ v) ]
  ∎ where open ≈-Reasoning

◇-⟦⟧ᵗ˘ :
  ⟨ s₁ ◇ s₂ ⟩≡ s
  ──────────────────────────
  ⟨ s₁ ◇ ⟦ t ⟧ s₂ ⟩≡ ⟦ t ⟧ s
◇-⟦⟧ᵗ˘ {s₁}{s₂}{s}{t}
  = ◇≡-comm {x = ⟦ t ⟧ s₂}
  ∘ ◇-⟦⟧ᵗ
  ∘ ◇≡-comm {x = s₁}

◇-⟦⟧ :
  ⟨ s₁ ◇ s₂ ⟩≡ s
  ─────────────────────
  ⟨ ⟦ l ⟧ s₁ ◇ s₂ ⟩≡ ⟦ l ⟧ s
◇-⟦⟧ {l = []} p = p
◇-⟦⟧ {l = t ∷ l} = ◇-⟦⟧ {l = l} ∘ ◇-⟦⟧ᵗ {t = t}

◇-⟦⟧˘ :
  ⟨ s₁ ◇ s₂ ⟩≡ s
  ─────────────────────
  ⟨ s₁ ◇ ⟦ l ⟧ s₂ ⟩≡ ⟦ l ⟧ s
◇-⟦⟧˘ {s₁}{s₂}{s}{l}
  = ◇≡-comm {x = ⟦ l ⟧ s₂}
  ∘ ◇-⟦⟧ {l = l}
  ∘ ◇≡-comm {x = s₁}

-- The proof of the frame rule from separation logic, allowing us to prove formulas in minimal contexts
-- and then weaken our results to the desired context.
[FRAME] : ∀ R →
  -- l ♯ R
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
[FRAME] {P}{l}{Q} R PlQ {s} (s₁ , s₂ , ≡s , Ps₁ , Rs₂) =
  ⟦ l ⟧ s₁ , s₂ , ◇-⟦⟧ {l = l} ≡s , PlQ Ps₁ , Rs₂

open HoareReasoning
ℝ[FRAME] : ∀ R →
  ℝ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ℝ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
ℝ[FRAME] {l = l} R (mkℝ PlQ) = mkℝ [FRAME] {l = l} R PlQ
