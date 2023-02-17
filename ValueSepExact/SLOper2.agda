---------------------------
-- ** Separation logic (SL)

open import Prelude.Init; open SetAsType
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

module ValueSepExact.SLOper2 (Part : Type) ⦃ _ : DecEq Part ⦄ where

open import ValueSepExact.Maps {K = Part}
open import ValueSepExact.Ledger Part ⦃ it ⦄
open import ValueSepExact.HoareLogicOper Part ⦃ it ⦄

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

◇≡-[↝∸] : ∀ A v →
  ∙ v ≤ s₁ A
    ────────────────────────────────────────────────────────
    ⟨ (s₁ [ A ↝ (_∸ v) ]) ◇ s₂ ⟩≡ ((s₁ ◇ s₂) [ A ↝ (_∸ v) ])
◇≡-[↝∸] A _ v≤ k with k ≟ A
... | yes refl = sym $ Nat.+-∸-comm _ v≤
... | no  _    = refl

◇-⟦⟧ᵗ :
  ∙ [ t ] , s₁ —→ s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────
    ⟨ ⟦ t ⟧₀ s₁ ◇ s₂ ⟩≡ ⟦ t ⟧₀ s
◇-⟦⟧ᵗ {t@(A —→⟨ v ⟩ B)}{s₁}{_}{s₂}{s} (step v≤ base) ≡s =
  begin
    s₁ [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ] ◇ s₂
  ≈⟨ ◇≡-[↝+] {s₁ = s₁ [ A ↝ (_∸ v) ]} {s₂ = s₂} B v ⟩
    ((s₁ [ A ↝ (_∸ v) ]) ◇ s₂) [ B ↝ (_+ v) ]
  ≈⟨ (λ k → cong (if k == B then _+ v else id)
          $ ◇≡-[↝∸] {s₁ = s₁} {s₂ = s₂} A v v≤ k) ⟩
    (s₁ ◇ s₂) [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]
  ≈⟨ ≈-[↝]² A B (s₁ ◇ s₂) s ≡s ⟩
    s  [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]
  ∎ where open ≈-Reasoning

◇-⟦⟧ᵗ˘ :
  ∙ [ t ] , s₂ —→ s₂′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────
    ⟨ s₁ ◇ ⟦ t ⟧₀ s₂ ⟩≡ ⟦ t ⟧₀ s
◇-⟦⟧ᵗ˘ {s₁ = s₁} t→ = ◇≡-comm {y = s₁} ∘ ◇-⟦⟧ᵗ t→ ∘ ◇≡-comm {x = s₁}

◇-⟦⟧ :
  ∙ l  , s₁ —→ s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────
    ⟨ ⟦ l ⟧₀ s₁ ◇ s₂ ⟩≡ ⟦ l ⟧₀ s
◇-⟦⟧ {l = []} l→ = id
◇-⟦⟧ {l = _ ∷ _} (step v≤ l→) = ◇-⟦⟧ l→ ∘ ◇-⟦⟧ᵗ (step v≤ base)

◇-⟦⟧˘ :
  ∙ l  , s₂ —→ s₂′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────
    ⟨ s₁ ◇ ⟦ l ⟧₀ s₂ ⟩≡ ⟦ l ⟧₀ s
◇-⟦⟧˘ {s₁ = s₁} l→ = ◇≡-comm {y = s₁} ∘ ◇-⟦⟧ l→ ∘ ◇≡-comm {x = s₁}

-- The proof of the frame rule from separation logic, allowing us to prove formulas
-- in minimal contexts and then weaken our results to the desired context.
[FRAME] : ∀ R →
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
[FRAME] {P}{l}{Q} R PlQ {s} (s₁ , s₂ , ≡s , Ps₁ , Rs₂) l→
  rewrite oper⇒denot₀ l→
  =
  let
    s₁′ = ⟦ l ⟧₀ s₁
    s′  = ⟦ l ⟧₀ s
    l→′ : l , s₁ —→ s₁′
    l→′ = {!l→!}
    -- THIS APPROACH BREAKS HERE
    -- the frame rule doesn't hold as such anymore,
    -- since we are not guaranteed validity of l from {P}l{Q}
    ≡s′ : ⟨ s₁′ ◇ s₂ ⟩≡ s′
    ≡s′ = ◇-⟦⟧ {l = l} {s₁ = s₁} {s₂ = s₂} l→′ ≡s
  in
    s₁′ , s₂ , ≡s′ , PlQ Ps₁ l→′ , Rs₂
