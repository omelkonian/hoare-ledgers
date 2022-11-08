---------------------------
-- ** Separation logic (SL)
{-# OPTIONS --allow-unsolved #-}
open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Apartness
open import Prelude.Semigroup
open import Prelude.Functor
open import Prelude.Monoid

module ValueSep.WeakSL (Part : Type) ⦃ _ : DecEq Part ⦄ where

open import ValueSep.Maps
open import ValueSep.Ledger Part ⦃ it ⦄
open import ValueSep.WeakHoareLogic Part ⦃ it ⦄

instance
  -- extensional version of disjointness
  Denotable//Assertion : ∀ {A : Type} → ⦃ Denotable A ⦄ → A // Assertion
  Denotable//Assertion ._♯_ x P = ∀ s → P s ⇔ lift↑ P (⟦ x ⟧ s)

≈-[↝] : ∀ (k A : Part) s s′ {f : Op₁ ℕ} →
  s ≈ s′
  ──────────────────────────────────
  (s [ A ↝ f ]) k ≡ (s′ [ A ↝ f ]) k
≈-[↝] k A s s′ s≈ rewrite s≈ k = refl

≈-[↝]² : ∀ (k A B : Part) s s′ {f g : Op₁ ℕ} →
  s ≈ s′
  ──────────────────────────────────
  (s [ A ↝ f ] [ B ↝ g ]) k ≡ (s′ [ A ↝ f ] [ B ↝ g ]) k
≈-[↝]² k A B s s′ s≈ rewrite s≈ k = refl


◇≡-[↝+] : ∀ A v →
  A ∈ᵈ s₁
  ────────────────────────────────────────────────────────
  ⟨ (s₁ [ A ↝ (_+ v) ]) ◇ s₂ ⟩≡ ((s₁ ◇ s₂) [ A ↝ (_+ v) ])
◇≡-[↝+] {s₁ = s₁} {s₂ = s₂} A v A∈ k
  with k ≟ A
◇≡-[↝+] {s₁ = s₁} {s₂ = s₂} A v A∈ k | yes refl
  with s₁ A | A∈
... | just v₁ | _
  with s₂ A
... | nothing = refl
... | just v₂ rewrite Nat.+-assoc v₁ v v₂ | Nat.+-comm v v₂ | sym $ Nat.+-assoc v₁ v₂ v = refl
◇≡-[↝+] {s₁ = s₁} {s₂ = s₂} A v A∈ k | no _
  with s₁ k | s₂ k
... | nothing | nothing = refl
... | nothing | just _  = refl
... | just  _ | nothing = refl
... | just  _ | just _  = refl

◇≡-[↝∸] : ∀ A v vᵃ →
  ∙ (_[_↦_] s₁ A vᵃ)
  ∙ v ≤ vᵃ
    ────────────────────────────────────────────────────────
    ⟨ (s₁ [ A ↝ (_∸ v) ]) ◇ s₂ ⟩≡ ((s₁ ◇ s₂) [ A ↝ (_∸ v) ])
◇≡-[↝∸] {s₁ = s₁} {s₂ = s₂} A v vᵃ A∈ v≤ k
  with k ≟ A
◇≡-[↝∸] {s₁ = s₁} {s₂ = s₂} A v vᵃ A∈ v≤ k | yes refl
  with s₁ A | A∈
... | .(just vᵃ) | refl
  with s₂ A
... | nothing = refl
... | just _  = cong just $ sym $ Nat.+-∸-comm _ v≤
◇≡-[↝∸] {s₁ = s₁} {s₂ = s₂} A v vᵃ A∈ v≤ k | no _
  with s₁ k | s₂ k
... | nothing | nothing = refl
... | nothing | just _  = refl
... | just  _ | nothing = refl
... | just  _ | just _  = refl

  -- ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
  -- ∙ t .sender ∉ᵈ s₁
  -- ∙ R s₂
  -- ∙ t ♯ R
  --   ────────────────────────────────
  --   t .sender ∉ᵈ s

◇-⟦⟧ᵗ⁻ :

  ∙ ⟦ t ⟧ s₁ ≡ nothing
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
  ∙ R s₂
  ∙ t ♯ R
    ────────────────────────────────
    ⟦ t ⟧ s ≡ nothing
◇-⟦⟧ᵗ⁻ {t@(A —→⟨ v ⟩ B)}{s₁}{s₂}{s}{R} ⟦t⟧s≡ ≡s Rs₂ t♯R
  = {!!}


◇-⟦⟧ᵗ : ∀ s₁′ →
  ∙ ⟦ t ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁′ ◇ s₂ ⟩≡_) (⟦ t ⟧ s)
◇-⟦⟧ᵗ {t@(A —→⟨ v ⟩ B)}{s₁}{s₂}{s} s₁′ ⟦t⟧s≡ ≡s
  rewrite sym $ ≡s A | sym $ ≡s B
  with s₁ A in As₁ | s₁ B in Bs₁
... | just vᵃ | just vᵇ
  with ↦-◇ˡ {s₁ = s₁}{A}{vᵃ}{s₂} As₁ | ↦-◇ˡ {s₁ = s₁}{B}{vᵇ}{s₂} Bs₁
... | .(s₂ ⁉⁰ A) , refl , p | .(s₂ ⁉⁰ B) , refl , q
  with v ≤? vᵃ
... | yes v≤
  rewrite sym (M.just-injective ⟦t⟧s≡)
  rewrite just-◇ˡ vᵃ (s₂ A) | just-◇ˡ vᵇ (s₂ B)
  with v ≤? vᵃ ◇ (s₂ ⁉⁰ A)
... | no v≰ = ⊥-elim $ v≰ $ Nat.≤-stepsʳ (s₂ ⁉⁰ A) $ v≤
... | yes _ = ret↑ qed
  where
    _s₁′ = s₁ [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]
    _s′  = s  [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]

    B∈₁ : B ∈ᵈ s₁
    B∈₁ rewrite Bs₁ = auto

    B∈₁′ : B ∈ᵈ (s₁ [ A ↝ (_∸ v) ])
    B∈₁′ = [↝]-mono A (_∸ v) s₁ B B∈₁

    qed : ⟨ _s₁′ ◇ s₂ ⟩≡ _s′
    qed k
      = begin
        (_s₁′ ◇ s₂) k
      ≡⟨⟩
        ((s₁ [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]) ◇ s₂) k
      ≡⟨ ◇≡-[↝+] {s₁ = s₁ [ A ↝ (_∸ v) ]} {s₂ = s₂} B v B∈₁′ k ⟩
        (((s₁ [ A ↝ (_∸ v) ]) ◇ s₂) [ B ↝ (_+ v) ]) k
      ≡⟨ (cong (fmap (if k == B then (_+ v) else id)) $ ◇≡-[↝∸] {s₁ = s₁} {s₂ = s₂} A v vᵃ As₁ v≤ k) ⟩
        ((s₁ ◇ s₂) [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]) k
      ≡⟨ ≈-[↝]² k A B (s₁ ◇ s₂) s ≡s ⟩
        (s [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]) k
      ≡⟨⟩
        _s′ k
      ∎ where open ≡-Reasoning

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
... | nothing  | ret∅ = ret∅
... | just s′  | ret↑ s₁′◇s₂≡s′
  with ⟦ l ⟧ s₁′ in ⟦l⟧s≡ | eq
... | just .s₁″           | refl
  = ◇-⟦⟧ {l = l} {s₁ = s₁′} {s₂ = s₂} s₁″ ⟦l⟧s≡ s₁′◇s₂≡s′

◇-⟦⟧⁻ :

  ∙ ⟦ l ⟧ s₁ ≡ nothing
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
  ∙ R s₂
  ∙ l ♯ R
    ────────────────────────────────
    ⟦ l ⟧ s ≡ nothing
◇-⟦⟧⁻ {l = t ∷ l} {s₁ = s₁} {s₂} {s} ⟦l⟧s₁ ≡s Rs₂ l♯R = {!!}

-- The proof of the frame rule from separation logic, allowing us to prove formulas in minimal contexts
-- and then weaken our results to the desired context.
[FRAME] : ∀ R →
  ∙ l ♯ R
  ∙ ⟨ P ⟩ l ⟨ Q ⟩
    ─────────────────────
    ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
[FRAME] {l}{P}{Q} R l♯R PlQ {s} (s₁ , s₂ , ≡s , Ps₁ , Rs₂)
  with ⟦ l ⟧ s₁ in s₁≡ | PlQ Ps₁
... | nothing   | ret∅ rewrite ◇-⟦⟧⁻ {l = l} s₁≡ ≡s Rs₂ l♯R = ret∅
... | .just s₁′ | ret↑ Qs₁′
 with ⟦ l ⟧ s in s≡ | ◇-⟦⟧ {l = l} {s₁ = s₁} {s₂ = s₂} s₁′ s₁≡ ≡s
... | nothing  | ret∅ = ret∅
... | .just s′ | ret↑ ≡s′
  = ret↑ (s₁′ , s₂ , ≡s′ , Qs₁′ , Rs₂)
