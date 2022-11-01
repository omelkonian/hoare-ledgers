{-# OPTIONS --allow-unsolved-metas #-}
---------------------------
-- ** Separation logic (SL)

module ValueSepUTxO.AbstractSL where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Apartness
open import Prelude.Semigroup
open import Prelude.Functor
open import Prelude.Monoid
open import Prelude.Membership

open import Prelude.Bags
open import ValueSepUTxO.AbstractUTxO
open import ValueSepUTxO.AbstractLedger
open import ValueSepUTxO.AbstractHoareLogic

◇-⟦⟧ᵗ : ∀ s₁′ →
  ∙ ⟦ t ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁′ ◇ s₂ ⟩≡_) (⟦ t ⟧ s)
◇-⟦⟧ᵗ = {!!}
-- ◇-⟦⟧ᵗ {t@(A —→⟨ v ⟩ B)}{s₁}{s₂}{s} s₁′ ⟦t⟧s≡ ≡s
--   rewrite sym $ ≡s A | sym $ ≡s B
--   = ?

postulate
  ◇-⟦⟧ᵗ˘ : ∀ s₂′ →
    ∙ ⟦ t ⟧ s₂ ≡ just s₂′
    ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
      ────────────────────────────────
      lift↑ (⟨ s₁ ◇ s₂′ ⟩≡_) (⟦ t ⟧ s)


◇-⟦⟧ : ∀ s₁′ →
  ∙ ⟦ l ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁′ ◇ s₂ ⟩≡_) (⟦ l ⟧ s)
◇-⟦⟧ {l = []} _ refl p = ret↑ p
◇-⟦⟧ {l = t ∷ l} {s₁ = s₁} {s₂} {s} s₁″ eq ≡s
  = {!!}
--   with ⟦ t ⟧ s₁ in ⟦t⟧s≡
-- ... | just s₁′
--   with ⟦ t ⟧ s | ◇-⟦⟧ᵗ {t = t} {s₁ = s₁} {s₂ = s₂} s₁′ ⟦t⟧s≡ ≡s
-- ... | just s′  | ret↑ s₁′◇s₂≡s′
--   with ⟦ l ⟧ s₁′ in ⟦l⟧s≡ | eq
-- ... | just .s₁″           | refl
--   = ◇-⟦⟧ {l = l} {s₁ = s₁′} {s₂ = s₂} s₁″ ⟦l⟧s≡ s₁′◇s₂≡s′

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
  = {!!}

--   with ⟦ l ⟧ s in s≡ | ◇-⟦⟧ {l = l} {s₁ = s₁} {s₂ = s₂} s₁′ s₁≡ ≡s
-- ... | nothing | _
--   = {!!}
-- ... | just s′ | ret↑ ≡s′
-- -- ◇-⟦⟧ {l = l} {s₁ = s₁} {s₂ = s₂} s₁′ s₁≡ ≡s
--   = ret↑ (s₁′ , s₂ , {! !} , Qs₁′ , Rs₂)

--   with ⟦ l ⟧ s in s≡ | ◇-⟦⟧ {l = l} {s₁ = s₁} {s₂ = s₂} s₁′ s₁≡ ≡s
-- ... | .just s′ | ret↑ ≡s′
--   = ret↑ (s₁′ , s₂ , ≡s′ , Qs₁′ , Rs₂)

open HoareReasoning
ℝ[FRAME] : ∀ R →
  ℝ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ℝ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
ℝ[FRAME] {l = l} R PlQ = mkℝ [FRAME] {l = l} R (begin PlQ)
