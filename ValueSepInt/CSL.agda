---------------------------------------
-- ** Concurrent separation logic (CSL)

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists
open import Prelude.InferenceRules

module ValueSepInt.CSL (Part : Type) ⦃ _ : DecEq Part ⦄ where

open import ValueSepInt.Maps {K = Part}
open import ValueSepInt.Ledger Part ⦃ it ⦄
open import ValueSepInt.HoareLogic Part ⦃ it ⦄
open import ValueSepInt.SL Part ⦃ it ⦄

◇-interleave :
  ∙ (l₁ ∥ l₂ ≡ l)
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ──────────────────────────────────
    ⟨ ⟦ l₁ ⟧ s₁ ◇ ⟦ l₂ ⟧ s₂ ⟩≡ ⟦ l ⟧ s
◇-interleave [] = id
◇-interleave {l = t ∷ _}     (keepˡ ≡l) = ◇-interleave ≡l ∘ ◇-⟦⟧ᵗ {t = t}
◇-interleave {l = t ∷ _}{s₁} (keepʳ ≡l) = ◇-interleave ≡l ∘ ◇-⟦⟧ᵗ˘ {s₁}{t = t}

-- ** Proof of CSL's [PAR] rule, which allows for modular reasoning.
[PAR] :
  ∙ l₁ ∥ l₂ ≡ l
  ∙ ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  ∙ ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
    ─────────────────────────
    ⟨ P₁ ∗ P₂ ⟩ l ⟨ Q₁ ∗ Q₂ ⟩
[PAR] {l₁} {l₂} {l} ≡l Pl₁Q Pl₂Q {s} (s₁ , s₂ , ≡s , Ps₁ , Ps₂) =
  ⟦ l₁ ⟧ s₁ , ⟦ l₂ ⟧ s₂ , ◇-interleave ≡l ≡s , Pl₁Q Ps₁ , Pl₂Q Ps₂

open HoareReasoning
ℝ[PAR] :
  ∙ l₁ ∥ l₂ ≡ l
  ∙ ℝ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  ∙ ℝ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
    ─────────────────────────
    ℝ⟨ P₁ ∗ P₂ ⟩ l ⟨ Q₁ ∗ Q₂ ⟩
ℝ[PAR] ≡l PlQ (mkℝ PlQ′) = mkℝ [PAR] ≡l (begin PlQ) PlQ′
