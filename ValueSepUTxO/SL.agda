---------------------------
-- ** Separation logic (SL)

module ValueSepUTxO.SL where

open import Prelude.Init; open SetAsType
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
open import Prelude.Setoid
open import Prelude.ToList

open import Prelude.Bags
open import ValueSepUTxO.UTxO
open import ValueSepUTxO.Ledger
open import ValueSepUTxO.HoareLogic
open import ValueSepUTxO.HoareProperties

destruct-⟦t⟧≡ :
  ⟦ t ⟧ s ≡ just s′
  ───────────────────────────────
  IsValidTx t s × (⟦ t ⟧₀ s ≡ s′)
destruct-⟦t⟧≡ {t}{s} eq
  with isValidTx? t s | eq
... | yes valid | refl = valid , refl

IsValidTx-transport :
  (stxoTx t ⊆ˢ s → stxoTx t ⊆ˢ s′) →
  IsValidTx t s → IsValidTx t s′
IsValidTx-transport f (record
  { validOutputRefs     = vor
  ; preservesValues     = pv
  ; allInputsValidate   = aiv
  ; validateValidHashes = vvh })
  = record
  { validOutputRefs     = f vor
  ; preservesValues     = pv
  ; allInputsValidate   = aiv
  ; validateValidHashes = vvh
  }

IsValidTx-resp-≈ : (IsValidTx t) Respects _≈_
IsValidTx-resp-≈ {t}{s}{s′} eq =
  IsValidTx-transport λ vor →
    ⊆ˢ-trans {i = stxoTx t}{s}{s′} vor (eq .proj₁)

IsValidTx-◇ˡ : IsValidTx t s → IsValidTx t (s ◇ s′)
IsValidTx-◇ˡ {t}{s}{s′} = IsValidTx-transport λ vor →
  ⊆ˢ-trans {i = stxoTx t}{s}{s ◇ s′} vor (⊆ˢ-◇ˡ {s = s}{s′})

IsValidTx-◇ʳ : IsValidTx t s′ → IsValidTx t (s ◇ s′)
IsValidTx-◇ʳ {t}{s′}{s} = IsValidTx-resp-≈ (◇-comm s′ s) ∘ IsValidTx-◇ˡ {t}{s′}{s}

◇-⟦⟧ᵗ : ∀ s₁′ →
  ∙ ⟦ t ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁′ ◇ s₂ ⟩≡_) (⟦ t ⟧ s)
◇-⟦⟧ᵗ {t}{s₁}{s₂}{s} s₁′ ⟦t⟧≡ ≡s
  with val , ≡s′ ← destruct-⟦t⟧≡ ⟦t⟧≡
  rewrite dec-yes (isValidTx? t s)
          (IsValidTx-resp-≈ {t = t}{s₁ ◇ s₂}{s} ≡s $ IsValidTx-◇ˡ val)
          .proj₂
  = ret↑ QED
  where
    QED : s₁′ ◇ s₂ ≈ (s ─ stxoTx t) ◇ utxoTx t
    QED =
      begin
        s₁′ ◇ s₂
      ≈⟨ ◇-congˡ {s₁ = s₁′}{⟦ t ⟧₀ s₁}{s₂}
       $ ≈-sym {x = ⟦ t ⟧₀ s₁}{s₁′}
       $ ≈-reflexive ≡s′ ⟩
        ((s₁ ─ stxoTx t) ◇ utxoTx t) ◇ s₂
      ≈⟨ ◇-assocʳ (s₁ ─ stxoTx t) (utxoTx t) s₂ ⟩
        (s₁ ─ stxoTx t) ◇ (utxoTx t ◇ s₂)
      ≈⟨ ◇-congʳ {s₁ = s₁ ─ stxoTx t} $ ∪-comm (utxoTx t) s₂ ⟩
        (s₁ ─ stxoTx t) ◇ (s₂ ◇ utxoTx t)
      ≈˘⟨ ◇-assocʳ (s₁ ─ stxoTx t) s₂ (utxoTx t) ⟩
        ((s₁ ─ stxoTx t) ◇ s₂) ◇ utxoTx t
      ≈˘⟨ ◇-congˡ {s₁ = (s₁ ◇ s₂) ─ stxoTx t}{(s₁ ─ stxoTx t) ◇ s₂}{utxoTx t}
        $ ◇-─-commute {s = stxoTx t}{s₁}{s₂} (val .validOutputRefs) ⟩
        ((s₁ ◇ s₂) ─ stxoTx t) ◇ utxoTx t
      ≈⟨ ◇-congˡ {s₁ = (s₁ ◇ s₂) ─ stxoTx t}{s ─ stxoTx t}{utxoTx t}
        $ ─-congˡ {s = s₁ ◇ s₂}{s}{stxoTx t} ≡s ⟩
        (s ─ stxoTx t) ◇ utxoTx t
      ∎ where open ≈-Reasoning

◇-⟦⟧ᵗ˘ : ∀ s₂′ →
  ∙ ⟦ t ⟧ s₂ ≡ just s₂′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁ ◇ s₂′ ⟩≡_) (⟦ t ⟧ s)
◇-⟦⟧ᵗ˘ {t}{s₂}{s₁}{s} s₂′ ⟦t⟧≡ ≡s
  = M.Any.map (λ {s} → ◇≡-comm {s = s} {x = s₂′}{s₁})
  $ ◇-⟦⟧ᵗ {t}{s₂}{s₁}{s} s₂′ ⟦t⟧≡ (◇≡-comm {s = s} {x = s₁}{s₂} ≡s)

◇-⟦⟧ : ∀ s₁′ →
  ∙ ⟦ l ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁′ ◇ s₂ ⟩≡_) (⟦ l ⟧ s)
◇-⟦⟧ {l = []} _ refl p = ret↑ p
◇-⟦⟧ {l = t ∷ l} {s₁ = s₁} {s₂} {s} s₁″ eq ≡s
  with ⟦ t ⟧ s₁ in ⟦t⟧s≡
... | just s₁′
  with ⟦ t ⟧ s | ◇-⟦⟧ᵗ {t}{s₁}{s₂}{s} s₁′ ⟦t⟧s≡ ≡s
... | just s′  | ret↑ s₁′◇s₂≡s′
  with ⟦ l ⟧ s₁′ in ⟦l⟧s≡ | eq
... | just .s₁″           | refl
  = ◇-⟦⟧ {l}{s₁′}{s₂}{s′} s₁″ ⟦l⟧s≡ s₁′◇s₂≡s′

◇-⟦⟧˘ : ∀ s₂′ →
  ∙ ⟦ l ⟧ s₂ ≡ just s₂′
  ∙ ⟨ s₁ ◇ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁ ◇ s₂′ ⟩≡_) (⟦ l ⟧ s)
◇-⟦⟧˘ {l}{s₂}{s₁}{s} s₂′ ⟦t⟧≡ ≡s
  = M.Any.map (λ {s} → ◇≡-comm {s = s} {x = s₂′}{s₁})
  $ ◇-⟦⟧ {l}{s₂}{s₁}{s} s₂′ ⟦t⟧≡ (◇≡-comm {s = s} {x = s₁}{s₂} ≡s)

-- The proof of the frame rule from separation logic, allowing us to prove formulas in minimal contexts
-- and then weaken our results to the desired context.
[FRAME] : ∀ R →
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
[FRAME] {P}{l}{Q} R PlQ {s} (s₁ , s₂ , ≡s , Ps₁ , Rs₂)
  with ⟦ l ⟧ s₁ in s₁≡ | PlQ Ps₁
... | .just s₁′ | ret↑ Qs₁′
  with ⟦ l ⟧ s in s≡ | ◇-⟦⟧ {l}{s₁}{s₂}{s} s₁′ s₁≡ ≡s
... | .just s′ | ret↑ ≡s′
  = ret↑ (s₁′ , s₂ , ≡s′ , Qs₁′ , Rs₂)

[FRAME]˘ : ∀ R →
  ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ⟨ R ∗ P ⟩ l ⟨ R ∗ Q ⟩
[FRAME]˘ {P}{l}{Q} R
  = consequence {l = l} (λ {x} → ∗↔ {x = x}) (λ {x} → ∗↔ {x = x})
  ∘ [FRAME] {l = l} R

open HoareReasoning
ℝ[FRAME] : ∀ R →
  ℝ⟨ P ⟩ l ⟨ Q ⟩
  ─────────────────────
  ℝ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
ℝ[FRAME] {l = l} R PlQ = mkℝ [FRAME] {l = l} R (begin PlQ)
