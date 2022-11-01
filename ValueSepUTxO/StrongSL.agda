{-# OPTIONS --allow-unsolved-metas #-}
---------------------------
-- ** Separation logic (SL)

module ValueSepUTxO.StrongSL where

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

open import ValueSepUTxO.Maps
open import ValueSepUTxO.UTxO
open import ValueSepUTxO.Ledger
open import ValueSepUTxO.StrongHoareLogic

⊎-⟦⟧ᵗ : ∀ s₁′ →
  ∙ ⟦ t ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ⊎ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁′ ⊎ s₂ ⟩≡_) (⟦ t ⟧ s)
⊎-⟦⟧ᵗ {t}{s₁}{s₂}{s} s₁′ eq (s₁♯s₂ , ≡s)
  with isValidTx? t s₁
... | yes valid-s₁
  with isValidTx? t s
... | no ¬valid
  = ⊥-elim $ ¬valid $ record
    { validOutputRefs = vor
    ; preservesValues = pv
    ; noDoubleSpending = valid-s₁ .noDoubleSpending
    ; allInputsValidate = valid-s₁ .allInputsValidate
    ; validateValidHashes = vvh
    }
  where
    pv : M.Any.Any (λ q → t .forge + q ≡ ∑ (t .outputs) value)
                   (∑M (map (getSpentOutput s) (t .inputs)) value)
    pv = {!!}

    vor : All (_∈ᵈ s) (outputRefs t)
    vor = {!!}

    vvh : All (λ i → M.Any.Any (λ o → o .address ≡ i .validator ♯) (getSpentOutput s i))
              (t .inputs)
    vvh = {!!}

... | yes valid-s
  = ret↑ (s₁♯s₂′ , ≡s′)
  where
    s₁≡ : s₁′ ≡ (s₁ ─ outputRefs t) ∪ utxoTxS t
    s₁≡ = sym $ M.just-injective eq

    s₁♯s₂′ : s₁′ ♯ s₂
    s₁♯s₂′ = {!!}

    ≡s′ : s₁′ ∪ s₂ ≈ ((s ─ outputRefs t) ∪ utxoTxS t)
    ≡s′ = {!!}

⊎-⟦⟧ᵗ˘ : ∀ s₂′ →
  ∙ ⟦ t ⟧ s₂ ≡ just s₂′
  ∙ ⟨ s₁ ⊎ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁ ⊎ s₂′ ⟩≡_) (⟦ t ⟧ s)
⊎-⟦⟧ᵗ˘ {t}{s₂}{s₁}{s} s₂′ ⟦t⟧s≡ ≡s
  with ⟦ t ⟧ s | ⊎-⟦⟧ᵗ {t = t}{s₂}{s₁} s₂′ ⟦t⟧s≡ (⊎≡-comm {x = s₁}{s₂} ≡s)
... | just _ | ret↑ ≡s′ = ret↑ (⊎≡-comm {x = s₂′}{s₁} ≡s′)

⊎-⟦⟧ : ∀ s₁′ →
  ∙ ⟦ l ⟧ s₁ ≡ just s₁′
  ∙ ⟨ s₁ ⊎ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁′ ⊎ s₂ ⟩≡_) (⟦ l ⟧ s)
⊎-⟦⟧ {l = []} _ refl p = ret↑ p
⊎-⟦⟧ {l = t ∷ l} {s₁ = s₁} {s₂} {s} s₁″ eq ≡s
  with ⟦ t ⟧ s₁ in ⟦t⟧s≡
... | just s₁′
  with ⟦ t ⟧ s | ⊎-⟦⟧ᵗ {t = t} {s₁ = s₁} {s₂ = s₂} s₁′ ⟦t⟧s≡ ≡s
... | just s′  | ret↑ s₁′⊎s₂≡s′
  with ⟦ l ⟧ s₁′ in ⟦l⟧s≡ | eq
... | just .s₁″           | refl
  = ⊎-⟦⟧ {l = l} {s₁ = s₁′} {s₂ = s₂} s₁″ ⟦l⟧s≡ s₁′⊎s₂≡s′

⊎-⟦⟧˘ : ∀ s₂′ →
  ∙ ⟦ l ⟧ s₂ ≡ just s₂′
  ∙ ⟨ s₁ ⊎ s₂ ⟩≡ s
    ────────────────────────────────
    lift↑ (⟨ s₁ ⊎ s₂′ ⟩≡_) (⟦ l ⟧ s)
⊎-⟦⟧˘ {l = l} {s₂ = s₂} {s₁} {s} s₂′ eq ≡s
  with ⟦ l ⟧ s | ⊎-⟦⟧ {l = l} {s₁ = s₂} {s₁} {s} s₂′ eq (⊎≡-comm {x = s₁}{s₂} ≡s)
... | just _ | ret↑ ≡s′ = ret↑ (⊎≡-comm {x = s₂′}{s₁} ≡s′)


_-supports-_ : List TxOutputRef → Assertion → Set
sup -supports- P = ∀ (s : S) → P s ↔ P (filterKeys (_∈? sup) s)

instance
  -- Apart-or : TxOutputRef // Assertion
  -- Apart-or ._♯_ or P = ¬ or -supports- P
  -- Apart-or ._♯_ or P = ∀ (s : S) → (P s ↔ P (s ─ [ or ]))
  --                                × (∀ (o : TxOutput) → P s ↔ P (s ∪ singleton (or , o)))

  Apart-L : L // Assertion
  -- Apart-L ._♯_ l P = All (λ or → or ♯ P) (concatMap outputRefs l)
  Apart-L ._♯_ l P = (_-supports- P) ⊆¹ (Disjoint $ concatMap outputRefs l)

-- The proof of the frame rule from separation logic, allowing us to prove formulas in minimal contexts
-- and then weaken our results to the desired context.
[FRAME] : ∀ R →
  ∙ l ♯ R
  ∙ ⟨ P ⟩ l ⟨ Q ⟩
    ─────────────────────
    ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩

{- Not provable without freshness side-conditions (i.e. l ♯ R).

Counter-example:

✓ ⟨ t₀₀ ↦ 1 at A ⟩
  t₁
  ⟨ t₁₀ ↦ 1 at B ⟩

¬ ⟨ t₀₀ ↦ 1 at A ∗ t₁₀ ↦ 2 at A ⟩
  t₁
  ⟨ t₁₀ ↦ 1 at B ∗ t₁₀ ↦ 2 at A ⟩

Alternatives:
  ∙ Allow key repetitions (e.g. `t₁₀`) and argue about a sensible genesis configuration.
  ∙ ⋯
-}

[FRAME] {l}{P}{Q} R l♯R PlQ {s} (s₁ , s₂ , ≡s , Ps₁ , Rs₂)
  with ⟦ l ⟧ s₁ in s₁≡ | PlQ Ps₁
... | .just s₁′ | ret↑ Qs₁′
  with ⟦ l ⟧ s in s≡ | ⊎-⟦⟧ {l = l} {s₁ = s₁} {s₂ = s₂} s₁′ s₁≡ ≡s
... | .just s′ | ret↑ ≡s′
    = ret↑ (s₁′ , s₂ , ≡s′ , Qs₁′ , Rs₂)

open HoareReasoning
ℝ[FRAME] : ∀ R →
  ∙ l ♯ R
  ∙ ℝ⟨ P ⟩ l ⟨ Q ⟩
    ─────────────────────
    ℝ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
ℝ[FRAME] {l = l} R l♯R PlQ = mkℝ [FRAME] {l = l} R l♯R (begin PlQ)
