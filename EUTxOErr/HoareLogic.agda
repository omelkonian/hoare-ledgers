-------------------------
-- ** Axiomatic semantics

module EUTxOErr.HoareLogic where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Ord
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Monad
open import Prelude.Apartness
open import Prelude.Maps

open import EUTxOErr.EUTxO
open import EUTxOErr.Ledger

open import Common.HoareLogic {S}{Tx} ⦃ it ⦄ public
open HoareReasoning

_[_↦_]∅ : S → TxOutputRef → TxOutput → Type
m [ k ↦ v ]∅ = m [ k ↦ v ] × ∀ k′ → k′ ≢ k → k′ ∉ᵈ m

private variable K V₁ V₂ : Type

emp : Assertion
emp m = ∀ k → k ∉ᵈ m

_∗_ : Op₂ Assertion
(P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → ⟨ s₁ ⊎ s₂ ⟩≡ s × P s₁ × Q s₂

_↦_ : TxOutputRef → TxOutput → Assertion
or ↦ o = _[ or ↦ o ]∅

infixr 10 _∗_
infix  11 _↦_

-- ** Lemmas about separating conjunction.

-- commutativity
∗↔ : P ∗ Q ⊢ Q ∗ P
∗↔ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) = s₂ , s₁ , ⊎≡-comm {x = s₁}{s₂} ≡s , Qs₂ , Ps₁

-- associativity
open import Prelude.Setoid
∗↝ : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R
∗↝ {x = s} (s₁ , s₂₃ , ≡s , Ps₁ , (s₂ , s₃ , ≡s₂₃ , Qs₂ , Rs₃)) =
  let ≡s₁₂ , s₁♯s₂ = ⊎≈-assocʳ {s₁ = s₁}{s₂ = s₂}{s₃} ≡s ≡s₂₃ in
  (s₁ ∪ s₂) , s₃ , ≡s₁₂ , (s₁ , s₂ , (s₁♯s₂ , ≈-refl) , Ps₁ , Qs₂) , Rs₃

↜∗ : (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R
↜∗ {x = s} (s₁₂ , s₃ , ≡s , (s₁ , s₂ , ≡s₁₂ , Ps₁ , Qs₂) , Rs₃) =
  let ≡s₂₃ , s₂♯s₃ = ⊎≈-assocˡ {s₃ = s₃}{s₁ = s₁}{s₂} ≡s ≡s₁₂ in
  s₁ , s₂ ∪ s₃ , ≡s₂₃ , Ps₁ , (s₂ , s₃ , (s₂♯s₃ , ≈-refl) , Qs₂ , Rs₃)

-- ** Useful lemmas when transferring a value between participants in the minimal context.

module _ {tx : Tx} {v frg : Value} {d : DATA} {B : Address} where
  postulate
    0⇒1 :
      tx ≡ record { inputs  = []
                  ; outputs = [ ⦉ d ⦊ v at B ]
                  ; forge   = frg }
      ─────────────────────────────────────────────────────
      ⟨ emp ⟩ [ tx ] ⟨ (tx ♯) indexed-at 0 ↦ ⦉ d ⦊ v at B ⟩

  𝟘⇒𝟙 :
    _
    ───────────────────
    ℝ⟨ _ ⟩ [ tx ] ⟨ _ ⟩
  𝟘⇒𝟙 = mkℝ_ ∘ 0⇒1

module _ {tx : Tx} {v frg v′ : Value} {d d′ : DATA} {B : Address}
         {or : TxOutputRef} {r : DATA} {val : Validator} (rtx : Resolved tx) where

  postulate
    1⇒1 :
      ∙ T $ call val (mkTxInfo tx rtx) r d
      ∙ tx ≡ record
          { inputs  = [ record {outputRef = or; validator = val; redeemer = r} ]
          ; outputs = [ ⦉ d′ ⦊ v′ at B ]
          ; forge   = frg }
        ────────────────────────────────────────────────
        ⟨ or ↦ ⦉ d ⦊ v at (val ♯) ⟩
        [ tx ]
        ⟨ (tx ♯) indexed-at 0 ↦ ⦉ d′ ⦊ (frg + v′) at B ⟩

  𝟙⇒𝟙 :
    ∙ _
    ∙ _
      ───────────────────
      ℝ⟨ _ ⟩ [ tx ] ⟨ _ ⟩
  𝟙⇒𝟙 = mkℝ_ ∘₂ 1⇒1

module _ {tx : Tx} {v frg v′ v″ : Value} {d d′ d″ : DATA} {B C : Address}
         {or : TxOutputRef} {r : DATA} {val : Validator} (rtx : Resolved tx) where

  postulate
    1⇒2 :
      ∙ T $ call val (mkTxInfo tx rtx) r d
      ∙ tx ≡ record
          { inputs  = [ record {outputRef = or; validator = val; redeemer = r} ]
          ; outputs = ⦉ d′ ⦊ v′ at B
                    ∷ ⦉ d″ ⦊ v″ at C
                    ∷ []
          ; forge   = frg }
        ────────────────────────────────────────────────
        ⟨ or ↦ ⦉ d ⦊ v at (val ♯) ⟩
        [ tx ]
        ⟨ (tx ♯) indexed-at 0 ↦ ⦉ d′ ⦊ v′ at B
        ∗ (tx ♯) indexed-at 1 ↦ ⦉ d″ ⦊ v″ at C ⟩

  𝟙⇒𝟚 :
    ∙ _
    ∙ _
      ───────────────────
      ℝ⟨ _ ⟩ [ tx ] ⟨ _ ⟩
  𝟙⇒𝟚 = mkℝ_ ∘₂ 1⇒2
