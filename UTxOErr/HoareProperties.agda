{-# OPTIONS --allow-unsolved-metas #-}
-------------------------------------
-- ** Properties for Hoare triples.

module UTxOErr.HoareProperties where

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.InferenceRules
open import Prelude.Apartness
open import Prelude.Setoid

open import UTxOErr.UTxO
open import UTxOErr.Ledger
open import UTxOErr.HoareLogic
-- open import UTxOErr.Maps
open import Prelude.Maps
postulate
  ⊎≡-comm : Symmetric (⟨_⊎_⟩≡ s)
  ⊎≈-assocʳ :
    ∙ ⟨ s₁ ⊎ s₂₃ ⟩≡ s
    ∙ ⟨ s₂ ⊎ s₃  ⟩≡ s₂₃
      ─────────────────────
      ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
    × (s₁ ♯ s₂)
  ⊎≈-assocˡ : ∀ {s₁₂} →
    ∙ ⟨ s₁₂ ⊎ s₃ ⟩≡ s
    ∙ ⟨ s₁ ⊎ s₂  ⟩≡ s₁₂
      ───────────────────
      ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s
    × (s₂ ♯ s₃)


-- ** Lemmas about separating conjunction.

-- commutativity
∗↔ : P ∗ Q ⊢ Q ∗ P
∗↔ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) = s₂ , s₁ , ⊎≡-comm {x = s₁}{s₂} ≡s , Qs₂ , Ps₁

-- associativity
∗↝ : P ∗ Q ∗ R ⊢ (P ∗ Q) ∗ R
∗↝ {x = s} (s₁ , s₂₃ , ≡s , Ps₁ , (s₂ , s₃ , ≡s₂₃ , Qs₂ , Rs₃)) =
  let ≡s₁₂ , s₁♯s₂ = ⊎≈-assocʳ ≡s ≡s₂₃ in
  (s₁ ∪ s₂) , s₃ , ≡s₁₂ , (s₁ , s₂ , (s₁♯s₂ , ≈-refl) , Ps₁ , Qs₂) , Rs₃

↜∗ : (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R
↜∗ {x = s} (s₁₂ , s₃ , ≡s , (s₁ , s₂ , ≡s₁₂ , Ps₁ , Qs₂) , Rs₃) =
  let ≡s₂₃ , s₂♯s₃ = ⊎≈-assocˡ ≡s ≡s₁₂ in
  s₁ , s₂ ∪ s₃ , ≡s₂₃ , Ps₁ , (s₂ , s₃ , (s₂♯s₃ , ≈-refl) , Qs₂ , Rs₃)

-- ** Useful lemmas when transferring a value between participants in the minimal context.
transfer : ∀ {tx : Tx} {v : Value} {B : Address} {or : TxOutputRef} {rdm : DATA} {val : TxInfo → DATA → Bool} →
  ∙ T (val (mkTxInfo tx {!!}) rdm)
  ∙ tx ≡ record { inputs  = [ record {outputRef = or; validator = val; redeemer = rdm} ]
                ; outputs = [ v at B ]
                ; forge   = 0 }
    ────────────────────────────────────
    ⟨ or ↦ v at (val ♯) ⟩
    [ tx ]
    ⟨ (tx ♯) indexed-at 0 ↦ v at B ⟩
transfer = {!!}

open HoareReasoning
transferℝ : ∀ {tx : Tx} {v : Value} {B : Address} {or : TxOutputRef} {rdm : DATA} {val : TxInfo → DATA → Bool} →
  ∙ T (val (mkTxInfo tx {!!}) rdm)
  ∙ tx ≡ record { inputs  = [ record {outputRef = or; validator = val; redeemer = rdm} ]
                ; outputs = [ v at B ]
                ; forge   = 0 }
    ────────────────────────────────────
    ℝ⟨ or ↦ v at (val ♯) ⟩
    [ tx ]
    ⟨ (tx ♯) indexed-at 0 ↦ v at B ⟩
transferℝ val tx≡ = mkℝ transfer val tx≡

-- _↝⟨_⟩_ : ∀ A v B {vᵃ}{vᵇ}{v≤ : v ≤ vᵃ} → ⟨ A ↦ vᵃ ∗ B ↦ vᵇ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ (vᵃ ∸ v) ∗ B ↦ (vᵇ + v) ⟩
-- (A ↝⟨ v ⟩ B) {vᵃ}{vᵇ}{vᵃ≤v} {s} (s₁ , s₂ , ≡s , As₁ , Bs₂)
--   with s₁ A | As₁ | ↦-⊎ˡ {s₁ = s₁}{A}{vᵃ}{s₂} As₁ | ≡s A
-- ... | .(just vᵃ) | refl | .(s₂ ⁉⁰ A) , refl , p | sA≡
--   with s₂ B | Bs₂ | ↦-⊎ʳ {s₂ = s₂}{B}{vᵇ}{s₁} Bs₂ | ≡s B
-- ... | .(just vᵇ) | refl | .(s₁ ⁉⁰ B) , refl , q | sB≡
--   with s A | trans (sym sA≡) p
-- ... | .(just (vᵃ ⊎ (s₂ ⁉⁰ A))) | refl
--   with s B | trans (sym sB≡) q
-- ... | .(just ((s₁ ⁉⁰ B) ⊎ vᵇ)) | refl
--   with v ≤? vᵃ ⊎ (s₂ ⁉⁰ A)
-- ... | no  v≰ = ⊥-elim $ v≰ $ Nat.≤-stepsʳ (s₂ ⁉⁰ A) $ vᵃ≤v
-- ... | yes v≤
--   = ret↑ (_s₁′ , _s₂′ , ≡s′ , As₁′ , Bs₂′)
--   where
--     sA≡′ : s A ≡ just (vᵃ ⊎ (s₂ ⁉⁰ A))
--     sA≡′ = trans (sym sA≡) p

--     sB≡′ : s B ≡ just ((s₁ ⁉⁰ B) ⊎ vᵇ)
--     sB≡′ = trans (sym sB≡) q

--     _s₁′ = s₁ [ A ↝ (_∸ v) ]
--     _s₂′ = s₂ [ B ↝ (_+ v) ]

--     _s′ = s [ A ↝ (_∸ v) ]
--             [ B ↝ (_+ v) ]

--     As₁′ : _s₁′ A ≡ just (vᵃ ∸ v)
--     As₁′ rewrite As₁ | ≟-refl A = refl

--     Bs₂′ : _s₂′ B ≡ just (vᵇ + v)
--     Bs₂′ rewrite Bs₂ | ≟-refl B = refl

--     ≡s′ : ⟨ _s₁′ ⊎ _s₂′ ⟩≡ _s′
--     ≡s′ k
--       rewrite sym $ ≡s k
--       with k ≟ A | k ≟ B
--     ≡s′ k | yes refl | yes refl -- ∙ k ≡ A ≡ B
--       rewrite ≟-refl A | ≟-refl B | As₁ | Bs₂
--       = cong just
--       $ begin (vᵃ ∸ v) + (vᵇ + v) ≡⟨ sym $ Nat.+-∸-comm _ vᵃ≤v ⟩
--               vᵃ + (vᵇ + v) ∸ v   ≡⟨ cong (_∸ v) $ sym $ Nat.+-assoc _ vᵇ v ⟩
--               (vᵃ + vᵇ) + v ∸ v   ≡⟨ Nat.m+n∸n≡m _ v ⟩
--               (vᵃ + vᵇ)           ≡⟨ sym $ Nat.m∸n+n≡m v≤ ⟩
--               (vᵃ + vᵇ) ∸ v + v   ∎ where open ≡-Reasoning
--     ≡s′ k | yes refl | no k≢B -- ∙ k ≡ A
--       rewrite ≟-refl A | As₁
--       with s₂ A
--     ... | nothing = refl
--     ... | just _  = cong just $ sym $ Nat.+-∸-comm _ vᵃ≤v
--     ≡s′ k | no k≢A   | yes refl -- ∙ k ≡ B
--       rewrite ≟-refl B | Bs₂
--       with s₁ B
--     ... | nothing  = refl
--     ... | just _   = cong just $ sym $ Nat.+-assoc _ vᵇ v
--     ≡s′ k | no k≢A   | no k≢B -- ∙ k ∉ {A, B}
--       rewrite M.map-id (s₁ k) | M.map-id (s₂ k) | M.map-id (s₁ k ⊎ s₂ k) | M.map-id (s₁ k ⊎ s₂ k)
--       = refl

-- _↝⁰_ : ∀ A B → ⟨ A ↦ v ∗ B ↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A ↦ 0 ∗ B ↦ (v′ + v) ⟩
-- _↝⁰_ {v = v} {v′ = v′} A B with p ← (A ↝⟨ v ⟩ B) {vᵇ = v′} {v≤ = ≤-refl {x = v}} rewrite Nat.n∸n≡0 v = p

-- _↜⟨_⟩_ : ∀ A v B {vᵃ}{vᵇ}{v≤ : v ≤ vᵇ} → ⟨ A ↦ vᵃ ∗ B ↦ vᵇ ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (vᵃ + v) ∗ B ↦ (vᵇ ∸ v) ⟩
-- (A ↜⟨ v ⟩ B) {vᵃ}{vᵇ}{v≤} (s₁ , s₂ , ≡s , As₁ , Bs₂)
--   = map↑ (λ where (s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′) → s₂′ , s₁′ , ⊎≡-comm {x = s₁′} ≡s′ , Bs₂′ , As₁′)
--          ((B ↝⟨ v ⟩ A) {v≤ = v≤} (s₂ , s₁ , ⊎≡-comm {x = s₁} ≡s , Bs₂ , As₁))

-- _↜⁰_ : ∀ A B → ⟨ A ↦ v′ ∗ B ↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A ↦ (v′ + v) ∗ B ↦ 0 ⟩
-- _↜⁰_ {v′ = v′} {v = v} A B with p ← (A ↜⟨ v ⟩ B) {vᵃ = v′} {v≤ = ≤-refl {x = v}} rewrite Nat.n∸n≡0 v = p
