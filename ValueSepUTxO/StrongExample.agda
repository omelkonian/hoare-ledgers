{-# OPTIONS --rewriting #-}
module ValueSepUTxO.StrongExample where

open import Agda.Builtin.Equality.Rewrite

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists hiding (_↦_)
open import Prelude.DecLists

open import ValueSepUTxO.Maps
open import ValueSepUTxO.UTxO
open import ValueSepUTxO.Ledger
open import ValueSepUTxO.StrongHoareLogic
open import ValueSepUTxO.HoareProperties
open import ValueSepUTxO.StrongSL
open import ValueSepUTxO.StrongCSL

A B C D : Address
A = 111; B = 222; C = 333; D = 444

postulate t₀ : Tx
t₀₀ = (t₀ ♯) indexed-at 0
t₀₁ = (t₀ ♯) indexed-at 1

postulate
  mkValidator : TxOutputRef → (TxInfo → DATA → Bool)
  in₁ : (mkValidator t₀₀) ♯ ≡ A
  in₂ : (mkValidator t₀₁) ♯ ≡ D
{-# REWRITE in₁ #-}
{-# REWRITE in₂ #-}

_—→⟨_∣_⟩_ : Address → Value → TxOutputRef → Address → Tx
A —→⟨ v ∣ or ⟩ B = record
  { inputs  = [ record { outputRef = or ; validator = mkValidator or; redeemer = 0 } ]
  ; outputs = [ 1 at B ]
  ; forge   = 0
  }

t₁ t₂ t₃ t₄ : Tx
-- t₀ = record {inputs = []; outputs = 1 at A ∷ 1 at D ∷ []; forge = 2}
t₁ = A —→⟨ 1 ∣ t₀₀ ⟩ B
t₂ = D —→⟨ 1 ∣ t₀₁ ⟩ C
postulate
  val₁ : T $ mkValidator t₀₀ (mkTxInfo t₁) 0
  val₂ : T $ mkValidator t₀₁ (mkTxInfo t₂) 0
t₁₀ = (t₁ ♯) indexed-at 0
t₂₀ = (t₂ ♯) indexed-at 0
postulate
  in₃ : (mkValidator t₁₀) ♯ ≡ B
  in₄ : (mkValidator t₂₀) ♯ ≡ C
{-# REWRITE in₃ #-}
{-# REWRITE in₄ #-}

t₃ = B —→⟨ 1 ∣ t₁₀ ⟩ A
t₄ = C —→⟨ 1 ∣ t₂₀ ⟩ D
postulate
  val₃ : T $ mkValidator t₁₀ (mkTxInfo t₃) 0
  val₄ : T $ mkValidator t₂₀ (mkTxInfo t₄) 0
t₃₀ = (t₃ ♯) indexed-at 0
t₄₀ = (t₄ ♯) indexed-at 0

t₁-₄ : L
t₁-₄ = t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ []
{-
 t₀         t₁        t₃
┌──┐  t₀₀  ┌──┐ t₁₀  ┌──┐ t₃₀
│  ∙───∘───│  ∙──∘───│  ∙──∘──⋯
│  │   A   └──┘  B   └──┘  A
│  │
│  │        t₂         t₄
│  │  t₀₁  ┌──┐ t₂₀  ┌──┐ t₄₀
│  ∙───∘───│  ∙──∘───│  ∙──∘──⋯
│  │   D   └──┘  C   └──┘  D
│  ⋮
│  ⋮
└──┘
-}

open HoareReasoning

-- 1a) proof using only SL.[FRAME]
_ : ⟨ t₀₀ ↦ 1 at A ∗ t₀₁ ↦ 1 at D ⟩
    t₁-₄
    ⟨ t₃₀ ↦ 1 at A ∗ t₄₀ ↦ 1 at D ⟩
_ = begin
  t₀₀ ↦ 1 at A ∗ t₀₁ ↦ 1 at D ~⟨ t₁ ∶- ℝ[FRAME] (t₀₁ ↦ 1 at D) (transferℝ val₁ refl) ⟩
  t₁₀ ↦ 1 at B ∗ t₀₁ ↦ 1 at D ~⟪ ∗↔ ⟩
  t₀₁ ↦ 1 at D ∗ t₁₀ ↦ 1 at B ~⟨ t₂ ∶- ℝ[FRAME] (t₁₀ ↦ 1 at B) (transferℝ val₂ refl) ⟩
  t₂₀ ↦ 1 at C ∗ t₁₀ ↦ 1 at B ~⟪ ∗↔ ⟩
  t₁₀ ↦ 1 at B ∗ t₂₀ ↦ 1 at C ~⟨ t₃ ∶- ℝ[FRAME] (t₂₀ ↦ 1 at C) (transferℝ val₃ refl) ⟩
  t₃₀ ↦ 1 at A ∗ t₂₀ ↦ 1 at C ~⟪ ∗↔ ⟩
  t₂₀ ↦ 1 at C ∗ t₃₀ ↦ 1 at A ~⟨ t₄ ∶- ℝ[FRAME] (t₃₀ ↦ 1 at A) (transferℝ val₄ refl) ⟩
  t₄₀ ↦ 1 at D ∗ t₃₀ ↦ 1 at A ~⟪ ∗↔ ⟩
  t₃₀ ↦ 1 at A ∗ t₄₀ ↦ 1 at D ∎

-- 1b) proof using CSL.[INTERLEAVE]
_ : ⟨ t₀₀ ↦ 1 at A ∗ t₀₁ ↦ 1 at D ⟩
    t₁-₄
    ⟨ t₃₀ ↦ 1 at A ∗ t₄₀ ↦ 1 at D ⟩
_ = begin t₀₀ ↦ 1 at A ∗ t₀₁ ↦ 1 at D ~⟨ t₁-₄ ∶- ℝ[PAR] (keepˡ $′ keepʳ $′ keepˡ $′ keepʳ []) H₁ H₂ ⟩++
          t₃₀ ↦ 1 at A ∗ t₄₀ ↦ 1 at D ∎
  where
    H₁ : ℝ⟨ t₀₀ ↦ 1 at A ⟩ t₁ ∷ t₃ ∷ [] ⟨ t₃₀ ↦ 1 at A ⟩
    H₁ = t₀₀ ↦ 1 at A ~⟨ t₁ ∶- transferℝ val₁ refl ⟩
         t₁₀ ↦ 1 at B ~⟨ t₃ ∶- transferℝ val₃ refl ⟩
         t₃₀ ↦ 1 at A ∎

    H₂ : ℝ⟨ t₀₁ ↦ 1 at D ⟩ t₂ ∷ t₄ ∷ [] ⟨ t₄₀ ↦ 1 at D ⟩
    H₂ = t₀₁ ↦ 1 at D ~⟨ t₂ ∶- transferℝ val₂ refl ⟩
         t₂₀ ↦ 1 at C ~⟨ t₄ ∶- transferℝ val₄ refl ⟩
         t₄₀ ↦ 1 at D ∎

{-
-- 2) overlapping proof
t₁′ = A —→⟨ 1 ⟩ B; t₂′ = C —→⟨ 1 ⟩ A
t₁₂ = L ∋ t₁′ ∷ t₂′ ∷ []

_ : ⟨ A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 1 ∗ A ↦ 0 ⟩
     t₁₂
     ⟨ A ↦ 0 ∗ B ↦ 1 ∗ C ↦ 0 ∗ A ↦ 1 ⟩
_ = begin A ↦ 1 ∗ B ↦ 0 ∗ C ↦ 1 ∗ A ↦ 0     ~⟪ ∗↝ {A ↦ 1} {B ↦ 0} {C ↦ 1 ∗ A ↦ 0} ⟩
          (A ↦ 1 ∗ B ↦ 0) ∗ (C ↦ 1 ∗ A ↦ 0) ~⟨ t₁₂ ∶- ℝ[PAR] auto H₁ H₂ ⟩++
          (A ↦ 0 ∗ B ↦ 1) ∗ (C ↦ 0 ∗ A ↦ 1) ~⟪ ↜∗ {A ↦ 0} {B ↦ 1} {C ↦ 0 ∗ A ↦ 1} ⟩
          A ↦ 0 ∗ B ↦ 1 ∗ C ↦ 0 ∗ A ↦ 1     ∎
  where
    H₁ : ℝ⟨ A ↦ 1 ∗ B ↦ 0 ⟩ [ t₁′ ] ⟨ A ↦ 0 ∗ B ↦ 1 ⟩
    H₁ = mkℝ A ↝⁰ B

    H₂ : ℝ⟨ C ↦ 1 ∗ A ↦ 0 ⟩ [ t₂′ ] ⟨ C ↦ 0 ∗ A ↦ 1 ⟩
    H₂ = mkℝ C ↝⁰ A
-}
