-- {-# OPTIONS -v try:100 #-}
module Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Set'
-- open import Prelude.Generics
-- open import Prelude.Try

import SL as SL

data Part : Set where
  A B C D : Part
unquoteDecl DecEq-Part = DERIVE DecEq [ quote Part , DecEq-Part ]

open import Ledger Part {{it}}
  hiding (A; B; C; D)
open import HoareLogic Part {{it}}
open import SL Part {{it}}
open import CSL Part {{it}}
open import Dec Part {{it}}
-- NB. {{it}} required due to Agda bug, reported at https://github.com/agda/agda/issues/5093

t₁ = A —→⟨ 1 ⟩ B
t₂ = D —→⟨ 1 ⟩ C
t₃ = B —→⟨ 1 ⟩ A
t₄ = C —→⟨ 1 ⟩ D

t₁-₄ : L
t₁-₄ = t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ []

open HoareReasoning

-- proof using only SL.[FRAME]
h : ⟨ A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1 ⟩
    t₁-₄
    ⟨ A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1 ⟩
h = begin A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1   ~⟨ ∗↝ {A `↦ 1} {B `↦ 0} {C `↦ 0 `∗ D `↦ 1}     ⟩
          (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ t₁ ∶- [FRAME] (C `↦ 0 `∗ D `↦ 1) p₁ (A ↝ B) ⟩
          (A `↦ 0 `∗ B `↦ 1) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ ∗↔ {A `↦ 0 `∗ B `↦ 1} {C `↦ 0 `∗ D `↦ 1}    ⟩
          (C `↦ 0 `∗ D `↦ 1) `∗ A `↦ 0 `∗ B `↦ 1 ~⟨ t₂ ∶- [FRAME] (A `↦ 0 `∗ B `↦ 1) p₂ (C ↜ D) ⟩
          (C `↦ 1 `∗ D `↦ 0) `∗ A `↦ 0 `∗ B `↦ 1 ~⟨ ∗↔ {C `↦ 1 `∗ D `↦ 0} {A `↦ 0 `∗ B `↦ 1}    ⟩
          (A `↦ 0 `∗ B `↦ 1) `∗ C `↦ 1 `∗ D `↦ 0 ~⟨ t₃ ∶- [FRAME] (C `↦ 1 `∗ D `↦ 0) p₃ (A ↜ B) ⟩
          (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 1 `∗ D `↦ 0 ~⟨ ∗↔ {A `↦ 1 `∗ B `↦ 0} {C `↦ 1 `∗ D `↦ 0}    ⟩
          (C `↦ 1 `∗ D `↦ 0) `∗ A `↦ 1 `∗ B `↦ 0 ~⟨ t₄ ∶- [FRAME] (A `↦ 1 `∗ B `↦ 0) p₄ (C ↝ D) ⟩
          (C `↦ 0 `∗ D `↦ 1) `∗ A `↦ 1 `∗ B `↦ 0 ~⟨ ∗↔ {C `↦ 0 `∗ D `↦ 1} {A `↦ 1 `∗ B `↦ 0}    ⟩
          (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ ↜∗ {A `↦ 1} {B `↦ 0} {C `↦ 0 `∗ D `↦ 1}     ⟩
          A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1   ∎
  where
    p₁ : [ t₁ ] ♯♯ (C `↦ 0 `∗ D `↦ 1)
    -- p₁ = try auto ∶- [ quote Dec-♯♯ ∙ ]
    p₁ = auto {{Dec-♯♯ {P = C `↦ 0 `∗ D `↦ 1}}}

    p₂ : [ t₂ ] ♯♯ (A `↦ 0 `∗ B `↦ 1)
    p₂ = auto {{Dec-♯♯ {P = A `↦ 0 `∗ B `↦ 1}}}

    p₃ : [ t₃ ] ♯♯ (C `↦ 1 `∗ D `↦ 0)
    p₃ = auto {{Dec-♯♯ {P = C `↦ 1 `∗ D `↦ 0}}}

    p₄ : [ t₄ ] ♯♯ (A `↦ 1 `∗ B `↦ 0)
    p₄ = auto {{Dec-♯♯ {P = A `↦ 1 `∗ B `↦ 0}}}

    -- NB. Agda cannot figure out how to use `Dec-♯♯`...
    -- working on a macro to do such things automatically

-- 2) proof using CSL.[INTERLEAVE]
h₁ : ⟨ A `↦ 1 `∗ B `↦ 0 ⟩ t₁ ∷ t₃ ∷ [] ⟨ A `↦ 1 `∗ B `↦ 0 ⟩
h₁ = begin A `↦ 1 `∗ B `↦ 0 ~⟨ t₁ ∶- A ↝ B ⟩
           A `↦ 0 `∗ B `↦ 1 ~⟨ t₃ ∶- A ↜ B ⟩
           A `↦ 1 `∗ B `↦ 0 ∎

h₂ : ⟨ C `↦ 0 `∗ D `↦ 1 ⟩ t₂ ∷ t₄ ∷ [] ⟨ C `↦ 0 `∗ D `↦ 1 ⟩
h₂ = begin C `↦ 0 `∗ D `↦ 1 ~⟨ t₂ ∶- C ↜ D ⟩
           C `↦ 1 `∗ D `↦ 0 ~⟨ t₄ ∶- C ↝ D ⟩
           C `↦ 0 `∗ D `↦ 1 ∎

h′ : ⟨ A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1 ⟩
     t₁-₄
     ⟨ A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1 ⟩
h′ = begin A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1   ~⟨ ∗↝ {A `↦ 1} {B `↦ 0} {C `↦ 0 `∗ D `↦ 1} ⟩
           (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ t₁-₄ ∶- [INTERLEAVE] inter h₁ h₂ p₁ p₂  ⟩′
           (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ ↜∗ {A `↦ 1} {B `↦ 0} {C `↦ 0 `∗ D `↦ 1} ⟩
           A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1   ∎
     where
       p₁ : (t₁ ∷ t₃ ∷ []) ♯♯ (C `↦ 0 `∗ D `↦ 1)
       p₁ = auto {{Dec-♯♯ {P = C `↦ 0 `∗ D `↦ 1}}}

       p₂ : (t₂ ∷ t₄ ∷ []) ♯♯ (A `↦ 1 `∗ B `↦ 0)
       p₂ = auto {{Dec-♯♯ {P = A `↦ 1 `∗ B `↦ 0}}}

       -- this is decidable (i.e. s/inter/auto), but stdlib-1.3 still doesn't have that
       open import Data.List.Relation.Ternary.Interleaving
       inter : (t₁ ∷ t₃ ∷ []) ∥ (t₂ ∷ t₄ ∷ []) ≡ t₁-₄
       inter = refl ∷ˡ (refl ∷ʳ (refl ∷ˡ (refl ∷ʳ [])))
