-- {-# OPTIONS -v try:100 #-}
module Example where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Sets
-- open import Prelude.Generics
-- open import Prelude.Try

import SL as SL

data Part : Set where
  A B C D : Part
unquoteDecl DecEq-Part = DERIVE DecEq [ quote Part , DecEq-Part ]

-- NB. {{it}} required due to Agda bug, reported at https://github.com/agda/agda/issues/5093
open import Ledger Part {{it}}
  hiding (A; B; C; D)
open import HoareLogic Part {{it}}
open import SL Part {{it}}
open import CSL Part {{it}}
-- open import Dec Part {{it}}
-- we cannot utilize the decision procedure for closed formulas, as Prelude.Sets is abstract

t₁ = A —→⟨ 1 ⟩ B
t₂ = D —→⟨ 1 ⟩ C
t₃ = B —→⟨ 1 ⟩ A
t₄ = C —→⟨ 1 ⟩ D

t₁-₄ : L
t₁-₄ = t₁ ∷ t₂ ∷ t₃ ∷ t₄ ∷ []

open HoareReasoning
pattern 𝟘_ x = here x
pattern 𝟙_ x = there x

-- proof using only SL.[FRAME]
h : ⟨ A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1 ⟩
    t₁-₄
    ⟨ A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1 ⟩
h = begin A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1   ~⟨ ∗↝ {A `↦ 1} {B `↦ 0} {C `↦ 0 `∗ D `↦ 1}     ⟩
          (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ t₁ ∶- [FRAME] (C `↦ 0 `∗ D `↦ 1) p₁ (A ↝ B ∶- auto) ⟩
          (A `↦ 0 `∗ B `↦ 1) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ ∗↔ {A `↦ 0 `∗ B `↦ 1} {C `↦ 0 `∗ D `↦ 1}    ⟩
          (C `↦ 0 `∗ D `↦ 1) `∗ A `↦ 0 `∗ B `↦ 1 ~⟨ t₂ ∶- [FRAME] (A `↦ 0 `∗ B `↦ 1) p₂ (C ↜ D ∶- auto) ⟩
          (C `↦ 1 `∗ D `↦ 0) `∗ A `↦ 0 `∗ B `↦ 1 ~⟨ ∗↔ {C `↦ 1 `∗ D `↦ 0} {A `↦ 0 `∗ B `↦ 1}    ⟩
          (A `↦ 0 `∗ B `↦ 1) `∗ C `↦ 1 `∗ D `↦ 0 ~⟨ t₃ ∶- [FRAME] (C `↦ 1 `∗ D `↦ 0) p₃ (A ↜ B ∶- auto) ⟩
          (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 1 `∗ D `↦ 0 ~⟨ ∗↔ {A `↦ 1 `∗ B `↦ 0} {C `↦ 1 `∗ D `↦ 0}    ⟩
          (C `↦ 1 `∗ D `↦ 0) `∗ A `↦ 1 `∗ B `↦ 0 ~⟨ t₄ ∶- [FRAME] (A `↦ 1 `∗ B `↦ 0) p₄ (C ↝ D ∶- auto) ⟩
          (C `↦ 0 `∗ D `↦ 1) `∗ A `↦ 1 `∗ B `↦ 0 ~⟨ ∗↔ {C `↦ 0 `∗ D `↦ 1} {A `↦ 1 `∗ B `↦ 0}    ⟩
          (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ ↜∗ {A `↦ 1} {B `↦ 0} {C `↦ 0 `∗ D `↦ 1}     ⟩
          A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1   ∎
  where
    pattern 𝟘𝟘  =   𝟘 𝟘 ()
    pattern 𝟘𝟙𝟘 = 𝟘 𝟙 𝟘 ()

    p₁ : [ t₁ ] ♯♯ (C `↦ 0 `∗ D `↦ 1)
    -- p₁ = try auto ∶- [ quote Dec-♯♯ ∙ ]
    -- p₁ = auto {{Dec-♯♯ {P = C `↦ 0 `∗ D `↦ 1}}}
    p₁ .C px (inj₁ refl) = case px of λ{ 𝟘𝟘 ; 𝟘𝟙𝟘 }
    p₁ .D px (inj₂ refl) = case px of λ{ 𝟘𝟘 ; 𝟘𝟙𝟘 }

    p₂ : [ t₂ ] ♯♯ (A `↦ 0 `∗ B `↦ 1)
    -- p₂ = auto {{Dec-♯♯ {P = A `↦ 0 `∗ B `↦ 1}}}
    p₂ .A px (inj₁ refl) = case px of λ{ 𝟘𝟘 ; 𝟘𝟙𝟘 }
    p₂ .B px (inj₂ refl) = case px of λ{ 𝟘𝟘 ; 𝟘𝟙𝟘 }

    p₃ : [ t₃ ] ♯♯ (C `↦ 1 `∗ D `↦ 0)
    -- p₃ = auto {{Dec-♯♯ {P = C `↦ 1 `∗ D `↦ 0}}}
    p₃ .C px (inj₁ refl) = case px of λ{ 𝟘𝟘 ; 𝟘𝟙𝟘 }
    p₃ .D px (inj₂ refl) = case px of λ{ 𝟘𝟘 ; 𝟘𝟙𝟘 }

    p₄ : [ t₄ ] ♯♯ (A `↦ 1 `∗ B `↦ 0)
    -- p₄ = auto {{Dec-♯♯ {P = A `↦ 1 `∗ B `↦ 0}}}
    p₄ .A px (inj₁ refl) = case px of λ{ 𝟘𝟘 ; 𝟘𝟙𝟘 }
    p₄ .B px (inj₂ refl) = case px of λ{ 𝟘𝟘 ; 𝟘𝟙𝟘 }

    -- NB. Agda cannot figure out how to use `Dec-♯♯`...
    -- working on a macro to do such things automatically

-- 2) proof using CSL.[INTERLEAVE]
h₁ : ⟨ A `↦ 1 `∗ B `↦ 0 ⟩ t₁ ∷ t₃ ∷ [] ⟨ A `↦ 1 `∗ B `↦ 0 ⟩
h₁ = begin A `↦ 1 `∗ B `↦ 0 ~⟨ t₁ ∶- A ↝ B ∶- auto ⟩
           A `↦ 0 `∗ B `↦ 1 ~⟨ t₃ ∶- A ↜ B ∶- auto ⟩
           A `↦ 1 `∗ B `↦ 0 ∎

h₂ : ⟨ C `↦ 0 `∗ D `↦ 1 ⟩ t₂ ∷ t₄ ∷ [] ⟨ C `↦ 0 `∗ D `↦ 1 ⟩
h₂ = begin C `↦ 0 `∗ D `↦ 1 ~⟨ t₂ ∶- C ↜ D ∶- auto ⟩
           C `↦ 1 `∗ D `↦ 0 ~⟨ t₄ ∶- C ↝ D ∶- auto ⟩
           C `↦ 0 `∗ D `↦ 1 ∎

h′ : ⟨ A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1 ⟩
     t₁-₄
     ⟨ A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1 ⟩
h′ = begin A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1   ~⟨ ∗↝ {A `↦ 1} {B `↦ 0} {C `↦ 0 `∗ D `↦ 1} ⟩
           (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ t₁-₄ ∶- [INTERLEAVE] inter h₁ h₂ p₁ p₂  ⟩′
           (A `↦ 1 `∗ B `↦ 0) `∗ C `↦ 0 `∗ D `↦ 1 ~⟨ ↜∗ {A `↦ 1} {B `↦ 0} {C `↦ 0 `∗ D `↦ 1} ⟩
           A `↦ 1 `∗ B `↦ 0 `∗ C `↦ 0 `∗ D `↦ 1   ∎
     where
       pattern 𝟘𝟙𝟘  =   𝟘 𝟙 𝟘 ()
       pattern 𝟘𝟙𝟙  =   𝟘 𝟙 𝟙 ()
       pattern 𝟙𝟘𝟙𝟘 = 𝟙 𝟘 𝟙 𝟘 ()
       pattern 𝟙𝟘𝟙𝟙 = 𝟙 𝟘 𝟙 𝟙 ()

       p₁ : (t₁ ∷ t₃ ∷ []) ♯♯ (C `↦ 0 `∗ D `↦ 1)
       -- p₁ = auto {{Dec-♯♯ {P = C `↦ 0 `∗ D `↦ 1}}}
       p₁ .C px (inj₁ refl) = case px of λ{ 𝟘𝟙𝟘; 𝟘𝟙𝟙; 𝟙𝟘𝟙𝟘 ;𝟙𝟘𝟙𝟙 }
       p₁ .D px (inj₂ refl) = case px of λ{ 𝟘𝟙𝟘; 𝟘𝟙𝟙; 𝟙𝟘𝟙𝟘 ;𝟙𝟘𝟙𝟙 }

       p₂ : (t₂ ∷ t₄ ∷ []) ♯♯ (A `↦ 1 `∗ B `↦ 0)
       -- p₂ = auto {{Dec-♯♯ {P = A `↦ 1 `∗ B `↦ 0}}}
       p₂ .A px (inj₁ refl) = case px of λ{ 𝟘𝟙𝟘; 𝟘𝟙𝟙; 𝟙𝟘𝟙𝟘 ;𝟙𝟘𝟙𝟙 }
       p₂ .B px (inj₂ refl) = case px of λ{ 𝟘𝟙𝟘; 𝟘𝟙𝟙; 𝟙𝟘𝟙𝟘 ;𝟙𝟘𝟙𝟙 }

       -- this is decidable (i.e. s/inter/auto), but stdlib-1.3 still doesn't have that
       open import Data.List.Relation.Ternary.Interleaving
       inter : (t₁ ∷ t₃ ∷ []) ∥ (t₂ ∷ t₄ ∷ []) ≡ t₁-₄
       inter = refl ∷ˡ (refl ∷ʳ (refl ∷ˡ (refl ∷ʳ [])))
