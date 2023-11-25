{-# OPTIONS --allow-unsolved-metas #-}
module Common.Data where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.Bifunctor

DATA = String

record ToData (A : Type) : Type where
  field
    serialise     : A → DATA
    serialise-inj : Injective≡ serialise
    deserialise   : (d : DATA) → Dec (∃ λ a → d ≡ serialise a)

  deserialise∘serialise : ∀ a → deserialise (serialise a) ≡ yes (a , refl)
  deserialise∘serialise a
    with deserialise (serialise a)
  ... | no ¬p = ⊥-elim (¬p (a , refl))
  ... | yes (_ , ser≡)
    with refl ← serialise-inj ser≡
    rewrite ser≡
    = refl
open ToData ⦃...⦄ public

private variable A B C : Type ℓ

dec-elim : (A → C) → (¬ A → C) → Dec A → C
dec-elim f g = λ where
  (yes a) → f a
  (no ¬a) → g ¬a

open Fun
ToData↔ : ⦃ ToData A ⦄ → (eq : A ↔ B) → Injective≡ (eq .Inverse.f⁻¹) → ToData B
ToData↔ record { f = A→B ; f⁻¹ = B→A; inverse = _ , B→A→B } B→A-inj = λ where
  .serialise → serialise ∘ B→A
  .serialise-inj → B→A-inj ∘ serialise-inj
  .deserialise →
    Nullary.map′ (λ (a , d≡) → A→B a , trans d≡ (cong serialise $ sym $ B→A→B _))
                 (λ (b , d≡) → B→A b , d≡)
    ∘ deserialise

instance
  ToData-DATA : ToData DATA
  ToData-DATA = λ where
    .serialise → id
    .serialise-inj → id
    .deserialise _ → yes (-, refl)

  ToData-Unit : ToData ⊤
  ToData-Unit .serialise tt = "tt"
  ToData-Unit .serialise-inj refl = refl
  ToData-Unit .deserialise d = Nullary.map′ -,_ proj₂ (d ≟ "tt")

  ToData-Bool : ToData Bool
  ToData-Bool .serialise = λ where true  → "true"; false → "false"
  ToData-Bool .serialise-inj {false}{false} refl = refl
  ToData-Bool .serialise-inj {true}{true}   refl = refl
  ToData-Bool .deserialise d
    = Nullary.map′
      Sum.[ true ,_ , false ,_ ]
      (λ where (true , d≡) → inj₁ d≡; (false , d≡) → inj₂ d≡)
      ¿ (d ≡ "true") ⊎ (d ≡ "false") ¿

  ToData-⊎ : ⦃ ToData A ⦄ → ⦃ ToData B ⦄ → ToData (A ⊎ B)
  ToData-⊎ .serialise = λ where
    (inj₁ a) → "0" ◇ serialise a
    (inj₂ b) → "1" ◇ serialise b
  ToData-⊎ .serialise-inj = {!!}
  ToData-⊎ .deserialise d = {!!}

  ToData-× : ⦃ ToData A ⦄ → ⦃ ToData B ⦄ → ToData (A × B)
  ToData-× .serialise (a , b) = serialise a ◇ "⨾" ◇ serialise b
  ToData-× .serialise-inj = {!!}
  ToData-× .deserialise d = {!!}
