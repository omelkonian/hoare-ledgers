open import Prelude.Init
open import Prelude.Sets
open import Prelude.DecEq
open import Prelude.Decidable

module Dec (Part : Set) ⦃ _ : DecEq Part ⦄ where

open import Ledger     Part ⦃ it ⦄
open import HoareLogic Part ⦃ it ⦄
open import SL         Part ⦃ it ⦄

-- ** Alternative formulation of `mod`/`addr` using finite sets...
mods : L → Set⟨ Part ⟩
mods [] = ∅
mods (t ∷ l) = fromList (sender t ∷ receiver t ∷ []) ∪ mods l

addrs : Assertion → Set⟨ Part ⟩
addrs `emp     = ∅
addrs (A `↦ _) = singleton A
addrs (P `∗ Q) = addrs P ∪ addrs Q
addrs (P `∘⟦ _ ⟧) = addrs P

-- ... which is equivalent to our previous predicate-based definition.
addr⇒addrs : addr A P → A ∈ˢ addrs P
addr⇒addrs {P = A `↦ v} refl = proj₂ singleton∈ˢ refl
addr⇒addrs {P = P `∗ Q} (inj₁ A∈) = ∈-∪⁺ˡ _ (addrs P) (addrs Q) $ addr⇒addrs {P = P} A∈
addr⇒addrs {P = P `∗ Q} (inj₂ A∈) = ∈-∪⁺ʳ _ (addrs P) (addrs Q) $ addr⇒addrs {P = Q} A∈
addr⇒addrs {P = P `∘⟦ _ ⟧} A∈ = addr⇒addrs {P = P} A∈

addrs⇒addr : A ∈ˢ addrs P → addr A P
addrs⇒addr {P = `emp} p = ⊥-elim $ ∉∅ _ p
addrs⇒addr {P = A `↦ v} p rewrite proj₁ singleton∈ˢ p = refl
addrs⇒addr {P = P `∗ Q} A∈ with ∈-∪⁻ _ (addrs P) (addrs Q) A∈
... | inj₁ A∈ˡ = inj₁ $ addrs⇒addr {P = P} A∈ˡ
... | inj₂ A∈ʳ = inj₂ $ addrs⇒addr {P = Q} A∈ʳ
addrs⇒addr {P = P `∘⟦ _ ⟧} A∈ = addrs⇒addr {P = P} A∈

mod⇒mods : mod A l → A ∈ˢ mods l
mod⇒mods {A}{l = (.A —→⟨ _ ⟩ P)  ∷ l} (here (here refl)) =
  let xs = A ∷ P ∷ []
  in ∈-∪⁺ˡ _ (fromList xs) (mods l) (∈ˢ-fromList⁺ (here refl))
mod⇒mods {A}{l = (P —→⟨ _ ⟩ .A) ∷ l} (here (there (here refl))) =
  let xs = P ∷ A ∷ []
  in ∈-∪⁺ˡ _ (fromList xs) (mods l) (∈ˢ-fromList⁺ (there (here refl)))
mod⇒mods {A}{l = (P —→⟨ _ ⟩ P′) ∷ l} (there A∈) =
  ∈-∪⁺ʳ _ (fromList (P ∷ P′ ∷ [])) (mods l) (mod⇒mods {l = l} A∈)

mods⇒mod : A ∈ˢ mods l → mod A l
mods⇒mod {A} {[]} A∈ = ⊥-elim $ ∉∅ _ A∈
mods⇒mod {A} {B —→⟨ _ ⟩ C ∷ l} A∈ with ∈-∪⁻ _ (fromList (B ∷ C ∷ [])) (mods l) A∈
... | inj₁ A∈ˡ = here (∈ˢ-fromList⁻ A∈ˡ)
... | inj₂ A∈ʳ = there (mods⇒mod A∈ʳ)

-- ** Disjointness via _♯♯_ is a decidable relation.
instance
  Dec-♯♯ : (l ♯♯ P) ⁇
  Dec-♯♯ {l = l}{P} .dec with mods l ♯? addrs P
  ... | yes p = yes $ h→ p
    where
      h→ : mods l ♯ addrs P → l ♯♯ P
      h→ p A A∈mod A∈addr =
        ∈-∩⇒¬♯ _ (mods l) (addrs P) (∈-∩⁺ _ (mods l) (addrs P) (mod⇒mods A∈mod) (addr⇒addrs {P = P} A∈addr)) p
  ... | no ¬p = no $ ¬p ∘ h←
    where
      h← : l ♯♯ P → mods l ♯ addrs P
      h← l♯P {A} (A∈mod , A∈addr) =
        l♯P A (mods⇒mod A∈mod) (addrs⇒addr {P = P} A∈addr)
