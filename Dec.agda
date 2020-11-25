open import Prelude.Init
open import Prelude.Set'
open import Prelude.DecEq
open import Prelude.Decidable

module Dec (Part : Set) {{_ : DecEq Part}} where

open import Ledger Part {{it}}
open import HoareLogic Part {{it}}
open import SL Part {{it}}

mods : L → Set⟨ Part ⟩
mods [] = ∅
mods (t ∷ l) = fromList (sender t ∷ receiver t ∷ []) ∪ mods l

addrs : Assertion → Set⟨ Part ⟩
addrs `emp     = ∅
addrs (A `↦ _) = singleton A
addrs (P `∗ Q) = addrs P ∪ addrs Q
addrs (P `∘ _) = addrs P

addr⇒addrs : addr A P → A ∈′ addrs P
addr⇒addrs {P = A `↦ v} refl = here refl
addr⇒addrs {P = P `∗ Q} (inj₁ A∈) = ∈-∪⁺ˡ {xs = addrs P}{addrs Q} $ addr⇒addrs {P = P} A∈
addr⇒addrs {P = P `∗ Q} (inj₂ A∈) = ∈-∪⁺ʳ {xs = addrs P}{addrs Q} $ addr⇒addrs {P = Q} A∈
addr⇒addrs {P = P `∘ _} A∈ = addr⇒addrs {P = P} A∈

addrs⇒addr : A ∈′ addrs P → addr A P
addrs⇒addr {P = A `↦ v} (here refl) = refl
addrs⇒addr {P = P `∗ Q} A∈ with ∈-∪⁻ {xs = addrs P}{addrs Q} A∈
... | inj₁ A∈ˡ = inj₁ $ addrs⇒addr {P = P} A∈ˡ
... | inj₂ A∈ʳ = inj₂ $ addrs⇒addr {P = Q} A∈ʳ
addrs⇒addr {P = P `∘ _} A∈ = addrs⇒addr {P = P} A∈

mod⇒mods : mod A l → A ∈′ mods l
mod⇒mods {A}{l = (.A —→⟨ _ ⟩ P)  ∷ l} (here (here refl)) =
  let xs = A ∷ P ∷ []
  in ∈-∪⁺ˡ {xs = fromList xs}{mods l} (∈-nub⁺ {xs = xs} $ here refl)
mod⇒mods {A}{l = (P —→⟨ _ ⟩ .A) ∷ l} (here (there (here refl))) =
  let xs = P ∷ A ∷ []
  in ∈-∪⁺ˡ {xs = fromList xs}{mods l} (∈-nub⁺ {xs = xs} $ there (here refl))
mod⇒mods {A}{l = (P —→⟨ _ ⟩ P′) ∷ l} (there A∈) =
  ∈-∪⁺ʳ {xs = fromList (P ∷ P′ ∷ [])}{mods l} (mod⇒mods {l = l} A∈)

mods⇒mod : A ∈′ mods l → mod A l
mods⇒mod {A} {B —→⟨ _ ⟩ C ∷ l} A∈ with ∈-∪⁻ {xs = fromList (B ∷ C ∷ [])}{mods l} A∈
... | inj₁ A∈ˡ = here (∈-nub⁻ A∈ˡ)
... | inj₂ A∈ʳ = there (mods⇒mod A∈ʳ)

h→ : mods l ♯ addrs P → l ♯♯ P
h→ {l}{P} p A A∈mod A∈addr =
  ∈-∩⇒¬♯ {xs = mods l}{addrs P}
    (∈-∩⁺ {xs = mods l}{addrs P} (mod⇒mods A∈mod) (addr⇒addrs {P = P} A∈addr))
    p

h← : l ♯♯ P → mods l ♯ addrs P
h← {l}{P} l♯P = ♯′→♯ {xs = mods l}{addrs P} λ A A∈mod A∈addr →
  l♯P A (mods⇒mod A∈mod) (addrs⇒addr {P = P} A∈addr)

instance
  Dec-♯♯ : (l ♯♯ P) ⁇
  Dec-♯♯ {l = l}{P} .dec with ¿ mods l ♯ addrs P ¿
  ... | yes p = yes $ h→ {P = P} p
  ... | no ¬p = no  $ ¬p ∘ h← {P = P}
