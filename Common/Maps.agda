open import Prelude.Init; open SetAsType; open ≡-Reasoning
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Maybes
open import Prelude.Membership
open import Prelude.ToList
open import Prelude.Apartness
open import Prelude.Lists.Dec
open import Prelude.InferenceRules

module Common.Maps {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : DecEq V ⦄ where

-- list properties
postulate
  nubBy-from∘to : ∀ {A B : Type} ⦃ _ : DecEq B ⦄ {f : A → B} {xs : List A} →
    Unique (map f xs) → nubBy f xs ≡ xs
  Unique-proj₁ : ∀ {A B : Type} {xys : List (A × B)} →
    Unique (map proj₁ xys) → Unique xys
  Disjoint-proj₁ : ∀ {A B : Type} {xys xys′ : List (A × B)} →
    map proj₁ xys ♯ map proj₁ xys′ → xys ♯ xys′

nub∘nubBy-from∘to : ∀ {A B : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄
  {f : A → B} {xs : List A} →
  Unique (map f xs) →
    nub (nubBy f xs) ≡ xs
nub∘nubBy-from∘to {f = f}{xs} uniq =
  begin
    nub (nubBy f xs)
  ≡⟨ nub-from∘to $ Unique-nubBy f xs ⟩
    nubBy f xs
  ≡⟨ nubBy-from∘to uniq ⟩
    xs
  ∎
--

open import Prelude.Maps public
  hiding (∈ᵈ⇒⁉)

-- [MONKEY PATCH] replace postulated `Prelude.Maps.∈ᵈ⇒⁉` + `_‼_`
∈ᵈ⇒⁉ : ∀ (s : Map⟨ K ↦ V ⟩) {k} → k ∈ᵈ s → Is-just (s ⁉ k)
∈ᵈ⇒⁉ s {k} k∈ rewrite dec-yes (k ∈ᵈ? s) k∈ .proj₂ = auto

_‼_ : {k : K} (m : Map⟨ K ↦ V ⟩) → k ∈ᵈ m → V
m ‼ k∈ = destruct-Is-just (∈ᵈ⇒⁉ m k∈) .proj₁

private variable
  m m′ : Map⟨ K ↦ V ⟩
  s s₁ s₂ s₃ s₁₂ s₂₃ : Map⟨ K ↦ V ⟩
  k : K
  v : V

private pattern 𝟘 = here refl

⁉-singleton : singleton (k , v) ⁉ k ≡ just v
⁉-singleton {k} rewrite ≟-refl k = refl

postulate ‼-singleton : singleton (k , v) ‼ 𝟘 ≡ v

-- map properties
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
--

_─ᵏˢ_ : Map⟨ K ↦ V ⟩ → List K → Map⟨ K ↦ V ⟩
m ─ᵏˢ ks = filterK (_∉? ks) m

keys : Map⟨ K ↦ V ⟩ → List K
keys = map proj₁ ∘ toList

values⊑ : (m : Map⟨ K ↦ V ⟩) → ∃ $ All (_∈ᵈ m) → List V
values⊑ m (ks , ks⊆) = mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆)

values values′ : Map⟨ K ↦ V ⟩ → List V
values = map proj₂ ∘ toList
values′ m = values⊑ m (keys m , L.All.tabulate id)

toList-∪ : keys m ♯ keys m′ →  toList (m ∪ m′) ≡ toList m ++ toList m′
toList-∪ {m@(_ ⊣ ·uniq-m)}{m′@(_ ⊣ ·uniq-m′)} m♯m′ =
  begin
    toList (m ∪ m′)
  ≡⟨⟩
    nub (nubBy proj₁ (toList m ++ toList m′))
  ≡⟨ cong nub $ nubBy-from∘to uniq-proj₁-++ ⟩
    nub (toList m ++ toList m′)
  ≡⟨ nub-from∘to uniq-++ ⟩
    toList m ++ toList m′
  ∎
  where
    uniq-m  = recompute dec ·uniq-m
    uniq-m′ = recompute dec ·uniq-m′

    uniq-++ : Unique (toList m ++ toList m′)
    uniq-++ = L.Uniq.++⁺ (Unique-proj₁ uniq-m) (Unique-proj₁ uniq-m′)
                         (Disjoint-proj₁ m♯m′)

    uniq-proj₁-++ : Unique $ map proj₁ (toList m ++ toList m′)
    uniq-proj₁-++ rewrite L.map-++-commute proj₁ (toList m) (toList m′)
      = L.Uniq.++⁺ uniq-m uniq-m′ m♯m′
