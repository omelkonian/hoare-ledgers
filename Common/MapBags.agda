-- ** Utilities relating Prelude.Maps and Prelude.Bags.

open import Prelude.Init; open SetAsType; open ≡-Reasoning
open import Prelude.Maybes
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Functor
open import Prelude.Lists.Dec
open import Prelude.Apartness

open import Prelude.Maps
import Prelude.Sets as S
import Prelude.Bags as B

module Common.MapBags {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : DecEq V ⦄ where

open import Common.Maps {K}{V}

keysˢ : Map⟨ K ↦ V ⟩ → B.Bag⟨ K ⟩
keysˢ = fromList ∘ keys

values⊑ˢ : (m : Map⟨ K ↦ V ⟩) → ∃ $ All (_∈ᵈ m) → B.Bag⟨ V ⟩
values⊑ˢ = fromList ∘₂ values⊑

valuesˢ valuesˢ′ : Map⟨ K ↦ V ⟩ → B.Bag⟨ V ⟩
valuesˢ = fromList ∘ map proj₂ ∘ toList
valuesˢ′ m = values⊑ˢ m (keys m , L.All.tabulate id)

private variable
  m m′ : Map⟨ K ↦ V ⟩
  ks : List K; kvs : List (K × V)

module _ m m′ (m♯m′ : keys m ♯ keys m′) where
  valuesˢ-∪ : valuesˢ (m ∪ m′) ≡ valuesˢ m B.∪ valuesˢ m′
  valuesˢ-∪ =
    begin
      valuesˢ (m ∪ m′)
    ≡⟨⟩
      fromList (proj₂ <$> toList (m ∪ m′))
    ≡⟨ cong (fromList ∘ map proj₂) $ toList-∪ {m}{m′} m♯m′ ⟩
      fromList (proj₂ <$> (toList m ++ toList m′))
    ≡⟨ cong fromList $ L.map-++-commute proj₂ (toList m) (toList m′) ⟩
      fromList ((proj₂ <$> toList m) ++ (proj₂ <$> toList m′))
    ≡⟨⟩
      fromList (proj₂ <$> toList m) B.∪ fromList (proj₂ <$> toList m′)
    ≡⟨⟩
      valuesˢ m B.∪ valuesˢ m′
    ∎

valuesˢ-─ : ∀ m (p : ∃ $ All (_∈ᵈ m)) →
  valuesˢ (m ─ᵏˢ p .proj₁) ≡ valuesˢ m B.─ values⊑ˢ m p
valuesˢ-─ m (ks , ks⊆) =
  begin
    valuesˢ (m ─ᵏˢ ks)
  ≡⟨⟩
    fromList (proj₂ <$> toList (m ─ᵏˢ ks))
  ≡⟨⟩
    fromList (proj₂ <$> filter ((_∉? ks) ∘ proj₁) (toList m))
  ≡⟨ cong fromList H ⟩
    fromList
      (map proj₂ (toList m) ∸[bag] (mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆)))
  ≡⟨⟩
    fromList (proj₂ <$> toList m)
      B.─
    fromList (mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆))
  ≡⟨⟩
    fromList (proj₂ <$> toList m) B.─ fromList (values⊑ m (-, ks⊆))
  ≡⟨⟩
    valuesˢ m B.─ values⊑ˢ m (-, ks⊆)
  ∎
  where
    postulate
      H : map proj₂ (filter ((_∉? ks) ∘ proj₁) (toList m))
        ≡ map proj₂ (toList m) ∸[bag] (mapWith∈ ks ((m ‼_) ∘ L.All.lookup ks⊆))

postulate
  values⊆⇒⊆[bag] : ∀ m (p : ∃ $ All (_∈ᵈ m)) → values⊑ m p ⊆[bag] values m

values⊆⇒⊆ˢ : ∀ m (p : ∃ $ All (_∈ᵈ m)) → values⊑ˢ m p B.⊆ˢ valuesˢ m
values⊆⇒⊆ˢ = values⊆⇒⊆[bag]

valuesˢ∘fromList : Unique (proj₁ <$> kvs) →
  valuesˢ (fromList kvs) ≡ fromList (proj₂ <$> kvs)
valuesˢ∘fromList = cong (fromList ∘ map proj₂) ∘ nub∘nubBy-from∘to
