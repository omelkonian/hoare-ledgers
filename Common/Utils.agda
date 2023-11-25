module Common.Utils where

open import Prelude.Init; open SetAsType
open import Prelude.Lists.Sums

∑ : ∀ {A : Type} → List A → (A → ℕ) → ℕ
∑ xs f = ∑ℕ (map f xs)

_€ = id
