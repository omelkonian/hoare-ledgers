module Common.Hash where

open import Prelude.Init; open SetAsType

HashId = String

postulate _♯ : ∀ {A : Type ℓ} → A → HashId
