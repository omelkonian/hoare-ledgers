-- Mostly copied from Prelude.Maps.

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Applicative
open import Prelude.Decidable
open import Prelude.Apartness
open import Prelude.InferenceRules
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Functor
open import Prelude.Membership

import Relation.Binary.Reasoning.Setoid as BinSetoid

module UTxOErr.Maps {K V : Type} where

Map = K → Maybe V
syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

private variable
  s s₁ s₂ s₃ s₁₂ s₂₃ m m′ m₁ m₂ m₃ m₁₂ m₂₃ : Map
  k k′ : K
  v v′ : V
  f g : Map → Map

∅ : Map
∅ = const nothing

infix 3 _∈ᵈ_ _∉ᵈ_ _∈ᵈ?_ _∉ᵈ?_
_∈ᵈ_ _∉ᵈ_ : K → Map → Type
k ∈ᵈ m = Is-just (m k)
k ∉ᵈ m = ¬ (k ∈ᵈ m)

_∈ᵈ?_ : Decidable² _∈ᵈ_
k ∈ᵈ? m with m k
... | just _  = yes auto
... | nothing = no  auto
_∉ᵈ?_ : Decidable² _∉ᵈ_
k ∉ᵈ? m = ¬? (k ∈ᵈ? m)

infix 3 _⊆ᵈ_ _⊈ᵈ_
_⊆ᵈ_ _⊈ᵈ_ : Rel₀ Map
m ⊆ᵈ m′ = ∀ k → k ∈ᵈ m → k ∈ᵈ m′
k ⊈ᵈ m = ¬ (k ⊆ᵈ m)

-- NB: left-biased
_∪_ : Op₂ Map
(m ∪ m′) k = m k <|> m′ k

module _ ⦃ _ : DecEq K ⦄ where
  singleton : K × V → Map
  singleton (k , v) k′ = if k == k′ then just v else nothing

  mkMap : List (K × V) → Map
  mkMap = λ where
    [] → ∅
    (kv ∷ kvs) → singleton kv ∪ mkMap kvs

  filterKeys : ∀ {P : Pred₀ K} → Decidable¹ P → Op₁ Map
  filterKeys P? m k = if ⌊ P? k ⌋ then m k else nothing

  _─_ : Map → List K → Map
  m ─ ks = filterKeys (_∉? ks) m

-- ** equivalence
infix 3 _≈_
_≈_ : Rel₀ Map
m ≈ m′ = ∀ k → m k ≡ m′ k

≈-refl : Reflexive _≈_
≈-refl _ = refl

≈-sym : Symmetric _≈_
≈-sym p k = sym (p k)

≈-trans : Transitive _≈_
≈-trans p q k = trans (p k) (q k)

≈-equiv : IsEquivalence _≈_
≈-equiv = record {refl = ≈-refl; sym = ≈-sym; trans = ≈-trans}

≈-setoid : Setoid 0ℓ 0ℓ
≈-setoid = record {Carrier = Map; _≈_ = _≈_; isEquivalence = ≈-equiv}

module ≈-Reasoning = BinSetoid ≈-setoid

≈-cong : ∀ {P : K → Maybe V → Type}
  → s₁ ≈ s₂
  → (∀ k → P k (s₁ k))
  → (∀ k → P k (s₂ k))
≈-cong {P = P} eq p k = subst (P k) (eq k) (p k)

-- ** separation
instance
  Apart-Map : Map // Map
  Apart-Map ._♯_ m m′ = ∀ k → ¬ ((k ∈ᵈ m) × (k ∈ᵈ m′))

♯-comm : Symmetric _♯_
♯-comm s₁♯s₂ k = s₁♯s₂ k ∘ Product.swap

♯-cong : s₁ ≈ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
♯-cong eq s₁♯s₃ k
  with p ← s₁♯s₃ k
  rewrite eq k = p

⟨_⊎_⟩≡_ : 3Rel₀ Map
⟨ m ⊎ m′ ⟩≡ m″ = (m ♯ m′) × ((m ∪ m′) ≈ m″)

-- ** membership
∈ᵈ-cong : ∀ {k s₁ s₂} → s₁ ≈ s₂ → k ∈ᵈ s₁ → k ∈ᵈ s₂
∈ᵈ-cong {k}{s₁}{s₂} s₁≈s₂ k∈ = subst Is-just (s₁≈s₂ k) k∈

module _ {s k} where
  ∉ᵈ⁺ : Is-nothing (s k) → k ∉ᵈ s
  ∉ᵈ⁺ p k∈ with just _ ← s k = case p of λ where (M.All.just ())

  ∉ᵈ⁻ : k ∉ᵈ s → Is-nothing (s k)
  ∉ᵈ⁻ k∉ with s k
  ... | just _  = ⊥-elim $ k∉ (M.Any.just tt)
  ... | nothing = auto

∉ᵈ-cong : ∀ {k s₁ s₂} → s₁ ≈ s₂ → k ∉ᵈ s₁ → k ∉ᵈ s₂
∉ᵈ-cong s≈ k∉ = k∉ ∘ ∈ᵈ-cong (≈-sym s≈)

_[_↦∅] = _∉ᵈ_

_[_↦_] : Map → K → V → Type
m [ k ↦ v ] = m k ≡ just v

_[_↦_]∅ : Map → K → V → Type
m [ k ↦ v ]∅ = m [ k ↦ v ] × ∀ k′ → k′ ≢ k → k′ ∉ᵈ m

-- ** Lemmas.

∪-comm : s₁ ♯ s₂ → (s₁ ∪ s₂) ≈ (s₂ ∪ s₁)
∪-comm {s₁}{s₂} s₁♯s₂ k
    with s₁ k | s₂ k | s₁♯s₂ k
... | nothing | nothing  | _ = refl
... | nothing | just _   | _ = refl
... | just _  | nothing  | _ = refl
... | just _  | just _   | p = ⊥-elim $ p (auto , auto)

∪-cong : s₁ ≈ s₂ → (s₁ ∪ s₃) ≈ (s₂ ∪ s₃)
∪-cong {s₁}{s₂}{s₃} eq k
  with s₁ k | s₂ k | eq k
... | nothing | .nothing  | refl = refl
... | just x  | .(just x) | refl = refl

∪-assocʳ : s₁ ∪ (s₂ ∪ s₃) ≈ (s₁ ∪ s₂) ∪ s₃
∪-assocʳ {s₁}{s₂}{s₃} k with s₁ k
... | just _  = refl
... | nothing = refl


∈ᵈ-∪⁻ : ∀ k s₁ s₂ → k ∈ᵈ (s₁ ∪ s₂) → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
∈ᵈ-∪⁻ k s₁ s₂ k∈
  with s₁ k
... | just _  = inj₁ auto
... | nothing
  with s₂ k | k∈
... | just _  | _ = inj₂ auto

∈ᵈ-∪⁺ : ∀ k s₁ s₂ → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂) → k ∈ᵈ (s₁ ∪ s₂)
∈ᵈ-∪⁺ k s₁ s₂ (inj₁ _)
  with just _ ← s₁ k = auto
∈ᵈ-∪⁺ k s₁ s₂ (inj₂ k∈)
  with s₁ k
... | just _  = auto
... | nothing = k∈


♯-∪⁻ʳ : s₁ ♯ (s₂ ∪ s₃) → (s₁ ♯ s₂) × (s₁ ♯ s₃)
♯-∪⁻ʳ {s₁}{s₂}{s₃} s₁♯s₂₃ = s₁♯s₂ , s₁♯s₃
  where
    s₁♯s₂ : s₁ ♯ s₂
    s₁♯s₂ k (k∈₁ , k∈₂) = s₁♯s₂₃ k (k∈₁ , ∈ᵈ-∪⁺ k s₂ s₃ (inj₁ k∈₂))

    s₁♯s₃ : s₁ ♯ s₃
    s₁♯s₃ k (k∈₁ , k∈₃) = s₁♯s₂₃ k (k∈₁ , ∈ᵈ-∪⁺ k s₂ s₃ (inj₂ k∈₃))

♯-∪⁻ˡ : (s₁ ∪ s₂) ♯ s₃ → (s₁ ♯ s₃) × (s₂ ♯ s₃)
♯-∪⁻ˡ p = let l , r = ♯-∪⁻ʳ (♯-comm p)
          in  ♯-comm l , ♯-comm r

♯-∪⁺ˡ : (s₁ ♯ s₃) × (s₂ ♯ s₃) → (s₁ ∪ s₂) ♯ s₃
♯-∪⁺ˡ {s₁}{s₃}{s₂} (s₁♯s₃ , s₂♯s₃) k (k∈₁₂ , k∈₃)
  with ∈ᵈ-∪⁻ k s₁ s₂ k∈₁₂
... | inj₁ k∈₁ = s₁♯s₃ k (k∈₁ , k∈₃)
... | inj₂ k∈₂ = s₂♯s₃ k (k∈₂ , k∈₃)

♯-∪⁺ʳ : (s₁ ♯ s₂) × (s₁ ♯ s₃) → s₁ ♯ (s₂ ∪ s₃)
♯-∪⁺ʳ {s₁}{s₂}{s₃} (s₁♯s₂ , s₁♯s₃) k (k∈₁ , k∈₂₃)
  with ∈ᵈ-∪⁻ k s₂ s₃ k∈₂₃
... | inj₁ k∈₂ = s₁♯s₂ k (k∈₁ , k∈₂)
... | inj₂ k∈₃ = s₁♯s₃ k (k∈₁ , k∈₃)

⊎≡-assocʳ : s₂ ♯ s₃ → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
⊎≡-assocʳ {s₂}{s₃}{s₁}{s} s₂♯s₃ (s₁♯s₂₃ , ≡s) = s₁₂♯s₃ , ≡s′
  where
    s₁₂♯s₃ : (s₁ ∪ s₂) ♯ s₃
    s₁₂♯s₃ = ♯-∪⁺ˡ (proj₂ (♯-∪⁻ʳ {s₂ = s₂} s₁♯s₂₃) , s₂♯s₃)

    p : (s₁ ∪ (s₂ ∪ s₃)) ≈ ((s₁ ∪ s₂) ∪ s₃)
    p k with s₁ k | s₂ k  | s₃ k
    ... | just _  | _       | _       = refl
    ... | nothing | nothing | nothing = refl
    ... | nothing | just _  | _       = refl
    ... | nothing | nothing | just _  = refl

    ≡s′ : ((s₁ ∪ s₂) ∪ s₃) ≈ s
    ≡s′ = ≈-trans (≈-sym p) ≡s

∪-chooseₗ : s₁ ♯ s₂ → (∀ {k} → k ∉ᵈ s₂ → (s₁ ∪ s₂) k ≡ s₁ k)
∪-chooseₗ {s₁}{s₂} _ {k} k∉ with s₁ k
... | just _ = refl
... | nothing with s₂ k | k∉
... | just _  | p = ⊥-elim $ p auto
... | nothing | _ = refl

∪-chooseᵣ : s₁ ♯ s₂ → (∀ {k} → k ∈ᵈ s₂ → (s₁ ∪ s₂) k ≡ s₂ k)
∪-chooseᵣ {s₁}{s₂} p {k} k∈ with s₁ k | p k
... | nothing | _  = refl
... | just _  | pk = ⊥-elim $ pk (auto , k∈)


⊎≡-comm : Symmetric (⟨_⊎_⟩≡ s)
⊎≡-comm (s₁♯s₂ , ≡s) = ♯-comm s₁♯s₂ , ≈-trans (≈-sym $ ∪-comm s₁♯s₂) ≡s

⊎≡-cong : s₁ ≈ s₂ → ⟨ s₁ ⊎ s₃ ⟩≡ s → ⟨ s₂ ⊎ s₃ ⟩≡ s
⊎≡-cong eq (s₁♯s₃ , ≡s) = ♯-cong eq s₁♯s₃ , ≈-trans (≈-sym (∪-cong eq)) ≡s

∪-assocˡ : (s₁ ∪ s₂) ∪ s₃ ≈ s₁ ∪ (s₂ ∪ s₃)
∪-assocˡ {s₁}{s₂}{s₃} = ≈-sym (∪-assocʳ {s₁}{s₂}{s₃})

⊎≈-assocʳ :
  ∙ ⟨ s₁ ⊎ s₂₃ ⟩≡ s
  ∙ ⟨ s₂ ⊎ s₃  ⟩≡ s₂₃
    ───────────────────
    ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
  × (s₁ ♯ s₂)
⊎≈-assocʳ {s₁}{s₂₃}{s}{s₂}{s₃} (s₁♯s₂₃ , ≡s) (s₂♯s₃ , ≡s₂₃) =
  ⊎≡-assocʳ s₂♯s₃ ≡ss , proj₁ (♯-∪⁻ʳ s₁♯s₂₃′)
  where
    s₁♯s₂₃′ : s₁ ♯ (s₂ ∪ s₃)
    s₁♯s₂₃′ = ♯-comm $ ♯-cong (≈-sym ≡s₂₃) $ ♯-comm s₁♯s₂₃

    ≡ss : ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s
    ≡ss = s₁♯s₂₃′ , ≈-trans (≈-trans (∪-comm s₁♯s₂₃′) (≈-trans (∪-cong ≡s₂₃) (≈-sym $ ∪-comm s₁♯s₂₃))) ≡s

⊎≡-assocˡ : ∀ {s₁ s₂ s₃ s} → s₁ ♯ s₂ → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s → ⟨ s₁ ⊎ (s₂ ∪ s₃)  ⟩≡ s
⊎≡-assocˡ {s₁}{s₂}{s₃}{s} s₁♯s₂ p@(s₁₂♯s₃ , _) =
    ⊎≡-comm ∘ ⊎≡-assocʳ (♯-comm $ proj₁ $ ♯-∪⁻ˡ s₁₂♯s₃)
  $ ⊎≡-comm ∘ ⊎≡-assocʳ s₁♯s₂
  $ ⊎≡-comm p

⊎≈-assocˡ :
  ∙ ⟨ s₁₂ ⊎ s₃ ⟩≡ s
  ∙ ⟨ s₁ ⊎ s₂  ⟩≡ s₁₂
    ───────────────────
    ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s
  × (s₂ ♯ s₃)
⊎≈-assocˡ {s₁₂}{s₃}{s}{s₁}{s₂} (s₁₂♯s₃ , ≡s) (s₁♯s₂ , ≡s₁₂) =
  ⊎≡-assocˡ s₁♯s₂ ≡ss , proj₂ (♯-∪⁻ˡ {s₁ = s₁} s₁₂♯s₃′)
  where
    s₁₂♯s₃′ : (s₁ ∪ s₂) ♯ s₃
    s₁₂♯s₃′ = ♯-cong (≈-sym ≡s₁₂) s₁₂♯s₃

    ≡ss : ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
    ≡ss = s₁₂♯s₃′ , ≈-trans (∪-cong ≡s₁₂) ≡s
