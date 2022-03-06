---------------------------
-- ** Separation logic (SL)

open import Prelude.Init
open L.Mem
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Maps as Map hiding (_♯_)
open import Prelude.Ord
open import Prelude.General
open import Prelude.InferenceRules


module SL (Part : Set) ⦃ _ : DecEq Part ⦄ where

open import Ledger     Part ⦃ it ⦄
open import HoareLogic Part ⦃ it ⦄

↔-trans : ∀ {A B C : Set} → A ↔ B → B ↔ C → A ↔ C
↔-trans (A→B , B→A) (B→C , C→B) = (B→C ∘ A→B) , (B→A ∘ C→B)

-- removeKey : Part → S → S
-- removeKey p s = buildMap λ k →
--   if p == k then nothing
--             else s ⁉ k

_∈ᶠ_ _∉ᶠ_ : Part → (S → S) → Set
k ∈ᶠ f = ∃ λ s → (s ⁉ k) ≢ (f s ⁉ k)
k ∉ᶠ f = ¬ k ∈ᶠ f
-- k ∉ᶠ f = ∀ s → (s ⁉ k) ≡ (f s ⁉ k)

_∉ᵃ_ : Part → Assertion → Set
p ∉ᵃ P =
  -- ∀ s s′ → p ∉ᵈ s → p ∉ᵈ s′ → P s ⇔ P s′
  -- ∀ s → P s ⇔ P (removeKey p s)
  -- ∀ s f → p ∉ᶠ f → P s ⇔ P (f s)
  -- ∀ s f → p ∈ᶠ f → P s ⇔ P (f s)
  ∀ s f → p ∈ᶠ f → (∀ p′ → p′ ≢ p → p′ ∉ᶠ f) → P s ⇔ P (f s)
  -- ∀ s → P s → p ∉ᵈ s

record _//_ (A : Set ℓ) (B : Set ℓ′) : Set (lsuc ℓ ⊔ₗ lsuc ℓ′) where
  field _♯_ : A → B → Set
open _//_ ⦃...⦄ public

private variable X : Set ℓ

instance
  -- Disjoint-SS : S // S
  -- Disjoint-SS ._♯_ = Map._♯_

  -- Disjoint-Part : Part // S
  -- Disjoint-Part ._♯_ = _∉ᵈ_

  -- Disjoint-TS : ⦃ Part // X ⦄ → Tx // X
  -- Disjoint-TS ._♯_ tx x = (tx .sender ♯ x) × (tx .receiver ♯ x)

  -- Disjoint-TX⇒LX : ⦃ Tx // X ⦄ → L // X
  -- Disjoint-TX⇒LX ⦃ i ⦄ ._♯_ l x = All (λ tx → _♯_ ⦃ i ⦄ tx x) l

  -- Disjoint-TA : Tx // Assertion
  -- Disjoint-TA ._♯_ tx P = (tx .sender ∉ᵃ P) × (tx .receiver ∉ᵃ P)

  Denotable//Assertion : ∀ {A : Set} → ⦃ Denotable A ⦄ → A // Assertion
  Denotable//Assertion ._♯_ x P = ∀ s → P s ⇔ P (⟦ x ⟧ s)

-- ⟦_⟧♯_ : ∀ {A : Set} → ⦃ Denotable A ⦄ → A → Assertion → Set
-- ⟦ x ⟧♯ P = ∀ s → P s ⇔ P (⟦ x ⟧ s)

-- ⟦_⟧♯ˢ_ : ∀ {A : Set} → ⦃ Denotable A ⦄ → A → S → Set
-- ⟦ x ⟧♯ˢ s = ⟦ x ⟧ s ≈ s

destruct-♯ : (t ∷ l) ♯ P → t ♯ P × l ♯ P
destruct-♯ p = (λ s → {!p s!}) , (λ s → {!p s!})
  -- where
  --   s : S
  --   p s : P s ⇔ P (⟦ t ∷ l ⟧ s)
  --             ⇔ P (⟦ l ⟧ (⟦ t ⟧ s))

-- ♯⇒♯ : l ♯ R → R s → l ♯ s
-- ♯⇒♯ {l = []} _ _ = λ k → refl
-- ♯⇒♯ {l = A —→⟨ _ ⟩ B ∷ _}{R}{s} l♯R Rs = λ k → {!l♯R s .proj₁ Rs!}
-- -- ♯⇒♯ {l = []} _ _ = []
-- -- ♯⇒♯ {l = A —→⟨ _ ⟩ B ∷ _} {s} ((A∉ , B∉) ∷ l♯R) Rs = (A∉ _ Rs , B∉ _ Rs) ∷ ♯⇒♯ l♯R Rs

-- frame-update :
--   ∙ A ∉ᵃ R
--     ──────────────────────
--     R s ⇔ R (update (A , v) s)
-- frame-update {A}{R}{s}{v} A∉ = A∉ s (update (A , v)) A∈ B∉
--   where
--     A∈ : A ∈ᶠ update (A , v)
--     A∈ = singleton (A , suc v) , neq
--       where
--         neq : singleton (A , suc v) ⁉ A
--             ≢ update (A , v) (singleton (A , suc v)) ⁉ A
--         neq rewrite singleton-law′ {k = A}{suc v}
--           | singleton-law′ {k = A}{v}
--           | singleton-accept {k = A}{v}{singleton (A , suc v)}
--           = λ ()

--     B∉ : ∀ B → B ≢ A → B ∉ᶠ update (A , v)
--     B∉ B B≢ (s , neq) = {!!}

-- {-
-- frame-modify : ∀ {f} →
--   ∙ A ∉ᵃ R
--     ──────────────────────
--     R s ⇔ R (modify A f s)
-- frame-modify {A = A} {s = s} A∉ with s ⁉ A
-- ... | nothing = id , id
-- ... | just x = frame-update A∉

-- -}

-- frame-⟦⟧ :
--   ∙ l ♯ R
--   ∙ R s
--     ────────────
--     R (⟦ l ⟧ s)
-- frame-⟦⟧ = {!!}
-- -- frame-⟦⟧ {[]} {R} {s} l♯R Rs = Rs
-- -- frame-⟦⟧ {tx@(A —→⟨ v ⟩ B) ∷ l} {R} {s} ((A∉ , B∉) ∷ l♯R) Rs = frame-⟦⟧ l♯R Rs′
-- --   where
-- --     Rs′ : R $ ⟦ tx ⟧ s
-- --     Rs′ with s ⁉ A
-- --     ... | nothing = Rs
-- --     ... | just vᵃ
-- --       with s ⁉ B
-- --     ... | nothing = Rs
-- --     ... | just _
-- --       with v ≤? vᵃ
-- --     ... | no _ = Rs
-- --     ... | yes v≤
-- --       = frame-modify A∉ .proj₁
-- --       $ frame-modify B∉ .proj₁ Rs

-- Helper lemma for [FRAME]: pushing ⟦ l ⟧ inside the partition.
frame-helper :
    ⟨ s₁ ◇ s₂ ⟩≡ s
  -- → l ♯ s₂
    -----------------------
  → ⟨ ⟦ l ⟧ s₁ ◇ ⟦ l ⟧ s₂ ⟩≡ ⟦ l ⟧ s
frame-helper = {!!}
-- {-
-- frame-helper {l = []} p = p
-- frame-helper {s₁}{s₂}{s}{l₀@(A —→⟨ v ⟩ B ∷ l)} (s₁♯s₂ , ≡s) =
--   frame-helper {run [ A ∣ v ↦ B ] s₁}{run [ A ∣ v ↦ B ] s₂}{run [ A ∣ v ↦ B ] s}{l} p′
--   where
--     A∉₂ : A ∉ᵈ s₂
--     A∉₂ = ?

--     B∉₂ : B ∉ᵈ s₂
--     B∉₂ = ?

--     p₁ : (run [ A ∣ v ↦ B ] s₁) ♯ (run [ A ∣ v ↦ B ] s₂)
--     p₁ = ? -- transfer-helper s₁♯s₂ B∉₂

--     ∉⇒≢ : ∀ k → k ∈ᵈ s₂ → (k ≢ A) × (k ≢ B)
--     ∉⇒≢ k k∈ = (λ where refl → A∉₂ k∈) , (λ where refl → B∉₂ k∈)

--     p₂ : (run [ A ∣ v ↦ B ] s₁) ∪ (run [ A ∣ v ↦ B ] s₂) ≈ run [ A ∣ v ↦ B ] s
--     p₂ k
--       with eq ← ≡s k
--       with eqᵃ ← ≡s A
--       with eqᵇ ← ≡s B
--       with ¿ k ∈ᵈ s₂ ¿
--     ... | yes k∈
--       with k≢A , k≢B ← ∉⇒≢ k k∈
--       rewrite ∪-chooseᵣ p₁ k∈
--             | ∪-chooseᵣ s₁♯s₂ k∈
--             | drop-[∣↦] {v = v} {s = s} k k≢A k≢B
--             = eq
--     ... | no k∉
--       rewrite ∪-chooseₗ p₁ k∉
--             | ∪-chooseₗ s₁♯s₂ k∉
--       with s₁ ⁉ A | inspect (s₁ ⁉_) A
--          | s  ⁉ A | inspect (s  ⁉_) A
--          | eqᵃ
--     ... | nothing | _ | nothing | _ | _ = eq
--     ... | nothing | ≡[ s₁A≡ ] | just _  | ≡[ sA≡ ] | _
--         = let p = ↦-∪⁺ʳ {s₂ = s₂} $ ⁉⇒∉ᵈ (subst Is-nothing (sym s₁A≡) auto)
--           in ⊥-elim $ A∉₂ $ ⁉⇒∈ᵈ $ subst Is-just (sym $ trans p (trans eqᵃ sA≡)) auto
--     ... | just vᵃ | ≡[ s₁A≡ ] | nothing | _ | eqᵃ′
--         = case trans (sym $ (↦-∪⁺ˡ {s₂ = s₂} s₁A≡)) eqᵃ′ of λ ()
--     ... | just vᵃ  | ≡[ s₁A≡ ] | just vᵃ′ | _ | eqᵃ′
--       with vᵃ ≟ vᵃ′
--     ... | no neq = ⊥-elim $ neq $ M.just-injective $ trans (sym $ ↦-∪⁺ˡ {s₂ = s₂} s₁A≡) eqᵃ′
--     ... | yes refl
--       with s₁ ⁉ B | inspect (s₁ ⁉_) B
--          | s  ⁉ B | inspect (s  ⁉_) B
--          | eqᵇ
--     ... | nothing | _ | nothing | _ | _
--         = eq
--     ... | nothing | ≡[ s₁B≡ ] | just _  | ≡[ sB≡ ] | _
--         = let p = ↦-∪⁺ʳ {s₂ = s₂} $ ⁉⇒∉ᵈ (subst Is-nothing (sym s₁B≡) auto)
--           in ⊥-elim $ B∉₂ $ ⁉⇒∈ᵈ $ subst Is-just (sym $ trans p (trans eqᵇ sB≡)) auto
--     ... | just vᵇ | ≡[ s₁B≡ ] | nothing | _ | eqᵇ′
--         = case trans (sym $ (↦-∪⁺ˡ {s₂ = s₂} s₁B≡)) eqᵇ′ of λ ()
--     ... | just vᵇ  | ≡[ s₁B≡ ] | just vᵇ′ | _ | eqᵇ′
--       with vᵇ ≟ vᵇ′
--     ... | no neq = ⊥-elim $ neq $ M.just-injective $ trans (sym $ ↦-∪⁺ˡ {s₂ = s₂} s₁B≡) eqᵇ′
--     ... | yes refl
--       with v ≤? vᵃ
--     ... | no  _ = eq
--     ... | yes _ = ≡-cong-update $ ≡-cong-update eq

--     p′ : ⟨ run [ A ∣ v ↦ B ] s₁ ⊎ run [ A ∣ v ↦ B ] s₂ ⟩≡ run [ A ∣ v ↦ B ] s
--     p′ = p₁ , p₂
-- -}
-- -- The proof of the frame rule from separation logic, allowing us to prove formulas in minimal contexts
-- -- and then weaken our results to the desired context (assuming the rest of the context is disjoint).

[FRAME] : ∀ R
  → l ♯ R
  → ⟨ P ⟩ l ⟨ Q ⟩
    -----------------------
  → ⟨ P ∗ R ⟩ l ⟨ Q ∗ R ⟩
[FRAME] {l}{P}{Q} R l♯R PlQ = denot⇒axiom d
  where
    d : (P ∗ R) ⊢ (Q ∗ R) ∘ ⟦ l ⟧
    d = {!!}
--    d {s} (s₁ , s₂ , s₁◇s₂ , Ps₁ , Rs₂) = ⟦ l ⟧ s₁ , ⟦ l ⟧ s₂  , p , Qs₁′ , Rs₂′
--       where
--         Qs₁′ : Q (⟦ l ⟧ s₁)
--         Qs₁′ = axiom⇒denot PlQ Ps₁

--         Rs₂′ : R (⟦ l ⟧ s₂)
--         Rs₂′ = frame-⟦⟧ l♯R Rs₂

--         p : ⟨ ⟦ l ⟧ s₁ ◇ ⟦ l ⟧ s₂ ⟩≡ ⟦ l ⟧ s
--         p = {!!} -- frame-helper s₁◇s₂ l♯s₂
