---------------------------
-- ** Axiomatic semantics

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Maps.Abstract

module ShallowHoare.HoareLogic (Part : Type) ⦃ _ : DecEq Part ⦄ where

-- NB. ⦃ it ⦄ required due to Agda bug, reported at https://github.com/agda/agda/issues/5093
open import ShallowHoare.Ledger Part ⦃ it ⦄

-- ** Deeply embedded formulas/propositions for our logic.
-- NB: this is necessary, in order to inspect the referenced participants later on.
data Assertion : Type₁ where
  `emp : Assertion                          -- ^ holds for the empty ledger
  _`↦_ : Part → ℕ → Assertion               -- ^ holds for the singleton ledger { A ↦ v }
  _`∗_ : Assertion → Assertion → Assertion  -- ^ separating conjuction
  _`∘⟦_⟧ : Assertion → L → Assertion        -- ^ holds for a ledger that is first transformed using ⟦ t₁⋯tₙ ⟧

infixl 9 _`∘⟦_⟧
infixr 10 _`∗_
infix 11 _`↦_

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

-- We denote assestions as predicates over ledger states.
private
  emp : Pred₀ S
  emp m = ∀ k → k ∉ᵈ m

  _∗_ : Pred₀ S → Pred₀ S → Pred₀ S
  (P ∗ Q) s = ∃ λ s₁ → ∃ λ s₂ → (⟨ s₁ ⊎ s₂ ⟩≡ s) × P s₁ × Q s₂

⟦_⟧ᵖ : Assertion → Pred₀ S
⟦ `emp    ⟧ᵖ = emp
⟦ p `↦ n  ⟧ᵖ s = s [ p ↦ n ]∅
⟦ P `∗ Q  ⟧ᵖ = ⟦ P ⟧ᵖ ∗ ⟦ Q ⟧ᵖ
⟦ P `∘⟦ l ⟧  ⟧ᵖ s = ⟦ P ⟧ᵖ $ ⟦ l ⟧ s

-- Convenient notation for working with assertions instead of predicates.
infixl 9 _`∘⟦_⟧ₜ
_`∘⟦_⟧ₜ : Assertion → Tx → Assertion
P `∘⟦ t ⟧ₜ = P `∘⟦ [ t ] ⟧

infix 1 _`⊢_
_`⊢_ : Assertion → Assertion → Type
P `⊢ Q = ⟦ P ⟧ᵖ ⊢ ⟦ Q ⟧ᵖ

_∙_ : Assertion → S → Type
P ∙ s = ⟦ P ⟧ᵖ s

-- ** Hoare triples
𝕆⟨_⟩_⟨_⟩ 𝔻⟨_⟩_⟨_⟩ ⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Type
𝕆⟨ P ⟩ l ⟨ Q ⟩ = ∀ {s s′} → P ∙ s → l , s —→⋆′ s′ → Q ∙ s′
𝔻⟨ P ⟩ l ⟨ Q ⟩ = ∀ {s} → P ∙ s → Q ∙ ⟦ l ⟧ s

𝔻⇒𝕆 : 𝔻⟨ P ⟩ l ⟨ Q ⟩ → 𝕆⟨ P ⟩ l ⟨ Q ⟩
𝔻⇒𝕆 PlQ Ps s→s′ rewrite sym $ oper⇒denot s→s′ = PlQ Ps

𝕆⇒𝔻 : 𝕆⟨ P ⟩ l ⟨ Q ⟩ → 𝔻⟨ P ⟩ l ⟨ Q ⟩
𝕆⇒𝔻 PlQ Ps = PlQ Ps (denot⇒oper refl)

module HoareOper where
  `base :
    --------------
    𝕆⟨ P ⟩ [] ⟨ P ⟩
  `base Ps base = Ps

  `step :
      𝕆⟨ P ⟩ l ⟨ R ⟩
      --------------------------
    → 𝕆⟨ P `∘⟦ t ⟧ₜ ⟩ t ∷ l ⟨ R ⟩
  `step PlR Ps (step singleStep tr) = PlR Ps tr

  weaken : P′ `⊢ P → 𝕆⟨ P ⟩ l ⟨ Q ⟩ → 𝕆⟨ P′ ⟩ l ⟨ Q ⟩
  weaken H PlQ P′s s→s′ = PlQ (H P′s) s→s′

  strengthen : Q `⊢ Q′ → 𝕆⟨ P ⟩ l ⟨ Q ⟩ → 𝕆⟨ P ⟩ l ⟨ Q′ ⟩
  strengthen H PlQ Ps = H ∘ PlQ Ps

  consequence :
      P′ `⊢ P          -- ^ weakening the pre-condition
    → Q  `⊢ Q′         -- ^ strengthening the post-condition
    → 𝕆⟨ P  ⟩ l ⟨ Q  ⟩
      ---------------
    → 𝕆⟨ P′ ⟩ l ⟨ Q′ ⟩
  consequence {P′}{P}{Q}{Q′} wk st = strengthen {Q}{Q′}{P′} st ∘ weaken {P′}{P}{_}{Q = Q} wk

module HoareDenot where
  `base :
    --------------
    𝔻⟨ P ⟩ [] ⟨ P ⟩
  `base Ps = Ps

  `step :
      𝔻⟨ P ⟩ l ⟨ R ⟩
      --------------------------
    → 𝔻⟨ P `∘⟦ t ⟧ₜ ⟩ t ∷ l ⟨ R ⟩
  `step PlR Ps = PlR Ps

  weaken : P′ `⊢ P → 𝔻⟨ P ⟩ l ⟨ Q ⟩ → 𝔻⟨ P′ ⟩ l ⟨ Q ⟩
  weaken H PlQ = PlQ ∘ H

  strengthen : Q `⊢ Q′ → 𝔻⟨ P ⟩ l ⟨ Q ⟩ → 𝔻⟨ P ⟩ l ⟨ Q′ ⟩
  strengthen H PlQ = H ∘ PlQ

  consequence :
      P′ `⊢ P          -- ^ weakening the pre-condition
    → Q  `⊢ Q′         -- ^ strengthening the post-condition
    → 𝔻⟨ P  ⟩ l ⟨ Q  ⟩
      ---------------
    → 𝔻⟨ P′ ⟩ l ⟨ Q′ ⟩
  consequence {P′}{P}{Q}{Q′}{l} wk st PlQ = st ∘ PlQ ∘ wk

⟨ P ⟩ l ⟨ Q ⟩ = 𝔻⟨ P ⟩ l ⟨ Q ⟩
open HoareDenot public

-- `step⁻ : ⟨ P ⟩ t ∷ l ⟨ Q ⟩
--        → ⟨ P `∘⟦ t ⟧ₜ⁻¹ ⟩ l ⟨ Q ⟩
-- `step⁻ PlQ Ps = let p = PlQ Ps in {!p!}


-- -- Derived alternative formulation for step, using list concatenation.
-- step′ :
--     ⟨ P ⟩ l  ⟨ Q ⟩
--   → ⟨ Q ⟩ l′ ⟨ R ⟩
--     -------------------
--   → ⟨ P ⟩ l ++ l′ ⟨ R ⟩
-- step′ {l = l} {l′ = l′} PlQ QlR {s} rewrite comp {l}{l′} s = QlR ∘ PlQ

-- -- Utilities for Hoare triples.
-- axiom-base⋆ : ⟨ P `∘⟦ l ⟧ ⟩ l ⟨ P ⟩
-- axiom-base⋆ = id

-- -- ** Reasoning syntax for Hoare triples.
-- module HoareReasoning where
--   infix  -2 begin_
--   infixr -1 _~⟪_⟩_ _~⟨_⟫_ _~⟨_∶-_⟩_ _~⟨_∶-_⟩′_
--   infix  0  _∎

--   begin_ : ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q ⟩
--   begin p = p

--   -- weakening syntax
--   _~⟪_⟩_ : ∀ P′ → P′ `⊢ P  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ l ⟨ R ⟩
--   -- _~⟪_⟩_ {P}{l}{R} P′ H = weaken {P′}{P}{l}{R} H
--   _ ~⟪ H ⟩ PlR = PlR ∘ H

--   -- strengthening syntax
--   _~⟨_⟫_ : ∀ R′ → R `⊢ R′  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
--   -- _~⟨_⟫_ {R}{P}{l} R′ H = strengthen {R}{R′}{P}{l} H
--   _ ~⟨ H ⟫ PlR = H ∘ PlR

--   -- step syntax
--   _~⟨_∶-_⟩_ : ∀ P′ → (t : Tx) → ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
--   _~⟨_∶-_⟩_ {P}{l}{R} P′ t H PlR = PlR ∘ H

--   -- step′ syntax
--   _~⟨_∶-_⟩′_ : ∀ P′ → (l : L) → ⟨ P′ ⟩ l ⟨ P ⟩ → ⟨ P ⟩ l′ ⟨ R ⟩ → ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
--   _~⟨_∶-_⟩′_ {P}{l′}{R} P′ l H PlR = step′ {P′}{l}{P}{l′}{R} H PlR

--   _∎ : ∀ P → ⟨ P ⟩ [] ⟨ P ⟩
--   p ∎ = `base {P = p}

-- -- ** Lemmas about separating conjunction.

-- -- commutativity
-- ∗↔ : P `∗ Q `⊢ Q `∗ P
-- ∗↔ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) = s₂ , s₁ , ∪≡-comm ≡s , Qs₂ , Ps₁

-- -- associativity
-- ∗↝ : P `∗ Q `∗ R `⊢ (P `∗ Q) `∗ R
-- ∗↝ {x = s} (s₁ , s₂₃ , ≡s , Ps₁ , (s₂ , s₃ , ≡s₂₃ , Qs₂ , Rs₃)) =
--   let ≡s′ , s₁♯s₂ = ⊎≈-assocʳ ≡s ≡s₂₃
--   in (s₁ ∪ s₂) , s₃ , ≡s′ , (s₁ , s₂ , (s₁♯s₂ , ≈-refl) , Ps₁ , Qs₂) , Rs₃

-- ↜∗ : (P `∗ Q) `∗ R `⊢ P `∗ Q `∗ R
-- ↜∗ {x = s} (s₁₂ , s₃ , ≡s , (s₁ , s₂ , ≡s₁₂ , Ps₁ , Qs₂) , Rs₃) =
--   let ≡s′ , s₂♯s₃ = ⊎≈-assocˡ ≡s ≡s₁₂
--   in s₁ , (s₂ ∪ s₃) , ≡s′ , Ps₁ , (s₂ , s₃ , (s₂♯s₃ , ≈-refl) , Qs₂ , Rs₃)

-- -- ** Useful lemmas when transferring a value between participants in the minimal context.
-- _↝_∶-_ : ∀ A B → A ≢ B → ⟨ A `↦ v `∗ B `↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A `↦ 0 `∗ B `↦ (v′ + v) ⟩
-- _↝_∶-_ {v}{v′} A B A≢B = d
--   where
--     tx = A —→⟨ v ⟩ B

--     d : A `↦ v `∗ B `↦ v′ `⊢ A `↦ 0 `∗ B `↦ (v′ + v) `∘⟦ [ tx ] ⟧
--     d {s} (s₁ , s₂ , ≡s , As₁ , Bs₂) = s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′
--       where
--         s₁′ s₂′ ⟦t⟧s : S
--         s₁′ = singleton (A , 0)
--         s₂′ = singleton (B , v′ + v)
--         ⟦t⟧s = ⟦ tx ⟧ s

--         As₁′ : (A `↦ 0) ∙ s₁′
--         As₁′ = singleton-law

--         Bs₂′ : (B `↦ (v′ + v)) ∙ s₂′
--         Bs₂′ = singleton-law

--         s₁♯s₂ : s₁′ ♯ s₂′
--         s₁♯s₂ = singleton♯ A≢B

--         s₁₂ = s₁ ∪ s₂

--         ≈s″ : (s₁′ ∪ s₂′) ≈ ⟦ tx ⟧ (s₁ ∪ s₂)
--         ≈s″ =
--           begin
--             s₁′ ∪ s₂′
--           ≡⟨⟩
--             singleton (A , 0) ∪ singleton (B , v′ + v)
--           ≈⟨ ≈-sym (transfer A≢B) ⟩
--             run [ A ∣ v ↦ B ] (singleton (A , v) ∪ singleton (B , v′))
--           ≈⟨ ≈-cong-cmd [ A ∣ v ↦ B ] s₁∪s₂≡ ⟩
--             run [ A ∣ v ↦ B ] (s₁ ∪ s₂)
--           ≡⟨⟩
--             ⟦ tx ⟧ (s₁ ∪ s₂)
--           ∎
--           where
--             open ≈-Reasoning

--             s₁∪s₂≡ : (singleton (A , v) ∪ singleton (B , v′)) ≈ (s₁ ∪ s₂)
--             s₁∪s₂≡ = ≈-sym $
--               begin
--                 s₁ ∪ s₂
--               ≈⟨ ∪-cong (singleton≈ As₁) ⟩
--                 singleton (A , v) ∪ s₂
--               ≈⟨ ∪-congʳ (♯-comm (♯-cong (≈-sym $ singleton≈ Bs₂) (singleton♯ (≢-sym A≢B)))) (singleton≈ Bs₂) ⟩
--                 singleton (A , v) ∪ singleton (B , v′)
--               ∎

--         ≈s′ : (s₁′ ∪ s₂′) ≈ ⟦t⟧s
--         ≈s′ = ≈-trans ≈s″ $ ≈-cong-cmd [ A ∣ v ↦ B ] (proj₂ ≡s)

--         ≡s′ : ⟨ s₁′ ⊎ s₂′ ⟩≡ ⟦t⟧s
--         ≡s′ = s₁♯s₂ , ≈s′

-- _↜_∶-_ : ∀ A B → A ≢ B → ⟨ A `↦ v′ `∗ B `↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A `↦ (v′ + v) `∗ B `↦ 0 ⟩
-- _↜_∶-_ {v}{v′} A B A≢B (s₁ , s₂ , ≡s , As₁ , Bs₂) =
--   let (s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′) = (B ↝ A ∶- (A≢B ∘ sym)) (s₂ , s₁ , ∪≡-comm ≡s , Bs₂ , As₁)
--   in (s₂′ , s₁′ , ∪≡-comm ≡s′ , Bs₂′ , As₁′)
