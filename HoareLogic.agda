-------------------------
-- ** Axiomatic semantics

open import Prelude.Init hiding (_⇔_)
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Maps

module HoareLogic (Part : Set) ⦃ _ : DecEq Part ⦄ where

open import Ledger Part ⦃ it ⦄

⟦⟧ₗ-mono : KeyMonotonic ⟦ l ⟧
⟦⟧ₗ-mono {[]} _ _ = id
⟦⟧ₗ-mono {t ∷ l} s p = ⟦⟧ₗ-mono {l} (⟦ t ⟧ s) p ∘ cmd-mon [ sender t ∣ value t ↦ receiver t ] s p

data Assertion : Set₁ where
  `emp : Assertion
  _`↦_ : Part → ℕ → Assertion
  _`∗_ : Assertion → Assertion → Assertion
  _`∘⟦_⟧ : Assertion → L → Assertion

infixl 9 _`∘⟦_⟧
infixr 10 _`∗_
infix 11 _`↦_

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

infixl 9 _`∘⟦_⟧ₜ
_`∘⟦_⟧ₜ : Assertion → Tx → Assertion
P `∘⟦ t ⟧ₜ = P `∘⟦ [ t ] ⟧

infix 1 _`⊢_
_`⊢_ : Assertion → Assertion → Set
P `⊢ Q = ⟦ P ⟧ᵖ ⊢ ⟦ Q ⟧ᵖ

_∙_ : Assertion → S → Set
P ∙ s = ⟦ P ⟧ᵖ s

variable
  P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

data ⟨_⟩_⟨_⟩ : Assertion → L → Assertion → Set₁ where

  base :
    ------------
    ⟨ P ⟩ [] ⟨ P ⟩

  step :
      ⟨ P ⟩ l ⟨ R ⟩
      -------------------------
    → ⟨ P `∘⟦ t ⟧ₜ ⟩ t ∷ l ⟨ R ⟩

  consequence :
      P′ `⊢ P
    → Q  `⊢ Q′
    → ⟨ P  ⟩ l ⟨ Q  ⟩
      ---------------
    → ⟨ P′ ⟩ l ⟨ Q′ ⟩

data ⟨_⟩_⟨_⟩′ : Assertion → L → Assertion → Set₁ where

  base :
    ----------------------------
    ⟨ P `∘⟦ t ⟧ₜ ⟩ [ t ] ⟨ P ⟩′

  step :
      ⟨ P ⟩ l  ⟨ Q ⟩′
    → ⟨ Q ⟩ l′ ⟨ R ⟩′
      --------------------
    → ⟨ P ⟩ l ++ l′ ⟨ R ⟩′

  consequence :
      P′ `⊢ P
    → Q  `⊢ Q′
    → ⟨ P ⟩ l ⟨ Q ⟩′
      ----------------
    → ⟨ P′ ⟩ l ⟨ Q′ ⟩′

-- utilities
weaken : P′ `⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken H = consequence H id

strengthen : Q `⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen H = consequence id H

axiom-base⋆ : ⟨ P `∘⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {P = P} {l = []}    = consequence {P = P} id id base
axiom-base⋆ {P = P} {l = t ∷ l} = consequence {P = P `∘⟦ l ⟧ `∘⟦ t ⟧ₜ} {Q = P} id id (step axiom-base⋆)

-- equivalences
axiom⇒denot : ⟨ P ⟩ l ⟨ Q ⟩ → (P `⊢ Q `∘⟦ l ⟧)
axiom⇒denot base = id
axiom⇒denot (step PlQ) = axiom⇒denot PlQ
axiom⇒denot (consequence P⊢P′ Q′⊢Q PlQ) = Q′⊢Q ∘ axiom⇒denot PlQ ∘ P⊢P′

denot⇒axiom : (P `⊢ Q `∘⟦ l ⟧) → ⟨ P ⟩ l ⟨ Q ⟩
denot⇒axiom {P = P} {Q = Q} {l = []} H =
  strengthen {Q = P} {Q′ = Q} H base
denot⇒axiom {P = P} {Q = Q} {l = t ∷ l} H =
  weaken {P′ = P} {P = Q `∘⟦ t ∷ l ⟧} H (axiom-base⋆ {P = Q} {l = t ∷ l})

axiom⇔denot : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (P `⊢ Q `∘⟦ l ⟧)
axiom⇔denot = axiom⇒denot , denot⇒axiom

axiom⇒oper : ⟨ P ⟩ l ⟨ Q ⟩ → (∀ {s s′} → P ∙ s → l , s —→⋆′ s′ → Q ∙ s′)
axiom⇒oper = (λ{ P⊢ Ps s→s′ → subst _ (proj₂ denot⇔oper s→s′) (P⊢ Ps)}) ∘ axiom⇒denot

oper⇒axiom : (∀ {s s′} → P ∙ s → l , s —→⋆′ s′ → Q ∙ s′) → ⟨ P ⟩ l ⟨ Q ⟩
oper⇒axiom = λ H → denot⇒axiom λ Ps → H Ps oper-base⋆

axiom⇔oper : ⟨ P ⟩ l ⟨ Q ⟩ ⇔ (∀ {s s′} → P ∙ s → l , s —→⋆′ s′ → Q ∙ s′)
axiom⇔oper = axiom⇒oper , oper⇒axiom

-- equational reasoning

step′ :
    ⟨ P ⟩ l  ⟨ Q ⟩
  → ⟨ Q ⟩ l′ ⟨ R ⟩
    -------------------
  → ⟨ P ⟩ l ++ l′ ⟨ R ⟩
step′ {P} {[]} {Q} {l′} {R} PlQ QlR = weaken (axiom⇒denot PlQ) QlR
step′ {.(_ `∘⟦ t ⟧ₜ)} {t ∷ l} {Q} {l′} {R} (step PlQ) QlR = step (step′ PlQ QlR)
step′ {P} {t ∷ l} {Q} {l′} {R} (consequence {P = P′}{Q = Q′} pre post PlQ) QlR = weaken pre p
  where
    p : ⟨ P′ ⟩ t ∷ l ++ l′ ⟨ R ⟩
    p = step′ PlQ (weaken post QlR)

module HoareReasoning where

  infix  -2 begin_
  infixr -1 _~⟨_⟩_
  infixr -1 _~⟨_∶-_⟩_
  infixr -1 _~⟨_∶-_⟩′_
  infix  0  _∎

  begin_ : ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q ⟩
  begin p = p

  _~⟨_⟩_ : ∀ P′ → P′ `⊢ P  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ l ⟨ R ⟩
  _ ~⟨ H ⟩ PlR = weaken H PlR

  _~⟨_⟩′_ : ∀ R′ → R `⊢ R′  → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
  _ ~⟨ H ⟩′ PlR = strengthen H PlR

  _~⟨_∶-_⟩_ : ∀ P′ → (t : Tx) → ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  P′ ~⟨ t ∶- H ⟩ PlR = P′ ~⟨ (axiom⇒denot H) ⟩ step {t = t} PlR

  _~⟨_∶-_⟩′_ : ∀ P′ → (l : L) → ⟨ P′ ⟩ l ⟨ P ⟩ → ⟨ P ⟩ l′ ⟨ R ⟩ → ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩′ PlR = step′ H PlR

  _∎ : ∀ P → ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = base {P = p}

-- ** lemmas

-- commutativity
∗↔ : P `∗ Q `⊢ Q `∗ P
∗↔ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) = s₂ , s₁ , ∪≡-comm ≡s , Qs₂ , Ps₁

-- associativity
∗↝ : P `∗ Q `∗ R `⊢ (P `∗ Q) `∗ R
∗↝ {x = s} (s₁ , s₂₃ , ≡s , Ps₁ , (s₂ , s₃ , ≡s₂₃ , Qs₂ , Rs₃)) =
  let ≡s′ , s₁♯s₂ = ⊎≈-assocʳ ≡s ≡s₂₃
  in (s₁ ∪ s₂) , s₃ , ≡s′ , (s₁ , s₂ , (s₁♯s₂ , ≈-refl) , Ps₁ , Qs₂) , Rs₃

↜∗ : (P `∗ Q) `∗ R `⊢ P `∗ Q `∗ R
↜∗ {x = s} (s₁₂ , s₃ , ≡s , (s₁ , s₂ , ≡s₁₂ , Ps₁ , Qs₂) , Rs₃) =
  let ≡s′ , s₂♯s₃ = ⊎≈-assocˡ ≡s ≡s₁₂
  in s₁ , (s₂ ∪ s₃) , ≡s′ , Ps₁ , (s₂ , s₃ , (s₂♯s₃ , ≈-refl) , Qs₂ , Rs₃)

_↝_∶-_ : ∀ A B → A ≢ B → ⟨ A `↦ v `∗ B `↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A `↦ 0 `∗ B `↦ (v′ + v) ⟩
_↝_∶-_ {v}{v′} A B A≢B = denot⇒axiom d
  where
    tx = A —→⟨ v ⟩ B

    d : A `↦ v `∗ B `↦ v′ `⊢ A `↦ 0 `∗ B `↦ (v′ + v) `∘⟦ [ tx ] ⟧
    d {s} (s₁ , s₂ , ≡s , As₁ , Bs₂) = s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′
      where
        s₁′ s₂′ ⟦t⟧s : S
        s₁′ = singleton (A , 0)
        s₂′ = singleton (B , v′ + v)
        ⟦t⟧s = ⟦ tx ⟧ s

        As₁′ : (A `↦ 0) ∙ s₁′
        As₁′ = singleton-law

        Bs₂′ : (B `↦ (v′ + v)) ∙ s₂′
        Bs₂′ = singleton-law

        s₁♯s₂ : s₁′ ♯ s₂′
        s₁♯s₂ = singleton♯ A≢B

        s₁₂ = s₁ ∪ s₂

        ≈s″ : (s₁′ ∪ s₂′) ≈ ⟦ tx ⟧ (s₁ ∪ s₂)
        ≈s″ =
          begin
            s₁′ ∪ s₂′
          ≡⟨⟩
            singleton (A , 0) ∪ singleton (B , v′ + v)
          ≈⟨ ≈-sym (transfer A≢B) ⟩
            run [ A ∣ v ↦ B ] (singleton (A , v) ∪ singleton (B , v′))
          ≈⟨ ≈-cong-cmd [ A ∣ v ↦ B ] s₁∪s₂≡ ⟩
            run [ A ∣ v ↦ B ] (s₁ ∪ s₂)
          ≡⟨⟩
            ⟦ tx ⟧ (s₁ ∪ s₂)
          ∎
          where
            open ≈-Reasoning

            s₁∪s₂≡ : (singleton (A , v) ∪ singleton (B , v′)) ≈ (s₁ ∪ s₂)
            s₁∪s₂≡ = ≈-sym $
              begin
                s₁ ∪ s₂
              ≈⟨ ∪-cong (singleton≈ As₁) ⟩
                singleton (A , v) ∪ s₂
              ≈⟨ ∪-congʳ (♯-comm (♯-cong (≈-sym $ singleton≈ Bs₂) (singleton♯ (≢-sym A≢B)))) (singleton≈ Bs₂) ⟩
                singleton (A , v) ∪ singleton (B , v′)
              ∎

        ≈s′ : (s₁′ ∪ s₂′) ≈ ⟦t⟧s
        ≈s′ = ≈-trans ≈s″ $ ≈-cong-cmd [ A ∣ v ↦ B ] (proj₂ ≡s)

        ≡s′ : ⟨ s₁′ ⊎ s₂′ ⟩≡ ⟦t⟧s
        ≡s′ = s₁♯s₂ , ≈s′

_↜_∶-_ : ∀ A B → A ≢ B → ⟨ A `↦ v′ `∗ B `↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A `↦ (v′ + v) `∗ B `↦ 0 ⟩
_↜_∶-_ {v}{v′} A B A≢B = denot⇒axiom λ{ (s₁ , s₂ , ≡s , As₁ , Bs₂) →
  let (s₁′ , s₂′ , ≡s′ , As₁′ , Bs₂′) = axiom⇒denot (B ↝ A ∶- (A≢B ∘ sym)) (s₂ , s₁ , ∪≡-comm ≡s , Bs₂ , As₁)
  in (s₂′ , s₁′ , ∪≡-comm ≡s′ , Bs₂′ , As₁′) }
