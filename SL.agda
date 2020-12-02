----------------------
-- ** Separation logic

open import Prelude.Init hiding (_⇔_)
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.PartialMaps

module SL (Part : Set) {{_ : DecEq Part}} where

open import Ledger Part {{it}}
open import HoareLogic Part {{it}}

mod : Part → L → Set
mod A = Any λ t → A ∈ (sender t ∷ receiver t ∷ [])

addr : Part → Assertion → Set
addr A `emp     = ⊥
addr A (B `↦ _) = A ≡ B
addr A (P `∗ Q) = addr A P ⊎ addr A Q
addr A (P `∘ _) = addr A P

_ˡ♯_ : L → S → Set
l ˡ♯ s = ∀ A → mod A l → A ∉ᵈ s

_♯ˡ_ : S → L → Set
s ♯ˡ l = ∀ A → A ∈ᵈ s → ¬ mod A l

_♯♯_ : L → Assertion → Set
l ♯♯ P = ∀ A → mod A l → ¬ addr A P

_♯♯′_ : L → S → Set
l ♯♯′ s = ∀ A → mod A l → A ∉ᵈ s

-- Lemmas about separation
singleton′ : Part × ℕ → S
singleton′ (A , v) k with k ≟ A
... | yes _ = just v
... | no  _ = nothing

singleton≡ : ⟦ A `↦ v ⟧ᵖ $ singleton′ (A , v)
singleton≡ {A}{v} = p₁ , p₂
  where
    p₁ : singleton′ (A , v) [ A ↦ v ]
    p₁ with A ≟ A
    ... | yes refl = refl
    ... | no  A≢A  = ⊥-elim $ A≢A refl

    p₂ : ∀ A′ → A′ ≢ A → A′ ∉ᵈ singleton′ (A , v)
    p₂ A′ A′≢ with A′ ≟ A
    ... | yes refl = ⊥-elim $ A′≢ refl
    ... | no  _    = M.All.nothing

MAll⇒¬MAny : ∀ {A : Set} {m : Maybe A} → M.All.All (const ⊥) m → ¬ M.Any.Any (const ⊤) m
MAll⇒¬MAny {m = nothing} M.All.nothing = λ ()

∉¬ : A ∉ᵈ s → ¬ A ∈ᵈ s
∉¬ {A}{s} A∉ A∈ with s A | A∉ | A∈
... | just _  | M.All.just () | _

¬∉ : ¬ A ∈ᵈ s → A ∉ᵈ s
¬∉ {A}{s} ¬A∈ with s A
... | nothing = M.All.nothing
... | just _  = ⊥-elim $ ¬A∈ (M.Any.just tt)

∈ᵈ-∪ : s₁ ∪ s₂ ≡ s → A ∈ᵈ s → A ∈ᵈ s₁ ⊎ A ∈ᵈ s₂
∈ᵈ-∪ {s₁}{s₂}{s}{A} (s₁♯s₂ , p) A∈
  with s A | A∈ | s₁ A | s₂ A | inspect s₂ A | p A
... | nothing | () | _       | _       | _        | _
... | just _  | _  | just _  | _       | _        | _  = inj₁ $ M.Any.just tt
... | just _  | _  | _       | just _  | _        | _  = inj₂ $ M.Any.just tt
... | just v  | _  | nothing | nothing | ≡[ s₂≡ ] | pA = case subst (_≡ just v) s₂≡ pA of λ ()

∈⇒addr : A ∈ᵈ s → P ∙ s → addr A P
∈⇒addr {A}{s}{P = `emp} A∈ Ps = ⊥-elim $ ∉¬ {A}{s} (Ps A) A∈
∈⇒addr {A}{s}{P = B `↦ v} A∈ Ps with A ≟ B
... | yes A≡B = A≡B
... | no  A≢B = ⊥-elim $ ∉¬ {A}{s} (proj₂ Ps A A≢B) A∈
∈⇒addr {A}{s}{P = P `∗ Q} A∈ (s₁ , s₂ , ≡s , Ps₁ , Qs₂)
  with ∈ᵈ-∪ ≡s A∈
... | inj₁ A∈₁ = inj₁ $ ∈⇒addr {P = P} A∈₁ Ps₁
... | inj₂ A∈₂ = inj₂ $ ∈⇒addr {P = Q} A∈₂ Qs₂
∈⇒addr {A}{s}{P = P `∘ f} A∈ Ps = ∈⇒addr {P = P} (f .monotone s A A∈) Ps

♯♯-skip : (t ∷ l) ♯♯ P → l ♯♯ P
♯♯-skip p A = p A ∘ there

ˡ♯⇒♯ˡ : l ˡ♯ s → s ♯ˡ l
ˡ♯⇒♯ˡ {s = s} p A A∈s A∈l with s A | p A A∈l | A∈s
... | nothing | _             | ()
... | just _  | M.All.just () | _

∉-splits : s₁ ∪ s₂ ≡ s → A ∉ᵈ s₁ → A ∉ᵈ s₂ → A ∉ᵈ s
∉-splits {s₁ = s₁}{s₂}{s}{A} (s₁♯s₂ , p) A∉₁ A∉₂
  with s₁ A | s₂ A | inspect s₂ A | A∉₁ | A∉₂ | s A | p A
... | just _  | _       | _        | M.All.just () | _             | _       | _
... | _       | just _  | _        | _             | M.All.just () | _       | _
... | nothing | nothing | _        | _             | _             | nothing | _
    = M.All.nothing
... | nothing | nothing | ≡[ s₂≡ ] | _             | _             | just v  | pA
    = case subst (_≡ just v) s₂≡ pA of λ ()

♯♯⇒ˡ♯ : l ♯♯ R → R ∙ s → l ˡ♯ s
♯♯⇒ˡ♯ {l}{`emp}{s} l♯R s∅ A A∈ = s∅ A
♯♯⇒ˡ♯ {l}{B `↦ v}{s} l♯R B↦ A A∈
  with A ≟ B
... | yes refl = ⊥-elim $ l♯R A A∈ refl
... | no  A≢B  = proj₂ B↦ A A≢B
♯♯⇒ˡ♯ {l}{R `∗ Q}{s} l♯R (s₁ , s₂ , ≡s , Rs₁ , Qs₂) A A∈
  with s₁ A | inspect s₁ A | s₂ A | inspect s₂ A
... | just _  | ≡[ s₁≡ ] | _       | _
    = ⊥-elim $ l♯R A A∈ $ inj₁ $ ∈⇒addr {A}{s₁}{R} (subst M.Is-just (sym s₁≡) auto) Rs₁
... | _       | _        | just _  | ≡[ s₂≡ ]
    = ⊥-elim $ l♯R A A∈ $ inj₂ $ ∈⇒addr {A}{s₂}{Q} (subst M.Is-just (sym s₂≡) auto) Qs₂
... | nothing | ≡[ s₁≡ ] | nothing | ≡[ s₂≡ ]
    = ∉-splits ≡s (subst M.Is-nothing (sym s₁≡) auto) (subst M.Is-nothing (sym s₂≡) auto)

♯♯⇒ˡ♯ {l}{R `∘ f}{s} l♯R Rs A A∈ = ¬∉ {A}{s} ¬A∈
  where
    A∉ : A ∉ᵈ f .transform s
    A∉ = ♯♯⇒ˡ♯ {R = R} {s = f .transform s} l♯R Rs A A∈

    ¬A∈ : ¬ A ∈ᵈ s
    ¬A∈ = ∉¬ {A}{f .transform s} A∉ ∘ f .monotone s A

-- Helper lemmas for [FRAME]

transfer-helper :
    s₁ ♯ s₂
  → B ∉ᵈ s₂
    ---------------------
  → (s₁ [ A ∣ v ↦ B ]) ♯ s₂
transfer-helper {s₁ = s₁}{s₂}{B}{A}{v} s₁♯s₂ B∉ with s₁ A | inspect s₁ A
... | nothing | _  = s₁♯s₂
... | just vᵃ | ≡[ A∈ ] with v Nat.≤? vᵃ
... | no  _ = s₁♯s₂
... | yes _ = λ k → go k
  where
    go : transfer s₁ (A , vᵃ) v B ♯ s₂
    go k with k ≟ A
    ... | yes refl =
      let (p , p′) = s₁♯s₂ A
      in  (λ _ → p (subst (M.Any.Any (const ⊤)) (sym A∈) auto))
        , λ A∈′ → case (subst (M.All.All (const ⊥)) A∈ (p′ A∈′)) of λ{ (M.All.just ()) }
    ... | no _ with k ≟ B
    ... | yes refl =
      let (p , p′) = s₁♯s₂ B
      in  (λ _ → B∉) , ⊥-elim ∘ MAll⇒¬MAny B∉
    ... | no _ = s₁♯s₂ k

drop-[∣↦] : ∀ k → k ≢ A → k ≢ B → (s [ A ∣ v ↦ B ]) k ≡ s k
drop-[∣↦] {A = A}{B}{s}{v} k k≢A k≢B with s A
... | nothing = refl
... | just vᵃ with v Nat.≤? vᵃ
... | no _  = refl
... | yes _ with k ≟ A
... | yes eq = ⊥-elim $ k≢A eq
... | no  _ with k ≟ B
... | yes eq = ⊥-elim $ k≢B eq
... | no  _ = refl

frame-helper :
    l ♯♯ R
  → R ∙ s₂
  → s₁ ∪ s₂ ≡ s
    -----------------------
  → ⟦ l ⟧ s₁ ∪ s₂ ≡ ⟦ l ⟧ s
frame-helper {l = []} _ _ p = p
frame-helper {l = l₀@(A —→⟨ v ⟩ B ∷ l)}{R}{s₂}{s₁}{s} l♯R Rs₂ (s₁♯s₂ , ≡s) =
  frame-helper {l}{R}{s₂}{s₁ [ A ∣ v ↦ B ]} {s [ A ∣ v ↦ B ]} (♯♯-skip {P = R} l♯R) Rs₂ p′
  where
    l♯s₂ : l₀ ˡ♯ s₂
    l♯s₂ = ♯♯⇒ˡ♯ {R = R} l♯R Rs₂

    A∉ : A ∉ᵈ s₂
    A∉ = l♯s₂ A $ here (here refl)

    B∉ : B ∉ᵈ s₂
    B∉ = l♯s₂ B $ here (there (here refl))

    p₁ : (s₁ [ A ∣ v ↦ B ]) ♯ s₂
    p₁ = transfer-helper s₁♯s₂ B∉

    ∉⇒≢ : ∀ k → k ∈ᵈ s₂ → (k ≢ A) × (k ≢ B)
    ∉⇒≢ k k∈ = k≢A , k≢B
      where
        k∉ : ¬ mod k l₀
        k∉ = ˡ♯⇒♯ˡ l♯s₂ k k∈

        k≢A : k ≢ A
        k≢A refl = ⊥-elim $ k∉ (here (here refl))

        k≢B : k ≢ B
        k≢B refl = ⊥-elim $ k∉ (here (there (here refl)))

    p₂ : ∀ k → ((s₁ [ A ∣ v ↦ B ]) ∪ s₂ ∶- p₁) k ≡ (s [ A ∣ v ↦ B ]) k
    p₂ k
      with eq ← ≡s k
      with eqᵃ ← ≡s A
      with eqᵇ ← ≡s B
      with Dec (k ∈ᵈ s₂) ∋ dec
    ... | yes k∈
      with k≢A , k≢B ← ∉⇒≢ k k∈
      rewrite ∪-chooseᵣ p₁ k∈
            | ∪-chooseᵣ s₁♯s₂ k∈
            | drop-[∣↦] {s = s} {v = v} k k≢A k≢B
            = eq
    ... | no ¬k∈
      with k∉ ← ¬∉ {k}{s₂} ¬k∈
      rewrite ∪-chooseₗ p₁ k∉
            | ∪-chooseₗ s₁♯s₂ k∉
      with s₁ A | s₂ A | A∉ | inspect s₂ A | s A | eqᵃ
    ... | nothing | just _  | M.All.just () | _          | _          | _
    ... | nothing | nothing | _             | ≡[ s₂≡ ]   | just _     | eqᵃ′
        = case trans (sym s₂≡) eqᵃ′ of λ ()
    ... | nothing | nothing | _             | _          | nothing    | _
        = eq
    ... | just vᵃ | _       | _             | _          | .(just vᵃ) | refl
      with v ≤? vᵃ
    ... | no  _ = eq
    ... | yes _
      with k ≟ A
    ... | yes k≡A = refl
    ... | no  k≢A
      with k ≟ B
    ... | no  k≢b = eq
    ... | yes k≡B
      with s₁ B | s₂ B | B∉ | inspect s₂ B | s B | eqᵇ
    ... | nothing | just _  | M.All.just () | _          | _          | _
    ... | nothing | nothing | _             | ≡[ s₂≡ ]   | just _     | eqᵇ′
        = case trans (sym s₂≡) eqᵇ′ of λ ()
    ... | nothing | nothing | _             | _          | nothing    | _
        = refl
    ... | just vᵇ | _       | _             | _          | .(just vᵇ) | refl
        = refl

    p′ : (s₁ [ A ∣ v ↦ B ]) ∪ s₂ ≡ (s [ A ∣ v ↦ B ])
    p′ = p₁ , p₂

[FRAME] :
    ⟨ P ⟩ l ⟨ Q ⟩
  → l ♯♯ R
    -----------------------
  → ⟨ P `∗ R ⟩ l ⟨ Q `∗ R ⟩
[FRAME] {P}{l}{Q}{R} PlQ sep = proj₂ axiom⇔denot d
  where
    d : (P `∗ R) `⊢ (Q `∗ R) `∘ ⟦ l ⟧ₗ
    d {s} (s₁ , s₂ , s₁♯s₂ , Ps₁ , Rs₂) = ⟦ l ⟧ s₁ , s₂  , p , Qs₁′ , Rs₂
      where
        Qs₁′ : Q ∙ ⟦ l ⟧ s₁
        Qs₁′ = proj₁ axiom⇔denot PlQ Ps₁

        p : ⟦ l ⟧ s₁ ∪ s₂ ≡ ⟦ l ⟧ s
        p = frame-helper {R = R} sep Rs₂ s₁♯s₂

fr : ∀ R → l ♯♯ R → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P `∗ R ⟩ l ⟨ Q `∗ R ⟩
fr R l♯R PlQ = [FRAME] {R = R} PlQ l♯R

postulate
  _↝_ : ∀ A B → ⟨ A `↦ v `∗ B `↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A `↦ 0 `∗ B `↦ (v′ + v) ⟩
  _↜_ : ∀ A B → ⟨ A `↦ v′ `∗ B `↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A `↦ (v′ + v) `∗ B `↦ 0 ⟩
  ∗↝ : P `∗ Q `∗ R `⊢ (P `∗ Q) `∗ R
  ↜∗ : (P `∗ Q) `∗ R `⊢ P `∗ Q `∗ R
  ∗↔ : P `∗ Q `⊢ Q `∗ P

  ⊢⇒addr : P `⊢ P′ → addr A P′ → addr A P
{-
⊢⇒addr {`emp} {A `↦ v} P⊢P′ refl with () ← P⊢P′ {∅′} λ k → M.All.nothing
⊢⇒addr {A′ `↦ v′} {A `↦ v} P⊢P′ refl
  with A ≟ A′ | proj₁ (P⊢P′ {singleton′ (A′ , v′)} singleton≡)
... | no _     | ()
... | yes refl | _  = refl

⊢⇒addr {P `∗ P₁} {A `↦ v} P⊢P′ refl = {!!}
⊢⇒addr {P `∘ x} {A `↦ v} P⊢P′ refl = {!!}
  -- where
  --   h : P `⊢ A `↦ v → addr A P

⊢⇒addr {P}{P′ `∗ _} P⊢P′ (inj₁ A∈) = {!!}
  -- where
  --   h : P `⊢ P′ `∗ _ → addr A P

⊢⇒addr {P}{_ `∗ P′} P⊢P′ (inj₂ A∈) = {!!}
  -- where
  --   h : P `⊢ _ `∗ P′ → addr A P

⊢⇒addr {P}{P′ `∘ f} P⊢P′ A∈ = {!!}
  -- where
  --   h : P `⊢ P′ `∗ _ → addr A P
-}
