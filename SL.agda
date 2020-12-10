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
addr A (P `∘⟦ _ ⟧) = addr A P

_ˡ♯_ : L → S → Set
l ˡ♯ s = ∀ A → mod A l → A ∉ᵈ s

_♯ˡ_ : S → L → Set
s ♯ˡ l = ∀ A → A ∈ᵈ s → ¬ mod A l

_♯♯_ : L → Assertion → Set
l ♯♯ P = ∀ A → mod A l → ¬ addr A P

_♯♯′_ : L → S → Set
l ♯♯′ s = ∀ A → mod A l → A ∉ᵈ s

-- Lemmas about separation
MAll⇒¬MAny : ∀ {A : Set} {m : Maybe A} → M.All.All (const ⊥) m → ¬ M.Any.Any (const ⊤) m
MAll⇒¬MAny {m = nothing} M.All.nothing ()

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

∉ᵈ-∪ : s₁ ∪ s₂ ≡ s → A ∉ᵈ s → A ∉ᵈ s₁ × A ∉ᵈ s₂
∉ᵈ-∪ {s₁}{s₂}{s}{A} (s₁♯s₂ , p) A∉
  with s A | A∉ | s₁ A | s₂ A | inspect s₂ A | p A
... | just _  | M.All.just () | _       | _       | _        | _
... | nothing | _             | nothing | just _  | ≡[ s₂≡ ] | pA = case subst (_≡ nothing) s₂≡ pA of λ ()
... | nothing | _             | nothing | nothing | _        | _  = M.All.nothing , M.All.nothing

∈⇒addr : A ∈ᵈ s → P ∙ s → addr A P
∈⇒addr {A}{s}{P = `emp} A∈ Ps = ⊥-elim $ ∉¬ {A}{s} (Ps A) A∈
∈⇒addr {A}{s}{P = B `↦ v} A∈ Ps with A ≟ B
... | yes A≡B = A≡B
... | no  A≢B = ⊥-elim $ ∉¬ {A}{s} (proj₂ Ps A A≢B) A∈
∈⇒addr {A}{s}{P = P `∗ Q} A∈ (s₁ , s₂ , ≡s , Ps₁ , Qs₂)
  with ∈ᵈ-∪ ≡s A∈
... | inj₁ A∈₁ = inj₁ $ ∈⇒addr {P = P} A∈₁ Ps₁
... | inj₂ A∈₂ = inj₂ $ ∈⇒addr {P = Q} A∈₂ Qs₂
∈⇒addr {A}{s}{P = P `∘⟦ l ⟧} A∈ Ps = ∈⇒addr {P = P} (⟦⟧ₗ-mono {l} s A A∈) Ps

∉-⟦⟧ₜ : A ∉ᵈ s → A ∉ᵈ ⟦ t ⟧ s
∉-⟦⟧ₜ {A}{s}{B —→⟨ v ⟩ C} A∉ with s B | inspect s B | s C | inspect s C
... | nothing | _        | _       | _        = A∉
... | just _  | _        | nothing | _        = A∉
... | just vᵇ | ≡[ sB≡ ] | just vᶜ | ≡[ sC≡ ] with v ≤? vᵇ
... | no _ = A∉
... | yes _ with A ≟ B
... | yes refl = case subst Is-nothing sB≡ A∉ of λ{ (M.All.just ()) }
... | no A≢B with A ≟ C
... | yes refl = case subst Is-nothing sC≡ A∉ of λ{ (M.All.just ()) }
... | no A≢C = A∉

∉-⟦⟧ₗ : A ∉ᵈ s → A ∉ᵈ ⟦ l ⟧ s
∉-⟦⟧ₗ {A}{s}{[]} A∉ = A∉
∉-⟦⟧ₗ {A}{s}{t ∷ l} A∉ = ∉-⟦⟧ₗ {l = l} (∉-⟦⟧ₜ {s = s}{t = t} A∉)

∉⇒¬addr : A ∉ᵈ s → P ∙ s → ¬ addr A P
∉⇒¬addr {A}{s}{P = `emp} A∉ Ps = λ ()
∉⇒¬addr {A}{s}{P = .A `↦ _} A∉ Ps refl with s A | A∉ | Ps
... | just v  | M.All.just () | _
... | nothing | _ | () , _
∉⇒¬addr {A}{s}{P = P `∗ Q} A∉ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) A∈
  with A∉ˡ , A∉ʳ ← ∉ᵈ-∪ ≡s A∉
  with A∈
... | inj₁ A∈ˡ = ∉⇒¬addr {P = P} A∉ˡ Ps₁ A∈ˡ
... | inj₂ A∈ʳ = ∉⇒¬addr {P = Q} A∉ʳ Qs₂ A∈ʳ
∉⇒¬addr {A}{s}{P = P `∘⟦ l ⟧} A∉ Ps A∈ = ∉⇒¬addr {P = P} (∉-⟦⟧ₗ {l = l} A∉) Ps A∈

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

♯♯⇒ˡ♯ {_}{R `∘⟦ l ⟧}{s} l♯R Rs A A∈ = ¬∉ {A}{s} ¬A∈
  where
    A∉ : A ∉ᵈ ⟦ l ⟧ s
    A∉ = ♯♯⇒ˡ♯ {R = R} {s = ⟦ l ⟧ s} l♯R Rs A A∈

    ¬A∈ : ¬ A ∈ᵈ s
    ¬A∈ = ∉¬ {A}{⟦ l ⟧ s} A∉ ∘ ⟦⟧ₗ-mono {l} s A

-- Helper lemmas for [FRAME]

transfer-helper :
    s₁ ♯ s₂
  → B ∉ᵈ s₂
    ---------------------
  → (s₁ [ A ∣ v ↦ B ]) ♯ s₂
transfer-helper {s₁ = s₁}{s₂}{B}{A}{v} s₁♯s₂ B∉
  with s₁ A | inspect s₁ A | s₁ B
... | nothing | _       | _ = s₁♯s₂
... | just _ | _       | nothing = s₁♯s₂
... | just vᵃ | ≡[ A∈ ] | just vᵇ
  with v Nat.≤? vᵃ
... | no  _ = s₁♯s₂
... | yes _ = λ k → go k
  where
    go : transfer s₁ (A , vᵃ) v (B , vᵇ) ♯ s₂
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
drop-[∣↦] {A = A}{B}{s}{v} k k≢A k≢B with s A | s B
... | nothing | _       = refl
... | just _  | nothing = refl
... | just vᵃ | just _  with v Nat.≤? vᵃ
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
      with s₁ B | s₂ B | B∉ | inspect s₂ B | s B | eqᵇ
    ... | nothing | just _  | M.All.just () | _          | _          | _
    ... | nothing | nothing | _             | ≡[ s₂≡ ]   | just _     | eqᵇ′
        = case trans (sym s₂≡) eqᵇ′ of λ ()
    ... | nothing | nothing | _             | _          | nothing    | _
        = eq
    ... | just vᵇ | _       | _             | _          | .(just vᵇ) | refl
      with v ≤? vᵃ
    ... | no  _ = eq
    ... | yes _
      with k ≟ A
    ... | yes k≡A = refl
    ... | no  k≢A
      with k ≟ B
    ... | no  k≢b = eq
    ... | yes k≡B = refl

    p′ : (s₁ [ A ∣ v ↦ B ]) ∪ s₂ ≡ (s [ A ∣ v ↦ B ])
    p′ = p₁ , p₂

[FRAME] : ∀ R
  → l ♯♯ R
  → ⟨ P ⟩ l ⟨ Q ⟩
    -----------------------
  → ⟨ P `∗ R ⟩ l ⟨ Q `∗ R ⟩
[FRAME] {l}{P}{Q} R l♯R PlQ = denot⇒axiom d
  where
    d : (P `∗ R) `⊢ (Q `∗ R) `∘⟦ l ⟧
    d {s} (s₁ , s₂ , s₁♯s₂ , Ps₁ , Rs₂) = ⟦ l ⟧ s₁ , s₂  , p , Qs₁′ , Rs₂
      where
        Qs₁′ : Q ∙ ⟦ l ⟧ s₁
        Qs₁′ = axiom⇒denot PlQ Ps₁

        p : ⟦ l ⟧ s₁ ∪ s₂ ≡ ⟦ l ⟧ s
        p = frame-helper {R = R} l♯R Rs₂ s₁♯s₂

postulate
  _↝_ : ∀ A B → ⟨ A `↦ v `∗ B `↦ v′ ⟩ [ A —→⟨ v ⟩ B ] ⟨ A `↦ 0 `∗ B `↦ (v′ + v) ⟩
  _↜_ : ∀ A B → ⟨ A `↦ v′ `∗ B `↦ v ⟩ [ B —→⟨ v ⟩ A ] ⟨ A `↦ (v′ + v) `∗ B `↦ 0 ⟩
  ∗↝ : P `∗ Q `∗ R `⊢ (P `∗ Q) `∗ R
  ↜∗ : (P `∗ Q) `∗ R `⊢ P `∗ Q `∗ R
  ∗↔ : P `∗ Q `⊢ Q `∗ P
