------------------------------------------
-- ** Denotational & operational semantics

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Maps

module Ledger
  (Part : Set) -- a fixed set of participants
  ⦃ _ : DecEq Part ⦄
  where

variable
  A B C D : Part
  v v′ v″ : ℕ

-- The state of a ledger is a collection of participants, along with their balance.
S : Set
S = Map⟨ Part ↦ ℕ ⟩

-- A transaction is transferring money from one participant to another.
record Tx : Set where
  constructor _—→⟨_⟩_
  field
    sender   : Part
    value    : ℕ
    receiver : Part
open Tx public

-- A ledger is a list of transactions.
L = List Tx

variable
  s s′ s″ s₁ s₂ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

-- ** Denotational semantics

-- The meaning of a transaction or a whole ledger will be denoted by state transformers,
-- i.e. function from the current state to the updated one.
Domain = S → S

record Denotable (A : Set) : Set where
  field
    ⟦_⟧ : A → Domain
open Denotable ⦃...⦄ public

-- Express the action of tranferring values between keys in a map.
-- NB: a transaction goes through only when:
--   1. both participants are present in the domain
--   2. the sender holds sufficient funds
--
-- Since Prelude.Maps exposes only an *abstract* interface, it would quickly get tedious to write
-- Hence we utilize a simple command language from Prelude.Maps that:
--   * lets us write our operation concisely
--   * re-use existing lemmas from the prelude library
--   * T0D0: investigate connection with algebraic-effects/effect-handlers??
--           e.g. ——⟨ alg.effects  ⟩—→ Denotational Semantics
--                ——⟨ eff.handlers ⟩—→ Practical effectful FP
--                ——⟨     ???      ⟩—→ Ergonomic dependently-typed FP / theorem-proving
[_∣_↦_] : Part → ℕ → Part → Cmd
[ A ∣ v ↦ B ] =
  just? A λ vᵃ →
  just? B λ vᵇ →
  iff (v ≤? vᵃ)
  ((A ≔ vᵃ ∸ v) ∶ (B ≔ vᵇ + v))


instance
  -- we denote a transaction as simply running the transaction based on the transfer operation above
  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ (A —→⟨ v ⟩ B) = run [ A ∣ v ↦ B ]

  -- we denote a ledger as the composition of the denotations of its transactions,
  -- i.e. we run all transactions in sequence
  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      s = s
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ l ⟧ ∘ ⟦ t ⟧

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l′ ⟧ ∘ ⟦ l ⟧) x
comp {l = []}    {l′} x = refl
comp {l = t ∷ l} {l′} x rewrite comp {l}{l′} (⟦ t ⟧ x) = refl

-- Executing transactions never introduces new keys in the resulting map out-of-thin-air.
⟦⟧ₗ-mono : KeyMonotonic ⟦ l ⟧
⟦⟧ₗ-mono {[]} _ _ = id
⟦⟧ₗ-mono {t ∷ l} s p = ⟦⟧ₗ-mono {l} (⟦ t ⟧ s) p ∘ cmd-mon [ sender t ∣ value t ↦ receiver t ] s p

-- Executing a transaction never removes existing keys.
[∣↦]-pre : KeyPreserving ⟦ t ⟧
[∣↦]-pre {t = A —→⟨ v ⟩ B} s k k∈
  with s ⁉ A | ⁉⇒∈ᵈ {s = s} {k = A}
... | nothing | _ = k∈
... | just vᵃ | A∈
  with s ⁉ B | ⁉⇒∈ᵈ {s = s} {k = B}
... | nothing | _ = k∈
... | just vᵇ | B∈
  with v ≤? vᵃ
... | no  _ = k∈
... | yes _
  with ∈ᵈ-∪⁻ _ _ _ k∈
... | inj₁ k∈ˡ rewrite singleton∈ k∈ˡ = B∈ auto
... | inj₂ k∈ʳ
  with ∈ᵈ-∪⁻ _ _ _ k∈ʳ
... | inj₁ k∈ˡ rewrite singleton∈ k∈ˡ = A∈ auto
... | inj₂ k∈ʳ′ = k∈ʳ′

-- ** Utility lemmas about membership/transfer/maps.
∉-⟦⟧ₜ : A ∉ᵈ s → A ∉ᵈ ⟦ t ⟧ s
∉-⟦⟧ₜ A∉s = ⊥-elim ∘ A∉s ∘ [∣↦]-pre _ _

∉-⟦⟧ₗ : A ∉ᵈ s → A ∉ᵈ ⟦ l ⟧ s
∉-⟦⟧ₗ {A}{s}{[]} A∉ = A∉
∉-⟦⟧ₗ {A}{s}{t ∷ l} A∉ = ∉-⟦⟧ₗ {l = l} (∉-⟦⟧ₜ {s = s}{t = t} A∉)

∉-splits : ⟨ s₁ ⊎ s₂ ⟩≡ s → A ∉ᵈ s₁ → A ∉ᵈ s₂ → A ∉ᵈ s
∉-splits {s₁ = s₁}{s₂}{s}{A} (s₁♯s₂ , p) A∉₁ A∉₂ A∈
  with ∈ᵈ-∪⁻ _ _ _ (∈ᵈ-cong (≈-sym p) A∈)
... | inj₁ A∈₁ = ⊥-elim $ A∉₁ A∈₁
... | inj₂ A∈₂ = ⊥-elim $ A∉₂ A∈₂

-- ** Lemmas about the transfer operation on maps.
transfer-helper : s₁ ♯ s₂ → B ∉ᵈ s₂ → (run [ A ∣ v ↦ B ] s₁) ♯ s₂
transfer-helper {s₁ = s₁}{s₂}{B}{A}{v} s₁♯s₂ B∉ = ♯-cong-pre [∣↦]-pre s₁♯s₂

drop-[∣↦] : ∀ k → k ≢ A → k ≢ B → (run [ A ∣ v ↦ B ] s) ⁉ k ≡ s ⁉ k
drop-[∣↦] {A}{B}{v}{s} k k≢A k≢B
  with s ⁉ A | inspect (s ⁉_) A
... | nothing | _ = refl
... | just vᵃ | ≡[ sᵃ ]
  with s ⁉ B | inspect (s ⁉_) B
... | nothing | _ = refl
... | just vᵇ | ≡[ sᵇ ]
  with v ≤? vᵃ
... | no _ = refl
... | yes _
  with k ≟ A
... | yes eq = ⊥-elim $ k≢A eq
... | no  _ with k ≟ B
... | yes eq = ⊥-elim $ k≢B eq
... | no  _  = trans (singleton-reject k≢B) (singleton-reject k≢A)

-- Transferring a value to/from distinct participants in the minimal map.
-- (utilizes general lemmas about the 3 available commands: `just?`/`iff`/`_≔_`)
transfer : ∀ {A B v v′}
  → A ≢ B
  → run [ A ∣ v ↦ B ] (singleton (A , v) ∪ singleton (B , v′))
  ≈ (singleton (A , 0) ∪ singleton (B , v′ + v))
transfer {A}{B}{v}{v′} A≢B =
  let
    m = singleton (A , v) ∪ singleton (B , v′)
  in
  begin
    run [ A ∣ v ↦ B ] m
  ≡⟨⟩
    run (just? A λ vᵃ → just? B λ vᵇ → iff (v ≤? vᵃ) ((A ≔ vᵃ ∸ v) ∶ (B ≔ vᵇ + v))) m
  ≈⟨ just?-accept (↦-∪⁺ˡ singleton-law′) ⟩
    run (just? B λ vᵇ → iff (v ≤? v) ((A ≔ v ∸ v) ∶ (B ≔ vᵇ + v))) m
  ≈⟨ just?-accept (↦-∪⁺ʳ′ (⊥-elim ∘ A≢B ∘ sym ∘ singleton∈) singleton-law′) ⟩
    run (iff (v ≤? v) ((A ≔ v ∸ v) ∶ (B ≔ v′ + v))) m
  ≈⟨ iff-accept {b = v ≤? v} (fromWitness Nat.≤-refl) ⟩
    run ((A ≔ v ∸ v) ∶ (B ≔ v′ + v)) m
  ≈⟨ ≈-cong-cmd (B ≔ v′ + v) update-update ⟩
    run (B ≔ (v′ + v)) (singleton (A , v ∸ v) ∪ singleton (B , v′))
  ≈⟨ ≈-cong-cmd (B ≔ v′ + v) (∪-comm $ singleton♯ A≢B) ⟩
    run (B ≔ (v′ + v)) (singleton (B , v′) ∪ singleton (A , v ∸ v))
  ≈⟨ update-update ⟩
    singleton (B , v′ + v) ∪ singleton (A , v ∸ v)
  ≈⟨ ∪-comm $ singleton♯ (≢-sym A≢B) ⟩
    singleton (A , v ∸ v) ∪ singleton (B , v′ + v)
  ≡⟨ cong (λ x → (singleton (A , x) ∪ singleton (B , v′ + v))) (Nat.n∸n≡0 v) ⟩
    singleton (A , 0) ∪ singleton (B , v′ + v)
  ∎ where
    open ≈-Reasoning

-- ** Operational semantics
-- We model configurations of the transition system as pairs of a ledger and its current state.

infix 0 _—→_ _—→⋆_ _—→⋆′_

data _—→_ : L × S → L × S → Set where
  singleStep :
     ------------------------
     t ∷ l , s —→ l , ⟦ t ⟧ s

data _—→⋆_ : L × S → L × S → Set where
   base :
       ---------
       ls —→⋆ ls

   step :
       ls —→ ls′
     → ls′ —→⋆ ls″
       ----------
     → ls —→⋆ ls″

_—→⋆′_ : L × S → S → Set
ls —→⋆′ s = ls —→⋆ ([] , s)

comp′ :
    l       , s  —→⋆′ s′
  → l′      , s′ —→⋆′ s″
  → l ++ l′ , s  —→⋆′ s″
comp′ {l = []}    base                   s′→s″ = s′→s″
comp′ {l = _ ∷ _} (step singleStep s→s′) s′→s″ = step singleStep (comp′ s→s′ s′→s″)

oper-base⋆ : l , s —→⋆′ ⟦ l ⟧ s
oper-base⋆ {l = []}    = base
oper-base⋆ {l = _ ∷ _} = step singleStep oper-base⋆

-- ** Relating denotational and operational semantics.
denot⇒oper : (⟦ l ⟧ s ≡ s′) → (l , s —→⋆′ s′)
denot⇒oper {l = []}    refl = base
denot⇒oper {l = _ ∷ _} refl = step singleStep (denot⇒oper refl)

oper⇒denot : (l , s —→⋆′ s′) → (⟦ l ⟧ s ≡ s′)
oper⇒denot {l = .[]}   base                = refl
oper⇒denot {l = _ ∷ _} (step singleStep p) = oper⇒denot p

denot⇔oper : (⟦ l ⟧ s ≡ s′) ⇔ (l , s —→⋆′ s′)
denot⇔oper = denot⇒oper , oper⇒denot
