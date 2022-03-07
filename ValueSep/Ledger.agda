------------------------------------------
-- ** Denotational & operational semantics

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Maps
open import Prelude.Ord
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Functor
open import Prelude.InferenceRules
open import Prelude.Apartness

module ValueSep.Ledger
  (Part : Set) -- a fixed set of participants
  ⦃ _ : DecEq Part ⦄
  where

variable
  A B C D : Part
  v v′ v″ : ℕ

-- The state of a ledger is a collection of participants, along with their balance.
S : Set
S = Map⟨ Part ↦ ℕ ⟩

instance
  Sℕ  = Semigroup-ℕ-+
  Sℕ⁺ = SemigroupLaws-ℕ-+
  Mℕ  = Monoid-ℕ-+
  Mℕ⁺ = MonoidLaws-ℕ-+

-- A transaction is transferring money from one participant to another.
record Tx : Set where
  constructor _—→⟨_⟩_
  field
    sender   : Part
    value    : ℕ
    receiver : Part
open Tx public
unquoteDecl DecEq-Tx = DERIVE DecEq [ quote Tx , DecEq-Tx ]

-- A ledger is a list of transactions.
L = List Tx

variable
  s s′ s″ s₁ s₂ s₃ s₂₃ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

-- ** Denotational semantics

-- The meaning of a transaction or a whole ledger will be denoted by state transformers,
-- i.e. function from the current state to the updated one.
Domain = S → S

record Denotable (A : Set) : Set where
  field ⟦_⟧ : A → Domain
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
  just? B λ _ →
  iff¿ v ≤ vᵃ ¿
    ( [ (_+ v) ← B ]
    ∶ [ (_∸ v) ← A ]
    )

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
... | just _  | B∈
  with v ≤? vᵃ
... | no  _ = k∈
... | yes _ = modify-pre s k
            $ modify-pre (run [ (_+ v) ← B ] s) k k∈

-- ** Utility lemmas about membership/transfer/maps.
∉-⟦⟧ₜ : A ∉ᵈ s → A ∉ᵈ ⟦ t ⟧ s
∉-⟦⟧ₜ A∉s = ⊥-elim ∘ A∉s ∘ [∣↦]-pre _ _

∉-⟦⟧ₗ : A ∉ᵈ s → A ∉ᵈ ⟦ l ⟧ s
∉-⟦⟧ₗ {A}{s}{[]} A∉ = A∉
∉-⟦⟧ₗ {A}{s}{t ∷ l} A∉ = ∉-⟦⟧ₗ {l = l} (∉-⟦⟧ₜ {s = s}{t = t} A∉)

-- ** Lemmas about the transfer operation on maps.
transfer-helper : s₁ ♯ s₂ → B ∉ᵈ s₂ → (run [ A ∣ v ↦ B ] s₁) ♯ s₂
transfer-helper {s₁ = s₁}{s₂}{B}{A}{v} s₁♯s₂ B∉ = ♯-cong-pre [∣↦]-pre s₁♯s₂

transfer-id : (run [ A ∣ v ↦ A ] s) ≈ s
transfer-id {A}{v}{s} k
  with s ⁉ A in s≡
... | nothing = refl
... | just vᵃ
  rewrite s≡
  with v ≤? vᵃ
... | no  _ = refl
... | yes v≤ =
  begin
    (modify A (_∸ v) $ modify A (_+ v) s) ⁉ k
  ≡⟨ modify∘modify k ⟩
    modify A ((_∸ v) ∘ (_+ v)) s ⁉ k
  ≡⟨ modify-id (λ _ → Nat.m+n∸n≡m _ v) k ⟩
    s ⁉ k
  ∎ where open ≡-Reasoning

drop-[∣↦] : ∀ k → k ≢ A → k ≢ B → (run [ A ∣ v ↦ B ] s) ⁉ k ≡ s ⁉ k
drop-[∣↦] {A}{B}{v}{s} k k≢A k≢B
  with s ⁉ A in sᵃ
... | nothing = refl
... | just vᵃ
  with s ⁉ B in sᵇ
... | nothing = refl
... | just _
  with v ≤? vᵃ
... | no _ = refl
... | yes _
  rewrite modify-other {k = A}{k}{run [ (_+ v) ← B ] s}{_∸ v} (≢-sym k≢A)
        | modify-other {k = B}{k}{s}{_+ v} (≢-sym k≢B)
  = refl

-- Transferring a value to/from distinct participants in the minimal map.
-- (utilizes general lemmas about the 3 available commands: `just?`/`iff`/`_≔_`)
transfer◇ : ∀ {A B v v′}
    → run [ A ∣ v ↦ B ] (singleton (A , v) ◇ singleton (B , v′))
    ≈ (singleton (A , 0) ◇ singleton (B , v′ + v))
transfer◇ {A}{B}{v}{v′}
  with A ≟ B
... | yes refl
  =
  begin
    run [ A ∣ v ↦ A ] (singleton (A , v) ◇ singleton (A , v′))
  ≈⟨ transfer-id ⟩
    singleton (A , v) ◇ singleton (A , v′)
  ≈⟨ singleton◇ ⟩
    singleton (A , v + v′)
  ≡⟨ cong (λ ◆ → singleton (A , ◆)) (◇-comm v v′) ⟩
    singleton (A , 0 + v′ + v)
  ≈⟨ ≈-sym $ singleton◇ ⟩
    singleton (A , 0) ◇ singleton (A , v′ + v)
  ∎ where open ≈-Reasoning
... | no A≢B
  =
  let Aᵥ = singleton (A , v); Bᵥ = singleton (B , v′); m = Aᵥ ◇ Bᵥ
      A∉ : ∀ {vᵇ} → A ∉ᵈ singleton (B , vᵇ)
      A∉ = ⊥-elim ∘ A≢B ∘ singleton∈
      B∉ : ∀ {vᵃ} → B ∉ᵈ singleton (A , vᵃ)
      B∉ = ⊥-elim ∘ A≢B ∘ sym ∘ singleton∈
  in begin
    run [ A ∣ v ↦ B ] m
  ≡⟨⟩
    run (just? A λ vᵃ → just? B λ _ → iff¿ v ≤ vᵃ ¿ ([ (_+ v) ← B ] ∶ [ (_∸ v) ← A ])) m
  ≈⟨ just?-accept (trans (sym $ ↦-◇⁺ˡ A∉) singleton-law′) ⟩
    run (just? B λ _ → iff¿ v ≤ v ¿ ([ (_+ v) ← B ] ∶ [ (_∸ v) ← A ])) m
  ≈⟨ just?-accept (trans (sym $ ↦-◇⁺ʳ B∉) singleton-law′) ⟩
    run (iff¿ v ≤ v ¿ ([ (_+ v) ← B ] ∶ [ (_∸ v) ← A ])) m
  ≈⟨ iff-accept {b = v ≤? v} (fromWitness Nat.≤-refl) ⟩
    run ([ (_+ v) ← B ] ∶ [ (_∸ v) ← A ]) m
  ≡⟨⟩
    run ([ (_+ v) ← B ] ∶ [ (_∸ v) ← A ]) (Aᵥ ◇ Bᵥ)
  ≈⟨ ≈-cong-cmd ([ (_+ v) ← B ] ∶ [ (_∸ v) ← A ]) (◇-comm Aᵥ Bᵥ) ⟩
    run ([ (_+ v) ← B ] ∶ [ (_∸ v) ← A ]) (Bᵥ ◇ Aᵥ)
  ≡⟨⟩
    run [ (_∸ v) ← A ] (modify B (_+ v) (Bᵥ ◇ Aᵥ))
  ≈⟨ ≈-cong-cmd [ (_∸ v) ← A ] (modify-thisˡ B∉) ⟩
    run [ (_∸ v) ← A ] (singleton (B , v′ + v) ◇ Aᵥ)
  ≈⟨ ≈-cong-cmd [ (_∸ v) ← A ] $ ◇-comm (singleton (B , v′ + v)) Aᵥ ⟩
    run [ (_∸ v) ← A ] (Aᵥ ◇ singleton (B , v′ + v))
  ≈⟨ modify-thisˡ A∉ ⟩
    singleton (A , v ∸ v) ◇ singleton (B , v′ + v)
  ≡⟨ cong (λ ◆ → singleton (A , ◆) ◇ singleton (B , v′ + v)) (Nat.n∸n≡0 v) ⟩
    singleton (A , 0) ◇ singleton (B , v′ + v)
  ∎ where open ≈-Reasoning

-- ** Operational semantics
-- We model configurations of the transition system as pairs of a ledger and its current state.

infix 0 _—→_ _—→⋆_ _—→⋆′_

data _—→_ : L × S → L × S → Set where

  singleStep :

     ─────────────────────────
     t ∷ l , s —→ l , ⟦ t ⟧ s

data _—→⋆_ : L × S → L × S → Set where

   base :

     ─────────
     ls —→⋆ ls

   step :

     ∙ ls —→ ls′
     ∙ ls′ —→⋆ ls″
       ───────────
       ls —→⋆ ls″

_—→⋆′_ : L × S → S → Set
ls —→⋆′ s = ls —→⋆ ([] , s)

comp′ :
  ∙ l       , s  —→⋆′ s′
  ∙ l′      , s′ —→⋆′ s″
    ────────────────────
    l ++ l′ , s  —→⋆′ s″
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
