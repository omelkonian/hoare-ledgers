------------------------------------------
-- ** Denotational & operational semantics

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
-- open import Prelude.Maps
open import ValueSep.Maps
open import Prelude.Ord
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Functor
open import Prelude.InferenceRules
open import Prelude.Apartness
open import Prelude.Monad

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
  s s′ s″ s₁ s₁′ s₁″ s₂ s₂′ s₂″ s₃ s₃′ s₃″ s₂₃ s₂₃′ s₂₃″ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

  ms ms′ ms″ : Maybe S
  mls mls′ mls″ : Maybe (L × S)

-- ** Denotational semantics

-- The meaning of a transaction or a whole ledger will be denoted by state transformers,
-- i.e. a function from the current state to the updated one that may produce an error.
Domain = S → Maybe S

record Denotable (A : Set) : Set where
  field ⟦_⟧ : A → Domain
open Denotable ⦃...⦄ public

-- Express the action of tranferring values between keys in a map.
-- NB: a transaction goes through only when:
--   1. both participants are present in the domain
--   2. the sender holds sufficient funds
instance
  -- we denote a transaction as the map transformation that implements the transfer
  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ (A —→⟨ v ⟩ B) m =
    case (m A , m B) of λ where
      (just vᵃ , just vᵇ) →
        if v ≤ᵇ vᵃ then
          just $ m [ A ↝ (_∸ v) ] [ B ↝ (_+ v) ]
        else
          nothing
      (_ , _) → nothing

  -- we denote a ledger as the composition of the denotations of its transactions,
  -- i.e. we run all transactions in sequence
  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ []      s = just s
  ⟦L⟧ .⟦_⟧ (t ∷ l) = ⟦ t ⟧ >=> ⟦ l ⟧

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l ⟧ >=> ⟦ l′ ⟧) x
comp {l = []}    x = refl
comp {l = t ∷ l} x with ⟦ t ⟧ x
... | nothing = refl
... | just s  = comp {l} s

-- Executing transactions never introduces new keys in the resulting map out-of-thin-air.
⟦⟧ₜ-mono : KeyMonotonicᵐ ⟦ t ⟧
⟦⟧ₜ-mono {t = A —→⟨ v ⟩ B} m
  with m A | m B
... | just _  | nothing = M.All.nothing
... | nothing | _       = M.All.nothing
... | just vᵃ | just vᵇ
  with v ≤ᵇ vᵃ
... | false = M.All.nothing
... | true  = M.All.just λ k → [↝]-mono B (_+ v) (m [ A ↝ (_∸ v) ]) k ∘ [↝]-mono A (_∸ v) m k

⟦⟧ₗ-mono : KeyMonotonicᵐ ⟦ l ⟧
⟦⟧ₗ-mono {[]}    _ = M.All.just λ _ → id
⟦⟧ₗ-mono {t ∷ l} s
  with ⟦ t ⟧ s | ⟦⟧ₜ-mono {t = t} s
... | nothing | _ = M.All.nothing
... | just s′ | M.All.just IHₜ
  with ⟦ l ⟧ s′ | ⟦⟧ₗ-mono {l = l} s′
... | nothing | _ = M.All.nothing
... | just s′ | M.All.just IHₗ = M.All.just (IHₗ _ ∘₂ IHₜ)

-- -- Executing a transaction never removes existing keys.
⟦⟧ₜ-pre : KeyPreservingᵐ ⟦ t ⟧
⟦⟧ₜ-pre {t = A —→⟨ v ⟩ B} m
  with m A in A≡ | m B in B≡
... | just _  | nothing = M.All.nothing
... | nothing | _       = M.All.nothing
... | just vᵃ | just vᵇ
  with v ≤ᵇ vᵃ
... | false = M.All.nothing
... | true  = M.All.just λ k k∈ → [↝]-pre A (_∸ v) m _ ([↝]-pre B (_+ v) (m [ A ↝ (_∸ v) ]) k k∈)

⟦⟧ₗ-pre : KeyPreservingᵐ ⟦ l ⟧
⟦⟧ₗ-pre {[]} _ = M.All.just λ _ → id
⟦⟧ₗ-pre {t ∷ l} s
  with ⟦ t ⟧ s | ⟦⟧ₜ-pre {t = t} s
... | nothing | _ = M.All.nothing
... | just s′ | M.All.just IHₜ
  with ⟦ l ⟧ s′ | ⟦⟧ₗ-pre {l = l} s′
... | nothing | _ = M.All.nothing
... | just s′ | M.All.just IHₗ = M.All.just (IHₜ _ ∘₂ IHₗ)

-- ** Utility lemmas about membership/transfer/maps.
∉-⟦⟧ₜ : A ∉ᵈ s → M.All.All (A ∉ᵈ_) (⟦ t ⟧ s)
∉-⟦⟧ₜ {A}{s}{t} A∉ with ⟦ t ⟧ s | ⟦⟧ₜ-pre {t = t} s
... | nothing | _ = M.All.nothing
... | just s′ | M.All.just IHₜ = M.All.just (A∉ ∘ IHₜ _)

∉-⟦⟧ₗ : A ∉ᵈ s → M.All.All (A ∉ᵈ_) (⟦ l ⟧ s)
∉-⟦⟧ₗ {A}{s}{[]} A∉ = M.All.just A∉
∉-⟦⟧ₗ {A}{s}{t ∷ l} A∉ with ⟦ t ⟧ s | ∉-⟦⟧ₜ {A}{s}{t} A∉
... | nothing | _ = M.All.nothing
... | just s′ | M.All.just IHₜ = ∉-⟦⟧ₗ {A} {s′} {l} IHₜ

-- ** Operational semantics
-- We model configurations of the transition system as pairs of a ledger and its current state.

infix 0 _—→_ _—→∅ _—→⋆_ _—→⋆∅ _—→⋆_✓

data _—→_ : L × S → Maybe (L × S) → Set where

  singleStep :

     ─────────────────────────
     t ∷ l , s —→ l ,_ <$> ⟦ t ⟧ s

-- data _—→⋆_ : Rel₀ (L × S) where

--    base :

--      ──────────────
--      ls —→⋆ ls

--    step :

--      ∙ ls  —→ just ls′
--      ∙ ls′ —→⋆ ls″
--        ───────────
--        ls —→⋆ ls″

-- comp′ :
--   ∙ l       , s  —→⋆′ s′
--   ∙ l′      , s′ —→⋆′ s″
--     ────────────────────
--     l ++ l′ , s  —→⋆′ s″
-- comp′ {l = []}    base                   s′→s″ = s′→s″
-- comp′ {l = t ∷ l}{s} (step x s→) s′→
--   with ⟦ t ⟧ s | singleStep {t}{l}{s}
-- ... | nothing | H = step {!singleStep!} s′→
-- ... | just s′ | H
--   = {!!}
-- (step singleStep s→s′) s′→s″ = step singleStep (comp′ s→s′ s′→s″)

data _—→⋆_ : L × S → Maybe (L × S) → Set where

  base :
    ──────────────
    ls —→⋆ just ls

  step-✓ :
    ∙ ls  —→  just ls′
    ∙ ls′ —→⋆ mls″
      ───────────
      ls  —→⋆ mls″

  step-∅ :
    ∙ ls  —→  nothing
      ───────────────
      ls  —→⋆ nothing

_—→∅ _—→⋆∅ : L × S → Set
ls —→∅  = ls —→  nothing
ls —→⋆∅ = ls —→⋆ nothing

_—→⋆_✓ : L × S → S → Set
ls —→⋆ s ✓ = ls —→⋆ just ([] , s)

-- comp′ :
--   ∙ l       , s  —→⋆ s′ ✓
--   ∙ l′      , s′ —→⋆ s″ ✓
--     ─────────────────────
--     l ++ l′ , s  —→⋆ s″ ✓
-- comp′ {.[]}      base         p = p
-- comp′ {t ∷ l}{s} (step-✓ p q) r
--   with ⟦ t ⟧ s | p
-- ... | nothing | absurd = {!!}
-- ... | just s′ | _ = {!!}
-- step-✓ {!comp′ s→s′ s′→s″!} {!s′→✓!}

-- comp′ {l = []}    base                   s′→s″ = s′→s″
-- comp′ {l = _ ∷ _} (step (singleStep s≡) s→s′) s′→s″ = step (singleStep s≡) (comp′ s→s′ s′→s″)

-- data _—→_ : Rel₀ (L × S) where

--   singleStep :

--      ⟦ t ⟧ s ≡ just s′
--      ─────────────────────────
--      t ∷ l , s —→ l , s′

-- data _—→⋆_ : Rel₀ (L × S) where

--    base :

--      ─────────
--      ls —→⋆ ls

--    step :

--      ∙ ls —→ ls′
--      ∙ ls′ —→⋆ ls″
--        ───────────
--        ls —→⋆ ls″

-- _—→⋆_✓ : L × S → S → Set
-- ls —→⋆ s ✓ = ls —→⋆ ([] , s)

-- comp′ :
--   ∙ l       , s  —→⋆′ s′
--   ∙ l′      , s′ —→⋆′ s″
--     ────────────────────
--     l ++ l′ , s  —→⋆′ s″
-- comp′ {l = []}    base                   s′→s″ = s′→s″
-- comp′ {l = _ ∷ _} (step (singleStep s≡) s→s′) s′→s″ = step (singleStep s≡) (comp′ s→s′ s′→s″)

oper-base⋆ :
  ⟦ l ⟧ s ≡ just s′
  ────────────────────
  l , s —→⋆ s′ ✓
oper-base⋆ {l = []} refl = base
oper-base⋆ {l = t ∷ l}{s} l≡ with ⟦ t ⟧ s | singleStep {t}{l}{s}
... | just s′ | H = step-✓ H (oper-base⋆ l≡)

-- ** Relating denotational and operational semantics.
-- denot⇒oper : (⟦ l ⟧ s ≡ ms′) → (l , s —→⋆ ms′ ✓)
-- denot⇒oper = oper-base⋆

-- oper⇒denot : (l , s —→⋆′ s′) → (⟦ l ⟧ s ≡ just s′)
-- oper⇒denot {l = .[]} base  = refl
-- oper⇒denot {l = _ ∷ _} (step (singleStep s≡) p) rewrite s≡ | oper⇒denot p = refl

-- denot⇔oper : (⟦ l ⟧ s ≡ just s′) ⇔ (l , s —→⋆′ s′)
-- denot⇔oper = denot⇒oper , oper⇒denot
