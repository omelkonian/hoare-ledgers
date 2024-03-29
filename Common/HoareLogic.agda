open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Monad
open import Prelude.Semigroup

open import Common.Denotational

module Common.HoareLogic
  {S   : Type}           -- type of states
  {Cmd : Type}           -- type of commands
  ⦃ _  : Denoteₑ Cmd S ⦄ -- denotational semantics of commands with explicit errors
  where

-- ** Shallow embedding of logic formulas/propositions.
Assertion = Pred₀ S

variable P P′ P₁ P₂ Q Q′ Q₁ Q₂ R : Assertion

-- ** Hoare triples.
weak↑ strong↑ : Pred₀ S → Pred₀ (Maybe S)
weak↑   = M.All.All
strong↑ = M.Any.Any

infixl 4 _↑∘_
_↑∘_ : Pred₀ S → (S → Maybe S) → Pred₀ S
P ↑∘ f = strong↑ P ∘ f

lift↑ = strong↑
pattern ret↑ x = M.Any.just x

map↑ : P ⊆¹ Q → lift↑ P ⊆¹ lift↑ Q
map↑ = M.Any.map

-- A program is a sequence of atomic commands.
Program = List Cmd

⟨_⟩_⟨_⟩ : Assertion → Program → Assertion → Type
⟨ P ⟩ l ⟨ Q ⟩ = P ⊢ Q ↑∘ ⟦ l ⟧

⟨_⟩_⟨_⟩＠_ : Assertion → Program → Assertion → S → Type
⟨ P ⟩ l ⟨ Q ⟩＠ s = P s → (Q ↑∘ ⟦ l ⟧) s

hoare-base :
  ──────────────
  ⟨ P ⟩ [] ⟨ P ⟩
hoare-base = ret↑

module _ (f : S → Maybe S) where
  lift∘>>= : ∀ {ms}
    → lift↑ (lift↑ P ∘ f) ms
    → lift↑ P (ms >>= f)
  lift∘>>= (ret↑ p) = p

  lift∘>>=˘ : ∀ {ms : Maybe S}
    → lift↑ P (ms >>= f)
    → lift↑ (lift↑ P ∘ f) ms
  lift∘>>=˘ {ms = just s} p = ret↑ p

  lift∘=<<  = lift∘>>=
  lift∘=<<˘ = lift∘>>=˘

module _ (f g : S → Maybe S) where
  lift²∘>=> : (P ↑∘ g ↑∘ f) ⊢ (P ↑∘ (f >=> g))
  lift²∘>=> = lift∘=<< _

  lift²∘>=>˘ : (P ↑∘ (f >=> g)) ⊢ (P ↑∘ g ↑∘ f)
  lift²∘>=>˘ = lift∘=<<˘ _

private variable
  x : Cmd
  l l′ : Program

hoare-step :
  ⟨ P ⟩ l ⟨ Q ⟩
  ──────────────────────────
  ⟨ P ↑∘ ⟦ x ⟧ ⟩ x ∷ l ⟨ Q ⟩
hoare-step {x = x} PlQ = lift²∘>=> ⟦ x ⟧ _ ∘ map↑ PlQ

consequence :
  ∙ P′ ⊢ P   -- ^ weakening the pre-condition
  ∙ Q  ⊢ Q′  -- ^ strengthening the post-condition
  ∙ ⟨ P  ⟩ l ⟨ Q  ⟩
    ───────────────
    ⟨ P′ ⟩ l ⟨ Q′ ⟩
consequence ⊢P Q⊢ PlQ = map↑ Q⊢ ∘ PlQ ∘ ⊢P

-- Utilities for Hoare triples.
weaken : P′ ⊢ P → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P′ ⟩ l ⟨ Q ⟩
weaken {l = l} H = consequence {l = l} H id

strengthen : Q ⊢ Q′ → ⟨ P ⟩ l ⟨ Q ⟩ → ⟨ P ⟩ l ⟨ Q′ ⟩
strengthen {l = l} H = consequence {l = l} id H

axiom-base⋆ : ⟨ P ↑∘ ⟦ l ⟧ ⟩ l ⟨ P ⟩
axiom-base⋆ {l = []}    =
  weaken {P′ = _ ↑∘ return} {l = []} (λ where (ret↑ p) → p) hoare-base
axiom-base⋆ {l = _ ∷ _} = map↑ id

-- Derived alternative formulation for step, using list concatenation.

hoare-step′ :
  ∙ ⟨ P ⟩ l  ⟨ Q ⟩
  ∙ ⟨ Q ⟩ l′ ⟨ R ⟩
    ──────────────────
    ⟨ P ⟩ l ◇ l′ ⟨ R ⟩
hoare-step′ {P}{l}{Q}{l′}{R} PlQ QlR =
  begin
    P
  ⊢⟨ PlQ  ⟩
    Q ↑∘ ⟦ l ⟧
  ⊢⟨ map↑ QlR ⟩
    R ↑∘ ⟦ l′ ⟧ ↑∘ ⟦ l ⟧
  ⊢⟨ lift²∘>=> ⟦ l ⟧ ⟦ l′ ⟧  ⟩
    R ↑∘ (⟦ l ⟧ >=> ⟦ l′ ⟧)
  ≗˘⟨ cong (lift↑ R) ∘ comp {l = l}{l′} ⟩
    R ↑∘ ⟦ l ◇ l′ ⟧
  ∎ where open ⊢-Reasoning

-- ** Reasoning syntax for Hoare triples.
module HoareReasoning where
  -- Reasoning newtype (for better type inference).
  record ℝ⟨_⟩_⟨_⟩ (P : Assertion) (l : Program) (Q : Assertion) : Type where
    constructor mkℝ_
    field begin_ : ⟨ P ⟩ l ⟨ Q ⟩
    infix -2 begin_
  open ℝ⟨_⟩_⟨_⟩ public
  infix  -2 mkℝ_
  infixr -1 _~⟪_⟩_ _~⟨_⟫_ _~⟨_∶-_⟩_ _~⟨_∶-_⟩++_
  infix  0  _∎

  -- weakening syntax
  _~⟪_⟩_ : ∀ P′ → P′ ⊢ P → ℝ⟨ P ⟩ l ⟨ R ⟩ → ℝ⟨ P′ ⟩ l ⟨ R ⟩
  _~⟪_⟩_ {l = l} _ H PlR = mkℝ weaken {l = l} H (begin PlR)

  -- strengthening syntax
  _~⟨_⟫_ : ∀ R′ → R ⊢ R′ → ⟨ P ⟩ l ⟨ R ⟩ → ⟨ P ⟩ l ⟨ R′ ⟩
  _~⟨_⟫_ {l = l} _ H PlR = strengthen {l = l} H PlR

  -- step syntax
  _~⟨_∶-_⟩_ : ∀ P′ t → ℝ⟨ P′ ⟩ [ t ] ⟨ P ⟩ → ℝ⟨ P ⟩ l ⟨ R ⟩ → ℝ⟨ P′ ⟩ t ∷ l ⟨ R ⟩
  _~⟨_∶-_⟩_ {l = l} {R = R} P′ t H PlR = mkℝ go
    where
      go : P′ ⊢ R ↑∘ ⟦ t ∷ l ⟧
      go {s} P′s with ⟦ t ⟧ s | (begin H) P′s
      ... | just _ | ret↑ Ps′ = (begin PlR) Ps′

  -- step′ syntax
  _~⟨_∶-_⟩++_ : ∀ P′ → (l : Program) → ℝ⟨ P′ ⟩ l ⟨ P ⟩ → ℝ⟨ P ⟩ l′ ⟨ R ⟩ → ℝ⟨ P′ ⟩ l ++ l′ ⟨ R ⟩
  P′ ~⟨ l ∶- H ⟩++ PlR = mkℝ hoare-step′ {l = l} (begin H) (begin PlR)

  _∎ : ∀ P → ℝ⟨ P ⟩ [] ⟨ P ⟩
  p ∎ = mkℝ hoare-base {P = p}
