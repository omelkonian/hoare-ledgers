{-# OPTIONS --rewriting #-} -- needed for UTxO hashing
module Main where

-------------------------
-- ** Linear bank ledgers
-------------------------

-- Shallow states, shallow predicates
-- ∙ S := K → Value
-- ∙ ⟦_⟧ := S → S
-- ∙ P := S → Set
-- ∙ Separation := IMPOSSIBLE
open import Shallow.Main

-- Deep states, shallow predicates
-- ∙ S := Map⟨ K ↦ Value ⟩
-- ∙ ⟦_⟧ := S → S
-- ∙ P := S → Set
-- ∙ Separation := _⊎_
open import Middle.Main

-- Deep states, deep predicates
-- ∙ S := Map⟨ K ↦ Value ⟩
-- ∙ ⟦_⟧ := S → S
-- ∙ P := Assertion
-- ∙ Separation := _⊎_
open import Deep.Main

-- <Deep> + shallow embedding of Hoare triples
--   ⋮
--   ∙ {P}l{Q} = ∀ s. P(s) → Q(⟦l⟧s)
open import ShallowHoare.Main

-- Monoidal separatation on values instead of participants.
-- ∙ S := Map⟨ K ↦ Value ⟩
-- ∙ ⟦_⟧ := S → Maybe S
-- ∙ P := S → Set
-- ∙ Separation := _◇_
open import ValueSep.Main

-- Simplified version of <ValueSep>.
-- ∙ S := K → ℕ
-- ∙ ⟦_⟧ := S → Maybe S
-- ∙ P := S → Set
-- ∙ Separation := _◇_
open import ValueSepSimple.Main

-----------------------------
-- ** UTxO blockchain ledgers
-------------------------

-- Initial prototype for extending to the UTxO case.
-- ∙ S := Set⟨ UTXO ⟩
-- ∙ ⟦_⟧ := S → S
-- ∙ P := S → Set
-- ∙ Separation := _⊎_
open import UTxO.Main

-- <UTxO> variant that explicitly errors/invalidity.
-- ∙ S := Map⟨ TxOutputRef ↦ TxOutput ⟩
-- ∙ ⟦_⟧ := S → Maybe S
-- ∙ P := S → Set
-- ∙ Separation := _⊎_
open import UTxOErr.Main

-- Value-separated **abstract** UTxO.
-- ∙ S := Bag⟨ Address × Value ⟩
-- ∙ ⟦_⟧ := S → Maybe S
-- ∙ P := S → Set
-- ∙ Separation := _◇_
open import ValueSepUTxO.Main
