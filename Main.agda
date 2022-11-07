{-# OPTIONS --rewriting #-} -- needed for UTxO hashing
module Main where

-- ∙ S := K → Value
-- ∙ P := S → Set
-- ∙ Separation := _∪_
open import Shallow.Main

-- ∙ S := Map⟨ K ↦ Value ⟩
-- ∙ P := S → Set
-- ∙ Separation := _∪_
open import Middle.Main

-- ∙ S := Map⟨ K ↦ Value ⟩
-- ∙ P := Assertion
-- ∙ Separation := _∪_
open import Deep.Main

-- <Deep.Main> + shallow embedding of Hoare triples
--   ∙ {P}l{Q} = ∀ s. P(s) → Q(⟦l⟧s)
open import ShallowHoare.Main

-- Initial prototype for extending to the UTxO case.
open import UTxO.Main

-- ∙ S := Map⟨ K ↦ Value ⟩
-- ∙ P := S → Set
-- ∙ Separation := _◇_
open import ValueSep.Main

-- Simplified version of above.
-- ∙ S := K → ℕ
-- ∙ P := S → Set
-- ∙ Separation := _◇_
open import ValueSepSimple.Main

-- Value-separated UTxO.
-- ∙ S := Bag⟨ Address × Value ⟩
-- ∙ P := S → Set
-- ∙ Separation := _◇_
open import ValueSepUTxO.Main

-- Value-separated **abstract** UTxO.
-- ∙ S := Bag⟨ Address × Value ⟩
-- ∙ P := S → Set
-- ∙ Separation := _◇_
open import ValueSepAbstractUTxO.Main
