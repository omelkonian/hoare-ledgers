module ValueSep.Main where

-- ** A simple definition of a bank ledger as a series of transactions: A —→⟨ v ⟩ B.
-- We model the ledger state as maps from participants to balances, using a concrete map implementation in ValueSep.Maps,
-- and define both operational and denotational semantics.
-- [Proofs]
--    * correspondence between operational and denotational semantics
--    * useful lemmas about the ledger-specific operation `transfer/[_∣_↦_]`
open import ValueSep.Ledger

-- ** A Hoare-style axiomatic semantics, based on a deep embedding of propositions.
-- We also provide some utilities for working with Hoare triples and convenient reasoning syntax.
-- [Proofs]
--   * correspondence with denotational semantics and, by transitivity, operational semantics.
--   * associativity/commutativity of separating conjuction _∗_
open import ValueSep.HoareLogic

-- ** Introduce the concept of disjointness for propositions, i.e. when the participants they refer to do not overlap,
-- which allows us to express the frame rule of Separation Logic (SL).
-- [Proofs]
--  * useful lemmas about separation, transferring values, etc...
--  * the [FRAME] inference rule, which allows us to reason about a sub-formula and then inject the result in a larger context
open import ValueSep.SL

-- **ISSUE** How do we formulate frame, seems incompatible with the semantics of a transaction that fails.
-- **SOLUTION** Change domain to incorporate failure, i.e. `S -> S` to `S -> Maybe S`.
