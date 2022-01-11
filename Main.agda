{-# OPTIONS --rewriting #-}
module Main where

-- ** A simple definition of a bank ledger as a series of transactions: A —→⟨ v ⟩ B.
-- We model the ledger state as maps from participants to balances, using the abstract map interface in Prelude.Maps,
-- and define both operational and denotational semantics.
-- [Proofs]
--    * correspondence between operational and denotational semantics
--    * useful lemmas about the ledger-specific operation `transfer/[_∣_↦_]`
open import Ledger

-- ** A Hoare-style axiomatic semantics, based on a deep embedding of propositions.
-- We also provide some utilities for working with Hoare triples and convenient reasoning syntax.
-- [Proofs]
--   * correspondence with denotational semantics and, by transitivity, operational semantics.
--   * associativity/commutativity of separating conjuction _∗_
open import HoareLogic

-- ** Introduce the concept of disjointness for propositions, i.e. when the participants they refer to do not overlap,
-- which allows us to express the frame rule of Separation Logic (SL).
-- [Proofs]
--  * useful lemmas about separation, transferring values, etc...
--  * the [FRAME] inference rule, which allows us to reason about a sub-formula and then inject the result in a larger context
open import SL

-- ** Define interleaving of two ledgers and prove the parallel rule of Concurrent Separation Logic (CSL).
-- [Proofs]
--  * the [PAR] inference rule, which utilizes [FRAME] to let us reason about disjoint ledgers independently/concurrently,
-- and then compose the proofs (given that the pre-/post-conditions are sufficiently disjoint)
-- to conclude something of a larger ledgers, namely any ledger that is an interleaving of the first two.
open import CSL

-- ** An example of a ledger consisting of 4 transactions t₁⋯t₄,
--    recording that values are correctly updated in pre-/post-conditions.
-- 1. the first proof h repeatively uses the [FRAME] rule,
--    but it quickly gets tedious because we need to reason about the whole ledger (all 4 transactions),
--    although t₁ and t₃ act on a completely different set of participants than t₂ and t₄.
-- 2. the second proof h′ utilizes modular reasoning via [PAR];
--    we only prove smaller/simpler proofs for t₁/t₃ and t₂/t₄ and then compose them.
open import Example
