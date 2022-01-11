{-# OPTIONS --allow-unsolved-metas #-}
---------------------------------------
-- ** Concurrent separation logic (CSL)

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Lists
open import Prelude.Sets as Set hiding (_♯_; _∪_)
open import Prelude.Maps as Map renaming (_♯_ to _♯ᵐ_)

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Ternary.Interleaving

module CSL where

open import UTxO
open import Ledger
open import HoareLogic
open import SL

-- ** Proof of CSL's [PAR] rule, which allows for modular reasoning.
[PAR] :
    l₁ ∥ l₂ ≡ l
  → ⟨ P₁ ⟩ l₁ ⟨ Q₁ ⟩
  → ⟨ P₂ ⟩ l₂ ⟨ Q₂ ⟩
  → l₁ ♯ P₂
  → l₂ ♯ P₁
    ---------------------------
  → ⟨ P₁ `∗ P₂ ⟩ l ⟨ Q₁ `∗ Q₂ ⟩
[PAR] = {!!}
