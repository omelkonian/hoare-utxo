------------------------------------------
-- ** Denotational & operational semantics

module Ledger where

open import Prelude.Init
open import Prelude.General
open import Prelude.Sets
open import Prelude.Membership

open import UTxO

-- ** Denotational semantics

-- The meaning of a transaction or a whole ledger will be denoted by state transformers,
-- i.e. function from the current state to the updated one.
Domain = S → S

record Denotable (A : Set) : Set where
  field ⟦_⟧ : A → Domain
open Denotable ⦃...⦄ public

instance
  -- we denote a transaction as simply running the transaction based on the transfer operation above
  ⟦Tx⟧ : Denotable Tx
  ⟦Tx⟧ .⟦_⟧ tx utxos =
    if isValidTx tx utxos then
        fromList (filter ((_∉? outputRefs tx) ∘ UTXO.outRef) (toList utxos))
      ∪ fromList (mapWith∈ (tx .outputs) (mkUtxo tx))
    else
      utxos

  -- we denote a ledger as the composition of the denotations of its transactions,
  -- i.e. we run all transactions in sequence
  ⟦L⟧ : Denotable L
  ⟦L⟧ .⟦_⟧ = λ where
    []      → id
    (t ∷ l) → ⟦ l ⟧ ∘ ⟦ t ⟧

variable
  s s′ s″ s₁ s₂ : S
  t t′ t″ : Tx
  l l′ l″ l₁ l₂ : L
  ls ls′ ls″ : L × S

comp : ∀ x → ⟦ l ++ l′ ⟧ x ≡ (⟦ l′ ⟧ ∘ ⟦ l ⟧) x
comp {l = []}    {l′} x = refl
comp {l = t ∷ l} {l′} x rewrite comp {l}{l′} (⟦ t ⟧ x) = refl

-- ** Lemmas about the transfer operation on maps.
-- transfer-helper : s₁ ♯ s₂ → B ∉ˢ s₂ → ⟦ tx ⟧ s₁ ♯ s₂
-- transfer-helper {s₁ = s₁}{s₂}{B}{A}{v} s₁♯s₂ B∉ = ♯-cong-pre [∣↦]-pre s₁♯s₂
