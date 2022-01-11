----------------------------------------------
-- ** Basic definition for UTxO-based ledgers.

module UTxO where

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.ToN
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Functor
open import Prelude.Applicative

Value   = ℕ
HashId  = ℕ
Address = HashId
postulate _♯ : ∀ {A : Set ℓ} → A → HashId

DATA = ℕ -- T0D0: more realistic data for redeemers

record TxOutputRef : Set where
  constructor _indexed-at_
  field txId  : HashId
        index : ℕ
open TxOutputRef public
unquoteDecl DecEq-TxOR = DERIVE DecEq [ quote TxOutputRef , DecEq-TxOR ]

record TxOutput : Set where
  constructor _at_
  field value    : Value
        address  : Address
open TxOutput public
unquoteDecl DecEq-TxO = DERIVE DecEq [ quote TxOutput , DecEq-TxO ]

record InputInfo : Set where
  field outputRef     : TxOutputRef
        validatorHash : HashId
        redeemerHash  : HashId

record TxInfo : Set where
  field inputs  : List InputInfo
        outputs : List TxOutput
        forge   : Value

record TxInput : Set where
  field outputRef : TxOutputRef
        validator : TxInfo → DATA → Bool
        redeemer  : DATA
open TxInput public

mkInputInfo : TxInput → InputInfo
mkInputInfo i = record
  { outputRef     = i .outputRef
  ; validatorHash = i .validator ♯
  ; redeemerHash  = i .redeemer ♯ }

record Tx : Set where
  field
    inputs  : List TxInput
    outputs : List TxOutput
    forge   : Value
open Tx public

mkTxInfo : Tx → TxInfo
mkTxInfo tx = record
  { inputs  = mkInputInfo <$> tx .inputs
  ; outputs = tx .outputs
  ; forge   = tx .forge }

-- A ledger is a list of transactions.
L = List Tx

record UTXO : Set where
  field outRef : TxOutputRef
        out    : TxOutput
unquoteDecl DecEq-UTXO = DERIVE DecEq [ quote UTXO , DecEq-UTXO ]

-- The state of a ledger is a collection of unspent transaction outputs.
S : Set
S = Set⟨ UTXO ⟩

mkUtxo : ∀ {out} tx → out L.Mem.∈ outputs tx → UTXO
mkUtxo {out} tx out∈ = λ where
  .UTXO.outRef → (tx ♯) indexed-at toℕ (L.Any.index out∈)
  .UTXO.out    → out

outputRefs : Tx → List TxOutputRef
outputRefs = map outputRef ∘ inputs

getSpentOutputRef : S → TxOutputRef → Maybe TxOutput
getSpentOutputRef s oRef = go (toList s)
  where
    go : List UTXO → Maybe TxOutput
    go [] = nothing
    go (record {outRef = or; out = o} ∷ xs) =
      if oRef == or then
        just o
      else
        go xs

getSpentOutput : S → TxInput → Maybe TxOutput
getSpentOutput s i = getSpentOutputRef s (i .outputRef)

∑ : ∀ {A : Set} → List A → (A → Value) → Value
∑ xs f = ∑ℕ (map f xs)

∑M : ∀ {A : Set} → List (Maybe A) → (A → Value) → Maybe Value
∑M xs f = (flip ∑ f) <$> seqM xs
  where
    -- if one fails everything fails
    seqM : ∀ {A : Set} → List (Maybe A) → Maybe (List A)
    seqM []       = just []
    seqM (x ∷ xs) = ⦇ x ∷ seqM xs ⦈

record IsValidTx (tx : Tx) (utxos : S) : Set where
  field
    validOutputRefs :
      outputRefs tx ⊆ map UTXO.outRef (toList utxos)

    preservesValues :
      M.Any.Any (λ q → tx .forge + q ≡ ∑ (tx .outputs) value)
                (∑M (map (getSpentOutput utxos) (tx .inputs)) value)

    noDoubleSpending :
      Unique (outputRefs tx)

    allInputsValidate :
      All (λ i → T (validator i (mkTxInfo tx) (i .redeemer)))
          (tx .inputs)

    validateValidHashes :
      All (λ i → M.Any.Any (λ o → o .address ≡ i .validator ♯) (getSpentOutput utxos i))
          (tx .inputs)

open IsValidTx public

isValidTx? : ∀ tx s → Dec (IsValidTx tx s)
isValidTx? tx utxos
  with outputRefs tx ⊆? map UTXO.outRef (toList utxos)
... | no ¬p = no (¬p ∘ validOutputRefs )
... | yes p₁
  with M.Any.dec (λ q → tx .forge + q ≟ ∑ (tx .outputs) value)
                 (∑M (map (getSpentOutput utxos) (tx .inputs)) value)
... | no ¬p = no (¬p ∘ preservesValues)
... | yes p₂
  with unique? (outputRefs tx)
... | no ¬p = no (¬p ∘ noDoubleSpending)
... | yes p₃
  with all? (λ i → T? (validator i (mkTxInfo tx) (i .redeemer)))
            (tx .inputs)
... | no ¬p = no (¬p ∘ allInputsValidate)
... | yes p₄
  with all? (λ i → M.Any.dec (λ o → o .address ≟ i .validator ♯) (getSpentOutput utxos i))
            (tx .inputs)
... | no ¬p = no (¬p ∘ validateValidHashes)
... | yes p₅ = yes record {validOutputRefs = p₁; preservesValues = p₂; noDoubleSpending = p₃; allInputsValidate = p₄; validateValidHashes = p₅}

isValidTx : Tx → S → Bool
isValidTx tx s = ⌊ isValidTx? tx s ⌋
