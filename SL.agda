{-# OPTIONS --allow-unsolved-metas #-}
---------------------------
-- ** Separation logic (SL)

module SL where

open import Prelude.Init
open L.Mem
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Sets as Set hiding (_♯_)
open import Prelude.Ord
open import Prelude.Functor

open import UTxO
open import Ledger
open import HoareLogic

-- Which addresses does a ledger modify?
mod : Address → L → Set
mod A = Any λ tx → A ∈ (address <$> tx .outputs)

-- Which addresses does an assertion refer to?
addr : Address → Assertion → Set
addr A `emp     = ⊥
addr A (B `↦ _) = A ≡ B
addr A (P `∗ Q) = addr A P ⊎ addr A Q
addr A (P `∘⟦ _ ⟧) = addr A P

-- Define disjointness between ledgers/states/formulas as disjointness of the participant set they refer to.
record _//_ (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ₗ lsuc ℓ′) where
  field _♯_ : A → B → Set
open _//_ ⦃...⦄ public

instance
  Disjoint-SS : S // S
  Disjoint-SS ._♯_ = Set._♯_

  Disjoint-LS : L // S
  Disjoint-LS ._♯_ l s = ∀ A → mod A l → ¬ ∃ λ utxo → (utxo .UTXO.out .address ≡ A) × (utxo ∈ˢ s)

  Disjoint-SL : S // L
  Disjoint-SL ._♯_ s l = ∀ A → (∃ λ utxo → (utxo .UTXO.out .address ≡ A) × (utxo ∈ˢ s)) → ¬ mod A l

  Disjoint-LA : L // Assertion
  Disjoint-LA ._♯_ l P = ∀ A → mod A l → ¬ addr A P

-- ** Utility lemmas about separation.

-- ∈ᵈ-∪ : ⟨ s₁ ⊎ s₂ ⟩≡ s → A ∈ᵈ s → A ∈ᵈ s₁ ⊎ A ∈ᵈ s₂
-- ∈ᵈ-∪ {s₁}{s₂}{s}{A} (s₁♯s₂ , p) A∈ = ∈ᵈ-∪⁻ _ _ _ (∈ᵈ-cong (≈-sym p) A∈)

-- ∉ᵈ-∪ : ⟨ s₁ ⊎ s₂ ⟩≡ s → A ∉ᵈ s → A ∉ᵈ s₁ × A ∉ᵈ s₂
-- ∉ᵈ-∪ {s₁}{s₂}{s}{A} (s₁♯s₂ , p) A∉ = A∉ ∘ ∈ᵈ-cong p ∘ ∈ᵈ-∪⁺ˡ _ _ _ , A∉ ∘ ∈ᵈ-cong p ∘ ∈ᵈ-∪⁺ʳ _ _ _

-- ∈⇒addr : A ∈ᵈ s → P ∙ s → addr A P
-- ∈⇒addr {A}{s}{P = `emp} A∈ Ps = ⊥-elim $ Ps A A∈
-- ∈⇒addr {A}{s}{P = B `↦ v} A∈ Ps with A ≟ B
-- ... | yes A≡B = A≡B
-- ... | no  A≢B = ⊥-elim $ proj₂ Ps A A≢B A∈
-- ∈⇒addr {A}{s}{P = P `∗ Q} A∈ (s₁ , s₂ , ≡s , Ps₁ , Qs₂)
--   with ∈ᵈ-∪ ≡s A∈
-- ... | inj₁ A∈₁ = inj₁ $ ∈⇒addr {P = P} A∈₁ Ps₁
-- ... | inj₂ A∈₂ = inj₂ $ ∈⇒addr {P = Q} A∈₂ Qs₂
-- ∈⇒addr {A}{s}{P = P `∘⟦ l ⟧} A∈ Ps = ∈⇒addr {P = P} (⟦⟧ₗ-mono {l} s A A∈) Ps

-- ∉⇒¬addr : A ∉ᵈ s → P ∙ s → ¬ addr A P
-- ∉⇒¬addr {A}{s}{P = `emp} A∉ Ps ()
-- ∉⇒¬addr {A}{s}{P = .A `↦ _} A∉ (Ps , _) refl = A∉ $ ⁉⇒∈ᵈ (subst Is-just (sym Ps) auto)
-- ∉⇒¬addr {A}{s}{P = P `∗ Q} A∉ (s₁ , s₂ , ≡s , Ps₁ , Qs₂) A∈
--   with A∉ˡ , A∉ʳ ← ∉ᵈ-∪ ≡s A∉
--   with A∈
-- ... | inj₁ A∈ˡ = ∉⇒¬addr {P = P} A∉ˡ Ps₁ A∈ˡ
-- ... | inj₂ A∈ʳ = ∉⇒¬addr {P = Q} A∉ʳ Qs₂ A∈ʳ
-- ∉⇒¬addr {A}{s}{P = P `∘⟦ l ⟧} A∉ Ps A∈ = ∉⇒¬addr {P = P} (∉-⟦⟧ₗ {l = l} A∉) Ps A∈

♯-skip : (t ∷ l) ♯ P → l ♯ P
♯-skip p A = p A ∘ there

-- ♯⇒♯ : l ♯ s → s ♯ l
-- ♯⇒♯ {s = s} p A A∈ A∈l = p _ A∈l A∈

♯♯⇒♯ : l ♯ R → R ∙ s → l ♯ s
♯♯⇒♯ {l} {`emp} {s} l♯R s∅ = λ _ _ (_ , _ , utxo∈) → s∅ _ utxo∈
♯♯⇒♯ {l} {A `↦ v} {s} l♯R Rs = {!!}
♯♯⇒♯ {l} {R `∗ Q} {s} l♯R Rs = {!!}
♯♯⇒♯ {_} {R `∘⟦ l ⟧} {s} l♯R Rs = {!!}

-- ♯♯⇒♯ {l}{`emp}{s} l♯R s∅ A A∈ = s∅ A
-- ♯♯⇒♯ {l}{B `↦ v}{s} l♯R (_ , B↦) A A∈ A∈′
--   with A ≟ B
-- ... | yes refl = l♯R A A∈ refl
-- ... | no  A≢B  = B↦ A A≢B A∈′
-- ♯♯⇒♯ {l}{R `∗ Q}{s} l♯R (s₁ , s₂ , ≡s , Rs₁ , Qs₂) A A∈
--   with s₁ ⁉ A | inspect (s₁ ⁉_) A | s₂ ⁉ A | inspect (s₂ ⁉_) A
-- ... | just _  | ≡[ s₁≡ ] | _       | _
--     = ⊥-elim $ l♯R A A∈ $ inj₁ $ ∈⇒addr {A}{s₁}{R} (⁉⇒∈ᵈ $ subst Is-just (sym s₁≡) auto) Rs₁
-- ... | _       | _        | just _  | ≡[ s₂≡ ]
--     = ⊥-elim $ l♯R A A∈ $ inj₂ $ ∈⇒addr {A}{s₂}{Q} (⁉⇒∈ᵈ $ subst M.Is-just (sym s₂≡) auto) Qs₂
-- ... | nothing | ≡[ s₁≡ ] | nothing | ≡[ s₂≡ ]
--   = ∉-splits ≡s (⊥-elim ∘ ⁉⇒∉ᵈ (subst Is-nothing (sym s₁≡) auto))
--                 (⊥-elim ∘ ⁉⇒∉ᵈ (subst Is-nothing (sym s₂≡) auto))
-- ♯♯⇒♯ {_}{R `∘⟦ l ⟧}{s} l♯R Rs A A∈ = ¬A∈
--   where
--     A∉ : A ∉ᵈ ⟦ l ⟧ s
--     A∉ = ♯♯⇒♯ {R = R} {s = ⟦ l ⟧ s} l♯R Rs A A∈

--     ¬A∈ : A ∉ᵈ s
--     ¬A∈ = A∉ ∘ ⟦⟧ₗ-mono {l} s A

-- Helper lemma for [FRAME]: pushing ⟦ l ⟧ inside the partition.
frame-helper :
    l ♯ R
  → R ∙ s₂
  → ⟨ s₁ ⊎ s₂ ⟩≡ s
    -----------------------
  → ⟨ ⟦ l ⟧ s₁ ⊎ s₂ ⟩≡ ⟦ l ⟧ s
frame-helper {l = []} _ _ p = p
frame-helper {l = tx ∷ l}{R}{s₂}{s₁}{s} l♯R Rs₂ (s₁♯s₂ , ≡s) =
  frame-helper {l}{R}{s₂}{⟦ tx ⟧ s₁}{⟦ tx ⟧ s} (♯-skip {P = R} l♯R) Rs₂ p′
  where
    p₁ : (⟦ tx ⟧ s₁) ♯ s₂
    p₁ = {!!}
    -- p₁ = transfer-helper s₁♯s₂ B∉₂

    p₂ : ((⟦ tx ⟧ s₁) ∪ s₂) ≈ˢ (⟦ tx ⟧ s)
    p₂ = {!!}

    p′ : ⟨ ⟦ tx ⟧ s₁ ⊎ s₂ ⟩≡ ⟦ tx ⟧ s
    p′ = p₁ , p₂


{-
frame-helper {l = l₀@(A —→⟨ v ⟩ B ∷ l)}{R}{s₂}{s₁}{s} l♯R Rs₂ (s₁♯s₂ , ≡s) =
  frame-helper {l}{R}{s₂}{run [ A ∣ v ↦ B ] s₁} {run [ A ∣ v ↦ B ] s} (♯-skip {P = R} l♯R) Rs₂ p′
  where
    l♯s₂ : l₀ ♯ s₂
    l♯s₂ = ♯♯⇒♯ {R = R} l♯R Rs₂

    A∉₂ : A ∉ᵈ s₂
    A∉₂ = l♯s₂ A $ here (here refl)

    B∉₂ : B ∉ᵈ s₂
    B∉₂ = l♯s₂ B $ here (there (here refl))

    p₁ : (run [ A ∣ v ↦ B ] s₁) Map.♯ s₂
    p₁ = transfer-helper s₁♯s₂ B∉₂

    ∉⇒≢ : ∀ k → k ∈ᵈ s₂ → (k ≢ A) × (k ≢ B)
    ∉⇒≢ k k∈ = k≢A , k≢B
      where
        k∉ : ¬ mod k l₀
        k∉ = ♯⇒♯ l♯s₂ k k∈

        k≢A : k ≢ A
        k≢A refl = ⊥-elim $ k∉ (here (here refl))

        k≢B : k ≢ B
        k≢B refl = ⊥-elim $ k∉ (here (there (here refl)))

    p₂ : (run [ A ∣ v ↦ B ] s₁) ∪ s₂ ≈ run [ A ∣ v ↦ B ] s
    p₂ k
      with eq ← ≡s k
      with eqᵃ ← ≡s A
      with eqᵇ ← ≡s B
      with ¿ k ∈ᵈ s₂ ¿
    ... | yes k∈
      with k≢A , k≢B ← ∉⇒≢ k k∈
      rewrite ∪-chooseᵣ p₁ k∈
            | ∪-chooseᵣ s₁♯s₂ k∈
            | drop-[∣↦] {v = v} {s = s} k k≢A k≢B
            = eq
    ... | no k∉
      rewrite ∪-chooseₗ p₁ k∉
            | ∪-chooseₗ s₁♯s₂ k∉
      with s₁ ⁉ A | inspect (s₁ ⁉_) A
         | s  ⁉ A | inspect (s  ⁉_) A
         | eqᵃ
    ... | nothing | _ | nothing | _ | _ = eq
    ... | nothing | ≡[ s₁A≡ ] | just _  | ≡[ sA≡ ] | _
        = let p = ↦-∪⁺ʳ {s₂ = s₂} $ ⁉⇒∉ᵈ (subst Is-nothing (sym s₁A≡) auto)
          in ⊥-elim $ A∉₂ $ ⁉⇒∈ᵈ $ subst Is-just (sym $ trans p (trans eqᵃ sA≡)) auto
    ... | just vᵃ | ≡[ s₁A≡ ] | nothing | _ | eqᵃ′
        = case trans (sym $ (↦-∪⁺ˡ {s₂ = s₂} s₁A≡)) eqᵃ′ of λ ()
    ... | just vᵃ  | ≡[ s₁A≡ ] | just vᵃ′ | _ | eqᵃ′
      with vᵃ ≟ vᵃ′
    ... | no neq = ⊥-elim $ neq $ M.just-injective $ trans (sym $ ↦-∪⁺ˡ {s₂ = s₂} s₁A≡) eqᵃ′
    ... | yes refl
      with s₁ ⁉ B | inspect (s₁ ⁉_) B
         | s  ⁉ B | inspect (s  ⁉_) B
         | eqᵇ
    ... | nothing | _ | nothing | _ | _
        = eq
    ... | nothing | ≡[ s₁B≡ ] | just _  | ≡[ sB≡ ] | _
        = let p = ↦-∪⁺ʳ {s₂ = s₂} $ ⁉⇒∉ᵈ (subst Is-nothing (sym s₁B≡) auto)
          in ⊥-elim $ B∉₂ $ ⁉⇒∈ᵈ $ subst Is-just (sym $ trans p (trans eqᵇ sB≡)) auto
    ... | just vᵇ | ≡[ s₁B≡ ] | nothing | _ | eqᵇ′
        = case trans (sym $ (↦-∪⁺ˡ {s₂ = s₂} s₁B≡)) eqᵇ′ of λ ()
    ... | just vᵇ  | ≡[ s₁B≡ ] | just vᵇ′ | _ | eqᵇ′
      with vᵇ ≟ vᵇ′
    ... | no neq = ⊥-elim $ neq $ M.just-injective $ trans (sym $ ↦-∪⁺ˡ {s₂ = s₂} s₁B≡) eqᵇ′
    ... | yes refl
      with v ≤? vᵃ
    ... | no  _ = eq
    ... | yes _ = ≡-cong-update $ ≡-cong-update eq

    p′ : ⟨ run [ A ∣ v ↦ B ] s₁ ⊎ s₂ ⟩≡ run [ A ∣ v ↦ B ] s
    p′ = p₁ , p₂
-}

-- The proof of the frame rule from separation logic, allowing us to prove formulas in minimal contexts
-- and then weaken our results to the desired context (assuming the rest of the context is disjoint).
[FRAME] : ∀ R
  → l ♯ R
  → ⟨ P ⟩ l ⟨ Q ⟩
    -----------------------
  → ⟨ P `∗ R ⟩ l ⟨ Q `∗ R ⟩
[FRAME] {l}{P}{Q} R l♯R PlQ = denot⇒axiom d
  where
    d : (P `∗ R) `⊢ (Q `∗ R) `∘⟦ l ⟧
    d {s} (s₁ , s₂ , s₁♯s₂ , Ps₁ , Rs₂) = ⟦ l ⟧ s₁ , s₂  , p , Qs₁′ , Rs₂
      where
        Qs₁′ : Q ∙ ⟦ l ⟧ s₁
        Qs₁′ = axiom⇒denot PlQ Ps₁

        p : ⟨ ⟦ l ⟧ s₁ ⊎ s₂ ⟩≡ ⟦ l ⟧ s
        p = frame-helper {R = R} l♯R Rs₂ s₁♯s₂
