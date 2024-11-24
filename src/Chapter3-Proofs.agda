module Chapter3-Proofs where

open import Chapter1-Agda using (Bool; true; false; _∨_; _∧_; not)
open import Chapter2-Numbers using (ℕ; zero; suc)

module Example-ProofsAsPrograms where
  open Chapter2-Numbers using (IsEven)
  open ℕ
  open IsEven

  zero-is-even : IsEven zero
  zero-is-even = zero-even

  -- one-is-even : IsEven (suc zero)
  -- one-is-even = {!   !}

module Definition where
  data _≡_ {A : Set} : A → A → Set where
    refl : {x : A} → x ≡ x

  infix 4 _≡_

  sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl
