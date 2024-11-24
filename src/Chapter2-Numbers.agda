module Chapter2-Numbers where

import Chapter1-Agda

module Definition-Naturals where
  data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

module Sandbox-Naturals where
  open import Data.Nat using (ℕ; zero; suc)

  one : ℕ
  one = suc zero

  two : ℕ
  two = suc one

  three : ℕ
  three = suc two

  four : ℕ
  four = suc three

  open Chapter1-Agda using (Bool; true; false)

  n=0? : ℕ → Bool
  n=0? zero    = true
  n=0? (suc x) = false

  n=2? : ℕ → Bool
  n=2? (suc (suc zero)) = true
  n=2? n                = false

  even? : ℕ → Bool
  even? zero          = true
  even? (suc zero)    = false
  even? (suc (suc n)) = even? n

  data Evenℕ : Set where
    zero    : Evenℕ
    suc-suc : Evenℕ → Evenℕ

  toℕ : Evenℕ → ℕ
  toℕ zero        = zero
  toℕ (suc-suc x) = suc (suc (toℕ x))

  module Sadnbox-Usable where
    postulate
      Usable   : Set
      Unusable : Set

    IsEven : ℕ → Set
    IsEven zero = Usable
    IsEven (suc zero) = Unusable
    IsEven (suc (suc x)) = IsEven x

  data IsEven : ℕ → Set where
    zero-even : IsEven zero
    suc-suc-even : {n : ℕ} → IsEven n → IsEven (suc (suc n))

  four-is-even : IsEven four
  four-is-even = suc-suc-even (suc-suc-even zero-even)

  -- three-is-even : IsEven three
  -- three-is-even = suc-suc-even {!   !}

  data IsOdd : ℕ → Set where
    one-odd : IsOdd (suc zero)
    suc-suc-odd : {n : ℕ} → IsOdd n → IsOdd (suc (suc n))

  data IsOdd’ : ℕ → Set where
    is-odd : {n : ℕ} → IsEven n → IsOdd’ (suc n)

  three-is-odd : IsOdd three
  three-is-odd = suc-suc-odd one-odd

  evenOdd : {n : ℕ} → IsEven n → IsOdd (suc n)
  evenOdd zero-even        = one-odd
  evenOdd (suc-suc-even x) = suc-suc-odd (evenOdd x)

  evenOdd’ : {n : ℕ} → IsEven n → IsOdd’ (suc n)
  evenOdd’ = is-odd

  data Maybe (A : Set) : Set where
    just    : A → Maybe A
    nothing : Maybe A

  evenEv : (n : ℕ) → Maybe (IsEven n)
  evenEv zero          = just zero-even
  evenEv (suc zero)    = nothing
  evenEv (suc (suc n)) with evenEv n
  ... | just x  = just (suc-suc-even x)
  ... | nothing = nothing

  _+_ : ℕ → ℕ → ℕ
  zero  + y = y
  suc x + y = suc (x + y)

  infixl 6 _+_

  module Example-Silly where
    open Chapter1-Agda using (not)

    data ℕ’ : Set where
      zero : ℕ’
      suc  : ℕ’ → ℕ’
      2suc : ℕ’ → ℕ’

    even?’ : ℕ’ → Bool
    even?’ zero = true
    even?’ (suc n) = not (even?’ n)
    even?’ (2suc zero) = true
    even?’ (2suc (suc n)) = not (even?’ n)
    even?’ (2suc (2suc n)) = even?’ n

  _*_ : ℕ → ℕ → ℕ
  zero  * y = zero
  suc x * y = y + (x * y)

  infixl 7 _*_

  _^_ : ℕ → ℕ → ℕ
  x ^ zero  = one
  x ^ suc y = x * (x ^ y)

  _∸_ : ℕ → ℕ → ℕ
  x ∸ zero = x
  zero ∸ suc y = zero
  suc x ∸ suc y = x ∸ y

  module Natural-Tests where
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)

    _ : one + two ≡ three
    _ = refl

    _ : three ∸ one ≡ two
    _ = refl

    _ : one ∸ three ≡ zero
    _ = refl

    _ : two * two ≡ four
    _ = refl

  -- not from the book
  module Naturals-Proofs where
    open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

    +-idl : {x : ℕ} → x + 0 ≡ x
    +-idl {zero} = refl
    +-idl {suc x} = cong suc +-idl

    +-idr : {x : ℕ} → 0 + x ≡ x
    +-idr {zero} = refl
    +-idr {suc x} = cong suc +-idr

    *-idl : {x : ℕ} → x * 1 ≡ x
    *-idl {zero} = refl
    *-idl {suc x} = cong suc *-idl

    *-idr : {x : ℕ} → 1 * x ≡ x
    *-idr {zero} = refl
    *-idr {suc x} = cong suc *-idr
