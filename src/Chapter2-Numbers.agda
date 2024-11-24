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

  module Sandbox-Usable where
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

module Misstep-Integers₁ where
  data ℤ : Set where
    zero : ℤ
    suc  : ℤ → ℤ
    pred : ℤ → ℤ

  normalize : ℤ → ℤ
  normalize zero            = zero
  normalize (suc zero)      = suc zero
  normalize (suc (suc x))   = suc (normalize (suc x))
  normalize (suc (pred x))  = normalize x
  normalize (pred zero)     = pred zero
  normalize (pred (suc x))  = normalize x
  normalize (pred (pred x)) = pred (normalize (pred x))

  module Counterexample where
    open import Relation.Binary.PropositionalEquality

    _ : normalize (suc (suc (pred (pred zero)))) ≡ suc (pred zero)
    _ = refl

module Misstep-Integers₂ where
  import Data.Nat as ℕ
  open ℕ using (ℕ; zero; suc)

  record ℤ : Set where
    constructor mkℤ
    field
      pos : ℕ
      neg : ℕ

  normalize : ℤ → ℤ
  normalize (mkℤ zero neg)            = mkℤ zero neg
  normalize (mkℤ (suc pos) zero)      = mkℤ (suc pos) zero
  normalize (mkℤ (suc pos) (suc neg)) = normalize (mkℤ pos neg)

  _+_ : ℤ → ℤ → ℤ
  mkℤ p₁ n₁ + mkℤ p₂ n₂ = normalize (mkℤ (p₁ ℕ.+ p₂) (n₁ ℕ.+ n₂))

  infixl 5 _+_

  _-_ : ℤ → ℤ → ℤ
  mkℤ p₁ n₁ - mkℤ p₂ n₂ = normalize (mkℤ (p₁ ℕ.+ n₂) (n₁ ℕ.+ p₂))

  infixl 5 _-_

  _*_ : ℤ → ℤ → ℤ
  mkℤ p₁ n₁ * mkℤ p₂ n₂ = normalize (mkℤ (p₁ ℕ.* p₂ ℕ.+ n₁ ℕ.* n₂) (p₁ ℕ.* n₂ ℕ.+ p₂ ℕ.* n₁))

  infixl 6 _*_

module Misstep-Integers₃ where
  open import Data.Nat

  data ℤ : Set where
    +_ : ℕ → ℤ
    -_ : ℕ → ℤ

  _ : ℤ
  _ = - 2

  _ : ℤ
  _ = + 6

  _ : ℤ
  _ = + 0

  _ : ℤ
  _ = - 0

module Sandbox-Integers where
  import Data.Nat as ℕ
  open ℕ using (ℕ)

  data ℤ : Set where
    +_ : ℕ → ℤ
    -[1+_] : ℕ → ℤ

  0ℤ : ℤ
  0ℤ = + 0

  1ℤ : ℤ
  1ℤ = + 1

  -1ℤ : ℤ
  -1ℤ = -[1+ 0 ]

  suc : ℤ → ℤ
  suc (+ x)          = + ℕ.suc x
  suc -[1+ ℕ.zero ]  = 0ℤ
  suc -[1+ ℕ.suc x ] = -[1+ x ]

  pred : ℤ → ℤ
  pred (+ ℕ.zero)  = -1ℤ
  pred (+ ℕ.suc x) = + x
  pred -[1+ x ]    = -[1+ ℕ.suc x ]

  -’_ : ℤ → ℤ
  -’ (+ ℕ.zero)  = 0ℤ
  -’ (+ ℕ.suc x) = -[1+ x ]
  -’ -[1+ x ]    = + ℕ.suc x

  pattern +[1+_] n = + ℕ.suc n
  pattern +0 = + ℕ.zero

  -_ : ℤ → ℤ
  - +0 = +0
  - -[1+ x ] = +[1+ x ]
  - +[1+ x ] = -[1+ x ]

  module Native-Addition where
    -- _+_ : ℤ → ℤ → ℤ
    -- +0       + y        = y
    -- +[1+ x ] + +0       = +[1+ x ]
    -- +[1+ x ] + +[1+ y ] = +[1+ 1 ℕ.+ x ℕ.+ y ]
    -- +[1+ x ] + -[1+ y ] = {!   !}
    -- -[1+ x ] + +0       = -[1+ x ]
    -- -[1+ x ] + +[1+ y ] = {!   !}
    -- -[1+ x ] + -[1+ y ] = -[1+ 1 ℕ.+ x ℕ.+ y ]

    _⊖_ : ℕ → ℕ → ℤ
    ℕ.zero  ⊖ ℕ.zero  = +0
    ℕ.zero  ⊖ ℕ.suc n = -[1+ n ]
    ℕ.suc m ⊖ ℕ.zero  = +[1+ m ]
    ℕ.suc m ⊖ ℕ.suc n = m ⊖ n

    infixl 5 _+_

    _+_ : ℤ → ℤ → ℤ
    + x      + + y      = + (x ℕ.+ y)
    + x      + -[1+ y ] = x ⊖ ℕ.suc y
    -[1+ x ] + + y      = y ⊖ ℕ.suc x
    -[1+ x ] + -[1+ y ] = -[1+ x ℕ.+ ℕ.suc y ]

    infixl 5 _-_

    _-_ : ℤ → ℤ → ℤ
    x - y = x + (- y)

    infixl 6 _*_

    _*_ : ℤ → ℤ → ℤ
    x * +0 = +0
    x * +[1+ ℕ.zero ] = x
    x * -[1+ ℕ.zero ] = - x
    x * +[1+ ℕ.suc y ] = (+[1+ y ] * x) + x
    x * -[1+ ℕ.suc y ] = (-[1+ y ] * x) - x

    module Tests where
      open import Relation.Binary.PropositionalEquality

      _ : - (+ 2) * - (+ 6) ≡ + 12
      _ = refl

      _ : (+ 3) - (+ 10) ≡ - (+ 7)
      _ = refl

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
  public

open Sandbox-Naturals
  using (one; two; three; four)
  public

open Sandbox-Naturals
  using (IsEven; IsOdd)
  renaming ( zero-even    to z-even
           ; suc-suc-even to ss-even
           ; one-odd      to 1-odd
           ; suc-suc-odd  to ss-odd
           )
  public

open import Data.Maybe using (Maybe; just; nothing) public
