module Chapter1-Agda where

module foo where
  module bar where
    module qux where
    module zaz where
  module ram where

module Example-Imports where
  open import Data.Bool
  _ : Bool
  _ = false

module Example-TypingJudgments where
  postulate
    Bool : Set
    false : Bool
    true : Bool
    -- illegal : false
    file-not-found : Bool

module Booleans where
  data Bool : Set where
    false : Bool
    true  : Bool

  not : Bool → Bool
  not false = true
  not true = false

  open import Relation.Binary.PropositionalEquality

  _ : not (not false) ≡ false
  _ = refl

  -- _ : not (not false) ≡ true
  -- _ = refl

  _∨_ : Bool → Bool → Bool
  false ∨ b = b
  true  ∨ b = true

  _∧_ : Bool → Bool → Bool
  false ∧ b = false
  true  ∧ b = b

  _∨₁_ : Bool → Bool → Bool
  false ∨₁ false = false
  false ∨₁ true  = true
  true  ∨₁ false = true
  true  ∨₁ true  = true

  _∨₂_ : Bool → Bool → Bool
  false ∨₂ b = b
  true  ∨₂ b = true

  foo = true ∨₂_
  bar = true ∨₁_

  postulate always-stuck : Bool

  foo₂ = true ∨₂ always-stuck
  bar₂ = true ∨₁ always-stuck

module Example-Employees where
  open Booleans
  open import Data.String using (String)

  data Department : Set where
    administrative : Department
    engineering    : Department
    finance        : Department
    marketing      : Department
    sales          : Department

  record Employee : Set where
    field
      name        : String
      department  : Department
      is-new-hire : Bool

  tillman : Employee
  tillman = record
    { name        = "Tillman"
    ; department  = engineering
    ; is-new-hire = false
    }

module Sandbox-Tuples where
  record _×_ (A : Set) (B : Set) : Set where
    field
      proj₁ : A
      proj₂ : B

  open Booleans

  my-tuple : Bool × Bool
  my-tuple = record { proj₁ = true ∨ true ; proj₂ = not true }

  first : Bool × Bool → Bool
  first record { proj₁ = x } = x

  open _×_

  my-tuple-first : Bool
  my-tuple-first = my-tuple .proj₁

  my-tuple-second : Bool
  my-tuple-second = proj₂ my-tuple

  my-copattern : Bool × Bool
  my-copattern .proj₁ = true ∨ true
  my-copattern .proj₂ = not true

  _,_ : {A B : Set} → A → B → A × B
  a , b = record { proj₁ = a ; proj₂ = b }

  my-tuple’ : Bool × Bool
  my-tuple’ = (true ∨ true) , not true

module Sandbox-Tuples₂ where
  open Booleans

  record _×_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B

  open _×_

  infixr 4 _,_
  infixr 2 _×_

  data _⊎_ (A : Set) (B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

  infixr 1 _⊎_

  module Example-Pets where
    open import Data.String using (String)

    data Species : Set where
      bird cat dog reptile : Species

    data Temperament : Set where
      anxious   : Temperament
      chill     : Temperament
      excitable : Temperament
      grumpy    : Temperament

    record Pet : Set where
      constructor makePet
      field
        species     : Species
        temperament : Temperament
        name        : String

    makeGrumpyCat : String → Pet
    makeGrumpyCat = makePet cat grumpy

  or : Bool × Bool → Bool
  or (false , b) = b
  or (true , b)  = true

  _ : Bool
  _ = or (true , false)

  curry : {A B C : Set} → (A × B → C) → A → B → C
  curry f a b = f (a , b)

  uncurry : {A B C : Set} → (A → B → C) → A × B → C
  uncurry f (a , b) = f a b

  _ : Bool × Bool → Bool
  _ = uncurry _∨_

module Sandbox-Implicits where
  open import Data.Bool using (Bool; false; true; not; _∨_)
  open import Data.Product
    using (_×_; proj₁; proj₂)
    renaming ( _,′_ to _,_
             ; curry′ to curry
             ; uncurry′ to uncurry
             )

  mk-tuple : (A : Set) → (B : Set) → A → B → A × B
  mk-tuple A B a b = a , b

  _ : Bool × Bool
  _ = mk-tuple Bool Bool true false

  data PrimaryColor : Set where
    red green blue : PrimaryColor

  -- bad-tuple : Bool × Bool
  -- bad-tuple = mk-tuple PrimaryColor Bool {!!} {!!}

  color-bool-tuple : PrimaryColor × Bool
  color-bool-tuple = mk-tuple _ _ red false

  mk-color-bool-tuple : PrimaryColor → Bool → PrimaryColor × Bool
  mk-color-bool-tuple = _,_ {A = PrimaryColor} {B = Bool}

  -- ambiguous : Bool
  -- ambiguous = _

open import Data.Bool
  using (Bool; false; true; not; _∨_; _∧_)
  public

open import Data.Product
  using (_×_; _,_; proj₁; proj₂; curry; uncurry)
  public

open import Data.Sum
  using (_⊎_; inj₁; inj₂)
  public
