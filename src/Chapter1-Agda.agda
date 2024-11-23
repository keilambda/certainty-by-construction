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
