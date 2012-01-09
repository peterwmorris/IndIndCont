{-# OPTIONS --universe-polymorphism #-}

module Lib where

open import Level

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

syntax Σ A (λ x → B) = Σ* x ∶ A *Σ B

infix 4 _≅_

data _≅_ {a} {A : Set a} (x : A) : {B : Set a} → B → Set a where
  refl : x ≅ x

_≡_ : ∀ {a} {A : Set a} (x : A) → A → Set a
_≡_ {a} {A} x y =  x ≅ y
