{-# OPTIONS --universe-polymorphism #-}

module Lib where

open import Level

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

syntax Σ A (λ x → B) = Σ* x ∶ A *Σ B

infix 4 _≅_

data _≅_ {a} {A : Set a} (x : A) : {B : Set a} → B → Set a where
  refl : x ≅ x

_≡_ : ∀ {a} {A : Set a} (x : A) → A → Set a
_≡_ {a} {A} x y =  x ≅ y

cong : ∀ {a b} {A : Set a} {B : A → Set b} {x y}
       (f : (x : A) → B x) → x ≅ y → f x ≅ f y
cong f refl = refl

subst : ∀ {a} {A : Set a} {p} (P : A → Set p) {x y} → x ≅ y → P x → P y
subst P refl p = p


postulate 
  dotdotdot : ∀ {a} {A : Set a} → A
