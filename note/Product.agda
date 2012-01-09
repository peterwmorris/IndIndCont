{-# OPTIONS --universe-polymorphism #-}

module Product where

open import Level 

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

syntax Σ A (λ x → B) = Σ* x ∶ A *Σ B