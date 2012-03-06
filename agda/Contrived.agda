module Contrived where

open import Data.Nat
open import Data.Fin

data A : Set
data B : A → Set

data A where
  a₀ : A
  a₁ : (x : A) → B x → A
  a₂ : (x₀ x₁ : A) → B x₀ → B x₀ → A 

data B where
  b₀ : B a₀
  b₁ : A → B a₀
  b₂ : (x₀ x₁ x₂ : A)(y₀ y₁ : B x₀)(y₁ y₂ : B x₁) → B (a₁ x₀ y₀)


record Cont : Set₁ where
  field
    S₀ : Set
    P₀ : S₀ → Set
    Q₀ : (s₀ : S₀) → P₀ s₀ → Set
    S₁ : S₀ → Set
    P₁ : (s₀ : S₀) → S₁ s₀ → Set
    Q₁₀ : (s₀ : S₀) → S₁ s₀ → P₀ s₀ → Set
    Q₁₁ : (s₀ : S₀)(s₁ : S₁ s₀) → P₁ s₀ s₁ → Set
  
Contrived : Cont
Contrived = record { S₀ = Fin 3; 
                     P₀ = λ {zero → Fin zero ; (suc zero) → Fin 1 ; (suc (suc zero)) → Fin 2 ; (suc (suc (suc ()))) } ; 
                     Q₀ = λ { zero () ; (suc zero) _ → Fin 1 ; 
                              (suc (suc zero)) zero → Fin 2 ; 
                              (suc (suc zero)) (suc zero) → Fin 0 ; 
                              (suc (suc zero)) (suc (suc ())) ; 
                              (suc (suc (suc ()))) _}; 
                     S₁ =  λ {zero → Fin 2 ; (suc zero) → Fin 1 ; (suc (suc zero)) → Fin zero ; (suc (suc (suc ()))) } ; 
                     P₁ = λ {zero zero → Fin zero ; zero (suc zero) → Fin 1 ; zero (suc (suc ())) ; 
                             (suc zero) zero → Fin 2 ; (suc zero) (suc ()) ; 
                             (suc (suc zero)) () ; 
                             (suc (suc (suc ()))) _ } ; 
                     Q₁₀ =  λ {zero _ () ; 
                               (suc zero) zero _ → Fin 1 ; (suc zero) (suc ()) _ ; 
                               (suc (suc zero)) () _ ; 
                               (suc (suc (suc ()))) _ _}; 
                     Q₁₁ = λ {zero _ _ → Fin zero ; 
                               (suc zero) zero zero → Fin 2 ; (suc zero) zero (suc zero) → Fin zero ; (suc zero) zero (suc (suc ())) ; (suc zero) (suc ()) _ ; 
                               (suc (suc zero)) () _ ; 
                               (suc (suc (suc ()))) _ _} }


{-

Can we think of an interesting but less contrived example?

What is Cont closed under? 

-}
