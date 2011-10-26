

\begin{code}

{-# OPTIONS --type-in-type 
 #-}

module iicont2 where

  open import Function
  open import Data.Unit
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
 
  record Fam : Set where
   constructor _,_
   field
    A : Set
    f : A → Set

  record IIC₀ : Set where -- IIC₀ = Fam (Fam Set) ^Op ??
   constructor _◁₀_
   field 
    S : Set
    P : S → Fam

  Fam[_⇒_] : Fam → Fam → Set
  Fam[ (A , f) ⇒ (B , g) ] = Σ[ m ∶ (A → B) ] ((a : A) → f a → g  (m a))

  Fam∘ : ∀ {X Y Z} → Fam[ Y ⇒ Z ] → Fam[ X ⇒ Y ] → Fam[ X ⇒ Z ]
  Fam∘ (sf , pf) (tf , qf) = (sf ∘ tf) , (λ a → pf (tf a) ∘ qf a)

  ⟦_⟧₀ : IIC₀ → Fam → Set
  ⟦ S ◁₀ P ⟧₀ X = Σ[ s ∶ S ] (Fam[ P s ⇒ X ])

  IIC₀[_⇒_] : IIC₀ → IIC₀ → Set
  IIC₀[ (S ◁₀ P) ⇒ (T ◁₀ Q) ] = Σ[ sf ∶ (S → T) ] ((s : S) → Fam[ Q (sf s) ⇒ P s ])

  IIC₀$ : {C D : IIC₀} {X : Fam} → IIC₀[ C ⇒ D ] → ⟦ C ⟧₀ X → ⟦ D ⟧₀ X
  IIC₀$ {S ◁₀ P} {T ◁₀ Q} {X} (sf , pf) (s , f) = (sf s) , Fam∘ {Z = X} f (pf s) 
 
  record IIC₁ (C : IIC₀) : Set where
    constructor _<_>_
    field
      D : IIC₀
      sf : IIC₀.S D → IIC₀.S C
      pf : (t : IIC₀.S D) → Fam.A (IIC₀.P D t) → ⊤ ⊎ Fam.A (IIC₀.P C (sf t))

  ⟦_⟧₁ : {C : IIC₀} → IIC₁ C → (X : Fam) → ⟦ C ⟧₀ X → Set
  ⟦_⟧₁ {S ◁₀ P} ((T ◁₀ Q) < sf > pf) X sfx = 
    Σ[ tgx ∶ ⟦ T ◁₀ Q ⟧₀ X ]  
    Σ[ seq ∶ sf (proj₁ tgx) ≡ proj₁ sfx ]  
      ((q : Fam.A (Q _)) 
       (p : Fam.A (P (sf _))) → 
       pf _ q ≡ inj₂ p → 
       proj₁ (proj₂ sfx) (subst (λ s′ → Fam.A (P s′)) seq p) ≡ proj₁ (proj₂ tgx) q) 



  \end{code}

