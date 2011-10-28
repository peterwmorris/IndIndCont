

\begin{code}

{-# OPTIONS --type-in-type 
 #-}

module iicont where

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

  ΣFam : Fam → Set
  ΣFam (A , f) = Σ A f

  record IIC₀ : Set where -- IIC₀ = Fam (Fam Set) ^Op ??
   constructor _◁₀_,_
   field 
    S : Set
    P : S → Set
    Q : (s : S) → P s → Set

  Fam[_⇒_] : Fam → Fam → Set
  Fam[ (A , f) ⇒ (B , g) ] = Σ[ m ∶ (A → B) ] ((a : A) → f a → g  (m a))

  Fam∘ : ∀ {X Y Z} → Fam[ Y ⇒ Z ] → Fam[ X ⇒ Y ] → Fam[ X ⇒ Z ]
  Fam∘ (sf , pf) (tf , qf) = (sf ∘ tf) , (λ a → pf (tf a) ∘ qf a)

  ⟦_⟧₀ : IIC₀ → Fam → Set
  ⟦ S ◁₀ P , Q ⟧₀ (X , Y) = Σ[ s ∶ S ] Σ[ f ∶ (P s → X) ] ((p : P s) → Q s p → Y (f p))

  record IIC₁ (C : IIC₀) : Set where
   constructor _◁₁_,_,_
   field 
    S : IIC₀.S C -> Set
    P : (s : IIC₀.S C) → S s → Set
    Q₀ : (s : IIC₀.S C) (t : S s) → IIC₀.P C s → Set
    Q₁ : (s : IIC₀.S C) (t : S s) → P s t → Set


  ⟦_⟧₁ : {C : IIC₀} → IIC₁ C → (X : Fam) → ⟦ C ⟧₀ X → Set
  ⟦_⟧₁ {S₀ ◁₀ P₀ , Q₀} (S₁ ◁₁ P₁ , Q₁₀ , Q₁₁) (X , Y) (s , (f , g)) = 
    Σ[ t ∶ S₁ s ] Σ[ h ∶ (P₁ s t → X) ] 
                  ((p : P₀ s) → Q₁₀ s t p → Y (f p)) 
               × (((p : P₁ s t) → Q₁₁ s t p → Y (h p)))  

  IIC : Set 
  IIC = Σ[ C ∶ IIC₀ ] IIC₁ C

  ⟦_⟧ : IIC → Fam → Fam
  ⟦ C , D ⟧ F = ⟦ C ⟧₀ F , ⟦ D ⟧₁ F

  IIC[_⇒_] : IIC → IIC → Set
  IIC[ ((S₀ ◁₀ P₀ , Q₀) , (S₁ ◁₁ P₁ , Q₁₀ , Q₁₁)) ⇒ D ] = (s₀ : S₀) → ΣFam (⟦ D ⟧ (A s₀ , B s₀)) 
    where A : S₀ → Set ; A s₀ = P₀ s₀ ⊎ (Σ[ s₁ ∶ S₁ s₀ ] P₁ s₀ s₁)  
          B : (s₀ : S₀) → A s₀ → Set 
          B s₀ (inj₁ p₀) = Q₀ s₀ p₀ ⊎ (Σ[ s₁ ∶ S₁ s₀ ] Q₁₀ s₀ s₁ p₀)
          B s₀ (inj₂ (s₁ , p₁)) = Q₁₁ s₀ s₁ p₁ 

  IIC$ : (F G : IIC) → IIC[ F ⇒ G ] → {X : Fam} → ΣFam (⟦ F ⟧ X) → ΣFam (⟦ G ⟧ X)
  IIC$ F G m {X , Y}  ((s₀ , (f , g))  , (s₁ , (h , (i , j)))) with m s₀ 
  ... | ((s₀' , (ff , gf)) , (s₁' , (hf , (if , jf)))) = ((s₀' , ({!!} , {!!})) , ({!!} , ( {!!} , ( {!!} , {!!} ))))

  \end{code}

