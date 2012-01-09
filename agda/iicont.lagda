

\begin{code}

{-# OPTIONS --type-in-type 
 #-}

module iicont where

  open import Function
  open import Data.Unit
  open import Data.Product
  open import Data.Sum renaming ([_,_] to case⊎; [_,_]′ to case⊎′)
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

  record IIC₀[_⇒_] (F G : IIC₀) : Set where
    constructor morii₀
    field
      sf : IIC₀.S F → IIC₀.S G
      pf : (s : IIC₀.S F) → IIC₀.P G (sf s) → IIC₀.P F s
      qf : (s : IIC₀.S F) (p : IIC₀.P G (sf s)) → IIC₀.Q G (sf s) p → IIC₀.Q F s (pf s p) 

  IIC₀$ : (C D : IIC₀) → IIC₀[ C ⇒ D ] → ∀ X → ⟦ C ⟧₀ X → ⟦ D ⟧₀ X
  IIC₀$ C D (morii₀ sf pf qf) X (s , f , g) = 
    sf s , (λ p → f (pf s p)) , (λ p q →  g (pf s p) (qf s p q))

  record IIC₁ (C : IIC₀) : Set where
   constructor _◁₁_,_,_
   field 
    S : IIC₀.S C -> Set
    P : (s : IIC₀.S C) → S s → Set
    Q₀ : (s : IIC₀.S C) (t : S s) → IIC₀.P C s → Set
    Q₁ : (s : IIC₀.S C) (t : S s) → P s t → Set


  compm : ∀ C D → (IIC₀[ C ⇒ D ]) → IIC₁ D → IIC₁ C
  compm (S ◁₀ P , Q) (S' ◁₀ P' , Q') (morii₀ sf pf qf) (T' ◁₁ P'₁ , Q'₁₀ , Q'₁₁)
      = T ◁₁ P₁ , Q₁₀ , Q₁₁
    where T : S → Set ; T s = T' (sf s)
          P₁ : (s : S) → T s → Set ; P₁ s t = P'₁ (sf s) t
          Q₁₀ : (s : S) → T s → P s → Set 
          Q₁₀ s t p = Σ[ p' ∶ P' (sf s) ] (pf s p' ≡ p × Q'₁₀ (sf s) t p')
          Q₁₁ : (s : S) (t : T s) → P₁ s t → Set 
          Q₁₁ s t p = Q'₁₁ (sf s) t p


  record IIC₁[_⇒_]† {C : IIC₀} (F G : IIC₁ C) : Set where
    constructor morii₁†
    field
      sf : (s : IIC₀.S C) → IIC₁.S F s → IIC₁.S G s
      pf :  (s : IIC₀.S C) (t : IIC₁.S F s) → IIC₁.P G s (sf s t) → IIC₀.P C s ⊎ IIC₁.P F s t
      qf₀ : (s : IIC₀.S C) (t : IIC₁.S F s) (p : IIC₀.P C s) → IIC₁.Q₀ G s (sf s t) p → IIC₁.Q₀ F s t p
      qf₁ : (s : IIC₀.S C) (t : IIC₁.S F s) (p : IIC₁.P G s (sf s t)) → case⊎′ (IIC₁.Q₀ F s t) (IIC₁.Q₁ F s t) (pf s t p) 


  ⟦_⟧₁ : {C : IIC₀} → IIC₁ C → (X : Fam) → ⟦ C ⟧₀ X → Set
  ⟦_⟧₁ {S₀ ◁₀ P₀ , Q₀} (S₁ ◁₁ P₁ , Q₁₀ , Q₁₁) (X , Y) (s , (f , g)) = 
    Σ[ t ∶ S₁ s ] Σ[ h ∶ (P₁ s t → X) ] 
                  ((p : P₀ s) → Q₁₀ s t p → Y (f p)) 
               × (((p : P₁ s t) → Q₁₁ s t p → Y (h p)))  


  IIC₁$† : {C : IIC₀} → (F G : IIC₁ C) → IIC₁[ F ⇒ G ]† → ∀ X (x : ⟦ C ⟧₀ X) → ⟦ F ⟧₁ X x → ⟦ G ⟧₁ X x
  IIC₁$† F G (morii₁† sf pf qf₀ qf₁) X (s , f , g) (t , h , i , j) = 
    sf s t , (λ p → case⊎′ f h (pf s t p)) , (λ p q → i p (qf₀ s t p q)) , foo
      where foo : (p : IIC₁.P G s (sf s t)) → IIC₁.Q₁ G s (sf s t) p → Fam.f X (case⊎′ f h (pf s t p))
            foo p q with qf₁ s t p 
            ...        | a with pf s t p
            ...               | inj₁ x = i x a
            ...               | inj₂ y = j y a


{-
  prf : (C D : IIC₀) (m : IIC₀[ C ⇒ D ]) (E : IIC₁ D) (X : Fam) (x : ⟦ C ⟧₀ X) → ⟦ compm C D m E ⟧₁ X x → ⟦ E ⟧₁ X (IIC₀$ C D m X x)
  prf (S ◁₀ P , Q) (S' ◁₀ P' , Q') (morii₀ sf pf qf) (T' ◁₁ P'₁ , Q'₁₀ , Q'₁₁)
      (X , Y) (s , f , g) (t , h , i , j) = t , h , (λ p q → i (pf s p) (p , (refl , q))) , j

  prf' : (C D : IIC₀) (m : IIC₀[ C ⇒ D ]) (E : IIC₁ D) (X : Fam) (x : ⟦ C ⟧₀ X) → ⟦ E ⟧₁ X (IIC₀$ C D m X x) → ⟦ compm C D m E ⟧₁ X x
  prf' (S ◁₀ P , Q) (S' ◁₀ P' , Q') (morii₀ sf pf qf) (T' ◁₁ P'₁ , Q'₁₀ , Q'₁₁)
      (X , Y) (s , f , g) (t , h , i , j) = t , h , (λ { p (p' , eq , q) → subst Y (cong f eq) (i p' q) }) , j

-}

{-

  IIC : Set 
  IIC = Σ[ C ∶ IIC₀ ] IIC₁ C

  ⟦_⟧ : IIC → Fam → Fam
  ⟦ C , D ⟧ F = ⟦ C ⟧₀ F , ⟦ D ⟧₁ F

  IIC[_⇒_] : IIC → IIC → Set
  IIC[ ((S₀ ◁₀ P₀ , Q₀) , (S₁ ◁₁ P₁ , Q₁₀ , Q₁₁)) ⇒ D ] = (s₀ : S₀) (s₁ : S₁ s₀) → ΣFam (⟦ D ⟧ (A s₀ s₁ , B s₀ s₁)) 
    where A : (s₀ : S₀) (s₁ : S₁ s₀) → Set ; A s₀ s₁ = P₀ s₀ ⊎ P₁ s₀ s₁  
          B : (s₀ : S₀) (s₁ : S₁ s₀) → A s₀ s₁ → Set 
          B s₀ s₁  = case⊎ (λ p₀ → Q₀ s₀ p₀ ⊎ Q₁₀ s₀ s₁ p₀)  (λ p₁ → Q₁₁ s₀ s₁ p₁)
          -- B s₀ s₁ (inj₂ p₁) = Q₁₁ s₀ s₁ p₁ 

  IIC$ : (F G : IIC) → IIC[ F ⇒ G ] → {X : Fam} → ΣFam (⟦ F ⟧ X) → ΣFam (⟦ G ⟧ X)
  IIC$ ((S₀ ◁₀ P₀ , Q₀) , (S₁ ◁₁ P₁ , Q₁₀ , Q₁₁)) ((S₀' ◁₀ P₀' , Q₀') , (S₁' ◁₁ P₁' , Q₁₀' , Q₁₁')) m {X , Y}  ((s₀ , (f , g))  , (s₁ , (h , (i , j)))) with m s₀ s₁
  ... | ((s₀' , (ff , gf)) , (s₁' , (hf , (if , jf)))) = (s₀' , ((λ p₀ → case⊎ {C = λ _ → X} f h (ff p₀)) , (λ p₀ q₀ → case⊎ {C = λ ffp₀ → Y (case⊎ f h ffp₀)} (λ pp → {!!} ) {!!} (ff p₀)))) , (s₁' , {!!})

  -}

  \end{code}

