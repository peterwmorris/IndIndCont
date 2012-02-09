%if style == code

\begin{code}

module note where

open import Function
open import Level
open import Lib
open import Data.Sum


\end{code}

%endif

\documentclass[a4paper]{article}
\usepackage{url}
\usepackage{times}
\usepackage{amsmath}
\usepackage{xypic}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{stmaryrd}
\usepackage{color}

%include lhs2TeX.fmt
%include agda.fmt

%format λ = "\lambda"
%format : = "\in"
%format α = "\alpha"

%format Σ* = "(\!"
%format ∶ = :
%format *Σ = "\!)" ×

%format ⇒ = "\Rightarrow" 
%format Fam_⇒_ = Fam  _ ⇒ _ 

%format ◁ = "\lhd"
%format _◁_ = _ ◁ _

%format ⟦ = "\llbracket"
%format ⟧ = "\rrbracket"

%format ⟦_⟧FamSet⇒ = ⟦ _ ⟧ FamSet ⇒
%format ⟦_⟧FamSet = ⟦ _ ⟧ FamSet

%format ⟧FamSet = ⟧ FamSet
%format ⟧FamSet⇒ = ⟧ FamSet ⇒ 

%format proj = "\pi"
%format proj₁ = proj "_{0}"
%format proj₂ = proj "_{1}"

%format ContFamSet_⇒_ = ContFamSet  _ ⇒ _ 

%format dotdotdot = "\ldots"

\begin{document}

\newcounter{theorem}

\newcommand{\question}[1]{\textcolor{red}{#1}}

\title{Tupperware}
\author{Thorsten Altenkirch 
   \and Peter Morris}
\date{\today}

\maketitle

\begin{abstract}

Abstract

\end{abstract}

We want to model simple inductive-inductive families such as Fredrik's 
buildings:

\begin{code}

data Platform : Set 

data Building : Platform → Set

data Platform where
  ground : Platform
  extend : ∀ {p} → Building p → Platform

data Building where 
  atop : ∀ {p} → Building p
  below : ∀ {p} {b : Building p} → Building (extend b) 

\end{code}

or this inductive presentaion of the fresh lists:

\begin{code}

module Fresh (A : Set) (_=/=_ : A → A → Set) where

  data #List  : Set 

  data _#_ : #List → A → Set

  data #List where
    nil : #List
    snoc : (as : #List) (a : A) → as # a → #List 
  
  data _#_ where
    nil : ∀ {a} → nil # a
    snoc : ∀ {as a p b} → as # b → a =/= b → (snoc as a p) # b   

\end{code}

We wish to construct these types as the fixed point of an endofunctor on the category |Fam|:

\begin{code}

Fam : Set₁
Fam = Σ* A ∶ Set *Σ (A → Set)

Fam_⇒_ : Fam → Fam → Set
Fam (A , f) ⇒ (B , g)  = Σ* m ∶ (A → B) *Σ ((a : A) → f a → (g (m a)))

idFam : ∀ {X} → Fam X ⇒ X 
idFam = id , (λ _ → id)

compFam : ∀ {X Y Z} → Fam Y ⇒ Z  → Fam X ⇒ Y  → Fam X ⇒ Z 
compFam (f₀ , f₁) (g₀ , g₁) = (f₀ ∘ g₀) , (λ a → f₁ (g₀ a) ∘ g₁ a) 

\end{code}

An endo-functor on this category is:


\begin{code}

record FuncFamFam : Set₁ where
  field
    obj : Fam → Fam
    mor : ∀ {X Y} → Fam X ⇒ Y → Fam (obj X) ⇒ (obj Y)
    idlaw : ∀ {X} → mor (idFam {X}) ≡ idFam {obj X}
    complaw : ∀ {X Y Z} {m : Fam Y ⇒ Z} {n : Fam X ⇒ Y} → 
                mor {X} {Z} (compFam {X} {Y} {Z} m n) 
                  ≡ compFam {obj X} {obj Y} {obj Z} (mor m) (mor n)

\end{code}

By expanding the definition of |Fam| in the codomain of this functor, we get this definition:

\begin{code}

record FuncFamFam' : Set₁ where
  field
    obj₀ : Fam → Set
    obj₁ : (X : Fam) → obj₀ X → Set
    mor₀ : ∀ {X Y} → Fam X ⇒ Y → (obj₀ X) → (obj₀ Y)
    mor₁ : ∀ {X Y} (m : Fam X ⇒ Y) (x : obj₀ X) → obj₁ X x → obj₁ Y (mor₀ m x)
    idlaw₀ : ∀ {X} → mor₀ (idFam {X}) ≡ id
    idlaw₁ : ∀ {X} (x : obj₀ X) → mor₁ {X} {X} (idFam {X}) x ≅ id {A = obj₁ X x}
    complaw₀ : ∀ {X Y Z} {m : Fam Y ⇒ Z} {n : Fam X ⇒ Y} → 
                 mor₀ {X} {Z} (compFam {X} {Y} {Z} m n) ≡ (mor₀ m ∘ mor₀ n)
    complaw₁ : ∀ {X Y Z} {m : Fam Y ⇒ Z} {n : Fam X ⇒ Y} (x : obj₀ X)→ 
                mor₁ {X} {Z} (compFam {X} {Y} {Z} m n) x 
                  ≅ (mor₁ {Y} {Z} m (mor₀ n x) ∘ mor₁ n x) 

\end{code}

Note that the quadruple |(obj₀ , mor₀ , idlaw₀ , complaw₀)| constitutes a functor from |Fam| to |Set|. The second parts for something more complicated \question{What do we call this?} but we'll deal with that complexity later. For the moment, let us tease out these two parts, and deal with each seperately. That is to say we'll treat a functor from |Fam| to |Fam| as a pair of a |FuncFamSet| and a |FuncFamFam₁|:

\begin{code}

record FuncFamSet : Set₁ where
  field
    obj₀ : Fam → Set
    mor₀ : ∀ {X Y} → Fam X ⇒ Y → (obj₀ X) → (obj₀ Y)
    idlaw₀ : ∀ {X} → mor₀ (idFam {X}) ≡ id
    complaw₀ : ∀ {X Y Z} {m : Fam Y ⇒ Z} {n : Fam X ⇒ Y} → 
                 mor₀ {X} {Z} (compFam {X} {Y} {Z} m n) ≡ (mor₀ m ∘ mor₀ n)

record NatFamSet (F G : FuncFamSet) : Set₁ where
  open module F = FuncFamSet F
  open module G = FuncFamSet G
  field
    α : ∀ {X} → F.obj₀ X → G.obj₀ X
    nat : ∀ {X Y} (m : Fam X ⇒ Y) (x : F.obj₀ X) → 
            (G.mor₀ {X} {Y} m (α {X} x)) ≡ (α {Y} (F.mor₀ {X} {Y} m x)) 

FuncFamFam₀ : Set₁
FuncFamFam₀ = FuncFamSet


record FuncFamFam₁ (F : FuncFamFam₀) : Set₁ where
  open module F = FuncFamSet F
  field
    obj₁ : (X : Fam) → F.obj₀ X → Set
    mor₁ : ∀ {X Y} (m : Fam X ⇒ Y) (x : F.obj₀ X) → 
             obj₁ X x → obj₁ Y (F.mor₀ m x) 
    idlaw₁ : ∀ {X} (x : F.obj₀ X) → mor₁ {X} {X} (idFam {X}) x ≅ id {A = obj₁ X x}
    complaw₁ : ∀ {X Y Z} {m : Fam Y ⇒ Z} {n : Fam X ⇒ Y} (x : F.obj₀ X)→ 
               mor₁ {X} {Z} (compFam {X} {Y} {Z} m n) x 
                   ≅ (mor₁ {Y} {Z} m (F.mor₀ n x) ∘ mor₁ n x) 

\end{code}

\section{Functors |Fam| to |Set|}

We build these functors by simply considering what containers with a {\em Family} of positions are:

\begin{code}

record ContFamSet : Set₁ where
  constructor _◁_
  field
    S : Set
    P : S → Fam

⟦_⟧FamSet : ContFamSet → Fam → Set
⟦ S ◁ P ⟧FamSet X = Σ* s ∶ S *Σ Fam P s ⇒  X 

⟦_⟧FamSet⇒ : (F : ContFamSet) → ∀ {X Y} → Fam X ⇒ Y  → ⟦ F ⟧FamSet X → ⟦ F ⟧FamSet Y
⟦ S ◁ P ⟧FamSet⇒ {X} {Y} m (s , f) = s , compFam {P s} {X} {Y} m f 

\end{code}

ContFamSet forms a category in exactly the same way that Cont itself does, indeed we can reuse the same constructions to establish that ContFamSet is a full and faithful sub-category of |[Fam , Set]|:

\begin{code}

record ContFamSet_⇒_ (F G : ContFamSet) : Set where
  constructor _◁_
  open module F = ContFamSet F
  open module G = ContFamSet G
  field 
    sf : F.S → G.S
    pf : (s : F.S) → Fam (G.P (sf s)) ⇒ (F.P s)

CFS$ : ∀ {F G} → (ContFamSet F ⇒ G)  → ∀ {X} → ⟦ F ⟧FamSet X → ⟦ G ⟧FamSet X
CFS$ (sf ◁ pf) {X} (s , f) = sf s , compFam {_} {_} {X} f (pf s)

CFSq : ∀ {F G} → (∀ {X} → ⟦ F ⟧FamSet X → ⟦ G ⟧FamSet X) → ContFamSet F ⇒ G 
CFSq {S ◁ P} {G} α = (λ s → proj₁ (q s) ) ◁ (λ s → proj₂ (q s))
  where q : (s : S) → ⟦ G ⟧FamSet (P s)
        q s = α {P s} (s , idFam)

\end{code}

Before we expand on the second part of the endofunctor, let us find an intuition for what is going on here. First, let us alter the definition of ContFamSet a bit, by expanding |Fam|:

\begin{code}

record ContFamFam₀ : Set₁ where
  constructor _◁_,_
  field
    S : Set
    P : S → Set
    Q : (s : S) → P s → Set

⟦_⟧FamFam₀ : ContFamFam₀ → Fam → Set
⟦ S ◁ P , Q ⟧FamFam₀ (X , Y) = Σ* s ∶ S *Σ Σ* f ∶ (P s → X) *Σ ((p : P s) → Q s p → Y (f p)) 

record ContFamFam₀_⇒_ (F G : ContFamFam₀) : Set where
  constructor _◁_,_
  open module F = ContFamFam₀ F
  open module G = ContFamFam₀ G
  field 
    sf : F.S → G.S
    pf : (s : F.S) → (G.P (sf s)) → (F.P s)
    qf : (s : F.S) (p : G.P (sf s)) → G.Q (sf s) p → F.Q s (pf s p)
 
CFF₀$ : ∀ {F G} → (ContFamFam₀ F ⇒ G)  → ∀ {X} → ⟦ F ⟧FamFam₀ X → ⟦ G ⟧FamFam₀ X
CFF₀$ (sf ◁ pf , qf) {X} (s , (f , g)) = sf s , ((f ∘ pf s) , (λ p → g (pf s p) ∘ qf s p))

CFF₀q : ∀ {F G} → (∀ {X} → ⟦ F ⟧FamFam₀ X → ⟦ G ⟧FamFam₀ X) → ContFamFam₀ F ⇒ G 
CFF₀q {S ◁ P , Q} {G} α = (λ s → proj₁ (q s) ) ◁ (λ s → proj₁ (proj₂ (q s))) , (λ s → proj₂ (proj₂ (q s)))
  where q : (s : S) → ⟦ G ⟧FamFam₀ (P s , Q s)
        q s = α {P s , Q s} (s , (id , λ _ → id))



\end{code}

The functor |⟦ S ◁ P , Q ⟧FamFam₀ (X , Y)| is a container for |X|s denoted by |P| positions, and |Y|s  denoted by |Q| positions. Notice that since |Y| is an |X| indexed family, the |Q| positions are indexed in turn by |P| positions.

\section{The Second bit}

Given some Fam-Set Container |S ◁ (P , Q)| we want to build a second |(X , Y)| container which repesents a family indexed by a value |(s , f) : ⟦ S ◁ (P , Q) ⟧FamFam₀ (X , Y)|. Again this will have positions for both |X|s and |Y|s, but this time the |Y|s can either be indexed by |X|s denoted by old |P| positions, or by a`new' position in the container we are constructing.

%format _◁_/_/_ = _ ◁ _ / _ / _

\begin{code}

record ContFamFam₁ (F₀ : ContFamFam₀) : Set₁ where
  constructor _◁_/_/_
  open module F₀ = ContFamFam₀ F₀
  field
    T : F₀.S → Set
    P₁ : (s : F₀.S) →  T s → Set
    Q₁₀ : (s : F₀.S) → T s → F₀.P s → Set
    Q₁₁ : (s : F₀.S) (t : T s) → P₁ s t → Set

⟦_⟧FamFam₁ : ∀ {F₀} → ContFamFam₁ F₀ → (X : Fam) → ⟦ F₀ ⟧FamFam₀ X → Set
⟦_⟧FamFam₁ {S ◁ P₀ , Q₀} (T ◁ P₁ / Q₁₀ / Q₁₁) (X , Y) (s , (pf₀ , qf₉)) = 
  Σ* t ∶ T s *Σ 
   Σ* pf₁ ∶ (P₁ s t  → X) *Σ 
    ((p₀ : P₀ s) → Q₁₀ s t p₀ → Y (pf₀ p₀)) × (
     ((p₁ : P₁ s t) → Q₁₁ s t p₁ → Y (pf₁ p₁))) 

\end{code}

\question{Can we make this look more natural?}

\subsection{morphisms}

We note that, in the functor case we need only consider the equivalent of natural transformations in the uniform case (that is the case where the domain and co-domain are indexed by the same FuncFamSet):

\begin{code}

FuncFamFam₁_⇒_ : ∀ {F₀} (F₁ G₁ : FuncFamFam₁ F₀) → Set₁
FuncFamFam₁_⇒_ {F₀} F₁ G₁ = 
    (X : Fam) (x : F₀.obj₀ X) → F₁.obj₁ X x → G₁.obj₁ X x 
  where open module F₀ = FuncFamSet F₀
        open module F₁ = FuncFamFam₁ F₁
        open module G₁ = FuncFamFam₁ F₁
        

\end{code}

We build a `change of base' combinator, that precomposes a |FunFamFam₁ G₀| with a natural trasformation in |NatFamSet F₀ G₀|, thus changing its index type.

%format m.α = m. α

\begin{code}

FuncFamFamcompmor : ∀  {F₀ G₀} → FuncFamFam₁ G₀ → 
                       (NatFamSet F₀ G₀) → FuncFamFam₁ F₀
FuncFamFamcompmor G₁ m = 
  record {  obj₁ = λ X x → G₁.obj₁ X (m.α x)
         ;  mor₁ = λ  {X} {Y} n x f → 
                      subst (G₁.obj₁ Y) (m.nat n x) (G₁.mor₁ {X} {Y} n (m.α x) f)  
         ;  idlaw₁ = dotdotdot
         ;  complaw₁ = dotdotdot 
         }
  where open module G₁ = FuncFamFam₁ G₁
        open module m = NatFamSet m
          

\end{code}

The more general case of natural transformations between these indexed psuedo-functors indexed by different functors is dealt with by this composition. Note that these |NatFamFam₁| transformations are idexed by |NatFamFam₀| transformations:

\begin{code}

FuncFamFam₁'_⇒_ : ∀ {F₀ G₀}  (F₁ : FuncFamFam₁ F₀) 
                             (G₁ : FuncFamFam₁ G₀) → 
                             NatFamSet F₀ G₀ → Set₁
FuncFamFam₁' F₁ ⇒ G₁ = 
  λ m → FuncFamFam₁ F₁ ⇒ (FuncFamFamcompmor G₁ m)

\end{code}

We can lift this change of base operation to the container world:

\begin{code}

ContFamFamcompmor : ∀   {F₀ G₀} → ContFamFam₁ G₀ → 
                        (ContFamFam₀ F₀ ⇒ G₀) → ContFamFam₁ F₀
ContFamFamcompmor {F₀} {S′ ◁ P₀′ , Q₀′} 
                    (T ◁ P₁ / Q₁₀ / Q₁₁) (sf ◁ pf , qf) = 
  (T ∘ sf)  ◁ (P₁ ∘ sf) 
            / (λ s t p → Σ* p' ∶ (P₀′ (sf s)) *Σ 
                            ((pf s p' ≅ p) × Q₁₀ (sf s) t p')) 
            / (Q₁₁ ∘ sf)
  

\end{code}

Then, we define the uniform morphisms:


\begin{code}

record ContFamFam₁_⇒_ {F₀} 
         (F₁ G₁ : ContFamFam₁ F₀) : Set where
  constructor _◁_/_/_
  open module F = ContFamFam₀ F₀
  open module F₁ = ContFamFam₁ F₁
  open module G₁ = ContFamFam₁ G₁
  field
    tf : (s : F.S) → F₁.T s → G₁.T s 
    pf : (s : F.S) (t : F₁.T s) → 
            G₁.P₁ s (tf s t) → F.P s ⊎ F₁.P₁ s t 
    qf₀ : (s : F.S) (t : F₁.T s) (p₀ : F.P s) → 
            G₁.Q₁₀ s (tf s t) p₀ → F.Q s p₀ ⊎ F₁.Q₁₀ s t p₀  
    qf₁ : (s : F.S) (t : F₁.T s) (p₁ : G₁.P₁ s (tf s t)) → 
            G₁.Q₁₁ s (tf s t) p₁ → 
              [  (λ p₀ → F.Q s p₀ ⊎ F₁.Q₁₀ s t p₀) 
              ,  F₁.Q₁₁ s t ]′ (pf s t p₁)

ContFamFam₁$ : ∀  {F₀} {F₁ G₁ : ContFamFam₁ F₀} → 
                  ContFamFam₁ F₁ ⇒ G₁ → 
                  ∀ {X} x → ⟦ F₁ ⟧FamFam₁ X x → ⟦ G₁ ⟧FamFam₁ X x
ContFamFam₁$ {F₀} {F₁} {G₁} 
               (tf ◁ pf₁ / qf₁₀ / qf₁₁) {X , Y} (s , (f₀ , g₀)) 
               (t , (f₁ , (g₁₀ , g₁₁)))  
  =     tf s t 
     ,  ((λ p₁ → [ f₀ , f₁ ]′ (pf₁ s t p₁)) 
     ,  (  ( λ p₀ q₁₀ → [ g₀ p₀ , g₁₀ p₀ ]′ (qf₁₀ s t p₀ q₁₀)) 
           , (λ p₁ → foo p₁ (pf₁ s t p₁) refl )))  
  where open ContFamFam₁ G₁ 
        foo :  (p₁ : P₁ s (tf s t)) 
               (x : ContFamFam₀.P F₀ s ⊎ ContFamFam₁.P₁ F₁ s t) → 
               x ≡ pf₁ s t p₁ → Q₁₁ s (tf s t) p₁ → Y ([ f₀ , f₁ ]′ x) 
        foo p x eq q with qf₁₁ s t p q
        foo p x eq q | qfq with pf₁ s t p 
        foo p (inj₁ y) refl q | qfq | ._ =  [ g₀ y , g₁₀ y ]′ qfq 
        foo p (inj₂ y) refl q | qfq | ._ = g₁₁ y qfq

ContFamFam₁q : ∀  {F₀} {F₁ G₁ : ContFamFam₁ F₀}  → 
                  (∀ {X} x → ⟦ F₁ ⟧FamFam₁ X x → ⟦ G₁ ⟧FamFam₁ X x) → 
                  ContFamFam₁ F₁ ⇒ G₁
ContFamFam₁q {F₀} {F₁} {G₁} m 
  =        (λ s t → proj₁ (q s t)) 
        ◁  (λ s t → proj₁ (proj₂ (q s t))) 
        /  (λ s t → proj₁ (proj₂ (proj₂ (q s t))))  
        /  (λ s t → proj₂ (proj₂ (proj₂ (q s t))))
  where open ContFamFam₀ F₀
        open ContFamFam₁ F₁
        q :  (s : S) (t : T s) → 
             ⟦ G₁ ⟧FamFam₁  (  (P s ⊎ P₁ s t) 
                            ,  [ (λ p₀ → Q s p₀ ⊎ Q₁₀ s t p₀) 
                            ,  Q₁₁ s t ])  
                ((s , (inj₁ , (λ p → inj₁))))
        q s t = m {(P s ⊎ P₁ s t) , [ (λ p₀ → Q s p₀ ⊎ Q₁₀ s t p₀) , Q₁₁ s t ]}
                  (((s , (inj₁ , (λ p → inj₁))))) (t , (inj₂ , ((λ p₀ → inj₂) , (λ p₁ → id))))

\end{code}

Effectively the morphisms for |ContFamFam₁| between |F₁| and |G₁| are iso 

%if style == newcode

\begin{code}

{-

\end{code}

%endif

\begin{code}

(s : S) (t : T s) → 
   ⟦ G₁ ⟧  (  (P s ⊎ P₁ s t) 
           ,  [ (λ p₀ → Q s p₀ ⊎ Q₁₀ s t p₀) , Q₁₁ s t]) 
      (s , (inj₁ , (\ _ → inj₁)))|

\end{code}

%if style == newcode

\begin{code}

-}

\end{code}

%endif

\end{document}
