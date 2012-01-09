%if style == code

\begin{code}

module note where

open import Function
open import Level
open import Lib




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

FuncFamFam₀ : Set₁
FuncFamFam₀ = FuncFamSet

module Fake where

  open FuncFamSet

  record FuncFamFam₁ (F : FuncFamFam₀) : Set₁ where
    field
      obj₁ : (X : Fam) → obj₀ F X → Set
      mor₁ : ∀ {X Y} (m : Fam X ⇒ Y) (x : obj₀ F X) → 
               obj₁ X x → obj₁ Y (mor₀ F m x) 
      idlaw₁ : ∀ {X} (x : obj₀ F X) → mor₁ {X} {X} (idFam {X}) x ≅ id {A = obj₁ X x}
      complaw₁ : ∀ {X Y Z} {m : Fam Y ⇒ Z} {n : Fam X ⇒ Y} (x : obj₀ F X)→ 
                 mor₁ {X} {Z} (compFam {X} {Y} {Z} m n) x 
                     ≅ (mor₁ {Y} {Z} m (mor₀ F n x) ∘ mor₁ n x) 

open Fake public

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
  field 
    sf : ContFamSet.S F → ContFamSet.S G
    pf : (s : ContFamSet.S F) → Fam (ContFamSet.P G (sf s)) ⇒ (ContFamSet.P F s)

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

\end{code}

The functor |⟦ S ◁ P , Q ⟧FamFam₀ (X , Y)| is a container for |X|s denoted by |P| positions, and |Y|s  denoted by |Q| positions. Notice that since |Y| is an |X| indexed family, the |Q| positions are indexed in turn by |P| positions.

\section{The Second bit}

Given some Fam-Set Container |S ◁ (P , Q)| we want to build a second |(X , Y)| container which repesents a family indexed by a value |(s , f) : ⟦ S ◁ (P , Q) ⟧FamFam₀ (X , Y)|. Again this will have positions for both |X|s and |Y|s, but this time the |Y|s can either be indexed by |X|s denoted by old |P| positions, or by a`new' position in the container we are constructing.

\begin{code}

record ContFamFam₁ (F₀ : ContFamFam₀) : Set₁ where
  constructor _◁_,_,_
  field
    T : ContFamFam₀.S F₀ → Set
    P₁ : (s : ContFamFam₀.S F₀) →  T s → Set
    Q₁₀ : (s : ContFamFam₀.S F₀) → T s → ContFamFam₀.P F₀ s → Set
    Q₁₁ : (s : ContFamFam₀.S F₀) (t : T s) → P₁ s t → Set

\end{code}

\question{Can we make this look more natural?}

\end{document}
