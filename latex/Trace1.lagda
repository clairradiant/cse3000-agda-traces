\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}

{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂) renaming (sym to eqSym; trans to eqTrans)
import Level using (zero)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Properties
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Sum
open import Function.Base using (case_of_)
open import Relation.Nullary using (contradiction)

open import nakata.Traces hiding (module Trace₁)
open import nakata.Language

module latex.Trace1 where


\end{code}

\begin{code}

data Trace₁ : Set where
    tnil : State → Trace₁
    tcons : State → ∞ Trace₁ → Trace₁

\end{code}

\begin{code}

data _≈_ : Rel Trace₁ Level.zero where
    tnil : ∀ {st} → (tnil st) ≈ (tnil st)
    tcons : ∀ {st tr₁ tr₂} 
        → ∞ (♭ tr₁ ≈ ♭ tr₂) 
        → (tcons st tr₁) ≈ (tcons st tr₂)

\end{code}

\begin{code}
mutual

    data exec : Stmt → State → Trace₁ → Set where
        execWhileLoop : 
            {c : Expr} {b : Stmt} 
            {st : State} (tr tr′ : Trace₁)
            → (isTrue (c st)) ≡ true 
            → execseq b (tcons st (♯ tnil st)) tr 
            → execseq (Swhile c b) tr tr′ 
            → exec (Swhile c b) st tr′

    data execseq : Stmt → Trace₁ → Trace₁ → Set where
        execseqNil : {st : State} {s : Stmt} {tr : Trace₁} 
            → exec s st tr 
            → execseq s (tnil st) tr
            
        execseqCons : {s : Stmt}
            (st : State) (tr tr′ : ∞ Trace₁) 
            → ∞ (execseq s (♭ tr) (♭ tr′)) 
            → execseq s (tcons st tr) (tcons st tr′)

\end{code}


\end{document}