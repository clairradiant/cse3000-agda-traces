\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}

{-# OPTIONS --guardedness --allow-incomplete-matches --allow-unsolved-metas #-}

open import Codata.Musical.Notation
open import Codata.Musical.Conat hiding (_≈_)
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
open import Data.Nat

open import work.MusicalTraces
open import work.Language

open Trace₁

module latex.MusicLeft where


\end{code}

\begin{code}
data _≈bad_ : Coℕ → Coℕ → Set where
  zero : zero ≈bad zero
  suc : {n m : Coℕ} 
    → ∞ (n ≈bad m) 
    → suc (♯ n) ≈bad suc (♯ m)

data _≈good_ : Coℕ → Coℕ → Set where
  zero : zero ≈good zero
  suc : {n m : ∞ Coℕ} 
    → ∞ (♭ n ≈good ♭ m) 
    → suc n ≈good suc m
\end{code}

\begin{code}
data exec : Stmt → State → Trace₁ → Set where
  execWhileFalse : 
    {c : Expr} {st : State} {tr : Trace₁} (b : Stmt)
    → isTrue (c st) ≡ false
    → tr ≈ (tcons st (♯ tnil st))
    → exec (Swhile c b) st tr
\end{code}


\end{document}