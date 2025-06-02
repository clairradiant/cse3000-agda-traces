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

open import nakata.Traces hiding (module Trace₂)
open import nakata.Language

module latex.Trace2 where


\end{code}

\begin{code}

mutual
    data rTrace₂ : Set where
        tnil : State → rTrace₂
        tcons : State → Trace₂ → rTrace₂

    record Trace₂ : Set where
        coinductive
        constructor mkTr
        field
            out : rTrace₂

\end{code}

\begin{code}
open Trace₂
\end{code}

\begin{code}

mutual
    data _r≈_ : Rel rTrace₂ Level.zero where
        tnil : ∀ {st} 
            → (tnil st) r≈ (tnil st)
        tcons : ∀ {st tr₁ tr₂} → tr₁ ≈ tr₂ 
            → (tcons st tr₁) r≈ (tcons st tr₂)

    record _≈_ (tr₁ tr₂ : Trace₂) : Set where
        coinductive
        constructor mkBisim
        field
            p : (out tr₁) r≈ (out tr₂)

\end{code}


\end{document}