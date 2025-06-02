\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}

{-# OPTIONS --guardedness --allow-incomplete-matches --allow-unsolved-metas #-}

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
open import Data.Nat

open import nakata.Traces
open import nakata.Language
open import nakata.BigRel2 hiding (execseqDeterministic₀; execWhileDeterministic₀; execWhileDeterministic₁)

open Trace₂

module latex.Pain where


\end{code}

\begin{code}

execseqDeterministic₀ : {s : Stmt} {tr₁ tr₂ tr₃ tr₄ : Trace₂} 
    → tr₁ ≈ tr₂ → execseq s tr₁ tr₃ → execseq s tr₂ tr₄ → tr₃ ≈ tr₄
execseqDeterministic₀ tr₁≈tr₂ exs₁ exs₂ ._≈_.p with (execseq.p exs₁) | execseq.p (exs₂)
... | rexecseqNil res₁ ex₁ | rexecseqNil res₂ ex₂ with _≈_.p tr₁≈tr₂
... | tnil? = {! tnil? !}
-- Remaining cases omitted for brevity

\end{code}


\end{document}