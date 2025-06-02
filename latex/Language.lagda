\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}

{-# OPTIONS --guardedness #-}

open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary.Decidable
open import Data.Nat
open import Data.Bool using (Bool)
open import Function.Base using (case_of_)

module latex.Language where

\end{code}

\begin{code}

Id : Set
Id = ℕ

Val : Set
Val = ℕ

State : Set
State = Id → Val

Expr : Set
Expr = State → Val

\end{code}



\begin{code}
data Stmt : Set where
    Sskip : Stmt
    Sassign : Id → Expr → Stmt
    Sseq : Stmt → Stmt → Stmt
    Sifthenelse : Expr → Stmt → Stmt → Stmt
    Swhile : Expr → Stmt → Stmt
\end{code}

\begin{code}
loop : Stmt
loop = Swhile 
    (λ _ → 1) 
    (Sassign 0 (λ st → st 0 + 1))
\end{code}


\end{document}