\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}

{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Level
open import Data.Nat

module latex.MStreams where

private variable
  a : Level

\end{code}

\begin{code}

data Stream (A : Set a) : Set a where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

\end{code}

\begin{code}

zeroes : Stream ℕ
zeroes = 0 ∷ ♯ zeroes

\end{code}


\end{document}