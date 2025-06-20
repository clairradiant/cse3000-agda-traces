\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}

{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Level
open import Data.Nat

module latex.GStreams where

private variable
  a : Level

\end{code}

\begin{code}

record Stream (A : Set a) : Set a where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

\end{code}

\begin{code}

zeroes : Stream ℕ
zeroes .head = 0
zeroes .tail = zeroes

\end{code}


\end{document}