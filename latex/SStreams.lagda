\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}

{-# OPTIONS --sized-types #-}

open import Size
open import Level
open import Data.Nat
open import Data.List

module latex.SStreams where

private variable
  a : Level

\end{code}

\begin{code}
record Thunk {ℓ} (F : SizedSet ℓ) (i : Size) : Set ℓ where
  coinductive
  field force : {j : Size< i} → F j
open Thunk

data Stream (A : Set a) (i : Size) : Set a where
  _∷_ : A → Thunk (Stream A) i → Stream A i
\end{code}

\begin{code}
zeroesBad : Stream ℕ ∞
zeroesBad = 0 ∷ (λ where .force → zeroesBad)

zeroes : ∀ {i} → Stream ℕ i
zeroes = 0 ∷ (λ where .force → zeroes)
\end{code}

\begin{code}
myList : List ℕ
myList = 1 ∷ 2 ∷ []
\end{code}



\end{document}