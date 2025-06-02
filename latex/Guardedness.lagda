\begin{document}
\begin{code}

{-# OPTIONS --guardedness --no-termination-check #-}

open import Codata.Musical.Notation
open import Data.Nat

module latex.Guardedness where

\end{code}
\begin{code}

mutual
    data Coℕr : Set where
        zero : Coℕr
        suc : Coℕ → Coℕr

    record Coℕ : Set where
        coinductive
        constructor mkCoℕ
        field
            out : Coℕr
\end{code}
\begin{code}
open Coℕ
\end{code}
\begin{code}
id : ∀ {a} {A : Set a} → A → A
id x = x 

inf : Coℕ
inf .out = suc inf

infBad : Coℕ
infBad .out = id (suc infBad)
\end{code}
\end{document}