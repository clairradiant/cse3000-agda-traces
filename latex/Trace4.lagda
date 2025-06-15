\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}

{-# OPTIONS --sized-types #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive; Substitutive)
open import Level using (zero)
open import Size
open import Codata.Sized.Thunk

open import nakata.Language

module latex.Trace4 where

\end{code}

\begin{code}
data Trace₄ (i : Size) : Set where
    tnil : State → Trace₄ i
    tcons : State 
        → Thunk Trace₄ i 
        → Trace₄ i
\end{code}

\begin{code}
data Bisim (i : Size) : Rel (Trace₄ ∞) Level.zero where
    tnil : ∀ {st} → Bisim i (tnil st) (tnil st)
    tcons : ∀ {st tr₁ tr₂} 
        → Thunk (λ s → Bisim s (force tr₁) (force tr₂)) i 
        → Bisim i (tcons st tr₁) (tcons st tr₂)
\end{code}



\end{document}