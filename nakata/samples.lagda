\documentclass{article}

\usepackage{amsmath}
\usepackage{amssymb}

\usepackage{agda}
\usepackage[utf8]{inputenc}
\usepackage{newunicodechar}

\newunicodechar{ℕ}{\ensuremath{\mathnormal\mathbb{N}}}
\newunicodechar{∞}{\ensuremath{\mathnormal\infty}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{₃}{\ensuremath{_3}}
\newunicodechar{♯}{\ensuremath{\mathnormal\sharp}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{≈}{\ensuremath{\mathnormal\approx}}

\begin{document}

\begin{code}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Language
open import Traces
open import Codata.Musical.Notation
open import Relation.Binary.PropositionalEquality using (_≡_)
open import BigRel hiding (execDeterministic)
open exloop hiding (exloopincrementing)
open Trace₁

\end{code}

\begin{code}
exloopincrementing : exec (Swhile (λ _ → 1) (Sassign 0 add1)) startState incrementingtrace
exloopincrementing = t startState
    where
        t : (st : State) → exec (Swhile (λ _ → 1) (Sassign 0 add1)) st (incrementingFrom st)
        t st = execWhileLoop 
            (tcons st (♯ (tcons st (♯ (tnil (update 0 (add1 st) st)))))) 
            _ 
            _≡_.refl 
            (execseqCons st _ _ (♯ execseqNil (execAssign (tcons (♯ tnil)))))
            (execseqCons st _ _ (♯ (execseqCons st _ _ (♯ (execseqNil (t (next st)))))))
\end{code}

\begin{code}
execDeterministic : {s : Stmt} {st : State} {tr₁ tr₂ : Trace₁} 
        → exec s st tr₁ 
        → exec s st tr₂ 
        → tr₁ ≈ tr₂
\end{code}

\begin{code}
-- Shut agda up about lack of implementation
execDeterministic = {!   !}
\end{code}


\end{document}