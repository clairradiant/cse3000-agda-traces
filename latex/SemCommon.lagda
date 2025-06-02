\documentclass{article}

\usepackage{agda}

\begin{document}

\begin{code}

{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Codata.Musical.Notation
open import Data.Nat using (ℕ; zero; suc; _<?_)
open import Function.Base using (case_of_)
open import Data.Nat using (_+_)
open import Relation.Nullary using (contradiction)
open import Relation.Nullary.Decidable
open import Relation.Binary.Bundles using (Setoid)

open import Traces
open import Language


\end{code}

\begin{code}

data exec : Stmt → State → Trace₁ → Set where
    execWhileFalse : {c : Expr} {st : State} {tr : Trace₁} (b : Stmt)
        → isTrue (c st) ≡ false
        → tr ≈ (tcons st (♯ tnil st))
        → exec (Swhile c b) st tr

    execWhileLoop : {c : Expr} {b : Stmt} {st : State} (tr tr′ : Trace₁)
        → (isTrue (c st)) ≡ true 
        → execseq b (tcons st (♯ tnil st)) tr 
        → execseq (Swhile c b) tr tr′ 
        → exec (Swhile c b) st tr′

\end{code}

\begin{code}

data execseq : Stmt → Trace₁ → Trace₁ → Set where
    execseqNil : {st : State} {s : Stmt} {tr : Trace₁} 
        → exec s st tr 
        → execseq s (tnil st) tr
        
    execseqCons : {s : Stmt} (st : State) (tr tr′ : ∞ Trace₁) 
        → ∞ (execseq s (♭ tr) (♭ tr′)) 
        → execseq s (tcons st tr) (tcons st tr′)

\end{code}


\end{document}