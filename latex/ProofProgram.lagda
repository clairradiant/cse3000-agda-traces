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
open import Data.Nat

open import nakata.Traces
open import nakata.Language
open import nakata.BigRel hiding (execDeterministic)

open exloop hiding (exloopincrementing; incrementingFrom; incrementingtrace; increasing; incrementingAlwaysIncrements)
open Trace₁

module latex.ProofProgram where


\end{code}

\begin{code}
incrementingFrom : State → Trace₁
incrementingFrom st = tcons st (♯ tcons st (♯ (incrementingFrom (next st))))

incrementingtrace : Trace₁
incrementingtrace = incrementingFrom startState
\end{code}
\begin{code}
exloopincrementing : exec (Swhile (λ _ → 1) (Sassign 0 add1)) startState incrementingtrace
exloopincrementing = forever startState
    where
        forever : (st : State) → exec (Swhile (λ _ → 1) (Sassign 0 add1)) st (incrementingFrom st)
        forever st = execWhileLoop 
            (tcons st (♯ (tcons st (♯ (tnil (update 0 (add1 st) st)))))) 
            _ 
            _≡_.refl 
            (execseqCons st _ _ (♯ execseqNil (execAssign (tcons (♯ tnil)))))
            (execseqCons st _ _ (♯ (execseqCons st _ _ (♯ (execseqNil (forever (next st)))))))
\end{code}

\begin{code}

postulate
    trace : Trace₁
    program : Stmt
    fromState : State
    proof : exec program fromState trace

\end{code}

\begin{code}
data increasing : Id → Val → Trace₁ → Set where
    increasingCons : {id : Id} {v : Val} {st : State} {tr tr₁ : Trace₁} 
        → st id ≡ v 
        → tr₁ ≈ tcons st (♯ (tcons st (♯ tr))) 
        → ∞ (increasing id (suc v) tr) 
        → increasing id v tr₁
\end{code}

\begin{code}
incrementingAlwaysIncrements : increasing 0 0 incrementingtrace
incrementingAlwaysIncrements = forever refl
    where
        open Setoid setoid₁ using () renaming (refl to ≈refl)
        open import Relation.Binary.PropositionalEquality
        open ≡-Reasoning

        lem₁ : {x : ℕ} → x + 1 ≡ suc x
        lem₁ {zero} = refl
        lem₁ {suc x} = begin
            suc (x + 1)
            ≡⟨⟩
            suc x + suc zero
            ≡⟨ cong suc (lem₁) ⟩
            suc (suc x)
            ∎

        lem₂ : {v : Val} → (st : State) → (st 0 ≡ v) → next st 0 ≡ suc v
        lem₂ {v} st x = begin
            next st 0
            ≡⟨⟩
            st 0 + 1
            ≡⟨ cong (_+ 1) x ⟩
            v + 1
            ≡⟨ lem₁ ⟩
            suc v
            ∎

        forever : {st : State} {v : Val} → (st 0 ≡ v) → increasing 0 v (incrementingFrom st)
        forever {st} x = increasingCons x (tcons (♯ (tcons (♯ ≈refl)))) (♯ forever (lem₂ st x))
\end{code}

\begin{code}
postulate
    execDeterministic : {s : Stmt} {st : State} {tr₁ tr₂ : Trace₁} 
        → exec s st tr₁ 
        → exec s st tr₂ 
        → tr₁ ≈ tr₂
\end{code}
\end{document}