{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Codata.Musical.Notation
open import Data.Nat using (ℕ; zero; suc)
open import Function.Base using (case_of_)
open import Data.Nat using (_+_)
open import Relation.Nullary using (contradiction)
open import Relation.Binary.Bundles using (Setoid)

open import Traces
open import Language

module BigRel where
    append : Trace₁ → Trace₁ → Trace₁
    append (tnil x) t₂ = tcons x (♯ t₂)
    append (tcons x t) t₂ = tcons x (♯ append (♭ t) t₂)

    -- unwind : Trace₁ → State
    -- unwind (tnil st) = st
    -- unwind (tcons st t) = unwind (♭ t)

    mutual
        data exec : (s : Stmt) → (st : State) → (tr : Trace₁) → Set where
            execSkip : ∀ (st) 
                → exec Sskip st (tnil st)

            execAssign : ∀ (id) (a) (st) (tr)
                → tr ≈ (tcons st (♯ tnil (update id (a st) st)))
                → exec (Sassign id a) st tr

            execSeq : (s₁ s₂ : Stmt) (st : State) (tr tr′ : Trace₁) 
                → exec s₁ st tr 
                → execseq s₂ tr tr′ 
                → exec (Sseq s₁ s₂) st tr′

            execIfThenElseTrue : (c : Expr) (t e : Stmt) (st : State) (tr : Trace₁) 
                → isTrue (c st) ≡ true 
                → execseq t (tcons st (♯ tnil st)) tr 
                → exec (Sifthenelse c t e) st tr

            execIfThenElseFalse : (c : Expr) (t e : Stmt) (st : State) (tr : Trace₁) 
                → isTrue (c st) ≡ false 
                → execseq e (tcons st (♯ tnil st)) tr 
                → exec (Sifthenelse c t e) st tr

            execWhileFalse : (c : Expr) (b : Stmt) (st : State) (tr : Trace₁)
                → isTrue (c st) ≡ false
                → tr ≈ (tcons st (♯ tcons st (♯ tnil st)))
                → exec (Swhile c b) st tr

            execWhileLoop : (c : Expr) (b : Stmt) (st : State) (tr tr′ : Trace₁) 
                → (isTrue (c st)) ≡ true 
                → execseq b (tcons st (♯ tnil st)) tr 
                → execseq (Swhile c b) tr tr′ 
                → exec (Swhile c b) st tr′

        data execseq : Stmt → Trace₁ → Trace₁ → Set where
            execseqNil : (st : State) (s : Stmt) (tr : Trace₁) 
                → exec s st tr 
                → execseq s (tnil st) tr
                
            execseqCons : (st : State) (s : Stmt) (tr tr′ : ∞ Trace₁) 
                → execseq s (♭ tr) (♭ tr′) 
                → execseq s (tcons st tr) (tcons st tr′)

    add1 : Expr
    add1 x = x 0 + 1

    startState : State
    startState = λ {0 → 0 ; _ → 42}

    ex : exec (Sassign 0 add1) startState (tcons startState (♯ (tnil (update 0 (add1 startState) startState))))
    ex = execAssign _ _ _ _ (tcons (♯ tnil))



    execseqDeterministic₀ : {s : Stmt} 
        → ({st : State} {tr₁ tr₂ : Trace₁} → exec s st tr₁ → exec s st tr₂ → tr₁ ≈ tr₂) 
        → ({tr₁ tr₂ tr₃ tr₄ : Trace₁} → tr₁ ≈ tr₂ → execseq s tr₁ tr₃ → execseq s tr₂ tr₄ → tr₃ ≈ tr₄)
    execseqDeterministic₀ h tnil              (execseqNil _ _ _ ex₁)         (execseqNil _ _ _ ex₂)         = h ex₁ ex₂
    execseqDeterministic₀ h (tcons tr₁′≈tr₂′) (execseqCons _ _ _ _ tr₁⇒tr₃) (execseqCons _ _ _ _ tr₂⇒tr₄) = tcons (♯ execseqDeterministic₀ h (♭ tr₁′≈tr₂′) tr₁⇒tr₃ tr₂⇒tr₄)

    execSeqDeterministic₀ : {s₁ s₂ : Stmt} 
        → ({st : State} {tr₁ tr₂ : Trace₁} → exec s₁ st tr₁ → exec s₁ st tr₂ → tr₁ ≈ tr₂)
        → ({st : State} {tr₁ tr₂ : Trace₁} → exec s₂ st tr₁ → exec s₂ st tr₂ → tr₁ ≈ tr₂)
        → {st : State} {tr₁ tr₂ : Trace₁} → exec (Sseq s₁ s₂) st tr₁ → exec (Sseq s₁ s₂) st tr₂ → tr₁ ≈ tr₂
    execSeqDeterministic₀ h₁ h₂ (execSeq _ _ _ _ _ ex₁ exseq₁) (execSeq _ _ _ _ _ ex₂ exseq₂) = execseqDeterministic₀ h₂ (h₁ ex₁ ex₂) exseq₁ exseq₂

    open Setoid setoid₁ using (refl; sym; trans)
            
    execWhileDeterministic₀ : {c : Expr} {b : Stmt} → ({st : State} {tr₁ tr₂ : Trace₁} → (exec b st tr₁ → exec b st tr₂ → tr₁ ≈ tr₂))
        → {st : State} {tr₁ tr₂ : Trace₁} → exec (Swhile c b) st tr₁ → exec (Swhile c b) st tr₂ → tr₁ ≈ tr₂
    execWhileDeterministic₀ _ (execWhileFalse _ _ _ _ _ tr₁≈result) (execWhileFalse _ _ _ _ _ tr₂≈result)                 = trans tr₁≈result (sym tr₂≈result)
    execWhileDeterministic₀ _ (execWhileFalse _ _ _ _ c＝false _)   (execWhileLoop _ _ _ _ _ c＝true _ _) rewrite c＝false = contradiction c＝true λ ()
    execWhileDeterministic₀ _ (execWhileLoop _ _ _ _ _ c＝true _ _) (execWhileFalse _ _ _ _ c＝false _)   rewrite c＝true  = contradiction c＝false λ ()
    execWhileDeterministic₀ {c} {b} h 
        (execWhileLoop _ _ _ _ _ _ (execseqCons _ _ _ _ (execseqNil _ _ _ exb₁)) exloop₁) 
        (execWhileLoop _ _ _ _ _ _ (execseqCons _ _ _ _ (execseqNil _ _ _ exb₂)) exloop₂) 
                                                                                                                          = execWhileDeterministic₁ (tcons (♯ (h exb₁ exb₂))) exloop₁ exloop₂
        where
            execWhileDeterministic₁ : {tr₁ tr₂ tr₃ tr₄ : Trace₁} → tr₁ ≈ tr₂ → execseq (Swhile c b) tr₁ tr₃ → execseq (Swhile c b) tr₂ tr₄ → tr₃ ≈ tr₄
            execWhileDeterministic₁ tnil              (execseqNil _ _ _ ex₁)       (execseqNil _ _ _ ex₂)       = execWhileDeterministic₀ h ex₁ ex₂
            execWhileDeterministic₁ (tcons tr₁′≈tr₂′) (execseqCons _ _ _ _ exseq₁) (execseqCons _ _ _ _ exseq₂) = tcons (♯ (execWhileDeterministic₁ (♭ tr₁′≈tr₂′) exseq₁ exseq₂))

    
    execDeterministic : {s : Stmt} {st : State} {tr₁ tr₂ : Trace₁} 
        → exec s st tr₁ 
        → exec s st tr₂ 
        → tr₁ ≈ tr₂
    execDeterministic (execSkip _)                               (execSkip _)                                               = refl
    execDeterministic (execAssign _ _ _ _ tr₁≈result)            (execAssign _ _ _ _ tr₂≈result)                            = trans tr₁≈result (sym tr₂≈result)
    execDeterministic l@(execSeq _ _ _ _ _ _ _)                  r@(execSeq _ _ _ _ _ _ _)                                  = execSeqDeterministic₀ execDeterministic execDeterministic l r
    execDeterministic (execIfThenElseTrue _ _ _ _ _ _ seq₁)      (execIfThenElseTrue _ _ _ _ _ _ seq₂)                      = execseqDeterministic₀ execDeterministic refl seq₁ seq₂
    execDeterministic (execIfThenElseTrue _ _ _ _ _ c＝true _)   (execIfThenElseFalse _ _ _ _ _ c＝false _) rewrite c＝true  = contradiction c＝false λ ()
    execDeterministic (execIfThenElseFalse _ _ _ _ _ c＝false _) (execIfThenElseTrue _ _ _ _ _ c＝true _)   rewrite c＝false = contradiction c＝true λ ()
    execDeterministic (execIfThenElseFalse _ _ _ _ _ _ seq₁)    (execIfThenElseFalse _ _ _ _ _ _ seq₂)                      = execseqDeterministic₀ execDeterministic refl seq₁ seq₂
    execDeterministic l@(execWhileFalse _ _ _ _ _ _)            r@(execWhileFalse _ _ _ _ _ _)                              = execWhileDeterministic₀ execDeterministic l r
    execDeterministic l@(execWhileFalse _ _ _ _ _ _)            r@(execWhileLoop _ _ _ _ _ _ _ _)                           = execWhileDeterministic₀ execDeterministic l r
    execDeterministic l@(execWhileLoop _ _ _ _ _ _ _ _)         r@(execWhileFalse _ _ _ _ _ _)                              = execWhileDeterministic₀ execDeterministic l r
    execDeterministic l@(execWhileLoop _ _ _ _ _ _ _ _)         r@(execWhileLoop _ _ _ _ _ _ _ _)                           = execWhileDeterministic₀ execDeterministic l r