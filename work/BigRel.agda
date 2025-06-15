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

open import work.MusicalTraces
open import work.Language

open Trace₁

module work.BigRel where
    mutual
        data exec : Stmt → State → Trace₁ → Set where
            execSkip : {st : State}
                → exec Sskip st (tnil st)

            execAssign : {id : Id} {a : Expr} {st : State} {tr : Trace₁}
                → tr ≈ (tcons st (♯ tnil (update id (a st) st)))
                → exec (Sassign id a) st tr

            execSeq : {s₁ s₂ : Stmt} {st : State} (tr tr′ : Trace₁) 
                → exec s₁ st tr 
                → execseq s₂ tr tr′ 
                → exec (Sseq s₁ s₂) st tr′

            execIfThenElseTrue : {c : Expr} {t : Stmt} {st : State} {tr : Trace₁} (e : Stmt)  
                → isTrue (c st) ≡ true 
                → execseq t (tcons st (♯ tnil st)) tr 
                → exec (Sifthenelse c t e) st tr

            execIfThenElseFalse : {c : Expr} {e : Stmt} {st : State} {tr : Trace₁} (t : Stmt) 
                → isTrue (c st) ≡ false 
                → execseq e (tcons st (♯ tnil st)) tr 
                → exec (Sifthenelse c t e) st tr

            execWhileFalse : {c : Expr} {st : State} {tr : Trace₁}
                → (b : Stmt)
                → isTrue (c st) ≡ false
                → tr ≈ (tcons st (♯ tnil st))
                → exec (Swhile c b) st tr

            execWhileLoop : {c : Expr} {b : Stmt} {st : State} (tr tr′ : Trace₁)
                → (isTrue (c st)) ≡ true 
                → execseq b (tcons st (♯ tnil st)) tr 
                → execseq (Swhile c b) tr tr′ 
                → exec (Swhile c b) st tr′

        data execseq : Stmt → Trace₁ → Trace₁ → Set where
            execseqNil : {st : State} {s : Stmt} {tr : Trace₁} 
                → exec s st tr 
                → execseq s (tnil st) tr
                
            execseqCons : {s : Stmt} (st : State) (tr tr′ : ∞ Trace₁) 
                → ∞ (execseq s (♭ tr) (♭ tr′)) 
                → execseq s (tcons st tr) (tcons st tr′)

    open Setoid setoid₁ using (refl; sym; trans)

    module examples where
        -- ### Common definitions
        startState : State
        startState = λ {0 → 0 ; _ → 42}

        add1 : Expr
        add1 x = x 0 + 1

        next : State → State
        next st = update 0 (add1 st) st

        -- Is the variable at location 0 less than 2 in the given state?
        lt2 : Expr
        lt2 x  = case x 0 <? 2 of λ {(yes _) → 1 ; (no _) → 0}

        -- Proof tree of a program that loops forever
        module loopForever where
            loopforevertrace : Trace₁
            loopforevertrace = tcons startState (♯ loopforevertrace)
            
            -- Proof tree of a program that loops forever
            exloopforever : exec (Swhile (λ _ → 1) Sskip) startState loopforevertrace
            exloopforever = execWhileLoop 
                (tcons startState (♯ (tnil startState))) 
                loopforevertrace
                _≡_.refl 
                (execseqCons _ _ _ (♯ execseqNil execSkip))
                (execseqCons _ _ _ (♯ execseqNil exloopforever))

        -- Proof tree of a program generating the naturals (exloopincrementing)
        -- As well as a proof the trace actually does this (incrementingAlwaysIncrements)
        module increasing where
            incrementingFrom : State → Trace₁
            incrementingFrom st = tcons st (♯ tcons st (♯ (incrementingFrom (next st))))

            incrementingtrace : Trace₁
            incrementingtrace = incrementingFrom startState

            exloopincrementing : exec (Swhile (λ _ → 1) (Sassign 0 add1)) startState incrementingtrace
            exloopincrementing = t startState
                where
                    t : (st : State) → exec (Swhile (λ _ → 1) (Sassign 0 add1)) st (incrementingFrom st)
                    t st = execWhileLoop 
                        (tcons st (♯ (tcons st (♯ (tnil (update 0 (add1 st) st)))))) 
                        _ 
                        _≡_.refl 
                        (execseqCons st _ _ (♯ execseqNil (execAssign (tcons (♯ refl)))))
                        (execseqCons st _ _ (♯ (execseqCons st _ _ (♯ (execseqNil (t (next st)))))))


            -- increasing id v tr : In trace tr, variable at location id starts with value v and always increases by 1 after 2 applications of tcons (one application for guard checking, and one for reassignment)
            data increasing : Id → Val → Trace₁ → Set where
                increasingCons : {id : Id} {v : Val} {st : State} {tr tr₁ : Trace₁} 
                    → st id ≡ v 
                    → tr₁ ≈ tcons st (♯ (tcons st (♯ tr))) 
                    → ∞ (increasing id (suc v) tr) 
                    → increasing id v tr₁

            incrementingAlwaysIncrements : increasing 0 0 incrementingtrace
            incrementingAlwaysIncrements = forever _≡_.refl
                where
                    open import Relation.Binary.PropositionalEquality hiding (refl)
                    open ≡-Reasoning

                    lem₁ : {x : ℕ} → x + 1 ≡ suc x
                    lem₁ {zero} = _≡_.refl
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
                    forever {st} x = increasingCons x (tcons (♯ (tcons (♯ refl)))) (♯ forever (lem₂ st x))

        -- Proof tree of a program that loops twice, then exits
        module loopTwice where
            append : Trace₁ → Trace₁ → Trace₁
            append (tnil x) t₂ = tcons x (♯ t₂)
            append (tcons x t) t₂ = tcons x (♯ append (♭ t) t₂)

            guardTest1 : Trace₁
            guardTest1 = tcons startState (♯ tnil startState)

            updateOnce : State
            updateOnce = update 0 (add1 startState) startState

            loop1 : Trace₁
            loop1 = append guardTest1 (tnil updateOnce)

            guardTest2 : Trace₁
            guardTest2 = append loop1 (tnil updateOnce)

            updateTwice : State
            updateTwice = update 0 (add1 updateOnce) updateOnce

            loop2 : Trace₁
            loop2 = append guardTest2 (tnil updateTwice)

            guardTest3 : Trace₁
            guardTest3 = append loop2 (tnil updateTwice)

            exlooping2 : exec (Swhile lt2 (Sassign 0 add1)) startState guardTest3
            exlooping2 = execWhileLoop
                loop1 
                guardTest3 
                _≡_.refl 
                (execseqCons 
                    startState 
                    _ 
                    _ 
                    (♯ execseqNil (execAssign (tcons (♯ tnil)))))

                (execseqCons 
                    startState 
                    _ 
                    _ 
                    (♯ (execseqCons 
                        startState 
                        _ 
                        _ 
                        (♯ (execseqNil 
                            (execWhileLoop 
                                (tcons updateOnce (♯ (tcons updateOnce (♯ (tnil updateTwice)))))
                                _ 
                                _≡_.refl 
                                (execseqCons updateOnce _ _ (♯ (execseqNil (execAssign (tcons (♯ tnil))))))
                                (execseqCons updateOnce _ _ (♯ (execseqCons updateOnce _ _ (♯ (execseqNil
                                    (execWhileFalse
                                    _ 
                                    _≡_.refl 
                                    (tcons (♯ tnil))))))))))))))

        -- Proof tree of a program utilizing if-then-else statements
        module ifThenElse where
            ITEfinal : Trace₁
            ITEfinal = (tcons startState (♯ (tcons startState (♯ (tcons (next startState) (♯ (tcons (next (next startState)) (♯ (tcons (next (next startState)) (♯ (tnil (next (next (next startState))))))))))))))

            exITE : exec 
                (Sifthenelse 
                    lt2 
                    (Sseq 
                        (Sseq (Sassign 0 add1) (Sassign 0 add1)) 
                        (Sifthenelse lt2 Sskip (Sassign 0 add1))) 
                    Sskip) 
                startState 
                ITEfinal
            exITE = execIfThenElseTrue 
                Sskip 
                _≡_.refl 
                (execseqCons _ _ _ (♯ (execseqNil (execSeq 
                    (tcons startState (♯ (tcons (next startState) (♯ (tnil (next (next startState))))))) _ 
                    (execSeq (tcons startState(♯ (tnil (next startState)))) _ (execAssign (tcons (♯ tnil))) (execseqCons _ _ _ (♯ (execseqNil (execAssign (tcons (♯ tnil))))))) 
                    (execseqCons _ _ _ (♯ (execseqCons _ _ _ (♯ (execseqNil (execIfThenElseFalse _ _≡_.refl (execseqCons _ _ _ (♯ (execseqNil (execAssign (tcons (♯ tnil)))))))))))))))) 
                    

    -- Determinsm proof        
    mutual
        execseqDeterministic₀ : {s : Stmt} → ({tr₁ tr₂ tr₃ tr₄ : Trace₁} → tr₁ ≈ tr₂ → execseq s tr₁ tr₃ → execseq s tr₂ tr₄ → tr₃ ≈ tr₄)
        execseqDeterministic₀ tnil              (execseqNil ex₁)             (execseqNil ex₂)             = execDeterministic ex₁ ex₂
        execseqDeterministic₀ (tcons tr₁′≈tr₂′) (execseqCons _ _ _ tr₁⇒tr₃) (execseqCons _ _ _ tr₂⇒tr₄) = tcons (♯ execseqDeterministic₀ (♭ tr₁′≈tr₂′) (♭ tr₁⇒tr₃) (♭ tr₂⇒tr₄))
                
        execWhileDeterministic₀ : {c : Expr} {b : Stmt} {st : State} {tr₁ tr₂ : Trace₁} → exec (Swhile c b) st tr₁ → exec (Swhile c b) st tr₂ → tr₁ ≈ tr₂
        execWhileDeterministic₀ (execWhileFalse _ _ tr₁≈result) (execWhileFalse _ _ tr₂≈result)                 = trans tr₁≈result (sym tr₂≈result)
        execWhileDeterministic₀ (execWhileFalse _ c＝false _)   (execWhileLoop _ _ c＝true _ _) rewrite c＝false = contradiction c＝true λ ()
        execWhileDeterministic₀ (execWhileLoop _ _ c＝true _ _) (execWhileFalse _ c＝false _)   rewrite c＝true  = contradiction c＝false λ ()
        execWhileDeterministic₀ {c} {b} 
            (execWhileLoop _ _ _ (execseqCons _ _ _ exsnil₁) (execseqCons _ _ _ exsloop₁)) 
            (execWhileLoop _ _ _ (execseqCons _ _ _ exsnil₂) (execseqCons _ _ _ exsloop₂)) 
            = tcons (♯ execWhileDeterministic₁ (execseqDeterministic₀ refl (♭ exsnil₁) (♭ exsnil₂)) (♭ exsloop₁) (♭ exsloop₂))
            where
                execWhileDeterministic₁ : {tr₁ tr₂ tr₃ tr₄ : Trace₁} → tr₁ ≈ tr₂ → execseq (Swhile c b) tr₁ tr₃ → execseq (Swhile c b) tr₂ tr₄ → tr₃ ≈ tr₄
                execWhileDeterministic₁ tnil              (execseqNil ex₁)       (execseqNil ex₂)       = execWhileDeterministic₀ ex₁ ex₂
                execWhileDeterministic₁ (tcons tr₁′≈tr₂′) (execseqCons _ _ _ exseq₁) (execseqCons _ _ _ exseq₂) = tcons (♯ (execWhileDeterministic₁ (♭ tr₁′≈tr₂′) (♭ exseq₁) (♭ exseq₂)))

        -- Observation: execWhileDeterministic₁ is necessary to "constrain" the execution path for the sake of guardedness.
        -- Using execseqDeterministic₀ results in a termination checking failure.
        -- This is not necessary for sized, where I can just put everything for the while case in execDeterministic directly

        
        execDeterministic : {s : Stmt} {st : State} {tr₁ tr₂ : Trace₁} 
            → exec s st tr₁ 
            → exec s st tr₂ 
            → tr₁ ≈ tr₂
        execDeterministic execSkip                           execSkip                                           = refl
        execDeterministic (execAssign tr₁≈result)            (execAssign tr₂≈result)                            = trans tr₁≈result (sym tr₂≈result)
        execDeterministic (execSeq _ _ ex₁ exs₁)             (execSeq _ _ ex₂ exs₂)                             = execseqDeterministic₀ (execDeterministic ex₁ ex₂) exs₁ exs₂
        execDeterministic (execIfThenElseTrue _ _ seq₁)      (execIfThenElseTrue _ _ seq₂)                      = execseqDeterministic₀ refl seq₁ seq₂
        execDeterministic (execIfThenElseTrue _ c＝true _)   (execIfThenElseFalse _ c＝false _) rewrite c＝true  = contradiction c＝false λ ()
        execDeterministic (execIfThenElseFalse _ c＝false _) (execIfThenElseTrue _ c＝true _)   rewrite c＝false = contradiction c＝true λ ()
        execDeterministic (execIfThenElseFalse _ _ seq₁)     (execIfThenElseFalse _ _ seq₂)                     = execseqDeterministic₀ refl seq₁ seq₂
        execDeterministic l@(execWhileFalse _ _ _)           r@(execWhileFalse _ _ _)                           = execWhileDeterministic₀ l r
        execDeterministic l@(execWhileFalse _ _ _)           r@(execWhileLoop _ _ _ _ _)                        = execWhileDeterministic₀ l r
        execDeterministic l@(execWhileLoop _ _ _ _ _)        r@(execWhileFalse _ _ _)                           = execWhileDeterministic₀ l r
        execDeterministic l@(execWhileLoop _ _ _ _ _)        r@(execWhileLoop _ _ _ _ _)                        = execWhileDeterministic₀ l r 