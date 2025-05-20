{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst) renaming (trans to eqTrans; sym to eqSym)
open import Codata.Musical.Notation
open import Data.Nat using (ℕ; zero; suc; _<?_)
open import Function.Base using (case_of_)
open import Data.Nat using (_+_)
open import Relation.Nullary using (contradiction)
open import Relation.Nullary.Decidable
open import Relation.Binary.Bundles using (Setoid)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product
open import Data.Sum

open import Traces
open import Language

open Trace₃

module BigRel2 where
    -- append : Trace₁ → Trace₁ → Trace₁
    -- append (tnil x) t₂ = tcons x (♯ t₂)
    -- append (tcons x t) t₂ = tcons x (♯ append (♭ t) t₂)

    -- unwind : Trace₁ → State
    -- unwind (tnil st) = st
    -- unwind (tcons st t) = unwind (♭ t)

    open Trace₃.Trace₃

    mutual
        data exec : (s : Stmt) → (st : State) → (tr : Trace₃) → Set where
            execSkip : {st : State}
                → exec Sskip st (mkTr st nothing)

            execAssign : {id : Id} {a : Expr} {st : State} {tr : Trace₃}
                → exec (Sassign id a) st (mkTr st (just (mkTr (update id (a st) st) nothing)))

            execSeq : {s₁ s₂ : Stmt} {st : State} (tr tr′ : Trace₃) 
                → exec s₁ st tr 
                → execseq s₂ tr tr′
                → exec (Sseq s₁ s₂) st tr′

            execIfThenElseTrue : {c : Expr} {t : Stmt} {st : State} {tr : Trace₃} (e : Stmt)  
                → isTrue (c st) ≡ true 
                → execseq t (mkTr st (just (mkTr st nothing))) tr
                → exec (Sifthenelse c t e) st tr

            execIfThenElseFalse : {c : Expr} {e : Stmt} {st : State} {tr : Trace₃} (t : Stmt) 
                → isTrue (c st) ≡ false 
                → execseq e (mkTr st (just (mkTr st nothing))) tr
                → exec (Sifthenelse c t e) st tr

            execWhileFalse : {c : Expr} {st : State} {tr : Trace₃} (b : Stmt)
                → isTrue (c st) ≡ false
                → exec (Swhile c b) st (mkTr st (just (mkTr st nothing)))

            execWhileLoop : {c : Expr} {b : Stmt} {st : State} (tr tr′ : Trace₃)
                → (isTrue (c st)) ≡ true 
                → execseq b (mkTr st (just (mkTr st nothing))) tr
                → execseq (Swhile c b) tr tr′
                → exec (Swhile c b) st tr′

        record execseq (s : Stmt) (tr₁ tr₂ : Trace₃) : Set where
            coinductive
            field
                p :
                    ∃ (λ st → (tr₁ ≈ mkTr st nothing) × (exec s st tr₂)) -- "nil" case
                    ⊎
                    ∃ {A = State × (Trace₃ × Trace₃)} λ (st , (tr₃ , tr₄)) → -- "cons" case
                            ((tr₁ ≈ mkTr st ((just tr₃))) × (tr₂ ≈ mkTr st (just tr₄))) 
                        × 
                            execseq s tr₃ tr₄

    add1 : Expr
    add1 x = x 0 + 1

    startState : State
    startState = λ {0 → 0 ; _ → 42}

    next : State → State
    next st = update 0 (add1 st) st

    -- open Trace₂.Trace₂

    -- Record of what didn't work
    -- incrementingFrom : State → Trace₂
    -- incrementingFrom st .t = just (st , (incrementingFrom (next st)))

    -- incrementing : Trace₂
    -- incrementing = incrementingFrom startState

    -- test : incrementing ≈ incrementing
    -- test = tcons _≡_.refl _≡_.refl {!   !}

    open Trace₃.Trace₃

    incrementingFrom : State → Trace₃
    incrementingFrom st .hd = st
    incrementingFrom st .tl = just (incrementingFrom (next st))

    incrementing : Trace₃
    incrementing = incrementingFrom startState

    test : incrementing ≈ incrementing
    test = forever startState
        where
        forever : (st : State) → (incrementingFrom st) ≈ (incrementingFrom st)
        forever st ._≈_.hd = _≡_.refl
        forever st ._≈_.tl = inj₂ (((incrementingFrom (next st)) , (incrementingFrom (next st))) , 
            (_≡_.refl , (_≡_.refl , (forever (next st)))))


    -- ex : exec (Sassign 0 add1) startState ?

    -- module exloop where
    --     -- Is the variable at location 0 less than 2 in the given state?
    --     lt2 : Expr
    --     lt2 x  = case x 0 <? 2 of λ {(yes _) → 1 ; (no _) → 0}

    --     guardTest1 : Trace₁
    --     guardTest1 = tcons startState (♯ tnil startState)

    --     updateOnce : State
    --     updateOnce = update 0 (add1 startState) startState

    --     loop1 : Trace₁
    --     loop1 = append guardTest1 (tnil updateOnce)

    --     guardTest2 : Trace₁
    --     guardTest2 = append loop1 (tnil updateOnce)

    --     updateTwice : State
    --     updateTwice = update 0 (add1 updateOnce) updateOnce

    --     loop2 : Trace₁
    --     loop2 = append guardTest2 (tnil updateTwice)

    --     guardTest3 : Trace₁
    --     guardTest3 = append loop2 (tnil updateTwice)

    --     -- Proof tree of a program that loops twice then exits
    --     exlooping2 : exec (Swhile lt2 (Sassign 0 add1)) startState guardTest3
    --     exlooping2 = execWhileLoop
    --         loop1 
    --         guardTest3 
    --         _≡_.refl 
    --         (execseqCons 
    --             startState 
    --             _ 
    --             _ 
    --             (♯ execseqNil (execAssign (tcons (♯ tnil))))) 

    --         (execseqCons 
    --             startState 
    --             _ 
    --             _ 
    --             (♯ (execseqCons 
    --                 startState 
    --                 _ 
    --                 _ 
    --                 (♯ (execseqNil 
    --                     (execWhileLoop 
    --                         (tcons updateOnce (♯ (tcons updateOnce (♯ (tnil updateTwice)))))
    --                         _ 
    --                         _≡_.refl 
    --                         (execseqCons updateOnce _ _ (♯ (execseqNil (execAssign (tcons (♯ tnil))))))
    --                         (execseqCons updateOnce _ _ (♯ (execseqCons updateOnce _ _ (♯ (execseqNil
    --                             (execWhileFalse
    --                             _ 
    --                             _≡_.refl 
    --                             (tcons (♯ tnil))))))))))))))

    --     loopforevertrace : Trace₁
    --     loopforevertrace = tcons startState (♯ loopforevertrace)
        
    --     -- Proof tree of a program that loops forever
    --     exloopforever : exec (Swhile (λ _ → 1) Sskip) startState loopforevertrace
    --     exloopforever = execWhileLoop 
    --         (tcons startState (♯ (tnil startState))) 
    --         loopforevertrace
    --         _≡_.refl 
    --         (execseqCons _ _ _ (♯ execseqNil execSkip))
    --         (execseqCons _ _ _ (♯ execseqNil exloopforever))

    --     next : State → State
    --     next st = update 0 (add1 st) st

    --     incrementingFrom : State → Trace₁
    --     incrementingFrom st = tcons st (♯ tcons st (♯ (incrementingFrom (next st))))

    --     incrementingtrace : Trace₁
    --     incrementingtrace = incrementingFrom startState

    --     exloopincrementing : exec (Swhile (λ _ → 1) (Sassign 0 add1)) startState incrementingtrace
    --     exloopincrementing = t startState
    --         where
    --             t : (st : State) → exec (Swhile (λ _ → 1) (Sassign 0 add1)) st (incrementingFrom st)
    --             t st = execWhileLoop 
    --                 (tcons st (♯ (tcons st (♯ (tnil (update 0 (add1 st) st)))))) 
    --                 _ 
    --                 _≡_.refl 
    --                 (execseqCons st _ _ (♯ execseqNil (execAssign (tcons (♯ tnil)))))
    --                 (execseqCons st _ _ (♯ (execseqCons st _ _ (♯ (execseqNil (t (next st)))))))


    --     -- increasing id v tr : In trace tr, variable at location id starts with value v and always increases by 1 after 2 applications of tcons (one application for guard checking, and one for reassignment)
    --     data increasing : Id → Val → Trace₁ → Set where
    --         increasingCons : {id : Id} {v : Val} {st : State} {tr tr₁ : Trace₁} → st id ≡ v → tr₁ ≈ tcons st (♯ (tcons st (♯ tr))) → ∞ (increasing id (suc v) tr) → increasing id v tr₁

    --     incrementingAlwaysIncrements : increasing 0 0 incrementingtrace
    --     incrementingAlwaysIncrements = forever refl
    --         where
    --             open Setoid setoid₁ using () renaming (refl to ≈refl)
    --             open import Relation.Binary.PropositionalEquality
    --             open ≡-Reasoning

    --             lem₁ : {x : ℕ} → x + 1 ≡ suc x
    --             lem₁ {zero} = refl
    --             lem₁ {suc x} = begin
    --                 suc (x + 1)
    --                 ≡⟨⟩
    --                 suc x + suc zero
    --                 ≡⟨ cong suc (lem₁) ⟩
    --                 suc (suc x)
    --                 ∎

    --             lem₂ : {v : Val} → (st : State) → (st 0 ≡ v) → next st 0 ≡ suc v
    --             lem₂ {v} st x = begin
    --                 next st 0
    --                 ≡⟨⟩
    --                 st 0 + 1
    --                 ≡⟨ cong (_+ 1) x ⟩
    --                 v + 1
    --                 ≡⟨ lem₁ ⟩
    --                 suc v
    --                 ∎

    --             forever : {st : State} {v : Val} → (st 0 ≡ v) → increasing 0 v (incrementingFrom st)
    --             forever {st} x = increasingCons x (tcons (♯ (tcons (♯ ≈refl)))) (♯ forever (lem₂ st x))

    --     ITEfinal : Trace₁
    --     ITEfinal = (tcons startState (♯ (tcons startState (♯ (tcons (next startState) (♯ (tcons (next (next startState)) (♯ (tcons (next (next startState)) (♯ (tnil (next (next (next startState))))))))))))))

    --     exITE : exec 
    --         (Sifthenelse 
    --             lt2 
    --             (Sseq 
    --                 (Sseq (Sassign 0 add1) (Sassign 0 add1)) 
    --                 (Sifthenelse lt2 Sskip (Sassign 0 add1))) 
    --             Sskip) 
    --         startState 
    --         ITEfinal
    --     exITE = execIfThenElseTrue 
    --         Sskip 
    --         _≡_.refl 
    --         (execseqCons _ _ _ (♯ (execseqNil (execSeq 
    --             (tcons startState (♯ (tcons (next startState) (♯ (tnil (next (next startState))))))) _ 
    --             (execSeq (tcons startState(♯ (tnil (next startState)))) _ (execAssign (tcons (♯ tnil))) (execseqCons _ _ _ (♯ (execseqNil (execAssign (tcons (♯ tnil))))))) 
    --             (execseqCons _ _ _ (♯ (execseqCons _ _ _ (♯ (execseqNil (execIfThenElseFalse _ _≡_.refl (execseqCons _ _ _ (♯ (execseqNil (execAssign (tcons (♯ tnil)))))))))))))))) 
                

            

    execseqDeterministic₀ : {s : Stmt}
        → ({st : State} {tr₁ tr₂ : Trace₃} → exec s st tr₁ → exec s st tr₂ → tr₁ ≈ tr₂) 
        → ({tr₁ tr₂ tr₃ tr₄ : Trace₃} → tr₁ ≈ tr₂ → execseq s tr₁ tr₃ → execseq s tr₂ tr₄ → tr₃ ≈ tr₄)
    -- execseqDeterministic₀ h tnil              (execseqNil ex₁)         (execseqNil ex₂)         = h ex₁ ex₂
    -- execseqDeterministic₀ h (tcons tr₁′≈tr₂′) (execseqCons _ _ _ tr₁⇒tr₃) (execseqCons _ _ _ tr₂⇒tr₄) = tcons (♯ execseqDeterministic₀ h (♭ tr₁′≈tr₂′) (♭ tr₁⇒tr₃) (♭ tr₂⇒tr₄))
    execseqDeterministic₀ h {tr₁} {tr₂} {tr₃} {tr₄} a b c ._≈_.hd with (execseq.p b) | (execseq.p c)
    ... | inj₁ (ab , abc , abcd) | inj₁ (bc , bcd , bcde) = 
        let
            t : hd tr₁ ≡ ab
            t = _≈_.hd abc

            t₂ : hd tr₂ ≡ bc
            t₂ = _≈_.hd bcd

            t₃ : bc ≡ ab
            t₃ = eqTrans (eqSym t₂) (eqTrans (eqSym (_≈_.hd a)) t)
        in
            _≈_.hd (h abcd (subst (λ x → exec _ x tr₄) t₃ bcde))
    execseqDeterministic₀ h {tr₁} {tr₂} {tr₃} {tr₄} a b c ._≈_.tl with (_≈_.tl a) | (execseq.p b) | (execseq.p c)
    ... | inj₂ ((aaa , aaaa) , (bbb , (bbbb , bbbbb))) | inj₂ ((ab , (abb , abbb)) , (abc , abcc) , abcd) | inj₂ (bc , bcd , bcde) = 
        let
            t = {!   !}
        in
            inj₂ ((tr₁ , tr₂) , ({!   !} , ({!   !} , {!   !})))
    -- execseqDeterministic₀ h a b c ._≈_.tl with (_≈_.hd a) | (_≈_.tl a) | (execseq.p b) | (execseq.p c)
    -- ... | aa | bb | inj₁ (fst , _ , ex₁) | inj₁ (fst2 , _ , ex₂) = h ex₁ {!   !}
    -- ... | _ | _ | _ | _ = {!   !}

    -- execSeqDeterministic₀ : {s₁ s₂ : Stmt} 
    --     → ({st : State} {tr₁ tr₂ : Trace₁} → exec s₁ st tr₁ → exec s₁ st tr₂ → tr₁ ≈ tr₂)
    --     → ({st : State} {tr₁ tr₂ : Trace₁} → exec s₂ st tr₁ → exec s₂ st tr₂ → tr₁ ≈ tr₂)
    --     → {st : State} {tr₁ tr₂ : Trace₁} → exec (Sseq s₁ s₂) st tr₁ → exec (Sseq s₁ s₂) st tr₂ → tr₁ ≈ tr₂
    -- execSeqDeterministic₀ h₁ h₂ (execSeq _ _ ex₁ exseq₁) (execSeq _ _ ex₂ exseq₂) = execseqDeterministic₀ h₂ (h₁ ex₁ ex₂) exseq₁ exseq₂

    -- open Setoid setoid₁ using (refl; sym; trans)
            
    -- execWhileDeterministic₀ : {c : Expr} {b : Stmt} → ({st : State} {tr₁ tr₂ : Trace₁} → (exec b st tr₁ → exec b st tr₂ → tr₁ ≈ tr₂))
    --     → {st : State} {tr₁ tr₂ : Trace₁} → exec (Swhile c b) st tr₁ → exec (Swhile c b) st tr₂ → tr₁ ≈ tr₂
    -- execWhileDeterministic₀ _ (execWhileFalse _ _ tr₁≈result) (execWhileFalse _ _ tr₂≈result)                 = trans tr₁≈result (sym tr₂≈result)
    -- execWhileDeterministic₀ _ (execWhileFalse _ c＝false _)   (execWhileLoop _ _ c＝true _ _) rewrite c＝false = contradiction c＝true λ ()
    -- execWhileDeterministic₀ _ (execWhileLoop _ _ c＝true _ _) (execWhileFalse _ c＝false _)   rewrite c＝true  = contradiction c＝false λ ()
    -- execWhileDeterministic₀ {c} {b} h (execWhileLoop _ _ _ (execseqCons _ _ _ x₁) x₂) (execWhileLoop _ _ _ (execseqCons _ _ _ x₄) x₅) = execWhileDeterministic₁ (tcons (♯ execseqDeterministic₀ h refl (♭ x₁) (♭ x₄))) x₂ x₅
    --     where
    --         execWhileDeterministic₁ : {tr₁ tr₂ tr₃ tr₄ : Trace₁} → tr₁ ≈ tr₂ → execseq (Swhile c b) tr₁ tr₃ → execseq (Swhile c b) tr₂ tr₄ → tr₃ ≈ tr₄
    --         execWhileDeterministic₁ tnil              (execseqNil ex₁)       (execseqNil ex₂)       = execWhileDeterministic₀ h ex₁ ex₂
    --         execWhileDeterministic₁ (tcons tr₁′≈tr₂′) (execseqCons _ _ _ exseq₁) (execseqCons _ _ _ exseq₂) = tcons (♯ (execWhileDeterministic₁ (♭ tr₁′≈tr₂′) (♭ exseq₁) (♭ exseq₂)))

    
    -- execDeterministic : {s : Stmt} {st : State} {tr₁ tr₂ : Trace₁} 
    --     → exec s st tr₁ 
    --     → exec s st tr₂ 
    --     → tr₁ ≈ tr₂
    -- execDeterministic execSkip                              execSkip                                               = refl
    -- execDeterministic (execAssign tr₁≈result)            (execAssign tr₂≈result)                            = trans tr₁≈result (sym tr₂≈result)
    -- execDeterministic l@(execSeq _ _ _ _)                  r@(execSeq _ _ _ _)                                  = execSeqDeterministic₀ execDeterministic execDeterministic l r
    -- execDeterministic (execIfThenElseTrue _ _ seq₁)      (execIfThenElseTrue _ _ seq₂)                      = execseqDeterministic₀ execDeterministic refl seq₁ seq₂
    -- execDeterministic (execIfThenElseTrue _ c＝true _)   (execIfThenElseFalse _ c＝false _) rewrite c＝true  = contradiction c＝false λ ()
    -- execDeterministic (execIfThenElseFalse _ c＝false _) (execIfThenElseTrue _ c＝true _)   rewrite c＝false = contradiction c＝true λ ()
    -- execDeterministic (execIfThenElseFalse _ _ seq₁)    (execIfThenElseFalse _ _ seq₂)                      = execseqDeterministic₀ execDeterministic refl seq₁ seq₂
    -- execDeterministic l@(execWhileFalse _ _ _)            r@(execWhileFalse _ _ _)                              = execWhileDeterministic₀ execDeterministic l r
    -- execDeterministic l@(execWhileFalse _ _ _)            r@(execWhileLoop _ _ _ _ _)                           = execWhileDeterministic₀ execDeterministic l r
    -- execDeterministic l@(execWhileLoop _ _ _ _ _)         r@(execWhileFalse _ _ _)                              = execWhileDeterministic₀ execDeterministic l r
    -- execDeterministic l@(execWhileLoop _ _ _ _ _)         r@(execWhileLoop _ _ _ _ _)                           = execWhileDeterministic₀ execDeterministic l r 