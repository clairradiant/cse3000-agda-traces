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
open import Data.Product
open import Data.Empty

open import Traces
open import Language

open Trace₂

module BigRel2 where
    -- append : Trace₁ → Trace₁ → Trace₁
    -- append (tnil x) t₂ = tcons x (♯ t₂)
    -- append (tcons x t) t₂ = tcons x (♯ append (♭ t) t₂)

    -- unwind : Trace₁ → State
    -- unwind (tnil st) = st
    -- unwind (tcons st t) = unwind (♭ t)

    open Trace₂.Trace₂

    mutual
        data exec : (s : Stmt) → (st : State) → (tr : Trace₂) → Set where
            execSkip : {st : State}
                → exec Sskip st (mkTr (tnil st))

            execAssign : {id : Id} {a : Expr} {st : State}
                → exec (Sassign id a) st (mkTr (tcons st (mkTr (tnil (update id (a st) st)))))

            execSeq : {s₁ s₂ : Stmt} {st : State} (tr tr′ : Trace₂) 
                → exec s₁ st tr 
                → execseq s₂ tr tr′ 
                → exec (Sseq s₁ s₂) st tr′

            execIfThenElseTrue : {c : Expr} {t : Stmt} {st : State} {tr : Trace₂} (e : Stmt)  
                → isTrue (c st) ≡ true 
                → execseq t ((mkTr (tcons st (mkTr (tnil st))))) tr 
                → exec (Sifthenelse c t e) st tr

            execIfThenElseFalse : {c : Expr} {e : Stmt} {st : State} {tr : Trace₂} (t : Stmt) 
                → isTrue (c st) ≡ false 
                → execseq e ((mkTr (tcons st (mkTr (tnil st))))) tr 
                → exec (Sifthenelse c t e) st tr

            execWhileFalse : {c : Expr} {st : State}
                → (b : Stmt)
                → isTrue (c st) ≡ false
                → exec (Swhile c b) st ((mkTr (tcons st (mkTr (tnil st)))))

            execWhileLoop : {c : Expr} {b : Stmt} {st : State} (tr tr′ : Trace₂)
                → (isTrue (c st)) ≡ true 
                → execseq b ((mkTr (tcons st (mkTr (tnil st))))) tr 
                → execseq (Swhile c b) tr tr′ 
                → exec (Swhile c b) st tr′

        -- postulate execseq : Stmt → Trace₂ → Trace₂ → Set

        data rexecseq : Stmt → Trace₂ → Trace₂ → Set where
            rexecseqNil : {st : State} {s : Stmt} {tr tr′ : Trace₂}
                → tr ≡ mkTr (tnil st)
                → exec s st tr′
                → rexecseq s tr tr′

            rexecseqCons : (s : Stmt) (st : State) (tr₁ tr₂ tr₃ tr′ : Trace₂)
                → tr₁ ≡ mkTr (tcons st tr₂) 
                → tr′ ≡ mkTr (tcons st tr₃)
                → execseq s tr₂ tr₃
                → rexecseq s tr₁ tr′

        record execseq (s : Stmt) (tr tr′ : Trace₂) : Set where
            coinductive
            constructor mkExecseq
            field
                p : rexecseq s tr tr′

        -- data execseq : Stmt → Trace₁ → Trace₁ → Set where
        --     execseqNil : {st : State} {s : Stmt} {tr : Trace₁} 
        --         → exec s st tr 
        --         → execseq s (tnil st) tr
                
        --     execseqCons : {s : Stmt} (st : State) (tr tr′ : ∞ Trace₁) 
        --         → ∞ (execseq s (♭ tr) (♭ tr′)) 
        --         → execseq s (tcons st tr) (tcons st tr′)

    add1 : Expr
    add1 x = x 0 + 1

    startState : State
    startState = λ {0 → 0 ; _ → 42}

    -- ex : exec (Sassign 0 add1) startState (tcons startState (♯ (tnil (update 0 (add1 startState) startState))))
    -- ex = execAssign (tcons (♯ tnil))

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

    loopforevertrace : Trace₂
    loopforevertrace .out = tcons startState loopforevertrace
        
    -- Proof tree of a program that loops forever
    -- exloopforever : exec (Swhile (λ _ → 1) Sskip) startState loopforevertrace
    -- exloopforever = execWhileLoop 
    --     (mkTr (tcons startState (mkTr (tnil startState))))
    --     loopforevertrace 
    --     _≡_.refl 
    --     (mkExecseq (rexecseqCons _ _ _ _ (mkExecseq (rexecseqNil execSkip)))) 
    --     proofforever
    --     where
    --         proofforever : execseq (Swhile (λ _ → 1) Sskip) (mkTr (tcons startState (mkTr (tnil startState)))) loopforevertrace
    --         proofforever .execseq.p = rexecseqCons _ _ _ _ (mkExecseq (rexecseqNil exloopforever))

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
    --         increasingCons : {id : Id} {v : Val} {st : State} {tr tr₁ : Trace₁} 
    --             → st id ≡ v 
    --             → tr₁ ≈ tcons st (♯ (tcons st (♯ tr))) 
    --             → ∞ (increasing id (suc v) tr) 
    --             → increasing id v tr₁

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

    tnil≠tcons : {st₁ st₂ : State} {tr : Trace₂} → (tnil st₁) ≡ (tcons st₂ tr) → ⊥
    tnil≠tcons ()

    mutual
        rexecseqDeterministic₀ : {s : Stmt}
            → ({st : State} {tr₁ tr₂ : Trace₂} → exec s st tr₁ → exec s st tr₂ → tr₁ ≈ tr₂) 
            → ({tr₁ tr₂ tr₃ tr₄ : Trace₂} → tr₁ ≈ tr₂ → rexecseq s tr₁ tr₃ → rexecseq s tr₂ tr₄ → (out tr₃) r≈ (out tr₄))
        rexecseqDeterministic₀ x x₁ (rexecseqNil _≡_.refl x₃) (rexecseqNil _≡_.refl x₅) with _≈_.p x₁
        ... | tnil = _≈_.p (x x₃ x₅)
        rexecseqDeterministic₀ x x₁ (rexecseqNil _≡_.refl x₃) (rexecseqCons _ st _ tr₂ tr₃ _ _≡_.refl x₅ x₆) with _≈_.p x₁
        ... | ()
        rexecseqDeterministic₀ x x₁ (rexecseqCons _ st _ tr₂ tr₃ _ _≡_.refl _≡_.refl x₄) (rexecseqNil _≡_.refl x₆) with _≈_.p x₁
        ... | ()
        rexecseqDeterministic₀ x x₁ (rexecseqCons _ st _ tr₂ tr₃ _ _≡_.refl _≡_.refl x₄) (rexecseqCons _ st₁ _ tr₄ tr₅ _ _≡_.refl _≡_.refl x₇) with _≈_.p x₁
        ... | tcons x₂ = tcons (execseqDeterministic₀ x x₂ x₄ x₇)

        execseqDeterministic₀ : {s : Stmt}
            → ({st : State} {tr₁ tr₂ : Trace₂} → exec s st tr₁ → exec s st tr₂ → tr₁ ≈ tr₂) 
            → ({tr₁ tr₂ tr₃ tr₄ : Trace₂} → tr₁ ≈ tr₂ → execseq s tr₁ tr₃ → execseq s tr₂ tr₄ → tr₃ ≈ tr₄)
        execseqDeterministic₀ x x₁ x₂ x₃ ._≈_.p = rexecseqDeterministic₀ x x₁ (execseq.p x₂) (execseq.p x₃)
        -- execseqDeterministic₀ x {tr₁} {tr₂} x₁ x₂ x₃ ._≈_.p with out tr₁ in eq₁ | out tr₂ in eq₂ | (_≈_.p x₁) | (execseq.p x₂) | (execseq.p x₃) 
        -- ... | tnil st | tnil st₁ | tnil | rexecseqNil a b | rexecseqNil c d = {!   !}
    -- execseqDeterministic₀ h tnil              (execseqNil ex₁)         (execseqNil ex₂)         = h ex₁ ex₂
    -- execseqDeterministic₀ h (tcons tr₁′≈tr₂′) (execseqCons _ _ _ tr₁⇒tr₃) (execseqCons _ _ _ tr₂⇒tr₄) = tcons (♯ execseqDeterministic₀ h (♭ tr₁′≈tr₂′) (♭ tr₁⇒tr₃) (♭ tr₂⇒tr₄))

    execSeqDeterministic₀ : {s₁ s₂ : Stmt} 
        → ({st : State} {tr₁ tr₂ : Trace₂} → exec s₁ st tr₁ → exec s₁ st tr₂ → tr₁ ≈ tr₂)
        → ({st : State} {tr₁ tr₂ : Trace₂} → exec s₂ st tr₁ → exec s₂ st tr₂ → tr₁ ≈ tr₂)
        → {st : State} {tr₁ tr₂ : Trace₂} → exec (Sseq s₁ s₂) st tr₁ → exec (Sseq s₁ s₂) st tr₂ → tr₁ ≈ tr₂
    execSeqDeterministic₀ h₁ h₂ (execSeq _ _ ex₁ exseq₁) (execSeq _ _ ex₂ exseq₂) = execseqDeterministic₀ h₂ (h₁ ex₁ ex₂) exseq₁ exseq₂

    open Setoid setoid₂ using (refl; sym; trans)

    execWhileDeterministic₀ : {c : Expr} {b : Stmt} → ({st : State} {tr₁ tr₂ : Trace₂} → (exec b st tr₁ → exec b st tr₂ → tr₁ ≈ tr₂))
        → {st : State} {tr₁ tr₂ : Trace₂} → exec (Swhile c b) st tr₁ → exec (Swhile c b) st tr₂ → tr₁ ≈ tr₂
    execWhileDeterministic₁ : {c : Expr} {b : Stmt} → ({st : State} {tr₁ tr₂ : Trace₂} → (exec b st tr₁ → exec b st tr₂ → tr₁ ≈ tr₂)) 
        → {tr₁ tr₂ tr₃ tr₄ : Trace₂} → tr₁ ≈ tr₂ → execseq (Swhile c b) tr₁ tr₃ → execseq (Swhile c b) tr₂ tr₄ → tr₃ ≈ tr₄

    execWhileDeterministic₀ _ (execWhileFalse _ _) (execWhileFalse _ _)                                     = refl 
    execWhileDeterministic₀ _ (execWhileFalse _ c＝false)   (execWhileLoop _ _ c＝true _ _) rewrite c＝false = contradiction c＝true λ ()
    execWhileDeterministic₀ _ (execWhileLoop _ _ c＝true _ _) (execWhileFalse _ c＝false)   rewrite c＝true  = contradiction c＝false λ ()
    execWhileDeterministic₀ {c} {b} h {st} {tr₁} {tr₂} (execWhileLoop _ _ _ aa x₂) (execWhileLoop _ _ _ bb x₅) ._≈_.p with execseq.p x₂ | execseq.p x₅
    ... | rexecseqNil _≡_.refl (execWhileFalse .b x₁) | rexecseqNil _≡_.refl (execWhileFalse .b x) = case _≈_.p (execseqDeterministic₀ h refl aa bb) of λ {tnil → tcons (mkBisim tnil)}

    -- ... | rexecseqNil _≡_.refl (execWhileFalse .b x₁) | rexecseqNil _≡_.refl (execWhileFalse .b x) = _≈_.p (execWhileDeterministic₁ h (execseqDeterministic₀ h refl aa bb) x₂ x₅)
    ... | rexecseqNil _≡_.refl (execWhileFalse .b x₁) | rexecseqNil _≡_.refl (execWhileLoop tr .tr₂ x x₃ x₄) = {!   !}
    ... | rexecseqNil _≡_.refl (execWhileLoop tr .tr₁ x₁ x₃ x₄) | rexecseqNil _≡_.refl (execWhileFalse .b x₆) = {!   !}
    ... | rexecseqNil _≡_.refl (execWhileLoop tr .tr₁ x₁ x₃ x₄) | rexecseqNil _≡_.refl (execWhileLoop tr₃ .tr₂ x₆ x₇ x₈) = {!   !}
-- ... | rexecseqNil x₁ x₃ | rexecseqCons .(Swhile c b) st₁ _ tr₃ tr₄ .tr₂ x₄ x₆ x₇ = {!   !}
-- ... | rexecseqCons .(Swhile c b) st₁ _ tr₃ tr₄ .tr₁ x₁ x₃ x₄ | rexecseqNil x₆ x₇ = {!   !}
    ... | rexecseqCons .(Swhile c b) st₁ _ tr₃ tr₄ .tr₁ _≡_.refl _≡_.refl x₄ | rexecseqCons .(Swhile c b) st₂ _ tr₅ tr₆ .tr₂ _≡_.refl _≡_.refl x₈ 
        = case _≈_.p (execseqDeterministic₀ h refl aa bb) of λ {(tcons x) → tcons (execWhileDeterministic₁ h x x₄ x₈)}
    -- = _≈_.p (execWhileDeterministic₁ (execseqDeterministic₀ h refl aa bb) x₂ x₅)
    -- = rexecWhileDeterministic₁ next (execseq.p x₂) (execseq.p x₅)
    -- rexecWhileDeterministic₁ (_≈_.p (execseqDeterministic₀ h refl (aa) (bb))) (x₂ .execseq.p) (x₅ .execseq.p)
    
    execWhileDeterministic₁ {c} {b} h x x₁ x₂ ._≈_.p with (execseq.p x₁) | (execseq.p x₂) | _≈_.p x
    -- ... | rexecseqNil _≡_.refl x₄ | rexecseqNil _≡_.refl x₆ | tnil = _≈_.p (execWhileDeterministic₀ h x₄ x₆)
    ... | rexecseqNil _≡_.refl (execWhileFalse .b x₃) | rexecseqNil _≡_.refl (execWhileFalse .b x₄) | tnil = tcons x
    ... | rexecseqNil _≡_.refl (execWhileFalse .b x₃) | rexecseqNil _≡_.refl (execWhileLoop tr _ x₄ x₅ x₆) | tnil = {!   !}
    ... | rexecseqNil _≡_.refl (execWhileLoop tr _ x₃ x₄ x₅) | rexecseqNil _≡_.refl (execWhileFalse .b x₆) | tnil = {!   !}
    ... | rexecseqNil _≡_.refl a@(execWhileLoop tr _ x₃ x₄ x₅) | rexecseqNil _≡_.refl b@(execWhileLoop tr₁ _ x₆ x₇ x₈) | tnil = _≈_.p (execWhileDeterministic₀ h a b)
    ... | rexecseqNil _≡_.refl x₄ | rexecseqCons .(Swhile c b) st _ tr₂ tr₃ _ _≡_.refl x₆ x₇ | ()
    ... | rexecseqCons .(Swhile c b) st _ tr₂ tr₃ _ _≡_.refl x₄ x₅ | rexecseqNil _≡_.refl x₇ | ()
    ... | rexecseqCons .(Swhile c b) st _ tr₂ tr₃ _ _≡_.refl _≡_.refl x₅ | rexecseqCons .(Swhile c b) st₁ _ tr₄ tr₅ _ _≡_.refl _≡_.refl x₈ | tcons x₃ = tcons (execWhileDeterministic₁ h x₃ x₅ x₈)
                -- execWhileDeterministic₁ tnil              (execseqNil ex₁)       (execseqNil ex₂)       = execWhileDeterministic₀ h ex₁ ex₂
                -- execWhileDeterministic₁ (tcons tr₁′≈tr₂′) (execseqCons _ _ _ exseq₁) (execseqCons _ _ _ exseq₂) = tcons (♯ (execWhileDeterministic₁ (♭ tr₁′≈tr₂′) (♭ exseq₁) (♭ exseq₂)))



            -- mutual
                -- rexecWhileDeterministic₁ : {tr₁ tr₂ tr₃ tr₄ : Trace₂} → tr₁ ≈ tr₂ → rexecseq (Swhile c b) tr₁ tr₃ → rexecseq (Swhile c b) tr₂ tr₄ → (out tr₃) r≈ (out tr₄)
                -- rexecWhileDeterministic₁ x x₁ x₂ with _≈_.p x
                -- rexecWhileDeterministic₁ x (rexecseqNil _≡_.refl x₂) (rexecseqNil _≡_.refl x₄) | tnil = _≈_.p (execWhileDeterministic₀ h x₂ x₄)
                -- rexecWhileDeterministic₁ x (rexecseqNil _≡_.refl x₂) (rexecseqCons .(Swhile c b) st _ tr₂ tr₃ _ _≡_.refl x₄ x₅) | ()
                -- rexecWhileDeterministic₁ x (rexecseqCons .(Swhile c b) st _ tr₂ tr₃ _ _≡_.refl x₂ x₃) (rexecseqNil _≡_.refl x₅) | ()
                -- rexecWhileDeterministic₁ x (rexecseqCons .(Swhile c b) st _ tr₂ tr₃ _ _≡_.refl _≡_.refl x₃) (rexecseqCons .(Swhile c b) st₁ _ tr₄ tr₅ _ _≡_.refl _≡_.refl x₆) | tcons x₁ = tcons (execWhileDeterministic₁ x₁ x₃ x₆)
                -- rexecWhileDeterministic₁ tnil aaa@(rexecseqNil x) bbb@(rexecseqNil x₁) = _≈_.p (execWhileDeterministic₀ h x x₁)
                -- rexecWhileDeterministic₁ (tcons x) (rexecseqCons _ _ _ tr′ x₁) (rexecseqCons _ _ _ tr′₁ x₂) = tcons (execWhileDeterministic₁ x x₁ x₂)
    execDeterministic : {s : Stmt} {st : State} {tr₁ tr₂ : Trace₂} 
        → exec s st tr₁ 
        → exec s st tr₂ 
        → tr₁ ≈ tr₂
    execDeterministic execSkip                           execSkip                                           = refl
    execDeterministic execAssign          execAssign                          = refl
    execDeterministic l@(execSeq _ _ _ _)                r@(execSeq _ _ _ _)                                = execSeqDeterministic₀ execDeterministic execDeterministic l r
    execDeterministic (execIfThenElseTrue _ _ seq₁)      (execIfThenElseTrue _ _ seq₂)                      = execseqDeterministic₀ execDeterministic refl seq₁ seq₂
    execDeterministic (execIfThenElseTrue _ c＝true _)   (execIfThenElseFalse _ c＝false _) rewrite c＝true  = contradiction c＝false λ ()
    execDeterministic (execIfThenElseFalse _ c＝false _) (execIfThenElseTrue _ c＝true _)   rewrite c＝false = contradiction c＝true λ ()
    execDeterministic (execIfThenElseFalse _ _ seq₁)     (execIfThenElseFalse _ _ seq₂)                     = execseqDeterministic₀ execDeterministic refl seq₁ seq₂
    execDeterministic l@(execWhileFalse _ _)           r@(execWhileFalse _ _)                           = execWhileDeterministic₀ execDeterministic l r
    execDeterministic l@(execWhileFalse _ _)           r@(execWhileLoop _ _ _ _ _)                        = execWhileDeterministic₀ execDeterministic l r
    execDeterministic l@(execWhileLoop _ _ _ _ _)        r@(execWhileFalse _ _)                           = execWhileDeterministic₀ execDeterministic l r
    execDeterministic l@(execWhileLoop _ _ _ _ _)        r@(execWhileLoop _ _ _ _ _)                        = execWhileDeterministic₀ execDeterministic l r 