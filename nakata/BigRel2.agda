{-# OPTIONS --guardedness --allow-incomplete-matches --allow-unsolved-metas #-}

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; subst₂) renaming (trans to eqTrans; sym to eqSym)
open import Codata.Musical.Notation
open import Data.Nat using (ℕ; zero; suc; _<?_)
open import Function.Base using (case_of_)
open import Data.Nat using (_+_)
open import Relation.Nullary using (contradiction)
open import Relation.Nullary.Decidable
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product
open import Data.Empty

open import nakata.Traces
open import nakata.Language

open Trace₂

module nakata.BigRel2 where
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
                → tr ≈ mkTr (tnil st)
                → exec s st tr′
                → rexecseq s tr tr′

            rexecseqCons : {s : Stmt} (st : State) (tr₁ tr₂ tr₃ tr′ : Trace₂)
                → tr₁ ≈ mkTr (tcons st tr₂) 
                → tr′ ≈ mkTr (tcons st tr₃)
                → execseq s tr₂ tr₃
                → rexecseq s tr₁ tr′

        record execseq (s : Stmt) (tr tr′ : Trace₂) : Set where
            coinductive
            constructor mkExecseq
            field
                p : rexecseq s tr tr′

    open Setoid setoid₂ using (refl; sym; trans)
    open Setoid setoid₂r using () renaming (refl to rrefl; sym to rsym; trans to rtrans)

    add1 : Expr
    add1 x = x 0 + 1

    startState : State
    startState = λ {0 → 0 ; _ → 42}

    loopforevertrace : Trace₂
    loopforevertrace .out = tcons startState loopforevertrace
        
    -- Proof tree of a program that loops forever
    exloopforever : exec (Swhile (λ _ → 1) Sskip) startState loopforevertrace
    exloopforever = execWhileLoop (mkTr (tcons startState (mkTr (tnil startState)))) loopforevertrace _≡_.refl 
        (mkExecseq (rexecseqCons startState _ (mkTr (tnil startState)) _ _ refl refl (mkExecseq (rexecseqNil refl execSkip))))
        forever
        where
            forever : execseq (Swhile (λ _ → 1) Sskip) (mkTr (tcons startState (mkTr (tnil startState)))) loopforevertrace
            forever .execseq.p = rexecseqCons startState _ (mkTr (tnil startState)) _ _ refl (mkBisim rrefl) (mkExecseq (rexecseqNil (mkBisim tnil) exloopforever))

    next : State → State
    next st = update 0 (add1 st) st

    incrementingFrom : State → Trace₂
    incrementingFrom st .out = tcons st (mkTr (tcons st (incrementingFrom (next st))))

    incrementingtrace : Trace₂
    incrementingtrace = incrementingFrom startState

    exloopincrementing : exec (Swhile (λ _ → 1) (Sassign 0 add1)) startState incrementingtrace
    exloopincrementing = t startState
        where
            t : (st : State) → exec (Swhile (λ _ → 1) (Sassign 0 add1)) st (incrementingFrom st)
            t₁ : (st : State) → execseq (Swhile (λ _ → 1) (Sassign 0 add1)) (mkTr (tcons st (mkTr (tcons st (mkTr (tnil (next st))))))) (incrementingFrom st)

            t st = execWhileLoop
                (mkTr (tcons st (mkTr (tcons st (mkTr (tnil (next st))))))) 
                _ 
                _≡_.refl 
                (mkExecseq (rexecseqCons st _ (mkTr (tnil st)) _ _ refl refl (mkExecseq (rexecseqNil refl execAssign)))) 
                (t₁ st)

            t₁ st .execseq.p = rexecseqCons st _ _ _ _ refl (mkBisim rrefl) (mkExecseq (rexecseqCons st _ _ _ _ refl refl (mkExecseq (rexecseqNil refl (t (next st))))))


    mutual
        record increasing (id : Id) (v : Val) (tr : Trace₂) : Set where
            coinductive
            field
                p : rincreasing id v tr

        data rincreasing : Id → Val → Trace₂ → Set where
            rinc : {id : Id} {v : Val} {st : State} {tr tr₁ : Trace₂} 
                → st id ≡ v 
                → tr₁ ≈ mkTr (tcons st (mkTr (tcons st tr)))
                → increasing id (suc v) tr
                → rincreasing id v tr₁


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
            forever {st} x .increasing.p = rinc x (mkBisim rrefl) (forever (lem₂ st x))
         

    tnil≠tcons : {st₁ st₂ : State} {tr : Trace₂} → (tnil st₁) ≡ (tcons st₂ tr) → ⊥
    tnil≠tcons ()

    linkH : ∀ {i₁ i₂ i₃ i₄} → i₁ ≈ i₂ → i₁ ≈ i₃ → i₂ ≈ i₄ → i₃ ≈ i₄
    linkH h a b = trans (sym a) (trans h b)

    linkHr : ∀ {i₁ i₂ i₃ i₄} → i₁ r≈ i₂ → i₁ r≈ i₃ → i₂ r≈ i₄ → i₃ r≈ i₄
    linkHr h a b = rtrans (rsym a) (rtrans h b)
    

    execDeterministic : {s : Stmt} {st : State} {tr₁ tr₂ : Trace₂} 
        → exec s st tr₁ 
        → exec s st tr₂ 
        → tr₁ ≈ tr₂

        -- This used to be mutual, but I merged it into a single function in an attempt to help the termination checker
        -- rexecseqDeterministic₀ : {s : Stmt}
        --     → ({st : State} {tr₁ tr₂ : Trace₂} → exec s st tr₁ → exec s st tr₂ → tr₁ ≈ tr₂) 
        --     → ({tr₁ tr₂ tr₃ tr₄ : Trace₂} → tr₁ ≈ tr₂ → rexecseq s tr₁ tr₃ → rexecseq s tr₂ tr₄ → (out tr₃) r≈ (out tr₄))
        -- rexecseqDeterministic₀ x x₁ (rexecseqNil a x₃) (rexecseqNil b x₅) with linkH x₁ a b ._≈_.p
        -- ... | tnil = _≈_.p (x x₃ x₅)
        -- rexecseqDeterministic₀ x x₁ (rexecseqNil a x₃) (rexecseqCons st _ tr₂ tr₃ _ b x₅ x₆) with linkH x₁ a b ._≈_.p
        -- ... | ()
        -- rexecseqDeterministic₀ x x₁ (rexecseqCons st _ tr₂ tr₃ _ a _ x₄) (rexecseqNil b x₆) with linkH x₁ a b ._≈_.p
        -- ... | ()
        -- rexecseqDeterministic₀ x x₁ (rexecseqCons st _ tr₂ tr₃ _ a c x₄) (rexecseqCons st₁ _ tr₄ tr₅ _ b d x₇) with linkH x₁ a b ._≈_.p
        -- -- ... | tcons x₂ = {!   !}
        -- ... | a@(tcons x₂) = linkHr (tcons (execseqDeterministic₀ x x₂ x₄ x₇)) (rsym (c ._≈_.p)) (rsym (d ._≈_.p))
        -- -- tcons (execseqDeterministic₀ x x₂ x₄ x₇)

        -- The calls to linkH are enough to show that both sides of bisim are either tnil or tcons (or absurd), allowing me to match
    execseqDeterministic₀ : {s : Stmt}
        -- → ({st : State} {tr₁ tr₂ : Trace₂} → exec s st tr₁ → exec s st tr₂ → tr₁ ≈ tr₂) 
        → ({tr₁ tr₂ tr₃ tr₄ : Trace₂} → tr₁ ≈ tr₂ → execseq s tr₁ tr₃ → execseq s tr₂ tr₄ → tr₃ ≈ tr₄)
    execseqDeterministic₀ tr₁≈tr₂ exs₁ exs₂ ._≈_.p with (execseq.p exs₁) | execseq.p (exs₂)
    ... | rexecseqNil res₁ ex₁ | rexecseqNil res₂ ex₂ with _≈_.p tr₁≈tr₂
    ... | tnil? = {! tnil?  !}
    execseqDeterministic₀ x₁ x₂ x₃ ._≈_.p | rexecseqNil a x₅ | rexecseqCons st _ tr₂ tr₃ _ b x₇ x₈ = {!   !}
    -- ... | rexecseqNil a x₅ | rexecseqNil b x₇ with linkH x₁ a b ._≈_.p
    -- ... | tnil = _≈_.p (execDeterministic x₅ x₇)
    -- execseqDeterministic₀ x₁ x₂ x₃ ._≈_.p | rexecseqNil a x₅ | rexecseqCons st _ tr₂ tr₃ _ b x₇ x₈ with linkH x₁ a b ._≈_.p
    -- ... | ()
    -- execseqDeterministic₀ x₁ x₂ x₃ ._≈_.p | rexecseqCons st _ tr₂ tr₃ _ a x₅ x₆ | rexecseqNil b x₈ with linkH x₁ a b ._≈_.p
    -- ... | ()
    execseqDeterministic₀ x₁ x₂ x₃ ._≈_.p | rexecseqCons st _ tr₂ tr₃ _ a c x₆ | rexecseqCons st₁ _ tr₄ tr₅ _ b d x₉ with linkH x₁ a b ._≈_.p
    -- ... | tcons x with _≈_.p c | _≈_.p d = ?
    -- ... | tcons x₄ | tcons x₅ = tcons (execseqDeterministic₀ {!   !} {!   !} {!   !})
    -- with linkH x₁ a b ._≈_.p
    -- ... | tcons x₂ = {!   !}
    ... | tcons n = let reshape = λ y → linkHr y (rsym (c ._≈_.p)) (rsym (d ._≈_.p)) in reshape {!   !}
    -- reshape (tcons ((execseqDeterministic₀ n x₆ x₉)))
            -- linkHr (tcons (execseqDeterministic₀ n x₆ x₉)) (rsym (c ._≈_.p)) (rsym (d ._≈_.p))
        -- execseqDeterministic₀ x {tr₁} {tr₂} x₁ x₂ x₃ ._≈_.p with out tr₁ in eq₁ | out tr₂ in eq₂ | (_≈_.p x₁) | (execseq.p x₂) | (execseq.p x₃) 
        -- ... | tnil st | tnil st₁ | tnil | rexecseqNil a b | rexecseqNil c d = {!   !}
    -- execseqDeterministic₀ h tnil              (execseqNil ex₁)         (execseqNil ex₂)         = h ex₁ ex₂
    -- execseqDeterministic₀ h (tcons tr₁′≈tr₂′) (execseqCons _ _ _ tr₁⇒tr₃) (execseqCons _ _ _ tr₂⇒tr₄) = tcons (♯ execseqDeterministic₀ h (♭ tr₁′≈tr₂′) (♭ tr₁⇒tr₃) (♭ tr₂⇒tr₄))

    execSeqDeterministic₀ : {s₁ s₂ : Stmt} 
        -- → ({st : State} {tr₁ tr₂ : Trace₂} → exec s₁ st tr₁ → exec s₁ st tr₂ → tr₁ ≈ tr₂)
        -- → ({st : State} {tr₁ tr₂ : Trace₂} → exec s₂ st tr₁ → exec s₂ st tr₂ → tr₁ ≈ tr₂)
        → {st : State} {tr₁ tr₂ : Trace₂} → exec (Sseq s₁ s₂) st tr₁ → exec (Sseq s₁ s₂) st tr₂ → tr₁ ≈ tr₂
    execSeqDeterministic₀ (execSeq _ _ ex₁ exseq₁) (execSeq _ _ ex₂ exseq₂) = execseqDeterministic₀ (execDeterministic ex₁ ex₂) exseq₁ exseq₂
    postulate
        execWhileDeterministic₀ : {c : Expr} {b : Stmt} → ({st : State} {tr₁ tr₂ : Trace₂} → (exec b st tr₁ → exec b st tr₂ → tr₁ ≈ tr₂))
            → {st : State} {tr₁ tr₂ : Trace₂} → exec (Swhile c b) st tr₁ → exec (Swhile c b) st tr₂ → tr₁ ≈ tr₂
        execWhileDeterministic₁ : {c : Expr} {b : Stmt} → ({st : State} {tr₁ tr₂ : Trace₂} → (exec b st tr₁ → exec b st tr₂ → tr₁ ≈ tr₂)) 
            → {tr₁ tr₂ tr₃ tr₄ : Trace₂} → tr₁ ≈ tr₂ → execseq (Swhile c b) tr₁ tr₃ → execseq (Swhile c b) tr₂ tr₄ → tr₃ ≈ tr₄

    -- With propositional equality, this would have worked
    -- execWhileDeterministic₁ x x₁ x₂ x₃ ._≈_.p with execseq.p x₂ | execseq.p x₃
    -- ... | rexecseqNil _ x₅ | rexecseqNil _ x₇ with _≈_.p x₁ in eq
    -- execWhileDeterministic₁ x x₁ x₂ x₃ ._≈_.p | rexecseqNil _≡_.refl (execWhileFalse _ _) | rexecseqNil _≡_.refl (execWhileFalse _ _) | tnil = tcons x₁
    -- execWhileDeterministic₁ x x₁ x₂ x₃ ._≈_.p | rexecseqNil _≡_.refl (execWhileFalse _ x₄) | rexecseqNil _≡_.refl (execWhileLoop _ _ x₅ _ _) | tnil rewrite x₄ = contradiction x₅ λ ()
    -- execWhileDeterministic₁ x x₁ x₂ x₃ ._≈_.p | rexecseqNil _≡_.refl (execWhileLoop _ _ x₄ _ _) | rexecseqNil _≡_.refl (execWhileFalse _ x₇) | tnil rewrite x₄ = contradiction x₇ λ ()
    -- execWhileDeterministic₁ x x₁ x₂ x₃ ._≈_.p | rexecseqNil _≡_.refl (execWhileLoop _ _ _ x₅ x₆) | rexecseqNil _≡_.refl (execWhileLoop _ _ _ x₈ x₉) | tnil with execseq.p x₅ | execseq.p x₈
    -- ... | rexecseqCons _ _ _ _ _ _≡_.refl _≡_.refl x₁₂ | rexecseqCons _ _ _ _ _ _≡_.refl _≡_.refl x₁₅ with execseq.p x₁₂ | execseq.p x₁₅
    -- ... | rexecseqNil _≡_.refl x₁₁ | rexecseqNil _≡_.refl x₁₄ with execseq.p x₆ | execseq.p x₉
    -- ... | rexecseqCons _ _ _ _ _ _≡_.refl _≡_.refl x₁₆ | rexecseqCons _ _ _ _ _ _≡_.refl _≡_.refl x₁₉ = tcons (execWhileDeterministic₁ x (x x₁₁ x₁₄) x₁₆ x₁₉)
    -- execWhileDeterministic₁ x x₁ x₂ x₃ ._≈_.p | rexecseqNil _≡_.refl _ | rexecseqCons _ _ _ _ _ _≡_.refl _ _ with _≈_.p x₁
    -- ... | ()
    -- execWhileDeterministic₁ x x₁ x₂ x₃ ._≈_.p | rexecseqCons _ _ _ _ _ _≡_.refl _ _ | rexecseqNil _≡_.refl _ with _≈_.p x₁
    -- ... | ()
    -- execWhileDeterministic₁ x x₁ x₂ x₃ ._≈_.p | rexecseqCons _ _ _ _ _ _≡_.refl _≡_.refl x₆ | rexecseqCons _ _ _ _ _ _≡_.refl _≡_.refl x₉ with _≈_.p x₁
    -- ... | tcons x₄ = tcons (execWhileDeterministic₁ x x₄ x₆ x₉)

    -- execWhileDeterministic₀ _ (execWhileFalse _ _) (execWhileFalse _ _) = refl
    -- execWhileDeterministic₀ _ (execWhileFalse _ x₁) (execWhileLoop _ _ x₂ _ _) rewrite x₁ = contradiction x₂ (λ ())
    -- execWhileDeterministic₀ _ (execWhileLoop _ _ x₁ _ _) (execWhileFalse _ x₄) rewrite x₁ = contradiction x₄ λ ()
    -- execWhileDeterministic₀ x (execWhileLoop _ _ _ x₂ x₃) (execWhileLoop _ _ _ x₅ x₆) ._≈_.p with execseq.p x₂ | execseq.p x₅
    -- ... | rexecseqCons _ _ _ _ _ _≡_.refl _≡_.refl x₉ | rexecseqCons _ _ _ _ _ _≡_.refl _≡_.refl x₁₂ with execseq.p x₉ | execseq.p x₁₂
    -- ... | rexecseqNil _≡_.refl x₁₄ | rexecseqNil _≡_.refl x₁₆ with execseq.p x₃ | execseq.p x₆
    -- ... | rexecseqCons _ _ _ _ _ _≡_.refl  _≡_.refl x₁₀ | rexecseqCons _ _ _ _ _  _≡_.refl  _≡_.refl x₁₅ = tcons (execWhileDeterministic₁ x (x x₁₄ x₁₆) x₁₀ x₁₅)


    execDeterministic execSkip                           execSkip                                           = refl
    execDeterministic execAssign          execAssign                          = refl
    execDeterministic l@(execSeq _ _ _ _)                r@(execSeq _ _ _ _)                                = execSeqDeterministic₀ l r
    execDeterministic (execIfThenElseTrue _ _ seq₁)      (execIfThenElseTrue _ _ seq₂)                      = execseqDeterministic₀ refl seq₁ seq₂
    execDeterministic (execIfThenElseTrue _ c＝true _)   (execIfThenElseFalse _ c＝false _) rewrite c＝true  = contradiction c＝false λ ()
    execDeterministic (execIfThenElseFalse _ c＝false _) (execIfThenElseTrue _ c＝true _)   rewrite c＝false = contradiction c＝true λ ()
    execDeterministic (execIfThenElseFalse _ _ seq₁)     (execIfThenElseFalse _ _ seq₂)                     = execseqDeterministic₀ refl seq₁ seq₂
    execDeterministic l@(execWhileFalse _ _)           r@(execWhileFalse _ _)                               = execWhileDeterministic₀ execDeterministic l r
    execDeterministic l@(execWhileFalse _ _)           r@(execWhileLoop _ _ _ _ _)                          = execWhileDeterministic₀ execDeterministic l r
    execDeterministic l@(execWhileLoop _ _ _ _ _)        r@(execWhileFalse _ _)                             = execWhileDeterministic₀ execDeterministic l r
    execDeterministic l@(execWhileLoop _ _ _ _ _)        r@(execWhileLoop _ _ _ _ _)                        = execWhileDeterministic₀ execDeterministic l r 