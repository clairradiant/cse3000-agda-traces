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

open import work.GuardedTraces
open import work.Language

open Trace₂

module work.BigRel2 where
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

    module examples where
        -- Common definitions
        startState : State
        startState = λ {0 → 0 ; _ → 42}

        -- Proof tree for a program that loops forever
        module loopForever where
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


        -- Proof tree of a program generating the naturals (exloopincrementing)
        -- As well as a proof the trace actually does this (incrementingAlwaysIncrements)        
        module increasing where
            add1 : Expr
            add1 x = x 0 + 1

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

    -- Helper functions for applying transitivity and symmetry
    linkH : ∀ {i₁ i₂ i₃ i₄} → i₁ ≈ i₂ → i₁ ≈ i₃ → i₂ ≈ i₄ → i₃ ≈ i₄
    linkH h a b = trans (sym a) (trans h b)

    linkHr : ∀ {i₁ i₂ i₃ i₄} → i₁ r≈ i₂ → i₁ r≈ i₃ → i₂ r≈ i₄ → i₃ r≈ i₄
    linkHr h a b = rtrans (rsym a) (rtrans h b)
    

    execDeterministic : {s : Stmt} {st : State} {tr₁ tr₂ : Trace₂} 
        → exec s st tr₁ 
        → exec s st tr₂ 
        → tr₁ ≈ tr₂


    -- The calls to linkH are enough to show that both sides of bisim are either tnil or tcons (or absurd), allowing me to match
    execseqDeterministic₀ : {s : Stmt} {tr₁ tr₂ tr₃ tr₄ : Trace₂} → tr₁ ≈ tr₂ → execseq s tr₁ tr₃ → execseq s tr₂ tr₄ → tr₃ ≈ tr₄
    execseqDeterministic₀ tr₁≈tr₂ exs₁ exs₂ ._≈_.p with (execseq.p exs₁) | execseq.p (exs₂)

    -- Nil-nil case presented in the paper showing Agda cannot identify tnil? must be a tnil due to unification problems
    -- ... | rexecseqNil res₁ ex₁ | rexecseqNil res₂ ex₂ with _≈_.p tr₁≈tr₂
    -- ... | tnil? = {! tnil?  !}

    -- Nil-nil case with "massaging" of known bisimilarities to convince Agda bisimilarity must be a tnil
    ... | rexecseqNil res₁ ex₁ | rexecseqNil res₂ ex₂ with linkH tr₁≈tr₂ res₁ res₂ ._≈_.p
    ... | tnil = _≈_.p (execDeterministic ex₁ ex₂)

    -- Nil-cons and cons-nil cases must be shown to be absurd by "massaging" bisimilarities
    -- As opposed to musical and sized, where Agda can exclude these cases automatically
    execseqDeterministic₀ x₁ x₂ x₃ ._≈_.p | rexecseqNil a x₅ | rexecseqCons st _ tr₂ tr₃ _ b x₇ x₈ with linkH x₁ a b ._≈_.p
    ... | ()
    execseqDeterministic₀ x₁ x₂ x₃ ._≈_.p | rexecseqCons st _ tr₂ tr₃ _ a x₅ x₆ | rexecseqNil b x₈ with linkH x₁ a b ._≈_.p
    ... | ()

    -- Unfillable hole: The hole needs to be reshaped (using reshape) to something with tcons on both sides,
    --     so that tcons can be introduced for the recursive call. However, application of reshape means the call is not guarded
    --     and as such termination checking fails, even though I argue the definition is still productive.
    --     See TermCheck.agda for a reduced example of productive but not guarded functions.
    execseqDeterministic₀ x₁ x₂ x₃ ._≈_.p | rexecseqCons st _ tr₂ tr₃ _ a c x₆ | rexecseqCons st₁ _ tr₄ tr₅ _ b d x₉ with linkH x₁ a b ._≈_.p
    ... | tcons n = let reshape = λ y → linkHr y (rsym (c ._≈_.p)) (rsym (d ._≈_.p)) in reshape (tcons (execseqDeterministic₀ n x₆ x₉))

    -- Implementation of execWhileDeterministic₀ was not reached due to failure of execseqDeterministic₀
    postulate
        execWhileDeterministic₀ : {c : Expr} {b : Stmt} {st : State} {tr₁ tr₂ : Trace₂} → exec (Swhile c b) st tr₁ → exec (Swhile c b) st tr₂ → tr₁ ≈ tr₂


    execDeterministic execSkip                           execSkip                                           = refl
    execDeterministic execAssign                         execAssign                                         = refl
    execDeterministic (execSeq a b c d)                  (execSeq e f g h)                                  = execseqDeterministic₀ (execDeterministic c g) d h
    execDeterministic (execIfThenElseTrue _ _ seq₁)      (execIfThenElseTrue _ _ seq₂)                      = execseqDeterministic₀ refl seq₁ seq₂
    execDeterministic (execIfThenElseTrue _ c＝true _)   (execIfThenElseFalse _ c＝false _) rewrite c＝true  = contradiction c＝false λ ()
    execDeterministic (execIfThenElseFalse _ c＝false _) (execIfThenElseTrue _ c＝true _)   rewrite c＝false = contradiction c＝true λ ()
    execDeterministic (execIfThenElseFalse _ _ seq₁)     (execIfThenElseFalse _ _ seq₂)                     = execseqDeterministic₀ refl seq₁ seq₂
    execDeterministic l@(execWhileFalse _ _)             r@(execWhileFalse _ _)                               = execWhileDeterministic₀ l r
    execDeterministic l@(execWhileFalse _ _)             r@(execWhileLoop _ _ _ _ _)                          = execWhileDeterministic₀ l r
    execDeterministic l@(execWhileLoop _ _ _ _ _)        r@(execWhileFalse _ _)                             = execWhileDeterministic₀ l r
    execDeterministic l@(execWhileLoop _ _ _ _ _)        r@(execWhileLoop _ _ _ _ _)                        = execWhileDeterministic₀ l r 