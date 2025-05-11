{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Codata.Musical.Notation
open import Data.Nat using (ℕ; zero; suc)
open import Function.Base using (case_of_)
open import Data.Nat using (_+_)
open import Relation.Nullary using (contradiction)

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

            execAssign : ∀ (id) (a) (st)
                → exec (Sassign id a) st (tcons st (♯ tnil (update id (a st) st)))

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

            execWhileFalse : (c : Expr) (b : Stmt) (st : State) 
                → isTrue (c st) ≡ false 
                → exec (Swhile c b) st (tcons st (♯ tcons st (♯ tnil st)))

            execWhileLoop : (c : Expr) (b : Stmt) (st : State) (tr tr′ : Trace₁) 
                → (isTrue (c st)) ≡ true 
                → execseq b (tcons st (♯ tnil st)) tr 
                → execseq (Swhile c b) tr tr′ 
                → exec (Swhile c b) st tr′

        data execseq : Stmt → Trace₁ → Trace₁ → Set where
            execseqNil : (st : State) (s : Stmt) (tr : Trace₁) 
                → exec s st tr 
                → execseq s (tnil st) tr
                
            execseqCons : (st : State) (s : Stmt) (tr tr′ : Trace₁) 
                → execseq s tr tr′ 
                → execseq s (tcons st (♯ tr)) (tcons st (♯ tr′))

    add1 : Expr
    add1 x = x 0 + 1

    startState : State
    startState = λ {0 → 0 ; _ → 42}

    ex : exec (Sassign 0 add1) startState (tcons startState {!   !})
    ex = execAssign 0 add1 startState

    -- ex1 : Stmt
    -- ex1 = Sseq (Sassign 0 add1) (Sassign 0 add1)

    -- ex3 : Trace₁
    -- ex3 = tnil ex2

    -- -- ex4 : exec ex1 ex2 {!   !}
    -- -- ex4 = execSeq 
    -- --     (Sassign 0 add1) 
    -- --     (Sassign 0 add1) 
    -- --     ex2 
    -- --     (tcons ex2 (♯ tnil (update 0 (add1 ex2) ex2))) 
    -- --     (tcons ex2 
    -- --         (♯ tcons ((update 0 (add1 ex2) ex2)) 
    -- --         (♯ tnil (update 0 (add1 (update 0 (add1 ex2) ex2)) ((update 0 (add1 ex2) ex2)))))) 
    -- --     {!  !}
    -- --     {! execseqCons ? ? ? ? ?  !}

    -- ex5 : Stmt
    -- ex5 = Sassign 0 add1

    -- ex6 : exec ex5 ex2 (tcons ex2 {! ♯ tnil ?  !})
    -- ex6 = execAssign 0 add1 ex2

    -- For any statement, given a proof that execution of this statement from a state results in two bisimilar traces, then given two bisimilar traces, executing s starting from these two traces results in traces which are again bisimilar
    execseqDeterministic₀ : {s : Stmt} → ({st : State} {tr₁ tr₂ : Trace₁} → exec s st tr₁ → exec s st tr₂ → tr₁ ≈ tr₂) → ({tr₁ tr₂ tr₃ tr₄ : Trace₁} → tr₁ ≈ tr₂ → execseq s tr₁ tr₃ → execseq s tr₂ tr₄ → tr₃ ≈ tr₄)
    execseqDeterministic₀ x tnil (execseqNil _ _ _ x₁) (execseqNil _ _ _ x₂) = x x₁ x₂
    execseqDeterministic₀ x (tcons tr₁′≈tr₂′) (execseqCons _ _ _ _ tr₁⇒tr₃) (execseqCons _ _ _ _ tr₂⇒tr₄) = tcons (♯ execseqDeterministic₀ x (♭ tr₁′≈tr₂′) tr₁⇒tr₃ tr₂⇒tr₄)

    execSeqDeterministic₀ : {s₁ s₂ : Stmt} → ({st : State} {tr₁ tr₂ : Trace₁} → exec s₁ st tr₁ → exec s₁ st tr₂ → tr₁ ≈ tr₂)
        → ({st : State} {tr₁ tr₂ : Trace₁} → exec s₂ st tr₁ → exec s₂ st tr₂ → tr₁ ≈ tr₂)
        → {st : State} {tr₁ tr₂ : Trace₁} → exec (Sseq s₁ s₂) st tr₁ → exec (Sseq s₁ s₂) st tr₂ → tr₁ ≈ tr₂
    execSeqDeterministic₀ h₁ h₂ (execSeq _ _ _ tr _ x₁ x) (execSeq _ _ _ tr₁ _ x₂ x₃) = execseqDeterministic₀ h₂ (h₁ x₁ x₂) x x₃

    execWhileDeterministic₀ : {c : Expr} {b : Stmt} → ({st : State} {tr₁ tr₂ : Trace₁} → (exec b st tr₁ → exec b st tr₂ → tr₁ ≈ tr₂))
        → {st : State} {tr₁ tr₂ : Trace₁} → exec (Swhile c b) st tr₁ → exec (Swhile c b) st tr₂ → tr₁ ≈ tr₂
    execWhileDeterministic₀ x (execWhileFalse _ _ _ x₁) (execWhileFalse _ _ _ x₂) = tcons (♯ tcons (♯ tnil))
    execWhileDeterministic₀ x (execWhileFalse _ _ _ x₁) (execWhileLoop _ _ _ tr _ x₂ x₃ x₄) rewrite x₁ = contradiction x₂ λ ()
    execWhileDeterministic₀ x (execWhileLoop _ _ _ tr _ x₁ x₃ x₄) (execWhileFalse _ _ _ x₂) rewrite x₁ = contradiction x₂ λ ()
    execWhileDeterministic₀ x (execWhileLoop _ _ _ tr _ x₁ x₃ x₄) (execWhileLoop _ _ _ tr₁ _ x₂ x₅ x₆) = {!   !}
        where
            execWhileDeterministic₁ : {!   !}

