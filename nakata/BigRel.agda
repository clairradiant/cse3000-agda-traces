{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Codata.Musical.Notation
open import Data.Nat using (ℕ; zero; suc)
open import Function.Base using (case_of_)
open import Data.Nat using (_+_)

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
        data exec : Stmt → State → Trace₁ → Set where
            execSkip : (st : State) → exec Sskip st (tnil st)
            execAssign : (id : Id) (a : Expr) (st : State) → exec (Sassign id a) st (tcons st (♯ tnil (update id (a st) st)))
            execSeq : (s₁ s₂ : Stmt) (st : State) (tr tr′ : Trace₁) → exec s₁ st tr → execseq s₂ tr tr′ → exec (Sseq s₁ s₂) st tr′
            execIfThenElseTrue : (c : Expr) (t e : Stmt) (st : State) (tr : Trace₁) → isTrue (c st) ≡ true → execseq t (tcons st (♯ tnil st)) tr → exec (Sifthenelse c t e) st tr
            execIfThenElseFalse : (c : Expr) (t e : Stmt) (st : State) (tr : Trace₁) → isTrue (c st) ≡ false → execseq e (tcons st (♯ tnil st)) tr → exec (Sifthenelse c t e) st tr
            execWhileFalse : (c : Expr) (b : Stmt) (st : State) → isTrue (c st) ≡ false → exec (Swhile c b) st (tcons st (♯ tcons st (♯ tnil st)))
            execWhileLoop : (c : Expr) (b : Stmt) (st : State) (tr tr′ : Trace₁) → (isTrue (c st)) ≡ true → execseq b (tcons st (♯ tnil st)) tr → execseq (Swhile c b) tr tr′ → exec (Swhile c b) st tr′

        data execseq : Stmt → Trace₁ → Trace₁ → Set where
            execseqNil : (st : State) (s : Stmt) (tr : Trace₁) → exec s st tr → execseq s (tnil st) tr
            execseqCons : (st : State) (s : Stmt) (tr tr′ : Trace₁) → execseq s tr tr′ → execseq s (tcons st (♯ tr)) (tcons st (♯ tr′))

    add1 : Expr
    add1 x = x 0 + 1

    ex1 : Stmt
    ex1 = Sseq (Sassign 0 add1) (Sassign 0 add1)

    ex2 : State
    ex2 = λ {0 → 0 ; _ → 42}

    ex3 : Trace₁
    ex3 = tnil ex2

    -- ex4 : exec ex1 ex2 {!   !}
    -- ex4 = execSeq 
    --     (Sassign 0 add1) 
    --     (Sassign 0 add1) 
    --     ex2 
    --     (tcons ex2 (♯ tnil (update 0 (add1 ex2) ex2))) 
    --     (tcons ex2 
    --         (♯ tcons ((update 0 (add1 ex2) ex2)) 
    --         (♯ tnil (update 0 (add1 (update 0 (add1 ex2) ex2)) ((update 0 (add1 ex2) ex2)))))) 
    --     {!  !}
    --     {! execseqCons ? ? ? ? ?  !}

    ex5 : Stmt
    ex5 = Sassign 0 add1

    ex6 : exec ex5 ex2 (tcons ex2 {! ♯ tnil ?  !})
    ex6 = execAssign 0 add1 ex2