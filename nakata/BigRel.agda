{-# OPTIONS --guardedness #-}

open import Data.Bool using (Bool; true; false)
open import Codata.Musical.Notation
open import Data.Nat using (zero; suc)

open import Traces
open import Language

module BigRel where
    isTrue : Val → Bool
    isTrue zero = false
    isTrue (suc x) = true

    exec : Stmt → State → Trace
    execseq : Stmt → Trace → Trace

    exec Sskip st = tnil st
    exec (Sassign id s) st = tcons st (♯ tnil (update id (s st) st))
    exec (Sseq s₁ s₂) st = execseq s₂ (exec s₁ st)
    exec (Sifthenelse c t e) st with isTrue (c st)
    ... | true = execseq t (tcons st (♯ tnil st))
    ... | false = execseq e (tcons st (♯ tnil st))
    exec (Swhile c l) st with isTrue (c st)
    ... | true = execseq (Swhile c l) (execseq l (tcons st (♯ tnil st)))
    ... | false = tcons st (♯ tnil st)

    execseq s (tnil st) = exec s st
    execseq s (tcons st t) = tcons st (♯ execseq s (♭ t))