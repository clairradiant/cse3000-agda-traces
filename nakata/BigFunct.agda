{-# OPTIONS --guardedness #-}

open import nakata.MusicalTraces
open Trace₁
open import nakata.Language
open import Data.Bool using (Bool; true; false)
open import Codata.Musical.Notation
open import Data.Nat using (ℕ; zero; suc; _<?_; _+_)
open import Function.Base using (case_of_)
open import Relation.Nullary.Decidable

-- Functional semantics of the language. Only implemented for Musical coinduction due to time constraints
module nakata.BigFunct where
    loop : (State → Trace₁) → (State → Bool) → State → Trace₁
    loopseq : (State → Trace₁) → (State → Bool) → Trace₁ → Trace₁

    loop k p st with (p st)
    ... | true with (k st)
    ...             | (tnil st₁) = tcons st₁ (♯ loop k p st₁)
    ...             | (tcons st₁ tr) = tcons st₁ (♯ loopseq k p (♭ tr))
    loop k p st | false = tnil st

    loopseq k p (tnil st) = tcons st (♯ loop k p st)
    loopseq k p (tcons st tr) = tcons st (♯ loopseq k p (♭ tr))

    sequence : (State → Trace₁) → Trace₁ → Trace₁
    sequence k (tnil st) = k st
    sequence k (tcons st tr) = tcons st (♯ sequence k (♭ tr))

    exec : Stmt → State → Trace₁
    exec Sskip st = tnil st
    exec (Sassign id a) st = tcons st (♯ tnil (update id (a st) st))
    exec (Sseq s₁ s₂) st = sequence (exec s₂) (exec s₁ st)
    exec (Sifthenelse c t e) st with isTrue (c st)
    ... | true = tcons st (♯ exec t st)
    ... | false = tcons st (♯ exec e st)
    exec (Swhile c b) st = tcons st (♯ loop (exec b) (λ st₁ → isTrue (c st₁)) st) 

    -- Examples

    prog₁ : Stmt
    prog₁ = Sseq (Sassign 0 λ st → st 0 + 1) ((Sassign 0 λ st → st 0 + 1))

    ex₁ : Trace₁
    ex₁ = exec prog₁ λ {0 → 0 ; _ → 42}

    prog₂ : Stmt
    prog₂ = Sassign 0 λ st → st 0 + 1

    ex₂ : Trace₁
    ex₂ = exec prog₂ λ {0 → 0 ; _ → 42}


    add1 : Expr
    add1 x = x 0 + 1

    lt2 : Expr
    lt2 x  = case x 0 <? 2 of λ {(yes _) → 1 ; (no _) → 0}

    startState : State
    startState = λ {0 → 0 ; _ → 42}

    prog₃ : Stmt
    prog₃ = Swhile lt2 (Sassign 0 add1)

    ex₃ : Trace₁
    ex₃ = exec prog₃ startState