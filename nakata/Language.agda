{-# OPTIONS --guardedness #-}

open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary.Decidable
open import Data.Bool using (Bool)
open import Traces
open import Function.Base using (case_of_)

module Language where
    Expr : Set
    Expr = State → Val

    -- -- concrete expressions (not part of original paper)
    -- data Id : Set where
    --     mkId : List Char → Id 

    -- data Exp : Set where
    --     eBool : (b : Bool) → Exp 
    --     eInt  : (i : ℤ) → Exp
    --     eId   : (i : Id) → Exp 


    data Stmt : Set where
        Sskip : Stmt
        Sassign : Id → Expr → Stmt
        Sseq : Stmt → Stmt → Stmt
        Sifthenelse : Expr → Stmt → Stmt → Stmt
        Swhile : Expr → Stmt → Stmt

    update : Id → Val → State → State
    update x v st  = λ y → case (x ≟ y) of λ {(yes _) → v ; (no _) → st y}
