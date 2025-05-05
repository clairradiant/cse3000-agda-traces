{-# OPTIONS --guardedness #-}

open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary.Decidable
open import Data.Bool using (Bool)
open import Traces

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
    update x v st with (st x) ≟ v
    ... | yes _ = λ y → v
    ... | no _ = λ y → st y

    
