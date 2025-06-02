{-# OPTIONS --guardedness #-}

open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary.Decidable
open import Data.Bool using (Bool)
open import nakata.Traces
open import Function.Base using (case_of_)

module nakata.Language where
    Expr : Set
    Expr = State → Val

    data Stmt : Set where
        Sskip : Stmt
        Sassign : Id → Expr → Stmt
        Sseq : Stmt → Stmt → Stmt
        Sifthenelse : Expr → Stmt → Stmt → Stmt
        Swhile : Expr → Stmt → Stmt

    update : Id → Val → State → State
    update x v st  = λ y → case (x ≟ y) of λ {(yes _) → v ; (no _) → st y}
