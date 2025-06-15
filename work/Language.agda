{-# OPTIONS --without-K #-}

open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary.Decidable
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Function.Base using (case_of_)

module work.Language where
    Id : Set
    Id = ℕ

    Val : Set
    Val = ℕ

    State : Set
    State = Id → Val

    isTrue : Val → Bool
    isTrue zero = false
    isTrue (suc x) = true

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
