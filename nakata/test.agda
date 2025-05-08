{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Agda.Builtin.Nat

data Coℕ : Set where
    zero : Coℕ
    suc  : ∞ Coℕ → Coℕ

data NatToSucNat : (n : Nat) → (m : Coℕ) → Set where
    zerois : NatToSucNat 0 (suc (♯ zero))
    sucis  : (n : Nat) (m : ∞ Coℕ) → NatToSucNat n (♭ m) → NatToSucNat (suc n) (suc m)

test : NatToSucNat 0 (suc {! ♯_  !})
test = zerois