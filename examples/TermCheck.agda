{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Data.Nat

-- Example module showing limitation of guardedness as a productivity condition
module examples.TermCheck where
    mutual
        data Coℕr : Set where
            zero : Coℕr
            suc : Coℕ → Coℕr

        record Coℕ : Set where
            coinductive
            constructor mkCoℕ
            field
                out : Coℕr

    open Coℕ

    id : ∀ {a} {A : Set a} → A → A
    id x = x 

    three : Coℕ
    three = mkCoℕ (suc (mkCoℕ (suc (mkCoℕ (suc (mkCoℕ zero))))))

    inf : Coℕ
    inf .out = suc inf

    infBad : Coℕ
    infBad .out = id (suc infBad)

    silly : Coℕ → Coℕ
    silly x .out with out x
    ... | zero = zero
    ... | suc a = suc (silly a)

    sillyBad : Coℕ → Coℕ
    sillyBad x .out with out x
    ... | zero = zero
    ... | suc a = id (suc (sillyBad a))

    zeroBecomesOne : Coℕ → Coℕ
    zeroBecomesOne x .out with out x
    ... | zero = out (zeroBecomesOne (mkCoℕ (suc (mkCoℕ zero))))
    ... | suc a = suc a

    zeroBecomesOneℕ : ℕ → ℕ
    zeroBecomesOneℕ zero = zeroBecomesOneℕ (suc zero)
    zeroBecomesOneℕ (suc x) = suc x

    -- The same problem exists in musical
    data 𝅘𝅥Coℕ : Set where
        zero : 𝅘𝅥Coℕ
        suc : ∞ 𝅘𝅥Coℕ → 𝅘𝅥Coℕ

    𝅘𝅥three : 𝅘𝅥Coℕ
    𝅘𝅥three = suc (♯ (suc (♯ (suc (♯ zero)))))

    𝅘𝅥inf : 𝅘𝅥Coℕ
    𝅘𝅥inf = suc (♯ 𝅘𝅥inf)

    𝅘𝅥infBad : 𝅘𝅥Coℕ
    𝅘𝅥infBad = id (suc (♯ 𝅘𝅥infBad))

    𝅘𝅥infBad2 : 𝅘𝅥Coℕ
    𝅘𝅥infBad2 = suc (♯ id (𝅘𝅥infBad2))

    𝅘𝅥silly : 𝅘𝅥Coℕ → 𝅘𝅥Coℕ
    𝅘𝅥silly zero = zero
    𝅘𝅥silly (suc x) = suc (♯ (𝅘𝅥silly (♭ x)))

    𝅘𝅥sillyBad : 𝅘𝅥Coℕ → 𝅘𝅥Coℕ
    𝅘𝅥sillyBad zero = zero
    𝅘𝅥sillyBad (suc x) = id (suc (♯ (𝅘𝅥sillyBad (♭ x))))

