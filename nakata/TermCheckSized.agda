{-# OPTIONS --sized-types #-}

open import Size
open import Codata.Sized.Thunk

-- Example module showing sized types do not constrain definitions in the same way as guardedness (see TermCheck.agda)
module nakata.TermCheckSized where
    data Coℕ (i : Size) : Set where
        zero : Coℕ i
        suc : Thunk Coℕ i → Coℕ i

    inf : ∀ {i} → Coℕ i
    inf = suc (λ where .force → inf)

    id : ∀ {a} {A : Set a} → A → A
    id x = x

    infOk : ∀ {i} → Coℕ i
    infOk = id (suc (λ where .force → infOk))
