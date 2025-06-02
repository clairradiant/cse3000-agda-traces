\documentclass{article}

\usepackage{amsmath}
\usepackage{amssymb}

\usepackage{agda}
\usepackage[utf8]{inputenc}
\usepackage{newunicodechar}

\newunicodechar{ℕ}{\ensuremath{\mathnormal\mathbb{N}}}
\newunicodechar{∞}{\ensuremath{\mathnormal\infty}}
\newunicodechar{→}{\ensuremath{\mathnormal\rightarrow}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{₃}{\ensuremath{_3}}
\newunicodechar{♯}{\ensuremath{\mathnormal\sharp}}
\newunicodechar{♭}{\ensuremath{\mathnormal\flat}}
\newunicodechar{≡}{\ensuremath{\mathnormal\equiv}}
\newunicodechar{λ}{\ensuremath{\mathnormal\lambda}}
\newunicodechar{≈}{\ensuremath{\mathnormal\approx}}
\newunicodechar{∀}{\ensuremath{\mathnormal\forall}}
\newunicodechar{∃}{\ensuremath{\mathnormal\exists}}
\newunicodechar{×}{\ensuremath{\mathnormal\times}}
\newunicodechar{⊎}{\ensuremath{\mathnormal\sqcup}}

\begin{document}

\begin{code}
{-# OPTIONS --guardedness #-}

open import Codata.Musical.Notation
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; subst₂) renaming (sym to eqSym; trans to eqTrans)
import Level using (zero)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Properties
open import Data.Bool using (Bool; true; false)
open import Data.Product
open import Data.Sum
open import Function.Base using (case_of_)
open import Relation.Nullary using (contradiction)

Id : Set
Id = ℕ

Val : Set
Val = ℕ

State : Set
State = Id → Val
\end{code}

\begin{code}
record Trace₃ : Set where
            coinductive
            constructor mkTr
            field
                hd : State
                tl : Maybe Trace₃

\end{code}

\begin{code}
open Trace₃
\end{code}

\begin{code}
record _≈_ (tr₁ tr₂ : Trace₃) : Set where
            coinductive
            field
                hd : hd tr₁ ≡ hd tr₂
                tl : (tl tr₁ ≡ nothing × tl tr₂ ≡ nothing)
                     ⊎
                     ∃ {A = (Trace₃ × Trace₃)} λ x → (
                        tl tr₁ ≡ just (proj₁ x)
                        ×
                        tl tr₂ ≡ just (proj₂ x)
                        ×
                        (proj₁ x) ≈ (proj₂ x))
\end{code}

\end{document}