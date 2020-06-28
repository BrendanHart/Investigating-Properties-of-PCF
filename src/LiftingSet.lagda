Tom de Jong 22nd May 2019

The lifting of a set is a set.
We need to assume propositional extensionality for the fixed universe 𝓣 of
propositions and two instances of function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module LiftingSet
  (𝓣 : Universe) -- fix a universe for the propositions
  where

open import UF-Subsingletons
open import UF-Base
open import UF-Retracts
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import Lifting 𝓣

lifting-of-set-is-a-set : (fe' : funext 𝓣 𝓤) 
                          → (fe : funext 𝓣 𝓣)
                          → (pe : propext 𝓣)
                          → (X : 𝓤 ̇ )
                          → is-set X
                          → is-set (𝓛 X)
lifting-of-set-is-a-set fe' fe pe  X i {l} {m} p q  = retract-of-prop r j p q
 where
  r : Σ has-section
  r = (to-Σ-≡ , from-Σ-≡ , tofrom-Σ-≡)
  j : is-prop (Σ (λ p₁ → transport (λ P → (P → X) × is-prop P)
               p₁ (pr₂ l) ≡ pr₂ m))
  j = Σ-is-prop
       (identifications-of-props-are-props pe fe (is-defined m)
        (being-defined-is-a-prop m) (is-defined l))
       (λ d → ×-is-set (Π-is-set fe' λ _ → i)
                       (props-are-sets (being-a-prop-is-a-prop fe)))

\end{code}
