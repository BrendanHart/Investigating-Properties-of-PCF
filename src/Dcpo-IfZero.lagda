Brendan Hart

\begin{code}

{-# OPTIONS --without-K --safe  #-}

open import SpartanMLTT
open import UF-PropTrunc

module Dcpo-IfZero
       (pt : propositional-truncations-exist)
       (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
       (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt
open import UF-Miscelanea
open import UF-Subsingletons hiding (⊥)
open import UF-Subsingletons-FunExt

open import DcpoConstructions pt fe
open DcpoConstructionsGeneral 𝓤₀
open LiftingDcpo 𝓤₀ pe

open import DcpoProducts pt fe
open DcpoProductsGeneral 𝓤₀

open import PCF-With-Lambda pt
open import Dcpo-Contexts pt fe pe

open import DcpoProducts-Curry pt fe 𝓤₀

open import Dcpo pt fe 𝓤₀
open import Dcpo-FunctionComposition pt fe 𝓤₀

⦅ifZero⦆-uncurried' : DCPO⊥[ 𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ , 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
⦅ifZero⦆-uncurried' = uncurryᵈᶜᵖᵒ⊥ 𝓛ᵈℕ 𝓛ᵈℕ (𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ⦅ifZero⦆

⦅ifZero⦆-uncurried : DCPO⊥[ (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ , 𝓛ᵈℕ ]
⦅ifZero⦆-uncurried = uncurryᵈᶜᵖᵒ⊥ (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) 𝓛ᵈℕ 𝓛ᵈℕ ⦅ifZero⦆-uncurried'

module _ {n : ℕ} (Γ : Context n)
        where

  ⦅ifZero⦆-arguments : DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
  ⦅ifZero⦆-arguments a b c = to-×-DCPO⊥ 【 Γ 】 (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) 𝓛ᵈℕ f c
        where
          f : DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
          f = to-×-DCPO⊥ 【 Γ 】 𝓛ᵈℕ 𝓛ᵈℕ a b

  ⦅ifZero⦆Γ : DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
  ⦅ifZero⦆Γ a b c = [ 【 Γ 】 , (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ , 𝓛ᵈℕ ] ⦅ifZero⦆-uncurried ∘ᵈᶜᵖᵒ⊥ (⦅ifZero⦆-arguments a b c)
\end{code}
