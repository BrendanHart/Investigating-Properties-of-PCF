Brendan Hart

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module ScottModelOfPCFWithLambda
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import NaturalNumbers-Properties
open import UF-Miscelanea

open import PCF-With-Lambda pt
open import ScottModelOfPCFWithLambda-Types pt fe pe

open import Dcpo pt fe 𝓤₀
open import DcpoConstructions pt fe
open import Dcpo-FunctionComposition pt fe 𝓤₀
open DcpoConstructionsGeneral 𝓤₀
open LiftingDcpo 𝓤₀ pe

open import Dcpo-IfZero pt fe pe
open import Dcpo-Contexts pt fe pe

open import DcpoProducts-Curry pt fe 𝓤₀
open import DcpoProducts pt fe
open DcpoProductsGeneral 𝓤₀

open import Lifting 𝓤₀
open import LiftingMonad 𝓤₀ hiding (μ)

⟦_⟧ₑ : {n : ℕ} {Γ : Context n} {σ : type} (t : PCF Γ σ) → DCPO⊥[ 【 Γ 】 , ⟦ σ ⟧ ]
⟦ Zero {_} {Γ} ⟧ₑ = (λ _ → η zero) , constant-functions-are-continuous ⟪ 【 Γ 】 ⟫ ⟪ ⟦ ι ⟧ ⟫ (η zero)
⟦ Succ {_} {Γ} t ⟧ₑ = [ 【 Γ 】 , ⟦ ι ⟧ , ⟦ ι ⟧ ]
                     (𝓛̇ succ , 𝓛̇-continuous ℕ-is-set ℕ-is-set succ) ∘ᵈᶜᵖᵒ⊥ ⟦ t ⟧ₑ 
⟦ Pred {_} {Γ} t ⟧ₑ = [ 【 Γ 】 , ⟦ ι ⟧ , ⟦ ι ⟧ ]
                     (𝓛̇ pred , 𝓛̇-continuous ℕ-is-set ℕ-is-set pred) ∘ᵈᶜᵖᵒ⊥ ⟦ t ⟧ₑ
⟦ IfZero {_} {Γ} t t₁ t₂ ⟧ₑ = ⦅ifZero⦆Γ Γ ⟦ t₁ ⟧ₑ ⟦ t₂ ⟧ₑ ⟦ t ⟧ₑ
⟦ ƛ {_} {Γ} {σ} {τ} t ⟧ₑ = curryᵈᶜᵖᵒ⊥ 【 Γ 】 ⟦ σ ⟧ ⟦ τ ⟧ ⟦ t ⟧ₑ 
⟦ _·_ {_} {Γ} {σ} {τ} t t₁ ⟧ₑ = [ 【 Γ 】 , ( ⟦ σ ⇒ τ ⟧ ×ᵈᶜᵖᵒ⊥ ⟦ σ ⟧) , ⟦ τ ⟧ ]
                               (eval⊥ ⟦ σ ⟧ ⟦ τ ⟧) ∘ᵈᶜᵖᵒ⊥ (to-×-DCPO⊥ 【 Γ 】 ⟦ σ ⇒ τ ⟧ ⟦ σ ⟧ ⟦ t ⟧ₑ ⟦ t₁ ⟧ₑ) 
⟦ v {_} {Γ} x ⟧ₑ = var-DCPO⊥ Γ x
⟦ Fix {_} {Γ} {σ} t ⟧ₑ = [ 【 Γ 】 , ⟦ σ ⇒ σ ⟧ , ⟦ σ ⟧ ] (μ ⟦ σ ⟧) ∘ᵈᶜᵖᵒ⊥ ⟦ t ⟧ₑ

\end{code}
