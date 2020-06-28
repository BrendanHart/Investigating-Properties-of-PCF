Brendan Hart

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module Dcpo-Contexts
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import UF-Miscelanea

open import PCF-With-Lambda pt
open import ScottModelOfPCFWithLambda-Types pt fe pe

open import Dcpo pt fe 𝓤₀
open import DcpoConstructions pt fe
open DcpoConstructionsGeneral 𝓤₀
open LiftingDcpo 𝓤₀ pe

open import DcpoProducts pt fe
open DcpoProductsGeneral 𝓤₀

open import DcpoProducts-Curry pt fe 𝓤₀
open import Dcpo-FunctionComposition pt fe 𝓤₀

⊤ᵈᶜᵖᵒ : DCPO {𝓤₁} {𝓤₁}
⊤ᵈᶜᵖᵒ = 𝟙 , _⊑⟨⊤⟩_ , set , prop-valued , (λ _ → *) , transitive , antisym , dc
  where
    _⊑⟨⊤⟩_ : 𝟙 {𝓤₁} → 𝟙 {𝓤₁} → 𝓤₁ ̇
    x ⊑⟨⊤⟩ y = 𝟙
    set : is-set 𝟙
    set = props-are-sets 𝟙-is-prop
    prop-valued : is-prop-valued {𝓤₁} {𝓤₁} {𝟙} (λ x y → 𝟙)
    prop-valued _ _ * * = refl
    reflexive : is-reflexive _⊑⟨⊤⟩_
    reflexive _ = *
    transitive : is-transitive {𝓤₁} {𝓤₁} {𝟙} (λ x y → 𝟙)
    transitive _ _ _ _ _ = *
    antisym : ∀ (x : 𝟙) y → x ⊑⟨⊤⟩ y → _ → x ≡ y
    antisym * * _ _ = refl
    dc : is-directed-complete (λ x y → 𝟙)
    dc _ _ _ = * , ((λ _ → *) , (λ _ _ → *))

⊤ᵈᶜᵖᵒ⊥ : DCPO⊥ {𝓤₁} {𝓤₁}
⊤ᵈᶜᵖᵒ⊥ = ⊤ᵈᶜᵖᵒ , (* , (λ y → *))

【_】 : {n : ℕ} (Γ : Context n) → DCPO⊥ {𝓤₁} {𝓤₁}
【 ⟨⟩ 】 = ⊤ᵈᶜᵖᵒ⊥
【 Γ ’ x 】 = 【 Γ 】 ×ᵈᶜᵖᵒ⊥ ⟦ x ⟧

extract : {n : ℕ} {σ : type} {Γ : Context n} → (x : Γ ∋ σ) → ⟨ ⟪ 【 Γ 】 ⟫ ⟩  → ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩
extract {n} {σ} {a} Z d = pr₂ d
extract {n} {σ₁} {Γ ’ σ} (S x) d = extract x (pr₁ d)

Γ₁⊑Γ₂→lookups-less : ∀ {n : ℕ} {Γ : Context n} {σ : type}
                      → (x : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
                      → (y : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
                      → x ⊑⟨ ⟪ 【 Γ 】 ⟫ ⟩ y
                      → (z : Γ ∋ σ)
                      → extract z x ⊑⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩ extract z y
Γ₁⊑Γ₂→lookups-less {.(succ _)} {Γ ’ σ} {.σ} x y e Z = pr₂ e
Γ₁⊑Γ₂→lookups-less {.(succ _)} {Γ ’ τ} {σ} x y e (S z) = Γ₁⊑Γ₂→lookups-less (pr₁ x) (pr₁ y) (pr₁ e) z

∘-of-prₓ-is-continuous : {n : ℕ} {Γ : Context n} {σ : type} (x : Γ ∋ σ) → is-continuous ⟪ 【 Γ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫ (extract x)
∘-of-prₓ-is-continuous {n} {Γ ’ σ} {σ} Z = continuity-of-function ⟪ 【 Γ ’ σ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫ (pr₂-is-continuous ⟪ 【 Γ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫)
∘-of-prₓ-is-continuous {n} {Γ ’ τ} {σ} (S x)
                       = continuity-of-function ⟪ 【 Γ ’ τ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫
                                    ( [ ⟪ 【 Γ ’ τ 】 ⟫ , ⟪ 【 Γ 】 ⟫ , ⟪ ⟦ σ ⟧ ⟫ ]
                                        (extract x) , (∘-of-prₓ-is-continuous x) ∘ᵈᶜᵖᵒ pr₁-is-continuous ⟪ 【 Γ 】 ⟫ ⟪ ⟦ τ ⟧ ⟫)

var-DCPO : {n : ℕ} {σ : type} (Γ : Context n) → (x : Γ ∋ σ) → DCPO[ ⟪ 【 Γ 】 ⟫ , ⟪ ⟦ σ ⟧ ⟫ ]
var-DCPO {n} {σ} Γ x = extract x , c
  where
    c : is-continuous ⟪ 【 Γ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫ (extract x)
    c = ∘-of-prₓ-is-continuous x

var-DCPO⊥ : {n : ℕ} {σ : type} (Γ : Context n) → (x : Γ ∋ σ)→ DCPO⊥[ 【 Γ 】 , ⟦ σ ⟧ ]
var-DCPO⊥ Γ x = var-DCPO Γ x
