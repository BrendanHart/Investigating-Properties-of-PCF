Brendan Hart

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc hiding (⊥)

module Dcpo-FunctionComposition
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open import DcpoConstructions pt fe
open DcpoConstructionsGeneral 𝓥

open import Dcpo pt fe 𝓥

[_,_,_]_∘ᵈᶜᵖᵒ_ : (𝓓 : DCPO {𝓤} {𝓤'})
             → (𝓔 : DCPO {𝓣} {𝓣'})
             → (𝓕 : DCPO {𝓦} {𝓦'})
             → DCPO[ 𝓔 , 𝓕 ]
             → DCPO[ 𝓓 , 𝓔 ]
             → DCPO[ 𝓓 , 𝓕 ]
[ 𝓓 , 𝓔 , 𝓕 ] g ∘ᵈᶜᵖᵒ f = h , c
  where
    h : ⟨ 𝓓 ⟩ → ⟨ 𝓕 ⟩
    h = pr₁ g ∘ pr₁ f
    h-is-monotone : is-monotone 𝓓 𝓕 h
    h-is-monotone x y p = γ
      where
        p₁ : pr₁ f x ⊑⟨ 𝓔 ⟩ pr₁ f y
        p₁ = continuous-functions-are-monotone 𝓓 𝓔 f x y p
        γ : h x ⊑⟨ 𝓕 ⟩ h y
        γ = continuous-functions-are-monotone 𝓔 𝓕 g (pr₁ f x) (pr₁ f y) p₁
    c : is-continuous 𝓓 𝓕 h
    c I α δ = u , v
      where
        u : is-upperbound (underlying-order 𝓕) (h (∐ 𝓓 δ)) (λ i → h (α i))
        u i = h-is-monotone (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)
        v : (u₁ : ⟨ 𝓕 ⟩) →
            ((i : I) → h (α i) ⊑⟨ 𝓕 ⟩ u₁) →
            h (∐ 𝓓 δ) ⊑⟨ 𝓕 ⟩ u₁
        v u₁ p = transport (λ - → - ⊑⟨ 𝓕 ⟩ u₁) (e₁ ⁻¹) p₁
          where
            isdir₁ : is-Directed 𝓔 (λ i → pr₁ f (α i))
            isdir₁ = image-is-directed 𝓓 𝓔 f δ
            isdir₂ : is-Directed 𝓕 (λ i → (pr₁ g ∘ pr₁ f) (α i))
            isdir₂ = image-is-directed 𝓔 𝓕 g isdir₁
            e₁ : h (∐ 𝓓 δ) ≡ ∐ 𝓕 isdir₂
            e₁ = h (∐ 𝓓 δ)
                ≡⟨ ap (λ - → pr₁ g -) (continuous-function-∐-≡ 𝓓 𝓔 f δ) ⟩
                pr₁ g (∐ 𝓔 isdir₁)
                ≡⟨ continuous-function-∐-≡ 𝓔 𝓕 g isdir₁ ⟩
                ∐ 𝓕 isdir₂ ∎
            p₁ : ∐ 𝓕 isdir₂ ⊑⟨ 𝓕 ⟩ u₁
            p₁ = ∐-is-lowerbound-of-upperbounds 𝓕 isdir₂ u₁ p


[_,_,_]_∘ᵈᶜᵖᵒ⊥_ : (𝓓 : DCPO⊥ {𝓤} {𝓤'})
               → (𝓔 : DCPO⊥ {𝓣} {𝓣'})
               → (𝓕 : DCPO⊥ {𝓦} {𝓦'})
               → DCPO⊥[ 𝓔 , 𝓕 ]
               → DCPO⊥[ 𝓓 , 𝓔 ]
               → DCPO⊥[ 𝓓 , 𝓕 ]
[ 𝓓 , 𝓔 , 𝓕 ] g ∘ᵈᶜᵖᵒ⊥ f = [ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ , ⟪ 𝓕 ⟫ ] g ∘ᵈᶜᵖᵒ f
\end{code}
