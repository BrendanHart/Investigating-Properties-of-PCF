Brendan Hart

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module PCF-With-Lambda-Substitution-Denotational
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import UF-Miscelanea

open import UF-Subsingletons

open import NaturalNumbers-Properties

open import PCF-With-Lambda pt

open import ScottModelOfPCFWithLambda-Types pt fe pe

open import ScottModelOfPCFWithLambda pt fe pe

open import Lifting 𝓤₀
open import LiftingMonad 𝓤₀ hiding (μ)
open import LiftingMiscelanea-PropExt-FunExt 𝓤₀ pe fe

open import DcpoProducts-Continuity pt fe 𝓤₀
open import DcpoProducts-Curry pt fe 𝓤₀
open import Dcpo pt fe 𝓤₀
open import Dcpo-Contexts pt fe pe

open import DcpoConstructions pt fe
open DcpoConstructionsGeneral 𝓤₀
open LiftingDcpo 𝓤₀ pe

open import DcpoProducts pt fe
open DcpoProductsGeneral 𝓤₀

replace-first-lemma : {n : ℕ} {Γ : Context n} {σ τ : type}
                      (x : (Γ ’ τ) ∋ σ)
                      (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
                      (T : PCF Γ τ)
                      → (pr₁ ⟦ v x ⟧ₑ (d , pr₁ ⟦ T ⟧ₑ d)) ≡ pr₁ ⟦ replace-first τ Γ T x ⟧ₑ d
replace-first-lemma {n} {Γ} {σ} {.σ} Z d T = refl
replace-first-lemma {n} {Γ} {σ} {τ} (S x) d T = refl

extract-S-lemma : {n : ℕ} {Γ : Context n} {σ : type}
                  → (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
                  → (e : ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩)
                  → (∀ {A} → (x : Γ ∋ A) → extract x d ≡ extract (S {n} {Γ} {A} {σ} x) (d , e))
extract-S-lemma d e Z = refl
extract-S-lemma d e (S x) = refl

rename-lemma : {n m : ℕ} {Γ : Context n} {Δ : Context m} {σ : type}
            → (M : PCF Γ σ)
            → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
            → (d : ⟨ ⟪ 【 Δ 】 ⟫ ⟩)
            → (e : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
            → (∀ {A} → (x : Γ ∋ A) → extract x e ≡ extract (ρ x) d)
            → pr₁ ⟦ rename ρ M ⟧ₑ d ≡ pr₁ ⟦ M ⟧ₑ e
rename-lemma Zero ρ d e eq = refl
rename-lemma (Succ M) ρ d e eq = ap (𝓛̇ succ) (rename-lemma M ρ d e eq)
rename-lemma (Pred M) ρ d e eq = ap (𝓛̇ pred) (rename-lemma M ρ d e eq)
rename-lemma (IfZero M M₁ M₂) ρ d e eq
             = ap₃ (λ x₁ x₂ x₃ → pr₁ (⦅ifZero⦆₁ x₂ x₃) x₁) (rename-lemma M ρ d e eq)
                   (rename-lemma M₁ ρ d e eq) (rename-lemma M₂ ρ d e eq)
rename-lemma (ƛ {n} {Γ} {σ} {τ} M) ρ d e eq = γ
  where
    ih : (λ z → pr₁ ⟦ rename (ext ρ) M ⟧ₑ (d , z)) ∼ (λ z → pr₁ ⟦ M ⟧ₑ (e , z))
    ih z = rename-lemma M (ext ρ) (d , z) (e , z) g
          where
            g : ∀ {A} → (x : (Γ ’ σ) ∋ A) → extract x (e , z) ≡ extract (ext ρ x) (d , z)
            g Z = refl
            g (S x) = eq x
    γ : pr₁ ⟦ rename ρ (ƛ M) ⟧ₑ d ≡ pr₁ ⟦ ƛ M ⟧ₑ e
    γ = to-subtype-≡ (being-continuous-is-a-prop ⟪ ⟦ σ ⟧ ⟫ ⟪ ⟦ τ ⟧ ⟫) (nfunext fe ih)
rename-lemma (M · M₁) ρ d e eq = ap₂ pr₁ (rename-lemma M ρ d e eq) (rename-lemma M₁ ρ d e eq)
rename-lemma (v x) ρ d e eq = eq x ⁻¹
rename-lemma (Fix {_} {_} {σ} M) ρ d e eq = ap (pr₁ (μ ⟦ σ ⟧)) (rename-lemma M ρ d e eq)

substitution-lemma : {n : ℕ}{Γ : Context n}
          {m : ℕ}{Δ : Context m}
          {σ : type}
          (M : PCF Γ σ)
          (f : ∀ {A} → Γ ∋ A → PCF Δ A)
          (e : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
          (d : ⟨ ⟪ 【 Δ 】 ⟫ ⟩)
          (g : ∀ {A} → (x : Γ ∋ A) → pr₁ ⟦ v x ⟧ₑ e ≡ pr₁ ⟦ f x ⟧ₑ d )
          → pr₁ ⟦ M ⟧ₑ e ≡ pr₁ ⟦ subst f M ⟧ₑ d
substitution-lemma Zero f e d g = refl
substitution-lemma (Succ M) f e d g = ap (𝓛̇ succ) (substitution-lemma M f e d g)
substitution-lemma (Pred M) f e d g = ap (𝓛̇ pred) (substitution-lemma M f e d g)
substitution-lemma (IfZero M M₁ M₂) f e d g =
                     pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ M₁ ⟧ₑ e) (pr₁ ⟦ M₂ ⟧ₑ e)) (pr₁ ⟦ M ⟧ₑ e) ≡⟨ i ⟩
                     pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ M₁ ⟧ₑ e) (pr₁ ⟦ M₂ ⟧ₑ e)) (pr₁ ⟦ subst f M ⟧ₑ d) ≡⟨ ii ⟩
                     pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ subst f M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ e)) (pr₁ ⟦ subst f M ⟧ₑ d) ≡⟨ iii ⟩
                     pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ subst f M₁ ⟧ₑ d) (pr₁ ⟦ subst f M₂ ⟧ₑ d)) (pr₁ ⟦ subst f M ⟧ₑ d) ∎
  where
    i = ap (pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ M₁ ⟧ₑ e) (pr₁ ⟦ M₂ ⟧ₑ e))) (substitution-lemma M f e d g)
    ii = ap (λ - → pr₁ (⦅ifZero⦆₁ - (pr₁ ⟦ M₂ ⟧ₑ e)) (pr₁ ⟦ subst f M ⟧ₑ d)) (substitution-lemma M₁ f e d g)
    iii = ap (λ - → pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ subst f M₁ ⟧ₑ d) -) (pr₁ ⟦ subst f M ⟧ₑ d)) (substitution-lemma M₂ f e d g)
substitution-lemma {_} {_} {m} {Δ} (ƛ {n} {Γ} {σ} {τ} M) f e d g = e₂
  where
    e₁ : (pr₁ (pr₁ ⟦ ƛ M ⟧ₑ e)) ∼ (pr₁ (pr₁ ⟦ subst f (ƛ M) ⟧ₑ d))
    e₁ x = substitution-lemma M (exts f) (e , x) (d , x) new_g
      where
        new_g : ∀ {A} → (z : (Γ ’ σ) ∋ A) → pr₁ ⟦ v z ⟧ₑ (e , x) ≡ pr₁ ⟦ exts f z ⟧ₑ (d , x)
        new_g Z = refl
        new_g {A} (S z) = pr₁ ⟦ v (S {n} {Γ} {A} {σ} z) ⟧ₑ (e , x)
                    ≡⟨ refl ⟩
                    pr₁ ⟦ v z ⟧ₑ e
                    ≡⟨  g z ⟩
                    pr₁ ⟦ f z ⟧ₑ d
                    ≡⟨ ( rename-lemma (f z) S (d , x) d (λ x₁ → refl) ) ⁻¹ ⟩
                    pr₁ ⟦ exts f (S z) ⟧ₑ (d , x) ∎
         
    e₂ : pr₁ ⟦ ƛ M ⟧ₑ e ≡ pr₁ ⟦ subst f (ƛ M) ⟧ₑ d
    e₂ = to-subtype-≡ (being-continuous-is-a-prop ⟪ ⟦ σ ⟧ ⟫ ⟪ ⟦ τ ⟧ ⟫) (nfunext fe e₁)
substitution-lemma (M · M₁) f e d g = γ
  where
    γ : pr₁ (pr₁ ⟦ M ⟧ₑ e) (pr₁ ⟦ M₁ ⟧ₑ e) ≡ pr₁ (pr₁ ⟦ subst f M ⟧ₑ d) (pr₁ ⟦ subst f M₁ ⟧ₑ d)
    γ = pr₁ (pr₁ ⟦ M ⟧ₑ e) (pr₁ ⟦ M₁ ⟧ₑ e) ≡⟨ ap (pr₁ (pr₁ ⟦ M ⟧ₑ e)) (substitution-lemma M₁ f e d g) ⟩
         pr₁ (pr₁ ⟦ M ⟧ₑ e) (pr₁ ⟦ subst f M₁ ⟧ₑ d) ≡⟨ ap (λ - → pr₁ - (pr₁ ⟦ subst f M₁ ⟧ₑ d)) (substitution-lemma M f e d g) ⟩
         pr₁ (pr₁ ⟦ subst (λ {A} → f) M ⟧ₑ d)
           (pr₁ ⟦ subst (λ {A} → f) M₁ ⟧ₑ d) ∎
substitution-lemma {n} {Γ} {m} {Δ} (v x) f e d g = g x 
substitution-lemma {n} {Γ} {m} {Δ} {σ} (Fix M) f e d g = ap (λ - → pr₁ (μ ⟦ σ ⟧ ) -) (substitution-lemma M f e d g)

β-equality : {n : ℕ}
         {Γ : Context n}
         {σ τ : type}
         (E : PCF (Γ ’ τ) σ)
         (T : PCF Γ τ)
         (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
         → pr₁ ⟦ (ƛ E) · T ⟧ₑ d ≡ pr₁ ⟦ E [ T ] ⟧ₑ d
β-equality {n} {Γ} {σ} {τ} E T d = substitution-lemma E (replace-first τ Γ T) (d , (pr₁ ⟦ T ⟧ₑ d)) d g
  where
    g : ∀ {A} → (x : (Γ ’ τ) ∋ A) → pr₁ ⟦ v x ⟧ₑ (d , pr₁ ⟦ T ⟧ₑ d) ≡ pr₁ ⟦ replace-first τ Γ T x ⟧ₑ d
    g Z = refl
    g (S x) = refl
    
\end{code}
