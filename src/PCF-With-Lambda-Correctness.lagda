Brendan Hart

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-PropTrunc

module PCF-With-Lambda-Correctness
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import UF-Miscelanea

open import NaturalNumbers-Properties

open import PCF-With-Lambda pt

open import ScottModelOfPCFWithLambda-Types pt fe pe

open import ScottModelOfPCFWithLambda pt fe pe

open import Lifting 𝓤₀
open import LiftingMonad 𝓤₀ hiding (μ)
open import LiftingMiscelanea-PropExt-FunExt 𝓤₀ pe fe

open import DcpoProducts-Curry pt fe 𝓤₀
open import Dcpo pt fe 𝓤₀
open import Dcpo-Contexts pt fe pe

open import DcpoConstructions pt fe
open DcpoConstructionsGeneral 𝓤₀
open LiftingDcpo 𝓤₀ pe

open import DcpoProducts pt fe
open DcpoProductsGeneral 𝓤₀

open import PCF-With-Lambda-Substitution-Denotational pt fe pe

canonical-numeral-correctness : {n : ℕ} {Γ : Context n} (k : ℕ) (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩) → pr₁ ⟦ ℕ-to-ι {_} {Γ} k ⟧ₑ d ≡ η k
canonical-numeral-correctness zero d = refl
canonical-numeral-correctness (succ n) d = pr₁ ⟦ Succ (ℕ-to-ι n) ⟧ₑ d ≡⟨ refl ⟩
                                           (𝓛̇ succ ∘ pr₁ ⟦ ℕ-to-ι n ⟧ₑ) d ≡⟨ ap (𝓛̇ succ) ih ⟩
                                           𝓛̇ succ (η n) ≡⟨ refl ⟩
                                           η (succ n) ∎
    where
    ih = canonical-numeral-correctness n d

correctness-IfZero-zero : {n : ℕ} {Γ : Context n}
                     → (N t t₁ t₂ : PCF Γ ι)
                     → pr₁ ⟦ t ⟧ₑ ∼ pr₁ ⟦ Zero {_} {Γ} ⟧ₑ
                     → pr₁ ⟦ t₁ ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
                     → pr₁ ⟦ IfZero t t₁ t₂ ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness-IfZero-zero N t t₁ t₂ c₁ c₂ d = ((⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) ♯) (pr₁ ⟦ t ⟧ₑ d) ≡⟨ i ⟩
                                            (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) ♯) (η zero) ≡⟨ ii ⟩
                                            ⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) zero ≡⟨ c₂ d ⟩
                                            pr₁ ⟦ N ⟧ₑ d ∎
  where
    i = ap ((⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) ♯) (c₁ d)
    ii = ♯-on-total-element (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) {η zero} *


correctness-IfZero-succ : {n : ℕ} {Γ : Context n}
                     → (N t t₁ t₂ : PCF Γ ι)
                     → (k : ℕ)
                     → pr₁ ⟦ t ⟧ₑ ∼ pr₁ ⟦ ℕ-to-ι {_} {Γ} (succ k) ⟧ₑ
                     → pr₁ ⟦ t₂ ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
                     → pr₁ ⟦ IfZero t t₁ t₂ ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness-IfZero-succ N t t₁ t₂ k c₁ c₂ d = ((⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) ♯) (pr₁ ⟦ t ⟧ₑ d) ≡⟨ i ⟩
                     (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) ♯) (pr₁ ⟦ Succ (ℕ-to-ι k) ⟧ₑ d) ≡⟨ ii ⟩
                     (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) ♯) (η (succ k)) ≡⟨ iii ⟩
                     ⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) (succ k) ≡⟨ c₂ d ⟩
                     pr₁ ⟦ N ⟧ₑ d ∎
  where
    i = ap ((⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) ♯ ) (c₁ d)
    ii = ap (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d) ♯) (canonical-numeral-correctness (succ k) d)
    iii = ♯-on-total-element (⦅ifZero⦆₀ (pr₁ ⟦ t₁ ⟧ₑ d) (pr₁ ⟦ t₂ ⟧ₑ d)) {η (succ k)} *

correctness-Fix : {n : ℕ} {Γ : Context n} {σ : type}
                  → (M : PCF Γ (σ ⇒ σ))
                  → (N : PCF Γ σ)
                  → pr₁ ⟦ M · Fix M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
                  → pr₁ ⟦ Fix M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness-Fix {_} {_} {σ} M N c d = pr₁ ⟦ Fix M ⟧ₑ d
            ≡⟨ refl ⟩
            pr₁ (μ ⟦ σ ⟧) (pr₁ ⟦ M ⟧ₑ d)
            ≡⟨ i ⟩
            pr₁ (pr₁ ⟦ M ⟧ₑ d) (pr₁ (μ ⟦ σ ⟧) ( pr₁ ⟦ M ⟧ₑ d))
            ≡⟨ refl ⟩
            pr₁ ⟦ M · Fix M ⟧ₑ d
            ≡⟨ c d ⟩
            pr₁ ⟦ N ⟧ₑ d ∎
  where
    i = μ-gives-a-fixed-point ⟦ σ ⟧ (pr₁ ⟦ M ⟧ₑ d)

correctness-· : {n : ℕ} {Γ : Context n} {σ τ : type}
                → (M : PCF Γ (σ ⇒ τ))
                → (E : PCF (Γ ’ σ) τ)
                → (T : PCF Γ σ)
                → (N : PCF Γ τ)
                → pr₁ ⟦ M ⟧ₑ ∼ pr₁ ⟦ ƛ E ⟧ₑ
                → pr₁ ⟦ E [ T ] ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
                → pr₁ ⟦ M · T ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness-· {_} {Γ} {σ} {τ} M E T N c₁ c₂ d = pr₁ ⟦ M · T ⟧ₑ d ≡⟨ refl ⟩
                                                pr₁ (pr₁ ⟦ M ⟧ₑ d) (pr₁ ⟦ T ⟧ₑ d) ≡⟨ i ⟩
                                                pr₁ (pr₁ ⟦ ƛ E ⟧ₑ d) (pr₁ ⟦ T ⟧ₑ d) ≡⟨ ii ⟩
                                                pr₁ ⟦ E [ T ] ⟧ₑ d ≡⟨ c₂ d ⟩
                                                pr₁ ⟦ N ⟧ₑ d ∎
  where
    i = ap (λ - → pr₁ - (pr₁ ⟦ T ⟧ₑ d)) (c₁ d)
    ii = β-equality E T d
                                                                                                         
correctness' : {n : ℕ} {Γ : Context n} {σ : type}
               → (M N : PCF Γ σ)
               → M ⇓' N
               → pr₁ ⟦ M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
correctness' .(v _) .(v _) var-id d = refl
correctness' .(ƛ _) .(ƛ _) ƛ-id d = refl
correctness' .Zero .Zero zero-id d = refl
correctness' (Pred M) .Zero (pred-zero r) d =
                     ap (𝓛̇ pred) (correctness' M Zero r d)
correctness' (Pred M) .(ℕ-to-ι _) (pred-succ {_} {_} {_} {k} r) d =
                     ap (𝓛̇ pred) (correctness' M (ℕ-to-ι (succ k)) r d)
correctness' (Succ M) .(Succ (ℕ-to-ι _)) (succ-arg {_} {_} {_} {k} r) d =
                     ap (𝓛̇ succ) (correctness' M (ℕ-to-ι k) r d)
correctness' (IfZero t t₁ t₂) N (IfZero-zero r r₁) =
                     correctness-IfZero-zero N t t₁ t₂ (correctness' t Zero r) (correctness' t₁ N r₁)
correctness' (IfZero t t₁ t₂) N (IfZero-succ {_} {_} {_} {_} {_} {_} {k} r r₁) =
                     correctness-IfZero-succ N t t₁ t₂ k (correctness' t (ℕ-to-ι (succ k)) r) (correctness' t₂ N r₁)
correctness' (Fix M) N (Fix-step r) = 
                      correctness-Fix M N (correctness' (M · Fix M) N r)
correctness' .(_ · _) N (·-step {_} {_} {_} {_} {M} {E} {T} {_} r r₁) =
                      correctness-· M E T N (correctness' M (ƛ E) r) (correctness' (E [ T ]) N r₁)

correctness : {n : ℕ} {Γ : Context n} {σ : type} (M N : PCF Γ σ) → M ⇓ N → ⟦ M ⟧ₑ ≡ ⟦ N ⟧ₑ
correctness {_} {Γ} {σ} M N x = γ
  where
    i : pr₁ ⟦ M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
    i d = ∥∥-rec (sethood ⟪ ⟦ σ ⟧ ⟫) (λ x₁ → correctness' M N x₁ d) x
    γ : ⟦ M ⟧ₑ ≡ ⟦ N ⟧ₑ
    γ = to-subtype-≡ (being-continuous-is-a-prop ⟪ 【 Γ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫) (nfunext fe i)


\end{code}
