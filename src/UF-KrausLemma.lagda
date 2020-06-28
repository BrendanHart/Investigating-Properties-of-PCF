Nicolai kraus, 2012

Adapted to our development.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-KrausLemma where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons

fix : {X : 𝓤 ̇ } → (f : X → X) → 𝓤 ̇
fix f = Σ x ꞉ domain f , x ≡ f x

key-lemma : {X Y : 𝓤 ̇ } (f : X → Y) (g : wconstant f) {x y : X} (p : x ≡ y)
         → ap f p ≡ (g x x)⁻¹ ∙ g x y
key-lemma f g {x} refl = sym-is-inverse (g x x)

key-insight : {X Y : 𝓤 ̇ } (f : X → Y) → wconstant f → {x : X} (p : x ≡ x) → ap f p ≡ refl
key-insight f g p = key-lemma f g p ∙ (sym-is-inverse(g _ _))⁻¹

transport-identifications-along-identifications : {X Y : 𝓤 ̇ } {x y : X} (p : x ≡ y) (h k : X → Y) (q : h x ≡ k x)
                           → transport (λ - → h - ≡ k -) p q ≡ (ap h p)⁻¹ ∙ q ∙ ap k p
transport-identifications-along-identifications refl h k q = refl-left-neutral ⁻¹

transport-identifications-along-identifications' : {X : 𝓤 ̇ } {x : X} (p : x ≡ x) (f : X → X) (q : x ≡ f x)
                            → transport (λ - → - ≡ f -) p q ≡ (p ⁻¹ ∙ q) ∙ ap f p
transport-identifications-along-identifications'  p f q = transport-identifications-along-identifications p id f q
                                    ∙ ap (λ - → - ⁻¹ ∙ q ∙ (ap f p)) ((ap-id-is-id p)⁻¹)

Kraus-Lemma : {X : 𝓤 ̇ } → (f : X → X) → wconstant f → is-prop(fix f)
Kraus-Lemma {𝓤} {X} f g (x , p) (y , q) =
  -- p : x ≡ f x
  -- q : y ≡ f y
  (x , p)        ≡⟨ to-Σ-≡ (r , refl) ⟩
  (y , p')       ≡⟨ to-Σ-≡ (s , t) ⟩
  (y , q) ∎
    where
     r : x ≡ y
     r = x ≡⟨ p ⟩
       f x ≡⟨ g x y ⟩
       f y ≡⟨ q ⁻¹ ⟩
         y ∎
     p' : y ≡ f y
     p' = transport (λ - → - ≡ f -) r p
     s : y ≡ y
     s = y   ≡⟨ p' ⟩
         f y ≡⟨ q ⁻¹ ⟩
         y   ∎
     q' : y ≡ f y
     q' = transport (λ - → - ≡ f -) s p'
     t : q' ≡ q
     t = q'                        ≡⟨ transport-identifications-along-identifications' s f p' ⟩
         (s ⁻¹ ∙ p') ∙ ap f s      ≡⟨ ∙assoc (s ⁻¹) p' (ap f s) ⟩
         s ⁻¹ ∙ (p' ∙ ap f s)      ≡⟨ ap (λ - → s ⁻¹ ∙ (p' ∙ -)) (key-insight f g s) ⟩
         s ⁻¹ ∙ (p' ∙ refl)        ≡⟨ ap (λ - → s ⁻¹ ∙ -) ((refl-right-neutral p')⁻¹) ⟩
         s ⁻¹ ∙ p'                 ≡⟨ refl ⟩
        (p' ∙ (q ⁻¹))⁻¹ ∙ p'       ≡⟨ ap (λ - → - ∙ p') ((⁻¹-contravariant p' (q ⁻¹))⁻¹) ⟩
        ((q ⁻¹)⁻¹ ∙ (p' ⁻¹)) ∙ p'  ≡⟨ ap (λ - → (- ∙ (p' ⁻¹)) ∙ p') (⁻¹-involutive q) ⟩
        (q ∙ (p' ⁻¹)) ∙ p'         ≡⟨ ∙assoc q (p' ⁻¹) p' ⟩
         q ∙ ((p' ⁻¹) ∙ p')        ≡⟨ ap (λ - → q ∙ -) ((sym-is-inverse p')⁻¹) ⟩
         q ∙ refl                  ≡⟨ (refl-right-neutral q)⁻¹ ⟩
         q  ∎

from-fix : {X : 𝓤 ̇ } (f : X → X) → fix f → X
from-fix f = pr₁

to-fix : {X : 𝓤 ̇ } (f : X → X) → wconstant f → X → fix f
to-fix f g x = (f x , g x (f x))

\end{code}

A main application is to show that, in pure spartan MLTT, if a type
has a wconstant endfunction then it has a propositional truncation.

\begin{code}

has-split-support : 𝓤 ̇ → 𝓤 ⁺ ̇
has-split-support {𝓤} X = Σ P ꞉ 𝓤 ̇ , is-prop P × (X ⇔ P)

fix-has-split-support : {X : 𝓤 ̇ }
                    → collapsible X
                    → has-split-support X
fix-has-split-support {𝓤} {X} (f , κ) = fix f , Kraus-Lemma f κ , to-fix f κ , from-fix f

has-prop-truncation : (𝓥 : Universe) → 𝓤 ̇ → (𝓤 ⊔ 𝓥)⁺ ̇
has-prop-truncation {𝓤} 𝓥 X = Σ X' ꞉ 𝓤 ̇ , is-prop X'
                                             × (X → X')
                                             × ((P : 𝓥 ̇ ) → is-prop P → (X → P) → X' → P)

split-truncation : {X : 𝓤 ̇ } → has-split-support X → ∀ 𝓥 → has-prop-truncation 𝓥 X
split-truncation {𝓤} {X} (X' , i , f , g) V = X' , i , f , λ P j h x' → h (g x')

collapsible-has-prop-truncation : {X : 𝓤 ̇ }
                                → collapsible X
                                → ∀ 𝓥 → has-prop-truncation 𝓥 X
collapsible-has-prop-truncation {𝓤} {X} c = split-truncation (fix-has-split-support c)

\end{code}
