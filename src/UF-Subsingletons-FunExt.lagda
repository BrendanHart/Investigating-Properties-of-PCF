In univalent logic, as opposed to Curry-Howard logic, a proposition is
a prop or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

About (sub)singletons using function extensionality.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Subsingletons-FunExt where

open import SpartanMLTT

open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-LeftCancellable
open import UF-Retracts

Π-is-prop : funext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
          → ((x : X) → is-prop (A x)) → is-prop (Π A)
Π-is-prop fe i f g = dfunext fe (λ x → i x (f x) (g x))

Π-is-prop' : funext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
        → ((x : X) → is-prop (A x)) → is-prop ({x : X} → A x)
Π-is-prop' fe {X} {A} i = retract-of-prop retr (Π-is-prop fe i)
 where
  retr : retract ({x : X} → A x) of Π A
  retr = (λ f {x} → f x) , (λ g x → g {x}) , (λ x → refl)

Π-is-singleton : funext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
               → ((x : X) → is-singleton (A x)) → is-singleton (Π A)
Π-is-singleton fe i = (λ x → pr₁ (i x)) , (λ f → dfunext fe (λ x → pr₂ (i x) (f x)))

being-a-prop-is-a-prop : {X : 𝓤 ̇ } → funext 𝓤 𝓤 → is-prop (is-prop X)
being-a-prop-is-a-prop {𝓤} {X} fe f g = c₁
 where
  l : is-set X
  l = props-are-sets f
  c : (x y : X) → f x y ≡ g x y
  c x y = l (f x y) (g x y)
  c₀ : (x : X) → f x ≡ g x
  c₀ x = dfunext fe (c x)
  c₁ : f ≡ g
  c₁  = dfunext fe c₀

identifications-of-props-are-props : propext 𝓤 → funext 𝓤 𝓤
                                   → (P : 𝓤 ̇ ) → is-prop P
                                   → (X : 𝓤 ̇ ) → is-prop (X ≡ P)
identifications-of-props-are-props {𝓤} pe fe P i = local-hedberg' P (λ X → g X ∘ f X , k X)
 where
  f : (X : 𝓤 ̇ ) → X ≡ P → is-prop X × (X ⇔ P)
  f X refl = i , (id , id)
  g : (X : 𝓤 ̇ ) → is-prop X × (X ⇔ P) → X ≡ P
  g X (l , φ , γ) = pe l i φ γ
  j : (X : 𝓤 ̇ ) → is-prop (is-prop X × (X ⇔ P))
  j X = ×-prop-criterion ((λ _ → being-a-prop-is-a-prop fe) ,
                          (λ l → ×-is-prop (Π-is-prop fe (λ x → i))
                                            (Π-is-prop fe (λ p → l))))
  k : (X : 𝓤 ̇ ) → wconstant (g X ∘ f X)
  k X p q = ap (g X) (j X (f X p) (f X q))

being-a-singleton-is-a-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-prop(is-singleton X)
being-a-singleton-is-a-prop fe {X} (x , φ) (y , γ) = to-Σ-≡ (φ y , dfunext fe λ z → iss {y} {z} _ _)
 where
  isp : is-prop X
  isp = singletons-are-props (y , γ)
  iss : is-set X
  iss = props-are-sets isp

Π-is-set : funext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
         → ((x : X) → is-set(A x)) → is-set(Π A)
Π-is-set {𝓤} {𝓥} fe {X} {A} isa {f} {g} = b
 where
  a : is-prop (f ∼ g)
  a p q = dfunext fe λ x → isa x (p x) (q x)
  b : is-prop(f ≡ g)
  b = left-cancellable-reflects-is-prop happly (section-lc happly (pr₂ (fe f g))) a

\end{code}

The meat of the following proof is being-set-is-a-prop'. The rest of the
code is to deal with implicit arguments in conjunction with function
extensionality. The solution is not ideal. Ideally, functions with
implicit parameters should be the same as their versions with explicit
parameters.

\begin{code}

being-set-is-a-prop : funext 𝓤 𝓤 → {X : 𝓤 ̇ } → is-prop (is-set X)
being-set-is-a-prop {𝓤} fe {X} = h
 where
  is-set' : 𝓤 ̇ → 𝓤 ̇
  is-set' X = (x y : X) → is-prop(x ≡ y)

  being-set-is-a-prop' : {X : 𝓤 ̇ } → funext 𝓤 𝓤 → is-prop (is-set' X)
  being-set-is-a-prop' fe = Π-is-prop fe
                              (λ x → Π-is-prop fe
                              (λ y → being-a-prop-is-a-prop fe))

  f : {X : 𝓤 ̇ } → is-set' X → is-set X
  f s {x} {y} = s x y

  g : {X : 𝓤 ̇ } → is-set X → is-set' X
  g s x y = s {x} {y}

  h : is-prop (is-set X)
  h = subtype-of-prop-is-a-prop g (ap f) (being-set-is-a-prop' fe)

\end{code}

\begin{code}

decidability-of-prop-is-prop : funext 𝓤 𝓤₀ → {P : 𝓤 ̇ } → is-prop P → is-prop(P + ¬ P)
decidability-of-prop-is-prop fe₀ i = sum-of-contradictory-props
                                      i
                                      (Π-is-prop fe₀ λ _ → 𝟘-is-prop)
                                      (λ p u → u p)

Ω-ext : funext 𝓤 𝓤 → propext 𝓤 → {p q : Ω 𝓤}
        → (p holds → q holds) → (q holds → p holds) → p ≡ q
Ω-ext {𝓤} fe pe {p} {q} f g =
 to-Σ-≡ (pe (holds-is-prop p) (holds-is-prop q) f g ,
         being-a-prop-is-a-prop fe _ _)

Ω-is-a-set : funext 𝓤 𝓤 → propext 𝓤 → is-set (Ω 𝓤)
Ω-is-a-set {𝓤} fe pe = Id-collapsibles-are-sets pc
 where
  A : (p q : Ω 𝓤) → 𝓤 ̇
  A p q = (p holds → q holds) × (q holds → p holds)
  A-is-prop : (p q : Ω 𝓤) → is-prop(A p q)
  A-is-prop p q = Σ-is-prop (Π-is-prop fe
                                   (λ _ → holds-is-prop q))
                                   (λ _ → Π-is-prop fe (λ _ → holds-is-prop p))
  g : (p q : Ω 𝓤) → p ≡ q → A p q
  g p q e = (b , c)
   where
    a : p holds ≡ q holds
    a = ap _holds e
    b : p holds → q holds
    b = transport (λ X → X) a
    c : q holds → p holds
    c = transport (λ X → X) (a ⁻¹)
  h  : (p q : Ω 𝓤) → A p q → p ≡ q
  h p q (u , v) = Ω-ext fe pe u v
  f  : (p q : Ω 𝓤) → p ≡ q → p ≡ q
  f p q e = h p q (g p q e)
  wconstant-f : (p q : Ω 𝓤) (d e : p ≡ q) → f p q d ≡ f p q e
  wconstant-f p q d e = ap (h p q) (A-is-prop p q (g p q d) (g p q e))
  pc : {p q : Ω 𝓤} → Σ f ꞉ (p ≡ q → p ≡ q) , wconstant f
  pc {p} {q} = (f p q , wconstant-f p q)

powersets-are-sets : funext 𝓤 (𝓥 ⁺) → funext 𝓥 𝓥 → propext 𝓥
                   → {A : 𝓤 ̇ } → is-set (A → Ω 𝓥)
powersets-are-sets fe fe' pe = Π-is-set fe (λ x → Ω-is-a-set fe' pe)

negations-are-props : {X : 𝓤 ̇ } → funext 𝓤 𝓤₀ → is-prop(¬ X)
negations-are-props fe = Π-is-prop fe (λ x → 𝟘-is-prop)

not : funext 𝓤 𝓤₀ → Ω 𝓤 → Ω 𝓤
not fe (P , i) = (¬ P , negations-are-props fe)

equal-⊤-is-true : (P : 𝓤 ̇ ) (i : is-prop P) → (P , i) ≡ ⊤ → P
equal-⊤-is-true P hp r = f *
 where
  s : 𝟙 ≡ P
  s = (ap pr₁ r)⁻¹
  f : 𝟙 → P
  f = transport id s

\end{code}

TODO. In the following, rather than using a P and i, use a p = (P , i) in Ω 𝓤.

\begin{code}

true-is-equal-⊤ : propext 𝓤 → funext 𝓤 𝓤 → (P : 𝓤 ̇ ) (i : is-prop P)
                → P → (P , i) ≡ ⊤
true-is-equal-⊤ pe fe P i p = to-Σ-≡ (pe i 𝟙-is-prop unique-to-𝟙 (λ _ → p) ,
                                      being-a-prop-is-a-prop fe _ _)

false-is-equal-⊥ : propext 𝓤 → funext 𝓤 𝓤 → (P : 𝓤 ̇ ) (i : is-prop P)
                 → ¬ P → (P , i) ≡ ⊥
false-is-equal-⊥ pe fe P i f = to-Σ-≡ (pe i 𝟘-is-prop (λ p → 𝟘-elim (f p)) 𝟘-elim ,
                                       being-a-prop-is-a-prop fe _ _)

Ω-ext' : propext 𝓤 → funext 𝓤 𝓤 → {p q : Ω 𝓤}
      → (p ≡ ⊤ → q ≡ ⊤) → (q ≡ ⊤ → p ≡ ⊤) → p ≡ q
Ω-ext' pe fe {(P , i)} {(Q , j)} f g = to-Σ-≡ (pe i j I II ,
                                              being-a-prop-is-a-prop fe _ _ )
 where
  I : P → Q
  I x = equal-⊤-is-true Q j (f (true-is-equal-⊤ pe fe P i x))
  II : Q → P
  II y = equal-⊤-is-true P i (g (true-is-equal-⊤ pe fe Q j y))

\end{code}

Without excluded middle, we have that:

\begin{code}

no-truth-values-other-than-⊥-or-⊤ : funext 𝓤 𝓤 → propext 𝓤
                                  → ¬ (Σ p ꞉ Ω 𝓤 , (p ≢ ⊥) × (p ≢ ⊤))
no-truth-values-other-than-⊥-or-⊤ fe pe ((P , i) , (f , g)) = φ u
 where
  u : ¬ P
  u p = g l
    where
     l : (P , i) ≡ ⊤
     l = Ω-ext fe pe unique-to-𝟙 (λ _ → p)
  φ : ¬¬ P
  φ u = f l
    where
     l : (P , i) ≡ ⊥
     l = Ω-ext fe pe (λ p → 𝟘-elim (u p)) unique-from-𝟘

\end{code}

The above and following 𝟘-elim is used to coerce from 𝟘 {𝓤} to 𝟘 {𝓤₀}
as this is where negations take values in.

\begin{code}

⊥-is-not-⊤ : ¬(⊥ {𝓤} ≡ ⊤ {𝓤})
⊥-is-not-⊤ b = 𝟘-elim(𝟘-is-not-𝟙 (ap _holds b))

\end{code}

Sometimes it is convenient to work with the type of true propositions,
which is a singleton and hence a subsingleton. But we will leave this
type nameless:

\begin{code}

𝟙-is-true-props-center : funext 𝓤 𝓤 → propext 𝓤
                       → (σ : Σ P ꞉ 𝓤 ̇ , is-prop P × P) → (𝟙 , 𝟙-is-prop , *) ≡ σ
𝟙-is-true-props-center fe pe = γ
 where
  φ : ∀ P → is-prop (is-prop P × P)
  φ P (i , p) = ×-is-prop (being-a-prop-is-a-prop fe) i (i , p)

  γ : ∀ σ → (𝟙 , 𝟙-is-prop , *) ≡ σ
  γ (P , i , p) = to-subtype-≡ φ s
   where
    s : 𝟙 ≡ P
    s = pe 𝟙-is-prop i (λ _ → p) (λ _ → *)

the-true-props-form-a-singleton-type : funext 𝓤 𝓤 → propext 𝓤
                                     → is-singleton (Σ P ꞉ 𝓤 ̇ , is-prop P × P)
the-true-props-form-a-singleton-type fe pe = (𝟙 , 𝟙-is-prop , *) , 𝟙-is-true-props-center fe pe


the-true-props-form-a-prop : funext 𝓤 𝓤 → propext 𝓤
                           → is-prop (Σ P ꞉ 𝓤 ̇ , is-prop P × P)
the-true-props-form-a-prop fe pe = singletons-are-props (the-true-props-form-a-singleton-type fe pe)

\end{code}

Added 5 March 2020 by Tom de Jong.

\begin{code}

¬-is-prop : funext 𝓤 𝓤₀ → {X : 𝓤 ̇ } → is-prop (¬ X)
¬-is-prop fe = Π-is-prop fe (λ x → 𝟘-is-prop)

\end{code}
