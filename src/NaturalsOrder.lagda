Martin Escardo, started 5th May 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module NaturalsOrder where

open import SpartanMLTT

open import UF-Subsingletons
open import OrdinalNotions hiding (_≤_ ; <-coarser-than-≤ ; ≤-refl)
open import NaturalsAddition renaming (_+_ to _+'_)
open import NaturalNumbers-Properties

_≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
zero ≤ n        = 𝟙
succ m ≤ zero   = 𝟘
succ m ≤ succ n = m ≤ n

x ≥ y = y ≤ x

≤-is-prop-valued : (m n : ℕ) → is-prop (m ≤ n)
≤-is-prop-valued zero n = 𝟙-is-prop
≤-is-prop-valued (succ m) zero = 𝟘-is-prop
≤-is-prop-valued (succ m) (succ n) = ≤-is-prop-valued m n

open import UF-Base
open import UF-Miscelanea

right-addition-is-embedding : (m n : ℕ) → is-prop (Σ k ꞉ ℕ , k +' m ≡ n)
right-addition-is-embedding zero n (.n , refl) (.n , refl) = refl
right-addition-is-embedding (succ m) zero (k , p) (k' , p') = 𝟘-elim (positive-not-zero (k +' m) p)
right-addition-is-embedding (succ m) (succ n) (k , p) (k' , p') = to-Σ-≡ (ap pr₁ IH , ℕ-is-set _ _)
 where
  IH : k , succ-lc p ≡ k' , succ-lc p'
  IH = right-addition-is-embedding m n (k , succ-lc p) (k' , succ-lc p')

subtraction : (m n : ℕ) → m ≤ n → Σ k ꞉ ℕ , k +' m ≡ n
subtraction zero n l = n , refl
subtraction (succ m) zero l = 𝟘-elim l
subtraction (succ m) (succ n) l = pr₁ IH , ap succ (pr₂ IH)
 where
  IH : Σ k ꞉ ℕ , k +' m ≡ n
  IH = subtraction m n l

cosubtraction : (m n : ℕ) → (Σ k ꞉ ℕ , k +' m ≡ n) → m ≤ n
cosubtraction zero n (.n , refl) = *
cosubtraction (succ m) zero (k , p) = positive-not-zero (k +' m) p
cosubtraction (succ m) (succ .(k +' m)) (k , refl) = cosubtraction m (k +' m) (k , refl)

zero-minimal : (n : ℕ) → zero ≤ n
zero-minimal n = *

zero-minimal' : (n : ℕ) → ¬(succ n ≤ zero)
zero-minimal' n l = l

zero-minimal'' : (n : ℕ) → n ≤ zero → n ≡ zero
zero-minimal'' zero l = refl

succ-monotone : (m n : ℕ) → m ≤ n → succ m ≤ succ n
succ-monotone m n l = l

succ-order-injective : (m n : ℕ) → succ m ≤ succ n → m ≤ n
succ-order-injective m n l = l

≤-induction : (P : (m n : ℕ) (l : m ≤ n) → 𝓤 ̇ )
            → ((n : ℕ) → P zero n (zero-minimal n))
            → ((m n : ℕ) (l : m ≤ n) → P m n l → P (succ m) (succ n) (succ-monotone m n l))
            → (m n : ℕ) (l : m ≤ n) → P m n l
≤-induction P base step zero n *            = base n
≤-induction P base step (succ m) zero l     = 𝟘-elim l
≤-induction P base step (succ m) (succ n) l = step m n l (≤-induction P base step m n l)

succ≤≡ : (m n : ℕ) → (succ m ≤ succ n) ≡ (m ≤ n)
succ≤≡ m n = refl

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero     = *
≤-refl (succ n) = ≤-refl n

≤-trans : (l m n : ℕ) → l ≤ m → m ≤ n → l ≤ n
≤-trans zero m n p q = *
≤-trans (succ l) zero n p q = 𝟘-elim p
≤-trans (succ l) (succ m) zero p q = 𝟘-elim q
≤-trans (succ l) (succ m) (succ n) p q = ≤-trans l m n p q

≤-anti : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
≤-anti zero zero p q = refl
≤-anti zero (succ n) p q = 𝟘-elim q
≤-anti (succ m) zero p q = 𝟘-elim p
≤-anti (succ m) (succ n) p q = ap succ (≤-anti m n p q)

≤-succ : (n : ℕ) → n ≤ succ n
≤-succ zero     = *
≤-succ (succ n) = ≤-succ n

unique-minimal : (n : ℕ) → n ≤ zero → n ≡ zero
unique-minimal zero l = refl
unique-minimal (succ n) l = 𝟘-elim l

≤-split : (m n : ℕ) → m ≤ succ n → (m ≤ n) + (m ≡ succ n)
≤-split zero n l = inl l
≤-split (succ m) zero l = inr (ap succ (unique-minimal m l))
≤-split (succ m) (succ n) l = cases inl (inr ∘ (ap succ)) (≤-split m n l)

≤-join : (m n : ℕ) → (m ≤ n) + (m ≡ succ n) → m ≤ succ n
≤-join m n (inl l) = ≤-trans m n (succ n) l (≤-succ n)
≤-join .(succ n) n (inr refl) = ≤-refl n

≤-down : (m n : ℕ) → m ≤ succ n → (m ≢ succ n) → (m ≤ n)
≤-down m n l u = cases id (λ p → 𝟘-elim (u p)) (≤-split m n l)

≤-+ : (m n : ℕ) → (m ≤ m +' n)
≤-+ m zero     = ≤-refl m
≤-+ m (succ n) = ≤-join m (m +' n) (inl IH)
 where
  IH : m ≤ m +' n
  IH = ≤-+ m n

≤-+' : (m n : ℕ) → (n ≤ m +' n)
≤-+' m n = transport (λ k → n ≤ k) γ (≤-+ n m)
 where
  γ : n +' m ≡ m +' n
  γ = addition-commutativity n m

_<_ _>_ : ℕ → ℕ → 𝓤₀ ̇
m < n = succ m ≤ n

<-succ : (n : ℕ) → n < succ n
<-succ = ≤-refl

x > y = y < x

not-less-than-itself : (n : ℕ) → ¬(n < n)
not-less-than-itself zero l = l
not-less-than-itself (succ n) l = not-less-than-itself n l

not-less-bigger-or-equal : (m n : ℕ) → ¬(n < m) → n ≥ m
not-less-bigger-or-equal zero n u = zero-minimal n
not-less-bigger-or-equal (succ m) zero = double-negation-intro (zero-minimal m)
not-less-bigger-or-equal (succ m) (succ n) = not-less-bigger-or-equal m n

bigger-or-equal-not-less : (m n : ℕ) → n ≥ m → ¬(n < m)
bigger-or-equal-not-less m n l u = not-less-than-itself n (≤-trans (succ n) m n u l)

less-not-bigger-or-equal : (m n : ℕ) → m < n → ¬(n ≤ m)
less-not-bigger-or-equal m n l u = bigger-or-equal-not-less n m u l

bounded-∀-next : (A : ℕ → 𝓤 ̇ ) (k : ℕ)
               → A k
               → ((n : ℕ) → n < k → A n)
               → (n : ℕ) → n < succ k → A n
bounded-∀-next A k a φ n l = cases f g s
 where
  s : (n < k) + (succ n ≡ succ k)
  s = ≤-split (succ n) k l
  f : n < k → A n
  f = φ n
  g : succ n ≡ succ k → A n
  g p = back-transport A (succ-lc p) a

\end{code}

Added 20th June 2018:

\begin{code}

<-is-prop-valued : (m n : ℕ) → is-prop(m < n)
<-is-prop-valued m n = ≤-is-prop-valued (succ m) n

<-coarser-than-≤ : (m n : ℕ) → m < n → m ≤ n
<-coarser-than-≤ m n = ≤-trans m (succ m) n (≤-succ m)

<-trans : (l m n : ℕ) → l < m → m < n → l < n
<-trans l m n u v = ≤-trans (succ l) m n u (<-coarser-than-≤ m n v)

<-split : (m n : ℕ) → m < succ n → (m < n) + (m ≡ n)
<-split m zero     l = inr (unique-minimal m l)
<-split m (succ n) l = ≤-split m n l

regress : (P : ℕ → 𝓤 ̇ )
        → ((n : ℕ) → P (succ n) → P n)
        → (n m : ℕ) → m ≤ n → P n → P m
regress P ρ zero m l p = back-transport P (unique-minimal m l) p
regress P ρ (succ n) m l p = cases (λ (l' : m ≤ n) → IH m l' (ρ n p))
                                   (λ (r : m ≡ succ n) → back-transport P r p)
                                   (≤-split m n l)
 where
  IH : (m : ℕ) → m ≤ n → P n → P m
  IH = regress P ρ n

<-is-well-founded : (m : ℕ) → is-accessible _<_ m
<-is-well-founded zero     = next zero     (λ y l → unique-from-𝟘 l)
<-is-well-founded (succ m) = next (succ m) (τ (<-is-well-founded m))
 where
  τ : is-accessible _<_ m → (n : ℕ) → n < succ m → is-accessible _<_ n
  τ a n u = cases (λ (v : n < m) → prev _<_ m a n v)
                  (λ (p : n ≡ m) → back-transport (is-accessible _<_) p a)
                  (<-split n m u)

course-of-values-induction : (P : ℕ → 𝓤 ̇ )
                           → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
                           → (n : ℕ) → P n
course-of-values-induction = transfinite-induction _<_ <-is-well-founded

<-is-extensional : is-extensional _<_
<-is-extensional zero     zero     f g = refl
<-is-extensional zero     (succ n) f g = unique-from-𝟘 (g zero (zero-minimal n))
<-is-extensional (succ m) (zero)   f g = unique-from-𝟘 (f zero (zero-minimal m))
<-is-extensional (succ m) (succ n) f g = ap succ (≤-anti m n (f m (≤-refl m)) (g n (≤-refl n)))

ℕ-ordinal : is-well-order _<_
ℕ-ordinal = <-is-prop-valued , <-is-well-founded , <-is-extensional , <-trans

\end{code}

Induction on z, then x, then y:

\begin{code}

ℕ-cotransitive : cotransitive _<_
ℕ-cotransitive zero     y        zero     l = inr l
ℕ-cotransitive (succ x) y        zero     l = inr (≤-trans 1 (succ(succ x)) y * l)
ℕ-cotransitive zero     (succ y) (succ z) l = inl (zero-minimal y)
ℕ-cotransitive (succ x) (succ y) (succ z) l = γ IH
 where
  IH : (x < z) + (z < y)
  IH = ℕ-cotransitive x y z l
  γ : (x < z) + (z < y) → (succ x < succ z) + (succ z < succ y)
  γ (inl l) = inl (succ-monotone (succ x) z l)
  γ (inr r) = inr (succ-monotone (succ z) y r)

\end{code}

Added December 2019.

\begin{code}

open import DecidableAndDetachable

≤-decidable : (m n : ℕ ) → decidable (m ≤ n)
≤-decidable zero     n        = inl (zero-minimal n)
≤-decidable (succ m) zero     = inr (zero-minimal' m)
≤-decidable (succ m) (succ n) = ≤-decidable m n

<-decidable : (m n : ℕ ) → decidable (m < n)
<-decidable m n = ≤-decidable (succ m) n

\end{code}

Bounded minimization (added 14th December 2019):

\begin{code}

βμ : (A : ℕ → 𝓤 ̇ ) → detachable A
  → (k : ℕ) → (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → A n → m ≤ n))
            + ((n : ℕ) → A n → n ≥ k)

βμ A δ 0 = inr (λ n a → zero-minimal n)
βμ A δ (succ k) = cases f g (βμ A δ k)
 where
  conclusion = type-of (βμ A δ (succ k))
  f : (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → A n → m ≤ n)) → conclusion
  f (m , l , a , φ) = inl (m , <-trans m k (succ k) l (<-succ k) , a , φ)
  g : ((n : ℕ) → A n → k ≤ n) → conclusion
  g φ = cases g₀ g₁ (δ k)
   where
    g₀ : A k → conclusion
    g₀ a = inl (k , ≤-refl k , a , φ)
    g₁ : ¬ A k → conclusion
    g₁ u = inr ψ
     where
      ψ : (n : ℕ) → A n → succ k ≤ n
      ψ 0 a = 𝟘-elim (v a)
       where
        p : k ≡ 0
        p = zero-minimal'' k (φ 0 a)
        v : ¬ A 0
        v = transport (λ - → ¬ A -) p u
      ψ (succ n) a = III
       where
        I : k ≤ succ n
        I = φ (succ n) a
        II : k ≢ succ n
        II p = transport (λ - → ¬ A -) p u a
        III : k ≤ n
        III = ≤-down k n I II

\end{code}

Given k : ℕ with A k, find the minimal m : ℕ with A m, by reduction to
bounded minimization:

\begin{code}

Σμ : (ℕ → 𝓤 ̇ ) → 𝓤 ̇
Σμ A = Σ m ꞉ ℕ , A m × ((n : ℕ) → A n → m ≤ n)

minimal-from-given : (A : ℕ → 𝓤 ̇ ) → detachable A → Σ A → Σμ A
minimal-from-given A δ (k , a) = cases f g (βμ A δ k)
 where
  conclusion = type-of (minimal-from-given A δ (k , a))
  f : (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → A n → m ≤ n)) → conclusion
  f (m , l , a' , φ) = m , a' , φ
  g : ((n : ℕ) → A n → k ≤ n) → conclusion
  g φ = k , a , φ

\end{code}
