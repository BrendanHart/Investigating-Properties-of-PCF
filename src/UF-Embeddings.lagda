\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Embeddings where

open import SpartanMLTT

open import Plus-Properties
open import UF-Base
open import UF-Subsingletons
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-LeftCancellable
open import UF-Yoneda
open import UF-Retracts
open import UF-FunExt
open import UF-Subsingletons-FunExt
open import UF-Univalence
open import UF-UA-FunExt

is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding f = ∀ y → is-prop(fiber f y)

being-embedding-is-a-prop : funext 𝓥 (𝓤 ⊔ 𝓥) → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                          → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                          → is-prop(is-embedding f)
being-embedding-is-a-prop fe fe' f = Π-is-prop fe (λ x → being-a-prop-is-a-prop fe')

embedding-criterion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → ((x : X) → is-prop (fiber f (f x)))
                    → is-embedding f
embedding-criterion f φ .(f x) (x , refl) = φ x (x , refl)

embedding-criterion' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                    → ((x x' : X) → (f x ≡ f x') ≃ (x ≡ x'))
                    → is-embedding f
embedding-criterion' {𝓤} {𝓥} {X} {Y} f e =
 embedding-criterion f (λ x' → equiv-to-prop (a x') (singleton-types'-are-props x'))
 where
  a : (x' : X) → fiber f (f x') ≃ (Σ x ꞉ X , x ≡ x')
  a x' = Σ-cong (λ x → e x x')

equivs-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f → is-embedding f
equivs-are-embeddings f e y = singletons-are-props (equivs-are-vv-equivs f e y)

_↪_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ Y = Σ f ꞉ (X → Y) , is-embedding f

etofun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ↪ Y) → X → Y
etofun = pr₁

is-embedding-etofun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                    → (e : X ↪ Y) → is-embedding (etofun e)
is-embedding-etofun = pr₂

equiv-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → X ≃ Y → X ↪ Y
equiv-embedding e = ⌜ e ⌝ , equivs-are-embeddings ⌜ e ⌝ (⌜⌝-is-equiv e)

embeddings-are-left-cancellable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
             → is-embedding f → left-cancellable f
embeddings-are-left-cancellable f e {x} {x'} p = ap pr₁ (e (f x) (x , refl) (x' , (p ⁻¹)))

is-embedding' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-embedding' f = ∀ x x' → is-equiv (ap f {x} {x'})

embedding-embedding' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                     → is-embedding f → is-embedding' f
embedding-embedding' {𝓤} {𝓥} {X} {Y} f ise = g
 where
  b : (x : X) → is-singleton(fiber f (f x))
  b x = (x , refl) , ise (f x) (x , refl)
  c : (x : X) → is-singleton(fiber' f (f x))
  c x = retract-of-singleton (pr₁ (fiber-lemma f (f x)) , pr₁(pr₂(fiber-lemma f (f x)))) (b x)
  g : (x x' : X) → is-equiv(ap f {x} {x'})
  g x = universality-equiv x refl (unique-element-is-universal-element
                                         (λ x' → f x ≡ f x')
                                         (pr₁(c x))
                                         (pr₂(c x)))

embedding'-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-embedding' f → is-embedding f
embedding'-embedding {𝓤} {𝓥} {X} {Y} f ise = g
 where
  e : (x : X) → is-the-only-element-of (Σ x' ꞉ X , f x ≡ f x') (x , refl)
  e x = universal-element-is-the-only-element
         (x , refl)
         (equiv-universality x refl (ise x))
  h : (x : X) → is-prop (fiber' f (f x))
  h x σ τ = σ ≡⟨ (e x σ)⁻¹ ⟩ (x , refl) ≡⟨ e x τ ⟩ τ ∎
  g' : (y : Y) → is-prop (fiber' f y)
  g' y (x , p) = transport (λ - → is-prop (Σ x' ꞉ X , - ≡ f x')) (p ⁻¹) (h x) (x , p)
  g : (y : Y) → is-prop (fiber f y)
  g y = left-cancellable-reflects-is-prop
            (pr₁ (fiber-lemma f y))
            (section-lc _ (pr₂ (pr₂ (fiber-lemma f y)))) (g' y)

pr₁-is-embedding : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                 → ((x : X) → is-prop(Y x))
                 → is-embedding (pr₁ {𝓤} {𝓥} {X} {Y})
pr₁-is-embedding f x ((.x , y') , refl) ((.x , y'') , refl) = g
 where
  g : (x , y') , refl ≡ (x , y'') , refl
  g = ap (λ - → (x , -) , refl) (f x y' y'')

pr₁-lc-bis : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → ({x : X} → is-prop(Y x)) → left-cancellable pr₁
pr₁-lc-bis f {u} {v} r = embeddings-are-left-cancellable pr₁ (pr₁-is-embedding (λ x → f {x})) r

pr₁-is-embedding-converse : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                          → is-embedding (pr₁ {𝓤} {𝓥} {X} {Y})
                          → ((x : X) → is-prop(Y x))
pr₁-is-embedding-converse {𝓤} {𝓥} {X} {Y} ie x = h
  where
    e : Σ Y → X
    e = pr₁ {𝓤} {𝓥} {X} {Y}
    isp : is-prop(fiber e x)
    isp = ie x
    s : Y x → fiber e x
    s y = (x , y) , refl
    r : fiber e x → Y x
    r ((x , y) , refl) = y
    rs : (y : Y x) → r(s y) ≡ y
    rs y = refl
    h : is-prop(Y x)
    h = left-cancellable-reflects-is-prop s (section-lc s (r , rs)) isp

K-idtofun-lc : K-axiom (𝓤 ⁺) → {X : 𝓤 ̇ } (x y : X) (A : X → 𝓤 ̇ )
             → left-cancellable(idtofun (Id x y) (A y))
K-idtofun-lc {𝓤} k {X} x y A {p} {q} r = k (𝓤 ̇ ) p q

lc-maps-into-sets-are-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                 → left-cancellable f
                                 → is-set Y
                                 → is-embedding f
lc-maps-into-sets-are-embeddings {𝓤} {𝓥} {X} {Y} f f-lc iss y (x , p) (x' , p') = to-Σ-Id (r , q)
 where
   r : x ≡ x'
   r = f-lc (p ∙ (p' ⁻¹))
   q : yoneda-nat x (λ x → f x ≡ y) p x' r ≡ p'
   q = iss (yoneda-nat x (λ x → f x ≡ y) p x' r) p'

lc-maps-are-embeddings-with-K :
    {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
  → left-cancellable f → K-axiom 𝓥 → is-embedding f
lc-maps-are-embeddings-with-K {𝓤} {𝓥} {X} {Y} f f-lc k =
    lc-maps-into-sets-are-embeddings f f-lc (k Y)

id-is-embedding : {X : 𝓤 ̇ } → is-embedding (id {𝓤} {X})
id-is-embedding = singleton-types'-are-props

∘-is-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                 {f : X → Y} {g : Y → Z}
               → is-embedding f
               → is-embedding g
               → is-embedding (g ∘ f)
∘-is-embedding {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} e d = h
 where
  T : (z : Z) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  T z = Σ w ꞉ fiber g z , fiber f (pr₁ w)
  T-is-prop : (z : Z) → is-prop (T z)
  T-is-prop z = subtype-of-prop-is-a-prop pr₁ (pr₁-lc (λ {t} → e (pr₁ t))) (d z)
  φ : (z : Z) → fiber (g ∘ f) z → T z
  φ z (x , p) = (f x , p) , x , refl
  γ : (z : Z) → T z → fiber (g ∘ f) z
  γ z ((.(f x) , p) , x , refl) = x , p
  γφ : (z : Z) (t : fiber (g ∘ f) z) → γ z (φ z t) ≡ t
  γφ .(g (f x)) (x , refl) = refl
  h : (z : Z) → is-prop (fiber (g ∘ f) z)
  h z = subtype-of-prop-is-a-prop
         (φ z)
         (sections-are-lc (φ z) (γ z , (γφ z)))
         (T-is-prop z)

\end{code}

TODO. Redo the above proof using the technique of the following proof.

\begin{code}

embedding-factor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
                 → is-embedding (g ∘ f)
                 → is-embedding g
                 → is-embedding f
embedding-factor {𝓤} {𝓥} {𝓦} {X} {Y} {Z} f g i j = embedding-criterion' f c
 where
  a : (x x' : X) → (x ≡ x') ≃ (g (f x) ≡ g (f x'))
  a x x' = ap (g ∘ f) {x} {x'} , embedding-embedding' (g ∘ f) i x x'
  b : (y y' : Y) → (y ≡ y') ≃ (g y ≡ g y')
  b y y' = ap g {y} {y'} , embedding-embedding' g j y y'
  c : (x x' : X) → (f x ≡ f x') ≃ (x ≡ x')
  c x x' = (f x ≡ f x')         ≃⟨ b (f x) (f x') ⟩
           (g (f x) ≡ g (f x')) ≃⟨ ≃-sym (a x x') ⟩
           (x ≡ x')             ■

embedding-exponential : FunExt
                      → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (f : X → Y)
                      → is-embedding f
                      → is-embedding (λ (φ : A → X) → f ∘ φ)
embedding-exponential {𝓤} {𝓥} {𝓦} fe {X} {Y} {A} f i = embedding-criterion' (λ φ → f ∘ φ) k
 where
  g : (φ φ' : A → X) (a : A) → (φ a ≡ φ' a) ≃ (f(φ a) ≡ f(φ' a))
  g φ φ' a = ap f {φ a} {φ' a} , embedding-embedding' f i (φ a) (φ' a)
  h : (φ φ' : A → X) → φ ∼ φ' ≃ f ∘ φ ∼ f ∘ φ'
  h φ φ' = Π-cong (fe 𝓦 𝓤) (fe 𝓦 𝓥) A (λ a → φ a ≡ φ' a) (λ a → f (φ a) ≡ f (φ' a)) (g φ φ')
  k : (φ φ' : A → X) → (f ∘ φ ≡ f ∘ φ') ≃ (φ ≡ φ')
  k φ φ' = (f ∘ φ ≡ f ∘ φ') ≃⟨ ≃-funext (fe 𝓦 𝓥) (f ∘ φ) (f ∘ φ') ⟩
           (f ∘ φ ∼ f ∘ φ') ≃⟨ ≃-sym (h φ φ') ⟩
           (φ ∼ φ')         ≃⟨ ≃-sym (≃-funext (fe 𝓦 𝓤) φ φ') ⟩
           (φ ≡ φ')         ■

disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → (X → A) → (Y → A) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
disjoint-images f g = ∀ x y → f x ≢ g y

disjoint-cases-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } (f : X → A) (g : Y → A)
                         → is-embedding f → is-embedding g → disjoint-images f g
                         → is-embedding (cases f g)
disjoint-cases-embedding {𝓤} {𝓥} {𝓦} {X} {Y} {A} f g ef eg d = go
  where
   go : (a : A) (σ τ : Σ z ꞉ X + Y , cases f g z ≡ a) → σ ≡ τ
   go a (inl x , p) (inl x' , p') = r
     where
       q : x , p ≡ x' , p'
       q = ef a (x , p) (x' , p')
       h : fiber f a → fiber (cases f g) a
       h (x , p) = inl x , p
       r : inl x , p ≡ inl x' , p'
       r = ap h q
   go a (inl x , p) (inr y  , q) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inl x  , p) = 𝟘-elim (d x y (p ∙ q ⁻¹))
   go a (inr y , q) (inr y' , q') = r
     where
       p : y , q ≡ y' , q'
       p = eg a (y , q) (y' , q')
       h : fiber g a → fiber (cases f g) a
       h (y , q) = inr y , q
       r : inr y , q ≡ inr y' , q'
       r = ap h p

\end{code}

TODO.
  (1) f : X → Y is an embedding iff fiber f (f x) is a singleton for every x : X.
  (2) f : X → Y is an embedding iff its corestriction to its image is an equivalence.

This can be deduced directly from Yoneda.

\begin{code}

is-dense : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
is-dense f = is-empty (Σ y ꞉ codomain f , ¬ fiber f y)

id-is-dense : {X : 𝓤 ̇ } → is-dense (id {𝓤} {X})
id-is-dense (y , n) = n (y , refl)

comp-dense : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                {f : X → Y} {g : Y → Z}
           → is-dense f
           → is-dense g
           → is-dense (g ∘ f)
comp-dense {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} e d = h
 where
  h : ¬ (Σ z ꞉ Z , ¬ fiber (g ∘ f) z)
  h (z , n) = d (z , k)
   where
    k : ¬ fiber g z
    k (y , refl) = e (y , l)
     where
      l : ¬ fiber f y
      l (x , refl) = n (x , refl)

\end{code}

We should find a better home for the above definition, which says that
the complement of the image of f is empty. Perhaps a better
terminology would be ¬¬-dense.

\begin{code}

_↪ᵈ_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X ↪ᵈ Y = Σ f ꞉ (X → Y) , is-embedding f × is-dense f

module _ {𝓤 𝓥} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } where

 retraction-is-dense : (r : X → Y) → has-section r → is-dense r
 retraction-is-dense r (s , rs) (y , n) = n (s y , rs y)

 is-equiv-is-dense : (f : X → Y) → is-equiv f → is-dense f
 is-equiv-is-dense f e = retraction-is-dense f (equivs-have-sections f e)

 equiv-dense-embedding : X ≃ Y → X ↪ᵈ Y
 equiv-dense-embedding e = ⌜ e ⌝ ,
                           equivs-are-embeddings ⌜ e ⌝ (⌜⌝-is-equiv e),
                           is-equiv-is-dense     ⌜ e ⌝ (⌜⌝-is-equiv e)

 detofun : (X ↪ᵈ Y) → X → Y
 detofun = pr₁

 is-embedding-detofun : (e : X ↪ᵈ Y) → is-embedding(detofun e)
 is-embedding-detofun e = pr₁ (pr₂ e)

 is-dense-detofun : (e : X ↪ᵈ Y) → is-dense(detofun e)
 is-dense-detofun e = pr₂ (pr₂ e)


module _ {𝓤 𝓥 𝓦 𝓣}
         {X : 𝓤 ̇ }
         {A : X → 𝓥 ̇ }
         {Y : 𝓦 ̇ }
         {B : Y → 𝓣 ̇ }
         (f : X → Y)
         (g : (x : X) → A x → B (f x))
       where

 pair-fun : Σ A → Σ B
 pair-fun (x , a) = (f x , g x a)

 pair-fun-embedding : is-embedding f
                    → ((x : X) → is-embedding (g x))
                    → is-embedding pair-fun
 pair-fun-embedding e d (y , b) = h
  where
   Z : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
   Z = Σ w ꞉ fiber f y , fiber (g (pr₁ w)) (back-transport B (pr₂ w) b)
   Z-is-prop : is-prop Z
   Z-is-prop = subtype-of-prop-is-a-prop
                pr₁
                (pr₁-lc (λ {w} → d (pr₁ w) (back-transport B (pr₂ w) b)))
                (e y)
   φ : fiber pair-fun (y , b) → Z
   φ ((x , a) , refl) = (x , refl) , (a , refl)
   γ : Z → fiber pair-fun (y , b)
   γ ((x , refl) , (a , refl)) = (x , a) , refl
   γφ : (t : fiber pair-fun (y , b)) → γ (φ t) ≡ t
   γφ ((x , a) , refl) = refl
   h : is-prop (fiber pair-fun (y , b))
   h = subtype-of-prop-is-a-prop φ (sections-are-lc φ (γ , γφ)) Z-is-prop

 pair-fun-dense : is-dense f
               → ((x : X) → is-dense (g x))
               → is-dense pair-fun
 pair-fun-dense i j = contrapositive γ i
  where
   γ : (Σ w ꞉ Σ B , ¬ fiber pair-fun w) → Σ y ꞉ Y , ¬ fiber f y
   γ ((y , b) , n) = y , m
    where
     m : ¬ fiber f y
     m (x , refl) = j x (b , l)
      where
       l : ¬ fiber (g x) b
       l (a , refl) = n ((x , a) , refl)

inl-is-embedding : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                 → is-embedding (inl {𝓤} {𝓥} {X} {Y})
inl-is-embedding {𝓤} {𝓥} X Y (inl a) (.a , refl) (.a , refl) = refl
inl-is-embedding {𝓤} {𝓥} X Y (inr b) (x , p) (x' , p') = 𝟘-elim (+disjoint p)

inr-is-embedding : (X : 𝓤 ̇ ) (Y : 𝓥 ̇ )
                 → is-embedding (inr {𝓤} {𝓥} {X} {Y})
inr-is-embedding {𝓤} {𝓥} X Y (inl b) (x , p) (x' , p') = 𝟘-elim (+disjoint' p)
inr-is-embedding {𝓤} {𝓥} X Y (inr a) (.a , refl) (.a , refl) = refl

maps-of-props-into-sets-are-embeddings : {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
                                       → is-prop P → is-set X → is-embedding f
maps-of-props-into-sets-are-embeddings f i j q (p , s) (p' , s') = to-Σ-≡ (i p p' , j _ s')

maps-of-props-are-embeddings : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } (f : P → Q)
                             → is-prop P → is-prop Q → is-embedding f
maps-of-props-are-embeddings f i j = maps-of-props-into-sets-are-embeddings f i (props-are-sets j)

×-embedding : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } {B : 𝓣 ̇ }
                (f : X → A ) (g : Y → B)
            → is-embedding f
            → is-embedding g
            → is-embedding (λ (z : X × Y) → (f (pr₁ z) , g (pr₂ z)))
×-embedding f g i j (a , b) = retract-of-prop (r , (s , rs))
                                                      (×-is-prop (i a) (j b))
 where
  r : fiber f a × fiber g b → fiber (λ z → f (pr₁ z) , g (pr₂ z)) (a , b)
  r ((x , s) , (y , t)) = (x , y) , to-×-≡ s t
  s : fiber (λ z → f (pr₁ z) , g (pr₂ z)) (a , b) → fiber f a × fiber g b
  s ((x , y) , p) = (x , ap pr₁ p) , (y , ap pr₂ p)
  rs : (φ : fiber (λ z → f (pr₁ z) , g (pr₂ z)) (a , b)) → r (s φ) ≡ φ
  rs ((x , y) , refl) = refl

NatΣ-is-embedding : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                  → ((x : X) → is-embedding(ζ x)) → is-embedding(NatΣ ζ)
NatΣ-is-embedding A B ζ i (x , b) = equiv-to-prop
                                     (≃-sym (NatΣ-fiber-equiv A B ζ x b))
                                     (i x b)

NatΣ-is-embedding-converse : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                           → is-embedding(NatΣ ζ) → ((x : X) → is-embedding(ζ x))
NatΣ-is-embedding-converse A B ζ e x b = equiv-to-prop
                                          (NatΣ-fiber-equiv A B ζ x b)
                                          (e (x , b))

NatΠ-is-embedding : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (ζ : Nat A B)
                  → funext 𝓤 𝓦  → funext 𝓤 (𝓥 ⊔ 𝓦)
                  → ((x : X) → is-embedding(ζ x)) → is-embedding(NatΠ ζ)
NatΠ-is-embedding A B ζ fe fe' i g = equiv-to-prop
                                      (≃-sym (NatΠ-fiber-equiv A B ζ fe g))
                                      (Π-is-prop fe' (λ x → i x (g x)))

\end{code}

For any proposition P, the unique map P → 𝟙 is an embedding:

\begin{code}

prop-embedding : (P : 𝓤 ̇ ) → is-prop P → ∀ 𝓥 → is-embedding (λ (p : P) → * {𝓥})
prop-embedding P i 𝓥 * (p , r) (p' , r') = to-×-≡ (i p p')
                                                  (props-are-sets 𝟙-is-prop r r')
\end{code}

Added by Tom de Jong.

If a type X embeds into a proposition, then X is itself a proposition.

\begin{code}

embedding-into-prop : {X : 𝓤 ̇ } {P : 𝓥 ̇ } → is-prop P → X ↪ P → is-prop X
embedding-into-prop i (f , e) x y = d
 where
   a : x ≡ y → f x ≡ f y
   a = ap f {x} {y}
   b : is-equiv a
   b = embedding-embedding' f e x y
   c : f x ≡ f y
   c = i (f x) (f y)
   d : x ≡ y
   d = inverse a b c

\end{code}

\begin{code}

infix  0 _↪_

\end{code}
