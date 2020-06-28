\documentclass[main.tex]{subfiles}
\begin{document}
\AgdaNoSpaceAroundCode{
\begin{code}[hide]

open import UF-PropTrunc
open import SpartanMLTT

module ScottModel
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt
open import PCF-With-Lambda pt
open import Dcpo pt fe 𝓤₀ renaming (constant-functions-are-continuous to const-functions-are-continuous)
open import DcpoConstructions pt fe
open DcpoConstructionsGeneral 𝓤₀
open LiftingDcpo 𝓤₀ pe

open import DcpoProducts pt fe 
open DcpoProductsGeneral 𝓤₀ hiding (to-×-DCPO ; to-×-DCPO⊥)
open import DcpoProducts-Curry pt fe 𝓤₀ hiding (eval)

open import Dcpo-IfZero pt fe pe hiding (⦅ifZero⦆-arguments ; ⦅ifZero⦆Γ ; ⦅ifZero⦆-uncurried' ; ⦅ifZero⦆-uncurried)
open import Dcpo-Contexts pt fe pe hiding ( ⊤ᵈᶜᵖᵒ ; ⊤ᵈᶜᵖᵒ⊥ ;【_】 ; var-DCPO ; var-DCPO⊥ ; extract ; ∘-of-prₓ-is-continuous )
open import Dcpo-FunctionComposition pt fe 𝓤₀
open import DcpoProducts-Continuity pt fe 𝓤₀

open import NaturalNumbers-Properties
open import UF-Miscelanea

open import Lifting 𝓤₀
open import LiftingMonad 𝓤₀ hiding (μ)

\end{code}
}
\section{Scott Model of PCF}
\label{scottmodel}
With our constructions in domain theory, we now have enough to define the Scott model of PCF \cite{Scott1993}.
\subsection{Types}
We define the following function from PCF types to their denotational interpretation:
\begin{code}
⟦_⟧ : type → DCPO⊥ {𝓤₁} {𝓤₁}
\end{code}
We have two cases we need to provide an interpretation for. The first is the base type, and the second is the function type.
\subsubsection*{The base type}
We first construct the representation of our base type \AgdaInductiveConstructor{ι}. We follow our intuitions from \cref{domaintheory} that we represent \AgdaInductiveConstructor{ι} as a DCPO, where the underlying set is $ℕ\cup⊥$, with the information ordering.

In our construction, to embed the notion of an undefined element into our set, we use the lifting monad as Tom de Jong does \cite{jong2019scott}. The lifting monad, from a type such as $ℕ$, construct a new type $𝓛\ ℕ$, called the ``lifting'' of $ℕ$. The lifting of $ℕ$ gives us a way to express the definedness of elements, allowing us to say that all elements from the original type $ℕ$ are ``total'' (defined), and there is an undefined element $⊥$.

The importance of using the lifting monad is it gives us a constructive way to represent the definedness of elements, and from this we can proceed to define an order which is compatible with our developments:
\begin{center}
$x \mathbin{⊑} y = \operatorname{is-defined} x → x ≡ y$
\end{center}
This order follows our intuition that for flat domains, $⊥$ is less than all other elements, and total elements are incomparable.

It also follows that a lifted type $𝓛\ Y$ forms a DCPO under the above ordering if the type $Y$ is a set, as shown by Knapp and Escard\'o \cite{escardoknapppartial}. This construction of a DCPO from a lifted type has been developed in Agda by Tom de Jong. We shall be making use of \AgdaFunction{𝓛-DCPO⊥}, which, given a set $Y$, will produce a DCPO with least element $⊥$ under the mentioned ordering, where the underlying set is the lifting of $Y$. We can produce the total elements of the lifting of $Y$ in Agda from an element \AgdaBound{n} of the type $Y$ as \AgdaFunction{η}\AgdaSpace{}\AgdaBound{n}, and there is always the undefined element \AgdaFunction{⊥} as previously discussed.

We can now construct the interpretation of the base type \AgdaInductiveConstructor{ι}. We use the fact that \AgdaDatatype{ℕ} is a set from Mart\'in Escard\'o's developments. For shorthand, we will use \AgdaFunction{𝓛ᵈℕ} to refer to the DCPO of the lifted natural numbers. 
\begin{code}
⟦ ι ⟧     = 𝓛ᵈℕ
\end{code}
\subsubsection*{Function types}
We then represent function type \AgdaPCFType{σ}{τ} as a DCPO with $⊥$ where the underlying set is continuous functions from the interpretation of \AgdaBound{σ} and the interpretation of \AgdaBound{τ}.
\begin{code}
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ ⟹ᵈᶜᵖᵒ⊥ ⟦ τ ⟧
\end{code}

\subsection{Contexts}
We interpret contexts simply as a product between the interpretation of each type within the context. 

The first consideration is to develop a representation for the empty context. We form a DCPO where the underlying set is \AgdaDatatype{𝟙} - the type with one element, namely \AgdaInductiveConstructor{*}. We associate an order which states for any \AgdaBound{x} and \AgdaBound{y} of type \AgdaDatatype{𝟙}, we have \AgdaBound{x}\AgdaSpace{}\AgdaFunction{⊑⟨⊤⟩}\AgdaSpace{}\AgdaBound{y}. The set \AgdaDatatype{𝟙} and this order form a DCPO, which we name in Agda as \AgdaType{\AgdaFunction{⊤ᵈᶜᵖᵒ}}{\AgdaFunction{DCPO}\AgdaSpace{}\AgdaSymbol{\{}\AgdaFunction{𝓤₁}\AgdaSymbol{\}}\AgdaSpace{}\AgdaSymbol{\{}\AgdaFunction{𝓤₁}\AgdaSymbol{\}}}. We omit the trivial definition and proof of DCPO axioms for brevity. It is also trivial to show this DCPO contains a least element, namely \AgdaInductiveConstructor{*}, which we show in Agda in the proof \AgdaType{\AgdaFunction{⊤ᵈᶜᵖᵒ⊥}}{\AgdaFunction{DCPO⊥}\AgdaSpace{}\AgdaSymbol{\{}\AgdaFunction{𝓤₁}\AgdaSymbol{\}}\AgdaSpace{}\AgdaSymbol{\{}\AgdaFunction{𝓤₁}\AgdaSymbol{\}}}.
\hide{
\begin{code}[hide]
⊤ᵈᶜᵖᵒ : DCPO {𝓤₁} {𝓤₁}
⊤ᵈᶜᵖᵒ = 𝟙 , _⊑⟨⊤⟩_ , s , p , r , t , a , d
  where
    _⊑⟨⊤⟩_ : 𝟙 {𝓤₁} → 𝟙 {𝓤₁} → 𝓤₁ ̇
    x ⊑⟨⊤⟩ y = 𝟙
    s : is-set 𝟙
    s = props-are-sets 𝟙-is-prop
    p : is-prop-valued {𝓤₁} {𝓤₁} {𝟙} (λ x y → 𝟙)
    p _ _ * * = refl
    r : is-reflexive _⊑⟨⊤⟩_
    r _ = *
    t : is-transitive {𝓤₁} {𝓤₁} {𝟙} (λ x y → 𝟙)
    t _ _ _ _ _ = *
    a : ∀ (x y : 𝟙) → x ⊑⟨⊤⟩ y → y ⊑⟨⊤⟩ x → x ≡ y
    a * * _ _ = refl
    d : is-directed-complete (λ x y → 𝟙)
    d _ _ _ = * , ((λ _ → *) , (λ _ _ → *))
\end{code}
Then, the proof that this forms a DCPO with bottom is trivial. We only have one possible element that can be our least element, the sole inhabitant of \AgdaFunction{𝟙}. Since our order is just defined as \AgdaFunction{𝟙} for any \AgdaBound{x} and \AgdaBound{y}, a proof that \AgdaInductiveConstructor{*} is less than any other element of the underlying set \AgdaFunction{𝟙} is just the sole element of \AgdaFunction{𝟙}, \AgdaInductiveConstructor{*}. 
\begin{code}
Tᵈᶜᵖᵒ⊥ : DCPO⊥ {𝓤₁} {𝓤₁}
Tᵈᶜᵖᵒ⊥ = ⊤ᵈᶜᵖᵒ , (* , λ _ → *)
\end{code}
}

We now can inductively define our interpretation of a context. For our inductive case where we have a context \AgdaExtendContext{Γ}{x}, we make use of \AgdaFunction{×ᵈᶜᵖᵒ⊥} to form the product between the interpretation of \AgdaBound{Γ} and the interpretation of the type \AgdaBound{x}.
\begin{code}
【_】 : {n : ℕ} (Γ : Context n) → DCPO⊥ {𝓤₁} {𝓤₁}
【 ⟨⟩ 】 = Tᵈᶜᵖᵒ⊥
【 Γ ’ x 】 = 【 Γ 】 ×ᵈᶜᵖᵒ⊥ ⟦ x ⟧
\end{code}
From this definition, we can think of \AgdaBound{d}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaFunction{⟨}\AgdaSpace{}\AgdaFunction{⟪}\AgdaSpace{}\AgdaFunction{【}\AgdaSpace{}\AgdaBound{Γ}\AgdaSpace{}\AgdaFunction{】}\AgdaSpace{}\AgdaFunction{⟫}\AgdaSpace{}\AgdaFunction{⟩} as representing a list of values for our variables in the context \AgdaBound{Γ} to be substituted with in our denotational interpretation.

\subsection{Terms}
We next inductively define the interpretation of terms. Since terms may contain free variables, we interpret a term of type \AgdaBound{σ} under a given context \AgdaBound{Γ} as a continuous function from the interpretation of the context to the interpretation of \AgdaBound{σ}. Intuitively, this means that given a list of values of the types listed in \AgdaBound{Γ}, we can produce a closed term belonging to the type \AgdaBound{σ}. We begin by first developing some constructs which we will use in our interpretation function.

\subsubsection*{Interpreting variables}
When interpreting the term \AgdaVar{i} which has the type $σ$ under a context \AgdaBound{Γ}, it makes sense that this is essentially the $i$-th projection of an inhabitant of \AgdaExtractSet{\AgdaExtractDCPO{\AgdaContextInterp{Γ}}}. As such, we can see this as a continuous function between \AgdaContextInterp{Γ} and \AgdaTypeInterp{σ}.

We implement this $i$-th projection in Agda by induction on the lookup judgement. We take the second projection after taking $i$ first projections, to extract the desired value.
\begin{code}
extract : {n : ℕ} {σ : type} {Γ : Context n} → (x : Γ ∋ σ) → ⟨ ⟪ 【 Γ 】 ⟫ ⟩  → ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩
extract Z (_ , a) = a
extract (S x) (d , _) = extract x d
\end{code}
Since in our setting we require that functions are continuous, we need a proof of continuity. For any variable \AgdaVar{x}, we will want our underlying function to be \AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x}. As a result we need to show that for any lookup judgement \AgdaBound{x}, \AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x} is a continuous function. We show this is the case by induction on the lookup judgement itself, as this determines the structure of \AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x}. The first case is when the lookup judgement is \AgdaInductiveConstructor{Z}, and we can provide our value. In this case, our function is just \AgdaField{pr₂}, so we provide a proof that \AgdaField{pr₂} is continuous.
\begin{code}
extract-is-continuous : {n : ℕ} {Γ : Context n} {σ : type} (x : Γ ∋ σ)
                        → is-continuous ⟪ 【 Γ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫ (extract x)
extract-is-continuous {_} {Γ ’ σ} {σ} Z = continuity-of-function ⟪ 【 Γ ’ σ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫
                                                        (pr₂-is-continuous ⟪ 【 Γ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫)
\end{code}
In the inductive case, we have a context \AgdaExtendContext{Γ}{τ}, and a proof \AgdaLookupJudge{x}{Γ}{σ}.
\AgdaFunction{extract}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x}} is the same as \AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x}\AgdaSpace{}\AgdaFunction{∘}\AgdaSpace{}\AgdaField{pr₁}. Since we have a proof \AgdaFunction{∘ᵈᶜᵖᵒ} that the composition of continuous functions produces a continuous function, we just need to prove that \AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x} is a continuous function, and that \AgdaField{pr₁} is continuous. The fact that \AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x} is continuous is provided by our inductive hypothesis, and \AgdaField{pr₁} is known to be continuous. As such, the continuity property of the composition of these continuous functions is enough to complete the proof.
\begin{code}
extract-is-continuous {_} {Γ ’ τ} {σ} (S x)
                   = continuity-of-function ⟪ 【 Γ ’ τ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫ ( [ ⟪ 【 Γ ’ τ 】 ⟫ , ⟪ 【 Γ 】 ⟫ , ⟪ ⟦ σ ⟧ ⟫ ]
                                 extract x , (extract-is-continuous x) ∘ᵈᶜᵖᵒ pr₁-is-continuous ⟪ 【 Γ 】 ⟫ ⟪ ⟦ τ ⟧ ⟫)
\end{code}
We then provide a function which, for any lookup judgement, provides a continuous function which extracts the desired value from a context.
\begin{code}
var-extract : {n : ℕ} {σ : type} {Γ : Context n} → (x : Γ ∋ σ) → DCPO[ ⟪ 【 Γ 】 ⟫ , ⟪ ⟦ σ ⟧ ⟫ ]
var-extract x = extract x , extract-is-continuous x
\end{code}
\subsubsection*{Interpreting IfZero} 
In his implementation of the Scott model of a combinatorial version of PCF, Tom de Jong has developed an interpretation of \AgdaInductiveConstructor{IfZero} in his setting. He defined the interpretation using the Kleisli extension as $\lambda x,y.\pa{\chi_{x,y}}^{\#}$, where:
    \[
      \chi_{x,y}(n) \colonequiv
      \begin{cases}
        x &\text{if } n = 0; \\
        y &\text{else};
      \end{cases}
    \]
However, since our implementation of PCF has contexts, we cannot just use Tom de Jong's interpretation for our \AgdaInductiveConstructor{IfZero}. Instead, we construct a way to first evaluate our terms \AgdaBound{t}, \AgdaBound{t₁}, and \AgdaBound{t₂} which make up a term \AgdaIfZero{t}{t₁}{t₂} under a context \AgdaBound{Γ}.
\begin{code}[hide]
module _ (𝓓 : DCPO {𝓤} {𝓤'})
        (𝓔 : DCPO {𝓣} {𝓣'})
        (𝓕 : DCPO {𝓦} {𝓦'})
    where
\end{code}

We first define a continuous function to apply a list of values for a context to two terms at once. We generalise this to constructing a new continuous function from two continuous functions of the same input domain. We omit the proof of continuity for brevity.
\begin{code}
  to-×-DCPO : DCPO[ 𝓓 , 𝓔 ] →  DCPO[ 𝓓 , 𝓕 ] → DCPO[ 𝓓 , 𝓔 ×ᵈᶜᵖᵒ 𝓕 ]
  to-×-DCPO f g = h , c
    where
      h : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩
      h d = (underlying-function 𝓓 𝓔 f d) , (underlying-function 𝓓 𝓕 g d)
      c : is-continuous 𝓓 (𝓔 ×ᵈᶜᵖᵒ 𝓕) h
      c I α δ = u , s -- Proofs of u and s omitted for brevity
\end{code}
\begin{code}[hide]
        where
          h-is-monotone : is-monotone 𝓓 (𝓔 ×ᵈᶜᵖᵒ 𝓕) h
          h-is-monotone x y p = (continuous-functions-are-monotone 𝓓 𝓔 f x y p)
                                    , (continuous-functions-are-monotone 𝓓 𝓕 g x y p)
          u : is-upperbound (underlying-order (𝓔 ×ᵈᶜᵖᵒ 𝓕)) (h (∐ 𝓓 δ)) (λ i → h (α i))
          u i = h-is-monotone (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i)
          s : (u₁ : ⟨ 𝓔 ×ᵈᶜᵖᵒ 𝓕 ⟩) →
                ((i : I) → underlying-order (𝓔 ×ᵈᶜᵖᵒ 𝓕) (h (α i)) u₁) →
                underlying-order (𝓔 ×ᵈᶜᵖᵒ 𝓕) (h (∐ 𝓓 δ)) u₁
          s (u₁ , u₂) p = e₁ , e₂
            where
              e₁ : underlying-function 𝓓 𝓔 f (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ u₁
              e₁ = transport (λ - → - ⊑⟨ 𝓔 ⟩ u₁) (p₁ ⁻¹) e₃
                where
                  p₁ : underlying-function 𝓓 𝓔 f (∐ 𝓓 δ) ≡ ∐ 𝓔 (image-is-directed 𝓓 𝓔 f δ)
                  p₁ = continuous-function-∐-≡ 𝓓 𝓔 f δ
                  e₃ : ∐ 𝓔 (image-is-directed 𝓓 𝓔 f δ) ⊑⟨ 𝓔 ⟩ u₁
                  e₃ = ∐-is-lowerbound-of-upperbounds 𝓔 (image-is-directed 𝓓 𝓔 f δ) u₁ (λ i → pr₁ (p i))
              e₂ : underlying-function 𝓓 𝓕 g (∐ 𝓓 δ) ⊑⟨ 𝓕 ⟩ u₂
              e₂ = transport (λ - → - ⊑⟨ 𝓕 ⟩ u₂) (p₁ ⁻¹) e₃
                where
                  p₁ : underlying-function 𝓓 𝓕 g (∐ 𝓓 δ) ≡ ∐ 𝓕 (image-is-directed 𝓓 𝓕 g δ)
                  p₁ = continuous-function-∐-≡ 𝓓 𝓕 g δ
                  e₃ : ∐ 𝓕 (image-is-directed 𝓓 𝓕 g δ) ⊑⟨ 𝓕 ⟩ u₂
                  e₃ = ∐-is-lowerbound-of-upperbounds 𝓕 (image-is-directed 𝓓 𝓕 g δ) u₂ (λ i → pr₂ (p i))
\end{code}
\begin{code}[hide]
module _ (𝓓 : DCPO⊥ {𝓤} {𝓤'})
        (𝓔 : DCPO⊥ {𝓣} {𝓣'})
        (𝓕 : DCPO⊥ {𝓦} {𝓦'})
    where
\end{code}
We then, for convenience, define this for continuous functions on DCPOs with least elements.
\begin{code}
  to-×-DCPO⊥ : DCPO⊥[ 𝓓 , 𝓔 ] → DCPO⊥[ 𝓓 , 𝓕 ] → DCPO⊥[ 𝓓 , 𝓔 ×ᵈᶜᵖᵒ⊥ 𝓕 ]
  to-×-DCPO⊥ f g = to-×-DCPO ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ f g
\end{code}
\begin{code}[hide]
module _ {a : ℕ} (Γ : Context a)
        where
\end{code}
Since we have three terms which we want to evaluate under the same context, we can then use \AgdaFunction{to-×-DCPO⊥} to construct a continuous function that can perform the denotational substitution of a list of values for the variables in the context to take on. This is just two applications of \AgdaFunction{to-×-DCPO⊥}. The first to form a continuous function that evaluates two terms under the same context, and the second application to form a continuous function which evaluates the original two terms and a third term under the same context. We construct this in such a manner that we end up with the result being a pair of the form $((a , b) , c)$ as opposed to $(a , (b , c))$. This will prevent us from having to use a proof of associativity of the product of DCPOs, which will become apparent later. 
\begin{code}
  ⦅ifZero⦆-arguments : DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
                   → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
  ⦅ifZero⦆-arguments a b c = to-×-DCPO⊥ 【 Γ 】 (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) 𝓛ᵈℕ f c
        where
          f : DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
          f = to-×-DCPO⊥ 【 Γ 】 𝓛ᵈℕ 𝓛ᵈℕ a b
\end{code}
Now we have a way to evaluate all three of our terms under the same context, we next look at how we can make use of Tom de Jong's interpretation of \AgdaInductiveConstructor{IfZero} from his combinatorial setting. The type of this interpretation is \AgdaConFunBot{\AgdaFunction{𝓛ᵈℕ}}{\AgdaFunction{𝓛ᵈℕ}\AgdaSpace{}\AgdaFunction{⟹ᵈᶜᵖᵒ⊥}\AgdaSpace{}\AgdaFunction{𝓛ᵈℕ}\AgdaSpace{}\AgdaFunction{⟹ᵈᶜᵖᵒ⊥}\AgdaSpace{}\AgdaFunction{𝓛ᵈℕ}}, and is named \AgdaFunction{⦅ifZero⦆}. We can not compose this directly with our function that evaluates our subterms of \AgdaInductiveConstructor{IfZero}, as the input of \AgdaFunction{⦅ifZero⦆} does not match the type of the output of \AgdaFunction{⦅ifZero⦆-arguments}. However, through the use of uncurry, we can construct a function from \AgdaFunction{⦅ifZero⦆} that takes the arguments as a product, as opposed to one at a time. We therefore construct \AgdaFunction{⦅ifZero⦆-uncurried} as follows:
\begin{code}
⦅ifZero⦆-uncurried' : DCPO⊥[ 𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ , 𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ ]
⦅ifZero⦆-uncurried' = uncurryᵈᶜᵖᵒ⊥ 𝓛ᵈℕ 𝓛ᵈℕ (𝓛ᵈℕ ⟹ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ⦅ifZero⦆

⦅ifZero⦆-uncurried : DCPO⊥[ (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ , 𝓛ᵈℕ ]
⦅ifZero⦆-uncurried = uncurryᵈᶜᵖᵒ⊥ (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) 𝓛ᵈℕ 𝓛ᵈℕ ⦅ifZero⦆-uncurried'
\end{code}
Now we can see why the associativity mattered when we were constructing a pair, as since applying uncurry once formed a pair of the outermost arguments, then again formed a pair where the first projection is the pair of the outermost arguments, and the second projection is the innermost argument of \AgdaFunction{⦅ifZero⦆}. We require the associativity of our argument construction to be the same. The reason is, for types $A$, $B$, and $C$, whilst $(A×B)×C$ is isomorphic to $A×(B×C)$, they are clearly not the same type, and to access an element of type $C$ in the first product type would require a different chain of projections to the second product type.

We now can produce our interpretation of \AgdaInductiveConstructor{IfZero} in our setting. We compose the function which evaluates each of the subterms of \AgdaIfZero{a}{b}{c} under a context \AgdaBound{Γ} with the uncurried \AgdaFunction{⦅ifZero⦆} construction. This provides us with a continuous function that takes a list of values to substitute for the variables, and produces the desired result of the \AgdaInductiveConstructor{IfZero} evaluation.
\begin{code}[hide]
module _ {a : ℕ} (Γ : Context a)
        where
\end{code}
\begin{code}
  ⦅ifZero⦆Γ : DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ] → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
            → DCPO⊥[ 【 Γ 】 , 𝓛ᵈℕ ]
  ⦅ifZero⦆Γ a b c = [ 【 Γ 】 , (𝓛ᵈℕ ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ) ×ᵈᶜᵖᵒ⊥ 𝓛ᵈℕ , 𝓛ᵈℕ ]
                    ⦅ifZero⦆-uncurried ∘ᵈᶜᵖᵒ⊥ (⦅ifZero⦆-arguments Γ a b c)
\end{code}

\subsubsection*{Interpreting application}
\begin{code}[hide]
module _ (𝓓 : DCPO {𝓤} {𝓤'})
         (𝓔 : DCPO {𝓣} {𝓣'})
       where
\end{code}
For an interpretation of \AgdaApp{M}{N}, we apply the interpretation of \AgdaBound{M} to the interpretation of \AgdaBound{N}. We begin by constructing a continuous function called \AgdaFunction{eval} which performs this application given a continuous function from a DCPO $𝓓$ to $𝓔$, and an element of the DCPO $𝓓$, corresponding to the evaluation map mentioned by Streicher \cite[Section~4]{domaintheoreticfoundations}.
\begin{AgdaAlign}
\begin{code}
  eval : DCPO[ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓 , 𝓔 ]
  eval = f , c
    where
      f : ⟨ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓 ⟩ → ⟨ 𝓔 ⟩
      f (g , d) = underlying-function 𝓓 𝓔 g d
\end{code}
\hide{
We first show that \AgdaFunction{f} is monotone, which is useful in our proof that \AgdaFunction{f} is continuous. We assume $(g₁ , d₁)$ and $(g₂ , d₂)$ as elements of the DCPO \AgdaBrackets{\AgdaBrackets{\FuncDcpo{𝓓}{𝓔}}\AgdaSpace{}\AgdaFunction{×ᵈᶜᵖᵒ}\AgdaSpace{}\AgdaBound{𝓓}}, and that $(g₁ , d₁)$ is less than $(g₂ , d₂)$. From this, we get that $g₁$ is less than $g₂$ and $d₁$ is less than $d₂$. We want to show that $f (g₁ , d₁)$ is less than $f (g₂ , d₂)$. Since continuous functions are monotone, and $g₁$ is a continuous function between the DCPOs $𝓓$ and $𝓔$, we use the monotonicity of $g₁$ to show that $f (g₁ , d₁)$ is less than $f (g₁ , d₂)$. We then show that $f (g₁ , d₂)$ is less than $f (g₂ , d₂)$. This follows simply from the definition of the pointwise order, and since the continuous function $g₁$ is less than $g₂$, it follows that $f (g₁ , d₂)$ is less than $f (g₂ , d₂)$. The transitivity of the order of the DCPO $𝓔$ concludes our proof. 
\begin{code}
      f-is-monotone : is-monotone ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓) 𝓔 f
      f-is-monotone (g₁ , d₁) (g₂ , d₂) (g₁⊑g₂ , d₁⊑d₂) =
                     f (g₁ , d₁) ⊑⟨ 𝓔 ⟩[ continuous-functions-are-monotone 𝓓 𝓔 g₁ d₁ d₂ d₁⊑d₂ ]
                     f (g₁ , d₂) ⊑⟨ 𝓔 ⟩[ g₁⊑g₂ d₂ ]
                     f (g₂ , d₂) ∎⟨ 𝓔 ⟩
\end{code}
}
We next provide a proof that \AgdaFunction{f} is continuous. Similarly to our uncurry proof, since our function input is a product, we can prove that \AgdaFunction{f} is continuous by showing it is continuous in each of its arguments. Since the proofs of \AgdaFunction{continuous₁} and \AgdaFunction{continuous₂} are relatively straightforward, we omit them for brevity.
\begin{code}
      c : is-continuous ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓) 𝓔 f
      c = continuous-in-arguments→continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) 𝓓 𝓔 f continuous₁ continuous₂
        where -- Proofs of continuity in arguments omitted.
\end{code}
\hide{
The proof that \AgdaFunction{f} is continuous in its first argument is short. For a fixed \AgdaBound{d}, we want to show that \AgdaFunction{f}\AgdaSpace{}\AgdaPair{\AgdaUpperBound{\AgdaBrackets{\FuncDcpo{𝓓}{𝓔}}}{δ}}{d} is the least upper bound of a directed family $λ i → \AgdaFunction{f} (α i , d)$, where \AgdaType{α}{\AgdaFun{I}{\AgdaExtractSet{\FuncDcpo{𝓓}{𝓔}}}}, and $δ$ is a proof that $α$ is directed. However, \AgdaFunction{f}\AgdaSpace{}\AgdaPair{\AgdaUpperBound{\AgdaBrackets{\FuncDcpo{𝓓}{𝓔}}}{δ}}{d} is the equal to the least upper bound of the pointwise family by definition, so our proof follows straight from the directed-completeness of the DCPO \AgdaBound{𝓔}, which states that there exists a least upper bound for every directed family in DCPO \AgdaBound{𝓔}, and that the pointwise family is a directed family in \AgdaBound{𝓔}.
\begin{code}
          continuous₁ : (d : ⟨ 𝓓 ⟩) → is-continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) 𝓔 (λ g → f (g , d))
          continuous₁ d I α δ = ∐-is-sup 𝓔 (pointwise-family-is-directed 𝓓 𝓔 α δ d)
\end{code}
We next consider how to show that \AgdaFunction{f} is continuous in its second argument. We want to show that for a fixed \AgdaBound{g}, any directed family $α : I → ⟨ 𝓓 ⟩$, where \AgdaBound{δ} is a proof that $α$ is directed, \AgdaFunction{f}\AgdaSpace{}\AgdaPair{g}{\AgdaUpperBound{𝓓}{δ}} is the least upper bound of the directed family $λ i → f (g , α i)$. We provide a proof \AgdaFunction{u} that it is first an upper bound, and a proof \AgdaFunction{l} that it is a least upper bound.
\begin{code}
          continuous₂ : (g : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟩) → is-continuous 𝓓 𝓔 (λ d → f (g , d))
          continuous₂ g I α δ = u , l
            where
\end{code}
The proof that $f (g , ∐ 𝓓 δ)$ is an upper bound follows trivially from the monotonicity of $f$. We want to show that for any $i$, $f (g , α i)$ is less than \AgdaFunction{f}\AgdaSpace{}\AgdaPair{g}{\AgdaUpperBound{𝓓}{δ}}. We can construct a proof that $g$ is less than $g$ by reflexivity of the order, and that $α i$ is less than $∐ 𝓓 δ$ by the definition of the least upper bound. From the definition of the component-wise ordering, it then follows that $(g , α i)$ is less than $(g , ∐ 𝓓 δ)$. From the monotonicity of $f$, it then follows that $f (g , α i)$ is less than \AgdaFunction{f}\AgdaSpace{}\AgdaPair{g}{\AgdaUpperBound{𝓓}{δ}}.
\begin{code}
              u : is-upperbound (underlying-order 𝓔) (f (g , ∐ 𝓓 δ)) (λ z → f (g , α z))
              u i = f-is-monotone (g , α i) (g , ∐ 𝓓 δ) ((reflexivity (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) g) , (∐-is-upperbound 𝓓 δ i))
\end{code}
We next want to show that for any other upper bound $u₁$ of $λ i. f (g , α i)$, that $f (g , ∐ 𝓓 δ)$ is less than $u₁$. Since $f (g , ∐ 𝓓 δ)$ is defined as \UnderlyingFunction{𝓓}{𝓔}{g}\AgdaBrackets{\AgdaSpace{}\AgdaUpperBound{𝓓}{δ}}, we use the continuity of $g$ to show that $f (g , ∐ 𝓓 δ)$ is equal to \AgdaUpperBound{𝓔}{\AgdaFunction{image-is-directed}\AgdaSpace{}\AgdaBound{𝓓}\AgdaSpace{}\AgdaBound{𝓔}\AgdaSpace{}\AgdaBound{g}\AgdaSpace{}\AgdaBound{δ}}, where \AgdaFunction{image-is-directed}\AgdaSpace{}\AgdaBound{𝓓}\AgdaSpace{}\AgdaBound{𝓔}\AgdaSpace{}\AgdaBound{g}\AgdaSpace{}\AgdaBound{δ} is a proof that the family $λ i. f (g , α i)$ is directed. We label this application of continuity $i$. We then show a proof that \AgdaUpperBound{𝓔}{\AgdaFunction{image-is-directed}\AgdaSpace{}\AgdaBound{𝓓}\AgdaSpace{}\AgdaBound{𝓔}\AgdaSpace{}\AgdaBound{g}\AgdaSpace{}\AgdaBound{δ}} is less than $u₁$, which follows by the definition of the least upper bound. We label this proof $ii$. Therefore, due to the equality we shown in $i$, we transport the property shown in $ii$, to show that \AgdaFunction{f}\AgdaSpace{}\AgdaPair{g}{\AgdaUpperBound{𝓓}{δ}} is less than $u₁$.
\begin{code}
              l : (u₁ : ⟨ 𝓔 ⟩) → ((i : I) → f (g , α i) ⊑⟨ 𝓔 ⟩ u₁) → f (g , ∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ u₁
              l u₁ p = transport (λ - → - ⊑⟨ 𝓔 ⟩ u₁) (i ⁻¹) ii
                where
                  i : f (g , ∐ 𝓓 δ) ≡ ∐ 𝓔 (image-is-directed 𝓓 𝓔 g δ)
                  i = continuous-function-∐-≡ 𝓓 𝓔 g δ
                  ii : (∐ 𝓔 (image-is-directed 𝓓 𝓔 g δ)) ⊑⟨ 𝓔 ⟩ u₁
                  ii = ∐-is-lowerbound-of-upperbounds 𝓔 (image-is-directed 𝓓 𝓔 g δ) u₁ p
\end{code}
}
We can then construct \AgdaFunction{eval⊥} for convenience, similar to as we have previously, to work on elements from \AgdaFunction{DCPO⊥} rather than \AgdaFunction{DCPO}.

With the above construction, we can now form our interpretation of application as the composition of our \AgdaFunction{to-×-DCPO⊥} construction which we use to evaluate two terms under a context simultaneously, and \AgdaFunction{eval⊥} which performs the application as we would expect.
\end{AgdaAlign}

\subsubsection*{Interpretation function of terms}

We begin with our interpretation function definition.
\begin{code}
⟦_⟧ₑ : {n : ℕ} {Γ : Context n} {σ : type} (t : PCF Γ σ) → DCPO⊥[ 【 Γ 】 , ⟦ σ ⟧ ]
\end{code}
We first consider the interpretation for the PCF term \AgdaZero{} under the context \AgdaBound{Γ}. This term has no free variables, and we always want it to correspond to the natural number \AgdaInductiveConstructor{zero} in \AgdaDatatype{ℕ}. So, we define a constant function where the output is always the total element \AgdaInductiveConstructor{zero} of the lifted set \AgdaFunction{𝓛}\AgdaSpace{}\AgdaDatatype{ℕ}. Since any constant function is continuous, then the function we have defined must be continuous.
\begin{code}
⟦ Zero {_} {Γ} ⟧ₑ = (λ _ → η zero) , const-functions-are-continuous ⟪ 【 Γ 】 ⟫ ⟪ ⟦ ι ⟧ ⟫ (η zero)
\end{code}
We next define the interpretation of \AgdaSucc{t}, under a context \AgdaBound{Γ}. Here we make use of \AgdaFunction{𝓛̇}, which is responsible for taking a function between two types, and producing a function between the lifting of the types. It maps elements as the original function would, just with the extra mapping of $⊥$ to $⊥$. The lifted function is also shown to be continuous. We compose this function with the interpretation of the term \AgdaBound{t}. We can view this first determining the value of \AgdaBound{t} under a context \AgdaBound{Γ}, and then taking the successor of the result.
\begin{code}
⟦ Succ {_} {Γ} t ⟧ₑ = [ 【 Γ 】 , ⟦ ι ⟧ , ⟦ ι ⟧ ]
                     (𝓛̇ succ , 𝓛̇-continuous ℕ-is-set ℕ-is-set succ) ∘ᵈᶜᵖᵒ⊥ ⟦ t ⟧ₑ 
\end{code}
The interpretation of \AgdaInductiveConstructor{Pred}\AgdaSpace{}\AgdaBound{t} under a context \AgdaBound{Γ} is then similar to that of \AgdaSucc{t}, except we use the function \AgdaFunction{pred} instead, which maps all natural numbers $n$ to $n-1$, apart from $0$ which maps to $0$.
\begin{code}
⟦ Pred {_} {Γ} t ⟧ₑ = [ 【 Γ 】 , ⟦ ι ⟧ , ⟦ ι ⟧ ]
                     (𝓛̇ pred , 𝓛̇-continuous ℕ-is-set ℕ-is-set pred) ∘ᵈᶜᵖᵒ⊥ ⟦ t ⟧ₑ
\end{code}
For \AgdaIfZero{t}{t₁}{t₂} under a context \AgdaBound{Γ}, we interpret this using the DCPO with $⊥$ we constructed previously. The order of the arguments is intentionally switched, as we define our arguments to \AgdaInductiveConstructor{IfZero} in the same order as Streicher \cite[Section~2]{domaintheoreticfoundations}, however we use the interpretation from Tom de Jong, who defines his in a slightly different order \cite{jong2019scott}.
\begin{code}
⟦ IfZero {_} {Γ} t t₁ t₂ ⟧ₑ = ⦅ifZero⦆Γ Γ ⟦ t₁ ⟧ₑ ⟦ t₂ ⟧ₑ  ⟦ t ⟧ₑ
\end{code}
Now we consider the interpretation of \AgdaLambda{t}. Since \AgdaLambda{t} has a type of \AgdaBound{σ}\AgdaSpace{}\AgdaInductiveConstructor{⇒}\AgdaSpace{}\AgdaBound{τ}, we need to produce a continuous function from \AgdaContextInterp{Γ} to the continuous function space \FuncDcpoBot{\AgdaTypeInterp{σ}}{\AgdaTypeInterp{τ}}. However, from the interpretation of \AgdaBound{t}, we have a continuous function from \AgdaContextInterp{Γ ’ σ} to \AgdaTypeInterp{τ}. We can therefore just apply the currying operation to \AgdaTermInterp{t}.
\begin{code}
⟦ ƛ {_} {Γ} {σ} {τ} t ⟧ₑ = curryᵈᶜᵖᵒ⊥ 【 Γ 】 ⟦ σ ⟧ ⟦ τ ⟧ ⟦ t ⟧ₑ 
\end{code}
As we previously explored, we represent the application of a term \AgdaBound{t} to a term \AgdaBound{t₁} as first evaluating both terms under a list of values to substitute for their free variables, and then performing the evaluation as specified by \AgdaFunction{eval⊥}.
\begin{code}
⟦ _·_ {_} {Γ} {σ} {τ} t t₁ ⟧ₑ = [ 【 Γ 】 , ( ⟦ σ ⇒ τ ⟧ ×ᵈᶜᵖᵒ⊥ ⟦ σ ⟧) , ⟦ τ ⟧ ]
                 (eval⊥ ⟦ σ ⟧ ⟦ τ ⟧) ∘ᵈᶜᵖᵒ⊥ (to-×-DCPO⊥ 【 Γ 】 ⟦ σ ⇒ τ ⟧ ⟦ σ ⟧ ⟦ t ⟧ₑ ⟦ t₁ ⟧ₑ) 
\end{code}
For a variable \AgdaVar{x} with type \AgdaBound{σ} under the context \AgdaBound{Γ}, we use our \AgdaFunction{var-extract} function we previously defined applied to \AgdaBound{x}. This provides us with a continuous function from the interpretation of the context \AgdaBound{Γ} to the interpretation of the type \AgdaBound{σ}.
\begin{code}
⟦ v x ⟧ₑ = var-extract x
\end{code}
When interpreting \AgdaFix{t}, we make use of Tom de Jong's interpretation of \AgdaInductiveConstructor{Fix} in his setting. The function \AgdaFunction{μ} provides us an interpretation of the fixed-point combinator for a type \AgdaBound{σ}. Therefore, this makes \AgdaFunction{μ}\AgdaSpace{}\AgdaTypeInterp{σ} a continuous function between the DCPOs \AgdaTypeInterp{\AgdaBound{σ}\AgdaSpace{}\AgdaInductiveConstructor{⇒}\AgdaSpace{}\AgdaBound{σ}} and \AgdaTypeInterp{σ}. Since we want to apply this fixed-point combinator to the interpretation of \AgdaBound{t}, we compose \AgdaFunction{μ}\AgdaSpace{}\AgdaTypeInterp{σ} with the interpretation of \AgdaBound{t}. This allows us to form a new continuous function which takes a list of values to substitute for the free variables in \AgdaBound{t}, and applies the fixed-point combinator to return a result of the type \AgdaTypeInterp{σ}, which is the fixed point of \AgdaTermInterp{t} after substituting the list of values for free variables.
\begin{code}
⟦ Fix {_} {Γ} {σ} t ⟧ₑ = [ 【 Γ 】 , ⟦ σ ⇒ σ ⟧ , ⟦ σ ⟧ ] (μ ⟦ σ ⟧) ∘ᵈᶜᵖᵒ⊥ ⟦ t ⟧ₑ
\end{code}


\end{document}
