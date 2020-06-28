\documentclass[main.tex]{subfiles}
\begin{document}
\begin{code}[hide]

open import UF-PropTrunc
open import SpartanMLTT

module DomainTheory 
        (𝓥 : Universe) -- where the index type for directed completeness lives
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
       where

open PropositionalTruncation pt
open import DcpoConstructions pt fe 
open import DcpoProducts-Continuity pt fe 𝓥
open DcpoConstructionsGeneral 𝓥 hiding (_hom-⊑_ ; _⟹ᵈᶜᵖᵒ_)
open import Dcpo pt fe 𝓥 hiding (is-least ; has-least ; DCPO⊥ ; is-directed ; dcpo-axioms ; is-continuous ; DCPO ; DCPO-structure ; DCPO[_,_] ; DCPO⊥[_,_] ) renaming (is-prop-valued to is-prop-valued' ;
                is-reflexive to is-reflexive' ;
                is-transitive to is-transitive' ;
                is-antisymmetric to is-antisymmetric' ;
                is-directed-complete to is-directed-complete' 
                )

\end{code}

\section{Domain Theory}
\label{domaintheory}
We have defined the semantics of PCF from an operational view. Next, we intend to look at the denotational view. To do this, we need to formalise the necessary domain theory which will allow us to construct the Scott model of PCF. We begin by providing some intuition for the use of domains, which are partially ordered sets with special structure.
\subsection{Intuition}
\label{intution}
When trying to define a mathematical model of a programming language, the first idea one might come up with is to interpret types as sets. For example, we may first try to interpret the PCF type \AgdaInductiveConstructor{ι} as the set of natural numbers. The issue which arises is what if we were to produce a program which did not terminate? We would not want to associate any natural number with this non-terminating program. We take Scott's approach of introducing the least element $⊥$ into each domain to represent programs which do not terminate.

Now we have an idea of what the elements of our representation for base types may be. We suggested the notion of a ``least'' element, but this only makes sense in the context of an ordering. So, we introduce a partial order which can be seen as the information ordering. Elements that are greater than other elements in this ordering can be seen as being ``more defined'' than the lesser elements. In classical mathematics, this could be defined as:
\begin{center}
$x \mathbin{⊑} y = (x \mathbin{≡} ⊥) \mathbin{∨} (x \mathbin{≡} y)$
\end{center}
This definition is useful for intuition, but is not useful in our constructive setting as discussed by Tom de Jong \cite{jong2019scott}. Later, we will reinterpret this definition using the lifting monad.

A domain for the PCF type \AgdaInductiveConstructor{ι} would contain the element $⊥$ representing the non-terminating programs of type \AgdaInductiveConstructor{ι}. $⊥$ would be less than every other element in the domain. The domain would also contain the natural numbers, which are all incomparable to each other as they are the total elements of the domain, but greater than the element $⊥$. We will call this domain $ℕ_{⊥}$, which can be seen in \cref{n-bot}.
\begin{figure}[h]
\centering
\vspace{-1em}
\[
   \begin{tikzcd}
     0 \arrow[drr, no head] & 1 \ar[dr, no head] & 2 \ar[d, no head]
     & 3 \ar[dl, no head] & \hspace{-1em}\cdots \ar[dll, no head] \\
     & & \bot
   \end{tikzcd}
\]
\vspace{-2em}
\caption{$ℕ_{⊥}$} 
\label{n-bot}
\end{figure}
\vspace{-1em}

After defining how we could represent programs of a base type, we next turn to modelling functions. Following from our intuition of definedness, we first consider which order we should associate with the function space. For two functions $f, g : A → B$, where A and B are domains, we define the pointwise order between these two functions as:
\begin{center}
$f \mathbin{⊑} g = ∀ (x : A) → f x \mathbin{⊑} g x$ 
\end{center}
Intuitively, this means that functions which are less defined are below functions which are more defined.

Let's consider the function space $ℕ_{⊥} → ℕ_{⊥}$. Under the pointwise order, it should be apparent that we will no longer have a flat domain like $ℕ_{⊥}$. Consider the identity function. Let's call $\operatorname{id}_{k}$ the identity function that's defined only up to the first $k$ natural numbers, and every other natural number input is undefined. From the pointwise ordering, $\operatorname{id}_{k} \mathbin{⊑} \operatorname{id}_{k+1}$. The identity function that's defined for all natural numbers we shall call $\operatorname{id}_{∞}$. We can then view this as a chain, from the function $⊥$ which maps all elements of $ℕ_{⊥}$ to $⊥_{ℕ}$, where $⊥_{ℕ}$ is the bottom element of the domain $ℕ_{⊥}$, up to $\operatorname{id}_{∞}$ at the very top of this chain. We can think of this as the higher up the chain we go, the more defined the function is, and the better it is as an approximation of the identity function, until we get to $\operatorname{id}_{∞}$. This function is the least upper bound of this chain.

One can also consider that we can approach $\operatorname{id}_{∞}$ from another direction, where we first build up the function in another order rather than $\operatorname{id}_{0}$, $\operatorname{id}_{1}$, etc. We can view all these chains as forming a directed set where $\operatorname{id}_{∞}$ is the least upper bound. From this, our intuition becomes that we can represent our types as directed-complete partial orders, which we define concretely later.

One note is that in our developments, we work with families instead of subsets. We do this because they were found to be more convenient in our constructive setting \cite{jong2019scott}.
\begin{definition}
An indexed family, or just family, is a function from an index set $I$ to a set $X$.
\end{definition}
We can view the image of the function as defining a subset of a set $X$. There is also the notion of a pointwise family, which we shall use later in our developments.
\begin{definition}
Given a family $α : I → (D → E)$, and an element $d : D$, we can form the pointwise family $λ i. α(i)(d)$.
\end{definition}

However, we cannot simply allow every possible function between two domains. Consider a function from $ℕ_{⊥}$ to $ℕ_{⊥}$ which maps $⊥$ to 1 and all natural numbers $n$ to $n+1$. There is a fundamental issue with such a construction in that we can use it to solve the halting problem. A similar issue is discussed by Knapp and Escardó \cite{escardoknapppartial}. Therefore, we endow our interpretation of functions with some extra constraints. 

The first constraint is that we consider monotone functions only. A way of viewing this constraint is that if we provide more information in the input, then we get more information in the output.
\begin{definition}
A function $f$ is monotone if $f x \mathbin{⊑} f y$ when $x \mathbin{⊑} y$.
\end{definition}
The problematic function we considered earlier is no longer a valid consideration, as we can consider that in the domain $ℕ_{⊥}$, for all $n$ it holds that $⊥ \mathbin{⊑} n$. The function is not monotonic, since $f ⊥ \mathbin{⋢} f n$.

The second constraint arises when we consider recursion. \AgdaFix{f} returns the least fixed point of the function $f$. In general, such a fixed point is not guaranteed to exist. To rectify this, we add the constraint that functions must be continuous, as it can be shown that continuous functions have fixed points \cite{Plotkin1983}.
\begin{definition}
A function $f : A → B$ is Scott-continuous if for any directed family $α : I → A$, $f(∐_{i : I}α(i)) \mathbin{≡} ∐_{i : I}f(α(i))$.
\end{definition}
Monotonicity follows from continuity, so we only need to consider functions which are continuous \cite[Section~4]{domaintheoreticfoundations}. It can also be shown that all computable functions are continuous \cite{weihrauch:95}, so we can be sure that all functions in PCF can be interpreted by this model.

\subsection{Defining DCPOs}

\begin{definition}
We define a poset $(X, ⊑)$ to be a set $X$ with a proposition-valued binary relation $⊑$, such that $⊑$ is:
\begin{itemize}
  \item Reflexive - $∀ (x : X) → x \mathbin{⊑} x$
  \item Antisymmetric - $∀ (x, y : X) → x \mathbin{⊑} y → y \mathbin{⊑} x → x \mathbin{≡} y$
  \item Transitive - $∀ (x, y, z : X) → x \mathbin{⊑} y → y \mathbin{⊑} z → x \mathbin{⊑} z$
\end{itemize}
\end{definition}
\begin{definition}
Given a poset $P$, an element $u$ of $P$ is called an upper bound of a family $α : I → P$ if $∀ (i : I) → α(i) \mathbin{⊑} u$.
\end{definition}

\begin{definition}
Given a poset $P$, an upper bound $b$ of a family $α : I → P$ is called a least upper bound, or a supremum, if for any other upper bound $u$ of $α$, it holds that $b \mathbin{⊑} u$.
\end{definition}

\begin{definition}
A family $α : I → P$ of a poset $P$ is called directed if the type $I$ is inhabited, and $∀ (i, j : I) → ∃ (k \mathbin{:} I) → α(i) \mathbin{⊑} α(k) \mathbin{∧} α(j) \mathbin{⊑} α(k)$.
\end{definition}

\begin{code}[hide]
module _ {𝓤 𝓣 : Universe}
         {D : 𝓤 ̇ }
         (_⊑_ : D → D → 𝓣 ̇ )
       where
\end{code}
We give the definition of \AgdaFunction{is-directed} in Agda, as it makes considerable use of propositional truncation.
\begin{code}
  is-directed : {I : 𝓥 ̇ } → (I → D) → 𝓥 ⊔ 𝓣 ̇
  is-directed {I} α = ∥ I ∥ × ((i j : I) → ∃ \(k : I) → (α i ⊑ α k) × (α j ⊑ α k))
\end{code}
The first projection of \AgdaFunction{is-directed} $α$ represents the proof that the index set $I$ is inhabited. It is the propositional truncation of the set $I$, as defined in \cref{propositions}. We use this as we only care about the fact that an element of $I$ exists - we do not care which, i.e. all elements are equal proofs of the inhabitance of $I$.

The second projection is our second property, that for all $i, j$, there exists a $k$ such that $α(i) \mathbin{⊑} α(k)$ and $α(j) \mathbin{⊑} α(k)$. In this definition, \AgdaFunction{∃} is the propositional truncation of the dependent pair, which is again explained in \cref{propositions}. As such, a proof of \AgdaFunction{is-directed} $α$ does not give a particular $k$ for each $i, j$, just the knowledge that one exists.

\begin{definition}
A poset $P$ is called directed-complete if every directed family in $P$ has a least upper bound in $P$.
\end{definition}

These definitions have been formalised in Agda by Tom de Jong, which we shall be using as a basis for further constructions. A DCPO can be defined in Agda, omitting the prior definitions, as:
\begin{AgdaAlign}
\begin{code} 
module _ {𝓤 𝓣 : Universe} {D : 𝓤 ̇ } (_⊑_ : D → D → 𝓣 ̇ ) where
\end{code}
\hide{
\begin{code}[hide]
  is-prop-valued = is-prop-valued' _⊑_
  is-reflexive = is-reflexive' _⊑_
  is-transitive = is-transitive' _⊑_
  is-antisymmetric = is-antisymmetric' _⊑_
  is-directed-complete = is-directed-complete' _⊑_
\end{code}}
\begin{code}
  dcpo-axioms : 𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓣 ̇    -- Prior definitions omitted for brevity.
  dcpo-axioms = is-set D × is-prop-valued × is-reflexive 
                × is-transitive × is-antisymmetric × is-directed-complete
\end{code} 
\begin{code}
module _ {𝓤 𝓣 : Universe} where
\end{code}
\hide{
\begin{code}[hide]
 private
\end{code}}
\begin{code}
  DCPO-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
  DCPO-structure D = Σ \(_⊑_ : D → D → 𝓣 ̇ ) → dcpo-axioms {𝓤} {𝓣} _⊑_ 
\end{code}
\begin{code}
  DCPO : (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
  DCPO = Σ \(D : 𝓤 ̇ ) → DCPO-structure D
\end{code}
\end{AgdaAlign}
We note the use of anonymous modules in Agda. Anonymous modules are useful when defining many statements which rely on the same assumptions. For example, \AgdaDatatype{is-reflexive}, \AgdaDatatype{is-antisymmetric}, and \AgdaDatatype{is-transitive} all rely on the assumption of a relation $⊑$ to define a property on. Therefore, we can make the assumption as a module parameter, saving us from having to add it as a parameter to each of the individual definitions explicitly. We can see this in action when we define \AgdaDatatype{DCPO-structure} in terms of the \AgdaDatatype{dcpo-axioms}. We do not explicitly define in the definition of \AgdaDatatype{dcpo-axioms} that we must pass the relation $⊑$, but it is required due to the parameter $\_⊑\_ : D → D → 𝓣$ \AgdaFunction{̇} of the anonymous module which \AgdaDatatype{dcpo-axioms} resides in. During this document, we will try to omit the anonymous module definitions where possible, as they do not add much to the understanding, but it is useful to see where some parameters to functions are coming from.

\subsection{DCPOs with \texorpdfstring{$⊥$}{Lg}}
From our intuition, we will be representing types as DCPOs with the least element $⊥$ to represent undefined. Therefore, we need a way to represent this, so we next construct a representation of DCPOs with a least element. We begin by defining what it means to be a least element.
\begin{code}[hide]
module _ {𝓤 𝓣 : Universe}
         {D : 𝓤 ̇ }
         (_⊑_ : D → D → 𝓣 ̇ )
       where
\end{code}
In Agda, we define that an element \AgdaBound{x} of \AgdaBound{D} is least if for any other element \AgdaBound{y} of \AgdaBound{D}, \AgdaBound{x}\AgdaSpace{}\AgdaBound{⊑}\AgdaSpace{}\AgdaBound{y}. We then use the dependent pair to construct \AgdaFunction{has-least}, which represents a proof that there is an element \AgdaBound{x} with the property that it is the least element of \AgdaBound{D}.
\begin{code}
  is-least : D → 𝓤 ⊔ 𝓣 ̇
  is-least x = ∀ (y : D) → x ⊑ y
\end{code}
\begin{code}
  has-least : 𝓤 ⊔ 𝓣 ̇
  has-least = Σ (\(x : D) → is-least x)
\end{code}
\begin{code}[hide]
module _ {𝓤 𝓣 : Universe}
    where
  DCPO-structure : 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
  DCPO-structure D = Σ \(_⊑_ : D → D → 𝓣 ̇ ) → dcpo-axioms {𝓤} {𝓣} _⊑_
 
  DCPO : (𝓤 ⁺) ⊔ (𝓥 ⁺) ⊔ (𝓣 ⁺) ̇
  DCPO = Σ \(D : 𝓤 ̇ ) → DCPO-structure D
\end{code}
Next, we define \AgdaFunction{DCPO⊥} to represent a DCPO with a least element.
\begin{code}
  DCPO⊥ : (𝓥 ⁺) ⊔ (𝓤 ⁺) ⊔ (𝓣 ⁺) ̇
  DCPO⊥ = Σ \(𝓓 : DCPO) → has-least (underlying-order 𝓓)
\end{code}

\subsection{DCPOs of continuous functions}
We can implement our definition of continuity in Agda as follows:
\begin{code}
is-continuous : (𝓓 : DCPO {𝓤} {𝓣}) (𝓔 : DCPO {𝓤'} {𝓣'}) 
                → (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
is-continuous 𝓓 𝓔 f = (I : 𝓥 ̇) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α)
                        → is-sup (underlying-order 𝓔) (f (∐ 𝓓 δ)) (f ∘ α)
\end{code}
We omit the definition of \AgdaFunction{is-sup}, but \AgdaFunction{is-sup}\AgdaSpace{}\AgdaBound{⊑}\AgdaSpace{}\AgdaBound{b}\AgdaSpace{}\AgdaBound{α} is a proof that \AgdaBound{b} is a least upper bound of the family \AgdaBound{α}, with respect to the order \AgdaBound{⊑}.

We then define continuous functions in Agda. We follow the definitions given in the previous section for continuity and monotonicity. Since monotonicity follows from continuity, we only need to ensure that each function is continuous. So, we can define our continuous functions as follows, where the term \AgdaFunction{⟨} $𝓓$ \AgdaFunction{⟩} refers to the underlying set of the DCPO $𝓓$:
\begin{code}[hide]
module _ {𝓤 𝓣 : Universe} where
\end{code}
\begin{code}
  DCPO[_,_] : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
  DCPO[ 𝓓 , 𝓔 ] = Σ (\(f : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) → is-continuous 𝓓 𝓔 f)
\end{code}
We then define the continuous functions for \AgdaFunction{DCPO⊥}. This is more for convenience than anything else, as \AgdaFunction{DCPO⊥} is just a \AgdaFunction{DCPO} with a proof that it does indeed have a bottom element. We use \AgdaExtractDCPO{𝓓} to extract the \AgdaFunction{DCPO} from \AgdaFunction{DCPO⊥}.
\begin{code}
  DCPO⊥[_,_] : DCPO⊥ {𝓤} {𝓣} → DCPO⊥ {𝓤'} {𝓣'} → (𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣' ̇
  DCPO⊥[ 𝓓 , 𝓔 ] = DCPO[ ⟪ 𝓓 ⟫ , ⟪ 𝓔 ⟫ ]
\end{code}
\begin{code}[hide]
module _ (𝓓 : DCPO {𝓤} {𝓣})
          (𝓔 : DCPO {𝓤'} {𝓣'})
           where

\end{code}
The pointwise order can be formalised as the type from elements \AgdaBound{d} of the underlying set of a DCPO \AgdaBound{𝓓} to a proof of \AgdaDcpoOrdering{\AgdaBound{f}\AgdaSpace{}\AgdaBound{d}}{𝓔}{\AgdaBound{g}\AgdaSpace{}\AgdaBound{d}}, where \AgdaFunction{⊑⟨}\AgdaSpace{}\AgdaBound{𝓔}\AgdaSpace{}\AgdaFunction{⟩} refers to the underlying order for the DCPO \AgdaBound{𝓔}.
\begin{code}
 _hom-⊑_ : DCPO[ 𝓓 , 𝓔 ] → DCPO[ 𝓓 , 𝓔 ] → 𝓤 ⊔ 𝓣' ̇
 (f , _) hom-⊑ (g , _) = ∀ d → f d ⊑⟨ 𝓔 ⟩ g d
\end{code}
Now we have defined the set of continuous functions between two DCPOs, we can next show this produces a DCPO when accompanied by the pointwise order. Since this is a previous development by Tom de Jong, we omit the proof of the DCPO axioms, but show the type of the definition and the underlying order used.
\begin{code}[hide]
module _ where
\end{code}
\begin{code}
 _⟹ᵈᶜᵖᵒ_ : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} 
           → DCPO {(𝓥 ⁺) ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓤' ⊔ 𝓣'} {𝓤 ⊔ 𝓣'}
 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 = DCPO[ 𝓓 , 𝓔 ] , _⊑_ , d -- Proof of DCPO axioms d omitted.
  where
   _⊑_ = 𝓓 hom-⊑ 𝓔
\end{code}
\begin{code}[hide]
   d : dcpo-axioms _⊑_
   d = s , p , r , t , a , c 
    where
     s : is-set DCPO[ 𝓓 , 𝓔 ]
     s = subsets-of-sets-are-sets (⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟩) (is-continuous 𝓓 𝓔)
         (Π-is-set fe (λ (x : ⟨ 𝓓 ⟩) →  sethood 𝓔))
         (λ {f} → being-continuous-is-a-prop 𝓓 𝓔 f)
     p : (f g : DCPO[ 𝓓 , 𝓔 ]) → is-prop (f ⊑ g)
     p (f , _) (g , _) = Π-is-prop fe
                         (λ (x : ⟨ 𝓓 ⟩) → prop-valuedness 𝓔 (f x) (g x))
     r : (f : DCPO[ 𝓓 , 𝓔 ]) → f ⊑ f
     r (f , _) x = reflexivity 𝓔 (f x)
     t : (f g h : DCPO[ 𝓓 , 𝓔 ]) → f ⊑ g → g ⊑ h → f ⊑ h
     t (f , _) (g , _) (h , _) l m x = transitivity 𝓔 (f x) (g x) (h x)
                                       (l x) (m x)
     a : (f g : DCPO[ 𝓓 , 𝓔 ]) → f ⊑ g → g ⊑ f → f ≡ g
     a f g l m =
      to-Σ-≡
       (dfunext fe
        (λ d → antisymmetry 𝓔
               ((underlying-function 𝓓 𝓔 f) d)
               ((underlying-function 𝓓 𝓔 g) d)
               (l d) (m d)) ,
       being-continuous-is-a-prop 𝓓 𝓔 (underlying-function 𝓓 𝓔 g) _
        (continuity-of-function 𝓓 𝓔 g))
     c : (I : _ ̇) (α : I → DCPO[ 𝓓 , 𝓔 ]) → is-directed _⊑_ α → has-sup _⊑_ α
     c I α δ = (continuous-functions-sup 𝓓 𝓔 α δ) , u , v
      where
       u : (i : I) → α i ⊑ continuous-functions-sup 𝓓 𝓔 α δ
       u i d = ∐-is-upperbound 𝓔 (pointwise-family-is-directed 𝓓 𝓔 α δ d) i
       v : (g : DCPO[ 𝓓 , 𝓔 ])
         → ((i : I) → α i ⊑ g)
         → continuous-functions-sup 𝓓 𝓔 α δ ⊑ g
       v (g , _) l d = ∐-is-lowerbound-of-upperbounds 𝓔
                       (pointwise-family-is-directed 𝓓 𝓔 α δ d)
                       (g d) (λ (i : I) → l i d)
 
\end{code} 

\subsection{The product of two DCPOs is a DCPO}
One construction which we have to formalise is the product between DCPOs. This is a new formalisation by us, as it was not needed in Tom de Jong's implementation since he considers a combinatorial implementation of PCF. We will, however, need the product when constructing our implementation of contexts, as we shall see when defining the Scott model of PCF.

The underlying set of the product between DCPOs will simply be the Cartesian product between the underlying sets. For the order, we shall use the component-wise ordering. Between DCPOs $𝓓$ and $𝓔$, this can be defined as:
\begin{center}
$(a , b) \mathbin{⊑_{𝓓\mathbin{×}𝓔}} (c , d) = (a \mathbin{⊑_{𝓓}} c) ∧ (b \mathbin{⊑_{𝓔}} d)$
\end{center}
In Agda, this can be represented as a type where its inhabitants are a pair of proofs, one which states \AgdaDcpoOrdering{a}{𝓓}{c}, and another that \AgdaDcpoOrdering{b}{𝓔}{d}. However, we need not define this order to depend on the definition of DCPOs. We can just define the function that says given a relation \AgdaBound{R₁} on the type \AgdaBound{D}, and a relation \AgdaBound{R₂} on the type \AgdaBound{E}, then two pairs from type \AgdaBound{D}\AgdaSpace{}\AgdaFunction{×}\AgdaSpace{}\AgdaBound{E} are related if the first projections are related by \AgdaBound{R₁}, and the second projections are related by \AgdaBound{R₂}.
\begin{code}[hide]
module _ {D : 𝓤 ̇} {E : 𝓤' ̇} where 
\end{code}
\begin{code}
  _⊑-×_ : (D → D → 𝓣 ̇) → (E → E → 𝓣' ̇) → (D × E → D × E → 𝓣 ⊔ 𝓣' ̇)
  _⊑-×_ R₁ R₂ (a , b) (c , d) = R₁ a c × R₂ b d
\end{code}

Before we show that, from two DCPOs, the Cartesian product between the two underlying sets with the component-wise ordering forms a DCPO, we need to show that composing the first projection with a directed family is also a directed family, and similarly for the second projection.

\begin{lemma}
If we have an order $⊑_{D}$ on a type $D$, an order $⊑_{E}$ on a type $E$, and a directed family $α : I → D × E$ under the component-wise ordering $⊑_{D × E}$, then we can form the directed family $pr₁ \mathbin{∘} α : I \mathbin{→} D$ under the order $⊑_{D}$.
\end{lemma}
\begin{proof}
\hide{
The first condition is that $I$ is inhabited. From our assumption that $α$ is a directed family, it must follow that $I$ is inhabited.

The second condition is that for any $i, j$ there exists $k$ such that $(pr₁ \mathbin{∘} α) i \mathbin{⊑_{D}} (pr₁ \mathbin{∘} α) k$ and $(pr₁ \mathbin{∘} α) j \mathbin{⊑_{D}} (pr₁ \mathbin{∘} α) k$. From our assumption that $α$ is directed, there must exist a $k$ such that for all $i, j$, $α(i) \mathbin{⊑_{D×E}} α(k)$ and $α(j) \mathbin{⊑_{D×E}} a(k)$. However, by definition, if $α(i) \mathbin{⊑_{D×E}} α(k)$, then it follows that $(pr₁ ∘ α) i \mathbin{⊑_{D}} (pr₁ ∘ α) k$, as the first projection of the proof that $α(i) \mathbin{⊑_{D×E}} α(k)$ is a proof that $(pr₁ ∘ α) i \mathbin{⊑_{D}} (pr₁ ∘ α) k$. Similarly for the index $j$. From this, we can see that clearly $k$ does exist, it is the same one we are given by our assumption that $α$ is directed.
In Agda, the proof is relatively similar. Let's step through the proof. }We first define what we are trying to prove. This is fairly similar to our definition on paper. The only difference is that we've used superscripts instead of subscripts to identify the orders. This is due to it not being possible to type $⊑_{d}$ in Agda. 
\begin{AgdaAlign}
\begin{code}
  pr₁∘α-is-directed : {I : 𝓥 ̇} → {α : I → D × E} → (⊑ᵈ : D → D → 𝓣 ̇) → (⊑ᵉ : E → E → 𝓣' ̇)
                      → is-directed (⊑ᵈ ⊑-× ⊑ᵉ) α → is-directed ⊑ᵈ (pr₁ ∘ α)
\end{code}
Next, we give our proof of \AgdaFunction{pr₁∘α-is-directed}. We use underscores to avoid giving names to the parameters we do not use in the body of our proof. \AgdaBound{δ} refers to the proof that a family \AgdaBound{α} is directed. Since we are trying to prove that \AgdaComp{\AgdaField{pr₁}}{α} is directed, we provide a pair as the result of the function. The first component is trivial - it is a proof that type $I$ is inhabited. This is given to us by the fact that \AgdaBound{α} is directed. More specifically, in our definition it is the first projection of \AgdaBound{δ}, but to make our proof more readable, we use a function \AgdaFunction{is-directed-gives-inhabited} to extract this fact. The proof of our second property is more involved, so we prove it under a \AgdaKeyword{where} clause so our proof is easier to read.
\begin{code}
  pr₁∘α-is-directed {_} {_} {I} {α} _⊑ᵈ_ _⊑ᵉ_ δ
                        = is-directed-gives-inhabited (_⊑ᵈ_ ⊑-× _⊑ᵉ_) α δ , o
    where
\end{code}
From our definition of directedness in Agda, \AgdaBound{δ} does not actually provide us with a $k$ for a given $i, j$ such that $α(i) \mathbin{⊑_{D×E}} α(k)$ and $α(j) \mathbin{⊑_{D×E}} α(k)$, just with the knowledge of its existence. However, we are able to use \AgdaFunction{∥∥-functor} to reason about this hypothetical $k$, and conclude that is is the same $k$ such that $(pr₁ ∘ α) i \mathbin{⊑_{D}} (pr₁ ∘ α) k$ and $(pr₁ ∘ α) j \mathbin{⊑_{D}} (pr₁ ∘ α) k$, as we can extract these proofs from our assumption that $α$ is directed.
\begin{code}
      o : (i j : I) → ∃ (λ k → ((pr₁ ∘ α) i) ⊑ᵈ ((pr₁ ∘ α) k) × ((pr₁ ∘ α) j) ⊑ᵈ ((pr₁ ∘ α) k))
      o i j = ∥∥-functor f (is-directed-order (_⊑ᵈ_ ⊑-× _⊑ᵉ_) α δ i j)
        where
          f : Σ (λ k → (_⊑ᵈ_ ⊑-× _⊑ᵉ_) (α i) (α k) × (_⊑ᵈ_ ⊑-× _⊑ᵉ_) (α j) (α k)) 
              → Σ (λ v → Σ (λ v₁ → pr₁ (α j) ⊑ᵈ pr₁ (α v)))
          f (k , (i₁⊑k₁ , i₂⊑k₂) , (j₁⊑k₁ , j₂⊑k₂)) = k , i₁⊑k₁ , j₁⊑k₁
\end{code}
\end{AgdaAlign}\vspace{-3.5em}\[\tag*{\qedhere}\]
\qedhere
\end{proof}

\begin{lemma}
If we have an order $⊑_{D}$ on a type $D$, an order $⊑_{E}$ on a type $E$, and a directed family $α : I → D × E$ under the component-wise ordering $⊑_{D × E}$, then we can form the directed family $pr₂ \mathbin{∘} α : I \mathbin{→} E$ under the order $⊑_{E}$.
\end{lemma}
\begin{proof}
This proof follows the same process as the previous, apart from we take the second projection of the proofs that $α(i) \mathbin{⊑_{D×E}} α(k)$ and $α(j) \mathbin{⊑_{D×E}} α(k)$.
\end{proof}
\begin{code}[hide]
  pr₂∘α-is-directed : {I : 𝓥 ̇} → {α : I → D × E} → (order₁ : D → D → 𝓣 ̇) → (order₂ : E → E → 𝓣' ̇)
                      → is-directed (order₁ ⊑-× order₂) α
                      → is-directed order₂ (pr₂ ∘ α)
  pr₂∘α-is-directed {_} {_} {I} {α} order₁ order₂ δ = is-directed-gives-inhabited (order₁ ⊑-× order₂) α δ , o
    where
      o : (i j : I) → ∃ (λ k → order₂ ((pr₂ ∘ α) i) ((pr₂ ∘ α) k) × order₂ ((pr₂ ∘ α) j) ((pr₂ ∘ α) k))
      o i j = ∥∥-functor (λ x → (pr₁ x) , (pr₂ (pr₁ (pr₂ x)) , pr₂ (pr₂ (pr₂ x)))) (is-directed-order (order₁ ⊑-× order₂) α δ i j)
\end{code}

Now we construct the product for DCPOs.
\begin{proposition}
Given a DCPO $𝓓$ with the underlying set $D$ and order $⊑_{D}$, and a DCPO $𝓔$ with the underlying set $E$ and order $⊑_{E}$, the Cartesian product of the underlying sets with the component-wise ordering forms a DCPO $𝓓 ×^{DCPO} 𝓔$.
\end{proposition}
\begin{proof}
\hide{
The facts that the Cartesian product of the underlying sets is a set, that the order is a proposition, reflexive, antisymmetric, and transitive all follow trivially from our assumptions that the DCPO axioms hold for $𝓓$ and $𝓔$.

We next are interested in showing that a least upper bound exists for each directed family. We can show that for each directed family, its least upper bound is calculated component-wise. We assume a directed family $α : I → D × E$. 

First, we show the component-wise least upper bound is indeed an upper bound of $α$, i.e. $∀ (i : I) → α(i) \mathbin{⊑_{D×E}} (∐_{j : I} pr₁(α(j)) , ∐_{k : I} pr₂(α(k)))$. By the definition of the component-wise ordering, we therefore need to show, for a given $i$, that $pr₁(α(i)) \mathbin{⊑_{D}} ∐_{j : I} pr₁(α(j))$, and that $pr₂(α(i)) \mathbin{⊑_{E}} ∐_{k : I} pr₂(α(k))$. This follows trivially from the definition of the least upper bound.

We next show that for any given upper bound $u$ of $α$, we have $(∐_{j : I} pr₁(α(j)) , ∐_{k : I} pr₂(α(k))) \mathbin{⊑_{D×E}} u$. Again, by the definition of the component-wise ordering, we need to show that $∐_{j : I} pr₁(α(j)) \mathbin{⊑_{D}} pr₁(u)$, and that $∐_{k : I} pr₂(α(k)) \mathbin{⊑_{E}} pr₂(u)$. It follows that if $u$ is an upper bound of $α$, then $pr₁(u)$ is an upper bound of $pr₁ ∘ α$ and $pr₂(u)$ is an upper bound of $pr₂ ∘ α$. The two statements we are interested in are now true by the definition of the least upper bound.

Now we consider how we can show this in Agda.} 
We begin our proof by stating that our new DCPO will have an underlying set of the Cartesian product between the underlying sets of the DCPOs $𝓓$ and $𝓔$. We also say that the order of this new DCPO is the component-wise order, which we construct from the underlying orders of $𝓓$ and $𝓔$, using \AgdaFunction{⊑-×}. We give this order an alias of \AgdaFunction{⊑-D×E}, which we use as an infix operator.
\begin{AgdaAlign} 
\begin{code}
_×ᵈᶜᵖᵒ_ : DCPO {𝓤} {𝓣} → DCPO {𝓤'} {𝓣'} → DCPO {𝓤 ⊔ 𝓤'} {𝓣 ⊔ 𝓣'}
𝓓 ×ᵈᶜᵖᵒ 𝓔 = (⟨ 𝓓 ⟩ × ⟨ 𝓔 ⟩) , _⊑-D×E_ , axioms
  where
    _⊑-D×E_ = (underlying-order 𝓓) ⊑-× (underlying-order 𝓔)
    axioms : dcpo-axioms _⊑-D×E_
    axioms = s , p , r , t , a , c -- Proofs s, p, r, t, a omitted.
      where
\end{code}
We next move into the proofs of the axioms. Directed-completeness requires more thought than the others which are more trivial, so we only show the proof \AgdaFunction{c}.
We first make use of our proofs that if \AgdaBound{α} is a directed family, then the projection maps composed with \AgdaBound{α} also form a directed family. We use these proofs to construct our least upper bound component wise, as we now have access to two least upper bounds by our assumption that both $𝓓$ and $𝓔$ are directed-complete. We then provide a proof \AgdaFunction{is-lub}, which is a proof that our constructed least upper bound is indeed a least upper bound of the directed family \AgdaBound{α}.
\begin{code}
        c : is-directed-complete _⊑-D×E_
        c I α δ = (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) , is-lub
          where
            pr₁∘α-is-dir : is-Directed 𝓓 (pr₁ ∘ α)
            pr₁∘α-is-dir = pr₁∘α-is-directed (underlying-order 𝓓) (underlying-order 𝓔) δ
            pr₂∘α-is-dir : is-Directed 𝓔 (pr₂ ∘ α)
            pr₂∘α-is-dir = pr₂∘α-is-directed (underlying-order 𝓓) (underlying-order 𝓔) δ
\end{code}
We provide a proof for each of the conditions that an element requires to be a least upper bound. The first is that it's an upper bound, and the second that it's the least of all upper bounds.
\begin{code}
            is-lub : is-sup _⊑-D×E_ (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) α
            is-lub = u , v
              where
\end{code}
We first consider showing that our constructed least upper bound is indeed an upper bound. This requires constructing a proof that for every \AgdaType{i}{I}, \AgdaDcpoOrdering{\AgdaField{pr₁}\AgdaSpace{}\AgdaBrackets{\AgdaBound{α}\AgdaSpace{}\AgdaBound{i}}}{𝓓}{\AgdaUpperBound{𝓓}{\AgdaFunction{pr₁∘α-is-directed}}}, and also \AgdaDcpoOrdering{\AgdaField{pr₂}\AgdaSpace{}\AgdaBrackets{\AgdaBound{α}\AgdaSpace{}\AgdaBound{i}}}{𝓔}{\AgdaUpperBound{𝓔}{\AgdaFunction{pr₂∘α-is-directed}}}. This is trivial - following from our assumption that $𝓓$ and $𝓔$ are directed-complete, we can construct both of these proofs.
\begin{code}
                u : is-upperbound _⊑-D×E_ (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) α
                u i = (∐-is-upperbound 𝓓 pr₁∘α-is-dir i) , (∐-is-upperbound 𝓔 pr₂∘α-is-dir i)
\end{code}
We next show that it is also less than any other upper bounds of \AgdaBound{α} under the component-wise ordering. For this, we assume an upper bound \AgdaBound{u}, and the property that this \AgdaBound{u} is an upper bound of the directed family \AgdaBound{α}. We provide a pair of proofs, the first is that \AgdaFunction{∐}\AgdaSpace{}\AgdaBound{𝓓}\AgdaSpace{}\AgdaFunction{pr₁∘α-is-dir} is less than \AgdaField{pr₁}\AgdaSpace{}\AgdaBound{u}, and the second that \AgdaFunction{∐}\AgdaSpace{}\AgdaBound{𝓔}\AgdaSpace{}\AgdaFunction{pr₂∘α-is-dir} is less than \AgdaField{pr₂}\AgdaSpace{}\AgdaBound{u}.
\begin{code}
                v : (u : ⟨ 𝓓 ⟩ × ⟨ 𝓔 ⟩) → is-upperbound _⊑-D×E_ u α
                                 → (∐ 𝓓 pr₁∘α-is-dir , ∐ 𝓔 pr₂∘α-is-dir) ⊑-D×E u
                v u u-is-upperbound = lub-in-pr₁ , lub-in-pr₂
                  where
\end{code}
From the definition of least upper bound, we have that \AgdaFunction{∐} \AgdaBound{𝓓} \AgdaFunction{pr₁∘α-is-dir} is less than all upper bounds of \AgdaComp{\AgdaField{pr₁}}{α}. We can show that \AgdaField{pr₁}\AgdaSpace{}\AgdaBound{u} is an upper bound of \AgdaComp{\AgdaField{pr₁}}{α} as it follows simply from the definition of the component-wise ordering that if \AgdaBound{α}\AgdaSpace{}\AgdaBound{i}\AgdaSpace{}\AgdaFunction{⊑-D×E}\AgdaSpace{}\AgdaBound{u}, then \AgdaField{pr₁}\AgdaSpace{}\AgdaBrackets{\AgdaBound{α}\AgdaSpace{}\AgdaBound{i}} \AgdaFunction{⊑⟨} \AgdaBound{𝓓} \AgdaFunction{⟩} \AgdaField{pr₁} \AgdaBound{u}. Similarly for the second projection. 
\begin{code}
                    lub-in-pr₁ = ∐-is-lowerbound-of-upperbounds 𝓓 pr₁∘α-is-dir (pr₁ u) p
                      where
                        p : is-upperbound (underlying-order 𝓓) (pr₁ u) (pr₁ ∘ α)
                        p i = pr₁ (u-is-upperbound i)
                    lub-in-pr₂ = ∐-is-lowerbound-of-upperbounds 𝓔 pr₂∘α-is-dir (pr₂ u) p
                      where
                        p : is-upperbound (underlying-order 𝓔) (pr₂ u) (pr₂ ∘ α)
                        p i = pr₂ (u-is-upperbound i)
\end{code}
\hide{
\begin{code}[hide]
        s : is-set (⟨ 𝓓 ⟩ × ⟨ 𝓔 ⟩)
        s = ×-is-set (sethood 𝓓) (sethood 𝓔)
        p : is-prop-valued _⊑-D×E_
        p (d₁ , e₁) (d₂ , e₂) (d-⊑₁ , e-⊑₁) (d-⊑₂ , e-⊑₂) = to-×-≡ (prop-valuedness 𝓓 d₁ d₂ d-⊑₁ d-⊑₂)
                                                                    (prop-valuedness 𝓔 e₁ e₂ e-⊑₁ e-⊑₂)
        r : is-reflexive _⊑-D×E_
        r (d , e) = (reflexivity 𝓓 d) , (reflexivity 𝓔 e)
        t : is-transitive _⊑-D×E_
        t (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) (x₁⊑y₁ , x₂⊑y₂) (y₁⊑z₁ , y₂⊑z₂) = e₁ , e₂
          where
            e₁ : x₁ ⊑⟨ 𝓓 ⟩ z₁
            e₁ = x₁ ⊑⟨ 𝓓 ⟩[ x₁⊑y₁ ] y₁ ⊑⟨ 𝓓 ⟩[ y₁⊑z₁ ] z₁ ∎⟨ 𝓓 ⟩
            e₂ : x₂ ⊑⟨ 𝓔 ⟩ z₂
            e₂ = x₂ ⊑⟨ 𝓔 ⟩[ x₂⊑y₂ ] y₂ ⊑⟨ 𝓔 ⟩[ y₂⊑z₂ ] z₂ ∎⟨ 𝓔 ⟩
        a : is-antisymmetric _⊑-D×E_
        a (a , b) (c , d) (a-⊑-c , b-⊑-d) (c-⊑-a , d-⊑-b) = to-×-≡ (antisymmetry 𝓓 a c a-⊑-c c-⊑-a)
                                                                    (antisymmetry 𝓔 b d b-⊑-d d-⊑-b)
\end{code}
}
\end{AgdaAlign}\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}
We then show that given two DCPOs with least elements, the product between these DCPOs also has a least element.
\begin{AgdaAlign}
\begin{code}
_×ᵈᶜᵖᵒ⊥_ : DCPO⊥ {𝓤} {𝓣} → DCPO⊥ {𝓤'} {𝓣'} → DCPO⊥ {𝓤 ⊔ 𝓤'} {𝓣 ⊔ 𝓣'}
𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔 = (⟪ 𝓓 ⟫ ×ᵈᶜᵖᵒ ⟪ 𝓔 ⟫) , least , p
  where
\end{code}
The least element is a pair, where the first component is the least element from \AgdaBound{𝓓}, and the second component is the least element from \AgdaBound{𝓔}. The property of this construction being the least element follows trivially from the fact that each component is the least element of their respective DCPOs.
\begin{code}
    least : ⟨ ⟪ 𝓓 ⟫ ×ᵈᶜᵖᵒ ⟪ 𝓔 ⟫ ⟩
    least = the-least 𝓓 , the-least 𝓔
    p : is-least (underlying-order (⟪ 𝓓 ⟫ ×ᵈᶜᵖᵒ ⟪ 𝓔 ⟫)) least
    p (d , e) = (least-property 𝓓 d) , (least-property 𝓔 e)
\end{code}
\end{AgdaAlign}

\subsection{Curry and uncurry}
We can represent a function which takes multiple arguments as a function where its input is a pair consisting of these arguments. For example, a function which takes two arguments might have the general type $f : A × B → C$. However, we can construct a function $g : A → (B → C)$ such that for any pair $(a , b)$, $f (a , b) \mathbin{≡} g(a)(b)$. We can also show that given $g$, we can construct the function $f$. From this, we have shown that the function space $A × B → C$ is isomorphic to that of $A → (B → C)$, i.e. that they are in one-to-one correspondence. We have names for these particular operations. Constructing $A → (B → C)$ from $A × B → C$ is called currying, and from $A → (B → C)$ to $A × B → C$ is called uncurrying. We show that the currying of a continuous function produces another continuous function, and that uncurrying also produces a continuous function.

We make use of the following lemmas, which we have proved in Agda, but omitted due to length.
\begin{lemma}
Given a continuous function \AgdaType{f}{\AgdaConFun{\AgdaProductDCPO{𝓓}{𝓔}}{𝓕}}, then it is continuous in both of its arguments.
\end{lemma}
\begin{lemma}\label{continuity-in-arguments-implies-continuous}
Given a function \AgdaType{f}{\AgdaFun{\AgdaExtractSet{\AgdaProductDCPO{𝓓}{𝓔}}}{\AgdaExtractSet{𝓕}}}, if it is continuous in both arguments then \AgdaBound{f} is continuous.
\end{lemma}

\begin{theorem}[Curry]
From a continuous function of the form \AgdaType{f}{\AgdaFun{\AgdaExtractSet{\AgdaProductDCPO{𝓓}{𝓔}}}{\AgdaExtractSet{𝓕}}}, we can construct a continuous function of the form \AgdaType{g}{\AgdaFun{\AgdaExtractSet{𝓓}}{\AgdaExtractSet{\FuncDcpo{𝓔}{𝓕}}}}, such that for all pairs \AgdaPair{d}{e}, \AgdaEq{\AgdaBound{f}\AgdaSpace{}\AgdaPair{d}{e}}{\AgdaBound{g}\AgdaSpace{}\AgdaBound{d}\AgdaSpace{}\AgdaBound{e}}. 
\end{theorem}
\begin{proof}
\hide{
We first define how to construct $g$. We want to construct this as a mapping from an element of $𝓓$ to a continuous function $𝓔 → 𝓕$. So, we can construct g as the function $λ d. λ e. f (d , e)$.

Since it is a requirement that the function $𝓔 → 𝓕$ is continuous, this is equivalent to saying $f$ is continuous in its second argument. Since a function being continuous implies it is continuous in each of its arguments, then it must follow that $𝓔 → 𝓕$ is continuous.

We are next interested in showing that the function from $𝓓$ to the continuous function $𝓔 → 𝓕$ is continuous. We assume a directed family $α : I → 𝓓$. We want to show that $∀ (i : I) → g(α(i)) \mathbin{⊑_{𝓔→𝓕}} g(∐_{k : I}α(k))$. From the definition of the pointwise ordering which we use for the function space, this is the same as $∀ (i : I) → g(α(i))(e) \mathbin{⊑_{𝓕}} g(∐_{k : I}α(k))(e)$. However, since $f$ is continuous in its first argument, it follows that $∐_{k : I} g(α(k))(e) \mathbin{≡} g(∐_{k : I}α(k))(e)$. Therefore, by definition of the least upper bound, the property we require holds.

Next we want to show that for all continuous functions $u$ from $𝓔$ to $𝓕$, if $u$ is an upper bound of $g ∘ α$, then $g(∐_{k : I}α(k))$ is less than $u$. By the pointwise ordering, this means we need to show for all $e : 𝓔$, $u(e)$ is less than $g(∐_{k : I}α(k))(e)$. Since $f$ is continuous in its first argument, we again have $∐_{k : I} g(α(k))(e) \mathbin{≡} g(∐_{k : I}α(k))(e)$. By the definition of the least upper bound, it follows that $u(e) \mathbin{⊑_{𝓕}} ∐_{k : I} g(α(k))(e)$ and therefore $u(e) \mathbin{⊑_{𝓕}} g(∐_{k : I}α(k))(e)$ as desired.
}
We define \AgdaFunction{curryᵈᶜᵖᵒ} as follows. We pattern match on the continuous function definition, and give the name \AgdaBound{f} to the underlying function, and \AgdaBound{f-is-continuous} to the proof that \AgdaBound{f} is continuous. We construct \AgdaFunction{g} as a function that, given \AgdaType{d}{\AgdaExtractSet{𝓓}}, produces a continuous function from \AgdaBound{𝓔} to \AgdaBound{𝓕}. Although, this is just the same as our definition of \AgdaFunction{continuous→continuous-in-pr₂} where we do not provide a particular \AgdaType{d}{\AgdaExtractSet{𝓓}} to fix. We also provide a proof that \AgdaFunction{g} is continuous.
\begin{code}[hide]
module _ (𝓓 : DCPO {𝓤} {𝓤'})
         (𝓔 : DCPO {𝓣} {𝓣'})
         (𝓕 : DCPO {𝓦} {𝓦'})
       where
\end{code}
\begin{AgdaAlign} 
\begin{code}
  curryᵈᶜᵖᵒ : DCPO[ (𝓓 ×ᵈᶜᵖᵒ 𝓔) , 𝓕 ] → DCPO[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ]
  curryᵈᶜᵖᵒ (f , f-is-continuous) = g , g-is-continuous
    where
      g : ⟨ 𝓓 ⟩ → ⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩
      g = continuous→continuous-in-pr₂ 𝓓 𝓔 𝓕 (f , f-is-continuous) 
\end{code}
We now begin to construct our proof that \AgdaFunction{g} is continuous. We further break this proof down into a proof \AgdaFunction{u} that \AgdaFunction{g}\AgdaSpace{}\AgdaBrackets{\AgdaUpperBound{𝓓}{δ}} is the upper bound of \AgdaComp{\AgdaFunction{g}}{α}, and a proof \AgdaFunction{v} that for any other \AgdaBound{u₁} which is an upper bound of \AgdaComp{\AgdaFunction{g}}{α}, then \AgdaDcpoOrdering{\AgdaFunction{g}\AgdaSpace{}\AgdaBrackets{\AgdaUpperBound{𝓓}{δ}}}{\FuncDcpo{𝓔}{𝓕}}{u₁}. 
\begin{code} 
      g-is-continuous : (I : 𝓥 ̇) (α : I → ⟨ 𝓓 ⟩) (δ : is-Directed 𝓓 α) →
                          is-sup (underlying-order (𝓔 ⟹ᵈᶜᵖᵒ 𝓕)) (g (∐ 𝓓 δ)) (g ∘ α)
      g-is-continuous I α δ = u , v
        where
\end{code}
We want to show that 
\AgdaDcpoOrdering{\AgdaBrackets{\AgdaComp{\AgdaFunction{g}}{α}}\AgdaSpace{}\AgdaBound{i}}{\FuncDcpo{𝓔}{𝓕}}{\AgdaFunction{g}\AgdaSpace{}\AgdaBrackets{\AgdaUpperBound{𝓓}{δ}}} for all \AgdaBound{i}. 
By the definition of the pointwise order and the definition of \AgdaBound{g}, this simplifies to showing 
\AgdaBound{f} (\AgdaBound{α} \AgdaBound{i} , \AgdaBound{e}) \AgdaFunction{⊑⟨} \AgdaBound{𝓕} \AgdaFunction{⟩} \AgdaBound{f} (\AgdaFunction{∐} \AgdaBound{𝓓} \AgdaBound{δ} , \AgdaBound{e}) for all \AgdaBound{e}. Our proof begins by constructing a continuous function where the second argument is fixed to be \AgdaBound{e}. We call this continuous function \AgdaFunction{f-fixed-e}. From the continuity of this function, it follows that the least upper bound is 
\AgdaBound{f}\AgdaSpace{}\AgdaSymbol{(}\AgdaUpperBound{𝓓}{δ}\AgdaSpace{}\AgdaSymbol{,}\AgdaSpace{}\AgdaBound{e}\AgdaSymbol{)}, and proof of this we give the name \AgdaFunction{p}. We can then show
\AgdaDcpoOrdering{\AgdaBound{f}\AgdaSpace{}\AgdaSymbol{(}\AgdaBound{α}\AgdaSpace{}\AgdaBound{i}\AgdaSpace{}\AgdaSymbol{,}\AgdaSpace{}\AgdaBound{e}\AgdaSymbol{)}}{𝓕}{\AgdaBound{f}\AgdaSpace{}\AgdaSymbol{(}\AgdaUpperBound{𝓓}{δ}\AgdaSpace{}\AgdaSymbol{,}\AgdaSpace{}\AgdaBound{e}\AgdaSymbol{)}} 
by applying the definition of the least upper bound via \AgdaFunction{is-sup-gives-upperbound}.
\begin{code}
          u : (i : I) → underlying-order (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) ((g ∘ α) i) (g (∐ 𝓓 δ))
          u i e = is-sup-gives-is-upperbound (underlying-order 𝓕) p i 
            where
              f-fixed-e : DCPO[ 𝓓 , 𝓕 ]
              f-fixed-e = continuous→continuous-in-pr₁ 𝓓 𝓔 𝓕 (f , f-is-continuous) e
              p : is-sup (underlying-order 𝓕) (f (∐ 𝓓 δ , e)) (λ i → f (α i , e))
              p = continuity-of-function 𝓓 𝓕 f-fixed-e I α δ
\end{code}
The proof that \AgdaFunction{g}\AgdaSpace{}\AgdaSymbol{(}\AgdaUpperBound{𝓓}{δ}\AgdaSymbol{)} is the least of all upper bounds of \AgdaFunction{g}\AgdaSpace{}\AgdaFunction{∘}\AgdaSpace{}\AgdaBound{α} requires that we show for any \AgdaBound{u₁}, if \AgdaBound{u₁} is an upper bound of \AgdaFunction{g}\AgdaSpace{}\AgdaFunction{∘}\AgdaSpace{}\AgdaBound{α}, then \AgdaDcpoOrdering{\AgdaFunction{g}\AgdaSpace{}\AgdaSymbol{(}\AgdaUpperBound{𝓓}{δ}\AgdaSymbol{)}}{\FuncDcpo{𝓔}{𝓕}}{u₁}. This simplifies to showing \AgdaDcpoOrdering{\AgdaBound{f}\AgdaSpace{}\AgdaSymbol{(}\AgdaUpperBound{𝓓}{δ}\AgdaSpace{}\AgdaSymbol{,}\AgdaSpace{}\AgdaBound{e}\AgdaSymbol{)}}{𝓕}{\UnderlyingFunction{𝓔}{𝓕}{u₁}\AgdaSpace{}\AgdaBound{e}} for all \AgdaBound{e}. Similar to the proof that \AgdaFunction{g}\AgdaSpace{}\AgdaSymbol{(}\AgdaUpperBound{𝓓}{δ}\AgdaSymbol{)} is an upper bound, we first construct \AgdaFunction{f-fixed-e}, and then prove the property \AgdaFunction{p} that \AgdaBound{f}\AgdaSpace{}\AgdaSymbol{(}\AgdaUpperBound{𝓓}{δ}\AgdaSpace{}\AgdaSymbol{,}\AgdaSpace{}\AgdaBound{e}\AgdaSymbol{)} is the least upper bound in the same way. We then apply the definition of least upper bound to show that \AgdaDcpoOrdering{\AgdaBound{f}\AgdaSpace{}\AgdaSymbol{(}\AgdaUpperBound{𝓓}{δ}\AgdaSpace{}\AgdaSymbol{,}\AgdaSpace{}\AgdaBound{e}\AgdaSymbol{)}}{𝓕}{\UnderlyingFunction{𝓔}{𝓕}{u₁}\AgdaSpace{}\AgdaBound{e}} as desired.
\begin{code}
          v : (u₁ : ⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩) → ((i : I) → g (α i) ⊑⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩ u₁) →
                g (∐ 𝓓 δ) ⊑⟨ 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ⟩ u₁
          v u₁ upper e = is-sup-gives-is-lowerbound-of-upperbounds (underlying-order 𝓕) p
                                            (underlying-function 𝓔 𝓕 u₁ e) (λ i → upper i e)
            where
              f-fixed-e : DCPO[ 𝓓 , 𝓕 ]
              f-fixed-e = continuous→continuous-in-pr₁ 𝓓 𝓔 𝓕 (f , f-is-continuous) e
              p : is-sup (underlying-order 𝓕) (f (∐ 𝓓 δ , e)) (λ i → f (α i , e))
              p = continuity-of-function 𝓓 𝓕 f-fixed-e I α δ
\end{code}
\end{AgdaAlign}\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}

We trivially extend this to a proof on \AgdaFunction{DCPO⊥}.
\begin{code}[hide]
module _ (𝓓 : DCPO⊥ {𝓤} {𝓤'})
         (𝓔 : DCPO⊥ {𝓣} {𝓣'})
         (𝓕 : DCPO⊥ {𝓦} {𝓦'})
       where
\end{code}
\begin{code}
  curryᵈᶜᵖᵒ⊥ : DCPO⊥[ 𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔 , 𝓕 ] → DCPO⊥[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ⊥ 𝓕 ]
  curryᵈᶜᵖᵒ⊥ f = curryᵈᶜᵖᵒ ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ f
\end{code}

\begin{theorem}[Uncurry]
From a continuous function of the form \AgdaType{g}{\AgdaFun{\AgdaExtractSet{𝓓}}{\AgdaExtractSet{\FuncDcpo{𝓔}{𝓕}}}}, we can construct a continuous function of the form \AgdaType{f}{\AgdaFun{\AgdaExtractSet{\AgdaProductDCPO{𝓔}{𝓔}}}{\AgdaExtractSet{𝓕}}}, such that for all \AgdaBound{d}, and for all \AgdaBound{e}, \AgdaEq{\AgdaBound{g}\AgdaSpace{}\AgdaBound{d}\AgdaSpace{}\AgdaBound{e}}{\AgdaBound{f}\AgdaSpace{}\AgdaPair{d}{e}}.
\end{theorem}
\begin{proof}
\hide{
We construct the function $f$ as $λ (d , e). g(d)(e)$. It follows than if a function is continuous in each of its arguments, then it is a continuous function.

As such, we show that $f$ is continuous in the first argument. So, for a fixed $e$, we want to show that for a directed family $α : I → 𝓓$, the least upper bound of the family $λ (i : I). f(α(i) , e)$ is $f(∐_{i : I} α(i) , e)$.

We begin by showing that $∀ (i : I) → f(α(i) , e) \mathbin{⊑_{𝓕}} f(∐_{i : I} α(i) , e)$. By definition of the least upper bound, it follows that $α(i) \mathbin{⊑_{𝓓}} ∐_{i : I}α(i)$. Since g is continuous, and continuous functions are monotone, it follows that the continuous function $g(α(i)) \mathbin{⊑_{𝓔→𝓕}} g(∐_{i : I}α(i))$. By the definition of the pointwise ordering, it then follows that $g(α(i))(e) \mathbin{⊑_{𝓕}} g(∐_{i : I}α(i))(e)$. Therefore, by definition, $f(α(i) , e) \mathbin{⊑_{𝓕}} f(∐_{i : I} α(i) , e)$.

We next require that for any upper bound $u$ of the directed family $λ (i : I). f(α(i) , e)$, $f(∐_{i : I}α(i) , e)$ is less than $u$. We have the following statements:
\begin{enumerate}[(i)]
  \item From the continuity of $g$, it follows that $∐_{i : I}g(α(i)) \mathbin{≡} g(∐_{i : I}α(i))$.
  \item $(∐_{i : I}g(α(i)))(e) \mathbin{≡} g(∐_{i : I}α(i))(e)$ follows since equal functions produce the same output for the same input.
  \item By definition, $(∐_{i : I}g(α(i)))(e)$ is the pointwise supremum, $∐_{i : I}g(α(i))(e)$.
  \item  $∐_{i : I}g(α(i))(e) \mathbin{≡} g(∐_{i : I}α(i))(e)$ by transitivity of $≡$ on facts (ii) and (iii).
  \item By the definition of the least upper bound, it follows that $∐_{i : I}f(α(i) , e) \mathbin{⊑_{𝓕}} u$.
\end{enumerate}  
From this, we can show $f(∐_{i : I}α(i) , e) \mathbin{⊑_{𝓕}} u$ from (iv) and (v), and the definition of $f$. Therefore, $f$ is continuous in its first argument.

The fact that $f$ is continuous in its second argument follows directly from the fact that for any $d$, $g(d)$ is continuous. Therefore, $f$ is continuous in each argument, and it follows that $f$ is continuous.

\begin{code}[hide]
module _ (𝓓 : DCPO {𝓤} {𝓤'})
         (𝓔 : DCPO {𝓣} {𝓣'})
         (𝓕 : DCPO {𝓦} {𝓦'})
       where
\end{code}
We now translate this proof into Agda. }We begin similarly to the curry proof, by pattern matching on the continuous function we assume. We then provide a function \AgdaFunction{f}, which is defined as taking a pair \AgdaType{\AgdaPair{d}{e}}{\AgdaExtractSet{\AgdaProductDCPO{𝓓}{𝓔}}} and applying each argument in turn to \AgdaBound{g}. We also provide a proof of continuity by \cref{continuity-in-arguments-implies-continuous}.
\begin{AgdaAlign} 
\begin{code}
  uncurryᵈᶜᵖᵒ : DCPO[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ 𝓕 ] → DCPO[ (𝓓 ×ᵈᶜᵖᵒ 𝓔) , 𝓕 ]
  uncurryᵈᶜᵖᵒ (g , g-is-continuous) = f , c
    where
      f : ⟨ 𝓓 ×ᵈᶜᵖᵒ 𝓔 ⟩ → ⟨ 𝓕 ⟩
      f (d , e) = underlying-function 𝓔 𝓕 (g d) e
      c : is-continuous (𝓓 ×ᵈᶜᵖᵒ 𝓔) 𝓕 f
      c = continuous-in-arguments→continuous 𝓓 𝓔 𝓕 f continuous-in-pr₁ continuous-in-pr₂
        where
\end{code}
Since all continuous functions are monotone, it follows that \AgdaBound{g} is monotone. 
\begin{code}
          g-is-monotone : is-monotone 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) g
          g-is-monotone = continuous-functions-are-monotone 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (g , g-is-continuous)
\end{code}
We then provide a proof that \AgdaFunction{f} is continuous in its first argument. We define this in terms of a proof \AgdaFunction{u} that \UnderlyingFunction{𝓔}{𝓕}{\AgdaBrackets{\AgdaBound{g}\AgdaSpace{}\AgdaBrackets{\AgdaUpperBound{𝓓}{δ}}}}\AgdaSpace{}\AgdaBound{e} is the upper bound of the pointwise family formed by \AgdaBound{g}\AgdaSpace{}\AgdaFunction{∘}\AgdaSpace{}\AgdaBound{α} and \AgdaBound{e}, and a proof \AgdaFunction{v} that \UnderlyingFunction{𝓔}{𝓕}{\AgdaBrackets{\AgdaBound{g}\AgdaSpace{}\AgdaBrackets{\AgdaUpperBound{𝓓}{δ}}}}\AgdaSpace{}\AgdaBound{e} is less than any other upper bounds of the pointwise family formed by \AgdaBound{g}\AgdaSpace{}\AgdaFunction{∘}\AgdaSpace{}\AgdaBound{α} and \AgdaBound{e}.
\begin{code}
          continuous-in-pr₁ : (e : ⟨ 𝓔 ⟩) 
                              → is-continuous 𝓓 𝓕 (λ d → underlying-function 𝓔 𝓕 (g d) e)
          continuous-in-pr₁ e I α δ = u , v
            where
\end{code}
The proof \AgdaFunction{u} follows easily from the fact that \AgdaBound{g} is monotone. We use the definition of the least upper bound to give us a proof that \AgdaBound{α}\AgdaSpace{}\AgdaBound{i} is less than \AgdaUpperBound{𝓓}{δ} for all \AgdaBound{i}. From the monotonicity of \AgdaBound{g}, we show that \AgdaBound{g}\AgdaSpace{}\AgdaBrackets{\AgdaBound{α}\AgdaSpace{}\AgdaBound{i}} is less than \AgdaBound{g}\AgdaSpace{}\AgdaBrackets{\AgdaUpperBound{𝓓}{δ}}. By the definition of the pointwise order, we apply \AgdaBound{e} to the proof we have constructed so far to achieve \AgdaBound{g}\AgdaSpace{}\AgdaBrackets{\AgdaBound{α}\AgdaSpace{}\AgdaBound{i}} applied to \AgdaBound{e} is less than \AgdaBound{g}\AgdaSpace{}\AgdaBrackets{\AgdaUpperBound{𝓓}{δ}} applied to \AgdaBound{e}.
\begin{code}
              u : is-upperbound (underlying-order 𝓕) (underlying-function 𝓔 𝓕 (g (∐ 𝓓 δ)) e)
                                                  (pointwise-family 𝓔 𝓕 (g ∘ α) e)
              u i = g-is-monotone (α i) (∐ 𝓓 δ) (∐-is-upperbound 𝓓 δ i) e
\end{code}
We next construct our proof \AgdaFunction{v}. We assume \AgdaBound{u₁}, and a proof \AgdaBound{p} that it is an upper bound. We begin our proof in the \AgdaKeyword{where} clause, where we first construct a proof that \AgdaComp{g}{α} is a directed family, and that the pointwise family of \AgdaComp{g}{α} and \AgdaBound{e} is directed. We use proofs that Tom de Jong has previously constructed to show these.
\begin{code}
              v : (u₁ : ⟨ 𝓕 ⟩) → ((i : I) → (underlying-function 𝓔 𝓕 ((g ∘ α) i) e) ⊑⟨ 𝓕 ⟩ u₁)
                  → (underlying-function 𝓔 𝓕 (g (∐ 𝓓 δ)) e) ⊑⟨ 𝓕 ⟩ u₁
              v u₁ p = γ
                where
                  ⟨g∘α⟩-is-directed : is-Directed (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (g ∘ α)
                  ⟨g∘α⟩-is-directed = image-is-directed 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (g , g-is-continuous) δ
                  ⟨g∘α⟩e-is-directed : is-Directed 𝓕 (pointwise-family 𝓔 𝓕 (g ∘ α) e)
                  ⟨g∘α⟩e-is-directed = pointwise-family-is-directed 𝓔 𝓕 (g ∘ α) ⟨g∘α⟩-is-directed e
\end{code}
We next show a proof \AgdaFunction{i}, that \AgdaUpperBound{𝓕}{\AgdaFunction{⟨g∘α⟩e-is-directed}} is less than \AgdaBound{u₁}. This follows from the definition of the least upper bound.
\begin{code} 
                  i : (∐ 𝓕 ⟨g∘α⟩e-is-directed) ⊑⟨ 𝓕 ⟩  u₁
                  i = ∐-is-lowerbound-of-upperbounds 𝓕 ⟨g∘α⟩e-is-directed u₁ p
\end{code} 
The continuity of \AgdaBound{g} produces the proof \AgdaFunction{ii}. We then use the congruence of equality to show 
\UnderlyingFunction{𝓔}{𝓕}{\AgdaBrackets{\AgdaBound{g}\AgdaSpace{}\AgdaBrackets{\AgdaUpperBound{𝓓}{δ}}}}\AgdaSpace{}\AgdaBound{e} 
is equal to 
\UnderlyingFunction{𝓔}{𝓕}{\AgdaBrackets{\AgdaUpperBound{\AgdaBrackets{\FuncDcpo{𝓔}{𝓕}}}{\AgdaFunction{⟨g∘α⟩-is-directed}}}}\AgdaSpace{}\AgdaBound{e}. However,
\UnderlyingFunction{𝓔}{𝓕}{\AgdaBrackets{\AgdaUpperBound{\AgdaBrackets{\FuncDcpo{𝓔}{𝓕}}}{\AgdaFunction{⟨g∘α⟩-is-directed}}}}\AgdaSpace{}\AgdaBound{e} is the same as \AgdaUpperBound{𝓕}{\AgdaFunction{⟨g∘α⟩e-is-directed}}, since the least upper bound is defined pointwise. From congruence, and Agda applying the definition that the least upper bound is constructed pointwise, we achieve \AgdaFunction{iii}.
\begin{code}
                  ii : g (∐ 𝓓 δ) ≡ ∐ (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) ⟨g∘α⟩-is-directed
                  ii = continuous-function-∐-≡ 𝓓 (𝓔 ⟹ᵈᶜᵖᵒ 𝓕) (g , g-is-continuous) δ
                  iii : underlying-function 𝓔 𝓕 (g (∐ 𝓓 δ)) e ≡ ∐ 𝓕 ⟨g∘α⟩e-is-directed
                  iii = ap (λ - → underlying-function 𝓔 𝓕 - e) ii
\end{code}
Since we have the proof \AgdaFunction{i}, we can transport the equality \AgdaFunction{iii} to produce the proof we desire. We use \AgdaFunction{back-transport} as we are required to show the property for the first operand of the equality, from the second operand possessing it.
\begin{code}
                  γ : underlying-function 𝓔 𝓕 (g (∐ 𝓓 δ)) e ⊑⟨ 𝓕 ⟩ u₁
                  γ = back-transport (λ - → - ⊑⟨ 𝓕 ⟩ u₁) iii i
\end{code}
\AgdaFunction{continuity-in-pr₂} is just the fact that \AgdaBound{g}\AgdaSpace{}\AgdaBound{d} is continuous.
\begin{code}
          continuous-in-pr₂ : (d : ⟨ 𝓓 ⟩) → is-continuous 𝓔 𝓕 (underlying-function 𝓔 𝓕 (g d))
          continuous-in-pr₂ d = continuity-of-function 𝓔 𝓕 (g d)
\end{code}
\end{AgdaAlign}\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}
\AgdaNoSpaceAroundCode{
\begin{code}[hide]
module _ (𝓓 : DCPO⊥ {𝓤} {𝓤'})
         (𝓔 : DCPO⊥ {𝓣} {𝓣'})
         (𝓕 : DCPO⊥ {𝓦} {𝓦'})
       where 
\end{code}
}
Again, we trivially extend this to \AgdaFunction{DCPO⊥}.
\begin{code}
  uncurryᵈᶜᵖᵒ⊥ : DCPO⊥[ 𝓓 , 𝓔 ⟹ᵈᶜᵖᵒ⊥ 𝓕 ] → DCPO⊥[ 𝓓 ×ᵈᶜᵖᵒ⊥ 𝓔 , 𝓕 ]
  uncurryᵈᶜᵖᵒ⊥ f = uncurryᵈᶜᵖᵒ ⟪ 𝓓 ⟫ ⟪ 𝓔 ⟫ ⟪ 𝓕 ⟫ f
\end{code}
\end{document}
