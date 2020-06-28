\documentclass[main.tex]{subfiles}

\begin{document}

\AgdaHide{
\begin{code}

open import UF-PropTrunc

module PCF-Chapter (pt : propositional-truncations-exist) where

open import SpartanMLTT

open PropositionalTruncation pt

infixr 1 _⇒_
infixl 1 _·_

\end{code}
}

\section{PCF}
\label{PCF}
In 1977, Gordon Plotkin considered Dana Scott's logic of computable functions as a programming language, called PCF (programming language for computable functions) \cite{Plotkin1977}. PCF can be seen as an extended version of the typed lambda calculus, since it contains extra constructs such as the fixed-point operator to allow for general recursion. One may question why we would consider such a toy language when we have practical languages such as Haskell or ML which we could reason about. However, PCF can be seen as a simplified version of these typed functional languages. Due to the simplistic nature, it is easier to reason about PCF compared to a large language with extra constructs or features such as concurrency.

We begin by formalising PCF with the base type of natural numbers, and a constructor to create function types. Since our terms can contain variables, we determine how we are going to represent them. We proceed to assign types to our terms intrinsically via the typing judgement.

\subsection{Types and terms}
\begin{definition}
We define the types of PCF inductively as follows:
\begin{itemize}
  \item The base type $ι$ represents the natural numbers.
  \item If $σ$ and $τ$ are types in PCF, $σ ⇒ τ$ is the function type from $σ$ to $τ$.
\end{itemize}
\end{definition}

We give meaning to these types later, when we define the semantics of PCF.

In Agda, we can define this as follows:
\begin{code}
data type : 𝓤₀ ̇  where
  ι : type
  _⇒_ : type → type → type
\end{code}
The \AgdaKeyword{data} keyword allows us to inductively define a datatype. We give the name \AgdaDatatype{type} to this particular datatype, as we are defining our PCF types. The definition states we have two constructors, \AgdaInductiveConstructor{ι}, which takes no arguments, and \AgdaInductiveConstructor{⇒}, which constructs a new type from two types. The underscores in the definition of \AgdaInductiveConstructor{⇒} define where the arguments go when using the constructor. Therefore, \AgdaInductiveConstructor{\AgdaUnderscore{}⇒\AgdaUnderscore{}} defines \AgdaInductiveConstructor{⇒} as an infix operator, e.g. \AgdaBound{σ}\AgdaSpace{}\AgdaInductiveConstructor{⇒}\AgdaSpace{}\AgdaBound{τ}. If we leave the underscores in the operator name when we use it, we can use the constructor in the same manner as standard application, i.e. \AgdaInductiveConstructor{_⇒_}\AgdaSpace{}\AgdaBound{σ}\AgdaSpace{}\AgdaBound{τ}. The definition also states that our datatype \AgdaDatatype{type} lives in the universe \AgdaPrimitive{𝓤₀}, which is our lowest level universe.

We then should consider the terms which we will be assigning these types to. The following grammar captures the terms we will be considering:
\begin{center}
L, M, N ::= v x | ƛ M | M · N | Zero | Succ M | Pred M | IfZero L M N | Fix M
\end{center}

From the above, we have the following terms that operate on the natural numbers:
\begin{itemize}
  \item Zero - Represents the natural number zero.
  \item Pred M - The predecessor of M (e.g. the predecessor of 4 would be 3).
  \item Succ M - The successor of M (e.g. the successor of 2 would be 3).
  \item IfZero L M N - Allows for conditional statements, and returns M or N depending on the value of L.
\end{itemize}

We then have the constructs for lambda abstraction, function application, and variables:
\begin{itemize}
  \item ƛ M - Represents a lambda abstraction, with body M.
  \item M · N - Represents applying a term M to a term N.
  \item v x - Represents a variable, with identifier x.
\end{itemize}

Finally, the construct for general recursion:
\begin{itemize}
  \item Fix M - Represents the fixed-point combinator, which returns the fixed point of M, allowing for general recursion.
\end{itemize}

\subsection{Representing variables}
\label{representing-variables}
Since a PCF term may contain free variables, we need some way of representing the variables that may occur inside a term. To do this, we use a context. A context is a list of variables and their associated types. They are of the form:
\begin{center}
$Γ \mathbin{=} x₀:σ₀, ..., xₙ : σₙ$
\end{center}
where $σᵢ$ is the type of the variable with identifier $xᵢ$. We tend to use the symbol $Γ$, and sometimes $Δ$, to represent an arbitrary context.

One uncertainty about the definition of the terms above is how should we identify variables, i.e. what should $xᵢ$ be. When we consider programming languages, we tend to use strings to refer to variables, which are called named variables. Whilst valid, let's consider the following program:
\begin{code}
example : ℕ -> ℕ -> ℕ 
example = λ x → λ x → x
\end{code}
Of course, the variable referred to in the body should be the one of the innermost lambda. The inner variable is said to mask the outer variable of the same name. Whilst obvious, this still requires insight to implement and overcome the issue of variable shadowing. When implementing substitution, if we wanted to replace the variable $x$ in the term \AgdaFunction{example} above, it requires we solve this complication of which $x$ we should, or should not, replace. One way of removing name conflicts is to use $α$-conversion, which is the renaming of bound variables. This has its own implementation complications. For example, if we rename a bound variable, we need to ensure the new identifier does not occur in the scope of the bound variable already, otherwise the meaning of the original term will not be preserved.

A common alternative is to use de Bruijn indices \cite{DEBRUIJN1972381}. Rather than using strings to identify variables, we use an index which identifies which variable in the context we are referring to. Since a variable in the context will have a unique index, the problem of variable shadowing disappears as terms written using these indices are invariant with respect to $α$-conversion.

Therefore, since the index of the variable is itself the identifier, we can instead represent variables as lists of just types:
\begin{center}
$Γ \mathbin{=} σ₀, ..., σₙ$
\end{center}

Now we decide how to formalise this in Agda. One may first consider representing a context as a list of types. However, the issue with this is when we want to extract the $i^{th}$ variable via the $i^{th}$ projection map, this function would not be defined for lists of length less than $i$. Agda is total, meaning we cannot define functions which are partial or throw exceptions. To ensure that we only allow projections which are valid, we embed the length of the list within the type. This is an example of the advantage of dependent types.

From this, we can consider a context to correspond to a vector of length $n$, where the type of elements of the vector is fixed to be PCF types. We define our context to grow to the right, as is convention.
\begin{code}
data Vec (X : 𝓤₀ ̇) : ℕ → 𝓤₀ ̇ where
  ⟨⟩ : Vec X zero
  _’_ : {n : ℕ} → Vec X n → X → Vec X (succ n)

Context : ℕ → 𝓤₀ ̇
Context = Vec type
\end{code}
Here, we see our first use of implicit arguments. Sometimes, an argument can be worked out by Agda based on the context, or other arguments to the function. In such cases, we may choose to make the argument implicit, which means when using the definition, we do not need to provide the implicit argument as Agda will infer it. In the definition of the symbol \AgdaInductiveConstructor{’}, we can see that \AgdaBound{n} is an implicit argument. We define implicit arguments by surrounding them with curly brackets. The reason Agda can work out the argument which should be given for \AgdaBound{n} is because it is uniquely determined by the constructor's second argument of type \AgdaDatatype{Vec}\AgdaSpace{}\AgdaBound{X}\AgdaSpace{}\AgdaBound{n}.

We then formalise the lookup judgement, for which we follow the definition in \cite{PLFA}. We define a datatype $Γ ∋ A$ for variables of type $A$ which exist in the context $Γ$. The inhabitants of these types can be seen as corresponding to the index of the variable in the context. We note that the zeroth index is the rightmost element of our context, and incrementing as we proceed left.
\begin{code}
data _∋_ : {n : ℕ} → Context n → type → 𝓤₀ ̇ where
  Z : ∀ {n : ℕ} {Γ : Context n} {σ : type} → (Γ ’ σ) ∋ σ 
  S : ∀ {n : ℕ} {Γ : Context n} {σ τ : type}
      → Γ ∋ σ
      → (Γ ’ τ) ∋ σ
\end{code}
Below are two examples of proofs of \AgdaBound{Γ}\AgdaSpace{}\AgdaDatatype{∋}\AgdaSpace{}\AgdaInductiveConstructor{ι}, where \AgdaBound{Γ} is our Agda representation of \AgdaInductiveConstructor{ι},\AgdaBrackets{\AgdaPCFType{\AgdaInductiveConstructor{ι}}{\AgdaInductiveConstructor{ι}}},\AgdaInductiveConstructor{ι},\AgdaBrackets{\AgdaPCFType{\AgdaInductiveConstructor{ι}}{\AgdaInductiveConstructor{ι}}}:
\begin{code}
ex₁ : ((((⟨⟩ ’ ι) ’ (ι ⇒ ι)) ’ ι) ’ (ι ⇒ ι)) ∋ ι
ex₁ = S Z
\end{code}
\begin{code} 
ex₂ : ((((⟨⟩ ’ ι) ’ (ι ⇒ ι)) ’ ι) ’ (ι ⇒ ι)) ∋ ι
ex₂ = S (S (S Z))
\end{code}
We can see that \AgdaInductiveConstructor{S Z} is similar to referring to the first index of the context, and \AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaInductiveConstructor{Z}}} is similar to referring to the third index.

\subsection{Assigning types to terms}

We next look at our typing judgement, which are a set of rules applied inductively to generate well-typed terms. For our definition, we follow a Church-style system, where types are an intrinsic part of the language semantics \cite{10.5555/509043}.

\begin{definition}
We inductively define the type $\PCF\ Γ\ σ$ to refer to the well-typed PCF terms which have type $σ$ under the context $Γ$ by the rules below:
\begin{small}
\[
\begin{bprooftree}
  \AxiomC{$x : Γ\ ∋\ σ$}
  \UnaryInfC{$v\ x : \PCF\ Γ\ σ$}
\end{bprooftree}\qquad
\begin{bprooftree}
  \AxiomC{$M : \PCF\ (Γ \mathbin{’} σ)\ τ$}
  \UnaryInfC{$ƛ\ M : \PCF\ Γ\ (σ \mathbin{⇒} τ)$}
\end{bprooftree}\qquad
\begin{bprooftree}
  \AxiomC{$M : \PCF\ Γ\ (σ \mathbin{⇒} τ)$}
  \AxiomC{$N : \PCF\ Γ\ σ$}
  \BinaryInfC{$M \mathbin{·} N : \PCF\ Γ\ τ$}
\end{bprooftree}
\]
\[
\begin{bprooftree}
  \AxiomC{ }
  \UnaryInfC{$\Zero : \PCF\ Γ\ ι$}
\end{bprooftree}\qquad
\begin{bprooftree}
  \AxiomC{$M : \PCF\ Γ\ ι$}
  \UnaryInfC{$\SuccPCF M : \PCF\ Γ\ ι$}
\end{bprooftree}\qquad
\begin{bprooftree}
  \AxiomC{$M : \PCF\ Γ\ ι$}
  \UnaryInfC{$\Pred M : \PCF\ Γ\ ι$}
\end{bprooftree}
\]
\[
\begin{bprooftree}
  \AxiomC{$M : \PCF\ Γ\ (σ \mathbin{⇒} σ)$}
  \UnaryInfC{$\Fix M : \PCF\ Γ\ σ$}
\end{bprooftree}\qquad
\begin{bprooftree}
  \AxiomC{$Mᵢ : \PCF\ Γ\ ι $}
  \RightLabel{i=1,2,3}
  \UnaryInfC{$\IfZero M₁\ M₂\ M₂ : \PCF\ Γ\ ι$}
\end{bprooftree}
\]
\end{small}
\end{definition}
In Agda, the definition looks very similar.
\begin{code}
data PCF : {n : ℕ} (Γ : Context n) (σ : type) → 𝓤₀ ̇ where
  Zero   : {n : ℕ} {Γ : Context n} → PCF Γ ι
  Succ   : {n : ℕ} {Γ : Context n} → PCF Γ ι → PCF Γ ι
  Pred   : {n : ℕ} {Γ : Context n} → PCF Γ ι → PCF Γ ι
  IfZero : {n : ℕ} {Γ : Context n} → PCF Γ ι → PCF Γ ι → PCF Γ ι → PCF Γ ι
  ƛ      : {n : ℕ} {Γ : Context n} {σ τ : type} → PCF (Γ ’ σ) τ → PCF Γ (σ ⇒ τ) 
  _·_    : {n : ℕ} {Γ : Context n} {σ τ : type} → PCF Γ (σ ⇒ τ) → PCF Γ σ → PCF Γ τ
  v      : {n : ℕ} {Γ : Context n} {A : type} → Γ ∋ A → PCF Γ A
  Fix    : {n : ℕ} {Γ : Context n} {σ : type} → PCF Γ (σ ⇒ σ) → PCF Γ σ
\end{code}
\end{document}
