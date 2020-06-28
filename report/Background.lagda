\documentclass[main.tex]{subfiles}

\begin{document}

\section{Background and Considerations}
We first explain some necessary background and considerations which will be required when understanding definitions in this text, particularly some concepts in type theory which we shall be using.

\subsection{Agda flags}
During our development, we use the following flags, which we specify at the top of each file:
\begin{itemize}
  \item \texttt{--without-K} - This disables Streicher's K axiom, allowing us to work with univalent mathematics.
  \item \texttt{--exact-split} - Makes Agda only accept definitions that behave like definitional equalities.
  \item \texttt{--safe} - Disables postulates.
\end{itemize}
This will be the only time we mention these flags throughout this text, but it helps to set some context for how we shall be working in Agda.

\subsection{Universes}
To avoid Russel's paradox, Agda has universes \cite{AgdaDocUniverses}. Universes are types whose elements are types themselves. We have an ascending, infinite number of universes. One might consider data types such as Int and Bool. These types may live in the universe $𝓤₀$, which we use to represent the lowest level universe. If we were to have 𝓤₀ belonging in the universe 𝓤₀, we would encounter Russel's paradox. As such, we define 𝓤₀ as existing in the universe 𝓤₁, and then 𝓤₁ exists in the universe 𝓤₂, etc.

In Agda, by default, the keyword \AgdaPrimitive{Set} is used to represent the lowest level universe, and the larger universes then as \AgdaPrimitive{Set₁}, \AgdaPrimitive{Set₂}, etc. The subscript \AgdaPrimitive{n} is the level of the universe \AgdaPrimitive{Setₙ}

We rename the default Agda implementation so we can match our original terminology, staying closer to the notation we tend to use in homotopy type theory. We perform the following renamings:
\begin{itemize}
  \item \AgdaPrimitive{Level} to \AgdaPrimitive{Universe}.
  \item \AgdaPrimitive{lzero} (the lowest level in Agda) to \AgdaPrimitive{𝓤₀}.
  \item \AgdaPrimitive{lsuc} to \AgdaPrimitive{⁺}, so we can refer to the universe above \AgdaPrimitive{𝓤₀} as \AgdaPrimitive{𝓤₀} \AgdaPrimitive{⁺}.
  \item \AgdaPrimitive{Setω} to \AgdaPrimitive{𝓤ω}, which is a universe where, for all $n$, \AgdaPrimitive{𝓤ω} is strictly above \AgdaPrimitive{𝓤ₙ}.
  \item Given a universe level \AgdaPrimitive{𝓤}, we denote the universe type as \AgdaPrimitive{𝓤}\AgdaSpace{}\AgdaFunction{̇} (note the combining dot above).
\end{itemize}

Throughout, we will use the letters $𝓤$, $𝓥$, $𝓦$, $𝓣$ to refer to arbitrary universes levels.

\subsection{The identity type}
We use Martin-L\"{o}f's identity type as our notion of equality. We say that the type $\operatorname{Id}\ X\ x\ y$ represents the equality of terms $x$ and $y$ under the type $X$. We have the sole constructor of this type, $\operatorname{refl}$, which produces an element of the type $\operatorname{Id}\ X\ x\ x$, for any $x : X$.

In our developments, we use an alternative notation. We say $x \mathbin{≡} y$ to represent the equality of terms $x$ and $y$ under a type $X$. We note that we do not need to provide the type $X$, as Agda can infer this. Our constructor, $\operatorname{refl}$, also does not explicitly require us to provide the $x$ in our Agda developments, as this can again be inferred from the type we are trying to construct.

\subsection{Propositions}
\label{propositions}
Propositions (sometimes called subsingletons, or truth values) are, in univalent mathematics, defined as a type with at most one element. Another way of saying this is that if we have two elements from a proposition, then by definition they must be equal. Formally, we define this as:
\begin{definition}
A type $X$ is a proposition if for any two elements $x, y : X$, $x$ is equal to $y$.
\end{definition}

There is a way we can ``squash'' a type down to a proposition. We call this propositional truncation. We use $\squash{X}$ to take the propositional truncation of $X$. For example, let's consider the propositional truncation of the dependent pair for a type family $P : X → 𝓤$, which we write as $\squash{\Sigma_{x : X}P(x)}$. We tend to think of the dependent pair as a proof that the first projection $x$ has a property $P(x)$, and the proof that $x$ has this property is the second projection. If we take the propositional truncation of this dependent pair, we then think of this truncated type as the fact that there exists some $x$ for which $P(x)$ holds, but we do not remember which particular $x$.

For a type $X$, we define the type $\squash{X}$ as the propositional truncation of $X$ using the following constructors:
\begin{itemize}
  \item For any $x : X$, $\tosquash{x} : \squash{X}$.
  \item For any $x , y : \squash{X}$, $x \mathbin{≡} y$.
\end{itemize}

The recursion principle of propositional truncation allows us to do case analysis when we are trying to prove another proposition from a proof of a truncated type. In our developments, we use \AgdaFunction{∥∥-rec} for this. Given a type \AgdaBound{X}, we can conclude a proposition \AgdaBound{P} holds if we can provide a proof that \AgdaBound{P} is a proposition, a proof \AgdaBound{X}\AgdaSpace{}\AgdaSymbol{→}\AgdaSpace{}\AgdaBound{P}, and a proof of \AgdaFunction{∥}\AgdaSpace{}\AgdaBound{X}\AgdaSpace{}\AgdaFunction{∥}. A particular case of \AgdaFunction{∥∥-rec} comes when we are trying to show, for types \AgdaBound{X} and \AgdaBound{Y}, \AgdaFunction{∥}\AgdaSpace{}\AgdaBound{Y}\AgdaSpace{}\AgdaFunction{∥} from \AgdaFunction{∥}\AgdaSpace{}\AgdaBound{X}\AgdaSpace{}\AgdaFunction{∥}. Since the propositional truncation is by definition a proposition, we can use \AgdaFunction{∥∥-functor} to show this, which only requires a proof \AgdaBound{X}\AgdaSpace{}\AgdaSymbol{→}\AgdaSpace{}\AgdaBound{Y}, and a proof of \AgdaFunction{∥}\AgdaSpace{}\AgdaBound{X}\AgdaSpace{}\AgdaFunction{∥}.

We note that in our developments we work with an axiomatic approach to propositional truncation, as Mart\'in Escard\'o does \cite{escard2019introduction}, meaning we assume the constructions defined above exist. 

\subsection{Sets}
In homotopy type theory, not all types are sets. Sets are types with a special property.
\begin{definition}
A type $X$ is a set if for any two elements $x$ and $y$ of type $X$, the identity type $x \mathbin{≡} y$ is a proposition.
\end{definition}
We use this definition later when defining DCPOs, as we require the underlying type to be a set.

\end{document}

  
