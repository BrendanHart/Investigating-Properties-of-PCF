\documentclass[main.tex]{subfiles}
\begin{document}
\AgdaNoSpaceAroundCode{
\begin{code}[hide]

open import UF-PropTrunc

module OpSem (pt : propositional-truncations-exist) where

open import SpartanMLTT

open PropositionalTruncation pt

data Vec (X : 𝓤₀ ̇) : ℕ → 𝓤₀ ̇ where
  ⟨⟩ : Vec X zero
  _’_ : {n : ℕ} → Vec X n → X → Vec X (succ n)

data Fin : (n : ℕ) → 𝓤₀ ̇ where
  zero : ∀ {n} → Fin (succ n)
  succ : ∀ {n} → Fin n → Fin (succ n)

data type : 𝓤₀ ̇  where
  ι : type
  _⇒_ : type → type → type

Context : ℕ → 𝓤₀ ̇
Context = Vec type


data _∋_ : {n : ℕ} → Context n → type → 𝓤₀ ̇ where
  Z : ∀ {n : ℕ} {Γ : Context n} {σ : type} → (Γ ’ σ) ∋ σ 
  S : ∀ {n : ℕ} {Γ : Context n} {σ τ : type}
      → Γ ∋ σ
      → (Γ ’ τ) ∋ σ

lookup : {n : ℕ} → Context n → Fin n → type
lookup (Γ ’ x) zero = x
lookup (Γ ’ x) (succ n) = lookup Γ n

count : {n : ℕ} {Γ : Context n} → (f : Fin n) → Γ ∋ lookup Γ f
count {.(succ _)} {Γ ’ x} zero = Z
count {.(succ _)} {Γ ’ x} (succ f) = S (count f)

infixr 1 _⇒_

data PCF : {n : ℕ} (Γ : Context n) (σ : type) → 𝓤₀ ̇ where
  Zero   : {n : ℕ} {Γ : Context n}
           → PCF Γ ι
  Succ   : {n : ℕ} {Γ : Context n}
           → PCF Γ ι
           → PCF Γ ι
  Pred   : {n : ℕ} {Γ : Context n}
           → PCF Γ ι
           → PCF Γ ι
  IfZero : {n : ℕ} {Γ : Context n}
           → PCF Γ ι
           → PCF Γ ι
           → PCF Γ ι
           → PCF Γ ι
  ƛ      : {n : ℕ} {Γ : Context n} {σ τ : type}
           → PCF (Γ ’ σ) τ
           → PCF Γ (σ ⇒ τ) 
  _·_    : {n : ℕ} {Γ : Context n} {σ τ : type}
           → PCF Γ (σ ⇒ τ)
           → PCF Γ σ
           → PCF Γ τ
  v      : {n : ℕ} {Γ : Context n} {A : type}
           → Γ ∋ A
           → PCF Γ A
  Fix    : {n : ℕ} {Γ : Context n} {σ : type}
           → PCF Γ (σ ⇒ σ)
           → PCF Γ σ
           
infixl 1 _·_


ext : ∀ {m n} {Γ : Context m} {Δ : Context n}
      → (∀ {A} → Γ ∋ A → Δ ∋ A)
      → (∀ {σ A} → (Γ ’ σ) ∋ A → (Δ ’ σ) ∋ A)
ext f Z = Z
ext f (S t) = S (f t)

rename : ∀ {m n} {Γ : Context m} {Δ : Context n}
        → (∀ {A} → Γ ∋ A → Δ ∋ A)
        → (∀ {A} → PCF Γ A → PCF Δ A)
rename f Zero = Zero
rename f (Succ t) = Succ (rename f t)
rename f (Pred t) = Pred (rename f t)
rename f (IfZero t t₁ t₂) = IfZero (rename f t) (rename f t₁) (rename f t₂)
rename f (ƛ t) = ƛ (rename (ext f) t)
rename f (t · t₁) = (rename f t) · (rename f t₁)
rename f (v x) = v (f x)
rename f (Fix t) = Fix (rename f t)

exts : ∀ {m n} {Γ : Context m} {Δ : Context n}
       → (∀ {A} → Γ ∋ A → PCF Δ A)
       → (∀ {σ A} → (Γ ’ σ) ∋ A → PCF (Δ ’ σ) A)
exts f Z = v Z
exts f (S t) = rename (_∋_.S) (f t)
\end{code}
}
\section{Operational Semantics}
\label{OpSem}
To execute code on a computer, there must be rules defined which a computer can then apply to arrive at a result. One might consider the operational semantics of Haskell to be the rules which the Haskell interpreter applies when executing a program. So, we can take the operational semantics of a language to be a model which represents the execution of valid programs in that language.

There are different approaches to defining this model, such as small-step semantics, or big-step semantics. The big-step semantics and small-step semantics are shown to coincide by Streicher \cite[Section~2]{domaintheoreticfoundations}. Streicher goes on to consider the big-step semantics throughout the paper since they are more abstract, as they lose the intermediate computation steps unlike small-step semantics. We shall also consider the big-step semantics for the same reasons, and to keep our proofs similar.

\subsection{Substitution}
Before we define the big-step semantics, we need the concept of substitution. When we consider the term \AgdaApp{\AgdaLambda{M}}{N}, it should evaluate to the same term as \AgdaBound{M} with \AgdaBound{N} substituted for the first variable. Due to our choice of variable implementation, the implementation of substitution is fairly simple.

We implement substitution in Agda as in \cite{PLFA}. We define the function \AgdaFunction{subst}, which defines how to apply a mapping, from variables in a context to terms in a new context, to a term. This is called simultaneous substitution. When we come across a lambda term, we essentially are introducing a new variable into the context. As a result, we want to extend our mapping by shifting the existing indices up by one, and leave the new zeroth index untouched when we apply the substitution to the subterm. The \AgdaFunction{exts} helper function performs this operation, although is omitted for brevity.
\begin{code}
subst : ∀ {m n} {Γ : Context m} {Δ : Context n} → (∀ {A} → Γ ∋ A → PCF Δ A)
                                                → (∀ {A} → PCF Γ A → PCF Δ A)
subst f Zero = Zero
subst f (Succ t) = Succ (subst f t)
subst f (Pred t) = Pred (subst f t)
subst f (IfZero t t₁ t₂) = IfZero (subst f t) (subst f t₁) (subst f t₂)
subst f (ƛ t) = ƛ (subst (exts f) t)
subst f (t · t₁) = (subst f t) · (subst f t₁)
subst f (v x) = f x
subst f (Fix t) = Fix (subst f t)
\end{code}
\hide{
Next we define a simple function by induction on the typing judgement which replaces the first variable, and reduces the index of the rest of the variables in the context by one.
\begin{code}
replace-first : {n : ℕ} (A : type) (Γ : Context n) (N : PCF Γ A) → (∀ {B} → (Γ ’ A) ∋ B → PCF Γ B)
replace-first A Γ N Z = N
replace-first A Γ N (S t) = v t
\end{code}
}
We then define a function which applies the substitution of \AgdaFunction{replace-first}, which replaces the first variable with a given term, and maps the variable \AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x} to \AgdaBound{x}, providing us with a function that replaces only the first variable in a term.
\begin{code}
_[_] : {n : ℕ} {Γ : Context n} {σ A : type}
         → PCF (Γ ’ A) σ → PCF Γ A → PCF Γ σ
_[_] {n} {Γ} {σ} {A} M N = subst (replace-first A Γ N) M 
\end{code}
\subsection{Big-step semantics of PCF}
From our understanding that the operational semantics relates to the evaluation of terms, we can define the big-step semantics for PCF, as well as consider some properties which follow from the definition.

For each natural number $n$, we write the canonical numeral as $\underline{n}$. When we are writing Agda code, we construct these canonical expressions with the function \AgdaFunction{ℕ-to-ι}. We can imagine this as a function which takes a natural number, and produces the simplest representation possible in PCF. E.g. \AgdaFunction{ℕ-to-ι}\AgdaSpace{}\AgdaBound{2} reduces to \AgdaSucc{\AgdaBrackets{\AgdaSucc{\AgdaZero}}}.
\begin{code}[hide]
ℕ-to-ι : ∀ {n} {Γ : Context n} → ℕ → PCF Γ ι
ℕ-to-ι zero = Zero
ℕ-to-ι (succ n) = Succ (ℕ-to-ι n)
\end{code}

\begin{code}[hide] 
peano-axiom-for-PCF : ∀ {n Γ k} → ℕ-to-ι {n} {Γ} zero ≢ ℕ-to-ι (succ k)
peano-axiom-for-PCF ()
\end{code}

\begin{definition}
We define the big-step relation between terms $M$ and $N$, $M ⇓ N$, using the inductive rules below:
\begin{small}
\[
\begin{bprooftree}
    \AxiomC{ }
    \UnaryInfC{$\Zero ⇓ \Zero$}
\end{bprooftree}\qquad
\begin{bprooftree}
    \AxiomC{$M ⇓ \underline{n}$}
    \UnaryInfC{$\SuccPCF M ⇓ \underline{n+1}$}
\end{bprooftree}\qquad
\begin{bprooftree}
    \AxiomC{$M ⇓ \underline{0}$}
    \UnaryInfC{$\Pred M ⇓ \underline{0}$}
\end{bprooftree}\qquad
\begin{bprooftree}
    \AxiomC{$M ⇓ \underline{n+1}$}
    \UnaryInfC{$\Pred M ⇓ \underline{n}$}
\end{bprooftree}
\]
\[
\begin{bprooftree}
    \AxiomC{ }
    \UnaryInfC{$v \ i ⇓ v \ i$}
\end{bprooftree}\qquad
\begin{bprooftree}
    \AxiomC{ }
    \UnaryInfC{$ƛ \ t ⇓ ƛ \ t$}
\end{bprooftree}\qquad
\begin{bprooftree}
    \AxiomC{$M ⇓ ƛ E$}
    \AxiomC{$E[N] ⇓ V$}
    \BinaryInfC{$M · N ⇓ V$}
\end{bprooftree}\qquad
\begin{bprooftree}
    \AxiomC{$M · (\Fix M) ⇓ V$}
    \UnaryInfC{$\Fix M ⇓ V$}
\end{bprooftree}
\]
\[
\begin{bprooftree}
    \AxiomC{$M ⇓ \underline{0}$}
    \AxiomC{$M₂ ⇓ V$}
    \BinaryInfC{$\IfZero M\ M₁\ M₂ ⇓ V$}
\end{bprooftree}\qquad
\begin{bprooftree}
    \AxiomC{$M ⇓ \underline{n+1}$}
    \AxiomC{$M₁ ⇓ V$}
    \BinaryInfC{$\IfZero M\ M₁\ M₂ ⇓ V$}
\end{bprooftree} 
\]
\end{small}
\end{definition}
  
From the above definition, it might be clear to see why it's called big-step. Rather than considering the individual steps of a computation like small-step would, the rules for big-step make assumptions about how the constituents of a term evaluate, in order to determine the value that the term itself evaluates to.   

In Agda, we first define the relation $⇓'$ as follows. Since the definition spans many lines and is very similar to the rules above, we only show select cases for comparison.
\begin{code}
data _⇓'_ : ∀ {n : ℕ} {Γ : Context n} {σ : type} → PCF Γ σ → PCF Γ σ → 𝓤₀ ̇ where
  -- Most rules omitted for brevity
  IfZero-zero : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι} {M₁ : PCF Γ ι} {M₂ : PCF Γ ι} {V : PCF Γ ι}
              → M ⇓' ℕ-to-ι {n} {Γ} zero
              → M₁ ⇓' V
              → IfZero M M₁ M₂ ⇓' V
  Fix-step  : {n : ℕ} {Γ : Context n} {σ : type} {M : PCF Γ (σ ⇒ σ)} {V : PCF Γ σ}
              → (M · (Fix M)) ⇓' V
              → Fix M ⇓' V
  ·-step    : {n : ℕ} {Γ : Context n} {σ τ : type}
              {M : PCF Γ (σ ⇒ τ)} {E : PCF (Γ ’ σ) τ} {N : PCF Γ σ} {V : PCF Γ τ}
              → M ⇓' ƛ E
              → (E [ N ]) ⇓' V
              → (M · N) ⇓' V
\end{code}
\hide{
\begin{code}[hide]
  IfZero-succ : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι} {M₁ : PCF Γ ι} {M₂ : PCF Γ ι} {V : PCF Γ ι} {k : ℕ}  
              → M ⇓' ℕ-to-ι {n} {Γ} (succ k)
              → M₂ ⇓' V
              → IfZero M M₁ M₂ ⇓' V
  var-id    : {n : ℕ} {Γ : Context n} {A : type} {i : Γ ∋ A}
              → (v i) ⇓' (v i)  
  ƛ-id      : {n : ℕ} {Γ : Context n} {σ τ : type} {t : PCF (Γ ’ σ) τ}
              → ƛ t ⇓' ƛ t
  zero-id   : {n : ℕ} {Γ : Context n}
              → ℕ-to-ι {n} {Γ} zero ⇓' ℕ-to-ι {n} {Γ} zero
  pred-zero : {n : ℕ} {Γ : Context n} {M : PCF Γ ι}
              → M ⇓' ℕ-to-ι {n} {Γ} zero
              → Pred M ⇓' ℕ-to-ι {n} {Γ} zero
  pred-succ : {n : ℕ} {Γ : Context n} {M : PCF Γ ι} {k : ℕ}
              → M ⇓' ℕ-to-ι {n} {Γ} (succ k)
              → Pred M ⇓' ℕ-to-ι {n} {Γ} k
  succ-arg  : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι} {k : ℕ}
              → M ⇓' ℕ-to-ι {n} {Γ} k
              → Succ M ⇓' ℕ-to-ι {n} {Γ} (succ k) 
\end{code}
}
One consideration is that we need the big-step relation to be a proposition. Whilst this should be true, it can be difficult to prove. As a result, we use propositional truncation which squashes a type down to a mere proposition, allowing us to define $⇓$ as:
\begin{code}
_⇓_ : {n : ℕ} {Γ : Context n} {σ : type} → PCF Γ σ → PCF Γ σ → 𝓤₀ ̇
M ⇓ N = ∥ M ⇓' N ∥
\end{code}
\hide{
In Agda, an example of how we would apply the successor step rule is

\begin{code}
ex₁ : {n : ℕ} {M : PCF ⟨⟩ ι} → M ⇓' ℕ-to-ι n → Succ M ⇓' ℕ-to-ι (succ n)
ex₁ x = succ-arg x
\end{code}
}

From this definition, we can then show that an application of big-step semantics always reduces a term to its normal form, which is called a value. For the following proofs, we omit the Agda code as the proofs are trivial.

\begin{definition}
A PCF term is a value if it is either a lambda abstraction, numeral, or a variable.
\end{definition}

\begin{lemma}\label{bigstepreducestoval}
For every PCF term \AgdaBound{M}, if \AgdaBigStepPrime{M}{V} then \AgdaBound{V} is a value.
\end{lemma}
\begin{proof}
By induction on \AgdaBigStepPrime{M}{V}.
\end{proof}
\hide{
We can then show that values only reduce to themselves.

\begin{lemma}\label{valsonlyreduceonce}
For every PCF term $M$, if $M$ is a value, and \AgdaBigStep{M}{V}, then $M$ and $N$ are equal.
\end{lemma}
\begin{proof}
By induction on \AgdaBigStep{M}{V}.
\end{proof}

From these two lemmas, we can easily show that there is at most one possible big-step reduction for any PCF term.
\begin{proposition}
If \AgdaBigStep{M}{N}, and \AgdaBigStep{N}{L}, then $N$ and $L$ are equal.
\end{proposition}
\begin{proof}
Since $N$ must be a value from \cref{bigstepreducestoval}, it must follow that $N$ is equal to $L$ from \cref{valsonlyreduceonce}.
\end{proof}
}
It is also interesting to note that there is only ever one unique reduction that can be applied to any given term. This means that the big-step relation is deterministic.

\begin{proposition}[Big-step is deterministic]
If \AgdaBigStepPrime{M}{N} and \AgdaBigStepPrime{M}{L}, then \AgdaBound{N} and \AgdaBound{L} are equal.
\end{proposition}
\begin{proof}
By induction on \AgdaBigStepPrime{M}{N}.
\end{proof}
\end{document}
