\documentclass[main.tex]{subfiles}
\begin{document}

\begin{code}[hide]
open import SpartanMLTT
open import UF-PropTrunc

module Correctness
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt
open import PCF-With-Lambda pt

open import ScottModelOfPCFWithLambda-Types pt fe pe

open import ScottModelOfPCFWithLambda pt fe pe

open import Dcpo pt fe 𝓤₀
open import Dcpo-Contexts pt fe pe
open import DcpoConstructions pt fe
open DcpoConstructionsGeneral 𝓤₀
open LiftingDcpo 𝓤₀ pe

open import Lifting 𝓤₀
open import LiftingMonad 𝓤₀ hiding (μ)
open import LiftingMiscelanea-PropExt-FunExt 𝓤₀ pe fe

open import NaturalNumbers-Properties
open import UF-Subsingletons
\end{code}

\section{Correctness}
\label{correctness}
We next move to our first proof that relates the operational semantics and denotational semantics. We show that the operational semantics are correct with respect to the Scott model. This means that for any terms \AgdaBound{P} and \AgdaBound{V}, if \AgdaBound{P}\AgdaSpace{}\AgdaDatatype{⇓}\AgdaSpace{}\AgdaBound{V}, then it must follow that \AgdaTermInterp{P}\AgdaSpace{}\AgdaDatatype{≡}\AgdaSpace{}\AgdaTermInterp{V}.

\subsection{Substitution lemma}
\label{sublem}
The substitution lemma is said to be proved by straightforward induction on the typing judgement \cite[Lemma~5.1]{domaintheoreticfoundations}. During our development, we experience some differences which Agda requires us to formalise, making the proof less straightforward. We first begin with a lemma, which is not formalised in the proof by Streicher. It only becomes evident that we require it when we try to prove the \AgdaInductiveConstructor{ƛ} case whilst proving the substitution lemma by induction on the typing judgement. We will see later exactly where the following lemma becomes useful.

\begin{lemma}
We assume a term \AgdaTypeJudge{M}{Γ}{σ}, and a map $ρ$ from variables in the context \AgdaBound{Γ} to variables under a new context \AgdaBound{Δ}. Given a set of values \AgdaBound{e} to substitute for variables in \AgdaBound{Γ}, and a set of values \AgdaBound{d} to substitute for variables in \AgdaBound{Δ}, if it is true that for all variables \AgdaBound{x} in the context \AgdaBound{Γ}, \AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x}\AgdaSpace{}\AgdaBound{e}\AgdaSpace{}\AgdaDatatype{≡}\AgdaSpace{}\AgdaFunction{extract}\AgdaSpace{}\AgdaBrackets{\AgdaBound{ρ}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaBound{d}, then it follows that the result of applying \AgdaBound{e} to the interpretation of \AgdaBound{M} is equal to the result of applying \AgdaBound{d} to the interpretation of \AgdaBound{M} with variables renamed according to \AgdaBound{ρ}.
\end{lemma}
\begin{proof}
We begin by formalising the type which we are aiming to prove. We use \AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M} as opposed to \AgdaFunction{underlying-function}\AgdaSpace{}\AgdaExtractDCPO{\AgdaContextInterp{Γ}}\AgdaSpace{}\AgdaExtractDCPO{\AgdaTypeInterp{σ}}\AgdaSpace{}\AgdaTermInterp{M} to access the underlying function from interpretation of a term \AgdaBound{M}. Whilst we prefer the latter as it is more readable, some lines in our proof would become excessively long otherwise.
\begin{AgdaAlign}
\begin{code} 
rename-lemma : {n m : ℕ} {Γ : Context n} {Δ : Context m} {σ : type}
            → (M : PCF Γ σ) → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
            → (d : ⟨ ⟪ 【 Δ 】 ⟫ ⟩) → (e : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
            → (∀ {A} → (x : Γ ∋ A) → extract x e ≡ extract (ρ x) d)
            → pr₁ ⟦ M ⟧ₑ e ≡ pr₁ ⟦ rename ρ M ⟧ₑ d
\end{code}
We case split on the term \AgdaBound{M}. The \AgdaInductiveConstructor{Zero} case is proved by definition, since the term \AgdaInductiveConstructor{Zero} does not change under renaming, and the interpretation of \AgdaInductiveConstructor{Zero} is a constant function to \AgdaFunction{η}\AgdaSpace{}\AgdaInductiveConstructor{zero}, any two arguments applied to the interpretation of \AgdaInductiveConstructor{Zero} always give the same result.
\begin{code} 
rename-lemma Zero ρ d e eq = refl
\end{code}
The case of \AgdaInductiveConstructor{Succ}\AgdaSpace{}\AgdaBound{M} makes use of \AgdaFunction{ap} as we have before, which is applying the fact that for any two types $A, B$, given $f : A → B$, and $x, y : A$, $x \mathbin{≡} y → f x \mathbin{≡} f y$. This is useful as our goal is to prove that \AgdaEq{\AgdaFunction{𝓛̇}\AgdaSpace{}\AgdaInductiveConstructor{succ}\AgdaSpace{}\AgdaBrackets{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaBound{e}}}{\AgdaFunction{𝓛̇}\AgdaSpace{}\AgdaInductiveConstructor{succ}\AgdaSpace{}\AgdaBrackets{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaFunction{rename}\AgdaSpace{}\AgdaBound{ρ}\AgdaSpace{}\AgdaBound{M}}\AgdaSpace{}\AgdaBound{d}}}. Since our inductive hypothesis gives \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaBound{e}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaFunction{rename}\AgdaSpace{}\AgdaBound{ρ}\AgdaSpace{}\AgdaBound{M}}\AgdaSpace{}\AgdaBound{d}}, the proof of this case is trivial. Similarly for the \AgdaPred{M} case, apart from we use \AgdaFunction{pred} instead of \AgdaInductiveConstructor{succ}.
\begin{code}
rename-lemma (Succ M) ρ d e eq = ap (𝓛̇ succ) (rename-lemma M ρ d e eq)
rename-lemma (Pred M) ρ d e eq = ap (𝓛̇ pred) (rename-lemma M ρ d e eq)
\end{code}
For the \AgdaIfZero{M}{M₁}{M₂} case, we use \AgdaFunction{ap₃} This follows the same concept as \AgdaFunction{ap}, apart from it works for functions of three arguments, and thus requires three proofs of equality - one for each argument. All three equalities are given from our inductive hypothesis.
\begin{code}
rename-lemma (IfZero M M₁ M₂) ρ d e eq = ap₃ (λ x₁ x₂ x₃ → pr₁ (⦅ifZero⦆₁ x₂ x₃) x₁)
             (rename-lemma M ρ d e eq) (rename-lemma M₁ ρ d e eq) (rename-lemma M₂ ρ d e eq)
\end{code}
The next case we show is for \AgdaLambda{M}, which is the most interesting case. 
\begin{code}
rename-lemma (ƛ {n} {Γ} {σ} {τ} M) ρ d e eq = γ
  where
\end{code}
We want to show that \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaLambda{M}}\AgdaSpace{}\AgdaBound{e}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaFunction{rename}\AgdaSpace{}\AgdaBound{ρ}\AgdaSpace{}\AgdaBrackets{\AgdaLambda{M}}}\AgdaSpace{}\AgdaBound{d}}. Our first step is the application of the definition of \AgdaFunction{rename}, which states that \AgdaFunction{rename}\AgdaSpace{}\AgdaBound{ρ}\AgdaSpace{}\AgdaBrackets{\AgdaLambda{M}} simplifies to \AgdaLambda{\AgdaBrackets{\AgdaFunction{rename}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{ext}\AgdaSpace{}\AgdaBound{ρ}}\AgdaSpace{}\AgdaBound{M}}}, where \AgdaFunction{ext}, given a map from variables in one context to variables in another, provides a map between the extended contexts as defined in \cite{PLFA}. Applying this definition means we now want to show that \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaLambda{M}}\AgdaSpace{}\AgdaBound{e}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaLambda{\AgdaBrackets{\AgdaFunction{rename}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{ext}\AgdaSpace{}\AgdaBound{ρ}}\AgdaSpace{}\AgdaBound{M}}}}\AgdaSpace{}\AgdaBound{d}}. Both sides of the equality are continuous functions from the domain \AgdaTypeInterp{\AgdaPCFType{σ}{τ}}.

Since our representation of a continuous function is a dependent pair, we begin by showing the first projections of both of the continuous functions are equal. The first projection of the pair is the underlying function itself. We say that two functions are equal if they always provide the same output as each other when given the same input. We use \AgdaFunction{∼} to represent this relation between two functions. Since the interpretation of lambda abstraction is the currying of the subterm, this means we want to show that \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaPair{e}{z}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaFunction{rename}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{ext}\AgdaSpace{}\AgdaBound{ρ}}\AgdaSpace{}\AgdaBound{M}}\AgdaSpace{}\AgdaPair{d}{z}} for all \AgdaBound{z}. However, we notice that this is just our inductive hypothesis.
\begin{code}
    ih :  (λ z → pr₁ ⟦ M ⟧ₑ (e , z)) ∼ (λ z → pr₁ ⟦ rename (ext ρ) M ⟧ₑ (d , z))
    ih z = rename-lemma M (ext ρ) (d , z) (e , z) g
      where
\end{code}
Our inductive hypothesis requires a new proof that extracting a value for a given variable \AgdaBound{x} from \AgdaPair{e}{z} is the same as renaming \AgdaBound{x} under the extended \AgdaBound{ρ} and then extracting a value from \AgdaPair{d}{z}. We prove this by induction on the lookup judgement. Our first case is \AgdaInductiveConstructor{Z}, from which it follows by definition that both sides reduce to \AgdaBound{z}, and thus our proof is just \AgdaInductiveConstructor{refl}.
\begin{code}
        g : ∀ {A} → (x : (Γ ’ σ) ∋ A) → extract x (e , z) ≡ extract (ext ρ x) (d , z)
        g Z = refl
\end{code}
Our next case is \AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x}. We want to show \AgdaEq{\AgdaFunction{extract}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaPair{e}{z}}{\AgdaFunction{extract}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{ext}\AgdaSpace{}\AgdaBound{ρ}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x}}}\AgdaSpace{}\AgdaPair{d}{z}} which reduces to showing \AgdaEq{\AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x}\AgdaSpace{}\AgdaBound{e}}{\AgdaFunction{extract}\AgdaSpace{}\AgdaBrackets{\AgdaBound{ρ}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaBound{d}} by definition, since \AgdaFunction{ext}\AgdaSpace{}\AgdaBound{ρ}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x}} reduces to \AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBrackets{\AgdaBound{ρ}\AgdaSpace{}\AgdaBound{x}}, and then \AgdaFunction{extract}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBrackets{\AgdaBound{ρ}\AgdaSpace{}\AgdaBound{x}}}\AgdaSpace{}\AgdaPair{d}{z} reduces to \AgdaFunction{extract}\AgdaSpace{}\AgdaBrackets{\AgdaBound{ρ}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaBound{d}, similarly \AgdaFunction{extract}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaPair{e}{z} reduces to \AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x}\AgdaSpace{}\AgdaBound{e}. We notice this case is trivial, as it is given by applying \AgdaBound{x} to our assumption \AgdaBound{eq}.
\begin{code}
        g (S x) = eq x
\end{code}
Since we have shown that the underlying functions produce equal output for the same input, we can provide a proof that these two functions are equal by \AgdaFunction{nfunext}, which applies our axiomatic approach to function extensionality. We also make use of Tom de Jong's proof that a given function being continuous is a proposition, which, as we have previously defined, means that any two proofs of continuity for a given function are equal. Since we have shown our underlying functions to be equal, and being continuous is a proposition, we can then make use of \AgdaFunction{to-subtype-≡} to provide a proof that the two dependent pairs are equal.
\begin{code}
    γ : pr₁ ⟦ ƛ M ⟧ₑ e ≡ pr₁ ⟦ rename ρ (ƛ M) ⟧ₑ d
    γ = to-subtype-≡ (being-continuous-is-a-prop ⟪ ⟦ σ ⟧ ⟫ ⟪ ⟦ τ ⟧ ⟫) (nfunext fe ih)
\end{code}
Application is then also trivial. We use \AgdaFunction{ap₂}, which again is similar to \AgdaFunction{ap} except for two argument functions. The two equalities of arguments we provide come from the induction hypothesis.
\begin{code}
rename-lemma (M · M₁) ρ d e eq = ap₂ pr₁ (rename-lemma M ρ d e eq) (rename-lemma M₁ ρ d e eq)
\end{code}
The variable case comes straight from our assumption \AgdaBound{eq}.
\begin{code}
rename-lemma (v x) ρ d e eq = eq x
\end{code}
Then our final case for \AgdaFix{M} is shown by a simple application of \AgdaFunction{ap}, with the induction hypothesis.
\begin{code}
rename-lemma (Fix {_} {_} {σ} M) ρ d e eq = ap (pr₁ (μ ⟦ σ ⟧)) (rename-lemma M ρ d e eq)
\end{code}
\end{AgdaAlign}\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}
With this lemma formalised, we can now move on to prove the lemma we are actually interested in. We formalise it as Streicher does, and then we try to formalise it in Agda.
\begin{lemma}[Substitution lemma]
Let \AgdaBound{Γ}$ = σ₁,...,σₙ$ be a context and \AgdaTypeJudge{M}{Γ}{τ} a term. For all contexts \AgdaBound{Δ} and terms \AgdaTypeJudge{Nᵢ}{Δ}{σᵢ} with $i=1,...,n$, it holds that for all \AgdaBound{d}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaExtractSet{\AgdaExtractDCPO{\AgdaContextInterp{Δ}}}:
\begin{center}
\AgdaField{pr₁} \AgdaTermInterp{\AgdaFunction{subst} f M} d \AgdaFunction{≡} \AgdaTermInterp{M}(\AgdaField{pr₁} \AgdaTermInterp{N₁} d,...,\AgdaField{pr₁} \AgdaTermInterp{Nₙ} d)
\end{center}
\end{lemma}
\begin{proof}
As stated, this proof should follow by induction on the typing judgement \AgdaTypeJudge{M}{Γ}{τ}. However, let's begin formalising this in Agda.

We first start with a helper function, which we use to construct the list of \AgdaTermInterp{Nᵢ} applied to \AgdaBound{d}.
\begin{code}
applied-all : {m n : ℕ} {Γ : Context n} → {Δ : Context m}
              → (∀ {A} → Γ ∋ A → PCF Δ A) → ⟨ ⟪ 【 Δ 】 ⟫ ⟩ → ⟨ ⟪ 【 Γ 】 ⟫ ⟩
applied-all {_} {_} {⟨⟩} f d = *
applied-all {_} {_} {Γ ’ x} f d = (applied-all (f ∘ S) d) , (pr₁ ⟦ f Z ⟧ₑ d)
\end{code}
Next, we begin to formalise the substitution lemma with our new construction. We use a substitution function \AgdaBound{f} to represent the mapping of variables with de Bruijn index $i$ to term $N_{i}$.
\begin{code}
substitution-lemma' : {n m : ℕ}{Γ : Context n}{Δ : Context m}{σ : type}
                    → (M : PCF Γ σ) → (f : ∀ {A} → Γ ∋ A → PCF Δ A) → (d : ⟨ ⟪ 【 Δ 】 ⟫ ⟩)
                    → pr₁ ⟦ M ⟧ₑ (applied-all f d) ≡ pr₁ ⟦ subst f M ⟧ₑ d
\end{code} 
\begin{code}[hide]
substitution-lemma' M f d = 𝟘-elim i
  where
    postulate
      i : 𝟘 {𝓤₀}
\end{code}
This seems to match the lemma we are trying to prove, but whilst attempting to prove this for the lambda abstraction case, we begin to uncover some lemmas which we need to prove regarding \AgdaFunction{applied-all}, some of which may be tricky.

This is one of the cases where our proof is made simple by reformulating what we are trying to prove. We make an extra assumption \AgdaBound{e}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaExtractSet{\AgdaExtractDCPO{\AgdaContextInterp{Γ}}}. We then add the constraint that for all lookup judgements \AgdaBound{x} of the context \AgdaBound{Γ}, we have \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaInductiveConstructor{v}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaBound{e}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaBound{f}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaBound{d}}. We can view this as the proof requiring a list of values \AgdaBound{e}, which take on the form similar to what we were trying to achieve with \AgdaFunction{applied-all}. The advantage this time is that we have access to the equality between extracting index \AgdaBound{x} from \AgdaBound{e} and the interpretation of the term \AgdaBound{f}\AgdaSpace{}\AgdaBound{x} applied to \AgdaBound{d}, which we did not have in our previous formation.
\begin{AgdaAlign}
\begin{code}
substitution-lemma : {n m : ℕ}{Γ : Context n}{Δ : Context m} {σ : type}
                  → (M : PCF Γ σ) → (f : ∀ {A} → Γ ∋ A → PCF Δ A)
                  → (e : ⟨ ⟪ 【 Γ 】 ⟫ ⟩) → (d : ⟨ ⟪ 【 Δ 】 ⟫ ⟩)
                  → (∀ {A} → (x : Γ ∋ A) → pr₁ ⟦ v x ⟧ₑ e ≡ pr₁ ⟦ f x ⟧ₑ d )
                  → pr₁ ⟦ M ⟧ₑ e ≡ pr₁ ⟦ subst f M ⟧ₑ d
\end{code}
Most of these cases are proved in a similar way to how we proved them for \AgdaFunction{rename-lemma}, so we shall only consider the interesting ones.

We first begin with the variable case. This is now trivial, since it's given by our assumption.
\begin{code}
substitution-lemma (v x) f e d eq = eq x 
\end{code}
Next is the lambda abstraction case. This is similar to the equivalent case for \AgdaFunction{rename-lemma}, although we need to construct a proof of \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaVar{x}}\AgdaSpace{}\AgdaPair{e}{z}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaFunction{exts}\AgdaSpace{}\AgdaBound{f}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaPair{d}{z}} for all~\AgdaBound{x}.
\begin{code}
substitution-lemma (ƛ {_} {Γ} {σ} {τ} M) f e d eq = γ
  where
    ih : (λ z → pr₁ ⟦ M ⟧ₑ (e , z)) ∼ (λ z → pr₁ ⟦ subst (exts f) M ⟧ₑ (d , z))
    ih z = substitution-lemma M (exts f) (e , z) (d , z) exts-eq
      where
\end{code}
We prove our new equality holds by induction on the lookup judgement. The base case is trivial, as it reduces to showing that \AgdaEq{z}{z}.
\begin{code}
        exts-eq : ∀ {A} → (x : (Γ ’ σ) ∋ A) → pr₁ ⟦ v x ⟧ₑ (e , z) ≡ pr₁ ⟦ exts f x ⟧ₑ (d , z)
        exts-eq Z = refl
\end{code}
The next case is more interesting. By definition, \AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaInductiveConstructor{v}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaImplicit{\_}\AgdaSpace{}\AgdaImplicit{\_}\AgdaSpace{}\AgdaImplicit{\_}\AgdaSpace{}\AgdaImplicit{σ}\AgdaSpace{}\AgdaBound{x}}}\AgdaSpace{}\AgdaPair{e}{z} reduces to \AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaInductiveConstructor{v}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaBound{e}. We have provided the implicit arguments to \AgdaInductiveConstructor{S}, as Agda struggles to work one out in this case. We use the underscore for the ones which Agda can work out, and provide the parameter which it can not. We then show \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaInductiveConstructor{v}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaBound{e}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaBound{f}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaBound{d}} by applying our assumption \AgdaBound{eq} to \AgdaBound{x}. We next consider showing \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaBound{f}\AgdaSpace{}\AgdaBound{x}}\AgdaSpace{}\AgdaBound{d}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaFunction{exts}\AgdaSpace{}\AgdaBound{f}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x}}}\AgdaSpace{}\AgdaPair{d}{z}}. However, since \AgdaFunction{exts}\AgdaSpace{}\AgdaBound{f}\AgdaSpace{}\AgdaBrackets{\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x}} reduces to \AgdaFunction{rename}\AgdaSpace{}\AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBrackets{\AgdaBound{f}\AgdaSpace{}\AgdaBound{x}}, showing this equality is just an application of \AgdaFunction{rename-lemma}. Constructing the proof that \AgdaFunction{rename-lemma} requires is trivial, as for all typing judgements \AgdaBound{x₁}, the equality we need to show reduces to \AgdaEq{\AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x}\AgdaSpace{}\AgdaBound{d}}{\AgdaFunction{extract}\AgdaSpace{}\AgdaBound{x}\AgdaSpace{}\AgdaBound{d}}, and we can provide the proof \AgdaInductiveConstructor{refl}.
\begin{code}
        exts-eq (S x) = pr₁ ⟦ v (S {_} {_} {_} {σ} x) ⟧ₑ (e , z) ≡⟨ eq x ⟩
                        pr₁ ⟦ f x ⟧ₑ d ≡⟨ rename-lemma (f x) S (d , z) d (λ x₁ → refl) ⟩
                        pr₁ ⟦ exts f (S x) ⟧ₑ (d , z) ∎
\end{code}
We show our representations of the continuous functions are equal in the same way we did in \AgdaFunction{rename-lemma}, using the proof that the underlying functions are equal by function extensionality.
\begin{code}
    γ : pr₁ ⟦ ƛ M ⟧ₑ e ≡ pr₁ ⟦ subst f (ƛ M) ⟧ₑ d
    γ = to-subtype-≡ (being-continuous-is-a-prop ⟪ ⟦ σ ⟧ ⟫ ⟪ ⟦ τ ⟧ ⟫) (nfunext fe ih)
\end{code}
\AgdaNoSpaceAroundCode{
\begin{code}[hide]
substitution-lemma Zero f e d g = refl
substitution-lemma (Succ M) f e d g = ap (𝓛̇ succ) (substitution-lemma M f e d g)
substitution-lemma (Pred M) f e d g = ap (𝓛̇ pred) (substitution-lemma M f e d g)
substitution-lemma (IfZero M M₁ M₂) f e d g =
                     pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ M₁ ⟧ₑ e) (pr₁ ⟦ M₂ ⟧ₑ e)) (pr₁ ⟦ M ⟧ₑ e) ≡⟨ i ⟩
                     pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ M₁ ⟧ₑ e) (pr₁ ⟦ M₂ ⟧ₑ e)) (pr₁ ⟦ subst f M ⟧ₑ d) ≡⟨ ii ⟩
                     pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ subst f M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ e)) (pr₁ ⟦ subst f M ⟧ₑ d) ≡⟨ iii ⟩
                     pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ subst f M₁ ⟧ₑ d) (pr₁ ⟦ subst f M₂ ⟧ₑ d)) (pr₁ ⟦ subst f M ⟧ₑ d) ∎
  where
    i = ap (pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ M₁ ⟧ₑ e) (pr₁ ⟦ M₂ ⟧ₑ e))) (substitution-lemma M f e d g)
    ii = ap (λ - → pr₁ (⦅ifZero⦆₁ - (pr₁ ⟦ M₂ ⟧ₑ e)) (pr₁ ⟦ subst f M ⟧ₑ d)) (substitution-lemma M₁ f e d g)
    iii = ap (λ - → pr₁ (⦅ifZero⦆₁ (pr₁ ⟦ subst f M₁ ⟧ₑ d) -) (pr₁ ⟦ subst f M ⟧ₑ d)) (substitution-lemma M₂ f e d g)
substitution-lemma (M · M₁) f e d g = γ
  where
    γ : pr₁ (pr₁ ⟦ M ⟧ₑ e) (pr₁ ⟦ M₁ ⟧ₑ e) ≡ pr₁ (pr₁ ⟦ subst f M ⟧ₑ d) (pr₁ ⟦ subst f M₁ ⟧ₑ d)
    γ = pr₁ (pr₁ ⟦ M ⟧ₑ e) (pr₁ ⟦ M₁ ⟧ₑ e) ≡⟨ ap (pr₁ (pr₁ ⟦ M ⟧ₑ e)) (substitution-lemma M₁ f e d g) ⟩
         pr₁ (pr₁ ⟦ M ⟧ₑ e) (pr₁ ⟦ subst f M₁ ⟧ₑ d) ≡⟨ ap (λ - → pr₁ - (pr₁ ⟦ subst f M₁ ⟧ₑ d)) (substitution-lemma M f e d g) ⟩
         pr₁ (pr₁ ⟦ subst (λ {A} → f) M ⟧ₑ d)
           (pr₁ ⟦ subst (λ {A} → f) M₁ ⟧ₑ d) ∎
substitution-lemma {n} {Γ} {m} {Δ} {σ} (Fix M) f e d g = ap (λ - → pr₁ (μ ⟦ σ ⟧ ) -) (substitution-lemma M f e d g)
\end{code}
} 
\end{AgdaAlign}\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}
We then prove a corollary, which we will need when we prove correctness.
\begin{corollary}
If \AgdaTypeJudge{M}{\AgdaBrackets{\AgdaBound{Γ}\AgdaSpace{}\AgdaInductiveConstructor{’}\AgdaSpace{}\AgdaBound{σ}}}{τ} and \AgdaTypeJudge{N}{Γ}{σ}, then
\AgdaFunEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaApp{\AgdaLambda{M}}{N}}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaReplace{M}{N}}} 
\end{corollary}
\begin{proof}
Our proof of \AgdaFunction{β-equality} follows easily from \AgdaFunction{substitution-lemma}.
\hide{
We see that it follows straight from \AgdaFunction{substitution-lemma}. Our substitution function comes from the definition of \AgdaReplace{M}{N}, which is 
\begin{code}
β-equality : {n : ℕ} {Γ : Context n} {σ τ : type} → (M : PCF (Γ ’ τ) σ) → (N : PCF Γ τ)
           → (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩) → pr₁ ⟦ (ƛ M) · N ⟧ₑ d ≡ pr₁ ⟦ M [ N ] ⟧ₑ d
β-equality {n} {Γ} {σ} {τ} M N d
               = substitution-lemma M (replace-first τ Γ N) (d , (pr₁ ⟦ N ⟧ₑ d)) d eq
  where
    eq : ∀ {A} → (x : (Γ ’ τ) ∋ A)
               → pr₁ ⟦ v x ⟧ₑ (d , pr₁ ⟦ N ⟧ₑ d) ≡ pr₁ ⟦ replace-first τ Γ N x ⟧ₑ d
    eq Z = refl
    eq (S x) = refl
\end{code}\vspace{-3.5em}\[\tag*{\qedhere}\]}
\end{proof}

\subsection{Proving correctness}

Now we have enough to construct our proof of correctness. There is no explicit proof of this theorem in the paper we are following for our proofs, although there is a mention that it is easy to verify by induction on the structure of derivations that correctness of the Scott model with respect to the operational semantics holds \cite[Section~7]{domaintheoreticfoundations}. Since in our setting \AgdaFunction{⇓} is defined as the propositional truncation of \AgdaFunction{⇓'}, we first begin with a lemma for \AgdaFunction{⇓'}. From this lemma, it becomes trivial to then show \AgdaTermInterp{M} and \AgdaTermInterp{V} are equal, and therefore correctness, since a function being continuous is a proposition.
\begin{lemma}
For any \AgdaTypeJudge{M}{Γ}{σ} and \AgdaTypeJudge{V}{Γ}{σ}, if \AgdaBound{M}\AgdaSpace{}\AgdaFunction{⇓'}\AgdaSpace{}\AgdaBound{V}, then \AgdaFunEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}}.
\end{lemma}
\begin{proof}
This proof is by induction on the derivations as suggested by Streicher. Some cases are simply applying induction hypothesis, and others make use of equalities already constructed by Tom de Jong. As such, for brevity, we omit most of this proof. We will consider the particular case for application, which makes use of \AgdaFunction{β-equality} we previously proved. To keep the lemma we are trying to prove tidy, we made the proof of this lemma for application a separate sublemma. Since the inductive hypothesis in the sublemma would not be strong enough, we take the inductive hypothesis from the main lemma as assumptions, which we can then give to the sublemma when it is applied. The assumptions are that the main lemma holds for \AgdaBigStepPrime{M}{\AgdaLambda{E}} and \AgdaBigStepPrime{\AgdaReplace{E}{T}}{N}.
\begin{code}
correctness-· : {n : ℕ} {Γ : Context n} {σ τ : type}
                → (M : PCF Γ (σ ⇒ τ)) → (E : PCF (Γ ’ σ) τ) → (T : PCF Γ σ) → (N : PCF Γ τ)
                → pr₁ ⟦ M ⟧ₑ ∼ pr₁ ⟦ ƛ E ⟧ₑ → pr₁ ⟦ E [ T ] ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
                → pr₁ ⟦ M · T ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
\end{code}
We assume \AgdaType{d}{\AgdaExtractSet{\AgdaExtractDCPO{\AgdaContextInterp{Γ}}}}, and show that the output of both functions are equal. We do this by equational reasoning. After applying the definition of \AgdaTermInterp{\AgdaApp{M}{T}}, our next step is the use of our assumption that \AgdaFunEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaLambda{E}}}. If we apply \AgdaBound{d} to this assumption, we can construct the proof that \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaBound{d}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaLambda{E}}\AgdaSpace{}\AgdaBound{d}}. We next make use of our proof of \AgdaFunction{β-equality}, to show that applying \AgdaBound{d} to \AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaApp{\AgdaLambda{E}}{T}} is the same as applying \AgdaBound{d} to \AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaReplace{E}{T}}. Our final step is the application of the assumption that \AgdaFunEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaReplace{E}{T}}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaBound{N}}}, similar to how we did previously.
\begin{code}
correctness-· M E T N c₁ c₂ d = pr₁ (pr₁ ⟦ M ⟧ₑ d) (pr₁ ⟦ T ⟧ₑ d)      ≡⟨ i ⟩
                                pr₁ (pr₁ ⟦ ƛ E ⟧ₑ d) (pr₁ ⟦ T ⟧ₑ d)    ≡⟨ ii ⟩
                                pr₁ ⟦ E [ T ] ⟧ₑ d                      ≡⟨ c₂ d ⟩
                                pr₁ ⟦ N ⟧ₑ d                            ∎
  where
    i = ap (λ - → pr₁ - (pr₁ ⟦ T ⟧ₑ d)) (c₁ d)
    ii = β-equality E T d
\end{code}
\begin{code}[hide]
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
\end{code}

As mentioned, since most cases are simple or just make use of equalities already constructed by Tom de Jong, we omit most of the proof. However, we will show how we apply the sublemma above. We see how the sublemma makes use of the inductive hypotheses from \AgdaFunction{correctness'}. 
\begin{code}
correctness' : {n : ℕ} {Γ : Context n} {σ : type}
               → (M N : PCF Γ σ) → M ⇓' N → pr₁ ⟦ M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
               -- Most cases omitted for brevity.
correctness' .(_ · _) N (·-step {_} {_} {_} {_} {M} {E} {T} {_} r r₁) =
                      correctness-· M E T N (correctness' M (ƛ E) r) (correctness' (E [ T ]) N r₁)
\end{code}\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}
\AgdaNoSpaceAroundCode{
\begin{code}[hide]
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

\end{code}
}
We next show correctness, which follows easily from \AgdaFunction{correctness'}.
\begin{theorem}[Correctness]
For any \AgdaTypeJudge{M}{Γ}{σ} and \AgdaTypeJudge{V}{Γ}{σ}, if \AgdaBigStep{M}{V} then it follows that \AgdaEq{\AgdaTermInterp{M}}{\AgdaTermInterp{V}}.
\end{theorem}
\begin{proof}
Our proof involves showing the continuous functions \AgdaTermInterp{M} and \AgdaTermInterp{N} are equal, which we do in a similar fashion to as we did in \AgdaFunction{substitution-lemma}. We use a proof \AgdaFunction{i} that the two functions produce the same output for the same input, meaning they are equal by function extensionality.
\begin{AgdaAlign}
\begin{code}
correctness : {n : ℕ} {Γ : Context n} {σ : type} (M N : PCF Γ σ) → M ⇓ N → ⟦ M ⟧ₑ ≡ ⟦ N ⟧ₑ
correctness {_} {Γ} {σ} M N step
            = to-subtype-≡ (being-continuous-is-a-prop ⟪ 【 Γ 】 ⟫ ⟪ ⟦ σ ⟧ ⟫) (nfunext fe i)
  where
\end{code}
We next look at the proof \AgdaFunction{i} that the underlying functions of the interpretations are related by \AgdaFunction{∼}. We assume \AgdaBound{d}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaExtractSet{\AgdaExtractDCPO{\AgdaContextInterp{Γ}}}, and show that \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaBound{d}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{N}\AgdaSpace{}\AgdaBound{d}}. Since \AgdaBound{step} is an element of type \AgdaBigStep{M}{N}, which is the propositional truncation of the type \AgdaBigStepPrime{M}{N}, we use \AgdaFunction{∥∥-rec} to prove what we are trying to show. We are able to do this since the underlying type of \AgdaTypeInterp{σ} is a set, therefore \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaBound{d}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{N}\AgdaSpace{}\AgdaBound{d}} is a proposition. We then provide a proof that from a given \AgdaBound{x₁}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaBigStepPrime{M}{N} we can produce a proof that \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaBound{d}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{N}\AgdaSpace{}\AgdaBound{d}} holds. Finally, we provide \AgdaBound{step}, which shows there exists a proof such that \AgdaBigStepPrime{M}{N}, and therefore conclude from the recursion principle that \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaBound{d}}{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{N}\AgdaSpace{}\AgdaBound{d}} holds.
\begin{code}
    i : pr₁ ⟦ M ⟧ₑ ∼ pr₁ ⟦ N ⟧ₑ
    i d = ∥∥-rec (sethood ⟪ ⟦ σ ⟧ ⟫) (λ x₁ → correctness' M N x₁ d) step
\end{code}
\end{AgdaAlign}\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}
\end{document}
