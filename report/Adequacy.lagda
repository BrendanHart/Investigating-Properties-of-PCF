\documentclass[main.tex]{subfiles}
\begin{document}
\begin{code}[hide]
open import SpartanMLTT
open import UF-PropTrunc

module Adequacy
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (pe : propext 𝓤₀)
       where

open PropositionalTruncation pt

open import UF-Miscelanea

open import NaturalNumbers-Properties

open import PCF-With-Lambda pt
open import PCF-With-Lambda-Substitution pt fe pe

open import ScottModelOfPCFWithLambda-Types pt fe pe

open import ScottModelOfPCFWithLambda pt fe pe

open import Lifting 𝓤₀
open import LiftingMonad 𝓤₀ hiding (μ)
open import LiftingMiscelanea-PropExt-FunExt 𝓤₀ pe fe

open import LiftingMiscelanea 𝓤₀

open import Dcpo pt fe 𝓤₀
open import Dcpo-Contexts pt fe pe
open import DcpoConstructions pt fe
open DcpoConstructionsGeneral 𝓤₀
open LiftingDcpo 𝓤₀ pe

\end{code}

\section{Computational Adequacy}
\label{adequacy}
We next show that the denotational semantics are computationally adequate with respect to the operational semantics, following the proof by Streicher \cite[Section~7]{domaintheoreticfoundations}. We show this in the usual way, with the construction of a logical relation. We first define a syntactic preorder, the applicative approximation relation.

\subsection{Applicative approximation}
\label{applicativeapprox}
We can view the applicative approximation relation between two closed terms as containing the information that the two terms are in some sense equivalent in terms of their reductions. This becomes clearer in our definition.
\begin{definition}
We define the applicative approximation relation between closed terms $M$ and $N$ of type $σ$, $M \mathbin{⊏̰_{σ}} N$, by induction on $σ$ as follows:
\begin{itemize} 
  \item For the base type $ι$, $M \mathbin{⊏̰_{ι}} N$ iff $∀ (n : ℕ) → M ⇓ \underline{n} → N ⇓ \underline{n}$.
  \item For function types $σ \mathbin{⇒} τ$, $M \mathbin{⊏̰_{σ \mathbin{⇒} τ}} N$ iff $∀ (P : \PCF\ ⟨⟩\ σ) → (M \mathbin{·} P) \mathbin{⊏̰_{τ}} (N \mathbin{·} P)$.
\end{itemize}
\end{definition}
In Agda, this translates almost directly, apart from the type is not a subscript of the relation symbol. Instead, it is an implicit parameter, as it can be inferred from the type of $M$ and $N$.
\begin{code}
_⊏̰_ : {σ : type} → PCF ⟨⟩ σ → PCF ⟨⟩ σ → 𝓤₀ ̇
_⊏̰_ {ι} M N = ∀ (n : ℕ) → M ⇓ ℕ-to-ι n → N ⇓ ℕ-to-ι n
_⊏̰_ {σ ⇒ τ} M N = ∀ (P : PCF ⟨⟩ σ) → (M · P) ⊏̰ (N · P)
\end{code}

During our attempts at following Streicher's proof of adequacy, we come across two lemmas regarding this relation which we depend upon. The first is the proof that for every PCF type $σ$ and \AgdaTypeJudge{M}{\AgdaEmptyContext}{\AgdaBrackets{\AgdaBound{σ}\AgdaSpace{}\AgdaInductiveConstructor{⇒}\AgdaSpace{}\AgdaBound{σ}}}, it holds that \AgdaAppApr{\AgdaApp{M}{\AgdaFix{M}}}{\AgdaFix{M}}. Streicher proves this by inspection of the inductive definition of \AgdaFunction{⇓}, so we first attempt to prove this by induction on \AgdaBound{σ}. This makes sense, since \AgdaFunction{⊏̰} is defined by induction on the type, but we seem to become stuck in the inductive case.

Later in the proof of adequacy, we come across another proof on \AgdaFunction{⊏̰}. Streicher notes that it generally holds that given \AgdaTypeJudge{M}{\AgdaBrackets{\AgdaExtendContext{\AgdaEmptyContext}{σ}}}{τ} and \AgdaTypeJudge{N}{\AgdaEmptyContext}{σ}, that \AgdaAppApr{\AgdaReplace{M}{N}}{\AgdaApp{\AgdaLambda{M}}{N}}. However, this is just a footnote and no proof is given. Agda will not accept that a statement is true unless we prove it. Again, we try to prove this by induction on \AgdaBound{τ}, but we become stuck.

One thing that seems common in both of our attempts at proving the lemmas is that the inductive hypothesis does not seem to be strong enough. However, we can notice some commonality in the lemmas we are trying to prove. From applying the big-step semantics, if \AgdaBigStepPrime{\AgdaApp{M}{\AgdaFix{M}}}{V}, then it follows that \AgdaBigStepPrime{\AgdaFix{M}}{V} for any \AgdaBound{V}. Similarly, we can also say if \AgdaBigStepPrime{\AgdaReplace{M}{N}}{V} then \AgdaBigStepPrime{\AgdaApp{\AgdaLambda{M}}{N}}{V} for any \AgdaBound{V}. So, it seems a more general form of what we are trying to prove is the following lemma:

\begin{lemma}
Given \AgdaTypeJudge{M}{\AgdaEmptyContext}{σ} and \AgdaTypeJudge{N}{\AgdaEmptyContext}{σ}, if for all \AgdaTypeJudge{V}{\AgdaEmptyContext}{σ}, \AgdaBigStepPrime{M}{V} implies that \AgdaBigStepPrime{N}{V}, then \AgdaAppApr{M}{N}.
\end{lemma}
\begin{proof}
We prove this by induction on \AgdaBound{σ}.
\begin{AgdaAlign}
\begin{code}
⊏̰-lemma : {σ : type} → (M N : PCF ⟨⟩ σ) → ((V : PCF ⟨⟩ σ) → M ⇓' V → N ⇓' V) → M ⊏̰ N
\end{code}
The base case is simple. From the definition of \AgdaFunction{⊏̰} for the base type, we want to show that for an \AgdaBound{n}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaDatatype{ℕ}, that if \AgdaBigStep{M}{\AgdaFunction{ℕ-to-ι}\AgdaSpace{}\AgdaBound{n}}, then \AgdaBigStep{N}{\AgdaFunction{ℕ-to-ι}\AgdaSpace{}\AgdaBound{n}}. We prove this using \AgdaFunction{∥∥-functor} as we have done previously. This requires that we show, given \AgdaBigStepPrime{M}{\AgdaFunction{ℕ-to-ι}\AgdaSpace{}\AgdaBound{n}}, then \AgdaBigStepPrime{N}{\AgdaFunction{ℕ-to-ι}\AgdaSpace{}\AgdaBound{n}}, but this follows straight from applying our assumption \AgdaBound{f}.
\begin{code}
⊏̰-lemma {ι} M N f n step = ∥∥-functor γ step
  where
    γ : M ⇓' ℕ-to-ι n → N ⇓' ℕ-to-ι n
    γ step₁ = f (ℕ-to-ι n) step₁
\end{code}
Our inductive case follows straight from the inductive hypothesis, however we rely on a proof \AgdaFunction{γ}.
\begin{code} 
⊏̰-lemma {σ ⇒ τ} M N f P = ⊏̰-lemma (M · P) (N · P) γ
  where
\end{code}
Our proof \AgdaFunction{γ} assumes a \AgdaTypeJudge{V}{\AgdaEmptyContext}{τ}, and \AgdaBound{step}\AgdaSpace{}\AgdaSymbol{:}\AgdaSpace{}\AgdaBigStepPrime{\AgdaBrackets{\AgdaApp{M}{P}}}{V}. Our goal is to show \AgdaBigStepPrime{\AgdaBrackets{\AgdaApp{N}{P}}}{V}. There is only one possible case for \AgdaBound{step}, and that's \AgdaInductiveConstructor{·-step}. So, we case split on \AgdaBound{step}, and end up with this single case. From this, we get a proof \AgdaBound{step₁} that, for some \AgdaBound{E}, \AgdaBigStepPrime{M}{\AgdaLambda{E}}, and a proof \AgdaBound{step₂} that \AgdaBigStepPrime{\AgdaReplace{E}{P}}{V}. Now since we want to show \AgdaBigStepPrime{\AgdaBrackets{\AgdaApp{N}{P}}}{V}, the only way we can show this is from \AgdaInductiveConstructor{·-step} which requires a proof that for some \AgdaBound{E}, \AgdaBigStepPrime{N}{\AgdaLambda{E}} and a proof that \AgdaBigStepPrime{\AgdaReplace{E}{P}}{V}.

We have that \AgdaBigStepPrime{N}{\AgdaLambda{E}} by applying our assumption \AgdaBound{f} to \AgdaBound{step₁}. Since we already have \AgdaBound{step₂}, we can now apply \AgdaInductiveConstructor{·-step} to conclude this proof.
\begin{code}
    γ : (V : PCF ⟨⟩ τ) → (M · P) ⇓' V → (N · P) ⇓' V
    γ V (·-step {_} {_} {_} {_} {_} {E} step₁ step₂) = ·-step N-step step₂
      where
        N-step : N ⇓' ƛ E
        N-step = f (ƛ E) step₁
\end{code}
\end{AgdaAlign}\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}

We now can show the main properties we are interested in, which follow from the above lemma easily.
\begin{corollary}
For each type $σ$ and term \AgdaTypeJudge{M}{\AgdaEmptyContext{}}{\AgdaBrackets{\AgdaBound{σ}\AgdaSpace{}\AgdaInductiveConstructor{⇒}\AgdaSpace{}\AgdaBound{σ}}}, it holds that \AgdaAppApr{\AgdaBrackets{\AgdaApp{M}{\AgdaFix{M}}}}{\AgdaBrackets{\AgdaFix{M}}}.
\end{corollary}
\begin{proof}
Our proof follows immediately from \AgdaFunction{⊏̰-lemma}. We provide \AgdaFunction{p}, which is a proof of the property we require the two terms of our applicative approximation to have in order to apply our lemma. To show \AgdaFunction{p}, we assume \AgdaTypeJudge{V}{\AgdaEmptyContext}{σ}, and given \AgdaBigStepPrime{\AgdaBrackets{\AgdaApp{M}{\AgdaFix{M}}}}{V}, we show \AgdaBigStepPrime{\AgdaFix{M}}{V} by the big-step rule \AgdaInductiveConstructor{Fix-step}.
\begin{code}
fix-⊏̰ : {σ : type} → {M : PCF ⟨⟩ (σ ⇒ σ)} → (M · (Fix M)) ⊏̰ (Fix M)
fix-⊏̰ {σ} {M} = ⊏̰-lemma (M · Fix M) (Fix M) p
  where
    p : (V : PCF ⟨⟩ σ) → (M · Fix M) ⇓' V → Fix M ⇓' V
    p _ step = Fix-step step
\end{code}
\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}

\begin{corollary}
Given \AgdaTypeJudge{M}{\AgdaBrackets{\AgdaExtendContext{\AgdaEmptyContext}{σ}}}{τ} and \AgdaTypeJudge{N}{\AgdaEmptyContext}{σ}, it follows that \AgdaAppApr{\AgdaBrackets{\AgdaReplace{M}{N}}}{\AgdaBrackets{\AgdaApp{\AgdaLambda{M}}{N}}}.
\end{corollary}
\begin{proof}
Our proof again follows immediately from \AgdaFunction{⊏̰-lemma}. We provide \AgdaFunction{p}, which is a proof of the property we require the two terms of our applicative approximation to have in order to apply our lemma. To show \AgdaFunction{p}, we assume \AgdaTypeJudge{V}{\AgdaEmptyContext}{τ}, and given \AgdaBigStepPrime{\AgdaBrackets{\AgdaReplace{M}{N}}}{V}, we show \AgdaBigStepPrime{\AgdaBrackets{\AgdaApp{\AgdaLambda{M}}{N}}}{V} by the big-step rule \AgdaInductiveConstructor{·-step}.
\begin{code}
β-⊏̰ : {σ τ : type} {M : PCF (⟨⟩ ’ σ) τ} {N : PCF ⟨⟩ σ} → (M [ N ]) ⊏̰ (ƛ M · N)
β-⊏̰ {_} {τ} {M} {N} = ⊏̰-lemma (M [ N ]) (ƛ M · N) p
  where
    p : (V : PCF ⟨⟩ τ) → (M [ N ]) ⇓' V → (ƛ M · N) ⇓' V
    p _ step = ·-step ƛ-id step
\end{code}
\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}

\subsection{Showing adequacy}
We begin by defining the adequacy relation. For the base case, we take the product with the singleton type \AgdaDatatype{𝟙}, which is a slight hack to ensure our resulting type is in the universe \AgdaFunction{𝓤₁}~\AgdaFunction{̇}, matching the \AgdaPCFType{σ}{σ₁} case. We could have formulated this differently, but in order to stay as close to Streicher's proof as possible and avoid any difficulties, we opt for this solution.
\begin{code}
adequacy-relation : (σ : type) (d : ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩) (M : PCF ⟨⟩ σ) → 𝓤₁ ̇
adequacy-relation ι d M = 𝟙 × ∀ (p : is-defined d) → M ⇓ ℕ-to-ι (value d p)
adequacy-relation (σ ⇒ σ₁) d M = ∀ (e : ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩) (N : PCF ⟨⟩ σ)
                               → adequacy-relation σ e N → adequacy-relation σ₁ (pr₁ d e) (M · N)
\end{code}
\hide{
\begin{code}[hide]
lemma7-1-1 : {σ : type}
          → (d : ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩)
          → (d' : ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩)
          → (d' ⊑⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩ d)
          → (M : PCF ⟨⟩ σ)
          → adequacy-relation σ d M
          → adequacy-relation σ d' M
lemma7-1-1 {ι} d d' x M (_ , o) = * , f
  where
    f : (p : is-defined d') → M ⇓ ℕ-to-ι (value d' p)
    f p = transport (λ - → M ⇓ ℕ-to-ι -) (e₂ ⁻¹) (o (≡-to-is-defined e₁ p))
      where
        e₁ : d' ≡ d
        e₁ = x p
        e₂ : value d' p ≡ value d (≡-to-is-defined e₁ p)
        e₂ = ≡-of-values-from-≡ e₁
lemma7-1-1 {σ ⇒ σ₁} f g x M p = γ
  where
    γ : (d : ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩) →
              Π (λ M₁ → adequacy-relation σ d M₁ → adequacy-relation σ₁ (pr₁ g d) (M · M₁))
    γ d N x₃ = ih
      where
        i : adequacy-relation σ₁ (pr₁ f d) (M · N)
        i = p d N x₃
        ii : pr₁ g d ⊑⟨ ⟪ ⟦ σ₁ ⟧ ⟫ ⟩ pr₁ f d
        ii = x d
        ih : adequacy-relation σ₁ (pr₁ g d) (M · N)
        ih = lemma7-1-1 (pr₁ f d) (pr₁ g d) ii (M · N) i

adequacy-lubs : {σ : type} {I : 𝓤₀ ̇}
             → (u : I → ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩)
             → (isdirec : is-Directed ⟪ ⟦ σ ⟧ ⟫ u)
             → (t : PCF ⟨⟩ σ)
             → ((i : I) → adequacy-relation σ (u i) t)
             → adequacy-relation σ (∐ ⟪ ⟦ σ ⟧ ⟫ isdirec) t
adequacy-lubs {ι} {I} u isdirec t rel = * , g
  where
    g : (p : is-defined (∐ ⟪ ⟦ ι ⟧ ⟫ isdirec)) →
          t ⇓ ℕ-to-ι (value (∐ ⟪ ⟦ ι ⟧ ⟫ isdirec) p)
    g p = ∥∥-rec ∥∥-is-a-prop f p
      where
        f : Σ (λ (i : I) → is-defined (u i)) → t ⇓ ℕ-to-ι (value (∐ ⟪ ⟦ ι ⟧ ⟫ isdirec) p)
        f i = transport (λ - → t ⇓ ℕ-to-ι -) value-lub-is-same (pr₂ (rel (pr₁ i)) (pr₂ i))
          where
            lub-is-same : u (pr₁ i) ≡ ∐ ⟪ ⟦ ι ⟧ ⟫ isdirec
            lub-is-same = ∐-is-upperbound ⟪ ⟦ ι ⟧ ⟫ isdirec (pr₁ i) (pr₂ i)
            value-lub-is-same : value (u (pr₁ i)) (pr₂ i) ≡ value (∐ ⟪ ⟦ ι ⟧ ⟫ isdirec) p
            value-lub-is-same = ≡-of-values-from-≡ lub-is-same
adequacy-lubs {σ ⇒ σ₁} {I} u isdirec t rel p M x = ih
  where
    ptfam : I → ⟨ ⟪ ⟦ σ₁ ⟧ ⟫ ⟩
    ptfam = pointwise-family ⟪ ⟦ σ ⟧ ⟫ ⟪ ⟦ σ₁ ⟧ ⟫ u p
    ptfam-is-directed : is-Directed ⟪ ⟦ σ₁ ⟧ ⟫ ptfam
    ptfam-is-directed = pointwise-family-is-directed ⟪ ⟦ σ ⟧ ⟫ ⟪ ⟦ σ₁ ⟧ ⟫ u isdirec p
    new_rel : (i : I) → adequacy-relation σ₁ (ptfam i) (t · M)
    new_rel i = rel i p M x
    ih : adequacy-relation σ₁ (∐ ⟪ ⟦ σ₁ ⟧ ⟫ ptfam-is-directed) (t · M)
    ih = adequacy-lubs {σ₁} {I} ptfam ptfam-is-directed (t · M) new_rel
        
adequacy-step : {σ : type}
              (M M' : PCF ⟨⟩ σ)
              → M ⊏̰ M'
              → (a : ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩)
              → adequacy-relation σ a M
              → adequacy-relation σ a M'
adequacy-step {ι} M M' r a (* , rel) = * , f
  where
    f : (p : is-defined a) → M' ⇓ ℕ-to-ι (value a p)
    f p = r (pr₁ (pr₂ a) p) (rel p)
adequacy-step {σ ⇒ σ₁} M M' r a rel d M₁ x = ih
  where
    new_rel : adequacy-relation σ₁ (pr₁ a d) (M · M₁)
    new_rel = rel d M₁ x
    ih : adequacy-relation σ₁ (pr₁ a d)
           (M' · M₁)
    ih = adequacy-step (M · M₁) (M' · M₁) (r M₁) (pr₁ a d) new_rel

adequacy-bottom : {σ : type}
                  → (t : PCF ⟨⟩ σ)
                  → adequacy-relation σ (the-least ⟦ σ ⟧) t
adequacy-bottom {ι} t = * , (λ p → 𝟘-elim p)
adequacy-bottom {σ ⇒ σ₁} t = (λ _ M _ → adequacy-bottom (t · M))

lemma8-9 : {σ : type}
          → (M : PCF ⟨⟩ (σ ⇒ σ))
          → (f : ⟨ ⟪ ⟦ σ ⇒ σ ⟧ ⟫ ⟩)
          → adequacy-relation (σ ⇒ σ) f M
          → adequacy-relation σ (pr₁ (μ ⟦ σ ⟧) f) (Fix M)
lemma8-9 {σ} M f rel = adequacy-lubs iter-M iter-M-is-directed (Fix M) fn
  where
    iter-M : ℕ → ⟨ ⟪ ⟦ σ ⟧ ⟫ ⟩
    iter-M n = iter ⟦ σ ⟧ n f
    iter-M-is-directed : is-Directed ⟪ ⟦ σ ⟧ ⟫ iter-M 
    iter-M-is-directed = (pr₁ (iter-is-directed ⟦ σ ⟧)) , order
      where
        order : (i j : ℕ) →
                  ∃
                  (λ k →
                     underlying-order ⟪ ⟦ σ ⟧ ⟫ (iter-M i) (iter-M k) ×
                     underlying-order ⟪ ⟦ σ ⟧ ⟫ (iter-M j) (iter-M k))
        order i j = ∥∥-functor (λ x → (pr₁ x) ,
                                           ((pr₁ (pr₂ x) f) ,
                                           (pr₂ (pr₂ x) f)))
                              (pr₂ (iter-is-directed ⟦ σ ⟧) i j)
    fn : ∀ n → adequacy-relation σ (iter ⟦ σ ⟧ n f) (Fix M)
    fn zero = adequacy-bottom (Fix M)
    fn (succ n) = adequacy-step (M · Fix M) (Fix M) fix-⊏̰ (iter ⟦ σ ⟧ (succ n) f) ih₁
      where
        ih : adequacy-relation σ (iter ⟦ σ ⟧ n f) (Fix M)
        ih = fn n
        ih₁ : adequacy-relation σ (iter ⟦ σ ⟧ (succ n) f) (M · (Fix M))
        ih₁ = rel (iter ⟦ σ ⟧ n f) (Fix M) ih

adequacy-succ :  {n : ℕ} {Γ : Context n}
                 → (M : PCF Γ ι)
                 → (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
                 → (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
                 → adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
                 → adequacy-relation ι (pr₁ ⟦ Succ M ⟧ₑ d) (subst f (Succ M))
adequacy-succ M d f (* , rel) = * , g
  where
    g : (p : is-defined (pr₁ ⟦ Succ M ⟧ₑ d)) →
          subst f (Succ M) ⇓ ℕ-to-ι (value (pr₁ ⟦ Succ M ⟧ₑ d) p)
    g p = ∥∥-functor (λ x → succ-arg x) (rel p)

pred-lemma : ∀ {n : ℕ} {Γ : Context n} {k : ℕ}
      → {M : PCF Γ ι}
      → M ⇓' ℕ-to-ι k
      → (Pred M) ⇓' ℕ-to-ι (pred k)
pred-lemma {n} {Γ} {zero} x = pred-zero x
pred-lemma {n} {Γ} {succ k} x = pred-succ x

ifzero-lemma : ∀ {n : ℕ} {Γ : Context n} {k : ℕ}
      → (M : PCF Γ ι)
      → (M₁ : PCF Γ ι)
      → (M₂ : PCF Γ ι)
      → (f : ∀ {A} → Γ ∋ A → PCF ⟨⟩ A)
      → (subst f M) ⇓ ℕ-to-ι k
      → (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
      → (M-is-defined : is-defined (pr₁ ⟦ M ⟧ₑ d))
      → (result-is-defined : is-defined (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) k))
      → (M₁-rel : adequacy-relation ι (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁))
      → (M₂-rel : adequacy-relation ι (pr₁ ⟦ M₂ ⟧ₑ d) (subst f M₂))
      → subst f (IfZero M M₁ M₂) ⇓ ℕ-to-ι (value (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) k) result-is-defined)
ifzero-lemma {n} {Γ} {zero} M M₁ M₂ f x d M-is-defined result-is-defined (* , M₁-rel) (* , M₂-rel) = γ
  where
    M₁-⇓ : subst f M₁ ⇓ ℕ-to-ι (value (pr₁ ⟦ M₁ ⟧ₑ d) result-is-defined)
    M₁-⇓ = M₁-rel result-is-defined
    γ : subst f (IfZero M M₁ M₂) ⇓ ℕ-to-ι (value (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) zero) result-is-defined)
    γ = ∥∥-functor (λ x → IfZero-zero (pr₁ x) (pr₂ x)) (binary-choice x M₁-⇓)
ifzero-lemma {n} {Γ} {succ k} M M₁ M₂ f x d M-is-defined result-is-defined (* , M₁-rel) (* , M₂-rel) = γ
  where
    M₂-⇓ : subst f M₂ ⇓ ℕ-to-ι (value (pr₁ ⟦ M₂ ⟧ₑ d) result-is-defined)
    M₂-⇓ = M₂-rel result-is-defined
    γ : subst f (IfZero M M₁ M₂) ⇓ ℕ-to-ι (value (⦅ifZero⦆₀ (pr₁ ⟦ M₁ ⟧ₑ d) (pr₁ ⟦ M₂ ⟧ₑ d) (succ k)) result-is-defined)
    γ = ∥∥-functor (λ x → IfZero-succ (pr₁ x) (pr₂ x)) (binary-choice x M₂-⇓)

adequacy-pred :  {n : ℕ} {Γ : Context n}
                 → (M : PCF Γ ι)
                 → (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
                 → (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
                 → adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
                 → adequacy-relation ι (pr₁ ⟦ Pred M ⟧ₑ d) (subst f (Pred M))
adequacy-pred M d f (* , rel) = * , g
  where
    g : (p : is-defined (pr₁ ⟦ Pred M ⟧ₑ d)) →
          subst f (Pred M) ⇓ ℕ-to-ι (value (pr₁ ⟦ Pred M ⟧ₑ d) p)
    g p = ∥∥-functor pred-lemma (rel p)
    
adequacy-ifzero :   {n : ℕ} {Γ : Context n}
                 → (M : PCF Γ ι) (M₁ : PCF Γ ι) (M₂ : PCF Γ ι)
                 → (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
                 → (f : ∀ {A} → (x : Γ ∋ A) → PCF ⟨⟩ A)
                 → adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
                 → adequacy-relation ι (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁)
                 → adequacy-relation ι (pr₁ ⟦ M₂ ⟧ₑ d) (subst f M₂)
                 → adequacy-relation ι (pr₁ ⟦ IfZero M M₁ M₂ ⟧ₑ d) (subst f (IfZero M M₁ M₂))
adequacy-ifzero {n} {Γ} M M₁ M₂ d f (* , M-rel) M₁-rel M₂-rel = * , g
  where
    g : (p : is-defined (pr₁ ⟦ IfZero M M₁ M₂ ⟧ₑ d)) →
          subst f (IfZero M M₁ M₂) ⇓
          ℕ-to-ι (value (pr₁ ⟦ IfZero M M₁ M₂ ⟧ₑ d) p)
    g (M-is-defined , result-is-defined) = ifzero-lemma M M₁ M₂ f (M-rel M-is-defined) d M-is-defined result-is-defined M₁-rel M₂-rel
\end{code}
}

We first state some lemmas, which we rely on in our proof. The proofs are shown by Streicher \cite[Section~7]{domaintheoreticfoundations}, and they translate into Agda without much difficulty. As such, we omit the proofs for brevity.
\begin{lemma}
Given a context \AgdaBound{Γ}, \AgdaTypeJudge{M}{Γ}{σ}, \AgdaType{\AgdaBound{d}\AgdaSpace{}\AgdaBound{d'}}{\AgdaExtractSet{\AgdaExtractDCPO{\AgdaTypeInterp{σ}}}}, if \AgdaDcpoOrdering{d}{\AgdaExtractDCPO{\AgdaTypeInterp{σ}}}{d'} and \AdequacyRel{σ}{d}{M}, then \AdequacyRel{σ}{d'}{M}. 
\end{lemma}
\begin{lemma}
Given a directed family \AgdaType{\AgdaBound{α}}{\AgdaFun{I}{\AgdaExtractSet{\AgdaExtractDCPO{\AgdaTypeInterp{σ}}}}}, a proof \AgdaBound{δ} that \AgdaBound{α} is directed, and a term \AgdaTypeJudge{M}{\AgdaEmptyContext}{σ}, if for all \AgdaType{i}{I} it holds that \AdequacyRel{σ}{\AgdaBrackets{\AgdaBound{α}\AgdaSpace{}\AgdaBound{i}}}{M}, then it follows that \AdequacyRel{σ}{\AgdaBrackets{\AgdaUpperBound{\AgdaExtractDCPO{\AgdaTypeInterp{σ}}}{δ}}}{M}.
\end{lemma}
\begin{lemma}
For every \AgdaTypeJudge{M}{\AgdaEmptyContext}{σ}, \AdequacyRel{σ}{\AgdaBrackets{\AgdaFunction{the-least}\AgdaSpace{}\AgdaExtractDCPO{\AgdaTypeInterp{σ}}}}{M}.
\end{lemma}
\begin{lemma}
\label{adequacy-step}
For \AgdaTypeJudge{M}{\AgdaEmptyContext}{σ}, \AgdaTypeJudge{M'}{\AgdaEmptyContext}{σ}, \AgdaType{d}{\AgdaExtractSet{\AgdaExtractDCPO{\AgdaTypeInterp{σ}}}}, if \AdequacyRel{σ}{d}{M} and \AgdaAppApr{M}{M'}, then \AdequacyRel{σ}{d}{M'}.
\end{lemma}
\begin{lemma}
\label{fix-from-f-lemma}
For a given \AgdaTypeJudge{M}{\AgdaEmptyContext}{\AgdaBrackets{\AgdaPCFType{σ}{σ}}}, and \AgdaType{f}{\AgdaExtractSet{\AgdaExtractDCPO{\AgdaTypeInterp{\AgdaPCFType{σ}{σ}}}}}, if \AdequacyRel{\AgdaBrackets{\AgdaPCFType{σ}{σ}}}{f}{M}, then \AdequacyRel{σ}{\AgdaBrackets{\AgdaField{pr₁}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{μ}\AgdaSpace{}\AgdaTypeInterp{σ}}\AgdaSpace{}\AgdaBound{f}}}{\AgdaBrackets{\AgdaFix{M}}}.
\end{lemma}

We can now begin to look at the main lemma we need for showing computational adequacy.
\begin{lemma}\label{mainlemma}
Given \AgdaTypeJudge{M}{Γ}{τ}, a list of values \AgdaType{d}{\AgdaExtractSet{\AgdaExtractDCPO{\AgdaContextInterp{Γ}}}}, and a mapping \AgdaBound{f} from variables in \AgdaBound{Γ} to closed terms, if for each variable \AgdaBound{i} in \AgdaBound{Γ} it is true that \AgdaFunction{extract}\AgdaSpace{}\AgdaBound{i}\AgdaSpace{}\AgdaBound{d} and \AgdaBound{f}\AgdaSpace{}\AgdaBound{i} are related by the adequacy relation, then \AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaBound{d} and \AgdaFunction{subst}\AgdaSpace{}\AgdaBound{f}\AgdaSpace{}\AgdaBound{M} are related by the adequacy relation.
\end{lemma}
\begin{proof}
As in Streicher's proof, we will only show the most interesting cases.
We begin by formulating the type of what we are trying to prove. This closely resembles the statement of the lemma.
\begin{AgdaAlign}
\begin{code}
main-lemma : {n : ℕ} {Γ : Context n} {τ : type} (M : PCF Γ τ) (d : ⟨ ⟪ 【 Γ 】 ⟫ ⟩)
           → (f : ∀ {A} → (i : Γ ∋ A) → PCF ⟨⟩ A)
           → (g : ∀ {A} → (i : Γ ∋ A) → adequacy-relation A (extract i d) (f i))
           → adequacy-relation τ (pr₁ ⟦ M ⟧ₑ d) (subst f M)
\end{code}
We show this by induction on \AgdaBound{M}. However, we will only explore the lambda abstraction, variable, and fixed-point combinator cases, as the rest, as Streicher suggests, go through without pain.

Our variable case follows immediately from our assumption \AgdaBound{g}.
\begin{code}
main-lemma (v x) d f g = g x
\end{code}
Next, we consider the \AgdaInductiveConstructor{Fix} case. From our inductive hypothesis, we have that \AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaBound{d} and \AgdaFunction{subst}\AgdaSpace{}\AgdaBound{f}\AgdaSpace{}\AgdaBound{M} are related by the adequacy relation. Therefore, we can apply \cref{fix-from-f-lemma} to conclude our proof.
\begin{code}
main-lemma {_} {_} {σ} (Fix M) d f g = lemma8-9 (subst f M) (pr₁ ⟦ M ⟧ₑ d) ih
  where
    ih : adequacy-relation (σ ⇒ σ) (pr₁ ⟦ M ⟧ₑ d) (subst f M)
    ih = main-lemma M d f g
\end{code}
We now consider the lambda abstraction case. Since the type of \AgdaLambda{M} is \AgdaPCFType{σ}{τ}, by the definition of \AgdaFunction{adequacy-relation} we further assume \AgdaType{d₁}{\AgdaExtractSet{\AgdaExtractDCPO{\AgdaTermInterp{σ}}}}, \AgdaTypeJudge{M₁}{\AgdaEmptyContext}{σ}, and \AgdaType{rel}{\AdequacyRel{σ}{d₁}{M₁}} on top of our previous assumptions. Our goal is to show that \AgdaField{pr₁}\AgdaSpace{}\AgdaBrackets{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{\AgdaLambda{M}}\AgdaSpace{}\AgdaBound{d}}\AgdaSpace{}\AgdaBound{d₁} and \AgdaApp{\AgdaFunction{subst}\AgdaSpace{}\AgdaBound{f}\AgdaSpace{}\AgdaBrackets{\AgdaLambda{M}}}{M₁} are related by the adequacy relation, which we give the name \AgdaFunction{γ}.
\begin{code}
main-lemma (ƛ {_} {Γ} {σ} {τ} M) d f g d₁ M₁ rel = γ
  where
\end{code}
Our first step in the proof is to apply our inductive hypothesis. Since \AgdaBound{M} is under the context \AgdaExtendContext{Γ}{σ}, we need to supply a mapping from each variable in this extended context to a closed term. We do this via mapping \AgdaInductiveConstructor{Z} to \AgdaBound{M₁}, and \AgdaInductiveConstructor{S}\AgdaSpace{}\AgdaBound{x} to \AgdaBound{f}\AgdaSpace{}\AgdaBound{x}, which is the function of \AgdaFunction{extend-with}\AgdaSpace{}\AgdaBound{M₁}\AgdaSpace{}\AgdaBound{f}. We also need to provide a proof that each of these mappings of variables is related to their respective values under the adequacy relation, which we call \AgdaFunction{ext-g}.
\begin{code}
    ih : adequacy-relation τ (pr₁ (pr₁ ⟦ ƛ M ⟧ₑ d) d₁) (subst (extend-with M₁ f) M)
    ih = main-lemma M (d , d₁) (extend-with M₁ f) ext-g 
      where
\end{code}
To construct \AgdaFunction{ext-g}, we perform induction on the lookup judgement. The base case is trivial, it is provided by our assumption \AgdaBound{rel}. The inductive case is also trivial, as these are just the variables which were in the context \AgdaBound{Γ}, and our assumption \AgdaBound{g} states the property holds for each of these.
\begin{code}
        ext-g : ∀ {A} → (x : (Γ ’ σ) ∋ A)
                      → adequacy-relation A (extract x (d , d₁)) (extend-with M₁ f x)
        ext-g Z = rel
        ext-g (S x) = g x
\end{code}
We next show \AgdaFunction{i}, an equality \AgdaEq{\AgdaFunction{subst}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{extend-with}\AgdaSpace{}\AgdaBound{M₁}\AgdaSpace{}\AgdaBound{f}}\AgdaSpace{}\AgdaBound{M}}{\AgdaReplace{\AgdaBrackets{\AgdaFunction{subst}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{exts}\AgdaSpace{}\AgdaBound{f}}\AgdaSpace{}\AgdaBound{M}}}{M₁}} which is mentioned simply without proof by Streicher \cite[Lemma~7.4]{domaintheoreticfoundations}. This is another example of the differences when proving properties with a proof assistant. Whilst mentioned trivially on paper, constructing \AgdaFunction{subst-ext} in Agda relied on many lemmas. The resulting lines of code were in the hundreds, as we were forced to convince Agda that the equality is true.
\begin{code}
    i : subst (extend-with M₁ f) M ≡ (subst (exts f) M) [ M₁ ]
    i = subst-ext M M₁ f
\end{code}
From \AgdaFunction{β-⊏̰}, we have that \AgdaAppApr{\AgdaReplace{\AgdaBrackets{\AgdaFunction{subst}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{exts}\AgdaSpace{}\AgdaBound{f}}\AgdaSpace{}\AgdaBound{M}}}{M₁}}{\AgdaApp{\AgdaLambda{\AgdaBrackets{\AgdaFunction{subst}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{exts}\AgdaSpace{}\AgdaBound{f}}\AgdaSpace{}\AgdaBound{M}}}}{M₁}}. We are then able to prove \AgdaAppApr{\AgdaFunction{subst}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{extend-with}\AgdaSpace{}\AgdaBound{M₁}\AgdaSpace{}\AgdaBound{f}}\AgdaSpace{}\AgdaBound{M}}{\AgdaApp{\AgdaLambda{\AgdaBrackets{\AgdaFunction{subst}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{exts}\AgdaSpace{}\AgdaBound{f}}\AgdaSpace{}\AgdaBound{M}}}}{M₁}} by transporting the equality \AgdaFunction{i} with the property shown by \AgdaFunction{β-⊏̰}. By definition, \AgdaFunction{subst}\AgdaSpace{}\AgdaBound{f}\AgdaSpace{}\AgdaBrackets{\AgdaLambda{M}} is the same as \AgdaLambda{\AgdaBrackets{\AgdaFunction{subst}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{exts}\AgdaSpace{}\AgdaBound{f}}\AgdaSpace{M}}}, so we have also shown \AgdaAppApr{\AgdaFunction{subst}\AgdaSpace{}\AgdaBrackets{\AgdaFunction{extend-with}\AgdaSpace{}\AgdaBound{M₁}\AgdaSpace{}\AgdaBound{f}}\AgdaSpace{}\AgdaBound{M}}{\AgdaBrackets{\AgdaApp{\AgdaBrackets{\AgdaFunction{subst}\AgdaSpace{}\AgdaBound{f}\AgdaSpace{}\AgdaBrackets{\AgdaLambda{M}}}}{M₁}}}, which is our proof \AgdaFunction{ii}. 
\begin{code}
    ii : subst (extend-with M₁ f) M ⊏̰ ((subst f (ƛ M)) · M₁)
    ii = back-transport (λ - → - ⊏̰ ((subst f (ƛ M)) · M₁)) i β-⊏̰
\end{code}
Finally, we apply \cref{adequacy-step} to conclude our proof.
\begin{code}
    γ : adequacy-relation τ (pr₁ (pr₁ ⟦ ƛ M ⟧ₑ d) d₁) ((subst f (ƛ M)) · M₁)
    γ = adequacy-step (subst (extend-with M₁ f) M) ((subst f (ƛ M)) · M₁) ii (pr₁ ⟦ M ⟧ₑ (d , d₁)) ih
\end{code}
\end{AgdaAlign}
\AgdaNoSpaceAroundCode{
\begin{code}[hide]
main-lemma {n} {Γ} {.ι} Zero d f g = * , λ p → ∣ zero-id ∣

main-lemma {n} {Γ} {.ι} (Succ M) d f g = adequacy-succ M d f ih
  where
    ih : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
    ih = main-lemma M d f g

main-lemma {n} {Γ} {.ι} (Pred M) d f g = adequacy-pred M d f ih
  where
    ih : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
    ih = main-lemma M d f g

main-lemma {n} {Γ} {.ι} (IfZero M M₁ M₂) d f g = adequacy-ifzero M M₁ M₂ d f ih₀ ih₁ ih₂
  where
    ih₀ : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ d) (subst f M)
    ih₀ = main-lemma M d f g
    ih₁ : adequacy-relation ι (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁)
    ih₁ = main-lemma M₁ d f g
    ih₂ : adequacy-relation ι (pr₁ ⟦ M₂ ⟧ₑ d) (subst f M₂)
    ih₂ = main-lemma M₂ d f g
main-lemma (_·_ {n} {Γ} {σ} {σ₁} M M₁) d f g = ih₀ (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁) ih₁
  where
    ih₀ : adequacy-relation (σ ⇒ σ₁) (pr₁ ⟦ M ⟧ₑ d) (subst f M)
    ih₀ = main-lemma M d f g
    ih₁ : adequacy-relation σ (pr₁ ⟦ M₁ ⟧ₑ d) (subst f M₁)
    ih₁ = main-lemma M₁ d f g
\end{code}
}
\vspace{-3.3em}\[\tag*{\qedhere}\]
\end{proof}
Adequacy now follows from \AgdaFunction{main-lemma} simply.
\begin{theorem}[Adequacy]
If the interpretation of a term \AgdaTypeJudge{M}{\AgdaEmptyContext}{\AgdaInductiveConstructor{ι}} is equal to \AgdaFunction{η}\AgdaSpace{}\AgdaBound{n}, for some natural number \AgdaBound{n}, then there exists a reduction such that \AgdaBigStep{M}{\AgdaFunction{ℕ-to-ι}\AgdaSpace{}\AgdaBound{n}}.
\end{theorem}

\begin{proof}
We develop a proof \AgdaFunction{γ} that the adequacy relation holds between \AgdaFunction{η}\AgdaSpace{}\AgdaBound{n} and \AgdaBound{M}. From this, it becomes trivial to show \AgdaBigStep{M}{\AgdaFunction{ℕ-to-ι}\AgdaSpace{}\AgdaBound{n}}, as a proof that \AgdaFunction{η}\AgdaSpace{}\AgdaBound{n} is defined is the unique element \AgdaInductiveConstructor{*} of the type \AgdaDatatype{𝟙}, as the total elements of the lifted set are always defined.
\begin{AgdaAlign}
\begin{code}
adequacy : (M : PCF ⟨⟩ ι) (n : ℕ) → pr₁ ⟦ M ⟧ₑ * ≡ η n → M ⇓ ℕ-to-ι n
adequacy M n eq = pr₂ γ *
  where
\end{code}
We first apply \AgdaFunction{main-lemma}. We provide the identity substitution \AgdaFunction{ids}, which is the unique substitution we can provide for a term with no free variables. A proof that each term in the empty context is related to its extraction from the empty context is trivial, as there is no case for \AgdaEmptyContext\AgdaSpace{}\AgdaDatatype{∋}\AgdaSpace{}\AgdaBound{A}. In Agda, \AgdaBrackets{} represents the absurd case. We conclude \AgdaFunction{i}, that the adequacy relation holds between the interpretation of \AgdaBound{M} and the identity substitution applied to \AgdaBound{M}.
\begin{code}
    i : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ *) (subst ids M)
    i = main-lemma M * ids f
      where
        f : ∀ {A} → (x : ⟨⟩ ∋ A) → adequacy-relation A (extract x *) (v x)
        f ()
\end{code}
We next apply the proof that the identity substitution is equal to the original term, specifically that \AgdaEq{\AgdaFunction{subst}\AgdaSpace{}\AgdaFunction{ids}\AgdaSpace{}\AgdaBound{M}}{M}. Like we have previously, we transport this equality to achieve a proof \AgdaFunction{ii} that the adequacy relation must hold between the interpretation of \AgdaBound{M} and the term \AgdaBound{M}.
\begin{code}
    ii : adequacy-relation ι (pr₁ ⟦ M ⟧ₑ *) M
    ii = transport (adequacy-relation ι (pr₁ ⟦ M ⟧ₑ *)) (sub-id M) i 
\end{code}
Finally, we can then prove the adequacy relation holds between \AgdaFunction{η}\AgdaSpace{}\AgdaBound{n} and \AgdaBound{M}. We use our assumption \AgdaBound{eq} that \AgdaEq{\AgdaField{pr₁}\AgdaSpace{}\AgdaTermInterp{M}\AgdaSpace{}\AgdaInductiveConstructor{*}}{\AgdaFunction{η}\AgdaSpace{}\AgdaBound{n}}.
\begin{code}
    γ : adequacy-relation ι (η n) M
    γ = transport (λ - → adequacy-relation ι - M) eq ii
\end{code}
\end{AgdaAlign}\vspace{-3.5em}\[\tag*{\qedhere}\]
\end{proof}

\end{document}
