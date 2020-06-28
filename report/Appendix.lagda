\documentclass[main.tex]{subfiles}

\begin{code}[hide]
open import UF-PropTrunc
open import SpartanMLTT

module Appendix 
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓥 : Universe)
       where

open import Dcpo pt fe 𝓥
open import DcpoConstructions pt fe
open DcpoConstructionsGeneral 𝓥

open import DcpoProducts pt fe
open DcpoProductsGeneral 𝓥
open import DcpoProducts-Continuity pt fe 𝓥
\end{code}

\begin{document}

\section{Type Checking}
The source code is verified to type check with Agda 2.6.0.1. It can not be guaranteed that the source code for this project will not encounter errors, such as unknown flags or syntax errors, with other versions. The full source code for this project can be found at \url{https://git-teaching.cs.bham.ac.uk/mod-ug-proj-2019/bxh538}. The source files can be found in the \texttt{src} folder, with the \texttt{.lagda} file extension.

Upon retrieval of the source code, individual files can be type checked by running:
\begin{lstlisting}[language=bash]
 $ agda <path-to-file>
\end{lstlisting} 
This will also ensure any imported files are type checked.

However, when exploring Agda code, we tend to use Emacs. There is the Agda mode for Emacs which adds functionality to Emacs for interacting with Agda files, such as loading an opened Agda file. Instructions for setting this up can be found at the \href{https://my-agda.readthedocs.io/en/latest/getting-started/installation.html}{Agda documentation}.

After opening an Agda file in Emacs, it can then be type checked with \texttt{Ctrl-c Ctrl-l}. A more detailed list of the Agda mode for Emacs can be found at \url{https://agda.readthedocs.io/en/v2.6.0.1/tools/emacs-mode.html}.

\section{Codebase Statistics}
\label{appendix:codestats}
We make use of Tom de Jong's foundations in domain theory, as well as formalisations of homotopy type theory by Mart\'in Escard\'o et al. The existing codebase is currently hosted at \url{https://www.cs.bham.ac.uk/~mhe/agda-new/}. The contributors are found at the beginning of each file as a comment.

We have added the following to the existing codebase:
\begin{itemize}
\item 4338 lines, approx. 11\% increase.
\item 375631 characters, approx. 14\% increase.
\item 18 new files, approx. 12\% increase.
\end{itemize}

\section{Shortening of Proofs}
\label{appendix:shorterproofs}
Below is an example of the simplification of the proof of \AgdaFunction{eval}, where we simplify the proof of continuity in the first argument to a single line.

First, our original \AgdaFunction{eval} proof:
\begin{code}[hide]
module _ (𝓓 : DCPO {𝓤} {𝓤'})
         (𝓔 : DCPO {𝓣} {𝓣'})
       where
\end{code}
\begin{code}
  eval-original : DCPO[ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓 , 𝓔 ]
  eval-original = f , c
    where
      f : ⟨ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓 ⟩ → ⟨ 𝓔 ⟩
      f (g , d) = underlying-function 𝓓 𝓔 g d
      f-is-monotone : is-monotone ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓) 𝓔 f
      f-is-monotone (g₁ , d₁) (g₂ , d₂) (g₁⊑g₂ , d₁⊑d₂) =
                     f (g₁ , d₁) ⊑⟨ 𝓔 ⟩[ continuous-functions-are-monotone 𝓓 𝓔 g₁ d₁ d₂ d₁⊑d₂ ]
                     f (g₁ , d₂) ⊑⟨ 𝓔 ⟩[ g₁⊑g₂ d₂ ]
                     f (g₂ , d₂) ∎⟨ 𝓔 ⟩
        
      c : is-continuous ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓) 𝓔 f
      c = continuous-in-arguments→continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) 𝓓 𝓔 f continuous₁ continuous₂
        where
          continuous₁ : (e : ⟨ 𝓓 ⟩) → is-continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) 𝓔 (λ d → f (d , e))
          continuous₁ d I α δ = u , v
            where
              u : is-upperbound (underlying-order 𝓔) (f (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ , d))
                                                              (λ z → f (α z , d))
              u i = f-is-monotone (α i , d) (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ , d)
                                  (∐-is-upperbound (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ i , reflexivity 𝓓 d)
              v : (u₁ : ⟨ 𝓔 ⟩) →
                    ((i : I) → f (α i , d) ⊑⟨ 𝓔 ⟩ u₁) →
                    f (∐ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) {I} {α} δ , d) ⊑⟨ 𝓔 ⟩ u₁
              v u₁ p = ∐-is-lowerbound-of-upperbounds 𝓔 isdir₁ u₁ p
                where
                  isdir₁ : is-Directed 𝓔 (pointwise-family 𝓓 𝓔 α d)
                  isdir₁ = pointwise-family-is-directed 𝓓 𝓔 α δ d
                  
          continuous₂ : (d : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟩) → is-continuous 𝓓 𝓔 (λ e → f (d , e))
          continuous₂ g I α δ = u , v
            where
              u : is-upperbound (underlying-order 𝓔) (f (g , ∐ 𝓓 δ)) (λ z → f (g , α z))
              u i = f-is-monotone (g , α i) (g , ∐ 𝓓 δ)
                                  ((reflexivity (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) g) , (∐-is-upperbound 𝓓 δ i))
              v : (u₁ : ⟨ 𝓔 ⟩) →
                    ((i : I) → f (g , α i) ⊑⟨ 𝓔 ⟩ u₁) → f (g , ∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ u₁
              v u₁ p = transport (λ - → - ⊑⟨ 𝓔 ⟩ u₁) (e₁ ⁻¹) p₁
                where
                  e₁ : f (g , ∐ 𝓓 δ) ≡ ∐ 𝓔 (image-is-directed 𝓓 𝓔 g δ)
                  e₁ = continuous-function-∐-≡ 𝓓 𝓔 g δ
                  p₁ : (∐ 𝓔 (image-is-directed 𝓓 𝓔 g δ)) ⊑⟨ 𝓔 ⟩ u₁
                  p₁ = ∐-is-lowerbound-of-upperbounds 𝓔 (image-is-directed 𝓓 𝓔 g δ) u₁ p
\end{code}
Next, we present the shorter proof:
\begin{code}
  eval : DCPO[ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓 , 𝓔 ]
  eval = f , c
    where
      f : ⟨ (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓 ⟩ → ⟨ 𝓔 ⟩
      f (g , d) = underlying-function 𝓓 𝓔 g d
      f-is-monotone : is-monotone ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓) 𝓔 f
      f-is-monotone (g₁ , d₁) (g₂ , d₂) (g₁⊑g₂ , d₁⊑d₂) =
                     f (g₁ , d₁) ⊑⟨ 𝓔 ⟩[ continuous-functions-are-monotone 𝓓 𝓔 g₁ d₁ d₂ d₁⊑d₂ ]
                     f (g₁ , d₂) ⊑⟨ 𝓔 ⟩[ g₁⊑g₂ d₂ ]
                     f (g₂ , d₂) ∎⟨ 𝓔 ⟩
      c : is-continuous ((𝓓 ⟹ᵈᶜᵖᵒ 𝓔) ×ᵈᶜᵖᵒ 𝓓) 𝓔 f
      c = continuous-in-arguments→continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) 𝓓 𝓔 f continuous₁ continuous₂
        where 
          continuous₁ : (d : ⟨ 𝓓 ⟩) → is-continuous (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) 𝓔 (λ g → f (g , d))
          continuous₁ d I α δ = ∐-is-sup 𝓔 (pointwise-family-is-directed 𝓓 𝓔 α δ d)
          continuous₂ : (g : ⟨ 𝓓 ⟹ᵈᶜᵖᵒ 𝓔 ⟩) → is-continuous 𝓓 𝓔 (λ d → f (g , d))
          continuous₂ g I α δ = u , l
            where
              u : is-upperbound (underlying-order 𝓔) (f (g , ∐ 𝓓 δ)) (λ z → f (g , α z))
              u i = f-is-monotone (g , α i) (g , ∐ 𝓓 δ)
                                  ((reflexivity (𝓓 ⟹ᵈᶜᵖᵒ 𝓔) g) , (∐-is-upperbound 𝓓 δ i))
              l : (u₁ : ⟨ 𝓔 ⟩) → ((i : I) → f (g , α i) ⊑⟨ 𝓔 ⟩ u₁) → f (g , ∐ 𝓓 δ) ⊑⟨ 𝓔 ⟩ u₁
              l u₁ p = transport (λ - → - ⊑⟨ 𝓔 ⟩ u₁) (i ⁻¹) ii
                where
                  i : f (g , ∐ 𝓓 δ) ≡ ∐ 𝓔 (image-is-directed 𝓓 𝓔 g δ)
                  i = continuous-function-∐-≡ 𝓓 𝓔 g δ
                  ii : (∐ 𝓔 (image-is-directed 𝓓 𝓔 g δ)) ⊑⟨ 𝓔 ⟩ u₁
                  ii = ∐-is-lowerbound-of-upperbounds 𝓔 (image-is-directed 𝓓 𝓔 g δ) u₁ p
\end{code}
\end{document}
