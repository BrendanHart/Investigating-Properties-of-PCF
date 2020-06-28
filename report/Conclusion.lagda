\documentclass[main.tex]{subfiles}

\begin{document}

\section{Conclusion}
Our investigations have shown the differences at times between paper proofs and proofs in a proof assistant. We have seen times where we have had to focus on formalising proofs which are not always detailed in texts, which our proof assistant required us to formalise.

We began by formalising the PCF types and terms in \cref{PCF}. We decided upon our choice of variables, considering the difference between de Bruijn indices and named variables in \cref{representing-variables}. We next moved on to define substitution and the operational semantics in \cref{OpSem}. Following this, we looked at PCF through a more mathematical lens. In \cref{domaintheory}, we built upon Tom de Jong's existing formalisations of domain theory to provide us with a framework to define the Scott model of PCF in \cref{scottmodel}. We then showed that the operational semantics are correct with respect to the Scott model in \cref{correctness}, and finally that the Scott model is computationally adequate with respect to the operational semantics in \cref{adequacy}.

The difference between paper proofs and using a proof assistant was particularly apparent in \cref{sublem} when formalising the substitution lemma and \cref{applicativeapprox} when formalising lemmas surrounding the applicative approximation relation. There were either no proofs for these lemmas, or the proof did not directly translate into Agda. As a result, we had to spend extra time developing these proofs, whereas if we weren't using a proof assistant we would probably have relied upon these statements as true. Whilst we managed to prove them, it is not impossible that we could come across situations similar to as Gouëzel did \cite{GOUEZEL20191258} where we come across a statement which does not hold. As a result, we have highlighted that a proof assistant requires explicit proofs of all properties and steps involved, whereas a paper proof may be more likely to leave out proofs or rely on assumptions which could turn out to be false.
\end{document}
