agda --latex report/Introduction.lagda &&
agda --latex report/Background.lagda &&
agda --latex report/PCF-Chapter.lagda &&
agda --latex report/OpSem.lagda &&
agda --latex report/DomainTheory.lagda &&
agda --latex report/ScottModel.lagda &&
agda --latex report/Correctness.lagda &&
agda --latex report/Adequacy.lagda &&
agda --latex report/Evaluation.lagda &&
agda --latex report/Conclusion.lagda &&
agda --latex report/Appendix.lagda &&
cd latex
xelatex --shell-escape -interaction=nonstopmode main.tex
biber main
xelatex --shell-escape -interaction=nonstopmode main.tex 
