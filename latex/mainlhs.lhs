\documentclass{article}
\usepackage[a4paper,margin=25mm,
% left=40mm,right=40mm
]{geometry}
\usepackage{apacite}
\usepackage{natbib}
\usepackage{listings}
\usepackage{tikz-cd}
\usepackage{float}
\usepackage{amsmath}
\usepackage{agda}
\usepackage[colorlinks=true,allcolors=blue]{hyperref}
%include lhs2TeX.fmt

\renewcommand{\tt}[1]{\texttt{#1}}
\usepackage{stmaryrd}
\newcommand{\catam}[1]{\llparenthesis #1 \rrparenthesis}
\newcommand{\anam}[1]{\llbracket #1 \rrbracket}
\usepackage[utf8]{inputenc}
\usepackage{newunicodechar}
%include agda_chars.tex
%include hs_chars.tex


\title{Master's Thesis}
\author{Eben Rogers}

\begin{document}

\maketitle
\tableofcontents


%include sections/10_introduction.lhs.tex
%include sections/20_background.lhs.tex
\input{sections/30_formalization}
\input{sections/40_haskell_optimizations}
\input{sections/50_conclusion}


\bibliographystyle{apacite}
\bibliography{references.bib}

\iffalse
\section{Outline}
\begin{itemize}
    \item Introduction
    \item Background
    \item Formalization work and structure
    \item Implementation of Haskell generator code?
    \item Conclusion
\end{itemize}
\fi

\iffalse
\section{Project plan}
\begin{itemize}
    \item \cite{Harper2011}'s guide for implementing shortcut fusion through Church encodings is useful.
    This paper aims to do the following:
    \begin{itemize}
        \item  Formalize the proofs present in \cite{Harper2011}'s work in Agda.
        \item  Investigate whether it is possible to mechanically generate Church encodings of arbitrary functors (initial algebra datastructures) in Haskell.
        (Probably, but why would you?...)
    \end{itemize}
\end{itemize}
\fi

\end{document}