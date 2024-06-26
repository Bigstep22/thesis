\documentclass[titlepage]{article}
\usepackage[T1]{fontenc}
\usepackage[a4paper,margin=25mm,
% left=35mm,right=35mm
]{geometry}
\usepackage[nottoc,numbib]{tocbibind}
\usepackage{svg}
\usepackage{apacite}
\usepackage{natbib}
\usepackage{listings}
\usepackage{tikz-cd}
\usepackage{float}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{agda}
\usepackage{subcaption}
\usepackage{enumitem}
\usepackage{epstopdf}
\usepackage{changepage}
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

\setcounter{tocdepth}{2}
\newcommand{\changelocaltocdepth}[1]{%
  \addtocontents{toc}{\protect\setcounter{tocdepth}{#1}}%
  \setcounter{tocdepth}{#1}%
}

\def\sectionautorefname{Section}
\def\subsectionautorefname{Section}
\def\subsubsectionautorefname{Section}


\begin{document}

\input{sections/04_titlepage}
\input{sections/06_abstract}
\begingroup
  \hypersetup{hidelinks}
  \tableofcontents
\endgroup
\pagebreak


%include sections/10_introduction.lhs.tex
%include sections/20_background.lhs.tex
\changelocaltocdepth{3}
%include sections/30_haskell_optimizations.lhs.tex
\input{sections/40_formalization}
\input{sections/48_related_works}
\input{sections/50_conclusion}
\bibliographystyle{apacite}
\bibliography{references.bib}
\changelocaltocdepth{1}
\appendix
%include sections/90_appendix.lhs.tex


\end{document}

