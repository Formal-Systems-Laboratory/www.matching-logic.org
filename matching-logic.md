---
title: Matching Logic and Langauges
classoption:
-   sigplan
-   10pt
-   anonymous
-   review
pandoc-latex-environment:
    definition: [definition]
    theorem: [theorem]
    lemma: [lemma]
abstract:
    We axiomatize a theory of words in matching logic.
    Within this axiomatization, we define a shallow embedding for regular expressions
    and a representation for the language of DFAs.
    This enables us to write a certificate-generating implementation of Brzozowski's method.
    This certificate is a matching logic proof that only relies on the fifteen proof rules of matching logic,
    and twelve axioms for this theory of words.
---


\renewcommand{\phi}{\varphi}
\renewcommand{\subset}{\subseteq}
\newcommand{\der}[2]{{\delta_{#1}(#2)}}
\newcommand{\matches}[2]{\mathrm{matches}(#1, #2)}
\newcommand{\N}             {\mathbb N} 
\renewcommand{\P}           {\mathcal P} 
\newcommand{\union}         {\cup}
\newcommand{\Union}         {\bigcup}
\newcommand{\intersection}  {\cap}
\newcommand{\Intersection}  {\bigcap}
\newcommand{\lfp}           {\mathrm{lfp}}
\newcommand{\gfp}           {\mathrm{gfp}}
\newcommand{\lOr}{\bigvee}
\newcommand{\lAnd}{\bigwedge}
\newcommand{\limplies}{\mathbin{\to}}
\newcommand{\liff}{\leftrightarrow}
\newcommand{\eval}[1]{|{#1}|}
\newcommand{\dsigma}{\bar\sigma}
\newcommand{\arity}[1]{\mathrm{arity}(#1)}
\newcommand{\inhabitants}[1]{\top_{#1}}
\newcommand{\prule}[1]{(\textsc{#1})}
\newcommand{\prop}[1]{propagation$_{#1}$}
\newcommand{\hole}{\square}
\newcommand{\cimplies}{\multimap}
\newcommand{\ceil}[1]{\lceil #1 \rceil}
\newcommand{\floor}[1]{\lfloor #1 \rfloor}
\newcommand{\proves}{\vdash}
\newcommand{\satisfies}{\vDash}
\newcommand {\parens}[1]{\left(#1\right)}
\newcommand {\curly}[1]{\left\{#1\right\}}
\newcommand{\free}{\mathrm{free}}
\newcommand{\EVar}{\mathop{\mathrm{EVar}}}
\newcommand{\SVar}{\mathop{\mathrm{SVar}}}
\newcommand{\Csigma}{C_\sigma}
\newcommand{\kleene}{^*}
\newcommand{\concat}{\cdot}
\newcommand{\word}{\mathrm{Word}}
\newcommand{\letter}{\mathrm{Letter}}
\newcommand{\GRE}{\Gamma_\word}
\newcommand{\recurse}[2]{\mathrm{recurse}(#2)[#1]}
\newcommand{\minLength}[1]{\mathrm{minLength}(#1)}
\newcommand{\SubstFP}{\Theta}
\newcommand{\SubstMG}{\Lambda}
\newcommand{\Unfold}{\mathrm{U}}
\newcommand{\substunfold}{\Unfold}
\newcommand{\rootn}{\mathcal{R}}
\newcommand{\pathto}{\mathit{path}}
\newcommand{\pat}{{\mathfrak{pat}}}
\newcommand {\ewp}[1]{\mathrm{ewp}(#1)}
\newcommand {\isEmpty}[1]{\mathrm{isEmpty}(#1)}
\newcommand {\true} {\mathrm{true}}
\newcommand {\false} {\mathrm{false}}
\newcommand {\lang}[1]{\mathcal{L}(#1)}
\newcommand{\itembfcompact}[1]{\item[\textbf{#1}]}
\newcommand{\itembf}[1]{\item[\textbf{#1}]\mbox{}\\}
\newcommand{\itemxx}[1]{\item}
\newcommand{\ite}[3]{\mathtt{if}\; #1 \;\mathtt{then}\; #2 \;\mathtt{else}\; #3 \;\mathtt{fi}}
\newcommand{\inv}{^{-1}}
\newcommand{\id}{{\mathrm{id}}}
\newcommand{\zero}{\mathop{\mathrm{zero}}}
\renewcommand{\succ}{\mathop{\mathrm{succ}}}
\newcommand{\even}{\mathop{\mathrm{even}}}
\newcommand{\odd}{\mathop{\mathrm{odd}}}
\newcommand{\Prop}           {\mathrm{Prop}} 
\newcommand{\app}[2]{{#1(#2)}}
\newcommand{\dapp}{dapp}
\newcommand{\lnext}[1]{\circ #1}
\newcommand{\snext}[1]{\bullet #1}
\newcommand{\taglabel}[1]{\tag{\textsc{#1}}\label{#1}}
\newcommand{\sepconj}{\mathbin{*}}
\newcommand{\sepimp}{\mathbin{-\kern-.29em{*}}}
\newcommand{\K}{{$\mathbb K$}}
\newcommand{\Q}{{\mathcal Q}}

# Motivation

- Why do we care about languages, expressions and automata?
- Why a shallow embedding?

# Preliminaries

## Lanauges, Automata, and Expressions

TODO: Define languages.

Let $A = \{ a_1, a_2, \ldots a_n\}$ be a finite alphabet.
Then extended regular expressions (ERE) over the alphabet $A$ are defined
using the following grammar:
$$
R := \emptyset \mid \epsilon \mid a \in A \mid R \concat R \mid R + R \mid R \kleene \mid \lnot R
$$
The \emph{language} for an ERE, denoted $\lang R$ is defined as usual:
\begin{align*}
\lang{\emptyset}       &= \emptyset         \\
\lang{\epsilon}        &= \{ \epsilon \}    \\
\lang{a}               &= \{ a \} \\
\lang{R_1 + R_2}       &= \lang{R_1} \union \lang{R_2} \\
\lang{R_1 \concat R_2} &= \{ w_1 \concat w_2 \mid w_1 \in \lang{R_1} \text{ and } w_2 \in \lang{R_2} \} \\
\lang{R\kleene}        &= \Union_{n=0}^\infty R^n \text{\quad where $R^0 = \epsilon$, and $R^n = R\concat R^{n-1}$} \\
\lang{\lnot R}         &= A\kleene \setminus \lang{R} 
\end{align*}

TODO: Define FA.

::: {.definition #def:fa}
A (non-deterministic) *finite automata* is a tuple  $\Q = (Q, A, \delta, q_0, F)$, where

*  $Q$ is a finite set of *states*,
*  $A$ is a finite set of input symbols called the *alphabet*,
*  $\delta: Q \times A \to \P(Q)$ is a *transition function*,
*  $q_0 \in Q$ is the *initial state*, and
*  $F\subset Q$ is the set of *accepting states*.*

If the range of $\delta$ contains only singleton sets, then we call $\Q$ a deterministic finite automata.
:::


## Brzozowski Derivatives

In \cite{brzozowski1964derivatives}, Brzozowski introduced an operation over languages called its derivative, denoted $\der a R$.
This operation results in a language that is the result of ``consuming'' a letter from the beginning of each word in the language:
\begin{definition}[Brzozowski Derivatives]
Given a set $R$ of sequences and a finite sequence $s$, the derivative of $R$ with respect to $s$ is denoted by $\der s R$ and is $\{ t \mid s\concat t \in R \}$.
\end{definition}
For extended regular expressions, it turns out that the derivative can also be defined syntactically,
as a recursive function, through the following equalities:
\begin{minipage}[t]{0.5\linewidth}
\small
\begin{align*}
\der{a}{\epsilon}                   &= \emptyset \\
\der{a}{\emptyset}                  &= \emptyset \\
\der{a}{a}                          &= \epsilon \\
\der{a}{b}                          &= \emptyset \text{\qquad if $a \ne b$.} \\
\der{a}{\alpha_1 + \alpha_2}        &= \der{a}{\alpha_1} + \der{a}{\alpha_1} \\
\der{a}{\alpha_1 \concat \alpha_2}  &= \\&\hspace{-2em} \der{a}{\alpha_1} \concat \alpha_2 + \alpha_1|_\epsilon \concat \der{a}{\alpha_2} \\
\der{a}{\alpha\kleene}              &= \der{a}{\alpha} \concat \alpha\kleene \\
\der{a}{\lnot\alpha}                &= \lnot \der{a}{\alpha}
\end{align*}
\end{minipage}
\begin{minipage}[t]{0.5\linewidth}
\small
\begin{align*}
\emptyset|_\epsilon                 &= \emptyset\\
\epsilon|_\epsilon                  &= \epsilon \\
a|_\epsilon                         &= \emptyset \\
(\alpha_1 + \alpha_2)|_\epsilon     &= \alpha_1|_\epsilon + \alpha_2|_\epsilon\\
(\alpha_1 \concat \alpha_2)|_\epsilon &= \alpha_1|_\epsilon \land \alpha_2|_\epsilon\\
(\alpha\kleene)|_\epsilon           &= \epsilon \\
(\lnot \alpha)|_\epsilon            &= \begin{cases}
                                          \epsilon  & \text{if $\alpha|_\epsilon = \emptyset$}\\
                                          \emptyset & \text{if $\alpha|_\epsilon = \epsilon$}
                                      \end{cases}
\end{align*}
\end{minipage}

There are two properties of derivatives that are important to us in this paper.
First, every ERE may be transformed into an equivalent form that partitions its language per the initial letter in its words:
\begin{theorem}[Brzozowski Theorem 4.4]\label{thm:brz-equivalence}
Every extended regular expression $R$ can be written in the form:
$$R = R|_\epsilon + \sum_{a\in A} a \concat \der a R$$
where the terms in the sum are disjoint.
\end{theorem}
Second, that repeatedly taking the derivative eventually converges (up to associativity, commutativity, and idemopotency of $+$):
\begin{theorem}[Brzozowski Theorem 5.2]\label{thm:brz-dissimilar}
Every extended regular expression has only a finite number of dissimilar derivatives.
\end{theorem}
Here, two EREs are said to be dissimilar if they are not similar:
\begin{definition}
Two extended regular expressions are similar iff they are identical modulo associativity, commutativity and idemopotency of the $+$ operator.
\end{definition}

These two properties give rise to an algorithm for generating a DFA for the language of the expression,
illustrated in Figure \ref{fig:dfa}.
We may construct a DFA where each state is identified with an ERE.
The initial state is identified with the ERE whose validity we are checking.
Each state transitions to the states identified by the derivative with respect to the input alphabet.
A state identified by $\alpha$ is accepting iff $\alpha|_\epsilon$ is similar to $\epsilon$.
The first theorem mentioned implies that acceptance by this DFA implies membership in the the expressions languages,
whereas the second shows us that this algorithm must terminate.
Now, we can check if the ERE is valid by simply checking that all states are accepting.


## What is Matching Logic?

In this subsection, we will describe the syntax and semantics of matching logic formulae, called \emph{patterns}.
Matching logic patterns are defined over a matching logic signature.
\begin{definition}
Let $\EVar$, $\SVar$, $\Sigma$ be disjoint countable sets.
Here, $\EVar$ contains \emph{element variables}, $\SVar$ contains \emph{set variables}
and $\Sigma$, called the \emph{signature} contains a set of \emph{symbols}.
\end{definition}
By convention, element variables are denoted using lower case letters, whereas for set variables we use upper case letters.
\begin{definition}
A $\Sigma$-pattern over a signature $\Sigma$ is defined inductively using the following grammar:
\begin{align*}\phi :=&
                \overbrace{ \bot   \mid \phi_1 \limplies\phi_2 }^\text{propositional}
        \mid    \overbrace{\sigma \in \Sigma \mid (\phi_1\;\;\phi_2)}^\text{modal} \\
        \mid&   \underbrace{ x \in \EVar  \mid \exists x \ldotp \phi }_\text{quantification}
        \mid    \underbrace{ X \in \SVar \mid \mu     X \ldotp \phi }_\text{fixedpoint}
\end{align*}
We call the pattern $(\phi_1\;\;\phi_2)$ an \emph{application}.
In the case of fixedpoint patterns, $\mu X\ldotp \phi$, the set variable $X$ must occur positively in $\phi$, that is,
in a pattern, they may only occur under the left-hand side of an implication an even number of times.
The constructs $\exists$ and $\mu$ bind the element variable $x$ and set variable $X$ respectively.
We use $\free(\phi)$ to denote the free (set or element) variables in a pattern $\phi$.
\end{definition}
We assume the usual syntactic sugar:
\begin{align*}
\lnot \phi &\equiv \phi \limplies \bot &
\top &\equiv \lnot \bot \\
\phi_1 \lor \phi_2 &\equiv \lnot \phi_1 \limplies \phi_2 &
\phi_1 \land \phi_2 &\equiv  \lnot (\phi_1 \limplies \lnot \phi_2) \\
\forall x \ldotp \phi &\equiv \lnot \exists x \ldotp \lnot \phi &
\nu X \ldotp \phi &\equiv \lnot \mu x \ldotp \lnot \phi[\lnot X / X]
\end{align*}
Patterns are evaluated in a model:
\begin{definition}
Given a signature $\Sigma$, a \emph{$\Sigma$-model} is the triple $(M, \_ \bullet \_, \{\sigma_M\}_{\sigma\in\Sigma})$ with:
\begin{enumerate}
\item a non-empty carrier set $M$;
\item a binary function $\_ \bullet \_ : M \times M \to \mathcal P(M)$ called application;
\item an interpretation $\sigma_M \subset M$ for each symbol $\sigma \in \Sigma$.
\end{enumerate}
\end{definition}
We extend $\_\bullet\_$ pointwise to sets as follows:
\begin{align*}
\_  \bar\bullet \_ &: \P(M) \times \P(M) \to \P(M) \\ A \bar\bullet B &\mapsto \Union \{ a\bullet b \mid a \in A, b \in B\}
\end{align*}

Matching Logic patterns have a \emph{pattern matching semantics}.
That is, each pattern is evaluated to the set of elements in the model that match it.
A matching logic model defines the evaluations of symbols and pattern applications.
Element variables and set variables have evaluations determined by an variable valuation function $\rho$.
An element variable is matched by precisely one element in the model,
whereas a set variable may have arbitrary sets as their evaluation.
No elements match $\bot$,
while $\phi_1 \land \phi_2$ and  $\phi_1 \lor \phi_2$
are matched by elements in the intersection and the union, respectively,
of the evaluations of their sub-patterns.
Formally,
\begin{definition}[Matching logic semantics]
An \emph{$M$-valuation} is a function $\EVar \union \SVar \to \P(M)$, such that each $x \in \EVar$ evaluates to a singleton.
Let $M$ be a model and $\rho$ be an $M$-valuation, then the evaluations of matching logic patterns is defined inductively as follows:
\begin{align*}
\eval{\bot}_{M,\rho}                    &= \emptyset \\
\eval{\sigma}_{M,\rho}                  &= \sigma_M \\
\eval{\phi_1 \limplies \phi_2}_{M,\rho} &= \left(M \setminus \eval{\phi_1}_{M,\rho}\right) \union \eval{\phi_2}_{M,\rho} \\
\eval{\phi_1 \;\; \phi_2}_{M,\rho}      &= \eval{\phi_1}_{M,\rho} \; \bar\bullet \; \eval{\phi_2}_{M,\rho} \\
\eval{x}_{M,\rho}                       &= \rho(x) \\
\eval{\exists x\ldotp \phi}_{M,\rho}    &= \Union_{a\in M}\eval{\phi}_{M,\rho[a/x]} \\
\eval{X}_{M,\rho}                       &= \rho(X) \\
\eval{\mu X\ldotp \phi}_{M,\rho}        &= \lfp\left(A \mapsto \eval{\phi}_{M,\rho[A/X]}\right)
\end{align*}
\end{definition}

Since matching logic patterns are set-valued, rather than true/false as in first-order logic,
defining validity is slightly more involved.
\begin{definition}
For a model $M$, we say that a pattern $\phi$ is \emph{valid} in $M$,
iff $\eval{\phi}_M^\rho = M$ for all $M$-valuations $\rho$.
Let $\Gamma$ be a set of patterns, called a \emph{theory}.
We say a model $M$ \emph{satisfies} $\Gamma$, if each $\gamma$ in $\Gamma$ is valid in $M$.
A pattern $\phi$ is \emph{valid} in a theory $\Gamma$, written $\Gamma \satisfies \phi$,
if for every model $M$ satisfying $\Gamma$, $\phi$ is valid.
\end{definition}

\begin{figure}[t]
\centering
\small
\def\arraystretch{1.2}
\begin{tabularx}{\linewidth}{rX}
\prule{Propositional 1}            &\quad $\phi \limplies ( \psi \limplies \phi )$ \\
\prule{Propositional 2}            &\quad $(\phi \limplies ( \psi \limplies  \theta ) )$ \\&$\qquad \limplies ( ( \phi \limplies \psi ) \limplies ( \phi  \limplies \theta ) )$ \\
\prule{Propositional 3}            &\quad $((\phi \limplies \bot) \limplies \bot) \limplies  \phi$ \\
\prule{Modus Ponens}               &\quad $\displaystyle
                                           \frac{\phi \qquad \phi \limplies \psi}
                                                {\psi}
                                          $
                                   \\
\prule{$\exists$-Quantifier}       &\quad $\phi[y/x] \limplies \exists x \ldotp \phi$ \\
\prule{$\exists$-Generalization}   &\quad $\displaystyle
                                           \frac{\phi \limplies \psi}
                                                {(\exists x \ldotp \phi) \limplies \psi}
                                          $ \\&\qquad where $x \notin FV(\psi)$
                                   \\[1em]
\cline{1-2} \\[-0.5em]
\prule{Propagation$_{\bot}$}       &\quad $C[\bot] \limplies \bot$ \\
\prule{Propagation$_{\vee}$}       &\quad $C[\phi \lor \psi] \limplies  C[\phi] \lor C[\psi]$ \\
\prule{Propagation$_{\exists}$}    &\quad $C[\exists x \ldotp \phi]  \limplies  \exists x \ldotp C[\phi]$
                                    \\&\qquad where $x \notin FV(C)$ \\[0.2em]
\prule{Framing}                    &\quad $\displaystyle
                                           \frac {\phi \limplies \psi}
                                                 {C[\phi] \limplies C[\psi]}
                                          $
\\[1em]
\cline{1-2} \\[-0.6em]
\prule{Prefixpoint}                &\quad $\phi[(\mu X \ldotp \phi)/X] \limplies \mu  X  \ldotp \phi$ \\
\prule{Knaster-Tarski}             &\quad $\displaystyle
                                           \frac{\phi[\psi/X] \limplies \psi}
                                               {(\mu X \ldotp \phi) \limplies \psi}
                                          $
                                   \\[1em]
\cline{1-2} \\[-0.6em]
\prule{Existence}                  &\quad $\exists x \ldotp x$
                                   \\
\prule{Singleton}                  &\quad $\neg (C_1[x \land \phi] \land C_2[x \land  \neg \phi])$
                                   \\
\prule{Substitution}               &\quad $\displaystyle
                                           \frac{\phi}
                                                {\phi[\psi/X]}
                                          $
\end{tabularx}
\caption{Matching logic proof system (where $C,C_1,C_2$ are application  contexts and $C[\phi] \equiv C[\phi/\hole]$).}
\label{fig:ml-proof-system}
\end{figure}

The matching logic proof system, shown in Figure \ref{fig:ml-proof-system},
defines the provability relation, written $\Gamma\proves\phi$, meaning
that $\phi$ can be proved using the proof system with the patterns in $\Gamma$ as additional axioms.
We call $\Gamma$ a matching logic theory.
To understand this proof system, we must first define application contexts.
\begin{definition}
A \emph{context} is a pattern with a hole variable $\hole \in \EVar \union \SVar$.
We write $C[\phi] \equiv C[\phi/\hole]$ as the result of context plugging.
We call $C$ an \emph{application context}, iff
\begin{enumerate}
\item $C \equiv \hole$ is the identity context
\item $C \equiv (\phi\;\; C')$ or $C \equiv (C' \;\;\phi)$, where $C'$ is an application context and $\hole \not\in \free(\phi)$.
\end{enumerate}
\end{definition}

These proof rules are sound with respect to the semantics,
and fall into four categories.
First, the FOL rules provide complete FOL reasoning.
The \prule{\prop{}} rules allow application to commute with constructs such as disjunction and exististentials which have a ``union'' semantics,
roughly a proof theoretic incarnation of lifting $\bullet$ to $\bar\bullet$.
When taken together, unary versions of \prule{\prop{\bot}}, \prule{\prop{\lor}} and \prule{framing},
are equivalent to modal logics axiom K and necessitation axioms.
The proof rule \prule{knaster-tarski} is an embodiement of the Knaster-Tarski fixedpoint theorem~\cite{knaster-tarski},
and together with \prule{prefixedpoint} correspond to the Park induction rules of modal logic~\cite{park1969fixpoint,kozen1983results}.


## Matching Logic Idioms

Before introducing our theory, let us look at some common idioms used when defining matching logic theories and proofs.

### Notation

In order to compactly represent complex logics, matching logic allows defining syntactic sugar over patterns.
Notation is used for defining ``standard'' sugar such as $\lnot$, $\forall$ and $\nu$, as well as complex constructs
such as equality, the Kleene star operator, and contextual implications described below.

### Predicate patterns

Unlike first-order logic formulae, matching logic patterns may be interpreted as any subset of the carrier set,
not just as either true or false.
Predicate patterns are a special class of matching logic patterns,
that can only be interpreted as either the empty set or the carrier set, depending on the valuation.
Predicate patterns of course include $\top$, $\bot$ and all propositional tautologies, as well as
equalities. Being two valued, they behave similarly to formulae in first-order logic.
Counter examples include $\even \equiv \mu X \ldotp \zero \lor (s (s X))$, and $\odd \equiv (s \even)$
both of which have non-empty interpretations in the theory of the naturals.

### Definedness

The theory of definedness is a foundational matching logic theory
that allows us to succinctly capture equality and other important predicates.
As shown in Figure \ref{fig:definedness}, it includes
one symbol, $\mathrm{def}$.
When applied it gives rise to the \emph{ceiling} operator, abbreviated $\lceil \phi \rceil$.
The axiom, \prule{definedness}, makes $\eval{\ceil{\phi}} = M$ for any $\phi$ with non-empty evaluation.
It also forces $\lceil \phi \rceil$ to be a predicate pattern for any $\phi$.
In particular, if $\phi$ has a non-empty evaluation, then $\eval{\lceil \phi \rceil} = M$.
Otherwise, it has $\emptyset$ as its evaluation.
Dually, $\lfloor \phi \rfloor$ (pronounced \emph{floor of $\phi$}) is evaluated as top if and only if
the evaluation of $\phi$ is top.
This allows us to define some important predicate patterns such as
equality ($\phi = \psi \equiv \lfloor \phi \liff \psi \rfloor$), and
subset ($\phi \subset \psi \equiv \lfloor \phi \limplies \psi \rfloor$).
\begin{figure}
\begin{minipage}[t]{0.45\linewidth}
\small
\begin{enumerate}[left=4em,itemindent=2em]
\itembfcompact{Symbols:} $\mathsf{def}$
\itembfcompact{Axioms:} $\forall x\ldotp \lceil x \rceil$\qquad \prule{definedness}
\itembfcompact{Notation:}
$\begin{aligned}[t]
\lceil  \phi \rceil &\equiv (\mathsf{def} \;\; \phi) \\
\lfloor \phi \rfloor &\equiv \lnot \lceil \lnot \phi \rceil \\
\end{aligned}$
\end{enumerate}
\end{minipage}
\begin{minipage}[t]{0.45\linewidth}
\small
\begin{enumerate}[left=4em,itemindent=2em]
\itembf{Notation:}
$\begin{aligned}[t]
x    \in \phi     &\equiv \lceil x \land \phi \rceil \\
\phi \subset \psi &\equiv \lfloor \phi \limplies \psi \rfloor \\
\phi = \psi &\equiv \lfloor \phi \liff \psi \rfloor \\
\end{aligned}$
\end{enumerate}
\end{minipage}
\caption{The theory of definedness}
\label{fig:definedness}
\end{figure}

### Functional patterns

Another interesting class of patterns are \emph{functional} patterns.
Functional patterns are patterns that are interpreted as singleton sets.
These behave like terms in first-order logic.
The semantics of matching logic ensures that element variables are functional patterns.
We may add axioms to enforce that symbols have functional interpretations---i.e.
they return a single output applied to a singleton input
by adding the following axiom to the theory:
$\forall \bar y \ldotp \exists x \ldotp x = (f \;\; \bar y)$.
The application of these symbols may then be used along with element variables to construct functional patterns.
For example $(\succ \zero)$ and $(\succ x)$ are both functional patterns in the naturals.

### Fixedpoint patterns
A pattern $\phi$, in which $X$ occurs only positively, induces a \emph{monotonic}
function $\mathcal F : \P(M) \to \P(M)$, where $\mathcal F(A) \mapsto \eval{\phi}^M_{\rho[A/X]}$~\cite{CR19}.
By the Knaster Tarski fixedpoint theorem~\cite{tarski1955lattice}, every monotonic function has a least- and greatest-fixedpoint.
Matching logic's $\mu$ construct lets us capture this fixedpoint explicitly.
For example, the axiom $\mu X \ldotp \zero \lor (\succ X)$
lets us capture the inductive nature of the naturals, and,
assuming the other necessary axioms, precisely pins down the standard model of the naturals~\cite{CR19}.
This means, that the L\"owenheim–Skolem theorem~\cite{skolem1879logico} does not hold for matching logic,
and that by Godel's theorems~\cite{godel1931formal}, matching logic is \emph{not} complete.
At the same time, matching logic is strictly more expressive than first-order logic~\cite{CR19}.

### Sorts

While matching logic does not provide a built-in concept of sorts,
they may easily be defined axiomatically.
Since, in this paper, we only deal with a simple sort hierarchy we will not go  into this in detail.
When dealing with a sort $s$, typically, its domain is represented by the pattern $\top_s$, read \emph{inhabitants of $s$}.
We may add an axiom to constrain that pattern to represent the domain of $s$.
For example, the axiom $\top_\N = \mu X \ldotp \zero \lor (\succ \;\; X)$
constrains $\top_\N$ to the domain of the naturals.
Further, we can constrain the domain of symbols.
For instance, the axiom $\N + \N \limplies \N$ forces the symbol $+$
to always return a natural when given two naturals as input.
Note that it does not constrain the symbol $+$ in any way for arguments outside of the naturals.
For example, we could extend $+$ to the domain of integers or even to concatenation of lists without any change to this axiom.
Finally, we can quantify over the elements of a sort.
For any sort $s$, the notation $\forall x:s \ldotp \phi \equiv \forall x \ldotp x\in\top_s \land \phi$
allows us to quantify over all elements restricted to the domain of $s$.

### Contextual implications
In order to enable fixedpoint reasoning, matching logic includes two rules:
\prule{prefixedpoint} and \prule{knaster-tarksi}.
While these rules are powerful, they are also very minimalistic.
For example to apply \prule{knaster-tarksi}, key to any inductive proof,
we \emph{must} have a least fixedpoint pattern on the left-hand side of an implication.
We may not, for example, have it within an application context.
We may need this in the case of trying to prove,
say $\even + \even \limplies \even$,
where $\even \equiv \mu X \ldotp \zero \lor (\succ \; (\succ \; X))$.

For any application context $C$ and pattern $\phi$ (where $\hole \not\in \free(\phi)$), we call
$C \cimplies \phi \equiv \exists \hole \ldotp \hole \land (C[\hole] \subset \phi)$
a \emph{contextual implication}.
Informally, the pattern evaluates to the set of elements that when plugged into the context $C$ imply $\phi$.
Using contextual implications, we may use the inferred rule $\prule{wrap}$ to pull any pattern out of an applicative context,
apply the \prule{knaster-tarski} rule, and then plug the result back into the context using \prule{unwrap}.
These two rule let us work around one of the major limitations of the \prule{knaster-tarski} rule.
This is explained in more detail in \cite{chen2020towards}.

\begin{figure}
$$
\prule{wrap}\quad \frac{\phi \limplies (C \cimplies \psi)}{C[\phi] \limplies \psi}
\qquad
\frac{C[\phi] \limplies \psi} {\phi \limplies (C \cimplies \psi)} \quad\prule{unwrap}
$$
\caption{The \prule{wrap} and \prule{unwrap} derived proof rules, first proved in \cite{CR19}
and effectively employed in \cite{chen2020towards} in the context of separation logic, reachability logic and LTL.}
\end{figure}


# A matching logic theory of finite words


## Theory of Finite Words

Given an alphabet, $A$, we define the theory of finite words as follows:

\begin{figure}
\small
\begin{enumerate}[left=4em,itemindent=4em]
\itembfcompact{Imports:} Definedness
  \itembfcompact{Sorts:} $\letter$, $\word$
\itembfcompact{Symbols:} $\epsilon$, $\concat$, and $a$ for each $a \in A$.
\itembf{Notation:}
$\begin{aligned}[t]
    \emptyset           &\equiv \bot &          
\inhabitants{\letter}   &\equiv \textstyle\lOr_{a \in A} a               \\
    (R_1 +  R_2)        &\equiv R_1 \lor R_2            &
\inhabitants{\word}     &\equiv \textstyle{\inhabitants{\letter}}\kleene \\
    R \kleene           &\equiv \mu X \ldotp \epsilon \lor (R \concat X) \qquad\\
\end{aligned}$
\itembfcompact{Axioms:}
\begin{align}
&\inhabitants{\word}     \tag{\textsc{domain-word}}\\
\intertext{For each $a \in A$,}
\exists x:\letter &\ldotp a = x \tag{\textsc{func$_a$}}\\
\exists w:\word   &\ldotp \epsilon = w \tag{\textsc{func$_\epsilon$}}\\
\forall w, v:\word& \ldotp \exists u:\word \ldotp  w \concat v = u \tag{\textsc{func$_\bullet$}}
\intertext{ For each distinct $a,b \in A$,}
    &a \ne b                                                    \tag{\textsc{no-conf}$_a$}\\
    &\epsilon \not \in \inhabitants{\letter}                    \tag{\textsc{no-conf}$_\epsilon$}
\\
 \forall u,v:\word &\ldotp \nonumber \\
   \epsilon = u \concat v & \limplies u = \epsilon \land v = \epsilon
                                                                \tag{\textsc{no-conf}$_\bullet$-1}\\
\forall x,y:\letter, u,\mathrlap{v:\word \ldotp} \nonumber \\
    x\concat u = y \concat v &\limplies x = y \land u = v       \tag{\textsc{no-conf}$_\bullet$-2}\\
    \forall u, v, w:\word \ldotp \nonumber \\
        (u \concat v) \concat w  &= u \concat (v \concat w)
\tag{\textsc{assoc}}\\
\forall x\ldotp (\epsilon \concat x) &= x \tag{\textsc{id$_L$}}\\
\forall x\ldotp (x \concat \epsilon) &= x \tag{\textsc{id$_R$}}
\end{align}
\end{enumerate}
\end{figure}

Our theory ``imports'' the theory Definedness.
That is, it includes all its axioms, symbols and notation.
This allows us to use equality, and sorted quantification in our theory.
The theory uses two sorts, one for letters, and one for words.
The inhabitants of these sorts are defined using notation---$\top_\letter$ denotes the set of all letters,
and $\top_\word$ the set of all words.
The signature defines symbols for the empty word, concatenation, and for each letter.
Note that we do not need symbols for the empty set, choice or Kleene star---these
are defined as notation for bottom, disjunction and using matching logic's fixpoint operator.
This let us represent regular expressions.

The first axiom \prule{domain-word} defines our domain as the set of words.
More formally, it constrains the universe of our model to the elements
that can be built through finite concatenations of the $\epsilon$ and letters.

The next three axioms restrict the symbols to functional interpretations.
\prule{func$_\epsilon$} and each \prule{func$_a$} ensure that $\epsilon$ and each letter $a$
are interpreted as single elements in the model (or, in first-order logic parlance, as constants).
\prule{func$_\bullet$} constrains the models of ones where concatenation is a function over
words.

The \prule{no-conf} axioms ensure that the interpretations of symbols are injective (modulo associativity, commutativity, and identity).
These are similar to those in \cite{chen2020-initial-algebra} for defining term algebras,
with the caveat that we must take into account the associativity of $\concat$ and its identity of $\epsilon$.
That is, we must relax them as compared to those in \cite{chen2020-initial-algebra}.

We must also add axioms the axioms \prule{assoc}, and \prule{id$_L$}, and \prule{id$_R$}
in order to enforce these properties and allow their use in proofs.
Note that we do not need to define axioms for the $+$ operator, since it is
notational sugar for matching logic's disjunction, that has all the required properties.

::: { .theorem title='Soundness' }
Let $M_\word$ be the standard model of words. Then $M \satisfies \GRE$.
:::

Now that we have defined our theory of words, we can represent regular expressions
in the obvious way using the defined notation.
We must first prove that this representation is faithful
to the expected interpretation of regular expressions.
This is shown in the following theorem:

::: { .theorem title='Faithfulness of Expressions'}
Let $M_\word$ be the standard model of words and
$\alpha$ be a regular expression. Then $\lang{\alpha} = \eval{\alpha}_{M_\word}$
:::


## Embedding Automata

While the above theory allows us to easily represent regular expressions,
it is less clear how we may represent finite state automata.

\begin{figure*}
\begin{subfigure}[t]{0.38\linewidth}
\centering
\small
\begin{tikzpicture}
\node[state, initial above, accepting] (e) {$(aa)\kleene \limplies a \kleene a + \epsilon$};
\node[state, accepting, below left = 2em and -6ex of e] (a) {$a (aa)\kleene \limplies a \kleene a + \epsilon + \emptyset$};
\node[state, accepting, below right = 2em and -5ex  of e] (b) {$\emptyset \limplies \emptyset$};
\node[state, accepting, below = 2em of a] (aa) {$(aa)\kleene \limplies a \kleene a + \epsilon + \emptyset$};
\draw (e)   edge            node[left]  {$a$} (a)
      (e)   edge            node[right] {$b$} (b)
      (a)   edge[bend left] node[right] {$a$} (aa)
      (a)   edge            node[above] {$b$} (b)
      (aa)  edge            node[above] {$b$} (b)
      (aa)  edge[bend left] node[left]  {$a$} (a)
      (b)   edge[loop below]node  {$a,b$} (b)
      ;
\end{tikzpicture}
\caption{A DFA for the ERE $(aa)\kleene \limplies a \kleene a + \epsilon$}
\label{fig:dfa}
\end{subfigure}
\begin{subfigure}[t]{0.58\linewidth}
\centering
\small
\begin{tikzpicture}
\node[state, label=$\rootn$] (e) {$(aa)\kleene \limplies a \kleene a + \epsilon$\\$\pat=\epsilon \lor a (\mu Y \ldotp \epsilon \lor a (\epsilon \lor a Y \lor b \top) \lor b \top) \lor b \top$};
\node[state, below left = 2em and -14em of e] (a) {$a (aa)\kleene \limplies a \kleene a + \epsilon + \emptyset$\\$\pat=\mu Y \ldotp \epsilon \lor a (\epsilon \lor a Y \lor b \top) \lor b \top$};
\node[state, below right = 2em and -6ex  of e] (b) {$\emptyset \limplies \emptyset$\\$\pat=\top$};
\node[state, below = 2em of a] (aa) {$(aa)\kleene \limplies a \kleene a + \epsilon + \emptyset$\\$\pat=\epsilon \lor a Y \lor b \top$};
\node[state, below = 2em of b] (ab) {$\emptyset \limplies \emptyset$\\$\pat=\top$};
\node[state, above right = -3ex and 2em of b]  (ba)     {$\emptyset \limplies \emptyset$ \\ $\pat = X$};
\node[state, below right = -3ex and 2em of b]  (bb)     {$\emptyset \limplies \emptyset$ \\ $\pat = X$};
\node[state, above right = -3ex and 6em of ab] (aba)    {$\emptyset \limplies \emptyset$ \\ $\pat = X$};
\node[state, below right = -3ex and 6em of ab] (abb)    {$\emptyset \limplies \emptyset$ \\ $\pat = X$};
\node[state, below       =  2em         of aa] (aaa)    {$a (aa)\kleene \limplies a \kleene a + \epsilon + \emptyset$\\$\pat=Y$};
\node[state, below       =  2em         of ab] (aab)    {$\emptyset \limplies \emptyset$\\$\pat=\top$};
\node[state, above right = -3ex and 2em of aab](aaba)   {$\emptyset \limplies \emptyset$ \\ $\pat = X$};
\node[state, below right = -3ex and 2em of aab](aabb)   {$\emptyset \limplies \emptyset$ \\ $\pat = X$};
\draw (e)   edge            node[right] {$a$}  (a)
      (e)   edge            node[above] {$b$}  (b)
      (a)   edge            node[right] {$a$}  (aa)
      (a)   edge            node[above] {$b$}  (ab)
      (b)   edge            node[above] {$a$}  (ba)
      (b)   edge            node[above] {$b$}  (bb)
      (ab)  edge            node[above] {$a$}  (aba)
      (ab)  edge            node[above] {$b$}  (abb)
      (aa)  edge            node[right] {$a$}  (aaa)
      (aa)  edge            node[above] {$b$}  (aab)
      (aab) edge            node[above] {$b$}  (aaba)
      (aab) edge            node[above] {$a$}  (aabb)
      ;
\end{tikzpicture}
\caption{
    The unfolding tree for the same ERE, where $\top \equiv \mu X\ldotp \epsilon \lor a X \lor b X$.
    Here, the first line of each node $n$ is a regular expression corresponding to $L(n)$,
    whereas the second line shows $\pat(n)$.
}
\label{fig:example-derivative-tree}
\end{subfigure}
\end{figure*}

In this subsection, we will define a pattern $\pat_\Q$ that captures the language of a DFA $\Q$ as a shallow
embedding---a pattern whose denotation is the same as the language of $\mathcal Q$.
These DFAs are represented as directed graphs that may have cycles. We must find some way of encoding these.
These cycles correspond to the inductive structure of the language they define, so the natural way to do so is to represent them using fixedpoint patterns.
A state in the cycle may be represented a fixedpoint pattern that binds a variable,
whereas returning to that state may be represented as the corresponding set variable.
By duplicating certain nodes, the *unfolding tree* of a finite automata
allows us to represent the automata as a tree.

::: {.definition #def:unfolding-tree}
For a finite automata $\mathcal Q = (Q, A, \delta, q_0, F)$, its *unfolding tree* is a
labeled tree $(N, E, L)$ where $N$ is the set of nodes,
$E \subset A \times N \times N$ is a labeled edge relation,
and $L: N \to Q$ is a labeling function.
It is the least tree defined inductively as follows:

*   the root node has label $q_0$,
*   if a node $n$ has label $q$ with no ancestors also labeled $q$,
    then for each $a \in A$ and $q' \in \delta(q, a)$, there is a node $n' \in N$
    with $L(n') = q'$, and $(a, q, q') \in E_a$.
:::

Note that all leaves in this tree have as labels states that complete a cycle in the original DFA.
These have $\pat(n) = X(L(n))$, a set variable.
This set variable is always bound pattern by the $\pat(a)$, where $a$ is the ancestor node also labeled by $L(n)$.
For a node $n$, we use $n_a$ to refer to the child whose label is $\delta(L(n), a)$.
The pattern $\pat_\Q$ captures the recursive structure of the DFA as a fixedpoint pattern, and allows us
to use the \prule{Knaster-Tarski} to easily.

To define $\pat_\Q$, we define a secondary labeling function, $\pat : N \to \mathsf{Pattern}$ over this tree,
and use that to define $\pat_{\Q}$.

::: {.definition #def:fp}
Let  $(N, E, L)$ be an unfolding tree for $\Q = (Q, A, \delta, q_0, F)$.
Let $X: Q \to \mathsf{SVar}$ be an injective function.
Then, we define $\pat$ recursively as follows:

1.  \label{node:leaf} For a leaf node $n$, $\pat(n) := X(L(n))$.
2.  For a non-leaf node,
    a.  \label{node:unnamed}
        if $n$ doesn't have a descendant with the same label, then:
        $$\pat(n) =
        \begin{cases}
        \displaystyle
                   \epsilon\; \lor  \lOr_{\mathclap{(a, n, n') \in E}} a \concat \pat(n') & \text{if $L(n)$ is accepting.}\\
        \displaystyle
          \phantom{\epsilon\; \lor} \lOr_{\mathclap{(a, n, n') \in E}} a \concat \pat(n') & \text{otherwise.}
        \end{cases}
        $$
    b.  \label{node:named}
        if $n$ has a descendant with the same label, then:
        $$\pat(n) =
        \begin{cases}
        \displaystyle
          \mu X(L(n)) \ldotp          \epsilon\; \lor  \lOr_{\mathclap{(a, n, n') \in E}} a \concat \pat(n') & \text{if $L(n)$ is accepting.}\\
        \displaystyle
          \mu X(L(n)) \ldotp \phantom{\epsilon\; \lor} \lOr_{\mathclap{(a, n, n') \in E}} a \concat \pat(n') & \text{otherwise.}
        \end{cases}
        $$

Finally, define $\pat_{\mathcal Q} := \pat(\rootn)$, where $\rootn$ is the root of this tree.
:::

Note that the case for (\ref{node:unnamed}) is quite similar to (\ref{node:named}),
except that we ``name'' the node by binding the variable $X(L(n))$.
This distinction isn't strictly necessary---we could name all nodes while only superficially affecting the proof.
The bound variable wouldn't occur under the fixedpoint pattern.
However, we find that making this distinction allows us to clearly embody the inductive structure as a pattern.
Figure \ref{fig:example-derivative-tree} shows the unfolding tree for a DFA that accepts the same language as $(aa)\kleene \limplies a \kleene a + \epsilon$.

::: { .theorem title='Faithfulness of Automata'}
Let $M_\word$ be the standard model of words and
$\Q$ be a finite automaton. Then $\lang{\Q} = \eval{\pat_\Q}_{M_\word}$
:::

## Brzozowski Derivative

In a somewhat surprising connection, Brzozowski derivatives are exactly contextual implications.
Let us review contextual implications.
For any pattern $\psi$ and context $C$, we define a contextual implication as the pattern
$C \cimplies \psi \equiv \exists \hole \ldotp \hole \land (C[\hole] \subset \psi)$.
For any context, a contextual implication has as its evaluation the set of elements that when
plugged into the context $C$ imply the pattern $\psi$.
So, for $C \equiv a \concat \hole$, we get the set of words that when prefixed with $a$ give us $\psi$.
Note that this definition also works for arbitrary words and not just single letters. 

For any word $w$ and pattern $\psi$, we may define its Brzozowski derivative as the matching logic pattern
$\der w \psi \equiv  (w\concat \hole \cimplies \psi)$.
This connection is quite striking and intriguing because it closely parallels the magic wand operator of separation logic:
$\phi \sepimp \psi \equiv \phi \sepconj \hole \cimplies \psi$.
At first glance, this seems like a somewhat weak connection,
but on closer inspection, the magic wand and derivatives are semantically quite similar---we
may think of the magic wand operator as taking the derivative of one heap with respect to the other. 
It is these connections between seemingly disparate areas of program verification
that matching logic seeks to bring to the foreground.

The following theorem, key to the certification, follows from properties of contextual implications:
for any functional context $C$, we have $\proves C [ \top ] \land \phi \liff C[ C \cimplies \phi ]$.

::: { .lemma title="Brzozowski Derivatives" #lemma:derivative-equivalence }
For any pattern $\phi$, $$\GRE \proves \phi = (\epsilon \land \phi) \lor \lOr_{a \in A} a \concat \der {a} \phi$$
:::

From the above notation for derivatives, we may also prove the syntactic simplifications, representing $\alpha|_\epsilon$ quite simply as $\alpha\land \epsilon$:

::: { .lemma title="Derivatives Simplification" #lemma:derivative-simplification }
For regular expressions $\alpha$ and $\beta$ and a letter $a$, and every $b \ne a$, the following hold:

1.  $\GRE\proves \der{a}{\epsilon} = \emptyset$
2.  $\GRE\proves \der{a}{\emptyset} = \emptyset$
3.  $\GRE\proves \der{a}{b} = \emptyset$
4.  $\GRE\proves \der{a}{a} = \epsilon$
5.  $\GRE\proves \der{a}{\alpha_1 + \alpha_2} = \der{a}{\alpha_1} + \der{a}{\alpha_1}$
6.  $\GRE\proves \der{a}{\alpha_1 \concat \alpha_2} = \der{a}{\alpha_1} \concat \alpha_2 + (\alpha_1 \land \epsilon) \concat \der{a}{\alpha_2}$
7.  $\GRE\proves \der{a}{\lnot\alpha} = \lnot \der{a}{\alpha}$
8.  $\GRE\proves \der{a}{\alpha\kleene} = \der{a}{\alpha} \concat \alpha\kleene$
:::

# Proofs

In this section, after proving some supporting lemmas,
we will show that when two regular expressions or automata are equivalent,
this can be proven by in our theory. The is, we will show that $\GRE\proves \alpha \liff \beta$
when $\alpha$ and $\beta$ describe the same language and are either regular expressions,
or $\pat_\Q$ for some automata $\Q$. We will also use a similar proof for Arden's rule,
for patterns of this form.

The general procedure for this is into two phases.
First, we produce a finite automata $\Q$ through Brzozowski's method corresponding
to $\alpha \liff \beta$, and show prove that it is total. That is, we prove that
$\GRE\proves\pat_\Q$.
Second, we prove that this automata's language subsumes that of $\alpha \liff \beta$.
That is, that $\GRE\proves \pat_\Q \limplies (\alpha \liff \beta)$.
Putting these together using \prule{modus ponens} gives us $\GRE\proves (\alpha \liff \beta)$.

Note that while in this paper, for $\Q$,
we use the DFA produced by Brzozowski's method,
the procedure should work for any automaton so long as we can prove that
**TODO: Figure our the exact criteria we need here.**

Let us first build a toolbox with which we shall prove this.

## From Words to Languages

Now that we have a theory of words, our next task becomes immediately apparent.
Each of the axioms above quantify over words.
However, it is more convenient to deal with languages.
In matching logic, the natural way to deal with this is to ``lift'' these axioms from element variables to set variables.
The proofs for these are technical and not particularly enlightening.

::: { .lemma #lemma:axioms-as-set-variables }
The following can be proved:
\begin{align}
\GRE&\proves (X \concat Y) \concat Z = X \concat (Y \concat Z) \tag{\sc assoc}\\
\GRE&\proves \epsilon \concat X = X \tag{\sc identity-l}\\
\GRE&\proves \lnot(a \concat X \land b \concat Y) \tag{\sc no-confusion-ab-l}\\
\GRE&\proves \lnot(\epsilon \land a \concat X) \tag{\sc no-confusion-$\epsilon$-l} \\
\GRE&\proves X \concat \epsilon = X \tag{\sc identity-right} \\
\GRE&\proves \lnot(X \concat a \land Y \concat b) \tag{\sc no-confusion-ab-r}\\
\GRE&\proves \lnot(\epsilon \land X \concat a) \tag{\sc no-confusion-$\epsilon$-r}
\end{align}
:::

## Alternative induction schema

Another important tool is having alternate formulations of the domain axioms for words.
This lets us induct using different bases on either the left or on the right.
The proofs of these are via the \prule{wrap} and \prule{unrwap} rules shown earlier.

::: { .lemma title='Inductive Domain' #lemma:inductive-domain }
The following patterns are equivalent in $\GRE$:

1. $\top_\word$
2. $\mu X \ldotp \epsilon \lor X \concat \top_\letter$
3. $\mu X \ldotp \epsilon \lor \top_\letter \lor X\concat X$
:::


## Proving an automata is total

We are now ready to prove that the automata $\Q$ is total.
By \prule{domain-words}, and Lemma \ref{lemma:inductive-domain},
this reduces to
$\GRE \proves (\mu X\ldotp \epsilon \lor X \concat \top_\letter) \limplies \pat_{\mathcal Q}$.
We may now use \prule{knaster-tarski} and reduce this to
$\GRE \proves (\epsilon \lor \pat_{\mathcal Q} \concat \top_\letter) \limplies \pat_{\mathcal Q}$.
Since the root node of $\Q$ is accepting, it is easy to prove that
$\GRE \proves \epsilon \limplies \pat_{\mathcal Q}$.
The remainder,
$\GRE \proves \pat_{\mathcal Q} \concat \top_\letter \limplies \pat_{\mathcal Q}$,
is then proved by applying the following lemma paralleling the the structure of the unfolding tree.

TODO: $n_a$ is not defined. We need to talk about this in terms of  the new NFA terminology.

::: { .lemma #lemma:top-implies-fp }
Let $n$ in be a node in the unfolding of tree of a  \emph{valid} regular expression. Then:

1.  if $n$ is a leaf node,        $\GRE \proves \pat(n)[\SubstFP_n] \concat \top_\letter \limplies \pat(n)[\Unfold_n]$, and
2.  if $n$ is an interior node,
    $$
        \frac{ \pat(n_a)[\SubstFP_{n_a}]\concat \top_\letter \limplies \pat(n_a)[\Unfold_{n_a}] \text{  for each $a \in A$} }
             { \pat(n)[\SubstFP_n] \concat \top_\letter \limplies \pat(n)[\Unfold_n]}
    $$

where,
\begin{align*}
\SubstFP_n &=
\begin{cases}
   \lambda                          & \text{when $n = \rootn$}\\
   \SubstFP_p[ \Psi_p / X_{L(p)} ]  & \text{when $\pat(p)$ binds $X_{L(p)}$}\\
   \SubstFP_p                       & \text{otherwise.}
\end{cases} \\
\Psi_p &= \hole \concat \top_\letter \cimplies \pat(p)[\Unfold_p] \\
\Unfold_n &= 
\begin{cases}
            \lambda                                      & \text{when $n = \rootn$}\\
            \Unfold_p[\pat(p) / X_{L(p)}]           & \text{when $\pat(p)$ binds $X_{L(p)}$}\\
            \Unfold_p                                    & \text{otherwise.}
\end{cases}
\end{align*}
:::

Here, we call $\Unfold_n$ the *unfolding* substitution.
It allows us to unfold a fixpoint pattern without changing its denotation.
This is, for a fixpoint pattern $\mu X \ldotp \phi$, we have $\eval{\phi[\Unfold_n/X]} = \eval{\mu X \ldotp \phi}$.

## Proving equivalence between expressions

To prove that two regular expressions are equivalent we may prove $\GRE\proves \alpha \liff \beta$.
As mentioned previously, proving this may be tricky because their inductive structure may not match.
To get around this, we may go via the automata lens.
Let $\Q$ be an automata with $\lang{Q} = \lang{\alpha \liff \beta}$.
We may now reduce the decompose the proof into two lemmas $\GRE\proves \pat_\Q$,
and $\GRE\proves \pat_Q \limplies (\alpha \liff \beta)$.
That is, that $\pat_\Q$ is valid ($\Q$ accepts all words)
and that the language of $\Q$ is a subset of $\alpha \liff \beta$.
The first lemma boils down to proving that $\GRE\proves \top_\word \limplies \pat_\Q$.
Notice that $\top_\word$ is equivalent to $\pat_{\mathcal T}$,
where ${\mathcal T}$ is the DFA with a single state that accepts every word.
This can thus be proved as per the previous subsection.

TODO: state definitions and inductive lemmas for this proof.


## Arden's rule and Salomaa's axiomatization

Arden's rule is a foundational theorem regarding languages.
In a sense, it captures the initiality of words, and distinguishes it from say $\omega$-words or streams.
So, even though it does not relate directly to our completeness result,
we will show that we can prove it, and use it to prove Salomaa's complete axiomatization..

::: { .theorem title="Arden's Rule"}
Let $A$ and $B$ be languages over an alphabet $\Sigma$.
Then the equation $X = A\concat X + B$ has a solution $X_0 = A\kleene \concat B$.
If $\epsilon \not\in A$, then this solution is unique.
In any case $X_0$ is the smallest solution.
:::

Arden's rule can be stated quite succinctly in matching logic:

::: { .theorem #thm:arden }
$\alpha\concat \beta\kleene$ is the least solution for $X = \alpha \lor \beta \concat X$.
Further, if $\epsilon \not\in \beta$, this solution is unique. We may formalize this in matching logic as:
\begin{align}
    \GRE  &\proves \beta \kleene\concat \alpha  = \mu X \ldotp \alpha \lor \beta \concat X
    \tag{Least Solution}\label{arden-least}\\
    \GRE  &\proves \epsilon \not\in \beta \limplies \beta \kleene \concat \alpha  = \nu X \ldotp \alpha \lor \beta \concat X
    \tag{Greatest Solution}\label{arden-greatest}
\end{align}
:::

This proof is particularly interesting because it involves proving that a
greatest fixedpoint implies a least fixedpoint (in \ref{arden-greatest}),
something the matching logic doesn't give us the tools to do out of the box.
To prove this, we extend derivatives to handle the above greatest fixedpoint pattern
and then use our previous completeness result to prove is as a schema over $\beta$.
When $\beta|_\epsilon = \emptyset$, we have:
\begin{align*}
\der{a}{\nu X \ldotp \alpha \lor \beta \concat X} &= \der{a}{\alpha \lor \beta \concat (\nu X \ldotp \alpha \lor \beta \concat X)} \\
                                                  &= \der{a}{\alpha} \lor \der{a}{\beta} \concat (\nu X \ldotp \alpha \lor \beta \concat X)
\end{align*}
It is easy to see that
$\GRE \proves (\nu X \ldotp \alpha \lor \beta \concat X) = \alpha \lor \beta \concat (\nu X \ldotp \alpha \lor \beta \concat X)$,
and so this extension preserves Lemma \ref{lemma:derivative-equivalence}.
It is also clear that Brzozowski's Theorem 5.2, stating that the derivatives of a regular expression form a finite set,
is preserved.
Instances of Arden's rule when $\alpha$ and $\beta$ are regular expressions
may now be proved easily through using the technique in the previous section.
This proof gives us the last piece of the puzzle needed to prove Salomaa's axiomatization of (unextended) regular expressions
shown in the Appendix.

TODO: Expand on this, the reviewers found this not detailed enough.


## Proving equivalence between a regular expression and an automata

To prove that a regular expression $\alpha$ and an automata $\Q$ have equal languages,
then we may prove $\GRE\proves \pat_\Q \liff \alpha$.
Again, this may be split into two lemmas, one for each direction.
In Subsection \ref{sec:xxx}, we saw how we can prove the forward direction $\GRE\proves \pat_\Q \limplies \alpha$.
The reverse direction, $\GRE\proves \alpha \limplies \pat_\Q$, is difficult because we have
$\pat_\Q$, whose inductive structure we need to use on the right-hand side instead of the left.
Fortunately, we may derive rules corresponding to \prule{knaster-tarski} and \prule{pre-fixpoint}
but for greatest-fixpoint patterns.

TODO: This is a new result.

# Proof Certificates

# Related Work

# Future Work


