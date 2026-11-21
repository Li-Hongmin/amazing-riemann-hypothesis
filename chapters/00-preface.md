# Chapter 0. Preface and reading guide

> Draft of 2026-11-21. Pinned sources: Lean archive sha256 `9631b4f0…9c7fc`, Alpöge's
> announcement sha256 `3fc97784…cfeb8d`, Masullo's draft sha256 `e039d3f6…97bf5`.
> Full hashes, URLs and retrieval times are in `sources/SOURCES.md`.

## 0.1 Why this book exists

On 20 November 2026 Levent Alpöge posted a four-page note, `https://alpo.ge/remark.pdf`,
which begins: "I believe I have, working with Claude, discovered a proof of the Riemann
Hypothesis." The note says that the method also proves "the so-called Generalized Riemann
Hypothesis", that he expects the Extended Riemann Hypothesis "with more time", and that the
arguments have been "formalized … without assumptions" in Lean [Paper; remark p. 1]. It gives no proof in
prose. Its footnote points to a Lean archive split into fourteen parts, and its second page
explains that an informal write-up generated along the way exceeded 250,000 pages and was
deliberately not posted [Paper; remark pp. 1–2].

The archive is large: 175,187 Lean files, 17,374,215 lines, about 1.03 GB of source (our
count on the pinned archive; the same figures appear in the community notes of
`leanprover-community/riemann-hypothesis`). Within a day, several groups had compiled it,
audited the axioms of its five final theorems and replayed it through independent proof
checkers; Chapter 1 records exactly what has been reported and what is still running.

A successful compilation tells us that the formal statements follow from the axioms of Lean's
type theory. It does not tell us *why* they follow. On that question the situation on the
day of writing is stark. The only human-written account of the argument is the four-page note,
whose description of the method is largely "a rough timeline Claude provided after a thorough
search" [Paper; remark p. 3]. The most careful public reading of the source, the reader's guide
of the independent LUMI checking effort (`github.com/aapolipponen/rh-lean-check-lumi`,
`docs/`), lists "most of the argument below the top levels" as not read by anyone, as far as
its reports know [Community].

This book, *Amazing Riemann Hypothesis*, is an attempt to explain, at the level of a graduate
student in number theory, why the Lean proof works: what each large block proves, how the blocks fit together, which parts
are classical, and where the new ideas sit. Alongside it we read Alessandro Masullo's
940-page draft *The Music of the Primes*, released the same day through Ravi Vakil's blog,
which claims a human-written proof of GRH for Hecke L-functions of all number fields by a
completely different method [Paper; Masullo p. 6]. The two documents have complementary defects: one is
machine-checked but unread, the other is readable but unfinished. Comparing them is
instructive about both.

## 0.2 What is and is not established (as of 2026-11-21, 04:42 UTC)

We separate four questions. Details and sources are in Chapter 1.

1. **Is the statement right?** The headline theorem proves Mathlib's own definition
   `RiemannHypothesis`, and the four further theorems use four short definitions that import
   nothing but Mathlib. We have read all of them and explain in Chapter 1 why they say what
   RH and GRH for Dirichlet L-functions say [Lean, read]. "GRH" here means Dirichlet
   L-functions only; Dedekind zeta functions and Hecke L-functions of other number fields are
   not covered.
2. **Does the formal proof check?** Compilation of all modules, an axiom audit showing only
   `propext`, `Classical.choice` and `Quot.sound`, a replay of every module by the Lean kernel,
   and acceptance by the independent checkers nanoda, con-leche and lean4lean have been
   reported [Community]. The end-to-end `lake comparator` run and the Lean kernel's replay of the
   exported proof were still running at the last public update [Open].
3. **Does anyone understand the proof?** Not yet. The top layers (the reduction to a
   single half-plane statement and the analytic endgame) are short and classical; we read
   them in Chapters 1–5. The arithmetic engine underneath is enormous and largely unread
   [Community; LUMI docs README].
4. **Is Masullo's argument complete?** No, by its author's own account: the introduction is
   unfinished, Chapter 13 — where GRH is to be deduced from the trace formula of
   Theorem 12.5.1.1 — consists of two pages that restate the trace formula, and the
   acknowledgements mention "several glitches here and there" [Paper; Masullo pp. 6, 521–522].

## 0.3 What this book adds to existing guides

Good material already exists, and we rely on it: the LUMI reader's guide (docs 01–10, with
AI-assisted review reports), the verification notes of the Comparator setup at
`leanprover-community/riemann-hypothesis`, Andrew Sutherland's verification page at
`math.mit.edu/~drew/grh/`, and, for Masullo, the formalization and errata project
`github.com/mccorvie/riemann-masullo`. These are organized module by module or check by check.
We cite them where we use their findings; we do not reuse their text.

The book differs in four ways.

- **One narrative.** The chapters follow a single line of argument from the final theorems
  down to the place where the exponent $1/2$ is produced, and then into the arithmetic
  machinery that justifies that step.
- **Every claim is tied to a declaration.** A mathematical statement that the archive proves
  is cited as `src/<path>:<line>` in the pinned archive, so that a reader can open the file
  and see it.
- **Every claim carries a status tag** (Section 0.4), and no tag claims more than we have
  actually checked.
- **Two proofs side by side.** Each chapter notes what, if anything, plays the same role in
  Masullo's draft; Chapters 14–15 make the comparison systematic.

Two companions support the narrative: `sources/SOURCES.md`, a map of every source we use with its
exact version, hash and a paragraph on what it contributes, and a running record of verification
(Chapter 1 for the statement and the machine checks, Chapter 16 for everything still open).

## 0.4 Status tags

We use exactly the six tags defined in the repository README.

| Tag | Meaning in this book |
|---|---|
| **[Lean]** | The statement is a declaration in the pinned build — the archive, or Mathlib at the commit the archive pins — and we cite it as file:line. We have read the statement; we have not necessarily read its proof. |
| **[Lean, read]** | As [Lean], and we have read the formal proof (or, for a definition, the definition) and checked that our prose says the same thing. |
| **[Paper]** | The claim is stated in a human-written mathematical source — Alpöge's note or Masullo's draft — and we give the page. We have not tied it to Lean ourselves. |
| **[Community]** | The claim is reported by others — a verification page, a community guide or review report, a formalization project, an expert's blog post or a press article — and we give the link; the version we read is pinned in `sources/SOURCES.md`. We have not checked it independently. |
| **[Expository]** | Our own explanation, heuristic or analogy. It is meant to help understanding and proves nothing. |
| **[Open]** | A gap, an unclear step, a disputed point, or a check that has not finished. |

Three conventions make the tags precise.

1. **Reading levels.** `notes/proof-map.md` records for each block whether we read the whole
   proof (R3), only the statement and the top of the proof (R2), or only located the
   declaration (R1). A chapter never tags a claim more strongly than the recorded level
   allows. In particular, "the archive proves a Prop called `PoitouTateDuality`" can be
   [Lean]; "that Prop is Poitou–Tate duality as in the literature" is [Open] until someone has
   compared them.
2. **Process facts.** Statements about who compiled what, which checker accepted which file,
   and which run is still in progress are reported facts, not theorems. They are tagged
   [Community] with their source and its timestamp, or [Open] if the check has not finished.
   Checks we ran ourselves (hashing the archive, a text scan, reading a file) are described
   with the command or script that reproduces them; they are not tagged as mathematics.
3. **Combining tags.** When a sentence mixes a formal fact and an interpretation, we split it
   or tag each part, for example "`core_gm` bounds $G_m(x)$ by $x^{1/2+(e_D+e_L+7)\varepsilon}$
   [Lean]; the exponent comes from choosing $m\approx\sqrt x$ lifts [Paper; remark p. 1]".

## 0.5 Citations

- **Lean archive.** Paths are relative to the archive's top-level `lean/` directory:
  `src/Main.lean:4` is line 4 of `lean/src/Main.lean` inside the tarball with sha256
  `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Line numbers refer to
  the line on which the declaration's header begins, unless the text says otherwise (a few
  citations point at an `import` line, a docstring, or a step inside a proof). The archive is
  not redistributed with this book; `sources/SOURCES.md` explains how to fetch and verify it.
- **Mathlib.** `Mathlib/<path>:<line>` refers to Mathlib at commit
  `0df444a360eaa60ab8c11dca51a86af692955474` (tag `v4.33.1`), the commit pinned by the
  archive's `lake-manifest.json`.
- **Masullo.** Section numbers and page numbers of the PDF with sha256 `e039d3f6…97bf5`
  (printed and PDF page numbers coincide).
- **Web sources.** URL and retrieval time (UTC) in `sources/SOURCES.md`; where a page
  changes over time we say which version we read.

Quoted Lean code is kept short and used for commentary. It remains the work of its authors;
the archive was published without a license (as noted by the
`leanprover-community/riemann-hypothesis` README) [Community].

## 0.6 The argument on one page

The following summary is the book in miniature. Each step names the chapter where it is
explained and tags what the step rests on.

1. **Five theorems from one half-plane.** All five final theorems follow from a single
   statement, `UpperTheory.EveryCharacter`: for every modulus $N\ge1$, every Dirichlet
   character $\chi$ mod $N$ and every $s$ with $\Re s>1/2$, $L(s,\chi)\ne0$ (except at the
   pole $\chi=1$, $s=1$) [Lean, read] (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13`).
   The reduction uses the functional equations of $\zeta$ and of primitive $L(s,\chi)$ and
   the Euler factors relating $\chi$ to its primitive character (Chapters 1–2).
2. **The half-plane from a one-sided bound on prime sums.** For a primitive $\psi$, consider the
   cyclic group of characters generated by $\psi$ and a positive combination $G_m(x)$ of the
   Riesz-weighted prime sums $\sum_{n\le x}\Lambda(n)\chi(n)(x/n-1)$, each normalized by its
   expected main term. If $0<\theta<1$ and $G_m(x)\le x^{\theta}$ for all $x$ in windows $[Y,Y^{1+\delta}]$
   with $Y$ arbitrarily large, then none of these $L$-functions vanishes on $\Re s>\theta$
   [Lean] (`src/Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean:8`;
   `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean:83`).
   This is a Landau-type argument: a one-sided bound suffices because the Laplace transform
   of $G_m(e^u)$ has its poles at the zeros (Chapter 3).
3. **The one-sided bound at exponent $1/2$.** The theorem `core_gm` gives
   $G_m(x)\le x^{1/2+(e_D+e_L+7)\varepsilon}$ for every large $x$ at which two bundles of
   data exist: "host" data `EAtH` and "chain" data `CoreAtH` [Lean]
   (`src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12`). Letting
   $\varepsilon\to0$ gives the half-plane $\Re s>1/2$ (Chapters 3–5).
4. **Where $1/2$ comes from.** The chain data describe a chain of $m$ "lifts" with
   $m\le x^{1/2+\varepsilon/2}$ [Lean] (hypothesis of `Deduction.ch_core`,
   `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:343`).
   According to the announcement and the LUMI reading, the chain imitates the high-order
   vanishing in Stepanov's proof of the Riemann hypothesis for curves over finite fields, each
   lift contributing one order of "multiplicity", and an error of size about $x/m+m$ is
   balanced at $m\approx\sqrt x$ [Paper; remark p. 1 and p. 4, timeline items 8–10] [Community; LUMI doc 04].
   We explain the function-field model in Chapter 6 [Expository].
5. **The engine.** Building the chain requires iterated theta lifts between definite unitary
   groups, $p$-adic divisibility of the chain at inert primes, Arakelov slope inequalities,
   near-orthogonality of periods, and a bound for the congruence modules of the lifts in terms
   of Tate–Shafarevich groups $Ш^1(\mathbb Q_\ell/\mathbb Z_\ell(-e))$ of abelian CM fields.
   The archive proves the Props that express these steps [Lean] (Chapters 7–10;
   `notes/proof-map.md`, P7–P11); what each Prop means in classical terms rests partly on
   reports we have not yet checked [Community].
6. **The window bound.** The needed bound on Tate–Shafarevich groups, `UpperTheory.Top.VWin`, is
   the single largest block of the archive. It is proved as `UpperTheory.One.vwin_of_row` [Lean]
   (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`),
   in a file whose import cone contains about 90% of all modules (our count,
   `notes/proof-map.md`). Its proof combines Iwasawa theory, Euler systems and
   a modularity theorem for residually reducible representations of $U(3)$ [Community; LUMI doc 06]
   (Chapter 11).
7. **Foundations.** Galois representations for automorphic forms on CM fields, a weak local
   Langlands correspondence, Green's classification of cuspidal characters of
   $\mathrm{GL}_d(\mathbb F_q)$ and about 250 named classical theorems are stated and
   proved inside the archive [Lean] (Chapters 12–13). Whether each named statement matches the
   published theorem of that name is a separate audit [Open].

Two remarks put this summary in perspective. First, steps 1–3 contain nothing that a specialist
in analytic number theory would find surprising: they are a careful, explicit version of the
classical principle that sufficiently good one-sided control of primes in progressions forces
zero-free regions [Expository]. All the novelty is in the existence of the chain data of step 4.
Second, nothing in steps 1–7 is "the Riemann hypothesis in disguise" in an obvious way — the
analytic inputs about auxiliary characters are zero-density and mean-value statements of
classical strength — but establishing that no hidden circularity exists is exactly the kind of
question this book is meant to make checkable. We return to it in Chapter 16 [Open].

## 0.7 Masullo's draft in brief

Masullo's draft works on the idele class group $C_F$ of a number field $F$. It builds spaces
of adelic theta functions and idelic zeta functions (Chapters 2–3, in the tradition of Tate's
thesis), Schauder and Markushevich bases, and Hardy–Sobolev completions (Chapters 4–9), and
it proves a trace formula equating a spectral side, in which the zeros of Hecke L-functions
appear with their multiplicities (Chapter 10), with a geometric side (Chapters 11–12). The
main theorem of the draft is the trace formula, Theorem 12.5.1.1 on p. 519 [Paper]. The
deduction of GRH for all unitary Hecke characters of all number fields is planned for
Chapter 13, which is not yet written beyond a restatement of the trace formula [Paper;
pp. 521–522]. The draft's acknowledgements say that Brian Conrad has been helping to
polish it and that he and the author "are aware of several glitches here and there" [Paper;
p. 6]. Vakil's announcement calls it "a proposed proof of GRH" and says that Conrad "has been
looking closely at it for months" and that it is "so far looking good to him" [Community].

Two facts matter for this book. Masullo's claimed scope is strictly larger than the Lean
theorem's: Hecke L-functions of all number fields versus Dirichlet L-functions of $\mathbb Q$.
And the two arguments share no machinery beyond the classical frame of functional equations and
explicit formulas; Chapter 14 explains Masullo's route and Chapter 15 compares the two.

## 0.8 Who should read what

- **Analytic number theorists.** Chapters 1–5 are self-contained and can be checked line by
  line against the Lean. Then Chapter 6 (the Stepanov model), Chapter 11 (the window bound)
  and Chapter 16.
- **Arithmetic geometers and automorphic-forms specialists.** Chapter 1, a quick pass through
  Chapter 5 to see what `core_gm` needs, then Chapters 6–13, where the unread parts are and
  where expert reading is most needed.
- **Lean users.** Chapter 1, `notes/proof-map.md`, Chapter 13 (the literature layer) and
  Chapter 16. Chapter 1 explains which Lean facts carry the statement's meaning and which
  checks remain.
- **Readers interested in the comparison.** Chapters 1, 3, 14 and 15.

Background assumed: complex analysis and the analytic theory of Dirichlet L-functions at the
level of H. Davenport, *Multiplicative Number Theory*, 3rd ed., revised by H. L. Montgomery
(Graduate Texts in Mathematics 74, Springer, 2000), or H. Iwaniec and E. Kowalski, *Analytic
Number Theory* (AMS Colloquium Publications 53, 2004, doi:10.1090/coll/053); for Part II, basic
algebraic number theory and Galois cohomology. Stepanov's method is explained from scratch in
Chapter 6, following E. Bombieri, "Counting points on curves over finite fields (d'après
S. A. Stepanov)", Séminaire Bourbaki 1972/73, exp. 430, Lecture Notes in Math. 383, Springer,
1974, pp. 234–241, doi:10.1007/BFb0057311. No knowledge of Lean is assumed; Chapter 1 introduces the few notions needed.

## 0.9 Authorship, method and corrections

The book is written by Hongmin Li with AI assistance (Anthropic Claude, OpenAI models) under
the author's direction. The proof is due to its announced authors, Levent Alpöge with Claude;
Masullo's draft is Masullo's. This book is commentary.

Our method is deliberately conservative. Every file:line in the book was located in our own
extraction of the pinned archive, and the citations are checked by a script before each
revision (`notes/proof-map.md`, "Reproducibility"). Where we depend on a community report we
say so. Where we do not know, we write [Open].

The state of verification is changing by the hour. Each chapter states the date of the
sources it uses; `sources/SOURCES.md` records exact versions. Corrections are welcome as
issues on the repository.
