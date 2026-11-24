# Sources: annotated bibliography and source map

Exact versions of everything the book cites. Times are UTC. "Retrieved" means our own download;
sha256 is of the bytes we received. Raw copies and the fetch logs are kept outside the
repository, in the run directory `~/Hermes/state/quota/runs/rhbook-architecture-11211200/`
(`sources/FETCH-LOG.txt`, `fetch_lean_parts.log`, `headers/`); nothing listed here is
redistributed with the book. The summaries below are ours; tags follow the README ([Paper] for
the two human-written mathematical sources, cited by page; [Community] for everything reported
by others, cited by link).

This file has two parts. **Part I** (below: the source map and the exact-version tables, first
written 2026-11-21 by run `rhbook-architecture-11211200`) pins the sources the mathematical
chapters cite. **Part II** (at the end: an annotated bibliography in six categories — primary
sources, verification, guides and teaching, errata and disputes, commentary, press — plus sources
surveyed only, added by run `rhbook-sources-11211242`) covers the wider public record and gives the
entry IDs that "The story so far" (`chapters/02-the-story-so-far.md`) cites.

## Source map: what each source contributes

**The Lean archive (Alpöge with Claude).** The primary object of the book: 175,187 Lean 4 files
(Lean v4.33.1, Mathlib v4.33.1) whose top file `src/Main.lean` proves five theorems — Mathlib's
`RiemannHypothesis` and four forms of GRH for Dirichlet L-functions defined in
`src/Statements.lean`. It contains no prose, no license file and no challenge file. Every
[Lean] citation in the book points into it by path and line (Section 1).

**Alpöge's note (`remark.pdf`).** Four pages posted on 2026-11-20 with the links to the archive
(footnote 1, p. 1). It announces the proof, made "working with Claude"; says that the method
also gives GRH and, the author expects, ERH; describes the argument as a descendant of
Stepanov's method in which a chain of theta lifts of length about $\sqrt X$ plays the role of
multiplicity (p. 1); explains why only the Lean code was released, mentioning an informal text
of more than 250,000 pages (p. 2); and lists a dated timeline of the main steps (pp. 3–4). It is
the only human account of the method. Cited as [Paper] with page (Section 2).

**Masullo's draft, *The Music of the Primes*.** A 940-page human-written draft released on
2026-11-20 through Vakil's blog, aiming at GRH for all unitary Hecke characters of all number
fields (p. 6). It builds adelic theta functions and idelic zeta functions (Chapters 2–3),
Schauder bases and Hardy–Sobolev topologies (Chapters 4–9), and a trace formula with a spectral
side (Chapter 10) and a geometric side (Chapter 12), Theorem 12.5.1.1 (p. 519). Chapter 13
(pp. 521–522), where GRH is to be deduced, is still a placeholder; Chapter 14 discusses
multiplicities, function fields and higher rank; Appendices A–E collect background. The
acknowledgements (p. 6) mention known glitches and Brian Conrad's help. Cited as [Paper] with
page (Section 3).

**Vakil's announcement.** Ravi Vakil's blog post of 2026-11-20, which released and hosts
Masullo's PDF. It reports that Conrad has studied the draft closely for months, that his feedback
is being incorporated and that it looks good to him so far, and that the work involves no AI.
[Community] (Section 3).

**The Masullo formalization project (`mccorvie/riemann-masullo`).** A community Lean
formalization of the draft's statements, proceeding in waves through the appendices and
chapters, with an errata log. Its README records that Chapter 13 does not yet state the main
theorem, that doubts about the trace formula raised on the Lean Zulip did not come from the
formalization, that its own last two target statements are reconstructions not yet reviewed, and
(at our 2026-11-22 03:30 UTC recheck, ~3,950 of ~4,700 stated theorems proved) that the printed
proof of Structure Theorem I (`Theorem 5.2.1.1`) in Wave 2 does not work as written. [Community]
(Section 3).

**Sutherland's verification page.** Andrew Sutherland's (MIT) log of machine checks, run with
Claude Code: compilation of every module, the axiom audit, `leanchecker` replay, the independent
kernels nanoda, con-leche (including `--compare`), and con-ron (`--compare`), lean4lean, an
independent bubblewrap-sandboxed `lake build Main` whose exported 61.57 GB proof stream matches
the published export byte-for-byte (`5ea74b91…244e`, added in the 2026-11-22 03:10 UTC update,
with 175,186 of 175,187 `.olean` files identical and the single 38-byte bound-variable race in
`LocModel.olean` isolated), and the status of the single-threaded Lean kernels on the export and
of `lake comparator` (still running as of 2026-11-22 03:10 UTC). The most detailed public record
of what has been checked. [Community] (Section 5).

**The LUMI check (`aapolipponen/rh-lean-check-lumi`).** Aapo Lipponen's independent sandboxed
build on the LUMI supercomputer: all modules compile, the hashes of `Main.olean` and
`Statements.olean` match Sutherland's, an axiom and dependency audit of 292 declarations, and the
count that `riemannHypothesis` uses 146,437 of the 175,187 modules. Its `docs/` form a reader's
guide (pages 01–10 and a glossary) edited from AI review reports, with explicit reading-status
markers and a list of what nobody has read. We use it for navigation and cite its findings as
[Community]; we do not reuse its text (Section 5).

**The Comparator setup (`leanprover-community/riemann-hypothesis`, moved from
`Deicyde/riemann-hypothesis`).** A mirror of the archive prepared for Lean's Comparator: a
challenge file stating the five theorems against Mathlib alone, CI, and verification notes that
review the statements, the dependency pins, the kernel fixes included in Lean v4.33.1, a static
scan and the archive's uses of metaprogramming. Its issue tracker holds build improvements and
readers' maps. No Comparator verdict had been posted at our last check. [Community] (Section 5).

**Mathlib at commit `0df444a`.** The eight Mathlib files whose definitions fix the meaning of the
five statements: `riemannZeta` and `RiemannHypothesis`, Dirichlet characters and conductors,
Dirichlet L-functions and their completions, the functional equations, non-vanishing on
$\Re s\ge1$, and the value assigned to $\zeta(1)$. Cited as [Lean] by path and line
(Section 4).

**Buzzard's Xena post (2026-11-12).** Kevin Buzzard's essay on what it means for a claimed proof
to be "checked in Lean", stressing that the first task is to compare the Lean statement with the
intended theorem. Quoted at the start of Chapter 1. [Community] (Section 5).

***Scientific American* (2026-11-20).** Clara Moskowitz's report on the verification effort,
quoting Sutherland's assessment and Buzzard's remark, made on the Lean community's chat server,
that a successful Comparator run was still awaited. Used only for those two quotations.
[Community] (Section 5).

**Literature.** Davenport's and Iwaniec–Kowalski's books are the analytic background the book
assumes; Stepanov's paper, Bombieri's Bourbaki exposé, Schmidt's monograph, and Hasse–Schmidt's
paper are our references for Stepanov's method and higher derivations (Chapter 6); Jacobi's
treatise, Weil's *Acta Mathematica* memoir, and the papers of Howe, Rallis, Kudla–Rallis, and
Gan–Takeda are our references for theta kernels and the theta correspondence (Chapter 7); Katz's
paper on $p$-adic Eisenstein series, Gillet–Soulé's and Bost's papers on Arakelov slopes,
Chowla–Selberg's and Siegel's papers on period/mass formulas, Ribet's and Hida's papers and
Bellaïche–Chenevier's monograph on Hecke congruence ideals and generalized matrix algebras, and the
papers and monographs of Iwasawa, Ferrero–Washington, Sinnott, Mazur–Wiles, Soulé, Rubin, Kato,
Taylor–Wiles, Clozel–Harris–Taylor, and Thorne are our references for the arithmetic engine of
Chapters 8–11; Harris–Taylor, Henniart, Bushnell–Kutzko, Shin, Caraiani, and Green are our
references for Galois representations, local Langlands, and finite general linear characters in
Chapters 12–13; and Hecke, Artin, Brauer, Tate, Weil, Grothendieck, Selberg, Hooley, Deninger,
Connes, Bombieri's Millennium Problem report, and Meyer are our references for Hecke/Artin
$L$-functions, explicit formulas, nuclear spaces, and idele-class spectral realizations in Part IV
Chapters 14–16 (Section 6).


**Chapter 3, §3.4.1.** In archive A2 (§1), `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LogDerivLocal.lean:9` consumes the finite-order factorization, and `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean:65,344,364,383` uses the resulting multiplicities and sign. The Mathlib bodies were checked online at the manifest pin. Beffara and Kebekus are credited in the analytic files. [Order.lean:71–134](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Order.lean#L71-L134) · [IsolatedZeros.lean:78–201](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/IsolatedZeros.lean#L78-L201) · [DSlope.lean:145–156](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/DSlope.lean#L145-L156) · [LogDeriv.lean:34–41](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/LogDeriv.lean#L34-L41)

**Chapter 3, §3.4.1, coefficient uniqueness and connected propagation.** The A2 call site is `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean:30–36,65` (joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`). The manifest pins the Mathlib sources below. Gouëzel authored the uniqueness file, Gouëzel and Kudryashov the change-of-centre and estimates files, and Beffara and Kebekus the isolated-zero file. The book gives scalar proofs of the tail estimate, coefficient uniqueness, re-centering and propagation and connects them to that call site. [Chapter 3](../chapters/03-landau-window-criterion.md#why-a-nonzero-analytic-germ-has-a-first-nonzero-coefficient) · [Uniqueness.lean:46–125](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Uniqueness.lean#L46-L125) · [Uniqueness.lean:159–217](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Uniqueness.lean#L159-L217) · [ChangeOrigin.lean:64–341](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/ChangeOrigin.lean#L64-L341) · [Basic.lean:683–773](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Basic.lean#L683-L773) · [ConvergenceRadius.lean:162–258](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/ConvergenceRadius.lean#L162-L258)

**Classical reference.** NIST Digital Library of Mathematical Functions, §1.10(i), equation (1.10.1) and the paragraph on multiplicity, and §1.10(ii), opening paragraph on analytic continuation. Version 1.2.8, released 2026-09-15, retrieved 2026-11-23 (HTML SHA-256 `b409528285039b541cae0157d4e2e9905762e436fd1b6de4d08576ba73b0826e`). It gives the classical expansion and multiplicity convention and the uniqueness used in analytic continuation. [Taylor expansion](https://dlmf.nist.gov/1.10#E1) · [Multiplicity](https://dlmf.nist.gov/1.10#Px2.p1) · [Analytic continuation](https://dlmf.nist.gov/1.10#ii.p1)

**Chapter 3, §3.4.1, weighted annular invariance.** The pinned Cauchy integral file applies planar divergence to a rectangle and obtains radius invariance via the exponential map. The book works out the orientations, the center limit and the pole-avoidance condition for complex scalars. The classical residue comparison was checked online on 2026-11-23 against NIST DLMF v1.2.8 (2026-09-15), §1.10(iv), equation (1.10.8). [Textbook subsection](../chapters/03-landau-window-criterion.md#weighted-circle-integrals-and-the-rectangle-theorem) · [Pinned CauchyIntegral, lines 186–453](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/CauchyIntegral.lean#L186-L453) · [Pinned planar divergence statement](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean#L503-L514) · [DLMF (1.10.8)](https://dlmf.nist.gov/1.10#E8)

**Chapter 3, §3.4.1, Cauchy expansion.** A2 calls the pinned Mathlib bridge at lines 30 and 60 of its pole-data proof. Yury Kudryashov authored the circle-integral and Cauchy-integral files. The book gives the scalar kernel argument with an explicit uniform error and two hand computations, using the weighted annular invariance proved in the accompanying subsection. NIST DLMF v1.2.8, retrieved online 2026-11-23 (HTML SHA-256 `8fcfc66cf1ebb81040cae6b075f307374c1d0b291449dd84a88de7e0e00d53f3`), gives the classical Taylor expansion and the coefficient integral in Laurent notation. [Chapter 3](../chapters/03-landau-window-criterion.md#from-complex-differentiability-to-a-power-series) · [Kernel series, lines 623–746](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/CircleIntegral.lean#L623-L746) · [Analyticity bridge, lines 589–651](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/CauchyIntegral.lean#L589-L651) · [DLMF (1.10.1)](https://dlmf.nist.gov/1.10#E1) · [DLMF (1.10.7)](https://dlmf.nist.gov/1.10#E7)

**Chapter 3, §3.4.1, rectangular divergence.** The pinned Mathlib proofs use local affine estimates in bounded-distortion tagged boxes, a summable error at countably many exceptional points, and a Bochner comparison before the product-integral step. The textbook gives the planar partition proof and works out the actual pullback in the Cauchy wrapper. Sources retrieved 2026-11-23. [Textbook subsection](../chapters/03-landau-window-criterion.md#rectangular-divergence-with-countable-exceptions) · [Planar and box proofs](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean#L108-L536) · [Gauge divergence](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean#L66-L279) · [Bochner comparison](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/BoxIntegral/Integrability.lean#L195-L301)

**Chapter 3, §3.4.1, Fubini and the box comparison.** The pinned planar divergence proof (§4) consumes the Bochner–McShane comparison at `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:121,128–136` and rectangle Fubini at line 531 of the same file. The book reads the comparison through indicator gauges, null functions and the three-term approximation by simple functions, which Yury Kudryashov's file bases on Gordon's monograph, and reads Fubini through slice measurability, null slices, the product-integrability criterion, the $L^1$ induction and the closure step, by Floris van Doorn, with the induction principle by Zhouhang Zhou, Yury Kudryashov and Heather Macbeth. Tonelli, the Bochner construction, simple-function density, regularity of Lebesgue measure and the box-integral foundations stay [Lean]. The classical counterexample with iterated integrals $\pm\pi/4$ was checked against [Shkoller2009] and [WikipediaFubini] (§6). Sources retrieved 2026-11-24. [Textbook subsection](../chapters/03-landau-window-criterion.md#fubini-and-the-box-comparison-on-a-rectangle) · [Comparison](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/BoxIntegral/Integrability.lean#L37-L301) · [Fubini](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Prod.lean#L126-L512) · [Product measure](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Prod.lean#L71-L781) · [Induction principle](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean#L805-L932)

**Chapter 3, §3.4.1, the Henstock–Sacks inequality.** The comparison proof above groups the cells of an admissible partition by the index $n(p_J)$ and controls each group by the Henstock–Sacks inequality, previously input (N6). The book now reads Yury Kudryashov's pinned proof body: the common completion of two prepartitions with the same union (`dist_integralSum_le_of_memBaseSet`), integrability on subboxes through the Cauchy net, and the $\pi_0$ form with the constant $\delta/(m+1)$ (`dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`), together with the admissibility bookkeeping in `Partition/Filter.lean`, `Partition/SubboxInduction.lean`, `Partition/Tagged.lean` and `Partition/Split.lean`. The filter description of the integral, Cousin's lemma, the splitting construction of the complement and two filter facts stay [Lean] as (N6a)–(N6d). The classical statement was checked against [Fremlin2010] and [EoMKurzweilHenstock] (§6). Sources retrieved 2026-11-24. [Textbook subsection](../chapters/03-landau-window-criterion.md#the-henstocksacks-inequality-tagged-sums-over-part-of-a-rectangle) · [Henstock–Sacks bodies](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/BoxIntegral/Basic.lean#L410-L594) · [Admissibility](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/BoxIntegral/Partition/Filter.lean#L282-L493) · [Completion](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/BoxIntegral/Partition/SubboxInduction.lean#L94-L234) · [Grouped call](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/BoxIntegral/Integrability.lean#L261-L285)

**Chapter 9, §9.4.5.** The joined Lean archive in §1 supplies the cone predicate
`src/Formalism/HermitianCurvature/StatementPB.lean:89,125,133` and the two conditional
proofs `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean:384,602`
[Lean, read]. The direct rank-one factorization dependency was checked online at the
Mathlib pin in §4. [Mathlib, `Positive.lean`, lines 544–566](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Positive.lean#L544-L566)
**Chapter 4, §4.7.** The joined Lean archive in §1 supplies the zero-density proof
`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13` and its
`CountZ*` files, read with their direct dependencies [Lean, read], and `page_across`
(`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPage.lean:37`). The classical
comparison uses Bombieri1965, Bombieri1971, Montgomery1968, Montgomery1969, Montgomery1971, Huxley1972,
Huxley1975, Page1935 and Siegel1935 (Section 6), and Masullo's Appendix B.4 and B.6 from the PDF in §3
(sha256 rechecked 2026-11-23).

**Chapter 4, §4.8.** The pinned Alpöge–Claude archive (§1) supplies the box log-derivative estimate and the contour bounds. The [declaration map](../chapters/04-auxiliary-prime-pairs-and-host-fields.md#48-from-the-zero-free-box-to-the-truncated-perron-tail) identifies the consumed kernel in `TailContourB` and lists the remaining R2 suppliers. The proof and constants come from the archive. The worked example and conditional exposition are the book’s.

**Chapter 4, §4.9.** The pinned Alpöge–Claude archive (§1) supplies the count and threshold in `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean:13–397`. The [declaration map](../chapters/04-auxiliary-prime-pairs-and-host-fields.md#49-counting-enough-candidates-before-the-sieve) follows the count into the pair and window constructions. Siegel1935 and Davenport2000 (§6) provide classical background. The exact relative estimate and real-zero separation used here are the archive statements, retained as named inputs. The examples and exposition are the book’s.

**Chapter 4, §4.10.** The pinned Alpöge–Claude archive (§1) supplies the character normalization, near and far estimates, splice and transfer to prime counts. The [source map](../chapters/04-auxiliary-prime-pairs-and-host-fields.md#410-joining-the-two-ranges-of-the-relative-progression-estimate) gives the proof bodies and the named analytic inputs. Davenport2000 (Springer catalogue and contents) and Siegel1935 (IMPAN and Crossref, pp. 83–86) were rechecked on 2026-11-23 for classical context. The two parameter examples and overlap calculation are the book’s.

**Chapter 4, §4.10.5.** The pinned Alpöge–Claude archive (§1) supplies `num_alg`, `num_main` and their consumer in `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean:7–158` and `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsm.lean:15–166`. The [source map](../chapters/04-auxiliary-prime-pairs-and-host-fields.md#4105-the-far-range-numerical-absorption-lemma-num_main) separates the proof bodies read in full from the analytic suppliers kept at R2. Gallagher1970 (Crossref and publisher metadata) and Tao2015 (Exercise 5 and Theorem 2) were checked on 2026-11-24 for the classical comparison; see the update entry below. The three calculations, the legal parameter set and their placeholder constants are the book’s.

**Chapter 10, §§10.4.5–10.4.6.** The joined Lean archive in §1 supplies the DVR determinant lemma
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DeterminantLemmaDiscreteValuationRingQuotientLen.lean:259`, the block-determinant lemmas
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetOneAddSmulBlkMem.lean:89` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CMemCoeffSub.lean:99`, the solution-module bound
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:77`, the peeling lemma
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthEqInfKerAddMap.lean:52`, the cyclotomic-block bound
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCyclotomicBlockCocyclesLeSha.lean:372`, the class-number bound
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexDvdClassNumber.lean:172` and the twist lemma
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:8`, read with their direct dependencies [Lean, read]. The
Mathlib leaves cited there (`IsLocalRing.length_restrictScalars`, `Polynomial.coeff_det_X_add_C_card`,
`Module.length_eq_add_of_exact`) were located at the pin in §4. The comparison uses Ribet1976,
MazurWiles1984 and SkinnerUrban2014 (Section 6); the archive cites none of them.

**Chapter 10, §10.4.7.** The pinned archive supplies the all-powers choice and transport,
the matrix-and-bounds construction of the auxiliary-prime proposition, and the
degree-one Chebotarev producer, with exact declaration locations in the chapter.
The author-hosted Skinner–Urban PDF was fetched again on 2026-11-23, with the same
SHA-256 as in Section 6. The contents and the section heading both print
“Constructing coycles”. The book's open PR #2 proposes a separate Chapter 16 example
comparing cubic and abelian Frobenius traces at 31 and 367. [Book PR #2](https://github.com/Li-Hongmin/amazing-riemann-hypothesis/pull/2)

**Chapter 10, §10.4.7.1.** The pinned archive (§1; tarball SHA-256 rechecked on 2026-11-24, and the twelve
cited files compared byte for byte with the tarball members) supplies the lattice transport `export_at`, its
lemmas and the reference family in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:17–496`, the signed-index lemmas in
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCommensurableOfIsLatIn.lean:16–70` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LenRBaseChangeSubquotient.lean:14–75`, the
all-powers assembly in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:17–64`, and the `partAB` steps of
the three producers, read [Lean, read]. The integrality suppliers are cited at statement level, while §10.4.7.2 reads `propABCD_of_rel` and the level lemma behind
`exists_level`. The comparison with the classical
lattice invariant uses SerreLocalFields, Ch. III, §1 (Section 6). [Declaration map](../chapters/10-congruence-modules-to-sha.md#10471-lattice-specialization-one-index-bound-for-every-coprime-power)

**Chapter 10, §10.4.7.2.** The pinned archive (§1; joined `lean.tar.gz` SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` rechecked on 2026-11-25, with all twenty cited `.lean` files verified byte-identical to their tarball members) supplies the conditional toric determinant proof `GlobalTheory.TwistDet.propABCD_of_rel` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:14–466`, called at `TwistTheoremAllPowersOfSelmerSupLattice.lean:35`) with its grid-vanishing, same-lattice index, common-eigenvector, and open-subgroup helpers (`IndexSpanMatrixEqValDet.lean:17–510`, `ExistsSubgroupIsUnit.lean:37–267`, `IsPlaceOverMoveValCc.lean:16–199`, `DvdTraceOfBalancedTensor.lean:7–34`), and the simultaneous level-order-exponent proof `GlobalTheory.T.exists_level_order_exponents_small_valuation_determinants` / `OrderEval.order_eval` (`ExistsLevelOrderExponentsSmallValuationDeterminaStatement.lean:5–6`, `ExistsLevelOrderExponentsSmallValuationDetermina.lean:15–377`, called in `IsAuxiliaryPlaceFamilyAtLevelMono.lean:321–353`) with its Tychonoff limit, Kronecker weight-separation, prime-power binomial divisibility, Weierstrass cancellation, and Newton-polygon tie-count lemmas (`ExistsLimitFamilyOfFiniteCoefficients.lean:7–26`, `ExistsExponentStrictlyLeastWeight.lean:9–48`, `NotDvdCoeffAevalOneAddXPowSubOne.lean:38–94`, `PowSubDvdChoosePrimePowOfLt.lean:6–35`, `CoeffAevalOneAddXPowSubOneNeZero.lean:23–55`, `ExistsLowCoeffNotDvdOfCongrMul.lean:12–66`, `NormalizedValuationPrimitiveRootPrimePowSubOne.lean:23–52`, `NormalizedValuationAlgebraMapEq.lean:41–49`, `ValuationPolynomialAtRootOfUnitySubOne.lean:10–193`), read at local `[Lean, read]` (`R3`). Deep twisting, Hecke, SNF, and Selmer inputs (`ThURel`, `AllGood`, `HkComm`, `OffRange`, `adm8`, `LengthQuotientSpanValuation.main`, `propE`, `GaloisSideTwistedSelmerAuxiliaryPrimes`) remain at `[Lean]`. Classical comparisons use Alon1999 (Theorem 1.1 and Lemma 2.1), SerreLocalFields (Ch. III, §1, Proposition 2), and Washington1997 (Proposition 2.1) in Section 6; Mathlib supplies `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` and `exists_clusterPt_of_compactSpace` at commit `0df444a360eaa60ab8c11dca51a86af692955474`. [Declaration map](../chapters/10-congruence-modules-to-sha.md#10472-toric-hecke-relations-and-simultaneous-level-exponent-selection)

**Chapter 10, §10.4.8.** The pinned archive (§1) supplies the tame dual-number relation and the conditional first-order Selmer argument in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TameLocalRelationDualNumberCocycle.lean:12–159` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerDeterminantOrderBound.lean:118–350`. The [chapter's declaration map](../chapters/10-congruence-modules-to-sha.md#1048-from-tame-inertia-to-the-order-of-a-selmer-determinant) gives the two consumers of `stepAB` and the hypotheses retained at the global Selmer boundary. SerreLocalFields is classical ramification background.

**Our derived data.** Declaration index, import graph, text scan and citation check, all
reproducible from the archive (Section 7).

# Exact versions

## 1. The Lean archive (primary source)

Chapter 8, Section 8.4.4 reads the local kernel expansion in
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelExpansionOfRestrictions.lean:116,136`
at the joined archive hash below. Its proof uses
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/NatCastInvMemRp.lean:52`
for factorial integrality and
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/InClassOfExp.lean:143`
for the finite coefficient expansion. Section 8.4.5 follows the production of the packet fields
`VolumeRatio₂` and `LowTermBound` through
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpV.lean:28`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaGeCOfNorm.lean:91`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/LiftBoundOfIntegrality.lean:103` and
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/YEPEComm.lean:131`, to the reader
`src/Formalism/SharpRestriction/GrowthBounds/JointsTw.lean:23,243`. Both sections depend only on the
archive for proofs; Katz1976 is background to the chapter, and LUMI's `docs/04-chain-and-one-half.md`
(re-fetched 2026-11-23; see Updates to Part I) is the community outline we compare against. The
finite-jet calculation and the explanation of these Lean declarations are the book's exposition.

**Chapter 5, §5.3.1.1.** The archive supplies the inertia orthogonality and the two
prime-power branches in `GaloisMapComplexConjugation.lean`:129,145,155,167,209,233.
The actual coefficient call is `PrimitiveCosets/PrimRead.lean`:56–61. The
[section's declaration map](../chapters/05-the-square-root-barrier-core-gm.md#5311-why-inertia-averaging-recovers-the-primitive-character) gives the full paths and the joined SHA-256.
The mod-$20$ example and proof exposition are the book's. Lipponen's
[LUMI guide to the chain and the exponent one-half](https://github.com/aapolipponen/rh-lean-check-lumi/blob/c6d0e2bc06/docs/04-chain-and-one-half.md)
supplies community context for the larger character-sum argument (§5 below).

Author's original parts, `https://alpo.ge/lean.tar.gz.partNN`, NN = 01…14, as linked in
footnote 1 of the announcement. Downloaded 2026-11-21 04:01:46–04:05:21 with `curl`; every part
answered `HTTP/2 200`; the server sent no `Last-Modified` header. (The server also answers 200
with an HTML page for parts that do not exist, so the joined hash below is the real check.)

| Part | Retrieved | Bytes | sha256 | ETag |
|---|---|---:|---|---|
| part01 | 2026-11-21T04:01:46Z | 18000000 | `86974b1c242ca7b6748f3299df4fc64ee0f6e06c776ac964fb64888101a3de77` | `b116580303b65e25529dae6e694a3bab` |
| part02 | 2026-11-21T04:01:59Z | 18000000 | `1c2a2477354a9dfa97ff1ce54861e96ed885bd456fffbaaabc2028314a229c42` | `47a77f2884ae9185547ee36e4c9cf397` |
| part03 | 2026-11-21T04:02:12Z | 18000000 | `1465a23b1b579a881e24e5ffaf7c4c3727af28ea24741f1ec80e1d67947530a3` | `9e114ce09eabe6118621772d21e1813c` |
| part04 | 2026-11-21T04:02:23Z | 18000000 | `3929e327eecb4e2c5c7cae30e104e6a4a52fa6b82d28325bcda8e9da1c86893b` | `edcca56981307792c45f36cf3482c39b` |
| part05 | 2026-11-21T04:02:39Z | 18000000 | `f25d7e80f7c4ad6d674aa18b323ca760f848857c8755501c149317c38a66c75d` | `fe2185367f419c5af1a93a6ca39dd52b` |
| part06 | 2026-11-21T04:02:50Z | 18000000 | `a8c651a68327811b37dce3cca8eda5e0b2102fa227c0d395cbb7553e4dd69939` | `3c430339a285463888abf3979c66353e` |
| part07 | 2026-11-21T04:03:03Z | 18000000 | `65c7e502a9b236a0f68d9e0aa6e089d4c09b9fc7a0960a149384063ccbe5e869` | `0e202b477aa10e6ce56593952cfe9932` |
| part08 | 2026-11-21T04:03:14Z | 18000000 | `71b027ad6e4179c3a50ce72921e3fec0a2dd751ec7472ac2c644ad145a50ec7e` | `687cc9a31b1117665e8d547dfc4d8d78` |
| part09 | 2026-11-21T04:03:31Z | 18000000 | `47718977ebaa8613f1647e93134479780db9320c5fa911463fd312a6257b796f` | `3e707df7cceb335083d5d4b246f7766c` |
| part10 | 2026-11-21T04:03:47Z | 18000000 | `1d85ece78e0779cec26b0cce29c6462d9f90180e56d78120b152df101715240b` | `76ba0730abcd0dc30c763d804e904ded` |
| part11 | 2026-11-21T04:04:01Z | 18000000 | `cf83a159d1a9540012229c376562587dd966da10cd657cbcef53acfd03232448` | `1564eacf9229f51a692673d67aafda05` |
| part12 | 2026-11-21T04:04:55Z | 18000000 | `1aa5415bd2db83b2689afeeb946419303b3c4f599ae790ad74d38465f768b502` | `599c8bfc235b218972f074276126643e` |
| part13 | 2026-11-21T04:05:09Z | 18000000 | `2de4edbce8ebdbfd0b94bc89bab518c7294209f408ec5b14a7be9e4832d9da81` | `004a3be6a80ad529c057d7572be98f8d` |
| part14 | 2026-11-21T04:05:21Z | 5275554 | `53f8ea43a9b5dcab97b84a52f3ac2848711c844a5420a4c56418093bacb3c6f6` | `8a60f30a51ada38b89908f1ab8fcd86c` |

**Joined archive** `lean.tar.gz` (parts concatenated in the order 01…14): 239,275,554 bytes,
sha256 **`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`**, verified
2026-11-21T04:06:03Z. This is the value published by Sutherland's verification page, the LUMI
run and the leanprover-community notes, and the value of our earlier download
(2026-11-21T03:01:59Z, run `rheval-1121/opportunity`).

Pitfall: macOS's `/bin/bash` (3.2) does not zero-pad the brace range `{01..14}`, so
`cat lean.tar.gz.part{01..14}` silently skips parts 01–09 (our first join gave 77,275,554
bytes). Use `for i in $(seq -w 1 14); do cat lean.tar.gz.part$i; done > lean.tar.gz`, or zsh.

Extracted locally outside this repository: 175,187 `.lean` files under `src/`,
17,374,215 lines, 1,030,531,854 bytes of source. `lean-toolchain` = `leanprover/lean4:v4.33.1`;
`lakefile.toml` pins Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`;
`lake-manifest.json` pins plausible `b7eb3304`, LeanSearchClient `5f4d51b8`, importGraph
`16f02aa7`, proofwidgets `4be2e3d5`, aesop `3448c0bc`, Qq `92c15be1`, batteries `4488d40d`,
Cli `6130a478`. The archive contains no license file and no challenge file.

## 2. Author's announcement

| Item | URL | Retrieved | Bytes | sha256 |
|---|---|---|---:|---|
| Four-page note | `https://alpo.ge/remark.pdf` | 2026-11-21T04:02:18Z | 245114 | `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d` |
| Home page | `https://alpo.ge/` | 2026-11-21T04:02:15Z; rechecked 04:42:17Z | 11625 | `a7ee08f4821ec5bfdebbc8860730b497b3e252a49fadc14d0d888c9e38a25276` |

Both are byte-identical to our copies of 2026-11-21T02:51Z (run `rheval-1121/opportunity`); no
further write-up had been posted at the recheck. Page references ("remark p. 3") are to the
PDF's four pages.

## 3. Masullo's draft

| Item | URL | Retrieved | Bytes | sha256 |
|---|---|---|---:|---|
| A. M. Masullo, *The Music of the Primes* (940 pp.) | `https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf` | 2026-11-21T04:05:30Z | 6756996 | `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5` |
| R. Vakil, "Hurried Announcement: Alessandro Masullo GRH" (blog post, 2026-11-20) | `https://math216.wordpress.com/2026/11/20/hurried-announcement-alessandro-masullo-grh/` | 2026-11-21T04:05:38Z | 76305 | `35796196c7483539808483fe19962596959e13cb19c2053e0b2aedd461b1828f` |
| Formalization project `mccorvie/riemann-masullo`, README | `https://raw.githubusercontent.com/mccorvie/riemann-masullo/main/README.md` | 2026-11-21T04:05:40Z | 8899 | `69352b475c7a8b58785d2d0e4ae50bb944cf7e7f79d422f8c36e81794e223b9f` |

The PDF is byte-identical to our copy of 2026-11-21T03:01Z. Printed page numbers coincide with
PDF page numbers (checked on pp. 6, 13, 519, 521, 522). The blog page is dynamic; we cite only
the text of the post. At our 2026-11-22T04:35Z recheck (`fetches/mccorvie_README.md`, 14,590 bytes,
sha256 `9072dc8b625f3b07e02b5e60be1edef38816c975aee2f5c03f2b05a1a4be5c2e`), `mccorvie/riemann-masullo`
had ~4,700 theorems stated, ~3,950 proved across ~1,360 merged PRs, Wave 3 (Chapters 10–13) seeded
as section issues, a `lake comparator` setup on Lean `v4.36.0`, and ~200 entries in `ERRATA.md`.

## 4. Mathlib at the pinned commit

All from
`https://raw.githubusercontent.com/leanprover-community/mathlib4/0df444a360eaa60ab8c11dca51a86af692955474/<path>`.

| Path | Retrieved | Bytes | sha256 |
|---|---|---:|---|
| `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` | 2026-11-21T04:02:31Z | 12306 | `db9f37f08bcce379c502549f604c0e98bf4a39b3a3440606861bbac847f2a1a9` |
| `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` | 2026-11-21T04:10:40Z | 18979 | `86d3aaad83e64cb64a24167fd4ddb2eeec5ca4a19a9298459e87a57fec151040` |
| `Mathlib/NumberTheory/DirichletCharacter/Basic.lean` | 2026-11-21T04:10:41Z | 26329 | `f004670a9bedc23c4dfaeb61b90d5e613a6b604f9486640eb1ce4ae3699ef64e` |
| `Mathlib/NumberTheory/LSeries/ZMod.lean` | 2026-11-21T04:10:42Z | 28254 | `8b65bc72be88177c735a919cc1deba62d62397796dfb9eae24e6609e24212ea3` |
| `Mathlib/NumberTheory/LSeries/HurwitzZeta.lean` | 2026-11-21T04:10:42Z | 8543 | `181fcf0d1e92ef1d38d1fccecf313d814b6511913aee8e6c4f2d720d0cb5220d` |
| `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` | 2026-11-21T04:10:43Z | 21780 | `945a2fd23ca9ebd2d48f101d771ef9117dd9847d48fd77ea2623d8c345f4f5a9` |
| `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean` | 2026-11-21T04:13:24Z | 32972 | `3eb3f0864a28c7085e7f37917e50e024e5dfa2073821e3324b3873f050dfed89` |
| `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean` | 2026-11-21T04:30:15Z | 39471 | `db0a44702615c879abb084e3d950085f0f9b3fd71fddbf57105ad4d9cfea92e8` |
| `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` | 2026-11-22T09:15:00Z | 21422 | `44a7d25a608a4242693b5b4f849c27ea0075ba585d9db48f16bbfe84df4ab5b5` |
| `Mathlib/RepresentationTheory/FinGroupCharZero.lean` | 2026-11-23T09:12Z | 4915 | `a031d85058b58616a33fac9b7f0a812ec6452d95a8e0e330734636fd485753c9` |
| `Mathlib/RingTheory/WittVector/Teichmuller.lean` | 2026-11-24T10:50Z | 4589 | `d67df6e0011067d6c78f4d9e1ec9914dd7e2fc502d8e1f7f267ac0ae4f0bc957` |
| `Mathlib/RingTheory/WittVector/Basic.lean` | 2026-11-24T10:50Z | 13227 | `dc9e2c2285cdfd4e72615841c22310a6312ac1385b0821b47dfa3acc05763045` |
| `Mathlib/RingTheory/WittVector/Domain.lean` | 2026-11-24T10:50Z | 3733 | `33f6631f8d62536e6e95153b3a4605d90b7a54d41def019ddacd16d5b3506f50` |
| `Mathlib/RingTheory/WittVector/Compare.lean` | 2026-11-24T10:50Z | 8129 | `998c8b8a4e9762170eb940cd239dab54bccf1323ad7f65e61bd347f3b68c137f` |
| `Mathlib/RepresentationTheory/Character.lean` | 2026-11-24T13:21Z | 9213 | `e5da5f309a87c34f67acb96b0f62adff7eb4e7464e7c9b4b67cf9e3399bec5fb` |
| `Mathlib/RepresentationTheory/Irreducible.lean` | 2026-11-24T13:21Z | 3720 | `6a9dab1cec7b8e57ff3e44f013fbacc789a941296cdc80c8fc8763eb96b76d13` |
| `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean` | 2026-11-24T13:24Z | 3797 | `feabf983b515b06af01a87777f299e192119f724d3e55d0a30c2d219da94acb8` |
| `Mathlib/Analysis/BoxIntegral/Integrability.lean` | 2026-11-24T13:50Z | 20146 | `95f4fcbf225612191084761616d1a9e5b1260bad4fd79b675f2ef8fab15c5f34` |
| `Mathlib/Analysis/BoxIntegral/Basic.lean` | 2026-11-24T14:02Z | 51364 | `68d3c7e2f6d03cbdf78966fd773b49973db57c41e197e37bf2eff1716c2d5c36` |
| `Mathlib/Analysis/BoxIntegral/Partition/Filter.lean` | 2026-11-24T14:02Z | 28335 | `96cf847c15739bc5465abeaa44e3b89dd399e65dce9b941c31be9215e5a98b04` |
| `Mathlib/MeasureTheory/Integral/Prod.lean` | 2026-11-24T13:50Z | 32393 | `c7d4d23349591c5c65aa5b1b6024331fb0b7f22e9b2b08d6a1fe19b1c258ec5b` |
| `Mathlib/MeasureTheory/Measure/Prod.lean` | 2026-11-24T13:50Z | 61776 | `739ba1838b5b67c1ff5d3b43ed263c2ad34f91e01e7a8946a6f529922d463e79` |
| `Mathlib/MeasureTheory/Function/SimpleFuncDenseLp.lean` | 2026-11-24T13:50Z | 42632 | `b1ecbd32e34997ddc82627f777d350abb79f4b26e107588c2eef84f46489f067` |
| `Mathlib/Analysis/BoxIntegral/Partition/Tagged.lean` | 2026-11-24T14:49Z | 16695 | `e123ed5591679e8fbff485a4307c62b93299618db2753a3e9ba7f6502bdbcbe7` |
| `Mathlib/Analysis/BoxIntegral/Partition/SubboxInduction.lean` | 2026-11-24T14:49Z | 10607 | `58c81caf56887b7dcf778326c857d8bf9490143d8de3ad76001e34e001714f7f` |
| `Mathlib/Analysis/BoxIntegral/Partition/Basic.lean` | 2026-11-24T14:49Z | 30786 | `f4aa207b4d0fc20d3dc249dbe5bb31ef518a29a1a35fa6a5c8981b3b3c0005df` |
| `Mathlib/Analysis/BoxIntegral/Partition/Split.lean` | 2026-11-24T14:50Z | 16127 | `d92e9e64b75db511d9f885aeff65ecea19ae4b60ee19b645e99ec58d7aa8d195` |
| `Mathlib/Analysis/BoxIntegral/Partition/Measure.lean` | 2026-11-24T14:50Z | 4580 | `f209fcff7b6874f83850875c364d67681b5a8e82c0b21b4078d5779c814bff92` |
| `Mathlib/Analysis/BoxIntegral/Box/Basic.lean` | 2026-11-24T14:50Z | 19219 | `161e399385de199889666ac58c366a723368989a3a1920a5aaea40d57991fe07` |
| `Mathlib/MeasureTheory/Function/SimpleFuncDense.lean` | 2026-11-24T14:23Z | 11999 | `faedff2e7de88c962fa4b94f6c9a3664a82ffa218461930353f424e789a52ba6` |
| `Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean` | 2026-11-24T13:50Z | 33762 | `7801deae1fa630bca3f1966f17b9005e0e9dfc86be62f7abd14e88bece1a26cc` |
| `Mathlib/Analysis/Complex/CauchyIntegral.lean` | 2026-11-24T13:50Z | 45558 | `7a2022a8a02dbef3b5466edd2ba9e4123a898f1e0b0dc5dc320104832405f14b` |
| `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` | 2026-11-23 UTC | 22917 | `720a9a72d742fbe1c9a89601dc3a00d82c0261c7368c98cccb58307dbffe3bbf` |
| `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean` | 2026-11-23 UTC | 28664 | `a7ac57c81c4e23a96885104166140fe33905bc46ff564203d9376b96bc494c99` |
| `Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean` | 2026-11-23 UTC | 9148 | `ea87e1b821adbe190be9655314f5ab3fa299276dd413a1401faa175437726fcb` |
| `Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean` | 2026-11-23 UTC | 15341 | `0988322f130952835b0da8d43d24b44c281af10bf149bb869ac750160ec1d5ac` |
| `Mathlib/MeasureTheory/Integral/PeakFunction.lean` | 2026-11-23 UTC | 27776 | `184a2c7bf02b3a64bdd2d6b68a684aa064b195d08c41b64c865d13906132bc29` |
| `Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean` | 2026-11-23 UTC | 12403 | `1f1ac074643b510181a749184849d8e7ee4bf6826bbac8b81e37a990f4e91f2a` |
| `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` | 2026-11-23 UTC | 17746 | `96a282f317e96505e89e51553f8129e52f381953dd142ee269f2525cb00f6197` |
| `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean` | 2026-11-23 UTC | 20585 | `5555dbaa4313f7590501bc8b6ea0d0a387de82ae40d9aa235e9c58ba0472cc85` |
| `Mathlib/Analysis/Convolution.lean` | 2026-11-25 UTC | 49907 | `2e02a96b2ee6de4b52b6414aa938fd46f89690939d5c86964071b73a88dbd184` |
| `Mathlib/MeasureTheory/Integral/ExpDecay.lean` | 2026-11-25 UTC | 1852 | `d7398961c690ff61535dd0e9befcbdd00988c564a5c9a6d986feed2859db7cea` |
| `Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean` | 2026-11-25 UTC | 12508 | `4e91cccdec97e9173e71a383db8a53d945baa1332f1892b6ca575b627ab18a3d` |
| `Mathlib/MeasureTheory/Integral/Asymptotics.lean` | 2026-11-25 UTC | 9283 | `206d3f200f208f572a85a067ffbfe92e5f3a3a89e4c8d19ec8b721c17168a204` |
| `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` | 2026-11-25 UTC | 50301 | `1f4e64fc28a20f4e19291a94dafd68daa82588b46f6ee5b9203df373ba595fa3` |
| `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean` | 2026-11-25 UTC | 19622 | `004e4d6013b20f95feedfcb23b257c07eb1ee4c7645b9d81fd6e4cb684a116d6` |

Chapter 13 §13.4.10 re-fetched `FinGroupCharZero.lean` on 2026-11-24T13:21Z (same SHA-256) and reads
`FDRep.simple_iff_char_is_norm_one` with `simple_iff_end_is_rank_one` (lines 90–128). From `Character.lean`,
`Irreducible.lean` and `GeneralLinearGroup/Card.lean` it uses the statements of `char_one`,
`card_inv_mul_sum_char_mul_char_eq_finrank`, `char_orthonormal`, `scalar_product_char_eq_finrank_equivariant`,
`IsIrreducible`, `irreducible_iff_isSimpleModule_asModule`, `finrank_intertwiningMap_self` and
`card_linearIndependent`, at the lines given in Table 13.4.10.

Chapter 2 §2.3.1 follows `DirichletCharacter/Basic.lean:66–158,173–196,233–319,333–360`
for the transition from admissible levels to recovery and the divisibility minimum. The direct
inputs for extension by zero and surjectivity on units are [MulChar/Basic.lean:134–192](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/MulChar/Basic.lean#L134-L192)
and [ZMod/Units.lean:23–71](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/ZMod/Units.lean#L23-L71),
retrieved at the same pin on 2026-11-23. The unit-fiber tables are the book’s worked examples.

**Chapter 2, §2.3.2.1.** Archive A2's manifest pins the Mathlib Gamma supply. Loeffler's
proof pairs two Euler quotients and takes the sine-product limit to obtain reflection.
The sine-product file credits David Salwinski, “Euler's Sine Product Formula: An Elementary
Proof,” *College Mathematics Journal* 49 (2018), 126–135. Crossref verifies the bibliographic
record. DLMF supplies the classical exact statements on the Euler integral, poles, half-value,
reflection, and both Euler and Weierstrass formulas. The book adds the explicit error estimates
and classroom examples. [Mathlib attribution](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean#L11-L20) · [Salwinski DOI](https://doi.org/10.1080/07468342.2018.1419703)

**Chapter 2, §2.3.2.2.** The Beta–Gamma identity in the pinned Mathlib is Loeffler's `Gamma_mul_Gamma_eq_betaIntegral`, which rests on van Doorn's convolution file: the forward convolution on $(0,\infty)$, its identification with the two-sided convolution of the zero extensions, the slice integrability argument and the Fubini exchange with translation invariance. `Convolution.lean` was fetched from the pinned revision on 2026-11-25 (SHA-256 in the table). DLMF 5.12.1 and 5.12.2 give the classical quotient and the trigonometric form used in the $a=b=1/2$ example; the DLMF page was retrieved on 2026-11-25 (SHA-256 `0a5b637be728bb03c53fcd035059aef105e7aef2aa09d226e72fe1a6d7e19a9f`). The two archive consumers are `src/Development/AbelianVarietyTheory/Definitions/Divisors/ChernFormSecondChernClass.lean` and `src/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBetaSum.lean` in archive A2. The book adds the composite Jacobian remark and the sharpness example. [Convolution.lean:944–998](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convolution.lean#L944-L998) · [DLMF 5.12](https://dlmf.nist.gov/5.12)

**Chapter 2, §2.3.2.3.** The Euler-integral supply in the pinned Mathlib is Loeffler's `Gamma/Basic.lean` (2022): the little-o tail estimate, the real and complex convergence proofs, the integration-by-parts recurrence for the truncated integral, and the recursive definition `GammaAux`/`Gamma` with its index-independence lemma, of which `Gamma_eq_integral` is the $n=0$ case. The tail test `integrable_of_isBigO_exp_neg` is Loeffler's `ExpDecay.lean`, resting on the filter-integrability lemma `LocallyIntegrableOn.integrableOn_of_isBigO_atTop` in `MeasureTheory/Integral/Asymptotics.lean`; the zero-end power lemma `intervalIntegrable_rpow'` is in `SpecialFunctions/Integrability/Basic.lean`; the modulus formula `norm_cpow_eq_rpow_re_of_pos` is in `Pow/Real.lean`. All five files were fetched from the pinned revision on 2026-11-25 (SHA-256 in the table; `Basic.lean` byte-identical to the §2.3.2.1 copy). DLMF 5.2.1 states the Euler integral with the condition $\Re z>0$, 5.4.1 and 5.4.6 the values at $1$ and $1/2$, 5.4.3 the modulus $|\Gamma(1+iy)|^2=\pi y/\sinh(\pi y)$, and 5.5.3 the reflection formula; DLMF §5.2 was retrieved on 2026-11-25 (SHA-256 `55178b5f947c6e20ebf933078bc199e3f743dabd6456745621e407d6aea25dad`). The direct archive consumer is `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean` in archive A2. The book adds the explicit domination constant, the two hand calculations and the sharpness example $s=it$. [Basic.lean:54–105,248–319](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L54-L105) · [ExpDecay.lean:31–46](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/ExpDecay.lean#L31-L46) · [DLMF 5.2](https://dlmf.nist.gov/5.2) · [DLMF 5.4](https://dlmf.nist.gov/5.4)

| Classical source snapshot | Retrieved | Bytes | sha256 |
|---|---|---:|---|
| [DLMF §4.22](https://dlmf.nist.gov/4.22) | 2026-11-23 UTC | 43536 | `957e0fe7dd5e02d3d6507f5f0a5fd997c60effc63f1fe970777a1ea32ae1d9bd` |
| [DLMF §5.2](https://dlmf.nist.gov/5.2) | 2026-11-23 UTC | 95978 | `a17d5a2f83f23646db5274355b3b2d031d091bbf7d204ec4e2bcb494ebd695f5` |
| [DLMF §5.4](https://dlmf.nist.gov/5.4) | 2026-11-23 UTC | 144848 | `7592b4e0088609869abe303f8f57015927ebd2d89e9b833b47e645b4eb7f9fe8` |
| [DLMF §5.5](https://dlmf.nist.gov/5.5) | 2026-11-23 UTC | 77542 | `10f690014ff4dd35394b9735cc62004a21a2c0faa709855b18073cf5f877ef0b` |
| [DLMF §5.8](https://dlmf.nist.gov/5.8) | 2026-11-23 UTC | 43709 | `90f491b9bf845b7e545b81f325bb00a53844b385247062ea104527a82c5b79fe` |
| [Crossref record for Salwinski (2018)](https://api.crossref.org/works/10.1080/07468342.2018.1419703) | 2026-11-23 UTC | 4504 | `14084d673dfcbb346a965a24b9a3a1768bf20d47de2a05d897cc1fe622796bb4` |

## 5. Verification reports and community guides

| Item | URL | Retrieved | Bytes | sha256 | Version read |
|---|---|---|---:|---|---|
| A. Sutherland, "Verification files for the Lean proof of the Riemann Hypothesis" | `https://math.mit.edu/~drew/grh/` | 2026-11-21T04:02:13Z; rechecked 2026-11-22T09:15Z | 27222 | `01a43fc8defab818d878bfa8fd900d7563073db3dbc6f150ad73baec0fe388a7` | "Page last updated 2026-11-22 04:35 UTC" (adds standalone `Robin1984` `lake comparator` `v4.36.0` pass at `04:16:52 UTC` and elaborated `lagariasStmt`; main and combined 62 GB `lake comparator` kernel stages still `running`; earlier `03:10 UTC` copy was 24,564 B, `17661672…`) |
| LUMI independent check (A. Lipponen), README | `https://raw.githubusercontent.com/aapolipponen/rh-lean-check-lumi/main/README.md` | 2026-11-21T04:02:26Z | 9064 | `4a51000fb1a6d43a22f8a4e26a160ffe6ef22e50646a18ac92ff9cc8e237789c` | repository head `82d91dbbd04d` (2026-11-20T23:56:59Z), unchanged at 04:42:16Z |
| LUMI reader's guide, `docs/README.md` | `…/rh-lean-check-lumi/main/docs/README.md` | 2026-11-21T04:02:57Z | 14124 | `b34663b4fa5484c87bd3b0be4a08308a114fe84fdc0661fd787ac252bda9495f` | docs added in `40e1ae43477a` (2026-11-20T22:40:20Z) |
| LUMI `docs/01-what-is-proved.md` | `…/docs/01-what-is-proved.md` | 2026-11-21T04:03:00Z | 13830 | `37eaf1cc6340053aa2edfa283d400361035b243f96f324e60d79a441660e603c` | |
| LUMI `docs/02-proof-map.md` | `…/docs/02-proof-map.md` | 2026-11-21T04:03:01Z | 21884 | `49aff9f68fcbbf7fd09d2231c040373679df2a82429c67fc72fa50d7cd303402` | |
| LUMI `docs/03-analytic-endgame.md` | `…/docs/03-analytic-endgame.md` | 2026-11-21T04:03:04Z | 19563 | `6cb255aadc9f50dde387456bab85a68f72c7daec4903bcef1baa42a5bdc5ebec` | |
| LUMI `docs/04-chain-and-one-half.md` | `…/docs/04-chain-and-one-half.md` | 2026-11-21T04:03:05Z | 31832 | `3650ba3e36082f3fa104357e992c3b4e544be2537d21c6819606008492c7afda` | |
| LUMI `docs/05-galois-representations.md` | `…/docs/05-galois-representations.md` | 2026-11-21T04:03:07Z | 21177 | `dc304e6a40d4f6233e8fa22feb1bfbb34a9b7f7c42be732f88c9f884a50b94a6` | |
| LUMI `docs/06-window-bound.md` | `…/docs/06-window-bound.md` | 2026-11-21T04:03:09Z | 20315 | `927a2874edca7eae6eb412de85bdf41b6e180f9fbf09e1bebfaa5cc1207f8ef0` | |
| LUMI `docs/07-named-theorems.md` | `…/docs/07-named-theorems.md` | 2026-11-21T04:03:11Z | 43596 | `27e9ac7e6b837cb098c6e288154c88a210e29297e91c22cc4f2cde38a84f3f20` | |
| LUMI `docs/08-archive-anatomy.md` | `…/docs/08-archive-anatomy.md` | 2026-11-21T04:03:13Z | 13011 | `05cae3471ef9c699fb03df4684518e918f18e285fde3bd2208045b98aaed44d4` | |
| LUMI `docs/09-building-and-checking.md` | `…/docs/09-building-and-checking.md` | 2026-11-21T04:03:15Z | 9952 | `baf959527315bb4be5ac868386d54c10cecfe33b3138b797c6e9207748d88a6c` | |
| LUMI `docs/10-open-frontier.md` | `…/docs/10-open-frontier.md` | 2026-11-21T04:03:17Z | 23552 | `14355d0d8d621789a7688a354f1fe2c86567b54d8645259cfb1a792cf7c7ccc1` | |
| LUMI `docs/glossary.md` | `…/docs/glossary.md` | 2026-11-21T04:03:19Z | 21761 | `60be9375373e6487d77ee3e0b18a2501617c1b8b62fc84da3f5de5fbeb95d555` | |
| LUMI `docs/reports/` (skeleton, vacuity-check, theta-chain, analytic-core, core-gm, literature, static-reachability) | `…/docs/reports/<name>.md` | 2026-11-21T04:03:20–04:03:28Z | — | see `FETCH-LOG.txt` | |
| LUMI `results/build-summary.json` | `…/rh-lean-check-lumi/main/results/build-summary.json` | 2026-11-21T04:23:06Z | 453 | `a2763844491a03287ecdbfe5868d71146a7d8ed22a70695b95bf7c12091fe072` | |
| LUMI `results/static-scan.txt` | `…/rh-lean-check-lumi/main/results/static-scan.txt` | 2026-11-21T04:23:07Z | 7128 | `d8c54329b1c86ba8eea4e2a0c9a89a252a253470d20c5da610387952d065d425` | |
| Comparator setup `leanprover-community/riemann-hypothesis` (moved from `Deicyde/riemann-hypothesis`), README | `https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/README.md` | 2026-11-21T04:02:24Z | 3575 | `e2ea5fa16f37c8d4509c517ca808dcf5babe8f4b0308ff33d3888e6c6a8fb34d` | head `371a1a26d5e1` (02:23:57Z) at retrieval; head `4286c9ca372a` (04:27:41Z, build-cache infrastructure) at the 04:42:15Z recheck |
| Comparator setup, `verification/NOTES.md` | `https://raw.githubusercontent.com/Deicyde/riemann-hypothesis/main/verification/NOTES.md` (redirects to the leanprover-community repository) | 2026-11-21T04:02:19Z | 15489 | `a0b67cd13f99bb2c6de9a3ff569716f44fe732abaf31fe013a07434fb5dfcf2b` | includes the correction made after issue #2 |
| Comparator setup, `src/Challenge.lean` | `https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/src/Challenge.lean` | 2026-11-21T04:23:07Z | 1222 | `a3cebbf30be6b9268a0ed413c9bbc256dfa9f4bfa04f1a75f144d135da5e21a5` | lines 3–16 byte-identical to the archive's `src/Statements.lean` lines 3–16 |
| Comparator setup, issue list | `https://api.github.com/repos/leanprover-community/riemann-hypothesis/issues?state=all&per_page=50` | 2026-11-21T04:42:17Z | 85066 | `b55903bce5d5e61222d2c9754ed260f7567ed336ae361fda4811f5ad7c1abc31` | issues #1–#10; no Comparator result posted |
| K. Buzzard, "…and the proof is checked in Lean", Xena blog, 2026-11-12 | `https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/` | 2026-11-21T04:23:04Z | 131922 | `b404e77b8472ae2f8e75a16bccdf8425bc875ba3777b222865d9f7802c5509e3` | quoted in Chapter 1 |
| C. Moskowitz, "The AI Riemann hypothesis proof is almost certainly true, independent mathematicians attest", *Scientific American*, 2026-11-20 | `https://www.scientificamerican.com/article/the-ai-riemann-hypothesis-proof-is-almost-certainly-true-independent-mathematicians-attest/` | 2026-11-21T04:23:05Z | 137656 | `f44ac91b93cc0ae1526e94a040a01821248c68649154baf694b899f83354a103` | quotes of Sutherland and Buzzard |

Consulted but not cited as evidence: T. Tao's blog post of 2026-11-20
(`https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/`,
retrieved 04:05:41Z, sha256 `28d6e810bd49e899bb653b0876336a90f56ee26248e39716e4b330e0b921d9e2`);
*Science* (`science.org`, HTTP 403, not read); the Lean Zulip threads (login required, not read;
cited only through the reports above).

## 6. Literature

Bibliographic data checked online on 2026-11-21 and 2026-11-22. Entries cited by `[AuthorYear]` key in the
textbook chapters carry their key in bold and an explicit `Verified:` record below.

- **[Alon1999]** N. Alon, "Combinatorial Nullstellensatz", *Combinatorics, Probability and
  Computing* 8 (1999), no. 1–2, 7–29, doi:10.1017/S0963548398003411 (Theorem 1.1 and Lemma 2.1,
  pp. 7–9, compared with `mem_span_of_aeval_eq_zero` in Chapter 10, §10.4.7.2).
  Verified: 2026-11-25 via Crossref (`doi:10.1017/S0963548398003411`) and the author-hosted PDF
  <https://www.tau.ac.il/~nogaa/PDFS/null2.pdf> (305,050 bytes, sha256
  `5933068242b0ecc6bba6944bf6d396492bb31c630d4cd7616e477b0a3e1646b7`), Theorem 1.1 and Lemma 2.1
  read directly.
- **[Artin1924]** E. Artin, "Über eine neue Art von $L$-Reihen", *Abhandlungen aus dem
  Mathematischen Seminar der Universität Hamburg* 3 (1924), 89–108, doi:10.1007/BF02954618 (cited
  in Chapter 16).
  Verified: 2026-11-22 via Crossref / Springer (`doi:10.1007/BF02954618`), *Abh. Math. Sem. Univ. Hamburg* vol. 3 (1924), pp. 89–108.
- **[Artin1927]** E. Artin, "Beweis des allgemeinen Reziprozitätsgesetzes", *Abhandlungen aus dem
  Mathematischen Seminar der Universität Hamburg* 5 (1927), 353–363, doi:10.1007/BF02952531 (cited
  in Chapter 18).
  Verified: 2026-11-22 via Crossref / Springer (`doi:10.1007/BF02952531`), *Abh. Math. Sem. Univ. Hamburg* vol. 5 (1927), pp. 353–363.
- **[Behrend1946]** F. A. Behrend, "On sets of integers which contain no three terms in
  arithmetical progression", *Proceedings of the National Academy of Sciences of the United States
  of America* 32 (1946), no. 12, 331–332, doi:10.1073/pnas.32.12.331 (cited in Chapter 17).
  Verified: 2026-11-22 via Crossref / PNAS (`doi:10.1073/pnas.32.12.331`), vol. 32, no. 12 (1946), pp. 331–332.
- **[BellaicheChenevier2009]** J. Bellaïche and G. Chenevier, *Families of Galois Representations and
  Selmer Groups*, Astérisque 324, Société Mathématique de France, Paris, 2009, xii+314 pp.,
  ISBN 978-2-85629-264-8 (cited in Chapters 10 and 12).
  Verified: 2026-11-21 via SMF / Numdam Astérisque vol. 324 (2009), xii+314 pp.
- **[Berger2002]** L. Berger, "Représentations $p$-adiques et équations différentielles",
  *Inventiones Mathematicae* 148 (2002), no. 2, 219–284, doi:10.1007/s002220100202 (cited in
  Chapter 18).
  Verified: 2026-11-22 via Crossref / Springer (`doi:10.1007/s002220100202`), *Invent. Math.* vol. 148, no. 2 (2002), pp. 219–284.
- **[BlochKato1990]** S. Bloch and K. Kato, "$L$-functions and Tamagawa numbers of motives", in
  P. Cartier et al. (eds.), *The Grothendieck Festschrift*, Vol. I, Progress in Mathematics 86,
  Birkhäuser, Boston, 1990, pp. 333–400, doi:10.1007/978-0-8176-4574-8_9 (cited in Chapter 10).
  Verified: 2026-11-21 via Birkhäuser Progress in Mathematics vol. 86 (1990), pp. 333–400.
- **[Bombieri1965]** E. Bombieri, "On the large sieve", *Mathematika* 12 (1965), no. 2, 201–225,
  doi:10.1112/S0025579300005313 (cited in Chapter 4).
  Verified: 2026-11-23 via Crossref (`doi:10.1112/S0025579300005313`), *Mathematika* vol. 12, no. 2 (1965), pp. 201–225.
- **[Bombieri1971]** E. Bombieri, "A note on the large sieve", *Acta Arithmetica* 18 (1971),
  401–404, doi:10.4064/aa-18-1-401-404 (cited in Chapter 4).
  Verified: 2026-11-23 via Crossref (`doi:10.4064/aa-18-1-401-404`) and EuDML (`doc/205002`), vol. 18 (1971), pp. 401–404. The generalized Bessel inequality attributed to it in Chapter 4 was checked against G. Harcos, "The Bombieri–Halász–Montgomery inequality" (note, `https://www.renyi.hu/~gharcos/bombieri-halasz-montgomery.pdf`) and S. S. Dragomir, arXiv:math/0307131, §1, (1.1).
- **[Bombieri1973]** E. Bombieri, "Counting points on curves over finite fields (d'après
  S. A. Stepanov)", *Séminaire Bourbaki*, 25e année (1972/73), exp. no. 430 (June 1973), in
  *Lecture Notes in Mathematics* 383, Springer, Berlin–Heidelberg, 1974, pp. 234–241,
  doi:10.1007/BFb0057311; open copy at `https://www.numdam.org/item/SB_1972-1973__15__234_0/`
  (cited in Chapters 6, 7, 8, and 15).
  Verified: 2026-11-21 via Numdam (`SB_1972-1973__15__234_0`) and Springer (`doi:10.1007/BFb0057311`), vol. 383, pp. 234–241.
- **[Bombieri1974]** E. Bombieri, *Le grand crible dans la théorie analytique des nombres*,
  Astérisque 18, Société Mathématique de France, Paris, 1974 (background reference).
  Verified: 2026-11-21 via SMF Astérisque catalogue (vol. 18, 1974).
- **[Bombieri2000]** E. Bombieri, "Problems of the Millennium: The Riemann Hypothesis", Clay
  Mathematics Institute, Cambridge, MA, 2000; reprinted in J. Carlson, A. Jaffe, and A. Wiles
  (eds.), *The Millennium Prize Problems*, Clay Mathematics Institute / American Mathematical
  Society, Providence, RI, 2006, pp. 107–124 (cited in Chapters 14 and 15).
  Verified: 2026-11-22 via Clay Mathematics Institute Millennium Problems official problem description (2000) and AMS/CMI volume (2006).
- **[Bost1996]** J.-B. Bost, "Périodes et isogénies des variétés abéliennes sur les corps de nombres
  (d'après D. Masser et G. Wüstholz)", *Séminaire Bourbaki*, Vol. 1994/95, exp. no. 795,
  Astérisque 237 (1996), 115–161; open copy at `http://www.numdam.org/item/SB_1994-1995__37__115_0/`
  (cited in Chapters 6 and 9; Chapter 6, §6.4.5 uses Appendix A: the rank-one Arakelov degree on
  p. 146, $\widehat{\deg}_n$, $\hat\mu$ and invariance under $f^{\ast}$ on p. 147, Prop. A.1 with
  torsion-free quotients and Prop. A.2 on pp. 148–149).
  Verified: 2026-11-21 via Numdam (`SB_1994-1995__37__115_0`) and SMF Astérisque vol. 237 (1996), exp. 795, pp. 115–161.
  Re-verified 2026-11-23 (CST) for Chapter 6: Numdam PDF, 3,794,367 B, sha256
  `13d2911a3b4460552d2ba649609f626a0342beae85966929940ab7df205b0edb`, Appendix A read on PDF pages 33–35
  (printed pp. 146–148).
- **[Bost2001]** J.-B. Bost, "Algebraic leaves of algebraic foliations over number fields",
  *Publications Mathématiques de l'IHÉS* 93 (2001), 161–221, doi:10.1007/s10240-001-8191-3
  (cited in Chapter 9).
  Verified: 2026-11-21 via Numdam / EuDML, *Publ. Math. IHÉS* vol. 93 (2001), pp. 161–221.
- **[Brauer1947]** R. Brauer, "On Artin's $L$-series with general group characters", *Annals of
  Mathematics* (2) 48 (1947), no. 2, 502–514, doi:10.2307/1969183 (cited in Chapter 16).
  Verified: 2026-11-22 via Crossref / JSTOR (`doi:10.2307/1969183`), *Annals of Mathematics* vol. 48, no. 2 (1947), pp. 502–514.
- **[BushnellKutzko1993]** C. J. Bushnell and P. C. Kutzko, *The Admissible Dual of $GL(N)$ via
  Compact Open Subgroups*, Annals of Mathematics Studies 129, Princeton University Press, Princeton,
  NJ, 1993, ISBN 978-0-691-02114-0 (cited in Chapters 12 and 13).
  Verified: 2026-11-22 via Princeton University Press Annals of Mathematics Studies vol. 129 (`ISBN 978-0-691-02114-0`).
- **[Caraiani2012]** A. Caraiani, "Local-global compatibility and the action of monodromy on nearby
  cycles", *Duke Mathematical Journal* 161 (2012), no. 12, 2311–2413,
  doi:10.1215/00127094-1723706 (cited in Chapter 12).
  Verified: 2026-11-22 via Project Euclid / Duke University Press (`doi:10.1215/00127094-1723706`), vol. 161, no. 12 (2012), pp. 2311–2413.
- **[Caraiani2014]** A. Caraiani, "Monodromy and local-global compatibility for $l = p$", *Algebra &
  Number Theory* 8 (2014), no. 7, 1597–1646, doi:10.2140/ant.2014.8.1597 (cited in Chapter 12).
  Verified: 2026-11-22 via MSP *Algebra & Number Theory* (`doi:10.2140/ant.2014.8.1597`), vol. 8, no. 7 (2014), pp. 1597–1646.
- **[ChowlaSelberg1967]** S. Chowla and A. Selberg, "On Epstein's zeta-function", *Journal für die
  reine und angewandte Mathematik* 227 (1967), 86–110, doi:10.1515/crll.1967.227.86 (cited in
  Chapter 9).
  Verified: 2026-11-21 via EuDML / De Gruyter, *J. Reine Angew. Math.* vol. 227 (1967), pp. 86–110.
- **[ChenevierHarris2013]** G. Chenevier and M. Harris, “Construction of automorphic Galois representations, II,” *Cambridge Journal of Mathematics* 1 (2013), doi:10.4310/CJM.2013.v1.n1.a2. Introduction and Theorem 3.2.3 (cited in Chapter 19). [Publisher PDF](https://intlpress.com/site/pub/files/_fulltext/journals/cjm/2013/0001/0001/CJM-2013-0001-0001-a002.pdf)
  Retrieved: 2026-11-23 07:04 UTC, publisher PDF, HTTP 200, 217,654 bytes, sha256
  `f77c7fef0640b3d6d7295b92b5af07b03a9b2cffacb0dc62acb9dfae024268a6`; the two quotations of
  Section 19.2 checked against the introduction. Chapter 19 records that the archive's
  `ChenevierHarris` proposition is defined but neither proved nor used.
- **[Clozel1990]** L. Clozel, "Motifs et formes automorphes: applications du principe de
  fonctorialité", in L. Clozel and J. S. Milne (eds.), *Automorphic Forms, Shimura Varieties, and
  $L$-Functions*, Vol. I, Perspectives in Mathematics 10, Academic Press, Boston, MA, 1990,
  pp. 77–159 (cited in Chapter 18).
  Verified: 2026-11-22 via Perspectives in Mathematics vol. 10 (Academic Press, 1990), Vol. I, pp. 77–159.
- **[ClozelHarrisTaylor2008]** L. Clozel, M. Harris, and R. Taylor, "Automorphy for some $l$-adic
  lifts of automorphic mod $l$ Galois representations", *Publications Mathématiques de l'IHÉS* 108
  (2008), 1–181, doi:10.1007/s10240-008-0016-1 (cited in Chapters 11 and 12).
  Verified: 2026-11-22 via Numdam / Springer (`doi:10.1007/s10240-008-0016-1`), *Publ. Math. IHÉS* vol. 108 (2008), pp. 1–181.
- **[Connes1999]** A. Connes, "Trace formula in noncommutative geometry and the zeros of the Riemann
  zeta function", *Selecta Mathematica (N.S.)* 5 (1999), no. 1, 29–106, doi:10.1007/s000290050042
  (cited in Chapters 14 and 15).
  Verified: 2026-11-22 via Crossref / Springer (`doi:10.1007/s000290050042`), *Selecta Math. (N.S.)* vol. 5, no. 1 (1999), pp. 29–106.
- **[Davenport2000]** H. Davenport, *Multiplicative Number Theory*, 3rd ed., revised by
  H. L. Montgomery, Graduate Texts in Mathematics 74, Springer, New York, 2000,
  ISBN 978-0-387-95097-6 (cited in Chapters 4, 7, and 16).
  Verified: 2026-11-21 via Springer GTM 74 catalogue (`ISBN 978-0-387-95097-6`).
- **[DeligneRibet1980]** P. Deligne and K. A. Ribet, "Values of abelian $L$-functions at negative
  integers over totally real fields", *Inventiones Mathematicae* 59 (1980), no. 3, 227–286,
  doi:10.1007/BF01453237 (cited in Chapter 18).
  Verified: 2026-11-22 via Crossref / Springer (`doi:10.1007/BF01453237`), *Invent. Math.* vol. 59, no. 3 (1980), pp. 227–286.
- **[Deninger1993]** C. Deninger, "Lefschetz trace formulas and explicit formulas in analytic number
  theory", *Journal für die reine und angewandte Mathematik* 441 (1993), 1–15,
  doi:10.1515/crll.1993.441.1 (cited in Chapters 14 and 15).
  Verified: 2026-11-22 via Crossref / EuDML (`doi:10.1515/crll.1993.441.1`), *J. Reine Angew. Math.* vol. 441 (1993), pp. 1–15.
- **[EoMKurzweilHenstock]** Encyclopedia of Mathematics, "Kurzweil–Henstock integral" (article by P. S. Bullen), EMS Press; states the Saks–Henstock lemma on an interval in both the norm-of-sum and the sum-of-absolute-values ($2\varepsilon$) forms and cites Gordon's monograph (cited in Chapter 3, §3.4.1, Henstock–Sacks subsection).
  Verified: 2026-11-24 through the Internet Archive capture of `https://encyclopediaofmath.org/wiki/Kurzweil-Henstock_integral` (SHA-256 of the retrieved capture `9b3bfaf6a6b0c4c55f33706a69cb4a95355b836bda0cdfdf0b41fc709b087a1e`); the live site returned HTTP 502 on two attempts.
- **[FerreroWashington1979]** B. Ferrero and L. C. Washington, "The Iwasawa invariant $\mu_p$
  vanishes for abelian number fields", *Annals of Mathematics* (2) 109 (1979), no. 2, 377–395,
  doi:10.2307/1971116 (cited in Chapters 11, 16, and 18).
  Verified: 2026-11-22 via *Annals of Mathematics* / JSTOR (`doi:10.2307/1971116`), vol. 109, no. 2 (1979), pp. 377–395.
- **[Gallagher1970]** P. X. Gallagher, "A large sieve density estimate near $\sigma=1$", *Inventiones
  Mathematicae* 11 (1970), no. 4, 329–339, doi:10.1007/BF01403187, MR0279049 (cited in Chapter 4).
  Verified: 2026-11-24 via Crossref (`doi:10.1007/BF01403187`: vol. 11, no. 4, pp. 329–339, issued 1970-12), the Springer
  article page and EuDML `doc/142061`. The full text is behind the publisher's paywall and was not read; the
  attribution of the far-range prime number theorem rests on [Tao2015].
- **[GanTakeda2016]** W. T. Gan and S. Takeda, "A proof of the Howe duality conjecture",
  *Journal of the American Mathematical Society* 29 (2016), no. 2, 473–493,
  doi:10.1090/jams/839 (cited in Chapter 7).
  Verified: 2026-11-21 via AMS (`doi:10.1090/jams/839`), vol. 29, no. 2, pp. 473–493.
- **[GilletSoule1990]** H. Gillet and C. Soulé, "Arithmetic intersection theory", *Publications
  Mathématiques de l'IHÉS* 72 (1990), 93–174; open copy at `http://www.numdam.org/item/PMIHES_1990__72__93_0/`
  (cited in Chapter 9).
  Verified: 2026-11-21 via Numdam (`PMIHES_1990__72__93_0`) and EuDML, *Publ. Math. IHÉS* vol. 72 (1990), pp. 93–174.
- **[CommelinLewis2021]** J. Commelin and R. Y. Lewis, "Formalizing the ring of Witt vectors", in *Proceedings of the 10th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2021)*, Association for Computing Machinery, New York, 2021, pp. 264–277, doi:10.1145/3437992.3439919 (cited in Chapter 13, §13.4.9, via Mathlib `Mathlib/RingTheory/WittVector/Teichmuller.lean`).
  Verified: 2026-11-24 via Crossref (`doi:10.1145/3437992.3439919`), CPP 2021, pp. 264–277. Author HTML v2 was retrieved 2026-11-24 for §§2.3, 5.2, and 6. [Author version](https://arxiv.org/html/2010.02595v2)
- **[Fremlin2010]** D. H. Fremlin, *Vector-valued Saks-Henstock indefinite integrals*, research note n10805, version of 2010-09-02, 15 pp., University of Essex; §1D states and proves the Saks–Henstock lemma for tagged-partition structures and §1F its converse (cited in Chapter 3, §3.4.1, Henstock–Sacks subsection).
  Verified: 2026-11-24, PDF retrieved from `https://www1.essex.ac.uk/maths/people/Fremlin/n10805.pdf` (SHA-256 `d0d66486d19a79bf44f9f48cf5b5a3c31733918c0acb668db07fa346a44e0155`); the proof of 1D completes a fine prepartition to a fine partition.
- **[Gordon1994]** R. A. Gordon, *The Integrals of Lebesgue, Denjoy, Perron, and Henstock*, Graduate
  Studies in Mathematics 4, American Mathematical Society, Providence, 1994, ISBN 0-8218-3805-9 (cited
  in Chapter 3 as the basis named in Mathlib's McShane comparison file; Chapter 10 treats the McShane integral).
  Verified: 2026-11-24 via the AMS bookstore record (GSM vol. 4, 1994, 395 pp., chapter list) and the AMS front-matter PDF, read through search-engine snapshots because direct downloads returned HTTP 403.
- **[Hazewinkel2009]** M. Hazewinkel, "Witt vectors. Part 1", in M. Hazewinkel (ed.), *Handbook of Algebra*, Vol. 6, Elsevier / North-Holland, Amsterdam, 2009, pp. 319–472, doi:10.1016/S1570-7954(08)00207-6 (cited in Chapter 13, §13.4.9, via Mathlib `Mathlib/RingTheory/WittVector/Teichmuller.lean`).
  Verified: 2026-11-24 via Crossref (`doi:10.1016/S1570-7954(08)00207-6`), *Handbook of Algebra* vol. 6 (2009), pp. 319–472. The author manuscript was retrieved 2026-11-24 for §§1.4 and 6.19–6.20. [Author manuscript](https://ir.cwi.nl/pub/12787/12787B.pdf)
- **[Green1955]** J. A. Green, "The characters of the finite general linear groups", *Transactions
  of the American Mathematical Society* 80 (1955), no. 2, 402–447,
  doi:10.1090/S0002-9947-1955-0072878-2 (cited in Chapter 13).
  Verified: 2026-11-22 via AMS (`doi:10.1090/S0002-9947-1955-0072878-2`), *Trans. Amer. Math. Soc.* vol. 80, no. 2 (1955), pp. 402–447.
  Text read for Section 13.4.4 (2026-11-23): the AMS free PDF as archived by the Internet Archive,
  `http://web.archive.org/web/20250730054741/https://www.ams.org/journals/tran/1955-080-02/S0002-9947-1955-0072878-2/S0002-9947-1955-0072878-2.pdf`
  (retrieved 2026-11-23T08:51Z, 3,328,037 B, sha256 `ded2dbd2e6fa499b64fe4c857ddaa8daf4ee4f74eef135958e4a40a02e6cac3d`;
  the AMS URL itself returned a Cloudflare challenge, HTTP 403, to our client). Pages read: 403–405
  (Theorem 1, the $\mathrm{GL}_2$ formulas for uniform functions, §1), 409 (Definition 2.2), 413–415 (§3,
  Brauer's characterisation, the fixed isomorphism $\theta$), 430–431 (Example (ii)), 437–438
  (Definition 7.3, Lemmas 7.4–7.6). Printed page = PDF page + 401. Not redistributed.
  Re-fetched and read on 2026-11-23 for Section 13.4.5, same SHA-256. Pages 403–404 and 413–415 supply the comparison of Theorem 1, the elementary-subgroup restriction criterion and equation (5) with the archive’s induced-unit argument.
  For §13.4.6 (2026-11-23), re-fetched the [archived AMS original](https://web.archive.org/web/20250730054741id_/https://www.ams.org/journals/tran/1955-080-02/S0002-9947-1955-0072878-2/S0002-9947-1955-0072878-2.pdf) with the same SHA-256. Read Lemma 6.3 (p. 435), Lemma 7.6 and the simplex definition (pp. 438–439), and the local multiplicity in the proof of Lemma 8.3 (pp. 442–443). The §13.4.6 endomorphism-mass proof follows A2.
  For §13.4.7, the AMS scan was retrieved on 2026-11-23 13:48 UTC, 3,328,037 bytes, SHA-256 `ded2dbd2e6fa499b64fe4c857ddaa8daf4ee4f74eef135958e4a40a02e6cac3d`. Printed p. 410, equations (2)–(4) and Theorem 2 give the weighted fixed-flag formula. The chapter derives the trivial quotient-factor specialization against the A2 implementation. [Archived AMS scan](https://web.archive.org/web/20250730054741id_/https://www.ams.org/journals/tran/1955-080-02/S0002-9947-1955-0072878-2/S0002-9947-1955-0072878-2.pdf).
  For §13.4.8, re-fetched the AMS scan on 2026-11-23 UTC (HTTP 200, 3,328,037 bytes, SHA-256 `ded2dbd2e6fa499b64fe4c857ddaa8daf4ee4f74eef135958e4a40a02e6cac3d`). Read Lemma 7.7 and Theorem 13 with the opening of its proof, pp. 439–440. Green counts partition-valued labels against conjugacy classes. The section’s Whittaker norm argument follows A2. [Green 1955](https://doi.org/10.1090/S0002-9947-1955-0072878-2).
  For the first §13.4.9 draft, re-fetched the archived AMS original on 2026-11-24T10:50Z (HTTP 200, 3,328,037 bytes, SHA-256 `ded2dbd2e6fa499b64fe4c857ddaa8daf4ee4f74eef135958e4a40a02e6cac3d`) and Crossref metadata (`doi:10.1090/S0002-9947-1955-0072878-2`). Read §1 (p. 405, universal splitting field $\mathrm{GF}(q^{n!})$) and §3 (p. 414, arbitrary choice $\theta = \phi^r$ of multiplicative isomorphism and prime-ideal reduction of $(p^a - 1)$-th roots of unity), comparing them with the archive's Witt-vector producer `TeichEmb.exists_teichmuller` and $\overline{\mathbb Z}$-reduction model `GLq.Model.teichM`.
  For the revised §13.4.9, the same PDF was retrieved 2026-11-24 (HTTP 200) and printed pp. 405 and 414 were read for the common splitting field and the change of multiplicative embedding.
  For §13.4.10, re-fetched the [archived AMS original](https://web.archive.org/web/20250730054741id_/https://www.ams.org/journals/tran/1955-080-02/S0002-9947-1955-0072878-2/S0002-9947-1955-0072878-2.pdf) on 2026-11-24T13:27Z (HTTP 200, 3,328,037 bytes, same SHA-256) and read printed pp. 437–439 in the page images: the degree of a not necessarily proper character, $J_d(k)(1)=\varphi_{d-1}(q)$, Lemma 7.5 (sign of the degree), Lemma 7.6 (norm one under distinct residues), and Theorem 12 with $(g^\lambda)=(-1)^{(s-1)v}I_s^k[\lambda]$. Green leaves the step from norm one and signed degree to irreducibility implicit; the section writes it out from A2.
- **[Brauer1953]** Richard Brauer, “A characterization of the characters of groups of finite order,” *Annals of Mathematics* 57 (1953), 357–377. Green cites it for the characterization in §3. Bibliographic record verified via Crossref on 2026-11-23. The proof in Brauer’s original paper is [Open] in the reading for §13.4.5. [DOI](https://doi.org/10.2307/1969864)
- **[GanQiuTakeda2014]** W. T. Gan, Y. Qiu and S. Takeda, “The regularized Siegel–Weil formula (the second term identity) and the Rallis inner product formula,” *Inventiones Mathematicae* 198 (2014), 739–831. Theorems 1.2–1.3 (cited in Chapter 19). [Author preprint](https://arxiv.org/abs/1207.4709)
  Version used: arXiv:1207.4709v3 (21 Jan 2014), PDF retrieved 2026-11-23 07:04 UTC, HTTP 200,
  667,816 bytes, sha256 `cde6b7ad22b974d4159f8cedd1e14a00bf4b05ec977ab750b54fdceb067adac5`.
  Theorems 1.2–1.3 (pp. 6–7) and §11.6 (p. 54, the unramified local zeta integral
  $L(s+1/2,\pi_v\times\chi_{V,v})/d_v(s,\chi_V)$ with $d_v$ referred to [LapidRallis2005]) were
  read in this version; page numbers are those of the preprint. On 2026-11-23 the Chapter 19
  follow-up retrieved the same PDF by SHA-256 and reread Theorems 1.2(ii) and 1.3 and §11.6.
- **[Grothendieck1955]** A. Grothendieck, *Produits tensoriels topologiques et espaces nucléaires*,
  Memoirs of the American Mathematical Society 16, American Mathematical Society, Providence, RI,
  1955, doi:10.1090/memo/0016 (cited in Chapters 14 and 18).
  Verified: 2026-11-22 via Crossref / AMS (`doi:10.1090/memo/0016`), *Mem. Amer. Math. Soc.* no. 16 (1955).
- **[HarrisTaylor2001]** M. Harris and R. Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties*, Annals of Mathematics Studies 151, Princeton University Press, Princeton, NJ, 2001,
  ISBN 978-0-691-09092-4 (cited in Chapters 12 and 16).
  Verified: 2026-11-22 via Princeton University Press Annals of Mathematics Studies vol. 151 (`ISBN 978-0-691-09092-4`).
- **[Hasse1936]** H. Hasse, "Zur Theorie der abstrakten elliptischen Funktionenkörper. I, II, III",
  *Journal für die reine und angewandte Mathematik* 175 (1936), 55–62, 69–88, 193–208,
  doi:10.1515/crll.1936.175.55, doi:10.1515/crll.1936.175.69, doi:10.1515/crll.1936.175.193
  (cited in Chapter 6).
  Verified: 2026-11-21 via EuDML and De Gruyter (*J. Reine Angew. Math.* 175 (1936), pp. 55–62, 69–88, 193–208).
- **[HasseSchmidt1937]** H. Hasse and F. K. Schmidt, "Noch eine Begründung der Theorie der höheren
  Differentialquotienten in einem algebraischen Funktionenkörper einer Unbestimmten", *Journal für
  die reine und angewandte Mathematik* 177 (1937), 215–237, doi:10.1515/crll.1937.177.215
  (cited in Chapters 6, 8, and 15).
  Verified: 2026-11-21 via De Gruyter (`doi:10.1515/crll.1937.177.215`), vol. 177, pp. 215–237.
- **[Hecke1920]** E. Hecke, "Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der
  Primzahlen. Zweite Mitteilung", *Mathematische Zeitschrift* 6 (1920), 11–51,
  doi:10.1007/BF01202991 (cited in Chapters 14, 15, and 16).
  Verified: 2026-11-22 via Crossref / Springer (`doi:10.1007/BF01202991`), *Math. Z.* vol. 6 (1920), pp. 11–51.
- **[Henniart2000]** G. Henniart, "Une preuve simple des conjectures de Langlands pour $\mathrm{GL}(n)$
  sur un corps $p$-adique", *Inventiones Mathematicae* 139 (2000), no. 2, 439–455,
  doi:10.1007/s002220050012 (cited in Chapter 12).
  Verified: 2026-11-22 via Springer (`doi:10.1007/s002220050012`), *Invent. Math.* vol. 139, no. 2 (2000), pp. 439–455.
- **[Hida1981]** H. Hida, "Congruences of cusp forms and special values of their zeta functions",
  *Inventiones Mathematicae* 63 (1981), no. 2, 225–261, doi:10.1007/BF01393877 (cited in
  Chapter 10).
  Verified: 2026-11-21 via EuDML / Springer (`doi:10.1007/BF01393877`), *Invent. Math.* vol. 63, no. 2 (1981), pp. 225–261.
- **[Hida1988]** H. Hida, "Modules of congruence of Hecke algebras and $L$-functions associated with
  cusp forms", *American Journal of Mathematics* 110 (1988), no. 2, 323–382, doi:10.2307/2374505
  (cited in Chapter 10).
  Verified: 2026-11-21 via JSTOR / Johns Hopkins University Press (`doi:10.2307/2374505`), *Amer. J. Math.* vol. 110, no. 2 (1988), pp. 323–382.
- **[Hooley1967]** C. Hooley, "On Artin's conjecture", *Journal für die reine und angewandte
  Mathematik* 225 (1967), 209–220, doi:10.1515/crll.1967.225.209 (cited in Chapter 16).
  Verified: 2026-11-22 via Crossref / EuDML (`doi:10.1515/crll.1967.225.209`), *J. Reine Angew. Math.* vol. 225 (1967), pp. 209–220.
- **[Howe1979]** R. Howe, "$\theta$-series and invariant theory", in A. Borel and W. Casselman
  (eds.), *Automorphic Forms, Representations and $L$-Functions* (Proc. Sympos. Pure Math., Oregon
  State Univ., Corvallis, 1977), Proceedings of Symposia in Pure Mathematics 33, Part 1, American
  Mathematical Society, Providence, RI, 1979, pp. 275–285 (cited in Chapters 7 and 14).
  Verified: 2026-11-21 via AMS PSPM vol. 33, Part 1 (1979), pp. 275–285.
- **[Huxley1972]** M. N. Huxley, "On the difference between consecutive primes", *Inventiones
  Mathematicae* 15 (1972), no. 2, 164–170, doi:10.1007/BF01418933 (cited in Chapter 4).
  Verified: 2026-11-23 via Crossref (`doi:10.1007/BF01418933`; Crossref issue date 1971-06), vol. 15, no. 2, pp. 164–170. The density exponent 12/5 was checked against arXiv:2607.04632, Theorem 4.2 and (18).
- **[Huxley1975]** M. N. Huxley, "Large values of Dirichlet polynomials, III", *Acta Arithmetica*
  26 (1975), no. 4, 435–444, doi:10.4064/aa-26-4-435-444 (cited in Chapter 4).
  Verified: 2026-11-23 via Crossref (`doi:10.4064/aa-26-4-435-444`), vol. 26, no. 4 (1975), pp. 435–444. Its role for the hybrid exponent 12/5 over primitive characters was checked against M. Jutila, "Recent progress in the theory of $L$-functions", *Séminaire Delange–Pisot–Poitou* 17 (1975/76), no. 1, exp. 6, §2, (2.3) (Numdam `SDPP_1975-1976__17_1_A6_0`), which credits Huxley's papers [5] and [9], i.e. Huxley1972 and Huxley1975.
- **[IwaniecKowalski2004]** H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium
  Publications 53, American Mathematical Society, Providence, RI, 2004, ISBN 978-0-8218-3633-0,
  doi:10.1090/coll/053 (cited in Chapters 6, 7, and 15).
  Verified: 2026-11-21 via AMS Colloquium Publications vol. 53 (`doi:10.1090/coll/053`).
- **[Iwasawa1959]** K. Iwasawa, "On $\Gamma$-extensions of algebraic number fields", *Bulletin of
  the American Mathematical Society* 65 (1959), no. 4, 183–226,
  doi:10.1090/S0002-9904-1959-10317-7 (cited in Chapter 11).
  Verified: 2026-11-22 via AMS (`doi:10.1090/S0002-9904-1959-10317-7`), *Bull. Amer. Math. Soc.* vol. 65, no. 4 (1959), pp. 183–226.
- **[Iwasawa1973]** K. Iwasawa, "On $\mathbf Z_l$-extensions of algebraic number fields", *Annals of
  Mathematics* (2) 98 (1973), no. 2, 246–326, doi:10.2307/1970784 (cited in Chapter 11).
  Verified: 2026-11-22 via *Annals of Mathematics* / JSTOR (`doi:10.2307/1970784`), vol. 98, no. 2 (1973), pp. 246–326.
- **[Jacobi1829]** C. G. J. Jacobi, *Fundamenta Nova Theoriae Functionum Ellipticarum*, Sumtibus
  Fratrum Borntraeger, Regiomonti (Königsberg), 1829; reprinted in *C. G. J. Jacobi's Gesammelte
  Werke*, Band 1, Reimer, Berlin, 1881, pp. 49–239 (cited in Chapter 7).
  Verified: 2026-11-21 via bibliographic records for Borntraeger (Königsberg, 1829) and *Gesammelte Werke* Bd. 1, pp. 49–239.
- **[Kato2004]** K. Kato, "$p$-adic Hodge theory and values of zeta functions of modular forms", in
  *Cohomologies $p$-adiques et applications arithmétiques, III*, Astérisque 295, Société
  Mathématique de France, Paris, 2004, pp. 117–290 (cited in Chapters 11, 16, and 18).
  Verified: 2026-11-22 via SMF / Numdam Astérisque vol. 295 (2004), pp. 117–290.
- **[Dwork1960]** B. Dwork, "On the rationality of the zeta function of an algebraic variety", *American
  Journal of Mathematics* 82 (1960), no. 3, 631–648, doi:10.2307/2372974 (cited in Chapter 8, §8.4.14, for the
  constant $\pi_D$ with $\pi_D^{p-1}=-p$ whose valuation $1/(p-1)$ is that of the archive's $\pi^{p+1}$).
  Verified: 2026-11-25 via the DOI resolver (`doi:10.2307/2372974` → JSTOR stable 2372974) and the reference list of the
  Wikipedia article "Weil conjectures"; JSTOR itself served an anti-bot page.
- **[Hazewinkel1978]** M. Hazewinkel, *Formal Groups and Applications*, Pure and Applied Mathematics 78, Academic Press,
  New York, 1978, ISBN 0-12-335150-2 (cited in Chapter 8, §8.4.14, for the functional-equation form of the height-two
  logarithm $\ell(T)=T+p^{-1}\ell(T^{p^2})$; section number not cited because it could not be checked online).
  Verified: 2026-11-25 (publisher, series, volume, year, ISBN) via the Wikipedia article "Formal group law"; the AMS Chelsea
  reprint page returned 403.
- **[Katz1976]** N. M. Katz, "$p$-adic interpolation of real analytic Eisenstein series", *Annals of
  Mathematics* (2) 104 (1976), no. 3, 459–571, doi:10.2307/1970966 (cited in Chapter 8).
  Verified: 2026-11-21 via JSTOR / *Annals of Mathematics* (`doi:10.2307/1970966`), vol. 104, no. 3 (1976), pp. 459–571.
- **[KudlaRallis1994]** S. S. Kudla and S. Rallis, "A regularized Siegel–Weil formula: the first
  term identity", *Annals of Mathematics* (2) 140 (1994), no. 1, 1–80, doi:10.2307/2118540
  (cited in Chapters 7, 8, 9, 12, 15, 16, and 18).
  Verified: 2026-11-21 via *Annals of Mathematics* / JSTOR (`doi:10.2307/2118540`), vol. 140, no. 1, pp. 1–80.
- **[Lagarias2002]** J. C. Lagarias, "An elementary problem equivalent to the Riemann hypothesis",
  *The American Mathematical Monthly* 109 (2002), no. 6, 534–543, doi:10.2307/2695443 (cited in
  `CONTRIBUTIONS.md`).
  Verified: 2026-11-21 via MAA / JSTOR (`doi:10.2307/2695443`), vol. 109, no. 6, pp. 534–543.
- **[Landau1905]** E. Landau, "Über einen Satz von Tschebyschef", *Mathematische Annalen* 61
  (1905), 527–550, doi:10.1007/BF01449495 (cited in Chapter 15).
  Verified: 2026-11-21 via Springer (`doi:10.1007/BF01449495`), vol. 61, pp. 527–550.
- **[LapidRallis2005]** E. M. Lapid and S. Rallis, "On the local factors of representations of
  classical groups", in J. W. Cogdell, D. Jiang, S. S. Kudla, D. Soudry and R. J. Stanton (eds.),
  *Automorphic Representations, L-Functions and Applications: Progress and Prospects*, Ohio State
  Univ. Math. Res. Inst. Publ. 11, de Gruyter, Berlin, 2005, 309–359,
  doi:10.1515/9783110892703.309 (cited in Chapter 19).
  Checked: 2026-11-23 07:05 UTC. The DOI resolves to the de Gruyter Brill chapter page, which served
  no content to our client (HTTP 202). The OpenAlex record
  (`api.openalex.org/works/doi:10.1515/9783110892703.309`) confirms the title and first page 309
  and lists the chapter as closed access (it gives last page 360; citing works give 309–359).
  Gan–Qiu–Takeda (§11.6, p. 54) cite its
  p. 334, Remark 3 for the explicit normalizing factor $d_v$. We have not read that page, so the
  split-place comparison of Section 19.5 remains [Open].
  Follow-up, 2026-11-23: the DOI landing page and publisher PDF endpoint both returned HTTP 202
  with empty bodies. OpenAlex listed no repository full text. A title search found a ResearchGate
  listing offering full text on request and a third-party viewer whose authorization could not
  be established. No authorized copy of p. 334 was obtained. The Satake, parameter and Haar
  comparisons remain [Open].
- **[Lemmermeyer2013]** F. Lemmermeyer, "The ambiguous class number formula revisited",
  *Journal of the Ramanujan Mathematical Society* 28 (2013), no. 4, 415–421; arXiv:1309.1071
  (cited in Chapter 11, §11.4.3.2).
  Verified: 2026-11-24 via the journal's issue listing (vol. 28, no. 4, December 2013, pp. 415–421) and the
  arXiv PDF v1 (sha256 `53a80b00b693203386df6ca3350b4d5891159580037ca72a2096d59776300065`), read in full.
  Theorem 1 gives, for a cyclic extension $L/K$ of prime degree $\ell$, the number of ambiguous classes as
  $h(K)\,\ell^{t-1}/(E_K:E_K\cap N L^\times)$, with $t$ the number of ramified primes including the infinite
  ones. Chapter 11 quotes it only for comparison with the archive's bound on the $\ell$-rank of the
  coinvariants, which does not use this formula.
- **[MazurWiles1984]** B. Mazur and A. Wiles, "Class fields of abelian extensions of $\mathbf Q$",
  *Inventiones Mathematicae* 76 (1984), no. 2, 179–330, doi:10.1007/BF01388599 (cited in
  Chapters 10 and 11).
  Verified: 2026-11-22 via EuDML / Springer (`doi:10.1007/BF01388599`), *Invent. Math.* vol. 76, no. 2 (1984), pp. 179–330.
- **[Meyer2005]** R. Meyer, "On a representation of the idele class group related to primes and zeros
  of $L$-functions", *Duke Mathematical Journal* 127 (2005), no. 3, 519–595,
  doi:10.1215/S0012-7094-04-12734-4 (cited in Chapters 14 and 15).
  Verified: 2026-11-22 via Crossref / Project Euclid (`doi:10.1215/S0012-7094-04-12734-4`), *Duke Math. J.* vol. 127, no. 3 (2005), pp. 519–595.
- **[Montgomery1968]** H. L. Montgomery, "A note on the large sieve", *Journal of the London
  Mathematical Society* s1-43 (1968), no. 1, 93–98, doi:10.1112/jlms/s1-43.1.93 (cited in Chapter 4).
  Verified: 2026-11-23 via Crossref (`doi:10.1112/jlms/s1-43.1.93`), vol. s1-43, no. 1 (1968), pp. 93–98.
- **[Montgomery1969]** H. L. Montgomery, "Zeros of $L$-functions", *Inventiones Mathematicae* 8
  (1969), no. 4, 346–354, doi:10.1007/BF01404638 (cited in Chapter 4).
  Verified: 2026-11-23 via Crossref (`doi:10.1007/BF01404638`), vol. 8, no. 4 (1969), pp. 346–354. The hybrid density exponent 5/2 attributed to it was checked against R. J. Lemke Oliver and J. Thorner, arXiv:1505.03122, §1, (1.6), and C. An, arXiv:2004.14410, §2.1.
- **[Montgomery1971]** H. L. Montgomery, *Topics in Multiplicative Number Theory*, Lecture Notes in
  Mathematics 227, Springer, Berlin–Heidelberg, 1971, ISBN 978-3-540-05641-6,
  doi:10.1007/BFb0060851 (Chapter 12, cited in Chapter 4).
  Verified: 2026-11-21 via Springer LNM vol. 227 (`doi:10.1007/BFb0060851`).
- **[MontgomeryVaughan2007]** H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I:
  Classical Theory*, Cambridge Studies in Advanced Mathematics 97, Cambridge University Press,
  2007, ISBN 978-0-521-84903-6 (Theorem 1.7 and §15.1, cited in Chapter 3).
  Verified: 2026-11-21 via Cambridge University Press CSAM vol. 97 (`ISBN 978-0-521-84903-6`).
- **[Neukirch1999]** J. Neukirch, *Algebraic Number Theory*, transl. N. Schappacher, Grundlehren
  der mathematischen Wissenschaften 322, Springer, Berlin–Heidelberg, 1999, ISBN 978-3-540-65399-8,
  doi:10.1007/978-3-662-03983-0 (cited in Chapter 18).
  Verified: 2026-11-22 via Crossref / Springer Grundlehren vol. 322 (`doi:10.1007/978-3-662-03983-0`).
- **[NeukirchSchmidtWingberg2008]** J. Neukirch, A. Schmidt, and K. Wingberg, *Cohomology of Number
  Fields*, 2nd ed., Grundlehren der mathematischen Wissenschaften 323, Springer, Berlin–Heidelberg,
  2008, ISBN 978-3-540-37888-4, doi:10.1007/978-3-540-37889-1 (cited in Chapter 18).
  Verified: 2026-11-22 via Crossref / Springer Grundlehren vol. 323 (`doi:10.1007/978-3-540-37889-1`).
- **[Page1935]** A. Page, "On the number of primes in an arithmetic progression", *Proceedings of
  the London Mathematical Society* (2) 39 (1935), 116–141, doi:10.1112/plms/s2-39.1.116 (cited in
  Chapter 4).
  Verified: 2026-11-21 via LMS (`doi:10.1112/plms/s2-39.1.116`), ser. 2, vol. 39, pp. 116–141.
- **[Polya1930]** G. Pólya, "Über das Vorzeichen des Restgliedes im Primzahlsatz", *Nachrichten von
  der Gesellschaft der Wissenschaften zu Göttingen, Mathematisch-Physikalische Klasse* 1930,
  19–27 (cited in Chapter 15).
  Verified: 2026-11-21 via Göttingen Digitalisierungszentrum (*Nachr. Ges. Wiss. Göttingen* 1930, pp. 19–27).
- **[Rallis1984]** S. Rallis, "On the Howe duality conjecture", *Compositio Mathematica* 51 (1984),
  no. 3, 333–399; open copy at `http://www.numdam.org/item/CM_1984__51_3_333_0/` (cited in
  Chapters 7 and 12).
  Verified: 2026-11-21 via Numdam (`CM_1984__51_3_333_0`) and EuDML (`doc/89648`), vol. 51, no. 3, pp. 333–399.
- **[Rallis1984b]** S. Rallis, "Injectivity properties of liftings associated to Weil
  representations", *Compositio Mathematica* 52 (1984), no. 2, 139–169; open copy at
  `http://www.numdam.org/item/CM_1984__52_2_139_0/` (cited in Chapter 9).
  Verified: 2026-11-21 via Numdam (`CM_1984__52_2_139_0`), *Compositio Math.* vol. 52, no. 2 (1984), pp. 139–169.
- **[Rallis1987]** S. Rallis, *$L$-Functions and the Oscillator Representation*, Lecture Notes in
  Mathematics 1245, Springer, Berlin–Heidelberg, 1987, xvi+239 pp., ISBN 978-3-540-17694-7,
  doi:10.1007/BFb0077894 (cited in Chapter 9).
  Verified: 2026-11-22 via Crossref / Springer LNM vol. 1245 (`doi:10.1007/BFb0077894`, `ISBN 978-3-540-17694-7`), xvi+239 pp.
- **[RamakrishnanValenza1999]** D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number
  Fields*, Graduate Texts in Mathematics 186, Springer, New York, 1999, ISBN 978-0-387-98436-0
  (cited in Chapter 14).
  Verified: 2026-11-21 via Springer GTM vol. 186 (`ISBN 978-0-387-98436-0`).
- **[Ribet1976]** K. A. Ribet, "A modular construction of unramified $p$-extensions of
  $\mathbb Q(\mu_p)$", *Inventiones Mathematicae* 34 (1976), no. 3, 151–162,
  doi:10.1007/BF01403065 (cited in Chapters 10 and 11).
  Verified: 2026-11-21 via EuDML / Springer (`doi:10.1007/BF01403065`), *Invent. Math.* vol. 34, no. 3 (1976), pp. 151–162.
- **[Riemann1859]** B. Riemann, "Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse",
  *Monatsberichte der Königlich Preußischen Akademie der Wissenschaften zu Berlin* (November 1859),
  671–680 (cited in Chapter 7).
  Verified: 2026-11-21 via Berlin Academy *Monatsberichte* (Nov. 1859, pp. 671–680).
- **[Roth1953]** K. F. Roth, "On certain sets of integers", *Journal of the London Mathematical
  Society* (1) 28 (1953), no. 1, 104–109, doi:10.1112/jlms/s1-28.1.104 (cited in Chapter 17).
  Verified: 2026-11-22 via Crossref / LMS (`doi:10.1112/jlms/s1-28.1.104`), *J. London Math. Soc.* vol. s1-28, no. 1 (1953), pp. 104–109.
- **[Rubin2000]** K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University
  Press, Princeton, NJ, 2000, xii+224 pp., ISBN 978-0-691-05076-8 (cited in Chapters 10 and 11).
  Verified: 2026-11-21 via Princeton University Press AMS vol. 147 (`ISBN 978-0-691-05076-8`), xii+224 pp.
- **[Schmidt1976]** W. M. Schmidt, *Equations over Finite Fields: An Elementary Approach*, Lecture
  Notes in Mathematics 536, Springer, Berlin–Heidelberg, 1976, ISBN 978-3-540-07855-5,
  doi:10.1007/BFb0080437 (cited in Chapter 6).
  Verified: 2026-11-21 via Springer LNM vol. 536 (`ISBN 978-3-540-07855-5`, `doi:10.1007/BFb0080437`).
- **[Selberg1956]** A. Selberg, "Harmonic analysis and discontinuous groups in weakly symmetric
  Riemannian spaces with applications to Dirichlet series", *Journal of the Indian Mathematical
  Society (N.S.)* 20 (1956), 47–87 (cited in Chapter 14).
  Verified: 2026-11-22 via bibliographic records for *J. Indian Math. Soc. (N.S.)* vol. 20 (1956), pp. 47–87 (reprinted in *Atle Selberg: Collected Papers*, Vol. I, Springer, 1989, pp. 423–463).
- **[SerreLocalFields]** Jean-Pierre Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer,
  New York, 1979, doi:10.1007/978-1-4757-5673-9. Chapter III, “Discriminant and Different”, pp. 47–60,
  doi:10.1007/978-1-4757-5673-9_4; §1 “Lattices” (Lemma 1 and Propositions 1–2, pp. 47–48) is compared
  with the signed index in Chapter 10, §§10.4.7.1–10.4.7.2.
  Verified: 2026-11-24 via Crossref (chapter title, pp. 47–60) and the printed text of §1, pp. 47–48
  (read through a full-text search excerpt; the Springer full text was not opened).
- **[Shin2011]** S. W. Shin, "Galois representations arising from some compact Shimura varieties",
  *Annals of Mathematics* (2) 173 (2011), no. 3, 1645–1741, doi:10.4007/annals.2011.173.3.9
  (cited in Chapters 12, 16, and 19).
  Verified: 2026-11-22 via *Annals of Mathematics* (`doi:10.4007/annals.2011.173.3.9`), vol. 173, no. 3 (2011), pp. 1645–1741.
  Retrieved: 2026-11-23 07:04 UTC, journal PDF
  <https://annals.math.princeton.edu/wp-content/uploads/annals-v173-n3-p09-p.pdf>, HTTP 200,
  1,192,295 bytes, sha256 `8a0aca35f1817d60967c48a7e0070d20973b5b057d2dde945780e70ca4a09678`;
  Theorem 1.2 (pp. 1647–1648) and the definition of slight regularity in §7.1 checked. Chapter 19
  records that the archive's `ShinGaloisRep` proposition is defined but neither proved nor used.
- **[Shkoller2009]** S. Shkoller, *Notes on $L^p$ and Sobolev spaces*, lecture notes, 52 pp., PDF dated
  2009-09-10, hosted on J. K. Hunter's UC Davis MAT 218A page; §1.13, Theorem 1.55 and the example after it, p. 15
  (cited in Chapter 3).
  Verified: 2026-11-24, PDF retrieved from `https://www.math.ucdavis.edu/~hunter/m218a_09/Lp_and_Sobolev_notes.pdf` (406322 bytes, SHA-256 `d821ad5b8feebb81500e9c0f6db2ebd137f4298d6c26efe5e0f0fe21f294aa7a`); the iterated integrals $-\pi/4$ and $\pi/4$ are stated on p. 15.
- **[Siegel1935]** C. L. Siegel, "Über die Classenzahl quadratischer Zahlkörper", *Acta Arithmetica*
  1 (1935), no. 1, 83–86, doi:10.4064/AA-1-1-83-86 (cited in Chapters 4 and 16).
  Verified: 2026-11-21 via IMPAN (`doi:10.4064/AA-1-1-83-86`), vol. 1, no. 1, pp. 83–86.
- **[Siegel1935b]** C. L. Siegel, "Über die analytische Theorie der quadratischen Formen", *Annals
  of Mathematics* (2) 36 (1935), no. 3, 527–606, doi:10.2307/1968644 (cited in Chapter 9).
  Verified: 2026-11-21 via EuDML / JSTOR (`doi:10.2307/1968644`), *Annals of Mathematics* vol. 36, no. 3 (1935), pp. 527–606.
- **[Sinnott1984]** W. Sinnott, "On the $\mu$-invariant of the $\Gamma$-transform of a rational
  function", *Inventiones Mathematicae* 75 (1984), no. 2, 273–282, doi:10.1007/BF01388565 (cited
  in Chapter 11).
  Verified: 2026-11-22 via EuDML / Springer (`doi:10.1007/BF01388565`), *Invent. Math.* vol. 75, no. 2 (1984), pp. 273–282.
  Content checked 2026-11-23 in the Göttingen digitization of the original printing, vol. 75,
  pp. 273–282. Theorem 1 compares the transform with the sign-symmetrized restriction to units.
  Section 3 gives the Laurent-monomial independence argument. Chapter 11 §11.4.3.1 gives the
  finite group-ring proof from the pinned Lean archive. The original Ferrero–Washington article
  is the historical theorem citation, and Sinnott is the reference for the transform approach.
  [Göttingen scan](https://gdz.sub.uni-goettingen.de/id/PPN356556735_0075)
- **[SkinnerUrban2014]** C. Skinner and E. Urban, "The Iwasawa Main Conjectures for $\mathrm{GL}_2$",
  *Inventiones Mathematicae* 195 (2014), no. 1, 1–277, doi:10.1007/s00222-013-0448-1 (cited in
  Chapter 10, §10.4.5: §4 "Constructing coycles" [sic] and the map (4.4.3.a), compared with Lemma 10.8;
  the archive does not cite it).
  Verified: 2026-11-23 via Crossref (`doi:10.1007/s00222-013-0448-1`), *Invent. Math.* vol. 195, no. 1 (2014),
  pp. 1–277; §4.3–§4.4 and (4.4.3.a) read in the author-hosted PDF
  <https://www.math.columbia.edu/~urban/eurp/MC.pdf> (1,544,674 bytes, sha256
  `f9faa40aa5e30eba705da88e3d68c8aa43069b5be01c1cc6ece212dd57879748`).
- **[Soule1979]** C. Soulé, "$K$-théorie des anneaux d'entiers de corps de nombres et cohomologie
  étale", *Inventiones Mathematicae* 55 (1979), no. 3, 251–295, doi:10.1007/BF01406843 (cited in
  Chapter 11).
  Verified: 2026-11-22 via EuDML / Springer (`doi:10.1007/BF01406843`), *Invent. Math.* vol. 55, no. 3 (1979), pp. 251–295.
- **[Stepanov1969]** S. A. Stepanov, "On the number of points of a hyperelliptic curve over a
  finite prime field" (Russian: *О числе точек гиперэллиптической кривой над конечным простым
  полем*), *Izvestiya Akademii Nauk SSSR, Seriya Matematicheskaya* 33 (1969), no. 5, 1171–1181;
  English transl. in *Mathematics of the USSR-Izvestiya* 3 (1969), no. 5, 1103–1114 (cited in
  Chapters 6, 7, and 8).
  Verified: 2026-11-21 via Math-Net.Ru (*Izv. AN SSSR Ser. Mat.* 33:5 (1969), 1171–1181) and *Math. USSR-Izv.* 3:5 (1969), 1103–1114.
- **[Tao2015]** T. Tao, "254A, Notes 7: Linnik's theorem on primes in arithmetic progressions", lecture notes on
  *What's new*, 22 February 2015 (cited in Chapter 4). Theorem 2 (a special case of Gallagher's theorem, following
  Chapter 18 of [IwaniecKowalski2004]) and Exercise 5 (truncation at $T=q^2$ with error $O(xq^{-2}\log^2q)$ for $x\ge q^C$).
  Retrieved 2026-11-24, HTML SHA-256 `c6db99bae3d078922b9cccc001041be70543008703a59947ddc2d18cc1f1283a`.
  [Notes](https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/)
- **[Tate1967]** J. T. Tate, "Fourier analysis in number fields, and Hecke's zeta-functions" (1950
  thesis), in J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Academic Press,
  London, 1967, pp. 305–347 (cited in Chapters 7, 8, 12, 14, 15, and 18).
  Verified: 2026-11-21 via Cassels–Fröhlich *Algebraic Number Theory* (Academic Press, 1967, Ch. XV, pp. 305–347).
- **[TaylorWiles1995]** R. Taylor and A. Wiles, "Ring-theoretic properties of certain Hecke
  algebras", *Annals of Mathematics* (2) 141 (1995), no. 3, 553–572, doi:10.2307/2118560 (cited
  in Chapter 11).
  Verified: 2026-11-22 via *Annals of Mathematics* / JSTOR (`doi:10.2307/2118560`), vol. 141, no. 3 (1995), pp. 553–572.
- **[Thorne2015]** J. A. Thorne, "Automorphy lifting for residually reducible $l$-adic Galois
  representations", *Journal of the American Mathematical Society* 28 (2015), no. 3, 785–870,
  doi:10.1090/S0894-0347-2014-00812-2 (cited in Chapters 11 and 16).
  Verified: 2026-11-22 via AMS (`doi:10.1090/S0894-0347-2014-00812-2`), *J. Amer. Math. Soc.* vol. 28, no. 3 (2015), pp. 785–870.
- **[Tschebotareff1926]** N. Tschebotareff, "Die Bestimmung der Dichtigkeit einer Menge von
  Primzahlen, welche zu einer gegebenen Substitutionsklasse gehören", *Mathematische Annalen* 95
  (1926), no. 1, 191–228, doi:10.1007/BF01206606 (cited in Chapter 18).
  Verified: 2026-11-22 via Crossref / EuDML (`doi:10.1007/BF01206606`), *Math. Ann.* vol. 95, no. 1 (1926), pp. 191–228.
- **[Washington1997]** L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Graduate
  Texts in Mathematics 83, Springer, New York, 1997, ISBN 978-0-387-94762-4 (Lemma 1.4 and
  Proposition 2.1, pp. 3, 9–10, cited in Chapter 10, §10.4.7.2; Theorem 4.3, cited in Chapters 2
  and 11).
  Verified: 2026-11-21 via Springer GTM vol. 83 (`ISBN 978-0-387-94762-4`).
  Chapter 11 §11.4.3.2 also cites §6.2 "Stickelberger's theorem" (p. 93), §10.2 "Reflection
  theorems" (p. 188) and §16.2 "Sinnott's proof that $\mu=0$" (p. 380). Section titles and first pages
  checked 2026-11-24 against the Deutsche Nationalbibliothek table-of-contents scan
  (<https://d-nb.info/949560073/04>) and Springer's chapter list (doi:10.1007/978-1-4612-1934-7). These
  sections are cited for the classical statements that the chapter compares with; the proofs it
  transcribes are the archive's.
- **[Weil1948]** A. Weil, *Sur les courbes algébriques et les variétés qui s'en déduisent*,
  Actualités Scientifiques et Industrielles 1041 (Publications de l'Institut de Mathématique de
  l'Université de Strasbourg VII), Hermann, Paris, 1948 (cited in Chapter 6).
  Verified: 2026-11-21 via Hermann ASI no. 1041 (1948) bibliographic records.
- **[Weil1952]** A. Weil, "Sur les «formules explicites» de la théorie des nombres premiers",
  *Communications du Séminaire Mathématique de l'Université de Lund* [Meddelanden från Lunds
  Universitets Matematiska Seminarium], Tome Supplémentaire dédié à Marcel Riesz (1952), 252–265
  (cited in Chapters 14 and 15).
  Verified: 2026-11-22 via Lund Riesz Festschrift bibliographic records (1952, pp. 252–265; reprinted in *André Weil: Œuvres Scientifiques*, Vol. II, Springer, 1979, pp. 48–61).
- **[Weil1964]** A. Weil, "Sur certains groupes d'opérateurs unitaires", *Acta Mathematica* 111
  (1964), 143–211, doi:10.1007/BF02391012 (cited in Chapters 7 and 14).
  Verified: 2026-11-21 via Project Euclid / Springer (`doi:10.1007/BF02391012`), vol. 111, pp. 143–211.
- **[Weil1965]** A. Weil, "Sur la formule de Siegel dans la théorie des groupes classiques", *Acta
  Mathematica* 113 (1965), 1–87, doi:10.1007/BF02391774 (cited in Chapters 15 and 18).
  Verified: 2026-11-22 via Crossref / Project Euclid (`doi:10.1007/BF02391774`), *Acta Math.* vol. 113 (1965), pp. 1–87.
- **[WikipediaFubini]** Wikipedia contributors, "Fubini's theorem", revision 1383075598 of
  2026-10-31T21:23:48Z, section "Failure of Fubini's theorem for non-integrable functions" (cited in Chapter 3).
  Verified: 2026-11-24, wikitext of that revision retrieved with `action=raw` (39938 bytes, SHA-256 `502ac6c4f68e320d9c9910aa4bd31fe15b5a604fbbced3b1b8aa217d3767d7a0`); it gives the iterated integrals $\pi/4$ and $-\pi/4$ and the divergent absolute integral.
- **[Wiles1995]** A. Wiles, "Modular elliptic curves and Fermat's Last Theorem", *Annals of
  Mathematics* (2) 141 (1995), no. 3, 443–551, doi:10.2307/2118559 (cited in Chapter 18).
  Verified: 2026-11-22 via Crossref / JSTOR (`doi:10.2307/2118559`), *Annals of Mathematics* vol. 141, no. 3 (1995), pp. 443–551.

## 7. Our own derived data (not in the repository)

In the run directory: `index/decls.tsv.gz` (1,057,807 declaration headers with file:line),
`index/imports.tsv.gz`, `index/files.tsv.gz`, `index/import_cones.json` (built by
`build_index.py`); `static_scan.json` (by `static_scan.py`); `kexactB_family_files.txt` (72 files);
`citations_report.txt` (by `check_citations.py`, a machine check of every file:line citation in
`chapters/` and `notes/` against the extracted archive and the Mathlib files above). See
`notes/proof-map.md`, "Reproducibility".

For Chapter 13, Section 13.4.4 (run `rhbook-ch13-green-existence-1123h-11231636`, 2026-11-23):
`verify_green_gl2f3.py` (sha256 `b06b1112486a148471e9f5a747fd7ec64837b8c0931a4741f843866645a0de9f`;
Python standard library only, no arguments, read-only) recomputes Example 13.4 in exact arithmetic in
$\mathbb Q(\zeta_{24})$ and passes 2,431 assertions in 0.39 s CPU; `check_section_citations.py` resolves
the 143 archive citations of the section against the pinned archive and prints each cited line.

For Chapter 13, Section 13.4.10 (run `rhbook-ch13-positive-sign-1124h-11242112`, 2026-11-24):
`check_positive_sign.py` (sha256 `b2a593adb24b260967f078c2dcf73084ed91c545a6b47a4671346703f72d2a9c`; Python standard library only, no arguments,
read-only) recomputes Examples 13.24–13.25 (exact arithmetic in $\mathbb Q(\zeta_8)$ for
$\mathrm{GL}_2(\mathbb F_3)$, all 81 endomorphisms), enumerates subspaces of $\mathbb F_2^n$ ($n\le4$),
$\mathbb F_3^n$ ($n\le3$) and $\mathbb F_5^n$ ($n\le2$) for Lemma 13.26 and the identity value of Lemma 13.27, and
checks the $q$-binomial and kernel-count identities. It passes 2,001 assertions in 0.12 s CPU.

# Part II. Annotated bibliography by category

*Added 2026-11-21 (run `rhbook-sources-11211242`); status as of 05:57 UTC. Part I above — the source map and the exact-version tables — is unchanged; entries here that Part I already pins point back to it instead of repeating its hashes.*

**Conventions.**

- All times are UTC. "Retrieved" is our own download in this run unless another run is named. Raw copies, API responses and the fetch logs (`FETCH-LOG.tsv`, one line per request: time, HTTP status, bytes, sha256, ETag, Last-Modified, final URL) are kept outside the repository in `~/Hermes/state/quota/runs/rhbook-sources-11211242/` (`raw/`, `research/*/raw/`); nothing listed here is redistributed with the book.
- sha256 is of the bytes we received. Pages with live parts (blogs with comment counts, news sites, GitHub pages, Zulip) return different bytes on every request, so for them the hash only identifies our copy; the version line says which text we read. Pages that refused scripted requests were read in a rendering browser; those have no byte hash, and we say so. "HEAD" means we asked for headers only.
- Internet Archive digests are base32 SHA-1 of the archived payload. Where we write "equals our copy", we computed the same digest from our file.
- Each entry ends with what the source contributes and how much weight it can bear. That judgment is about the source as a record of events; it is not a verdict on the mathematics.
- Entry IDs (A1, V3, …) are cited in "The story so far" (`chapters/02-the-story-so-far.md`). A: primary sources; V: verification; G: guides and teaching; E: errata and disputes; C: commentary; P: press; S: surveyed only.

## Primary sources (A)

### Alpöge

<a id="a1"></a>
**A1. Levent Alpöge, four-page note announcing the proof (`remark.pdf`).**

- URL: <https://alpo.ge/remark.pdf>
- Author: Levent Alpöge (the note is unsigned; it is posted on his site and its footnote 1 links the archive).
- Version / date: PDF `CreationDate` 2026-11-20 12:52:48 UTC. First Internet Archive capture 2026-11-20 14:19:58 UTC, digest `M652L7WBO6BAV3OFKUXHFEEP4J767IYF`, which equals our copy: the file has not changed since that capture.
- Retrieved: 2026-11-21 04:47:40 UTC, HTTP 200, 245,114 bytes, sha256 `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d`; byte-identical to the copies of 02:51 (run `rheval-1121`), 04:02 (Part I) and 04:58 UTC
- Contribution and reliability: The only account of the method by its author. Page 1 states the claim ("I believe I have, working with Claude, discovered a proof of the Riemann Hypothesis"), says the method gives GRH and, the author expects, ERH "with more time", and that the arguments are formalized "without assumptions"; it describes the proof as a descendant of Stepanov's method in which a chain of theta lifts of length about $\sqrt X$ plays the role of multiplicity. Page 2 explains the timing ("This all happened for me late Sunday night"; he messaged "Dario" — identified by the press as Anthropic's chief executive Dario Amodei — about announcing) and why only Lean was released; its footnote 2 says the informal text "hit 250,000+ pages". Pages 3–4 give a dated list of twenty steps from 2026-10-06 to "11/16/26: GRH", which the note says Claude compiled. Authoritative for what the author claims and when; it contains no proofs, and the author himself warns that parts of the timeline paraphrase an AI summary and may need correcting. Cited as [Paper] by page.

<a id="a2"></a>
**A2. Alpöge, Lean archive `lean.tar.gz`, 14 parts.**

- URL: <https://alpo.ge/lean.tar.gz.part01>; …; <https://alpo.ge/lean.tar.gz.part14>
- Author: Levent Alpöge "working with Claude" (A1, p. 1); no author or licence file inside the archive (Part I, §1).
- Version / date: One version only. Joined archive 239,275,554 bytes, sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` (Part I, §1, with the hash of every part). Internet Archive captures of 2026-11-20 14:20:03 UTC (part01, digest `CZ6VXZQYX2DFMC5VUK5DU4DNNWQZ6MJ6`) and 14:20:02 UTC (part14, digest `MJWCBVZTTX6PBY6G3CU7VZBR3MKIL2SD`) equal our copies.
- Retrieved: Downloaded 2026-11-21 04:01:46–04:05:21 UTC (Part I, §1). Re-checked by HEAD requests at 04:52:54 UTC (parts 01, 14) and 05:23:34–05:23:40 UTC (all 14): every part answered HTTP 200 with the ETag recorded at download. The ETag is not a content hash (it differs from the parts' MD5), so it is evidence that the server holds the same file, not proof.
- Contribution and reliability: The primary object of the book: 175,187 Lean files whose `src/Main.lean` proves Mathlib's `RiemannHypothesis` and four forms of GRH for Dirichlet L-functions (Chapter 1). Every public check (V1–V9) names the same joined hash, so all reports are about the same bytes. The server answers HTTP 200 with an HTML page for parts that do not exist, so only the joined hash is a real check (Part I, §1).

<a id="a3"></a>
**A3. Alpöge, personal home page.**

- URL: <https://alpo.ge/>
- Author: Levent Alpöge.
- Version / date: No date on the page. The Internet Archive holds 44 captures from 2024-07-28 to 2026-10-19 (CDX index, retrieved 05:23:40 UTC); none after the announcement.
- Retrieved: 2026-11-21 04:47:40 UTC, HTTP 200, 11,625 bytes, sha256 `a7ee08f4821ec5bfdebbc8860730b497b3e252a49fadc14d0d888c9e38a25276`; same bytes as the copies of 02:51, 04:02 and 04:42 UTC (Part I, §2)
- Contribution and reliability: Establishes that the note and the archive sit on the author's own domain; the page itself does not link them, so the note is reachable only by its direct URL. Useful only for provenance.

### Masullo

<a id="a4"></a>
**A4. Alessandro Maria Masullo, *The Music of the Primes* (draft, 940 pages).**

- URL: <https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf>
- Author: Alessandro Maria Masullo. Posted by Ravi Vakil on his Math 216 blog (A5).
- Version / date: PDF `CreationDate` 2026-11-20 19:13:46 +01:00 (18:13:46 UTC). First Internet Archive capture 2026-11-20 18:35:24 UTC, digest `JIP2RPUAOK3GITO37F4XCPDPBWJBGJ56`, which equals our copy. sha256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`, 6,756,996 bytes (Part I, §3).
- Retrieved: 2026-11-21 04:58:41 UTC, HTTP 200, 6,756,996 bytes, sha256 `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`; identical to Part I's download of 04:05:30 UTC and to the copy of 03:01 UTC
- Contribution and reliability: The human-written GRH draft: an adelic trace-formula route aimed at GRH for Hecke L-functions of all number fields (p. 6). By its author's account it is unfinished — the acknowledgements (p. 6) mention "several glitches here and there" known to him and Brian Conrad, footnotes such as "Insert statement." remain, and Chapter 13, where GRH should follow from Theorem 12.5.1.1, is two pages without a main theorem (pp. 521–522). The same page says the work took "nearly 12 years", that Conrad and Vakil were arranging "for me to return to Stanford for a year to finish the polishing of the paper", that "In light of the current climate I am being advised to release the current version as it is", and that "The math is complete, and only filling in some writing remains on several parts across this long paper". Authoritative for what Masullo claims; its correctness is disputed (E1–E7). Cited as [Paper] by page.

<a id="a5"></a>
**A5. Ravi Vakil, "Hurried Announcement: Alessandro Masullo GRH" (blog post).**

- URL: <https://math216.wordpress.com/2026/11/20/hurried-announcement-alessandro-masullo-grh/>
- Author: Ravi Vakil (Stanford).
- Version / date: Published 2026-11-20 18:18:42 UTC; edited, `dateModified` 2026-11-21 02:54:54 UTC. Original text preserved by Internet Archive captures of 18:35:24 and 20:18:59 UTC (CDX digests `X5TH55RVY7PF3HJRPDJVUBJWXY7G5NN5`, `VGEGSYSHI6NYEWT5AAZAS7HACOPRVCQM`).
- Retrieved: 2026-11-21 04:58:46 UTC, HTTP 200, 76,180 bytes, sha256 `e8097afe19b0a095e2cc2df04d9ee94c44162e71a247f0e928ebbfee309c62f4`; capture of 18:35:24 UTC read via `web.archive.org/web/20261120183524id_/…`, 2026-11-21 05:01:26 UTC, HTTP 200, 86,353 bytes, sha256 `45dfdec5e57dfeaddf7c928f515fcd3d470e3a0ad66a4e5520a548e3aa30c524`; Part I's copy of 04:05:38 UTC is the edited version
- Contribution and reliability: The release of Masullo's draft. The original post, written from an AMS meeting, says Conrad "has been looking closely at it for months", that it is "so far looking good", that "It is all human, with no AI", and that the plan had been to bring Masullo to Stanford for a year before announcing. The edit (our diff of the capture against the live page) changes the name to "Alessandro Maria Masullo", "so far looking good" to "so far looking good to him", and the plan to "have Brian work with Alessandro for a year", and adds an "Update about 8 hours later": several people reported problems found "with the assistance of different AI models", and "(I make no claim as to the correctness of the proof strategy.)". First-hand for Vakil's own statements; second-hand for Conrad's view (Conrad's own words are in P4). Quote the version you mean.

### Background documents (not about the November claims)

<a id="a6"></a>
**A6. Anthropic, "Learning more about Claude's mathematical capabilities" (research post on zeros of ζ).**

- URL: <https://www.anthropic.com/research/riemann-zeta>
- Author: Anthropic (organisation).
- Version / date: Published 2026-08-10; `dateModified` 2026-11-13 22:37:05 UTC.
- Retrieved: 2026-11-21 05:23:46 UTC, HTTP 200, 169,931 bytes, sha256 `55ba08ad9eb05e1fab4f9e8c2e60a7fa453c62ca62a636ff9129cc21948f4c43`
- Contribution and reliability: Context only. Anthropic reports that an unreleased Claude model raised the proven proportion of zeros of ζ on the critical line from 41.6% to 67.2%, with the paper examined by Brian Conrey and Dan Goldston, and states "We don’t expect that the techniques Claude used will lead to proving the Riemann hypothesis" — a sentence The Verge quoted on 20 November (P10). A company statement about its own model, not about Alpöge's claim.

<a id="a7"></a>
**A7. Alessandro Maria Masullo, *Arithmetic deformations of crystalline cohomology* (Ph.D. thesis, Stanford University).**

- URL: <https://purl.stanford.edu/kp533pz4708>; <https://mathgenealogy.org/id.php?id=272472>
- Author: Alessandro Maria Masullo.
- Version / date: Stanford Digital Repository record dated 2020; the Mathematics Genealogy Project lists the Ph.D. in 2019.
- Retrieved: 2026-11-21 05:03:06 UTC, HTTP 200, 22,629 bytes, sha256 `d81ce2ef3bbbe45e855c26258957f6caea7cfbad8a325a6f10cee423dc93ade2`; MGP page 2026-11-21 05:03:07 UTC, HTTP 200, 10,409 bytes, sha256 `d32bd28f89e7160628725d95c7d97ed52abf4d37f46de444d88c177ccae5a476`
- Contribution and reliability: Background on the author: a Stanford Ph.D. in arithmetic geometry; the record lists Brian Conrad as degree supervisor and Conrad, Daniel Bump and Ravi Vakil as thesis advisors. It explains why Conrad and Vakil appear in A4–A5. It says nothing about his present position, which the press reports inconsistently (P7, P12, P17 citing LinkedIn, and P21 call him a postdoctoral researcher at Stanford; A4, p. 6, speaks of arrangements "for me to return to Stanford for a year").

## Verification (V)

<a id="v1"></a>
**V1. Andrew Sutherland, "Verification files for the Lean proof of the Riemann Hypothesis".**

- URL: <https://math.mit.edu/~drew/grh/>
- Author: Andrew Sutherland (MIT); "checks run with Claude Code" (page header).
- Version / date: Three versions seen. (a) "Page last updated 2026-11-20 19:45 UTC", preserved by the only Internet Archive capture (2026-11-20 19:57:27 UTC); we read it via the `id_` endpoint, retrieved 2026-11-21 05:25:07 UTC, HTTP 200, 10,285 bytes, sha256 `73f96192496df3a3adca39a462e704c7dd4186e342f5c53c32ae1910ee91a697`. (b) "Page last updated 2026-11-20 22:05 UTC", retrieved through 05:56 UTC (`12,782` bytes, `de7153ec…`). (c) "Page last updated 2026-11-21 10:05 UTC", retrieved 2026-11-21 12:42:26 UTC, HTTP 200, 18,306 bytes, sha256 `d35ac26a55e5f4a318450fd4e8b52029fbe82df546f1559511ce9cbc1bda629b` (adds the `kimihiro64/Robin1984` arithmetic-consequences checks on a 61,752,134,938-byte combined export `44651dcc…` and a 240-module `lake build` path-comparison sample; main `lake comparator` and export Lean kernels remain "running").
- Retrieved: 2026-11-21 05:24:05 UTC, HTTP 200, 12,782 bytes, sha256 `de7153ec1b22acab193a99824d427d41050e2c0d2c4374ec518d52fc0de62307`; identical bytes at 02:51, 04:02, 04:42 (Part I, §5) and 04:47:41 UTC; files linked from the page retrieved 05:24:06–05:24:14 UTC: `SHA256SUMS` sha256 `d8496902f492eeb0274460e525071cc30803bba7817d59b27c874f5a25317373`, `comparator.json` `8ea890e6ccda9cf3983ada343af18a41d12542036875a3936e7925ed5b1582ff`, `audit.log` `0a1473fce6eed840011f4a76b1c51558fc6f03edd1e6bd1ee542e6c738d87a62`, `nanoda.log` `d4c5360b02d8dd885150c1cc28b616cb6fb5bf5b20d142558d79a7b15ae9d9df`, con-leche logs `23e27eacb9e83785…`, `5a068bf55f24904e…`; each equals the value in `SHA256SUMS`. The export `solution.ndjson.zst` (7,699,933,588 bytes, Last-Modified 2026-11-20 18:37:31 UTC), `challenge.ndjson.zst` (46,881,299 bytes, 19:03:08 UTC) and `project-oleans.sha256` (28,865,695 bytes, 19:39:50 UTC) were checked by HEAD only
- Contribution and reliability: The most detailed public record of the machine checks: full compile (finished 16:43:21 UTC), axiom audit, `leanchecker` replay of every module (about 18:17), nanoda on the 61.57 GB export (exit 0 at 19:05:45), con-leche master and `--compare` (21:19:04 and 21:19:12), lean4lean module by module (about 21:55), with versions, hashes, a reproduction recipe and an explicit list of caveats (unsandboxed build; a 77-module sample compared with `lake build`; sandboxed-export comparison not yet made). The 19:45 version showed con-leche and con-ron "declined" (older binaries could not read one reflexive inductive type); the 22:05 version records the master build accepting. As of our last check the Lean default and paranoid kernels on the export and the end-to-end `lake comparator` run are "running". A careful first-hand log by a named expert; the checks were orchestrated by an AI agent and the page is updated in place, so cite the version.

<a id="v2"></a>
**V2. Lean Zulip, channel #general, topic "Discussion: Alpöge Proves the Riemann Hypothesis".**

- URL: <https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis>; read through the public API: `https://leanprover.zulipchat.com/json/messages` with narrow `channels:web-public`, `channel:general`, `topic:<name>`
- Author: Lean community; 119 distinct posters in our copy. First message by Jack McCarthy (Zulip user 989743).
- Version / date: 403 messages, ids 642224678 (2026-11-20 13:58:06 UTC) to 642423725 (2026-11-21 05:23:32 UTC). Messages can be edited, moved or deleted by moderators, who said they had deleted off-topic messages (Rémy Degenne, quoted at 17:14:14; Buzzard, 18:39:29).
- Retrieved: 2026-11-21 05:27:36 UTC, JSON 793,590 bytes, sha256 `8337bcdddb66a9b65970a6a2ba28ad12c09c51b99446a80ece725c1dbe8b95a3`; the 40 newest messages again at 2026-11-21 05:57:11 UTC (to id 642425070, 05:35:31 UTC; 80,510 bytes, sha256 `b45b9e8882b8c38616f18f6430b1685ff1e3b2ac681ceb5d89255b22df9e651e`); and the 80 newest messages at 2026-11-21 12:42:37 UTC (to id 642473400, 12:37:00 UTC; 137,989 bytes, sha256 `b3ee190658a57bce05dc1bd66acc92fc587194c0718186560854f3cb7707648f`, including Dixit's build/trace/export-hash posts `#642435200` and `#642470541` and Loeffler's `KatoTwoW` reply `#642442900`)
- Contribution and reliability: The working record of the verification: the first public report (McCarthy 13:58:06, compiling "on two separate devservers"), Sutherland's posts of his compile (16:53:16, 16:55:59) and of nanoda (19:09:53), Teżewski's runs of con-leche (20:40:10), pestka (20:58:04) and gruszka (01:56:46), Breitner's and Carneiro's explanations of the checkers, Buzzard's moderation and his "we still await a successful `comparator` run" (18:44:35), and Kim Morrison's summary that "there are essentially no remaining doubts as to whether this is a correct proof" (01:07:22) with plans for clean-up. Earlier book text and Part I treated the stream as login-only; it is web-public. Primary for who reported what and when; each claim is the poster's own and many posts relay AI-generated summaries (marked as spoilers per channel rules). Cite by message id (`/near/<id>`).

<a id="v3"></a>
**V3. Lean Zulip, channel #general, topic "Formalising Masullo's proof of GRH".**

- URL: <https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Formalising.20Masullo.27s.20proof.20of.20GRH>
- Author: Lean community; opened by David Loeffler.
- Version / date: 106 messages, ids 642314625 (2026-11-20 19:16:18 UTC) to 642417410 (2026-11-21 04:30:16 UTC).
- Retrieved: 2026-11-21 05:28:04 UTC, JSON 125,534 bytes, sha256 `8d27170d8f5f7f19b3feccbbf11e399c8d1348fd2507985620a4d2f164ba037c`; the 40 newest messages again at 2026-11-21 05:57:12 UTC (52,519 bytes, sha256 `626025488f4c2b51f5097a2c2000e35f1a15836c158e6cb61f5c05d4cd376aa9`), no new message
- Contribution and reliability: Where the Masullo formalization was organised (Prove2Me mission opened 19:16:58, live 21:41:34) and where the first public doubts about the main theorem appeared: Tim Gehrunger reported at 19:32:09 that an LLM found an apparently simple counterexample to Theorem 12.5.1.1 and at 19:42:57 that correcting one error reduces it to a classical formula ("at least that is what Astra and Fable seem to agree on"); Brent Yee linked the Refine report (E6) at 22:38:07. Buzzard objected (20:05:57) to using the forum "to deconstruct someone's proof in public", since the author "did not ask for it to be disassembled in this public way"; Floris van Doorn replied (20:13:09) by quoting Vakil's request that people "quickly check it, formalize, fill any small gaps". Primary for the sequence; the mathematical claims are relayed AI readings unless stated otherwise.

<a id="v4"></a>
**V4. Lean Zulip, channel #AI authored projects, topic "Anthropic employee claims proof of the Riemann Hypothesis?".**

- URL: <https://leanprover.zulipchat.com/#narrow/channel/AI%20authored%20projects>
- Author: Kelly Davis (opening post), Kevin Buzzard, Junyan Xu.
- Version / date: 4 messages, 2026-11-20 16:16:43–17:36:28 UTC.
- Retrieved: 2026-11-21 05:28:25 UTC, JSON 3,884 bytes, sha256 `2ed47e42b413df0f826d1e48adb70ca7bd3840c45520c1904c0ca673ddf487c0`
- Contribution and reliability: A short side thread, redirected by Buzzard to V2; its value is Junyan Xu's pointers to the first two public repositories of the extracted code (G8). Minor.

<a id="v5"></a>
**V5. Comparator setup `leanprover-community/riemann-hypothesis` (created as `Deicyde/riemann-hypothesis`).**

- URL: <https://github.com/leanprover-community/riemann-hypothesis>
- Author: Created by GitHub user Deicyde (commits as Jack McCarthy); contributions by marcelolynch, kim-em and others.
- Version / date: Created 2026-11-20 14:47:49 UTC; first commit `40e56bab0265` 14:36:09 "Mirror the submission exactly as published"; HEAD `4286c9ca372a` (2026-11-21 04:27:41) at our check; 27 commits, issues and PRs #1–#10, 42 CI runs.
- Retrieved: GitHub API (repository, commits, issues, pulls, Actions runs, tree) retrieved 2026-11-21 05:24:18–05:24:32 UTC; `README.md` 2026-11-21 05:24:33 UTC, HTTP 200, 4,642 bytes, sha256 `1e6b09aa2f416d580eea1ccb1532ac1d76f0d51aac0600c368db84463a7faa95` (changed since Part I's copy of 04:02:24 UTC); `verification/NOTES.md` 2026-11-21 05:24:33 UTC, HTTP 200, 15,489 bytes, sha256 `a0b67cd13f99bb2c6de9a3ff569716f44fe732abaf31fe013a07434fb5dfcf2b` (same as Part I); `src/Challenge.lean` 2026-11-21 05:24:34 UTC, HTTP 200, 1,222 bytes, sha256 `a3cebbf30be6b9268a0ed413c9bbc256dfa9f4bfa04f1a75f144d135da5e21a5`
- Contribution and reliability: A byte-exact mirror of the archive plus what Comparator needs: a challenge file stating the five theorems against Mathlib alone, a pinned export procedure, CI that publishes the challenge export (its sha256 `bd484ac9…b2b9` matches V1), and verification notes on the statements, pins, kernel fixes and metaprogramming. The notes were corrected after issue #2 (commit `e50d09817ad8`, 20:43:21). After moving to the leanprover-community organisation it became the hub for clean-up: a public build cache (PR #7, merged 04:27:42), import minimisation (PRs #4, #8–#10, open) and the observation that `.olean` hashes depend on the build directory (issue #6). It does not itself post a Comparator verdict. Reliable as a record of procedure; the repository is a mirror, so we link rather than copy it.

<a id="v6"></a>
**V6. Aapo Lipponen, independent check on LUMI (`aapolipponen/rh-lean-check-lumi`).**

- URL: <https://github.com/aapolipponen/rh-lean-check-lumi>
- Author: Aapo Lipponen; docs edited from AI review reports.
- Version / date: README "Status: compile complete (updated 2026-11-20 22:30 UTC)" at HEAD `82d91dbbd04d` (2026-11-20 23:56:59 UTC); updated to "Status: compile and dependency audit complete (updated 2026-11-21 12:40 UTC)" at HEAD `d6881c9066` (2026-11-21 12:37:16 UTC), walking all 1,478,243 constants in the compiled proof terms (`146,437 / 175,187` project modules and `5,081` Mathlib modules used).
- Retrieved: README 2026-11-21 05:24:35 UTC, HTTP 200, 9,064 bytes, sha256 `4a51000fb1a6d43a22f8a4e26a160ffe6ef22e50646a18ac92ff9cc8e237789c`; re-retrieved 2026-11-21 12:42:27 UTC, HTTP 200, 9,779 bytes, sha256 `72da7b8d8e8ad0b3c6822fbc7151a198e8234516093b9a2ad11fb6a54c01ec7a`; `results/build-summary.json` 2026-11-21 05:24:36 UTC, HTTP 200, 453 bytes, sha256 `a2763844491a03287ecdbfe5868d71146a7d8ed22a70695b95bf7c12091fe072`; earlier copies identical to Part I's (§5)
- Contribution and reliability: A second full compile, each `lean` process in a no-network sandbox on 8 LUMI-C nodes: 175,187 of 175,187 modules, 0 failures, `src/Main.lean` finished 22:21 UTC; `Main.olean` and `Statements.olean` hashes equal to Sutherland's. That match is the strongest public evidence that V1's unsandboxed build was not tampered with. The README is explicit about what it did not run (kernel replay, second kernel) and credits V1 and Teżewski for those. High reliability for what it reports.

<a id="v7"></a>
**V7. Infatoshi, "Independent Verification Receipts" (`Infatoshi/rh-verification-receipts`).**

- URL: <https://github.com/Infatoshi/rh-verification-receipts>
- Author: GitHub user Infatoshi.
- Version / date: Repository created 2026-11-20 21:51:07 UTC, last push 21:51:13 UTC.
- Retrieved: 2026-11-21 05:32:03 UTC, HTTP 200, 5,192 bytes, sha256 `b34fb1aa96eea0af2a86b881f1d0bee96264e09bedb3a260dec5c0c8584a5ba7`
- Contribution and reliability: A third compile (stock Lean 4.33.1 called directly, 175,187 of 175,187 modules, finished 19:05:21 UTC), a statement pin against unmodified Mathlib, `#print axioms`, a static scan, and a nanoda run (commit `0da9f98f`) over the closure of the five theorems: "Checked 1484729 declarations with no errors". Its `Main.olean` hash (`ce9a2006…`) differs from V1/V6, probably because compiled files record the build directory (V5, issue #6; our inference), so it confirms the result, not V1's bytes. Pseudonymous and self-published, but the receipts are specific and reproducible.

<a id="v8"></a>
**V8. Simon DeDeo, "Compiled oleans for the alpo.ge Proof of the Riemann Hypothesis" (Proofs & Reasons).**

- URL: <https://proofsandreasons.io/rh-oleans.html>
- Author: Simon DeDeo (Carnegie Mellon); the page credits a John Templeton Foundation grant.
- Version / date: Build of 2026-11-20 (x86_64 Linux, Lean 4.33.1, Mathlib v4.33.1); link posted on V2 at 20:13:23 UTC.
- Retrieved: 2026-11-21 05:32:05 UTC, HTTP 200, 25,330 bytes, sha256 `f31a6196e3ecb3426c45f52e5bfe3a3c680a3072b70ed2faab9c5379a76339f9`
- Main-theorem export (compressed SHA-256 `d5fad83247dd024e1a77d283aa766ac745432b7159dfffc11bb05996c46a89fb`,
  as listed by DeDeo). [Direct download](https://photos.proofsandreasons.io/alp-oleans-357309b5dd12/alp-export-main-theorems.ndjson.gz)
- Contribution and reliability: Hosts the `.olean` files of all 175,187 modules (31.9 GiB in 14 archives) and two `lean4export` files so that others can run kernels without about 530 CPU-hours of compiling. Reports `#print axioms` and a kernel replay with Lean itself, and says plainly that no second kernel was run there and that "Sharing them is not a statement about whether the proof is correct." A resource, honestly labelled.

- Chapter 19 follow-up, 2026-11-23: retrieved the 9,360,239,746-byte
  [main-theorem export](https://photos.proofsandreasons.io/alp-oleans-357309b5dd12/alp-export-main-theorems.ndjson.gz)
  and verified the compressed SHA-256 `d5fad83247dd024e1a77d283aa766ac745432b7159dfffc11bb05996c46a89fb`
  against the publisher's manifest. Its decompressed SHA-256 is
  `4301ce4828d397c728e87f3e6a1251aa42abe5e12809bb9e0b73cc3d33072e7e`.
  The `5ea74b91…244e` in Chapter 16 identifies the separately published Sutherland stream (V1).
  The DeDeo file has five roots. The §19.4 computation parsed all 1,080,769,494 NDJSON records and
  traversed declaration types and values, projections, and inductive data from `riemannHypothesis`
  alone. The traversal reached 1,478,219 declarations. Its positive checks include
  `ResidueKilled.DM` and `ResidueKilled.dm_of_two`. The full `DoublingMethod` and
  `SiegelEisensteinSimplePole` are absent from the export. The computation establishes
  named dependency membership for this export.

<a id="v9"></a>
**V9. Szymon Teżewski, independent-checker runs, and the Gruszka kernel (`jasisz/gruszka`).**

- URL: <https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642355040>; <https://github.com/jasisz/gruszka>
- Author: Szymon Teżewski (Zulip); GitHub user jasisz.
- Version / date: Zulip messages 642334721 (20:40:10), 642338051 (20:52:29), 642339366 (20:58:04), 642340706 (21:02:44), 642355040 (22:06:33), 642395135 (2026-11-21 01:56:46). Repository created 2026-11-16, last push 2026-11-21 02:02:35 UTC.
- Retrieved: Zulip messages from V2; repository metadata by GitHub API at 05:32 UTC.
- Contribution and reliability: The first report that con-leche accepts the export (20:40, before V1 recorded it), a run of the pestka checker (accepted), notes on checkers that did not get through (nano-lean could not parse the export; gruszka stuck on two declarations — "neither is a rejection"), a table of all accepted runs at 22:06, and later a fixed gruszka accepting the whole export "in 4.5 min on my laptop". Specific and consistent with V1; individual claims are the poster's own.

<a id="v10"></a>
**V10. Rohan Arun, "Independent replay of Alpöge’s RH release" (`rohanarun/alpoge-rh-replay`).**

- URL: <https://github.com/rohanarun/alpoge-rh-replay>
- Author: GitHub user rohanarun.
- Version / date: README as of our retrieval: "Full replay in progress. No full RH verification receipt has been produced by this project."
- Retrieved: 2026-11-21 05:32:04 UTC, HTTP 200, 24,355 bytes, sha256 `2ab5aeaae069a52752a7b010842acfa8f6b3b5f4a873b102d4e07c1da7bdae85`
- Contribution and reliability: A crowd-sourced, module-by-module replay with 175,187 tasks in 2,858 packets; only a pilot has run. Useful as infrastructure; no result yet.

<a id="v11"></a>
**V11. The checkers and toolchains.**

- URL: <https://github.com/leanprover/con-leche>; <https://github.com/leanprover/con-leche/pull/22>; <https://github.com/digama0/lean4lean>; <https://github.com/leanprover/lean4/releases/tag/v4.36.0>; <https://github.com/leanprover/lean4/releases/tag/v4.34.1>
- Author: Lean FRO and contributors (con-leche: Joachim Breitner and others; lean4lean: Mario Carneiro).
- Version / date: Versions used in V1: con-leche master `cd2eceab` and branch `compare` `5dc36dc1`; lean4lean `67f63b0c`; nanoda as bundled with Lean v4.36.0 (published 2026-11-16 15:45:27 UTC); Lean v4.34.1 published 2026-09-24. con-leche master has moved on since (HEAD `11d8ff13`, 2026-11-21 01:20:35 UTC).
- Retrieved: GitHub API (release records, con-leche commit lists) retrieved 2026-11-21 05:24:30–05:24:32 UTC.
- Contribution and reliability: Background for reading V1, V7 and V9: what each checker is and which version produced which verdict. Breitner explains on V2 (20:50:29) what con-leche's guarantees rest on, and that the version bundled with Lean 4.36 was out of date (20:54:33). Cite release pages for versions only.

<a id="v12"></a>
**V12. Internet Archive captures used as integrity evidence.**

- URL: <https://web.archive.org/web/20261120141958/https://alpo.ge/remark.pdf>; <https://web.archive.org/web/20261120183524/https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf>; <https://web.archive.org/web/20261120195727/https://math.mit.edu/~drew/grh/>
- Author: Internet Archive (captures made by its crawlers or by readers).
- Version / date: CDX records: remark 20261120141958; part01 20261120142003; part14 20261120142002; Masullo PDF 20261120183524; Vakil post 20261120183524 and 20261120201859; Sutherland page 20261120195727; alpo.ge root, 44 captures to 20261019120255.
- Retrieved: CDX API retrieved 2026-11-21 05:23:40–05:23:45 UTC (`raw/A/wayback/`).
- Contribution and reliability: Our own integrity check [Checked]: for remark.pdf, part01, part14 and the Masullo PDF the archived SHA-1 equals that of our download, so these files have not changed since the first captures (14:19–14:20 and 18:35 UTC on 20 November). For the HTML pages the captures preserve earlier wording (A5, V1) but the digests are of the archived payload and need not equal a fresh download.

### Formalization of Masullo's draft

<a id="v13"></a>
**V13. Ryan McCorvie and contributors, `mccorvie/riemann-masullo` (Lean formalization of the draft).**

- URL: <https://github.com/mccorvie/riemann-masullo>
- Author: Ryan McCorvie (integrator) with human and agent contributors.
- Version / date: README states: "On hold (20 November 2026)" in commit `9384ba8` (20:03:39 UTC); "Active: formalizing the prerequisites" again in `579875a8` (22:57:02 UTC); last README change `f0e128c2` (2026-11-21 03:06:11); HEAD `27567d50` (04:56:05). Counts at 04:59 UTC: 1,845 issues (1,086 open) and 605 PRs (587 merged).
- Retrieved: 2026-11-21 04:59:47 UTC, HTTP 200 (gh api, authenticated read-only), 8,899 bytes, sha256 `69352b475c7a8b58785d2d0e4ae50bb944cf7e7f79d422f8c36e81794e223b9f`; README byte-identical to Part I's copy of 04:05:40 UTC; README at `9384ba8` and the counts are in `research/GM-guides-masullo/raw/gh/`
- Contribution and reliability: A public, agent-assisted formalization proceeding in waves (appendices and early chapters first). Its README separates what the project found (small errors in standard material, logged in E1) from the concerns about Theorem 12.5.1.1 raised on V3, which "did not come from this formalization". The "On hold" episode and its reversal are part of the story (Chapter 2). Reliable as a record of its own state; its statements of Masullo's results are reconstructions, some explicitly unreviewed.

<a id="v14"></a>
**V14. Prove2Me mission "Masullo: The Music of the Primes — Riemann Hypothesis specialization".**

- URL: <https://prove2.me/missions/Masullo%3A_The_Music_of_the_Primes_%E2%80%94_Riemann_Hypothesis_specialization>
- Author: Mission captain "davidloeffler" (page); announced on V3 by David Loeffler.
- Version / date: Announced 2026-11-20 19:16:58 UTC, live after maintainer approval at 21:41:34 UTC (V3).
- Retrieved: 2026-11-21 05:03:05 UTC, HTTP 200, 96,430 bytes, sha256 `92bd19702276e818356467cd4f84734b6358e66df4d861cc00a82571fee454bf`
- Contribution and reliability: A second formalization effort, working backwards from the goal: by 22:18 Loeffler reported a formal proof that RH follows from Masullo's "Main Theorem" 12.5.1.1 (V3). The page is script-heavy and shows little without login; that the captain is the number theorist David Loeffler is our inference from the matching names. Cite for the mission's existence and stated scope.

## Guides and teaching (G)

<a id="g1"></a>
**G1. LUMI reader's guide, `docs/` of `aapolipponen/rh-lean-check-lumi` (pages 01–10, glossary, reports).**

- URL: <https://github.com/aapolipponen/rh-lean-check-lumi/tree/main/docs>
- Author: Aapo Lipponen (editor), from AI-agent review reports.
- Version / date: Added in commit `40e1ae43477a` (2026-11-20 22:40:20 UTC); unchanged at HEAD `82d91dbbd04d`.
- Retrieved: Every file pinned in Part I, §5 (retrieved 04:02:57–04:03:28 UTC); re-downloaded at 04:57:55–04:58:16 UTC by this run with identical hashes for the twelve guide files
- Contribution and reliability: The most complete map of the archive: what is proved, the proof map, the analytic endgame, the theta chain, Galois representations, the window bound, the named theorems, the archive's anatomy, building and checking, and the open frontier, each with reading-status markers and a list of what nobody has read. Its reports include a vacuity check (E10). Edited AI readings, labelled as such; use for navigation and cite findings as [Community]. The book does not reuse its text (outline, design decision 5).

<a id="g2"></a>
**G2. Readers' maps in the Comparator repository: issues #3 and #5.**

- URL: <https://github.com/leanprover-community/riemann-hypothesis/issues/3>; <https://github.com/leanprover-community/riemann-hypothesis/issues/5>
- Author: GitHub users keithadler (#3) and JoseClaudioSJr (#5).
- Used in Chapter 6, §6.4.5 (Remark 6.12): #5 states the cone status of `SlopesN`, `QuotientSlopeBoundsWith`,
  `MeanBoundOfLossBounds` and `PointwiseBoundVariant` and read $s$ as the rank-weighted average of $\mu(N_u) - h_u$.
  Re-fetched 2026-11-23 (CST) by `gh api`: body 63,424 B, sha256
  `82efbf2283b040750b78af9dc65263ad3be25b7b165851199136d0f61445cae3`, a different size from the 2026-11-21 retrieval
  above; GitHub reports `updated_at` 2026-11-22T19:16:06Z.
- Version / date: #3 opened 2026-11-20 21:58:55 UTC, corrected by its author at 22:08 and 23:30; #5 opened 2026-11-21 02:10:48 UTC, follow-ups to 04:09.
- Retrieved: 2026-11-21 05:01:44 UTC, HTTP 200 (gh api, authenticated read-only), 5,944 bytes, sha256 `5b39ee857bcfb74530837d22146603761148472fa922c15d3c757a06a4cb331a`; #5 2026-11-21 05:01:44 UTC, HTTP 200 (gh api, authenticated read-only), 46,695 bytes, sha256 `4d3d5783d700643e4dd43a48a9fb69b735a90a8b246371814af560819e097ecc`
- Contribution and reliability: Two independent call-path maps from `riemannHypothesis` down to the load-bearing inputs (#3 by declaration-level reachability, #5 tagged [code]/[reading], AI-assisted). #3 retracted its first headline figure (55% of declarations needed) for about 80% (a safe reduction of only about 9%) after a trimmed build failed; cite the corrected figures only. Both agree with G1 on the upper chain. Useful cross-checks, not verifications.

<a id="g3"></a>
**G3. Kim Morrison, plan for the "next stage" (Lean Zulip).**

- URL: <https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642386327>
- Author: Kim Morrison (Lean FRO).
- Version / date: Messages 642386327–642386494 (2026-11-21 01:07:22–01:07:57 UTC), 642418781 (04:41:53) and 642420104 (04:52:43).
- Retrieved: From V2
- Contribution and reliability: Declares the checking stage finished and sets out the next one: AI-assisted autoinformalization and written accounts; stating intermediate results in Lean (pointing to `lean-lang.org/eval` and to Prove2Me missions); condensing material into Mathlib and Tau Ceti; and, at 04:41–04:52, instructions for getting the repository with cached `.olean`s plus a to-do list (minimise imports, delete dead code, bump Lean and Mathlib, remove duplicates). The organising voice of the community effort; programmatic, not a result.

<a id="g4"></a>
**G4. Chris Birkbeck, AI-generated overview of the proof and Tau Ceti roadmaps (Lean Zulip).**

- URL: <https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642250042>
- Author: Chris Birkbeck (UEA), relaying a summary "fable has given me".
- Version / date: Messages 642250042 (15:18:32 UTC), 642254589 (15:31:46) and 642372756 (23:45:35).
- Retrieved: From V2
- Contribution and reliability: The first public sketch of the architecture (RH from non-vanishing for $\Re s>1/2$; that from bounds on Selmer/Ш-type groups in a family of fields; use of Galois representations attached to polarized cuspidal automorphic representations), widely relayed — by MathOverflow (C8) and TechCrunch (P12). An AI summary, labelled as such by its poster; later readings (G1, G2) refine it. Do not cite as a description of the proof without checking against the archive.

<a id="g5"></a>
**G5. tamnd, `riemann` ("A written proof, for people, of the Lean proof of the Riemann Hypothesis").**

- URL: <https://github.com/tamnd/riemann>; <https://riemann.tamnd.com>
- Author: GitHub user tamnd.
- Version / date: Repository created 2026-11-20 18:28:36 UTC; last push 2026-11-21 05:07:31 UTC.
- Retrieved: 2026-11-21 05:32:05 UTC, HTTP 200, 3,246 bytes, sha256 `18e1c3520cd2d63fd027d7a1b2faba67a6985afde83579997ecae205f5c15770`
- Contribution and reliability: An announced top-down written account (overview, chapters, steps, declarations) with learning paths. Its own README says: "The claim is not checked yet. We did not build the project yet". Not examined further by us; likely AI-generated at this scale and speed (our inference). Listed for completeness.

<a id="g6"></a>
**G6. Lean 4 Dev Editorial Team, "The Riemann Hypothesis: a claimed proof, delivered in Lean".**

- URL: <https://lean4.dev/proofs/riemann-hypothesis-claim>
- Author: Lean 4 Dev Editorial Team (unnamed).
- Version / date: Date-only metadata (2026-11-20).
- Retrieved: 2026-11-21 04:59:33 UTC, HTTP 200, 338,020 bytes, sha256 `622a8da758acb74e6a7cf1e3aa4adfcaeeccb6640640ced105f9e92bce37b158`
- Contribution and reliability: A clear explainer of the statement in Lean and of what was checked, and one of the few that places the 250,000-page figure correctly (A1, p. 2, fn. 2). Commercial learning site, anonymous, probably AI-assisted; no errors found in what we checked. Low–medium weight.

<a id="g7"></a>
**G7. Masullo manuscript search tool.**

- URL: <https://masullo-grh.vercel.app/>
- Author: Not named; "Powered by TopK".
- Version / date: Undated.
- Retrieved: 2026-11-21 04:59:36 UTC, HTTP 200, 5,595 bytes, sha256 `f9ba81db7bfc59bc736aa931c0ac1b69a6b21bb6f12c1df9af4947a03a144056`
- Contribution and reliability: A semantic-search front end for A4: type an idea, get pages. A finding aid only.

<a id="g8"></a>
**G8. Build guides and early repositories of the extracted code.**

- URL: <https://github.com/CocoSgt/riemann-hypothesis-lean>; <https://github.com/TomasOrtega/RH>
- Author: GitHub users CocoSgt and TomasOrtega.
- Version / date: TomasOrtega/RH created 2026-11-20 14:16:39 UTC (first commit "import extracted Lean project", 14:16:28); CocoSgt/riemann-hypothesis-lean created 14:59:14 UTC, last push 15:13:36 UTC.
- Retrieved: CocoSgt README 2026-11-21 05:23:47 UTC, HTTP 200, 8,726 bytes, sha256 `2c613919744434c3499c5f75c8019f5686673bc85e2487189f619ca76980cf89`; TomasOrtega README 2026-11-21 05:32:06 UTC, HTTP 200, 296 bytes, sha256 `3d0957ad7c8e8ac811779c2cef6f706fb70ec8d8b2a5db1750938b9bbeb67143`
- Contribution and reliability: Both repositories are mirrors of the archive (we link, never copy). TomasOrtega/RH is the earliest public repository of the extracted code we found (V4); CocoSgt's README gives step-by-step download, hash check (`9631b4f0…`) and build instructions, and asks reporters to include commit, toolchain and machine. Practical guides; no checking of their own.

<a id="g9"></a>
**G9. Video explainers.**

- URL: <https://www.youtube.com/watch?v=Lrle6EiXqfs>; <https://www.youtube.com/watch?v=ptivrqGvoV8>; <https://www.youtube.com/watch?v=sMZMpsHeFKc>; <https://www.youtube.com/watch?v=zlm1aajH6gY>
- Author: Dirac (@DiracExplained), Numberphile, Quanta Magazine.
- Version / date: Upload dates not available to us; titles via YouTube oEmbed.
- Retrieved: 2026-11-21 05:05:26 UTC, HTTP 200, 846 bytes, sha256 `9e3e0538eb71292bf58db6705cfbbe40b242d399e1fda4900f5d25cc7816b1f4`
- Contribution and reliability: Popular explainers of the two claims and of RH. Not watched by us; the auto-generated descriptions misspell names. Surveyed only.

<a id="g10"></a>
**G10. Manvir Jaswal, "The Riemann hypothesis for Dirichlet L-functions [after Levent Alpöge]" (`[Jaswal2026]`).**

- URL: <https://hexagonmath.org/pdf/2611.00799v1> (identifier `hexagon:2611.00799v1`; not an arXiv identifier).
- Author: Manvir Jaswal (Toronto), per the PDF title page and metadata.
- Version / date: Version 1, November 21, 2026; 54 pages.
- Retrieved: 2026-11-23 (CST) by curl, HTTP 200, 893,650 bytes, sha256 `ed3219310e356ef99dad8acb6a2a63ed92df18bd8a73f0dfef63ba5a4e8e57a7`.
- Contribution and reliability: A Bourbaki-style exposition with archive paths. Section 3, item (c), describes `QuotientSlopeBoundsWith` as a comparison of the slopes of the $N_\omega$ with the stage-zero slopes "shifted by the gains", and the following paragraph describes taking "the rank-weighted mean of the shifted slopes of the $N_\omega$". Cited in Chapter 6, §6.4.5 [Community]. Not reviewed beyond these passages.

## Errata and disputes (E)

<a id="e1"></a>
**E1. McCorvie et al., `ERRATA.md` of `mccorvie/riemann-masullo`.**

- URL: <https://github.com/mccorvie/riemann-masullo/blob/27567d5098ecaf57d44fed6b6bfa146ca54a68f3/ERRATA.md>
- Author: Ryan McCorvie (integrator), from reports by contributors and their agents.
- Version / date: File added 2026-11-20 20:22:11 UTC (commit `e61d5090`); last ERRATA commit `3641550c` (2026-11-21 04:39:42); read at HEAD `27567d50`.
- Retrieved: 2026-11-21 05:00:08 UTC, HTTP 200 (gh api, authenticated read-only), 57,398 bytes, sha256 `9b6e7f1e6343ea1a60048f6e8373886ddcc12a51ea42123e56a419be909a8469`
- Contribution and reliability: A running list with page numbers: at our copy 123 entries — 96 imprecise or wrongly justified, 18 false as stated, 7 placeholders or missing material, 2 reported from reading beyond what is formalized. The file says most entries were first reported by an AI agent and that none has been reviewed by a specialist. A progress indicator for the formalization, not a verdict on the draft.

<a id="e2"></a>
**E2. mccorvie/riemann-masullo issue #1169: the uniform bound on biorthogonal pairs after (10.3.1.18).**

- URL: <https://github.com/mccorvie/riemann-masullo/issues/1169>
- Author: Opened by yikerman; comments by grootstebozewolf, PeaBrane, leecrossley and others.
- Version / date: Opened 2026-11-20 23:35:48 UTC; comments to 2026-11-21 04:22:08 (edited 04:39).
- Retrieved: 2026-11-21 04:59:47 UTC, HTTP 200 (gh api, authenticated read-only), 6,323 bytes, sha256 `29294e8a6f04f2c9d7045e944482c487f041a1e2e092acb97a4beffd4c93c44a`
- Contribution and reliability: The best-documented technical objection: the draft needs a constant bounding $\|\eta\|\cdot\|\psi\|$ for biorthogonal pairs uniformly in the zero (p. 451, resting on Terminology 10.2.1.2(2), p. 444), and close pairs of zeros of ζ on the critical line make such a bound impossible. Comments add a Rocq file, a repair via finite-rank windows (E3), and a trace-class argument. Community work, partly AI-assisted; the counterexample is elementary and we reproduced it (E9). The Refine report (E6) had stated the same failure about two hours earlier.

<a id="e3"></a>
**E3. Yan Ru Pei, "Trace class without bounded biorthogonals: repairing a step in Masullo's spectral nuclearity theorem" (Zenodo).**

- URL: <https://doi.org/10.5281/zenodo.24409811>
- Author: Pei, Yan Ru (independent researcher; GitHub PeaBrane).
- Version / date: Version 1, record 24409812, created 2026-11-21 01:56:01 UTC; concept DOI 10.5281/zenodo.24409811.
- Retrieved: 2026-11-21 04:59:44 UTC, HTTP 200, 6,510 bytes, sha256 `dbabf22dc9aae9b256516c541989d0108417def60cc67d83428d939ffdb8fb07`
- Contribution and reliability: A 19-page AI-assisted note proposing a repair of the step in E2 on the critical line ($I=\{0\}$), crediting the counterexample to Yi Cao (issue #1169). It says the strip case is not repaired and that it does not bear on the main theorem. Self-published, not peer reviewed, and its abstract says the arguments have not been checked by human experts.

<a id="e4"></a>
**E4. mccorvie/riemann-masullo issue #587: Theorem 12.5.1.1 as printed, and its corrected form.**

- URL: <https://github.com/mccorvie/riemann-masullo/issues/587>
- Author: GitHub user AVBlom.
- Version / date: Opened 2026-11-20 22:06:36 UTC; no replies at 05:15 UTC.
- Retrieved: 2026-11-21 05:05:20 UTC, HTTP 200 (gh api, authenticated read-only), 6,739 bytes, sha256 `154d1a8fbdca773a406b5c1a32b77dfe873c4e26fd6e3dc9a2e7a7145b17cf79`
- Contribution and reliability: Claims, with numerical checks, that the trace formula as printed fails for $\mathbb Q(i)$ and $\mathbb Q(\sqrt{-3})$ by a normalising factor, and that once corrected it coincides with Weil's explicit formula (the draft's own B.4.4.7) — consistent with the claim reported on V3 at 19:42:57. If right, the main theorem carries no information beyond the classical explicit formula. One contributor, unreviewed; [Open].

<a id="e5"></a>
**E5. mccorvie/riemann-masullo issue #1358: shell cutoff in the proof of Theorem 11.3.2.1.**

- URL: <https://github.com/mccorvie/riemann-masullo/issues/1358>
- Author: GitHub user yikerman.
- Version / date: Opened 2026-11-21 00:07:23 UTC.
- Retrieved: 2026-11-21 05:05:20 UTC, HTTP 200 (gh api, authenticated read-only), 6,377 bytes, sha256 `d307ec3d8ef5095baac5e881e9fc89049820c05009d30a3379dabc9648513741`
- Contribution and reliability: Reports two steps on pp. 495–496 that must be replaced before they can feed Theorem 12.5.1.1. Unreviewed community report.

<a id="e6"></a>
**E6. Refine Technologies, Inc., "Report on The Music of the Primes".**

- URL: <https://github.com/Refine-Technologies-Inc/music-of-primes-report-by-refine>; <https://raw.githubusercontent.com/Refine-Technologies-Inc/music-of-primes-report-by-refine/main/report.pdf>
- Author: Refine Technologies, Inc. ("We used the Refine harness and all frontier models to prepare this report").
- Version / date: 8 pages; PDF `CreationDate` 2026-11-20 15:12:41 −06:00 (21:12:41 UTC); first commit `1aa155d494` 21:12:42 UTC, files renamed in `f4844e58ed` 21:20:43 UTC. Linked on V3 at 22:38:07 UTC.
- Retrieved: 2026-11-21 05:29:02 UTC, HTTP 200, 304,050 bytes, sha256 `13669bfc6a53d46da0df19ef1afc114dfdc0b93b7ac144979d450052411dcadc`
- Contribution and reliability: An AI-produced audit that concludes the draft "does not establish the claimed results": ten gaps or errors, including the two omitted central steps (Section 12.3; Theorem 13.3.1.2), the Chapter 11 prime-shell truncation that "collapses every prime shell to zero", and — earliest in writing among the sources we found — the failure of the individual biorthogonal bound at p. 451 because clustered zeros make individual norms unbounded (citing Bui–Conrey–Young). The repository also hosts a copy of the draft (we link the original, A4). A company report made with AI tools and not peer reviewed; detailed and page-referenced, so checkable.

<a id="e7"></a>
**E7. Early public error reports on the Masullo draft.**

- URL: <https://x.com/AcerFur/status/2123853069599547786>; <https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Formalising.20Masullo.27s.20proof.20of.20GRH/near/642318488>; <https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Formalising.20Masullo.27s.20proof.20of.20GRH/near/642362262>
- Author: @AcerFur (X); Tim Gehrunger and Brent Yee (Lean Zulip).
- Version / date: X post 2026-11-20 18:56:45 UTC (from the post id); Zulip messages 642318488 (19:32:09), 642321263 (19:42:57), 642362262 (22:42:18).
- Retrieved: 2026-11-21 05:22:49 UTC, HTTP 200, 3,207 bytes, sha256 `bb5032eb29b5f1dd49683beb00b661139a46c1bcd4f99c9d8f0a7437e44d2968`; Zulip messages from V3
- Contribution and reliability: The first public signals, all relaying AI readings: "ok GPT quickly finds some errors, but idk how irreparable it is" (18:56:45); an LLM-found counterexample to Theorem 12.5.1.1 (19:32:09) and the reduction to a classical formula (19:42:57); and Brent Yee's quotation, without naming its source, of the note "Error on page 444. He claims a Markushevich basis whose vectors are bounded away from zero necessarily has a bounded biorthogonal sequence. This is not true." (22:42:18). These dated the dispute; the substance is in E2, E4 and E6.

<a id="e8"></a>
**E8. Premature report of a completed paranoid Comparator run.**

- URL: <https://x.com/nasqret/status/2123858004542189855>
- Author: Bartosz Naskręcki (@nasqret).
- Version / date: 2026-11-20 19:16:22 UTC (post id); an earlier post, id 2123816210441936983 (16:30:17 UTC), had said "We don't yet have full confirmation from the paranoid-mode comparator test, but we are close".
- Retrieved: 2026-11-21 05:14:36 UTC, HTTP 200, 5,706 bytes, sha256 `6a7ac526c9b87b88f56871a12417c65bee277ee724c4fdc0ba41f46edb739a54`; post JSON also at 2026-11-21 05:23:59 UTC, HTTP 200, 5,706 bytes, sha256 `747729d5d3e9f9321ca619b90cb419165b84bbec82ff79be8c456dc5f20985e0`
- Contribution and reliability: States: "We have a full confirmation from Andrew Sutherland who first managed to finish the nanoda kernel run and comparator in paranoid mode." [Checked]: neither version of V1 (19:45 and 22:05 UTC) supports the second half — nanoda had accepted at 19:05:45, but the paranoid kernels and `lake comparator` were still "running". A widely shared (232k views at our fetch) overstatement; cite only as an example of how status was misreported.

<a id="e9"></a>
**E9. Our reproduction of the p. 451 gap (not in the repository).**

- URL: run `rheval-opportunity-11211046`, `work/masullo/NOTE-mbasis-gap.md` and `verify_mbasis.py` (outside the repository)
- Author: This project (run `rheval-opportunity-11211046`, 2026-11-21).
- Version / date: Note written 2026-11-21 about 03:38 UTC; computation `verify_mbasis.py` (CPU 25.2 s). An independent audit of that run was in progress at 05:45 UTC.
- Retrieved: Local files; not published
- Contribution and reliability: [Checked]: for $F=\mathbb Q$, $\chi=1$, the norm formula of Prop. 10.2.1.3 (p. 443) gives $\|\eta_t\|\cdot\|\psi_t\|\ge (J_s/Q_s(d))^{1/2}$ for two critical zeros at distance $d$, which is about $1/d$ for $s=4$; since zeros with $d\to0$ exist (Conrey 1989 plus zero counting), no uniform constant exists. A ball-arithmetic computation of Hardy's $Z$ finds sign changes isolating two zeros (nos. 6709 and 6710, about 0.0377 apart) in an interval of length 0.0497, which forces $\|\eta_t\|\,\|\psi_t\|\ge 20.4565$ for $s=4$. Priority belongs to others (E6, E2); our note had credited E2 and is corrected here. A same-project check, not yet independently audited.

<a id="e10"></a>
**E10. LUMI report, "Vacuity check of the load-bearing statements".**

- URL: <https://github.com/aapolipponen/rh-lean-check-lumi/blob/82d91dbbd04d71f2cb45c3f2898f421b91c1c9d7/docs/reports/vacuity-check.md>
- Author: AI agent (read-only review), in G1.
- Version / date: Committed 2026-11-20 22:40:20 UTC (`40e1ae43`).
- Retrieved: 2026-11-21 04:58:15 UTC, HTTP 200, 14,690 bytes, sha256 `4c50ec8cba3dfe9e8e874d49a089d6b00bda71b462b05f2128376409367e814b`
- Contribution and reliability: Addresses the worry that a load-bearing hypothesis might be vacuous or trivially satisfied: it finds the window hypothesis applied to window pairs the archive proves exist, the Ш bound not trivial by definition, and part of `Row0b` not vacuous, and names the density proof `pair_share` and `vwin_of_row` as the places most deserving scrutiny. An AI reading, not human-checked; good evidence that no public reviewer has found vacuity, not a proof of non-vacuity.

<a id="e11"></a>
**E11. Statement-fidelity and metaprogramming disputes about the Lean archive.**

- URL: <https://github.com/leanprover-community/riemann-hypothesis/issues/2>; <https://github.com/leanprover-community/riemann-hypothesis/issues/6>; <https://news.ycombinator.com/item?id=50576189>
- Author: GitHub users joni15 (#2; reply by Deicyde) and patunz (#6); Hacker News commenters.
- Version / date: #2 opened 2026-11-20 20:14:38 UTC; #6 opened 2026-11-21 02:33:46 UTC; HN parent comment 2026-11-20 15:31:47 UTC.
- Retrieved: #2 2026-11-21 05:01:44 UTC, HTTP 200 (gh api, authenticated read-only), 4,492 bytes, sha256 `0ad0767ef965ca2e08019c05052ebb8ccd8d09504d91151f20cdbdc46ff1327b`; HN 2026-11-21 05:10:28 UTC, HTTP 200, 192 bytes, sha256 `642746d086274444b4d365ed8ba6eb14124e554ad5c32fa16c751a0fade8ad9e`
- Contribution and reliability: Issue #2: a static audit finding every module inside `Main`'s import cone, no `sorry`/`axiom`/`native_decide`, but four home-made tactics and three `MVarId.assign` sites that bypass elaboration-time type checks (the kernel still checks the final terms); it led to the correction of V5's notes. Issue #6: `.olean` hashes depend on the build directory. On Hacker News, a reply (seen by us only in search-result snippets, not fetched) asserted that the archive might certify an LLM-written definition rather than the real statement; other commenters rebutted it in the same sub-thread, and the archive in fact proves Mathlib's own definition (Chapter 1). Record the first two as resolved observations and the third as a refuted claim.

<a id="e12"></a>
**E12. Criticism of the announcement itself.**

- URL: <https://www.nature.com/articles/d41586-026-03812-7>; <https://www.quantamagazine.org/updates/transformation/>; <https://siliconreckoner.substack.com/p/mathematics-as-gift-economy>
- Author: Andrew Granville (quoted in P1); Maksym Radziwiłł (quoted in P6); Michael Harris (C6).
- Version / date: 2026-11-20.
- Retrieved: See P1, P6, C6
- Contribution and reliability: Granville: "What he released is garbled", and the author should have prepared a clearer write-up; Radziwiłł: the object of mathematics is the question "why?" and "this doesn’t answer it at all"; Harris: "very little sense can be extracted from the sketch in Alpöge’s four-page announcement". These are disputes about readability and understanding, not about correctness of the formal proof.

<a id="e13"></a>
**E13. Factual errors in coverage, checked against the primary sources.**

- URL: see the Press section (P1–P38)
- Author: Compiled by us.
- Version / date: Checked 2026-11-21 04:50–05:35 UTC.
- Retrieved: Outlet copies listed under Press
- Contribution and reliability: [Checked] against A1, A4, A5: (1) the "250,000 pages" are the unposted informal text (A1, p. 2, fn. 2), but BBC English and Japanese (P15, P16) say the Lean proof is over 250,000 pages, and New Scientist's explainer (P8) calls the 250,000-page text the proof and Lean its "translation"; (2) BBC's headline spells "Reimann"; (3) BBC Japanese dates the message to Amodei to the 5th, whereas the note says "late Sunday night" and BBC English says Sunday (15 November); (4) TechCrunch calls Vakil president of the "American Mathematics Association" (P12); (5) Scientific American's 21:00 story quotes Buzzard's Xena essay of 12 November as "a blog post" in a way that reads as a comment on this claim, which it predates (P5); (6) Masullo is called a Stanford postdoc by several outlets, which neither A4 nor A7 confirms. Correct the record by citing the primary source, not the outlet.

<a id="e14"></a>
**E14. Nielsen's vacuity critique of the Alpöge archive.**

- URL: <https://philpapers.org/rec/NIEIOT-2> (versions: <https://philpapers.org/versions/NIEIOT-2>); discussion: <https://dev.to/frankchu/grh-proofs-geometry-is-fun-true-in-24-files-2n2b>; <https://carlostoledo.co/reports/alpoge-grh.html>; Harry Tong, <https://github.com/harrytong/rh-verification/blob/main/RH_critics_dependency_findings.md>
- Author: Jenny Lorraine Nielsen (Center for Topological Physics, Lawrence, Kansas); commentary by Frank Chu (DEV), Carlos Toledo; compiled-dependency audit by Harry Tong (`harrytong/rh-verification`, posted in the DEV comments 2026-11-22 20:42 UTC); Nielsen's own reply in the DEV comments (2026-11-22 11:20 UTC).
- Version / date: v1 2026-11-20 21:14 UTC to v16 2026-11-22 18:09 UTC (PhilArchive).
- Retrieved: PDF (17 pp., created 2026-11-22 18:08 UTC, corresponding to v16) supplied by Hongmin Li on 2026-11-23, sha256 `15ac01d0bc60a4e98f4d50c7ef1eaa675108c84738974bda0ab5225f6601b5a6` (local copy, not redistributed); PhilArchive pages themselves blocked (HTTP 403, Cloudflare); DEV article and comments via the dev.to API. Tong's findings retrieved 2026-11-23, HTTP 200, 15,663 bytes, sha256 `7b150a82471ec5e038ae3fa748434eff2c62b0d508ca19d1c1e8fa3f75ddd98e`. Code claims checked by us against the pinned archive (A2, sha256 `9631b4f0…7fc`).
- Contribution and reliability: [Checked] `anyGeometry : GeoP := fun _ _ _ => True` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean:19`), its use as `geoCl anyGeometry` in `nonempty_hyps_definite_side_of_closed_bound` and `EveryCharacterE.lean`, 24 files, and the `geoDegenerate`/`mdlJunk`/`algDegenerate` models in `Inhabited.lean`. [Checked] the four extraction lemmas occur only at their declarations. [Community] Tong's dependency-closure walk (not rerun by us). The paper's conclusion that the proof is invalid does not follow from these observations; see Chapter 16, §16.6. Not peer reviewed.

## Commentary (C)

<a id="c1"></a>
**C1. Terence Tao, "Unforced Euler singularity, unforced Navier-Stokes singularity, and the Generalized Riemann Hypothesis" (blog post and comments).**

- URL: <https://terrytao.wordpress.com/2026/11/20/unforced-euler-singularity-unforced-navier-stokes-singularity-and-the-generalized-riemann-hypothesis/>
- Author: Terence Tao (UCLA).
- Version / date: Published 2026-11-20 17:19:00 UTC, modified 19:13:39 UTC (the "UPDATE" on Zulip moderation); 31 comments at our copy.
- Retrieved: 2026-11-21 04:58:59 UTC, HTTP 200, 319,924 bytes, sha256 `adc622033b887bf59000424a6ac973f2e36e577d3b94b1049d47b1bea7503157`; Part I's copy of 04:05:41 UTC has sha256 `28d6e810…` (comments differ)
- Contribution and reliability: Lists three AI-assisted results "in decreasing order of how “digested”" they are; of the GRH claim: "Levent Alpöge, using an internal AI model, has generated an (enormous) Lean-only proof of the Generalized Riemann Hypothesis", points to V2 as "probably the best place to follow the efforts to verify the proof", and adds "I imagine the digestion process will take some time, though in this case at least we have a human author to communicate with to assist with this task." In a comment he notes the AI proof seems to use automorphic, algebraic and arithmetic-geometric inputs and, after an edit, places Masullo's manuscript "closer to Deninger’s strategy towards RH than Connes’". Expert, careful, explicitly preliminary.

<a id="c2"></a>
**C2. Kevin Buzzard, "…and the proof is checked in Lean" (Xena blog), and his moderation on V2.**

- URL: <https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/>; <https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Discussion.3A.20Alp.C3.B6ge.20Proves.20the.20Riemann.20Hypothesis/near/642306912>
- Author: Kevin Buzzard (Imperial College London).
- Version / date: Essay of 2026-11-12, eight days before the announcement (pinned in Part I, §5); Zulip messages 642305635 (18:39:29) and 642306912 (18:44:35).
- Retrieved: 2026-11-21 04:58:59 UTC, HTTP 200, 131,894 bytes, sha256 `1276c27358e0c092c9986df031ebc1dbb8b800b27980673d236eae0a09cd08cc`; Part I's copy of 04:23:04 UTC has sha256 `b404e77b…` (dynamic page)
- Contribution and reliability: The essay explains what "checked in Lean" does and does not mean, starting with comparing the Lean statement with the intended theorem; it predates and does not mention the claim, although press quoted it as if it did (E13). On the day, Buzzard kept V2 on Lean topics ("posts which are not about Lean are off-topic") and stated what was still missing: a successful `comparator` run, checking (a) that nothing redefines the symbols in the statement and (b), in paranoid mode, acceptance by several independent kernels. Authoritative on the Lean side.

<a id="c3"></a>
**C3. Scott Aaronson, "The stochastic parrots have apparently proved the Riemann Hypothesis" (Shtetl-Optimized).**

- URL: <https://scottaaronson.blog/?p=10344>
- Author: Scott Aaronson (UT Austin).
- Version / date: Published 2026-11-20 18:29:03 UTC; modified 22:20:32 UTC; 62 comments at our copy.
- Retrieved: 2026-11-21 05:13:17 UTC, HTTP 200, 97,548 bytes, sha256 `cb664f92e0a545e23ee6973a45b903e7d7d593933f29f2c70045ece8e80cef19`
- Contribution and reliability: A widely read reaction: "my bet is that the proof will stand", while "Mathematicians of course won’t be satisfied with 17 million lines of Lean." Opinion by a computer scientist; useful for the reception, not for the mathematics.

<a id="c4"></a>
**C4. Gil Kalai, "Fan Chang, Hong Liu, and Maio Liu Proved Chvátal’s 1972 conjecture" (Combinatorics and more), opening update.**

- URL: <https://gilkalai.wordpress.com/2026/11/20/fan-chang-hong-liu-and-maio-liu-proved-chvatals-1972-conjecture/>
- Author: Gil Kalai.
- Version / date: Posted 2026-11-20.
- Retrieved: 2026-11-21 05:13:20 UTC, HTTP 200, 318,636 bytes, sha256 `8ec3e04af47a0f32c3ffa70d5ec1177e4df0e46f7a121ed248a583f6a2875e27`
- Contribution and reliability: A one-line mention ("Levent Alpöge also announced a proof of the Riemann Hypothesis. Good day for Levent!"). Reception only.

<a id="c5"></a>
**C5. Simon Willison, link posts on the two announcements.**

- URL: <https://simonwillison.net/2026/Nov/20/levent-alpoge/>; <https://simonwillison.net/2026/Nov/20/ravi-vakil/>
- Author: Simon Willison.
- Version / date: Dated 2026-11-20; the page time ("7:21 pm") has no time zone.
- Retrieved: 2026-11-21 05:13:17 UTC, HTTP 200, 14,006 bytes, sha256 `4f67bb70d4030328e554d16348985d82156cc0a13c3281f39f5083b9ea437e70`; Vakil post 2026-11-21 04:59:37 UTC, HTTP 200, 13,023 bytes, sha256 `76be14d4206d5e9ce747eedd65c5fdeb45dbef098f526c8a36378b5597a74f5c`
- Contribution and reliability: Quotation posts without analysis; useful as an independent witness of the original wording of A5 ("bring Alessandro to Stanford for a year").

<a id="c6"></a>
**C6. Michael Harris, "Mathematics as gift economy" (Silicon Reckoner).**

- URL: <https://siliconreckoner.substack.com/p/mathematics-as-gift-economy>
- Author: Michael Harris (Columbia).
- Version / date: Published 2026-11-20 18:51:48 UTC.
- Retrieved: 2026-11-21 05:14:04 UTC, HTTP 200, 297,602 bytes, sha256 `bdc6e16971f308781c16a61e5457e6d7732e1eec6d3ede95c9d2f5a9246e538a`
- Contribution and reliability: A critical essay: Harris says his 2024 guess that a proof of RH might arrive as about a million pages of code was "of the right order of magnitude", and that "very little sense can be extracted from the sketch in Alpöge’s four-page announcement". Opinion by a number theorist; reception and critique.

<a id="c7"></a>
**C7. X posts that spread the news.**

- URL: <https://x.com/scottnarmstrong/status/2123773647919661288>; <https://x.com/kevinweil/status/2123798040339419484>; <https://x.com/thomasfbloom/status/2123800965677748665>; <https://x.com/nasqret/status/2123816210441936983>
- Author: Scott Armstrong; Kevin Weil; Thomas Bloom; Bartosz Naskręcki.
- Version / date: Times decoded from the post ids and matched against fxtwitter: 13:41:10, 15:18:05, 15:29:43 and 16:30:17 UTC on 2026-11-20.
- Retrieved: Armstrong 2026-11-21 05:03:49 UTC, HTTP 200, 2,235 bytes, sha256 `d6c7e0b34f97bc59015e2c09cb5d7449aff5e7e3b43e468ae9f6defbe81c3a08`; Weil 2026-11-21 05:14:37 UTC, HTTP 200, 4,407 bytes, sha256 `5d50ec15faad2a7366ca702f1e6f6494ae388c9226f281e9c2afe473b7fcb592`; Bloom 2026-11-21 05:14:59 UTC, HTTP 200, 2,751 bytes, sha256 `d58c42ed09fa4282bf36e5c816481b0943077d37d12b1472706d386edd86b806`; Naskręcki 2026-11-21 05:14:35 UTC, HTTP 200, 5,472 bytes, sha256 `4cb483c276a7b8b65a9b6e20b4f31500083663ec41fe43faf8a33baa879acc12`
- Contribution and reliability: Armstrong's screenshot of the note ("@__alpoge__ ftw") is the earliest public signal we found, 17 minutes before V2 opened; Quanta reports he posted it because Tristan Buckmaster had sent it to him (P17). Weil's post spread it to the AI audience; Bloom pointed readers to V2 ("Lean experts are currently investigating"); Naskręcki's 16:30 post correctly said the paranoid check was not done (compare E8). Timestamps reliable; content is reaction.

<a id="c8"></a>
**C8. MathOverflow and Mathematics Stack Exchange.**

- URL: <https://mathoverflow.net/questions/518033>; <https://mathoverflow.net/questions/518043>; <https://math.stackexchange.com/questions/5155823>
- Author: Sam Hopkins (518033, answers by Will Sawin, Timothy Chow and others); Will Jagy (518043); Ashwin Sivakumar (5155823).
- Version / date: 518033 asked 2026-11-20 15:42:16 UTC; 518043 asked 2026-11-21 00:39:02 UTC and closed 00:46:53 UTC.
- Retrieved: 518033 2026-11-21 05:01:06 UTC, HTTP 200, 2,353 bytes, sha256 `0f92282961ab54cf816190b0b669c343e6703c2724f816aa0a2ac5c8503bbe1f`; 518043 2026-11-21 04:59:37 UTC, HTTP 200, 2,284 bytes, sha256 `e7ebe7e78e4aca9513fee6f281ef35dace5f29570e7bec9bd78fac5b89860eba`; MSE 2026-11-21 05:01:07 UTC, HTTP 200, 830 bytes, sha256 `10fc7422ec8cf9b9b29dfda79ba8d3912133d4489111595496e4f918ca1a3681`
- Contribution and reliability: 518033, "How to 'human verify' enormous AI math output?", gathers expert views on understanding a proof nobody has read (Sawin on collaborative partial expositions; Chow relaying G4). 518043 pasted A5's original text and was closed as unsuitable within eight minutes. Expert discussion; Chow's answer is second-hand.

<a id="c9"></a>
**C9. Hacker News discussions.**

- URL: <https://news.ycombinator.com/item?id=50574968>; <https://news.ycombinator.com/item?id=50578358>; <https://news.ycombinator.com/item?id=50579568>; <https://news.ycombinator.com/item?id=50581084>; <https://news.ycombinator.com/item?id=50583982>
- Author: Submitters iamronaldo (A1), archon1410 (C1), jasondavies (A5), stratos123 (C3), _dain_ (an essay, "Re: Riemann").
- Version / date: 2026-11-20/21.
- Retrieved: HN Algolia API 2026-11-21 05:23:59 UTC, HTTP 200, 29,754 bytes, sha256 `47da9525ee54961102e34436ac1d9efb3ef3c8a85d958650f211e5df72ac2e30`; item pages: 2026-11-21 05:05:22 UTC, HTTP 200, 2,567 bytes, sha256 `50338f49311cc2abc884ab668131a3f8debf71a14936de4f8c3b70acac7cd452`
- Contribution and reliability: Large public discussions; the first thread (50574968) is the one Kelly Davis cited on V4. Anonymous comments; useful for reception and as a source of claims to check (E11), not as evidence.

<a id="c10"></a>
**C10. Blogs and accounts checked without a relevant post.**

- URL: <https://www.math.columbia.edu/~woit/wordpress/>; <https://mathstodon.xyz/@tao>
- Author: Peter Woit; Lance Fortnow and Bill Gasarch; Daniel Litt (Bluesky); Terence Tao (Mathstodon).
- Version / date: Checked 2026-11-21 05:00–05:14 UTC.
- Retrieved: 2026-11-21 05:13:18 UTC, HTTP 200, 146,164 bytes, sha256 `aed8cf91db00eb926dbacd75c869fa64ffd83d3d7b98396133b44e7e45fd3f91`; Mathstodon 2026-11-21 05:00:58 UTC, HTTP 200, 195,770 bytes, sha256 `665110db606e0897494fb7a49fe5628407044483b05956ba070a59087602acbf`
- Contribution and reliability: Negative results, recorded so that later readers know these were looked at: no post on the claims at our check (Tao's latest Mathstodon status was of 10 November). Searches not exhaustive.

## Press (P)

Ordered by first publication. Unless stated, outlets report the claims second-hand from A1, A5, V1 and V2; quotations of Alpöge in the press match A1 verbatim where we checked.

<a id="p1"></a>
**P1. Joseph Howlett, "Anthropic mathematician claims to prove Riemann hypothesis, most famous problem in all of math", *Scientific American*.**

- URL: <https://www.scientificamerican.com/article/anthropic-mathematician-claims-to-prove-riemann-hypothesis-most-famous-problem-in-all-of-math/>
- Author: Joseph Howlett (edited by Claire Cameron).
- Version / date: Published 2026-11-20 14:00 UTC; `dateModified` 23:26:31 UTC.
- Retrieved: 2026-11-21 04:57:37 UTC, HTTP 200, 146,746 bytes, sha256 `ee1ee085c8f3bc8b7c035e213da6c8befcec0ec6e9d76b9369e69dcf22b57795`
- Contribution and reliability: The first press report we found, timestamped two minutes after the first Zulip message. The later updates add Sutherland's comments ("This is indeed an historic moment"; he calls it "a human triumph") after his 16:43 compile, so the article as read is not the 14:00 text. Careful science journalism; cite with the version caveat.

<a id="p2"></a>
**P2. Matthew Sparkes, "Anthropic mathematician claims AI-assisted proof of the Riemann hypothesis", *New Scientist*.**

- URL: <https://www.newscientist.com/article/2600134-anthropic-mathematician-claims-ai-assisted-proof-of-the-riemann-hypothesis/>
- Author: Matthew Sparkes.
- Version / date: Published 2026-11-20 15:20:01 UTC; modified 16:39:22 UTC.
- Retrieved: 2026-11-21 05:08:28 UTC (browser); curl got HTTP 406 at 05:02:07Z, no byte hash
- Contribution and reliability: Early report with Buzzard's reaction, "Let’s see if it compiles first", and James McKee's "There are numerous results that are conditional on the generalised Riemann hypothesis, and now those are theorems!". Read in a browser (curl refused).

<a id="p3"></a>
**P3. Robert Hart, "Anthropic mathematician claims to have solved prestigious Millennium Prize problem with Claude", *The Verge*.**

- URL: <https://www.theverge.com/ai-artificial-intelligence/1010051/anthropic-riemann-hypothesis-millennium-prize-problem>
- Author: Robert Hart (JSON-LD also lists Emma Roth).
- Version / date: Published 2026-11-20 16:34:13 UTC.
- Retrieved: 2026-11-21 05:02:16 UTC, HTTP 200, 446,993 bytes, sha256 `81d97a58f3b317ab59adbe83745c32839c0cbfc6ce560632dc26978877d1aa49`
- Contribution and reliability: Early tech-press report: notes Anthropic had not commented, quotes Anthropic's August statement (A6) and explains the Clay prize rules. Second-hand; minor spelling errors.

<a id="p4"></a>
**P4. Joseph Howlett, "Dueling claims of Riemann hypothesis proofs emerge", *Scientific American*.**

- URL: <https://www.scientificamerican.com/article/dueling-claims-of-riemann-hypothesis-proofs-emerge/>
- Author: Joseph Howlett (edited by Lee Billings).
- Version / date: Published 2026-11-20 20:40 UTC; modified 21:32:45 UTC.
- Retrieved: 2026-11-21 04:57:38 UTC, HTTP 200, 136,175 bytes, sha256 `a059f86dbe7db91b7640465f244d044b4fefbee462d8573bf88514c73a66c654`
- Contribution and reliability: The only source with Brian Conrad's own words on the Masullo draft: "To judge the success of the method requires the paper to reach a stage of more final revision" and "It’s undergoing major revision." Primary for Conrad's view as quoted.

<a id="p5"></a>
**P5. Clara Moskowitz, "The AI Riemann hypothesis proof is almost certainly true, independent mathematicians attest", *Scientific American*.**

- URL: <https://www.scientificamerican.com/article/the-ai-riemann-hypothesis-proof-is-almost-certainly-true-independent-mathematicians-attest/>
- Author: Clara Moskowitz (edited by Lee Billings).
- Version / date: Published 2026-11-20 21:00 UTC; modified 21:47:41 UTC (pinned in Part I, §5).
- Retrieved: 2026-11-21 04:57:39 UTC, HTTP 200, 137,656 bytes, sha256 `f51e63f20b44981373271181cfb46554ee66668612e1af3f972af9dbf22faac4`
- Contribution and reliability: Quotes Sutherland ("Honestly the chance that anything is fishy here is approximately zero"; the proof "has been compiled and independently rechecked by the Lean kernel with only the three standard axioms") and Buzzard's Zulip line that a successful comparator run was still awaited. Calls the 12 November Xena essay a "blog post" on this claim (E13). Good on status as of 21:00.

<a id="p6"></a>
**P6. Lee Billings, "What the Riemann hypothesis proof really means about AI and the future", *Scientific American*.**

- URL: <https://www.scientificamerican.com/article/what-the-riemann-hypothesis-proof-really-means-about-ai-and-the-future/>
- Author: Lee Billings (edited by Clara Moskowitz).
- Version / date: Published 2026-11-20 18:10 UTC; modified 18:38:14 UTC.
- Retrieved: 2026-11-21 04:57:39 UTC, HTTP 200, 144,081 bytes, sha256 `164781bcbcd05084dab05adf29d56107958b11cb4112bbaf26e10ba17a16dd63`
- Contribution and reliability: Explainer on consequences (no threat to RSA; significance as evidence of AI capability). Does not note that the Lean statement covers Dirichlet L-functions only. Analysis, not reporting.

<a id="p7"></a>
**P7. AFP (Alex Pigman with Thomas Urbain), "Anthropic researcher says Claude solved math's greatest riddle", via France 24.**

- URL: <https://www.france24.com/en/live-news/20261120-anthropic-researcher-says-claude-solved-math-s-greatest-riddle-1>; earliest syndicated dispatch <https://today.rtl.lu/news/world/anthropic-researcher-says-claude-solved-maths-greatest-riddle-376623520>
- Author: Agence France-Presse.
- Version / date: Earliest AFP version seen: RTL Today, 2026-11-20 17:25:53 UTC (short, no expert quotes; retrieved 2026-11-21 05:10:20 UTC, HTTP 200, 388,224 bytes, sha256 `6f99d9a5fa0d88a3766ce55ce34d39675e109bf76c3d8a0282f6873b40aeffea`). France 24 version published 18:34:17 UTC, modified 22:10:30 UTC (adds Conrey and Vakil).
- Retrieved: France 24 page read in a rendering browser at 2026-11-21 05:09:28 UTC (curl got HTTP 403 at 04:57:41 UTC), no byte hash
- Contribution and reliability: Wire story carried worldwide (copies under S1). Its expanded version quotes Brian Conrey: "It's a monumental moment in human history. It's really the biggest thing I think that's ever happened in mathematics", while reporting that he had seen only the remarks on Alpöge's site and had asked for a manuscript. Reports Vakil's announcement and that neither Vakil nor Masullo had responded. Read in a browser (curl got HTTP 403); copies on phys.org and Yahoo have byte hashes (S1).

<a id="p8"></a>
**P8. Karmela Padavic-Callaghan and Matthew Sparkes, "What is the Riemann hypothesis and why is its solution so monumental?", *New Scientist*.**

- URL: <https://www.newscientist.com/article/2600226-what-is-the-riemann-hypothesis-and-why-is-its-solution-so-monumental/>
- Author: Karmela Padavic-Callaghan and Matthew Sparkes.
- Version / date: 2026-11-20 (browser read).
- Retrieved: 2026-11-21 05:08:34 UTC (browser); curl HTTP 406, no byte hash
- Contribution and reliability: Explainer. Error: says Alpöge wrote that his proof "is over 250,000 pages long" and that "its translation into the language of the proof-checking software Lean is 17,000,000 lines long" — the reverse of A1, where Lean is the only proof released and the 250,000+ pages are an unposted informal text (E13).

<a id="p9"></a>
**P9. Hallie Golden (AP), "Anthropic worker claims to have solved a Holy Grail of math problems with the help of AI", via *The Independent*.**

- URL: <https://www.the-independent.com/news/claude-anthropic-san-francisco-rutgers-university-wall-street-b3089058.html>
- Author: Hallie Golden (Associated Press).
- Version / date: AP original 2026-11-20 (apnews.com not readable to us); The Independent's copy published 2026-11-21 04:32:55 UTC.
- Retrieved: 2026-11-21 05:02:12 UTC, HTTP 200, 238,039 bytes, sha256 `348a91c801af67e45c3b81dca539216b0392f9ba5362d7637f24a31d8b1837dc`
- Contribution and reliability: Adds the Clay Mathematics Institute's response: its president Martin Bridson calls it "an announcement of historic significance" and warns that "the journey from today’s announcement to a place of real understanding will be long and difficult"; quotes Alex Kontorovich ("Navier-Stokes fell and now the Riemann Hypothesis"). Wire copy; reliable for quotations.

<a id="p10"></a>
**P10. Mark Wilson, "Claude helps Anthropic mathematician solve a 167-year-old…", *TechRadar*.**

- URL: <https://www.techradar.com/ai-platforms-assistants/claude/claude-helps-anthropic-mathematician-solve-a-167-year-old-math-problem-riemann-hypothesis-potentially-proven-after-the-ai-flew-danced-and-sparkled-in-breakthrough>
- Author: Mark Wilson.
- Version / date: Published 2026-11-20 18:42:11 UTC.
- Retrieved: 2026-11-21 05:02:14 UTC, HTTP 200, 1,902,828 bytes, sha256 `4879fe85f987de6bf868c55c1fd0d8aa8fb081280fac6a8d7717ee7d8742ab72`
- Contribution and reliability: Consumer-tech rewrite of A1; correct on the 250,000-page draft and on Lean being the only release; errs on Anthropic's listing figures. Low weight.

<a id="p11"></a>
**P11. Express Global Desk, report on the claim, *The Indian Express*.**

- URL: <https://indianexpress.com/article/world/us-news/anthropic-claude-ai-riemann-hypothesis-proof-claim-10971928/>
- Author: Express Global Desk.
- Version / date: Published 2026-11-20 19:15:38 UTC.
- Retrieved: 2026-11-21 05:02:13 UTC, HTTP 200, 719,742 bytes, sha256 `b1c80a401e0119055abef9ae454c2e44c6c4ff3f0e52dae8a373a44dd3f02cf8`
- Contribution and reliability: Aggregated from Scientific American and OfficeChai; reasonable paraphrase of the method. Low weight.

<a id="p12"></a>
**P12. Tim Fernholz, "AI claimed a solution to the 167-year-old Riemann hypothesis — and a human did, too", *TechCrunch*.**

- URL: <https://techcrunch.com/2026/11/20/ai-claimed-a-solution-to-the-167-year-old-riemann-hypothesis-and-a-human-did-too/>
- Author: Tim Fernholz.
- Version / date: Published 2026-11-20 19:32:08 UTC; modified 22:51:18 UTC ("updated to include that" independent sources had checked the Lean code).
- Retrieved: 2026-11-21 04:57:40 UTC, HTTP 200, 237,868 bytes, sha256 `c320a0e64b6878ccd2185d40e2ec8f90e2c99f5ae90bbf4050220bcf3b640bf6`
- Contribution and reliability: An early piece covering both claims (AFP had mentioned Vakil's announcement at 18:34, P7); reproduces a Zulip remark by Chris Birkbeck on Galois representations (G4) and Masullo's acknowledgement line "we are still here. We are very much alive. We are not going anywhere." (A4, p. 6). Errors: calls Vakil president of the "American Mathematics Association" (it is the American Mathematical Society) and Masullo a "Stanford postdoc" (unconfirmed; E13).

<a id="p13"></a>
**P13. Truman Dickerson, "Anthropic mathematician says he used AI to solve Riemann hypothesis", *Business Insider*.**

- URL: <https://www.businessinsider.com/reimann-hypothesis-anthropic-claude-solved-biggest-problem-in-math-2026-11>
- Author: Truman Dickerson.
- Version / date: Published 2026-11-20 19:34:11 UTC.
- Retrieved: 2026-11-21 05:02:11 UTC, HTTP 200, 429,810 bytes, sha256 `657840773e1e852861772cd4d0556352392d00b49fd184a9807f12f026234f2f`
- Contribution and reliability: Quotes Steven Strogatz: "If it holds up, it's an extremely big deal" and "So it's fair to say that the claimed proof has not yet been independently verified". General-audience; the URL misspells Riemann.

<a id="p14"></a>
**P14. Anna Loren, report on the claim, *The Independent* (own story).**

- URL: <https://www.independent.co.uk/tech/riemann-hypothesis-solved-levent-alpoge-b3088927.html>
- Author: Anna Loren.
- Version / date: Published 2026-11-20 18:42:01 UTC.
- Retrieved: 2026-11-21 05:12:15 UTC, HTTP 200, 268,450 bytes, sha256 `559acde2de33d8aaddfd225793bce4ac0962668c826cae4502d27c2c3bdd7958`
- Contribution and reliability: Rewrite of A1 quotes with biographical colour. Low weight.

<a id="p15"></a>
**P15. Kali Hays, "Anthropic may have solved major maths problem Reimann hypothesis" [sic], *BBC News*.**

- URL: <https://www.bbc.com/news/articles/c6pqr2g7w059o>
- Author: Kali Hays (technology reporter).
- Version / date: Published 2026-11-20 23:08:57 UTC.
- Retrieved: 2026-11-21 04:57:40 UTC, HTTP 200, 243,335 bytes, sha256 `3e0cb47fbc0a574a3ea937026645d5e63b0451b95ddcbba01d2b9b6b2bd97322`
- Contribution and reliability: Mainstream general-news report: places the claim in the context of Anthropic's listing and OpenAI's mathematical announcements, says Alpöge messaged Dario Amodei on Sunday, quotes A1 ("The precise timing is horrible"; "There is an obvious cynical view, to do with the timing, but it is false") and C1. Errors: "Reimann" in the headline, "Terrance Tao", and a 250,000-page Lean proof (E13). The page differs between requests.

<a id="p16"></a>
**P16. BBC News Japan, Japanese version of P15.**

- URL: <https://www.bbc.com/japanese/articles/cwlyl6ymz841o>
- Author: カリ・ヘイズ (Kali Hays), translated by BBC News Japan.
- Version / date: Published 2026-11-21 03:52:23 UTC.
- Retrieved: 2026-11-21 04:57:41 UTC, HTTP 200, 282,159 bytes, sha256 `4ef92e38cd3b29a70b6e45eb33d00806cc95cd5d34ce6c2b97539f36cbd53011`
- Contribution and reliability: Translation; carries P15's errors and adds two: the message to Amodei is dated to the 5th (the note says "late Sunday night", 15 November), and a typo (照明 for 証明). Main Japanese mainstream source.

<a id="p17"></a>
**P17. Konstantin Kakaes, "Transformation" (Quanta Magazine live updates): "As mathematicians race to verify AI Riemann proof, a human…".**

- URL: <https://www.quantamagazine.org/updates/transformation/>
- Author: Konstantin Kakaes.
- Version / date: Items dated 2026-11-20 on the page (no machine-readable time); Quanta's X post linking it, 19:17:14 UTC.
- Retrieved: 2026-11-21 05:02:08 UTC, HTTP 200, 197,031 bytes, sha256 `dac1ce074077dbc3780ce1fc52eef1f8731b819dc642351383075362df27bd09`
- Contribution and reliability: Reported detail found nowhere else: Armstrong posted the screenshot because Buckmaster had sent it to him (phone call); Sutherland finished compiling "shortly before noon" Eastern (consistent with V1's 16:43:21 UTC); Simon DeDeo: "I’d be very surprised if there were any secret tricks"; Radziwiłł on "why?"; Alpöge obtained the result on Monday 16 November. It also writes, without a source, that an earlier RH proof Masullo worked on "did not, in the end, hold up" — not checked by us [Open]. Strong science journalism; the live page changes.

<a id="p18"></a>
**P18. Davide Castelvecchi, "Mathematician says he and AI solved Riemann hypothesis — the field’s biggest outstanding challenge", *Nature* (news).**

- URL: <https://www.nature.com/articles/d41586-026-03812-7>
- Author: Davide Castelvecchi.
- Version / date: Dated 20 November 2026 (no time exposed).
- Retrieved: 2026-11-21 04:57:35 UTC, HTTP 200, 233,821 bytes, sha256 `4f1c7c5e97af3ebb2d8659e0ed0588a71f52df8db89ba5d32426207233a29ceb`
- Contribution and reliability: Quotes James Maynard ("If this fully checks out, it is clearly a historic milestone in mathematics") and Andrew Granville ("What he released is garbled"; Alpöge should have prepared a clearer write-up before announcing, which came "just days after" Anthropic's IPO). The leading science-news source for expert reactions.

<a id="p19"></a>
**P19. Ariel Zilber, report on the claim, *New York Post*.**

- URL: <https://nypost.com/2026/11/20/business/anthropic-researcher-claims-claude-cracked-legendary-1m-math-problem-and-left-him-struggling-to-keep-up/>
- Author: Ariel Zilber.
- Version / date: Published 2026-11-20 21:06:45 UTC.
- Retrieved: 2026-11-21 05:12:14 UTC, HTTP 200, 746,503 bytes, sha256 `7a767c81486a1cb2800ede6d7c056b023f4a2718af1bdd72fe009ee6921c040d`
- Contribution and reliability: Tabloid rewrite of A1 with biography; correct on the 250,000-page draft. Low weight.

<a id="p20"></a>
**P20. Karmela Padavic-Callaghan and Matthew Sparkes, "Mathematicians are amazed by ‘holy grail’ proof of Riemann hypothesis", *New Scientist*.**

- URL: <https://www.newscientist.com/article/2600235-mathematicians-are-amazed-by-holy-grail-proof-of-riemann-hypothesis/>
- Author: Karmela Padavic-Callaghan and Matthew Sparkes.
- Version / date: Published 2026-11-20 22:33:06 UTC; modified 2026-11-21 02:26:43 UTC.
- Retrieved: 2026-11-21 05:08:38 UTC (browser); curl HTTP 406, no byte hash
- Contribution and reliability: Reaction round-up; paywalled, only the opening was readable to us. Existence and framing only.

<a id="p21"></a>
**P21. Truman Dickerson, "Race to prove Riemann Hypothesis just became a human-versus-AI showdown", *Business Insider*.**

- URL: <https://www.businessinsider.com/riemann-hypothesis-math-human-ai-dueling-solution-alpoge-masullo-2026-11>
- Author: Truman Dickerson.
- Version / date: Published 2026-11-20 23:33:11 UTC.
- Retrieved: 2026-11-21 05:02:12 UTC, HTTP 200, 430,472 bytes, sha256 `0dd7aa983dd56cb36601af7c0ed3e45a81a33605a39dc3f83caa18c5e7316c6f`
- Contribution and reliability: Follow-up on the Masullo claim with Strogatz ("The plot thickens!", from X) and Sergei Gukov; reports that Masullo, Conrad and Alpöge did not respond. Second-hand.

<a id="p22"></a>
**P22. Bloomberg, "Anthropic researcher claims AI helped solve 150-year-old Riemann hypothesis", via *Business Standard* (also Bloomberg Law).**

- URL: <https://www.business-standard.com/technology/tech-news/anthropic-researcher-claims-ai-helped-solve-150-year-old-riemann-hypothesis-126112100179_1.html>
- Author: Bloomberg News (the Bloomberg Law copy credits Elena Eisenstadt).
- Version / date: Bloomberg Law copy 2026-11-21 00:17:14 UTC; Business Standard copy 04:10:18 UTC.
- Retrieved: 2026-11-21 05:12:01 UTC, HTTP 200, 218,951 bytes, sha256 `a85f8916c7653a44aaaf8fdce1fcd5ede6a23d2f20e0ed6ea62bacd25d2952cf`
- Contribution and reliability: Adds that Sutherland said he had verified the code on his own computer and had seen at least three other verifications on multiple systems by professional mathematicians, and that Anthropic declined to comment. Business wire; quotations of A1 accurate.

<a id="p23"></a>
**P23. Keiichi Nakane (中根圭一), report from Washington, *Yomiuri Shimbun*.**

- URL: <https://www.yomiuri.co.jp/science/20261121-GYT1T00089/>
- Author: Keiichi Nakane.
- Version / date: Published 2026-11-20 22:13 UTC (07:13 JST on 21 November).
- Retrieved: 2026-11-21 05:12:08 UTC, HTTP 200, 217,269 bytes, sha256 `3255b821cba7428f33a2ebfa406d0126db4c3aa7303dd69f99fcea4a7261c4f5`
- Contribution and reliability: Main Japanese newspaper report by its own correspondent. Second-hand; no errors spotted in the visible part.

<a id="p24"></a>
**P24. Ken Narabe and Tetsuya Ishikura (奈良部健, 石倉徹也), report, *Asahi Shimbun*.**

- URL: <https://www.asahi.com/articles/ASVCP10Z2VCPUHBI00GM.html>
- Author: Per search snippet.
- Version / date: Published 2026-11-21 03:23:02 UTC.
- Retrieved: 2026-11-21 05:12:09 UTC, HTTP 200, 216,187 bytes, sha256 `5695b4c7df7b9295dadde09117dfeb62473f9da834b500854dbc8b90d90c0213`
- Contribution and reliability: Paywalled after the lead; paraphrases A1 correctly. Existence and lead only.

<a id="p25"></a>
**P25. Nikkei Science (日経サイエンス), news item.**

- URL: <https://nk-science.nikkei.com/atcl/nsc/00058/112100036/>
- Author: No personal byline.
- Version / date: Published 2026-11-21 01:00 UTC.
- Retrieved: 2026-11-21 05:12:12 UTC, HTTP 200, 39,516 bytes, sha256 `b31ae6dcd02c2a19bf113095337144dfdad5b7e245a94d91022f0a3ea09a75ac`
- Contribution and reliability: Short Japanese science-magazine item. Second-hand.

<a id="p26"></a>
**P26. José Luis Ávila, report, *El País* (US edition).**

- URL: <https://elpais.com/us/2026-11-21/un-matematico-de-anthropic-asegura-haber-resuelto-la-hipotesis-de-riemann-el-mayor-enigma-de-las-matematicas-con-ayuda-de-la-ia.html>
- Author: José Luis Ávila.
- Version / date: Published 2026-11-21 01:12:10 UTC.
- Retrieved: 2026-11-21 05:12:05 UTC, HTTP 200, 338,439 bytes, sha256 `96d066b4007e3fd4e07454bc00c947318968bd0f8f4f66789548db710206f338`
- Contribution and reliability: Spanish-language report drawing on Quanta; attributes Maynard's "historic milestone" line to "IBM Think", which we could not check (we saw the line in P18).

<a id="p27"></a>
**P27. Tristan Vey, report, *Le Figaro*.**

- URL: <https://www.lefigaro.fr/sciences/l-hypothese-de-riemann-plus-celebre-probleme-de-mathematiques-au-monde-aurait-ete-resolue-par-claude-l-ia-d-anthropic-20261120>
- Author: Tristan Vey.
- Version / date: Published 2026-11-20 17:10:46 UTC.
- Retrieved: 2026-11-21 05:12:06 UTC, HTTP 200, 587,485 bytes, sha256 `bec3c7975697a62d95fefe037903314d5baf52e62df2872c5f3d70c76a15fd69`
- Contribution and reliability: Main French report found. Second-hand.

<a id="p28"></a>
**P28. *Der Spiegel*, report on the claim.**

- URL: <https://www.spiegel.de/wissenschaft/riemann-vermutung-mathematiker-behauptet-mit-ki-einen-beweis-fuer-den-heiligen-gral-der-mathematik-gefunden-zu-haben-a-cb24fb59-9f4e-44f7-a7cc-c3c19418721b>
- Author: No personal byline in the metadata.
- Version / date: Published 2026-11-20 17:30 UTC.
- Retrieved: 2026-11-21 05:12:04 UTC, HTTP 200, 596,139 bytes, sha256 `5033a65cf7927ed112357d77deea2cf369ebbae7e81522fee303665c2894dbf4`
- Contribution and reliability: Main German report; stresses that Alpöge does not yet fully understand the proof himself (cf. A1, p. 2). Second-hand.

<a id="p29"></a>
**P29. Nan Boyi (南博一), report, *The Paper* (澎湃新闻).**

- URL: <https://www.thepaper.cn/newsDetail_forward_34527053>
- Author: Nan Boyi.
- Version / date: Published 2026-11-21 02:35:46 UTC.
- Retrieved: 2026-11-21 05:12:13 UTC, HTTP 200, 22,139 bytes, sha256 `343ec6e4f2302a6ae92f289b14502267e5d46bda54fd85c5785032de6e74b406`
- Contribution and reliability: Mainland Chinese mainstream report. Second-hand summary.

<a id="p30"></a>
**P30. Jiang Yu (江宇), round-up, *Zhidx* (智东西; also on 36Kr).**

- URL: <https://zhidx.com/p/612978.html>
- Author: Jiang Yu.
- Version / date: Published 2026-11-20 23:12:50 UTC.
- Retrieved: 2026-11-21 05:12:14 UTC, HTTP 200, 54,936 bytes, sha256 `45304f083d1c5e437539b6e7fa5bd6eff48d2d13641d7f28cee73aeaa0f9b060`
- Contribution and reliability: Chinese round-up of reactions; it reproduces a screenshot only "suspected" (疑似) to be from Deng Yu. We do not attribute that statement to anyone.

<a id="p31"></a>
**P31. QbitAI (量子位), report.**

- URL: <https://www.qbitai.com/2026/11/511727.html>
- Author: QbitAI editorial.
- Version / date: 2026-11-20/21 (no machine-readable time).
- Retrieved: 2026-11-21 05:12:13 UTC, HTTP 200, 57,983 bytes, sha256 `190f9e07d62f5087c7fd519173e06be8059011b83549e9249221b72f15017c67`
- Contribution and reliability: Chinese AI-industry summary of A1 and the archive. Second-hand.

<a id="p32"></a>
**P32. Liu Jia (刘佳), report, *Yicai* (第一财经).**

- URL: <https://www.yicai.com/news/103448932.html>
- Author: Per search snippet.
- Version / date: Published 2026-11-21 00:25:49 UTC.
- Retrieved: 2026-11-21 05:12:13 UTC, HTTP 200, 26,545 bytes, sha256 `eb376b5f877959cd9ff2dca742b1592e50000588af1eb3b56052d92a45022cc8`
- Contribution and reliability: Chinese financial-press report; recalls an earlier bet on AI and RH. Second-hand.

**Coverage that exists but that we could not read.** Each is known from search results or from a blocked page; none is cited as evidence.

<a id="p33"></a>
- **P33.** *Science* (AAAS), "AI may have solved math’s greatest mystery. Can humans understand the answer?". <https://www.science.org/content/article/ai-may-have-solved-math-s-greatest-mystery-can-humans-understand-answer>. Retrieved 2026-11-21 05:02:11 UTC (curl) and 2026-11-21 05:09:05 UTC (browser), HTTP 403 to curl; Cloudflare challenge in browser; web_extract unavailable (search-only backend), 5,997 bytes, sha256 `30f532cb2d5b0a23000fbe80eda275492dad26f146abd101ae1a1216b2119bf7` (of the error or challenge page we received, not of the article).
<a id="p34"></a>
- **P34.** *The New York Times*, Kenneth Chang and Siobhan Roberts, "Anthropic Mathematician Claims to Have Solved Math’s Most Famous Problem" (known from syndicated copies and Kyodo). <https://www.dailygazette.com/nyt-feed/anthropic-mathematician-claims-to-have-solved-maths-most-famous-problem/article_44676e77-ae1c-5bdb-91a0-5325ede658a8.html>; <https://www.deccanherald.com/technology/anthropic-mathematician-claims-to-have-solved-maths-most-famous-problem-riemann-hypothesis-4226294>. Retrieved 2026-11-21 05:12:03 UTC, HTTP 429 from dailygazette.com; text not read, 66 bytes, sha256 `4d68560587b8c4aa50b4e432c88f96c8c411f4b7d4402b2d17fc34154e707261` (of the error or challenge page we received, not of the article).
<a id="p35"></a>
- **P35.** *The Wall Street Journal*, "Anthropic Mathematician Says AI Has Solved the Most Famous Problem in Math". <https://www.wsj.com/tech/ai/anthropic-mathematician-says-claude-has-solved-the-most-famous-problem-in-math-9361920b>. Retrieved 2026-11-21 05:12:00 UTC, HTTP 401, 767 bytes, sha256 `b6673fc66e18fa11bd7ea3d669e30499615a80bfd32a3e3510708b9389490515` (of the error or challenge page we received, not of the article).
<a id="p36"></a>
- **P36.** *Financial Times*, "Anthropic staffer claims solution to mathematics’ Riemann hypothesis". <https://www.ft.com/content/fa8eeb49-2cb4-4286-8131-03db15383d87>. Retrieved 2026-11-21 05:12:00 UTC, HTTP 403, 270,573 bytes, sha256 `3b525cb840e2357ce9768be4a78f81efc82e02cb91e8b62ff14f230fded58395` (of the error or challenge page we received, not of the article).
<a id="p37"></a>
- **P37.** *Quartz*, report on the claim. <https://qz.com/anthropic-alpoge-claude-riemann-hypothesis-proof-112026>. Retrieved 2026-11-21 05:02:15 UTC (curl) and 2026-11-21 05:09:13 UTC (browser), HTTP 403 to curl; Cloudflare challenge in browser, 5,807 bytes, sha256 `3e88594dde57835cdc93883f514576059144a90f4e30aebe5e769490df2ad1e0` (of the error or challenge page we received, not of the article).
<a id="p38"></a>
- **P38.** Associated Press original at apnews.com (content read via P9). <https://apnews.com/article/anthropic-claude-math-solution-ai-4fe8b69a891f160f9e7f0c85af8c55c8>. Retrieved 2026-11-21 04:57:42 UTC (curl) and 2026-11-21 05:07:57 UTC (browser), HTTP 403 to curl; Cloudflare challenge in browser (not bypassed), 5,911 bytes, sha256 `08806ebb4554eda4ca3ca8614f0910c7bbd24db365901d44cb48f781ce5fcf4e` (of the error or challenge page we received, not of the article).

## Surveyed only (S)

Seen and logged, not relied on. Listed so that readers can judge coverage and so that errors repeated from these sites can be traced.

<a id="s1"></a>
- **S1.** AFP copies: phys.org. <https://phys.org/news/2026-11-anthropic-claude-math-greatest-riddle.html>. Retrieved 2026-11-21 05:10:09 UTC, HTTP 403, 17,730 bytes, sha256 `1724bbea90ac1af05cc26e52c149ffb5155d7267dbaa2db11e6c22f9e823c8aa` (of the error or challenge page we received, not of the article).
<a id="s2"></a>
- **S2.** AFP copy: Yahoo Tech. <https://tech.yahoo.com/ai/claude/articles/anthropic-researcher-says-claude-solved-183242612.html>. Retrieved 2026-11-21 05:10:10 UTC, HTTP 200, 538,180 bytes, sha256 `23287aa15f5ada3c87f97c69aa784e24caba665107a9c4216daf75d7e3abd242`.
<a id="s3"></a>
- **S3.** AFP copy: The Straits Times. <https://www.straitstimes.com/world/united-states/anthropic-researcher-says-ai-chatbot-claude-solved-maths-greatest-riddle>. Retrieved 2026-11-21 05:10:12 UTC, HTTP 200, 138,572 bytes, sha256 `ad9c400cbf3f78c360f3dc04c71b1ebb6c240799be025a332a60acd2c3736e5f`.
<a id="s4"></a>
- **S4.** AFP copy: RTL Today (earliest AFP version, 17:25:53 UTC; also recorded under P7). <https://today.rtl.lu/news/world/anthropic-researcher-says-claude-solved-maths-greatest-riddle-376623520>. Retrieved 2026-11-21 05:10:20 UTC, HTTP 200, 388,224 bytes, sha256 `6f99d9a5fa0d88a3766ce55ce34d39675e109bf76c3d8a0282f6873b40aeffea`.
<a id="s5"></a>
- **S5.** AP copies (Winnipeg Free Press and others). <https://winnipegfreepress.com/arts-and-life/life/sci-tech/2026/11/20/anthropic-worker-claims-to-have-solved-a-holy-grail-of-math-problems-with-the-help-of-ai>. Not fetched; seen in web_search results 2026-11-21 between 05:05Z and 05:16Z, HTTP n/a (search result only), no byte hash.
<a id="s6"></a>
- **S6.** NYT and Kyodo copies (Deccan Herald and Japanese regional papers). <https://www.deccanherald.com/technology/anthropic-mathematician-claims-to-have-solved-maths-most-famous-problem-riemann-hypothesis-4226294>. Not fetched; seen in web_search results 2026-11-21 between 05:05Z and 05:16Z, HTTP n/a (search result only), no byte hash.
<a id="s7"></a>
- **S7.** Other outlets: Washington Post (not readable), Tom's Hardware, SiliconANGLE, NDTV, OfficeChai, Deutschlandfunk, Der Standard, Le Parisien, Numerama and others. <https://www.washingtonpost.com/technology/2026/11/20/using-anthropic-ai-mathematician-claims-have-solved-riemann-hypothesis/>. Retrieved 2026-11-21 05:11:59 UTC, HTTP 000, 0 bytes, sha256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (sha256 of the empty 0-byte response when curl failed to connect or timed out, not an error page or the article).
<a id="s8"></a>
- **S8.** Chinese aggregators: 36Kr (果壳), cls.cn, ifeng (知识分子), qq.com. <https://www.36kr.com/p/4078902157185920>. Not fetched; seen in web_search results 2026-11-21 between 05:05Z and 05:16Z, HTTP n/a (search result only), no byte hash.
<a id="s9"></a>
- **S9.** Machine-written or low-quality news sites (nacionale, huggingnews, traictory, kingy.ai and about 25 others); do not cite. <https://nacionale.com/en/articles/is-riemann-hypothesis-proof-correct-what-mathematicians-say-sutherland-buzzard-lean>. Not fetched; seen in web_search results 2026-11-21 between 05:05Z and 05:16Z, HTTP n/a (search result only), no byte hash.
<a id="s10"></a>
- **S10.** riemannhypothesisclaude.org (anonymous site with a "verification log"). <https://riemannhypothesisclaude.org/>. Retrieved 2026-11-21 04:59:35 UTC, HTTP 200, 34,517 bytes, sha256 `f2e51bcf496fab96240f1120cead6d7b7676c0019c942979f7d15e92c49439e5`.
<a id="s11"></a>
- **S11.** felloai.com, "Riemann hypothesis solved". <https://felloai.com/riemann-hypothesis-solved>. Retrieved 2026-11-21 04:59:35 UTC, HTTP 403, 5,594 bytes, sha256 `984d3a1c08990245213f22ffffd30bdbe53d9d2c3c94ffa0a6f51df5150d5a4f` (of the error or challenge page we received, not of the article).
<a id="s12"></a>
- **S12.** explainx.ai, "claimed vs verified" explainers on both claims. <https://explainx.ai/blog/levent-alpoge-anthropic-riemann-hypothesis-claude-lean-proof-claimed-vs-verified-2026>. Retrieved 2026-11-21 05:03:01 UTC, HTTP 200, 195,246 bytes, sha256 `9005cc834e9d081e8a19f0b665e0ee4dc7027187dbff87864656712ffa51ae52`.
<a id="s13"></a>
- **S13.** HN comment repeating the 250,000-page error. <https://news.ycombinator.com/item?id=50580704>. Retrieved 2026-11-21 05:10:29 UTC, HTTP 200, 216 bytes, sha256 `405f2cb996710fed79d3d0b377f3ee0001939da644b8238918e53c13816bda3d`.
<a id="s14"></a>
- **S14.** OfficeChai, "Hours after Alpöge’s AI-assisted Riemann Hypothesis proof, AMS president Ravi Vakil…". <https://officechai.com/ai/hours-after-alpoges-ai-assisted-riemann-hypothesis-proof-ams-president-ravi-vakil-rushes-out-a-rival-all-human-proof-by-alessandro-masullo/>. Retrieved 2026-11-21 05:05 UTC-05:11Z (approx.), HTTP web_search snippet only (not fetched), no byte hash.

## Updates to Part I

- **Lean Zulip (Part I, §5, last paragraph).** The two threads are web-public and were read in full through Zulip's public API on 2026-11-21 05:27–05:28 UTC (V2–V4); the remark "login required, not read" applied to the web client only.
- **Comparator repository (Part I, §5).** Its README changed after Part I's copy (04:02:24 UTC): new copy in V5. Still no Comparator verdict posted at 05:24 UTC.
- **Sutherland's page (Part I, §5).** Unchanged at 04:47:41 and 05:24:05 UTC; the earlier 19:45 UTC version is now pinned (V1).
- **Priority on the p. 451 gap.** The earliest written statement we found is the Refine report (E6, 21:12 UTC), before mccorvie issue #1169 (E2, 23:35 UTC).
- **First public report on Zulip.** Posted by Jack McCarthy (V2), who also created the Comparator mirror (V5, commits as Deicyde).
- **Final re-check, 2026-11-21 05:56:45–05:57:12 UTC** (`raw/F/`): A1, A3, A4, V1 (page), V5 (README) and V6 (README) returned the same sha256 as listed above; parts 01 and 14 of A2 returned the same ETags; V5 had new items #11 and #12 (05:38, 05:41) but no Comparator verdict; the two Zulip threads had no new verification report.
- **Re-check during Part I completion, 2026-11-21 12:42:26–12:42:37 UTC** (run `rhbook-ch4-5-1121d-11212036/fetches/`): `alpo.ge` unchanged (`11,625` B, `a7ee08f4…`); Sutherland's page (V1) updated at `10:05 UTC` (`18,306` B, `d35ac26a…`, adding `kimihiro64/Robin1984` arithmetic-consequences logs and a 240-module `lake build` path check, with main and combined `lake comparator` and export Lean kernels still running); LUMI (V6) updated at `12:40 UTC` (`README.md` `9,779` B, `72da7b8d…`, compiled-environment walk of `1,478,243` constants complete); Comparator repository (V5) at HEAD `d4544218d7` (`12:39:14 UTC`, `README.md` `5,290` B, `de494296…`, `verification/NOTES.md` `16,117` B, `d1c06dee…`, no Comparator verdict yet); `ishaan2006/rh-lean-reproduction` (`README.md` `24,807` B, `0ea8d58d…`, Zulip `#642470541`) reported a byte-identical `lean4export` sha256 match (`5ea74b91…244e`) with Sutherland's 61.57 GB export; `shosonoda/lean-rh-alpoge` (`README.md` `18,375` B, `939ab080…`) reported sandboxed Comparator rebuild/export complete and kernel replay running; `mccorvie/riemann-masullo` `README.md` unchanged (`8,899` B, `69352b47…`) and `ERRATA.md` (`61,379` B, `05a26a0e…`) at 127 paper entries.
- **Re-check during Part II opening (Chapters 6–7), 2026-11-21 16:10–16:13 UTC** (run `rhbook-ch6-7-1121e-11220006/fetches/`): the Lean and Mathlib communities published an official joint verification statement (`https://leanprover-community.github.io/blog/posts/riemann-hypothesis/`, dated `2026-11-21 13:55 UTC`, `8,501` B, sha256 `f1bc87e6bf7aa9285fc0507377b850cfa166c9035c8fbc6394a182655f0a9a35`, announced by Johan Commelin on Zulip `#642485818`), endorsed by the Lean FRO and the Mathlib Initiative, certifying that both the statement and the Lean proof of `RiemannHypothesis` are correct; Sutherland's page (V1) updated at `12:55 UTC` (`20,460` B, sha256 `e46488825acc7e4f…`, main and combined `lake comparator` and single-threaded export Lean kernels still listed as `running`); LUMI `README.md` (V6) updated (`11,570` B, sha256 `28c0a13c24d5642a…`), cross-checking its `1,478,243`-constant walk against James Shore's newly published kernel-term dependency dataset (`https://github.com/james-shore/rh-proof-dependencies`, `README.md` `22,828` B, sha256 `394093e4cd4e8a78…`, reporting `804,912 / 1,061,400` project declarations and `146,287 / 175,187` source files used, or `1,484,729` constants including `6,486` unreferenced recursors); `leanprover-community/riemann-hypothesis` reached issue/PR `#40`, including merged PR `#34` (`gh-dv-openclaw`, machine-checked equivalence of `PrimitiveDirichletLZerosOnLine` with `formal-conjectures`'s GRH) and open issue `#39` (`aapolipponen`, table of named classical theorems); and this book's own repository (`Li-Hongmin/amazing-riemann-hypothesis`) had open community PR `#1` (`leecrossley`, `2026-11-21 09:43:46 UTC`, proposing a three-term delayed-difference note on Theorem 3.6 backed by `leecrossley/dirichlet-window-transfer` and `doi:10.5281/zenodo.24410863`).
- **Re-check during Part II continuation (Chapters 8–10), 2026-11-21 19:04:53 UTC** (run `rhbook-ch8-10-1122a-11220300/fetches/`): Sutherland's verification page (V1) unchanged at `12:55 UTC` (`20,460` B, sha256 `e46488825acc7e4fdcc2576af4c887d8f754cbbaeb270c74031c90c97e99870b`, single-threaded export Lean kernels and `lake comparator` still listed as `running`); LUMI `README.md` (V6) unchanged (`11,570` B, sha256 `28c0a13c24d5642a40687d43de71d2925884a7070b79d6c0196e7121c56d8202`); `leanprover-community/riemann-hypothesis` reached issue/PR `#45` (adding PRs `#40`, `#44`, and `#45` removing unused modules and dead code); `Li-Hongmin/amazing-riemann-hypothesis` had open community PR `#1` (`leecrossley`) and zero other issues/PRs; and 14 additional classical references (`[BellaicheChenevier2009]` through `[Siegel1935b]`) were verified online and added to Part I, §6 above.
- **Re-check during Part II closing & Part III completion (Chapters 11–13), 2026-11-22 00:02:53 UTC** (run `rhbook-ch11-13-1122b-11220724/fetches/`): Sutherland's verification page (V1) unchanged at `12:55 UTC` (`20,460` B, sha256 `e46488825acc7e4fbf3c0c744edcfaa5219f773571a9267b06df26b11f18a1a3`, single-threaded export Lean kernels and `lake comparator` still listed as `running`); LUMI `README.md` (V6) unchanged in length (`11,570` B, sha256 `28c0a13c24d5642a2fed464cf2cfd148ab1880367ea5a6c167ae2850b9d69b68`); `leanprover-community/riemann-hypothesis` reached issue/PR `#59` (continuing dead-code, unused-import, and wrapper-collapsing PRs); `Li-Hongmin/amazing-riemann-hypothesis` had open community PR `#1` (`leecrossley`) and zero other issues/PRs; and 17 additional classical references (`[BushnellKutzko1993]` through `[Thorne2015]`) were verified online and added to Part I, §6 above.
- **Re-check during Part IV completion (Chapters 14–16), 2026-11-22 03:29–03:30 UTC** (run `rhbook-ch14-16-1122c-11221118/fetches/`): Sutherland's verification page (V1) updated at `2026-11-22 03:10 UTC` (`24,564` B, sha256 `17661672e3dcc7cc83f170b11027cf55e75d808530f1dff1e74a0a221c808010`, adding sandboxed `lake build Main` byte-identical export `5ea74b91…244e` and `con-ron --compare` pass); `mccorvie/riemann-masullo` `README.md` at `13,030` B (`f121f834…`, ~4,700 stated / ~3,950 proved across ~1,360 PRs, ~200 `ERRATA.md` entries); `leanprover-community/riemann-hypothesis` reached PR `#65` (pruning 10,724 unused files); and 12 additional classical references (`[Artin1924]` through `[Weil1965]`) were verified online and added to Part I, §6 above.
- **Re-check during Chapters 17–18 expansion & full-book audit closure, 2026-11-22 09:15 UTC** (run `rhbook-ch17-18-1122d-11221700/fetches/`): pinned Mathlib `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` (`21,422` B, sha256 `44a7d25a608a4242693b5b4f849c27ea0075ba585d9db48f16bbfe84df4ab5b5`) retrieved and added to Part I, §4 above; Sutherland's verification page (V1) updated at `2026-11-22 04:35 UTC` (`27,222` B, sha256 `01a43fc8defab818d878bfa8fd900d7563073db3dbc6f150ad73baec0fe388a7`, reporting standalone `kimihiro64/Robin1984` passing both Comparator `v4.33.0` at `03:31:06 UTC` and `lake comparator` `v4.36.0` at `04:16:52 UTC` alongside elaborated `lagariasStmt`, while main and combined 62 GB `lake comparator` kernel stages remain `running`); `mccorvie/riemann-masullo` `README.md` updated (`14,590` B, sha256 `9072dc8b625f3b07e02b5e60be1edef38816c975aee2f5c03f2b05a1a4be5c2e`, Wave 3 seeded as section issues and `lake comparator` harness added); `rStation` `riemann_hypothesis_189` updated to `v3` (`2026-11-22 05:23 UTC`, `142,166` B, sha256 `15bbcef5a144e33264be7de5f0e7291ebd9a89546e3d9d0de10f3b03cc96e863`); and 10 classical references (`[Artin1927]`, `[Behrend1946]`, `[Berger2002]`, `[Clozel1990]`, `[DeligneRibet1980]`, `[Neukirch1999]`, `[NeukirchSchmidtWingberg2008]`, `[Roth1953]`, `[Tschebotareff1926]`, `[Wiles1995]`) were verified online via Crossref and added in strict alphabetical order to Part I, §6 above.

- **Nielsen critique, 2026-11-23 (CST)**: E14 added; code claims verified against the pinned archive; analysis in Chapter 16, §16.6.

- **Chapter 8, Sections 8.4.4–8.4.5, 2026-11-23T06:54Z**: `[Katz1976]` re-verified via Crossref (`doi:10.2307/1970966`: Katz, *The Annals of Mathematics* 104, no. 3, first page 459, issue date 1976-11), unchanged. LUMI `docs/04-chain-and-one-half.md` re-fetched (`32,281` B, sha256 `5258df0f8b20609b38926ca1ef54b0ac45afc5b2f7749022dc7086d64573f9f9`, last commit `c6d0e2bc06` at 2026-11-21T13:02:26Z; §5 lists the earlier `31,832`-byte copy of 2026-11-21T04:03:05Z). Its section "How the divisibility `Conclusion1` is proved" outlines the jet bound `kernel_a_one_generic`, the gain identity `ea_A1U`/`ea_BrNum` and the accumulation `lift_bound_of_integrality`/`main_ind` [Community]; Section 8.4.5 reads these declarations against the pinned archive.

- **Chapter 13, Section 13.4.4, 2026-11-23T09:23Z**: `[Green1955]` read in the Internet Archive copy recorded in Part I, §6 (pages listed there). LUMI `docs/07-named-theorems.md` re-fetched from `https://raw.githubusercontent.com/aapolipponen/rh-lean-check-lumi/main/docs/07-named-theorems.md` (`44,821` B, sha256 `e857b8c5f9b6d00f66f645c7bd1183564c7852ac03820c3552821c6895809391`; §5 lists the earlier `43,596`-byte copy); its row for `GreenRegularCharacters` reads "special case — Green's cuspidal characters of GL_d(𝔽_q), only for q = p prime" (review R2 #14) [Community]. Mathlib `FinGroupCharZero.lean` added to Part I, §4 for `FDRep.simple_iff_char_is_norm_one`.

- **Chapter 6, Section 6.4.5, 2026-11-23 (CST)** (run `rhbook-ch06-quotient-slopes-1123h-11231636/fetches/`): [Bost1996] Numdam PDF re-fetched (sha256 `13d2911a…0edb`), Appendix A read on printed pp. 146–148; G2 issue #5 body re-fetched (63,424 B, sha256 `82efbf22…cae3`); G10 [Jaswal2026] added (sha256 `ed321931…57a7`). Main-theorem export (V-section entry above) re-hashed locally: `d5fad832…89fb`, unchanged.


### Internal review of Chapters 17–18

The same-source preliminary audit `ssaudit-rhbook-ch17-18-1122d-11221700-11222118`
recorded partial acceptance in `REPORT.md`, with itemized findings in
`work/AUDIT_DETAILS.md`. These are internal review records. The book's corrections are
based on the pinned Lean source and Masullo's PDF (A4). See Chapters 14 and 16–18.
Masullo's Appendix A.4 is pp. 562–565, and Appendices B–E are pp. 587–654,
655–742, 743–822 and 823–932 respectively.

### P11 global Selmer presentation

- **A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, supplies the square-presentation and scalar-transport proofs. A1 p. 1 n. 1 names the fourteen archive parts. [Author announcement](https://alpo.ge/remark.pdf) · [Chapter 10](../chapters/10-congruence-modules-to-sha.md#10412-a-square-presentation-of-the-global-selmer-functor)
- **Stacks Project, Algebra §10.39 and Lemmas 10.51.2 and 15.8.2.** Flat tensor exactness, Artin–Rees for finite modules over a Noetherian ring, and independence of Fitting ideals from presentation, respectively. [Flatness](https://stacks.math.columbia.edu/tag/00H9) · [Artin–Rees](https://stacks.math.columbia.edu/tag/00IN) · [Fitting ideals](https://stacks.math.columbia.edu/tag/07Z8)

- **J. S. Milne, Arithmetic Duality Theorems, 2nd ed. (2006), I.2.8, I.4.10 and I.5.1, pp. 31, 56–57 and 67.** The local Euler characteristic, the degree-two tail of Poitou–Tate, and the global Euler characteristic. The last term in the degree-two tail is dual to the global invariants of the twisted dual. Retrieved 2026-11-24, SHA-256 `2c6195ec76a974f3f336c77cb71cc3845b018aad2d43136716b3477a3bc5fb31`. [Author PDF](https://www.jmilne.org/math/Books/ADTnot.pdf)
- **Online versions retrieved 2026-11-24.** A1 PDF SHA-256 `3fc97784b71ddd44ff8aa0a177e99622a1c61b13cfa843a0989ee4a7a0cfeb8d`. Stacks flatness section HTML SHA-256 `2a8b0d6e5e27464d05517762910d5420d4c1fade42f4ec742b821cdaaf59925c`; Artin–Rees lemma HTML SHA-256 `3e7f0333310107c55a4ecd715be67d87df9b3b248f35e6cefa6a986316565cd0`.

### Chapter 18 §18.3.7, local Euler characteristic

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The direct cardinality proof, absolute-to-place transport, and `GC.locEuler` give the production and consumption of the Euler field. [Subsection](../chapters/18-auditing-the-published-layer-case-studies.md#1837-local-euler-characteristics-away-from-the-residue-prime)
- **J. S. Milne**, *Arithmetic Duality Theorems*, 2nd ed. (2006), I, Theorem 2.8 and Lemmas 2.9 and 2.11, pp. 31–34. The local Euler–Poincaré formula, the residue-prime-to-order proof, and the mixed-characteristic equivariant calculation. Retrieved 2026-11-24, SHA-256 `2c6195ec76a974f3f336c77cb71cc3845b018aad2d43136716b3477a3bc5fb31`. [Author PDF](https://www.jmilne.org/math/Books/ADTnot.pdf)
- **John Tate**, “Duality theorems in Galois cohomology,” Proc. ICM Stockholm (1962), pp. 288–295, Theorems 2.2 and 2.4, pp. 289–290. The historical local Euler formula and the unramified exact annihilator theorem. PDF retrieved 2026-11-24, SHA-256 `61f99c052fe734da98ef56de080bbd5fbc640973e7c4649e3be423f9d2e2302f`. [Original proceedings scan](https://math.stanford.edu/~conrad/BSDseminar/refs/TateICM.pdf)

### Chapter 18 §18.3.8, completion comparison

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The comparison `decEquiv` and its inputs in `DecompositionGroupEquivLocalGaloisGroup.lean`, `FiniteDimensionalAdjoinRange.lean`, `LocalInertiaIffMemPlaceInertia.lean` and `MemSpanLIff.lean`; the transport lemmas in `TransportA.lean` and `TateShafarevichTransport.lean`; the consumer `localEulerChar_holds`. All 34 cited files were compared byte for byte with the archive tarball. [Subsection](../chapters/18-auditing-the-published-layer-case-studies.md#1838-decomposition-groups-as-galois-groups-of-completions)
- **Mathlib** at commit `0df444a360eaa60ab8c11dca51a86af692955474`, pinned by the archive: continuity of roots, Krull-topology lemmas, spectral-norm invariance, equivalence of absolute values, profinite conjugacy of primes and the compact-to-Hausdorff lemma, checked by statement. [Mathlib at that commit](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)
- **J. S. Milne**, *Arithmetic Duality Theorems*, 2nd ed. (2006), Proposition 0.15 and the following paragraph, p. 11, and I, Corollary 2.3, p. 28. Conjugation invariance of localization maps and local duality. Retrieved 2026-11-24, SHA-256 `2c6195ec76a974f3f336c77cb71cc3845b018aad2d43136716b3477a3bc5fb31`. [Author PDF](https://www.jmilne.org/math/Books/ADTnot.pdf)
- **J. S. Milne**, *Class Field Theory*, v4.03 (2020), I, Theorems 1.1 and 1.4, pp. 20–22, and II, Proposition 1.34, p. 71. Local reciprocity, the existence theorem and inflation–restriction, used in the inert example. Retrieved 2026-11-24, SHA-256 `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`. [Author PDF](https://www.jmilne.org/math/CourseNotes/CFT.pdf)
- **J. S. Milne**, *Algebraic Number Theory*, v3.08 (2020), Theorem 3.34, p. 59, and Proposition 8.10, p. 139. The identity $\sum e_if_i=[L:K]$ and the classical isomorphism of decomposition groups with local Galois groups. Retrieved 2026-11-24, SHA-256 `24b83c789a89f25aebffb3cbe4ae5ca29edd0075acc072de093d140770630847`. [Author PDF](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

### Chapter 18 §18.3.9, local degree count

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The four counting proofs `ballCard`, `denseSurj`, `kerProp` and `normCard` with their helpers in `MemIntegralClosureIffMemBall.lean`, `ExistsDen.lean`, `IsEquivAdicAbvNormAbv.lean` and `SpanLIsMaximal.lean` (`src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompletionDegrees/`), their assembly `locDegOf_of` and its application `finrank_closure_eq_locDeg`. `placeProp` (`NormLeOneOfInteger.lean:73–75`) stays a named input. All 21 cited files were compared byte for byte with the archive tarball. [Subsection](../chapters/18-auditing-the-published-layer-case-studies.md#1839-counting-the-local-degree-closed-balls-integral-approximation-and-the-power-kernel)
- **Mathlib** at commit `0df444a360eaa60ab8c11dca51a86af692955474`, pinned by the archive: the spectral norm of `PadicAlgCl`, minimal polynomials over integrally closed domains, finiteness, freeness and rank of integral closures, the reduction $\mathbb Z_p\to\mathbb F_p$, localizations of Dedekind domains at primes, adic valuations and factorization counts, the length-based ramification index, the absolute norm and residue degrees, and the closure criterion, checked by statement. [Mathlib at that commit](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)
- **J. S. Milne**, *Algebraic Number Theory*, v3.08 (2020), p. 8, Example 2.41, p. 39, p. 59, Theorems 3.34 and 3.41, pp. 59–63, Lemma 7.25 and Proposition 7.26, pp. 116–117, Theorem 7.38, p. 123, and Corollary 7.42 with Remark 7.43, p. 124. The rings of integers and prime factorizations in the two examples, the layer count behind $\sum e_if_i=n$, completions as inverse limits, the unique extension of absolute values and $n=ef$. Retrieved 2026-11-24, SHA-256 `24b83c789a89f25aebffb3cbe4ae5ca29edd0075acc072de093d140770630847`. [Author PDF](https://www.jmilne.org/math/CourseNotes/ANT.pdf)
- **Internal review** `audit-rhbook-ch18-completion-comparison-1124j-11242136-11242248` (partial acceptance) found that Corollary 18.3.8.1(b) stated $e_D$ only as a group isomorphism. The archive assumes `eD : ∀ i, D i ≃ₜ* D' (eI i)` at `TateShafarevichTransport.lean:46`, and the corollary now requires $e_D$ and $e_D^{-1}$ to be continuous.

### Chapter 12 §12.4.4, holomorphic Lefschetz input

- **Classical context for §12.4.4.** M. F. Atiyah and R. Bott, *A Lefschetz fixed point formula for elliptic complexes. I*, Annals of Mathematics 86 (1967), 374–407, DOI 10.2307/1970694, gives the analytic elliptic-complex precedent. J.-P. Serre, *Géométrie algébrique et géométrie analytique*, Annales de l’Institut Fourier 6 (1956), 1–42, Théorème 1, DOI 10.5802/aif.59, gives coherent cohomology comparison. Checked online 2026-11-23. [Annals](https://annals.math.princeton.edu/1967/86-2/p07) · [Numdam](https://www.numdam.org/item/AIF_1956__6__1_0/)
- **Community reading for §12.4.4.** LUMI doc 05 already outlines the algebraic Lefschetz proof and its use in the complex trace comparison. Re-fetched at revision `c6d0e2bc06ae4562d6656c6ef118739670d19eeb` on 2026-11-23, SHA-256 `dc304e6a40d4f6233e8fa22feb1bfbb34a9b7f7c42be732f88c9f884a50b94a6`. [LUMI guide](https://github.com/aapolipponen/rh-lean-check-lumi/blob/c6d0e2bc06ae4562d6656c6ef118739670d19eeb/docs/05-galois-representations.md#L89-L103)

### Chapter 12 local Lefschetz weight

- **A2.** The local chart proof uses a common Čech representative, evaluates the diagonal pairing on the cotangent exterior powers, compares the two Koszul components, and sums the trace over the reduced fibre. Complete paths and reading levels are in the subsection. [Local Lefschetz weight](../chapters/12-galois-representations-and-local-langlands.md#from-a-finite-étale-chart-to-the-local-lefschetz-weight)
- **Atiyah–Bott I.** Theorem A, pp. 377–378, in the 1967 original gives the simple-fixed-point formula for elliptic complexes with the absolute real determinant. Its Dolbeault specialization explains the complex determinant for a single map. [Original publication](https://doi.org/10.2307/1970694)
- **Serre, GAGA.** No. 12, Théorème 1, p. 19, gives the coherent-cohomology comparison. [Original PDF](https://www.numdam.org/article/AIF_1956__6__1_0.pdf)

### Chapter 12 global boundary comparison

- **A2.** The <code>yCmpG_of</code> producer compares the origin column by localization, uses column exactness elsewhere and applies the filtered total-boundary criterion. The chapter records the complete paths and proof-body reading levels. [Global comparison](../chapters/12-galois-representations-and-local-langlands.md#from-fixed-point-vanishing-to-a-global-čech-boundary)
- **The Stacks Project, online text retrieved 2026-11-24.** Lemma 10.23.1 proves localization detection for modules and exactness. Lemma 15.29.5 gives the homological Koszul homotopy whose cochain counterpart is the signed contraction in the chapter. Lemma 30.2.6 identifies Čech and sheaf cohomology for quasi-coherent coefficients on the affine-intersection cover used in the failure example. [00HN](https://stacks.math.columbia.edu/tag/00HN) · [0626](https://stacks.math.columbia.edu/tag/0626) · [01XD](https://stacks.math.columbia.edu/tag/01XD)

### Chapter 12 §12.4.4, reduced-fibre trace

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The producer `trF_locCoch_eq_finsum_fib` behind `trace_cechCochain_fraction_eq_sum_fibre`; `TraceOrigin.ev_eq_trace_quot`, `trace_quotient_eq_of_projective`, `FibTrace.trace_quot_eq_finsum_fib`, `FibFin`, `finite_card_trace_algHom_of_isReduced_baseChange` with its point-count lemmas, `ResEv.chart0`, `integralClosure_projective_rA` and `exists_isRes`; the consumers `deRham_restriction_trace_degree_one`, `trTop_of`, `fieldLe_of`, `yMain_of` and `geoStep_of`. All 32 files of the run's source map were compared byte for byte with the archive tarball. [Subsection](../chapters/12-galois-representations-and-local-langlands.md#from-the-finite-algebra-trace-to-the-reduced-fibre)
- **Mathlib** at commit `0df444a360eaa60ab8c11dca51a86af692955474`, pinned by the archive. `Mathlib/RingTheory/Trace/Quotient.lean`, lines 40–50 and 69–125, and `Mathlib/RingTheory/IntegralClosure/IntegralRestrict.lean`, lines 263–331, read in full; the étale splitting, character-independence and integrality lemmas checked by statement. Retrieved 2026-11-24, SHA-256 `5ba85ac0a9a570bf2f87136fbaa3a1e22437b1325458216ec1c942e256f08db2` and `0fc965dfe7c123152ec38710ed8a22d43e63629d324b3d435a2fe69b82506c57`. [Quotient.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Quotient.lean) · [IntegralRestrict.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/IntegralClosure/IntegralRestrict.lean)
- **The Stacks Project**, online text retrieved 2026-11-24. Lemmas 9.13.1 and 9.13.4: independence of characters, and $K\otimes_FL\cong\prod_\sigma L$ for $K/F$ finite separable and $L$ algebraically closed (tag 0CKK, page SHA-256 `5c5c65527ed18f67d7968a36483b725c5b3cf966650e95d55953d121aa5cbbf3`). Lemmas 9.20.3 and 9.20.5: the trace as a multiple of a coefficient of the minimal polynomial, and transitivity of traces (tag 0BIE, `1fe21ce54aba4cebd3afe798c443a0544a3734e761a6dc4dce3f6322a0931213`). Lemma 10.161.8 with Lemma 10.38.6: traces of integral elements over a normal domain (tags 032L, `ab6529a0cf20c0dfb03e16aa3e883fd89bd15d1d536f2349e216ca856c1c6b5a`, and 037E, `455e73532a0b872d0f8462e5f3838fc4c6d5963cd46bb2423733199c31875e13`). Lemma 10.128.1: miracle flatness (tag 00R4, `cc7f1947308a6c8db0d6d0d406bfecc4ef2363d710f694b1cc5fe9bb0ba8219f`). Lemma 10.78.2: finite projective modules (tag 00NX, `eff659c72d1c4d401af55b2b26f59588f21b98f64ca4c811faeb28eed7cc2ff4`). Lemma 30.8.1: cohomology of projective space by Laurent monomials (tag 01XT, `5de00d1c2631c43c32f5995529fe5e3a6b1156cc21c65a7497c8ca667c07938f`). [0CKK](https://stacks.math.columbia.edu/tag/0CKK) · [0BIE](https://stacks.math.columbia.edu/tag/0BIE) · [032L](https://stacks.math.columbia.edu/tag/032L) · [037E](https://stacks.math.columbia.edu/tag/037E) · [00R4](https://stacks.math.columbia.edu/tag/00R4) · [00NX](https://stacks.math.columbia.edu/tag/00NX) · [01XT](https://stacks.math.columbia.edu/tag/01XT)

### Chapter 12 §12.4.4, reduced auxiliary projection

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The producer `FibRed.exists_finCover_fibre_reduced` behind `exists_finiteCover_projSpace_reduced_fibre_origin`, the germ quotient `FibRed.quotEquiv_of_germ`, `exists_transversal_forms_first_separate`, `isFinCover_of_forms` with `isFinite_formMap` and `exists_finCover_of_isFinite`, `isReduced_quotient_of_artinian_of_maximal_le`, `MaxPt.exists_cxPts_ker_eq`, `isArtinianRing_fib_quot`, and the transport `etaleCorrespondence_fieldExtension_statement`; the consumers `holomorphic_lefschetz_finiteEtale_integral`, `field0_of` and `fieldLe_of`. All 48 archive files of the run's source map were compared byte for byte with their tarball members, with file hashes and complete paths. [Subsection](../chapters/12-galois-representations-and-local-langlands.md#from-a-general-projection-to-a-reduced-origin-fibre)
- **Mathlib** at commit `0df444a360eaa60ab8c11dca51a86af692955474`, pinned by the archive; statements and file-header authors checked on files retrieved 2026-11-24. `IsFinite.iff_isProper_and_isAffineHom` (`Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:98`), `germ_injective_of_isIntegral` (`Mathlib/AlgebraicGeometry/FunctionField.lean:55`), `IsArtinianRing.isNilpotent_jacobson_bot` (`Mathlib/RingTheory/Artinian/Ring.lean:54`), `finite_of_finite_type_of_isJacobsonRing` (`Mathlib/RingTheory/Jacobson/Ring.lean:676`), `IsAlgClosed.algebraMap_bijective_of_isIntegral` (`Mathlib/FieldTheory/IsAlgClosed/Basic.lean:220`), `Algebra.FormallyUnramified.of_isSeparable` and `isReduced_of_field` (`Mathlib/RingTheory/Unramified/Field.lean:44,123`) and `MeasureTheory.Measure.pi_hyperplane` (`Mathlib/MeasureTheory/Constructions/Pi.lean:409`). [Proper.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean) · [FunctionField.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/AlgebraicGeometry/FunctionField.lean)
- **The Stacks Project**, online text retrieved 2026-11-24. Lemma 29.45.11: finite is affine and proper (tag 01WN, page SHA-256 `2cec950febea13f47f1d8f544b6f6ce46c2234771db392c3395b227140273a9d`). Lemmas 10.53.4 and 10.53.5: the Jacobson radical of an Artinian ring is nilpotent, and a ring with finitely many maximal ideals and locally nilpotent Jacobson radical is the product of its localizations (00J8, `f0b1795d42c7c949069a172f11a9146e3ad10e7e0df9949b4a7d452562794070`; 00JA, `3f948768fc4731faa7e06a7d240bab362bd90bc6fd44451f3f12da9c2880b205`). Theorem 10.34.1: the Nullstellensatz (00FV, `6cd63b63c40ce5998c105e5c5ce5b3e78aa099ff5dea75c17280eb1d66030bde`). Lemmas 10.140.1 and 10.140.3: cotangent dimension and smoothness over a field (00TQ, `134798bbf3b68ffb99a149710ffe2fbd2a607d03522ca94162dc58514207f2ab`). Lemma 10.163.7: smooth over a reduced ring is reduced (033B, `9e61f25f016c76fc18afea19297818075dac3aa8f2a5d85f8beff5cab0c5a074`). Lemma 10.143.4: étale algebras over a field (00U3, `a9f84f12996a09134dbbdf4a71bea07a6cfd19af2a9e11429da632b0b0596b72`). Lemma 43.23.1: projection from a point off $X$ is finite (0B1P, `0436150f0073a11090982e4f90f0c05292745ba0563e7e9125d749f36dded46e`). [01WN](https://stacks.math.columbia.edu/tag/01WN) · [00J8](https://stacks.math.columbia.edu/tag/00J8) · [00JA](https://stacks.math.columbia.edu/tag/00JA) · [00FV](https://stacks.math.columbia.edu/tag/00FV) · [00TQ](https://stacks.math.columbia.edu/tag/00TQ) · [033B](https://stacks.math.columbia.edu/tag/033B) · [00U3](https://stacks.math.columbia.edu/tag/00U3) · [0B1P](https://stacks.math.columbia.edu/tag/0B1P)
- **A. Sard**, “The measure of the critical values of differentiable maps,” *Bull. Amer. Math. Soc.* 48 (1942), 883–890, p. 883: for a $C^q$ map from a region of $\mathbb R^m$ to $\mathbb R^n$ with $m\le n$ and $q\ge1$, the critical values have $m$-dimensional measure zero. The book uses $m=n=2d$. The text was read through a search index on 2026-11-24; the publisher's PDF could not be downloaded directly, so no file hash is recorded. [DOI](https://doi.org/10.1090/S0002-9904-1942-07811-6)

### Chapter 12 §12.4.4, forms with prescribed jets

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The producer `EtProj.Jets.exists_jet_forms` behind `exists_forms_vanishing_complexPoints_fullJets` (`ExistsFormsVanishingComplexPointsFullJets.lean`, file SHA-256 `8c2bbda5f30e8e7c2ab1d6196c5b3357b5bf12350ef6883bb57d3513a7452efa`), with `exists_lin_sep`, `exists_sep`, `exists_lin_mul`, `exists_form_jet`, `jet_range`, `ratio_sq_mem`; `RatSpan.adjoin_fRatio_eq_top` and `RatSpan.ratio_span_cotangent` (`AlgebraMapBasicOpen.lean`, `6384ec674fde8ba5b85badf2edc77fd774a64fdd82dbf54c0577d9433aac1192`); `Generic.exists_finite_gen`, `Generic.coheight_step` (`ExistsGenericForms.lean`, `4f5bc380d705a184cd787a94c1bffd402af25ffe852b7290a727790b1dc0fd11`); the consumer `exists_transversal_forms_first_separate`. All twelve archive files of the run's source map were compared byte for byte with their tarball members. [Subsection](../chapters/12-galois-representations-and-local-langlands.md#forms-with-prescribed-jets-at-finitely-many-points)
- **Mathlib** at commit `0df444a360eaa60ab8c11dca51a86af692955474`, pinned by the archive; statements and file-header authors checked on a local checkout of the pinned commit on 2026-11-25. `Submodule.exists_forall_notMem_of_forall_ne_top` (`Mathlib/Algebra/Module/Submodule/Union.lean:90`), `linearIndependent_fin_snoc` (`Mathlib/LinearAlgebra/LinearIndependent/Lemmas.lean:696`), `Order.coheight_add_one_le` (`Mathlib/Order/KrullDimension.lean:306`), `NoetherianSpace.exists_finite_set_isClosed_irreducible` (`Mathlib/Topology/NoetherianSpace.lean:176`), `ext_of_apply_closedPoint_eq` (`Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean:90`), `isClosedImmersion_of_comp_eq_id` (`Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:432`), `MvPolynomial.homogeneousSubmodule_one_pow` (`Mathlib/RingTheory/MvPolynomial/Homogeneous.lean:194`), `Submodule.eq_of_le_of_finrank_eq` (`Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:261`), `finrank_span_eq_card` (`Mathlib/LinearAlgebra/Dimension/Constructions.lean:461`) and `Proj.isAffineOpen_basicOpen` (`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:201`). [Union.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Module/Submodule/Union.lean) · [KrullDimension.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Order/KrullDimension.lean) · [NoetherianSpace.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/NoetherianSpace.lean)
- **The Stacks Project**, online text retrieved 2026-11-25. Lemma 5.9.2: a Noetherian space has finitely many irreducible components (tag 0052, page SHA-256 `c095a351e6754249ea6dfdd89b6b942a6178191d91bd686a80c32800651e1474`). Lemma 28.10.3: codimension of an irreducible closed subset equals the dimension of the local ring at its generic point (02IZ, `374c28c6ca76352c84f3a1d7fa0f589134312ccd751d85d33b3b615e65546ee6`). Lemma 33.20.3: dimension theory of locally algebraic schemes, in particular a strict specialization raises the dimension of the local ring (0A21, `0445097ccfceafb02963c01d20f2159c031fe93c1ddfdc64e9132812827020de`). Lemma 33.22.2: a linear form vanishing at a rational point and not at finitely many other points, the classical form of the archive's separation lemma (0B58, `1c79162311ecb6a126252efd76a5369dd0c8a2a6ea0568f5b8b8ad4b4efadfdc`). Lemmas 10.140.1 and 10.140.3: cotangent dimension at a smooth point (00TR, `73d1730c5020d9d862bce52110afbb578aba7516e1924f7b3b9a8fb3d9a4c113`; 00TT, `46fa4519b3ce15c9a4ec4bb5eb6f6671785fa2f25ed6035220b923d25aa40103`). Cited as the route the archive does not take: Lemma 30.14.1(4), Serre vanishing on projective space (01YS, `0743f92934c4b3ac02321af5c4b18135651e27098dfebc15c486682afbcef090`), and Lemma 33.23.2, very ampleness through length-two subschemes (0E8T, `9ffba193df6a9f5dc6520edce569d7d71cbd8ec9ab286ad1a05a96780408f08a`). [0052](https://stacks.math.columbia.edu/tag/0052) · [02IZ](https://stacks.math.columbia.edu/tag/02IZ) · [0A21](https://stacks.math.columbia.edu/tag/0A21) · [0B58](https://stacks.math.columbia.edu/tag/0B58) · [00TR](https://stacks.math.columbia.edu/tag/00TR) · [00TT](https://stacks.math.columbia.edu/tag/00TT) · [01YS](https://stacks.math.columbia.edu/tag/01YS) · [0E8T](https://stacks.math.columbia.edu/tag/0E8T)
- **Exact checks.** `check_jet_forms.py` in the run directory: 82 exact assertions over $\mathbb Q$ for the two hand calculations (polynomial identities, Gröbner-basis membership in $\mathfrak m^2$-primary ideals, change of denominator, degree bounds).

### Chapter 10 §10.4.13 auxiliary prime selection

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The conditional selection, the evaluation bridge, and the actual call sites are pinned by complete paths and lines in the chapter. [Chapter 10, §10.4.13](../chapters/10-congruence-modules-to-sha.md#10413-choosing-the-auxiliary-primes-in-a-common-galois-quotient)
- **Andrew V. Sutherland**, *18.785 Number Theory I*, Lecture 28 (8 December 2021), §28.5, Theorem 28.9, p. 6. Qualitative Dirichlet density for conjugation-stable sets in a finite Galois group, used for the degree-one deduction. PDF read online 2026-11-24, SHA-256 `89548327d6ec7c6773ad38b82b7afdf395cd51c95829884cebafe301156fa0d8`. [MIT lecture notes](https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf)

### Chapter 10 §10.4.11.1 global invariant sum in the new-place reciprocity

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, rechecked 2026-11-24. The producer `SumInvEqZeroOfUnramifiedCocyclePow.lean:8–29`, the descent lemma `SumInvEqZeroOfUnramifiedCocycle.lean:9–20`, the nine-term tail evaluation `PoitouTateNineTermTransgressionZeroApply.lean:196–220,254–280,305–340` and the consumer `ReciprocityRelaxedSelmerDualSelmerNewPlace.lean:22–315` are pinned by full paths and lines in the subsection; `PoitouTateTotallyComplex` (`:288–301`) is cited as a named input. [Subsection](../chapters/10-congruence-modules-to-sha.md#104111-the-global-invariant-sum-in-the-new-place-reciprocity)
- **J. Neukirch, A. Schmidt, K. Wingberg**, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323, Springer 2008, Theorem 8.6.10 (the Poitou–Tate nine-term exact sequence) and Theorem 8.6.7 (duality of the Tate–Shafarevich groups). Numbering checked online 2026-11-24 against citations in Geisser–Schmidt, *Poitou–Tate duality for arithmetic schemes* ([arXiv:1709.06913](https://arxiv.org/abs/1709.06913)), which cite (8.6.7) and (8.6.10) for exactly these two statements. [DOI](https://doi.org/10.1007/978-3-540-37889-1)
- **J. S. Milne**, *Arithmetic Duality Theorems*, 2nd ed. (2006), Theorem I.4.10, pp. 56–57. The degree-two tail of the sequence, whose last term is dual to the invariants of the twisted dual; for the cyclotomic character this is the reciprocity law for the Brauer group used in Examples 10.22a–10.22b. Same PDF and hash as the entry under "P11 global Selmer presentation" above. [Author PDF](https://www.jmilne.org/math/Books/ADTnot.pdf)

### Chapter 11 §11.4.3.3 — Kummer reflection

- **[MilneFT]** J. S. Milne, *Fields and Galois Theory*, v5.10 (2022), pp. 75–76, Theorem 5.30 and Remark 5.32. The author’s notes give the Hilbert 90 derivation of the Kummer correspondence and perfect pairing. Retrieved 2026-11-24, SHA-256 `5c43ea0bf4ec190b819727fe720414a80e09f9e762533d08bad5b8a0b6de7273`. [Author PDF](https://www.jmilne.org/math/CourseNotes/FT.pdf).
- **[Gras1998]** Georges Gras, “Théorèmes de réflexion,” *Journal de Théorie des Nombres de Bordeaux* 10(2) (1998), 399–499, §4, Definitions 4.1 and Lemma and Definition 4.3, pp. 418–419. The mirror-character formula twists the inverse character by the cyclotomic character. Retrieved 2026-11-24, SHA-256 `fdd27a7dc75c575e9ba93ee87bd58ec5f62f9df12a3819c19f3de59f3a7fa31c`. [Journal scan](https://www.numdam.org/item/JTNB_1998__10_2_399_0.pdf).
- The [Chapter 11 source map](../chapters/11-the-window-bound-vwin.md#11433-kummer-reflection-and-the-root-of-unity-kernel) locates the finite-layer proof in the pinned Alpöge archive. The two literature references supply the pairing and classical twist comparison. The proof of the particular root-character bound follows the archive.

### Chapter 11 §11.4.3.4 — binary sign supply

- **[MilneCFT]** J. S. Milne, *Class Field Theory*, v4.03 (2020), Ch. VIII, §3, Theorem 3.1 (Hasse norm theorem) and its proof, p. 234. The proof deduces the theorem from $H^1(G,C_L)=0$ and periodicity, as the archive does from the vanishing of $\widehat H^{-1}$ of the idele class group. Retrieved 2026-11-24; same PDF and SHA-256 `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5` as the Chapter 18 entry above. [Author PDF](https://www.jmilne.org/math/CourseNotes/CFT.pdf)
- **[Lemmermeyer1995]** F. Lemmermeyer, “Ideal class groups of cyclotomic number fields I,” *Acta Arithmetica* 72(4) (1995), 347–359, §1 and Proposition 1(a), (b), (c), (g), pp. 347–349. The paper defines the minus class group as the kernel of the relative norm and collects Hasse's results on the unit index (Sätze 14, 16–17, 25 and 27): $Q\in\{1,2\}$; no capitulation from $K^+$ to $K$ when $Q=2$; $Q=1$ when $K^+$ has units of every signature; $Q=2$ for $\mathbb Q(\zeta_m)$ with $m\not\equiv2\bmod4$ composite, proved from $(1-\zeta_m)^{1-\sigma}=-\zeta_m$. Retrieved 2026-11-24, SHA-256 `af477031783dfbf5aa96248c521f32c177da73eaa57019ce168279736b32b726`. [Journal scan](http://matwbn.icm.edu.pl/ksiazki/aa/aa72/aa7245.pdf)
- [Lemmermeyer2013] (above), Theorem 1, re-downloaded 2026-11-24 with the same SHA-256, is used only to check the two examples of §11.4.3.4 against the ambiguous class number formula.
- The [Chapter 11 source map](../chapters/11-the-window-bound-vwin.md#11434-signs-of-real-generators-and-the-binary-minus-defect) locates the sign proofs in the pinned Alpöge archive. The classical sources supply comparisons; the proofs in the chapter follow the archive.

### Chapter 11 §11.4.3.5 — unramified local unit norms

- **[MilneCFT]** J. S. Milne, *Class Field Theory*, v4.03 (2020), Ch. III, §1, Proposition 1.2 with Lemmas 1.3–1.5 and the proof, pp. 97–98. The norm $U_L\to U_K$ of a finite unramified extension of local fields is onto: the residue norm and trace are onto, and the principal-unit steps are iterated to a limit. This is the route the archive formalizes in `normIntegerUnits_surjective`. Re-downloaded 2026-11-25, SHA-256 `50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`. [Author PDF](https://www.jmilne.org/math/CourseNotes/CFT.pdf)
- **Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`**, `Mathlib/FieldTheory/Finite/GaloisField.lean:236` (`FiniteField.unitsMap_norm_surjective`; file SHA-256 `4adddf6dbdeb841074d2b6373bfa419aa47d23414f79906a65c589853b5cc6dd`) and `Mathlib/RingTheory/Trace/Basic.lean:521` (`Algebra.trace_surjective`; file SHA-256 `685fb38703fd188fd027acb4cd9d8d2ea79628a6a2c5c7435999d61986d0e9d9`), retrieved 2026-11-25 from raw.githubusercontent.com. The two finite-field inputs of the proof. Statements checked against the pinned source; proofs not read.
- The [Chapter 11 source map](../chapters/11-the-window-bound-vwin.md#11435-norms-of-local-units-in-unramified-extensions) locates the local-field proofs in the pinned Alpöge archive (joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`). The three calculations over $\mathbb Q_3$ are textbook exposition.

### Chapter 19 §19.3.1 Siegel-set control

**Chapter 19, §19.3.1.** A2 (joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`) supplies the Siegel-set Haar estimate and the weighted cone-integrability proof. The original production declarations and read boundaries are cited in the subsection. The rank-one calculations are textbook exposition. [Subsection](../chapters/19-published-layer-case-studies-ii.md#1931-siegel-sets-and-the-integrable-majorant)

### Chapter 19 rational covering

**[Borel1963]** Armand Borel, “Some finiteness properties of adele groups
over number fields,” *Publications Mathématiques de l'IHÉS* 16 (1963),
5–30. Original PDF retrieved 2026-11-23, SHA-256
`678a378a947a25edd682942539cc9d22de47e8e141db0a19dd124e5138d2fedc`.
Section 4.1 and Theorem 4.5, printed pp. 113–114, supply the comparison
between finitely many pieces of a fundamental set and rational
translations, including the extra overlap condition.
[Original PDF](https://www.numdam.org/item/PMIHES_1963__16__5_0.pdf)

**A2, §19.3.2.** The joined archive supplies the compact-tail induction,
parabolic slice and final absorption. [Subsection](../chapters/19-published-layer-case-studies-ii.md#1932-rational-reduction-and-the-covering-of-the-adelic-quotient)

| Reading | Declaration and source | Role and dependency boundary |
|---|---|---|
| R3 | `torus_zero`, `mul_mem_one`, `ratV_zero`, `nearMin_rat`, `step`, `hasRed_zero`, `hasRed_all`, `torus_neg`, `conj_mem_one`, `cov_main` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitarySiegelDomainExists.lean:26–265` | Entire covering production body, including closure, rank induction and adjustment on the fixed compact set |
| R3 | `ratV_injective`, `Sends.inv`, `hgt_mul` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RatVInjective.lean:41–58` | Pointwise tensor embedding, inverse action and transport of vector heights |
| R3 | `exists_pos_le_hgt` and `exists_nearMin` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsNearMinimalVector.lean:54–97` | Operator-bound and product-formula input, then the positive infimum and factor two |
| R3 | `exists_ratPts_sends_isotropic` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RationalUnitarySendsIsotropic.lean:16–55` | `WittPartner.full` and `HyperbolicPairTransitive.full` supply the isometry. Their internal proofs are outside this reading |
| R3 | `exists_sends_hE` and `hE_mulVec_self` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RationalUnitaryWittExtension.lean:12–41` | Rational matrices act on rational vectors and preserve self-pairing |
| R3 | `exists_sends_of_rat_mem_minPar` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MinimalParabolicScalesIsotropic.lean:11–61` | Extracts the rational matrix, descends its triangular action by injectivity and inverts the nonzero first diagonal entry |
| R3 | `exists_compact_iwasawa_of_frame` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryAdelicIwasawa.lean:11–17` | Assembles the two local compacts and keeps compactness and Iwasawa |
| R3 | `levi_cocompact` and `minParOne_cocompact` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MinimalParabolicRationalCompact.lean:22–54` | Assembly. The underlying `commutant_closed_subgroup_compact_quotient` and `UnipCocompact.unipMin_cocompact` are named supplies |
| R3 | `Fr.dec` and `exists_levi` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WittFrameReduceRank.lean:719–821` | Covers the final decomposition and assembly. `exists_fr_witt`, the `Fr.iG` base-change infrastructure, and `Fr.iG_tor` and `Fr.iG_comm` are used through their interfaces |
| R3 | `exists_isotropic_le` and `First.exp_neg_le` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ReductionTheoryHeightBound.lean:75–128` | Short-vector versus thick-part proof, then first-coordinate estimate. `small_height_vector_isotropic`, `unitary_points_height_bound_finite`, `unitary_points_height_bound_compact` and `torus_siegel_height_lower_bound` are supplied |
| R3 | `hgt_line`, `hgt_pair`, `upper_bound`, `Simple.simple_bound` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ReductionTheoryLowerBound.lean:110–170` and `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ReductionTheoryLowerBound.lean:199–346` | The pair-of-columns calculation and adjacent-coordinate estimate. `adelic_tensor_rational_approximation`, `compact_height_lower_bound`, `adelic_box_compact` and `compact_adelic_norm_bounded` are supplied |
| R3 | `unitary_siegel_domain_exists` at `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitarySiegelDomainExistsStatement.lean:8–9` and `SiegelRed.siegelCore` at `src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SiegelSetUnitary.lean:17–30` | Exact forwarding and cover field assignment |
| R3 | `siegelCore_holds` at `src/Development/WeilBound/CoreStatements/AbelianHeightsDuality/PublishedTheoremStatements/SiegelSetUnitaryHolds.lean:7–8` and `UpperTheory.Lit.siegelSetUnitary_of_core`, `UpperTheory.Lit.weilThetaConvergence` at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/WeilRepresentation/WeilTheta.lean:7–10` | Actual main-path wrappers |
| R3 | `weilThetaConvergence_of_siegelSet` at `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilThetaConvergenceOfSiegelSet.lean:23–54` | Reads the rational cover at line 38, followed by compact-conjugate and cone bounds |
| R3 | `exists_torus_section` at `src/Development/WeilBound/ThetaLifts/Reductions/SiegelAbs.lean:275–335` | Supplies continuity, additivity, section and kernel splitting through `exists_tau` |
| R2 | `PMod.map_mul_torus_of` at `src/Development/WeilBound/ThetaLifts/Reductions/SiegelParMod.lean:437` | Separate modulus computation |
| R3 | `GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le` at `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicMatrixSchwartzMajorantInvMulLeStatement.lean:12` and `GlobalTheory.T.siegelTorus_tsum_majorant_translatedRationalPoints_le` at `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelTorusTsumMajorantTranslatedRationalPointsLStatement.lean:12` | Direct proof bodies and application read in §19.3.3. Deeper arithmetic and analytic supplies remain open |

### Chapter 19 §19.3.3 lattice majorant

- NIST Digital Library of Mathematical Functions, §1.8(iv), equation
  (1.8.14), retrieved 2026-11-23. This gives the shifted periodization
  identity specialized to the Gaussian in the rank-one example.
  [Original](https://dlmf.nist.gov/1.8.E14)
- Gan–Qiu–Takeda, author version 3, §§1.7, 2.2 and 3.1, printed pp. 3, 8
  and 14, retrieved 2026-11-23. SHA-256
  `cde6b7ad22b974d4159f8cedd1e14a00bf4b05ec977ab750b54fdceb067adac5`.
  These passages specify the unitary convergent range used for comparison.
  [Author manuscript](https://arxiv.org/pdf/1207.4709v3)
- Pinned Lean archive, joined SHA-256
  `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
  The proof and consumer line citations are in the chapter. The deeper
  suppliers for the finite-place denominator and frame norm are read in §19.3.4. Integral-lattice counting and Schwartz–Bruhat support and decay remain statement-level inputs. [Subsection](../chapters/19-published-layer-case-studies-ii.md#1933-the-lattice-majorant-for-the-inverse-torus)

### Chapter 19 §19.3.4 finite support and Minkowski lattices

- **A2** (joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`). The subsection records the direct denominator, matrix, scaled norm and compact-translate production proofs with their full archive-relative paths and line numbers. [Chapter 19](../chapters/19-published-layer-case-studies-ii.md#1934-from-finite-support-to-a-fixed-minkowski-lattice)
- **Andrew V. Sutherland**, *18.785 Number Theory I*, Lecture 25 (29 November 2021), Definitions 25.1 and 25.7, Propositions 25.6 and 25.10. Restricted products, their local compactness and adelic scalar extension. Original PDF checked online 2026-11-24, SHA-256 `1941241af698ce35d40e63ce0b9bca1950514fb60866a30d098103ebef5bd4a5`. [MIT lecture notes](https://math.mit.edu/classes/18.785/2021fa/LectureNotes25.pdf)
- **James S. Milne**, *Algebraic Number Theory*, v3.08 (19 July 2020), Proposition 4.26, pp. 79–80. Integral ideal lattices via the embedding matrix. Original PDF checked online 2026-11-24, SHA-256 `24b83c789a89f25aebffb3cbe4ae5ca29edd0075acc072de093d140770630847`. [Author’s notes](https://www.jmilne.org/math/CourseNotes/ANT.pdf)
- **Gan–Qiu–Takeda**, arXiv:1207.4709v3, §2.2 and §3.1, pp. 8 and 14. Rechecked the definition of $d(n)$ and the classical convergence range quoted in §19.3.3. [Author preprint](https://arxiv.org/pdf/1207.4709v3)

### Chapter 19 §19.3.5 (2026-11-24)

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Supplies the finite-level characterization, majorant proof and theta consumers. The subsection pins the individual source lines and the scope of the reading. [Subsection](../chapters/19-published-layer-case-studies-ii.md#1935-a-common-finite-support-for-schwartz-majorants)
- **Gan–Qiu–Takeda**, arXiv:1207.4709v3, PDF SHA-256 `cde6b7ad22b974d4159f8cedd1e14a00bf4b05ec977ab750b54fdceb067adac5`, retrieved 2026-11-24. Section 2.1, p. 8, identifies the test space by restricted tensor products. Sections 2.2 and 3.1, pp. 8 and 14, give $d(n)$ and the Weil convergence range. [Author preprint](https://arxiv.org/pdf/1207.4709v3)
- **Andrew Sutherland**, MIT 18.785 Fall 2021, Lecture 25, PDF SHA-256 `1941241af698ce35d40e63ce0b9bca1950514fb60866a30d098103ebef5bd4a5`, retrieved 2026-11-24. Definition 25.7 and Proposition 25.10 give the place model and its classical base-change comparison. [Lecture notes](https://math.mit.edu/classes/18.785/2021fa/LectureNotes25.pdf)

### Chapter 19 §19.3.6 (2026-11-24)

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Supplies the tensor split, the CM chart and the real-parameter size proof. The subsection gives the exact source paths and reading boundaries. [Subsection](../chapters/19-published-layer-case-studies-ii.md#1936-compatible-adelic-coordinates-and-real-parameters)
- **Sutherland, Lecture 25** and **Gan–Qiu–Takeda**, at the versions recorded for §19.3.5. Definition 25.7 and Proposition 25.10 describe the classical adelic model. Sections 2.1 and 3.1 of the preprint give the Schwartz tensor convention and theta integral context. [MIT notes](https://math.mit.edu/classes/18.785/2021fa/LectureNotes25.pdf) · [Author preprint](https://arxiv.org/pdf/1207.4709v3)

### Chapter 19 §19.3.7 (2026-11-24)

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Supplies `weighted_count`, its cell and coordinate lemmas and the stacked call sites. The subsection pins the paths and lines; per-file hashes are in the run directory. [Subsection](../chapters/19-published-layer-case-studies-ii.md#1937-unit-cells-and-the-uniform-weighted-lattice-count)
- **Mathlib** at the pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`. `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean` (SHA-256 `66562d624f53b8d641de6ad75615d5f5e5d28d0bd8744710ce91de1d96b2b075`), lines 80–89, 112–136 and 164–178, gives `norm_le_iff`, `latticeBasis` and `integralBasis_repr_apply` (author Xavier Roblot). `Mathlib/NumberTheory/NumberField/Basic.lean` (SHA-256 `68833cc080857da33ed2661fac14c281651f140904af0fb587a447e23b81bac6`), lines 397–398, 406–409 and 415–416, gives `integralBasis`, `integralBasis_repr_apply` and `RingOfIntegers.rank` (authors Ashvni Narayanan and Anne Baanen). Retrieved 2026-11-24. [Canonical embedding](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean) · [Number fields](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/Basic.lean)
- **NIST DLMF**, equations 25.6.1, 5.15.1–5.15.5 and 2.10.1, retrieved 2026-11-24. They give $\zeta(2)$ and $\zeta(4)$, the trigamma values at integers and half-integers, and the first-order Euler–Maclaurin comparison. [§25.6](https://dlmf.nist.gov/25.6) · [§5.15](https://dlmf.nist.gov/5.15) · [§2.10](https://dlmf.nist.gov/2.10)
- **James S. Milne**, *Algebraic Number Theory*, v3.08, Propositions 2.26 and 4.26, pp. 34 and 79–80. The squared determinant of the embedding matrix of a basis is its discriminant, which is nonzero. Rechecked 2026-11-24, SHA-256 `24b83c789a89f25aebffb3cbe4ae5ca29edd0075acc072de093d140770630847`. [Author’s notes](https://www.jmilne.org/math/CourseNotes/ANT.pdf)
- **Eric W. Weisstein**, “Apéry’s Constant,” MathWorld, equation (1), retrieved 2026-11-24. It gives the decimal value of $\zeta(3)$ used in Example 2. [MathWorld](https://mathworld.wolfram.com/AperysConstant.html)

### Chapter 19 §19.3.8 (2026-11-24)

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Supplies the place identification `GlobalTheory.CMTypePlaces.mk_tauE_bijective` and its restriction `places_bijective` (`src/Development/AbelianVarietyTheory/Proofs/HeightProofs/CmTypeRestrictRealSubfieldInfinitePlaceBijective.lean:14–60`), the enumeration `factEmb` (`src/Formalism/LocalRingCardinality/RankBoundMonotoneInDimension.lean:516–522`) with `HostRaw.hostEmb` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean:258–266`), the host structures `HostRaw`, `HostDer` and `HostAx` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:12–175`) and `Host` (`src/Formalism/LocalRingCardinality/DataHost.lean:39–122`), and the separate proof `LevelSeries.mk_tauE_bij` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharInfinityEqCoeffMulHalfNormPow.lean:51–70`). The consumers are `SiegelConeIntegralMatrixLatticeCount.lean:145` and `ExistsInverseChart.lean:17`; the subsection gives the remaining lines.
- **Mathlib** at the pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`, files retrieved 2026-11-24: [InfinitePlace/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean) (SHA-256 `58a2b448c78accf9ca7dfe1490954e51ebf0b64e2f42f35adc71ebf91d309b87`; `mk_conjugate_eq` at line 108, `mk_eq_iff` at 144), [InfinitePlace/Embeddings.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean) (`1c387b8e514d0511c5a6164bc2c661d9de542114b6b56a67449626d8f2aa0634`; `conjugate_coe_eq` at 205), [CMField.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/CMField.lean) (`859821a8d728906bd029df2b8be1412c942cd0f94dda0e819e6dd424ff485ba2`; `IsCMField` at 71, `equivInfinitePlace` at 101–104) and [CanonicalEmbedding/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean) (`66562d624f53b8d641de6ad75615d5f5e5d28d0bd8744710ce91de1d96b2b075`; `conj_apply` at 65, `norm_le_iff` at 80, `latticeBasis` at 112).
- **J. S. Milne**, *Complex Multiplication*, v0.10 (14 July 2020), Definition 1.8, display (3) and the extension of CM types from a CM subfield, p. 11; Proposition 1.9, Corollary 1.10 and Exercise 1.11, p. 12. PDF retrieved 2026-11-24, SHA-256 `0ac337a885d72f6938f15724b897f568fe350d0d754d0b52370b8f3a01d2e2b5`. [Original PDF](https://www.jmilne.org/math/CourseNotes/CM.pdf)
- **Andrew V. Sutherland**, *18.785 Number Theory I*, Fall 2021, Lecture 13, Corollary 13.7, Definition 13.8 and Corollary 13.9, p. 3 (PDF SHA-256 `7d45006469b85335185189d0f6a783180e63907ea856e3931fccee0c89a514c8`), and Lecture 14, pp. 3–4, the real subspace $K_{\mathbb R}\subset K_{\mathbb C}$ (PDF SHA-256 `4e59e33ada17f0c8f74237723236ef738cdf74b215f80f7cf3eecd52de2f8206`). [Lecture 13](https://math.mit.edu/classes/18.785/2021fa/LectureNotes13.pdf) · [Lecture 14](https://math.mit.edu/classes/18.785/2021fa/LectureNotes14.pdf)
- **NIST DLMF**, equation 25.6.1, and **Eric W. Weisstein**, “Apéry’s Constant,” MathWorld, equation (1), rechecked online 2026-11-25, for $\zeta(2)$, $\zeta(4)$ and $\zeta(3)$ in the $\mathbb Q(i)$ calculation. [DLMF 25.6.1](https://dlmf.nist.gov/25.6.E1) · [MathWorld](https://mathworld.wolfram.com/AperysConstant.html)

### Chapter 19 §19.3.9 (2026-11-25)

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` (recomputed 2026-11-25). Supplies the raw and derived host structures and `DerOfRaw` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:12–175`, SHA-256 `db32b7af86f38a66…`), the general producer `HostRaw.der` and `HostAx.ofRaw` (`…/TotientGaloisClasses/InertiaGaloisSymmetry/OfRawToHostRaw.lean:9–44`, `0202439b2981a8e0…`), the producers `Der.cmType` and `Der.hostCore` (`…/InertiaGaloisSymmetry/CycAll.lean:14–59,90–106`, `1edbd1b0508a04e3…`), the lifting, cyclotomic-conjugation, `conj_apply`, `conj_iff`, `cm`, degree and `mem_F` proofs (`…/InertiaGaloisSymmetry/CycBasic.lean:17–187`, `5cc47b1f4efe246c…`), `HostCore` (`…/InertiaGaloisSymmetry/DecompTypeI.lean:12–60`, `f351d6679a5a5754…`), the frame group and signs (`…/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:15–18,87–116,137`), `HostHyp`, `G0` and `c0` (`src/Formalism/FrobeniusOrbits/Statement.lean:13–14,27,35`, `be6f07f572e21568…`), the second producer `hostDer` (`…/TotientGaloisClasses/NonemptyFieldAxiomsCyclicPow.lean:537,651`, `bf171e8d0eff1464…`), and the call sites `FieldChi.lean:54` (`784b9d6aed029254…`), `FieldAny.lean:39,47` (`1faafb8b112daf3a…`) and `ExistsHostAxEven.lean:10` (`3eea172feb69406c…`). Consumers as in §19.3.8 (`RankBoundMonotoneInDimension.lean:507–522`, `HostFacts.lean:258–266,274–277,340–344`, `DataHost.lean:39–62,120–122`). Full hashes are in the run directory. [Subsection](../chapters/19-published-layer-case-studies-ii.md#1939-the-host-fields-raw-data-derived-properties-and-their-producers)
- **Mathlib** at the pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`: [CMField.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/CMField.lean) (SHA-256 `859821a8d728906bd029df2b8be1412c942cd0f94dda0e819e6dd424ff485ba2`; `IsCMField` at 71–73, `of_forall_isConj` at 521–522, statement level) and [InfinitePlace/TotallyRealComplex.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean) (SHA-256 `ff3824921455594ba747cd0c5f807d6b6ba7776de4f21532afb5c1127293e5c2`; `mem_maximalRealSubfield_iff` at 136–137), files retrieved 2026-11-24; `isComplex_iff` and `isReal_iff` at `InfinitePlace/Basic.lean:206–209` and `InfinitePlace/Embeddings.lean:213` as pinned for §19.3.8. The cyclotomic Galois-group lemmas `galEquivZMod` and `adjoin_primitive_root_eq_top` are cited by name only.
- **J. S. Milne**, *Complex Multiplication*, v0.10 (14 July 2020), Proposition 1.4 and the definition of CM-fields, p. 10 (the three equivalent conditions; (b) is the unique complex conjugation). PDF re-retrieved 2026-11-25, SHA-256 `0ac337a885d72f6938f15724b897f568fe350d0d754d0b52370b8f3a01d2e2b5`, identical to the 2026-11-24 copy. [Original PDF](https://www.jmilne.org/math/CourseNotes/CM.pdf)
- **J. S. Milne**, *Algebraic Number Theory*, v3.08 (19 July 2020), p. 95 (the injective homomorphism $\operatorname{Gal}(\mathbb Q[\zeta]/\mathbb Q)\to(\mathbb Z/n\mathbb Z)^\times$, an isomorphism) and pp. 101–102 (under any embedding into $\mathbb C$, $\zeta^{-1}$ maps to the complex conjugate of $\zeta$; $\mathbb Q[\zeta]$ is a CM field with maximal totally real subfield $\mathbb Q[\zeta+\zeta^{-1}]$). PDF re-retrieved 2026-11-25, SHA-256 `24b83c789a89f25aebffb3cbe4ae5ca29edd0075acc072de093d140770630847`. [Author’s notes](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

### Chapter 8 §8.4.14 — `ea_RestSU` producers (2026-11-25)

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` (read-only archive). Supplies the complete proofs read in §8.4.14, per-file SHA-256 under `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/`: `EaRestSExpVOf.lean:1–274` (`f06bb82f70d6938a1184c5299cc3ab2f148a965ef0d8c510f1ea91a26f06f001`), `EaRestSExpV.lean:1–49` (`f9c6faf8cf99592d7a5905336a2051588f8e01e52fde82e297d666fb8e1a1c64`), `AtPiEqRescale.lean:1–73` (`d5975b42e3c58df7b300549791142820d72dceee4c864ff4897929697095879a`), `InParamMap.lean:1–145` (`91a6a86bddc600ab7b4e520d14f4374b7fd21f79f814f67d079db9f8710eadc8`), `IntRPsubst.lean:1–164` (`41c77429ee1e5b5c0a8c0273d9d3f3d82b46012b6cab703ad62f9bf3b4b68dfd`), `SubstitutionOfVariables.lean:1–259` (`e0956271883c6c36e7479c177723790d5d00a4f1cc31c9afcb7ce485bfb65798`), `NatCastInvMemRp.lean:1–86` (`845efcf947b65945b74f2853e14845f002ce043a1a4aec4e32ef18b49c2049dd`), `IntegralExpRename.lean:1–127` (`e85a105b18cd2d076180f40096215172a49e9419bc9b3dff09cd54e6191b5ed8`); statements in `DworkExponentialRestrictions.lean` (`216e1324dd292ff46a3ab84b6d0363e862acd57c50bbc107ed94673a700ba068`), `KernelExpansionOfRestrictions.lean` (`d9d1629cc9a4463b1bdc91bb5a20afb10c830be9d97527a500ea81aca24762a7`), `AllPlacesOfRestrictions.lean` (`4fd7b359489f848ee7294422964ec23bdc9f1558f51e7444896c5b2455124c75`), `ThRestGcVOf.lean` (`ece460f48b2d2f7d82f23fbf8124202949e0f774f7a5973deaad2700c6ff4ac2`), `EntryAOneParity.lean` (`8e3eec27c93447018c03e994ef5d8ebecaf200cdc65808cba5cb07bdc623bcb1`), `FirstTheoremPlaceBound.lean` (`63e27a4e322f0ca021a8c3a0a77fd49775373258b07b48658602af252a3d799e`), `../FormalGroupSystem.lean` (`6315fb0a32d369b39cabd61db614775b73d3fdc1c96395f4b7571e36a32ed666`), and `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/OddLogRelation.lean` (`b525022a133672071d91c1d9bcde85b26b943a74ec44328c467048f6805b0653`), `CyclicPowerClassOfExpEquiv.lean` (`1ec14f04cf377fbb985e8d13c518f0f491123bc110a23fbb0d25421f73995fc8`).
- **Mathlib (pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`)**, statements checked against the current Mathlib documentation on 2026-11-25 (docs built from commit `bce3fc3a37ff1790b2e3b0ccf8f941053aefde19`): `PowerSeries.substInvOfIsUnit`, `PowerSeries.subst_substInvOfIsUnit_right`, `PowerSeries.constantCoeff_substInvOfIsUnit`, `PowerSeries.rescale_eq_subst`, `PowerSeries.subst_comp_subst_apply` (`Mathlib/RingTheory/PowerSeries/Substitution.lean`); `MvPowerSeries.rescale`, `MvPowerSeries.coeff_rescale`, `MvPowerSeries.rescale_eq_subst`, `MvPowerSeries.subst_comp_subst_apply`, `MvPowerSeries.map_subst`, `MvPowerSeries.subst_mul`, `MvPowerSeries.HasSubst.smul_X`, `MvPowerSeries.hasSubst_of_constantCoeff_zero` (`Mathlib/RingTheory/MvPowerSeries/Substitution.lean`); `MvPowerSeries.invOfUnit`, `MvPowerSeries.mul_invOfUnit` (`Mathlib/RingTheory/MvPowerSeries/Inverse.lean`); `sub_one_mul_padicValNat_factorial` (`Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`; in current Mathlib a deprecated alias, since 2026-10-28, of `Nat.Prime.sub_one_mul_multiplicity_factorial`); `WittVector.isUnit_of_coeff_zero_ne_zero` (`Mathlib/RingTheory/WittVector/DiscreteValuationRing.lean`). File headers at the pinned commit: the two `Substitution.lean` files by Antoine Chambert-Loir and María Inés de Frutos Fernández; `MvPowerSeries/Inverse.lean` by Johan Commelin and Kenny Lau.
- **[Dwork1960]**, **[Hazewinkel1978]** (§6): classical background for the valuation $1/(p-1)$ of $\pi^{p+1}$ and the functional-equation shape of the logarithm `logF`.

### Chapter 4 §4.10.5, far-range numerical absorption

- **Archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. `num_alg`, the two helper lemmas and `num_main` in `PNTBAsmA.lean:7–63,88–158` are read in full; the consumer `psi_relative_far_range`, `etaOf_lower`, `glue_ranges` and the interface definitions keep the reading of §4.10. The eight cited files (`PNTBAsmA`, `PNTBAsm`, `PNTBAsmB`, `DeuringHeilbronnM`, `PNTEOf`, `PNTGlue`, `PNTRangeA`, `PNTFinal`) were compared byte for byte with the archive tarball on 2026-11-24. [Subsection](../chapters/04-auxiliary-prime-pairs-and-host-fields.md#4105-the-far-range-numerical-absorption-lemma-num_main)
- **Mathlib** at commit `0df444a360eaa60ab8c11dca51a86af692955474`, pinned by the archive: `Real.log_le_sub_one_of_pos` (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:307`), `Real.rpow_def_of_pos` and `Real.rpow_natCast` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:51,62`) and `Real.exp_one_lt_d9` (`Mathlib/Analysis/Complex/ExponentialBounds.lean:38`), checked by statement. Files retrieved 2026-11-24, SHA-256 `1f36a9802233e878953d809b16e020beaf0ace5afd4c8279d47b52af6ee186bf`, `1f4e64fc28a20f4e19291a94dafd68daa82588b46f6ee5b9203df373ba595fa3` and `690c5e4fb7f5dcea80acf0ff8f22fb6c10c74ea61b3ac337fa801685be3e0e25`. [Mathlib at that commit](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)
- **[Gallagher1970]**, metadata only. Crossref record retrieved 2026-11-24 (SHA-256 `bd46e09f3c0332db8f103069a2558fc246dcb1c6c85d8c146808d34e2a9f44e4`): *Invent. Math.* 11, no. 4, pp. 329–339, December 1970. The Springer article page shows the same volume and pages; the full text is paywalled and was not read. [Publisher](https://doi.org/10.1007/BF01403187)
- **[Tao2015]**, read for Theorem 2, Exercise 5 and its hint (the $\log^2x$ versus $\log^2q$ remark and the bound $\Lambda(n)\le\log n$). The notes link Gallagher's theorem to MR0279049 and the treatment to Chapter 18 of Iwaniec–Kowalski (MR2061214). Retrieved 2026-11-24, SHA-256 `c6db99bae3d078922b9cccc001041be70543008703a59947ddc2d18cc1f1283a`. [Notes](https://terrytao.wordpress.com/2015/02/22/254a-notes-7-linniks-theorem-on-primes-in-arithmetic-progressions/)
### Chapter 1, §1.3.2 — Dirichlet series and the Hurwitz sum

- The fixed Mathlib implementation supplies the residue-class grouping, the
  common-pole subtraction and the two differentiability wrappers.
  [ZMod.lean:70–144](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L70-L144),
  [DirichletContinuation.lean:61–100](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L61-L100),
  [HurwitzZetaEven.lean:630–650](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L630-L650).
- The NIST Digital Library of Mathematical Functions gives the classical
  Hurwitz series, the finite Dirichlet L-function formula and the value at
  zero. [DLMF 25.11.1](https://dlmf.nist.gov/25.11.E1),
  [25.15.3](https://dlmf.nist.gov/25.15.E3),
  [25.11.13](https://dlmf.nist.gov/25.11.E13).

**Even Hurwitz continuation.** [Chapter 1 §1.2.2.1](../chapters/01-statement-and-fidelity.md#1221-how-the-theta-integral-produces-the-even-hurwitz-pole) maps the local proof to the pinned Mathlib
theta kernels, the abstract functional-equation pair, and its Mellin suppliers.
[Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean:334–369](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean#L334-L369) · [Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean:630–642](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean#L630-L642)

NIST DLMF, §25.11(i), (v), online edition retrieved 2026-11-23. The classical series,
pole and zero-argument value supply independent comparisons for the two shifts.
[DLMF §25.11](https://dlmf.nist.gov/25.11) · [DLMF 25.11.13](https://dlmf.nist.gov/25.11.E13)

**Chapter 1, §1.3.2.1.** David Loeffler's odd Hurwitz development in the
pinned Mathlib source constructs the signed theta kernels, their Mellin transforms
and the completed reflection. The corresponding odd finite-sum consumer is
in ZMod.lean, with the character specialization in DirichletContinuation.lean.
Retrieved 2026-11-23. The odd Hurwitz source has SHA-256
cce8ee2bc4e5329f8931146110e9e54c7a230a89dcdee0012d0131f5019033bd. [HurwitzZetaOdd](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean#L302)
· [ZMod](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/ZMod.lean#L432)
· [DirichletContinuation](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L303)

NIST DLMF v1.2.8, consulted 2026-11-23, gives the independent classical
Hurwitz zero-value check and the primitive character functional equation in
ordinary normalization. [DLMF 25.11.13](https://dlmf.nist.gov/25.11.E13)
· [DLMF 25.15.5](https://dlmf.nist.gov/25.15.E5)

### Chapter 1, §1.2.2.2 — Removable values and reciprocal Gamma

- Mathlib at the A2 manifest pin, `0df444a360eaa60ab8c11dca51a86af692955474`, retrieved 2026-11-24. Yury Kudryashov's removable-singularity file produces the differentiable update from the divided difference. David Loeffler's Gamma files produce the entire reciprocal and the Deligne normalization. The Hurwitz file uses them at zero and subtracts the common pole at one. The zeta asymptotics file by David Loeffler and Terence Tao identifies the actual value at one. [Fixed proof locations and reading boundary](../notes/proof-map.md#p1-chapter-1-removable-values)
- NIST Digital Library of Mathematical Functions, v1.2.8, retrieved 2026-11-24. The Gamma pole and reciprocal conventions, half-argument digamma value, Laurent expansion at one, and classical Hurwitz zero value give independent checks of the normalizations. The book's total-function assignment at one comes from Mathlib. [DLMF §5.2](https://dlmf.nist.gov/5.2) · [DLMF 5.4.13](https://dlmf.nist.gov/5.4#E13) · [DLMF 25.2.4–5](https://dlmf.nist.gov/25.2#E4) · [DLMF 25.11.13](https://dlmf.nist.gov/25.11#E13)

### Chapter 1, §1.2.2.3 — Laurent constant at one

- Mathlib at the A2 manifest pin, `0df444a360eaa60ab8c11dca51a86af692955474`, files retrieved from that commit 2026-11-24 (SHA-256 of each in the run directory). David Loeffler's `EulerMascheroni.lean` defines $\gamma$ as the limit of `harmonic n - log (n+1)` and proves $1/2<\gamma<2/3$. The zeta asymptotics file by David Loeffler and Terence Tao evaluates the Euler-summation error sum at $s=1$ and $s>1$, proves its continuity, obtains the right-real limit $\gamma$ of $\zeta(s)-1/(s-1)$, transfers it to the punctured complex neighborhood, and identifies `riemannZeta 1`. The derivative of the Deligne factor at one is in `GammaDeriv.lean`. [EulerMascheroni.lean:48–172](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean#L48-L172) · [ZetaAsymp.lean:61–450](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean#L61-L450) · [GammaDeriv.lean:180–227](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/GammaDeriv.lean#L180-L227) · [Fixed proof locations and reading boundary](../notes/proof-map.md#p1-chapter-1-laurent-constant-at-one)
- NIST Digital Library of Mathematical Functions, v1.2.8, retrieved 2026-11-24. The digamma series and Gauss's rational-argument formula give the classical check $-\psi(1/4)=\gamma+3\log 2+\pi/2$ of the quarter-shift Laurent constant; the Stieltjes expansion names $\gamma_0=\gamma$. These are independent comparisons, not formalized in the pinned Mathlib. [DLMF 5.7.6](https://dlmf.nist.gov/5.7#E6) · [DLMF 5.4.19](https://dlmf.nist.gov/5.4#E19) · [DLMF 5.4.13](https://dlmf.nist.gov/5.4#E13) · [DLMF 25.2.4–5](https://dlmf.nist.gov/25.2#E4)

### Chapter 1, §1.2.2.4 — Derivative of Gamma at one half

- Mathlib at the A2 manifest pin, `0df444a360eaa60ab8c11dca51a86af692955474`, files retrieved from that commit 2026-11-25 (SHA-256 of each in the run directory; `GammaDeriv.lean` byte-identical to the §1.2.2.3 copy). David Loeffler's `GammaDeriv.lean` proves $\Gamma'(n+1)=n!(H_n-\gamma)$ from the log-convexity of $\Gamma$ and the harmonic limit, $\Gamma'(1/2)=-\sqrt\pi(\gamma+2\log2)$ from Legendre's duplication formula, transports both to the complex function and derives the derivatives of the Deligne factors $\Gamma_{\mathbb R}$ and $\Gamma_{\mathbb C}$ at one. The log-convexity (Bohr–Mollerup file), the duplication formula (Beta file) and $\Gamma(1/2)=\sqrt\pi$ (Gaussian integral) are used as named inputs. [GammaDeriv.lean:32–228](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Harmonic/GammaDeriv.lean#L32-L228) · [BohrMollerup.lean:111–119](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean#L111-L119) · [Beta.lean:559–601](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L559-L601) · [Fixed proof locations and reading boundary](../notes/proof-map.md#p1-chapter-1-derivative-of-gamma-at-one-half)
- NIST Digital Library of Mathematical Functions, v1.2.8, retrieved 2026-11-25. The digamma values $\psi(1)=-\gamma$, $\psi(1/2)=-\gamma-2\ln2$, the integer and half-integer formulas, the recurrence $\psi(z+1)=\psi(z)+1/z$ and the duplication formula are the classical comparisons for the hand calculations at $1/2$ and $3/2$; the half-integer formula is not formalized in the pinned Mathlib. [DLMF 5.4.12–15](https://dlmf.nist.gov/5.4#E12) · [DLMF 5.5.2](https://dlmf.nist.gov/5.5#E2) · [DLMF 5.5.5](https://dlmf.nist.gov/5.5#E5) · [DLMF 5.4.6](https://dlmf.nist.gov/5.4#E6)

### Chapter 6 §§6.4.9–6.4.13 — stabilizer, finite-order and pro-$g$ supplies

**Chapter 6 §6.4.9 (2026-11-23 CST).** A2 joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The published background for the simple-root lifting step is the Stacks Project, Étale Cohomology, §59.32, Definition 59.32.2 and Theorem 59.32.3, consulted online. The completed valuation ring is complete for the maximal-ideal topology and the derivative of the quadratic is a residue unit, the hypotheses used here. [Original text](https://stacks.math.columbia.edu/tag/03QD)

**Chapter 6 §6.4.10 (2026-11-23).** A2 supplies the formal local torsion and finite-stabilizer proofs with the joined archive SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc.

**Chapter 6 §6.4.11 (2026-11-24).** A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, supplies the formal production and transport proofs. The Stacks Project, §5.22, Definition 5.22.1 and Lemma 5.22.2, live online version retrieved 2026-11-24, supplies the compact totally disconnected characterization used for background. Haruzo Hida, *p-adic ordinary Hecke algebras for GL(2)*, Annales de l’Institut Fourier 44 (1994), 1289–1322, p. 1298, original journal PDF retrieved 2026-11-24, gives the invertibility/topological nilpotence convention for ordinary projectors. Retrieved SHA-256 values are `7aaef08d0216803b398bcd51fd364f3a479b982912a2042eabf6d0600b9bd395` (Stacks HTML) and `95e8ab3b25ef04537ee85cca6374b92efa7714007e0274b2704cae2a7bba1e45` (Hida PDF). [Stacks §5.22](https://stacks.math.columbia.edu/tag/08ZW) · [Hida 1994](https://www.numdam.org/item/AIF_1994__44_5_1289_0.pdf)

**Chapter 6 §6.4.12 (2026-11-24).** A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, supplies the formal definite adelic and host degree proofs. Keith Conrad, *Cyclotomic Extensions*, p. 10, §5, Theorem 5.3, undated online notes retrieved 2026-11-24, gives the prime-power cyclotomic formula, its Eisenstein translate and the degree consequence used for the textbook bounds. PDF SHA-256 `2962191954ae1903a827393dd9aeba758e18af65671ee021992bb80fa164ad7a`. [Original notes](https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf)

**Chapter 6 §6.4.13 (2026-11-24).** A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, supplies the formal homeomorphism, Iwahori pro-$g$ and transport proofs. Keith Conrad, *Field automorphisms of R and Q_p*, undated online notes, §6, Theorem 6.1 and Corollary 6.3, pp. 5–6, retrieved 2026-11-24 15:00 UTC, prove by Hensel's lemma that field homomorphisms between finite extensions of $\mathbb Q_p$ are isometries and that endomorphisms are continuous automorphisms. PDF SHA-256 `ec5cc92673ec8579e49c9943ff8c55c156923e249e3bb75d9ca3c17985df3add`. [Original notes](https://kconrad.math.uconn.edu/blurbs/gradnumthy/autRandQp.pdf) Benjamin Klopsch, *Five Lectures on Analytic Pro-p Groups*, LMS-EPSRC Short Course notes (Oxford, 2007), Section 8, p. 32 and Proposition 8.1, retrieved 2026-11-24, state that $G_1=1+p\,\mathrm{Mat}_d(\mathbb Z_p)$ is the kernel of reduction and a pro-$p$ group. PDF SHA-256 `8ea2625fb3527301289edb411442c536cc9f070a33c9d0973399a3626523563a`. [Lecture notes](https://www.math.uni-duesseldorf.de/~klopsch/mathematics/Manuskripte/analytic_groups.pdf) Stacks Project §5.22, Lemma 5.22.2, consulted online 2026-11-24, HTML SHA-256 `7aaef08d0216803b398bcd51fd364f3a479b982912a2042eabf6d0600b9bd395`. [Stacks 08ZW](https://stacks.math.columbia.edu/tag/08ZW)

### Host Gram definiteness

**A2 [Lean, read].** SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The core proofs are `src/Formalism/SharpRestriction/GlobalSchurBounds/JointsL.lean:412–565`, including the negative branch at :563–565. The host Gram inputs are in `src/Formalism/LocalRingCardinality/DataLevel.lean:48–52,77–82`. The definitions of signature and definiteness are `src/Formalism/SatakeDualWeyl/Statement.lean:104,483–486` and `src/Formalism/SharpRestriction/GlobalSchurBounds/CMFieldLemmas.lean:135–140,194–197`. The distinct family consumers are `src/Formalism/SharpRestriction/GlobalSchurBounds/JointsF.lean:90–93,125–132`. Their instances use `gram0Def` in `JointsL.lean:571–573,1169–1172`. [Chapter 6 §6.4.14](../chapters/06-stepanovs-method-and-multiplicity.md#6414-definiteness-of-the-host-gram-matrix-at-real-embeddings)

**Milne [Paper].** J. S. Milne, *Fields and Galois Theory*, v5.10, September 2022, Theorem 6.6, p. 90. Read on 2026-11-25. The embedding extension proof uses the minimal polynomial at each adjunction and a maximal extension for arbitrary algebraic extensions. PDF SHA-256 `5c43ea0bf4ec190b819727fe720414a80e09f9e762533d08bad5b8a0b6de7273`. [Author's PDF](https://www.jmilne.org/math/CourseNotes/FT.pdf)

**Mathlib embedding lift [Lean, read] (2026-11-25).** Pinned Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Proof bodies read: `IsAlgClosed.lift`/`liftAux` (`Mathlib/FieldTheory/IsAlgClosed/Basic.lean:324–357`, SHA-256 `4aa5c7c0a9a17d356d084bfabe5a2a54c0fa108ef3a90282e23961710cf06643`); the Zorn, chain-union and single-root steps (`Mathlib/FieldTheory/Extension.lean:35–138, 208–228, 297–317, 364–373`, SHA-256 `d096b49a470ecf91e0dc5a3256739ae71dc80e0149405342a2b00eb1d9d5e336`); `algHomAdjoinIntegralEquiv` (`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:600–609`, SHA-256 `657f34bb6b19d57cf1f96dec3ded1265ac6133675d6fd7c769a71eb31223df7b`); `PowerBasis.lift`, `lift_gen`, `liftEquiv'` (`Mathlib/RingTheory/PowerBasis.lean:287–331`, SHA-256 `e4ecfdc08c66dbf032614ff045f408cc7edb771263d76ad7be216f55bb0ed840`); `rootOfSplits` (`Mathlib/Algebra/Polynomial/Splits.lean:274–292`, SHA-256 `09540ced6c5feebb7f9cddc7c01f1ae7f4102a147e2242ebec12378c43701713`); `RingHom.injective` (`Mathlib/RingTheory/SimpleRing/Basic.lean:67–70`, SHA-256 `a7533e6639806f0905b9a31bcf07efcc046137eaf607b99257afcfdc43d60a25`); `Algebra.IsAlgebraic.of_finite` and `Module.finite_of_finrank_pos` (`Mathlib/RingTheory/Algebraic/Integral.lean:101–109`, SHA-256 `274fa0e1081281ec183227917b8b2ae1004b8ce5bd3c0e33dd35669def0d80fa`; `Mathlib/LinearAlgebra/Dimension/Free.lean:272–274`, SHA-256 `b397ec5589984e2705973863705657bcbd82f4c9826670b3b1bf878cd795970a`). The consumer is `exists_ext` at A2 `src/Formalism/SharpRestriction/GlobalSchurBounds/JointsL.lean:489–492`, called at :501; the algebraicity premise is produced at :544–545 from `deg2`. `Complex.isAlgClosed`, the fraction-ring glue and `algHomEquivSigma` are cited by statement only. Milne, *Fields and Galois Theory*, Theorem 6.6, p. 90 (same PDF and SHA-256 as above, re-downloaded 2026-11-25) and the Stacks Project, Tag 09GU, consulted online 2026-11-25, give the published argument; Mathlib's chain formulation cites I. M. Isaacs, *Roots of polynomials in algebraic extensions of fields*, Amer. Math. Monthly 87 (1980), 543–544, DOI 10.1080/00029890.1980.11995085, checked against Crossref. [Pinned `Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IsAlgClosed/Basic.lean#L324-L357) · [Pinned `Extension.lean`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Extension.lean#L297-L317) · [Stacks 09GU](https://stacks.math.columbia.edu/tag/09GU) · [Chapter 6 §6.4.15](../chapters/06-stepanovs-method-and-multiplicity.md#6415-extending-a-real-embedding-to-the-host-field-the-algebraically-closed-lift)

### P16 integral expansion of virtual characters

- **Alpöge archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. §13.4.11 reads the direct constituent, quotient and coordinate transports and the zero/direct-sum witness used by `mem_virt_iff_sub`. Full paths and read boundaries appear in the chapter. Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`. [§13.4.11](../chapters/13-greens-theorem-and-the-literature-layer.md#13411-why-virtual-characters-have-integral-coefficients)
- **Pavel Etingof et al., Introduction to Representation Theory**, arXiv:0901.0827, Theorem 3.1, pp. 33–34. The lecture notes give the averaged projection proof of Maschke's theorem. Retrieved 2026-11-24, PDF SHA-256 `30325e113dcd5d9d6153cb257e1dfca8f44df19ce8d0c3019df63563ac1e0a3c`. [Lecture notes](https://arxiv.org/pdf/0901.0827)
- **J. A. Green, 1955**, p. 402, introduction. The generalized-character norm and degree criterion is stated there. Original checked online 2026-11-24, PDF SHA-256 `ded2dbd2e6fa499b64fe4c857ddaa8daf4ee4f74eef135958e4a40a02e6cac3d`. [AMS original via Internet Archive](https://web.archive.org/web/20250730054741id_/https://www.ams.org/journals/tran/1955-080-02/S0002-9947-1955-0072878-2/S0002-9947-1955-0072878-2.pdf)

### Chapter 13 §13.4.12 — naming laws, `PM.greenCuspidal`, and label well-definedness (2026-11-25)

- **Alpöge archive A2**, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` (read-only archive). §13.4.12 reads at R3 the coordinate-free naming laws `UpperTheory.Zero.LLC.nameLaws` (`NameLaws.lean:11–123`) with its Parseval-plus-shift pinning `UpperTheory.Zero.LLC.pin` (`PinNum.lean:7–253`, `PinFld.lean:9–194`, `PinChar.lean:10–133`, `PairCheckThreeTwo.lean:8–179`), central scalar law `nameCentral` (`NameCentral.lean:15–108`), and local-Langlands consumers `parEx` (`CentralUnit.lean:39–202`) and `parUniq` (`ParUniq.lean:15–53`); the representation-level parametrization `PM.greenCuspidal` (`HarishChandraModules.lean:12–13`, `GreenCuspidal.lean:12–304`, `LabelMapNonempty.lean:18–132`, `ExistsCuspidalWithLabel.lean:57–135`, `CuspidalParametrization.lean:22–72`), all-primes Newton power-sum uniqueness (`CuspidalLabelUnique.lean:118–406`, `CuspidalLabelPolynomialUniqueAllPrimes.lean:17–159`), and the three main-path consumers `GreenSeries.green_series` (`ProdFactorsOfMonic.lean:67–351`, `BridgesAut.lean:49–50`), `cuspParam_of_green` (`CuspParamOfGreenParametrisation.lean:20–138`), and `exists_perm_deg` / `exists_perm` / `eSer_eq` (`AdmissibleLabelWeightsOfGreenCuspidalParametrisa.lean:33–250`). All 29 cited archive files were hashed byte for byte and checked in exact cyclotomic arithmetic by `verify_green_label_laws.py` (SHA-256 `e43b46e58003067e5b1b7ead17448be9243cfd2a2c7b9fee50c4b5cdde8ea1fc`, 2,728 assertions passed). [§13.4.12](../chapters/13-greens-theorem-and-the-literature-layer.md#13412-naming-laws-pmgreencuspidal-and-label-well-definedness-across-consumers)
- **Mathlib** at pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`, retrieved 2026-11-25: `Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean` (SHA-256 `ba070370c584d7bb748403346989c34403dc33e8b338d44f1bcd5a6016ca74e6`, `esymm` at lines 70 and 195, `psum` at line 344; authors Hanting Zhang and Johan Commelin), `Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean` (SHA-256 `50070f0cc1d7b518705395356b56a3f31e8a63136974c51dda0040c7ee3b8d9a`, `mul_esymm_eq_sum` at line 225; author Michael Lee), and `Mathlib/Data/ZMod/Basic.lean` (SHA-256 `c910cf5089e3f961c495763c0a6c9609bcb8033f500faa1e7e4f0666f7eb5f99`, `RingHom.ext_zmod` at line 1096; author Chris Hughes). [Symmetric/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean) · [NewtonIdentities.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean) · [ZMod/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/ZMod/Basic.lean)
- **[Green1955]** J. A. Green, *Trans. Amer. Math. Soc.* 80(2) (1955), 402–447: §7 Definition 7.3 ($k$-simplexes, p. 438), Lemmas 7.4–7.7 and Theorems 12–13 (primary/cuspidal characters and elliptic orbit values, pp. 439–442), and §8 Lemma 8.3 and Theorem 14 (parabolic compound characters, pp. 443–445). Verified online 2026-11-25 against the Wayback AMS PDF (`ded2dbd2e6fa499b64fe4c857ddaa8daf4ee4f74eef135958e4a40a02e6cac3d`). [AMS original via Internet Archive](https://web.archive.org/web/20250730054741id_/https://www.ams.org/journals/tran/1955-080-02/S0002-9947-1955-0072878-2/S0002-9947-1955-0072878-2.pdf)
- **[BushnellKutzko1993]** C. J. Bushnell and P. C. Kutzko, *The Admissible Dual of GL(N) via Compact Open Subgroups*, Annals of Mathematics Studies 129, Princeton University Press, 1993, Chs. 5–6 (depth-zero simple types and unramified elliptic tori, background for `NameLaws` and `CentralUnit.parEx`).
### Cyclotomic arithmetic in Chapter 5

- **J. S. Milne**, *Algebraic Number Theory*, v3.08 (July 19, 2020), Proposition 6.2 (pp. 96–98), Remark 8.12 (p. 140), pp. 141–142 and Example 8.18 (p. 143). These give the prime-power cyclotomic calculation, the decomposition and inertia conventions, and the unramified power action. Retrieved 2026-11-23. SHA-256 `24b83c789a89f25aebffb3cbe4ae5ca29edd0075acc072de093d140770630847`. [Course notes PDF](https://www.jmilne.org/math/CourseNotes/ANT.pdf)
- **Alpöge with Claude**, pinned archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The reduction-of-roots and host identification bodies and their P6 consumers are indexed in [Chapter 5 §5.3.1.2](../chapters/05-the-square-root-barrier-core-gm.md#5312-frobenius-and-inertia-in-the-cyclotomic-host).

### Chapter 5, second host sign

- **Alpöge with Claude**, joined Lean archive A2. The algebraic Gauss-sum, descent, sign-recovery and consumer proofs are indexed by file and line in [§5.3.1.3](../chapters/05-the-square-root-barrier-core-gm.md#5313-the-second-host-sign-from-a-quadratic-gauss-sum).
- **Mathlib contributors**, `Mathlib/NumberTheory/GaussSum.lean` at the archive's manifest revision `0df444a360eaa60ab8c11dca51a86af692955474`, retrieved 2026-11-23, SHA-256 `710816aacd15b8bed8b0821bb47ae2da7f2d7b2219df487688ca7cef753b5186`. Lines 71–86, 166–201 and 222–228 supply the finite-field shift, product and square. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/GaussSum.lean)
- **J. S. Milne**, *Algebraic Number Theory*, v3.08, retrieved 2026-11-23, SHA-256 `24b83c789a89f25aebffb3cbe4ae5ca29edd0075acc072de093d140770630847`. Page 101 discusses the quadratic subfield for 23 and the splitting of 2. Example 8.19 and pp. 143–144 give the classical Frobenius comparison, reciprocity and the supplementary law. [Original notes](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

### Quadratic reciprocity and the host splitting signs (§5.3.1.4)

The archive calls and their line references appear in [Chapter 5](../chapters/05-the-square-root-barrier-core-gm.md#5314-quadratic-reciprocity-and-the-host-splitting-signs). The following Mathlib sources were read at manifest revision `0df444a360eaa60ab8c11dca51a86af692955474`, retrieved 2026-11-23.

- **Mathlib**, `Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean`. The prime-factor product, vanishing criterion, sign and double multiplicative extension. SHA-256 `24c6610d4c75840dee9d22a664291e53bcfa5db41627bf69bdccda55d8543dfd`. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean)
- **Mathlib**, `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`. Prime specialization and the equal-prime zero branch. SHA-256 `24ffbf256f6f6f7a2617901323c2d532e2d7871c826a8b11f0580b283e994302`. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean)
- **Mathlib**, `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean`. Finite-field quadratic-character identities behind prime reciprocity and the supplement at two. SHA-256 `54c2a184b863d6047a87a2686b1a2ba818a4374f274f519260939dcfef74428b`. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean)
- **Mathlib**, `Mathlib/NumberTheory/GaussSum.lean`. Frobenius power, nonzero cancellation and the explicit eighth-root sum. SHA-256 `710816aacd15b8bed8b0821bb47ae2da7f2d7b2219df487688ca7cef753b5186`. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/GaussSum.lean)
- **Mathlib**, `Mathlib/NumberTheory/LegendreSymbol/Basic.lean`. Legendre specialization, zero value and the supplement at minus one. SHA-256 `e719ed31ee33a23d312f2747347358da79cfee90d2ba6a8ed0de81b1aa6cd47b`. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/Basic.lean)
- **Mathlib**, `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean`. The finite-field proof of the value at minus one. SHA-256 `1c6b797c79503a628561d498d1ee26e6ff516e082d889df2d15fc8f9f56f6d61`. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean)
- **Mathlib**, `Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean`. The sign characters modulo four and eight and their evaluation. SHA-256 `91650588effef6e496df87468c8410a9d82a15bb98e131711e17ff26502c9f43`. [Pinned source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean)
- **J. S. Milne**, *Algebraic Number Theory*, v3.08, pp. 101, 143–144. The splitting example at 23 and the classical prime reciprocity and eighth-root comparison. Retrieved 2026-11-23, SHA-256 `24b83c789a89f25aebffb3cbe4ae5ca29edd0075acc072de093d140770630847`. [Original notes](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

### Chapter 5 Euler criterion sources

Retrieved 2026-11-23. Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474` from the A2 manifest.

- Field cardinal parity, unit-group exponent and square test (SHA-256 `536872e588f1ed90ea0bc359ae5997a84e777eff71c5bdf04517156b5861628f`). [Mathlib/FieldTheory/Finite/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Basic.lean)
- Both quadratic-character power identities and multiplicativity (SHA-256 `1c6b797c79503a628561d498d1ee26e6ff516e082d889df2d15fc8f9f56f6d61`). [Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean)
- Cyclic additive kernel, primitive-root construction and trace composition (SHA-256 `19b06c1956274e1e66ecafbcf1c0436fb44af084eac2e903cbcd1271140d808d`). [Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean)
- Actual calls to the additive interface (SHA-256 `710816aacd15b8bed8b0821bb47ae2da7f2d7b2219df487688ca7cef753b5186`). [Mathlib/NumberTheory/GaussSum.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/GaussSum.lean)
- Integer-sign recovery and application of the primed formula (SHA-256 `54c2a184b863d6047a87a2686b1a2ba818a4374f274f519260939dcfef74428b`). [Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean)
- **Keith Conrad, Finite Fields**, pp. 1–2, Theorems 1.1 and 1.5, Lemma 1.6 and Example 1.7. Classical finite-field background and the polynomial model for the field of order nine. The online copy carries no version number (SHA-256 `f27e8da415a99d96761797c95ba34a547c81b0150b43a8995e1b1238db109c2a`). [Original](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf)

### Chapter 5 cyclic multiplicative groups

The A2 archive at `/Volumes/UGREEN-WD_BLACK4TB/Projects/Active/RH-lean-archive/lean.tar.gz` has SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Its `lean/lake-manifest.json:10,13` fixes Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. Mathlib paths below are relative to that pinned repository root. Retrieved 2026-11-24. R3 is a local reading of the listed bodies.

| Full repository path and lines | Declaration and use |
|---|---|
| Mathlib/RingTheory/IntegralDomain.lean:118–154 | R3 for `card_nthRoots_subgroup_units`, `isCyclic_of_injective_ringHom`, the instance for finite units and `isCyclic_subgroup_units`. The injection bounds the solution set by the polynomial multiset; the instances supply unit coercion or its composition with subgroup inclusion. |
| Mathlib/Algebra/Polynomial/Roots.lean:58–78,352–383 | R3 for the root multiset wrapper, `card_roots`, `nthRoots`, `mem_nthRoots` and `card_nthRoots`. The positive-index polynomial has degree $n$. The zero-index proof uses the convention that the zero polynomial has an empty root multiset and the degree bound for constants otherwise. |
| Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:59–149 | R3 for `card_pow_eq_one_eq_orderOf_aux`, both `card_orderOf_eq_totient_aux` bodies and `isCyclic_of_card_pow_eq_one_le`. Strong induction computes the count when a divisor is attained. Erasing a missing divisor then contradicts the partition of the full group by exact order. |
| Mathlib/GroupTheory/SpecificGroups/Cyclic/Basic.lean:31–33,111–127,200–203 | R3 for generator extraction from `IsCyclic`, the order/cardinality criterion and its direction from a generating witness. The latter rewrites the subgroup to top. |
| Mathlib/GroupTheory/OrderOfElement.lean:175–181,263–277,570–576,835–845,864–869,939–944,1101–1103,1143–1167,1185–1192 | R3 for order as a minimal period, divisibility and its converse, the finite powers equivalences, the partition of solutions by order, conversion from integer to natural powers, the Fintype powers cardinality and divisibility by group cardinality. The quotient-product equivalence supplies the coset count. |
| Mathlib/Dynamics/PeriodicPts/Defs.lean:150–155,343–360 | R3 for remainder of a period and divisibility by the minimal period. A positive putative remainder contradicts minimality. |
| Mathlib/Data/ZMod/QuotientGroup.lean:157–163 | R3 for the body of `Nat.card_zpowers`. It uses the orbit equivalence at $1$, whose cardinality is rewritten through `Nat.card_zmod` and `orbit_subgroup_one_eq_self`. |
| Mathlib/Algebra/GroupWithZero/Units/Equiv.lean:25–29 and Mathlib/Algebra/GroupWithZero/Units/Fintype.lean:33–54 | R3 for units as nonzero elements, finiteness from the injection and the two cardinality wrappers. |
| Mathlib/Data/Nat/Totient.lean:144–172 | R3 for the totient fiber count by gcd and `sum_totient`. |
| Mathlib/FieldTheory/Finite/Basic.lean:801–834 | R3 consumer, already read in §5.3.1.5 and rechecked here. At $F^\times$, `hg` witnesses generator surjectivity, the exponent argument is $nm$, and the positive factor canceled is $m=\lfloor q/2\rfloor$. |
| Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean:87–90,181–195,257–265 and Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean:36–40,77–90 | Euler consumers rechecked at these bodies. Unprimed at $-1$, primed at $2$ for the supplement and at the cast of $\chi_F(-1)|F|$ into $F'$ for the cardinality comparison. |
| /Volumes/UGREEN-WD_BLACK4TB/Projects/Active/RH-lean-archive/lean/src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean:19–34,36–51 | Rechecked the existing Gauss-sum route. `Cond.chi_neg_one` uses $F=\mathbb Z/p\mathbb Z$, $a=-1$, and casts the resulting integer sign to $K$ after applying `quadraticChar_neg_one`. The coefficient field $K$ has characteristic zero. |

**Imported boundaries [Lean].** On the polynomial side: `exists_multiset_roots`, `mem_roots`, `X_pow_sub_C_ne_zero`, `degree_X_pow_sub_C`, `Multiset.toFinset_card_le` and `Finset.card_le_card_of_injOn`. On the group side: the class field `exists_zpow_surjective`, `Subgroup.card_eq_iff_eq_top`, `Subgroup.card_top`, `MulAction.orbitZPowersEquiv`, `Nat.card_zmod`, `orbit_subgroup_one_eq_self`, `groupEquivQuotientProdSubgroup`, `isOfFinOrder_of_finite`, `pow_injOn_Iio_orderOf`, `zpow_mod_orderOf`, `orderOf_pow` and its finite-order supplier, `totient_pos`, `Finset.card_biUnion`, `Finset.sum_erase_lt_of_pos`. For unit cardinality: `Units.val_injective`, `Equiv.sumCompl` and the basic cardinality rewrites. For Euler and its applications: `FiniteField.card`, `FiniteField.odd_card_of_char_ne_two`, `FiniteField.pow_card_sub_one_eq_one`, `FiniteField.pow_dichotomy`, `Nat.two_mul_odd_div_two`, `Nat.dvd_of_mul_dvd_mul_right`, `FiniteField.two_pow_card`, `MulChar.IsQuadratic.eq_of_eq_coe`, and `Char.card_pow_card` retain their individual or predecessor reading boundaries. The additive, trace and host inputs of §5.3.1.5 retain theirs, including `FiniteField.trace_to_zmod_nondegenerate`, `IsCyclotomicExtension.zeta_spec`, `zeta_pow`, `isUnit_iff_not_dvd_char` and `zO_sub_mem_iff`. No kernel replay. The textbook prime-power composition has a self-contained proof here. Mathlib's separate exponent route through `Monoid.exists_orderOf_eq_exponent` is outside the scoped R3 claim.

**Classical references.** Keith Conrad, *Finite Fields*, Theorem 1.1, Lemma 1.6, Theorem 1.10 and Appendix A, pp. 1–3, 12–13. The appendix extracts coprime parts to combine orders. The Stacks Project, Fields, Lemma 9.17.1, Tag 09HX, uses invariant factors under its abelian bounded-torsion hypotheses. Both originals read online. [Conrad](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf) · [Stacks Project](https://stacks.math.columbia.edu/tag/09HX)

**Retrieved originals and SHA-256.**

- SHA-256 `516bc9a90f3ace258fabd159a954e09f5dbf00dc28cc12890784c66c1a5fff01`. [Mathlib/RingTheory/IntegralDomain.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/IntegralDomain.lean)
- SHA-256 `e2e260981e2cd985149de5ebb4a157aa3216ee7c359bb9bfe83a133b3f869574`. [Mathlib/Dynamics/PeriodicPts/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Dynamics/PeriodicPts/Defs.lean)
- SHA-256 `536872e588f1ed90ea0bc359ae5997a84e777eff71c5bdf04517156b5861628f`. [Mathlib/FieldTheory/Finite/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Basic.lean)
- SHA-256 `408b9a10bf32cbc70a6ad7df28a0e04351f4665b2aba66bcc2a7136bfb405a9c`. [Mathlib/GroupTheory/SpecificGroups/Cyclic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/GroupTheory/SpecificGroups/Cyclic.lean)
- SHA-256 `0899e45ca8c2f54d4b8e049ee6ecaf54266810915cca238aa38a70ab4b1050f9`. [Mathlib/GroupTheory/SpecificGroups/Cyclic/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/GroupTheory/SpecificGroups/Cyclic/Basic.lean)
- SHA-256 `14a886d32d5d0a0d6dd32b949be3384db82eb2a4083931d1b8953cf361399b0f`. [Mathlib/GroupTheory/OrderOfElement.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/GroupTheory/OrderOfElement.lean)
- SHA-256 `ce9238694ae37afc0bbd4b50ae4f44a62d1c8356a1c70867bbffab6a067cf3fd`. [Mathlib/Algebra/GroupWithZero/Units/Fintype.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/GroupWithZero/Units/Fintype.lean)
- SHA-256 `35738cdfdc4953a8a7467bffb97dce4a243aa67e3736c2da1efc4bbd9ee3bfbe`. [Mathlib/Algebra/GroupWithZero/Units/Equiv.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/GroupWithZero/Units/Equiv.lean)
- SHA-256 `162d86710afc10cc3ed158236994ed020e589f7fa15d5b39a30bd3e1f153080c`. [Mathlib/Algebra/Polynomial/Roots.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean)
- SHA-256 `943c40005c794e014241782a406445e6dcc2a88f369f8388188ba37a58ee82ea`. [Mathlib/Data/Nat/Totient.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Totient.lean)
- SHA-256 `8c9f8cdc04f49eb959c946b3ada45aa8a13a72bf9d9ec2139d8bf7803611fa32`. [Mathlib/Data/ZMod/QuotientGroup.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/ZMod/QuotientGroup.lean)
- SHA-256 `1c6b797c79503a628561d498d1ee26e6ff516e082d889df2d15fc8f9f56f6d61`. [Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean)
- SHA-256 `54c2a184b863d6047a87a2686b1a2ba818a4374f274f519260939dcfef74428b`. [Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean)
- SHA-256 `f27e8da415a99d96761797c95ba34a547c81b0150b43a8995e1b1238db109c2a`. [conrad.pdf](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf)
- SHA-256 `8bb423ab325fb6a89465bdbfa4130e877862614cca5dd4e175c63f217d4d1d81`. [stacks-09HX.html](https://stacks.math.columbia.edu/tag/09HX)

### Trace pairings and additive characters (§5.3.1.7)

The Mathlib paths below are relative to the repository at manifest revision `0df444a360eaa60ab8c11dca51a86af692955474`. Original sources checked online 2026-11-24. The A2 paths are relative to the read-only extraction at `/Volumes/UGREEN-WD_BLACK4TB/Projects/Active/RH-lean-archive/lean`. Archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, with the manifest pin at `lake-manifest.json:10,13`. R3 applies locally to the specified bodies. [Chapter 5 §5.3.1.7](../chapters/05-the-square-root-barrier-core-gm.md#5317-trace-pairings-and-the-additive-input-to-gauss-sums)

| Source | Reading |
|---|---|
| `Mathlib/FieldTheory/Finite/Trace.lean:37–44,49–56` | R3 for `trace_to_zmod_nondegenerate` and `algebraMap_trace_eq_sum_pow`. The former extracts the left nondegeneracy implication by contradiction. The latter rewrites the trace as a sum over automorphisms and reindexes by powers of the finite-field Frobenius. |
| `Mathlib/RingTheory/Trace/Basic.lean:431–452,462–507` | R3 for the embedding/Vandermonde matrix identities, `det_traceMatrix_ne_zero'`, `det_traceForm_ne_zero` and `traceForm_nondegenerate`. Scalar extension and a separable power basis give the product of embedding differences. Changing basis multiplies by invertible determinants, and the determinant criterion gives the bilinear-form statement. |
| `Mathlib/NumberTheory/Cyclotomic/Basic.lean:79–85,649–687` | R3 for the `IsCyclotomicExtension` class (`:79–85`), the `CyclotomicField` definition (`:654–655`) and the body of `CyclotomicField.isCyclotomicExtension`. A split root is primitive by the cyclotomic-root criterion, and the splitting-field roots generate the extension. |
| `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean:85–95,106–107` | R3 for `zeta`, `zeta_spec` and `zeta_pow`. The singleton existence witness, its specification, and the projected power identity refer to the same chosen root. |
| `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean:59–61,83–86,138–197,212–230` | R3 for the definition of primitivity, field inverse-shift proof, cyclic character construction and kernel test, and `FiniteField.primitiveChar`. The finite-field proof uses nondegeneracy at $1$. |
| `Mathlib/NumberTheory/GaussSum.lean:175–201,214–228,283–319,340–401` | R3 for the direct product, nonvanishing and square bodies and the previously read consumers. The field comparison uses `ψ.char` and `ψ.prim` and the supplement uses order eight on the cyclic ring. |
| `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean:36–40,77–99`; `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean:107–119,123–130`; `Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean:406–427` | Previously read interfaces, rechecked at the calls from the quadratic character to `Char.card_pow_card` and from Jacobi to the prime reciprocity theorem. |
| `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean:19–51` | A2 receipt. `Cond.gs` uses the specified $p$th root and `Cond.gs_sq` gets primitivity from this root. The nontrivial multiplicative witness is $-1$ when $p\equiv3\pmod4$. |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean:98,158,166,185` | A2 prior reading. `zO_sub_mem_iff` is the actual host comparison. The cyclic kernel reformulation is conditional on its already obtained order statement. |

**Imported boundaries [Lean].** These include `Field.powerBasisOfFiniteOfSeparable`, `AlgHom.card`, `trace_eq_sum_embeddings`, `trace_eq_sum_automorphisms`, `bijective_frobeniusAlgEquivOfAlgebraic_pow`, `det_vandermonde`, `BilinForm.nondegenerate_of_det_ne_zero`, the finite-field separability and finite-dimensionality instances, `Splits.exists_eval_eq_zero`, `degree_cyclotomic_pos`, `isRoot_cyclotomic_iff`, `IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots`, `IsPrimitiveRoot.pow_inj`, `NeZero.of_not_dvd`, `isUnit_iff_not_dvd_char`, `sum_mulShift` and the deeper host root-reduction inputs. No kernel replay.

**Classical sources.** Keith Conrad, *Finite Fields*, Theorem 4.6, printed pp. 9–10, gives the sum of Frobenius powers and the nonzero-polynomial proof of surjectivity. Stacks Project, Tag 0BIL, gives the separable trace criterion and the division argument for nondegeneracy. Both originals read online 2026-11-24. [Conrad](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf) · [Stacks Project](https://stacks.math.columbia.edu/tag/0BIL)

Pinned producer files

- SHA-256 `eef729883f2ab8f6a1024c6977276cbdba715a3fb931c5bb1a76bf24db77cfd8`. [Mathlib/FieldTheory/Finite/Trace.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Trace.lean)
- SHA-256 `685fb38703fd188fd027acb4cd9d8d2ea79628a6a2c5c7435999d61986d0e9d9`. [Mathlib/RingTheory/Trace/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean)
- SHA-256 `4a342f77c87361d411fcecb17532ccc5ac019e42d6d91ac7d21467a49b1f6bce`. [Mathlib/NumberTheory/Cyclotomic/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Cyclotomic/Basic.lean)
- SHA-256 `3981089ca12533c20e9e54bb7c57b8dcb53fdb3bc523b074bdba33b635936436`. [Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean)
- SHA-256 `19b06c1956274e1e66ecafbcf1c0436fb44af084eac2e903cbcd1271140d808d`. [Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean)

### Finite-field trace by embeddings (§5.3.1.8)

Archive A2 (read-only): `/Volumes/UGREEN-WD_BLACK4TB/Projects/Active/RH-lean-archive/lean.tar.gz`, verified SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Its `lean/lake-manifest.json:5–14` pins Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. All Mathlib coordinates below are complete paths relative to that commit. This is a local source reading.

| Reading | File and lines | Role |
|---|---|---|
| R3 [Lean, read] | `Mathlib/RingTheory/Trace/Defs.lean:68–79,87–115,118–129,138–141` | Multiplication trace, scalar trace and trace through a tower via the diagonal of a block matrix. |
| R3 [Lean, read] | `Mathlib/RingTheory/Trace/Basic.lean:78–95,127–131,218–272` | Generator trace by the characteristic coefficient, restriction fibers, `trace_eq_sum_embeddings` and normal reindexing in `trace_eq_sum_automorphisms`. |
| R3 [Lean, read] | `Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean:75–84`; `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:438–457`; `Mathlib/RingTheory/PowerBasis.lean:295–338` | Cayley–Hamilton plus the power-basis degree bound, simple-adjoin basis transported from the polynomial quotient, and reindexing by roots. |
| R3 [Lean, read] | `Mathlib/RingTheory/AlgebraTower.lean:188–218`; `Mathlib/FieldTheory/PrimitiveElement.lean:346–362`; `Mathlib/FieldTheory/Separable.lean:767–779` | Restriction and extension of scalars are inverse to forgetting the intermediate structure. The split embedding-count wrappers use a supplied separable power basis and count the distinct roots. |
| R3 [Lean, read] | `Mathlib/FieldTheory/Normal/Defs.lean:127–163,204–218`; `Mathlib/RingTheory/Algebraic/Basic.lean:491–499,519–525` | Restrict embeddings to the normal image and include automorphisms in the ambient field. An algebraic endomorphism is onto since it permutes the finite root set of a polynomial over the base for each target element. |
| R3 [Lean, read] | `Mathlib/FieldTheory/Finite/Basic.lean:327–345,359–406`; `Mathlib/FieldTheory/Finite/GaloisField.lean:44–62,196–205` | The order proof uses $X^{q^m}-X$ and the finite-field cardinality. Powers of the computed order inject and the embedding bound forces surjectivity. Transfer along the multiplicative equivalence gives `bijective_frobeniusAlgEquivOfAlgebraic_pow`. The Galois instance uses the separable splitting polynomial. |
| R3 [Lean, read] | `Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean:65–94` | The upper bound on embeddings uses their linear independence over the target and the dimension of the space of linear forms. |
| R3 formula rechecked, remaining receipt inherited | `Mathlib/FieldTheory/Finite/Trace.lean:37–56`; `Mathlib/RingTheory/Trace/Basic.lean:444–446,462–507`; `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean:212–230`; `Mathlib/NumberTheory/GaussSum.lean:283–319` | The output trace sum uses the bijection explicitly. The trace-form factorization separately consumes the embedding sum. The additive character and Gauss-sum use retain the predecessor's reading. |
| [Lean], deeper inputs | `Mathlib/FieldTheory/PrimitiveElement.lean:227–229`; `Mathlib/GroupTheory/OrderOfElement.lean:573–579`; `Mathlib/Algebra/Polynomial/Roots.lean:136–139` | `Field.powerBasisOfFiniteOfSeparable` and its primitive-element proof, general order/powers and polynomial root infrastructure. Also retain the upstream proofs of `linearIndependent_algHom_toLinearMap`, `AdjoinRoot.powerBasis`, the characteristic coefficient identity, the splitting-field and finite-dimensional instances, and `AlgHom.normal_bijective` as interfaces here. |

The historical §5.3.1.7 list recorded the three requested declarations at interface level. The entries above record their later local reading. The general separable power-basis existence proof still supplies Mathlib's embedding count and the trace-pairing determinant. The textbook instead counts extensions one simple adjunction at a time. The matrix examples and inseparable model are [Expository]. No Lean kernel replay or full dependency closure reading was performed.

Classical originals read online 2026-11-24:

- Keith Conrad, *Finite Fields*, printed pp. 8–11, Theorems 4.1, 4.6 and 5.6. Frobenius order, trace power sum and surjectivity, including the general finite base. [Author PDF](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf)
- Keith Conrad, *Trace and Norm, II*, printed p. 8, Theorem 5.1 and Example 5.3. Galois conjugates occur with the multiplicities of the fibers over the simple subfield. [Author PDF](https://kconrad.math.uconn.edu/blurbs/galoistheory/tracenorm2.pdf)
- The Stacks Project, §9.20, Lemma 9.20.7. The purely inseparable degree-$p$ case has zero trace, in contrast to the separable trace criterion. [Original](https://stacks.math.columbia.edu/tag/0BIL)

Retrieved file hashes

- SHA-256 `15507f0a6df59ac12e71d23cdd5debc5206d4d4fa384321b441ef3663662c5f1`. [Mathlib/RingTheory/Trace/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Defs.lean)
- SHA-256 `685fb38703fd188fd027acb4cd9d8d2ea79628a6a2c5c7435999d61986d0e9d9`. [Mathlib/RingTheory/Trace/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean)
- SHA-256 `3df0342f61058233d34105b594335f1fec4ba6350d960ac65d82128edc708a84`. [Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean)
- SHA-256 `657f34bb6b19d57cf1f96dec3ded1265ac6133675d6fd7c769a71eb31223df7b`. [Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean)
- SHA-256 `e4ecfdc08c66dbf032614ff045f408cc7edb771263d76ad7be216f55bb0ed840`. [Mathlib/RingTheory/PowerBasis.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/PowerBasis.lean)
- SHA-256 `71da3061e7a7933aba8d41577ab163f6c1fcd49bfc2b35406e2dbc066a87228f`. [Mathlib/RingTheory/AlgebraTower.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AlgebraTower.lean)
- SHA-256 `ae93272abab413b8236452f96507a2dcc6f576d16bc34ca0f4ed02c723950b05`. [Mathlib/FieldTheory/PrimitiveElement.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean)
- SHA-256 `771fc28028ba2337db37e71a59bf48e635817a803b2f14744be120073c1f0593`. [Mathlib/FieldTheory/Separable.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Separable.lean)
- SHA-256 `131279d5867651ea15aecc6442076b7ff3d4b165265cec7533cfbc504a164389`. [Mathlib/FieldTheory/Normal/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Normal/Defs.lean)
- SHA-256 `a687e6a70bf57275df97310733e0a52e80379da2ea23b92c74318e35985ffdd1`. [Mathlib/RingTheory/Algebraic/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Algebraic/Basic.lean)
- SHA-256 `536872e588f1ed90ea0bc359ae5997a84e777eff71c5bdf04517156b5861628f`. [Mathlib/FieldTheory/Finite/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Basic.lean)
- SHA-256 `4adddf6dbdeb841074d2b6373bfa419aa47d23414f79906a65c589853b5cc6dd`. [Mathlib/FieldTheory/Finite/GaloisField.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/GaloisField.lean)
- SHA-256 `849e51cac94ee999dae9fbb3d91079b07f42f97c3caa7148f00c7661ec3244b7`. [Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean)
- SHA-256 `eef729883f2ab8f6a1024c6977276cbdba715a3fb931c5bb1a76bf24db77cfd8`. [Mathlib/FieldTheory/Finite/Trace.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Trace.lean)
- SHA-256 `19b06c1956274e1e66ecafbcf1c0436fb44af084eac2e903cbcd1271140d808d`. [Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean)
- SHA-256 `710816aacd15b8bed8b0821bb47ae2da7f2d7b2219df487688ca7cef753b5186`. [Mathlib/NumberTheory/GaussSum.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/GaussSum.lean)
- SHA-256 `14a886d32d5d0a0d6dd32b949be3384db82eb2a4083931d1b8953cf361399b0f`. [Mathlib/GroupTheory/OrderOfElement.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/GroupTheory/OrderOfElement.lean)
- SHA-256 `162d86710afc10cc3ed158236994ed020e589f7fa15d5b39a30bd3e1f153080c`. [Mathlib/Algebra/Polynomial/Roots.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Roots.lean)
- SHA-256 `f27e8da415a99d96761797c95ba34a547c81b0150b43a8995e1b1238db109c2a`. [conrad.pdf](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf)
- SHA-256 `db1ce27258c5255bf9b4683c2f4136b7021eb7ebb399d102b66481de0ecf0033`. [tracenorm2.pdf](https://kconrad.math.uconn.edu/blurbs/galoistheory/tracenorm2.pdf)
- SHA-256 `7a26b06355150e4fca0dc3f170b4c015c64a3ae213c8472c975c906542cc3407`. [stacks-0BIL.html](https://stacks.math.columbia.edu/tag/0BIL)

### Primitive elements and power bases (§5.3.1.9)

Archive A2 (read-only): `/Volumes/UGREEN-WD_BLACK4TB/Projects/Active/RH-lean-archive/lean.tar.gz`, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` (verified by §5.3.1.8). Its `lean/lake-manifest.json:5–14` pins Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. All coordinates below are complete paths at that commit, retrieved from GitHub on 2026-11-25 and compared by hash with the §5.3.1.8 copies where both exist. This is a local source reading; no Lean kernel replay was performed.

| Reading | File and lines | Role |
|---|---|---|
| R3 [Lean, read] | `Mathlib/FieldTheory/PrimitiveElement.lean:54–72` | `exists_primitive_element_of_finite_top` and `_of_finite_bot`: a generator of the cyclic unit group generates the field; finite-dimensional over finite is finite. |
| R3 [Lean, read] | `Mathlib/FieldTheory/PrimitiveElement.lean:83–95` | `primitive_element_inf_aux_exists_c`: the finite set of root quotients, its preimage under the injective base map, and a scalar outside it. |
| R3 [Lean, read] | `Mathlib/FieldTheory/PrimitiveElement.lean:100–167` | `primitive_element_inf_aux`: $\gamma=\alpha+c\beta$, the greatest common divisor over $F(\gamma)$ and over $E$, separability and splitting of the divisor, the single-root argument against the chosen scalar, and $\beta=-p_0/p_1$. |
| R3 [Lean, read] | `Mathlib/FieldTheory/PrimitiveElement.lean:206–221` | `exists_primitive_element`: case split on `Fintype F`, adjoin induction with the predicate "equals a simple adjoin", finite branch by `_of_finite_bot`. |
| R3 [Lean, read] | `Mathlib/FieldTheory/PrimitiveElement.lean:223–231` | `powerBasisOfFiniteOfSeparable`: `Classical.choose`, `adjoin.powerBasis`, transport along `equivOfEq` and `topEquiv` by `PowerBasis.map`. |
| R3 [Lean, read] | `Mathlib/FieldTheory/PrimitiveElement.lean:346–362` | `AlgHom.natCard_of_splits`, `AlgHom.card_of_splits`, `AlgHom.card`: embedding count from the power basis and `PowerBasis.finrank`. |
| R3 [Lean, read] | `Mathlib/FieldTheory/Separable.lean:442–447,477–495,767–779` | `card_rootSet_eq_natDegree`, `eq_X_sub_C_of_separable_of_root_eq` (roots of the mapped polynomial form the singleton, then injectivity of the map), `AlgHom.natCard_of_powerBasis` (embeddings of a power-basis algebra correspond to distinct roots of the separable minimal polynomial). |
| R3 [Lean, read] | `Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:301–305`; `Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:578–579,686–699` | `induction_on_adjoin` via Noetherian finite generation, `induction_on_adjoin_fg` and `induction_on_adjoin_finset` by `Finset` induction, and `adjoin_simple_adjoin_simple`. |
| R3 [Lean, read] | `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:440–470` | `powerBasisAux`, `adjoin.powerBasis`, `adjoin.finiteDimensional`, `adjoin.finrank`. |
| R3 reread at call sites | `Mathlib/RingTheory/Trace/Basic.lean:235–262,462–507` | `sum_embeddings_eq_finrank_mul` consumes `AlgHom.card`; `det_traceMatrix_ne_zero'` consumes `AlgHom.card`; `det_traceForm_ne_zero` sets `pb := Field.powerBasisOfFiniteOfSeparable`; `traceForm_nondegenerate`. Bodies read in §5.3.1.7 and §5.3.1.8. |
| Inherited | §5.3.1.6 (`isCyclic_of_subgroup_isDomain`, `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean`), §5.3.1.7 (`FiniteField.trace_to_zmod_nondegenerate`, `primitiveChar`), §5.3.1.8 (`trace_eq_sum_embeddings`, `trace_eq_sum_automorphisms`) | Cyclicity of finite unit groups and the trace consumers. |
| [Lean], named inputs | `IsCyclic.exists_generator`, `zpow_mem`, `Module.finite_of_finite`, `Infinite.exists_notMem_finset`, `AdjoinRoot.powerBasis`, `adjoinRootEquivAdjoin`, `PowerBasis.map`, `IntermediateField.equivOfEq`, `IntermediateField.topEquiv`, `EuclideanDomain.gcd`, `gcd_map`, `separable_gcd_right`, `eval_gcd_eq_zero`, `root_left_of_root_gcd`, `root_right_of_root_gcd`, `Splits.of_dvd`, `SplittingField.splits`, `IsNoetherian.iff_fg`, `IntermediateField.fg_of_noetherian`, `adjoin_adjoin_left` | Used at interface level; bodies not read here. The Steinitz equivalence `exists_primitive_element_iff_finite_intermediateField` (`PrimitiveElement.lean:329–337`) is noted but not on the trace path. |

Classical originals read online 2026-11-25:

- The Stacks Project, Lemma 9.19.1 (Tag 030N), "Primitive element": a finite extension has a primitive element if and only if it has finitely many subextensions, and both hold when the extension is separable. The infinite-base proof avoids finitely many proper subspaces; the finite-base case is referred to Section 9.18. The pinned `exists_primitive_element` carries `@[stacks 030N "The moreover part"]`. [Original](https://stacks.math.columbia.edu/tag/030N)
- The Stacks Project, Section 9.18 (Tag 09HY), "Finite fields": the unit group is cyclic, so a generator generates the field over the prime field and over any subfield. The pinned `exists_primitive_element_of_finite_top` carries `@[stacks 09HY "second part"]`. [Original](https://stacks.math.columbia.edu/tag/09HY)
- J. S. Milne, *Fields and Galois Theory*, v5.10 (September 2022), Proposition 4.19, p. 53 (every extension of finite fields is simple, via the cyclic unit group) and Theorem 5.1 with Remark 5.2, pp. 61–62 (primitive element for $F[\alpha_1,\ldots,\alpha_r]$ with $\alpha_2,\ldots,\alpha_r$ separable; the scalar $c$ avoids the solutions of $\alpha_i+X\beta_j=\alpha+X\beta$; the worked example $\mathbb Q[\sqrt2,\sqrt3]=\mathbb Q[\sqrt2+\sqrt3]$). Same file and hash as **[MilneFT]**. [Author PDF](https://www.jmilne.org/math/CourseNotes/FT.pdf)
- Keith Conrad, *Separability II*, Theorems 1.1 and 1.2 (pp. 1–4), which invoke the primitive element theorem for the trace and nilpotent criteria; consulted for the classical use of the theorem in trace arguments, not for its proof. [Author PDF](https://kconrad.math.uconn.edu/blurbs/galoistheory/separable2.pdf)

Retrieved file hashes

- SHA-256 `ae93272abab413b8236452f96507a2dcc6f576d16bc34ca0f4ed02c723950b05`. [Mathlib/FieldTheory/PrimitiveElement.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean)
- SHA-256 `771fc28028ba2337db37e71a59bf48e635817a803b2f14744be120073c1f0593`. [Mathlib/FieldTheory/Separable.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Separable.lean)
- SHA-256 `da8cdce2a744754d50ef30fe52f845cc78617edada2411deeac5ac7120ab2762`. [Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean)
- SHA-256 `acccf606573e67aeb67d1354c50e8f0531ede578922f22bc4fa376b74b22d967`. [Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean)
- SHA-256 `657f34bb6b19d57cf1f96dec3ded1265ac6133675d6fd7c769a71eb31223df7b`. [Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean)
- SHA-256 `685fb38703fd188fd027acb4cd9d8d2ea79628a6a2c5c7435999d61986d0e9d9`. [Mathlib/RingTheory/Trace/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean)
- SHA-256 `408b9a10bf32cbc70a6ad7df28a0e04351f4665b2aba66bcc2a7136bfb405a9c`. [Mathlib/GroupTheory/SpecificGroups/Cyclic.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/GroupTheory/SpecificGroups/Cyclic.lean)
- SHA-256 `677fa779865113c6d5fc435ed9704d4b632faf03c2abbfbb2adee74d023fceea`. [stacks-030N.html](https://stacks.math.columbia.edu/tag/030N)
- SHA-256 `f1de06e5e510a000b23610d157d8b46d6f2c40c87c448e61566188ab8b907be6`. [stacks-09HY.html](https://stacks.math.columbia.edu/tag/09HY)
- SHA-256 `5c43ea0bf4ec190b819727fe720414a80e09f9e762533d08bad5b8a0b6de7273`. [milne-FT.pdf](https://www.jmilne.org/math/CourseNotes/FT.pdf)
- SHA-256 `357828e20fd6e2e47cdc164b994e6e768136b90d708b15b419c368597a507588`. [separable2.pdf](https://kconrad.math.uconn.edu/blurbs/galoistheory/separable2.pdf)

### Chapter 7, §7.4.3.1 — spherical split-place transfer

- **A2**. Joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, checked again 2026-11-24. The subsection's verification entry gives the actual split-GL proof path and the reading boundaries. [Chapter 7](../chapters/07-chains-of-theta-lifts.md#7431-spherical-transfer-at-a-split-place)
- **Alberto Mínguez**, *Correspondance de Howe explicite : paires duales de type II*, Ann. Sci. Éc. Norm. Sup. 41 (2008), 717–741. Section 1 normalizes induction and Jacquet modules, §2 filters the matrix representation by rank, §3 computes its Jacquet modules, and Theorem 6.1 and Corollary 6.3 (pp. 733–734) give the classical type-II comparison. PDF retrieved 2026-11-24, SHA-256 `b379de638b8f3be2932ccf68485078ac00d776f7e6a244e9cb602a29958575ab`. [Numdam](https://www.numdam.org/item/ASENS_2008_4_41_5_717_0/)
- **Ichirō Satake**, *Theory of spherical functions on reductive algebraic groups over p-adic fields*, Publ. Math. IHÉS 18 (1963), 5–69. Chapter II, §§5–6 and Theorem 3 give the spherical Hecke transform and classification of its characters. PDF retrieved 2026-11-24, SHA-256 `bd6c8f5c0076257c1252f8d34e659727ac4b30ee58073ed1224ee1eb3d1f23c9`. [Numdam](https://www.numdam.org/item/PMIHES_1963__18__5_0/)
- **Aapo Lipponen / LUMI guide [Community]**. The chain guide records the successive rank and parameter increments. Its chapter 04 was retrieved 2026-11-24, SHA-256 `5258df0f8b20609b38926ca1ef54b0ac45afc5b2f7749022dc7086d64573f9f9`. [Guide](https://github.com/aapolipponen/rh-lean-check-lumi/blob/main/docs/04-chain-and-one-half.md)

### Chapter 7 §7.4.3.2 — Single-cell evaluation

- **I. N. Bernstein and A. V. Zelevinsky**, *Induced representations of reductive p-adic groups I*, Ann. Sci. Éc. Norm. Sup. 10 (1977), 441–472. Theorem 5.2 (p. 460) states the orbit filtration. Sections 5.15–5.17 (pp. 465–467) identify the orbit functor, construct the quotient-fiber integral and prove its isomorphism. Original PDF retrieved 2026-11-24, SHA-256 8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092. [Numdam](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0/)
- **Alpöge–Claude A2 archive**, SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. The archive supplies finite stabilized cell averages, the normalized row-to-column transport, placement congruence and normalized unit evaluation. [Declaration map](../chapters/07-chains-of-theta-lifts.md#single-cell-supply-for-proposition-73g)

### Chapter 7 §7.4.3.3 — Bump and kernel supply

- **I. N. Bernstein and A. V. Zelevinsky**, *Induced representations of reductive p-adic groups I*, Ann. Sci. Éc. Norm. Sup. (4) 10 (1977), no. 4, 441–472, DOI 10.24033/asens.1333. Section 5.17 (pp. 466–467) proves the fiber isomorphism by reduction to the regular representation, free resolutions and exactness. Numdam item page re-checked 2026-11-24 (title, authors, volume, pages and PDF link confirmed); the PDF hash recorded for §7.4.3.2 is unchanged. [Numdam](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0/)
- **Alpöge–Claude A2 archive**, SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. Files read in full for this subsection: `lean/src/GroundTheory/AutomorphicForms/GeometricLemmaCellSurjective.lean` (SHA-256 4ab724f7619b12ee8560bddbd1ded8720b687894827518ac1a208ae73747eaac), `GeometricLemmaCellKernel.lean` (d0b7d3c552fa3501e3ad0b5e8643f3995bfab3c6a2ba3d631b2cb19fcefa231d) and `GeometricLemmaJacquetCell.lean` (d81c00dd165210d9065719d3b4bbfa2aa11d3db89b2bff4609b1364cbaec7cef). The archive supplies the covariant bump, the level exhaustion by torus-conjugated integral points, the positivity argument, the finite-subtraction surjectivity and the averaged-difference kernel. [Declaration map](../chapters/07-chains-of-theta-lifts.md#bump-and-kernel-supply-for-theorems-73l-and-73n)

### Chapter 7 §7.4.3.4 — Bruhat filtration

- **I. N. Bernstein and A. V. Zelevinsky**, *Induced representations of reductive p-adic groups I*, Ann. Sci. Éc. Norm. Sup. (4) 10 (1977), no. 4, 441–472, DOI 10.24033/asens.1333. Proposition 1.9(a) (p. 445) gives the exactness of the Jacquet functor. Condition 5.1(3) and Theorem 5.2 (p. 460) give the ordering of the orbits with open initial unions and the filtration. Sections 5.3–5.4 (p. 461) define the subfunctor of an open union by applying the exact Jacquet functor to the sections supported there, and the orbit functor as a quotient of two such subfunctors. PDF retrieved again 2026-11-25; SHA-256 8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092, unchanged from §7.4.3.2. [Numdam](https://www.numdam.org/item/ASENS_1977_4_10_4_441_0/)
- **A. V. Zelevinsky**, *Induced representations of reductive p-adic groups II. On irreducible representations of GL(n)*, Ann. Sci. Éc. Norm. Sup. (4) 13 (1980), no. 2, 165–210, DOI 10.24033/asens.1379. Theorem 1.2 (p. 170) and its reformulation 1.3 (p. 171) give the filtration for $\mathrm{GL}_n$, the sufficiency of the open-union condition and the closed cell as a quotient. Section 1.6 (pp. 171–172) indexes the cells by matrices $B(w)$. PDF retrieved 2026-11-25, SHA-256 663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac. [Numdam](https://www.numdam.org/item/ASENS_1980_4_13_2_165_0/)
- **Alpöge–Claude A2 archive**, SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. Files read for this subsection, with SHA-256: `GeometricLemmaCells.lean` (ba853ff3a312edc142e82a0c78a4cb9b656067dcfd515b86a12e0b7e48117b1e), `GeometricLemmaFiltration.lean` (4bad875c57ee45fad3e72e893119c7f287102018ac2deaa58246fd019f835dc6), `GeometricLemmaGraded.lean` (df9a16e4b81679afaf56539824b6a2a1fb75afd6128c535bbed3f8cd77aa99fb), `GeometricLemmaUnnormalized.lean` (e45c0c7868be8d144eec809761ee106d437940ccdc183b6beb9ed747857cc999), `BernsteinZelevinskyGeometricLemma.lean` (12244c79a749899a52ae1525c5b279ff4a00b51d64955661ecdbba43e8ce6a55), `JacquetOfInducedFiltration.lean` (7800f6b0ef5dab1e2a0a70eb13446167073175ba0b883117dbb23f2c02a4beda), `ExistsCellOfIsSubquotient.lean` (b4c15a02799ec2356185bb053930eae9eb77d59357793cf9455a630a310a1d28), `NontrivialOfIrreducible.lean` (edb7565dd1908ad144297c27c0ed485a7d7326a631b3f7b4c81d69747afd35ab). Each file hash agrees with the copy extracted from the archive. The archive supplies the rank-array order of the double cosets, the image filtration, the descent of the cell map to coinvariant classes, and the assembly through normalization, block coordinates and multiplicities. [Declaration map](../chapters/07-chains-of-theta-lifts.md#filtration-supply-for-theorems-73o73r)
