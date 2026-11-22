# Outline of the book

Working plan, derived from `notes/proof-map.md` (node IDs P0–P18 refer to that note).
Lengths are estimates in words of prose, excluding quoted Lean and tables
(roughly 500 words per printed page).

## Design decisions

1. **One spine, read top down, then bottom up.** Part I follows the proof from the final
   theorems down to the one place where the exponent $1/2$ is produced (`core_gm`, P6).
   Everything above that point is classical analytic number theory and can be explained
   completely. Part II then opens the hypotheses of `core_gm`, which is where the new
   mathematics lives. Part III covers the foundations that the archive builds for itself.
   Part IV compares with Masullo and lists what is still unverified.
2. **Every claim tagged.** `[Lean]` / `[Lean, read]` claims cite `src/…:line` in the pinned
   archive (or `Mathlib/…:line` at commit `0df444a`). Content we take from the announcement or
   Masullo's draft is `[Paper]` with its page; content from verification pages, community guides,
   formalization projects, blogs and press is `[Community]` with its link; our own explanations
   are `[Expository]`; anything unresolved is `[Open]` (tags as in the README). A chapter may not upgrade a tag beyond what
   `notes/proof-map.md` records as our reading level (R1/R2/R3).
3. **Explain the classical layer fully, the new layer honestly.** For P1–P5 and P13 the book
   gives proofs a graduate student can check by hand. For P7–P12 and P14–P17 the book explains
   the role, the statement and the classical analogue, and says plainly which proofs nobody
   (as far as we know) has read.
4. **Masullo side by side, not interleaved everywhere.** Each chapter ends with a short
   "Masullo's counterpart" box (often "none"); the full comparison is Chapters 14–15.
5. **No copying.** Community guides (LUMI docs 01–10, Deicyde/leanprover-community notes,
   mccorvie/riemann-masullo) are cited as sources; their text is not reused.

## Chapters

| # | Title | Core idea to make clear | Prerequisites | Lean nodes | Masullo | Length |
|---|---|---|---|---|---|---|
| 0 | Preface and reading guide | What the book is for, what is and is not established, how tags and citations work, reading paths, the argument on one page. | — | overview of P0–P18 | the draft's status and scope | 4,500 |
| 1 | The statement and its fidelity | Mathlib's `RiemannHypothesis` and `DirichletCharacter.LFunction`; the exact five theorems; why the hypotheses are the right exclusions; the definitional identities checked by the kernel; the reduction to `EveryCharacter`; axioms, metaprogramming, kernel versions; public verification status and what a pass does not show. | 0 | P0, P1 (statements), static scan | Ch. 13 (scope comparison only) | 8,000 |
| **Part I** | **The analytic endgame** | | | | | |
| 2 | One half-plane implies everything: functional equations and primitive characters | The five theorems follow from "no zeros on $\Re s>1/2$" by reflection $s\mapsto1-s$ and by removing Euler factors; worked proofs mirroring `rh_of_right`, `critLine`, `Claim.strip`, `imprimitive`. | 1 | P1, P3 | Ch. 3 (Tate's thesis), §13.1 | 5,000 |
| 3 | Prime sums with a sign: the Landau-window criterion | Riesz-weighted prime sums $G_\chi(x)=\sum_{n\le x}\Lambda(n)\chi(n)(x/n-1)+\dots$; their explicit formula $-\sum_\rho x^\rho/(\rho(\rho-1))$; why a **one-sided** bound on **windows** $[Y,Y^{1+\delta}]$ already forces zero-freeness right of $\theta$ (Landau/Pólya on the Laplace transform, `PoleData`); why one needs a positive combination over a cyclic level. | 2 | P5, P4 (the $\varepsilon\to0$ limit) | App. B.4 (explicit formulas) as the contrasting zeros↔primes link | 8,000 |
| 4 | Auxiliary prime pairs and host fields | Choosing $q\equiv3\ (8)$, $d\equiv7\ (16)$ of size $\exp(Y^{\varepsilon/5})$ so that quadratic twists have square-root prime-sum bounds and zero-free boxes; zero density + mean square + Siegel; the CM host fields $E\subset\mathbb Q(\zeta_N)$ and the role of the constants $1/400$, $401$, $\varepsilon<1/52$. | 3 | P13, `IsChiField`/`WinPair` from P12 | App. B.1 (pp. 588–591), B.6 (pp. 636–643) | 6,000 |
| 5 | The square-root barrier as bookkeeping: `core_gm` | What `core_gm` proves and what it assumes; the finite Fourier analysis on the host's character group; where $1/2$ comes from (chain length $m\approx\sqrt x$, error $\approx x/m+m$); why the hard content is in the Props `EAtH` and `CoreAtH`. | 3, 4 | P6 | none (contrast: the $\lvert\cdot\rvert^{1/2}$ normalization, §1.2.1) | 7,000 |
| **Part II** | **The arithmetic engine: Stepanov over the integers** | | | | | |
| 6 | Stepanov's method and what "multiplicity over $\mathbb Z$" could mean | Function-field warm-up: Stepanov's auxiliary polynomial with high vanishing order and the resulting point count; the announcement's idea of replacing derivatives by a chain of theta lifts; the dictionary we will use in Chapters 7–11. Largely `[Expository]` and `[Paper]`. | 5 | motivation for P7–P10 | §14.2 (function fields) as the other route to the function-field analogue | 6,000 |
| 7 | Chains of theta lifts | Iterated lifts $U(X_0)\to U(X_1)\to\dots\to U(X_m)$ between definite unitary groups; Howe duality, Siegel–Weil and the matching of theta integrals; the families `HypsAlt` and the chain data `ChainTied`/`SizeData₂`; how $m$ and the 2-power level are chosen. | 6 | P17, P7 | none (Ch. 2 "θ-functions" is a different object; say so) | 9,000 |
| 8 | Divisibility at inert primes | The statement `Conclusion1`; supersingular CM points and $p$-adic analysis of theta kernels (as reported); the analogue of vanishing order; what has and has not been read. | 7 | P8 | none | 7,000 |
| 9 | Heights, slopes and near-orthogonality | Hermitian lattices, Bost's slope inequality (`SlopeIneq`), height of a composite of $m$ steps, the divisor inequality; near-orthogonality of periods (`LinkS`) and gains (`LinkG`); the announcement's Chowla–Selberg / Siegel mass / Rallis inputs. | 7, 8 | P9, P10 | none | 7,000 |
| 10 | From congruence modules to Tate–Shafarevich groups | Congruence numbers of each lift; the Fitting-ideal argument on a generalized matrix algebra (`CutCoreUnit.main`); killing Selmer classes by twisting (`TwistingCharacterExistence`); where the Ш bound enters (`HypV`, `LinkN`). | 9 | P11 | none | 8,000 |
| 11 | The window bound `VWin` | Statement (`VVle`, `VAt`, `VWinAt`); split into $\ell=2$, minus and plus parts; Bernoulli numbers and Euler systems; U(3) congruences and residually reducible modularity (`PropGK`, `PfromAut`); Ferrero–Washington; why a bound of size $\exp(x^\varepsilon/2)$ suffices. The largest block of the archive. | 10 | P12 | none | 10,000 |
| **Part III** | **Foundations built inside the archive** | | | | | |
| 12 | Galois representations and partial local Langlands | `Row0b`: Galois representations for polarized cuspidal $\pi$ on $\mathrm{GL}_a$ over CM fields with weak local–global compatibility; their construction (Shimura-variety cohomology, congruences, theta lifts for even rank) as reported; `RecTExists` and how weak it is compared with local Langlands. | 11 | P14, P15 | Ch. 3 is the $\mathrm{GL}_1$ case (local class field theory) | 8,000 |
| 13 | Green's theorem and the literature layer | Cuspidal characters of $\mathrm{GL}_d(\mathbb F_g)$ (`Green`); the ~250 named theorems stated as `GlobalTheory.Published.*` Props and proved in the archive; how to audit a name against the literature; current verdicts (with sources). | 12 | P16, P18 | Apps. A–E (cited background) | 6,000 |
| **Part IV** | **Comparison and assessment** | | | | | |
| 14 | Masullo's trace-formula route | Tate's thesis → Schauder bases → Hardy–Sobolev completions → spectral side (Ch. 10) = geometric side (Ch. 12) → Theorem 12.5.1.1 → the unwritten Ch. 13; why the content of GRH sits in the independence of the geometric side from the strip parameter; the public gap in Ch. 10 (with Pei's unreviewed $I=\{0\}$ partial repair and the unrepaired strip case $I=[-\alpha,\alpha]$ `[Open]`); the formalization effort. | 1, 3 | none | Chs. 1–13, App. B | 9,000 |
| 15 | Two proofs side by side | Scope (Dirichlet vs. all Hecke characters), method (Stepanov/theta chain vs. trace formula), verification state (kernel-checked but unread vs. readable but unfinished), shared classical frame, what each would teach the other. | 5, 11, 14 | P0–P18 summary | whole draft | 6,000 |
| 16 | Open problems and what remains to be checked | Pending machine checks; statement-fidelity items; unread proof bodies by block; fidelity of literature Props; Masullo's open items; consequences that do and do not follow (ERH not covered); a checklist for readers who want to help. | all | all | all | 5,000 |

Total ≈ 129,000 words.

## Dependencies between chapters

```
0 → 1 → 2 → 3 → 4 → 5 → 6 → 7 → 8 → 9 → 10 → 11 → 12 → 13
                3 ──────────────────────────────────────────→ 14 → 15 → 16
```
Chapters 12–13 can be read after Chapter 7 by readers interested only in the foundations;
Chapter 14 needs only Chapters 1 and 3.

## What each chapter needs from the archive before it can be written

| Chapter | Reading needed (beyond proof-map level) |
|---|---|
| 2 | done (R3; written in `chapters/02-functional-equations-and-primitive-characters.md`) |
| 3 | done (R3; `landau_window`, `lemmaL`, `windowHyp_of_rpow`, `poleData`, `level_family`, `level_of_tiedWin`, `zeroFreeOn_of_levels` all read in full; written in `chapters/03-landau-window-criterion.md`) |
| 4 | done (R3 for all `CharacterBoxes/` and `MeanSquareBounds/` glue, `bad_share`, `winPairs`, `supplyChi`, `ExistsPageN`, `IsChiField`; R2 `[Lean]` for imported classical analytic sub-packages; written in `chapters/04-auxiliary-prime-pairs-and-host-fields.md`) |
| 5 | done (R3; `core_gm`, `ch_core`, `ch_top`, `ch_balance`, `proposition_size_bound`, `CoreAtH`, `EAtH`, `gmA_eq`, `sigA_le`, `level_gm_le_on_family_scales` all read in full; written in `chapters/05-the-square-root-barrier-core-gm.md`) |
| 6 | done (Stepanov–Bombieri function-field proof + R3 reading of `EvenCeil`, `DataParams₂`, `MeanBoundSecondForm`, `WeightedMeanData`, `QuotientSlopeBoundsWith`, `LevelOfCongruence`, `SChain`, `FamCore`, `ParConsts`, `TieGlobal`, plus post-audit precision fixes; written in `chapters/06-stepanovs-method-and-multiplicity.md`) |
| 7 | done (R3 reading of `Hyps`, `SiegelEisensteinSecondTermHypotheses`, `WeilTensorModels`, `LiftLambdaBound`, `BernsteinUnitaryProductIrreducible`, `TopPlug`, `TopShape`, `DesWin`, `LiftConvContGrowth`, `IntegrableThetaKernelProduct`, `ThetaChainUpwardLiftHeckeParamTransferred`, `FirstOccurrenceRuleThetaChainStepBothDirections`, `ThetaChainUpwardInductionFixedMetric`, `PairLiftOfHoweDualityBernstein`, plus post-audit precision fixes; written in `chapters/07-chains-of-theta-lifts.md`) |
| 8 | done (R3 reading of `WeilJacquetShalikaLaw`, `DataDIVDefs`, `DataParams₂`, `DataExtra`, `DefsInst`, `DataG`, `JointServices`, `GServT`, `DIVRecBridgeSel`; R2 for `FormalGroupSystem` and `trueColumns_row_sharp_bounds`; written in `chapters/08-divisibility-at-inert-primes.md`) |
| 9 | done (R3 reading of `LatticeSlopes/`, `HarderNarasimhan/` including `SlopeIneq`, `ShiftInvariance`, `StatementFrame`, `Example`, plus `DivisionHeightBoundStatement`, `GlobalBoundRefinements`, `GlobalTheoremInputs`, `TieGlobal`, and top wrappers `LinkG`/`LinkAltAltBis`; R2 for deep period cones; written in `chapters/09-heights-slopes-and-near-orthogonality.md`) |
| 10 | done (R3 reading of `DivinNOfHypV`, `IdempotentChoiceDepthZero`, `LengthHeckeValueIdealLeDeterminantBound`, `GlobalCongruenceCountOfRootDifferenceUnit`, `IntegralHeckeForms`, `ChosenTwistAnnihilatesSelmerGroups`, `LinkNAlongFamilyOfLocalBounds`, `LinkEta`, `GaloisCohomology/Statement`; R2 for imported DVR/cocycle/twisting sub-lemmas; written in `chapters/10-congruence-modules-to-sha.md`) |
| 11 | done (R3 reading of `ExistsPageN`, `IsChiField`, `StmtFields`, `LengthEqAddEigen`, `PrimeSetBoundDataOfPrimitiveChar`, `IsCMFieldOfIsChiField`, `ConductorBoundsOfIsChiField`, `minusle`, `ErrorTermsLeSqrtExpRpow`, `AdmissibleOfPageN`, `PointArith`, `ThmHV`, `CountVs`, `SumOut`, `FinalLe`, `JointWinOfCounts`, `PublishedTheorems/FerreroWashington`, `FerreroWashingtonIndex/FerreroWashington`, `ExistsIwasawaRankBoundOfFerreroWashington`, `LemmaK`, `KatoUse`, `TaylorWilesObstructionBound`, `WindowBoundOfLiteratureLevel`, `TopMainZj`, `VwinOfRow`; R2/R1 `[Open]` for deep 157,603-module proof cone; written in `chapters/11-the-window-bound-vwin.md`) |
| 12 | done (R3 reading of `MainConclusion`, `WeightsConjBis`, `RecT`, `WeakOfAtt`, `RowSrc`, `GaloisRepresentationsOfThetaLift`, `IntegralStructures/Development`, `WeightOneGeometricRealization`, `TLiftK`, `IsRecTOfIsRec`, `LocalCentralUnits/RecTExists`; R2 `[Open]` for deep 66,167-module and 26,672-module proof cones; written in `chapters/12-galois-representations-and-local-langlands.md`) |
| 13 | done (R3 reading of `LabelDatum`, `GreenRegularCharacters`, `SumRangeEqRoots`, `DiscreteSpectrumResidualClassification`, `StandardTheoremStatements/GlobalArtinReciprocity`, and top assembly of `EveryCharacterOfLiteratureOfVWin` and `TemperedProductOfSquareIntegrable`; R1/R2 `[Open]` for unreviewed named literature `Prop`s and 151,285-module proof cone; written in `chapters/13-greens-theorem-and-the-literature-layer.md`) |

## Next batch

Part IV Chapters 14–16 (completing the book: Masullo's adelic trace-formula route and its Chapter 10
spectral-nuclearity gap in `chapters/14-masullos-trace-formula-route.md`, the side-by-side structural
comparison of the two claimed proofs in `chapters/15-two-proofs-side-by-side.md`, and the consolidated
open-problems and verification checklist in `chapters/16-open-problems-and-what-remains.md`).

## Numbering note (2026-11-21)

`chapters/02-the-story-so-far.md` ("The story so far": a dated narrative of the two announcements and
of the verification effort, with every fact tagged [Author], [Community] or [Checked]) was added at
the owner's request under the filename prefix `02`, which the table above assigns to "One half-plane implies
everything". Its heading is `# The story so far` (with unnumbered sections) and in `SUMMARY.md` it is
placed as an unnumbered prefix chapter alongside `00-preface.md`, so the mathematical chapters retain
unambiguous numbering throughout the book (`chapters/02-functional-equations-and-primitive-characters.md`
as Chapter 2 through `chapters/05-the-square-root-barrier-core-gm.md` as Chapter 5). The story chapter
cites `sources/SOURCES.md`, Part II, by entry ID.
