# Proof map: the load-bearing skeleton of the Lean archive

Working note for the book. It records, top down from `Main.lean`, the chapter-sized blocks
that carry the argument, where each block lives in the archive, what it does mathematically,
how much of it *we* have read, and what (if anything) plays the same role in Masullo's draft.

- **Archive.** `lean.tar.gz` joined from the 14 parts at `https://alpo.ge/lean.tar.gz.partNN`,
  239,275,554 bytes, sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`
  (re-downloaded and re-verified 2026-11-21 04:01–04:06 UTC; see `sources/SOURCES.md`).
  Paths below are relative to the archive's `lean/` directory, so `src/Main.lean:4` means line 4
  of `lean/src/Main.lean`. Toolchain `leanprover/lean4:v4.33.1`; Mathlib pinned at
  `0df444a360eaa60ab8c11dca51a86af692955474` (tag v4.33.1).
- **Masullo.** *The Music of the Primes*, 940 pp., sha256 `e039d3f6…97bf5`; section numbers and
  printed page numbers (they coincide with PDF page numbers).
- **How the map was made.** A text-level index of all 1,057,807 declaration headers and the
  import graph of all 175,187 files (scripts and outputs in the run directory, see the end of
  this note), then a manual walk through proof terms starting at `Main.lean`. Community guides,
  in particular the LUMI docs (`aapolipponen/rh-lean-check-lumi`, `docs/02-proof-map.md`), were
  used for navigation only; every file:line below was located in our own extraction, and where
  our line numbers differ from a community guide we give ours.

## Reading levels used in this note

| Level | Meaning | Book tag it supports |
|---|---|---|
| **R3** | we read the declaration and its whole proof term | `[Lean, read]` |
| **R2** | we read the statement (type) and the top of the proof | `[Lean]` for the statement only |
| **R1** | we located the declaration and its type at file:line; the description of its *content* comes from the announcement or a community guide | `[Lean]` for existence; content is `[Paper]` (announcement), `[Community]` (community guide) or `[Open]` |

"Import cone" = number of archive modules transitively imported by the file that contains the
node's main declaration (text-level import graph; 175,187 modules in total). It is an upper
bound on what the node *can* use, not a measured dependency. Measured per-declaration
dependency counts exist in the LUMI audit (`results/per-declaration-dependencies.tsv`); we
have not reproduced them.

## The skeleton on one screen

```
P0  five target theorems (Main.lean)  ── statements in Statements.lean + Mathlib's RiemannHypothesis
 ▲
P1  functional-equation reductions (short, Mathlib only)
 ▲
P2  assembly: EveryCharacter  :=  L(s,χ) ≠ 0 for Re s > 1/2, all N, all χ
 ▲
P3  primitive → all characters (Euler factors)
 ▲
P4  zero-free engine: per cyclic "level", let ε → 0
 ▲            ▲
P5  Landau-window criterion         P6  core_gm:  Gm(x) ≤ x^{1/2+(eD+eL+7)ε} on windows
    (one-sided prime-sum bound           ▲  hypotheses: host data (EAtH) + chain data (CoreAtH)
     on windows ⇒ zero-free)             │
                                         ├── P13 auxiliary prime pairs (zero density, mean squares, Siegel)
                                         └── P7  chain data: m ≈ √x lifts, SizeData₂ clauses
                                               ├── P8  divisibility at inert primes (Conclusion1)
                                               ├── P9  slope inequality / heights (Bost)
                                               ├── P10 near-orthogonality of periods (LinkS, LinkG)
                                               └── P11 congruence modules ≤ Selmer + Ш (LinkN, HypV)
                                                      ▲
                                                     P12 window bound VWin on Ш of CM fields
                                                      ▲
P17 theta-lift chain families (Hyps)   P14 Galois representations (Row0b)   P15 partial local Langlands
P16 Green's classification (finite GL_d)   P18 "literature layer": ~250 named theorems proved as Props
```

The two halves have very different sizes. The analytic endgame (P3–P6, P13) sits in import
cones of 10 to about 1,300 modules; the arithmetic engine behind the hypotheses of `core_gm`
(P7–P12, P14–P17) sits in cones of up to 157,603 modules. Everything hard is hidden in Props
that `core_gm` takes as hypotheses and that are *proved* elsewhere in the archive.

## Node table

| ID | Block | Main Lean declarations (file:line) | What it does, in one sentence | We read | Import cone | Masullo counterpart |
|---|---|---|---|---|---|---|
| P0 | Target statements | `riemannHypothesis` … `LFunction_eq_zero_re_of_isPrimitive` (`src/Main.lean:4,6,8,10,12`); four Props (`src/Statements.lean:3,6,10,14`); Mathlib `RiemannHypothesis` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`) | RH for ζ, non-vanishing of every Dirichlet $L(s,\chi)$ on $\Re s>1/2$, and zeros of every Dirichlet $L(s,\chi)$ in $0<\Re s<1$ on the line, stated with Mathlib objects only. | R3 | Statements: 0 (Mathlib only) | Ch. 13 §13.3 (pp. 521–522): the GRH statement for Hecke L-functions of every number field is announced there but not yet stated as a theorem. Masullo's target is strictly larger. |
| P1 | Functional-equation reductions | `allChi`, `rhOfAll`, `critAll`, `claimAll` (`src/Supplements/Kernels/MainTheorems.lean:7,9,11,15`); `Formalism.VW.rh_of_every`, `critLine`, `gammaFactor_ne_zero` (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:29,11,6`); `Formalism.VW.rh_of_right` (`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5`); `Claim.strip`, `Claim.zeta`, `prim_zero`, `prim_reflect` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:59,75,23,42`) | All five targets follow from the single half-plane statement `EveryCharacter` by the functional equations of ζ and of primitive $L(s,\chi)$ and by removing the Euler factors that separate $\chi$ from its primitive character. | R3 | RhOfRight 0; ClaimStrip 1; CritLine 14,300 (through an import of `EveryCharacter.lean`, not used by the proofs) | Ch. 3 (idelic zeta functions, Tate's thesis; functional equation) and the intended §13.1. Same classical mathematics. |
| P2 | Assembly of `EveryCharacter` | `UpperTheory.EveryCharacter` (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13`); `UpperTheory.FinalTheorems.everyCharacter_of_row`, `everyCharacter` (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7,10`); `OpenLiteratureStatements`, `every_character_of_literature_of_vWin` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215,810`); `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` (`…/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69`); `UpperTheory.Top.zero_free_all_of_green_v_win`, `every_character_of_green_v_win` (`…/ThirdPlaceSeries/TopPlug.lean:12,16`) | `EveryCharacter` is obtained from four packages — Galois representations (`Row0b`), a partial local Langlands map (`RecTExists`), the window bound `VWin`, and a bundle of theta-lift hypotheses (`HypsAlt`) together with Green's theorem — after a long list of named "literature" theorems has been proved and passed in. | R2 (proof terms of the five assembly theorems read; the bundle fields not) | MainConclusion 175,173; EveryCharacterOfLiteratureOfVWin 151,285; SiegelEisenstein… 112,384; TopPlug 17,275 | None. |
| P3 | Primitive → all characters | `UpperTheory.Top.imprimitive` (`src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5`) | Zero-freeness of primitive $L(s,\chi^*)$ on $\Re s>1/2$ gives it for every $\chi$, because $L(s,\chi)=L(s,\chi^*)\prod_{p\mid N}(1-\chi^*(p)p^{-s})$ and each factor has modulus $\ge 1-p^{-\Re s}>0$. | R3 | 10 | Implicit in Masullo's use of primitive Hecke characters (Ch. 3); same classical step. |
| P4 | Zero-free engine (limit $\varepsilon\to0$) | `UpperTheory.Top.TopG`, `zeroFreeAll_of_topG` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:12,26`); `ChebyshevInequalityOnWindows`, `ChebyshevInequalityAtWindowScale`, `level_of_tiedWin`, `zeroFreeOn_of_tiedWin`, `zeroFreeOn_of_tiedWin_cyc` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean:26,30,68,83,90`); `PChar.ZeroFreeAbove`, `ZeroFreeOn`, `ZeroFreeAll`, `Level.Gm`, `Level.cyc` (`…/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:11,14,18,38,121`) | For each primitive $\psi$ the archive works with the cyclic group of characters generated by $\psi$ (a "level"); it combines (a) the bound $G_m(x)\le x^{1/2+(e_D+e_L+7)\varepsilon}$ on windows, (b) the Landau-window criterion, and (c) the existence of windows at every scale, and lets $\varepsilon\to0$. | R3 (all three files read in full; upstream proof of `TopG` in P16–P17 remains R2) | ZeroFreeAllOfTopG 753; TopWin 218; ExplicitFormula… 9 | None (Masullo's zeros-to-primes link is the explicit formula, not a positivity/limit argument). |
| P5 | Landau-window criterion | `UpperTheory.Comparison₂.formB` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/Imports.lean:8`); `UpperTheory.Comparison₂.level_family` (`…/PrimitiveCosets/LevelFamily.lean:41`); `Level.FormBAt`, `Level.FormB`, `HasWindows` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Window.lean:30,33,7`); `Deduction.zeroFree_of_rpow_window` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean:11`); `Deduction.windowHyp_of_rpow` (`…/LandauTheorems/WindowHypOfRpow.lean:27`); `Deduction.lemmaL` (`…/LandauTheorems/lemmaL.lean:13`); `Deduction.poleData` (`…/LandauTheorems/poleData.lean:248`); `Deduction.landau_window` (`…/LandauTheorems/landauWindow.lean:83`); `Deduction.PoleData`, `WindowHypU` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean:15,25`); `Deduction.Gchi`, `CharFamily`, `Gm`, `ZeroFree` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean:15,24,36,38`); `Formalism.Sz`, `Formalism.Gz` (`src/Formalism/StatementOC.lean:11,13`); `An.gChi` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:23`) | If a positive combination $G_m$ of the normalized Riesz prime sums $\sum_{n\le x}\Lambda(n)\chi(n)(x/n-1)$ satisfies the one-sided bound $G_m(x)\le Cx^{\theta}$ for all $x$ in windows $[Y,Y^{1+\delta}]$ with $Y$ arbitrarily large, then no $L(s,\chi)$ in the family vanishes on $\Re s>\theta$ (a Landau/Pólya argument on a Laplace transform whose poles are the zeros). | R3 (whole `LandauTheorems/` subtree for `poleData` and `landau_window`, plus `LevelFamily`, `GzEq`, `GChiEq`, `Imports`, `Window`) | landauWindow 15; Window 10; formB file 131 | App. B.4 "Explicit Formulas for Hecke L-functions" (pp. 606–625) and the planned §13.1 play the same *role* (zeros ↔ primes); the mechanism differs. |
| P6 | The bound at exponent 1/2 (`core_gm`) | `level_gm_le_on_family_scales`, `tiedCore_of_chainTied` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean:28,13`); `windowInequality_of_artinInputs`, `FamCoreConstantBounds` (`…/PrimitiveCosets/WindowInequalityOfArtinInputs.lean:17,11`); `UpperTheory.Comparison₂.core_gm` (`…/PrimitiveCosets/CoreGm.lean:12`); `CoreAtH` (`…/PrimitiveCosets/CoreAtH.lean:29`); `Deduction.ch_core` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:343`); `Deduction.ch_top` (`…/LandauTheorems/ChTop.lean:37`); `Deduction.CH.ch_balance` (`…/LandauTheorems/ChBalance.lean:200`); `proposition_size_bound` (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507`); `Formalism.HC.EAtH` (`…/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:144`) | Given host data `EAtH` and chain data `CoreAtH` at scale $x$, finite Fourier projection on $E_0\times\varphi.A$ and the four-term chain size bound (`SZ.T1`–`SZ.T4` at $x^{1/2-\varepsilon}\le m\le x^{1/2+\varepsilon/2}$) give $\Lambda.\mathrm{Gm}(x)\le x^{1/2+(e_D+e_L+7)\varepsilon}$. | R3 (entire `PrimitiveCosets/` subtree plus `ChCore`, `ChTop`, `ChBalance`, `SplitInertia`, `LipschitzWeightAndMinimum`, `LevelOfCongruence` read in full; upstream proof of `ChainTied` in P7 remains R2) | CoreGm 114; LevelGm… 406 | None. Masullo has no Chebyshev-type bound; in his set-up the critical line enters through the shift $L(s+1/2,\chi)$ and the factor $\lvert\cdot\rvert_F^{1/2}$ in the "Fundamental Divisor Exact Sequence" (§1.2.1, pp. 12–15, especially p. 13). |
| P7 | Chain data (`ChainTied`, `SizeData₂`) | `Formalism.MainNotions.ChainTied` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97`); `SizeData₂` (`src/Formalism/SizeWindowBrackets/SChain.lean:17`); `each_unit_bound_statement` (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`); `proposition_size_bound` (`…/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507`); `GlobalTheory.Mem.Num.evenCeil`, `eAt`, `mAt` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:11,15,21`) | At each scale the archive packages a chain of $m$ lifts with eleven conjoined clauses (Hida setting, divisibility `DIV`, slopes, loss bounds, slope inequality, height bound, …); `mAt` defines $m=2\lceil\sqrt{x\,\delta_1}/2\rceil$ and `eAt` a 2-power level $\approx x^{2+8\varepsilon}$. | R2 (definitions); R1 for the meaning of the clauses | TieGlobal 303; SChain 19; EvenCeil 342 | None. (Masullo's "multiplicity" in §7.1 and §14.1 means multiplicity of zeros or poles, a different notion.) |
| P8 | Divisibility at inert primes | `Formalism.MainNotions.WeilJacquetShalikaLaw.Conclusion1` (`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97`) | The columns of the chain are divisible at places of the host that are inert, to an order given by the accumulated gains — the integer analogue of the high vanishing order of Stepanov's auxiliary function. | R1 (definition header read; proof not located by us) | 321 | None. |
| P9 | Slope inequality and heights | `Formalism.HN.SlopeIneq` (`src/Formalism/HarderNarasimhan/Statement.lean:91`); `Formalism.L2.DIV.DivClauses`, `height_chain`, `divClauses_of` (`src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:553,641,752`); `Formalism.DivisionValues.divisor_inequality_explicit` (`src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:91`) | Bost's slope inequality: a nonzero map of Hermitian lattices of operator norm $\le C$ forces $\hat\mu_{\min}(L)-\log C\le\hat\mu_{\min}(\text{image})$ and $\hat\mu_{\min}(L)\le\hat\mu_{\max}(M)+\log C$; this converts p-adic divisibility plus archimedean size into a numerical inequality on the chain. | R2 for `SlopeIneq`; R1 otherwise | Statement 1; DivisionHeight… 763 | None. |
| P10 | Near-orthogonality and gains (`LinkS`, `LinkG`) | `Formalism.MainNotions.LinkG`, `LinkS`, `LinkN` (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:138,152,45`) | Period vectors attached to different chain words are nearly orthogonal (defects $\le\exp(-x^{\varepsilon/8})$), and the gains control the analytic sums; the announcement attributes these to norms of lifts, Chowla–Selberg, Siegel mass and Rallis/Bessel periods. | R2 (definitions) | 306 | None. Masullo's trace formula (Chs. 10–12) is on the idele class group $C_F$, not a relative trace formula on unitary groups. |
| P11 | From congruences to Ш | `UpperTheory.Top.HypV`, `divinN_of_hypV` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10,117`); `GlobalTheory.CutCoreUnit.main` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:44`); `TwistingCharacterExistence` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:166`) | The excess divisibility of each lift (a congruence number) is bounded by a Selmer length plus $\sum_e \operatorname{len}Ш^1(\mathbb Q_\ell/\mathbb Z_\ell(-e))$ plus $v_\ell(h_E)$ plus tame terms; `HypV` supplies the Ш part from `VWin`. | R2 (statements of `HypV`, `divinN_of_hypV`, `CutCoreUnit.main`) | DivinNOfHypV 311; CutCoreUnit 3,287 | None. |
| P12 | The window bound `VWin` | `VVle`, `IsChiField`, `WinPair`, `PageN`, `VAt`, `VWinAt`, `VWin` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12,19,27,39,41,44,49`); `UpperTheory.One.vwin_of_row` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`); `automorphic_window_of_inputs` (`…/DenseThresholdCases/TopMainZj.lean:71`); `UpperTheory.V.HV.vwin_of_counts` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/JointWinOfCounts.lean:30`); `ShaPlus`, `ShaMinus`, `vvle_of_parts` (`…/AutomorphicVarieties/LengthEqAddEigen.lean:68,71,127`); `ThmBab`, `ThmBcFree` (`…/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:49,64`); `UpperTheory.V.U3.PropGK` (`…/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:36`); `UpperTheory.V.FW.ferreroWashington` (`…/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104`); `UpperTheory.V.LemmaK` (`…/AutomorphicVarieties/GeneratorCountTuples/LemmaK.lean:13`); `UpperTheory.V.Pa.PfromAut` (`…/AutomorphicVarieties/PatchingModules/TaylorWilesObstructionBound.lean:150`) | For the abelian "host" fields $E\subset\mathbb Q(\zeta_N)$ cut out by $\psi$, the Jacobi symbols mod $q,d$ and a 2-power level (`IsChiField`; complex conjugation is excluded because $q\equiv3\bmod 8$, so $E$ is CM), the sum over any finite set of primes $\ell$ of $\log\ell\cdot\sum_{1\le e<\lfloor x^{401}\rfloor}\operatorname{len}_{\mathbb Z_\ell}Ш^1(G_{E,S_\ell},\mathbb Q_\ell/\mathbb Z_\ell(-e))$ is at most $\exp(x^{\varepsilon}/2)$ (`VVle`, `VAt`; the length is `Formalism.GaloisCohomology.shaLen`, `src/Formalism/GaloisCohomology/Statement.lean:78`); it is split into an $\ell=2$ part, a minus part (Bernoulli numbers / Euler systems) and a plus part (U(3) congruences and a residually reducible modularity theorem), with Ferrero–Washington for $\mu=0$. | R3 for `ExistsPageN.lean` and `IsChiField.lean`; R2 for the statements of `vwin_of_counts`, `vvle_of_parts`; R1 for the rest | VwinOfRow 157,603 (largest block); TopMainZj 157,602; KatoUse 1,713; TaylorWiles… 1,711 | None. |
| P13 | Auxiliary prime pairs | `UpperTheory.Top.PairGood`, `PairEx` (`src/Development/AutomorphicArithmetic/CharacterBoxes/PairGood.lean:18,28`); `QH.pairEx` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112`); `QH.stage` (`…/MeanSquareBounds/StagePow.lean:41`); `…ZD.zero_density_box` (`src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/CountZAll.lean:13`); `QH.twistK`, `QH.meanSqK`, `QH.bad_share` (`…/MeanSquareBounds/twistK.lean:148`, `…/meanSqK.lean:51`, `…/BadShare.lean:251`); `UpperTheory.Top.winPairs` (`src/Development/AutomorphicArithmetic/CharacterBoxes/WinPairs.lean:5`); `UpperTheory.Top.supplyChi` (`…/CharacterBoxes/SupplyChi.lean:8`) | For every large $Y$ there are primes $q\equiv3\ (8)$ and $d\equiv7\ (16)$ with $\log q\approx Y^{\varepsilon/5}$ and $\log d\approx Y^{\varepsilon/5}(\log Y)^2$ such that the parasitic quadratic twists have square-root bounds on their prime sums over $[Y,Y^A]$ and no zeros in boxes of width $1/400$; this uses only zero-density estimates, mean squares over the family and Siegel's theorem, and supplies the CM host fields used by `VWin` and `core_gm`. | R3 for all `CharacterBoxes/` and `MeanSquareBounds/` files plus `supplyOfAdmOf`, `MSqMain`, `ConjEMemHostFIff`, `HostFacts` (Chapter 4); R2 for imported `zero_density_box`, `box_tail_bound`, `twist_bound`, `pnt_progressions_relative_weak_holds`, `excBound`, `hostOfField` | StagePow 260; pairEx 292; SupplyChi 1,329 | App. B.1 (convexity bound, pp. 588–591) and App. B.6 (classical zero-free regions, pp. 636–643) are the nearest classical analytic inputs; Masullo does not use families of twists or zero-density estimates. |
| P14 | Galois representations | `UpperTheory.GalStar.Row0b` (`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:69`); `galoisLocalGlobalStrong_recParameter` (`…/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`); `galoisRepresentations_of_thetaLift` (`…/IntegralStructures/GaloisRepresentationsOfThetaLift.lean:6`); `UpperTheory.TP.K.tLiftK` (`…/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean:4`); `UpperTheory.Gal.Int.Geo.geoOne_holds` (`…/IntegralStructures/GeometricFlagBases/WeightOneGeometricRealization.lean:11`) | To each regular algebraic polarized cuspidal representation of $\mathrm{GL}_a$ over a CM field the archive attaches an $\ell$-adic Galois representation with prescribed Hodge–Tate weights and a weak local–global compatibility (properties bundled in `PropsB`). | R2 (statement of `Row0b`; one-line proofs of `RowSrc`, `GaloisRepresentationsOfThetaLift`) | RowSrc 66,167; GaloisRep…OfThetaLift 61,080; WeightOne… 45,859 | None (Masullo works with $\mathrm{GL}_1$ / Hecke characters only). |
| P15 | Partial local Langlands | `UpperTheory.Zero.LLC.IsRecT`, `RecTExists` (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:76,78`); `UpperTheory.Zero.LLC.recTExists` (`…/LocalLanglands/LocalCentralUnits/RecTExists.lean:20`) | At every finite place of a number field there is a map from irreducible representations of $\mathrm{GL}_n(E_w)$ to Weil–Deligne representations obeying a restricted list of laws (`LawsT`), a weak form of local Langlands. | R2 (definitions; first lines of the proof) | RecTExists 26,672; IsRecTOfIsRec 1,063 | Ch. 3 treats local Tate theory, i.e. the $\mathrm{GL}_1$ case (local class field theory); no higher-rank analogue. |
| P16 | Green's classification | `GlobalTheory.GLq.Green` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108`); `GlobalTheory.GreenBridge.green_of_regular` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumRangeEqRoots.lean:225`); `UpperTheory.Top.shape_closed_link_n_of_green` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33`) | For prime fields $\mathbb F_g$ ($g$ prime), cuspidal irreducible characters of $\mathrm{GL}_d(\mathbb F_g)$ are parametrized injectively and exhaustively by labels, with degree $\prod_{i=1}^{d-1}(g^i-1)$; this is used to shape the chain families. | R2 (statement of `Green`) | LabelDatum 199; SumRangeEqRoots 232; TopShape 16,990 | None. |
| P17 | Theta-lift chain families | `GlobalTheory.Fc.HypsAlt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Hyps.lean:22`); `UpperTheory.Lit.nonempty_hyps_definite_side_of_closed_bound` (`…/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44`); inputs `ThetaIntegralsAgree`, `LocalMatching` (`src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/WeilTensorModels.lean:585,581`), `CovolumeBoundOfX` (`…/ThirdPlaceSeries/LiftLambdaBound.lean:60`), `UnitaryGroupThirdPlaceHypotheses` (`…/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:22`) | Constructs, from Howe duality, Siegel–Weil, matching of theta integrals and covolume bounds, the families of iterated theta lifts between definite unitary groups whose rows, twists and divisibility rows the chain data of P7 require. | R2 (statement and first 10 lines of the proof of `nonempty_hyps_definite_side_of_closed_bound`; the `HypsAlt` fields) | SiegelEisenstein… 112,384; Hyps 14,732 | None. Masullo's Ch. 2 "Adelic θ-functions" are $\mathrm{GL}_1$ theta series of Tate's thesis — the same word, a different object. |
| P18 | Literature layer | `UpperTheory.LiteratureTheorems.OpenLiteratureStatements` and the `*_of_literature` theorems assembled in `…/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215–813` | Named classical theorems (Poitou–Tate, Ferrero–Washington, Kawamata–Viehweg, arithmetic Hilbert–Samuel, Siegel–Weil, …) are stated as Props in `GlobalTheory.Published.*` and proved inside the archive; whether each Prop says what its name claims is a separate question. | R1 (we counted 257 theorem headers in `UpperTheory.LiteratureTheorems.*` by text index, 176 of them named `*_of_literature`) | — | Masullo's Appendices A–E play the background role but cite the literature instead of re-proving it. |

## Notes on individual nodes

**P0–P1 (read in full).** The four definitions of `Statements.lean` and Mathlib's
`RiemannHypothesis` are the whole trusted statement surface. `Main.lean:6` proves
`RiemannZetaZerosOnLine` with the same term `rhOfAll` that proves Mathlib's `RiemannHypothesis`
at `Main.lean:4`, so the kernel has checked that the two Props are definitionally equal; the
same holds for `DirichletLNonvanishingRightOfHalf` versus `UpperTheory.EveryCharacter`
(`Main.lean:8`). The reductions in `ClaimStrip.lean` import only `HalfPlane.lean`, which imports
only Mathlib. Detail and prose: Chapter 1.

**P2 (two assembly routes).** The archive contains a second assembly of `EveryCharacter`,
`UpperTheory.Top.plugAll` (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:16`),
and a second derivation of RH, `UpperTheory.FinalTheorems.riemannHypothesis`
(`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:13`) via
`UpperTheory.riemannHypothesis_of_everyCharacter`
(`src/Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:215`).
`Main.lean` uses neither: its route is `MainTheorems.lean:7` →
`MainConclusion.lean:10` → `EveryCharacterOfLiteratureOfVWin.lean:810` →
`SiegelEisensteinSecondTermHypotheses.lean:69` → `TopPlug.lean:16`. (The LUMI compiled-term walk
reports 146,437 of 175,187 project modules used in the closure of `Main.lean` [Community]; which
specific side routes lie outside that closure we have not checked ourselves [Open].)

**P4–P6 (the logical shape of the endgame).** In `zeroFreeAll_of_topG` the three inputs of
`zeroFreeOn_of_tiedWin_cyc` are: `level_gm_le_on_family_scales` (P6), `formB` (P5), and the
window-scale data obtained from `TopG` and the host supply `supplyChi` (P13, P12). `TopG` is
not an analytic statement; it is proved from Green's classification and the theta-lift
hypotheses (P16, P17) in `TopPlug.lean:12`. This is the point where the arithmetic engine
enters the analytic endgame.

**P6 → P7 (where the weight is).** `core_gm` has a small import cone (114 modules) because its
content is in its hypotheses: `EAtH` and `CoreAtH` are Props. Their proofs come from the
families built in P17 and the clauses of P7–P11; they are attached in
`tiedCore_of_chainTied` (`LevelGmLeOnFamilyScales.lean:13`). A book chapter on `core_gm` can be
honest and short; the chapters behind its hypotheses cannot.

**P8 (line-number discrepancy).** The LUMI map cites `WeilJacquetShalikaLaw.lean:101` for
`Conclusion1`; in our extraction the `def Conclusion1` header is at line 97 (its last line is
101). Likewise `LinkS` is at `GlobalTheoremInputs.lean:152` in our extraction (LUMI: 145).
We cite ours.

**P12 (size).** `VwinOfRow.lean` (6 lines) imports a cone of 157,603 modules, 90% of the
archive. By import weight the window bound is the largest single component of the proof.

**P18 (fidelity of names).** That a Prop is called `PoitouTateDuality` does not make it Poitou–Tate
duality. The LUMI doc 07 reports verdicts on 105 such statements. For the book every
"literature" input must be tagged `[Lean]` for the Prop that is proved and `[Open]` for the
claim that it matches the published theorem, until someone has compared the two.

## Masullo's route in the same format (for the comparison chapters)

| Masullo | Content (our summary) | Role relative to the Lean skeleton |
|---|---|---|
| Chs. 2–3 | adelic θ-functions and idelic zeta functions (Tate's thesis, functional equation, Weil's identity) | P1 (functional equation): same classical content |
| Chs. 4–9 | Schauder bases, spaces of θ-functions, local–global structure, orbits, Hardy–Sobolev topologies | no Lean counterpart |
| Ch. 10 | trace formula, spectral side (zeros counted with multiplicity on a Hilbert-space completion) | no Lean counterpart; known gap at p. 451 after (10.3.1.18) (resting on Terminology 10.2.1.2(2), p. 444): Yan Ru Pei (`doi:10.5281/zenodo.24409811`) proposes an unreviewed partial repair on the critical line $I = \{0\}$ only [Community], leaving the positive-width strip case $I = [-\alpha, \alpha]$ needed by Theorem 12.5.1.1 unrepaired [Open] |
| Chs. 11–12 | shell structure; trace formula, geometric side; Main Theorem 12.5.1.1 (p. 519) | no Lean counterpart |
| Ch. 13 (pp. 521–522) | intended deduction of GRH for Hecke L-functions from 12.5.1.1; only Theorem 13.3.1.1 (restatement of the trace formula) is written | P0 (same type of conclusion, larger scope) |
| Ch. 14 | multiplicities of zeros, function fields, higher rank | none; §14.2 (function fields) is relevant to the Stepanov motivation of P7–P8 |
| App. B | convexity bound, explicit formulas, zero-free regions | P5 and P13 (classical analytic inputs) |

The two arguments share only the classical frame (functional equations, explicit-formula-type
links between zeros and primes). Their engines are disjoint: an adelic trace formula on
$C_F$ versus a Stepanov-type auxiliary construction made of theta lifts, controlled by
Iwasawa theory and Galois cohomology.

## Reproducibility

Run directory: `/Users/lihongmin/Hermes/state/quota/runs/rhbook-architecture-11211200/`.

- `fetch_lean_parts.sh`, `fetch_lean_parts.log`, `headers/` — download, per-part sha256 and ETag.
- `build_index.py` → `index/decls.tsv.gz` (name, kind, file, line), `index/imports.tsv.gz`,
  `index/files.tsv.gz`; 24 s CPU.
- `index/import_cones.json` — the import-cone sizes quoted above.
- `static_scan.py` → `static_scan.json` — text scan used in Chapter 1; 123 s CPU.
- `check_citations.py` → `citations_report.txt` — machine check that every `src/…:line` and
  `Mathlib/…:line` in `chapters/` and `notes/` resolves to an existing line of the pinned
  sources and that a declaration named nearby appears on that line; the citations it cannot
  match automatically (a cited `import` line, a docstring, a name only in a code block) are
  listed for manual review and were checked by hand before each commit.
- `kexactB_family_files.txt` — the 72 files that mention `kexactB`, `kc%`, `tr_via` or
  `tr_clause` (Chapter 1, Section 1.5.4).

All computations ran single-threaded under `nice -n 19`; total CPU well under 10 minutes.
