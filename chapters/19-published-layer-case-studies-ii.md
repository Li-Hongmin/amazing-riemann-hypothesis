# Chapter 19. Published layer case studies II

> **Status tags used in this chapter:** `[Lean, read]` for definitions, wrappers and local
> deductions read line by line (`R3`), including the main-path producer and consumer lines of
> Sections 19.0, 19.3, 19.4 and 19.6; `[Lean]` for declarations cited at statement level (`R2`);
> `[Paper]` for the published sources; `[Expository]` for our comparisons and worked examples;
> `[Open]` for proof cones, readers and normalizations that we have not traced.

Chapter 18 compared fourteen `Published` propositions with the theorems their names evoke. This
chapter treats six more, all from the automorphic side of the archive: two existence theorems for
Galois representations (Shin; Chenevier–Harris) and four statements from the theta and doubling
machinery (absolute convergence of theta integrals; the global doubling method; the unramified
doubling integral at a split place; the Rallis inner product formula in the convergent range).

For each proposition we ask two questions. The first is the fidelity question of Chapter 18:
does the `Prop` say what the paper says? The second is new here: where does the proof of
`src/Main.lean` actually touch the proposition? An `import` line only shows that a module is
reachable. A proposition is *used* when a proof term mentions it: a theorem that proves it (a
producer), and a theorem that takes it as a hypothesis or reads it out of a bundle (a consumer).
We follow such terms from the main theorem downwards and read the shortest producer–consumer
pairs line by line.

The answer differs sharply between the two groups. The two Galois propositions are never
mentioned by any proof term in the pinned archive. The four automorphic ones are produced in the
literature layer and handed to the main assembly, but in one case the proposition handed over is
a weakened variant of the one whose name appears in the published-theorem files.

## 19.0 How the main path reaches the literature layer

**Motivation.** Chapters 11–13 reached the literature layer from below, through `VWin` and the
local Langlands interfaces. Here we start at the top. The final theorem of the archive is three
lines long, and each of its lines names the next term to open.

**Definition 19.1 (the row and the literature bundle).** Write `Row0b recT` for the statement
`UpperTheory.GalStar.Row0b` with the reciprocity notion `recT`. It asserts: for every CM field
$E$ with algebraic closure $\Omega$, prime $\ell$, comparison isomorphism $\iota$, rank $a\ge1$,
cuspidal representation $\pi$ that is regular algebraic and forms a polarized pair with a Hecke
character $\chi$ of the maximal totally real subfield, there are a representation
$r : G_E\to\mathrm{GL}_a(\overline{\mathbb Q}_\ell)$, a weight and a Hodge–Tate multiset satisfying
the property bundle `PropsB` (continuity, semisimplicity, local–global compatibility away from
$\ell$, weights, and the clauses above $\ell$). See
`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:54–73`.
The literature bundle `OpenLiteratureStatements` has three fields: two copies of this row
(`caraianiLocalGlobalDual`, `galoisRepOfPolarizedPairLit`) and the existence statement
`localLanglandsExists`. See
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215–218`. [Lean, read]

**Lemma 19.1 (the top of the main path).**

1. `riemannHypothesis` is `riemannHypothesis_of_everyCharacter everyCharacter`, and
   `everyCharacter` is `everyCharacter_of_row galoisLocalGlobalStrong_recParameter`.
2. `everyCharacter_of_row h` feeds the literature assembly with the bundle
   $\langle h, \mathtt{recTExists}, h\rangle$ and with `vwin_of_row h`.
3. The row itself is produced by the archive's theta-lift construction:
   `galoisLocalGlobalStrong_recParameter` is `galoisRepresentations_of_thetaLift tLiftK`, which is
   `galoisLocalGlobalStrong_of_geometry_lift geoOne_holds tLiftK`, which applies `Row0.row0b` to
   `rest (coreAll_of …)`.
4. The literature assembly `every_character_of_literature_of_vWin O hV` passes the bundles
   `published_results_eigen O` and `published_results_first O` to
   `every_character_of_theta_integrals_local_matching`.

*Proof.* (1) and (2) are the three theorems of
`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7–14`. (3) is
`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`,
`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GaloisRepresentationsOfThetaLift.lean:6`
and `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/Development.lean:18–31`.
`Row0.row0b` only weakens the property bundle `Props` to `PropsB` field by field
(`src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjBis.lean:75–86`).
(4) is `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810–812`. $\square$ [Lean, read]

The deep lemmas named in (3), `coreAll_of_core` and
`galoisLocalGlobal_of_localGlobalCompatibility`, are cited here at statement level. [Lean]

**Remark (what the table below records).** For each proposition we list the theorem that
produces it on the main path, the place where the literature layer hands it on, and the first
line we found that reads it.

| Proposition | Producer on the main path | Handed on at (`EveryCharacterOfLiteratureOfVWin.lean`) | First reader found |
|---|---|---|---|
| `ShinGaloisRep` | none | none | none (Lemma 19.2) |
| `ChenevierHarris` | none | none | none (Lemma 19.2) |
| `WeilThetaConvergence` | `UpperTheory.Lit.weilThetaConvergence` | `:483–484` | `rallis_of_dm`, Section 19.3 |
| `DoublingMethod` | replaced by `DoublingMethodLocalZetaIntegrals` | `:371–372`, `:654`, `:678`, `:740` | `rallis_of_dm` and two bundle readers, Section 19.4 |
| `UnramifiedDoublingGL` | `GlobalTheory.UnramDoublingProof.unramifiedDoublingGL` | `:529–530`, `:655`, `:679`, `:741` | two bundle readers, Section 19.5 |
| `RallisInnerProductConvergent` | `rallis_of_dm` | `:485–486`, `:739` | not found, Section 19.6 |

## 19.1 Shin's Galois representation

**Motivation.** Local compatibility can preserve the monodromy operator or only the
characteristic polynomials of Weil elements. The distinction matters at ramified places.

**Example.** In rank two the decreasing infinity parameters $(3/2,1/2)$ have gap $1$,
which fails the strict slight-regularity test. The pair $(5/2,1/2)$ has gap $2$ and passes
the numerical test. These are tests of the guard for proposed infinity data. [Expository]

**Definition.** `ShinGaloisRep` universally quantifies over CM fields, primes and cuspidal
representations of rank $a\ge2$ that are conjugate self-dual, regular algebraic and
`OddOrSlightlyReg`. It supplies one continuous semisimple representation. Away from
$\ell$, the equality uses `algNorm` of an explicitly equivalent contragredient.
At coefficient-prime bridges it supplies potential semistability, prescribed jumps, and
crystalline or semistable assertions under the spherical or Iwahori conditions respectively.
See `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/ShinGaloisRep.lean:13–31`. [Lean]

| Polarity | Clause |
|---|---|
| Input | Odd rank or one strict gap at an even index |
| Output | One global representation, then local assertions for every eligible choice |
| Input to local clause | A tied period-ring system and an inducing bridge |

**Lemma (parity guard).** At even rank, `oddOrSlightlyReg_iff_of_even` removes the odd-rank
disjunct by contradiction and introduces the other disjunct directly. The auxiliary
`SlightlyRegAll.slightlyReg` takes the pair of indices $0,1$ using $a\ge2$.
See `src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/OddOrSlightlyRegIffOfEven.lean:16–35`. [Lean, read]

**Lemma 19.2 (the two Galois propositions are never used).** In the pinned archive the names
`ShinGaloisRep` and `ChenevierHarris` each occur on exactly three lines: the definition, and an
`import` of the defining file in
`src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ClauseAtOfRepIso.lean:17–18` and in
`src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SphericalContragredientMonomial.lean:17–18`.
Hence no theorem proves either proposition, no theorem assumes it, and no structure has a field
of that type. [Lean, read]

*Proof.* A Lean term can refer to a constant only through its name, and neither definition
carries an attribute that would let a tactic find it. We searched every line of the 175,187
`.lean` files of the pinned tarball for the two names and read each of the six hits. The count is
easy to reproduce: `tar -xzOf lean.tar.gz | grep -c ShinGaloisRep` prints `3`, and likewise for
`ChenevierHarris`. $\square$

The row of Definition 19.1 is the archive's own replacement. Lemma 19.1(3) shows that the main
path obtains it from the theta-lift construction, so neither Shin's theorem nor
Chenevier–Harris enters the proof of `src/Main.lean` under these names. The local clauses that
both propositions share with the row are separate definitions (`ClauseAt` in Section 19.2).

**Comparison.** Shin's Theorem 1.2 says “$\Xi$ is slightly regular, if $m$ is even” and
“an isomorphism of Weil-Deligne representations” in (i). The parity and the full local
comparison have counterparts in the Lean interface. The paper also enumerates purity
conditions in (ii)–(iii). [Shin2011]

**Remark (status).** The earlier question whether `Row0b` consumes this proposition directly is
settled by Lemmas 19.1 and 19.2: it does not, and no archive proof of the proposition exists.
What remains is a fidelity question about a statement the main path never uses: the comparison
of Shin's normalization with `wdOf` and the contragredient in the Lean clause is [Open].

## 19.2 Chenevier–Harris and monodromy

**Motivation.** A bound on monodromy, vanishing of monodromy, and equality of Weil
characteristic polynomials are distinct outputs.

**Example.** On a two-dimensional space take Frobenius with matrix
$\operatorname{diag}(q^{-1},1)$ and trivial inertia. Both $N=0$ and $N=E_{12}$ satisfy
$FNF^{-1}=q^{-1}N$. The characteristic polynomials coincide on every Weil element
while the monodromy ranks are $0$ and $1$. [Expository]

**Definition.** `ChenevierHarris` takes a conjugate self-dual cohomological cuspidal
representation over a CM field with $a\ge2$. It produces a continuous semisimple
representation with Weil characteristic-polynomial equality away from $\ell$ and
`mono0` at spherical places away from $\ell$. At inducing period-ring bridges the
conclusions are de Rham, jumps with shift $(a-1)/2-z$, and crystallinity under a
spherical hypothesis. See
`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/ChenevierHarris.lean:13–31`. [Lean]

| Polarity | Clause |
|---|---|
| Input | Cohomological and conjugate self-dual |
| Output | One representation with all the local conclusions |
| Input to conditional output | Spherical local component for `mono0` or crystallinity |

**Lemma (transport of local clauses).** The related `ClauseAt` separates characteristic
polynomials, purity, de Rham with jumps, crystallinity and the Iwahori clause. Its transfer under
`RepIso` conjugates the Weil representation and the restrictions to decomposition groups.
The `ss` and `pure` clauses rewrite via `wdOf_eq_of_conj`. The de Rham and crystalline
clauses use `local_conj`; the Iwahori branch transports semistability and then `wdAt`.
This is a transport lemma for local clauses.
See `src/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/IsWeight.lean:25–48`
and `src/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ClauseAtOfRepIso.lean:31–60`. [Lean, read]

`ClauseAtOfRepIso.lean` imports the files defining `ShinGaloisRep` and `ChenevierHarris`, but its
proofs use only `ClauseAt` and the transport lemmas. This is the import-without-use pattern of
Lemma 19.2.

**Comparison.** The published introduction refers to “the partial ordering on the
associated Weil-Deligne representations” and says the representation “is de Rham
(in Fontaine’s sense).” The former includes monodromy information beyond a
characteristic-polynomial test. The latter parallels the inducing-bridge clause.
The paper's crystalline Frobenius polynomial comparison is additional data.
[ChenevierHarris2013]

**Remark (status).** By Lemma 19.2 the archive neither proves nor uses `ChenevierHarris`, so the
question of its use by `Row0b` is closed. The comparison above describes an unused interface;
the paper's own proof is outside the archive and is not audited here.

## 19.3 Absolute theta convergence

**Motivation.** The inner product argument integrates a theta kernel along a quotient.
Absolute convergence is an input to that step.

**Example.** At target rank $6$ and Witt index $2$, theta degree $3$ passes
$3+2<6$ and degree $4$ fails $4+2<6$. The numerical equality case gives no
convergence conclusion from this interface. At Witt index zero the separate
anisotropic disjunct applies, for instance at degree $5$ and rank $6$. [Expository]

**Definition.** `WeilThetaConvergence` assumes $n\ge1$ and Witt index zero or
$n+\operatorname{wittIdx}(V)<\operatorname{rank}(V)$. For every eligible infinity
family, Haar measure and element of `schwartzA`, the output is `absThetaInt < ⊤`.
See `src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/WeilThetaConvergence.lean:18–21`. [Lean]

| Polarity | Clause |
|---|---|
| Input | Theta degree, Witt rank guard, specified Schwartz inputs |
| Output | Finiteness of the absolute integral for every Haar measure |

**Lemma 19.3 (reduction to a Siegel set).** `weilThetaConvergence_of_siegelSet` derives
`WeilThetaConvergence` from the Siegel-set statement `SiegelSetUnitary`.

*Proof.* The proof obtains a Witt frame with $r\le\operatorname{wittIdx}(V)$ and transfers the
guard to $r$. It bounds the quotient integral by an integral on a Siegel set, then bounds that by
a torus integral with the modulus factor. The strict inequality makes the cited torus integral
finite. See
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilThetaConvergenceOfSiegelSet.lean:23–54`. $\square$ [Lean, read]

**Lemma 19.4 (producer and consumer on the main path).**

1. The archive proves `SiegelSetUnitary` as `siegelSetUnitary_of_core`, defined as
   `siegel_of_core siegelCore_holds`, and proves `WeilThetaConvergence` as
   `weilThetaConvergence_of_siegelSet siegelSetUnitary_of_core`.
2. The literature layer supplies this theorem as `weil_theta_convergence_of_literature O` and
   passes it, with the doubling input of Section 19.4 and the convergent Siegel–Weil formula, to
   `rallis_of_dm`.
3. Inside `rallis_of_dm` the hypothesis is read twice: in the convergent Siegel–Weil evaluation of
   the theta kernel and in the $L^2$ and moderate-growth bounds for the kernel.

*Proof.* (1) is `src/Development/AutomorphicArithmetic/ThetaCorrespondence/WeilRepresentation/WeilTheta.lean:7–10`.
(2) is `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:483–486`.
(3) is `src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/RallisDM.lean:52`
and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/RallisDM.lean:63`. $\square$ [Lean, read]

**Comparison.** Gan–Qiu–Takeda Theorem 1.3 distinguishes “the second term range or the
convergent range” according to whether $m\le n+\epsilon_0+r$. In the unitary
case $\epsilon_0=0$ the strict branch of the Lean guard selects the convergent
side of this boundary. [GanQiuTakeda2014]

**Remark (status).** The producer of the Siegel-set input is now located. Its proof is not read:
the missing terms are `siegel_of_core`
(`src/Development/WeilBound/ThetaLifts/Reductions/SiegelOfCore.lean:232`) and `siegelCore_holds`
(`src/Development/WeilBound/CoreStatements/AbelianHeightsDuality/PublishedTheoremStatements/SiegelSetUnitaryHolds.lean:7–8`),
which forwards to `GlobalTheory.CompanionTheory.SiegelRed.siegelCore`. The reduction-theory
content behind them is [Open].

## 19.4 Global doubling

**Motivation.** Unfolding identifies an Eisenstein period with a doubling zeta integral
in a right half-plane. The flat section family allows the integrals to be studied as functions
of the parameter. The domain of the unfolding identity and the pole bound for the Eisenstein
family answer different questions.

**Example.** At rank $2$, the right half-plane is $\Re s>1$. A section based at
$s_1=3/2$ passes the numerical guard, while sections based at $s_1=1$ or $s_1=1/2$
fall outside it. With $b=4$ the separate pole bound applies at $(4-2)/2=1$,
exactly on the boundary of the unfolding region. With $b=2$ the pole clause's
guard $2<b$ fails. These are checks of the numerical premises for otherwise eligible data.
[Expository]

**Definition 19.2 (two doubling interfaces).** Both `GlobalTheory.Published.DoublingMethod`
and `ResidueKilled.DM` take a positive-rank Hermitian space $V$ over the archive datum $D$,
majorant and Iwasawa data for the doubled group, a Hecke character $\mu$ with restriction
`ResEta D μ b`, and a section $\varphi$ in `degPS V a μ s₁`. For this input they give
three conjuncts.

1. The flat family has Eisenstein continuation and, at each $s_0$, satisfies `EisRegularAt`
   for some order $k$. This gives a holomorphic extension of the family multiplied
   by $(s-s_0)^k$, with joint continuity and a local uniform polynomial height bound.
2. In `DoublingMethod`, if $\operatorname{rank}(V)<b$, the Eisenstein family has a pole
   of order at most one at $(b-\operatorname{rank}(V))/2$. In `DM` this conjunct is `True`.
3. For each eligible infinity family, signature, Cartan frame, Haar measure and pair of
   cusp forms, the first component gives `BasicIdentity` at every
   $\Re s>\operatorname{rank}(V)/2$. The second gives meromorphic continuation of the
   zeta integral. The identity itself includes convergence on both sides and equality.

See `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/EisRegularAtOfEisPoleLE.lean:17–28`
and `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/EisRegularAtOfEisPoleLE.lean:36–46`,
and `src/Development/WeilBound/RepresentationTheoryGL/EisensteinResidues/AnisotropicGlobalForms/DmOfHyp.lean:13–22`.
The literature bundles carry `DoublingMethodLocalZetaIntegrals`, an abbreviation for `DM`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:6`).
[Lean, read]

**Lemma (the archive's base-point identity).** `GlobalTheory.Eis.basicIdentity_of_mem`
explicitly includes `hP : Published.DoublingMethod`, positive rank, the majorant and Iwasawa
hypotheses, the Hecke and `ResEta` conditions, and section membership at $s_1$. It further
requires $\operatorname{rank}(V)/2<\Re s_1$, an eligible infinity family and signature,
a cusp Cartan frame, a measure with a Haar instance, and membership of both forms in
`Cusp.A0 θ V A`. Its conclusion is `BasicIdentity V μ m φ f₁ f₂`.
See `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/EisRegularAtOfEisPoleLE.lean:159–167`.
[Lean, read]

**Proof and DM version.** The same conclusion follows from `hDM : ResidueKilled.DM` with all
the other premises above. Here is the deduction alongside the operations in the archive proof
at line 167.

| Operation | Archive proof | Deduction with `DM` |
|---|---|---|
| Instantiate at the section | Apply `hP D V h0 a ha hI μ b hμ hb s₁ φ hφ` | Apply `hDM` to the same arguments |
| Take conjunct 3 | Project `.2.2` and supply `θ hθ hV A hA m hm f₁ h₁ f₂ h₂` | Take the same projection and give the same cusp-form data |
| Evaluate the identity | Apply `.1` at `s₁` with the strict inequality `hs` | Do the same, obtaining the identity for `flat V a φ s₁ s₁` |
| Return to the original section | Rewrite with `flatH_self` | Use the same rewrite to replace the flat section at its base point by `φ` |

The archive's proof reads conjunct 3. The right column is the textbook deduction obtained
by reading the matching conjunct of `DM`. The flat section abbreviations and the rewrite
are in `src/Development/AbelianVarietyTheory/Definitions/Foundations/T2SpaceAdeleRing.lean:25–42`,
`src/Development/AbelianVarietyTheory/Definitions/Foundations/T2SpaceAdeleRing.lean:161–165`
and `src/Development/AbelianVarietyTheory/Definitions/Foundations/T2SpaceAdeleRing.lean:306–310`.
[Expository]

**Lemma 19.5 (main-path doubling input).**

1. `dm_of_two` proves `DM` from `CuspRapidDecay`, `SiegelEisensteinContinuation` and `True`.
2. The literature layer defines `doubling_method O` as `dm_of_two` applied to its proofs of the
   first two inputs and `trivial`, and assigns it to the `dbl` and `doublingMethod` fields of the
   bundles `published_results_analytic : GeometricGaloisRepCompatibility` (`:645–657`),
   `published_results_eigen : UnitaryGroupThirdPlaceHypotheses` (`:666–726`) and
   `published_results_first : ThetaLocalInputs` (`:727–780`).
3. The companion slot `siegelEisensteinSimplePole` of the bundle `UnitaryGroupThirdPlaceHypotheses`
   has type `UnusedSlot72`, which is `True`, and the literature layer fills it with `trivial`.
4. `rallis_of_dm` destructs `DM` as $\langle h_1,-,h_3\rangle$ and never reads the middle conjunct.
5. On the main path the `doublingMethod` field of `published_results_eigen` is read by
   `ontoX_and_lamLow_of_unitaryGroupHypotheses'` and by `open_orbit_of_unramified_exponents_alt`.

*Proof.* (1) In `src/Development/WeilBound/RepresentationTheoryGL/EisensteinResidues/AnisotropicGlobalForms/DmOfHyp.lean:24–34`,
conjunct 1 is the value of `SiegelEisensteinContinuation` at the given data (`:26`). The continuation
statement is in
`src/Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂/SiegelEisensteinContinuationOfDoublingMethod.lean:14–19`.
The middle conjunct is `trivial` (`:27`). For conjunct 3, rapid decay of the two cusp forms comes from
`rapidDec_of_cuspForm` (`:28–29`), which uses smooth automorphy and cuspidality extracted from
`Cusp.A0` membership. See
`src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/UnifModGrowthOfIsUnifModerate.lean:99–112`
and `src/Development/AbelianVarietyTheory/Definitions/Foundations/MemL2OfBoundedContinuousInvariant.lean:306–319`.
The basic identity on $\Re s>\operatorname{rank}(V)/2$ comes from
`doubling_basicIdentity_unfolding` with the moderate-growth estimate
`siegelEisenstein_spherical_moderateGrowth_real_point` (`:30–32`). Zeta continuation comes from
`zetaContinues_of_eisRegularAt` (`:33–34`). The two unfolding inputs are assembled in
`src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DoublingBasicIdentityUnfoldingStatement.lean:15–16`
and `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelEisensteinSphericalModerateGrowthRealPointStatement.lean:17–18`.
The unfolding splits off the open orbit, makes the negligible orbits vanish by cuspidality,
and identifies the open-orbit integral with `zetaH`
(`src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DoublingBasicIdentityUnfolding.lean:38–155`).
The moderate-growth proof applies local regularity to the spherical section at the real point
(`src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelEisensteinSphericalModerateGrowthRealPoint.lean:22–30`).
The zeta continuation integrates the locally regularized family against the two rapidly decreasing
forms, using a common integrable majorant, then divides by the regularizing power and checks
agreement on the original half-plane
(`src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelEisensteinContinuationAndPoles.lean:24–96`).
[Lean, read]
(2) is `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:371–372`,
with the assignments at `:654`, `:678` and `:740`.
(3) is `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:74`,
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`
and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:505–506`, with the assignment at `:718`.
(4) is `src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/RallisDM.lean:40–41`.
(5) `every_character_of_theta_integrals_local_matching` passes its bundle `P` to
`nonempty_hyps_definite_side_of_closed_bound`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69–74`).
That proof calls the two readers at `:51` and `:58`, the second through the wrapper
`open0_of_unitary_group_hypotheses`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OpenOrbitOfUnramifiedExponents.lean:75–76`).
They hand `P.doublingMethod` on to
`lamLow_of_hypotheses_alt_alt`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SurjectiveAndLowWeightOfUnramifiedExponents.lean:27–29`)
and to `main_theorem_published_inputs_third_alt_alt`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/OpenOrbitOfUnramifiedExponents.lean:50–53`). $\square$ [Lean, read]

**Comparison.** Gan–Qiu–Takeda Theorem 1.3 calls $Z^*$ “the normalized doubling zeta
integral.” The Lean basic identity concerns the period integral and `zetaH`, at
first in a right half-plane, while that theorem evaluates an $L$-factor times
$Z^*$ at the Rallis point. [GanQiuTakeda2014]

**Remark (the full construction).** `doublingMethod_of_three` takes proofs of
`CuspRapidDecay`, `SiegelEisensteinContinuation` and `SiegelEisensteinSimplePole` as direct
arguments. At fixed section data it pairs the continuation with the guarded pole bound and
passes the pair to `siegel_eisenstein_continuation_and_poles`, which forwards to
`doublingMethod_of_eisenstein`. The latter uses the same rapid decay, unfolding and zeta
continuation as `dm_of_two` and carries the supplied pole proof into the middle conjunct.
See `src/Development/AbelianVarietyTheory/PublishedTheorems/SiegelWeil₂/SiegelEisensteinSimplePoleOfDoublingMethod.lean:14–19`,
`src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DoublingMethodOfEisensteinFacts.lean:8–11`,
`src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelEisensteinContinuationAndPolesStatement.lean:16–17`
and `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelEisensteinContinuationAndPoles.lean:98–110`.
[Lean, read]

**Remark (the dependency closure).** We checked the declarations exported from
`riemannHypothesis` by following references in declaration types, proof and definition
bodies, and inductive declarations in DeDeo's verified main-theorem export. This closes
the question of whether the exported RH proof consumes the full named interface.
[DeDeo, V8](../sources/SOURCES.md#v8) [Checked]

| Reachability from `riemannHypothesis` | Archive declarations |
|---|---|
| Absent from the closure and from the five-root export | `GlobalTheory.Published.DoublingMethod`, `GlobalTheory.Published.SiegelEisensteinSimplePole`, `basicIdentity_of_mem`, `doublingMethod_of_three`, `siegel_eisenstein_continuation_and_poles`, `doublingMethod_of_eisenstein`, `siegelEisensteinContinuation_of_doublingMethod`, and the full-interface Rallis bridge `UpperTheory.Lit.rallisInnerProductConvergent` |
| Reachable from the RH root | `ResidueKilled.DM`, `dm_of_two`, `doubling_method`, `SiegelEisensteinContinuation`, `rallis_of_dm`, and both bundle readers in Lemma 19.5(5) |

This is a result about named declarations in the exported proof. Other pole-order reasoning
can occur in the closure, which contains `EisRegularAt.of_poleLE`. The literature wrapper
for `SiegelEisensteinContinuation` supplies `PositivityTheory.RgEis.Sp.Hd.siegelEisensteinContinuation`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:369–370`).
The upstream proof of that input and the eventual extraction of data by the two bundle readers
remain [Open].

**Remark (normalization).** The step from the archive's `zetaH` to the normalized
$Z^*$ of Gan–Qiu–Takeda (arXiv:1207.4709v3, Theorems 1.2(ii) and 1.3, §11.6)
is [Open]. The comparison requires matching the Satake, spectral parameter and Haar
measure conventions, including the local factor $d_v$ referred to in Lapid–Rallis,
p. 334, Remark 3. See Section 19.5. [GanQiuTakeda2014] [LapidRallis2005]

## 19.5 Unramified split doubling

**Motivation.** At a split unramified place the doubling integral contributes
two standard factors and an inverse normalization factor.

**Example.** Let $n=1$, $q=4$, $s=1/2$, and take trivial Satake parameter.
The prescribed product is $(1-4^{-1})^{-2}(1-4^{-2})=5/3$. In rank one with the
trivial character, the two valuation tails sum to $1+2\sum_{j\ge1}4^{-j}=5/3$.
In general $(1+X)/(1-X)=(1-X)^{-2}(1-X^2)$ with $X=q^{-(s+1/2)}$.
Rescaling Haar measure by two doubles the integral wherever it converges.
Thus the Haar normalization is essential. [Expository]

**Definition.** `UnramifiedDoublingGL` takes a characteristic-zero nonarchimedean
local field, Haar measure with volume one for the maximal compact, a representation
with Satake parameter $\alpha$, and a zonal coefficient. It asserts one real threshold
for each such input and integrability at every complex $s$ to its right. The integral
equals $L(\alpha,s+1/2)L(\alpha^{-1},s+1/2)$ times
$\prod_{i=1}^n(1-q^{-(2s+i)})$.
See `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean:304–324`. [Lean]

| Polarity | Clause |
|---|---|
| Input | Normalized Haar measure and Satake and zonal conditions |
| Output | Existential threshold followed by universal complex parameter |
| Output | Integrability and the unramified product identity |

**Lemma (proof of the local identity).** The proof obtains a uniformizer, substitutes a spherical
function with equal double-coset sums and uses the generating-series radius to
choose the threshold. It returns to the zonal coefficient by swapping the coset sums,
then applies the coset integral theorem with volume one. The consumer `hasSum`
takes integrability and bi-invariance from the formula and evaluates it on the
antitone Cartan representatives.
See `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsCommensuratedKO.lean:125–161`
and `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean:326–343`. [Lean, read]

**Lemma 19.6 (main-path producer and readers).** The literature layer supplies the closed theorem
`GlobalTheory.UnramDoublingProof.unramifiedDoublingGL` as `unramified_doubling_gl_of_literature O`
and assigns it to the fields `GeometricGaloisRepCompatibility.udbl`, `unramifiedDoublingGL` and
`unramifiedDoublingGL` of the three bundles of Lemma 19.5(2). The two readers of Lemma 19.5(5) pass `P.unramifiedDoublingGL` on
together with `P.doublingMethod`.

*Proof.* See `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:529–530`,
the assignments at `:655`, `:679` and `:741`, and the reader lines cited in Lemma 19.5(5). $\square$ [Lean, read]

**Comparison.** Gan–Qiu–Takeda call $L(s,\pi)$ “the standard L-function of $\pi$” in
Theorem 1.3. For unramified data they state that the local zeta integral equals
$L(s+1/2,\pi_v\times\chi_{V,v})/d_v(s,\chi_V)$, where $d_v$ is “the product of a number of
explicit Hecke L-factors (see [LR, P. 334, Remark 3])” (§11.6, p. 54). The Lean right-hand side
has this shape: $\prod_{i=1}^n(1-q^{-(2s+i)})$ is the reciprocal of a product of local zeta
factors, and $L(\alpha,s+1/2)L(\alpha^{-1},s+1/2)$ is the form a standard factor takes at a split
place. [GanQiuTakeda2014] [Expository]

**Remark (status).** The term-by-term check needs the explicit $d_v$ of Lapid–Rallis
[LapidRallis2005, Remark 3, p. 334], which Gan–Qiu–Takeda cite without restating. We could not
consult that page through an open source, so the split-place comparison remains [Open]. What the
two readers of Lemma 19.5(5) do with the identity is also [Open].

## 19.6 Convergent Rallis inner product

**Motivation.** The formula translates a pairing of lifts into a special value
of a doubling integral.

**Example.** The archive's rank pair $(5,9)$ with target signature $(8,1)$ has
Witt index at most $1$, so $5+1<9\le10$. At rank pair $(5,6)$ with Witt index
$1$, the strict convergence test fails even though $5<6\le10$.
See `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/LowerLiftsZeroOfWittIdxEqZero.lean:89–95`. [Lean, read]

**Definition.** `RallisInnerProductConvergent` requires $a<b\le2a$ and
Witt index zero or $a+r_B<b$. It takes compatible ordinary and doubled Weil data,
majorant, covolume and Cartan data, cusp forms and lower-lift vanishing, and a
$K$-finite doubled vector made from the two theta inputs. For each pair it asserts
convergence, square-integrability and `ZetaValueAt` with value the Petersson
pairing divided by the target quotient volume.
See `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/LowerLiftsZeroOfWittIdxEqZero.lean:22–32`
and `src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/LowerLiftsZeroOfWittIdxEqZero.lean:41–59`. [Lean]

| Polarity | Clause |
|---|---|
| Input | Convergent range, compatible Schwartz data and lower-lift vanishing |
| Output | Convergence and square-integrability of both lifts |
| Output | Volume-normalized pairing as the doubling zeta value |

**Lemma 19.7 (`rallis_of_dm`).** `DM`, `SiegelWeilUnitaryConvergent` and `WeilThetaConvergence`
imply `RallisInnerProductConvergent`.

*Proof.* `rallis_of_dm` obtains the value of the doubled Eisenstein section and
passes it to the holomorphic zeta-value argument. Seesaw Fubini proves the two
integrability assertions and rewrites the paired lift integral. The kernel product
identity cancels the determinant character with its inverse, and quotient averaging
gives the volume factor. The proof introduces the lower-lift premise as `_hLow`
and closes this convergent deduction without using it. By Lemma 19.5(4) it also leaves the
middle conjunct of `DM` unread.
See `src/Development/AutomorphicArithmetic/ThetaCorrespondence/FockModels/RallisDM.lean:24–110`. $\square$ [Lean, read]

**Lemma 19.8 (where the formula goes).** The literature layer defines
`rallis_inner_product_convergent_of_literature O` as `rallis_of_dm` applied to the doubling,
Siegel–Weil and theta-convergence inputs above. It assigns the result to the field
`rallisInnerProductConvergent` of `published_results_first O : ThetaLocalInputs`, which is passed
as `F` to `every_character_of_theta_integrals_local_matching` and then to
`nonempty_hyps_definite_side_of_closed_bound`. That proof reads `F.siegelSetUnitary` and
`F.howeDualityReal` by name, and passes `F` whole to further lemmas. No line of the archive
projects the field `.rallisInnerProductConvergent`.

*Proof.* See `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:485–486`,
the assignment at `:739`, the call at `:811`, and
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:44–74`.
The field is declared at
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/BernsteinUnitaryProductIrreducible.lean:18`.
The absence of projections is a search over all lines of the pinned archive; the only dotted
occurrence is the theorem name
`UpperTheory.Lit.rallisInnerProductConvergent` of Section 19.4. $\square$ [Lean, read]

**Comparison.** Gan–Qiu–Takeda Theorem 1.3(i) uses the phrase “is cuspidal” for the first-occurrence
lift under lower-lift vanishing, and expresses the pairing via the
value of the product of a standard factor and normalized doubling integral. The
Lean interface specializes to the convergent side and states the zeta value before
this factorization. Theorem 1.2(ii) in the second term range compares Laurent
coefficients modulo the image of an Eisenstein residue. The rank $(5,6)$ example
exhibits the boundary that prevents simply extending the convergent proof across it.
[GanQiuTakeda2014]

**Remark (status).** Two items stay [Open]. First, a reader of the Rallis field: none was found by
name, and a positional destructuring of `F` further down cannot be excluded by a name search.
Second, the second-term identity. None of the literature inputs traced in this chapter states it,
so the comparison with Gan–Qiu–Takeda Theorem 1.2(ii) has no Lean counterpart to check here.

## 19.7 Status of the open items

| Section | Earlier [Open] item | Status now |
|---|---|---|
| 19.1 | Proof of `ShinGaloisRep` and a direct `Row0b` consumer | Closed by Lemmas 19.1–19.2: no proof, no consumer. The normalization against `wdOf` stays [Open], off the main path |
| 19.2 | Proof of `ChenevierHarris` and its use by `Row0b` | Closed by Lemmas 19.1–19.2 |
| 19.3 | Source proof of the Siegel-set input | Producer located (Lemma 19.4); `siegel_of_core` and `siegelCore_holds` unread |
| 19.4 | Does the RH proof consume the full `DoublingMethod`? How does the normalization compare? | Closed for the named full interface and `SiegelEisensteinSimplePole`: both are absent from the `riemannHypothesis` closure. Upstream `SiegelEisensteinContinuation`, the use of `DM` beyond the two bundle readers, and the $Z^*$ normalization remain [Open] |
| 19.5 | Split-place comparison with the published normalization | [Open]: needs $d_v$ from [LapidRallis2005, p. 334] |
| 19.6 | Second-term identity | [Open]: not stated by the inputs traced here; reader of the Rallis field not found |

The two Galois dependency questions and the full doubling dependency question are closed. The pattern in
Sections 19.4 and 19.6 adds a case to the polarity table of Section 18.1.2: a literature slot
whose name evokes a full theorem can be filled by a weaker proposition (`DM`), by `True`
(`UnusedSlot72`), or by a proposition whose reader has not been found.
