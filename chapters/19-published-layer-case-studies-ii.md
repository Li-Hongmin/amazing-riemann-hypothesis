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

**Remark (status).** §§19.3.1–19.3.8 trace the Siegel-set producer through the
measure bound, rational cover, lattice majorant, arithmetic supply, Schwartz input,
adelic coordinates, weighted lattice count and CM-type place identification.

### 19.3.1 Siegel sets and the integrable majorant

**Motivation.** The absolute theta integral lives on the left quotient of the
adelic unitary group by its rational points. A Siegel set gives representatives
for that quotient and separates the directions that can go to infinity from
compact factors. Three estimates enter the argument: a cover bounds the
quotient integral by an integral on the group, a Haar bound reduces that
integral to the torus, and the torus density must absorb the growth of the
absolute theta sum. [Lean, read]

**Example (the smallest positive Witt rank).** Take $F=\mathbb Q$,
$E=\mathbb Q(i)$ and the hyperbolic Hermitian plane with Gram matrix
$J=\begin{pmatrix}0&1\\1&0\end{pmatrix}$. The two coordinate vectors form a
Witt frame, so the Hermitian dimension is $m=2$ and the Witt rank is $r=1$.
The torus element scales them by $u$ and $u^{-1}$ at infinity and is the
identity at finite places. For any positive cutoff $c$, the cone is
$[c,\infty)$, the modulus is $u^2$, and the cone density is $u^{-3}du$.
Thus the constant majorant has integral $1/(2c^2)$. With growth $u^\beta$
the integral is $c^{\beta-2}/(2-\beta)$ for $\beta<2$. At $\beta=2$
its integral up to $R$ is $\log(R/c)$, which tends to infinity.
This endpoint is the model majorant for theta degree $1$ in this dimension.
For a convergent theta-degree example keep $r=1$ and take a hyperbolic plane plus an anisotropic line, so $m=3$. At degree $n=1$ the majorant $u^2$ against $u^{-5}du$ has integral $1/(2c^2)$. [Expository]

**Definition.** Fix number fields $F\subset E$ with the archive's CM
extension hypothesis `IsCMExt F E σ` and conjugation $\sigma$.
Let $J$ be an $m$-by-$m$ nondegenerate $\sigma$-Hermitian matrix and put
$G=U(J)(\mathbb A_F)$ and $\Gamma=U(J)(F)$, embedded diagonally.
These are `GAd σ J` and `ratPts σ J`. A Witt frame consists of
$m$-by-$r$ matrices $X,Y$ with $X^\dagger JX=Y^\dagger JY=0$, $X^\dagger JY=I_r$ and
anisotropic common orthogonal complement. The dagger denotes conjugate
transpose. The subgroup $P$ preserves the flag of columns of $X$, acting
on them by an upper triangular matrix. Write $P^1$ for the part whose
diagonal entries each have adelic absolute value $1$.

The continuous torus homomorphism $a(s)$, for $s\in\mathbb R^r$, has
archimedean eigenvalues $e^{s_i}$ on $X_i$ and $e^{-s_i}$ on $Y_i$, fixes
the common complement, and has trivial finite component. For $u_i=e^{s_i}$
write $a(\log u)$ for the same element. Use zero-based indices. The cutoff
$c>0$ imposes $u_i>0$, $u_i\ge c u_{i+1}$ for $0\le i<r-1$, and
$u_{r-1}\ge c$ if $r>0$. Call this set $D_c$ and write $L_c=\log D_c$.
Then $S=\Omega a(L_c)K$. Here $K$ is a compact subgroup and $\Omega$
a compact subset of $P^1$. If $r=0$, the torus and cone each have one point.

Let $b=[F:\mathbb Q]$. The archive uses
$\rho_2(m,s)=\sum_{i=0}^{r-1}(m-2i-1)s_i$ and
$\rho(s)=2b\rho_2(m,s)$. Its modulus is
$\delta(u)=\prod_i u_i^{2b(m-2i-1)}$. The sign convention is that
right translation by $a(s)$ pushes left Haar measure on $P$ to
$e^{\rho(s)}$ times itself. The logarithmic density is
$e^{-\rho(s)}ds$, and its expression in positive coordinates is
$\delta(u)^{-1}\prod_i(du_i/u_i)$. The ambient Haar measure is arbitrary.
The auxiliary measure on $K$ has mass one. [Lean]

Definitions and normalization are in
`src/Development/AbelianVarietyTheory/Definitions/Foundations/OfInfProjInfMulOfFinProjFin.lean:40,349`,
`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsSmoothModerateOfIsAutFunSm.lean:21–53,91–109`,
`src/Development/WeilBound/ThetaLifts/FrameEstimates/SquareIntegrableWeilRange.lean:52`,
and `src/Development/WeilBound/ThetaLifts/Reductions/SiegelPar.lean:75–79`.

**Lemma (Siegel-set control).** In the setting just defined, assume
$G=PK$, $K$ is compact and in `GoodPosition`, $\Omega\subset P^1$ is
compact, and $c>0$. Good position here means each element of $P\cap K$
is a product of a frame-diagonal Levi element in $K$ and a unipotent element
in $K$ whose flag action has diagonal $1$ and whose displacement on the
orthogonal complement of $X$ takes values in the span of $X$.
Then $S$ is closed. For every Haar measure $\mu$ on $G$, it has finite
$\mu$-measure and there is a finite $C_\mu\ge0$ such that for every
$f:G\to[0,\infty]$ and measurable $H:\mathbb R^r\to[0,\infty]$ with
$f(p a(\log u)k)\le H(u)$ for all $p\in\Omega$, $u\in D_c$ and
$k\in K$, one has
$\int_S f\,d\mu\le C_\mu\int_{D_c}H(u)\delta(u)^{-1}\prod_i(du_i/u_i)$.
Use the nonnegative lower integral, defined via measurable simple
minorants. The production statement allows arbitrary $f$. [Lean, read]

**Proof.**

1. **Coordinates and closedness.** The parabolic is closed. The
   continuous additive map $\tau:P\to\mathbb R^r$ extracted from the
   diagonal absolute values satisfies $\tau(a(s))=s$,
   $\tau(P^1)=\{0\}$ and $p a(-\tau(p))\in P^1$.
   The last property also refines $G=PK$ to a decomposition with a
   $P^1$ factor and an unrestricted positive torus factor. Exponentiation
   identifies $L_c$ with $D_c$. In logarithmic coordinates the remaining
   cutoff inequalities are closed, and uniqueness of the torus element
   gives the set equality $S=\Omega a(L_c)K$. The continuous left
   inverse $\tau$ makes the section a closed embedding into $P$.
   Its closed cone image is also closed in $G$. Multiplication on
   either side by the respective compact set preserves closedness.
   See `src/Development/WeilBound/ThetaLifts/Reductions/SiegelOfCore.lean:18–76`
   and `src/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean:130–133`.

2. **Haar measure in logarithmic coordinates.** For any compact
   $B\subset\ker\tau$ and left Haar measure $\nu$ on $P$, put
   $T=B a(\mathbb R^r)$. This is closed by the preceding argument.
   Restrict $\nu$ to $T$, weight it by $e^{\rho(\tau(p))}$ and push it
   forward by $\tau$. The resulting measure on $\mathbb R^r$ is
   translation invariant. Indeed $T$ is stable under right translation
   by $a(s)$, $\tau(p a(s))=\tau(p)+s$, and the weight at $p a(s)$ is
   $e^{\rho(s)}$ times the weight at $p$. In the integral of a
   translated test function this factor cancels the factor in the
   pushforward of $\nu$. The weighted measure is finite on compacts:
   the preimage in $T$ of a compact $Q$ is $B a(Q)$, compact, with
   bounded weight there. Uniqueness of translation-invariant locally
   finite measure gives a finite nonnegative multiple of Lebesgue
   measure, allowing the zero measure. Testing against a measurable
   function times $e^{-\rho}$ removes the weight. Thus
   $\int_T h(\tau(p))\,d\nu(p)=C_B\int h(s)e^{-\rho(s)}ds$.
   See `src/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean:135–206`.

3. **Compact fibers and domination.** Set $M=P\cap K$.
   The image $\tau(M)$ is a bounded additive subgroup. For $m_0\in M$,
   $\tau(m_0^j)=j\tau(m_0)$, forcing $\tau(m_0)=0$. Good position and
   compactness give commutation of $M$ with the torus.
   Apply step 2 with $B=\Omega M$. The Haar product theorem for
   $G=PK$ writes the integral of each nonnegative measurable test
   function as a finite constant times the iterated integral over
   $P$ and $K$, using left Haar on $P$ and probability Haar on $K$.
   Use this identity on each simple minorant of $\mathbf1_S f$.
   If $pk=q a(s)k'$ is in $S$ with $p\in P$, $q\in\Omega$, $s\in L_c$
   and $k,k'\in K$, then $(q a(s))^{-1}p=k'k^{-1}\in M$. Consequently
   $p\in\Omega M a(\mathbb R^r)$ and $\tau(p)=s$.
   The minorant at $pk$ is therefore bounded by
   $\mathbf1_T(p)(\mathbf1_{L_c}(H\circ\exp))(\tau(p))$. Outside $S$
   it is zero. Integrate this bound over $K$, whose mass is one,
   then apply step 2 and take the supremum over simple minorants.
   See `src/Development/WeilBound/ThetaLifts/Reductions/SiegelHaar.lean:216–304` and the Haar product input [Lean] in `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarProductClosedCompactHolds.lean:239–266`.

4. **Jacobian and finite volume.** The derivative of coordinatewise
   exponentiation is diagonal with determinant $\prod_i e^{s_i}$.
   It is injective on $L_c$ with inverse coordinatewise logarithm.
   In the change-of-variables formula the determinant cancels the
   denominator $\prod_i u_i$, leaving the stated logarithmic density.
   For finite volume apply the bound with $f=H=1$. Backward induction
   from the last cutoff gives $u_i\ge c^{r-i}$. On the product of
   these half-lines the density is the product of
   $u_i^{-2b(m-2i-1)-1}$. A Witt frame gives $2r\le m$, so each
   exponent is strictly below $-1$. Product integrability and
   monotonicity give finiteness. In rank zero the product has mass one.
   See `src/Development/WeilBound/ThetaLifts/Reductions/SiegelOfCore.lean:78–230`.
   $\square$

**Remark (where the reduction data enter).** The lemma takes $PK$ and
good position as inputs. The theorem `siegel_of_core` takes the
proposition `SiegelCore` as an ordinary proof parameter. In addition
to the hypotheses in the lemma, this parameter gives $G=\Gamma S$,
compact containment of $a^{-1}pa$ on the cone, the height inequality
$\operatorname{ht}(g)\le C\operatorname{ht}(\gamma g)^A$
for $g\in S$, $\gamma\in\Gamma$, and rapid decay
$|\phi(g)|\operatorname{ht}(g)^N\le C_N$ on $S$ for smooth moderate
cuspidal $\phi$ and each $N$. The proof packages these inputs with the
refined Iwasawa decomposition, closedness and the measure lemma.

The actual `siegelCore_holds` forwards to `SiegelRed.siegelCore`.
That proof assembles the archimedean and finite compact subgroups
and their good-position data into one $K$, takes $\Omega,c$ and the
rational cover from `unitary_siegel_domain_exists`, and fills the
three remaining fields with `conj_compact`, `cusp_form_siegel_bound`
and `cusp_form_rapid_decay`. These assembly steps are [Lean, read].
See `src/Development/WeilBound/ThetaLifts/Reductions/SiegelCore.lean:18–50`,
`src/Development/WeilBound/ThetaLifts/Reductions/SiegelOfCore.lean:232–236`,
`src/Development/WeilBound/CoreStatements/AbelianHeightsDuality/PublishedTheoremStatements/SiegelSetUnitaryHolds.lean:7–8`,
and `src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SiegelSetUnitary.lean:17–30`.

**Consumption by `WeilTheta`.** In the production consumer, let $n$
be the theta degree and $m$ the dimension of $V$. The integral is of
the descended sum of absolute values
$\sum_{\xi\in E^{m\times n}}|\Phi(g^{-1}\xi)|$
on the left quotient by $\Gamma$ with `autMeasure` induced from $\mu$.
After installing the adelic topology, the proof obtains a Witt frame,
bounds $r$ by the Witt index and derives $r=0$ or $n+r<m$.
The Schwartz hypotheses give continuity. Closedness and rational
coverage then bound the quotient integral by the group integral on
$S$. For the pointwise bound, write $p a k=a(a^{-1}p a k)$.
The parenthesized factor lies in the product of the supplied compact
conjugation set and $K$. The theta estimate on that compact product
supplies $H(u)=C_\Phi\prod_i u_i^{2bn}$. The consumer applies the
Haar inequality with this $H$, pulls $C_\Phi$ out of the integral,
and uses the weighted cone estimate below. The bare finite-volume
field, height bound and rapid-decay field are discarded in this
proof. [Lean, read]

See
`src/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/WeilSiegelFormulaUnitary.lean:24–31`,
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilThetaConvergenceOfSiegelSet.lean:23–54`,
and
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/WeilRepresentation/WeilTheta.lean:7–10`.

**Why the two comparison bounds apply.** The quotient measure is the
pushforward of group Haar restricted to the archive's standard measurable
fundamental domain. The absolute theta sum is rationally left invariant by
reindexing the rational matrices. Hence the quotient integral equals the
group integral over the standard domain. Intersect that domain with the
countably many translates of $S$. Their union covers the domain.
Subadditivity gives an upper bound by the sum of integrals over the pieces.
Translate the integrands back using rational invariance. The fundamental
domain formula identifies that sum with the integral on $S$.
See
`src/Development/AbelianVarietyTheory/Definitions/Foundations/AestronglyMeasurableQuotMeasureIffLift.lean:283,650`,
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsThetaIntLeSetLIntegralOfCover.lean:13–30`
and
`src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LintegralFundamentalDomainLeOfMeetsOrbits.lean:9–31`.
[Lean, read]

For the growth bound, the Schwartz hypothesis gives a finite-adelic
support and a family of archimedean decay majorants indexed by an order
$N$. The compact-factor estimate enlarges the support and bounds the
majorant after multiplication by $y^{-1}$ uniformly for $y$ in the
compact product. The rational-point sum estimate for the enlarged support
chooses $N$ and gives the power $\prod_i u_i^{2bn}$. With that $N$,
use $(ay)^{-1}\xi=y^{-1}(a^{-1}\xi)$ to compare each absolute theta
summand with the enlarged majorant evaluated at $a^{-1}\xi$.
The proof replaces the Schwartz constant by its maximum with zero,
multiplies by the nonnegative compact-factor constant, then sums using
monotonicity of the nonnegative series. The resulting constant is the
product of these two constants and the rational-point sum constant.
See
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsThetaSumSiegelSetLeTorusPower.lean:17–64`.
[Lean, read]

**Weighted cone estimate.** Put $A_i=2bn-2b(m-2i-1)$, so the
weighted density has powers $u_i^{A_i-1}$. For $1\le j\le r$,
$\sum_{i<j} A_i=2bj(n-m+j)$, which is negative under $n+r<m$.
Individual powers need not be integrable on independent half-lines.
The proof uses the cutoff coupling. For one variable, the integral
with exponent $A_0-1$ from $c$ is $c^{A_0}/(-A_0)$.
For two or more variables split off $u_0$. For each tail in the
smaller cone the inner integral starts at $c u_1$ and gives
$c^{A_0}u_1^{A_0}/(-A_0)$. For tails outside the smaller cone,
the indicator vanishes. The production proof uses the product
lower-integral bound and absorbs $u_1^{A_0}$ into the next power.
The new list is $(A_0+A_1,A_2,\ldots)$, with its prefix sums inherited
from the original list, so induction proves finiteness. The
general modulus lemma does this for growth exponent $bd$ and guard
$d<2(m-r)$; its consumer takes $d=2n$. The Witt wrapper treats
$r=0$ separately as the empty product with singleton measure.
This proves finiteness of the majorant consumed above. [Lean, read]

See
`src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LintegralSiegelConeInvModulusLtTopWeil.lean:8–154,160–207`,
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralSiegelTorusConeModulusLtTop.lean:13–23`,
and
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralSiegelTorusConeModulusLtTopStatement.lean:12–13`.

**Reading boundary.** The proof bodies cited for the assembly,
measure estimate, weighted cone calculation and consumer are read
against the joined Alpöge–Claude archive, SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
The primitives used for the parabolic and torus section, commutation
and modulus computation are inputs here [Lean]. See
`src/Development/WeilBound/ThetaLifts/Reductions/SiegelPar.lean:35–85`
and `src/Development/WeilBound/ThetaLifts/Reductions/SiegelParMod.lean:437`.
The rational cover `RedCov.cov_main` is read in §19.3.2. Deeper compact-factor construction,
conjugation, height and rapid-decay proofs are [Open] at this read level.
The quotient estimate and theta growth bound are forwarded through
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsThetaIntLeSetLIntegralOfCoverStatement.lean:12–13`
and
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsThetaSumSiegelSetLeTorusPowerStatement.lean:12–13`
[Lean]. The underlying measurable-domain construction and the decay and
lattice-summation estimates remain [Open] at this read level, in
particular `adelicMatrixSchwartzMajorant_inv_mul_le` and
`siegelTorus_tsum_majorant_translatedRationalPoints_le`, supplied in
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicMatrixSchwartzMajorantInvMulLeStatement.lean:12`
and
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelTorusTsumMajorantTranslatedRationalPointsLStatement.lean:12`.
The full theta convergence dependency cone remains [Open] at this read level.

**Literature note.** Gan, Qiu and Takeda state Weil's convergent range in
§3.1 of their author preprint. For unitary pairs their parameter
$\epsilon_0$ is zero, giving the rank and degree condition used above.
The cone calculation here follows the archive's coordinates and measure.
[Paper] [GanQiuTakeda2014]

### 19.3.2 Rational reduction and the covering of the adelic quotient

**Motivation.** The quotient estimate in §19.3.1 requires every rational
orbit to meet a single Siegel set. To find a meeting point, first move a
short isotropic vector to a fixed rational line and reduce on the complement
of its hyperbolic plane. This produces a compact tail. Absorbing the tail
into the specified Iwasawa group costs a uniform change of cone cutoff.

**Example (rank one).** Over $\mathbb Q(i)/\mathbb Q$ take a hyperbolic
basis $(x,y)$ with Gram matrix $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$.
Let $a[t]$ have matrix $\operatorname{diag}(t,t^{-1})$ at infinity and
identity finite components. The rational isometry $w$ swaps $x$ and $y$.
For $g=a[1/3]$, the inverse action at infinity gives lengths $3$ and
$1/3$ on the two vectors. Since $wa[t]w^{-1}=a[t^{-1}]$,
$w^{-1}g=a[3]w$. The parameter $3$ satisfies the rank-one cutoff $1$,
and the right factor belongs to the compact group $\{1,w\}$. Here
the rational swap has its diagonal adelic image at every place.
[Expository]

**Example (rank two).** Over the same field take two hyperbolic planes
in the order $(x_0,x_1,y_0,y_1)$, with off-diagonal identity blocks in
the Gram matrix. Let $B=\left(\begin{smallmatrix}1&2\\0&1\end{smallmatrix}\right)$.
Block multiplication shows that
$\delta=\operatorname{diag}(B,(B^{\ast})^{-1})$ preserves the form, where
$B^{\ast}$ is the conjugate transpose. The diagonal flag coefficients
are both $1$. Use $a(s)=a[\exp(s)]$ with two coordinates. For
$s=(\log4,\log2)$ and $v=(-\log2,\log2)$ one has
$g=\delta a(s)a(v)=\delta a(s+v)$. The initial $(4,2)$ satisfies both
cone inequalities with cutoff $2$ at equality. The final $(2,4)$ has
ratio $1/2$ and terminal coordinate $4$. For a tail $a(v)$ whose
parabolic part is itself, the norm-one part is $1$, and the rational
parabolic reduction can take $\delta$ out of the left factor. The
cutoff loss from the shift is $2\exp(-2\log2)=1/2$, with equality
in the first inequality. These two examples calculate individual
factorizations. [Expository]

**Definitions.** Let $E/F$ be a CM extension of number fields with
conjugation $\sigma$ and a nondegenerate Hermitian form $J$ on $E^m$.
Let $G=U(J)(\mathbb A_F)$ and $\Gamma=U(J)(F)$ embedded diagonally.
A Witt frame $(X,Y)$ has $r$ paired columns $(x_i,y_i)$, indexed from
zero. The two spans are totally isotropic, their pairing is the
identity, and their joint orthogonal complement is anisotropic.
The flag of successive initial columns of $X$ has stabilizer $P$.
Write $P^1$ for the subgroup where each diagonal flag coefficient has
adelic absolute value $1$. This is a product over places. The product
formula gives $\Gamma\cap P\subseteq P^1$.

The logarithmic torus $a:\mathbb R^r\to P$ has identity finite components.
At infinity it scales $x_i$ by $\exp(s_i)$ and $y_i$ by $\exp(-s_i)$
and fixes the orthogonal complement. Let $L_c$ consist of $s$ with
$t_i=\exp(s_i)$ satisfying $t_i\ge c t_{i+1}$ for every $0\le i\lt r-1$
and $t_{r-1}\ge c$ when $r>0$. For $r=0$ put $L_c=\mathbb R^0$.
Write $S(\Omega,c,K)=\Omega a(L_c)K$. [Lean, read]
(`src/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsSmoothModerateOfIsAutFunSm.lean:21–49`;
`src/Development/WeilBound/ThetaLifts/Reductions/SiegelOfCore.lean:43–61`)

**Theorem (conditional rational covering).** For every datum above
and every compact subgroup $K\le G$ with $G=PK$, there exist a compact
$\Omega\subseteq P^1$ and a real $c>0$ such that for every $g\in G$ there
are $\gamma\in\Gamma$, $\omega\in\Omega$, $s\in L_c$ and $k\in K$
with $g=\gamma\omega a(s)k$. Thus
$G=\bigcup_{\gamma\in\Gamma}\gamma S(\Omega,c,K)$.
The archive interface also takes `GoodPosition`, which factors every
element of $P\cap K$ into its specified Levi and unipotent pieces
inside $K$. The body of `cov_main` discards that argument. §19.3.1
uses it for the measure inequality. The following proof is conditional
on the arithmetic suppliers identified below. [Lean, read]
(`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitarySiegelDomainExists.lean:202–265`)

**Lemma (parabolic compact slice).** There is a compact $\Omega\subseteq P^1$
with $P^1=(\Gamma\cap P)\Omega$.

*Proof.* Write $q\in P^1$ as $um$ by the Levi decomposition. The norm-one
Levi slice gives $m=\delta_M c_M$. The rational Levi element $\delta_M$
normalizes the unipotent subgroup, so apply the unipotent slice to
$\delta_M^{-1}u\delta_M=\delta_U c_U$. Then
$q=(\delta_M\delta_U)c_Uc_M$. The production slice is
$(C_U\cap P^1)C_M$, where $C_U$ and $C_M$ are the compact unipotent and
norm-one Levi slices. Closedness of $P^1$ and continuity of multiplication
give compactness. The reverse containment uses the product formula.
The Levi producer obtains $C_M$ from the compact quotient of the closed
Levi in the projection commutant, with a uniform lower bound from a
jointly anisotropic Hermitian family. $\square$ [Lean, read]
(`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MinimalParabolicRationalCompact.lean:22–54`)

**Lemma (reduction with a compact tail).** For each datum and each
torus as above there are compact $C\subseteq G$ and $c_0>0$, independent
of $g$, such that every $g$ is $\gamma q a(s)\kappa$, with
$\gamma\in\Gamma$, $q\in P^1$, $s\in L_{c_0}$ and $\kappa\in C$.
This is `HasRed`. [Lean, read]
(`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RatVInjective.lean:36–39`)

*Proof.* Induct on $r$, allowing the dimension and Hermitian form to vary.
In rank zero the flag is empty, so $P^1=G$. Take $C=\{1\}$, $c_0=1$,
$\gamma=1$ and $q=g$.

For $r>0$ remove the plane spanned by $x_0,y_0$. Its orthogonal complement
has the remaining frame and group $G'$. The rank-reduction supplier
embeds $G'$ continuously by $\iota:G'\to G$ acting trivially on the
removed plane. It preserves rationality and sends $(P')^1$ into $P^1$.
The embedded torus satisfies $\iota(a'(s'))=a(0,s')$ and
$a(s_0,0)$ commutes with all of $\iota(G')$. For $p\in P$ the supplier
gives $p=q_0a(s_0,0)\iota(g')$, where
$\iota(h')^{-1}q_0\iota(h')\in P^1$ for every $h'\in G'$.
Indeed $g'$ is the induced isometry on $x_0^\perp/Ex_0$. The
normalization removes that isometry and the norm of the first flag
coefficient. The remainder acts on $x_0$ by a norm-one coefficient
and on the complement by the identity modulo the first line. These
two properties survive conjugation by the embedded group.

Choose an auxiliary compact Iwasawa subgroup $K_0$ from the supplier.
The induction hypothesis gives $C',c'$ in $G'$. Fix the compact
parabolic slice $\Omega$, and put $C=\iota(C')K_0$. This set is compact
and is chosen before $g$.

For a rational vector $v$ put $H_g(v)=\operatorname{hv}(g^{-1}v)$,
using the diagonal embedding and the archive's adelic norm in
restriction-of-scalars coordinates. A nonzero rational isotropic
$v$ is near minimal if $H_g(v)\le2H_g(u)$ for every nonzero rational
isotropic $u$. For fixed $g$ the inverse operator bound and the
product formula give a positive lower bound on nonzero rational
vector heights. The isotropic height set contains the height of $x_0$.
Choose a vector with height below twice the positive infimum.
If $\eta\in\Gamma$ sends $u$ to $v$, the identity
$H_{\eta^{-1}g}(u)=H_g(v)$ transports near minimality because rational
isometries permute the nonzero rational isotropic vectors.

For the given $g$ choose a near-minimal $v$, then a rational isometry
$\gamma_1$ sending $x_0$ to $v$. The supplier completes $v$ to a
hyperbolic pair and uses transitivity on pairs. Write
$\gamma_1^{-1}g=pk_0$ and decompose $p$ as above.
Inductively write $g'=\gamma' q' a'(s')\kappa'$. By the conjugation
property and the embedding of $(P')^1$,
$Q=\iota(\gamma')^{-1}q_0\iota(\gamma')\iota(q')\in P^1$.
Use the compact slice to write $Q=\delta\omega$. Moving the first
torus factor past the embedded factors gives
$g=(\gamma_1\iota(\gamma')\delta)\omega a(s_0,s')\iota(\kappa')k_0$.
The left product is rational. If $\delta x_0=d_0x_0$, then
$e=d_0^{-1}\in E^\times$ and the left product sends $ex_0$ to $v$.
Consequently $ex_0$ is near minimal for the reduced element
$\omega a(s_0,s')\iota(\kappa')k_0$.

The two uniform height suppliers, applied to $\Omega$ and $C$, give
$M_1,M_2>0$ with $\exp(-s_0)\le M_1$ and, if $r\ge2$,
$\exp(s_1)\le M_2\exp(s_0)$ for this reduced element, where $s_1$
is the first coordinate of $s'$ when it exists. Take
$c_0=\min(c',M_1^{-1},M_2^{-1})$. In rank one the first bound
gives the terminal inequality. In higher rank the second bound gives
the first adjacent inequality and all other inequalities follow from
the smaller cone. $\square$ [Lean, read]
(`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitarySiegelDomainExists.lean:26–175`)

**Proof of the covering theorem.** Use the compact-tail lemma, then
factor $\kappa=pk$ using the specified $K$. Every allowed $p$ lies in
the fixed compact set $D=(CK)\cap P$, since $p=\kappa k^{-1}$ and $P$
is closed. The continuous additive coordinate map
$\tau:P\to\mathbb R^r$ has $\tau(a(s))=s$ and $\ker\tau=P^1$.
For $u=\tau(p)$ put $p_1=p a(u)^{-1}\in P^1$. Compactness gives
$B_0\ge0$ with $|\tau(p)_i|\le B_0$ uniformly on $D$ in every coordinate.
This works for any choices in the Iwasawa factorization.
Since $P^1$ is a kernel,
$q a(s)p_1a(s)^{-1}\in P^1$. Reduce it as $\delta\omega$ using the
compact slice. Reordering gives $g=(\gamma\delta)\omega a(s+u)k$.

The new adjacent ratios are
$\exp(s_i-s_{i+1})\exp(u_i-u_{i+1})\ge c_0\exp(-2B_0)$.
The new terminal coordinate is at least $c_0\exp(-B_0)$, hence at
least $c_0\exp(-2B_0)$. Thus the final cutoff is
$c=c_0\exp(-2B_0)>0$. Both requirements are vacuous for the empty frame.
The reverse inclusion of the covering equality follows because all
factors lie in $G$. $\square$ [Lean, read]
(`src/Development/WeilBound/ThetaLifts/Reductions/SiegelPar.lean:55–73`;
`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitarySiegelDomainExists.lean:181–265`)

**Representatives and cardinality.** On the left quotient the assertion
is that $\pi(S)$ is the entire left quotient, where $\pi$ is the orbit map.
Set-theoretic choice gives one point of $S$ per coset. A measurable
choice belongs to the separate quotient measure argument.
The rational translates in $G$ form a countably indexed union
because $E^{m^2}$ is countable. The cover allows overlaps.
A finite subdivision $\Omega=\bigcup_{j=1}^h\Omega_j$ gives a
finite union of pieces $\Omega_j a(L_c)K$ before lifting by
$\Gamma$. For example, if one fixes an open subgroup of the
finite adelic group, the finite projection of $\Omega$ meets finitely
many of its open cosets by compactness. This finiteness counts pieces
of the compact parameter, while the cover in the ambient group is
indexed by rational points. [Expository]

**Return to the theta integral.** `SiegelRed.siegelCore` assembles $K$
from archimedean and finite-place suppliers. Via
`GlobalTheory.T.unitary_siegel_domain_exists` it takes $\Omega,c$
and the covering field from `cov_main`. It fills compact conjugation,
height control and rapid decay with separate suppliers.
`siegelCore_holds` forwards the bundle. `siegel_of_core` preserves
the cover and adds closedness and Haar control as in §19.3.1.
`UpperTheory.Lit.siegelSetUnitary_of_core` passes that bundle to
`weilThetaConvergence_of_siegelSet`. The consumer uses the closed
covering set in the quotient integral inequality, then applies the
compact conjugation bound, a pointwise theta majorant and the weighted
cone estimate. [Lean, read]
(`src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SiegelSetUnitary.lean:17–30`;
`src/Development/WeilBound/CoreStatements/AbelianHeightsDuality/PublishedTheoremStatements/SiegelSetUnitaryHolds.lean:7–8`;
`src/Development/WeilBound/ThetaLifts/Reductions/SiegelOfCore.lean:232–236`;
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/WeilRepresentation/WeilTheta.lean:7–10`;
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilThetaConvergenceOfSiegelSet.lean:23–54`)

**Arithmetic suppliers.** The pin is the joined Alpöge–Claude archive,
SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
The two height estimates use different competitors.

- `RedCov.First.exp_neg_le` first finds a uniformly bounded isotropic
  competitor, either from a short vector or by moving $x_0$ back from
  a compact representative in the thick part. Near minimality supplies
  the upper bound and the first-line height estimate supplies the
  lower bound proportional to $\exp(-[F:\mathbb Q]s_0)$.
  The underlying supplies include `small_height_vector_isotropic`,
  `unitary_points_height_bound_finite` with `unitary_points_height_bound_compact`,
  and `torus_siegel_height_lower_bound`. [Lean, read]
  (`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ReductionTheoryHeightBound.lean:75–128`)
- `RedCov.Simple.simple_bound` compares with a vector $q x_1-bx_0$
  with $1\le q\le N$ and $b\in E$ supplied by
  `adelic_tensor_rational_approximation`. The approximation makes
  the first coefficient after $\omega^{-1}$ small, and bounds the
  integer multiplier in the second. With $A=\exp(-s_0)$,
  $D_1=\exp(-s_1)$ and $d=[F:\mathbb Q]$, the compact height and
  norm comparisons give $A^d\le L\max(\varepsilon A,ND_1)^d$ with
  $L\varepsilon^d\lt 1$. The maximum must be $ND_1$, giving the
  adjacent inequality. [Lean, read]
  (`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ReductionTheoryLowerBound.lean:199–346`)

The source map gives the read boundaries for local compact
construction, Witt extension, adelic approximation, height compactness
and the anisotropic commutant and unipotent compactness. These deeper
supplies are [Lean] with their independent readings [Open].
The modulus computation is a separate supply `PMod.map_mul_torus_of`
at `src/Development/WeilBound/ThetaLifts/Reductions/SiegelParMod.lean:437`.
The lattice majorant separately uses
`adelicMatrixSchwartzMajorant_inv_mul_le` and
`siegelTorus_tsum_majorant_translatedRationalPoints_le`, via
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicMatrixSchwartzMajorantInvMulLeStatement.lean:12`
and
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelTorusTsumMajorantTranslatedRationalPointsLStatement.lean:12`.
Section 19.3.3 reads their direct proofs. The deeper measurable-domain construction
remains [Open].

**Literature note.** Borel's *Some finiteness properties of adele groups
over number fields*, §4.1 and Theorem 4.5 (pp. 113–114), constructs a
fundamental set using a finite union for reductive groups over
$\mathbb Q$ in a matrix-group presentation. Rational translates then
cover the ambient group. His definition uses right translations and
also requires finiteness of the set of rational translations that
meet the original set. The comparison distinguishes the two index
sets and clarifies the extra assertion in *fundamental set*. The
conditional proof here follows the archive's rational height and
parabolic suppliers. [Borel1963]

### 19.3.3 The lattice majorant for the inverse torus

**Motivation.** A theta summand decays rapidly at infinity, but as a torus coordinate grows, more rational points enter the region where the summand is large. The estimate needed in §19.3.1 counts those points with a constant uniform in the compact factors of the Siegel set. Each expanding width contributes its own power. The rational-cover step in §19.3.2 supplies the region on which we use the estimate.

**Example 1 (rank one, Poisson summation).** On a real line of width $u>0$, let $g(x)=e^{-\pi x^2}$. For any $\alpha\in\mathbb R$,
$$
\sum_{k\in\mathbb Z}g((k+\alpha)/u)
=u\sum_{\ell\in\mathbb Z}e^{-\pi u^2\ell^2}e^{2\pi i\ell\alpha}.
$$
Indeed the left side is a continuous periodic function of $\alpha$, by uniform convergence on a period. Its $\ell$-th Fourier coefficient is the integral of $g(x/u)e^{-2\pi i\ell x}$ over the real line, found by unfolding the period. The Gaussian transform is $g$ with this Fourier convention, and the resulting coefficients are absolutely summable, which proves the identity by uniqueness of Fourier coefficients. For $u\ge1$, the difference from $u$ has absolute value at most $2u e^{-\pi u^2}/(1-e^{-\pi u^2})$, by $\ell^2\ge\ell$ for positive integers. For $0<u\le1$, reduce $\alpha$ to $[-1/2,1/2]$. The $k=0$ term is at most one, and the other terms sum to at most $2\sum_{k\ge1}e^{-\pi(k-1/2)^2}$. Thus the uniform bound is a constant times $\max(1,u)$.

In one hyperbolic pair over $\mathbb Q(i)$, with one column, use the Gaussian on the four real coordinates of $\mathbb Z[i]^2$. The two real coordinates on the first line have width $u$ and the two on the second have width $u^{-1}$. The four one-dimensional bounds give growth $O(u^2)$ for $u\ge1$. At zero shift the contracted pair contributes at least one and the expanded pair has sum asymptotic to $u^2$, by the same identity. This exhibits the exponent two in the lattice estimate. [NIST DLMF, §1.8(iv), formula (1.8.14)](https://dlmf.nist.gov/1.8.E14)

**Example 2 (rank two, unequal widths).** Take two hyperbolic pairs over $\mathbb Q(i)$, one column, $t_1=8$ and $t_2=2$. In Witt coordinates on $\mathbb Z[i]^4$, take the inverse-torus box given by the half-open interval $[-1/2,1/2)$ in each scaled real coordinate. Give each of the four expanded real coordinates shift $1/3$, and leave the contracted coordinates unshifted. For the two real coordinates of the first expanded line, the admissible integers satisfy $-4\le k+1/3<4$, so each has eight choices. The second expanded line gives $-1\le k+1/3<1$, hence two choices per real coordinate. The contracted widths are $1/8$ and $1/2$, each giving only zero. The count is $8^2\cdot2^2=256$. A nonnegative smooth compactly supported function equal to one on the closure of the box gives a sum at least this large. For any positive integer widths in place of $8,2$, a half-open interval of integer length contains exactly that many points of every translate of $\mathbb Z$. Taking one width fixed and the other large already distinguishes the separate powers from a bound obtained by using the largest width in both pairs.

**Definition (width and seminorm).** [Expository] Let $\Lambda_j$ be a full lattice in a real normed space $W_j$ of dimension $d_j$, for $1\le j\le q$. Write $D_0=\sum_j d_j$. For widths $s_j>0$ set $R_s(z)=\sum_j\|z_j\|_j/s_j$. For a function on a normed space of real points, write $p_N(f)=\sup_z (1+\|z\|)^N|f(z)|$. This is the order-zero weighted Schwartz seminorm. The adelic version with finite support in a fixed compact set takes the supremum over the permitted finite components as well. A finite sum of Schwartz–Bruhat tensors has this bound for every $N$: the archimedean factors have finite Schwartz seminorms, and each locally constant finite factor is bounded on its compact support. Below we take the archive's Schwartz–Bruhat identification and its majorant as named inputs.

**Lemma (uniform translated lattice estimate).** For $N>D_0$ there is $A_N<\infty$, depending only on the lattices, norms and $N$, such that for every $s$ and every shift vector $\alpha$,
$$
\sum_{z\in\prod_j(\Lambda_j+\alpha_j)}(1+R_s(z))^{-N}
\le A_N\prod_j\max(1,s_j)^{d_j}.
$$
The same estimate applies to the image of any subset under an injective map into the displayed coset, if the weight at a point is bounded by a constant times the weight at its image.

**Proof.** In a fixed lattice basis, a norm ball of radius $v$ lies inside a coordinate cube of radius $B_jv$, with $B_j$ independent of its centre. Each coordinate interval of length $2B_jv$ contains at most $1+2B_jv$ points of a translate of $\mathbb Z$. Thus the number with $R_s(z)\le H$, for $H\ge1$, is at most a fixed constant times $H^{D_0}\prod_j\max(1,s_j)^{d_j}$. On $2^h\le1+R_s(z)<2^{h+1}$, with $h\ge0$, the weight is at most $2^{-hN}$. Apply the counting bound with $H=2^{h+1}$ and sum the geometric series. The zero-dimensional space has one point and needs no decay. For $D_0>0$ the threshold is sharp for the full product with fixed positive widths and the polynomial weight: in lattice coordinates take disjoint dyadic shells in the sup norm. Each has at least a constant times $2^{hD_0}$ points for large $h$, and norm equivalence bounds $1+R_s$ there by a constant times $2^h$. The shell contributions stay bounded below at $N=D_0$ and grow for $N<D_0$. The threshold concerns polynomial domination. A Schwartz function can use higher seminorms. $\square$

**Proposition (conditional adelic torus majorant).** Let $E/F$ be the CM extension in §19.3.1, $b=[F:\mathbb Q]$, $m=\dim_E V$, and let $n$ be the number of columns. Fix a rational Witt frame $(X,Y)$ of size $r$, a cone constant $c>0$, and a compact set $K$ of adelic $m$-by-$n$ matrices. Use the following arithmetic and archimedean inputs.

1. Rational matrices whose finite components lie in the projection of $K$ lie in $L^{-1}\mathcal O_E^{m\times n}$ for some positive integer $L$. In the chosen family of complex realizations, the diagonal realization of $\mathcal O_E$ is a full lattice in the product of the $b$ complex places. We use the archimedean entry-sum norm in these realizations.
2. For an admissible torus element $a(t)$ its finite component is the identity, and its archimedean action multiplies $X_i$ by $t_i$, $Y_i$ by $t_i^{-1}$, and fixes the orthogonal complement.

Write $M_{K,N}(x)$ for the indicator that the finite component of $x$ belongs to the finite projection of $K$, multiplied by $(1+\|x_\infty\|)^{-N}$. Then one may take an integer $N>2bn(2r+m)$ and a constant $C\ge0$, independent of $t$ and the admissible $a(t)$, such that
$$
\sum_{\xi\in E^{m\times n}} M_{K,N}(a(t)^{-1}\xi)
\le C\prod_{i=1}^r t_i^{2bn}.
$$
The same conclusion holds for a compact family of right factors $y$ and the sum of $|\Phi((a(t)y)^{-1}\xi)|$ provided that $|\Phi|\le p_N M_{K_0,N}$ for each $N$ with a common compact $K_0$, and that a compact enlarged support $K$ and a finite $B\ge1$ satisfy, uniformly in $y$,
$$
M_{K_0,N}(y^{-1}x)\le B^N M_{K,N}(x).
$$
Here $p_N$ is the corresponding weighted seminorm or any larger finite bound.

**Proof.** Write $J$ for the Hermitian Gram matrix, $X'=X^*J$, $Y'=Y^*J$, where the star denotes conjugate transpose, and put $P=I-XY'-YX'$. The frame identities are $X'X=Y'Y=0$ and $X'Y=Y'X=I_r$. The map $T$ stacks $Y'$, $X'$, and $P$. It has left inverse $S=(X,Y,I)$ since $ST=I$. In particular it preserves distinctness of rational matrices. For each $\xi$ on the support, $T\xi$ has entries in $(ML)^{-1}\mathcal O_E$ for a fixed positive integer $M$ clearing the denominators of $T$. This embeds the rational summation into a product of $n(2r+m)$ copies of a fixed real lattice of dimension $2b$. The image can lie in a proper subspace of that product.

Set the row widths to $t_i,t_i^{-1},1$ in the three blocks. Applying $T$ to $a(t)^{-1}\xi$ divides each entry of $T\xi$ by the width of its row. Indeed $Y'$ extracts the $X$ coordinates, $X'$ extracts the $Y$ coordinates, and $P$ projects onto the fixed complement. In all the complex realizations the entry-sum norm of this stacked matrix is at most $B_0\|a(t)^{-1}\xi\|$ for a fixed $B_0\ge1$ from the operator norm of $T$. Consequently
$$
(1+\|a(t)^{-1}\xi\|)^{-N}\le B_0^N(1+R_s(T\xi))^{-N}.
$$
The lemma bounds the sum by a constant times $\prod_i(\max(1,t_i)\max(1,t_i^{-1}))^{2bn}$. Each $t_i\ge\delta=(\min(1,c))^r>0$ by the adjacent inequalities and the lower bound on the final coordinate. Therefore $\max(1,t_i)\le\delta^{-1}t_i$ and $\max(1,t_i^{-1})\le\delta^{-1}$. For $r=0$ the product is one. The bound follows. An independent rational basis of the complement reduces the proof's sufficient decay threshold to $N>2bmn$, by replacing the redundant $m$ rows of $P$ with $m-2r$ coordinates on its image. At fixed torus parameters the full rank-$2bmn$ lattice has the corresponding critical polynomial divergence when all of it is allowed by the support. For an arbitrary support, the assertion above is a sufficient bound.

For the compact factors use $(a(t)y)^{-1}=y^{-1}a(t)^{-1}$ and apply the two pointwise estimates before summing. For such a family the finite support enlargement amounts to taking the compact union of the images of the original finite support under $y_f$. In the archimedean part $\|x_\infty\|\le B\|(y^{-1}x)_\infty\|$ follows from bounded operator norms of $y_\infty$ on the compact parameter set. The resulting constant is at most $p_N B^N C$. For a uniformly bounded family of seminorms with common enlarged support the same choice works for the family. $\square$

**Remark (translations and denominators).** The lattice lemma is uniform over arbitrary translates of a fixed lattice. If the summation in the proposition is over a translate of the fixed denominator lattice, the same injection lands in a translate of the enlarged product lattice, with shift $T\alpha$. If a rational translate of the full rational vector space is used in both the evaluation and the support condition, reindex by the translated variable. A finite union of cosets contributes at most the sum of their bounds. Constants depend on the base lattice or a common denominator and stay uniform in the shifts. Replacing the lattice by increasingly fine denominator lattices would change this information: even in $[-1,1]$, the count in $L^{-1}\mathbb Z$ is $2L+1$. In the archive, `InBox K` means equality of finite components with some point of $K$. The declaration `siegelTorus_tsum_majorant_translatedRationalPoints_le` sums over all rational matrices with this finite-support cut and torus inverse; it has no independent additive shift parameter. The compact group factor in its consumer acts by multiplication.

**Remark (absolute summation and integration).** Each admissible $t,y$ gives an absolutely summable series. For measurable summands on a parameter space, Tonelli's theorem for counting measure interchanges the sum of absolute values with the integral, with infinite values allowed. If the majorant is integrable there, the sum of the integrals of the absolute values is finite and Fubini permits termwise integration of the complex series. Continuity of the test function and measurability of the parameter maps give measurable summands. When passing to the adelic quotient one uses the rational invariance and representative measure control of §§19.3.1–19.3.2; rational left multiplication reindexes the sum on the group. The individual summands are functions on the group or on a chosen measurable representative domain. To integrate the series term by term over the quotient, first pull it back to that domain and use its representative measure. For the existing weighted cone estimate the hypothesis is $r=0$ or $n+r<m$. At $r>0$ and $n+r=m$ the last ratio variable in §19.3.1 has density proportional to $dv/v$ in the model majorant. Outside that dimensional range ($n+r>m$) the same model grows by a positive power in that variable. Failure of an integrable upper bound of this form leaves the actual integral undecided by this argument. Without the lower bounds on the widths, even a nonnegative Gaussian with the zero term present rules out a uniform bound by $\prod_i t_i^{2bn}$ as one coordinate tends to zero when $n>0$.

**Remark (production and consumption in Lean).** [Lean, read] In the pinned archive (joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`), the named theorem is a forwarding declaration in `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelTorusTsumMajorantTranslatedRationalPointsLStatement.lean:12–13`. Its producer `GlobalTheory.SiegelSet.tsum_maj_invPt_torus_le`, in the same directory in `SiegelTorusTsumMajorantTranslatedRationalPointsL.lean:13–41`, first obtains $L$ and the stacked bound. At a torus point it uses the finite identity to invoke the denominator bound in the supported branch of `maj`. Entrywise compatibility from `IsInfFam` and multiplicativity of the complex realizations identify the archimedean norm with that in the stacked estimate. The unsupported branch is zero. The Lean inequality uses the nonnegative extended-real sum throughout.

The stacking and enlargement steps are `TorusInverseLatticeCountStackedEigenprojections.lean:14–46` and `LatticeCountSumBoundOfRationalDiagonalising.lean:16–70` in that directory. The latter injects by $T\xi$, clears its denominators, compares the weighted size and enlarges to the entire product indexed by rows and columns. The formal bound there chooses a sufficient natural exponent through `weighted_integral_tuple_lattice_count_bound`; the dyadic argument above gives an explicit sufficient threshold. §19.3.7 reads that proof: the exponent it returns is $N=4bn(2r+m)$, twice this threshold. The rank identity used to express the weight in terms of $F$ is $[E:\mathbb Q]=2[F:\mathbb Q]$.

The direct consumer `AbsThetaSumSiegelSetLeTorusPower.lean:17–64` first obtains the finite support and all-orders decay, enlarges the support for the compact inverse action, then chooses $N$ from the lattice theorem. Only then does it take the two constants at that order. `WeilThetaConvergenceOfSiegelSet.lean:23–54` takes the compact right factors from the compact conjugation set times the compact group supplied along the SiegelCore route, using $pak=a(a^{-1}pa k)$. It feeds the product bound to the independent weighted integration and quotient estimates. Gan–Qiu–Takeda give the classical convergent range in §3.1, with $d(n)=n$ for the quadratic extension in §2.2. [Gan–Qiu–Takeda, v3](https://arxiv.org/pdf/1207.4709v3)

**Reading boundary.** §19.3.4 supplies the denominator, full-lattice and compact-factor lemmas. The archive’s weighted product counting implementation is read in §19.3.7. §19.3.5 supplies the Schwartz–Bruhat majorant.

### 19.3.4 From finite support to a fixed Minkowski lattice

**Motivation.** A bound at infinity alone leaves infinitely many points of the rational vector space in every neighbourhood of zero. The finite support of an adelic test function remedies this by giving one integer denominator. At infinity the integral points then occupy a discrete grid with one real dimension for each real place and two for each complex place. The order matters in §19.3.3: enlarge the support to handle the compact right factors, fix a denominator for that enlargement, and use the resulting grid for every torus parameter.

**Example 1 (two finite primes over $\mathbb Q$).** At all primes other than $2,3$ impose integrality. For the box $2^{-2}\mathbb Z_2\times 3^{-1}\mathbb Z_3$ at $2,3$, a reduced fraction $a/b$ has $v_2(b)\le2$, $v_3(b)\le1$, and no other prime dividing $b$. The diagonal points form $\frac1{12}\mathbb Z$. The point $1/12$ shows that any positive common denominator is divisible by $12$. In the real interval $[-1/2,1/2]$ the numerators range from $-6$ to $6$, giving thirteen points.

For a second box use the same outside conditions and take $1/4+\mathbb Z_2$ and $1/3+\mathbb Z_3$ at the two primes. These boxes lie inside the first one, so again write $x=k/12$. The two translated conditions are $k\equiv 3\pmod 4$ and $k\equiv 4\pmod 3$. Their joint solution is $k\equiv 7\pmod{12}$, giving $7/12+\mathbb Z$. In $[-1/2,1/2]$ its only point is $-5/12$. The common denominator remains $12$, as $7/12$ is reduced. Both boxes are compact in the restricted product topology.

**Example 2 (a Gaussian fractional ideal).** In $E=\mathbb Q(i)$ take $I=(1+i)^{-1}\mathbb Z[i]$. Impose valuation at least $-1$ at the prime $(1+i)$ and at least zero at every other finite prime. Factorization in $\mathbb Z[i]$ gives exactly the diagonal points of $I$. The integer $2=(1+i)(1-i)$ clears $I$, whereas $1$ fails at $(1+i)^{-1}$. Under $i\mapsto i$ its basis vectors are $(1/2,-1/2)$ and $(1/2,1/2)$ in real and imaginary coordinates. The determinant is $1/2$, so the fundamental parallelogram has area $1/2$. The coordinates of the point indexed by $(a,b)\in\mathbb Z^2$ are $((a+b)/2,(b-a)/2)$. In the square $[-1/2,1/2]^2$ the doubled coordinates are both in $\{-1,0,1\}$ and must have the same parity. This gives the origin and four corners. The larger lattice $\frac12\mathbb Z[i]$ has nine points in that square. This is the kind of enlargement used after stacking the matrix coordinates.

**Definitions.** Write $\mathbb A_{E,f}=\prod_{v<\infty}' E_v$ for the restricted product relative to the local integer rings $\mathcal O_v$. Thus each element is integral at almost all finite places, and $\widehat{\mathcal O}_E=\prod_{v<\infty}\mathcal O_v$ is a compact open subring. Put $E_\infty=\mathbb R^{r_1}\times\mathbb C^{r_2}$, taking all real embeddings and one member of each complex conjugate pair. Denote the resulting diagonal map by $\iota$. A full lattice is the integer span of a real basis. Use the sum of the real absolute values and complex moduli as the norm, summed over entries for matrices. For $E$ CM, $r_2=[F:\mathbb Q]$ for its maximal totally real subfield $F$. The tensor-product model in the archive uses finite and infinite components over $F$ with coefficients extended to $E$. The usual adelic base change identifies this with the place model. [Sutherland, Lecture 25, Definition 25.7 and Proposition 25.10](https://math.mit.edu/classes/18.785/2021fa/LectureNotes25.pdf)

**Lemma (common denominator and full lattice).** For every compact $K_f\subset\mathbb A_{E,f}^{m\times n}$ there is a positive integer $L$ such that every $\xi\in E^{m\times n}$ with $\xi_f\in K_f$ belongs to $L^{-1}\mathcal O_E^{m\times n}$. The image of $L^{-1}\mathcal O_E$ in $E_\infty$ is a full lattice of real dimension $[E:\mathbb Q]$. The same full-lattice assertion holds for every nonzero fractional ideal.

**Proof.** The factorials $h!$ converge to zero in the finite adeles: at each fixed finite place over $p$, the valuation grows without bound, and every factorial is integral at all places. A basic neighbourhood imposes extra conditions at only finitely many places. For each $z\in K_f$, continuity of multiplication gives neighbourhoods $U_z$ of zero in the scalar ring and $V_z$ of $z$ in the matrix space such that $U_zV_z\subset\widehat{\mathcal O}_E^{m\times n}$. Take a finite subcover by the $V_z$ and intersect the corresponding $U_z$. Take $L=h!$ in the intersection. For an empty set one can take $L=1$. This proves that $L K_f$ is integral everywhere at the finite end. A nonzero field element integral at all finite places has only nonnegative prime-ideal exponents in its principal fractional ideal, and its principal fractional ideal therefore lies in $\mathcal O_E$. Apply this to the entries of $L\xi$, including zero directly. In the formal proof of the matrix statement one first forms the finite union of the compact entry projections and invokes the scalar result once on that union.

For the infinite end let $d=[E:\mathbb Q]$, and take a $\mathbb Z$-basis of $\mathcal O_E$. It is a $\mathbb Q$-basis of $E$. In the power basis of a primitive element, the square matrix of all $d$ complex-valued embeddings is a Vandermonde matrix on its distinct conjugates. Its determinant is nonzero and stays nonzero after the invertible rational change of basis to the integral basis. A real linear relation between the vectors in $E_\infty$ would also hold at the omitted conjugates, by complex conjugation of the relation. The square matrix then forces all coefficients to vanish. These $d$ vectors are a real basis of the $d$-dimensional space. The basis matrix takes $\mathbb Z^d$ homeomorphically to a discrete subgroup with compact fundamental parallelepiped. Scaling by $L^{-1}$ preserves these properties. For a fractional ideal $I$, choose $a\in I$ nonzero and $D>0$ integral with $DI\subset\mathcal O_E$. Then $a\mathcal O_E\subset I\subset D^{-1}\mathcal O_E$, so $I$ is a free abelian group of rank $d$ spanning $E$ over $\mathbb Q$. The same basis proof applies. $\square$ [Milne, Proposition 4.26, pp. 79–80](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

**Lemma (matrix action and scaled norm).** Fix $T\in E^{q\times m}$. There is an integer $M>0$ such that for every $L>0$ integral and every $\xi\in L^{-1}\mathcal O_E^{m\times n}$, one has $T\xi\in(ML)^{-1}\mathcal O_E^{q\times n}$. If $S\in E^{m\times q}$ satisfies $ST=I$, the map $\xi\mapsto T\xi$ is injective. For positive row widths $s_k$ and matrices $B_\sigma$ at infinity such that $T_\sigma B_\sigma=\operatorname{diag}(s_k^{-1})T_\sigma$ at every chosen place, one has
$$
 R_s(\iota(T\xi))=\sum_{k,j,\sigma}\frac{|\sigma((T\xi)_{kj})|}{s_k}
 \le C_T\sum_{\sigma,i,j}|(B_\sigma\xi_\sigma)_{ij}|.
$$
Here $T_\sigma$ and $\xi_\sigma$ are entrywise realizations and $C_T\ge1$ can be chosen before $s,B,\xi$.

**Proof.** Express the entries of $T$ in an integral basis and clear their rational coefficients with one $M$. Each entry of $(ML)T\xi=(MT)(L\xi)$ is a sum of products of algebraic integers. The formal proof takes a common nonzero integer multiplier and squares its absolute value to obtain a positive natural multiplier. Apply $S$ to recover $\xi$. For the estimate the matrix identity gives $s_k^{-1}\sigma((T\xi)_{kj})=(T_\sigma B_\sigma\xi_\sigma)_{kj}$. The triangle inequality and the bound on each column sum $\sum_k|(T_\sigma)_{ki}|$ by $1+\sum_{\sigma,k,i}|(T_\sigma)_{ki}|$ give the result. The formal proof uses the coarser constant $1+q\sum_{\sigma,k,i}|(T_\sigma)_{ki}|$. $\square$

**Theorem (arithmetic and compact-factor supply for §19.3.3).** Let $E/F$ be CM and fix a Hermitian $E$-space of dimension $m$ with rational Witt frame $X,Y$ of size $r$. Fix $n$ and $c>0$. Let $t$ range over positive coordinates with $t_i\ge c t_{i+1}$ and $t_r\ge c$ when $r>0$. Assume an adelic torus action $a(t)$ whose finite component is the identity and which, at each complex place, acts by $t_i$ on $X_i$, by $t_i^{-1}$ on $Y_i$, and by the identity on the orthogonal complement. Fix a compact finite support $K_0$ and a compact subset $Q$ of the adelic matrix group acting continuously on the left. Let $\Phi$ be a function on the adelic matrix space such that for every nonnegative integer $N$,
$$
 |\Phi(x)|\le p_N\mathbf 1_{K_0}(x_f)(1+\|x_\infty\|)^{-N},\qquad p_N<\infty.
$$
Then there is a constant $C<\infty$ such that for every admissible $t$ and $y\in Q$,
$$
 \sum_{\xi\in E^{m\times n}}|\Phi((a(t)y)^{-1}\xi)|
 \le C\prod_{i=1}^r t_i^{[E:\mathbb Q]n}.
$$
With measurable summands on a parameter measure space and an integrable right side, the series may be integrated termwise there. The quotient application uses the representative-domain and measure hypotheses in §§19.3.1–19.3.3.

**Proof.** The set $K_f=\{y_f z_f:y\in Q,\ z_f\in K_0\}$ is the continuous image of a compact product. Choose $L$ for this $K_f$. When a summand is nonzero, $y_f^{-1}\xi_f\in K_0$ by the finite identity of $a(t)$, hence $\xi_f\in K_f$. This gives one $L$ simultaneously for all $t,y,\xi$ and all decay orders. For $x=a(t)^{-1}\xi$, compactness bounds the archimedean matrix operator norms of $y$ by some $H\ge1$. Thus $\|x_\infty\|\le H\|(y^{-1}x)_\infty\|$. The inverse action has left inverse $y$, with this uniform bound.

Let $J$ be the Gram matrix and write $X'=X^*J$, $Y'=Y^*J$, where the star denotes conjugate transpose. Set $P=I-XY'-YX'$, stack $T=(Y',X',P)$ vertically, and take $S=(X,Y,I)$ horizontally. Then $ST=I$. The Witt identities show that $Y'$ extracts the $X$ coordinates, $X'$ the $Y$ coordinates, and $P$ the complement. Consequently $B_\sigma=a(t)_\sigma^{-1}$ satisfies the scaled matrix identity with row widths $t_i,t_i^{-1},1$, respectively. The left inverse of the rational stack is fixed. The compact factor is controlled by the separate identity $x=y(y^{-1}x)$, so the rational injection stays $T$.

By the lemmas the supported points inject by $\iota(T\xi)$ into the fixed product of $qn$ copies of $\iota((ML)^{-1}\mathcal O_E)$, with $q=2r+m$. Their summands are bounded by $p_N(HC_T)^N(1+R_s)^{-N}$. Choose an integer $N>qn[E:\mathbb Q]$. Apply the product lattice estimate of §19.3.3 with this order and enlarge the sum to the whole product by nonnegativity. The bound is a constant times $\prod_i(\max(1,t_i)\max(1,t_i^{-1}))^{[E:\mathbb Q]n}$. The cone gives $t_i\ge\delta=(\min(1,c))^r$ by iteration, so the product is at most $\delta^{-2r[E:\mathbb Q]n}\prod_i t_i^{[E:\mathbb Q]n}$. At $r=0$ the product is empty and equals one. For measurable summands, Tonelli first gives finiteness of the sum of absolute integrals by the integrable bound. Fubini then applies to the scalar series. $\square$

**Failure of uniformity.** With the noncompact set of finite diagonal images of $2^{-j}$, $j\ge0$, every proposed positive $L$ fails for $j>v_2(L)$. The points even lie in a bounded real interval, where infinitely many carry weight at least $2^{-N}$ for any fixed order $N$. Conversely compact finite support cannot compensate for a missing archimedean place. In the CM field $\mathbb Q(\sqrt 2,i)$ keep only the place with $\sqrt2\mapsto+\sqrt2$ and $i\mapsto i$. The distinct algebraic integers $(\sqrt2-1)^j$ all pass the integral finite box and tend to zero at the retained place, while the modulus in the other complex place is $(\sqrt2+1)^j$. The partial projection has accumulation at zero, and its polynomial-weight sum at unit widths diverges. Keeping one member of each conjugate pair retains both real coordinates of that place.

**Reading the production proof.** [Lean, read] Archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The scalar proof uses the pullback of the open subgroup `intAE` under the continuous finite projection, and the scalar sequence with infinite component zero and finite component $h!$. Using the finite-component equality, it transfers subgroup membership to the diagonal point $h!\xi$ and reads off integrality. The theorem `exists_denominator_bound_matrix_mul` supplies $M$ before $L$, and `exists_scaledEmbeddingNorm_bound_hostField` supplies $C_T$ before the widths and matrices. The latter is a triangle-inequality estimate even for a finite list of maps. Full place coverage is needed when using that estimate for lattice counting. The formal proof enlarges the supported sum in nonnegative extended reals. The compact multiplication proof uses the compact image of the full box and the bound $\max(1,n\sup_{y\in Q}\operatorname{realSize}(y))$ for a nonempty family, then raises the bound to order $N$. Our finite projection of the image gives the same support condition.

| Role | Archive-relative source and proof lines |
|---|---|
| Scalar denominator and its public forwarding declaration | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RationalFinPartInCompactBoundedDenominator.lean:19–45`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RationalFinPartInCompactBoundedDenominatorStatement.lean:12–13` |
| Factorial transfer and compactness argument | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/StdCharAnnihilatorOpenSubgroupFinPartCompact.lean:63–68,90–113`, `src/Development/AbelianVarietyTheory/Definitions/HeightFunctions/IntegralOfMemIntAE.lean:102–109` |
| Matrix denominator and scaled norm with forwarding declarations | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDenominatorBoundMatrixMul.lean:11–40`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScaledEmbeddingNormBoundHostField.lean:11–77`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDenominatorBoundMatrixMulStatement.lean:12–13`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScaledEmbeddingNormBoundHostFieldStatement.lean:12–13` |
| Compact image and operator bound | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompactBoxOfUnitaryTranslateCompact.lean:12–25`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicMatrixRealSizeLeConstMulOfCompactTranslate.lean:16–52`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicMatrixSchwartzMajorantInvMulLe.lean:13–35` |
| Consumers giving the fixed entry denominator, injection, support cut and right-factor estimate | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBoundedDenominatorRationalMatricesInBox.lean:13–24`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeCountSumBoundOfRationalDiagonalising.lean:16–70`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelTorusTsumMajorantTranslatedRationalPointsL.lean:13–41`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsThetaSumSiegelSetLeTorusPower.lean:17–64` |

**Reading boundary.** [Lean] The formal inputs behind these proof bodies include `GlobalTheory.AdSplit.exists_adele_equiv`, `GlobalTheory.SchwartzBruhatTensor.isOpen_intAE`, `GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele`, `GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral`, `GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff`, and Mathlib's `exists_integral_multiples`. The formal compact norm uses `continuous_realSize`, `continuous_mt'`, `compAt_mul`, and `norm_compAt_le_realSize`. The proof here supplies full-lattice and norm facts in the standard place model. The archive's integral-coordinate counting implementation `weighted_integral_tuple_lattice_count_bound` is read in §19.3.7. Its identification of the chosen embeddings with place coordinates, `GlobalTheory.CMTypePlaces.mk_tauE_bijective`, is read in §19.3.8. Its statement coincides with that of `LevelSeries.mk_tauE_bij` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharInfinityEqCoeffMulHalfNormPow.lean:62`), which is not on this path. The torus component and eigenprojection interfaces in §19.3.3 retain their stated roles. §19.3.5 proves the Schwartz–Bruhat input. The theorem above uses their geometric and test-function conclusions as hypotheses. The Siegel-set cover and integration of the weighted cone are used as in the preceding subsections.

### 19.3.5 A common finite support for Schwartz majorants

**Motivation.** In §19.3.4, the denominator is chosen from a compact finite box and the lattice estimate then prescribes an order of decay. This requires a box that works before the order is known. It also requires, at that order, a constant that works for every adelic matrix and every right factor in the compact family. Decay on separate archimedean slices with unrestricted slice-dependent constants would leave this last step unjustified.

**Example over $\mathbb Q$.** Write $\widehat{\mathbb Z}=\prod_p\mathbb Z_p$ and take
$\Phi(x)=e^{-\pi x_\infty^2}\mathbf 1_{(1/2)\widehat{\mathbb Z}}(x_f)$ on $\mathbb A_{\mathbb Q}$. This is one Schwartz tensor. The finite factor is the indicator of a compact open additive subgroup, and each derivative of the Gaussian is a polynomial times the Gaussian. To illustrate inverse multiplication, fix the compact set of scalar ideles $y$ with $y_\infty=s\in[1,2]$ and $y_f\in\widehat{\mathbb Z}^{\times}$. Multiplication by $y_f$ preserves the box $K=(1/2)\widehat{\mathbb Z}$. On that box, $|\Phi(y^{-1}x)|=e^{-\pi(x_\infty/s)^2}$. For $u\ge0$, $N\ge1$, and $\alpha>0$,
$$(1+u)^N e^{-\alpha u^2}\le 2^N\max\{1,(N/(2\alpha e))^{N/2}\}.$$
Indeed $1+u\le2\max(1,u)$ and the logarithmic derivative of $u^N e^{-\alpha u^2}$ for $u>0$ is $N/u-2\alpha u$, so its maximum occurs at $u=\sqrt{N/(2\alpha)}$. With $\alpha=\pi/4$ this gives a single constant for all $s,x$ at each $N\ge1$. At $N=0$ the constant is $1$.

For a rational $x$, the box condition means $2x\in\mathbb Z_p$ for every $p$, hence $x=k/2$ for an integer $k$ by prime factorization of denominators. The absolute series is $1+2\sum_{k\ge1}e^{-\pi k^2/(4s^2)}$. Since $s\le2$ and $k^2\ge k$, this is bounded by $1+2q/(1-q)$ for $q=e^{-\pi/16}$. In particular the scalar series can be integrated term by term in $s$ against Lebesgue measure on $[1,2]$. This is a scalar illustration of the compact-factor estimate.

**Example over the Gaussian integers.** Let $E=\mathbb Q(i)$ and $\mathcal O=\mathbb Z[i]$. There is one complex place, with two real coordinates. Use
$\Phi(z)=e^{-\pi |z_\infty|^2}\mathbf 1_{\prod_{v<\infty}\mathcal O_v}(z_f)$.
All real partial derivatives are polynomials in the two coordinates times the Gaussian. Fix scalar ideles $y$ with $1\le |y_\infty|\le2$ and $y_v\in\mathcal O_v^\times$ for every finite $v$. The one finite box is preserved by every such $y$. The preceding one-variable inequality with $u=|z_\infty|$ and $\alpha=\pi/4$ bounds all the translates simultaneously at each order. An element of $\mathbb Q(i)$ in the box is in $\mathbb Z[i]$: in a reduced fraction of Gaussian integers, any prime dividing the denominator would give negative valuation. Thus the absolute series, for $s=|y_\infty|$, factors as
$$\sum_{a,b\in\mathbb Z} e^{-\pi(a^2+b^2)/s^2}
=\left(1+2\sum_{a\ge1}e^{-\pi a^2/s^2}\right)^2
\le\left(1+\frac{2e^{-\pi/4}}{1-e^{-\pi/4}}\right)^2.$$
The factorization follows first for rectangular partial sums and then by monotone convergence. The uniform bound works for any finite measure on the displayed compact parameter set. The two independent integer sums account for both real directions of this complex place. [Expository]

**Definition (place model).** Let $E$ be a number field, $X=\operatorname{Mat}_{m,n}$, and write $X(\mathbb A_E)=X_\infty\times X_f$ using the product of all archimedean places and the finite restricted product. Put $R(x)=\sum_{v\mid\infty,i,j}|x_{v,ij}|$, using ordinary complex modulus at a complex place. A Schwartz–Bruhat test function here is a finite sum of products $c_j f_j(x_\infty)g_j(x_f)$, with $f_j$ Schwartz on the entire real vector space $X_\infty$, and $g_j$ locally constant with compact support. The classical restricted tensor product description uses integral-lattice indicators at almost all finite places. [Gan–Qiu–Takeda, §2.1, p. 8](https://arxiv.org/pdf/1207.4709v3) · [Sutherland, Definition 25.7](https://math.mit.edu/classes/18.785/2021fa/LectureNotes25.pdf)

**Lemma (finite-level description).** In the place model the test functions are exactly the functions with a global open additive group of finite periods, a compact finite set containing the finite projection of their nonzero locus, and Schwartz restrictions along every injective real affine parametrization in the archimedean directions.

*Proof.* For a locally constant compactly supported $g$, compactness gives a finite cover of its support by cosets of compact open additive subgroups on which $g$ is constant. Their intersection is compact open. Each covering coset is invariant under the intersection, as is the complement of their union, on which $g$ vanishes. Thus the intersection consists of global periods. For a finite sum intersect these period groups and unite the finite supports. A continuous additive map from a real vector space to $X_\infty$ is real linear by rational homogeneity and continuity. An injective such map $A$ has $\|At\|\ge c\|t\|$ for a positive $c$, by the minimum on the unit sphere in positive dimension. For a fixed translate $b$ this bounds $1+\|t\|$ by a constant times $1+\|b+At\|$. By the chain rule each derivative of $f(b+At)$ is a linear combination with constant coefficients of derivatives of $f$ evaluated there. Thus all derivative-weight bounds hold along the affine slice. In dimension zero the restriction is a scalar.

Conversely take a compact open additive subgroup $W$ inside the given group of finite periods. Such subgroups form a neighborhood basis by the restricted product topology and the local integral lattices. The compact finite support meets only finitely many $W$-cosets, since these cosets form an open cover by disjoint sets. For each such coset $q$, choose its representative $z_q$. The full archimedean parametrization shows that $f_q(u)=\Phi(u,z_q)$ is Schwartz. Invariance gives
$$\Phi(u,z)=\sum_q f_q(u)\mathbf 1_{z_q+W}(z).$$
On a listed coset there is exactly one contributing coefficient, and outside their union both sides vanish. The indicators are locally constant and compactly supported. $\square$

**Theorem (common-support Schwartz majorant).** Fix a test function $\Phi$ and a compact family $Q$ of invertible adelic left multipliers, acting as in §19.3.4. Then $\Phi$ is continuous and there exists a compact $K_Q\subset X_f$ such that
$$\forall N\in\mathbb Z_{\ge0}\quad \exists C_N\ge0\quad \forall y\in Q\quad \forall x\in X(\mathbb A_E),\qquad
|\Phi(y^{-1}x)|\le C_N\mathbf 1_{K_Q}(x_f)(1+R(x))^{-N}.$$
For each order the right side is a nonnegative Borel function of $x$. In the theta application, set $x=a^{-1}\xi$ with $a$ an admissible torus element. The resulting series of majorants for the order prescribed by the lattice estimate in §19.3.3 is finite pointwise and satisfies the torus-power estimate of §19.3.4. On measurable parameter domains with that torus power integrable, the theta series may be integrated term by term.

*Proof.* Choose a finite tensor expression and let $K$ be the union of the supports of its $g_j$. Continuity follows from continuity of the two projections and of both factors. Set $K_Q=\{y_f z:y\in Q,\ z\in K\}$, a compact image. If $K$ or $Q$ is empty the bounds are immediate. Otherwise choose $H\ge1$ bounding the archimedean operator norms of $y$ on $Q$, with respect to $R$. Then $R(x)\le H R(y^{-1}x)$. These choices precede $N$.

Given $N$, set $G_j=\sup_z|g_j(z)|<\infty$ and $S_{j,N}=\sup_u (1+R(u))^N|f_j(u)|<\infty$. The second supremum is a Schwartz seminorm in an equivalent norm, since the sum of moduli over all places and entries is a norm on the finite-dimensional real space. The first is finite by compact support and continuity. The triangle inequality gives a constant $P_N=\sum_j |c_j|G_j S_{j,N}$ for the untranslated bound on $K$. A nonzero translated term forces $x_f\in K_Q$, and $1+R(x)\le H(1+R(y^{-1}x))$. Hence take $C_N=H^N P_N$. The suprema are taken across entire spaces. Equivalently, in the coset expression, take the finitely many full archimedean seminorms and sum them. Compactness of $K_Q$ makes it closed in the Hausdorff finite matrix space. Its indicator is Borel, and the inverse polynomial factor is continuous and nonnegative.

For the consumer fix the Witt frame and cone as in §19.3.4. With $K_Q$ fixed, use the common denominator and fixed rational injection of that subsection. The weighted lattice estimate then selects a sufficient order $N$, after which the proof evaluates $C_N$. For each $\xi\in X(E)$ the group map $h\mapsto h^{-1}\xi$ is continuous. This gives measurable theta summands and, on measurable parameter domains, measurable composed majorants. The rational index set is countable since $E$ has a finite basis over $\mathbb Q$. Thus the sum of nonnegative majorants and the absolute theta sum are measurable extended real functions. At the selected order the sum of majorants is bounded by $B\prod_i t_i^{[E:\mathbb Q]n}$ for a fixed finite $B\ge0$ by the preceding lattice estimate. On any measurable parameter domain where that bound is integrable, monotone convergence applied to finite partial sums gives
$$\sum_\xi\int |\Phi(h^{-1}\xi)|=\int\sum_\xi |\Phi(h^{-1}\xi)|<\infty.$$
In particular the scalar partial sums are dominated by an integrable function and dominated convergence gives $\int\sum_\xi\Phi(h^{-1}\xi)=\sum_\xi\int\Phi(h^{-1}\xi)$. For the quotient use the cover of §19.3.2 and the measure estimates of §19.3.1 in their stated range. Left rational translation reindexes the entire absolute sum by a bijection of $X(E)$. Termwise integration uses the summands on a measurable representative domain with the induced measure, as in §19.3.3. $\square$

**Failure examples.** With finite factor $\mathbf 1_{\widehat{\mathbb Z}}$ and infinite factor $(1+x_\infty^2)^{-1/2}$ over $\mathbb Q$, all integers survive. For positive integers $k$, $(1+k^2)^{-1/2}\ge 1/(\sqrt2 k)$, so even at the identity the absolute sum diverges. This smooth archimedean factor with a compact finite cutoff lacks rapid decay. Conversely let $K_j=2^{-j}+\widehat{\mathbb Z}$ for $j\ge1$. These cosets are pairwise disjoint, and their union is clopen since it is a union of cosets of an open subgroup whose complementary cosets are open as well. Take the real Gaussian times the indicator of this union. Every archimedean slice has rapid decay with constants even independent of the slice, while $x=2^{-j}$ gives distinct diagonal points of absolute value at least $e^{-\pi/4}$. No compact finite set can contain all their finite images: their images in the discrete quotient by $\widehat{\mathbb Z}$ are infinitely many distinct points. The missing common compact support allows divergence. [Expository]

**Reading the archive.** [Lean, read] The two public declarations forward to `SchwartzPure.isSchwartzBruhat_of_mem_schwartzA` and `SchwartzMaj.continuous_and_le_maj`. The first uses span induction. For a pure tensor it pulls back the open period group of the finite factor and uses its compact support. Along a real parametrization the size bounds make the coordinate map continuous and injective. Its linear lower bound makes the affine map antilipschitz, giving Schwartz pullback with a constant finite factor. The second declaration first uses the reverse implication of the Schwartz equivalence. The reverse proof intersects the finite pullback of the level with the integral finite matrix subgroup, covers the support by finitely many cosets, and uses a full real chart to obtain the Schwartz coefficients at coset representatives.

For a pure tensor the formal majorant lifts the finite support by the continuous section $z\mapsto(0,z)$, since `InBox` is defined by equality of finite projections to a point of a compact set of full matrices. The sum of all coordinate moduli `realSize` obeys $1+\operatorname{realSize}(x)\le(1+k)(1+\|x_\infty\|_{\mathrm{sup}})$ for $k$ the number of complex entries across the chosen family. The order-zero derivative seminorm at weight $N$ supplies the uniform bound for the infinite factor, and the bounded finite factor supplies the other constant. For addition the formal proof uses a compact union and sums the absolute values of the two constants via monotonicity of the box majorant. In `absTheta_le_torus`, the actual order is test function and compact family, box $K$, compact enlargement $K'$, counting order $N$, test-function constant and compact-translation constant at $N$. Nonnegativity permits termwise comparison in the extended nonnegative reals. The separate measurability proof uses continuity of inverse evaluation and countability, then descends the absolute sum by left invariance.

Archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

| Role | Archive-relative source and lines |
|---|---|
| Span and mixed conditions | `src/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/ModerateGrowthSchwartz.lean:19–23`, `src/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/SchwartzBruhatMixedFamilies.lean:15–27` |
| Forward direction | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartzStatement.lean:18–19`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz.lean:26–214` |
| Equivalence and coset decomposition | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsSchwartzBruhatIffMemAdelicMatrixSchwartzSpaceStatement.lean:16–17`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsSchwartzBruhatIffMemAdelicMatrixSchwartzSpace.lean:16–21`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemSchwartzAOfIsSchwartzBruhat.lean:19–53,61–97,107–137,145–241` |
| Majorant | `src/Development/AbelianVarietyTheory/Definitions/LatticeFrames/RealSizeNonneg.lean:17–24,35–42`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement.lean:18–19`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatAdelicMatrixContinuousLeMajorant.lean:20–150` |
| Theta bound and measurability consumers | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsThetaSumSiegelSetLeTorusPower.lean:17–64`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsoluteThetaIntegralLeContinuousSeminorm.lean:29–45` |

**Reading boundary.** R3 here covers the cited bodies only. The place model in the theorem is the standard adelic model. The archive's comparison and chart inputs `AdSplit.exists_adele_equiv`, `RealLineAt.exists_inverse_chart`, `Member.continuous_finPart`, `RealWeil.continuous_compAt`, and `adelicMatrixRealSize_bounds_along_real_parametrisation` are used at their interfaces in this subsection. [§19.3.6](#1936-compatible-adelic-coordinates-and-real-parameters) reads the splitting, inverse chart and real-parameter size producers. The integral subgroup wrappers use `IdeleParts.isOpen_nsmul_adelicCompletion_integers`, `IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers`, and `SmoothForms.Cover.exists_compact_denom` at statement level. The Schwartz pullback and seminorm library lemmas and the quotient helpers `leftInv_absTheta` and `measurable_from_quotient` are used at their interfaces. The earlier adelic model, weighted counting and deeper spectral boundaries retain the scope recorded in §§19.3.3–19.3.4. The two hand calculations and the Borel and termwise-integration argument are textbook exposition.

### 19.3.6 Compatible adelic coordinates and real parameters

A Schwartz tensor evaluates its finite and infinite factors on the two projections of one matrix. In the converse construction of §19.3.5, a finite coset representative is lifted with zero archimedean coordinate, and a real parameter is lifted with zero finite coordinate. To use the resulting estimate inside the theta sum, the two lifts, matrix multiplication, and the size of a matrix must all refer to the same coordinates.

**Example over $\mathbb Q$.** In the ordinary real-place model, take the two-real-parameter family and the origin of the affine slice to be
$$
 L(u,v)=\left(\begin{pmatrix}u&v\\0&0\end{pmatrix},0\right),
 \qquad
 b=\left(\begin{pmatrix}1&-1\\0&0\end{pmatrix},
                 \begin{pmatrix}1/2&0\\0&0\end{pmatrix}_{f}\right).
$$
The subscript $f$ means the diagonal finite adele of the rational entries. The finite coordinate of $b+L(u,v)$ stays equal to $b_f$, and its first real row is $(1+u,-1+v)$. Subtracting the real row of $b$ recovers $(u,v)$, and adding the zero-infinite finite lift and the zero-finite infinite lift recovers the original matrix. Here and below size is the sum of the absolute values of the archimedean entries. Thus $R(L(u,v))=|u|+|v|\le 2\|(u,v)\|_\infty$ and
$$
 \|(u,v)\|_\infty\le |u|+|v|
 \le |1+u|+|-1+v|+2
 =R(b+L(u,v))+R(b).
$$
Now take the compact right factors $g_s$ with real part $\left(\begin{smallmatrix}1&s\\0&1\end{smallmatrix}\right)$ and finite part $I_2$, for $|s|\le1$. The first row of $L(u,v)g_s$ is $(u,v+su)$. Its size is at most $2(|u|+|v|)$ since $|v+su|\le |v|+|u|$. The inverse row operation $(r,w)\mapsto(r,w-sr)$ gives the reverse bound with the same factor $2$. In particular
$$
 \tfrac12\|(u,v)\|_\infty\le R(L(u,v)g_s)\le 4\|(u,v)\|_\infty .
$$
Every product keeps its original finite coordinate. The one-place real chart is the ordinary zero-finite inclusion. This example illustrates the splitting and bounds in a real place.

**Example over $\mathbb Q(i)$.** Take $F=\mathbb Q$, $E=\mathbb Q(i)$ and the embedding sending $i$ to $i$. Put $\alpha=(1/2)_f\otimes 1$ and $\beta=1_f\otimes i$ in the finite tensor ring. Set
$$
 b=\left(\begin{pmatrix}1&i\\0&0\end{pmatrix},
          \begin{pmatrix}\alpha&\beta\\0&0\end{pmatrix}\right),
 \qquad
 L(u,v)=\left(\begin{pmatrix}u+iv&0\\0&0\end{pmatrix},0\right).
$$
Concretely the top-left entry of $b+L(u,v)$ in the unsplit ring is
$$
 (1+u,1/2_f)\otimes1+(v,0)\otimes i .
$$
The top-right entry is $(1,1_f)\otimes i$. These tensors give precisely the displayed finite matrix and the infinite row $(1+u+iv,i)$. The inverse of the parameter chart on the difference from $b$ reads the real and imaginary parts of its top-left entry. The size satisfies
$$
 \|(u,v)\|_\infty\le |u+iv|\le\sqrt2\|(u,v)\|_\infty,\qquad
 |u+iv|\le |1+u+iv|+1\le R(b+L(u,v))+R(b).
$$
For $1\le r\le2$ take $g_r$ with complex part $\left(\begin{smallmatrix}ir&1\\0&1\end{smallmatrix}\right)$ and finite part $I_2$. For any first row $(z,w)$ its image is $(irz,z+w)$, with size $r|z|+|z+w|\le 3(|z|+|w|)$. Conversely $|w|\le |z+w|+|z|$, so $|z|+|w|\le 2(r|z|+|z+w|)$. In particular $L(u,v)g_r$ has size $(r+1)|u+iv|$, between $2\|(u,v)\|_\infty$ and $3\sqrt2\|(u,v)\|_\infty$. The finite row of $b$ remains $(\alpha,\beta)$ throughout.

This example also shows what can go wrong with separately chosen coordinate identifications. Label the coordinate of the matrix $x$ supported in the top-left entry with coordinates $(i,0)$ using $i\mapsto i$, and that of the right factor with complex part $\operatorname{diag}(i,1)$ using $i\mapsto-i$. Their displayed entries would multiply to $1$ in the top left, whereas the product read in the first chart has entry $-1$. Even the affine sum can fail: reading $x$ in the first chart and $-x$ in the second gives $i+i$ in place of $0$. A single simultaneous conjugation preserves the identities and moduli. Independent chart choices can preserve individual sizes while destroying the algebraic identities that the size and support arguments use. [Expository]

**Definitions.** Let $F$ be a number field, let $E/F$ be finite, and put $A=\mathbb A_{F,\infty}$ and $B=\mathbb A_{F,f}$. Write $T=(A\times B)\otimes_F E$, $T_\infty=A\otimes_F E$, and $T_f=B\otimes_F E$, with their respective module topologies over $A\times B$, $A$, and $B$. Write $p,q$ for the ring maps induced by the two projections. We use these same letters entrywise on matrices. The classical place interpretation of adelic base change is a separate comparison. The tensor splitting below already supplies both projections in the archive's model. [Sutherland, Definition 25.7 and Proposition 25.10](https://math.mit.edu/classes/18.785/2021fa/LectureNotes25.pdf)

For the archimedean chart, assume $F$ is totally real and $E=F(\delta)$ is CM with $\delta^2=-d$ for a positive rational $d$. Fix a finite family $\theta_\tau:T_\infty\to\mathbb C$ of continuous ring maps extending embeddings $\tau:E\to\mathbb C$ with $\tau(\delta)=i\sqrt d$. Assume that the restrictions $\tau|_F$ enumerate the real places bijectively and that $\theta_\tau(a\otimes1)$ is the corresponding real place coordinate of $a\in A$, viewed in $\mathbb C$. These are the chart inputs for the host and the chosen infinite family. For $X=\operatorname{Mat}_{m,n}(T)$ put
$$
 U(x)_{\tau,ij}=\theta_\tau(p(x_{ij})),\qquad
 R(x)=\sum_{\tau,i,j}|U(x)_{\tau,ij}|.
$$
The group of square invertible matrices has its topological group topology, equivalently the topology from the pair of matrix and inverse. Use the maximum norm on $\mathbb R^k$, including the zero space for $k=0$.

**Theorem (splitting, inverse chart and uniform sizes).** Under the tensor hypotheses, $(p,q)$ is a topological ring isomorphism. Under the chart hypotheses, $(U,q)$ gives a homeomorphism on matrices, and the inverse on the zero-finite slice is additive. For every continuous additive $L:\mathbb R^k\to X$ with $qL=0$, there is $C\ge0$ with $R(Lt)\le C\|t\|_\infty$ for all $t$. If $L$ is injective, there is $D>0$ such that for every $x\in X$ and $t\in\mathbb R^k$,
$$
 \|t\|_\infty\le D\big(R(x+Lt)+R(x)\big).
$$
Fix a compact set $Q$ of right factors in $\operatorname{GL}_n(T)$. There is $H\ge1$ such that for every $g\in Q$ and $y\in X$,
$$
 H^{-1} R(y)\le R(yg)\le H R(y).
$$
Consequently the same $C,D$ and the fixed $H$ give $R((Lt)g)\le HC\|t\|_\infty$ and $\|t\|_\infty\le DH\big(R((x+Lt)g)+R(xg)\big)$ in the injective case. The pairwise version holds with $x+Lt,x$ replaced by $x+Lt,x+Ls$ on the right and $\|t-s\|_\infty$ on the left. If the base point $x$ also ranges over a fixed compact set $P$, set $M=\sup_{x\in P}R(x)$, with $M=0$ for the empty set. Then
$$
 \frac{\|t\|_\infty}{DH}-\frac{M}{H}\ \le\
 R((x+Lt)g)\ \le\ H(M+C\|t\|_\infty).
$$
In the last display $L$ is injective and the constants are chosen after fixing the compact sets and before varying $x,g,t$.

*Proof.* For the splitting, let $j_\infty:T_\infty\to T$ come from $(a,0)$ on the first tensor factor and let $j_f:T_f\to T$ come from $(0,b)$. The projection identities $p j_\infty=\mathrm{id}$, $q j_f=\mathrm{id}$, $q j_\infty=0$, $p j_f=0$ follow on pure tensors, hence on sums. On a pure tensor $(a,b)\otimes e$, the sum $j_\infty p+j_f q$ returns $(a,0)\otimes e+(0,b)\otimes e=(a,b)\otimes e$. By additivity this holds everywhere. Both projections preserve multiplication and the unit, so the inverse $j_\infty(u)+j_f(v)$ is also a ring map. For continuity, choose any $F$-basis of $E$. In basis coordinates each module topology is the ordinary finite product of copies of its base ring. Indeed the finite free module with product topology has continuous addition and scalar action, and into any topological module each linear map out of it is continuous by the finite sum of scalar multiples of fixed images of basis vectors. This is the universal property of the module topology. The projections in these coordinates are ordinary continuous projections, and the two sections are continuous zero insertions. Addition is continuous, so the displayed inverse is continuous. This is the coordinate version of the archive's continuity argument using semilinearity for the projections and equivariant additivity for the zero insertions.

To construct the inverse chart, let $\rho:\mathbb R^{\{\tau\}}\to A$ place each scalar into its indexed real completion. It is continuous and additive since it is coordinate reindexing followed by the inverse real completion identifications. If all real place coordinates of $a\in A$ vanish, then $a=0$. Define
$$
 \sigma(z)=j_\infty\left(\rho(\operatorname{Re}z)\otimes1
          +\rho(\operatorname{Im}z/\sqrt d)\otimes\delta\right).
$$
Taking real parts, taking imaginary parts, dividing by $\sqrt d$, and applying $\rho$ are continuous additive operations. The maps $a\mapsto a\otimes e$ are continuous by scalar multiplication on the fixed vector $1\otimes e$. Thus $\sigma$ is continuous additive, and $q\sigma=0$. The multiplicativity and normalization of $\theta_\tau$ give $\theta_\tau(p\sigma(z))=\operatorname{Re} z_\tau+i\sqrt d\,\operatorname{Im} z_\tau/\sqrt d=z_\tau$. Every element of $T_\infty$ is $a_0\otimes1+a_1\otimes\delta$ by expanding in the basis $1,\delta$. Its coordinate at $\tau$ is $(a_0)_\tau+i\sqrt d(a_1)_\tau$. If every coordinate vanishes then each of the two real coordinate families vanishes, and $a_0=a_1=0$. Hence $(U,q)$ determines the original matrix. Its inverse is entrywise $\sigma(u)+j_f(v)$, where $\sigma$ is applied to the family of coordinates at each entry. Both directions are continuous in the finite product topology. In particular the inverse chart is the inverse of the archimedean coordinate map restricted to the zero-finite slice.

Next let $\ell=U L$. It is continuous additive and hence real linear: the additive identities first give rational homogeneity, which extends to real scalars by continuity. With $h$ the number of complex coordinates, $\|U(y)\|_\infty\le R(y)\le h\|U(y)\|_\infty$ by the maximum and sum inequalities, also for the zero space. Thus $C=h\|\ell\|_{\mathrm{op}}$ works. When $L$ is injective, $\ell t=0$ and $q(Lt)=0$ force $Lt=0$ by the chart, then $t=0$. For $k>0$ the positive continuous function $\|\ell t\|_\infty$ on the unit sphere has a positive minimum, so its reciprocal $D$ bounds $\|t\|_\infty/\|\ell t\|_\infty$ for $t\ne0$. For $k=0$ take $D=1$. The triangle inequality and $R(-x)=R(x)$ give
$$
 \|t\|_\infty\le D R(Lt)\le D\big(R(x+Lt)+R(x)\big).
$$
This proves the translated lower bound with the same $D$ for every base point. The base term is essential because $x=-Lt$ can cancel the entire infinite part.

Finally, for each archimedean coordinate the entry-sum norm is submultiplicative: expand $(YZ)_{ij}=\sum_l Y_{il}Z_{lj}$, apply the triangle inequality, and bound the resulting sum by $(\sum_{i,l}|Y_{il}|)(\sum_{l,j}|Z_{lj}|)$. The coordinate maps are ring maps, so this bound applies to $yg$. Choose $H$ as the maximum of $1$ and the suprema of $R(g)$ and $R(g^{-1})$ over $Q$, ignoring empty suprema. They are finite by compactness and continuity of coordinates and inversion. Summing the entry bounds across places gives $R(yg)\le HR(y)$, and applying it to $(yg)g^{-1}$ gives the other inequality. Substitution proves the two translated bounds, applying the same argument at $x+Ls$ to the parameter $t-s$ proves the pairwise version, and $R(x)\le M$ gives the compact-base display. $\square$

**How the bounds enter the Schwartz and theta arguments.** [Lean, read] The audit shorthand `realParam_size_bounds` names `GlobalTheory.Unf.realParam_size_bounds`, the actual proof under `GlobalTheory.T.adelicMatrixRealSize_bounds_along_real_parametrisation`. Its upper constant comes from the operator norm of the real-linear coordinate map. Its lower constant comes from the antilipschitz estimate after the chart's extensionality field proves trivial kernel. The compact-factor estimates are a separate step. The theorem above writes a right *matrix* product $yg$. In the theta decomposition $h=ay$, the compact factor $y$ occurs on the **right of the group product** but acts by **left** inverse multiplication on the matrix: $h^{-1}\xi=y^{-1}(a^{-1}\xi)$. For left matrix multiplication the same proof compares $R(Y)$ and $R(gY)$ using the entry-sum inequality in that order and then applying $g^{-1}$.

In the forward Schwartz direction, the upper bound gives continuity of the additive coordinate map, and the lower bound at base point zero proves its injectivity. Its affine translate therefore pulls Schwartz functions back along an antilipschitz real linear part, while the finite factor is constant along the slice. In the converse, use the finite section $j_f$ to lift a coset representative and the full real chart $\sigma$ to evaluate the whole archimedean coefficient. Their sum has exactly the two prescribed projections. For the majorant, the same section lifts the compact finite support to the compact matrix box of §19.3.5.

Fix the test function and compact family first. The common finite support $K$ and its translated compact image $K'$ are then fixed, independently of the order of decay. Apply the denominator-lattice result of §19.3.4 to $K'$ and use the existing weighted count to choose a sufficient $N$. Only then use the test-function constant at $N$ and the compact-translation factor $H^N$. Indeed if $z=y^{-1}Y$ lies in the original finite box, then $Y_f=y_f z_f$ belongs to the enlarged box, and $1+R(Y)\le H(1+R(z))$. Inserting $Y=a^{-1}\xi$ yields the majorant summed by `absTheta_le_torus`. The Siegel covering and integrable torus bound give the measurable summation and integration conclusion of §19.3.5 on its stated domains. [§19.3.2](#1932-rational-reduction-and-the-covering-of-the-adelic-quotient) · [§19.3.4](#1934-from-finite-support-to-a-fixed-minkowski-lattice) · [§19.3.5](#1935-a-common-finite-support-for-schwartz-majorants) · [Gan–Qiu–Takeda, §§2.1 and 3.1](https://arxiv.org/pdf/1207.4709v3)

**Archive scope.** Archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. R3 [Lean, read] applies to the three producers and the direct chart and size bodies listed below. The compact two-sided formulation and the matrix examples are textbook deductions. The archive inputs `InfAdeleCM.hom_tmul`, `ext_eq_ofReal`, `conj_tmul_one`, `FockCompare.continuous_comp`, the Mathlib module-topology continuity lemmas, and `LinearMap.exists_antilipschitzWith` are used at their interfaces. The compact translation interfaces retain their scope in §§19.3.3–19.3.5, and the weighted count `weighted_integral_tuple_lattice_count_bound` is read in §19.3.7. The CM-type indexing of the real places is `CMTypePlaces.places_bijective`. The archive derives it in two lines from `CMTypePlaces.mk_tauE_bijective` through `IsCMField.equivInfinitePlace` (`src/Development/AbelianVarietyTheory/Proofs/HeightProofs/CmTypeRestrictRealSubfieldInfinitePlaceBijective.lean:57–60`), and the weighted count calls the same `mk_tauE_bijective`. The chart and the count therefore rest on one named input, read in §19.3.8 together with `tauE_sqrtMinusD`.

| Producer or consumer | Archive-relative source and lines |
|---|---|
| Tensor splitting | `src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsAdeleRingTensorEquivInfiniteProdFinite.lean:9–114` |
| Real chart and lift | `src/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsRealChartInfiniteAdelesCmType.lean:15–55`, `src/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIsArchimedeanAdeleChartOfRealChart.lean:13–171`, `src/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseChart.lean:15–18` |
| Real-parameter size | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AdelicMatrixRealSizeBoundsAlongRealParametrisati.lean:24–123`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AdelicMatrixRealSizeBoundsAlongRealParametrisatiStatement.lean:18–19` |
| Forward and reverse Schwartz use | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz.lean:167–203`, `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemSchwartzAOfIsSchwartzBruhat.lean:19–53,145–241` |
| Majorant and theta use | `src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatAdelicMatrixContinuousLeMajorant.lean:20–43,98–150`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdelicMatrixSchwartzMajorantInvMulLe.lean:13–37`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsThetaSumSiegelSetLeTorusPower.lean:17–64` |

### 19.3.7 Unit cells and the uniform weighted lattice count

**Motivation.** After §§19.3.3–19.3.4 the torus majorant is a weighted sum over one fixed lattice. The rational stack $T$ sends each supported matrix injectively to $n(2r+m)$ entries in $(ML)^{-1}\mathcal O_E$, and each entry carries a width $t_i$, $t_i^{-1}$ or $1$. One counting statement remains. The weighted sum over a product of copies of one integer lattice must be at most a constant times $\prod_k\max(1,s_k)^{[E:\mathbb Q]}$, with the constant independent of the widths. §19.3.3 proved an estimate of this shape by dyadic shells. The archive takes a more explicit route. It bounds the weight of a point by a product of one-dimensional weights, factors the lattice sum coordinate by coordinate, and compares each one-dimensional sum with an integral over unit cells. This subsection follows that proof and records the exponent the archive chooses. It then traces how that exponent and the constant enter the stacking threshold of §19.3.3 and the Schwartz order of §19.3.5.

**Example 1 (one dimension: on the lattice and on the half lattice).** Take $\mathbb Z\subset\mathbb R$, a width $s>0$ and the weight with exponent two. The archive uses exponent two for one block of real dimension one. For a shift $\beta$ put
$$S_\beta(s)=\sum_{z\in\mathbb Z}\Big(1+\frac{|z+\beta|}{s}\Big)^{-2}.$$
At $s=1$ the shift $\beta=0$ gives one point at the origin and two at each distance $n\ge1$. Thus $S_0(1)=1+2\sum_{n\ge1}(1+n)^{-2}=1+2(\zeta(2)-1)=\pi^2/3-1\approx2.290$. The half-lattice shift $\beta=1/2$ gives two points at each distance $k+1/2$ with $k\ge0$, so
$$S_{1/2}(1)=2\sum_{k\ge0}(k+3/2)^{-2}=2\psi'(3/2)=2(\pi^2/2-4)=\pi^2-8\approx1.870.$$
The cell bound proved below gives $1+2s=3$ for both shifts. In the archive's version the cell $[i,i+1]$ controls its right endpoint:
$$(2+i)^{-2}\le\big((1+i)(2+i)\big)^{-1}=(1+i)^{-1}-(2+i)^{-1}.$$
These differences telescope to at most $1$ on each side of the origin.

The limits in the width show which parts of the bound are forced. As $s\to0$, $S_0(s)\to1$ because the origin always contributes one. Meanwhile $S_{1/2}(s)\le s^2\sum_z(z+1/2)^{-2}=\pi^2s^2\to0$. Hence no bound of the form $Cs$ holds uniformly in the shift, and up to constants the factor must be $\max(1,s)$. As $s\to\infty$, the two-sided cell lemma gives $2s-1\le S_\beta(s)\le2s+1$ for every $\beta$. The coefficient $2=\int_{\mathbb R}(1+|x|)^{-2}\,dx$ therefore cannot be lowered. With exponent one in place of two, each $S_\beta(s)$ is infinite by comparison with the harmonic series.

Unit cells also count points: $[-H,H]$ contains at most $2H+1$ points of $\beta+\mathbb Z$. Equality holds on the lattice when $H$ is an integer and on the half lattice when $H$ is a half-integer. For instance, $H=5/2$ gives the six points $\pm1/2,\pm3/2,\pm5/2$. A denominator only changes the cell size. On $\tfrac{1}{2}\mathbb Z$ the coordinates are $2x$ and the bound becomes $1+4s$, the one-dimensional form of the $2L+1$ remark in §19.3.3. [Expository] [DLMF 25.6.1](https://dlmf.nist.gov/25.6.E1) · [DLMF 5.15.1–5.15.5](https://dlmf.nist.gov/5.15)

**Example 2 (two dimensions, unequal widths).** Two blocks of real dimension one model the two stacked rows of a hyperbolic pair, with widths $t$ and $t^{-1}$. Take $t=2$. With $|P|=2$ coordinates the archive's exponent is $N=4$, and the sum is
$$W=\sum_{(z_1,z_2)\in\mathbb Z^2}\Big(1+\frac{|z_1|}{2}+2|z_2|\Big)^{-4}.$$
Both $|z_1|/2$ and $2|z_2|$ are at most their sum, so pointwise
$$\Big(1+\frac{|z_1|}{2}+2|z_2|\Big)^{-4}\le\Big(1+\frac{|z_1|}{2}\Big)^{-2}\big(1+2|z_2|\big)^{-2}.$$
The right side is a product. Its sum over $\mathbb Z^2$ is $S_0(2)S_0(1/2)$, with
$$S_0(2)=1+8\sum_{n\ge1}(n+2)^{-2}=1+8\Big(\frac{\pi^2}{6}-\frac{5}{4}\Big)=\frac{4\pi^2}{3}-9\approx4.159\le1+2\cdot2,$$
$$S_0(1/2)=1+2\sum_{n\ge1}(2n+1)^{-2}=1+2\Big(\frac{\pi^2}{8}-1\Big)=\frac{\pi^2}{4}-1\approx1.467\le1+2\cdot\tfrac{1}{2}.$$
Thus $W\le S_0(2)S_0(1/2)\approx6.104\le5\cdot2=10$. With $C_0=L=1$ the archive's final form is $(1+2)^2\max(1,2)\max(1,\tfrac{1}{2})=18$. The line $z_2=0$ alone gives the lower bound
$$W\ge1+32\sum_{n\ge1}(n+2)^{-4}=1+32\Big(\frac{\pi^4}{90}-\frac{17}{16}\Big)=\frac{16\pi^4}{45}-33\approx1.634.$$

The separate factors matter. Using the larger width for both coordinates would give $(1+2\cdot2)^2=25$. For widths $(t,t^{-1})$ with $t\ge1$, the product bound $(1+2t)(1+2/t)\le9t$ grows linearly, while $(1+2t)^2$ grows quadratically. The contracted factor $S_0(1/2)$ exceeds $1/2$, as Example 1 predicts: a small width contributes a constant, not a small factor.

The total real dimension is $D_0=2$, and the threshold is sharp. With both widths one, the shell $\{|z_1|+|z_2|=R\}$ has exactly $4R$ points for $R\ge1$. Using $R(1+R)^{-N}=(1+R)^{1-N}-(1+R)^{-N}$,
$$\sum_{z\in\mathbb Z^2}\big(1+|z_1|+|z_2|\big)^{-N}=1+4\sum_{R\ge1}\frac{R}{(1+R)^N}=1+4\big(\zeta(N-1)-\zeta(N)\big)\qquad(N>2).$$
At $N=2$ the shell terms are $4R/(1+R)^2\ge1/R$, and the series diverges. At $N=3$ the value is $1+4(\zeta(2)-\zeta(3))\approx2.772$, and at the archive's $N=4$ it is $1+4(\zeta(3)-\zeta(4))\approx1.479$. [Expository] [DLMF 25.6.1](https://dlmf.nist.gov/25.6.E1) · [MathWorld, Apéry's constant](https://mathworld.wolfram.com/AperysConstant.html)

**Definitions.** Let $E$ be a number field of degree $d=[E:\mathbb Q]$ and $E_{\mathbb R}=E\otimes_{\mathbb Q}\mathbb R$, a real vector space of dimension $d$. Fix a $\mathbb Z$-basis $\omega_1,\dots,\omega_d$ of $\mathcal O_E$. It is also a $\mathbb Q$-basis of $E$ and an $\mathbb R$-basis of $E_{\mathbb R}$, with real-linear coordinate functions $c_1,\dots,c_d$. Let $(\tau_j)_{j\in J}$ be a finite family of field embeddings $E\to\mathbb C$, extended real-linearly to $E_{\mathbb R}$, and put $\|x\|_\tau=\sum_j|\tau_j(x)|$. The family *represents every place* if each embedding $\varphi:E\to\mathbb C$ satisfies $|\varphi(x)|=|\tau_j(x)|$ for some $j$ and all $x$, that is, $\varphi$ and $\tau_j$ define the same archimedean place. Then $\varphi=\tau_j$ or $\varphi=\overline{\tau_j}$, so the equality persists on $E_{\mathbb R}$.

For an integer $L\ge1$ the fixed lattice is $\Lambda_L=L^{-1}\mathcal O_E\subset E_{\mathbb R}$. Blocks are indexed by a finite set $\kappa$, widths are $s\in(0,\infty)^\kappa$, and for $\eta\in E_{\mathbb R}^\kappa$
$$R_s(\eta)=\sum_{k\in\kappa}\frac{\|\eta_k\|_\tau}{s_k},\qquad D_0=d\,|\kappa|,\qquad P=\kappa\times\{1,\dots,d\}.$$
This is the weight of §19.3.3 with block norms $\|\cdot\|_\tau$. Each block has real dimension $d$, $D_0$ is the total real dimension, and $|P|=D_0$.

**Lemma (coordinate domination).** If the family represents every place, there is $C_0>0$, depending only on $E$ and $\omega$, such that $\sum_l|c_l(x)|\le C_0\|x\|_\tau$ for every $x\in E_{\mathbb R}$.

*Proof.* Let $j(x)=(\varphi(x))_\varphi\in\mathbb C^{\operatorname{Hom}(E,\mathbb C)}$, with the maximum norm. The square matrix $(\varphi(\omega_l))$ has nonzero determinant, since its square is the discriminant of the basis. Hence the vectors $j(\omega_l)$ form a complex basis, with coordinate functionals $f_l$. Both $f_l\circ j$ and $c_l$ are real-linear on $E_{\mathbb R}$ and agree on the basis, so they are equal. Thus $|c_l(x)|\le\|f_l\|\,\|j(x)\|_\infty$. Every $\varphi$ has $|\varphi(x)|=|\tau_j(x)|$ for some $j$, hence $\|j(x)\|_\infty\le\|x\|_\tau$. Take $C_0=1+\sum_l\|f_l\|$. $\square$ [Milne, Propositions 2.26 and 4.26, pp. 34 and 79–80](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

For $E=\mathbb Q(i)$ with the embedding $\tau=\mathrm{id}$ and the basis $1,i$, one has $c_1=\operatorname{Re}$ and $c_2=\operatorname{Im}$, and $|\operatorname{Re}x|+|\operatorname{Im}x|\le\sqrt2|x|$ is optimal. On $\mathbb C^2$, the functionals in the proof are $(z_1+z_2)/2$ and $(z_1-z_2)/(2i)$, each of norm one, so the proof's constant is $3$. Dropping a place destroys the lemma. In the $\mathbb Q(\sqrt2,i)$ example of §19.3.4, the algebraic integers $(\sqrt2-1)^j$ tend to zero at the retained place, while their integral coordinates are not all zero.

**Lemma (unit cells on a translated line).** Let $f:\mathbb R\to[0,\infty)$ be even, nonincreasing on $[0,\infty)$ and integrable. For every $\beta\in\mathbb R$,
$$\int_{\mathbb R}f-f(0)\ \le\ \sum_{z\in\mathbb Z}f(z+\beta)\ \le\ \int_{\mathbb R}f+f(0).$$
In particular, for $b>0$ and $q>1$,
$$\sum_{z\in\mathbb Z}(1+b|z+\beta|)^{-q}\le1+\frac{2}{b(q-1)},$$
which is $1+2/b$ at $q=2$. For $0<q\le1$ the sum is infinite for every $\beta$ and $b$.

*Proof.* Replacing $\beta$ by its fractional part only reindexes the sum, so let $u=\beta\in[0,1)$. The points of $\beta+\mathbb Z$ have absolute values $u+k$ and $1-u+k$ for $k\ge0$. For $k\ge1$ the cell $[u+k-1,u+k]$ lies in $[0,\infty)$, where $f$ is nonincreasing, so $f(u+k)\le\int_{u+k-1}^{u+k}f$. Summing gives $\sum_{k\ge1}f(u+k)\le\int_u^\infty f$, and likewise $\sum_{k\ge1}f(1-u+k)\le\int_{1-u}^\infty f$. For the two points nearest the origin, $\int_0^uf\ge uf(u)$ and $\int_0^{1-u}f\ge(1-u)f(1-u)$, hence
$$f(u)+f(1-u)=uf(u)+(1-u)f(1-u)+(1-u)f(u)+uf(1-u)\le\int_0^uf+\int_0^{1-u}f+f(0).$$
Adding the three estimates and using evenness gives the upper bound. For the lower bound, $f(u+k)\ge\int_{u+k}^{u+k+1}f$ and $f(1-u+k)\ge\int_{1-u+k}^{2-u+k}f$ for $k\ge0$. The sum is therefore at least
$$\int_u^\infty f+\int_{1-u}^\infty f\ \ge\ \int_{\mathbb R}f-uf(0)-(1-u)f(0).$$
For $f(x)=(1+b|x|)^{-q}$ one has $f(0)=1$, and $\int_{\mathbb R}f=2/(b(q-1))$ when $q>1$. When $q\le1$ the integral is infinite, and the lower bound gives divergence. $\square$

The first-order Euler–Maclaurin formula gives the same comparison with an explicit remainder for smooth $f$. The cell argument needs only monotonicity. [DLMF 2.10.1](https://dlmf.nist.gov/2.10.E1)

**Theorem (uniform weighted count by unit cells).** Assume the family $(\tau_j)$ represents every place, and let $C_0$ be the constant of the coordinate lemma. Fix a finite block set $\kappa$, an integer $L\ge1$ and a real $N>D_0$. When $D_0>0$, put $q=N/D_0$. Then for all widths $s\in(0,\infty)^\kappa$ and every translation $\alpha\in E_{\mathbb R}^\kappa$,
$$\sum_{\eta\in\alpha+\Lambda_L^\kappa}\big(1+R_s(\eta)\big)^{-N}\ \le\ \prod_{k\in\kappa}\Big(1+\frac{2C_0Ls_k}{q-1}\Big)^{d}\ \le\ \Big(1+\frac{2C_0L}{q-1}\Big)^{D_0}\prod_{k\in\kappa}\max(1,s_k)^{d}.$$
For $D_0=0$ the sum consists of the single term $1$. The archive chooses $N=2D_0$, for which the constant is $(1+2C_0L)^{D_0}$. With $\alpha=0$, $N=2D_0$, the family `tauE` and Mathlib's integral basis, the theorem is exactly the archive's statement with the archive's constant.

The constants are chosen in a fixed order: first $C_0$ from $E$ and $\omega$, then $N$ from $D_0$ alone, then the constant from $C_0$, $L$, $D_0$ and $N$. None of them depends on $s$ or $\alpha$. When $D_0>0$, at the critical equality $N=D_0$ every one-dimensional factor in the proof diverges. Over the full lattice with fixed widths the sum itself also diverges, by the shell argument of §19.3.3; Example 2 shows this at $D_0=2$.

*Proof.* *Step 1 (coordinates).* For $\eta\in\alpha+\Lambda_L^\kappa$ and $p=(k,l)\in P$ put $z_p=Lc_l(\eta_k)$. If $\lambda\in\Lambda_L$, then $L\lambda\in\mathcal O_E$ has integer coordinates. Hence $z_p\in\beta_p+\mathbb Z$ with $\beta_p=Lc_l(\alpha_k)$. The map $\eta\mapsto z$ is injective because the $c_l$ are coordinates on $E_{\mathbb R}$.

*Step 2 (domination).* Put $b_k=(C_0Ls_k)^{-1}$. By the coordinate lemma, for every $l$,
$$b_k|z_{(k,l)}|=\frac{|c_l(\eta_k)|}{C_0s_k}\le\frac{\|\eta_k\|_\tau}{s_k}\le R_s(\eta).$$

*Step 3 (product weight).* Each factor $(1+b_k|z_p|)^q$ is at most $(1+R_s(\eta))^q$. Multiplying over the $|P|=D_0$ coordinates and inverting gives
$$\big(1+R_s(\eta)\big)^{-N}\le\prod_{p\in P}\big(1+b_{k(p)}|z_p|\big)^{-q}.$$

*Step 4 (enlargement and factorization).* All terms are nonnegative. By injectivity, the sum over $\eta$ is at most the sum of the product weight over the whole translated lattice $\prod_p(\beta_p+\mathbb Z)$. For a product of nonnegative functions on a finite product of countable sets, the sum is the product of the sums, by Tonelli's theorem for counting measure.

*Step 5 (unit cells).* By the cell lemma, the factor at $p=(k,l)$ is at most $1+2/(b_k(q-1))=1+2C_0Ls_k/(q-1)$, and each $k$ has $d$ such factors. Finally,
$$1+\frac{2C_0Ls_k}{q-1}\le\Big(1+\frac{2C_0L}{q-1}\Big)\max(1,s_k).$$
At $q=1$ the cell lemma makes the factors infinite. The divergence of the sum itself is the shell lower bound of §19.3.3, which is not repeated here. $\square$

**Remark (near the critical exponent).** In Example 2 with widths one, the exact sum is $1+4(\zeta(N-1)-\zeta(N))$. By the same cell comparison, $\zeta(N-1)-1$ lies between $2^{2-N}/(N-2)$ and $1/(N-2)$, so the sum grows like $4/(N-2)$ as $N\downarrow2$. Since $C_0=L=d=1$ and $q-1=(N-2)/2$, the theorem's constant is $(1+4/(N-2))^2$, which grows like the square of that rate. The product method is sharp in the threshold but not in the rate of blow-up. The archive's choice $N=2D_0$ stays far from the threshold, where the constant is simply $(1+2C_0L)^{D_0}$.

**Corollary (the stacked torus count).** Let $E$ be the CM field of §19.3.1 and $b=[F:\mathbb Q]$, so $d=2b$. In `lattice_count_diag_mul` the theorem is applied with zero translation and lattice $\Lambda_{ML}$. The block set is $(\mathrm{Fin}\,r\sqcup\mathrm{Fin}\,r\sqcup\mathrm{Fin}\,m)\times\mathrm{Fin}\,n$, that is, rows of the stack $T$ times columns. The width of a block is $t_i$, $t_i^{-1}$ or $1$ according as its row belongs to $Y'$, to $X'$ or to $P$. Hence
$$D_0=2bn(2r+m),\qquad N=2D_0=4bn(2r+m),$$
and the bound is $(1+2C_0ML)^{D_0}\prod_i\big(\max(1,t_i)\max(1,t_i^{-1})\big)^{2bn}$, since the $P$ rows contribute $1$.

For this block set, the redundant stacking threshold $N>2bn(2r+m)$ of §19.3.3 is exactly $N>D_0$. The archive's exponent is twice that threshold. The sharper threshold $N>2bmn$, from an independent basis of the complement, is not used: the archive keeps all $m$ rows of $P$. The cone conditions $t_i\ge ct_{i+1}$ and $t_r\ge c$ enter only afterwards. With $c_0=\min(c,1)^r$ they give $t_i\ge c_0$, hence $\max(1,t_i)\le c_0^{-1}t_i$ and $\max(1,t_i^{-1})\le c_0^{-1}$. The stacked constant is therefore $C_T^NC_1C'$, with
$$C_1=(1+2C_0ML)^{D_0},\qquad C'=c_0^{-4bnr}.$$
Here $C_T$ is the scaled-norm constant of §19.3.4, raised to the power $N$ because it bounds $1+R_s(T\xi)$ before the weight is raised to that power.

**Remark (order of choices and the Schwartz order).** The whole chain fixes its data in this order. First come the test function $\Phi$ and the compact family $Q$. Then come the common finite support $K$ and its enlargement $K'$ (§19.3.5). Then the denominator $L$ of $K'$ and the denominator $M$ of the stack (§19.3.4). The order $N=4bn(2r+m)$ comes next, and after it the constants $C_1$, $C_T^N$ and $C'$. Last come the Schwartz constant $C^\Phi_N$ and the compact-translation constant $C^Q_N$ at that same order.

The order $N$ depends only on $r,m,n$ and $[E:\mathbb Q]$. It does not depend on $\Phi$, $Q$, $K'$, $L$ or $M$, although it is formally chosen after $L$. Thus the all-order Schwartz bound of §19.3.5 is used at one order, fixed by the Witt frame and the column count. The test function and the compact family influence the final bound only through $L$ (in $C_1$) and through the two constants at that order. The final constant is $\max(C^\Phi_N,0)\,C^Q_N\,C_T^N\,C_1\,C'$, chosen before any of $t$, $a$, $y$.

**Remark (scale domain and translations).** The archive's count holds for all widths in $(0,\infty)^\kappa$ with no further condition. The factor $\max(1,s_k)^d$ absorbs both $s_k\to0$ and $s_k\to\infty$, as Example 1 shows in one dimension. The stacked application needs positive widths only through the cone, and the cone is used solely for the final absorption into $\prod_it_i^{2bn}$. Outside the cone the count is still valid, but $\max(1,t_i^{-1})^{2bn}$ is unbounded as $t_i\to0$. By the remark on absolute summation in §19.3.3, no bound by $\prod_it_i^{2bn}$ survives there.

The archive's declaration sums over $\Lambda_L^\kappa$ itself and has no translation parameter. In the theorem, uniformity in $\alpha$ costs nothing. Only Step 5 sees the shift, through the cell lemma, and the constant is unchanged. A fixed denominator with arbitrary cosets is therefore harmless. Refining the denominator raises the constant like $L^{D_0}$, in agreement with the $2L+1$ count of §19.3.3.

**Reading the production proof.** [Lean, read] Archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The public declaration `GlobalTheory.T.weighted_integral_tuple_lattice_count_bound` forwards to `GlobalTheory.WeightedCount.weighted_count`. Its statement quantifies over the host datum $D$, a finite type $\kappa$ and $L>0$, and asserts the existence of $N$ and $C\ge0$. For every positive width function $s$ it then bounds a sum in the extended nonnegative reals over all of $E^\kappa$. The summand is the indicator of the tuples with every $L\eta_k$ integral, times $(1+R_s(\eta))^{-N}$ with the block norm summed over the family `tauE`. The bound is $C\prod_k\max(1,s_k)^{[E:\mathbb Q]}$. The lattice is therefore $(L^{-1}\mathcal O_E)^\kappa$, the block norm is the sum over the CM-type family `tauE`, and the widths are arbitrary.

The proof proceeds in five steps.

1. `exists_repr_le` supplies $C_0=1+\sum_l\|f_l\|$, where $f_l$ are the coordinate functionals of Mathlib's `canonicalEmbedding.latticeBasis`. It bounds the maximum norm with `canonicalEmbedding.norm_le_iff` and replaces each embedding by a member of `tauE` at the same place, using the surjective half of the place identification.
2. The proof sets $\iota$ to be the basis index of $\mathcal O_E$ and $P=\kappa\times\iota$, and chooses $N=2|P|$ and $C=(1+2C_0L)^{|P|}$ before $s$.
3. It passes to the subtype of supported tuples, with $b_p=1/(C_0Ls_{p_1})$ and the integer vector $z_p=\lfloor c_{p_2}(L\eta_{p_1})\rfloor$. This vector is exact on the support by `repr_int` and `repr_nat_mul`.
4. The weight at order $2|P|$ is dominated pointwise by the product $\prod_p(1+b_p|z_p|)^{-2}$. The proof then checks injectivity, $|\iota|=[E:\mathbb Q]$ (from `RingOfIntegers.rank`), and $1+2/b_p\le(1+2C_0L)\max(1,s_{p_1})$.
5. A final chain of inequalities concludes. It compares termwise, enlarges by `ENNReal.tsum_comp_le_tsum_of_injective`, and factors by `tsum_pi_prod_ennreal`, which inducts on the finite index type through an `Option` decomposition. It then applies `tsum_int_le` to each factor. There `tail_term` is the cell inequality $(1+b(i+1))^{-2}\le b^{-1}\big((1+bi)^{-1}-(1+b(i+1))^{-1}\big)$, `tail_le` telescopes the partial sums to at most $1/b$, and `tsum_int_split` separates $0$, the positive integers and the negative integers.

| Call (actual arguments) | Archive-relative source and lines |
|---|---|
| `absTheta_le_torus`: $K$, then $K'$, then the torus sum at $K'$, then the two constants at the returned $N$ | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsThetaSumSiegelSetLeTorusPower.lean:19–27` |
| `tsum_maj_invPt_torus_le`: $L$ from $K'$, then the stacked count with $X'=X^{\dagger}J$, $Y'=Y^{\dagger}J$, $c$, $L$ | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SiegelTorusTsumMajorantTranslatedRationalPointsL.lean:15–18` |
| `lattice_count_stack`: $ST=1$, block set $\mathrm{Fin}\,r\sqcup\mathrm{Fin}\,r\sqcup\mathrm{Fin}\,m$, widths $(t,t^{-1},1)$, cone exponent $[F:\mathbb Q]\cdot2n$ | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorusInverseLatticeCountStackedEigenprojections.lean:16–24` |
| `lattice_count_diag_mul`: $M$ from $T$, then the weighted count at $(\kappa\times\mathrm{Fin}\,n,\,ML)$, then $C_T$; widths $s'(k,j)=s_k$; exponent conversion by $[E:\mathbb Q]=2[F:\mathbb Q]$ | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeCountSumBoundOfRationalDiagonalising.lean:18–21,30–33,61–70` |
| Forwarding declaration and producer `weighted_count` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedIntegralTupleLatticeCountBoundStatement.lean:11–13`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeightedIntegralTupleLatticeCountBound.lean:15–129` |
| Cells, coordinate bound, cone, exact coordinates | `src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SiegelConeIntegralMatrixLatticeCount.lean:26–101,109–131,135–168,177–190` |
| Product of sums | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumPiProdEnnreal.lean:11–39` |
| Cone absorption and its forwarding declaration | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMaxOnePowLeOnSiegelTorusCone.lean:13–51`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdMaxOnePowLeOnSiegelTorusConeStatement.lean:12–13` |

**Reading boundary.** R3 [Lean, read] covers `weighted_count` and its forwarding declaration, `exists_repr_le`, `repr_int`, `repr_nat_mul`, `tail_term`, `tail_nonneg`, `tail_le`, `tsum_int_split`, `tsum_int_le`, `tsum_pi_prod_ennreal`, `cone_pow_le` and `prod_max_le_prod`. The four consumer bodies keep their R3 reading from §§19.3.3–19.3.5; only their call lines were reread here, to fix the actual arguments.

Several inputs are read at statement level only [Lean]. The place identification `GlobalTheory.CMTypePlaces.mk_tauE_bijective` (`src/Development/AbelianVarietyTheory/Proofs/HeightProofs/CmTypeRestrictRealSubfieldInfinitePlaceBijective.lean:14–15`) is used only through its surjective half, at line 145 of the cell file; §19.3.8 reads its proof. The declaration `GlobalTheory.LevelSeries.mk_tauE_bij` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharInfinityEqCoeffMulHalfNormPow.lean:62`) is named in §19.3.4 and has the same statement, but it is not called on this path; §19.3.8 compares the two proofs. The degree identity `finrank_cmField_eq_two_mul_totallyRealSubfield` is used at its interface. So are the Mathlib inputs at the pinned commit: `canonicalEmbedding.latticeBasis`, `canonicalEmbedding.integralBasis_repr_apply`, `canonicalEmbedding.norm_le_iff`, `NumberField.integralBasis_repr_apply`, `RingOfIntegers.rank` and the extended-real summation lemmas. The definition `tauE D τ = D.host.emb (D.eTau τ).1` (`src/Formalism/LocalRingCardinality/DataTheta.lean:491`) is read here, and §19.3.8 reads the host embedding and the CM-type enumeration behind it down to the host structure fields.

The coordinate lemma, the two-sided translated cell lemma, the real-exponent theorem and the two examples are textbook exposition [Expository] in the place model. The archive proves the zero-translation case at $N=2D_0$. The dyadic proof of §19.3.3, the denominator and full-lattice lemmas of §19.3.4, the Schwartz majorant of §19.3.5 and the adelic coordinates of §19.3.6 are cited, not repeated.

### 19.3.8 CM types and the place identification

**Motivation.** Two of the preceding subsections index archimedean coordinates by one finite set. In §19.3.7 the block norm $\|x\|_\tau=\sum_\tau|\tau(x)|$ runs over the family `tauE`, and the coordinate lemma needs this family to represent every archimedean place of $E$. In §19.3.6 the real chart reads one real part and one imaginary part for each member of the family and puts them at the real places of $F$. The chart therefore needs every real place of $F$ to occur exactly once, and every member to send the chosen square root of $-d$ to the same root $i\sqrt d$. In the archive both requirements come from one theorem, `GlobalTheory.CMTypePlaces.mk_tauE_bijective`. It says that sending a member of `tauE` to the infinite place it defines is a bijection. This subsection reads that proof and its direct producers.

The arithmetic is classical. The complex embeddings of a number field come in conjugate pairs, each pair is one complex place, and a CM type picks one member of each pair. The bookkeeping matters for the lattice count. A block contributes $[E:\mathbb Q]$ real dimensions, two for each complex place, and this number is the critical exponent of §§19.3.3 and 19.3.7. Treating both members of a pair as separate complex places would double it.

**Example 1 ($\mathbb Q(i)$).** Take $E=\mathbb Q(i)$, $F=\mathbb Q$, $\delta=i$ and $d=1$, so that $\delta^2=-d$. There are two embeddings, $\iota(i)=i$ and $\bar\iota(i)=-i$, and they form one conjugate pair. Both define the absolute value $x\mapsto|x|$, so $E$ has a single infinite place $w$, and it is complex. The rule "send $\delta$ to $i\sqrt d$" selects $\Phi=\{\iota\}$. The other root $\delta'=-i$ also satisfies $\delta'^2=-1$ and selects $\{\bar\iota\}$. Restricting $w$ to $\mathbb Q$ gives the real place of $\mathbb Q$. The place coordinate is $z=\iota(x)$. On $E_{\mathbb R}=E\otimes_{\mathbb Q}\mathbb R\cong\mathbb C$ the element $a+bi$ has real coordinates $(\operatorname{Re}z,\operatorname{Im}z)=(a,b)$, and the chart of §19.3.6 is $z\mapsto\operatorname{Re}z\otimes1+\operatorname{Im}z\otimes i$. The real dimension is $2=[E:\mathbb Q]$.

Recording both embeddings instead gives the vector $(z,\bar z)\in\mathbb C^2$, in a space of real dimension four. The image of $\mathbb Z[i]$ spans only the real plane $\{(z,\bar z)\}$, and the counting exponent stays two. Put $S_N=\sum_{x\in\mathbb Z[i]}(1+|x|)^{-N}$, the weighted sum of §19.3.7 for one block of width one, and write $x=a+bi$. One has $\max(|a|,|b|)\le|x|\le|a|+|b|$. For $R\ge1$ exactly $4R$ points of $\mathbb Z^2$ have $|a|+|b|=R$, and exactly $8R$ have $\max(|a|,|b|)=R$. With $R(1+R)^{-N}=(1+R)^{1-N}-(1+R)^{-N}$ this gives, for $N>2$,
$$1+4\big(\zeta(N-1)-\zeta(N)\big)\ \le\ S_N\ \le\ 1+8\big(\zeta(N-1)-\zeta(N)\big).$$
The lower bound is the exact $\ell^1$ sum of Example 2 in §19.3.7. At $N=2$ its shells contribute $4R/(1+R)^2\ge1/R$, so $S_2=\infty$. Thus $S_N$ is finite exactly for $N>2$. At $N=3$ the two bounds are approximately $2.772$ and $4.543$. At the archive's exponent for one block, $N=2D_0=4$, they are approximately $1.479$ and $1.958$. Direct summation gives $S_3\approx3.67$ and $S_4\approx1.686$. A count with two independent complex places would predict the threshold $N>4$ and declare $N=4$ critical. [Expository] [DLMF 25.6.1](https://dlmf.nist.gov/25.6.E1) · [MathWorld, Apéry's constant](https://mathworld.wolfram.com/AperysConstant.html)

**Example 2 ($\mathbb Q(\zeta_8)=\mathbb Q(\sqrt2,i)$).** Let $\zeta=e^{2\pi i/8}$. Then $i=\zeta^2$, $\sqrt2=\zeta+\zeta^{-1}$, and $\sqrt{-2}:=\zeta+\zeta^3$ satisfies $(\sqrt{-2})^2=-2$. The four embeddings are $\sigma_k(\zeta)=\zeta^k$ for $k=1,3,5,7$, with the following values.

| $k$ | $\sigma_k(\sqrt2)$ | $\sigma_k(i)$ | $\sigma_k(\sqrt{-2})$ | conjugate embedding |
|---|---|---|---|---|
| $1$ | $\sqrt2$ | $i$ | $i\sqrt2$ | $\sigma_7$ |
| $3$ | $-\sqrt2$ | $-i$ | $i\sqrt2$ | $\sigma_5$ |
| $5$ | $-\sqrt2$ | $i$ | $-i\sqrt2$ | $\sigma_3$ |
| $7$ | $\sqrt2$ | $-i$ | $-i\sqrt2$ | $\sigma_1$ |

Since $\bar\sigma_k=\sigma_{-k}$, the conjugate pairs are $\{\sigma_1,\sigma_7\}$ and $\{\sigma_3,\sigma_5\}$. They define the two complex places $w_+$ and $w_-$ of $E$, which restrict to the two real places $v_\pm(\sqrt2)=\pm\sqrt2$ of $F=\mathbb Q(\sqrt2)$. The root $\delta=i$, with $d=1$, selects $\Phi_i=\{\sigma_1,\sigma_5\}$. The root $\delta=\sqrt{-2}$, with $d=2$, selects $\Phi_{\sqrt{-2}}=\{\sigma_1,\sigma_3\}$. Each chooses one member of each pair, so each maps bijectively onto $\{w_+,w_-\}$; at $w_-$ the two choices differ by complex conjugation. These two CM types and their conjugates are all four ways of choosing one member per pair.

For $x=a+b\sqrt2+(c+e\sqrt2)i$ with real $a,b,c,e$, the coordinates of $\Phi_i$ are
$$z_+=\sigma_1(x)=(a+b\sqrt2)+i(c+e\sqrt2),\qquad z_-=\sigma_5(x)=(a-b\sqrt2)+i(c-e\sqrt2).$$
In the notation of §19.3.6, $x=a_0+a_1\delta$ with $a_0=a+b\sqrt2$ and $a_1=c+e\sqrt2$ in $F_{\mathbb R}$, and $z_\pm=(a_0)_{v_\pm}+i(a_1)_{v_\pm}$. The real-linear map $(a,b,c,e)\mapsto(\operatorname{Re}z_+,\operatorname{Im}z_+,\operatorname{Re}z_-,\operatorname{Im}z_-)$ has determinant of absolute value $(2\sqrt2)^2=8$, so $E_{\mathbb R}\cong\mathbb C^{\Phi_i}$ has real dimension $4=[E:\mathbb Q]$. With $\delta=\sqrt{-2}$ the chart writes $x=a_0+a_1'\sqrt{-2}$ with $a_1'=e+\tfrac c2\sqrt2$. At $v_-$ it reads $(a_0)_{v_-}+i\sqrt2\,(a_1')_{v_-}=(a-b\sqrt2)-i(c-e\sqrt2)=\sigma_3(x)=\overline{z_-}$. The moduli, and hence the weights, agree, but the imaginary parts read at $w_-$ have opposite signs. Using the chart of $\Phi_i$ for one factor and the chart of $\Phi_{\sqrt{-2}}$ for another is therefore an instance of the separately chosen identifications that §19.3.6 shows to break the algebraic identities over $\mathbb Q(i)$.

All four embeddings together send $E_{\mathbb R}$ onto the real subspace $\{(z_1,z_3,z_5,z_7):z_7=\bar z_1,\ z_5=\bar z_3\}$ of $\mathbb C^4$. It has real dimension four, not eight. One block therefore has $D_0=4$, and the lattice sums of §19.3.7 over $\mathbb Z[\zeta]$ converge exactly for $N>4$; four independent complex places would give $8$. Dropping a pair is fatal. §19.3.4 kept only $\sigma_1$ and found integers $(\sqrt2-1)^j$ that tend to zero at $w_+$, while $|\sigma_3((\sqrt2-1)^j)|=(\sqrt2+1)^j$. A family that represents $w_+$ twice, such as $(\sigma_1,\sigma_7,\sigma_5)$, still dominates every embedding. It breaks the norm formula, however: $|\sigma_1(x)\sigma_7(x)\sigma_5(x)|^2=|N_{E/\mathbb Q}(x)|\,|\sigma_1(x)|^2$. [Expository]

**Definitions.** In this subsection $d$ is the positive rational of §19.3.6, and the degree, written $d$ in §19.3.7, is written $[E:\mathbb Q]$. Let $E$ be a number field and let $c$ be complex conjugation. For an embedding $\psi:E\to\mathbb C$ write $\bar\psi=c\circ\psi$ and $w_\psi(x)=|\psi(x)|$. The set $V_\infty(E)$ of infinite places consists of the absolute values $w_\psi$. Each $\psi$ extends uniquely to a real-linear ring map $E_{\mathbb R}\to\mathbb C$, still written $\psi$, and $\bar\psi$ extends to $c\circ\psi$. Hence $\|x\|_w=|\psi(x)|$, for $x\in E_{\mathbb R}$ and any $\psi$ with $w_\psi=w$, does not depend on the choice of $\psi$. A *CM type* is a subset $\Phi\subset\operatorname{Hom}(E,\mathbb C)$ with $\operatorname{Hom}(E,\mathbb C)=\Phi\sqcup\bar\Phi$. For $\delta\in E$ with $\delta^2=-d$ and rational $d>0$ put
$$\Phi_\delta=\{\psi\in\operatorname{Hom}(E,\mathbb C):\psi(\delta)=i\sqrt d\}.$$
This is the archive's `HostRaw.cmType`, with $\delta$ the field `sqd`. In the archive $d$ is a prime with $d\equiv7\pmod{16}$ (`HostHyp`); only $d>0$ is used below. For a finite set $\mathcal T$ and a map $t\mapsto\tau_t$ into $\operatorname{Hom}(E,\mathbb C)$ put
$$\mathbf z_{\mathcal T}(x)=(\tau_t(x))_{t\in\mathcal T}\in\mathbb C^{\mathcal T},\qquad \|x\|_{\mathcal T}=\sum_{t\in\mathcal T}|\tau_t(x)|\qquad(x\in E_{\mathbb R}).$$
The canonical embedding $j(x)=(\psi(x))_{\psi}\in\mathbb C^{\operatorname{Hom}(E,\mathbb C)}$ carries the maximum norm, as in Mathlib's `canonicalEmbedding`. [Milne, *Complex Multiplication*, Definition 1.8, p. 11](https://www.jmilne.org/math/CourseNotes/CM.pdf)

The archive's host data enter as hypotheses [Lean]:

- (H1) $E$ is Galois over $\mathbb Q$ (the field `galois`), and $g\mapsto\sigma_g$ is a group isomorphism from a finite group $G$ onto $\operatorname{Aut}(E/\mathbb Q)$. It is `sigmaOf`, the inverse of the field `gal`, and $G$ is the group `GG`.
- (H2) $\delta^2=-d$ and $d>0$. These are `sqd_sq` and the inequality $4tr+1<d$ in `qd_big`.
- (H3) A homomorphism $\chi:G\to\{\pm1\}$ satisfies $\sigma_g(\delta)=\chi(g)\delta$. This is `gal_sqd`, with $\chi$ the sign `chD`.
- (H4) An embedding $\varphi_0$ satisfies $\varphi_0(\delta)=i\sqrt d$. This is `φ₀_mem`.
- (H5) $\Psi=\ker\chi$, which is `Frame.Psi`, and $e:\mathcal T\to\Psi$ is an equivalence, the field `eTau`.

The archive then defines $\operatorname{emb}(g)=\varphi_0\circ\sigma_g$ (`Host.emb`) and $\tau_t=\operatorname{emb}(e(t))$ (`tauE`).

**Lemma (conjugate pairing).** Let $\delta\in E$ satisfy $\delta^2=-d$ with $d>0$. For every embedding $\psi$ one has $\psi(\delta)\in\{i\sqrt d,-i\sqrt d\}$ and $\bar\psi(\delta)=-\psi(\delta)$. Hence $\psi\ne\bar\psi$, exactly one of $\psi,\bar\psi$ lies in $\Phi_\delta$, and $\Phi_\delta$ is a CM type with $|\Phi_\delta|=[E:\mathbb Q]/2$. In particular $E$ has no real embedding.

*Proof.* We have $\psi(\delta)^2=\psi(\delta^2)=-d$. The only complex numbers with square $-d$ are $\pm i\sqrt d$, since $z^2+d=(z-i\sqrt d)(z+i\sqrt d)$. Complex conjugation fixes $\sqrt d$ and sends $i$ to $-i$, so $\bar\psi(\delta)=\overline{\psi(\delta)}=-\psi(\delta)$. As $\sqrt d\ne0$, the two values differ. So $\psi\ne\bar\psi$, and exactly one of them sends $\delta$ to $i\sqrt d$. The involution $\psi\mapsto\bar\psi$ has no fixed point and exchanges $\Phi_\delta$ with its complement. This gives the disjoint decomposition and $|\Phi_\delta|=|\operatorname{Hom}(E,\mathbb C)|/2=[E:\mathbb Q]/2$. A real embedding would satisfy $\psi=\bar\psi$. $\square$

**Lemma (place identification for a CM type).** Let $\Phi$ be a CM type of $E$. Then $\pi:\Phi\to V_\infty(E)$, $\psi\mapsto w_\psi$, is a bijection. Its inverse $\nu$ sends a place $w$ to the unique member of $\Phi$ among the embeddings that define $w$. Explicitly, if $\varphi$ is any embedding with $w_\varphi=w$, then $\nu(w)=\varphi$ when $\varphi\in\Phi$ and $\nu(w)=\bar\varphi$ otherwise.

*Proof.* We use the classical fact that $w_\varphi=w_\psi$ holds exactly when $\psi\in\{\varphi,\bar\varphi\}$; in Mathlib this is `InfinitePlace.mk_eq_iff`. The direction "if" is $|\bar z|=|z|$.

*Well defined.* For any one embedding $\varphi$ defining $w$, the embeddings defining $w$ form the set $\{\varphi,\bar\varphi\}$. A CM type contains exactly one element of each conjugate pair, so this set meets $\Phi$ in one element. The displayed rule picks that element, whichever defining embedding we start from.

*Injective.* If $w_\psi=w_{\psi'}$ with $\psi,\psi'\in\Phi$, then $\psi'\in\{\psi,\bar\psi\}$. Since $\bar\psi\notin\Phi$, we get $\psi'=\psi$.

*Surjective.* Every place is $w_\varphi$ for some $\varphi$. One of $\varphi,\bar\varphi$ lies in $\Phi$, and both define $w_\varphi$.

The two constructions are mutually inverse: $w_{\nu(w)}=w$ because $\nu(w)$ defines $w$, and $\nu(w_\psi)=\psi$ for $\psi\in\Phi$ by uniqueness. $\square$ [Sutherland, Lecture 13, Corollary 13.7 and Definition 13.8, p. 3](https://math.mit.edu/classes/18.785/2021fa/LectureNotes13.pdf)

When $E$ contains an element $\delta$ as in the pairing lemma, every place of $E$ is therefore complex and $|V_\infty(E)|=[E:\mathbb Q]/2$. The place $w$ comes with the complex coordinate $x\mapsto\nu(w)(x)$. Mathlib's `InfinitePlace.embedding w` is an arbitrary choice of defining embedding, so it equals $\nu(w)$ or $\overline{\nu(w)}$. The archive's proof below tests which case occurs.

**Lemma (the archive's enumeration of $\Phi_\delta$).** Assume (H1)–(H5). Then $g\mapsto\operatorname{emb}(g)$ is a bijection $G\to\operatorname{Hom}(E,\mathbb C)$, and $\operatorname{emb}(g)\in\Phi_\delta$ if and only if $g\in\Psi$. Consequently $t\mapsto\tau_t$ is a bijection $\mathcal T\to\Phi_\delta$.

*Proof.* If $\varphi_0\circ\sigma=\varphi_0\circ\sigma'$, then $\sigma=\sigma'$, because $\varphi_0$ is injective. A Galois extension has $|\operatorname{Aut}(E/\mathbb Q)|=[E:\mathbb Q]=|\operatorname{Hom}(E,\mathbb C)|$. So $\sigma\mapsto\varphi_0\circ\sigma$ is bijective, and so is its composite with $g\mapsto\sigma_g$. Next, $\operatorname{emb}(g)(\delta)=\varphi_0(\chi(g)\delta)=\chi(g)\,i\sqrt d$. Since $i\sqrt d\ne-i\sqrt d$, this equals $i\sqrt d$ exactly when $\chi(g)=1$, that is, when $g\in\Psi$. Hence $\operatorname{emb}$ restricts to a bijection $\Psi\to\Phi_\delta$, and composing with $e$ proves the last claim. $\square$

Under $g\mapsto\sigma_g$ the subgroup $\Psi$ is $\operatorname{Gal}(E/K)$ for the imaginary quadratic field $K=\mathbb Q(\delta)$, the archive's `HostRaw.K`, because $\sigma_g$ fixes $\delta$ exactly when $\chi(g)=1$. Hence $\Phi_\delta=\{\psi:\psi|_K=\varphi_0|_K\}$. The archive's CM type is the extension to $E$ of the CM type $\{\varphi_0|_K\}$ of $K$, in Milne's construction $\Phi=\{\varphi:\varphi|_{E_0}\in\Phi_0\}$. When $E\ne K$, the proper CM subfield $K$ witnesses that $(E,\Phi_\delta)$ is not primitive in Milne's sense. The archive's hosts have $[E:\mathbb Q]=4\,\mathrm{ord}\ge4$, by the `HostDer` field `finrank_E`, so this is always the case. Milne's Exercise 1.11, which he attributes to Shimura and Taniyama, uses the same selection $\operatorname{Im}\varphi(\alpha)>0$ for $E=F[\alpha]$ with $\alpha^2\in F$ totally negative. For $\alpha=\delta$ its primitivity condition (a), $F[\alpha]=\mathbb Q[\alpha]$, says $E=K$. [Paper] [Milne, *Complex Multiplication*, pp. 11–12](https://www.jmilne.org/math/CourseNotes/CM.pdf)

**Theorem (CM-type place identification).** Assume (H1)–(H5).

1. The map $t\mapsto w_{\tau_t}$ is a bijection $\mathcal T\to V_\infty(E)$. This is `mk_tauE_bijective`.
2. Assume moreover that $E$ is a CM field with maximal totally real subfield $F$. Then restriction $w\mapsto w|_F$ is a bijection $V_\infty(E)\to V_\infty(F)$. The map $t\mapsto v_t:=w_{\tau_t|_F}=w_{\tau_t}|_F$ is a bijection $\mathcal T\to V_\infty(F)$. This is `places_bijective`.
3. The coordinate map $\mathbf z_{\mathcal T}:E_{\mathbb R}\to\mathbb C^{\mathcal T}$ is a real-linear isomorphism, and $|\mathbf z_{\mathcal T}(x)_t|=\|x\|_{w_{\tau_t}}$. Equivalently, $x\mapsto(\nu(w)(x))_{w\in V_\infty(E)}$ identifies $E_{\mathbb R}$ with a product of one complex factor per place. Consequently $[E:\mathbb Q]=2|\mathcal T|$, and for every $x\in E_{\mathbb R}$
$$\|j(x)\|_\infty\ \le\ \|x\|_{\mathcal T}\ \le\ |\mathcal T|\,\|j(x)\|_\infty .$$
The first inequality uses only the surjectivity in (1).
4. Under (2), $E=F\oplus F\delta$ and $E_{\mathbb R}=F_{\mathbb R}\oplus F_{\mathbb R}\delta$. For $a_0,a_1\in F_{\mathbb R}$,
$$\tau_t(a_0+a_1\delta)=(a_0)_{v_t}+i\sqrt d\,(a_1)_{v_t},$$
where $a_v$ denotes the real coordinate of $a$ at $v$. Let $\rho:\mathbb R^{\mathcal T}\to F_{\mathbb R}$ put $y_t$ at the place $v_t$. Then $\sigma(z)=\rho(\operatorname{Re}z)+\rho(\operatorname{Im}z/\sqrt d)\,\delta$ is the inverse of $\mathbf z_{\mathcal T}$. At one matrix entry, with zero finite component, this is the inverse chart of §19.3.6.
5. For blocks indexed by $\kappa$ and widths $s\in(0,\infty)^\kappa$, the weight of §19.3.7 is
$$R_s(\eta)=\sum_{k\in\kappa}\frac{\|\eta_k\|_{\mathcal T}}{s_k}=\sum_{k\in\kappa}\ \sum_{w\in V_\infty(E)}\frac{\|\eta_k\|_w}{s_k},$$
with each complex place counted once. The total real dimension of $E_{\mathbb R}^\kappa$ is $D_0=[E:\mathbb Q]\,|\kappa|=2|\mathcal T|\,|\kappa|$.

*Proof.* (1) By the pairing lemma, $\Phi_\delta$ is a CM type. Compose the bijection $\mathcal T\to\Phi_\delta$ of the enumeration lemma with the bijection $\pi$ of the place lemma.

(2) For $w=w_\psi$ the restriction is $w|_F=w_{\psi|_F}$, so $w_{\tau_t}|_F=w_{\tau_t|_F}$. The field $F$ is totally real, so its places correspond one-to-one to its $[F:\mathbb Q]=[E:\mathbb Q]/2$ embeddings. By (1) and the pairing lemma, $|V_\infty(E)|=|\mathcal T|=[E:\mathbb Q]/2$ as well. Every embedding of $F$ extends to $E$, because $E/F$ is finite and separable and $\mathbb C$ is algebraically closed. So restriction is surjective, and a surjection between finite sets of equal size is bijective. Compose with (1).

(3) The map is real-linear. Suppose $\mathbf z_{\mathcal T}(x)=0$. Then also $\bar\tau_t(x)=\overline{\tau_t(x)}=0$ for every $t$. By the two lemmas, $\{\tau_t\}\cup\{\bar\tau_t\}=\Phi_\delta\sqcup\bar\Phi_\delta$ is all of $\operatorname{Hom}(E,\mathbb C)$, so $j(x)=0$. The map $j$ is injective on $E_{\mathbb R}$. Indeed, for a $\mathbb Q$-basis $(\omega_l)$ of $E$ the square matrix $(\psi(\omega_l))$ has squared determinant equal to the discriminant of the basis, so it is invertible. Hence the vectors $j(\omega_l)$ are linearly independent over $\mathbb C$, and a fortiori over $\mathbb R$. So $x=0$. Both sides have real dimension $[E:\mathbb Q]=2|\mathcal T|$, hence $\mathbf z_{\mathcal T}$ is an isomorphism. The identity $|\mathbf z_{\mathcal T}(x)_t|=\|x\|_{w_{\tau_t}}$ is the definition of $\|\cdot\|_w$, and the reformulation through $\nu$ reindexes the coordinates along (1).

For the inequalities let $\psi$ be any embedding. By the surjectivity in (1) there is $t$ with $w_{\tau_t}=w_\psi$. Then $\psi\in\{\tau_t,\bar\tau_t\}$, so $|\psi(x)|=|\tau_t(x)|\le\|x\|_{\mathcal T}$; now maximize over $\psi$. The second inequality holds termwise.

(4) If $\delta$ lay in $F$, then $\psi(\delta)$ would be real for every embedding, since $F$ is totally real. This contradicts the pairing lemma. As $[E:F]=2$, the elements $1,\delta$ form an $F$-basis of $E$, and tensoring with $\mathbb R$ over $\mathbb Q$ gives the decomposition of $E_{\mathbb R}$. The restriction of $\tau_t$ to $F$ is the real embedding defining $v_t$. Its real-linear extension to $F_{\mathbb R}\cong\mathbb R^{V_\infty(F)}$ reads the coordinate at $v_t$. Multiplicativity and $\tau_t(\delta)=i\sqrt d$ give the displayed formula. The map $\rho$ is well defined and bijective because $t\mapsto v_t$ is a bijection, by (2). Then $\tau_t(\sigma(z))=\operatorname{Re}z_t+i\sqrt d\cdot\operatorname{Im}z_t/\sqrt d=z_t$. So $\sigma$ is a right inverse of the isomorphism $\mathbf z_{\mathcal T}$, hence its inverse.

(5) Reindex the inner sum along the bijection (1) and use (3). The dimension count is (3) applied blockwise. $\square$

Item (3) is Milne's isomorphism $E\otimes_{\mathbb Q}\mathbb R\to\prod_{\rho:F\to\mathbb R}\mathbb C$ for the CM type $\Phi_\delta$, and the conjugation constraint in its proof is Sutherland's description of $K_{\mathbb R}$ inside $K_{\mathbb C}$. [Milne, *Complex Multiplication*, (3), p. 11](https://www.jmilne.org/math/CourseNotes/CM.pdf) · [Sutherland, Lecture 14, pp. 3–4](https://math.mit.edu/classes/18.785/2021fa/LectureNotes14.pdf)

In the place model, (1) and (2) are the archive's `mk_tauE_bijective` and `places_bijective`. Items (3)–(5) are the uses made of them in §§19.3.6–19.3.7. The chart of §19.3.6 has three hypotheses. The enumeration lemma gives the value $\tau(\delta)=i\sqrt d$, which the archive proves separately as `tauE_sqrtMinusD`. Item (2) gives the bijective enumeration of the real places of $F$. The third hypothesis, that $\theta_\tau(a\otimes1)$ is the real coordinate of $a$, comes from `IsInfFam` through `hom_tmul` and `ext_eq_ofReal` and stays at its interface. In the archive's proof of (1) the link between $\Psi$ and $\delta$, which (H3) and (H5) provide here, enters only through the structure field `der.cmType.2.2`, applied by `factEmb` to $\varphi_0$. The archive's lemmas `galE_mem_Psi_iff` and `tauE_sqrtMinusD` derive the same link from `gal_sqd`, as in the enumeration proof above. [Lean, read] for (1)–(2) at the cited bodies; the rest of the theorem is textbook exposition [Expository] in the place model.

**Corollary (the step of §19.3.7 that consumes the identification).** In `exists_repr_le` the archive fixes $y\in E$ and an arbitrary embedding $\varphi$. It applies the surjective half of (1) to the place $w_\varphi$ and obtains $t$ with $w_{\tau_t}=w_\varphi$, hence $|\varphi(y)|=|\tau_t(y)|\le\|y\|_{\mathcal T}$. Through `canonicalEmbedding.norm_le_iff` this is the first inequality of (3) on $E$. The coordinate functionals $f_l$ of the lattice basis then give $\sum_l|c_l(y)|\le C_0\|y\|_{\mathcal T}$ with $C_0=1+\sum_l\|f_l\|$. This is the coordinate-domination lemma of §19.3.7, and through it the unit-cell count and the stacked torus bound of §19.3.3. Injectivity is never used there. A family that represented some place twice would only enlarge the block norm, and the domination and the count would remain valid. [Lean, read]

**Remark (counting every embedding as a complex place doubles the exponent).** Mathlib's canonical embedding lands in $\mathbb C^{\operatorname{Hom}(E,\mathbb C)}$, a space of real dimension $2[E:\mathbb Q]$, and `latticeBasis` is a complex basis of that space. The lattice $\mathcal O_E$ has rank $[E:\mathbb Q]$, however. Its image lies in the real subspace $\{z:z_{\bar\psi}=\overline{z_\psi}\ \text{for all}\ \psi\}$, of real dimension $[E:\mathbb Q]$; this is Mathlib's `canonicalEmbedding.conj_apply`. If each embedding were counted as an independent complex place, a block would be assigned real dimension $2[E:\mathbb Q]$. In the theorem of §19.3.7 this replaces $D_0=[E:\mathbb Q]|\kappa|$ by $2D_0$, the threshold $N>D_0$ by $N>2D_0$, and the width factor $\max(1,s_k)^{[E:\mathbb Q]}$ by its square. In the stacked count, $D_0=2bn(2r+m)$ would become $4bn(2r+m)$. The archive's exponent $N=2D_0=4bn(2r+m)$ would then sit exactly at the new threshold, where the product bound is infinite.

The torus power would become $\prod_it_i^{4bn}$, while the modulus $\delta(u)=\prod_iu_i^{2b(m-2i-1)}$ of §19.3.1 belongs to the group and would not change. The prefix sums of the cone exponents would become $2bj(2n-m+j)$, so the cone estimate would need $2n+r<m$ in place of $n+r<m$. In the opening example of §19.3, with $m=6$ and $r=2$, this would leave only $n=1$, whereas the archive's guard admits $n=1,2,3$.

The archive avoids the doubling by construction. The exponent is $2|P|$ with $|P|=|\kappa|\cdot|\iota|$, and $|\iota|=[E:\mathbb Q]$ is the rank of $\mathcal O_E$ (`RingOfIntegers.rank`). The place identification enters only through the norm inequality in (3), where a doubled family would change constants and nothing else. [Expository]

**Remark (which half each consumer uses).** The three consumers read in this chapter use the identification differently.

| Consumer | Declaration it calls | Half used | Reason |
|---|---|---|---|
| `exists_repr_le` (§19.3.7) | `CMTypePlaces.mk_tauE_bijective` | surjective | every embedding is dominated at its own place |
| `exists_real_chart_general`, through `exists_inverse_chart` (§19.3.6) | `CMTypePlaces.places_bijective` | both | `Equiv.ofBijective` puts one coordinate at each real place of $F$; surjectivity gives the zero kernel |
| `inf_eq_mul_normPow` (Hecke character at infinity) | `LevelSeries.mk_tauE_bij` | both | the norm formula $\prod_t\lvert\tau_t(a)\rvert^2=\lvert N_{E/\mathbb Q}(a)\rvert$ needs each complex place exactly once |

The pinned tarball has further call sites, which we did not read. Outside its own file `mk_tauE_bijective` is called on 11 lines in 9 files, one of them line 145 of the cell file. `places_bijective` is called on 37 lines in 30 files besides its forwarding declaration, and `LevelSeries.mk_tauE_bij` on 4 lines in 3 files. [Lean, read] for the three rows; the counts come from a text scan.

**Remark (two proofs of one statement).** `GlobalTheory.LevelSeries.mk_tauE_bij` has the same statement as `mk_tauE_bijective` but a separate proof, and the path of §19.3.7 does not call it. Its injectivity uses `conjugate_tauE_ne_tauE`, which compares imaginary parts at `sqrtMinusD` through `tauE_sqrtMinusD` and takes $d>0$ from the primality of $d$ in `HostHyp` rather than from `qd_big`. Its surjectivity `CharInfPlace.exists_mk_tauE` works in the group. If $g\notin\Psi$, then $gc\in\Psi$ for the conjugation element $c$ (`Frame.cc`), and `conjugate_emb` identifies $\overline{\operatorname{emb}(g)}$ with $\operatorname{emb}(gc)$. The version in `CMTypePlaces` squares the value at $\delta$ instead. Both start from `factEmb`. [Lean, read]

**Reading the production proof.** [Lean, read] Archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The theorem `GlobalTheory.CMTypePlaces.mk_tauE_bijective` takes `factEmb D.R D.host` apart into the bijectivity `hb` of `D.host.emb` and the membership equivalence `hm`. It then records `sqd_sq`, the inequality $0\le d$, and the identity `hmem` that every `tauE D τ` sends `sqd` to $i\sqrt d$, obtained from `hm` and the membership proof carried by `D.eTau τ`. Positivity $0<d$ comes from `qd_big`, hence $\sqrt d\ne0$, and `hconj` computes $\overline{i\sqrt d}=-i\sqrt d$. The auxiliary statement `hsurj` says that an embedding sending `sqd` to $i\sqrt d$ is some `tauE D τ`. Its proof writes the embedding as `emb g` by `hb.2`, deduces $g\in\Psi$ by `hm`, and takes the preimage under `eTau`.

For injectivity, `InfinitePlace.mk_eq_iff` gives equality or conjugacy of the two embeddings. Equality returns $\tau=\tau'$ through `hb.1` and the injectivity of `eTau`. Conjugacy, evaluated at `sqd`, gives $-i\sqrt d=i\sqrt d$; `linear_combination` turns this into $i\sqrt d=0$, contradicting $i\ne0$ and $\sqrt d\ne0$. For surjectivity, the proof squares `w.embedding sqd` using `map_pow`, `sqd_sq`, $i^2=-1$ and `Real.sq_sqrt`, and splits by `sq_eq_sq_iff_eq_or_eq_neg`. The sign $+$ gives `tauE D τ = w.embedding` and closes with `mk_embedding`. The sign $-$ applies `hsurj` to the conjugate embedding and closes with `mk_conjugate_eq`.

`places_bijective` installs the instance `isCMField_hostE` and composes Mathlib's `IsCMField.equivInfinitePlace`, the restriction of places to the maximal real subfield, with `mk_tauE_bijective`. The composite agrees with the stated function by unfolding the restriction. Mathlib builds `equivInfinitePlace` by `Equiv.ofBijective` from `comap_surjective` and the equality of place counts, which is the argument of (2). `factEmb` obtains bijectivity from `HostRaw.hostEmb`, which proves injectivity from that of $\varphi_0$ and equal cardinalities from `IsGalois.card_aut_eq_finrank` and `NumberField.Embeddings.card`. It composes with the bijective `gal.symm`. Membership is `der.cmType.2.2` applied to $\varphi_0$, `φ₀_mem` and `sigmaOf g`, rewritten by `gal (sigmaOf g) = g`.

| Role | Archive-relative source and lines |
|---|---|
| Place identification and its restriction to $F$ | `src/Development/AbelianVarietyTheory/Proofs/HeightProofs/CmTypeRestrictRealSubfieldInfinitePlaceBijective.lean:14–55,57–60` |
| Public forwarding declaration of the restricted form | `src/Development/AbelianVarietyTheory/Proofs/HeightProofs/CmTypeRestrictRealSubfieldInfinitePlaceBijectiveStatement.lean:9–10` |
| Enumeration of embeddings and the host fields it uses | `src/Formalism/LocalRingCardinality/RankBoundMonotoneInDimension.lean:516–522`, `src/Formalism/LocalRingCardinality/DataHost.lean:39,54,61–62,117–122,147,186–187`, `src/Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:76–89` |
| Raw host, derived properties and the sign test | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:12–31,58–66,87–96,172–182,198,202–224`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean:240,254–266`, `src/Formalism/FrobeniusOrbits/Statement.lean:13–14` |
| Sign character, conjugation element and $\Psi$ | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean:102,106,112–116` |
| The family `tauE` and the value at `sqrtMinusD` | `src/Formalism/LocalRingCardinality/DataTheta.lean:491`, `src/Formalism/LocalToGlobal/BesselHermitianTheta/LemmasSign.lean:10–26` |
| The second proof and its consumer | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharInfinityEqCoeffMulHalfNormPow.lean:51–70,83–87`, `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsMkTauE.lean:72–92`, `src/Formalism/LocalToGlobal/LatticeGeometry/CmTypeMeetsConjugatePair.lean:10–33`, `src/Formalism/LocalRingCardinality/DataDIV.lean:365–366` |
| Consumers in §§19.3.6–19.3.7 | `src/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SiegelConeIntegralMatrixLatticeCount.lean:142–152`, `src/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsInverseChart.lean:15–18`, `src/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsRealChartInfiniteAdelesCmType.lean:15–37,45–55` |
| Mathlib at commit `0df444a360eaa60ab8c11dca51a86af692955474` | `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean:99–110,144`, `Mathlib/NumberTheory/NumberField/InfinitePlace/Embeddings.lean:61,192,205`, `Mathlib/NumberTheory/NumberField/CMField.lean:71–73,89–104`, `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:65–67,80–81,112` |

**Reading boundary.** R3 [Lean, read] covers `mk_tauE_bijective`, `places_bijective` and its forwarding declaration `GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective`, `factEmb`, `HostRaw.hostEmb`, `HostRaw.conj_sqd` and `HostRaw.gal_conj`. It covers the definitions of `tauE`, `Host.emb`, `sigmaOf`, `sqrtMinusD`, `HostRaw.cmType`, `HostRaw.K`, `FactEmb`, `chD`, `cc` and `Psi`, and the lemmas `galE_mem_Psi_iff`, `sqd_ne_zero`, `HostAx.conjE_apply`, `sigmaOf_sqrtMinusD` and `tauE_sqrtMinusD`. It also covers the second proof `LevelSeries.mk_tauE_bij` with `conjugate_tauE_ne_tauE` and `mk_tauE_complex`, the bodies of `CharInfPlace.exists_mk_tauE` and `conjugate_emb`, and the helpers `exists_tauEmb_iff`, `mem_Psi_iff_mul_cc_notMem` and `emb_mul_cc_comp` with the definition `DV.tauEmb`. The consumer bodies keep their reading levels from §§19.3.6–19.3.7; only their call lines were reread.

Several inputs stay at statement level [Lean]. The host properties are fields of structures, not theorems: `der : HostDer`, in particular `der.cmType`, `der.conj_iff` and `der.cm`, which gives `isCMField_hostE`, together with `φ₀_mem`, `qd_big`, `hyp`, `sqd_sq`, `gal_sqd`, `gal`, `galois` and `eTau`. The proposition `DerOfRaw`, which would derive the `HostDer` properties from the raw host, is defined but neither proved nor used anywhere in the archive. How each host supplies these fields when it is constructed is [Open] for this reading. The lemma `IsCMField.complexEmbedding_complexConj` used by `conjugate_emb` stays at statement level. From Mathlib at the pinned commit we read the definitions of `IsCMField`, `equivInfinitePlace` and `InfinitePlace.embedding` and the short proofs of `mk_embedding`, `mk_conjugate_eq` and `canonicalEmbedding.conj_apply`. `InfinitePlace.mk_eq_iff`, proved through `Complex.uniformContinuous_ringHom_eq_id_or_conj`, is used at statement level, as are `comap_surjective`, `card_infinitePlace_eq_card_infinitePlace`, `canonicalEmbedding.norm_le_iff`, `NumberField.Embeddings.card` and `IsGalois.card_aut_eq_finrank`. The degree identity `finrank_cmField_eq_two_mul_totallyRealSubfield` is not needed here and stays at its interface in §19.3.7. The two examples are not archive hosts. They, the place-model theorem and the doubling remark are textbook exposition [Expository]. The weighted count of §19.3.7, the Schwartz supply of §19.3.5 and the adelic charts of §19.3.6 are cited, not repeated.

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
| 19.3.1 | Siegel-set control and the weighted torus integral | [Lean, read] for the assembly, control lemma and cone induction |
| 19.3.2 | Rational covering and compact-tail reduction | [Lean, read] for the induction and absorption; deeper compactness and modulus inputs [Open] |
| 19.3.3 | Translated lattice estimates and the torus majorant | [Lean, read] for the direct producer and consumers; the weighted count is read in §19.3.7. The Schwartz input is in §19.3.5 |
| 19.3.4 | Common denominator, full lattice and compact right action | [Lean, read] for the cited production bodies and consumers. The full lattice is proved in the place model |
| 19.3.5 | A common finite support and all-order Schwartz bound | [Lean, read] for the finite tensor decomposition, majorant and stated consumers. See §19.3.6 for the three model and chart producers |
| 19.3.6 | Compatible adelic coordinates and real parameters | [Lean, read] for the direct splitting, inverse chart and size producers. Compact two-sided comparison is textbook exposition |
| 19.3.7 | Uniform weighted lattice count | [Lean, read] for the count, its cell and coordinate lemmas and the stacked call. The place identification is read in §19.3.8 |
| 19.3.8 | CM-type place identification | [Lean, read] for `mk_tauE_bijective`, `places_bijective` and the enumeration `factEmb`. The host structure fields stay [Lean]; their construction is [Open] |
| 19.4 | Does the RH proof consume the full `DoublingMethod`? How does the normalization compare? | Closed for the named full interface and `SiegelEisensteinSimplePole`: both are absent from the `riemannHypothesis` closure. Upstream `SiegelEisensteinContinuation`, the use of `DM` beyond the two bundle readers, and the $Z^*$ normalization remain [Open] |
| 19.5 | Split-place comparison with the published normalization | [Open]: needs $d_v$ from [LapidRallis2005, p. 334] |
| 19.6 | Second-term identity | [Open]: not stated by the inputs traced here; reader of the Rallis field not found |

The two Galois dependency questions and the full doubling dependency question are closed. The pattern in
Sections 19.4 and 19.6 adds a case to the polarity table of Section 18.1.2: a literature slot
whose name evokes a full theorem can be filled by a weaker proposition (`DM`), by `True`
(`UnusedSlot72`), or by a proposition whose reader has not been found.
