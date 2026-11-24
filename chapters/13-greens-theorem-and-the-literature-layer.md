# Chapter 13. Green's theorem and the literature layer

> **Status tags used in this chapter:** `[Lean, read]` for declarations and `sorry`-free proof
> bodies read line by line in `LabelDatum.lean`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean`,
> `SumRangeEqRoots.lean`, `DiscreteSpectrumResidualClassification.lean`,
> `StandardTheoremStatements/GlobalArtinReciprocity.lean`,
> `EveryCharacterOfLiteratureOfVWin.lean` (`OpenLiteratureStatements` and top assembly), and
> `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean` (`OpenImageCondition`) (`R3`), and, in Section 13.4.4, the producer of
> `GreenRegularCharacters` (`ExistsCuspidalCharacterOfRegularCharacterGLn.lean`,
> `IsCharacterCuspidalRootSumRegular.lean`, `GreenCuspidalCharsByRegularCharsProof.lean` and the
> definitions they unfold, `R3`), in Sections 13.4.5–13.4.11, the conditional production proofs
> for inputs `(I1)`, `(I2)`, `(I4)`–`(I8)` (including the virtual-character integral expansion), and `(I9)` at their stated interfaces (`R3`), in Section 13.4.12, the coordinate-free naming laws `nameLaws` (`NameLaws.lean`, `Pin*.lean`, `PairCheckThreeTwo.lean`, `NameCentral.lean`), the representation-level parametrization `PM.greenCuspidal` (`GreenCuspidal.lean`, `LabelMapNonempty.lean`, `ExistsCuspidalWithLabel.lean`, `CuspidalLabelUnique.lean`, `CuspidalLabelPolynomialUniqueAllPrimes.lean`), and their downstream consumer bridges (`CentralUnit.lean`, `ParUniq.lean`, `ProdFactorsOfMonic.lean`, `CuspParamOfGreenParametrisa…`, `AdmissibleLabelWeights…`, `R3` at their stated interfaces), and, in Section 13.4.13, the elliptic determination of cuspidal characters `GlobalTheory.CuspGL.cuspElliptic_statement` (`IrrCharEqOneOfSubsingleton.lean`, `CuspEllipticValues.lean`) together with its direct unipotent-block, integer-Gram, elliptic-Fourier, and Parseval/Vandermonde production chain (`ExistsStandardUnipotentRadicalBijOnNilradical.lean`, `CharacterCosetSumEqZeroOfSubgroupSum.lean`, `CharpolyBlockAndInvariantUnderStabilizerNilradic.lean`, `IsPrimitiveExtendZeroOfSumUnipotentRadical.lean`, `RegularIffNatDegreeAndExistsEllipticGL.lean`, `ExistsIntCoeffPrimitiveGLCharacter.lean`, `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean`, `OrthogonalIntVectorsNotAgreeOnRegular.lean`, `ParsevalBoundIntegerVectorSmallFourierSupport.lean`, `CardNonregularResiduesModPowSubOneLe.lean`, `SeparationNumericalIneqCuspidalGL.lean`, `NoNormEightOfFourierVanishingOrderFifteen.lean`, `NoNormTwelveOrderSixtythree.lean`, `R3` at their stated interfaces), and, in Section 13.4.14, the converse regular-label existence `GlobalTheory.CuspFormula.exists_regular` (`ExistsLabel.lean`) together with its esymm-virtuality, primary-class esymm, period-divisibility, and regular-exponent production chain (`EsymmMemVirtualCharactersOfPowerSumEigenvalues.lean`, `NatDegreeMulEsymmRootsPow.lean`, `DvdOfPeriodOfDvdSumPowersetCard.lean`, `CardDvdSumOfInvariantOfCardStabilizerDvd.lean`, `ExistsRegularExponentOfSumSqEq.lean`) and its three call sites (`LabelMapNonempty.lean`, `CuspidalParametrization.lean`, `PCuspChar.lean`), `R3` at their stated interfaces; `[Lean]` for the existence
> and proved status of individual `UpperTheory.LiteratureTheorems.*` and `GlobalTheory.Published.*`
> declarations (`R1` / `R2`); `[Paper]` for citations to Alpöge's `remark.pdf` and Masullo's draft;
> `[Community]` for public statement-fidelity reviews (notably LUMI's four-batch review of 105
> statements); `[Expository]` for classical Green character theory on $\mathrm{GL}_d(\mathbb F_q)$,
> worked $\mathrm{GL}_2(\mathbb F_q)$ / $\mathrm{GL}_2(\mathbb F_3)$ calculations, and audit
> methodology; `[Open]` for unreviewed named literature `Prop` definitions and unread proof cones.

In Chapter 12 (`src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7–11`) [Lean, read], we saw that once `Row0b recT` (`P14`) and
`RecTExists` (`P15`) are supplied, the final bridge to `UpperTheory.EveryCharacter` passes through
two remaining nodes of our proof map (`notes/proof-map.md`):

1. **Node P16 (`GlobalTheory.GLq.Green`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108`, proved from `GreenRegularCharacters` in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumRangeEqRoots.lean:225`):**
   J. A. Green's 1955 classification `[Green1955]` of the complex cuspidal irreducible characters of
   the finite general linear group $\mathrm{GL}_d(\mathbb F_g)$ ($g$ prime): they are parametrized
   bijectively by degree-$d$ monic irreducible polynomials $P \in \mathbb F_g[X]$ ($P(0) \neq 0$),
   have exact degree $\prod_{i=1}^{d-1}(g^i - 1)$, and take the Galois-orbit trace value
   $(-1)^{d-1}\sum_{i=0}^{d-1}\theta_x(z^{g^i})$ on elliptic elements of irreducible characteristic
   polynomial!
2. **Node P18 (`OpenLiteratureStatements` and `OpenImageCondition`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215–813`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207–343`):**
   The **literature layer** of the archive: **257 `theorem` declarations** in the namespace
   `UpperTheory.LiteratureTheorems.*` (176 named `*_of_literature` and 60 named `*_of_open`) that
   prove ~182 distinct named propositions (chiefly in `GlobalTheory.Published.*`, spanning Poitou–Tate
   duality, global Artin reciprocity, Bernstein–Zelevinsky finiteness, Siegel–Weil, Hironaka
   resolution, Kawamata–Viehweg, arithmetic Hilbert–Samuel, Bhatt–Scholze prismatic crystals, and
   `GreenRegularCharacters` itself!) **inside the archive without axioms**, and bundle them for
   Part II (`P17` and `P12`).

Pairing **P16** and **P18** in the closing chapter of Part III is deliberate. First, we work out
Green's cuspidal character theory by hand on $\mathrm{GL}_2(\mathbb F_q)$ and $\mathrm{GL}_2(\mathbb F_3)$
(order $48$) and read the complete 306-line formal proof of `green_of_regular` (`SumRangeEqRoots.lean`)
line by line (`R3` / `[Lean, read]`). Because `green_of_regular` sits directly atop
`GlobalTheory.Published.GreenRegularCharacters` — which formalizes Green's theorem **restricted to
prime fields $\mathbb F_g = \mathbb Z/g\mathbb Z$** (`Fact g.Prime`) rather than arbitrary prime
powers $q = p^f$ — it serves as a crystal-clear worked specimen of the entire literature layer! From
there we prove why misnamed, narrowed, or even `True`-valued internal `Prop`s (`UnusedSlot72`) **cannot
compromise the logical soundness of `src/Main.lean`**, lay out a rigorous four-step **statement-fidelity
audit methodology**, and synthesize the current community review verdicts across 105 audited
statements (`[Community]`).

---

## 13.1 Motivation

### 13.1.1 Where finite $\mathrm{GL}_d(\mathbb F_g)$ characters enter an analytic number theory proof

Why does a proof of the Riemann Hypothesis need the character table of the finite group
$\mathrm{GL}_d(\mathbb F_g)$ `[Green1955]` [Expository]? We have already met **both** places where
node **P16** bears weight:

1. **Shaping depth-zero level projectors along the theta-lift chain (Chapter 7, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33,54`):**
   On a totally definite unitary group $U(X_j)$ split at an auxiliary prime $g$ (`D.host.g 0`, `D.host.g 1`,
   where $U(r_j)(\mathbb Q_g) \cong \mathrm{GL}_{r_j}(\mathbb Q_g)$ and reduction modulo $g$ maps
   $\mathrm{GL}_{r_j}(\mathbb Z_g) \twoheadrightarrow \mathrm{GL}_{r_j}(\mathbb F_g)$!), cutting out
   irreducible depth-zero local types with controlled dimension and central idempotents (`zOf χ`,
   `eSerC L n f`, `ESerTie D` in `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:27,102,114` [Lean, read]) requires knowing:
   - that cuspidal irreducible characters $\tau_P$ of $\mathrm{GL}_d(\mathbb F_g)$ exist for every
     monic irreducible polynomial $P \in \mathbb F_g[X]$ of degree $d \ge 1$ with $P(0) \neq 0$,
   - that distinct polynomials $P \neq P'$ give **orthogonal** cuspidal characters $\tau_P \neq \tau_{P'}$,
   - that *every* cuspidal character arises this way, so Harish-Chandra parabolic induction (`hcL`, `:55`)
     partitions the entire irreducible dual of $\mathrm{GL}_n(\mathbb F_g)$ by polynomial labels (`HasLabel`, `:98`), and
   - that the dimension $\tau_P(1) = \prod_{i=1}^{d-1}(g^i - 1)$ is known explicitly (`closed_linkIRR_of_join_count hGreen`,
     `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:54` [Lean, read])!
2. **Pinning down depth-zero supercuspidal inertia in partial local Langlands (Chapter 12, `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/IsRecTOfIsRec.lean:35–53`):**
   In `TypeLaw` (Definition 12.1(2)) and `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:58–66` [Lean, read], inflating a cuspidal
   representation $\tau_\theta$ of $\mathrm{GL}_n(\mathbb F_g)$ to $\mathrm{GL}_n(\mathbb Q_g)$
   produces a depth-zero supercuspidal representation `[BushnellKutzko1993]` whose Weil–Deligne
   parameter on inertia has characteristic polynomial $\prod_{j=0}^{n-1}(X - \theta(z^{g^j}))$ —
   matching Green's elliptic character formula $(-1)^{n-1}\sum_{j=0}^{n-1}\theta(z^{g^j})$!

### 13.1.2 Why an axiom-free archive still has a "literature layer" — and what an audit actually checks

In a human paper, an author writes *"By Green `[Green1955]`, Theorem 12…"* or *"By Poitou–Tate duality…"*
and moves on. In Lean 4, if you want `src/Main.lean` to depend **only** on Lean's three foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`) — as Alpöge announced (`remark.pdf` p. 1: *"formalized the
arguments without assumptions"* [Paper; remark p. 1]) and half a dozen independent kernel checkers have
verified (Chapter 1; `CONTRIBUTIONS.md` [Community]) — **you cannot write `axiom PoitouTateDuality`**!
Every single classical theorem used anywhere in the argument must be **stated as a Lean `Prop` and
proved from Mathlib**!

To manage a 175,187-file codebase, the archive organizes those classical theorems through an explicit
internal interface (`EveryCharacterOfLiteratureOfVWin.lean` and `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean`):

- Lower-level folders (`PublishedTheorems/`, `StandardTheoremStatements/`, etc.) define named
  propositions such as `GlobalTheory.Published.GreenRegularCharacters : Prop`,
  `GlobalTheory.Published.GlobalArtinReciprocity : Prop`, or `GlobalTheory.Published.ArithHilbertSamuel : Prop`;
- Proof folders (`DivisorProofs/`, `AutomorphicKernels/`, `TemperedRepresentationTheory/`, etc.)
  **prove** each such `Prop` from Mathlib (plus, in 23 cases, from `Row0b` or `RecTExists`);
- `EveryCharacterOfLiteratureOfVWin.lean` collects those proved `Prop` terms into record bundles
  (`UnitaryGroupThirdPlaceHypotheses`, `ThetaLocalInputs`, `PublishedHodgeBundleTheorems`, …) and feeds
  them into Part II!

Here is the crucial distinction that every reader of this book must grasp [Expository]:

- **Machine kernel checking (`con-leche --compare`, `nanoda`, `lean4lean`, `leanchecker`) ALREADY guarantees
  that no unproved assumption leaks into `src/Main.lean`**, *regardless* of what the intermediate `Prop`s in
  `GlobalTheory.Published.*` are named or how weak they are!
- **Human statement-fidelity auditing** asks a *different*, equally vital mathematical question:
  *Does the Lean `Prop` named `GlobalTheory.Published.Foo` actually state the textbook theorem "Foo",
  a narrower special case (e.g. prime fields $\mathbb F_g$ or CM fields), a weaker statement, or even
  a `True` placeholder (`UnusedSlot72`) left over from refactoring?* Without answering that question,
  mathematicians cannot tell which classical theorems have genuinely been formalized for the first time
  in history (reusable for Mathlib!) and where the archive took legitimate shortcuts tailored to its
  specific pipeline!

---

## 13.2 Worked examples

### 13.2.1 Complete hand calculation of Green's cuspidal characters on $\mathrm{GL}_2(\mathbb F_q)$ and $\mathrm{GL}_2(\mathbb F_3)$

Let $q$ be any prime power (in the Lean archive's `Green`, $q = g$ is prime), and put
$G := \mathrm{GL}_2(\mathbb F_q)$, of order $\lvert G \rvert = (q^2 - 1)(q^2 - q) = q(q - 1)^2(q + 1)$
`[Green1955]` [Expository]. Let us construct all cuspidal characters of $G$ and verify parabolic
restriction (`res`), cuspidality (`IsCusp`), and Schur orthonormality (`ip`) completely by hand!

1. **The four conjugacy-class types of $\mathrm{GL}_2(\mathbb F_q)$:** Every matrix $x \in \mathrm{GL}_2(\mathbb F_q)$
   is classified up to $\mathrm{GL}_2(\mathbb F_q)$-conjugacy by its rational canonical / Jordan form over $\mathbb F_q$:
   - **Central scalars** $c_a := \begin{pmatrix} a & 0 \\ 0 & a \end{pmatrix}$ ($a \in \mathbb F_q^\times$):
     **$q - 1$ classes**, each of size $1$ (centralizer $G$);
   - **Regular unipotent shears** $u_a := \begin{pmatrix} a & 1 \\ 0 & a \end{pmatrix}$ ($a \in \mathbb F_q^\times$):
     **$q - 1$ classes**, centralizer $\bigl\{\begin{pmatrix} c & b \\ 0 & c \end{pmatrix} : c \in \mathbb F_q^\times,\ b \in \mathbb F_q\bigr\}$
     of order $q(q - 1)$, so each class has size $\frac{q(q-1)^2(q+1)}{q(q-1)} = q^2 - 1$;
   - **Split regular semisimple** $s_{a, b} := \begin{pmatrix} a & 0 \\ 0 & b \end{pmatrix}$ ($\{a, b\} \subset \mathbb F_q^\times$, $a \neq b$):
     **$\frac{(q-1)(q-2)}{2}$ classes**, centralizer the split torus $T(\mathbb F_q) \cong (\mathbb F_q^\times)^2$
     of order $(q - 1)^2$, so each class has size $\frac{q(q-1)^2(q+1)}{(q-1)^2} = q(q + 1)$;
   - **Elliptic (irreducible-charpoly) semisimple** $y_{\{z, z^q\}}$, acting as $\mathbb F_q$-linear
     multiplication by $z \in \mathbb F_{q^2}^\times \setminus \mathbb F_q^\times$ on $\mathbb F_{q^2} \cong \mathbb F_q^2$,
     with irreducible characteristic polynomial $P_z(X) = (X - z)(X - z^q) \in \mathbb F_q[X]$:
     **$\frac{q^2 - q}{2}$ classes** (one for each Frobenius pair $\{z, z^q\}$), centralizer the nonsplit
     torus $\mathbb F_{q^2}^\times$ of order $q^2 - 1$, so each class has size $\frac{q(q-1)^2(q+1)}{q^2 - 1} = q(q - 1)$!

   Check the total element count and total class count:
   $$(q - 1)\cdot 1 + (q - 1)(q^2 - 1) + \frac{(q - 1)(q - 2)}{2}\,q(q + 1) + \frac{q(q - 1)}{2}\,q(q - 1)
   = q(q - 1)^2(q + 1) = \lvert G \rvert,$$
   and the total number of conjugacy classes (hence of irreducible complex characters!) is
   $(q - 1) + (q - 1) + \frac{(q-1)(q-2)}{2} + \frac{q(q-1)}{2} = q^2 - 1$!

2. **What Harish-Chandra induction (`hc 1 1 α β 2`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:45`) produces — and what it misses:**
   Let $B = \bigl\{\begin{pmatrix} h_1 & v \\ 0 & h_2 \end{pmatrix}\bigr\} = M U \subset G$ be the
   upper-triangular Borel subgroup (`InPar 1`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:36`), of order $q(q - 1)^2$ and index
   $[G : B] = q + 1$. Inflating $\alpha \otimes \beta : (\mathbb F_q^\times)^2 \to \mathbb C^\times$
   from $M$ across $U$ and inducing to $G$ (`hc 1 1 α β 2`) gives a representation of degree $q + 1$
   that **vanishes identically on every elliptic class $y_{\{z, z^q\}}$** (because an elliptic matrix has
   no $\mathbb F_q$-eigenvector, hence cannot be conjugated into $B$!).
   - For $\alpha = \beta$ ($q - 1$ choices), $\operatorname{Ind}_B^G(\alpha \otimes \alpha) = (\alpha \circ \det) \oplus (\mathrm{St}_2 \otimes (\alpha \circ \det))$
     splits into **$q - 1$ characters of degree $1$** and **$q - 1$ Steinberg characters of degree $q$**;
   - For $\{\alpha, \beta\}$ distinct ($\frac{(q-1)(q-2)}{2}$ unordered pairs), $\operatorname{Ind}_B^G(\alpha \otimes \beta)$
     is irreducible of **degree $q + 1$**.
   Count how many irreducibles parabolic induction has found:
   $(q - 1) + (q - 1) + \frac{(q-1)(q-2)}{2} = \frac{(q-1)(q+2)}{2}$. Subtracting from $q^2 - 1$ leaves
   $$(q^2 - 1) - \frac{(q - 1)(q + 2)}{2} = \frac{q(q - 1)}{2} \quad \text{missing irreducible characters — the cuspidal characters!}$$

3. **Green's formula for $\tau_\theta$, Jacquet vanishing (`IsCusp`), and Schur unit norm:**
   Let $\theta : \mathbb F_{q^2}^\times \to \mathbb C^\times$ be any **regular** character (`IsRegularChar`,
   `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:10`: $\theta^q \neq \theta$, i.e. $\theta$ does not factor through
   $\operatorname{Nm}_{\mathbb F_{q^2}/\mathbb F_q} : \mathbb F_{q^2}^\times \twoheadrightarrow \mathbb F_q^\times$;
   there are $(q^2 - 1) - (q - 1) = q(q - 1)$ such characters, forming $\frac{q(q-1)}{2}$ Frobenius pairs
   $\{\theta, \theta^q\}$!). Green's class function $\tau_\theta : \mathrm{GL}_2(\mathbb F_q) \to \mathbb C$ is:
   $$\tau_\theta(c_a) = (q - 1)\,\theta(a), \qquad
   \tau_\theta(u_a) = -\theta(a), \qquad
   \tau_\theta(s_{a, b}) = 0, \qquad
   \tau_\theta\bigl(y_{\{z, z^q\}}\bigr) = -\bigl(\theta(z) + \theta(z^q)\bigr)$$
   (notice that on $c_1 = I_2$ this matches `τ θ 1 = ∏_{i ∈ [1,2)} (q^i - 1) = q - 1`, and on elliptic
   $y_{\{z, z^q\}}$ it matches `(-1)^(2-1) * ∑_{i<2} θ(z^(q^i)) = -(θ(z) + θ(z^q))` in
   `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:16–18`!). Check **both** cuspidality and unit norm by hand:
   - **Jacquet restriction (`res 1 1 τ_θ`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:47–49, 64–65`) vanishes identically:**
     For any $h_1, h_2 \in \mathbb F_q^\times$, `res 1 1 τ_θ h₁ h₂` averages $\tau_\theta\begin{pmatrix} h_1 & b \\ 0 & h_2 \end{pmatrix}$
     over the $q$ unipotent entries $b \in \mathbb F_q$:
     - if $h_1 \neq h_2$, every $\begin{pmatrix} h_1 & b \\ 0 & h_2 \end{pmatrix}$ has distinct eigenvalues
       $h_1, h_2 \in \mathbb F_q^\times$, hence is conjugate to $s_{h_1, h_2}$, where $\tau_\theta = 0$!
     - if $h_1 = h_2 = a$, then $b = 0$ gives $c_a$ (contributing $(q - 1)\theta(a)$) while the $q - 1$
       nonzero values $b \in \mathbb F_q^\times$ are all conjugate via $\operatorname{diag}(1, b)$ to $u_a$
       (each contributing $-\theta(a)$), so
       $$\mathrm{res}_{1, 1}(\tau_\theta)(a, a) = \frac{1}{q}\Bigl((q - 1)\theta(a) + (q - 1)\bigl(-\theta(a)\bigr)\Bigr) = 0!$$
   - **Schur inner product (`ip τ_θ τ_θ`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:22–23`) equals $1$:**
     Since $\theta^{q-1} \neq 1$ on $\mathbb F_{q^2}^\times$, character orthogonality on $\mathbb F_{q^2}^\times$
     gives $\sum_{z \in \mathbb F_{q^2}^\times} \theta(z^{q-1}) = 0$, whence
     $$\sum_{z \in \mathbb F_{q^2}^\times \setminus \mathbb F_q^\times} \bigl\lvert \theta(z) + \theta(z^q) \bigr\rvert^2
     = \sum_{z \in \mathbb F_{q^2}^\times} \bigl(2 + \theta(z^{q-1}) + \overline{\theta(z^{q-1})}\bigr) - \sum_{a \in \mathbb F_q^\times} 4
     = 2(q^2 - 1) - 4(q - 1) = 2(q - 1)^2.$$
     Dividing by $2$ (for unordered pairs $\{z, z^q\}$) and multiplying by class sizes gives
     $$\sum_{x \in G} \lvert \tau_\theta(x) \rvert^2
     = (q - 1)\cdot (q - 1)^2 + (q - 1)(q^2 - 1)\cdot 1 + 0 + q(q - 1)\cdot (q - 1)^2
     = (q - 1)\bigl[(q - 1)^2 + (q^2 - 1) + q(q - 1)^2\bigr] = q(q - 1)^2(q + 1) = \lvert G \rvert,$$
     so $\langle \tau_\theta, \tau_\theta \rangle_G = 1$! (And because $\tau_\theta$ is realized on a
     virtual character of degree $q - 1 > 0$ — e.g. via the Weil representation or Brauer's theorem —
     $\langle \tau_\theta, \tau_\theta \rangle_G = 1$ with $\tau_\theta(1) > 0$ proves irreducibility!)

4. **Concrete specialization at $g = q = 3$ ($\lvert \mathrm{GL}_2(\mathbb F_3) \rvert = 48$):**
   Over $\mathbb F_3$, $\mathbb F_9^\times$ is cyclic of order $3^2 - 1 = 8$. Choose generator
   $\zeta \in \mathbb F_9^\times$ with minimal polynomial $P_1(X) = X^2 + X + 2 \in \mathbb F_3[X]$
   ($\zeta^2 = 2\zeta + 1$, $\zeta^4 = -1 \in \mathbb F_3^\times$), and send $\zeta \mapsto \omega_8 := e^{2\pi i/8} = \frac{1+i}{\sqrt{2}}$
   via `L.teich`. Since $\theta_\zeta(-1) = \theta_\zeta(\zeta^4) = \omega_8^4 = -1$,
   $\omega_8 + \omega_8^3 = \frac{1+i}{\sqrt{2}} + \frac{-1+i}{\sqrt{2}} = i\sqrt{2}$, and
   $\omega_8^2 + \omega_8^6 = i + (-i) = 0$, the $\frac{3(3-1)}{2} = 3$ monic irreducible polynomials
   `IsPrimeLab 2 P` in $\mathbb F_3[X]$ ($P_1 = X^2 + X + 2$, $P_2 = X^2 + 2X + 2$, $P_3 = X^2 + 1$)
   give the following exact degree-$2$ cuspidal characters $\tau_P$ across all $8$ conjugacy classes of
   $\mathrm{GL}_2(\mathbb F_3)$:

   | Label $P \in \mathbb F_3[X]$ | Roots in $\mathbb F_9^\times$ | $\theta_x(\zeta)$ | $c_1 = I_2$ ($1$) | $c_2 = -I_2$ ($1$) | $u_1$ ($8$) | $u_2$ ($8$) | $s_{1,2}$ ($12$) | $y_{X^2+1}$ ($6$) | $y_{X^2+X+2}$ ($6$) | $y_{X^2+2X+2}$ ($6$) |
   |---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
   | $P_1 = X^2 + X + 2$ | $\{\zeta, \zeta^3\}$ | $\omega_8$ | $2$ | $-2$ | $-1$ | $+1$ | $0$ | $0$ | $-i\sqrt{2}$ | $+i\sqrt{2}$ |
   | $P_2 = X^2 + 2X + 2$ | $\{\zeta^5, \zeta^7\}$ | $-\omega_8$ | $2$ | $-2$ | $-1$ | $+1$ | $0$ | $0$ | $+i\sqrt{2}$ | $-i\sqrt{2}$ |
   | $P_3 = X^2 + 1$ | $\{\zeta^2, \zeta^6\}$ | $i$ | $2$ | $+2$ | $-1$ | $-1$ | $0$ | $+2$ | $0$ | $0$ |

   Check Schur orthonormality directly from the table:
   $$\langle \tau_{P_1}, \tau_{P_1} \rangle = \frac{1}{48}\bigl(1\cdot 4 + 1\cdot 4 + 8\cdot 1 + 8\cdot 1 + 0 + 0 + 6\cdot 2 + 6\cdot 2\bigr) = \frac{48}{48} = 1,$$
   $$\langle \tau_{P_1}, \tau_{P_2} \rangle = \frac{1}{48}\bigl(4 + 4 + 8 + 8 + 0 + 0 + 6(-i\sqrt{2})(-i\sqrt{2}) + 6(i\sqrt{2})(i\sqrt{2})\bigr) = \frac{24 - 12 - 12}{48} = 0,$$
   $$\langle \tau_{P_1}, \tau_{P_3} \rangle = \frac{1}{48}\bigl(1(2)(2) + 1(-2)(2) + 8(-1)(-1) + 8(+1)(-1) + 0 + 6(0)(2) + 0 + 0\bigr) = 0.$$
   Every row has degree $3 - 1 = 2$, Schur norm $1$, Jacquet restriction $0$, and exact pairwise
   orthogonality!

### 13.2.2 Three concrete specimens from `GlobalTheory.Published.*`: faithful, special-case, and `True`

Before stating the general definitions of node **P18**, inspect three actual declarations in the
archive (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:13`,
`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70` alongside its proof wrapper
`src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8`, and
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:6–7`) [Lean, read]:

1. **A faithful special case (`GlobalTheory.Published.GreenRegularCharacters`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:13–20`):**
   Quantifies over `∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ K [Field K] [Algebra (ZMod g) K], finrank (ZMod g) K = d → ...`.
   Every mathematical clause (cuspidality, degree $\prod_{i=1}^{d-1}(g^i - 1)$, elliptic trace
   $(-1)^{d-1}\sum_{i=0}^{d-1}\theta(z^{g^i})$, Frobenius orbit equivalence $\theta' = \theta^{g^i}$,
   and exhaustion of `IsCusp`) matches Green `[Green1955]`, specialized to **prime base fields
   $\mathbb F_g = \mathrm{ZMod}\,g$** (because the archive only reduces $\mathbb Z_g$-lattices at split
   degree-$1$ places $E_w \cong \mathbb Q_g$!).
2. **A full classical statement (`GlobalTheory.Published.GlobalArtinReciprocity`, `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70–72`):**
   States `IsGlobalArtin art` (`:25–39`: open quotient map $\mathbb A_E^\times \twoheadrightarrow G_E^{\mathrm{ab}}$
   with kernel $\overline{E^\times (E_\infty^\times)^\circ}$, inertia image $\overline{\mathrm{art}(\mathcal O_v^\times)}$,
   and geometric Frobenius on uniformizers) over **every** number field $E$, proved unconditionally via
   the wrapper `PositivityTheory.Stage1.PM.globalArtinReciprocity`
   (`src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8–15`,
   invoking `CompanionTheory.FamInh.globalArtin` `[Lean]`), used in Chapter 10 (`CutCoreUnit.main`),
   and audited line by line at `R3` in **Chapter 18** (`Section 18.2`) [Lean, read]!
3. **A `True` placeholder fossil (`GlobalTheory.Published.UnusedSlot72`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:7`):**
   Literally defined as:
   ```lean
   abbrev GlobalTheory.Published.DoublingMethodLocalZetaIntegrals : Prop := ResidueKilled.DM
   abbrev GlobalTheory.Published.UnusedSlot72 : Prop := True
   ```
   and "proved" in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:505–506` [Lean, read] by:
   ```lean
   theorem UpperTheory.LiteratureTheorems.siegel_eisenstein_simple_pole
       (O : OpenLiteratureStatements) : GlobalTheory.Published.UnusedSlot72 :=
     trivial
   ```
   As we verified directly in Chapter 7 (Section 7.5.1), `siegelEisensteinSimplePole` is stored as field
   #52 of `UnitaryGroupThirdPlaceHypotheses` and **never projected anywhere downstream**! Meanwhile its
   neighbor `DoublingMethodLocalZetaIntegrals` (`:6`) is **not** `True` — it proves the global doubling
   identity `ResidueKilled.DM` (`doubling_method`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:371–372`) —
   yet its name mentions "LocalZetaIntegrals" even though local zeta integrals were refactored out
   (`[Community]`, LUMI R2 #18)!

---

## 13.3 Definitions

### 13.3.1 Finite $\mathrm{GL}_d(\mathbb F_g)$ characters, `LabelDatum`, and `Green` (`LabelDatum.lean`)

**Definition 13.1 (`hc`, `res`, `IsCusp`, `LabelDatum`, `thetaOf`, `IsPrimeLab`, `IsCuspOf`, `HasLabel`, and `Green`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:22,45,47,64,81,88,91,93,98,108`).** [Lean, read]

Fix a prime $g$ (`[Fact g.Prime]`) and write `Gn g n := GL (Fin n) (ZMod g)` and
`Mt g n := Matrix (Fin n) (Fin n) (ZMod g)` (`:11–13`), with normalized character inner product
`ip α β := |G|⁻¹ * ∑ x, α x * β x⁻¹` (`:22–23`).

1. **Harish-Chandra induction, Jacquet restriction, and cuspidality (`:36–65`):**
   Write `InPar a M` (`:36`) if $M \in M_n(\mathbb F_g)$ is block upper-triangular with lower-left
   $(n - a) \times a$ block zero, and `tl a M` / `br a b M` for its $a \times a$ top-left and $b \times b$
   bottom-right Levi blocks:
   - `hc a b α β n` (`:40–45`): normalized parabolic induction of class functions $\alpha$ on $\mathrm{GL}_a(\mathbb F_g)$
     and $\beta$ on $\mathrm{GL}_b(\mathbb F_g)$ to $\mathrm{GL}_n(\mathbb F_g)$ (iterated along lists of
     pairs in `hcL`, `:55–57`);
   - `res a b χ h₁ h₂` (`:47–49`): normalized Jacquet (unipotent-coinvariant) average
     $g^{-ab}\sum_{x \in \mathrm{InPar}(a),\ \mathrm{tl}=h_1,\ \mathrm{br}=h_2} \chi(x)$;
   - `IsCusp χ` (`:64–65`): $0 < d$, `IsIrr χ`, and **`∀ a, 0 < a → a < d → res a (d - a) χ 1 1 = 0`**
     (note: for an irreducible character $\chi$, vanishing of the unipotent invariant dimension
     $\dim V^{U_{a, d-a}} = \mathrm{res}_{a, d-a}(\chi)(1, 1) = 0$ forces the entire module $V^{U_{a, d-a}} = 0$,
     hence `res a (d - a) χ h₁ h₂ = 0` for all $(h_1, h_2)$!).
2. **Compatible multiplicative generators and polynomial labels (`LabelDatum`, `IsPrimeLab`, `IsCuspOf`, `HasLabel`, `:81–101`):**
   - `LabelDatum g` (`:81–86`) packages an injective multiplicative Teichmüller embedding
     `teich : Fbar g →* ℂ` (`teich_inj` on $\overline{\mathbb F}_g^\times$) together with norm-compatible
     generators `gen d ∈ Fbar g` of exact multiplicative order $g^d - 1$ (`gen (d*e)^((g^(de)-1)/(g^d-1)) = gen d`);
   - `thetaOf L d x z` (`:88–89`) sends $z = (\mathrm{gen}\,d)^n$ to $(\mathrm{teich}\,x)^n$ (and $0$ if $z \notin \langle \mathrm{gen}\,d \rangle$);
   - `IsPrimeLab d P` (`:91`): $P \in \mathbb F_g[X]$ is monic, irreducible, $P(0) \neq 0$, and $\deg P = d$;
   - `IsCuspOf L P χ` (`:93–96`): `IsPrimeLab d P`, `IsCusp χ`, and for **every** root $x \in \overline{\mathbb F}_g$
     of $P$, every $y \in \mathrm{GL}_d(\mathbb F_g)$ with irreducible characteristic polynomial, and
     every root $z \in \overline{\mathbb F}_g$ of $\mathrm{charpoly}(y)$,
     $$\chi(y) = (-1)^{d - 1} \sum_{i = 0}^{d - 1} \mathrm{thetaOf}(L, d, x, z^{g^i});$$
   - `HasLabel L χ f` (`:98–100`): $\chi$ has nonzero inner product with `hcL` of a list of cuspidal
     pieces `(P_k, χ_k)` whose polynomial labels multiply to $f = \prod_k P_k \in \mathbb F_g[X]$,
     cutting out the central Hecke projector `eSerC L n f` (`:102`).
3. **Green's classification (`GlobalTheory.GLq.Green`, `:108–112`):** For every prime $g$, every
   `L : LabelDatum g`, and every $d > 0$, there exists $\tau : \mathbb F_g[X] \to \mathrm{GL}_d(\mathbb F_g) \to \mathbb C$
   such that:
   - *(Existence & degree)* for every $P$ with `IsPrimeLab d P`, `IsCuspOf L P (τ P)` holds and
     $\tau(P)(1) = \prod_{i = 1}^{d - 1} (g^i - 1)$;
   - *(Injectivity)* if `IsPrimeLab d P`, `IsPrimeLab d P'`, and $\tau(P) = \tau(P')$, then $P = P'$;
   - *(Exhaustion)* for every cuspidal character $\chi$ (`IsCusp χ`), $\chi = \tau(P)$ for some `IsPrimeLab d P`.

### 13.3.2 The literature layer (`OpenLiteratureStatements`, `OpenImageCondition`, and `GlobalTheory.Published.*`)

**Definition 13.2 (Architecture of the literature layer, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215–813` and `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207–343`).** [Lean, read]

1. **The two root `Prop` structures (`:215` and `:207`):**
   - On the main `EveryCharacter` branch (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215–218`),
     `UpperTheory.LiteratureTheorems.OpenLiteratureStatements : Prop` is a **3-field structure**
     `(caraianiLocalGlobalDual : Row, localLanglandsExists : RecTExists, galoisRepOfPolarizedPairLit : Row)`
     whose first and third fields both have type `UpperTheory.One.M.Row` (`Row0b recT`, Chapter 12);
   - On the `VWin` branch (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207–208`),
     `UpperTheory.LiteratureTheorems.OpenImageCondition : Prop` is a **1-field structure**
     `(galoisRepOfPolarizedPairLit : RowT)`, where `RowT` is definitionally identical to `Row`.
2. **Exact inventory of `UpperTheory.LiteratureTheorems.*` and `PublishedTheorems` directories:**
   Across the entire 175,187-file archive (`notes/proof-map.md`, node `P18`), the namespace
   `UpperTheory.LiteratureTheorems.*` contains **257 `theorem` declarations** in total (**195** in
   `EveryCharacterOfLiteratureOfVWin.lean`, import cone **151,285**, and **62** in
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean`, import cone **146,662**), comprising:
   - **176** individual theorems named `*_of_literature : OpenLiteratureStatements → <Prop>`,
   - **60** individual theorems named `*_of_open : OpenImageCondition → <Prop>`,
   - **20** named-theorem aliases and intermediate bundle constructors (`literature_local`,
     `literature_automorphy`, `literature_cohomology`, `literature_nonexistence`, `published_results_analytic`,
     `published_results_local`, `published_results_eigen`, `published_results_first`, `published_results_arithmetic`, …), and
   - the master theorem `every_character_of_literature_of_vWin : OpenLiteratureStatements → VWin → EveryCharacter` (`:810`).

   The target propositions live across eight `PublishedTheorems` / `PublishedInputs` directory trees
   (`AbelianVarietyTheory/PublishedTheorems`, `AutomorphicVarieties/PublishedTheorems`,
   `AutomorphicSpectrum/PublishedTheorems`, `WeilBound/CoreStatements/PublishedTheorems`,
   `WeilBound/CoreStatements/StandardPublishedResults`, `PositivityTheory/PublishedTheorems`,
   `PositivityTheory/AutomorphicForms/PublishedInputs`, and `CompanionTheory/.../PublishedTheorems`),
   representing ~182 distinct statement constants (~155 in `GlobalTheory.Published.*` and 27 in
   `ReciprocityTheory.Gal.*`, `Formalism.GaloisCohomology.*`, and `GlobalTheory.CompanionTheory.*`)
   `[Lean]`, `[Community]`.

---

## 13.4 Lemmas and proofs

### 13.4.1 Complete proof of `green_of_regular`: from regular characters of $\mathbb F_{g^d}^\times$ to polynomial labels (`SumRangeEqRoots.lean`)

We read all 306 lines of `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumRangeEqRoots.lean`
(import cone **232** modules) line by line (`R3` / `[Lean, read]`). Let us give its complete human proof!

**Proposition 13.1 (Galois-orbit bridge from `GreenRegularCharacters` to `Green`: `green_of_regular`).**
*If `GlobalTheory.Published.GreenRegularCharacters` holds (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:13`), then
`GlobalTheory.GLq.Green` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:108`) holds.*
*(Lean: `exists_unit_gen`, `th_inj`, `th_surj`, `pow_inj`, `regular_iff`, `sum_range_eq_roots`,
`thetaOf_pow`, and `GlobalTheory.GreenBridge.green_of_regular`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumRangeEqRoots.lean:53,142,148,180,207,213,218,225`.)* [Lean, read]

*Proof.* Fix a prime $g$, `L : LabelDatum g`, and $d > 0$. Let $K := \mathrm{GaloisField}\,g\,d \cong \mathbb F_{g^d}$
(`KK g d`, `:18`), of dimension $[K : \mathbb F_g] = d$ and cardinality $g^d$ (`card_KK`, `:26`),
embedded $\mathbb F_g$-linearly into $\overline{\mathbb F}_g = \mathrm{Fbar}\,g$ via `emb g d` (`:20–24`).

1. **Teichmüller parametrization of $\widehat{K^\times} = \operatorname{Hom}(K^\times, \mathbb C^\times)$ (`:53–160`):**
   Since `L.gen d` has order $g^d - 1$, it satisfies $w^{g^d} = w$, hence lies in the image of $K^\times$
   under `emb g d`, defining a cyclic generator $u := \mathrm{uu}(L) \in K^\times$ of order $g^d - 1$
   (`exists_unit_gen`, `orderOf_uu`, `:53, 83`). For every $x \in \overline{\mathbb F}_g$ with
   $x^{g^d - 1} = 1$, `L.teich x` is a $(g^d - 1)$-st root of unity in $\mathbb C^\times$ (`orderOf_tu_dvd`, `:99`),
   so sending $u^n \mapsto (\mathrm{L.teich}\,x)^n$ defines a character $\mathrm{th}(L, x) : K^\times \to \mathbb C^\times$
   (`:105–120`) satisfying:
   - $\mathrm{th}(L, x)(k) = \mathrm{thetaOf}(L, d, x, \mathrm{emb}(k))$ for all $k \in K^\times$ (`th_apply`, `:122`);
   - $\mathrm{th}(L, x^m) = \mathrm{th}(L, x)^m$ for all $m \in \mathbb N$ (`th_pow`, `:137`);
   - **bijectivity** between $\{x \in \overline{\mathbb F}_g : x^{g^d - 1} = 1\}$ and $\operatorname{Hom}(K^\times, \mathbb C^\times)$
     (`th_inj` at `:142` from `L.teich_inj`; `th_surj` at `:148` since `L.teich (L.gen d)` is a primitive
     $(g^d - 1)$-st root of unity in $\mathbb C^\times$!).
2. **Regularity $\iff$ distinct Frobenius conjugates $\iff$ degree-$d$ minimal polynomial (`:172–212`):**
   Using $\mathrm{th}(L, x)^{g^i} = \mathrm{th}(L, x^{g^i})$ and injectivity `th_inj`, `regular_iff` (`:207–211`)
   proves that for $x^{g^d - 1} = 1$,
   $$\mathrm{IsRegularChar}\bigl(g, d, \mathrm{th}(L, x)\bigr)
   \iff \forall\, 0 \le i, j < d,\quad x^{g^i} = x^{g^j} \implies i = j.$$
   In particular, for any `IsPrimeLab d P` ($\deg P = d$, $P$ monic irreducible over $\mathbb F_g$,
   $P(0) \neq 0$), its chosen root $x_0 := \mathrm{rootOf}\,P \in \overline{\mathbb F}_g$ (`:187–195`)
   satisfies $x_0^{g^d - 1} = 1$ (`root_unit`, `:197`) and has $d$ distinct Frobenius conjugates
   $x_0, x_0^g, \dots, x_0^{g^{d-1}}$ (`pow_inj`, `:180–185`), so $\theta_P := \mathrm{th}(L, x_0)$ is
   regular (`hreg`, `:228–231`)!
3. **Constructing $\tau(P) := \tau_G(\theta_P)$ and verifying the three clauses of `Green` (`:225–305`):**
   Apply `hG : GreenRegularCharacters` to $(g, d, K)$ to obtain $\tau_G : (K^\times \to \mathbb C^\times) \to \mathrm{Gn}\,g\,d \to \mathbb C$ (`:227`),
   and set $\tau(P) := \tau_G\bigl(\mathrm{th}(L, \mathrm{rootOf}\,P)\bigr)$ (`:232`):
   - *Degree and root-independent trace (`:233–272`):* `h1` gives `IsCusp (τ P)` and $\tau(P)(1) = \prod_{i=1}^{d-1}(g^i - 1)$.
     For any *other* root $x$ of $P$ and any root $z$ of an irreducible characteristic polynomial $f = \mathrm{charpoly}(y)$,
     $x = x_0^{g^j}$ for some $0 \le j < d$ (`:259–261`). Because $z \mapsto z^{g^j}$ permutes the
     Frobenius root set $\{z, z^g, \dots, z^{g^{d-1}}\}$ of $f$ (`sum_range_eq_roots`, `:213–216`) and
     `thetaOf` satisfies the duality symmetry $\mathrm{thetaOf}(L, d, x_0^{g^j}, w) = \mathrm{thetaOf}(L, d, x_0, w^{g^j})$
     (`thetaOf_pow`, `:218–223`, since $(u^n)^{g^j}$ and $(x_0^{g^j})^n$ both raise $(\mathrm{teich}\,x_0)^n$ to $g^j$!),
     $$\sum_{i = 0}^{d - 1} \mathrm{thetaOf}(L, d, x_0, z^{g^i})
     = \sum_{i = 0}^{d - 1} \mathrm{thetaOf}\bigl(L, d, x_0, (z^{g^j})^{g^i}\bigr)
     = \sum_{i = 0}^{d - 1} \mathrm{thetaOf}\bigl(L, d, x_0^{g^j}, z^{g^i}\bigr),$$
     proving `IsCuspOf L P (τ P)` independently of which root $x$ of $P$ is chosen!
   - *Injectivity (`:273–280`):* If $\tau(P) = \tau(P')$, then `h2` gives $\mathrm{th}(L, x_0') = \mathrm{th}(L, x_0)^{g^i} = \mathrm{th}(L, x_0^{g^i})$
     for some $i < d$, so `th_inj` gives $x_0' = x_0^{g^i}$, which is also a root of $P$ (`root_pow`, `:165`).
     Since $P$ and $P'$ are both monic and irreducible over $\mathbb F_g$ and share the root $x_0'$,
     both equal $\mathrm{minpoly}_{\mathbb F_g}(x_0')$, so $P = P'$ (`:279–280`)!
   - *Exhaustion (`:281–305`):* Given `IsCusp χ`, `h3` gives $\chi = \tau_G(\theta)$ for some regular $\theta$,
     and `th_surj` writes $\theta = \mathrm{th}(L, x)$ with $x^{g^d - 1} = 1$. Let $P := \mathrm{minpoly}_{\mathbb F_g}(x)$
     (`:285`): since $x^{g^d} = x$, $\deg P \mid d$ (`:288`), and if $\deg P < d$ then $x^{g^{\deg P}} = x^1$
     would violate `regular_iff` at $(i, j) = (\deg P, 0)$ (`:291–294`)! Hence $\deg P = d$ and
     `IsPrimeLab d P` holds (`:295`). Finally, $x_0 = \mathrm{rootOf}\,P$ equals $x^{g^j}$ for some $j < d$
     (`:298–302`), so $\mathrm{th}(L, x_0) = \theta^{g^j}$ and `h2` gives $\tau_G(\theta) = \tau_G(\mathrm{th}(L, x_0)) = \tau(P)$ (`:304`)! $\square$

Proposition 13.1 is conditional on its hypothesis `hG`. Section 13.4.4 reads the archive's proof of
`hG`: how regular characters produce the cuspidal characters, and how exhaustion is obtained.

### 13.4.2 Logical soundness vs. statement fidelity: a formal meta-lemma on internal `Prop` layers

Let us state with complete precision why the `GlobalTheory.Published.*` layer does **not** weaken the
machine-checked validity of the five target theorems in `src/Main.lean` [Expository].

**Proposition 13.2 (Cut-elimination / soundness invariance under internal `Prop` naming).**
*In Lean's Calculus of Inductive Constructions, suppose a closed target proposition $T$ defined purely
in terms of Mathlib constants (such as `RiemannHypothesis` in `src/Main.lean:4`) has a well-typed proof
term $t_T : T$ constructed by Modus Ponens $t_T = f\,p$ from an internal proposition $P : \mathrm{Prop}$,
a proof $p : P$, and an implication proof $f : P \to T$, such that the transitive constant closure of
$t_T$ uses no `axiom` declarations beyond `{propext, Classical.choice, Quot.sound}`.* [Lean, read]

1. *(Soundness of $T$ is independent of $P$'s external meaning)* *Whether $P$ faithfully formalizes the
   published mathematical theorem suggested by its identifier, formalizes only a restricted special
   case, formalizes a weaker statement, or is definitionally equal to `True` (`UnusedSlot72`), $t_T = f\,p$
   remains a valid axiom-free derivation of $T$!*
2. *(Polarity dichotomy for intermediate interfaces)* *If $P$ is **weaker** than its namesake classical
   theorem $P_{\mathrm{lit}}$ ($P_{\mathrm{lit}} \implies P$), then proving $p : P$ is easier than
   proving $P_{\mathrm{lit}}$, while proving the consumer $f : P \to T$ requires $T$ to follow from
   less; conversely, if $P$ were **false**, no closed proof $p : P$ could typecheck in a consistent
   kernel!*

*Proof.* Immediate from subject reduction / typing of function application $\frac{\Gamma \vdash f : P \to T \quad \Gamma \vdash p : P}{\Gamma \vdash f\,p : T}$
in Lean's kernel, verified independently on `src/Main.lean` by `con-leche --compare` and `nanoda` against the
Mathlib-only `Challenge.lean` export (Chapter 1, Section 1.6) [Community]. $\square$

### 13.4.3 Statement-fidelity audit methodology and current community verdicts (`[Community]` / `[Open]`)

If Proposition 13.2 guarantees that internal `Prop` names cannot smuggle unproved assumptions into
`src/Main.lean`, why did community teams immediately launch statement-fidelity reviews of
`GlobalTheory.Published.*` (`LUMI doc 07`, `aapolipponen/rh-lean-check-lumi/docs/07-named-theorems.md`
[Community])? Because for **human mathematical understanding** (and for extracting standalone theorems
into Mathlib), we need to know *what mathematics is actually inside the 151,285-module cone*!

A rigorous **four-step statement-fidelity audit** of any named declaration `D : Prop` proceeds as follows [Expository]:

1. **Unfold custom types to Mathlib primitives:** Expand every project-defined wrapper (`CuspSub`,
   `IsPartialZeta`, `IsGlobalArtinMap`, `LocTied`, `GrothendieckMessing`'s categorical PD cohomology)
   at least two definition layers deep so no hidden hypothesis is buried inside a structure type.
2. **Check quantifier polarity and non-vacuity of hypotheses:** Verify that universal hypotheses
   (`∀ P AI, Nonempty (LocTied l P AI) → ...` or `∀ f, IsPartialZeta ... → ...`) are actually inhabited
   by an in-archive existence theorem (as verified for `exists_locPrime_tied`), ensuring the `Prop` is
   not vacuously true on an empty domain!
3. **Classify against the published theorem:** Place `D` into one of five precise buckets:
   - **Faithful:** matches the standard textbook/journal theorem (up to standard equivalences);
   - **Special case:** proves a genuine, non-vacuous restriction (e.g. prime fields $\mathbb F_g$, CM or
     totally complex number fields, unitary groups $U(p, q)$, or convergent Siegel–Weil range);
   - **Safe weakening:** asserts strictly less than the namesake theorem (e.g. qualitative infinitude
     in `ChebotarevDegreeOne` without natural density, or `Row0b` / `RecTExists` in Chapter 12);
   - **Placeholder / misnamed:** `Prop := True` (`UnusedSlot72`) or a declaration whose content belongs
     to a different step than its identifier (`DoublingMethodLocalZetaIntegrals`);
   - **Undetermined / project-specific:** relies on bespoke project definitions not yet matched to
     standard definitions (e.g. categorical crystalline cohomology or `VWin`).
4. **Trace downstream projection sites:** Check whether downstream theorems actually project `D` or
   discard it (`intro _ ...`).

Across four read-only review batches dated 2026-11-20 (`LUMI doc 07` [Community]), community reviewers
applied Steps 1–3 to **105 named statements** (out of ~182 distinct statement constants in the
literature layer, leaving **77–83 constants not yet audited** `[Open]`). Aggregating their twelve
subject tables into five broad mathematical domains gives the following picture (`[Community]`):

| Mathematical domain (synthesized from `LUMI doc 07`) | Audited | Faithful | Special case | Safe weakening | Undetermined | Representative declarations |
|---|---:|---:|---:|---:|---:|---|
| Number fields, class field theory, algebraic groups, and analytic inputs | 24 | 19 | 4 | 1 | 0 | `GlobalArtinReciprocity`, `HermitianHassePrinciple`, `Linnik`, `ChebotarevDegreeOne` |
| Complex, birational, and Arakelov geometry; abelian moduli | 25 | 17 | 4 | 2 | 2 | `ResolutionCharZero`, `KawamataViehweg`, `ArithHilbertSamuel`, `SerreTate` |
| Galois cohomology and $\ell = p$ Hodge theory | 8 | 6 | 1 | 1 | 0 | `BhattScholzeIntegral`, `FontaineBcris`, `DeRhamPotSemistable`, `PoitouTateNormalised` |
| Finite-field, non-archimedean, and archimedean representation theory | 22 | 19 | 3 | 0 | 0 | `GreenRegularCharacters`, `BernsteinZelevinskyFiniteness`, `LocalConverseGL`, `CasselmanWallach` |
| Automorphic forms, theta/Siegel–Weil inputs, and project load-bearing packages | 26 | 4 | 17 | 3 | 2 | `ClozelPurity`, `WeilSiegelFormulaUnitary`, `Row0b`, `RecTExists`, `VWin` |
| **Combined total across all audited statements** | **105** | **65** | **29** | **7** | **4** | **77–83 further constants remain unaudited `[Open]`** |

Three headline takeaways emerge from this community audit (`[Community]`):

1. **Zero vacuous statements found among the 105 audited rows:** Even where an early batch flagged
   period-ring quantification (`LocTied` in `BhattScholzeIntegral`, `BlochKatoLocal`, `DeRhamPotSemistable`),
   a follow-up check located `exists_locPrime_tied` (`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLocalPrimeAinf.lean:281`), confirming
   non-vacuity [Community].
2. **Pragmatic specialization is the norm in automorphic forms:** Nearly 90% (14 of 16) of the audited
   automorphic-form statements restrict to totally complex / CM fields or unitary groups — the exact
   setting needed for our CM host fields $E$!
3. **Massive standalone formalization value (pending proof digestion `[Open]`):** If human refactoring
   confirms the definitions of the **65 faithful** theorems — which include Hironaka's resolution of
   singularities in characteristic zero (`ResolutionCharZero`), Kawamata–Viehweg vanishing, arithmetic
   Hilbert–Samuel, Bhatt–Scholze's prismatic realization of crystalline lattices, Berger's $p$-adic
   monodromy theorem, global Artin reciprocity, Bernstein–Zelevinsky's segment ring, Henniart's local
   converse theorem, and Linnik's theorem — the archive contains formal proofs of dozens of landmark
   twentieth- and twenty-first-century theorems never previously formalized in any proof assistant!


### 13.4.4 Where `GreenRegularCharacters` comes from: regular characters produce cuspidal characters

> **Reading level of this section.** `R3` / [Lean, read] for the existence supplier
> `GlobalTheory.GreenRegular.exists_cusp_of_regular`, its two assembly lemmas
> `GlobalTheory.ParamLabel.isCusp_psi` and `GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular`, its one
> direct consumer `GlobalTheory.greenRegularCharacters_holds`, the definitions they unfold, and the
> elementary Lemmas 13.4, 13.5 and 13.7; `R2` / [Lean] (statement and call site read, proof not read)
> for (I3) (with (I4)–(I5) read in §13.4.6 and (I7) read in §13.4.7). Section 13.4.5 reads (I6), Section 13.4.8 reads (I9), Section 13.4.9 reads (I1) and its `ParamLabel` / choice-of-embedding bridges, and Section 13.4.10 reads (I2) and (I8), each at its stated conditional depth. Paths are relative to `lean/` in the pinned
> `lean.tar.gz` (sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`).

**Motivation.** Proposition 13.1 turned `GlobalTheory.Published.GreenRegularCharacters` into polynomial
labels, but it took that statement as a hypothesis `hG`. On the main path the hypothesis is supplied
twice, both times by the same term [Lean, read]. First, `every_character_of_literature_of_vWin`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810–813`)
hands the bundle `published_results_eigen O` (`:666`) of type `UnitaryGroupThirdPlaceHypotheses`
(field `greenRegularCharacters` declared at
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/BernsteinUnitaryProductIrreducible.lean:50`,
filled at `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:694`) to `every_character_of_theta_integrals_local_matching`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69–73`),
whose line `:72` reads `green_of_regular P.greenRegularCharacters`. The field value is a chain of wrappers:
`green_regular_characters_of_literature O := PositivityTheory.Stage1.PM.greenRegularCharacters`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:399–400`; the argument `O` is not used)
`:= GlobalTheory.T.greenCuspidalCharsByRegularChars_proof`
(`src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GreenRegularCharacters.lean:5–6`)
`:= GlobalTheory.greenRegularCharacters_holds`
(`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProofStatement.lean:8–9`,
proof at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProof.lean:137–168`).
Second, the same call passes as its argument `hX` the covolume bound `topCovolSlim2_use_alt_alt`
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:812`),
whose proof uses `green_of_regular greenRegularCharacters_holds` directly
(`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopCovolSlim2Use.lean:16–18`).
The `VWin`-side twin `green_regular_characters_of_open`
(`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:285–286`)
is the same term. So no Green input on this path uses the argument `O : OpenLiteratureStatements`.
`greenRegularCharacters_holds` does two things: it takes the characters $\tau_\theta$ from the existence
theorem `GlobalTheory.T.exists_cuspidalCharacter_of_regularCharacter_GLn`
(`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLnStatement.lean:8–9`,
which is `GlobalTheory.GreenRegular.exists_cusp_of_regular`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:65–225`),
and it proves exhaustion by counting. The archive builds $\tau_\theta$ directly as a Möbius inversion of
a root power sum over the lattice of invariant subspaces (Definition 13.3); in the files read we found
neither Deligne–Lusztig induction nor Green's uniform functions and degeneracy rule. We first watch the
construction work on $\mathrm{GL}_2(\mathbb F_3)$.

**Example 13.3 ($\mathrm{GL}_2(\mathbb F_3)$ and the characters of $\mathbb F_9^\times$).** [Expository;
every number below was checked in exact arithmetic by our script `verify_green_gl2f3.py`, which is not in
the repository; see `sources/SOURCES.md`, Part I §7]
Take $g = 3$, $d = 2$ and $K = \mathbb F_9 = \mathbb F_3[\zeta]/(\zeta^2 + \zeta + 2)$ as in §13.2.1(4); $\zeta$
generates $K^\times$, which is cyclic of order $8$. Let $\theta_0$ send $\zeta^n$ to $\omega_8^n$ with
$\omega_8 = e^{2\pi i/8}$ and $0$ to $0$. It is multiplicative and injective on nonzero elements, which is
all the archive asks of its Teichmüller map (the archive's map lives on $\overline{\mathbb F}_3$; only its
restriction to $\mathbb F_9$ enters here). Every character of $K^\times$ is
$\theta_k : \zeta^n \mapsto \omega_8^{kn}$ for exactly one $k \in \mathbb Z/8$.

1. *Frobenius orbits.* Raising to the $g$-th power sends $\theta_k$ to $\theta_k^3 = \theta_{3k}$.
   `IsRegularChar 3 2 θ_k` asks $\theta_k^{3^0} \neq \theta_k^{3^1}$, that is $2k \not\equiv 0 \pmod 8$, that is
   $k \notin \{0, 4\}$. The six regular characters form three orbits $\{\theta_1,\theta_3\}$,
   $\{\theta_2,\theta_6\}$, $\{\theta_5,\theta_7\}$, each of length exactly $d = 2$ (since $\theta^8 = 1$,
   $\theta^{3^2} = \theta$). The two non-regular characters $\theta_0, \theta_4$ are the ones that factor
   through the norm $K^\times \to \mathbb F_3^\times$.
2. *The class function.* Put $s_k(P) := \sum_\alpha \theta_0(\alpha)^k$, the sum over the roots of $P$ in
   $\overline{\mathbb F}_3$ counted with multiplicity (the archive's `rootSum`). For every $2 \times 2$ matrix $x$
   over $\mathbb F_3$ set
   $\psi_k(x) := s_k(\mathrm{charpoly}\,x) - \sum_W \psi_k(x|_W)$, the sum over the $x$-invariant subspaces
   $W \neq \mathbb F_3^2$. The zero subspace contributes $s_k(1) = 0$, and an invariant line on which $x$ acts
   by $a$ contributes $s_k(X - a) = \theta_0(a)^k$. Class by class ($a \neq b$ in $\mathbb F_3^\times$,
   $z \in \mathbb F_9 \setminus \mathbb F_3$):
   - scalar $aI$: all four lines are invariant, so $\psi_k = 2\theta_0(a)^k - 4\theta_0(a)^k = -2\theta_0(a)^k$;
   - Jordan block with eigenvalue $a$: one invariant line, $\psi_k = 2\theta_0(a)^k - \theta_0(a)^k = \theta_0(a)^k$;
   - $\mathrm{diag}(a, b)$: two invariant lines, $\psi_k = 0$;
   - elliptic $y$ with roots $z, z^3$: no invariant line, $\psi_k = \theta_0(z)^k + \theta_0(z^3)^k$.

   The archive's character is $\tau_k := (-1)^{d-1}\psi_k = -\psi_k$. With $q = 3$ its values are
   $(q-1)\theta_k(a)$, $-\theta_k(a)$, $0$ and $-(\theta_k(z) + \theta_k(z^3))$: exactly the cuspidal
   character of §13.2.1(3).
3. *Dimension and labels.* $\tau_k(1) = 2 = g - 1 = \prod_{i=1}^{d-1}(g^i - 1)$ for every $k$. The function
   $\tau_k$ depends only on the orbit ($\tau_1 = \tau_3$, $\tau_2 = \tau_6$, $\tau_5 = \tau_7$), and the
   three orbits give three different functions: the three rows of the table in §13.2.1(4), whose labels
   $X^2 + X + 2$, $X^2 + 1$, $X^2 + 2X + 2$ are the minimal polynomials of $\zeta$, $\zeta^2$, $\zeta^5$.
4. *Why regularity is needed.* For $k = 0$ the same recursion gives $\tau_0 = \mathrm{St} - 1$, and for
   $k = 4$ it gives $\tau_4 = (\mathrm{St} - 1)\cdot(\mathrm{sgn}\circ\det)$, where $\mathrm{St}(x)$ is the number
   of $x$-invariant lines minus one. Both have $\langle\tau,\tau\rangle = 2$, so neither is irreducible.
   Both still have vanishing Jacquet sum $\sum_{b}\tau\bigl(\begin{smallmatrix}1&b\\0&1\end{smallmatrix}\bigr) = 0$
   (because $\mathrm{St}$ and $1$ each have a one-dimensional space of unipotent invariants). Cuspidality in
   the sense of Jacquet sums holds for every $k$; only irreducibility needs regularity.
5. *Exact certificate.* The script computes in $\mathbb Q(\zeta_{24})$ with rational coordinates and checks:
   $\psi_k(1) = 1 - 3$ for all $k$; the four class-type values of item 2 at all $48$ elements and all $8$
   values of $k$, and the elliptic formula for both roots; the primitivity identity of Definition 13.3(4)
   for each of the $4$ lines $A$ and each of the $27$ endomorphisms (invertible or not) preserving $A$, for
   all $8$ values of $k$; the Gram identity
   $\sum_{x \in \mathrm{GL}_2(\mathbb F_3)} \psi_k(x)\,\overline{s_l(\mathrm{charpoly}\,x)} = 48 \cdot \#\{i < 2 : 3^i k \equiv l \bmod 8\}$
   for all $64$ pairs $(k, l)$; the norms ($1$ for regular $k$, $2$ for $k = 0, 4$); the orbit
   equivalence; and the $24$ entries of the three rows of the table in §13.2.1(4) ($\tau_1$, $\tau_5$,
   $\tau_2$ give the rows of $P_1$, $P_2$, $P_3$). Independently of the archive it checks
   $\tau_k = \mathrm{Ind}_{ZN}^{G}(\theta_k|_Z \cdot \epsilon) - \mathrm{Ind}_{K^\times}^{G}(\theta_k)$ for regular $k$
   ($ZN$ the scalars times the upper unipotent matrices, $\epsilon$ a nontrivial additive character of
   $\mathbb F_3$ on the unipotent entry, $K^\times$ the elliptic torus), so in this example $\tau_k$ is a difference of two induced
   characters with norm $1$ and degree $2$, hence an irreducible character. Finally the eight functions
   $1$, $\mathrm{sgn}\circ\det$, $\mathrm{St}$, $\mathrm{St}\cdot(\mathrm{sgn}\circ\det)$,
   $\mathrm{Ind}_B^G(1 \otimes \mathrm{sgn})$, $\tau_1$, $\tau_2$, $\tau_5$ are orthonormal, so they are all of
   $\mathrm{Irr}(\mathrm{GL}_2(\mathbb F_3))$, and exactly the three $\tau$'s have zero Jacquet sum: the
   exhaustion clause holds in this example ($2{,}431$ assertions, $0.39$ s CPU).

The example only fixes what the symbols mean; the general statement is proved below.

**Definition 13.3 (the archive's construction).** [Lean, read] Let $F$ be a finite field with $q$
elements, $V$ a finite-dimensional $F$-vector space and $\mathrm{End}_F(V)$ the set of all endomorphisms,
invertible or not. Citations are to
`src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean`
unless stated otherwise.

1. *Additive functions* (`IsAdditive`, `:21–22`): $s : F[X] \to \mathbb C$ with $s(PQ) = s(P) + s(Q)$ for
   monic $P, Q$. Then $s(1) = 0$.
2. *Root power sums* (`rootSum`, `:65–66`): for $\theta_0 : \overline F \to \mathbb C$ multiplicative and
   $k \in \mathbb N$, $s_k(P) := \sum_{\alpha} \theta_0(\alpha)^k$ over the roots of $P$ in $\overline F$ with
   multiplicity (with Lean's conventions $\theta_0(0) = 0$ and $x^0 = 1$).
3. *Invariant-subspace Möbius inverse* (`invariantSubspaceMobiusInverseRec`, `:24–29`; `psi`, `:35–37`;
   unfolding lemma `psi_eq`, `:55–63`):
   $\psi_s(V, x) = s(\mathrm{charpoly}\,x) - \sum_{W \neq V,\ xW \subseteq W} \psi_s(W, x|_W)$.
   Equivalently $\sum_{W} \psi_s(W, x|_W) = s(\mathrm{charpoly}\,x)$ over all $x$-invariant $W$: $\psi_s$ is the
   Möbius inverse of $W \mapsto s(\mathrm{charpoly}(x|_W))$ on the lattice of $x$-invariant subspaces.
4. *Primitive functions* (`nilRad`, `:11–12`; `IsPrimitive`, `:17–19`): $\varphi : \mathrm{End}_F(V) \to \mathbb C$
   is primitive if $\sum_{h \in N_A}\varphi(x + h) = 0$ for every subspace $0 \neq A \neq V$ and every $x$ with
   $xA \subseteq A$, where $N_A = \{h : h(V) \subseteq A,\ h(A) = 0\}$. For $x = 1$ the set $1 + N_A$ is the
   unipotent radical of the stabilizer of $A$; primitivity is Jacquet vanishing, required on all of
   $\mathrm{End}_F(V)$.
5. *Inner product* (`ipGL`, `:83–84`; `glCard`, `:72`):
   $\mathrm{ipGL}(\varphi, \varphi') = \sum_{x\ \text{invertible}} \varphi(x)\,\overline{\varphi'(x)}$, the
   unnormalized Hermitian product over $\mathrm{GL}(V)$, and $\mathrm{glCard}\,F\,n = \lvert\mathrm{GL}_n(F)\rvert$.
6. *Virtual characters* (`BI.IsChar`, `BI.IsIrrChar`, `BI.Virt`,
   `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/AbByPOfComm.lean:5–12`): $\chi$ is a
   character if it is the trace of some $\rho : G \to \mathrm{GL}_n(\mathbb C)$; `Virt` is the additive group
   generated by characters.
7. *Regular characters and cuspidality* (`IsRegularChar`,
   `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:10–11`;
   `IsIrr` and `IsCusp`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:19–20, 64–65`):
   $\theta : K^\times \to \mathbb C^\times$ is regular if $\theta^{g^i} = \theta^{g^j}$ with $i, j < d$ forces
   $i = j$. `IsCusp χ` asks $d > 0$, that $\chi$ be the character of a simple finite-dimensional complex
   representation, and `res a (d-a) χ 1 1 = 0` for $0 < a < d$. If $\chi$ is the character of $V$, then
   `res a b χ 1 1` $= g^{-ab}\sum_{u \in U_{a,b}}\chi(u) = \dim V^{U_{a,b}}$, so this is the usual cuspidality: no
   nonzero vector is fixed by the unipotent radical of a maximal standard parabolic.

**Lemma 13.4 (elementary properties).** [Lean, read]

1. Each $s_k$ is additive and $s_k((X - 1)^j) = j$ (`rootSum_isAdditive_and_pow_X_sub_one`,
   `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharacterAdditiveAndXSubOnePow.lean:9–20`).
2. If $s$ is additive, $\psi_s(V, x) = 0$ when $\dim V = 0$, and $\psi_s(V, x) = s(\mathrm{charpoly}\,x)$ when
   $\mathrm{charpoly}\,x$ is irreducible (`psi_of_finrank_eq_zero`, `finrank_eq_zero_of_irreducible_charpoly`,
   `psi_of_irreducible_charpoly`,
   `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseCharpolyOfIrreduci.lean:7–20, 33–50, 52–56`).
3. If $f \in \mathbb F_g[X]$ is irreducible with a root $z \in \overline{\mathbb F}_g$, its roots are
   $z, z^g, \dots, z^{g^{\deg f - 1}}$, each once (`GreenExists.pow_eq_self_iff`, `GreenExists.rootsBar_eq`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CuspidalCharExistsOfGreen.lean:60–66, 68–94`).
4. If $\varphi$ is primitive on $\mathrm{End}(F^d)$ and $0 < a < d$, then $\sum_{u \in U_{a,d-a}}\varphi(u) = 0$
   (`IsPrimitive.finsum_unipotentRadical_eq_zero`,
   `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FinsumUnipotentRadicalEqZero.lean:10–26`).

*Proof.* (1) The roots of a product of monic polynomials are the union of the root multisets;
$(X - 1)^j$ has the root $1$ with multiplicity $j$, and $\theta_0(1)^k = 1$. (2) On the zero space the
characteristic polynomial is $1$, there is no proper subspace, and $s(1) = 0$ because $s(1) = s(1 \cdot 1) = 2s(1)$.
If $\mathrm{charpoly}\,x$ is irreducible and $W \neq V$ is invariant with $\dim W > 0$, the minimal polynomial
of $x|_W$ is not constant and divides $\mathrm{charpoly}\,x$, so equals it up to a unit; it also divides
$\mathrm{charpoly}(x|_W)$, of degree $\dim W < \dim V$: impossible. So every proper invariant subspace is $0$
and contributes $0$.
(3) $z^{g^n} = z$ if and only if $\deg f \mid n$, so the $\deg f$ values $z^{g^i}$ are distinct roots, and
there are no others. (4) The statement `exists_standardUnipotentRadical_bijOn_nilradical`
(`src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsStandardUnipotentRadicalBijOnNilradicalStatement.lean:7`, [Lean])
supplies a subspace $A$ of dimension $a$ such that $u \mapsto u - 1$ maps $U_{a,d-a}$ bijectively onto $N_A$.
Since $0 < a < d$, $A \neq 0$ and $A \neq F^d$, and primitivity at $x = 1$ gives
$\sum_{u \in U_{a,d-a}}\varphi(u) = \sum_{h \in N_A}\varphi(1 + h) = 0$. $\square$

**Lemma 13.5 (characters of $K^\times$ as powers of one character).** [Lean, read] Let $g$ be prime,
$d > 0$, and $K$ a field with an $\mathbb F_g$-algebra structure and $[K : \mathbb F_g] = d$. Then
$\lvert K\rvert = g^d$ and $\lvert K^\times\rvert = g^d - 1$. Fix $\theta_0 : \overline{\mathbb F}_g \to \mathbb C$
multiplicative and injective on nonzero elements, an $\mathbb F_g$-embedding $\iota : K \to \overline{\mathbb F}_g$,
and put $\lambda := \theta_0 \circ \iota$ on $K^\times$. Then: (i) $\lambda$ is injective, so $\lambda(\gamma)$ is a
primitive $(g^d - 1)$-th root of unity for a generator $\gamma$ of $K^\times$; (ii) $\lambda^a = \lambda^b$ if and
only if $a \equiv b \pmod{g^d - 1}$; (iii) every $\theta : K^\times \to \mathbb C^\times$ is $\lambda^k$ for some $k$,
written $k(\theta)$; (iv) if $\theta$ is regular, $k(\theta)\,g^i \not\equiv k(\theta) \pmod{g^d - 1}$ for
$0 < i < d$. (`…/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:78–81` for the field
size via `Module.card_eq_pow_finrank`, `:85–97` for (i), `:100–110` for (ii), `:111–122` for (iii),
`:123–130` for (iv).)

*Proof.* (i) $\theta_0$ is injective on nonzero elements and $\iota$ is injective. (ii) Evaluate at $\gamma$;
conversely every $u \in K^\times$ satisfies $u^{g^d - 1} = 1$. (iii) $\theta(\gamma)^{g^d - 1} = 1$, so
$\theta(\gamma) = \lambda(\gamma)^k$ for some $k$, and $\gamma$ generates. (iv) If $k g^i \equiv k$, then
$\theta^{g^i} = \lambda^{k g^i} = \lambda^k = \theta^{g^0}$, contradicting regularity at $(i, 0)$. $\square$

Condition (iv) uses only the comparisons with $j = 0$; because $\theta^{g^d} = \theta$ it is equivalent to
full regularity, that is, to "$k, kg, \dots, kg^{d-1}$ are distinct modulo $g^d - 1$", which is Green's
condition (Remark 13.4.4(2)).

**The inputs read at statement level.** The proofs below call the following archive theorems. Each
`GlobalTheory.T.*` statement is a one-line wrapper (`first | exact @…`) of the lemma named after it; we
have read the statements, the wrappers and the call sites, but not the proofs [Lean]. Whether each
proof establishes what its classical counterpart says is part of what remains [Open].

- (I1) A multiplicative $\theta_0 : \overline F \to \mathbb C$ injective on nonzero elements exists
  (`T.exists_teichmuller_map_algebraicClosure_finiteField`,
  `…/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement.lean:7`; lemma
  `CuspGL.TeichEmb.exists_teichmuller`, `…/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:24`). Section 13.4.9 reads this Witt-vector production proof, its zero-extension and `ParamLabel` bridges, and how changing the embedding permutes labels.
- (I2) If $\dim V > 0$ and $s((X - 1)^j) = j$ for all $j$, then
  $\psi_s(V, 1) = \prod_{i \in [1, \dim V)}(1 - q^i)$ (`T.invariantSubspaceMobiusInverse_one_prod_Ico`,
  `…/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIcoStatement.lean:6`; lemma `CuspGL.psi_one`,
  `…/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIco.lean:74`). Section 13.4.10 reads its
  production proof, a count over the subspace lattice (Lemmas 13.26 and 13.27).
- (I3) For additive $s$, $\psi_s$ is primitive (`T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse`,
  `…/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement.lean:6`; lemma
  `CuspGL.isPrimitive_psi`, `…/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobi.lean:188`),
  and for every $s$ it is invariant under transport by linear isomorphisms, in particular under
  conjugation (`T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj`,
  `…/CharacterTheory/InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement.lean:6`; lemma
  `CuspGL.psi_conj`, `…/CharacterTheory/InvariantSubspaceMobiusInverseCharpolyLinearEqui.lean:43`).
- (I4) The Gram identity, for $\dim V = d > 0$ and $\theta_0$ as in (I1):
  $\mathrm{ipGL}(\psi_{s_k}, s_l \circ \mathrm{charpoly}) = \lvert\mathrm{GL}_d(F)\rvert \cdot \#\{i < d : k q^i \equiv l \bmod q^d - 1\}$
  (`T.invertibleEndInnerProduct_rootPowerSum_mobius`,
  `…/CharacterTheory/InvertibleEndInnerProductRootPowerSumMobiusStatement.lean:7`; lemma
  `CuspGL.ipGL_psi_rootSum`, `…/CharacterTheory/InvertibleEndInnerProductRootPowerSumMobius.lean:30`).
- (I5) For additive $s$ and primitive $\varphi$,
  $\mathrm{ipGL}(\varphi, \psi_s) = \mathrm{ipGL}(\varphi, s \circ \mathrm{charpoly})$
  (`T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse`,
  `…/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiuStatement.lean:6`; lemma
  `CuspGL.PrimOrth.ipGL_psi_eq`, `…/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean:92`);
  and for a primitive class function $\varphi$ and invertible $x$,
  $\lvert\mathrm{GL}_d(F)\rvert \cdot d \cdot \varphi(x) = \sum_{l < q^d - 1}\mathrm{ipGL}(\varphi, s_l \circ \mathrm{charpoly})\,\psi_{s_l}(x)$
  (`T.primitiveClassFunction_expansion_rootSums`,
  `…/CharacterTheory/PrimitiveClassFunctionExpansionRootSumsStatement.lean:7`; lemma
  `CuspGL.expand_primitive`, `…/CharacterTheory/PrimitiveClassFunctionExpansionRootSums.lean:156`).
- (I6) $x \mapsto s_k(\mathrm{charpoly}\,x)$ is a virtual character of $\mathrm{GL}_n(F)$ for all $n, k$
  (`T.rootPowerSum_charpoly_mem_virtualCharacters_GL`,
  `…/CharacterTheory/RootPowerSumCharpolyMemVirtualCharactersGLStatement.lean:7`; lemma
  `CuspGL.rootSum_charpoly_mem_virt`, `…/CharacterTheory/RootPowerSumCharpolyMemVirtualCharactersGL.lean:213`,
  whose file imports a Brauer-type induction package (`OneMemClosureInducedCentralByPrimePower`,
  `IsCharacterBrauerLiftAbelianByPrimePower`), elementary symmetric functions of the roots
  (`IsCharacterEsymmRootsCharpoly`) and Newton's identities (`MultisetPowerSumNewtonIdentity`)). This is a
  special case of Green's Theorem 1. Section 13.4.5 reads the production proof and its Brauer-type induction supplier.
- (I7) Parabolic induction preserves virtual characters (`ParabVirt.parab_virt`,
  `…/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean:193`): if $\Phi$ is invariant under
  transport by linear isomorphisms and $x \mapsto \Phi(F^a, x)$ is virtual on $\mathrm{GL}_a(F)$, then
  $x \mapsto \sum_{W\ x\text{-invariant},\ \dim W = a}\Phi(W, x|_W)$ is virtual on $\mathrm{GL}_n(F)$. See §13.4.7 for its proof and use in the subtraction.
- (I8) A virtual character of norm one is $\pm$ an irreducible character, and a character of norm one is
  irreducible of positive degree (`T.irreducible_of_virtualCharacter_norm_one`,
  `…/CharacterTheory/IrreducibleOfVirtualCharacterNormOneStatement.lean:7`; lemma `BI.irr_of_norm_one`,
  `…/CharacterTheory/IrreducibleOfVirtualCharacterNormOne.lean:57`); $\overline{\chi(x)} = \chi(x^{-1})$ for
  virtual $\chi$ (`T.star_virtualCharacter_eq_apply_inv`,
  `…/CharacterTheory/StarVirtualCharacterEqApplyInvStatement.lean:7`; lemma `CuspGL.star_virt_eq_inv`,
  `…/CharacterTheory/StarVirtualCharacterEqApplyInv.lean:10`); the bookkeeping identity that rewrites
  $\mathrm{ipGL}$ as a sum over $\mathrm{GL}_d(F)$ (`T.generalLinearFunctionExtendZeroEnd_properties`,
  `…/CharacterTheory/GeneralLinearFunctionExtendZeroEndPropertiesStatement.lean:7`; lemma
  `CuspGL.extZero_spec`, `…/CharacterTheory/GeneralLinearFunctionExtendZeroEndProperties.lean:87`); and
  Mathlib's criterion `FDRep.simple_iff_char_is_norm_one`
  (`Mathlib/RepresentationTheory/FinGroupCharZero.lean:121` at the pinned commit): for a finite group $G$
  and an algebraically closed field of characteristic $0$, a finite-dimensional representation $V$ is
  simple if and only if $\sum_{g \in G}\chi_V(g)\chi_V(g^{-1}) = \lvert G\rvert$. Section 13.4.10 reads the
  production proofs of these four statements (Lemmas 13.28–13.30 and Theorem 13.31).
- (I9) (exhaustion only) A finite set of distinct multisets of cuspidal characters of total degree $n$ has at
  most $g^n - g^{n-1}$ elements (`T.card_cuspidal_multisets_total_degree_le`,
  `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardCuspidalMultisetsTotalDegreeLeStatement.lean:8`).
  We read its assembly `CuspMultisetCount.card_le` (`…/InertiaEigenvalues/CardCuspidalMultisetsTotalDegreeLe.lean:30–61`):
  each multiset is sent to an irreducible constituent of its Harish-Chandra induction with a nonzero
  Whittaker functional, distinct multisets give distinct constituents, and there are at most
  $g^n - g^{n-1}$ such generic irreducible characters. See Theorem 13.17 and its three preceding lemmas for the production proof and its named inputs.

**Proposition 13.6 (the existence supplier `exists_cusp_of_regular`).** [Lean, read], conditional on
(I1)–(I8). Let $g$ be prime, $d > 0$ and $K$ a field with an $\mathbb F_g$-algebra structure and
$[K : \mathbb F_g] = d$. For $\theta : K^\times \to \mathbb C^\times$ put
$\tau_\theta(x) := (-1)^{d-1}\,\psi_{s_{k(\theta)}}(\mathbb F_g^d, x)$ for $x \in \mathrm{GL}_d(\mathbb F_g)$, with
$k(\theta)$ as in Lemma 13.5 (`…/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:133–134`). Then for every
regular $\theta$:

1. `IsCusp τ_θ`: $\tau_\theta$ is the character of a simple finite-dimensional complex representation, and
   `res a (d-a) τ_θ 1 1 = 0` for $0 < a < d$;
2. $\tau_\theta(1) = \prod_{i=1}^{d-1}(g^i - 1)$;
3. if $\mathrm{charpoly}\,y$ is irreducible and $z \in K^\times$ is one of its roots, then
   $\tau_\theta(y) = (-1)^{d-1}\sum_{i<d}\theta(z^{g^i})$;

and for regular $\theta, \theta'$:

4. $\tau_\theta = \tau_{\theta'}$ if and only if $\theta' = \theta^{g^i}$ for some $i < d$.

These are the first conjuncts of `GreenRegularCharacters` (`…/GaloisCohomology₂/GreenRegularCharacters.lean:13–20`),
everything except exhaustion.

*Proof.* Write $k = k(\theta)$, $\psi_k := \psi_{s_k}(\mathbb F_g^d, \cdot)$ and $G = \mathrm{GL}_d(\mathbb F_g)$.

*Step 1 ($\psi_k$ is a virtual character;*
`src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean:55–88`*).*
Strong induction on $d$. Sorting the proper invariant subspaces by their dimension $a < d$ (helper
`finsum_proper_invariant_eq_sum_range_finrank`, `:19–52`),
$\psi_k(x) = s_k(\mathrm{charpoly}\,x) - \sum_{a<d}\sum_{W\ x\text{-invariant},\ \dim W = a}\psi_k(W, x|_W)$.
The first term is virtual by (I6). For each $a$ the inner sum is virtual by (I7), applied to
$\Phi = \psi_{s_k}$ (invariant under transport of structure by (I3), `:63–68`) and the induction
hypothesis on $\mathrm{GL}_a$. The proof term is `sub_mem (rootSum_charpoly_mem_virt …) (sum_mem … parab_virt …)`
(`:84–88`).

*Step 2 (norm; `:101–118`).* By (I3) $\psi_k$ is primitive, so by (I5)
$\mathrm{ipGL}(\psi_k, \psi_k) = \mathrm{ipGL}(\psi_k, s_k \circ \mathrm{charpoly})$, which by (I4) is
$\lvert G\rvert \cdot \#\{i < d : k g^i \equiv k\}$ (`:105–107`). Lemma 13.5(iv) makes the set $\{0\}$, so
$\sum_{x \in G}\lvert\psi_k(x)\rvert^2 = \lvert G\rvert$.

*Step 3 (sign; `:119–184`).* $\chi := (-1)^{d-1}\psi_k$ is virtual (Step 1), satisfies
$\sum_x \lvert\chi(x)\rvert^2 = \lvert G\rvert$ by Step 2 and the bookkeeping identity of (I8) (`:134–143`), and
$\chi(1) = \prod_{i=1}^{d-1}(g^i - 1) > 0$ by (I2) and Lemma 13.4(1) (`:145–165`). By (I8) $\chi$ or $-\chi$ is
an irreducible character. If $-\chi$ were, (I8) would give a natural number $n > 0$ with $-\chi(1) = n$,
that is $n + \prod(g^i - 1) = 0$ in $\mathbb N$, which is impossible (`:173–184`). So $\chi$ is the character of
some $\rho : G \to \mathrm{GL}_n(\mathbb C)$ (Theorem 13.31(B) in §13.4.10 gives the complete argument). This is `isChar_psi_rootSum_of_regular` (`:92–184`; statement
wrapper `T.isCharacter_cuspidal_rootSum_regular`,
`…/CharacterTheory/IsCharacterCuspidalRootSumRegularStatement.lean:7–8`).

*Step 4 (`IsCusp`;*
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18–48`*).*
Irreducibility (`:25–38`): the representation `FDRep.of ρ` has character $\tau_\theta$; by Mathlib's
criterion (I8) it is simple if and only if $\sum_x \tau_\theta(x)\tau_\theta(x^{-1}) = \lvert G\rvert$; since
$\overline{\tau_\theta(x)} = \tau_\theta(x^{-1})$ for virtual characters (I8) and $((-1)^{d-1})^2 = 1$, this is
Step 2, rewritten as a sum over $G$ by the bookkeeping identity of (I8) (Theorem 13.31(B)(4)). Jacquet vanishing
(`:39–48`): by (I3) and Lemma 13.4(4), $\sum_{u \in U_{a,d-a}}\psi_k(u) = 0$, and
`GreenExists.mem_grUnipBlock_iff`
(`…/InertiaEigenvalues/CuspidalCharExistsOfGreen.lean:17–58`) identifies $U_{a,d-a}$ with the matrices summed
in `res a (d-a) τ_θ 1 1`. This step uses no regularity: every $\psi_s$ with $s$ additive is primitive.

*Step 5 (degree; `…/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:137–142`).* (I2) with
Lemma 13.4(1) gives $\psi_k(1) = \prod_{i\in[1,d)}(1 - g^i)$; multiply by $(-1)^{d-1} = \prod_{i \in [1,d)}(-1)$.

*Step 6 (elliptic values; `:143–157`).* If $\mathrm{charpoly}\,y$ is irreducible, Lemma 13.4(2) (through its
statement wrapper `T.invariantSubspaceMobiusInverseCharpoly_of_irreducible`, `:145`) gives
$\psi_k(y) = s_k(\mathrm{charpoly}\,y) = \sum_\alpha\theta_0(\alpha)^k$; by Lemma 13.4(3) applied to $\iota(z)$
(`:152`) the roots are $\iota(z)^{g^i}$ for $i < d$; and $\theta_0(\iota(z)^{g^i})^k = \lambda(z^{g^i})^k = \theta(z^{g^i})$.

*Step 7 (orbit equivalence; `:158–225`).* ($\Rightarrow$) If $\tau_\theta = \tau_{\theta'}$, cancelling the sign
gives $\psi_k = \psi_{k'}$ on $G$, where $k' = k(\theta')$. Pair both sides with $s_{k'} \circ \mathrm{charpoly}$ and
use (I4): $\#\{i < d : k g^i \equiv k'\} = \#\{i < d : k' g^i \equiv k'\} \ge 1$ (the term $i = 0$). So
$k g^i \equiv k' \pmod{g^d - 1}$ for some $i < d$, and $\theta' = \lambda^{k g^i} = \theta^{g^i}$ by Lemma 13.5(ii)
(`:184–205`). ($\Leftarrow$) If $\theta' = \theta^{g^i}$, then $k' \equiv k g^i$, and for every $l$ the sets
$\{i' < d : k' g^{i'} \equiv l\}$ and $\{i' < d : k g^{i'} \equiv l\}$ have the same size, because
$i' \mapsto (i' + i) \bmod d$ carries one onto the other (`pow_modEq_pow_mod`, `filter_modEq_congr`,
`card_filter_le_shift`, `card_filter_shift`, `:21–59`). So $\psi_k$ and $\psi_{k'}$ have the same Gram
coefficients against every $s_l$. Both are primitive class functions (I3), and in the expansion (I5) the
right-hand side depends on the function only through these coefficients; hence
$\lvert G\rvert\, d\, \psi_k(x) = \lvert G\rvert\, d\, \psi_{k'}(x)$ for invertible $x$ (`:206–225`). $\square$

**Lemma 13.7 (an injective labelling for the count).** [Lean, read] With $g, d, K$ as above there is a map
$c$ from $\mathbb F_g[X]$ to the characters of $K^\times$ such that $c(P)$ is regular whenever
`IsPrimeLab d P`, and $c(P') = c(P)^{g^i}$ with $i < d$ forces $P = P'$ for such $P, P'$
(`PrimeLabOrbit.primeLab_to_regularChar`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MonicIrreducibleInjectRegularCharacterOrbits.lean:125–151`,
helpers `:12–124`).

*Proof.* Fix an isomorphism $e : K^\times \cong \mathrm{Hom}(K^\times, \mathbb C^\times)$ (Mathlib's
`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`, `:131`; it exists because $K^\times$ is a finite
commutative group and $\mathbb C$ contains all roots of unity). For `IsPrimeLab d P` the field
$\mathbb F_g[X]/(P)$ has $g^d$ elements, so it is isomorphic to $K$ and $P$ has a root $u \in K^\times$
(`exists_unit_root`, `:81–101`); set $c(P) := e(u)$. Its conjugates $u^{g^i}$, $i < d$, are distinct, since
$u^{g^m} = u$ with $0 < m$ makes $P \mid X^{g^m} - X$ and forces $d \le m$ (`le_of_dvd`, `orbit_regular`,
`:60–75`, `:103–124`); as $e$ is a group isomorphism, $c(P)$ is regular. If $c(P') = c(P)^{g^i}$ then the
root $u'$ of $P'$ equals $u^{g^i}$, a root of $P$, so $P = \mathrm{minpoly}(u') = P'$. $\square$

The isomorphism $e$ is not canonical; these labels serve only the count below. The canonical labelling by
roots and the Teichmüller datum of `LabelDatum` is made afterwards by `green_of_regular` (Proposition 13.1).

**Proposition 13.8 (the direct consumer `greenRegularCharacters_holds`: exhaustion by counting).**
[Lean, read], conditional on Proposition 13.6 and (I9). `GlobalTheory.Published.GreenRegularCharacters`
holds: for every prime $g$, every $d > 0$ and every $K$ as above, the $\tau$ of Proposition 13.6 also has
the property that every $\chi : \mathrm{GL}_d(\mathbb F_g) \to \mathbb C$ with `IsCusp χ` equals $\tau_\theta$ for
some regular $\theta$. Citations are to
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProof.lean`.

*Proof.* *Step 1 (labels in every degree; `family`, `:23–33`, and `:141–159`).* For each $e > 0$ choose a
field $K_e$ of degree $e$ (the given $K$ if $e = d$, `GaloisField g e` otherwise), take $\tau^{(e)}$ from
Proposition 13.6 for $K_e$ (`:139`, `:156`) and $c$ from Lemma 13.7 (through its statement wrapper
`T.monicIrreducible_inject_regularCharacterOrbits`, `:30`), and set $L_e(P) := \tau^{(e)}(c(P))$. When
`IsPrimeLab e P`, $L_e(P)$ is cuspidal and equals some $\tau^{(e)}_\theta$ with $\theta$ regular; and
$L_e(P) = L_e(P')$ forces $c(P') = c(P)^{g^i}$ (Proposition 13.6(4)) and then $P = P'$ (Lemma 13.7). For
$e = 0$ no polynomial qualifies (`isPrimeLab_pos`, `:18–21`).

*Step 2 (the count; `count`, `:56–131`).* Suppose $\chi$ is cuspidal on $\mathrm{GL}_d(\mathbb F_g)$ and differs
from every $L_d(P)$. Let $T$ be the set of monic $f$ of degree $d$ with $f(0) \neq 0$. Then
$\lvert T\rvert = g^d - g^{d-1}$ (`:71–72`): the $g^d$ monic polynomials of degree $d$ minus the $g^{d-1}$ of
the form $X h$ (statement `T.ncard_monic_natDegree_coeff_zero_ne_zero`, proved by
`GrPolys.card_monic_coeff_zero_ne_zero`,
`…/InertiaEigenvalues/NcardMonicNatDegreeCoeffZeroNeZero.lean:8–63`). Each monic irreducible factor $P$ of
$f \in T$ has $P(0) \neq 0$, so satisfies `IsPrimeLab` (`factor_lab`,
`…/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProof.lean:35–46`), and the factors multiply back
to $f$ (`prod_factors`, `:48–54`). Send $f$ to the multiset $F(f)$ of pairs $\langle \deg P, L_{\deg P}(P)\rangle$
over its factors. $F$ is injective on $T$: map each pair back through the inverse of
$P \mapsto \langle\deg P, L(P)\rangle$ and multiply (`:62–83`). The singleton $\{\langle d, \chi\rangle\}$ is not
of the form $F(f)$, for otherwise $f$ would have a single factor $P$ of degree $d$ with $L_d(P) = \chi$
(`:84–103`). So $\{\{\langle d, \chi\rangle\}\} \cup F(T)$ consists of $g^d - g^{d-1} + 1$ distinct multisets of
cuspidal characters of total degree $d$ (`:104–130`), contradicting (I9) (`:125, 131`).

*Step 3 (`:160–168`).* If no regular $\theta$ had $\chi = \tau_\theta$, then $\chi \neq L_d(P)$ for every
$P$ (each $L_d(P)$ is some $\tau_\theta$), and Step 2 gives a contradiction. $\square$

In Example 13.3 ($g = 3$, $d = 2$) the count reads as follows. $T$ has $3^2 - 3 = 6$ elements: the three
irreducible labels give the singletons $\{\langle 2, \tau\rangle\}$ for the three cuspidal characters
$\tau_1, \tau_2, \tau_5$, and the three products $(X - a)(X - b)$ with $a, b \in \mathbb F_3^\times$ give the
three multisets of two characters of $\mathrm{GL}_1(\mathbb F_3) = \mathbb F_3^\times$. A fourth cuspidal
character of $\mathrm{GL}_2(\mathbb F_3)$ would give a seventh multiset, against the bound $6$ of (I9).

Together with Proposition 13.1, Propositions 13.6 and 13.8 give the whole Green node `P16` on the main path,
with its two hard inputs isolated: virtuality of $s_k \circ \mathrm{charpoly}$ (I6) and the count of
cuspidal multisets (I9).

**Remarks 13.4.4.**

1. *Green's Theorem 1 and Brauer.* [Green1955, pp. 403–404, Theorem 1] states: if $x \mapsto R(x)$ is a
   representation of a finite group by nonsingular $n \times n$ matrices over a finite field $\mathfrak F^\ast$
   that contains the latent roots $\xi_1(x), \dots, \xi_n(x)$ of every $R(x)$, if $\theta : a \mapsto a_\theta$ is
   any homomorphism of the multiplicative group of $\mathfrak F^\ast$ into that of $\mathbb C$, and if $S$ is a
   symmetric polynomial with rational integer coefficients, then $x \mapsto S(\xi_1(x)_\theta, \dots, \xi_n(x)_\theta)$
   is a character. Green's "character" allows virtual characters (p. 437: "the degree of a character
   $\chi$ of $\mathfrak G$ (even if $\chi$ is not a proper character)"), and his proof rests on Brauer's
   characterisation of characters (p. 403, and §3, pp. 413–415). Input (I6) is the case $R$ = the natural
   representation of $\mathrm{GL}_n(F)$, $S$ = the power sum $t_1^k + \dots + t_n^k$, and the archive's proof
   file also imports a Brauer-type induction package. Green fixes $\theta$ as an isomorphism of the
   multiplicative group of $\mathfrak F^\ast = \mathrm{GF}(q^{n!})$ into that of $\mathbb C$ (p. 415); the
   archive's $\theta_0$ is a multiplicative map on the whole algebraic closure, injective on nonzero elements.
2. *Normalization.* Green's $J_d(k) = I_d^k[1]$ has degree $J_d(k)(1) = \varphi_{d-1}(q)$ (p. 437), where
   $\varphi_r(t) = (1 - t)(1 - t^2)\cdots(1 - t^r)$ (Definition 2.2, p. 409). It vanishes off the primary
   classes, and on a primary class $(f^\lambda)$ it equals
   $k(\lambda, q^{d(f)})\{\theta^k(\gamma) + \theta^{qk}(\gamma) + \cdots + \theta^{q^{d(f)-1}k}(\gamma)\}$ for a root
   $\gamma$ of $f$ (p. 431). The degree of $I_s^k[\lambda]$ has the sign of $(-1)^{(s-1)v}$ (Lemma 7.5, p. 438),
   and $\lVert I_s^k[\lambda]\rVert = 1$ if $k, kq, \dots, kq^{s-1}$ are $s$ distinct residues modulo $q^s - 1$
   (Lemma 7.6, p. 438). The archive's $\psi_{s_k}$ has the same degree $\varphi_{d-1}(q)$ (input (I2)), and on
   elements with irreducible characteristic polynomial its value is the root sum
   $\theta^k(\gamma) + \theta^{qk}(\gamma) + \cdots + \theta^{q^{d-1}k}(\gamma)$ that appears in Green's display.
   The factor $(-1)^{d-1}$ in $\tau_\theta$ is the sign that makes the degree $\prod(q^i - 1)$ positive, and the
   archive's regularity hypothesis is Green's condition of Lemma 7.6 (Lemma 13.5). For $d = 2$ the two
   functions agree on every class [Expository]. Green writes a uniform function on $\mathrm{GL}_2$ through
   two principal parts, $U(c_1) = (q + 1)U'(\alpha, \alpha)/2 + (1 - q)U''(\alpha)/2$,
   $U(c_2) = U'(\alpha, \alpha)/2 + U''(\alpha)/2$, $U(c_3) = U'(\alpha, \beta)$, $U(c_4) = U''(\eta)$ on the
   scalar, Jordan, split and elliptic classes (p. 404). By Example (ii) (pp. 430–431) the principal parts
   of $J_2(k)$ are $0$ for the partition $\{1^2\}$ and $T_{2,1}(k : \eta) = \theta^k(\eta) + \theta^{qk}(\eta)$ for the
   partition $\{2\}$. Reading these as $U'$ and $U''$ (Green's footnote on p. 404 says the general notation
   of Definition 4.12 differs slightly; we did not read Definition 4.12), $J_2(k)$ takes the values
   $(1 - q)\theta^k(\alpha)$, $\theta^k(\alpha)$, $0$, $\theta^k(\eta) + \theta^{qk}(\eta)$, and its degree $1 - q$ agrees with
   p. 437. The recursion of Example 13.3(2), run over $\mathbb F_q$ (a scalar matrix has $q + 1$ invariant
   lines), gives the same four values for $\psi_{s_k}$. For $d \ge 3$, whether $\psi_{s_k}$ agrees with
   $J_d(k)$ off the elliptic classes is neither stated nor needed in the archive, and we leave it [Open].
3. *Field and characteristic.* Green works over $\mathrm{GF}(q)$ for every prime power $q$ (§1, p. 405). The
   archive's general layer (Definition 13.3 and inputs (I2)–(I8)) is stated for every finite field $F$ with
   $q = $ `Nat.card F` (for example `…/CharacterTheory/IsCharacterCuspidalRootSumRegularStatement.lean:7`). The
   restriction to prime fields $\mathbb F_g = \mathbb Z/g\mathbb Z$ enters only when Proposition 13.6
   instantiates $F := \mathbb Z/g\mathbb Z$, as the statement of `GreenRegularCharacters` and
   `Gn g n = GL (Fin n) (ZMod g)` (`…/NonGaloisDescent/LabelDatum.lean:11`) require. No further condition on
   $g$ is used on this path; the hypothesis $5 \le p$ of `isCuspOf_cuspOn_of_green`
   (`…/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:154`), a theorem in the same file as
   `isCusp_psi`, belongs to a different statement. The community statement-fidelity table classifies
   `GreenRegularCharacters` as a special case, "Green's cuspidal characters of GL_d(𝔽_q), only for q = p
   prime" (`LUMI doc 07`, review row R2 #14, an AI statement reading that the page marks as not checked
   against the sources; copy of 2026-11-23, see `sources/SOURCES.md`) [Community]; the reading above shows
   where that restriction enters.
4. *What the route avoids, and where the difficulty went.* In the files read, neither Deligne–Lusztig
   induction nor Green's $S$-functions and degeneracy rule appear. Cuspidality comes from the Möbius
   inversion (I3), irreducibility from a norm computation (I4)–(I5) plus virtuality (I6)–(I7), and
   exhaustion from counting (I9). Section 13.4.5 reads the supply of (I6) conditional on its named lifting inputs, Section 13.4.8 reads the (I9) producers, and Section 13.4.9 reads (I1) and its label-transport bridges at their stated conditional depths.
5. *Other readers of the producer.* Besides the two main-path read sites of the Motivation,
   `PM.greenRegularCharacters` is called directly in the partial local Langlands construction (`nameLaws`,
   `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/NameLaws.lean:81`,
   Chapter 12). The bundle `UnitaryGroupThirdPlaceHypotheses` also carries `greenCuspidal : GreenCuspidal`,
   filled by a separate proof `PositivityTheory.Stage1.PM.greenCuspidal`
   (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:397–398, 668`).
   Both production chains and their actual downstream consumers are read in [§13.4.12](#13412-naming-laws-pmgreencuspidal-and-label-well-definedness-across-consumers) [Lean, read].

**Table 13.4.4 (source-to-text map).**

| Archive declaration | File:line (`lean/`) | Used in | Level |
|---|---|---|---|
| `green_regular_characters_of_literature`, `published_results_eigen`, field `greenRegularCharacters`, `every_character_of_literature_of_vWin` | `…/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:399–400, 666, 694, 810–813` | Motivation | [Lean, read] |
| `every_character_of_theta_integrals_local_matching` (read of `P.greenRegularCharacters`) | `…/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69–73` | Motivation | [Lean, read] |
| `topCovolSlim2_use_alt_alt` (read of `greenRegularCharacters_holds` in the argument `hX`) | `…/ThirdPlaceSeries/TopCovolSlim2Use.lean:16–18`; call at `…/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:812` | Motivation | [Lean, read] |
| `PM.greenRegularCharacters`, `greenCuspidalCharsByRegularChars_proof`, `exists_cuspidalCharacter_of_regularCharacter_GLn` | `…/StandardTheoremStatements/GreenRegularCharacters.lean:5–6`; `…/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProofStatement.lean:8–9`; `…/ExistsCuspidalCharacterOfRegularCharacterGLnStatement.lean:8–9` | Motivation | [Lean, read] |
| `psi`, `psi_eq`, `rootSum`, `IsAdditive`, `IsPrimitive`, `nilRad`, `ipGL`, `glCard`; `BI.IsChar`, `BI.Virt` | `…/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:11–93`; `…/CommutativeAlgebra/AbByPOfComm.lean:5–12` | Definition 13.3 | [Lean, read] |
| `rootSum_isAdditive_and_pow_X_sub_one`, `psi_of_irreducible_charpoly`, `GreenExists.rootsBar_eq`, `IsPrimitive.finsum_unipotentRadical_eq_zero` | `…/CharacterTheory/RootPowerSumCharacterAdditiveAndXSubOnePow.lean:9–20`; `…/InvariantSubspaceMobiusInverseCharpolyOfIrreduci.lean:7–56`; `…/InertiaEigenvalues/CuspidalCharExistsOfGreen.lean:17–94`; `…/CharacterTheory/FinsumUnipotentRadicalEqZero.lean:10–26` | Lemma 13.4 | [Lean, read] |
| `GreenRegular.exists_cusp_of_regular` and shift lemmas | `…/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:21–225` | Lemma 13.5, Proposition 13.6 | [Lean, read] |
| `CuspGL.isChar_psi_rootSum_of_regular` (with `psi_rootSum_charpoly_mem_virt`) | `…/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean:19–184` | Proposition 13.6, Steps 1–3 | [Lean, read] |
| `ParamLabel.isCusp_psi` | `…/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18–48` | Proposition 13.6, Step 4 | [Lean, read] |
| `PrimeLabOrbit.primeLab_to_regularChar` | `…/InertiaEigenvalues/MonicIrreducibleInjectRegularCharacterOrbits.lean:12–151` | Lemma 13.7 | [Lean, read] |
| `greenRegularCharacters_holds`, `family`, `factor_lab`, `prod_factors`, `count`; `GrPolys.card_monic_coeff_zero_ne_zero` | `…/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProof.lean:18–168`; `…/NcardMonicNatDegreeCoeffZeroNeZero.lean:8–63` | Proposition 13.8 | [Lean, read] |
| inputs (I2)–(I3) and (I8) (with (I1), (I4)–(I5), and (I7) read conditionally in §§13.4.9, 13.4.6, and 13.4.7, and (I2) and (I8) read in §13.4.10): `T.*` statement wrappers and the `CuspGL`/`BI`/`ParabVirt` lemmas they name | files listed with (I1)–(I8) before Proposition 13.6 | Propositions 13.6 and 13.8 | [Lean] statement; for (I2) and (I8) see Table 13.4.10; other unread deeper proofs [Open] |
| `FDRep.simple_iff_char_is_norm_one` (Mathlib) | `Mathlib/RepresentationTheory/FinGroupCharZero.lean:121` (commit `0df444a`) | Proposition 13.6, Step 4 | [Lean] (Mathlib; statement and proof read in §13.4.10) |

---

### 13.4.5 Why lifted power sums are virtual characters

**Motivation.** Lifting the eigenvalues of a finite-field matrix to complex roots of unity and adding their powers gives a class function. In (I6) we need its coefficients in the irreducible-character basis to be integers, so that we can subtract virtual characters in the Möbius recursion.

**Example 13.9 (positive degree and a negative multiplicity).** Let $G=\mathrm{GL}_2(\mathbb F_3)$ and let $S_4(g)$ be the sum of fourth powers of its two lifted eigenvalues under an injective multiplicative lift. The action on the four lines of $\mathbb F_3^2$ identifies $\mathrm{PGL}_2(\mathbb F_3)$ with $\mathfrak S_4$. A matrix fixing every line is scalar, and the quotient has order $(9-1)(9-3)/2=24$.

For split characteristic polynomials the fourth powers both equal $1$. Scalars act trivially, nonscalar repeated-root matrices act projectively with order three, and distinct roots in $\mathbb F_3$ give two fixed lines and a transposition. For an irreducible polynomial the roots are $z^a,z^{3a}$ with $z$ a generator of $\mathbb F_9^\times$ and $a\notin\{0,4\}$ modulo $8$. Since the lift of $z$ has order eight, both fourth powers equal $(-1)^a$. Multiplication by $z^a$ on $\mathbb F_9$ fixes no line and has projective order equal to the order of $a$ modulo four. Even $a$ gives a double transposition and odd $a$ a four-cycle.

Let $T$ be the character of the sum-zero subspace of the complex permutation representation on the lines, and let $\epsilon$ be the sign of the action.

| Cycle type | $1^4$ | $2\,1^2$ | $2^2$ | $3\,1$ | $4$ |
| --- | ---: | ---: | ---: | ---: | ---: |
| Class size in $\mathfrak S_4$ | 1 | 6 | 3 | 8 | 6 |
| $S_4$ | 2 | 2 | 2 | 2 | $-2$ |
| $T$ (fixed lines minus one) | 3 | 1 | $-1$ | 0 | $-1$ |
| $\epsilon$ | 1 | $-1$ | 1 | 1 | $-1$ |

Thus $S_4=1+\epsilon+T-\epsilon T$. The norm squared of $T$ is $(9+6+3+0+6)/24=1$. Hence $T$ and its sign twist are irreducible and they differ on a transposition. Pullback along the surjection preserves irreducibility and distinctness. Both have degree three, so they are distinct from the two displayed linear characters. The coefficient $-1$ of $\epsilon T$ precludes a genuine character even though $S_4(1)=2$.

**Definition 13.4.** For a finite group $G$ let $R(G)$ be the additive subgroup of complex functions generated by genuine representation characters. Complete reducibility and character orthogonality identify it with the integer span of the irreducible characters. Tensor products give pointwise multiplication, and restriction, pullback along a group homomorphism, and induction preserve virtuality by the corresponding operations on representations. Call $E\le G$ *admissible* here if $E/Z(E)$ is an $\ell$-group for some prime $\ell$. Equivalently, for a single prime $\ell$ each $y\in E$ has an $\ell$-power $y^{\ell^j}$ in the center. The archive's `AbByP` replaces the center by an abelian normal subgroup. Admissibility implies `AbByP`, which passes to subgroups by intersection with the chosen normal subgroup.

**Lemma 13.10 (induction and the unit).** Let $A$ consist of the functions $\operatorname{Ind}_E^G v$ with $E$ admissible and $v\in R(E)$. Then $1$ belongs to the integer span of $A$. Consequently a class function $\chi$ belongs to $R(G)$ if its restrictions to all admissible subgroups are virtual.

*Proof.* First construct an integer-valued witness for each $x\in G$ and prime $\ell$. Write $x=cu=uc$ with $c,u$ powers of $x$, the order $m$ of $c$ prime to $\ell$ and the order of $u$ an $\ell$-power. Such powers follow from the Chinese remainder theorem in $\langle x\rangle$. Put $Z=C_G(c)$ and choose a Sylow $\ell$-subgroup $P$ of $Z$ containing $u$. Then $E=\langle c\rangle\times P$ is admissible. Choose an integer $a\equiv 1$ modulo $m$ and $a\equiv 0$ modulo $|P|$. On $E$, $e\mapsto e^a$ is projection onto $\langle c\rangle$. Choose a primitive $m$th root $\zeta$ and the linear character $\lambda$ sending $c$ to $\zeta$ and trivial on $P$. The geometric sum $\sum_{j=0}^{m-1}\zeta^{-j}\lambda(e)^j$ equals $m$ if $e^a=c$ and zero otherwise. By the induction formula, the function $f=\sum_j\zeta^{-j}\operatorname{Ind}_E^G(\lambda^j)$ has value $|D_g|/|P|$ at $g$, where
$$D_g=\{t\in G:t^{-1}gt\in E,\ (t^{-1}gt)^a=c\}.$$
Indeed the sum over $t$ has normalization $1/|E|=1/(m|P|)$. Right multiplication by $P$ preserves $D_g$ since $P$ centralizes $c$, so $f(g)$ is an integer. At $g=x$, the power condition forces $t\in Z$ because $x^a=c$. The remaining condition is $t^{-1}ut\in P$. Thus $f(x)$ counts fixed cosets for $\langle u\rangle$ on $Z/P$, and is congruent to $[Z:P]$ modulo $\ell$ by orbit sizes. This is nonzero modulo $\ell$. The coefficients of $f$ in the displayed induced sum are algebraic integers.

Now for any class function $\phi$,
$$\operatorname{Ind}_E^G(v)\phi=\operatorname{Ind}_E^G(v\,\phi|_E).$$
Every contributing term in the induction sum evaluates $\phi$ on a conjugate of $g$, so the common factor $\phi(g)$ can be taken out. In particular $A$ is multiplicatively closed. Let $J$ be its span over the complex algebraic integers and $B=J\cap\mathbb Z^G$. Both are closed under pointwise multiplication. The value subgroup $B(x)\le\mathbb Z$ is all of $\mathbb Z$ since the witnesses show that no prime divides its generator. Choose $f_x\in B$ with $f_x(x)=1$. The expression $1-\prod_{x\in G}(1-f_x)$ lies in $B$ by induction, starting with zero and changing the current expression $b$ to $b+f_x-bf_x$. The product vanishes at each point, so $1\in J$.

Write $1=\sum_i r_i a_i$ with $r_i$ algebraic integers and $a_i\in A$. In the additive group $M$ generated by $1$ and the $r_i$, the quotient $M/\mathbb Z$ is torsion-free because a rational algebraic integer is an integer. It is finitely generated, hence free. Lifting a basis furnishes an additive retraction $M\to\mathbb Z$ fixing $1$. Let $c_i\in\mathbb Z$ be the images of $r_i$. Put $b=\sum_i c_i a_i-1$. Since $b,a_i,1$ are virtual, $m_i=\langle a_i,b\rangle$ and $d=\langle 1,b\rangle$ are integers. The inner product is linear in its first argument. Pairing the original relation with $b$ gives $\sum_i r_i m_i=d$. Retraction gives $\sum_i c_i m_i=d$, whence $\langle b,b\rangle=0$ and $b=0$. This proves $1=\sum_i c_i a_i$ in the integer span. Multiplying this relation by $\chi$ shows $\chi\in R(G)$ since each term $a_i\chi$ is virtual by the projection formula and the restriction hypothesis. $\square$

**Proposition 13.11 (the virtuality input (I6)).** Let $F$ be a finite field of characteristic $p$, let $n,k\ge 0$, and let $\theta:\overline F\to\mathbb C$ be a multiplicative monoid homomorphism injective on nonzero elements. For $g\in\mathrm{GL}_n(F)$ put $S_k(g)=\sum_\alpha\theta(\alpha)^k$, summing over the roots of the characteristic polynomial in $\overline F$ with multiplicity. Then $S_k\in R(\mathrm{GL}_n(F))$, conditional in this reading on two named inputs.

1. **Monomial basis.** Over an algebraically closed field $K$, every finite-dimensional representation of a finite `AbByP` group $H$ with $|H|\ne 0$ in $K$ has a basis which each group element permutes up to scalar. This is `CuspGL.exists_monomial_basis_of_abByP` [Lean]/[Open].
2. **Trace comparison.** For a monomial matrix $M$ over $K$, form $M_\theta$ by lifting its nonzero entries, where $\theta:K\to\mathbb C$ satisfies the same multiplicativity and injectivity assumptions. If $M^N=M_\theta^N=1$ and $N\ne 0$ in $K$, then $\operatorname{tr}(M_\theta)$ equals the sum of lifted eigenvalues of $M$, with multiplicity. This is `MonoTrace.trace_lift_monomial` [Lean]/[Open].

*Proof.* Take an admissible subgroup $E$ and its prime $\ell$. An element of order prime to $\ell$ is central because it is a power of its own central $\ell^j$th power. For a Sylow $p$-subgroup $Q$ of $E$, if $\ell=p$, the index of $Z(E)Q$ divides both $[E:Z(E)]$ and $[E:Q]$, which are coprime. Thus $E=Z(E)Q$ and $Q$ is normal. If $\ell\ne p$, $Q$ is central and again normal. Schur–Zassenhaus gives a complement $H$ of order prime to $p$. The two factors commute because $H$ is central in the first case and $Q$ is central in the second. The quotient $E/Q$ identifies with $H$, giving a homomorphism $\pi:E\to H$.

Write $g=\pi(g)s$ with $s\in Q$, and choose $m$ with $s^{p^m}=1$. Then $g^{p^m}=\pi(g)^{p^m}$. Over $K=\overline F$, the multiset of roots of a matrix power is obtained by raising the original roots individually to that power, as is seen in a triangular basis. Raising to $p^m$ is injective on $K$, so the original root multisets coincide. Base extension simply maps the characteristic polynomial into $K[X]$. Hence $S_k|_E=(S_k|_H)\circ\pi$.

The group $H$ has `AbByP` and order invertible in $K$. Apply input 1 to the base-changed representation on $H$. Write $h b_i=c(h,i)b_{\sigma_h(i)}$ with nonzero $c(h,i)$. Invertibility makes $\sigma_h$ a permutation. Composition gives $\sigma_{ht}=\sigma_h\sigma_t$ and $c(ht,i)=c(h,\sigma_t(i))c(t,i)$. Applying $\theta$ preserves these identities and the identity matrix, producing a complex representation $\rho$. Both the original and lifted matrices have $|H|$th power the identity, so input 2 gives $\operatorname{tr}\rho(h)=S_1(h)$. Evaluating at $h^k$ and using the power rule on roots gives $S_k(h)=\operatorname{tr}(\rho(h)^k)$.

Let $P_r$ be the $r$th power sum of the complex roots of $\rho(h)$ as a function of $h$ and $e_i$ their elementary symmetric functions. Each $e_i$ is the character of the $i$th exterior power, represented in the archive by the compound matrix. In a triangular basis its trace sums products over $i$ distinct diagonal indices. This includes $e_0=1$ and $e_i=0$ above the dimension. Also $P_0=\dim(\rho)\,1$. Comparing coefficients in $tE'(t)=E(t)\sum_{r\ge1}(-1)^{r-1}P_rt^r$ for $E(t)=\prod_j(1+\alpha_j t)$ gives
$$P_r=(-1)^{r+1}r e_r-\sum_{0<i<r}(-1)^i e_iP_{r-i}\qquad(r>0).$$
Induction in $r$ using the ring operations in $R(H)$ gives $P_k\in R(H)$. The pullback along $\pi$ gives $S_k|_E\in R(E)$. This holds for every admissible $E$. Since conjugation preserves the characteristic polynomial, $S_k$ is a class function and Lemma 13.10 applies. $\square$

**Remarks.**

1. The restrictions in the global test are to subgroups with prime-power central quotient. Its witnesses come from the elementary subgroups $\langle c\rangle\times P$. Cyclic subgroups enter in the element decomposition and the geometric sum. Cyclic restrictions alone are insufficient in general. On $C_2\times C_2$, half the regular character restricts on each order-two subgroup to its regular character, yet its four global irreducible coefficients are all $1/2$.
2. Algebraic integrality is used for the coefficients of the induced linear characters. Integer inner products of **already virtual** characters descend the unit relation. The values of $S_k$ are themselves algebraic integers because the lifted eigenvalues are roots of unity. Pointwise integrality plays no role in the global test, and the proof does not compute the inner products of $S_k$ with individual irreducibles.
3. Green proves a symmetric-function result, invoking Brauer's characterization via elementary subgroups. Green cites Brauer’s 1953 paper for that characterization [Paper]. Its original proof stays [Open] in this reading. Green's characteristic-zero lifting on a group of order prime to $p$ and the deletion of the $p$-part in equation (5) serve the corresponding local purpose. The archive uses a monomial basis and a trace comparison, and obtains the global test by proving the induced-unit identity above. This comparison concerns virtuality. [Green 1955, pp. 403–404 and §3, pp. 413–415](https://doi.org/10.1090/S0002-9947-1955-0072878-2).
4. In Proposition 13.6, Step 1, (I6) supplies exactly the unsigned first term of the subtraction. After rewriting with `heq`, `psi_rootSum_charpoly_mem_virt` uses `rootSum_charpoly_mem_virt F θ hθ d k` as the first argument of `sub_mem` at line 84. For the second argument, line 86 applies (I7) with the induction hypothesis in dimension $a<d$. Line 125 uses the resulting auxiliary virtuality inside `isChar_psi_rootSum_of_regular`. The `T` wrapper exposes the same statement, and line 84 calls the producer directly. The inputs are $n=d$ and the same $\theta,k$. The regularity and sign conditions belong to subsequent steps.

**Source map.** All paths are relative to the unpacked archive pinned by `lean.tar.gz` SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The hand calculation is [Expository]. The R3 reading of the archive is conditional at the depth marked below.

| Role | Archive path and lines | Reading |
| --- | --- | --- |
| `IsChar`, `Virt`, `ind`, `AbByP` | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/AbByPOfComm.lean:5–25` | Definitions |
| `rootSum` | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:65–66` | Definition |
| Virtual-character operations and projection formula | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharactersMulComapConjIndLinear.lean:62–108` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IndMulClassFunEqIndMulRestrict.lean:9–21` | [Lean, read] |
| Local witness | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsInducedIntPrimeTo.lean:68–351` | [Lean, read] |
| Integer-valued unit, descent and induced unit | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemOfMulMemOfForallPrimeNotDvd.lean:5–44`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemVirtualCharactersOfIntegralCombination.lean:9–53` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/OneMemClosureInducedCentralByPrimePower.lean:13–67` | [Lean, read] |
| Monomial lift and trace interface | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterBrauerLiftAbelianByPrimePower.lean:10–74` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MatrixTraceIffIsCharacterOverSubfieldComplex.lean:7–28` | [Lean, read] conditional on inputs 1 and 2 |
| Monomial basis and trace comparison | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsMonomialBasisAbelianByPrimePower.lean:39` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/TraceLiftMonomialMatrixEqSumEigenvalues.lean:42` | [Lean]/[Open], inputs 1 and 2 |
| Compound characters, power maps on roots and Newton identity | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterEsymmRootsCharpoly.lean:10–83`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootsCharpolyPowEqMapPow.lean:10–79` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MultisetPowerSumNewtonIdentity.lean:8–37` | [Lean, read] |
| Local splitting, Newton recursion and global virtuality | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharpolyMemVirtualCharactersGL.lean:14–233` | [Lean, read] conditional as above |
| `T.rootPowerSum_charpoly_mem_virtualCharacters_GL` and direct use of (I6) | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharpolyMemVirtualCharactersGLStatement.lean:7–8` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean:55–88` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean:125` | Wrapper and call sites |

The Lean bodies behind `T.exists_int_relation_of_isIntegral_relation` (`src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIntRelationOfIsIntegralRelationStatement.lean:7–8`) and `T.virtualCharacter_inner_eq_int_mul_card` (`src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterInnerEqIntMulCardStatement.lean:7–8`) stay [Lean]/[Open] at statement level. Lemma 13.10 gives the corresponding retraction and orthogonality proofs in prose. The new R3 reading covers the mapped proof bodies supplying (I6).

### 13.4.6 The Gram matrix and Fourier expansion of primitive class functions

The invariant-subspace recursion supplies a function on every endomorphism of a finite vector space. Its pairings on the invertible elements serve two purposes. They measure the size of the function, and they determine whether two labels give the same function on the group. The production proof goes through characteristic-polynomial fibers and then through Fourier analysis on a single finite-field torus.

**Example (rank two, by hand) [Expository].** Take $F=\mathbb F_3$, $K=F[i]$ with $i^2=-1$, and $z=1+i$. Since $z^2=-i$ and $z^4=-1$, $z$ generates $K^\times$. Write $\omega=\theta(z)$, a primitive eighth root. Let $R_k$ be the sum of the $k$th powers of the lifted roots and let $\psi_k$ be its invariant-subspace inverse. On a line with eigenvalue $a$ this inverse is $\theta(a)^k$. In rank two the recursion subtracts one such term per invariant line.

| Type | Class size (per label) | $R_k$ | $\psi_k$ |
|---|---:|---|---|
| Scalar $aI$, two choices | 1 | $2\theta(a)^k$ | $-2\theta(a)^k$ |
| One Jordan block with eigenvalue $a$, two choices | 8 | $2\theta(a)^k$ | $\theta(a)^k$ |
| Distinct eigenvalues $1,-1$ | 12 | $1+(-1)^k$ | $0$ |
| Irreducible characteristic polynomial, $j=1,2,5$ | 6 | $\omega^{jk}+\omega^{3jk}$ | $\omega^{jk}+\omega^{3jk}$ |

There are four, one, two and zero invariant lines in the four rows. The centralizers have orders $48$, $3(3-1)$, $(3-1)^2$ and $3^2-1$ respectively. In the last case a commuting map is multiplication by an element of $K$, since the matrix generates the field algebra. The class sizes sum to $48$. The last row labels are representatives of the exponent pairs $(1,3),(2,6),(5,7)$.

Put $t_k(j)=\omega^{jk}+\omega^{3jk}$. The scalar and Jordan contributions to the unnormalized mixed pairing are $(-2+8)2\theta(a)^k\overline{\theta(a)^l}$ for each $a$. At $j=0,4$ this is $3t_k(j)\overline{t_l(j)}$. Each irreducible pair contributes $6t_k(j)\overline{t_l(j)}$, or $3$ times the summand at each of its two roots. Thus the pairing is $3\sum_{j=0}^7 t_k(j)\overline{t_l(j)}$. Summing the four geometric series gives $48(\mathbf 1_{k=l}+\mathbf 1_{3k=l})$, with labels taken modulo eight. Here $\theta(-1)=\omega^4=-1$. The same answer holds for the self-family pairing: the scalar and Jordan contributions there are $(4+8)\theta(a)^k\overline{\theta(a)^l}$. In the order $0,1,2,3,4,5,6,7$, the **normalized Gram matrix** is

$$
\begin{pmatrix}
2&0&0&0&0&0&0&0\\
0&1&0&1&0&0&0&0\\
0&0&1&0&0&0&1&0\\
0&1&0&1&0&0&0&0\\
0&0&0&0&2&0&0&0\\
0&0&0&0&0&1&0&1\\
0&0&1&0&0&0&1&0\\
0&0&0&0&0&1&0&1
\end{pmatrix}.
$$

Multiply by $48$ for the archive pairing. The trivial torus character $k=0$ is nonregular. Both Frobenius indices fix it, so its normalized squared norm is $2$ and the norm-one input to the character argument is unavailable. The Gram formula and expansion still apply. Even this one label exhibits the role of the primary reducible fibers: the scalar and Jordan elements contribute $24$ to its squared norm before normalization.

In rank one over the same field, $\psi_0=R_0$ takes values $(1,1)$ on $(1,-1)$ and $\psi_1=R_1$ takes $(1,-1)$. The two sums of squares are $2$ and the cross sum is $1-1=0$. The unnormalized matrix is $2I_2$, and for $\varphi$ taking values $(u,v)$ the expansion is $2\varphi=(u+v)\psi_0+(u-v)\psi_1$. There are no proper nonzero subspaces and every invertible class is elliptic.

**Definitions.** Let $F=\mathbb F_q$, let $V$ be finite-dimensional, and put $G=\mathrm{GL}(V)$ and $E=\operatorname{End}_F(V)$. Write $P_x=\operatorname{charpoly}(x)$. For $A\subseteq V$, put $H_A=\{h\in E:h(V)\subseteq A,\ h(A)=0\}$. A function $\varphi:E\to\mathbb C$ is primitive if $\sum_{h\in H_A}\varphi(x+h)=0$ whenever $0<A<V$ and $xA\subseteq A$. Class invariance means invariance under $G$-conjugation on all of $E$. The mass $M_\varphi(P)$ sums $\varphi$ over all $x\in E$ with $P_x=P$. A polynomial function $s$ is additive if $s(PQ)=s(P)+s(Q)$ on monic factors. The recursion is
$\psi_s(V,x)=s(P_x)-\sum_{W<V,\ xW\subseteq W}\psi_s(W,x|_W)$.
Write $B(\varphi,\eta)=\sum_{x\in G}\varphi(x)\overline{\eta(x)}$ for the archive's $\mathrm{ipGL}$, linear in its first variable. The normalized Hermitian pairing is $B/|G|$. A conjugacy-class sum for $B$ has weight $|G|/|C_G(x)|$ per representative. A polynomial fiber sum can contain several such classes.

Given a multiplicative monoid map $\theta:\overline F\to\mathbb C$ injective on nonzero elements, let $s_k(P)=\sum_\alpha\theta(\alpha)^k$, over roots with multiplicity, $R_k(x)=s_k(P_x)$ and $\psi_k=\psi_{s_k}(V,\cdot)$. These are defined on $E$. Root multiset addition under monic multiplication makes $s_k$ additive. Transport by a linear isomorphism preserves the recursion, by induction on dimension and the bijection of invariant subspaces.

**Lemma (replacement in the pairing).** For additive $s$ and primitive $\varphi:E\to\mathbb C$, one has $B(\varphi,\psi_s)=B(\varphi,s\circ P)$ in every dimension. Here $s\circ P$ means $x\mapsto s(P_x)$.

*Proof.* For $W<V$, denote the summand of the recursion by $r_W(x)$, extended by zero when $W$ is not stable. The term for $W=0$ is zero since $s(1)=s(1)+s(1)$. For $0<W<V$, let $b(x)=\mathbf 1_G(x)\overline{r_W(x)}$. Translation by $h\in H_W$ preserves stability of $W$, and for stable $W$ it preserves the diagonal blocks of $x$, hence invertibility and restriction to $W$. Therefore $b(x+h)=b(x)$. Translation in the finite set $E$ gives
$|H_W|\sum_{x\in E}\varphi(x)b(x)=\sum_{x\in E}b(x)\sum_{h\in H_W}\varphi(x+h)=0$.
For stable $W$ the inner sum is zero by primitivity, and otherwise $b(x)=0$. The cardinality is positive because $0\in H_W$, and its complex cast is nonzero. This disposes of each correction term. Class invariance and positive ambient dimension are unnecessary for this identity. $\square$

**Proposition (Gram and expansion).** Suppose $d=\dim_F V>0$ and $\theta$ is as in the definitions. Set $N=q^d-1$ and $m_{kl}=\#\{0\le i<d:kq^i\equiv l\pmod N\}$. For all nonnegative integers $k,l$,
$B(\psi_k,R_l)=B(\psi_k,\psi_l)=|G|m_{kl}$.
For every primitive class function $\varphi$ on $E$ and every $x\in G$,
$$
|G|d\,\varphi(x)=\sum_{k=0}^{N-1} B(\varphi,R_k)\psi_k(x).
$$
The statement uses arbitrary finite fields and imposes no regularity condition on $k$. The injectivity of $\theta$ and the full endomorphism hypotheses on $\varphi$ are retained from the producers.

*Proof.* We develop the polynomial and Fourier steps in the order needed by the Gram calculation and the expansion.

**Primitivity of the inverse.** The archive's dimension induction can be seen by summing the recursion over $x+H_A$ for stable $A$. Subspaces contained in $A$ contribute $|H_A|s(P_{x|_A})$ in total. For subspaces disjoint from $A$, fix their image $U\subseteq V/A$. Only quotient-stable $U$ can occur. Its lifts disjoint from $A$ are graphs of maps $U\to A$ after a splitting. For each graph, stability prescribes the restriction of $h:V/A\to A$ to $U$, leaving $|H_A|/q^{\dim A\,\dim U}$ choices. These choices all induce the quotient action on the graph. Counting the $q^{\dim A\,\dim U}$ graphs and summing over $U$ gives $|H_A|s(P_{x_{V/A}})$. For a proper $W$ with $0<W\cap A<W$, the stabilizing translations, if nonempty, form an affine space. Restricting its direction space to $W$ surjects onto $\operatorname{Hom}(W/(W\cap A),W\cap A)$ by extension from the image of $W$ in $V/A$. The fibers have equal size and the smaller-dimensional primitivity sum is zero. The zero subspace contributes zero in both sums. Since $P_x=P_{x|_A}P_{x_{V/A}}$ and all translations have the same characteristic polynomial, the two surviving contributions cancel the leading term. This proves primitivity for additive $s$.

**Polynomial support and the torus.** The condition $P(0)\ne0$ makes the entire fiber invertible by the determinant formula. Thus $B(\varphi,R_l)$ first groups into $M_\varphi(P)\overline{s_l(P)}$ over monic $P$ of degree $d$ with $P(0)\ne0$. An empty fiber has mass zero.

If $P_x=f^m Q$ with $f$ monic irreducible, $m>0$, $Q$ nonconstant and coprime to $f$, choose $A=\ker f(x)^m$. Bézout and Cayley–Hamilton give the primary splitting with complementary kernel $\ker Q(x)$. Both summands are nonzero, since each irreducible divisor of $P_x$ divides every annihilating polynomial, as seen by evaluating on a corresponding eigenvector over a splitting field. On the off-diagonal space $H_A$, the map $u\mapsto ux-xu$ is injective. A commuting $u$ induces an intertwiner from $V/A$ into $A$, which is zero by Bézout for their coprime annihilators. The map is consequently surjective. As $u^2=uxu=0$, conjugation by $1+u$ sends $x$ to $x+ux-xu$. The primitive sum is therefore $|H_A|\varphi(x)$, forcing pointwise vanishing.

The remaining polynomials have the form $P=f^m$ with $f(0)\ne0$. This includes the elliptic classes where $f$ is irreducible of degree $d$ and $m=1$. There the fiber is a single class with centralizer of order $N$, and $\psi_k(x)=R_k(x)$ by the absence of proper nonzero invariant subspaces. The primary powers with $m>1$ retain their full fiber mass. For $T=\mathbb F_{q^d}^{\times}\subset\overline F$, let $f_\alpha$ be the minimal polynomial of $\alpha\in T$, $e_\alpha=\deg f_\alpha$ and $m_\alpha=d/e_\alpha$. The positive integer $e_\alpha$ divides $d$. The roots of $f_\alpha$ are the distinct points in its length-$e_\alpha$ Frobenius orbit. The fiber of $\alpha\mapsto f_\alpha^{m_\alpha}$ over $f^m$ consists precisely of the roots of $f$. Each root occurs $m$ times in $f^m$, so the grouped pairing becomes
$$
B(\varphi,R_l)=\sum_{\alpha\in T}m_\alpha M_\varphi(f_\alpha^{m_\alpha})\overline{\theta(\alpha)^l}.
$$
This is the torus identity for any primitive class function. In particular the torus includes subfield points. Excluding them would lose the primary powers.

**Computing the mass of the inverse.** For monic $P$ let $\mu(P)=M_1(P)/|\mathrm{GL}_{\deg P}(F)|$ in the space of dimension $\deg P$. Use convolution $(a*b)(P)=\sum_{DE=P}a(D)b(E)$ over ordered monic factors, and write $\mathbf 1$ for the constant function on monic polynomials. Counting invariant $W$ together with $x$ implements convolution. In dimensions $\deg D=a$, $\deg E=b$, the two diagonal blocks have polynomials $D,E$ and the off-diagonal block has $q^{ab}$ choices. The number of $a$-planes times $q^{ab}$ is $|\mathrm{GL}_{a+b}(F)|/(|\mathrm{GL}_a(F)||\mathrm{GL}_b(F)|)$ by the stabilizer formula. Thus for a transport-invariant family $\Phi(W,x|_W)$, the normalized mass of its sum over stable $W$ is the convolution of the normalized masses of $\Phi$ with $\mu$. All group orders are positive, including the order one in dimension zero.

Apply the same count with $\Phi$ equal to the number of cyclic vectors for the restriction. For each $x$ every vector generates one stable subspace on which it is cyclic, so the sum over stable subspaces is $q^{\deg P}$. For fixed monic $D$ of degree $a$, pairs $(y,v)$ with $P_y=D$ and $v$ cyclic are in bijection with bases $(v,yv,\ldots,y^{a-1}v)$, since $D$ specifies the last column. This gives normalized mass one, including the empty basis for $a=0$. Hence $\mu(1)=1$ and $\sigma\mu=\mathbf 1*\mu$, where $(\sigma b)(P)=q^{\deg P}b(P)$.

Define $\Lambda_s(f^m)=s(f)$ for monic irreducible $f$ and $m>0$, and set it to zero elsewhere. By unique factorization, $s=\Lambda_s*\mathbf 1$ on monic polynomials. Set $L(P)=\Lambda_s(P)/(q^{\deg P}-1)$ for positive degree and $L(1)=0$. This last value is the zero value used in the archive's totalized division. The multiplier $\sigma$ distributes over convolution and multiplication by $s$ obeys the Leibniz rule for convolution, because degrees and $s$ add on factors. Write $U=s\mu$ pointwise and $W=L*\mu$. Then
$$
\sigma U=(\Lambda_s*\mathbf 1)*\mu+\mathbf 1*U,\qquad
\sigma W=(\Lambda_s*\mathbf 1)*\mu+\mathbf 1*W.
$$
The second identity uses $\sigma L=L+\Lambda_s$. Both functions vanish at $1$. By induction on $\deg P$, the difference satisfies $(q^{\deg P}-1)(U-W)(P)=0$ for $\deg P>0$: in $\mathbf 1*(U-W)$ the other terms have smaller degree. Every such divisor is positive. The recursion and stable-subspace count give $U=A*\mu$ where $A$ is the normalized mass of $\psi_s$. Comparing with $L*\mu$ and isolating the term with second factor $1$ gives $A=L$ by degree induction, since $\mu(1)=1$. In particular
$$
M_{\psi_s}(f^m)=\frac{|G|}{q^d-1}\,s(f)\quad\text{when }\deg(f^m)=d.
$$

**Gram calculation.** Insert this mass in the torus identity for $\psi_k$. The factor $m_\alpha$ repeats each of the $e_\alpha$ roots exactly $d/e_\alpha$ times. Hence
$$
B(\psi_k,R_l)=\frac{|G|}{N}\sum_{i=0}^{d-1}\sum_{\alpha\in T}
  \theta(\alpha)^{kq^i}\overline{\theta(\alpha)^l}.
$$
The multiplicative group of $K=\mathbb F_{q^d}$ is cyclic of order $N$. The integer $N$ is nonzero in $F$ (its image is $-1$) and in $\mathbb C$ (it is positive). A generator maps under $\theta$ to a primitive $N$th root, since injectivity on $T$ preserves its order. Values on $T$ have modulus one. With generator image $\omega$, the inner sum is the geometric series with ratio $\omega^{kq^i-l}$. The ratio-one branch gives $N$ and the other branch divides by a nonzero $1-\omega^{kq^i-l}$ and gives zero. Cancelling $N$ proves the mixed Gram formula. The replacement lemma gives the self-family formula. For a label orbit of length $r$, each reachable label occurs $d/r$ times in the $d$ indices. This is a count on exponents modulo $N$, independent of the earlier orbit length $e_\alpha$ of a field element.

**Why the pairings determine a function.** Fourier inversion recovers each $m_\alpha M_\varphi(f_\alpha^{m_\alpha})$ from $B(\varphi,R_l)$. In fact, multiply the torus identity by $\theta(\beta)^l$ and sum over $0\le l<N$. The ratio $\theta(\beta)\overline{\theta(\alpha)}$ is one exactly when $\beta=\alpha$, by injectivity. Every other geometric sum is zero and the diagonal gives $N$. Thus zero pairings imply zero primary mass, since each admissible $f^m$ has a root in $T$ and the positive integer $m=d/\deg f$ has nonzero complex cast.

To pass from mass zero to pointwise zero on a primary fiber, first consider a primitive class function vanishing on that fiber's semisimple points, the endomorphisms killed by $f$. Such vanishing propagates by induction on the codimension of $A=\ker f(x)$. For a nonsemisimple $x$, the subspace $A$ is proper and nonzero by nilpotence of $f(x)$. Every $x+h$ for $h\in H_A$ has the same characteristic polynomial and has $\ker f(x+h)\supseteq A$. Polynomial evaluations at $x+h$ and $x$ agree on $A$ and modulo $A$. When the kernels of $f$ agree, the kernels of every $f^j$ agree: for $j\ge1$, membership is tested by whether the evaluation of $f^{j-1}$ lands in $A$. Equal kernel dimensions give conjugacy, since on a cyclic block $F[X]/(f^b)$ the dimension for $f^j$ is $\deg(f)\min(j,b)$. Divide by $\deg f>0$ and take successive differences to recover the number of blocks of each size. In the primitive sum, the terms with strictly larger kernel vanish by induction, while the same-kernel terms equal the original value. Their count is positive by $h=0$, so the value is zero.

For a general $\varphi$, take $\pi=\psi_s$ for $s(P)=\deg P$. Its mass on this fiber is $|G|\deg f/N\ne0$. Consequently its value at a semisimple point $x_0$ is nonzero, by the preceding propagation argument. The semisimple points with polynomial $f^m$ form one conjugacy class, since their $F[X]$-module is $(F[X]/(f))^m$. The function $\pi(x_0)\varphi-\varphi(x_0)\pi$ is primitive and vanishes on this class, hence on the entire fiber. Taking the mass and using $M_\varphi(P)=0$ gives $\varphi(x_0)=0$, then $\pi(x_0)\ne0$ gives $\varphi=0$ on the fiber. Together with nonprimary vanishing, this proves the required injectivity on $G$.

**Expansion.** Write $a_k=B(\varphi,R_k)$. If $kq^i\equiv l\bmod N$, reindex the torus identity by $\alpha\mapsto\alpha^{q^i}$. The minimal polynomial and its multiplicity stay the same, so $a_k=a_l$. For fixed $l,i$, multiplication by $q^i$ permutes the residues modulo $N$ because $q$ is coprime to $N$. Summing over $k$ first at each $i$ gives $\sum_{k<N}a_k m_{kl}=d a_l$. The full-endomorphism function $D=|G|d\,\varphi-\sum_{k<N}a_k\psi_k$ is primitive and conjugation-invariant. By the mixed Gram formula $B(D,R_l)=|G|d\,a_l-|G|\sum_{k<N}a_km_{kl}=0$ for all $l$. Injectivity on $G$ proves the expansion there. The factors $|G|$ and $d$ are nonzero in $\mathbb C$. With the normalized pairing, the expansion reads $\varphi=d^{-1}\sum_{k<N}\langle\varphi,\psi_k\rangle_G\psi_k$ on $G$. $\square$

**Remark (use in the chapter).** Proposition 13.6 uses the replacement and diagonal Gram identities in Step 2. A regular label has orbit length $d$, so the normalized squared norm is one. Its Step 7 uses the mixed Gram coefficients to detect a common orbit, and the expansion to turn equality of coefficients into equality on $G$. Proposition 13.8 consumes that orbit distinction through the injective labeling used in its count. The other inputs of those propositions retain their existing status. In particular, the count (I9), parabolic virtual-character preservation (I7), and the existence of the lifting map (I1, read in §13.4.9) remain separate inputs to this reading.

**Remark (classical source).** Green's original Lemma 6.3 gives an inner product for his uniform functions using torus conjugacy. In the proof of Lemma 8.3 he identifies the local multiplicity as $d/s$ for a simplex of degree $s$, and Lemma 7.6 states the distinct-residue condition for the degree-$s$ primary character. The orbit count above is the same finite-field mechanism. The endomorphism mass, convolution, and reconstruction argument written here follows the pinned Lean production path. [Green 1955, pp. 435, 438–439, 442–443](https://doi.org/10.1090/S0002-9947-1955-0072878-2).

**Source map [Lean, read].** The following bodies were read against the archive A2, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Paths start at the archive root.

| Proof step | Archive location |
|---|---|
| Definitions | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:11–84` |
| Root additivity and transport | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/RootPowerSumCharacterAdditiveAndXSubOnePow.lean:9–20`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseCharpolyLinearEqui.lean:10–51` |
| Primitivity induction | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsPrimitiveEndClassFunctionInvariantSubspaceMobi.lean:62–199` |
| Pairing replacement | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndomorphismInnerProductPrimitiveMobiu.lean:10–161` |
| Nonprimary vanishing | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqZeroOfNotPrimary.lean:9–123`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsConjEqAddOfIsCoprime.lean:8–84` |
| Polynomial fibers and torus regrouping | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsUnitIffCharpolyCoeffZeroNe.lean:11–69`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FiniteMonicNatDegree.lean:8–99`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndInnerProductRootPowerSumEqTorusSum.lean:12–24` |
| Mass and convolution | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassMobiusInverseMonicEq.lean:15–52`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EndomorphismMassMulParabolicInductionTrivial.lean:83–162`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CharpolyEndomorphismDensityGLRecursion.lean:72–95`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean:10–129`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveMulEqVonMangoldtConvolution.lean:14–144`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionCancelOfOne.lean:18–49` |
| Frobenius and orthogonality | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusMinpolyDegreeRootPowerSum.lean:14–124`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/FrobeniusTorusCharacterOrthogonality.lean:9–92` |
| Gram production | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndInnerProductRootPowerSumMobius.lean:17–96` |
| Fourier injectivity and mass detection | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqZeroOfFinsumMulStarPowEqZero.lean:8–68`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveEndClassFunctionZeroOfCharpolyMassZero.lean:18–98`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveEndClassFunctionEqZeroOfPrimary.lean:11–73` |
| Kernel comparison and primary conjugacy | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/KerAevalAddStabilizerNilradicalSocle.lean:10–81`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ConjOfPrimaryFinrankKerPowEq.lean:9–37` |
| Frobenius covariance and expansion | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InnerProductRootPowerSumEqOfFrobeniusModEq.lean:10–50`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveClassFunctionExpansionRootSums.lean:18–220` |

The norm call is in `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean:101–111`. The orbit calls are in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:175–225`.

The following deeper suppliers remain [Lean] with their source-body comparison [Open]. The mixed, transversal and contained-subspace counts use `sum_primitiveEndClassFunction_restrict_mixed_subspace`, `finsum_mobiusInverseCharpoly_transversal_subspaces` and `finsum_mobiusInverseCharpoly_invariant_le`. The cyclic-vector recurrence uses `finsum_card_cyclic_vectors_invariant_subspaces` and `endomorphismMassOfCharpoly_card_cyclic_vectors`. The normalized block count uses `finsum_subspaceStabilizer_mul_block_functions` and `card_subspaces_mul_generalLinearGroupCard`. The primary conjugacy proof uses `primary_endomorphism_cyclic_decomposition_finrank_ker` and `exists_perm_of_sum_min_eq_positive_family`. The elementary counting and module arguments in this section explain the interfaces supplied by these lemmas.

### 13.4.7 Parabolic induction and the virtual-character subtraction

The Green candidate is defined by subtracting its values on proper invariant subspaces from a root power sum. A trace in a smaller dimension supplies a value on each subspace, but the sum is a function on the large group. The stabilizer of a single subspace yields a representation whose trace is the whole sum. This puts the subtraction in the integer lattice needed for the norm-one argument.

**First example.** Over $F=\mathbb F_3$, let $\varepsilon$ be the sign character of $F^\times$. In $G=\mathrm{GL}_2(F)$ the stabilizer $P$ of the first coordinate line consists of upper triangular matrices. Inflate the character that reads $\varepsilon$ on the first diagonal entry, and induce to $G$. The group has order $(9-1)(9-3)=48$, the stabilizer has order $2\cdot2\cdot3=12$, and there are four lines. Each fixed line contributes the sign of its eigenvalue. At $I,-I,\operatorname{diag}(1,-1)$, a nonidentity unipotent Jordan block, and an element with irreducible characteristic polynomial, the induced values are respectively $4,-4,0,1,0$. The split element's two fixed lines contribute opposite signs. The Jordan element fixes just its eigenline. For exponent $k=1$ the lift restricts to $\varepsilon$, and the dimension-one Möbius candidate equals $\varepsilon$. At the first four elements the raw root sums are $2,-2,0,2$, so subtraction gives the unsigned dimension-two values $-2,2,0,1$. At the irreducible element the correction is zero. The dimension-two sign reverses all the unsigned values.

**Definitions.** For a finite group $H$, let $R(H)$ be the additive group generated by complex representation characters. Complete reducibility and character orthogonality identify it with the free abelian group on the irreducible characters, embedded in the space of complex class functions. Use the pairing linear in the first variable,

$$
\langle f,h\rangle_H=\frac1{|H|}\sum_{y\in H} f(y)\overline{h(y)}.
$$

The archive's bilinear pairing uses $h(y^{-1})$ in place of $\overline{h(y)}$. These agree for virtual $h$ by unitarizing representations using a group average. The archive's $\mathrm{ipGL}$ is the unnormalized Hermitian sum over the invertible endomorphisms, hence gives $|\mathrm{GL}_n(F)|$ times the normalized pairing in dimension $n$.

For $H\le G$, let $\widetilde f$ extend $f$ by zero. Finite-group induction is

$$
(\operatorname{Ind}_H^G f)(x)=\frac1{|H|}\sum_{t\in G}\widetilde f(t^{-1}xt).
$$

For an $a$-plane $W_0$ in $V=F^n$, put $P=\operatorname{Stab}_{\mathrm{GL}(V)}(W_0)$. A complement gives upper block triangular coordinates. The map $\pi:P\to L=\mathrm{GL}(W_0)\times\mathrm{GL}(V/W_0)$ sends an element to its two diagonal actions. Its kernel $U$, the unipotent radical, has identity diagonal blocks and arbitrary upper-right block. The block diagonal section identifies $L$ with a Levi subgroup. Inflation of $\lambda$ is the composite $\lambda\circ\pi$. The archive uses the restriction map $p\mapsto p|_{W_0}$, which inflates $\alpha\boxtimes 1$ by taking the first component of $\pi$.

**Lemma 13.12 (induction on the lattice and Frobenius reciprocity).** Pullback along a group homomorphism preserves virtual characters. For $H\le G$ finite, induction maps $R(H)$ into $R(G)$, and for class functions $f$ on $H$ and $h$ on $G$,

$$
\langle\operatorname{Ind}_H^G f,h\rangle_G=\langle f,h|_H\rangle_H.
$$

For a Levi class function $\lambda$ this gives

$$
\langle\operatorname{Ind}_P^G(\lambda\circ\pi),h\rangle_G
=\langle\lambda,h_U\rangle_L,\qquad
h_U(\ell)=\frac1{|U|}\sum_{u\in U}h(\dot\ell u).
$$

Here $\dot\ell$ is any lift in $P$. For a character, $h_U$ is the character of the action of $L$ on the $U$-fixed space.

*Proof.* Pullback composes the representation with the homomorphism and then takes its trace. For induction, choose representatives $r_C$ for the cosets $C=tH$. Given an $H$-representation $\sigma$ on $E$, use one copy of $E$ per coset with action

$$
(gv)_C=\sigma(r_C^{-1}g r_{g^{-1}C})v_{g^{-1}C}.
$$

The argument of $\sigma$ lies in $H$ because $g r_{g^{-1}C}H=r_CH$. The group law follows by inserting $r_{g^{-1}C}r_{g^{-1}C}^{-1}$ in the product for a pair of group elements. Only the fixed cosets contribute diagonal blocks to the trace. The block on such a coset contributes $f(r_C^{-1}gr_C)$ for $f=\chi_\sigma$. For the full sum over $t$, replacing $r_C$ by $r_C h_0$ for $h_0\in H$ conjugates the argument by $h_0$, preserving both membership in $H$ and the value of the extended class function. Thus each contributing block occurs $|H|$ times before division. Additivity of extension by zero and summation now carries integer linear combinations of characters into $R(G)$. This is the archive's closure induction under zero, addition and negation.

For reciprocity substitute the induction definition into the pairing and set $x=tyt^{-1}$ in the inner sum. Then $h(x)=h(y)$ and only $y\in H$ survives. The sum over $t$ cancels $|G|^{-1}$, leaving $|H|^{-1}\sum_{y\in H}f(y)\overline{h(y)}$. For the Levi formula group the remaining sum over $P$ by fibers of $\pi$. Each fiber is a coset of $U$, and $|P|=|L||U|$. Changing the lift permutes that fiber. For a representation $\rho$, the operator $|U|^{-1}\sum_{u\in U}\rho(u)$ projects onto the fixed vectors and commutes with $\rho(P)$ by normality. Composing with $\rho(\dot\ell)$ gives the claimed trace. ∎

**Theorem 13.13 (the conditional supply of (I7)).** [Lean, read] Let $F$ be finite, $a,n\ge 0$, and let $\Phi_V:\operatorname{End}_F(V)\to\mathbb C$ be a family on finite-dimensional $F$-spaces. Assume $\Phi_{V'}(e y e^{-1})=\Phi_V(y)$ for every linear isomorphism $e:V\to V'$ and endomorphism $y$. Assume $\alpha:z\mapsto\Phi_{F^a}(z)$ belongs to $R(\mathrm{GL}_a(F))$. Then on $\mathrm{GL}_n(F)$ the function

$$
T_{a,n}\Phi(x)=\sum_{\substack{W\subset F^n,\ \dim W=a\\xW=W}}\Phi_W(x|_W)
$$

is virtual. For $a\le n$ it equals $\operatorname{Ind}_P^G((\alpha\boxtimes1)\circ\pi)$ after identifying $W_0$ with $F^a$.

*Proof.* If $a>n$, the sum is empty. Otherwise choose $W_0$ and an isomorphism $e_0:W_0\to F^a$. A stable subspace of an invertible map is preserved with equality by injectivity and dimension. The restriction $p\mapsto e_0(p|_{W_0})e_0^{-1}$ is therefore a homomorphism to $\mathrm{GL}_a(F)$. Transport identifies the pullback of $\alpha$ with $\beta(p)=\Phi_{W_0}(p|_{W_0})$, so $\beta$ is virtual.

Every $a$-plane is $tW_0$ for some $t$, by extending bases to the ambient space. Two elements $s,t$ give the same plane exactly when $s^{-1}t\in P$. Each fiber of $t\mapsto tW_0$ consequently has $|P|$ elements. The plane $tW_0$ is fixed by $x$ exactly when $t^{-1}xt\in P$. In that case the restriction of $t$ intertwines $(t^{-1}xt)|_{W_0}$ and $x|_{tW_0}$, so the summand equals $\Phi_{tW_0}(x|_{tW_0})$. Otherwise the extended summand is zero. Grouping by fibers cancels $|P|$, giving coefficient one per fixed plane and proving the asserted identity and virtuality. For $a=0$ the sole summand is constant, and for $a=n$ the sole summand is $\Phi_{F^n}(x)$. ∎

**The subtraction in the candidate.** Fix the lift $\theta$ and exponent $k$ of (I6). Let $s(P)$ be the corresponding root power sum, with roots counted with multiplicity, and take $\Phi_V(y)=\psi_s(V,y)$ on all endomorphisms. The recurrence subtracts the lower-dimensional values over all proper stable subspaces. Transport preserves the characteristic polynomial and bijects those subspaces, and the corresponding restricted maps are conjugate. Induction on dimension proves the transport identity. The Lean proof uses induction on the recursion depth followed by specialization to depth $\dim V+1$.

Write $S_d(x)=s(\operatorname{charpoly}x)$ and $\psi_d(x)=\Phi_{F^d}(x)$ on $\mathrm{GL}_d(F)$. Sorting the proper stable subspaces by dimension gives

$$
\psi_d=S_d-\sum_{0\le a<d}T_{a,d}\Phi .
$$

The rank-zero value is $S_0=s(1)=0$ and the outer sum is empty. Assume (I6) through rank $d$. Strong induction supplies virtuality of the unsigned $\psi_a$ for each $a<d$. After the field argument, the actual Lean call passes the family $\Phi$, its transport proof, the dimensions $a,d$, and the witness from the strong induction hypothesis evaluated at $a$ with $a<d$. Theorem 13.13 places each inner sum in $R(\mathrm{GL}_d(F))$. With the leading term supplied by (I6), the subtraction stays in the integer lattice. This step applies to every exponent covered by (I6). The dimension sign $(-1)^{d-1}$ acts by an integer scalar. For $d>0$ and a regular exponent, the existing Gram step gives normalized squared norm one. The signed candidate then has integer coordinates in the orthonormal irreducible basis, and their squares sum to one. Its positive value at the identity selects the positive irreducible, as in Proposition 13.6.

**A rank-three calculation.** Over $\mathbb F_3$ take the $(2,1)$ Levi $\mathrm{GL}_2(F)\times F^\times$ and inflate $\psi_2\boxtimes 1$ from the first example. Here $|G|=26\cdot24\cdot18=11232$ and $|P|=48\cdot2\cdot3^2=864$, so the index is $13$. This is the number $(27-1)/(3-1)$ of planes, counted by nonzero defining forms modulo scalars. At the identity the plane correction is $13(-2)=-26$, the line correction is $13$, and $\psi_3(I)=3-13-(-26)=16$.

For a noncentral check let $xe_1=e_1$, $xe_2=e_2+e_1$, $xe_3=-e_3$. Stable planes are kernels of eigenforms. The $+1$ eigenforms are multiples of the second coordinate form and the $-1$ eigenforms multiples of the third. The two planes are therefore $\langle e_1,e_3\rangle$ and $\langle e_1,e_2\rangle$. Their restrictions are split with eigenvalues $1,-1$ and unipotent Jordan, respectively. The plane correction is $0+1=1$. The Jordan plane thus contributes $864$ identical unit terms before division. The stable lines $\langle e_1\rangle,\langle e_3\rangle$ have total weight $1-1=0$. The raw root sum is $1+1-1=1$, so $\psi_3(x)=0$.

**Remarks.** Green's fixed-flag product weights each fixed flag once by the product of characters on its successive quotients. The two-block specialization with trivial quotient character gives the formula above. Green uses right cosets $Pt$ with conjugation $txt^{-1}$. Inversion gives the convention $tP$, $t^{-1}xt$ used here. [Green1955, p. 410, Theorem 2 and equations (2)–(4)](https://doi.org/10.1090/S0002-9947-1955-0072878-2).

The I7 supply assumes transport invariance and lower-dimensional virtuality. The Green subtraction additionally consumes (I6). Norm and orbit arguments retain (I4)/(I5). Section 13.4.8 supplies the conditional (I9) bound used in Proposition 13.8, and Section 13.4.9 reads the conditional supply of the lift (I1), `CuspGL.TeichEmb.exists_teichmuller`.

**Source map.** Paths are relative to the pinned A2 archive’s `lean/` directory (SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`). R3 marks the bodies used and read here. The two closure clauses on pullback and induction are at lines 84–91 and 98–106 of their file. The Green entry at line 136 calls the cuspidality supplier, which reaches the regular-character consumer through its statement wrapper. The Frobenius pairing calculation above is a textbook derivation.

| Reading | Role | A2 path and lines |
|---|---|---|
| R3 | I7 producer and all its local helpers | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean:11–289` |
| R3 | Pullback and induction closure clauses, including additivity | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharactersMulComapConjIndLinear.lean:47–106` |
| R3 | Pullback of traces | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldRestrictClassFunctionOne.lean:6–22` |
| R3 | Ordinary character induction assembly | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldInducedClassFunction.lean:9–17` |
| R3 | Group sum to coset sum | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InducedClassFunctionFromSubgroupEqFinsumCosets.lean:7–64` |
| R3 | Coset cocycle, representation and diagonal trace | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterFinsumConjSubgroupFunctionExtendByZer.lean:8–108` |
| R3 | Recursion depth, stable-subspace formula and root-sum definition | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:24–66` |
| R3 | Transport of the candidate | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseCharpolyLinearEqui.lean:10–51` |
| R3 | Rank grouping, strong induction and concrete I7 application | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean:19–88` |
| R3 | Regular character consumer, sign, norm and positivity assembly | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean:92–184` |
| R3 | Cuspidality assembly entering regular character consumer | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18–48` |
| R3 | Choice of exponent and path through cuspidality | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:65–136` |
| Definition | Virtual lattice, extension, induction and inverse pairing | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/AbByPOfComm.lean:5–22` |
| Definition | Unnormalized Hermitian sum | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:83–84` |
| R2 | Coordinate realization of representation traces | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentation.lean:51` |
| R3 (§13.4.9) | I1 lift existence | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:24` |
| R3 (§13.4.8) | I9 counting assembly and named direct producers | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardCuspidalMultisetsTotalDegreeLeStatement.lean:8` |

The R3 entries for the character consumer and cuspidality concern the assembly, using the norm, identity-value and primitive-radical results at their stated interfaces. The present reading invokes `GlobalTheory.BI.irr_of_norm_one` at its interface, together with `CuspGL.extZero_spec`, `CuspGL.psi_one` and `T.finsum_unipotent_radical_eq_zero_of_isPrimitive`. Section 13.4.10 reads the first three. The I4/I5 and I6 production readings are recorded in §§13.4.6 and 13.4.5.

### 13.4.8 Why the cuspidal count exhausts Green's list

A list of cuspidal characters can induce a reducible character. Proposition 13.8 needs one place in a finite counting set for each **multiset** of cuspidal characters, even when the same character occurs several times. A Whittaker functional singles out a constituent that can occupy such a place. Harish–Chandra orthogonality prevents two multisets from using the same place, and the Gelfand–Graev norm bounds the number of places.

Consider the permutation representation of $G_2=\mathrm{GL}_2(\mathbb F_3)$ on the four lines. It comes from the multiset containing two copies of the trivial character of $G_1$. The upper unitriangular subgroup fixes one line and acts regularly on the other three. A nontrivial character of this subgroup therefore occurs once. The trivial summand of the permutation representation has no such functional, so the three-dimensional complement supplies the desired constituent. The whole permutation character has squared norm $2$, since the action has two orbits on ordered pairs of lines. This is the first instance where the count must permit repeated factors.

**Definitions.** Let $g$ be prime, $G_j=\mathrm{GL}_j(\mathbb F_g)$, and fix a nontrivial additive character $\psi$ of $\mathbb F_g$. Write $U_j$ for the upper unitriangular group and $\lambda_j(u)=\psi(\sum_{i=1}^{j-1}u_{i,i+1})$. Use the trivial group and its trivial character in rank zero. For class functions put

$$
 B_H(f,h)=\frac{1}{|H|}\sum_{x\in H}f(x)h(x^{-1}),\qquad
 W_j(f)=\frac{1}{|U_j|}\sum_{u\in U_j}\lambda_j(u)^{-1} f(u).
$$

The bilinear form $B_H$ agrees with the usual Hermitian pairing on pairs of genuine characters. The first superdiagonal adds under multiplication, so $\lambda_j$ is a character. The weighted average defining $W_j$ is the trace of the projection onto the $\lambda_j$-eigenspace. Hence $W_j(\rho)$ is a nonnegative integer for every character $\rho$. Call an irreducible character generic if this integer is positive. Let $\Gamma_j=\operatorname{Ind}_{U_j}^{G_j}\lambda_j$. These conventions give $\Gamma_j(1)=|G_j|/|U_j|$ and $B_{G_j}(f,\Gamma_j)=W_j(f)$. In fact the ordinary induction sum has denominator $|U_j|$, and reindexing the pairing by conjugation cancels its denominator $|G_j|$ and replaces $\lambda_j(u^{-1})$ by $\lambda_j(u)^{-1}$.

A cuspidal entry is a pair $p=(a,\sigma)$ with $a>0$ and $\sigma$ an irreducible character of $G_a$ with zero fixed space for each proper two-block parabolic radical. Write $H_L$ for iterated Harish–Chandra induction along the list $L$ of such entries, with the empty product equal to $1$ on $G_0$. At each two-block step, inflate the tensor product to the upper block parabolic $P$ and induce with denominator $|P|$. This gives a genuine character. The adjoint operation $r_{a,b}$ on characters is trace on invariants under the radical of order $g^{ab}$. Its formula averages over the radical, so cuspidality at the identity gives zero restriction as a character. On central scalars $zI$, every constituent of $H_L$ has central character $\prod_{(a,\sigma)\in L}\omega_\sigma(z)$, with each entry contributing separately. This follows in the induced model because a scalar belongs to $P$ and commutes with every coset representative.

**Lemma 13.14 (existence of a generic constituent).** [Lean, read] Assume the cuspidal Whittaker positivity input $W_a(\sigma)>0$ for every cuspidal entry and the two-block Whittaker product identity

$$
 W_{a+b}(\alpha\circ\beta)=W_a(\alpha)W_b(\beta),
$$

where $\circ$ denotes Harish–Chandra induction. Then every $H_L$ contains a generic irreducible constituent.

**Proof.** Induct on the list, applying the two-block identity to its head and induced tail. The empty list gives $W_0(1)=1$. The resulting product of Whittaker dimensions is positive because every factor is positive.

Write the induced character as a sum of irreducible characters with repetitions. By linearity some term has a positive Whittaker dimension. Its pairing with the induced character counts its occurrences by irreducible orthogonality, so that pairing is also positive.

The two-block supplier organizes the Whittaker sum over double cosets of the unitriangular group and the parabolic. A shuffle placing a first-block coordinate immediately before a second-block coordinate contributes zero by nontrivial additive-character cancellation on the corresponding radical root subgroup. In the surviving shuffle the second block precedes the first, and the intersection is the product of the two block unitriangular groups. The normalized average there is the product displayed above. $\square$

**Lemma 13.15 (pairing the induced characters).** [Lean, read] Use the Harish–Chandra restriction formula for a cuspidal product. For $L,L'$ of the same total rank,

$$
 B(H_L,H_{L'})=0
$$

if their multisets differ. If their multisets agree, the pairing is $\prod_p m_p!$, with $m_p$ the multiplicity of $p$ in $L$. In particular the squared norm is $1$ when all entries are distinct.

**Proof.** The restriction formula for the split $a+b$ is a sum over subsets $I$ of the **positions** in $L$ whose ranks sum to $a$, with term $H_{L_I}\boxtimes H_{L_{I^c}}$. One way to understand the formula is to compare the $a$-plane with the input flag. Each input block is split according to the successive intersection dimensions. A split into two positive ranks imposes proper radical invariants on that cuspidal character and contributes zero. An unsplit block is assigned to one side, accounting for the indexed subsets and the two products.

For $L'=(a,\sigma)::K$, reciprocity, the restriction formula, and the pairing on a direct product give

$$
 B(H_L,H_{L'})=\sum_{I} B(H_{L_I},\sigma) B(H_{L_{I^c}},H_K).
$$

The first pairing is zero for two or more entries, by reciprocity at the first split and cuspidality of $\sigma$. The empty subset cannot have rank $a>0$. For a singleton, the first pairing is $1$ exactly when its entry is $(a,\sigma)$ and is $0$ otherwise. Thus the recurrence removes one matching position and pairs the remaining lists. For the empty right list, rank zero forces the left list to be empty and the pairing is $1$. Iteration counts bijections of positions preserving the entries. Unequal multisets admit none, while equal ones give $m_p!$ independent choices for the matching among copies of each $p$. The archived theorem states the vanishing and the multiplicity-free diagonal, and its consumer uses the vanishing alone. The factorial formula follows from the same recurrence. $\square$

**Lemma 13.16 (the generic count).** [Lean, read] Use the two-block Whittaker product identity from Lemma 13.14 and assume the mirabolic restriction identity and twisted derivative formula specified below. In rank $n>0$ the number of generic irreducible characters is at most $g^n-g^{n-1}$.

**Proof.** Set $a_j=W_j(\Gamma_j)$ and $t_j=j(j-1)/2$. Denote by $\delta_j$ the indicator of the identity on $G_j$. The numerical step in the archive applies the mirabolic restriction identity to $\delta_{k+1}$, restricted to $\operatorname{diag}(h,1)$ with $h\in G_k$. In its derivative convention $D_i f$ is a function on $G_i$, obtained by Harish–Chandra restriction to $G_i\times G_{k+1-i}$ followed by Whittaker averaging in the second variable. The identity reads

$$
 \delta_k=\sum_{i=0}^k (D_i\delta_{k+1})\circ\Gamma_{k-i}.
$$

In the derivative average only the identity matrix contributes, and only at $h=1$. Its weight is $g^{-i(k+1-i)-t_{k+1-i}}$, from the radical and the lower-rank Whittaker subgroup. Also $W_i(\delta_i)=g^{-t_i}$, including $i=0$. Apply $W_k$ and the two-block product identity. Since $t_i+i(k+1-i)+t_{k+1-i}=t_{k+1}=t_k+k$, every summand has the same scalar factor:

$$
 g^{-t_k}=g^{-t_{k+1}}\sum_{j=0}^k a_j,
 \qquad \sum_{j=0}^k a_j=g^k.
$$

Subtract the identity for $k=n-1$ from that for $k=n$ to get $a_n=g^n-g^{n-1}$. By reciprocity $a_n=B(\Gamma_n,\Gamma_n)$. Expanding in the orthonormal basis of irreducible characters gives

$$
 a_n=\sum_{\rho\in\operatorname{Irr}(G_n)}W_n(\rho)^2.
$$

The expansion can also be obtained by applying $W_n$ to the class-function expansion of $\Gamma_n$. Each positive integer coefficient contributes at least one to the sum of squares, proving the bound. This argument uses neither a multiplicity-one theorem nor any count of cuspidal labels. $\square$

**Theorem 13.17 (conditional count of cuspidal multisets, input (I9)).** [Lean, read] Let $n>0$ and let $S$ be a finite set of distinct multisets of cuspidal entries of total rank $n$. Under the inputs of Lemmas 13.14–13.16, one has $|S|\le g^n-g^{n-1}$.

**Proof.** Fix the same $\psi$ for every multiset. For each $M\in S$ choose a list of its occurrences and then choose any generic constituent $\rho_M$ of the induced character using Lemma 13.14. If the choices for $M$ and $M'$ agree, write both induced characters as genuine sums, with multiplicities $b_\rho$ and $b'_\rho$. Their pairing is $\sum_\rho b_\rho b'_\rho$, a sum of nonnegative integers with a positive term at the common constituent. Lemma 13.15 forces the lists to be permutations of one another, hence $M=M'$. This works for any choices and even if the central characters agree. The finite set of irreducible characters contains the image. Lemma 13.16 bounds its generic subset as required. In Lean the fixed additive character is `ZMod.stdAddChar`. Its values at $0$ and $1$ differ by injectivity, so it is nontrivial. The list `M.toList` has the same rank sum as $M$, and permutation of two lists is equality of their multiset images. $\square$

**Hand calculation in $\mathrm{GL}_2(\mathbb F_3)$.** The group has order $48$, and $U_2$ has order $3$. Its two nonidentity elements are conjugate. The centralizer of a nonidentity unipotent consists of invertible $aI+bN$, where $N$ is its nonzero nilpotent part, and has order $6$. Therefore the induced character has value $16$ at the identity and $6(-1)/3=-2$ on this unipotent class, using $\psi(1)+\psi(2)=-1$. It vanishes outside those classes. The normalized norm is $16^2/48+(-2)^2/6=6$.

The polynomial labels give three quadratic singleton entries, with exponent orbits $\{1,3\},\{2,6\},\{5,7\}$ modulo $8$. The two linear characters are $1$ and $\epsilon$, the sign on $\mathbb F_3^\times$. The remaining supports are $[1,1]$, $[1,\epsilon]$, and $[\epsilon,\epsilon]$. The double copies give squared norm $2$ each, and the mixed pair has norm $1$. The repeated sign case is the repeated trivial case twisted by $\epsilon\circ\det$, which is trivial on $U_2$. The repeated pairs have trivial central character, and the mixed pair has central character $\epsilon$. On $-I$ the quadratic entries act by $(-1)^k$ for exponent $k$, since $-1$ is the fourth power of a generator of $\mathbb F_9^\times$. Thus both central characters occur on several supports. Orthogonality across supports accounts for all six places and explains why matching central characters alone would be insufficient.

**Hand calculation in $\mathrm{GL}_3(\mathbb F_2)$.** Write $u\in U_3$ using upper entries $u_{12}=a$, $u_{23}=b$, $u_{13}=c$. Then $\lambda_3(u)=(-1)^{a+b}$ and $(u-I)^2=abE_{13}$. There are two regular unipotents in $U_3$, both with weight $+1$. Of the five transvections one has weight $+1$ and four have weight $-1$. A transvection is specified by a nonzero image vector $v$ and a nonzero functional vanishing on $v$, giving $7\cdot3=21$ elements in its conjugacy class. Its centralizer has order $168/21=8$. A regular unipotent has centralizer of order $4$, since every commuting operator is a polynomial in its cyclic nilpotent part and the constant term must be $1$. Induction gives $\Gamma_3$ values $21,-3,1$ on the identity, the transvections, and the regular unipotents, respectively. The norm is

$$
 21^2/168+(-3)^2/8+1^2/4=4.
$$

The four multisets supplied by polynomial labels correspond to $(X+1)^3$, $(X+1)(X^2+X+1)$, $X^3+X+1$, and $X^3+X^2+1$. The two cubics are irreducible because neither has a root in $\mathbb F_2$. The first multiset has three identical entries. Its induced character acts on complete flags and its squared norm is $6$, the number of relative permutations of two flags. Its values on the three unipotent classes above are $21,5,1$. A transvection has three invariant lines in its kernel and three invariant planes containing its image. The image line lies in all three planes, while each of the other two invariant lines determines just the kernel plane. A regular unipotent fixes only its Jordan flag. Hence the Whittaker average for the complete-flag character is $(21+(1-4)5+2)/8=1$. The second multiset has one rank-one and one rank-two entry, with squared norm $1$ by Lemma 13.15. The center is trivial in this field. The norm $4$ counts the available generic constituents with squared Whittaker multiplicities, so the repeated triple still costs only one of the four places.

**Return to Proposition 13.8.** Use the injective cuspidal labeling in every positive rank supplied by Proposition 13.6 and Lemma 13.7. Factor each monic polynomial of degree $d$ with nonzero constant term into monic irreducibles and label its factors with their multiplicities. The resulting support determines the factor multiset by injectivity in each rank and therefore determines the polynomial. These polynomials number $(g-1)g^{d-1}$ by independent choices of their coefficients. A missing degree-$d$ cuspidal character would give a new singleton multiset. If that singleton already came from a polynomial, the polynomial would have a single irreducible factor of degree $d$ with multiplicity one, and its label would give the supposedly missing character. Adjoining the singleton therefore contradicts Theorem 13.17. The argument still depends on the construction of the cuspidal labels, including (I1), and on the named inputs below.

**Reading notes.** The two-block product proof is `GlobalTheory.GLq.WhMul.wh_hcT`. Its deeper inputs include `Shuffle.existsUnique_shuffle`, `mackey_doubleCoset_pairing`, `OpenCell.openCell` and `NonOpenCell.whittaker_term_eq_zero`. Cuspidal positivity enters as `T.whittakerDimension_pos_of_cuspidal_character`. The pairing recurrence uses `T.harishChandraRestriction_cuspidal_product_sum_subsets`, `T.harishChandra_frobenius_reciprocity` and `T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero`. The cumulative Gelfand–Graev calculation uses `T.mirabolicClassFun_blockDiagonal_eq_sum_derivatives` and `T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum`. These named inputs are [Lean] at their interfaces, with deeper proof readings [Open] here. The Whittaker idempotent, character decomposition and finiteness, and orthogonality also enter through the interfaces recorded in the source map. Section 13.4.9 reads the lifting input `CuspGL.TeichEmb.exists_teichmuller` at its stated Witt-vector interface.

Green's Lemma 7.7 matches degree-$s$ simplexes with irreducible polynomial labels. His Theorem 13 and the argument opening its proof count partition-valued labels against conjugacy classes. Here the multiset retains only the multiplicity at each cuspidal label, and the proof uses the squared Whittaker multiplicities instead of the full conjugacy-class count. [Green 1955, pp. 439–440](https://doi.org/10.1090/S0002-9947-1955-0072878-2).

**Source map.** Paths start at `lean/` in A2. The archive SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. R3 covers the indicated proof bodies at the stated interface depth. R2 marks inputs used at statement level.

| Reading | Use | Archive path and lines |
| --- | --- | --- |
| R3 | Proposition 13.8, exhaustion consumer and call at line 125 | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProof.lean:56–168` |
| R3 | I9 wrapper | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardCuspidalMultisetsTotalDegreeLeStatement.lean:8–9` |
| R3 | Theorem 13.17 | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardCuspidalMultisetsTotalDegreeLe.lean:16–61` |
| R3 | Existence wrapper | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGenericConstituentHarishChandraCuspidalStatement.lean:8–9` |
| R3 | Lemma 13.14 | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGenericConstituentHarishChandraCuspidal.lean:20–125` |
| R3 | Two-block product proof using cell inputs | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerDimensionHarishChandraInductionMul.lean:65–184` |
| R3 | Lemma 13.15, vanishing and distinct-entry diagonal | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharacterPairingHarishChandraCuspidalMackey.lean:19–263` |
| R3 | Common constituent implies nonzero pairing | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HarishChandraSeriesLabelExistsUniqueGLn.lean:16–71` |
| R3 | Generic count wrapper | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardGenericIrreducibleCharactersGLnLeStatement.lean:8–9` |
| R3 | Lemma 13.16, finite sum of squares | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardGenericIrreducibleCharactersGLnLe.lean:18–88` |
| R3 | Reciprocity and difference of cumulative sums | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GelfandGraevCharacterGLnNormAndReciprocity.lean:16–91` |
| R3 | Identity indicator and cumulative sum | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockDiagonalWithIdentityGLEqOneIff.lean:17–171` |
| Definitions | Pairing, induction, restriction, and Whittaker conventions | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:11–75` |
| R2 | Cuspidal Whittaker positivity | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerDimensionPosOfCuspidalCharacterStatement.lean:8–9` |
| R2 | Restriction sum indexed by subsets | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HarishChandraRestrictionCuspidalProductSumSubsetStatement.lean:8–9` |
| R2 | Cuspidal restriction vanishing | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HarishChandraRestrictionTwoBlockCuspidalEqZeroStatement.lean:8–9` |
| R2 | Parabolic reciprocity | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HarishChandraFrobeniusReciprocityStatement.lean:8–9` |
| R2 | Mirabolic restriction identity | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MirabolicClassFunBlockDiagonalEqSumDerivativesStatement.lean:7–8` |
| R2 | Twisted derivative formula | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BernsteinZelevinskyDerivativeGLnEqTwistedSumStatement.lean:7–8` |
| R2 | Shuffle double cosets | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUniqueShuffle.lean:104` |
| R2 | Shuffle characterization, file reference | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ShuffleNoDescentIffOpen.lean:25` |
| R2 | Double coset pairing | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardDoubleCosetMulCardInter.lean:81` |
| R2 | Open cell evaluation | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsUnitOfUniUp.lean:384` |
| R2 | Other cell cancellation | `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WhittakerTermEqZero.lean:118` |
| R2 | Idempotence and identity coefficient | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement.lean:8` |
| R2 | Integral projection traces | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement.lean:8` |
| R2 | Finiteness of irreducibles | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteIrrCharactersAndFinsumCentralIdempotentsEqStatement.lean:8` |
| R2 | Decomposition and expansion | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharacterDecompositionAndClassFunctionExpansionStatement.lean:8` |
| R2 | Orthogonality | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CentralIdempotentOfIrrCharacterOrthogonalCentralStatement.lean:8` |
| R2 | Genuine list product | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HarishChandraProductListIsCharacterAndPermInvari.lean:74` |
| R2 | Rank-zero Whittaker value | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BernsteinZelevinskyDerivativeHarishChandraProduct.lean:42` |
| R3 (§13.4.9) | I1 lift | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:24` |


### 13.4.9 Teichmüller lifts, Frobenius orbits, and choice of labels

> **Reading levels.** The common finite-layer comparison in Proposition 13.23
> is an expository proof using (I4) and (I5). The source table identifies the
> formal proof bodies used here and the interfaces on which they depend. The
> Witt-vector and parameter constructions in Theorem 13.21 and Lemma 13.22
> incorporate the preceding exposition at its stated conditional depth.

**Motivation.** Every matrix $x \in \mathrm{GL}_d(F)$ over a finite field $F$ of characteristic $p$ has eigenvalues in an algebraic closure $\overline{F}$ of characteristic $p$, whereas ordinary complex characters take values in $\mathbb C$ of characteristic $0$. Because $p \cdot 1_{\overline{F}} = 0 \neq p \cdot 1_{\mathbb C}$, **no ring homomorphism $\overline{F} \to \mathbb C$ exists**; addition cannot be preserved across the characteristic barrier. What can be lifted is the **multiplicative structure** alone: every nonzero element of $\overline{F}$ generates a finite subfield of cardinality $q^m = p^{fm}$, so its multiplicative order divides $q^m - 1$, an integer coprime to $p$. Embedding the prime-to-$p$ torsion group $\overline{F}^\times = \bigcup_{m \ge 1} \mu_{q^m - 1}(\overline{F})$ into $\mathbb C^\times$ and extending by $0 \mapsto 0$ turns eigenvalues into complex roots of unity, from which Sections 13.4.4–13.4.7 form the root power sums $s_k$ and their invariant-subspace Möbius inverses $\psi_{s_k}$.

Two structural questions immediately govern how such a lift enters node `P16`:

1. *Existence and zero conventions:* How does the archive construct an injective multiplicative map $\theta_0 : \overline{F} \to \mathbb C$ without hand-picking compatible generators level by level, and why do some interfaces type $\theta_0$ as a bare multiplicative homomorphism (`AlgebraicClosure F →* ℂ`, injective on nonzero elements) while the parameter-label layer requires a zero-preserving embedding (`Fbar p →*₀ ℂ`)?
2. *Non-canonical choice and label permutation:* Choosing $\theta_0$ requires a non-canonical comparison between characteristic-$p$ roots of unity and complex roots of unity. When we replace one valid embedding $\theta_0$ by another $\theta_0'$, the *set* of cuspidal characters of $\mathrm{GL}_d(\mathbb F_g)$ cannot change, yet individual polynomial labels $P \in \mathbb F_g[X]$ and exponent coordinates $k \bmod (g^d - 1)$ can shift! How does arithmetic Frobenius interact with $\theta_0$, how are the resulting parameters wired into `GlobalTheory.ParamLabel`, and what exact group permutes the polynomial labels when the lift changes?

Before proving the general theorems, we compute every piece by hand over $\mathbb F_9 / \mathbb F_3$ (degree $d = 2$, characteristic $3$) and $\mathbb F_{16} / \mathbb F_2$ (degree $d = 4$, characteristic $2$).

**Example 13.18 ($\mathbb F_9 / \mathbb F_3$: zero extension, $3$-adic vs. complex choice, and label permutation on $\mathrm{GL}_2(\mathbb F_3)$).** [Expository]
Take $F = \mathbb F_3$ ($p = g = 3$), $d = 2$, and $K = \mathbb F_9 = \mathbb F_3[\zeta]/(\zeta^2 + \zeta + 2)$ as in Section 13.2.1(4) and Example 13.3. Here $\lvert K \rvert = 9$ and $N = \lvert K^\times \rvert = 3^2 - 1 = 8$.

1. *Characteristic and divisibility:* Since $\gcd(8, 3) = 1$ ($8 \equiv 2 \not\equiv 0 \pmod 3$), $X^8 - 1$ has derivative $8X^7 = 2X^7$ coprime to $X^8 - 1$ over $\mathbb F_3$, so $K^\times \cong C_8$ consists of $8$ distinct $8$-th roots of unity ($\zeta^2 = 2\zeta + 1$, $\zeta^4 = 2 = -1$, $\zeta^8 = 1$). Conversely, complex $3$-power roots of unity such as $e^{2\pi i/3} \in \mathbb C^\times$ never occur in $\theta_0(\overline{\mathbb F}_3^\times)$, because $x^3 = 1$ in characteristic $3$ forces $(x - 1)^3 = x^3 - 1 = 0$, hence $x = 1$.
2. *Zero extension:* Any multiplicative homomorphism $\theta_0 : \mathbb F_9 \to \mathbb C$ that is injective on $\mathbb F_9^\times$ satisfies $\theta_0(-1) = -1 \neq 1$, whence $\theta_0(0) = \theta_0(0 \cdot (-1)) = \theta_0(0)(-1)$ forces $\theta_0(0) = 0$ automatically. In `rootSum θ₀ k P` (`src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:65–66`), a zero root of a singular $2 \times 2$ matrix contributes $\theta_0(0)^k = 0^k = 0$ for every $k \ge 1$, while Lean's convention $0^0 = 1$ gives $\theta_0(0)^0 = 1$ so that $s_0(P) = \deg P$ remains additive across singular endomorphisms.
3. *Why the complex choice is non-canonical:* Inside the Witt ring $W_3(\mathbb F_9) \cong \mathbb Z_3[\xi]/(\xi^2 + \xi + 2)$, Hensel's lemma (or `WittVector.teichmuller 3`) singles out a *unique* $8$-th root of unity $\tau_3(\zeta) = (\zeta, 0, 0, \dots)$ reducing to $\zeta \bmod 3$. Passing to $\mathbb C$, however, requires embedding $\mathbb Q(\omega_8)$ ($\omega_8 = e^{2\pi i/8}$, minimal polynomial $\Phi_8(X) = X^4 + 1$). Modulo $3$, $\Phi_8$ splits into two quadratic factors:
   $$X^4 + 1 \equiv (X^2 + X + 2)(X^2 + 2X + 2) \pmod 3,$$
   corresponding to the two prime ideals $\mathfrak p_1 = (3, \omega_8^2 + \omega_8 + 2)$ and $\mathfrak p_2 = (3, \omega_8^2 + 2\omega_8 + 2)$ of $\mathbb Z[\omega_8]$ above $3$, each with residue field $\mathbb F_9$. Each ideal has two $\mathbb F_3$-identifications with $\mathbb F_9$ related by Frobenius $u \mapsto u^3$, giving all $\varphi(8) = 4$ injective multiplicative lifts $\theta_0^{(a)} : \zeta^n \mapsto \omega_8^{an}$ for $a \in (\mathbb Z/8\mathbb Z)^\times = \{1, 3, 5, 7\}$.
4. *Frobenius orbits and label permutation:* Under Frobenius $u \mapsto u^3$, exponents multiply by $3 \bmod 8$: the non-regular exponents $\{0\}$ and $\{4\}$ factor through $\operatorname{Nm}_{\mathbb F_9/\mathbb F_3}(u) = u^4$, while the $6$ regular exponents form the $3$ length-$2$ orbits $\{1, 3\}$, $\{5, 7\}$, and $\{2, 6\}$, matching $P_1(X) = X^2 + X + 2$ (roots $\{\zeta, \zeta^3\}$), $P_2(X) = X^2 + 2X + 2$ (roots $\{\zeta^5, \zeta^7\}$), and $P_3(X) = X^2 + 1$ (roots $\{\zeta^2, \zeta^6\}$). Fix `L.gen 2 = ζ` and compare `L_a` (built with $\theta_0^{(a)}$) against the baseline $L_1$ ($a = 1$) from Section 13.2.1(4). A fixed character $\chi$ with baseline root $x$ acquires the new root $x' = x^{a^{-1}} = x^a$ (since $a^2 \equiv 1 \pmod 8$ for every odd $a$):
   - For $a \in \{1, 3\} = \langle 3 \rangle$ (the Frobenius coset of $\mathfrak p_1$), $\zeta \mapsto \zeta$ or $\zeta^3$, so **all three polynomial labels $(P_1, P_2, P_3)$ stay unchanged**.
   - For $a \in \{5, 7\}$ (the coset of $\mathfrak p_2$; $a = 7$ is complex conjugation $\omega_8 \mapsto \overline{\omega}_8 = \omega_8^7$), $\zeta \mapsto \zeta^5$ or $\zeta^7$ while $\zeta^2 \mapsto \zeta^{10} = \zeta^2$ or $\zeta^{14} = \zeta^6$. Thus **changing the lift by $a \in \{5, 7\}$ swaps $P_1 \leftrightarrow P_2$ and fixes $P_3$**, matching the exchange of elliptic character values $\mp i\sqrt{2} \leftrightarrow \pm i\sqrt{2}$ between the $P_1$ and $P_2$ rows of the table in Section 13.2.1(4) while leaving the real-valued row $P_3$ untouched!

**Example 13.19 ($\mathbb F_{16} / \mathbb F_2$: degree-$4$ subfield strata, regular order-$5$ roots, and label permutation).** [Expository]
Now change both the characteristic and the extension degree: take $F = \mathbb F_2$ ($p = g = 2$), $d = 4$, and $K = \mathbb F_{16} = \mathbb F_2[\alpha]/(\alpha^4 + \alpha + 1)$, of cardinality $16$ and unit group order $N = 2^4 - 1 = 15 = 3 \times 5$.

1. *Characteristic, zero extension, and norm tower:* Because $15$ is odd ($\gcd(15, 2) = 1$), $X^{15} - 1$ is separable over $\mathbb F_2$; by contrast, $-1 \in \mathbb C^\times$ has order $2 = p$ and cannot lie in $\theta_0(\overline{\mathbb F}_2^\times)$ ($x^2 = 1 \implies (x + 1)^2 = 0 \implies x = 1$). Even without $-1$, $\alpha \neq 1$ gives $\theta_0(\alpha) \neq 1$, so $\theta_0(0) = \theta_0(0 \cdot \alpha) = \theta_0(0)\theta_0(\alpha)$ still forces $\theta_0(0) = 0$. Along the subfield tower $\mathbb F_2 \subset \mathbb F_4 \subset \mathbb F_{16}$ ($1 \mid 2 \mid 4$), $(2^1 - 1) = 1 \mid (2^2 - 1) = 3 \mid (2^4 - 1) = 15$; setting $\mathrm{gen}(4) = \alpha$ (order $15$), the norm-compatibility law `gen_norm` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:86`) forces $\mathrm{gen}(2) = \alpha^{(15)/3} = \alpha^5$ (order $3$, minimal polynomial $X^2 + X + 1$ over $\mathbb F_2$) and $\mathrm{gen}(1) = \alpha^{15} = 1$.
2. *Three Frobenius orbit-length strata and why regularity is weaker than primitivity:* Arithmetic Frobenius $u \mapsto u^2$ multiplies exponents modulo $15$ by $2$, partitioning $\mathbb Z/15\mathbb Z$ into five orbits:
   - $k = 0$: $\{0\}$ (size $1$, trivial character, root $1$ of $X + 1$);
   - $k \in \{5, 10\}$: orbit $\{5, 10\}$ of **size $2 \lt 4$**, factoring through $\operatorname{Nm}_{\mathbb F_{16}/\mathbb F_4}(u) = u^5$ (roots $\{\alpha^5, \alpha^{10}\}$ of $X^2 + X + 1$). Notice that $5 \cdot 2^1 = 10 \not\equiv 5 \pmod{15}$ passes the $i = 1$ test, yet $5 \cdot 2^2 = 20 \equiv 5 \pmod{15}$ fails `IsRegularChar 2 4` at $i = 2 \lt 4$!
   - $12$ regular exponents forming **three orbits of full length $4$**, which produce the three cuspidal irreducible characters of $\mathrm{GL}_4(\mathbb F_2)$ of degree $\prod_{i=1}^{3}(2^i - 1) = 1 \cdot 3 \cdot 7 = 21$:
     $$\begin{aligned}
     \{1, 2, 4, 8\} &\longleftrightarrow P_1(X) = X^4 + X + 1 \quad (\text{roots }\alpha, \alpha^2, \alpha^4, \alpha^8\text{ of order }15),\\
     \{7, 14, 13, 11\} &\longleftrightarrow P_2(X) = X^4 + X^3 + 1 \quad (\text{roots }\alpha^7, \alpha^{14}, \alpha^{13}, \alpha^{11}\text{ of order }15),\\
     \{3, 6, 12, 9\} &\longleftrightarrow P_3(X) = X^4 + X^3 + X^2 + X + 1 = \Phi_5(X) \quad (\text{roots }\alpha^3, \alpha^6, \alpha^{12}, \alpha^9\text{ of order }5).
     \end{aligned}$$
   Observe the third row: $\alpha^3$ has multiplicative order $5 \lt 15$, so it **does not generate $\mathbb F_{16}^\times$**, yet its minimal polynomial over $\mathbb F_2$ still has degree $4$ (because $2$ has multiplicative order $4$ modulo $5$, so $\mathbb F_2(\alpha^3) = \mathbb F_{16}$), making $\theta_3$ a genuine regular character!
3. *Changing the embedding:* Fix $\zeta_{15} = e^{2\pi i/15} \in \mathbb C^\times$. There are $\varphi(15) = 8$ injective lifts $\theta_0^{(a)} : \alpha^n \mapsto \zeta_{15}^{an}$ indexed by $(\mathbb Z/15\mathbb Z)^\times = \{1, 2, 4, 7, 8, 11, 13, 14\}$, corresponding to the modulo-$2$ factorization of the $15$-th cyclotomic polynomial:
   $$\Phi_{15}(X) = X^8 - X^7 + X^5 - X^4 + X^3 - X + 1 \equiv (X^4 + X + 1)(X^4 + X^3 + 1) \pmod 2.$$
   The Frobenius subgroup $\langle 2 \rangle = \{1, 2, 4, 8\}$ has index $2$ in $(\mathbb Z/15\mathbb Z)^\times$, with non-trivial coset $-\langle 2 \rangle = \{7, 14, 13, 11\}$. At fixed generator $\mathrm{gen}(4) = \alpha$, replacing $a = 1$ by $a \in \{1, 2, 4, 8\}$ fixes $(P_1, P_2, P_3)$, whereas any $a \in \{7, 14, 13, 11\}$ sends $x \mapsto x^{a^{-1}} \in \{x^7, x^{14}, x^{13}, x^{11}\}$, which **swaps $P_1 \leftrightarrow P_2$ and fixes $P_3 = \Phi_5$** (since $3 \cdot 13 = 39 \equiv 9 \in \{3, 6, 12, 9\} \pmod{15}$; indeed no multiplicative automorphism can carry an order-$5$ root of $P_3$ to an order-$15$ root of $P_1$ or $P_2$!).

**Three boundary calculations.** [Expository]

1. In $\mathbb F_3^\times=\{1,2\}$ take $u=2=-1$. Its order is two. For a unital multiplicative map $\theta_0$ injective on units, $\theta_0(2)^2=1$ and $\theta_0(2)\ne1$, so $\theta_0(2)=-1$. Then $0\cdot2=0$ gives $\theta_0(0)=-\theta_0(0)$ and hence $\theta_0(0)=0$. In characteristic three, $X^3-1=(X-1)^3$ and $X^2+X+1=(X-1)^2$. Both have only the root $1$.
2. Over $\mathbb F_2$, let $C=\begin{pmatrix}0&1\\1&1\end{pmatrix}$ and $M=\operatorname{diag}(1,C)$. We have $\det C=1$ and $\det(XI-C)=X^2+X+1$. A root $\xi$ satisfies $\xi^2=\xi+1$ and $\xi^3=1$. Hence $\xi^7=\xi\ne1$, although the whole invariant space has dimension three. The root has degree two and lies in $\mathbb F_{2^{3!}}$ since $2\mid6$. Its order divides $63$. If $\omega(\xi)=\zeta_3$, the root sum on $M$ is $1+\zeta_3+\zeta_3^2=0$ at exponent one and $3$ at exponent zero. At exponent seven the root sum is again $0$, so even on this invertible matrix the period $2^3-1$ fails for the root sum. The proper invariant subspaces are zero, the first coordinate line, and the companion plane. Indeed, the coprime factors of the characteristic polynomial give projections polynomial in $M$, and each summand is simple. At exponent one the recursive values on those subspaces are $0,1,-1$, since the two nonzero summands are simple. Thus the recursive value on $M$ is $0-1-(-1)=0$. At exponent zero the subspace values are $0,1,2$, and the recursive value is $3-1-2=0$.
3. On a one-dimensional space let $T=0$. The characteristic polynomial is $X$ with one root $0$. Lean's natural powers give $0^0=1$, so the root sum is $1$ at exponent zero and $0$ at every positive exponent. The sole proper invariant space is zero, with characteristic polynomial $1$ and recursive value zero. Thus $\psi$ also takes values $1$ and $0$, respectively. Both functions fail to have a positive additive exponent period on all endomorphisms. In particular a zero exponent cannot always be replaced by a positive representative.

---

**Definition 13.5 (Teichmüller lifts, finite-level tori, and parameter-label predicates).** [Lean, read]

1. *Multiplicative vs. zero-preserving Teichmüller maps:* For any finite field $F$, an *(unpointed) multiplicative Teichmüller map* is a monoid homomorphism $\theta_0 : \overline{F} \to^* \mathbb C$ injective on nonzero elements (`∀ x y, x ≠ 0 → y ≠ 0 → θ₀ x = θ₀ y → x = y`, as in `GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement.lean:7`, and `LabelDatum.teich`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:82–83`). Over `Fbar g := AlgebraicClosure (ZMod g)` (`src/Formalism/CyclotomicNorms/StatementT.lean:14`, $g$ prime), a *zero-preserving Teichmüller embedding* is an injective `MonoidWithZeroHom` $\omega : \mathrm{Fbar}\,g \to^{*_0} \mathbb C$; for $\iota : (\mathrm{Fbar}\,g)^\times \to^* \mathbb C^\times$, `GlobalTheory.GoodCharsCompare.Ext ι ω` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspidalCharacterFormula.lean:308`) states that `(ι u : ℂ) = ω u` for every unit $u \in (\mathrm{Fbar}\,g)^\times$.
2. *Torsion subgroups and norm maps (`LevelCuspCharacters.lean`):* For prime $p$ and $d \in \mathbb N$, `Tor p d := rootsOfUnity (p ^ d - 1) (Fbar p)` (`src/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/LevelCuspCharacters.lean:100`) is the subgroup of $(p^d - 1)$-th roots of unity in $(\mathrm{Fbar}\,p)^\times$; when $d \mid D$, `torNorm p h : Tor p D →* Tor p d` (`:102–108`) raises $u$ to $(p^D - 1)/(p^d - 1)$. Given $\theta : \mathrm{Tor}\,p\,d \to^* \mathbb C^\times$, `torVal θ : Fbar p → ℂ` (`:142–143`) extends $\theta$ by $0$ outside $\mathrm{Tor}\,p\,d$, and `cuspOn θ : Gn p d → ℂ` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LabelsCharOne.lean:29–32`, unfolding `cuspChar` at `src/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/LevelCuspCharacters.lean:147–153`) evaluates the explicit primary-eigenvalue character formula on $\mathrm{GL}_d(\mathbb F_p)$.
3. *`ParamLabel` and `GoodCharsCompare` labelings:*
   - Given `L : LabelDatum p`, `GlobalTheory.ParamLabel.LabelsChar L θ x` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LabelsCharOne.lean:13–14`) holds for $\theta : \mathrm{Tor}\,p\,d \to^* \mathbb C^\times$ and $x \in \mathrm{Fbar}\,p$ if $x^{p^d - 1} = 1$ and $\theta(u) = \mathrm{thetaOf}(L, d, x, u)$ for every $u \in \mathrm{Tor}\,p\,d$ (recalling from Definition 13.1(2) that `thetaOf L d x z` sends $z = (\mathrm{L.gen}\,d)^n$ to $(\mathrm{L.teich}\,x)^n$).
   - Without fixing finite-field generators, `rootC n := exp(2πi / n)` (`src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CuspValueComparison.lean:18`) fixes the standard primitive $n$-th root of unity in $\mathbb C$, and `labelChar ω d x y := ω x ^ sInf {a : ℕ | ω y = rootC (g ^ d - 1) ^ a}` (`:20–21`) pairs $x, y \in \mathrm{Fbar}\,g$ through $\omega : \mathrm{Fbar}\,g \to^{*_0} \mathbb C$ alone.
   - For a multiplicative automorphism $\beta : \mathrm{Fbar}\,g \simeq^* \mathrm{Fbar}\,g$ and polynomials $f, f' \in (\mathbb F_g)[X]$, `GlobalTheory.GoodCharsCompare.Tr β f f'` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspidalCharacterFormula.lean:137–138`) means that $f'$ is monic and its multiset of algebraic-closure roots satisfies `rootsBar f' = (rootsBar f).map β`.

**Lemma 13.20 (Torsion order, prime-to-$p$ separability, and zero extension).** [Lean, read] for the finite-order, preimage and `exists_ext` arguments. Automatic zero preservation for the bare multiplicative map is [Expository].

Let $F$ be a finite field of characteristic $p$ and cardinality $q$.

1. Every nonzero $x \in \overline{F}$ generates a finite extension $F(x)/F$ and satisfies $x^n = 1$ for some $n \gt 0$ coprime to $p$; when $F = \mathbb F_g$ ($g$ prime) and $d_x := \deg \operatorname{minpoly}_{\mathbb F_g}(x)$, one has $d_x \gt 0$ and $x^{g^{d_x} - 1} = 1$ (`exists_pow_eq_one_algebraicClosure_of_finite`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:9–20`; `dg_pos`, `pow_dg`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOrbitDegreeOverPrimeFieldFbar.lean:67–68, 204–206`).
2. For every prime $g$ and $d \gt 0$, the integer $g^d - 1 \gt 0$ casts to $-1 \neq 0$ in $\overline{\mathbb F}_g$, so $X^{g^d - 1} - 1$ is separable with exactly $g^d - 1$ distinct roots in $\overline{\mathbb F}_g$; consequently, every injective $\omega : \overline{\mathbb F}_g \to^{*_0} \mathbb C$ restricts to a bijection from $\{y \in \overline{\mathbb F}_g : y^{g^d - 1} = 1\}$ onto $\{z \in \mathbb C : z^{g^d - 1} = 1\}$ (`exists_preimage`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOrbitDegreeOverPrimeFieldFbar.lean:272–305`).
3. Every multiplicative monoid homomorphism $\theta_0 : \overline{F} \to^* \mathbb C$ injective on $\overline{F} \setminus \{0\}$ automatically satisfies $\theta_0(0) = 0$ and is globally injective on all of $\overline{F}$. Conversely, for every injective unit-group homomorphism $\iota : (\overline{\mathbb F}_g)^\times \to^* \mathbb C^\times$, setting $\omega(0) := 0$ and $\omega(x) := \iota(x)$ for $x \neq 0$ defines an injective $\omega : \overline{\mathbb F}_g \to^{*_0} \mathbb C$ satisfying `Ext ι ω` (`exists_ext`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspidalCharacterFormula.lean:312–351`).

*Proof.* (1) Every $x \in \overline{F}$ is integral over $F$, so $F(x)$ is finite-dimensional over $F$ (`IntermediateField.adjoin.finiteDimensional`, `:12`), hence a finite field (`Module.finite_of_finite F`, `:13`). If $x \neq 0$, then $x \in F(x)^\times$ is an element of a finite group, so $x^n = 1$ for $n = \lvert F(x)^\times \rvert = q^{[F(x):F]} - 1 \gt 0$ (`isOfFinOrder_of_finite`, `:17`), which is congruent to $-1 \pmod p$ and hence coprime to $p$. Over $\mathbb F_g$, $[ \mathbb F_g(x) : \mathbb F_g ] = d_x \gt 0$ gives $x^{g^{d_x}} = x$, and cancelling $x \neq 0$ yields $x^{g^{d_x} - 1} = 1$ (`pow_sub_one_eq_one_of_pow_pow_eq`, `pow_dg`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOrbitDegreeOverPrimeFieldFbar.lean:197–206`).

(2) In characteristic $g$, $(g^d - 1 : \overline{\mathbb F}_g) = g^d - 1 = 0 - 1 = -1 \neq 0$ (`hnF`, `:278–281`), so `separable_X_pow_sub_C` (`:282–283`) makes $X^{g^d - 1} - 1$ separable with $g^d - 1$ distinct roots in the algebraically closed field $\overline{\mathbb F}_g$ (`:284–287`). Injectivity of $\omega$ sends those $g^d - 1$ roots injectively into the $(g^d - 1)$-th roots of $1$ in $\mathbb C$, which have cardinality at most $g^d - 1$ (`card_nthRoots`, `:294–295`); by the pigeonhole principle (`Finset.eq_of_subset_of_card_le`, `:296–297`), the image is the entire complex group $\mu_{g^d - 1}(\mathbb C)$.

(3) If $p\ne2$, choose $u=-1$. If $p=2$, choose a root of $X^2+X+1$ in $\overline F$. Its values at both zero and one are $1$, so $u$ is a nonidentity unit in either case. Injectivity on nonzero elements gives $\theta_0(u)\ne1$. From $\theta_0(0)=\theta_0(0)\theta_0(u)$ we get $\theta_0(0)=0$. Also $\theta_0(x)\theta_0(x^{-1})=1$ for every $x\ne0$. This proves global injectivity. For the converse, the proof of `exists_ext` begins with the piecewise function at line 316. A product with a zero factor maps to zero. For two nonzero factors, `Units.mk0_mul` turns the required equality into multiplicativity of the original homomorphism. The image of a unit has nonzero complex value, so a collision between zero and a unit is impossible. On two units, equality of complex values gives equality of complex units, then injectivity of the original homomorphism gives equality of the arguments. Agreement on units follows by evaluating the nonzero branch. This proves `Ext` as well as uniqueness of the zero-preserving extension. $\square$

**Theorem 13.21 (Conditional supply of `(I1)` via Witt vectors, and the `LabelDatum` reduction model).** [Lean, read], conditional on Mathlib's Witt-ring domain, $p$-adic comparison, and algebraically-closed lifting instances (`WittVector.instIsDomain`, `WittVector.equiv`, `IsAlgClosed.lift`, [Lean]).

1. *(The `(I1)` producer `exists_teichmuller`)* For every finite field $F$, there exists a multiplicative monoid homomorphism $\theta_0 : \overline{F} \to^* \mathbb C$ injective on nonzero elements (and in fact satisfying $\theta_0(0) = 0$ and global injectivity on $\overline{F}$). *(Lean: `WittVector.teichmuller`, `Mathlib/RingTheory/WittVector/Teichmuller.lean:93`; `GlobalTheory.CuspGL.TeichEmb.exists_teichmuller`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:24–77`; statement wrapper `GlobalTheory.T.exists_teichmuller_map_algebraicClosure_finiteField`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement.lean:7–8`.)*
2. *(Inhabiting `LabelDatum g` via algebraic-integer reduction)* For every prime $g$, let $\overline{\mathbb Z} := \mathrm{integralClosure}\,\mathbb Z\,\mathbb C$ (`ZC`), choose a maximal ideal $Q \subset \overline{\mathbb Z}$ lying over $(g) \subset \mathbb Z$ to form a ring homomorphism $\mathrm{red}_g : \overline{\mathbb Z} \to \overline{\mathbb F}_g$, and put $\mathrm{ez}(n) := e^{2\pi i/n} \in \overline{\mathbb Z}$. Then $\mathrm{gen}(d) := \mathrm{red}_g(\mathrm{ez}(g^d - 1))$ has exact multiplicative order $g^d - 1$ for all $d \gt 0$ and satisfies $\mathrm{gen}(de)^{(g^{de}-1)/(g^d-1)} = \mathrm{gen}(d)$ for all $d, e \gt 0$; pairing $\mathrm{gen}$ with *any* `(t, ht)` as in (1) (or with the reduction-inverse lift `teichM g`) constructs a term `datumOf g t ht : LabelDatum g`. *(Lean: `exists_red`, `gen_prim`, `ez_pow`, `teichM`, `datumOf`, `datum`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemRootsBarXSubC.lean:12–220`.)*

*Proof.* **Part 1 (the Witt-vector production body).** First inspect Mathlib's `WittVector.teichmuller` (`Mathlib/RingTheory/WittVector/Teichmuller.lean:44–126`) for any prime $p$ and commutative ring $R$. Set $\tau_p(r) := (r, 0, 0, \dots) \in W_p(R)$ (`teichmullerFun`, `:44–45`). Evaluating the $n$-th Witt polynomial $W_n(X_0, \dots, X_n) = \sum_{i=0}^n p^i X_i^{p^{n-i}}$ at $\tau_p(r)$ kills every $i \gt 0$ term (since $0^{p^{n-i}} = 0$ for $p \gt 0$) and leaves $w_n(\tau_p(r)) = r^{p^n}$ (`ghostComponent_teichmullerFun`, `:62–69`), while ring homomorphisms $f : R \to S$ commute componentwise with $\tau_p$ because $f(0) = 0$ (`map_teichmullerFun`, `:71–75`). To prove $\tau_p(xy) = \tau_p(x)\tau_p(y)$ without assuming $p$ invertible in $R$, Mathlib runs Witt's three-step universal-polynomial argument:

- Over $R_{\mathbb Q} := \mathbb Q[X_r : r \in R]$, $p$ is invertible so the ghost map $W_p(R_{\mathbb Q}) \to (R_{\mathbb Q})^{\mathbb N}$ is bijective (`ghostMap.bijective_of_invertible`), and $(xy)^{p^n} = x^{p^n} y^{p^n}$ in every ghost coordinate proves $\tau_p(xy) = \tau_p(x)\tau_p(y)$ on $R_{\mathbb Q}$ (`teichmuller_mul_aux₁`, `:77–82`);
- Injecting $R_{\mathbb Z} := \mathbb Z[X_r : r \in R] \hookrightarrow R_{\mathbb Q}$ transfers multiplicativity to $R_{\mathbb Z}$ via `WittVector.map_injective` (`teichmuller_mul_aux₂`, `:84–88`, using `Mathlib/RingTheory/WittVector/Basic.lean:260`);
- Surjectivity of tautological evaluation $R_{\mathbb Z} \twoheadrightarrow R$ (`counit_surjective`) descends multiplicativity to arbitrary $R$, while $\tau_p(1) = (1, 0, 0, \dots) = 1_{W_p(R)}$ and $\tau_p(0) = (0, 0, 0, \dots) = 0_{W_p(R)}$ hold coordinate by coordinate (`teichmuller`, `:93–104`; `teichmuller_zero`, `:114–115`), with $0$-th coordinate projection $(\tau_p(r))_0 = r$ (`teichmuller_coeff_zero`, `:106–107`).

Now follow `exists_teichmuller` (`src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:24–77`) for a finite field $F$. Let $p := \operatorname{ringChar} F$; since $F$ is finite, $p \neq 0$, so $p$ is prime (`:28–30`), and the injective structure map $F \hookrightarrow \overline{F}$ gives $\overline{F}$ characteristic $p$ and makes it a perfect integral domain (`:31–33`). Form $W := W_p(\overline{F})$ (`:34`):

1. *Domain and characteristic zero (`:35–43`):* Because $\overline{F}$ is a characteristic-$p$ integral domain, $W$ is an integral domain (`IsDomain W`, `:35`, supplied by Mathlib's `WittVector.instIsDomain` at `Mathlib/RingTheory/WittVector/Domain.lean:117`). Composing the inverse of Mathlib's ring isomorphism $W_p(\mathbb Z/p\mathbb Z) \simeq \mathbb Z_p$ (`WittVector.equiv p`, `Mathlib/RingTheory/WittVector/Compare.lean:199`) with functoriality `WittVector.map` along $\mathbb Z/p\mathbb Z \hookrightarrow \overline{F}$ embeds $\mathbb Z_p \hookrightarrow W$ injectively (`:38–42`); since $\mathbb Z_p$ has characteristic $0$, so does $W$ (`hW : CharZero W`, `:43`)!
2. *Injective multiplicative lift into an algebraically closed overfield (`:44–55`):* Let $\Omega := \overline{\operatorname{Frac}(W)}$ (`:44`), which inherits characteristic $0$ via the injective ring map $g : W \hookrightarrow \operatorname{Frac}(W) \hookrightarrow \Omega$ (`:45–50`). Define $\iota := g \circ \tau_p : \overline{F} \to^* \Omega$ (`:51`). If $\iota(x) = \iota(y)$, injectivity of $g$ gives $\tau_p(x) = \tau_p(y)$ in $W$, and reading Witt coordinate $0$ recovers $x = y$ (`hι : Function.Injective ι`, `:52–55`).
3. *Landing inside $\overline{\mathbb Q}^{\,\Omega}$ and lifting to $\mathbb C$ (`:56–76`):* The construction needs only the elements algebraic over $\mathbb Q$. Lines `:56–67` verify that **every image $\iota(x)$ lies in the relative algebraic closure $\overline{\mathbb Q}^{\,\Omega}$ of $\mathbb Q$ in $\Omega$** (`hmem`): if $x = 0$, then $\iota(0) = g(\tau_p(0)) = g(0) = 0$ is algebraic over $\mathbb Q$ (`:59–64`); if $x \neq 0$, Lemma 13.20(1) supplies $n \gt 0$ with $x^n = 1$, whence $\iota(x)^n = \iota(x^n) = 1$ is integral (hence algebraic) over $\mathbb Q$ (`:65–67`). Because $\overline{\mathbb Q}^{\,\Omega}$ is algebraic over $\mathbb Q$ (`:68`) and $\mathbb C$ is algebraically closed of characteristic $0$, `IsAlgClosed.lift` produces a $\mathbb Q$-algebra embedding $\varphi : \overline{\mathbb Q}^{\,\Omega} \hookrightarrow \mathbb C$ (`:69`). Setting $\theta_0(x) := \varphi(\iota(x))$ preserves $1$ and multiplication (`:70–74`), maps $0 \mapsto \varphi(0) = 0$, and is injective because both $\varphi$ and $\iota$ are injective (`:75–76`).

**Part 2 (the reduction model `datumOf` and `teichM`).** In `MemRootsBarXSubC.lean:12–220`, since $(g)$ is maximal in $\mathbb Z$ and $\mathbb Z \hookrightarrow \overline{\mathbb Z}$ is an integral extension, going-up (`Ideal.exists_ideal_over_maximal_of_isIntegral`, `:21–22`) furnishes a maximal ideal $Q \subset \overline{\mathbb Z}$ contracting to $(g)$. The quotient field $\overline{\mathbb Z}/Q$ is algebraic over $\mathbb Z/g\mathbb Z$, so `IsAlgClosed.lift` embeds $\overline{\mathbb Z}/Q \hookrightarrow \overline{\mathbb F}_g$, giving $\mathrm{red}_g : \overline{\mathbb Z} \to \overline{\mathbb F}_g$ (`:23–42`). For $d \gt 0$, $X^{g^d - 1} - 1$ splits into distinct linear factors $\{X - \mathrm{ez}(g^d - 1)^i : 0 \le i \lt g^d - 1\}$ over $\overline{\mathbb Z}$ (`:71–79`) and remains separable over $\overline{\mathbb F}_g$ (`N_ne`, `:46–52, 81–82`), so $\mathrm{red}_g$ injects the $(g^d - 1)$-th roots of unity and $\mathrm{gen}(d) := \mathrm{red}_g(\mathrm{ez}(g^d - 1))$ has exact order $g^d - 1$ (`gen_prim`, `:67–100`). Because $\mathrm{ez}(m k)^k = e^{(2\pi i/(mk))\cdot k} = \mathrm{ez}(m)$ in $\mathbb C$ (`ez_pow`, `:101–116`) and $(g^d - 1) \mid (g^{de} - 1)$ (`N_dvd`, `:117–118`), applying $\mathrm{red}_g$ immediately gives `gen_norm` (`:214–215`), so `datumOf g t ht` (`:209–216`) turns any `(t, ht)` from Part 1 into a `LabelDatum g`! (Lines `:120–208` also construct a standalone lift `teichM g` directly from $\mathrm{red}_g$ by sending $x \neq 0$ of level $x^{g^d - 1} = 1$ to the unique prime-to-$g$ root of unity $\omega \in \overline{\mathbb Z}$ with $\mathrm{red}_g(\omega) = x$, checking uniqueness and multiplicativity on a common multiple level $d d'$ via `lifts_unique` and `lifts_mul`.) $\square$

**Lemma 13.22 (Frobenius equivariance, regular orbits, and argument-by-argument wiring into `ParamLabel`).** [Lean, read] (with item 3's primary-matrix identification `cuspOn_eq_psi` using the conditional primary-formula bridge `GlobalTheory.CuspFormula.cuspVal_eq_psi`, and cuspidality conditional on `isCharacter_cuspidal_rootSum_regular` at the depth of Sections 13.4.4–13.4.7).

1. *(Frobenius equivariance and exact orbit size)* For any multiplicative map $\theta_0 : \overline{F} \to^* \mathbb C$ and any $m \in \mathbb N$, $\theta_0(x^m) = \theta_0(x)^m$; in particular, for arithmetic Frobenius $\mathrm{Frob}_q(x) = x^q$, $\theta_0(\mathrm{Frob}_q^i(x)) = \theta_0(x)^{q^i}$. Over $\mathbb F_g$ ($g$ prime), every $y \in \overline{\mathbb F}_g$ satisfies $y^{g^{d_y}} = y$ and has $d_y = \deg \operatorname{minpoly}_{\mathbb F_g}(y)$ pairwise distinct Frobenius conjugates $y, y^g, \dots, y^{g^{d_y - 1}}$ (`frobenius_orbit_degreeOverPrimeFieldFbar`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOrbitDegreeOverPrimeFieldFbar.lean:72–138`). Consequently, if $\zeta \in \overline{F}$ has multiplicative order $\lvert F \rvert^d - 1$ ($d \gt 0$) and $\deg \operatorname{minpoly}_F(\zeta^k) = d$, then $k \lvert F \rvert^i \not\equiv k \pmod{\lvert F \rvert^d - 1}$ for all $0 \lt i \lt d$ (`exponent_regular_of_natDegree_minpoly_pow`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExponentRegularOfNatDegreeMinpolyGeneratorPow.lean:8–20`).
2. *(Exact argument wiring into `exists_cusp_of_regular` and `ParamLabel.isCusp_psi`)* In `GlobalTheory.GreenRegular.exists_cusp_of_regular` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:65–226`), given prime $g$, $d \gt 0$, and $[K : \mathbb F_g] = d$:
   - line `:85` calls Theorem 13.21(1) at $F = \mathbb Z/g\mathbb Z$ (`ZMod g`) to obtain $(\theta_0, h\theta_0)$;
   - lines `:86–130` choose $\iota : K \hookrightarrow_{\mathbb F_g} \overline{\mathbb F}_g$ via `IsAlgClosed.lift`, form the injective character $\lambda := (\mathrm{Units.map}\,\theta_0) \circ (\mathrm{Units.map}\,\iota) : K^\times \to^* \mathbb C^\times$ mapping a generator $\gamma \in K^\times$ to a primitive $(g^d - 1)$-th root of unity, represent each $\theta : K^\times \to^* \mathbb C^\times$ as $\lambda^{k(\theta)}$ (`kOf θ`), and translate `IsRegularChar g d θ` into `hreg θ hθ : ∀ i, 0 < i → i < d → ¬ kOf θ * Nat.card (ZMod g) ^ i ≡ kOf θ [MOD Nat.card (ZMod g) ^ d - 1]`;
   - line `:136` invokes `GlobalTheory.ParamLabel.isCusp_psi θ₀ hθ₀ hd (hreg θ hθ)` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18–49`), passing the exact tuple `(θ := θ₀, hθ := hθ₀, {d := d}, {k := kOf θ}, hd, hk := hreg θ hθ)`, which line `:23` forwards to `T.isCharacter_cuspidal_rootSum_regular (ZMod p) θ hθ d k hd hk` while lines `:179, 214` pass `(θ₀, hθ₀)` directly into `(I4)` and `(I5)`!
3. *(Connecting `LabelDatum` and torus parameters to `ParamLabel.isCuspOf_cuspOn`)* Let $p$ be prime, `L : LabelDatum p`, $\iota$ a finite index type of cardinality $d \gt 0$, $\theta : \mathrm{Tor}\,p\,d \to^* \mathbb C^\times$, and $x \in \mathrm{Fbar}\,p$ satisfying `LabelsChar L θ x` and $\deg \operatorname{minpoly}_{\mathbb F_p}(x) = d$. Then:
   - writing $x = (\mathrm{L.gen}\,d)^k$, one has $\mathrm{thetaOf}(L, d, (\mathrm{L.gen}\,d)^k, z) = (\mathrm{L.teich}\,z)^k$ for all $z^{p^d - 1} = 1$ (`thetaOf_gen`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:50–56`);
   - extending `Units.map L.teich` by zero via Lemma 13.20(3) produces an injective $\omega : \mathrm{Fbar}\,p \to^{*_0} \mathbb C$ agreeing with `L.teich` on $\mu_{p^d - 1}(\mathrm{Fbar}\,p)$, under which `cuspOn θ` equals $y \mapsto (-1)^{d-1}\psi(\mathrm{rootSum}\,\omega\,k)(\mathbb F_p^d, y)$ (`cuspOn_eq_psi`, `:70–100`) and satisfies `IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ)` (`isCuspOf_cuspOn`, `:102–153`, wrapped as `isCuspOf_cuspOn_of_green` at `:154–155` and `T.greenCuspidalChar_isCuspidalOfMinpoly_of_param` at `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParamStatement.lean:10–11`).
   Moreover, for every $d \gt 0$ and $\theta : \mathrm{Tor}\,p\,d \to^* \mathbb C^\times$, some $x \in \mathrm{Fbar}\,p$ satisfies `LabelsChar L θ x` (`exists_labelsChar_of_pos`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLabelsSemisimpleParameterGLFiniteField.lean:12–36`), `LabelsChar` makes $\theta^m = (\theta')^m \iff x^m = (x')^m$ (`Congr.pow_eq_iff`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LabelledCharactersEqAndCongrPrimeToPart.lean:85–118`), and norm composition `torNorm p h` ($d \mid N$) carries label $x$ of $\theta$ to label $x^n$ of $(\theta \circ \mathrm{torNorm})^n$ (`LabelNorm.labels_norm_pow`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFieldCharacterLabelsCompatNormPowInv.lean:40–55`).

*Proof.* (1) $\theta_0(x^m) = \theta_0(x)^m$ is `map_pow`. In `frobenius_orbit_degreeOverPrimeFieldFbar` (`:76–138`), $\mathbb F_g(y)$ has cardinality $g^{d_y}$ (`:82–85`), so $y^{g^{d_y}} = y$ (`:121–123`). Conversely, if $y^{g^k} = y$ for $k \gt 0$, then the $k$-th iterate of Frobenius fixes $\mathbb F_g(y)$ elementwise (`:88–97`), so every element of $\mathbb F_g(y)$ is a root of $X^{g^k} - X$, forcing $g^{d_y} \le g^k$ and $d_y \le k$ (`:98–119`); if $y^{g^i} = y^{g^j}$ with $0 \le i \lt j \lt d_y$, injectivity of Frobenius gives $y^{g^{j-i}} = y$ with $0 \lt j - i \lt d_y$, a contradiction (`:124–137`). In `exponent_regular_of_natDegree_minpoly_pow` (`:8–20`), if $k q^i \equiv k \pmod{q^d - 1}$ with $0 \lt i \lt d$ and $\zeta^{q^d - 1} = 1$, then $(\zeta^k)^{q^i} = \zeta^{k q^i} = \zeta^k$, so $\operatorname{minpoly}_F(\zeta^k) \mid X^{q^i} - X$, forcing $d = \deg \operatorname{minpoly}_F(\zeta^k) \mid i$ and hence $d \le i$, contradicting $i \lt d$.

(2) Each line in `ExistsCuspidalCharacterOfRegularCharacterGLn.lean:85–136` and `GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18–49` was verified in Proposition 13.6; here `(I1)` is discharged at `:85` by Theorem 13.21(1), and the only properties of $\theta_0$ consumed anywhere in `exists_cusp_of_regular` or `isCusp_psi` are monoid multiplicativity (`map_one`, `map_mul`, `map_pow`) and nonzero injectivity `hθ₀`.

(3) Fix `L : LabelDatum p` and $d = \lvert \iota \rvert \gt 0$. Because `L.gen d` has order $p^d - 1$, every $z$ with $z^{p^d - 1} = 1$ is $(\mathrm{L.gen}\,d)^n$ for some $n$; `Model.thetaOf_gen_pow` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemRootsBarXSubC.lean:224–244`) checks that `thetaOf` does not depend on the representative $n$ modulo $p^d - 1$, giving $\mathrm{thetaOf}(L, d, (\mathrm{L.gen}\,d)^k, (\mathrm{L.gen}\,d)^n) = (\mathrm{L.teich}((\mathrm{L.gen}\,d)^k))^n = (\mathrm{L.teich}((\mathrm{L.gen}\,d)^n))^k = (\mathrm{L.teich}\,z)^k$ (`thetaOf_gen`, `:50–56`). Extending `Units.map L.teich` by zero via `exists_ext` (`:111–119`) yields an injective $\omega : \mathrm{Fbar}\,p \to^{*_0} \mathbb C$ with $\omega(z) = \mathrm{L.teich}(z)$ whenever $z^{p^d - 1} = 1$, so $\theta(u) = \omega(u)^k$ on `Tor p d`. In `cuspOn_eq_psi` (`:70–100`), Lemma 13.20(2) (`exists_preimage`, `:77`) picks $x_1 \in \mu_{p^d - 1}(\mathrm{Fbar}\,p)$ with $\omega(x_1) = \mathrm{rootC}(p^d - 1)^k$, rewrites `torVal θ z = ω z ^ k = labelChar ω d x_1 z` on primary eigenvalues (`:82–93`), and applies `CuspFormula.cuspVal_eq_psi` (`:94`) plus basis reindexing `Fintype.equivFin ι` (`:95–100`). In `isCuspOf_cuspOn` (`:102–153`), writing $x = (\mathrm{L.gen}\,d)^k$ (`:110`) and applying part (1)'s `exponent_regular_of_natDegree_minpoly_pow` (`:129`) feeds `isCusp_psi` (`:128`) for cuspidality; for any root $x_0 = x^{p^j}$ of $\operatorname{minpoly}_{\mathbb F_p}(x)$ (`:131`) and any root $z$ of an irreducible $\operatorname{charpoly}(y)$, cyclic shift invariance $\sum_{i \lt d} (\omega(z)^{p^j})^{k p^i} = \sum_{i \lt d} \omega(z)^{k p^i}$ (`sum_shift`, `:144–145`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOrbitDegreeOverPrimeFieldFbar.lean:443–470`) identifies the root power sum with $\sum_{i \lt d} \mathrm{thetaOf}(L, d, x^{p^j}, z^{p^i})$ (`:146–152`). Finally, `exists_labelsChar_of_pos` (`:18–35`) uses primitivity of `L.teich (L.gen d)` in $\mu_{p^d - 1}(\mathbb C)$ to solve $\theta(\mathrm{L.gen}\,d) = \mathrm{L.teich}(\mathrm{L.gen}\,d)^k$ and sets $x := (\mathrm{L.gen}\,d)^k$; `Congr.pow_eq_iff` (`:85–118`) evaluates at `L.gen d` and cancels via `L.teich_inj`; and `labels_norm_pow` (`:40–55`) uses `L.gen_norm` so `torNorm` sends $(\mathrm{L.gen}\,N)^k \mapsto (\mathrm{L.gen}\,d)^k$. $\square$

**Proposition 13.23 (Choice of lift, coordinates, and the resulting character).** [Expository] for the common finite layer argument. The formal comparison lemmas used below are [Lean, read] at the scope recorded in the source table.

Let $g$ be prime, $d\ge1$, $F=\mathbb F_g$, and $[K:F]=d$. Write $N=g^d-1$. A lift $\omega$ means an injective zero-preserving multiplicative map from $\overline F$ to $\mathbb C$. Write $\psi_{\omega,k}(V,T)$ for the inverse on invariant subspaces with input $s_{\omega,k}(P)=\sum_{\xi\in\operatorname{roots}(P)}\omega(\xi)^k$, counting roots in $\overline F$ with multiplicity. For an $F$-embedding $\iota:K\hookrightarrow\overline F$ put $\lambda=\omega\circ\iota$ on $K^\times$. There is a unique exponent class $k$ modulo $N$ with $\theta=\lambda^k$. The value assigned to $\theta$ at $T\in\mathrm{GL}_d(F)$ is $(-1)^{d-1}\psi_{\omega,k}(F^d,T)$. This function is independent of the lift, the embedding, and the natural-number representative of $k$. For regular $\theta$, the preceding character theorem identifies it as cuspidal.

*Comparison on a common finite layer.* A lift maps the units of each $\mathbb F_{g^e}$ bijectively onto the $(g^e-1)$-st complex roots of unity by injectivity and equality of cardinalities. Every element of $\overline F^\times$ lies in one of these groups. Conversely each order prime to $g$ divides $g^e-1$ for some $e\ge1$, since $g$ is invertible modulo that order. Thus any two lifts have the same image. The map $\alpha=\omega^{-1}\circ\omega'$ is the unique multiplicative bijection with $\omega\circ\alpha=\omega'$. It preserves multiplicative orders and acts on each finite cyclic layer by a unit power, since it takes a generator to a generator. These are the comparisons in `exists_alpha` and `exists_exp`.

Set $D=d!$, $L=\mathbb F_{g^D}\subset\overline F$, and $B=g^D-1$. Let $R$ be the exponent of $\alpha$ on $L^\times$, a unit modulo $B$. For any $T$-invariant subspace $W$ of dimension $a$, the restriction $T|_W$ is injective and hence bijective. A root $\xi$ of its characteristic polynomial is nonzero and its minimal polynomial divides that characteristic polynomial. Thus $e=\deg\operatorname{minpoly}_F(\xi)$ satisfies $1\le e\le a\le d$. The zero-dimensional restriction has no roots. Since $e\mid d!$, $\xi$ belongs to $\mathbb F_{g^e}\subset L$ and has order dividing $B$. In the primary case the polynomial is a power of one irreducible and $e\mid a$; this is the case in which `root_pow` gives the smaller period $g^a-1$.

Choose natural exponents $k,m$ with $Rm\equiv k\pmod B$. For every root at every restriction,
$$\omega'(\xi)^m=\omega(\xi)^{Rm}=\omega(\xi)^k.$$
Summing over the unchanged multiset gives equality of the polynomial inputs on each restriction. The equality includes an empty multiset and includes exponent zero under the stated congruence.

In Lean, `invariantSubspaceMobiusInverseRec` starts at zero at depth zero. At depth $n+1$ it takes the input at the current characteristic polynomial and subtracts the sum of depth-$n$ values on all proper invariant subspaces. Induct on common depth, simultaneously for all $T|_W$. At depth zero both values vanish. At depth $n+1$ the polynomial inputs agree. A proper invariant subspace for $T|_W$ is itself $T$-invariant and its iterated restriction acts by the same operator as its direct restriction. Every summand agrees by the induction hypothesis. Taking depth $d+1$, the depth defining `psi` on $F^d$, gives $\psi_{\omega',m}(F^d,T)=\psi_{\omega,k}(F^d,T)$.

*Descent to the intrinsic parameter.* Both embeddings of $K$ have image the unique degree-$d$ subfield, and $\iota'=\operatorname{Frob}_g^j\circ\iota$ for some $0\le j\lt d$. Thus $\lambda'=\lambda^{Rg^j}$. If $\theta=(\lambda')^{k'}=\lambda^k$ then $Rg^j k'\equiv k\pmod N$. Choose $m$ with $Rm\equiv k\pmod B$. Since $N\mid B$, cancellation gives $m\equiv g^j k'\pmod N$. To pass from $m$ to $k'$ with the lift $\omega'$ fixed, use (I4) and (I5) of §13.4.6. For a test exponent $l$, the Gram pairing is the order of the group times the number of $0\le i\lt d$ with $mg^i\equiv l\pmod N$. This count equals that for $k'$ because $i\mapsto i+j\bmod d$ permutes the indices and $g^d\equiv1\pmod N$. The primitive class-function expansion uses the same test functions for both exponents. All coefficients agree and the common normalization is nonzero. Hence the functions agree pointwise on $\mathrm{GL}_d(F)$, and the sign is the same in both constructions. With $j=0$ this also proves independence of representatives. For $k=0$ take $m=0$, even if $k'$ was chosen positive. This reasoning includes $N=1$, whose exponent group has one class. The archive's fixed-lift orbit step is in `exists_cusp_of_regular`, lines 206–225. The common-layer comparison applies its formula across different choices.

For the elliptic trace, replacing a root $z$ of an irreducible degree-$d$ characteristic polynomial by $z^{g^j}$ rotates the list in $\sum_{i=0}^{d-1}\theta(z^{g^i})$. With a fixed lift the reverse implication on regular parameters follows from testing equality of GL functions against the second exponent in (I4). Its self-count contains $i=0$, so the first exponent has a Frobenius iterate equal to the second modulo $N$. This is the argument at lines 184–205.

*Explicit generators and polynomial labels.* For a label datum $(\omega,v)$ in degree $d$, the label $x$ denotes the character sending $z=v^n$ to $\omega(x)^n$. Thus $x=v^k$ denotes the $k$-th power of the lift on the layer. Frobenius sends $x$ to $x^g$ and raises the character to its $g$-th power. The regular labels are exactly the roots of degree $d$ by Lemma 13.22. If $\omega'(u)=\omega(u^a)$ on this layer and $v'=v^b$, then $z=(v')^{b^{-1}n}$. Substitution yields
$$\mathrm{thetaOf}(L',d,x',z)=\mathrm{thetaOf}(L,d,(x')^{ab^{-1}},z).$$
A fixed character therefore has $x'=x^{a^{-1}b}$. This power bijection commutes with Frobenius and so transports the polynomial label to $\operatorname{minpoly}_F(x')$. It also compares the elliptic traces in `IsCuspOf` term by term over the corresponding label roots. With the generator fixed, the kernel on primitive polynomial labels is exactly $\langle g\rangle$, since a primitive $x$ satisfies $x^{a^{-1}}=x^{g^j}$ precisely when $a^{-1}\equiv g^j\pmod N$. With norm-compatible generators, the pulled-back character takes on the large generator the original value on the small generator. Its label is the same element viewed in the larger field. In exponent coordinates the multiplier from degree $d$ to degree $D$ is $(g^D-1)/(g^d-1)$.

*Fixed complex reference root and the square.* Let $c_N=\exp(2\pi i/N)$ as in `rootC`. The implicit generator of `labelChar` is $\omega^{-1}(c_N)$. Write $\omega(y)=c_N^n$ and $\omega(x')=c_N^s$. Under $\omega'$ the same elements have logarithms $an$ and $as$, so
$$\mathrm{labelChar}(\omega',d,x',y)=c_N^{a^2sn}
 =\mathrm{labelChar}(\omega,d,\beta(x'),y),\qquad \beta=\alpha\circ\alpha.$$
This is `exists_beta`. The same direction is visible in the recursive formula. The exponent of $x'$ relative to the reference root and $\omega'$ is $as\bmod N$, while the exponent of $\beta(x')$ relative to $\omega$ is $a^2s\bmod N$. With the field embedding fixed, these exponents give the same intrinsic character since $\omega'(y)^{as}=\omega(y)^{a^2s}$ on the degree-$d$ torus. Proposition 13.23 gives equality on the whole general linear group, and `cuspVal_eq_psi` identifies these pointwise values with the two primary formulas. The explicit-generator rule gives the same result because the implicit generator moves by $b=a^{-1}$, so the label of a fixed character moves by $a^{-2}$. In degree one the same pairing transports tame labels on base-field units. Evaluation at the preimage of $c_{g-1}$ recovers the label by injectivity, and inversion of the character sends the label to its inverse.

The map $\beta$ carries the full root orbit of $\operatorname{minpoly}_F(x')$ to that of $\operatorname{minpoly}_F(\beta(x'))$. Factoring a monic polynomial and carrying each orbit with its multiplicity gives the unique monic polynomial with the transported root multiset. This is `Tr`, with inverse given by $\beta^{-1}$. It preserves degrees, divisibility, squarefreeness and the absence of a zero root. The prime-to-$\ell$ part commutes with transport since it uses only multiplicative order and exponentiation.

For an invertible matrix with primary characteristic polynomial, all its distinct roots lie in the torsion layer of the matrix size by `root_pow`. The coefficient outside the sum in `cuspVal` depends only on the matrix, so `exists_beta` compares the summands with that coefficient fixed. On the other branch `cuspVal` is zero for both labels. This gives `cuspVal_congr`. In `isTypeChar_tr` apply it in every diagonal block, transporting the root and polynomial labels and preserving the block representation and its induced character. The displayed direction in `FullGood.change` is from the primed datum to the unprimed datum. Transport the matching base-field labels by the same root bijection. Degree and squarefree conditions survive, equalities of prime-to-$\ell$ parts pull back by injectivity, and both remaining factor conditions follow by divisibility and inverse transport. A forbidden divisor of prescribed degree would pull back to a forbidden divisor of the same degree, while the required large prime-degree irreducible factor maps to another irreducible of that degree.

*The conditional block-formula interface.* The identifier `CuspidalCharacterFormula` is a proposition. For a specified lift and cuspidal block datum it supplies nonzero labels of degree the corresponding block size and expresses the character as the product of the `cuspVal` functions. The proof `typeChar_full_of_torus` takes this proposition as $H$ and uses `Ext` to compare the unit-group lift with the zero-preserving lift. For a fixed block choose a root of its prescribed torus polynomial. Vary the torus element in that block through preimages of all powers of the reference root, with the other blocks at the unit. The proof constructs these test matrices by `exists_block`. The other blocks give identical nonzero factors on both sides, and `torus_coef_ne` gives the nonzero scalar in the active block. After cancellation and use of `sum_period` to extend the test sums to the full block degree, sums of powers for the two complex Frobenius orbits agree. The supplied `mem_orbit_of_sums` gives orbit membership. Injectivity then gives the desired equality of finite-field minimal polynomials. The consumer uses $H$ as input. The separate `CuspFormula.cuspVal_eq_psi` bridge compares the primary formula with the recursion on invertible matrices. Its hypothesis on the label is $\omega(x)=c_N^k$ with $x$ in the degree-$d$ torsion layer. In the primary branch, choose a root $y$ of the irreducible factor and write the characteristic polynomial as $P^m$ for $P=\operatorname{minpoly}_F(y)$. The distinct roots are exactly the roots of $P$, and their number is $e=\deg P$. The kernel-dimension input gives the dimension of $\ker P(T)$ as $e$ times the eigenspace dimension, for every root of $P$. Thus the eigenspace dimensions agree. The primary Möbius identity now gives $\psi_{\omega,k}=s_{\omega,k}(P)\prod_{1\le i<t}(1-g^{ei})$, where $t$ is that eigenspace dimension. For a root $z$ of $P$, write $\omega(z)=c_N^n$ using the primary root bound. The term $\mathrm{labelChar}(\omega,d,x,z)$ is $(c_N^k)^n=\omega(z)^k$. The distinct-root sum and the factors therefore agree after inserting the sign $(-1)^{d-1}$. In the nonprimary branch the supplied vanishing theorem for primitive class functions gives zero, matching the definition of `cuspVal`.

**Remarks 13.4.9.**

1. *Comparison with Green (1955) and Witt-vector formalization.* For matrices of fixed size $n$ over $\mathrm{GF}(q)$, Green works inside the finite universal splitting field $\mathfrak F^\ast = \mathrm{GF}(q^{n!})$ ([Green1955, §1, p. 405]). In his proof of Theorem 1 ([Green1955, §3, p. 414]), Green explicitly notes that any two multiplicative isomorphisms $\theta, \phi : M(\mathfrak F^\ast) \hookrightarrow \mathbb C^\times$ satisfy $\theta = \phi^r$ for some integer $r$ (matching Proposition 13.23(1)), and constructs one such $\phi$ by reducing the $(p^a - 1)$-th roots of unity of $\mathbb Q(\zeta_{p^a - 1})$ modulo a prime ideal $\mathfrak p \mid p$ and inverting the reduction map. In the archive, `GlobalTheory.GLq.Model.teichM` (`MemRootsBarXSubC.lean:12–208`, Theorem 13.21(2)) globalizes Green's reduction method to $\overline{\mathbb Z}/Q \hookrightarrow \overline{\mathbb F}_g$ across all degrees at once, whereas the `(I1)` supplier `TeichEmb.exists_teichmuller` (`ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:24–77`, Theorem 13.21(1)) goes in the opposite direction via $p$-typical Witt vectors $W_p(\overline{F})$ ([Hazewinkel2009]; [CommelinLewis2021]) and `IsAlgClosed.lift`, working uniformly for every finite field $F$ without choosing compatible roots of unity in $\mathbb C$ beforehand.
2. *Where the condition $5 \le p$ enters — and where it does not.* Theorem 13.21, Lemma 13.22, and Proposition 13.23 hold for **every** prime ($p = 2, 3$ included, as in Examples 13.18–13.19). In `GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:154–155`, the wrapper `isCuspOf_cuspOn_of_green` takes both `Green` and `5 ≤ p` as unused hypotheses (`fun _ _ _ L _ ... => isCuspOf_cuspOn L θ x hd hL hx`), matching the interface expected by `Labels.series` (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimeToPartFrob.lean:144, 159`). In `PrimeToPartFrob.lean`, the assumption `5 ≤ p` is actually used in `good_iff` (`:92, 133–134`, to ensure the auxiliary prime $\ell = 2$ satisfies $2 \neq p$) and in `GLq.Label.lab_eq` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HarishChandraSeriesLabelExistsUniqueGLn.lean:78–83`, via `cuspidalCharacter_label_unique_GLn`). Besides `ExistsCuspidalCharacterOfRegularCharacterGLn.lean:85` and `CuspidalCharacterFormula.lean:3`, `(I1)` is also imported by `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:220` (proving primitive irreducible characters of $\mathrm{GL}_d(F)$ are determined by their elliptic values), `PResEmbEx.lean:3`, and `IsIrreducibleTransportRep.lean:5` [Lean].
3. *Scope of the reading.* The primary bridge proof and the conditional block consumer are read at their stated interfaces. The source table names the deeper primary and block inputs. The supply of (I2), (I8), and the deeper hypotheses of §§13.4.4–13.4.8 retain their earlier reading levels here; §13.4.10 reads (I2) and (I8). For singular endomorphisms the termwise common-layer comparison also works when both exponents are positive (zero roots contribute zero), or both are zero. The example with characteristic polynomial $X$ precludes the unrestricted claim with one exponent zero and the other positive.

**Table 13.4.9 (source-to-text map).** Paths are relative to `lean/` in the pinned archive `lean.tar.gz` (SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`), or to Mathlib at commit `0df444a360eaa60ab8c11dca51a86af692955474`.

| Reading | Role in §13.4.9 | Archive / Mathlib path and lines |
|---|---|---|
| R3 / [Lean, read] | `(I1)` statement wrapper `T.exists_teichmuller_map_algebraicClosure_finiteField` | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteFieldStatement.lean:7–8` |
| R3 / [Lean, read] | Finite-order helper and `(I1)` Witt-vector producer `CuspGL.TeichEmb.exists_teichmuller` | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:9–77` |
| R3 / [Lean, read] | `WittVector.teichmuller`, ghost components, polynomial reduction, `teichmuller_coeff_zero`, `teichmuller_zero` | `Mathlib/RingTheory/WittVector/Teichmuller.lean:44–126` (commit `0df444a`) |
| R3 / [Lean, read] | Parallel algebraic-integer reduction model `exists_red`, `gen_prim`, `ez_pow`, `teichM`, `datumOf`, `thetaOf_gen_pow`, `thetaOf_norm` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemRootsBarXSubC.lean:12–254` |
| R3 / [Lean, read] | Main-path `(I1)` call site, $\lambda = \theta_0 \circ \iota$, exponent `kOf`, regularity `hreg`, call to `ParamLabel.isCusp_psi` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:65–225` |
| R3 / [Lean, read] | `ParamLabel.isCusp_psi`, `thetaOf_gen`, `torVal_eq`, `cuspOn_eq_psi` (cond. on `cuspVal_eq_psi`), `isCuspOf_cuspOn`, `isCuspOf_cuspOn_of_green` + wrapper | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18–156`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParamStatement.lean:10–11` |
| R3 / [Lean, read] | Regularity of generator-power exponents `CuspGL.exponent_regular_of_natDegree_minpoly_pow` + wrapper | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExponentRegularOfNatDegreeMinpolyGeneratorPow.lean:8–20`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement.lean:7–8` |
| R3 / [Lean, read] | Frobenius orbit size `frobenius_orbit_degreeOverPrimeFieldFbar`, `pow_dg`, `exists_prim`, `labelChar_eq`, `exists_preimage`, `sum_shift` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOrbitDegreeOverPrimeFieldFbar.lean:63–305` |
| R3 / [Lean, read] | Change-of-embedding automorphisms `exists_alpha`, `exists_exp`, `exists_beta`, polynomial transport `Tr`, `tr_minpoly`, `exists_tr`, `isGood_tr`, `isTypeChar_tr`, zero extension `exists_ext`, and `FullGood.change` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspidalCharacterFormula.lean:52–85, 126–351`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GoodFamilyOfRealised.lean:43–67` |
| R3 / [Lean, read] | `LabelsChar` existence, power/congruence equivalence, and norm compatibility | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLabelsSemisimpleParameterGLFiniteField.lean:12–71`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LabelledCharactersEqAndCongrPrimeToPart.lean:73–127`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFieldCharacterLabelsCompatNormPowInv.lean:15–83` |
| Definitions | `Fbar`, `rootsBar`; `LabelDatum`, `thetaOf`, `IsCuspOf`; `Tor`, `torNorm`, `torVal`, `cuspChar`; `LabelsChar`, `cuspOn`; `rootC`, `labelChar`, `IsTypeChar` | `src/Formalism/CyclotomicNorms/StatementT.lean:14–18`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:81–97`; `src/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/LevelCuspCharacters.lean:98–154`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LabelsCharOne.lean:13–33`; `src/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/CuspValueComparison.lean:18–46` |
| R2 / [Lean] | Mathlib Witt-vector functoriality, domain, and $p$-adic ring isomorphism (`map_injective`, `instIsDomain`, `equiv`) | `Mathlib/RingTheory/WittVector/Basic.lean:253, 260`; `Mathlib/RingTheory/WittVector/Domain.lean:117`; `Mathlib/RingTheory/WittVector/Compare.lean:199` (commit `0df444a`) |
| Definitions and R3 | `rootSum`, finite-depth recursion, stabilization and `psi_eq` | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:24–66` |
| R3 / [Lean, read] | Primary root bound and pointwise transport, `root_pow` and `cuspVal_congr` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspidalCharacterFormula.lean:88–135` |
| Definition and conditional R3 | Block formula hypothesis and its consumer, `CuspidalCharacterFormula` and `typeChar_full_of_torus` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspidalCharacterFormula.lean:380–502` |
| Conditional R3 | Primary and nonprimary branches of `CuspFormula.cuspVal_eq_psi` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLabel.lean:132–185` |
| R2 / [Lean] | Inputs to the primary branch, `T.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace'` and `T.invariantSubspaceMobiusInverseCharpoly_primary_eq` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAlStatement.lean:5`, `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InvariantSubspaceMobiusInverseCharpolyPrimaryEqStatement.lean:7` |
| R2 / [Lean] | Input to the zero branch, `T.classFn_eq_zero_of_charpoly_not_irreducible_pow` | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqZeroOfNotPrimaryStatement.lean:6` |
| R2 / [Lean] | Block-test inputs `exists_matrix`, `cuspVal_eq_torusValue`, `sum_period`, `period_of`, `mem_orbit_of_sums` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FrobeniusOrbitDegreeOverPrimeFieldFbar.lean:306,393,472,484,489` |
| Interfaces consumed from §13.4.6 | Gram and primitive expansion identities (I4)/(I5) | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvertibleEndInnerProductRootPowerSumMobiusStatement.lean:7`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/PrimitiveClassFunctionExpansionRootSumsStatement.lean:7` |

### 13.4.10 From a norm-one virtual character to a positive irreducible character

> **Reading levels.** `R3` / [Lean, read] for the last steps of `CuspGL.isChar_psi_rootSum_of_regular`
> (`IsCharacterCuspidalRootSumRegular.lean:119–184`), the simplicity branch of `ParamLabel.isCusp_psi`
> (`GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:22–38`), the degree step of `exists_cusp_of_regular`
> (`ExistsCuspidalCharacterOfRegularCharacterGLn.lean:137–142`), and the production proofs of (I2)
> `CuspGL.psi_one` and of (I8) `BI.irr_of_norm_one`, `CuspGL.star_virt_eq_inv` and `CuspGL.extZero_spec`,
> down to the interfaces listed in Table 13.4.10. The deeper inputs named in the last rows of that table are
> `R2` / [Lean]. The inputs (I1), (I3)–(I7) and (I9) are used at the reading levels recorded in
> §§13.4.5–13.4.9 and are not reopened here. Paths are relative to `lean/` in the pinned `lean.tar.gz`
> (SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`). Mathlib paths are at commit
> `0df444a360eaa60ab8c11dca51a86af692955474`.

**Motivation.** Let $F=\mathbb F_q$, $d>0$ and $G=\mathrm{GL}_d(F)$. For a regular exponent $k$ write
$\psi_k(x)=\psi_{s_k}(F^d,x)$ for the Möbius inverse of Definition 13.3. Steps 1 and 2 of Proposition 13.6
supply two facts. First, $\psi_k$ is an integer combination of irreducible characters, by (I6) and (I7)
(§§13.4.5 and 13.4.7). Second, $\sum_{x\in G}\lvert\psi_k(x)\rvert^2=\lvert G\rvert$, by (I3)–(I5) (§13.4.6).
The candidate $\psi_k$ has norm one as a virtual character. Its sign is positive in odd dimension and negative in even dimension. The archive uses three ingredients to certify the signed candidate.

1. *A lattice fact.* In the lattice $R(G)$ with its orthonormal basis of irreducible characters, a vector
   of length one is plus or minus a basis vector.
2. *A sign.* A genuine character takes the value $\dim V>0$ at the identity. So the sign is decided by
   $\psi_k(1)$. At the identity every subspace is invariant, and the recursion becomes a count over the
   whole subspace lattice.
3. *An interface.* `BI.IsChar` asks for a matrix representation $G\to\mathrm{GL}_n(\mathbb C)$ with the
   given trace, while `IsCusp` asks for a simple object of the category `FDRep ℂ G`. The archive passes
   from one to the other through Mathlib's norm criterion, which needs
   $\overline{\chi(x)}=\chi(x^{-1})$.

The two examples show each ingredient at work. They also show that the norm condition and the positivity of
the degree each do real work.

**Example 13.24 ($\mathrm{GL}_1(\mathbb F_q)$ and the empty case).** [Expository; the cases $q=2,3,5,7$ are
checked by `check_positive_sign.py`, see Table 13.4.10] Take $d=1$, so $G=F^\times$ and $V=F$. The only proper
subspace of $V$ is $0$, where the recursion gives $\psi(0,\cdot)=s_k(1)=0$. Hence for $x\in F^\times$
$$\psi_k(x)=s_k(X-x)-\psi(0,\cdot)=\theta_0(x)^k .$$
Since $x^{q-1}=1$, the value $\theta_0(x)$ is a $(q-1)$-st root of unity, and $\psi_k$ is the linear
character $x\mapsto\theta_0(x)^k$. Every exponent is regular, because the condition of Lemma 13.5(iv) is
empty when $d=1$.

- *Value at $1$.* Both subspaces are invariant under $1$, and $\psi_k(1)=s_k(X-1)-\psi(0,1)=1-0=1$. This
  is the empty product $\prod_{1\le i<1}(1-q^i)$ of (I2). The sign $(-1)^{d-1}$ is $+1$.
- *Norm.* $\sum_{x\in F^\times}\theta_0(x)^k\,\overline{\theta_0(x)^k}=q-1=\lvert G\rvert$, because
  $\lvert\theta_0(x)\rvert=1$.
- *Inverse and conjugate.* $\theta_0(x)\theta_0(x^{-1})=\theta_0(1)=1$ and $\lvert\theta_0(x)\rvert=1$ give
  $\overline{\theta_0(x)^k}=\theta_0(x^{-1})^k$. So Mathlib's sum $\sum_x\chi(x)\chi(x^{-1})$ is
  $\sum_x1=q-1$, and the one-dimensional representation $\rho_k(x)=(\theta_0(x)^k)$ gives a simple object
  $\mathrm{FDRep.of}\,\rho_k$.
- *Norm one leaves the sign open.* The function $-\psi_k$ also lies in $R(G)$ and has the same norm
  $q-1$. Its value at $1$ is $-1$, and no representation has dimension $-1$. Two candidates have norm
  one, and only the value at $1$ separates them.
- *The empty case $d=0$.* Here $V=0$ and $\mathrm{GL}_0(F)=\{1\}$, and $\psi(0,1)=s_k(1)=0$. The candidate
  is the zero function. Its norm is $0\ne1=\lvert\mathrm{GL}_0(F)\rvert$, and its value at $1$ is $0$, not
  the empty product $1$. This is why (I2) assumes $\dim V>0$, and why the consumer and `IsCusp` assume
  $d>0$.
- *Outside the group.* At the singular endomorphism $x=0$ of $V$ the recursion gives $\theta_0(0)^k$. This
  is $1$ for $k=0$, by Lean's convention $0^0=1$, and $0$ for $k>0$. The value never enters the argument
  below, which evaluates $\psi_k$ only at invertible arguments (Remark 13.4.10(2)).

**Example 13.25 ($\mathrm{GL}_2(\mathbb F_3)$ with a regular and a nonregular exponent).** [Expository;
every number below is checked in exact arithmetic in $\mathbb Q(\zeta_8)$ by `check_positive_sign.py`]
Keep the notation of Example 13.3: $q=3$, $\mathbb F_9=\mathbb F_3[\zeta]$ with $\zeta^2+\zeta+2=0$, and
$\theta_0(\zeta^n)=\omega^n$ with $\omega=e^{2\pi i/8}$. Then $\theta_0(1)=1$ and
$\theta_0(2)=\theta_0(\zeta^4)=-1$. The group has order $(9-1)(9-3)=48$.

*(a) The identity value by counting subspaces.* The space $V=\mathbb F_3^2$ has one zero subspace,
$(9-1)/(3-1)=4$ lines and one plane, all invariant under $1$. The recursion gives $\psi(0,1)=0$ and
$\psi(L,1)=s_k(X-1)-0=1$ on each line $L$, and then
$$\psi_k(1)=s_k\bigl((X-1)^2\bigr)-\bigl(\psi(0,1)+4\,\psi(L,1)\bigr)=2-4=-2=1-q .$$
In the notation of Lemma 13.26 this is $\sum_{W}\omega_3(\dim W)=0+4\cdot1+1\cdot(-2)=2=\dim V$. The
counts come from Lemma 13.26(1) with every factor displayed: $N_1\,(3-1)=9-1$ gives $N_1=4$, and
$N_2\,(9-1)(9-3)=(9-1)(9-3)$ gives $N_2=1$. The value $-2$ is the same for all $k$. With the sign,
$\tau_k(1)=(-1)^{2-1}(-2)=2=3-1>0$.

*(b) Values.* By the class computation of Example 13.3(2), $\tau_k=-\psi_k$ takes the following values. Here
$a\in\mathbb F_3^\times$, and an elliptic element has the roots $\zeta^j,\zeta^{3j}$ with $j\in\{1,2,5\}$.

| Type | Number of elements | Value of $\tau_k$ |
|---|---:|---|
| scalar $aI$ | $1+1$ | $2\theta_0(a)^k$ |
| one Jordan block, eigenvalue $a$ | $8+8$ | $-\theta_0(a)^k$ |
| $\mathrm{diag}(1,2)$ and its conjugates | $12$ | $0$ |
| elliptic, $j=1,2,5$ | $6+6+6$ | $-(\omega^{jk}+\omega^{3jk})$ |

The counts add up to $2+16+12+18=48$.

*(c) The regular exponent $k=1$.* Here $\omega+\omega^3=i\sqrt2$, $\omega^2+\omega^6=0$ and
$\omega^5+\omega^7=-i\sqrt2$. So $\tau_1$ takes the elliptic values $-i\sqrt2$, $0$ and $i\sqrt2$ for
$j=1,2,5$, and
$$\sum_{x\in G}\lvert\tau_1(x)\rvert^2=2\cdot4+16\cdot1+12\cdot0+6\,(2+0+2)=48 .$$
This agrees with the Gram count $m_{11}=\#\{i<2:3^i\equiv1\pmod 8\}=1$ of §13.4.6. The inverse of an
elliptic element of type $j=1$ has the roots $\zeta^{-1}=\zeta^7$ and $\zeta^{-3}=\zeta^5$, so it has type
$j=5$. Its value $i\sqrt2$ is the conjugate of $-i\sqrt2$, as Lemma 13.28 predicts, and Mathlib's sum
$\sum_x\tau_1(x)\tau_1(x^{-1})$ is also $48$. By Theorem 13.31, $\tau_1$ is an irreducible character of
degree $2$. The unsigned function $\psi_1=-\tau_1$ has norm one as well, but its value at $1$ is $-2$. Norm
one does not make $\psi_1$ a character. The sign $(-1)^{d-1}$, read off from the identity value, is needed.

*(d) The nonregular exponent $k=0$.* Now $\theta_0(a)^0=1$, and $\tau_0$ takes the values $2,-1,0,-2$ on the
four types. Thus
$$\sum_{x\in G}\lvert\tau_0(x)\rvert^2=2\cdot4+16\cdot1+12\cdot0+18\cdot4=96=2\cdot48,$$
in agreement with $m_{00}=2$. Let $\mathrm{St}(x)$ be the number of $x$-invariant lines minus one; its values
on the four types are $3,0,1,-1$. So $\tau_0=\mathrm{St}-1$. The function $\mathrm{St}$ is the permutation
character on the four lines minus the trivial character, with squared norm $(2\cdot9+0+12+18)/48=1$, so it
is irreducible. The coordinates of $\tau_0$ in the irreducible basis are $+1$ at $\mathrm{St}$ and $-1$ at the
trivial character. Their squares sum to $2$. So $\tau_0$ is a virtual character with positive degree $2$
that is not a character. Positivity of the degree without norm one does not suffice. The exponent $k=4$
behaves in the same way, with $\tau_4=(\mathrm{St}-1)\cdot(\mathrm{sgn}\circ\det)$ (Example 13.3(4)).

The example only fixes what the symbols mean. The general statements are proved below.

**Definition 13.6 (two character predicates, three pairings, and a zero extension).** Let $H$ be a finite
group.

1. *Coordinate characters* (`BI.IsChar`, `BI.IsIrrChar`, `BI.Virt`, `AbByPOfComm.lean:5–12`). A function
   $\chi:H\to\mathbb C$ is a *character* if $\chi(h)=\operatorname{tr}\rho(h)$ for some $n\ge0$ and some
   representation $\rho$ of $H$ on $\mathbb C^n$ (in Lean, `Representation ℂ H (Fin n → ℂ)`). It is an
   *irreducible character* if moreover $\rho$ is irreducible in Mathlib's sense
   `Representation.IsIrreducible`: the subrepresentations form a simple order, so $\mathbb C^n\ne0$ and no
   subrepresentation lies strictly between $0$ and $\mathbb C^n$ (`Mathlib/RepresentationTheory/Irreducible.lean:30–31`).
   $R(H)$ is the additive subgroup of $\mathbb C^H$ generated by the characters.
2. *Categorical irreducibility* (`GLq.IsIrr`, `LabelDatum.lean:19–20`). For $H=\mathrm{GL}_d(\mathbb F_g)$ the
   predicate `IsCusp` (`LabelDatum.lean:64–65`) asks instead for an object $V$ of `FDRep ℂ H` that is simple
   in the sense of `CategoryTheory.Simple` and has character $\chi$.
3. *Three pairings.* The Hermitian sum $\sum_h\varphi(h)\overline{\varphi'(h)}$ appears in (I8). Restricted
   to the units of $\operatorname{End}_F(F^d)$, it is the archive's `ipGL`
   (`InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:83–84`). Mathlib's criterion uses the sum
   $\sum_h\chi(h)\chi(h^{-1})$. The archive's `BI.pair` is $\lvert H\rvert^{-1}\sum_ha(h)b(h^{-1})$
   (`AbByPOfComm.lean:21–22`). For virtual characters the three agree up to the factor
   $\lvert H\rvert$ once Lemma 13.28 is known.
4. *Zero extension* (`extZero`, `InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:86–87`). For
   $\chi:\mathrm{GL}_d(F)\to\mathbb C$ and $g\in\operatorname{End}_F(F^d)$, the value $\mathrm{extZero}\,\chi\,g$
   is the sum of $\chi(x)$ over the matrices $x$ whose linear map $\iota x=\operatorname{toLin'}x$ is $g$.

**Lemma 13.26 (subspace count and a $q$-binomial identity).** [Lean, read] Let $F$ have $q$ elements, let
$\dim V=n$, and let $N_a$ be the number of $a$-dimensional subspaces of $V$. Put $\omega_q(0)=0$ and
$\omega_q(a)=\prod_{i=1}^{a-1}(1-q^i)$ for $a\ge1$.

1. For $0\le a\le n$, $N_a\prod_{i=0}^{a-1}(q^a-q^i)=\prod_{i=0}^{a-1}(q^n-q^i)$
   (`SubspaceNumber.card_subspaces_mul`, `CardSubspacesOfFinrankMulCardBases.lean:32–60`).
2. $\sum_{a=1}^{n}N_a\,\omega_q(a)=n$; equivalently $\sum_{W\le V}\omega_q(\dim W)=n$
   (`QBinomialSum.sum_gaussian_mul_prod`, `SumGaussianMulProd.lean:63–91`; `sum_oneValue_finrank`,
   `InvariantSubspaceMobiusInverseOneProdIco.lean:13–43`).

*Proof.* (1) Send a linearly independent $a$-tuple in $V$ to its span. The fibre over an $a$-dimensional $W$
is the set of linearly independent $a$-tuples in $W$, that is, of ordered bases of $W$ (`card_fibre`,
`:7–30`). Mathlib's `card_linearIndependent` (`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean:39–41`)
counts $\prod_{i<a}(q^m-q^i)$ linearly independent $a$-tuples in a space of dimension $m\ge a$: the
$(i+1)$-st vector must avoid the $q^i$ vectors spanned by the first $i$. Use $m=a$ for each fibre and $m=n$
for the total.

(2) Put $A_{n,a}=\prod_{i<a}(q^n-q^i)$ and $D_a=A_{a,a}$. The factors of $D_a$ are $q^i(q^{a-i}-1)$ with
$q\ge2$, so $D_a\ne0$ (`den_ne`, `:15–21`; the input is $q^{j+1}-1\ne0$ for every $j$, `:66–71`). Write
$[n,a]=A_{n,a}/D_a$; by (1), $N_a=[n,a]$. Splitting off the factor $i=0$ and pulling $q$ out of the other
factors gives $A_{n+1,a+1}=(q^{n+1}-1)q^aA_{n,a}$ (`prod_succ_succ`, `:7–13`), and $A_{n,a+1}=A_{n,a}(q^n-q^a)$.
Hence
$$[n+1,a+1]=[n,a]\,\frac{q^{n+1}-1}{q^{a+1}-1},\qquad
[n,a]+q^{a+1}[n,a+1]=[n,a]\Bigl(1+\frac{q^{n+1}-q^{a+1}}{q^{a+1}-1}\Bigr)=[n+1,a+1].$$
Set $P_a=\prod_{i=1}^{a}(1-q^i)$, $c_n(a)=[n,a]P_a$ and $t_n(a)=[n,a+1]P_a$. The sum in (2) is
$S(n)=\sum_{a=0}^{n-1}t_n(a)$. Because $P_{a+1}=P_a(1-q^{a+1})$, the Pascal rule above becomes
$$t_{n+1}(a)=t_n(a)+c_n(a)-c_n(a+1)$$
(`key`, `:34–52`). Sum over $0\le a\le n$. The extra term $t_n(n)$ is zero, because $A_{n,n+1}$ contains
the factor $q^n-q^n$. The differences telescope to $c_n(0)-c_n(n+1)=1-0$. So $S(n+1)=S(n)+1$ with $S(0)=0$
(`sum_eq`, `:23–61`). Finally, the sum over all subspaces groups by dimension, and the term $a=0$ vanishes
because $\omega_q(0)=0$ (`sum_oneValue_finrank`, `InvariantSubspaceMobiusInverseOneProdIco.lean:13–43`). $\square$

**Lemma 13.27 (input (I2): the value at the identity).** [Lean, read] Let $s:F[X]\to\mathbb C$ satisfy
$s((X-1)^j)=j$ for all $j\ge0$. Then $\psi_s(V,1)=\omega_q(\dim V)$ for every finite-dimensional $V$
(`psi_one_eq_oneValue`, `InvariantSubspaceMobiusInverseOneProdIco.lean:45–72`). In particular, if
$\dim V=n>0$,
$$\psi_s(V,1)=\prod_{i=1}^{n-1}(1-q^i)=(-1)^{n-1}\prod_{i=1}^{n-1}(q^i-1),\qquad
(-1)^{n-1}\psi_s(V,1)=\prod_{i=1}^{n-1}(q^i-1)\ge1$$
(`psi_one`, `:74–77`; statement wrapper `T.invariantSubspaceMobiusInverse_one_prod_Ico`,
`InvariantSubspaceMobiusInverseOneProdIcoStatement.lean:6–7`). The hypothesis holds for $s=s_k$ by
Lemma 13.4(1). Additivity of $s$ is not used.

*Proof.* Use strong induction on $n=\dim V$. The characteristic polynomial of $1_V$ is $(X-1)^n$, so the
leading term of the recursion is $n$ (`:55–57`). Every subspace $W$ is invariant under $1$, the restriction
of $1_V$ to $W$ is $1_W$, and $\dim W<n$ when $W\ne V$ (`:58–65`). By `psi_eq` and the induction hypothesis,
$$\psi_s(V,1)=n-\sum_{W<V}\omega_q(\dim W).$$
By Lemma 13.26(2) the sum over all $W\le V$ is $n$, and its term $W=V$ is $\omega_q(n)$. So the displayed sum
is $n-\omega_q(n)$, and $\psi_s(V,1)=\omega_q(n)$ (`:66–72`). For $n=0$ both sides vanish. For the sign, each
factor $1-q^i$ with $1\le i\le n-1$ is $-(q^i-1)$, and $q^i-1\ge q-1\ge1$. $\square$

**Lemma 13.28 (inverse equals conjugate).** [Lean, read] Let $H$ be a finite group and $\chi\in R(H)$. Then
$\overline{\chi(h)}=\chi(h^{-1})$ for every $h\in H$ (`CuspGL.star_virt_eq_inv`,
`StarVirtualCharacterEqApplyInv.lean:10–24`).

*Proof.* Both sides are additive in $\chi$ and change sign with $\chi$. By induction over the generators of
$R(H)$ (`AddSubgroup.closure_induction`, `:15–24`) it suffices to treat $\chi=\operatorname{tr}\rho$. Let $B$
be the matrix of $\rho(h)$ in a basis and $C$ that of $\rho(h^{-1})$, and put $N=\lvert H\rvert$. Then
$B^N=1$ and $CB=1$ (`character_inv`, `CentralIdempotentIrreducibleCharacterProps.lean:12–19`). Average the
standard Hermitian form over the powers of $B$:
$$K=\sum_{j=0}^{N-1}(B^j)^{\dagger}B^j .$$
The term $j=0$ is the identity and the other terms are positive semidefinite, so $K$ is positive definite and
invertible. Shifting the index and using $B^N=1$ gives $B^{\dagger}KB=K$. Hence $B^{-1}=K^{-1}B^{\dagger}K$,
and
$$\operatorname{tr}C=\operatorname{tr}\bigl(K^{-1}B^{\dagger}K\bigr)=\operatorname{tr}B^{\dagger}=\overline{\operatorname{tr}B}$$
(`trace_inv_of_pow_eq_one`, `src/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean:699–729`). $\square$

**Lemma 13.29 (input (I8): integral expansion and norm one).** [Lean, read] Let $H$ be a finite group and
$\varphi\in R(H)$.

1. There are integers $c_\chi$, almost all zero and indexed by the irreducible characters $\chi$ as
   functions, with $\varphi=\sum_\chi c_\chi\chi$ and
   $\sum_{h}\varphi(h)\overline{\varphi(h)}=\bigl(\sum_\chi c_\chi^2\bigr)\lvert H\rvert$
   (`BI.virt_expand`, `VirtualCharacterIrreducibleExpansionNormSq.lean:67–98`; statement wrapper
   `T.virtualCharacter_irreducible_expansion_normSq`).
2. If $\sum_h\varphi(h)\overline{\varphi(h)}=\lvert H\rvert$, then $\varphi$ or $-\varphi$ is an irreducible
   character.
3. If, in addition, $\varphi$ is a character, then $\varphi$ is irreducible and $\varphi(1)$ is a positive
   integer.

Parts (2) and (3) are `BI.irr_of_norm_one` (`IrreducibleOfVirtualCharacterNormOne.lean:57–87`; statement
wrapper `T.irreducible_of_virtualCharacter_norm_one`).

*Proof.* (1) Proposition 13.35 in [§13.4.11](#13411-why-virtual-characters-have-integral-coefficients) constructs the integer coefficient family from virtuality.
For the norm, replace
$\overline{\varphi(h)}$ by $\varphi(h^{-1})$ using Lemma 13.28 (`:82`) and expand both factors. The orthogonality
relation $\sum_h\chi(h)\chi'(h^{-1})=\lvert H\rvert$ if $\chi=\chi'$, and $0$ otherwise, for irreducible
$\chi,\chi'$ (`:49–63`), comes from Mathlib. On the diagonal, Schur's lemma gives a one-dimensional space of
intertwiners (`pair_self_of_isIrrChar_algClosed`, `FiniteGroupFunctionPairingSelfIrreducibleAlgClos.lean:6–20`).
Distinct characters come from non-isomorphic representations, which are orthogonal
(`pair_eq_zero_of_isIrrChar_ne`, `FiniteGroupFunctionPairingEqZeroOfDistinctIrredu.lean:7–26`). The double sum
collapses to $\sum_\chi c_\chi^2\,\lvert H\rvert$ (`:84–98`).

(2) Cancel $\lvert H\rvert\ne0$ in (1). Since $\mathbb Z\to\mathbb C$ is injective, $\sum_\chi c_\chi^2=1$ in
$\mathbb Z$ (`IrreducibleOfVirtualCharacterNormOne.lean:59–65`). Every nonzero $c_\chi$ has $c_\chi^2\ge1$, so at most one coefficient is nonzero. The sum is
not $0$, so exactly one is, and it is $\pm1$ (`finsupp_eq_single_of_sum_sq_eq_one`, `:10–39`). Thus
$\varphi=\pm\chi$ for an irreducible $\chi$.

(3) An irreducible $\rho$ on $\mathbb C^n$ makes $\mathbb C^n$ a simple module over the group algebra. A simple
module is nonzero, so $n>0$, and $\chi(1)=\operatorname{tr}1=n$ (`exists_pos_nat_apply_one_of_isIrrChar`,
`:41–55`). If $\varphi=\chi$ we are done. If $\varphi=-\chi$ and $\varphi$ is a character, then $\varphi(1)$ is
the dimension $m$ of its representation (`isChar_restrict_conj_one`,
`IsCharacterOverSubfieldRestrictClassFunctionOne.lean:6–22`). So $m=-n$ and $m+n=0$ in $\mathbb N$,
contradicting $n>0$ (`:79–87`). $\square$

**Lemma 13.30 (`extZero_spec`: the bookkeeping identity).** [Lean, read] Let $F$ be finite, $d\ge0$ and
$\chi:\mathrm{GL}_d(F)\to\mathbb C$. Write $\iota x=\operatorname{toLin'}x$ for the linear map of a matrix. Line
numbers refer to `GeneralLinearFunctionExtendZeroEndProperties.lean`.

1. $\mathrm{extZero}\,\chi\,(\iota x)=\chi(x)$ for $x\in\mathrm{GL}_d(F)$ (`:23–31`).
2. $\mathrm{extZero}\,\chi\,g=0$ if $g$ is not a unit of $\operatorname{End}_F(F^d)$ (`:33–41`).
3. $\mathrm{ipGL}(\varphi,\varphi')=\sum_{x\in\mathrm{GL}_d(F)}\varphi(\iota x)\overline{\varphi'(\iota x)}$ for all
   $\varphi,\varphi':\operatorname{End}_F(F^d)\to\mathbb C$ (`:43–51`).
4. If $\chi$ is a class function, then $\mathrm{extZero}\,\chi$ is invariant under conjugation by every linear
   automorphism of $F^d$ (`:53–85`).

The four parts are bundled as `extZero_spec` (`GeneralLinearFunctionExtendZeroEndProperties.lean:87–90`).

*Proof.* The map $\iota$ is injective (`:11–12`), and its image is exactly the set of units of
$\operatorname{End}_F(F^d)$ (`:14–21`). So the fibre of $\iota$ over $\iota x$ is $\{x\}$, which gives (1), and
the fibre over a non-unit is empty, which gives (2). For (3), `ipGL` sums over the units, which form the range
of the injective map $\iota$, and the sum can be reindexed along $\iota$. For (4), a unit $g=\iota y$
conjugated by $e$ is $\iota(EyE^{-1})$ for the matrix $E$ of $e$, and a non-unit stays a non-unit. $\square$

Only part (3) is used in this section. It is used twice, at `IsCharacterCuspidalRootSumRegular.lean:140` and
at `GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:33`, and at both places the function $\chi$ is a
placeholder ($\psi$ itself, respectively the zero function), since part (3) does not involve $\chi$. Part (3)
turns the Gram norm of Step 2, a sum over the invertible endomorphisms of $F^d$, into a sum over the finite
group $\mathrm{GL}_d(F)$, where `Virt`, `IsChar` and `FDRep` live. Parts (1), (2) and (4), the zero extension
proper, are not used on this path (Remark 13.4.10(4)).

**Theorem 13.31 (from a norm-one virtual character to a positive irreducible character).** [Lean, read],
part (B) conditional on (I3)–(I7) at their recorded reading levels.

*(A) General form.* Let $H$ be a finite group and $\varphi\in R(H)$ with
$\sum_{h\in H}\lvert\varphi(h)\rvert^2=\lvert H\rvert$. Exactly one of $\varphi$ and $-\varphi$ is a character,
namely the one with positive value at $1$, and it is irreducible. If $\varphi(1)$ is a natural number, then
$\varphi$ is the character of an irreducible representation $\rho$ of $H$ on $\mathbb C^n$ with
$n=\varphi(1)>0$, and $\mathrm{FDRep.of}\,\rho$ is a simple object of `FDRep ℂ H` with character $\varphi$.

*(B) The instance in Proposition 13.6.* Let $F$ be a finite field with $q$ elements, $\theta_0$ multiplicative
and injective on nonzero elements as in (I1), $d>0$, and $k$ regular in the sense of Lemma 13.5(iv). Put
$\psi(x)=\psi_{s_k}(F^d,\iota x)$ on $G=\mathrm{GL}_d(F)$ and $\tau=(-1)^{d-1}\psi$. Then:

1. $\tau\in R(G)$ and $\sum_{x\in G}\tau(x)\overline{\tau(x)}=\lvert G\rvert$;
2. $\tau(1)=\prod_{i=1}^{d-1}(q^i-1)\ge1$;
3. $\tau$ is an irreducible character, and $\psi$ is a character exactly when $d$ is odd;
4. for $F=\mathbb Z/g\mathbb Z$, the representation $\rho$ with character $\tau$ gives a simple object
   $\mathrm{FDRep.of}\,\rho$ with character $\tau$. This is the `IsIrr` clause of `IsCusp τ`.

*Proof.* (A) By Lemma 13.29(2) there is an irreducible character $\chi$ with $\varphi=\pm\chi$, and
$\chi(1)=n>0$ by Lemma 13.29(3). The value of a character at $1$ is a natural number, its dimension. So $-\chi$,
whose value at $1$ is $-n$, is not a character. This proves the first claim. If $\varphi(1)=m\in\mathbb N$ and
$\varphi=-\chi$, then $m+n=0$, which is impossible. So $\varphi=\chi$ and $m=n>0$. Write
$\chi=\operatorname{tr}\rho$ with $\rho$ on $\mathbb C^n$. Mathlib's `FDRep.simple_iff_char_is_norm_one`
(`Mathlib/RepresentationTheory/FinGroupCharZero.lean:121–128`) says that, over an algebraically closed field of
characteristic zero and for a finite group, $\mathrm{FDRep.of}\,\rho$ is simple if and only if
$\sum_h\chi(h)\chi(h^{-1})=\lvert H\rvert$. Lemma 13.28 gives $\chi(h^{-1})=\overline{\chi(h)}$, so this is the
hypothesis.

(B) We follow `IsCharacterCuspidalRootSumRegular.lean:92–184`.

*Norm* (`:98–118`, Step 2 of Proposition 13.6). By (I3), (I5) and (I4),
$\mathrm{ipGL}(\psi_{s_k},\psi_{s_k})=\lvert G\rvert\cdot\#\{0\le i<d:kq^i\equiv k\pmod{q^d-1}\}$, and regularity
reduces the set to $\{0\}$.

*Virtuality* (`:124–131`). $\psi\in R(G)$ by Step 1 of Proposition 13.6, and $\tau=(-1)^{d-1}\cdot\psi$ is an
integer multiple of it.

*Norm on the group* (`:132–143`). Since $(-1)^{d-1}\,\overline{(-1)^{d-1}}=1$, the products
$\tau\overline\tau$ and $\psi\overline\psi$ agree pointwise. Lemma 13.30(3) turns
$\mathrm{ipGL}(\psi_{s_k},\psi_{s_k})=\lvert G\rvert$ into $\sum_{x\in G}\tau(x)\overline{\tau(x)}=\lvert G\rvert$. The
same identity holds for $-\tau$. This proves (1).

*Degree* (`:144–165`). Lemma 13.27 with $s=s_k$ and $\dim F^d=d>0$ (`:146–148`) gives
$\psi(1)=\prod_{1\le i<d}(1-q^i)$. Write $(-1)^{d-1}=\prod_{1\le i<d}(-1)$ and multiply factor by factor. This gives
$\tau(1)=\prod_{1\le i<d}(q^i-1)$ as the image of a natural number; the subtraction is exact in $\mathbb N$ because
$q^i\ge1$ (`:149–158`). The product is positive because $q\ge2$ (`:159–165`). This proves (2).

*Case split* (`:166–184`). By Lemma 13.29(2), $\tau$ or $-\tau$ is an irreducible character. In the second
case $-\tau$ is a character, and Lemma 13.29(3) applied to $-\tau$ gives $n>0$ with $-\tau(1)=n$. Then
$n+\prod_{1\le i<d}(q^i-1)=0$ in $\mathbb N$, a contradiction. Hence $\tau$ is an irreducible character, and in
particular `IsChar τ` holds. When $d$ is even, $\psi(1)=-\tau(1)<0$ excludes a character. For odd $d$, $\psi=\tau$. This proves (3). For example, at $q=2$, $d=3$, $k=1$, the residues $1,2,4$ modulo $7$ are distinct and $\psi(1)=(1-2)(1-4)=3$. It is part (A) with $\varphi=\tau$.

*The `FDRep` interface* (`GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:22–38`). `isCusp_psi` calls the
theorem through its statement wrapper (`:23`) and keeps only `IsChar τ` and the Gram norm. It extracts
$\rho$ on $\mathbb C^n$ (`:27`), forms $\mathrm{FDRep.of}\,\rho$ with character $\tau$ (`:28–31`), and applies
Mathlib's criterion (`:32`). It then rewrites the Gram norm as a finite sum over
$\mathrm{GL}_d(\mathbb Z/g\mathbb Z)$ by Lemma 13.30(3) (`:33`). The summands match because
$\tau(x^{-1})=\overline{\tau(x)}$, by Lemma 13.28 applied to $\tau\in R(G)$ (`:26`), and because
$((-1)^{d-1})^2=1$ (`:34–38`). This proves (4). The irreducibility returned by (I8) is not used here; the
simplicity of $\mathrm{FDRep.of}\,\rho$ is derived again from the norm. $\square$

The degree clause of Proposition 13.6(2) is the same computation in a separate proof term
(`ExistsCuspidalCharacterOfRegularCharacterGLn.lean:137–142`). It applies Lemma 13.27 through its statement
wrapper (`:138`) and multiplies by $(-1)^{d-1}=\prod_{1\le i<d}(-1)$ factor by factor (`:139–142`).

**Remarks 13.4.10.**

1. *Integrality is essential.* Over $\mathbb Q$ the lattice fact fails. In $\mathrm{GL}_2(\mathbb F_3)$ take
   $\varphi=\tfrac35\,\mathrm{St}+\tfrac45\,\mathrm{Ind}_B^G(1\otimes\mathrm{sgn})$, a combination of two of the
   orthonormal irreducible characters listed in Example 13.3(5). It has norm $\tfrac9{25}+\tfrac{16}{25}=1$ and
   degree $\tfrac35\cdot3+\tfrac45\cdot4=5$, a positive integer, but it is not $\pm$ an irreducible character. In
   the archive the integrality of $\psi_k$ comes from (I6) and (I7).
2. *The boundary between $\mathrm{GL}$ and $\operatorname{End}$.* The function $\psi_{s_k}(F^d,\cdot)$ is defined on
   all of $\operatorname{End}_F(F^d)$. This section evaluates it only at units: the Gram norm sums over units
   (`ipGL`), the identity is a unit, and Lemma 13.30(3) moves the sum to the matrix group. The character
   statements are statements about $\mathrm{GL}_d(F)$. On singular endomorphisms the recursion depends on Lean's
   conventions $\theta_0(0)=0$ and $0^0=1$ (Example 13.24 and Remark 13.4.9(3)). Nothing here asserts
   character-like behaviour there. This is the boundary adopted in §13.4.9.
3. *Green's argument.* Green defines the degree of a character $\chi$ as $\chi(1)$, "even if $\chi$ is not a
   proper character", and records $J_d(k)(1)=\varphi_{d-1}(q)=(1-q)(1-q^2)\cdots(1-q^{d-1})$
   [Green1955, p. 437], the value of Lemma 13.27. His Lemma 7.5 states that the degree of $I_s^k[\lambda]$ has
   the sign of $(-1)^{(s-1)v}=(-1)^{n-v}$, and his Lemma 7.6 that $\lVert I_s^k[\lambda]\rVert=1$ if
   $k,kq,\dots,kq^{s-1}$ are $s$ distinct residues modulo $q^s-1$ (p. 438). He then writes
   $(g^\lambda)=(-1)^{(s-1)v}I_s^k[\lambda]$ and, after "The lemmas in this section allow us to deduce",
   states in Theorem 12 that $(g^\lambda)$ is an irreducible character of degree
   $(-1)^{(s-1)v}\varphi_{sv}(q)\{\lambda:q^s\}$ (p. 439). For $v=1$ and $\lambda=\{1\}$ this is
   $(-1)^{s-1}J_s(k)$, of degree $\prod_{i=1}^{s-1}(q^i-1)$: the archive's $\tau$. Green states the generalized-character criterion in his introduction (p. 402) and uses it at Theorem 12. Lemma 13.29 and Theorem 13.31(A) give the archive's argument. Green
   obtains integrality from his Theorem 1 and Brauer's characterization (Remarks 13.4.4(1)); the archive
   obtains it from (I6) and (I7).
4. *Where the zero extension and the inverse-conjugate identity are used.* On the path of
   Proposition 13.6, `extZero_spec` enters only through part (3) of Lemma 13.30, twice. Lemma 13.28 enters inside
   (I8) (`VirtualCharacterIrreducibleExpansionNormSq.lean:82`) and in `isCusp_psi`
   (`GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:26, 38`). The zero extension proper, parts (1), (2) and
   (4), is used elsewhere in the archive. Examples are the converse statement `exists_regular`
   (`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLabel.lean:49–58`), which concerns an
   irreducible character whose zero extension is primitive and takes parts (1), (3) and (4) at `:58`, and the files
   `IsPrimitiveExtendZeroOfSumUnipotentRadical.lean:40, 84`, `ExistsIntCoeffPrimitiveGLCharacter.lean:26` and
   `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:46–47, 148` in `…/Proofs/CharacterTheory/`. This section only
   locates these calls; Section 13.4.13 reads the files in `…/Proofs/CharacterTheory/` and Section 13.4.14 reads
   `exists_regular` [Lean, read]. The zero extension of a function on $\mathrm{GL}_d(F)$ is unrelated to
   the convention $\theta_0(0)=0$ for a Teichmüller map in Lemma 13.20(3).
5. *A second proof of Lemma 13.26(2).* [Expository] Count the linear maps $F^n\to F^m$ by their kernels. A map
   with $a$-dimensional image is given by its kernel, of codimension $a$ ($[n,a]$ choices), and an injective map
   from the $a$-dimensional quotient into $F^m$ ($\prod_{i<a}(q^m-q^i)$ choices). So
   $q^{mn}=\sum_{a=0}^{n}[n,a]\prod_{i=0}^{a-1}(q^m-q^i)$ for every $m\ge0$. Both sides are polynomials in
   $x=q^m$ that agree at infinitely many points, so
   $x^n=\sum_{a=0}^{n}[n,a](x-1)(x-q)\cdots(x-q^{a-1})$. Differentiate at $x=1$. The term $a=0$ is constant, and
   the term $a\ge1$ contributes $[n,a]\prod_{i=1}^{a-1}(1-q^i)$. The result is Lemma 13.26(2). The archive's proof is
   the telescoping recurrence given above.
6. *Two irreducibility predicates.* `BI.IsIrrChar` uses `Representation.IsIrreducible`, while `IsCusp` uses
   `CategoryTheory.Simple` in `FDRep ℂ G`. The archive does not prove the two equivalent on this path.
   Lemma 13.29 uses the first only to know that the degree is positive. `isCusp_psi` then obtains the second
   directly from the norm, through Mathlib. The norm identity is used twice, once for each predicate.

**Table 13.4.10 (source-to-text map).** Paths in the third column are relative to `lean/` in the pinned
archive (SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`), unless they start with
`Mathlib/` (commit `0df444a360eaa60ab8c11dca51a86af692955474`). The prefix `CT/` stands for
`src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/`.

| Reading | Role in §13.4.10 | Path and lines |
|---|---|---|
| R3 / [Lean, read] | Norm, virtuality, sign, degree and case split in `isChar_psi_rootSum_of_regular` | `CT/IsCharacterCuspidalRootSumRegular.lean:92–184` |
| R3 / [Lean, read] | `isCusp_psi`: `FDRep.of ρ`, Mathlib criterion, Gram rewrite, inverse-conjugate matching | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18–38` |
| R3 / [Lean, read] | Degree clause of Proposition 13.6 | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:137–142` |
| R3 / [Lean, read] | (I2): `oneValue`, `sum_oneValue_finrank`, `psi_one_eq_oneValue`, `psi_one`; wrapper | `CT/InvariantSubspaceMobiusInverseOneProdIco.lean:10–77`; `CT/InvariantSubspaceMobiusInverseOneProdIcoStatement.lean:6–7` |
| R3 / [Lean, read] | $q$-binomial identity: `prod_succ_succ`, `den_ne`, `sum_eq`, `sum_gaussian_mul_prod` | `CT/SumGaussianMulProd.lean:7–91` |
| R3 / [Lean, read] | Subspace count: `card_fibre`, `card_subspaces_mul`; wrapper | `CT/CardSubspacesOfFinrankMulCardBases.lean:7–60`; `CT/CardSubspacesOfFinrankMulCardBasesStatement.lean:6–7` |
| R3 / [Lean, read] | (I8): `finsupp_eq_single_of_sum_sq_eq_one`, `exists_pos_nat_apply_one_of_isIrrChar`, `irr_of_norm_one`; wrapper | `CT/IrreducibleOfVirtualCharacterNormOne.lean:10–87`; `CT/IrreducibleOfVirtualCharacterNormOneStatement.lean:7–8` |
| R3 / [Lean, read] | Integer expansion and norm formula `virt_expand`; wrapper | `CT/VirtualCharacterIrreducibleExpansionNormSq.lean:14–98`; `CT/VirtualCharacterIrreducibleExpansionNormSqStatement.lean:7–8` |
| R3 / [Lean, read] | Characters as sums of irreducibles, differences, orthogonality, degree of a character | `CT/IsCharacterOverSubfieldInductionIrreducible.lean:7–50`; `CT/MemVirtualCharactersIffSubCharacters.lean:7–24`; `CT/FiniteGroupFunctionPairingSelfIrreducibleAlgClos.lean:6–20`; `CT/FiniteGroupFunctionPairingEqZeroOfDistinctIrredu.lean:7–26`; `CT/IsCharacterOverSubfieldRestrictClassFunctionOne.lean:6–22` |
| R3 / [Lean, read] | Inverse equals conjugate: `star_virt_eq_inv`, `character_inv`, `trace_inv_of_pow_eq_one`; wrapper | `CT/StarVirtualCharacterEqApplyInv.lean:10–24`; `src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CentralIdempotentIrreducibleCharacterProps.lean:12–19`; `src/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean:699–729`; `CT/StarVirtualCharacterEqApplyInvStatement.lean:7–8` |
| R3 / [Lean, read] | `extZero_spec` and its four parts; wrapper | `CT/GeneralLinearFunctionExtendZeroEndProperties.lean:11–90`; `CT/GeneralLinearFunctionExtendZeroEndPropertiesStatement.lean:7–8` |
| Definitions | `IsChar`, `IsIrrChar`, `Virt`, `pair`; `IsClassFn`, `psi`, `psi_eq`, `rootSum`, `glCard`, `ipGL`, `extZero`; `GLq.IsIrr`, `IsCusp` | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/AbByPOfComm.lean:5–22`; `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:14–15, 24–66, 72, 83–87`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:17–20, 64–65` |
| [Lean] (Mathlib; statement and proof read) | `FDRep.simple_iff_char_is_norm_one`, with `simple_iff_end_is_rank_one` | `Mathlib/RepresentationTheory/FinGroupCharZero.lean:90–128` |
| [Lean] (Mathlib; statements read) | `Representation.char_one`, `card_inv_mul_sum_char_mul_char_eq_finrank`, `char_orthonormal`, `FDRep.scalar_product_char_eq_finrank_equivariant`; `IsIrreducible`, `irreducible_iff_isSimpleModule_asModule`, `finrank_intertwiningMap_self`; `card_linearIndependent` | `Mathlib/RepresentationTheory/Character.lean:64, 115, 134, 211`; `Mathlib/RepresentationTheory/Irreducible.lean:30–35, 81`; `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean:39–41` |
| R3 / [Lean, read] | Constituent extraction and zero/sum supply | [§13.4.11](#13411-why-virtual-characters-have-integral-coefficients) for the proof bodies and named trace and Schur inputs. |
| R3 in [§13.4.13](#13413-elliptic-character-formulas-and-determination-of-cuspidal-characters-on-regular-elliptic-elements) and [§13.4.14](#13414-converse-regular-label-existence-exists_regular) | Other consumers of the zero extension and of Lemmas 13.28–13.29 | `CT/IsPrimitiveExtendZeroOfSumUnipotentRadical.lean:40, 84`; `CT/ExistsIntCoeffPrimitiveGLCharacter.lean:26`; `CT/EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:46–47, 148` (`R3` in §13.4.13); `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLabel.lean:49–128` (`R3` in §13.4.14) |
| Our check | `check_positive_sign.py`: Examples 13.24–13.25, Lemma 13.26 and the identity in Remark 13.4.10(5) in exact arithmetic | not in the repository; see `sources/SOURCES.md`, Part I §7 |

### 13.4.11 Why virtual characters have integral coefficients

Lemma 13.29 uses the norm on a lattice. Its integral coordinates originate in representation theory: direct sums add traces, and removing an invariant subspace leaves a quotient whose trace accounts for the remainder. We first compute two lattices explicitly.

**Example 13.32 ($C_3$).** [Expository] Write $C_3=\langle t\rangle$ and $\omega=e^{2\pi i/3}$. All classes have size one. The matrix of $t$ satisfies $X^3-1=0$, which has simple roots $1,\omega,\omega^2$. Every eigenline is invariant, so an irreducible must be one-dimensional. Each root gives one such representation:

| Character | $1$ | $t$ | $t^2$ |
|---|---:|---:|---:|
| $\chi_0$ | $1$ | $1$ | $1$ |
| $\chi_1$ | $1$ | $\omega$ | $\omega^2$ |
| $\chi_2$ | $1$ | $\omega^2$ | $\omega$ |

The pairing of rows $j,k$ is $\frac13(1+\omega^{j-k}+\omega^{2(j-k)})$. It is one on the diagonal and zero elsewhere since $1+\omega+\omega^2=0$. The regular action permutes its three basis vectors with no fixed vector of the basis for $t$ or $t^2$. Its character $(3,0,0)$ is the sum of the three rows. Subtracting $2\chi_0$ gives $(1,-2,-2)$ with coefficients $(-1,1,1)$ and normalized squared norm $(1+4+4)/3=3$.

The function $f=(3\chi_0+4\chi_1)/5$ has values $7/5$, $(3+4\omega)/5$ and $(3+4\omega^2)/5$. The last two squared moduli are both $(9+16+12(\omega+\omega^2))/25=13/25$. Thus the squared norm is $(49+13+13)/75=1$. Its row pairings are $(3/5,4/5,0)$. A genuine character has integer eigenvalue multiplicities and a virtual character has differences of those multiplicities, so $f$ lies outside the lattice.

**Example 13.33 ($S_3$).** [Expository] The identity, transpositions and three-cycles have class sizes $1,3,2$. In the permutation action on $\mathbb C^3$ the traces count fixed coordinates, giving $(3,1,0)$. The constant line affords the trivial character, and its invariant complement $W=\{(x_1,x_2,x_3):x_1+x_2+x_3=0\}$ has trace row $\sigma=(2,0,-1)$. A three-cycle has eigenvalues $1,\omega,\omega^2$ on $\mathbb C^3$, so $W$ has the last two eigenlines. A transposition conjugates the cycle to its inverse and exchanges those lines. Thus $W$ is irreducible.

| Character | $1$ | $(12)$ | $(123)$ |
|---|---:|---:|---:|
| $\mathbf 1$ | $1$ | $1$ | $1$ |
| $\epsilon$ (sign) | $1$ | $-1$ | $1$ |
| $\sigma$ | $2$ | $0$ | $-1$ |

The three squared norms are $(1+3+2)/6$, $(1+3+2)/6$ and $(4+0+2)/6$. The cross pairings are $(1-3+2)/6$, $(2+0-2)/6$ and $(2+0-2)/6$. These orthonormal rows span the three-dimensional space of class functions. Schur orthogonality would put any additional irreducible character perpendicular to all three rows, so the table is complete.

Pairing the regular character $(6,0,0)$ with the rows gives coefficients $(1,1,2)$. Subtracting twice the permutation character gives $(0,-2,0)=\epsilon-\mathbf 1$, with squared norm $3\cdot4/6=2$. Subtracting the permutation character and the sign character from the regular character gives $\sigma$, of degree two and norm one. Finally $h=(2\mathbf 1+2\epsilon+\sigma)/3=(2,0,1)$ has squared norm $(4+0+2)/6=1$ and positive integer degree two. Its three coefficients $(2/3,2/3,1/3)$ exhibit the failure of the norm and degree test without virtuality.

**Definition 13.7 (fields of representation and of values).** [Lean, read] Let $\iota:K\hookrightarrow L$ be a field embedding. The predicate `IsChar K L a` has a witness $\rho$ on $K^n$, with $a(g)=\iota(\operatorname{tr}_K\rho(g))$ for all $g$. The predicate `IsIrrChar K L a` requires an irreducible witness over $K$. The predicate $f\in\mathrm{Virt}(K,L,H)$ is membership in the additive subgroup of $L^H$ generated by genuine characters. Over $K=L=\mathbb C$ this is $R(H)$ from Definition 13.6. [Source map](#source-map-for-the-integral-expansion).

In an extended basis of $L\otimes_K V$, the matrix entries of the action are the images under $\iota$ of their original entries, so its trace is the image of the original trace. The archive first transports coordinates over $K$ and then maps trace values into $L$. Irreducibility can be lost under extension of scalars: multiplication by $X$ on $\mathbb Q[X]/(X^2+X+1)$ affords an irreducible rational representation of $C_3$, since the polynomial has no rational root. Over $\mathbb C$ it splits into the $\chi_1$ and $\chi_2$ eigenlines.

**Lemma 13.34 (direct sum and constituent extraction).** [Lean, read] For fields $K\hookrightarrow L$ and a group $H$, zero and sums of genuine characters are genuine. Every nonzero genuine character $a$ has the form $\eta+b$, where $\eta$ has an irreducible witness over $K$ and $b$ is genuine over $K$.

*Proof.* The wrapper `T.isCharacterOverSubfield_zero_and_add` forwards to `BI.isChar_zero_and_add`. The unique action on $K^0$ has zero trace. For witnesses $\rho,\sigma$ on $K^n,K^m$, concatenate tuples by the coordinate isomorphism $e:K^n\times K^m\to K^{n+m}$. The product operators $D_g=\rho(g)\oplus\sigma(g)$ satisfy $D_1=1$ and $D_gD_h=D_{gh}$ block by block. Conjugating by $e$ preserves these identities and preserves trace. The two diagonal blocks contribute $\operatorname{tr}\rho(g)+\operatorname{tr}\sigma(g)$, and $\iota$ preserves their sum. The resulting action is a witness of dimension $n+m$, including when either summand has dimension zero.

For the decomposition, a nonzero trace function requires a nonzero witness space $V$. Choose a nonzero invariant subspace $S$ of least dimension, using $V$ itself as a candidate. If $T$ is a nonzero invariant subspace of $S$, its image under inclusion is invariant in $V$ and has dimension $\dim T$. Minimality gives $\dim S\le\dim T$. Since $T\subseteq S$, equality holds and $T=S$. Thus $S$ is irreducible.

For any injective intertwiner $j:U\to V$, equivariance gives $\rho(g)j(u)=j(\sigma(g)u)$. The range is invariant, so $Q=V/j(U)$ inherits a representation. Inclusion and projection give a short exact sequence with commuting actions. The archive invokes `T.linear_map_short_exact_commute` to get $\operatorname{tr}\rho(g)=\operatorname{tr}\sigma(g)+\operatorname{tr}\rho_Q(g)$. In a basis of $j(U)$ extended to one of $V$, the action has block upper triangular form, and the two diagonal blocks are the actions on $U$ and $Q$.

To certify these traces under the archive predicates, choose a basis of each space $E$, identifying it with $K^{\dim E}$ by $u$. The operators $u\rho_E(g)u^{-1}$ define an action with unchanged traces. Taking preimages along $u$ carries invariant subspaces of the transported action to invariant subspaces of $E$. Taking preimages along $u^{-1}$ is inverse. Both operations preserve inclusion, giving an order isomorphism that preserves irreducibility. This proves the two projections of `T.isCharacterOverSubfield_of_representation` after applying $\iota$. Use the quotient assertion with $j:S\hookrightarrow V$, the irreducible projection for $S$ and the genuine projection for $V/S$. The transported trace equation is exactly `BI.exists_irrChar_add`. $\square$

**Complete reducibility over $\mathbb C$.** [Expository] For a finite group, take any linear projection $p$ onto an invariant subspace $S$. The average $P=|H|^{-1}\sum_g\rho(g)p\rho(g^{-1})$ commutes with the action by reindexing. Each summand has image in $S$ and acts on $S$ as the identity. Therefore $P$ is a projection with invariant kernel, and $V=S\oplus\ker P$. Induction decomposes $V$ into irreducibles. The archive's quotient argument obtains the character decomposition through exact trace additivity, which also works for a nonsplit sequence. [Etingof et al., Theorem 3.1, pp. 33–34](https://arxiv.org/pdf/0901.0827).

**Proposition 13.35 (integral expansion from virtuality).** [Lean, read] Let $H$ be finite and $f:H\to\mathbb C$. If $f\in\mathrm{Virt}(\mathbb C,\mathbb C,H)$, there is a finitely supported integer family $(c_\chi)_\chi$, indexed by distinct irreducible character functions, with $f=\sum_\chi c_\chi\chi$. Conversely any such sum is virtual. Given the complex Schur orthogonality input of Lemma 13.29, the coefficients are unique and equal to $\frac1{|H|}\sum_g f(g)\overline{\chi(g)}$.

*Proof.* The differences $a-b$ of genuine characters contain $0$ and every genuine character $a=a-0$. By Lemma 13.34, addition takes $(a-b)+(c-d)$ to $(a+c)-(b+d)$ with both terms genuine. Negation exchanges the summands. The generated subgroup in turn contains every such difference. This is `mem_virt_iff_sub`, whose line 9 consumes both projections of `T.isCharacterOverSubfield_zero_and_add`.

For a genuine character, induct on its degree. Degree zero gives the empty sum. For a nonzero character $a$ of degree $n$, Lemma 13.34 gives $a=\eta+b$. Evaluation at the identity gives $n=\eta(1)+b(1)$ in $\mathbb N$ by injectivity of the natural-number map to $\mathbb C$. The constituent has positive degree, so $b$ has smaller degree. Add one to the coefficient of $\eta$ in the finite expansion of $b$. This is the singleton update in the archive and counts repeated occurrences of the same character function. Apply the induction to both terms in $f=a-b$ and subtract the coefficient families. The new support lies in the finite union of the old supports. The converse follows from closure under integer multiples and addition. Orthogonality isolates each coefficient by pairing with its row. $\square$

**Remarks.** The difference $[\rho]-[\sigma]$ belongs to the additive Grothendieck group of representations. Trace sends it to $\chi_\rho-\chi_\sigma$. Complete reducibility gives additive multiplicity coordinates and complex Schur orthogonality makes the trace coordinates unique. Taking the complex span permits arbitrary complex coordinates, as in the two norm-one examples. The existence of integral coefficients in Proposition 13.35 is proved before taking any pairing.

Lemma 13.29(1) uses Proposition 13.35 to obtain its coefficient family and then computes its norm. For Theorem 13.31(B), (I6) and (I7) supply virtuality for $\psi$ and hence for $\tau=(-1)^{d-1}\psi$. The archive passes the family and norm identity from `virt_expand` to `irr_of_norm_one`. The norm-one and positive-degree results of §13.4.10 then select the positive irreducible character. Green states the analogous generalized-character test in his introduction. [Green 1955, p. 402](https://doi.org/10.1090/S0002-9947-1955-0072878-2).

#### Source map for the integral expansion

Paths start at the extracted Lean project root. Joined archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. R3 covers the indicated bodies using the named interfaces.

| Reading | Declaration or handoff | Full archive path and lines |
|---|---|---|
| Definitions | `IsChar`, `IsIrrChar`, `Virt` | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/AbByPOfComm.lean:5–12` |
| R3 | Zero and sum, including the product action | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldZeroAndAdd.lean:6–40` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldZeroAndAddStatement.lean:6–7` |
| R3 | Minimal subrepresentation and constituent extraction | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIrrCharAdd.lean:8–45,47–65` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIrrCharAddStatement.lean:6–7` |
| R3 | Invariant range and quotient trace | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsCharacterQuotientOfInjectiveIntertwining.lean:8–22` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsCharacterQuotientOfInjectiveIntertwiningStatement.lean:6–7` |
| R3 | Coordinate action, trace and subspace transport | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentation.lean:10–48,51–67` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldOfRepresentationStatement.lean:6–7` |
| Already read in §13.4.10 | Difference and induction consumers, finite support and norm handoff | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MemVirtualCharactersIffSubCharacters.lean:7–24`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldInductionIrreducible.lean:32–50`, `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterIrreducibleExpansionNormSq.lean:14–46,67–76` and `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleOfVirtualCharacterNormOne.lean:57–65` |
| R2 / [Lean] | Short exact trace production `GlobalTheory.trace_eq_add_of_shortExact` through its interface | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/LinearMapShortExactCommuteStatement.lean:5–6` |
| [Lean], Mathlib interfaces | `trace_conj'`, `trace_prodMap'`, `Submodule.finrank_map_subtype_eq`, `Submodule.eq_top_of_finrank_eq`. Deeper Schur inputs `Representation.char_orthonormal`, `card_inv_mul_sum_char_mul_char_eq_finrank` and `finrank_intertwiningMap_self` | Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`. For the last three interfaces see `Mathlib/RepresentationTheory/Character.lean:115,134` and `Mathlib/RepresentationTheory/Irreducible.lean:81`. |

---

### 13.4.12 Naming laws, `PM.greenCuspidal`, and label well-definedness across consumers

**Motivation.** Section 13.4.1 showed how `green_of_regular` (`SumRangeEqRoots.lean:225`) converts `GreenRegularCharacters` into the polynomial-labeled predicate `GlobalTheory.GLq.Green` (`LabelDatum.lean:108`), and Sections 13.4.4–13.4.11 opened the Möbius-inverse, Teichmüller-lift, positive-sign, and virtual-integrality machinery behind `GreenRegularCharacters`. Yet Remark 5 of Section 13.4.4 left two load-bearing main-path junctions unopened:

1. *The coordinate-free naming laws on the local Langlands side (`UpperTheory.Zero.LLC.nameLaws`, `NameLaws.lean:78, 81`).* In Chapter 12 (`P15`), depth-zero supercuspidal representations of $\mathrm{GL}_n(E_w)$ are probed along varying unramified extensions $D/E_w$ whose residue fields $K$ are abstract degree-$n$ extensions of $\mathbb F_g$ with **no** distinguished primitive root or Teichmüller lift. How does the archive attach a Frobenius orbit of regular characters $\theta : K^\times \to \mathbb C^\times$ to a simple cuspidal module $\tau$, prove that two regular names of the same $\tau$ lie in one $\mathrm{Gal}(K/\mathbb F_g)$-orbit, extract the central character $\tau(c I_n) = \theta(c)\,\mathrm{id}$, and transport names across bare ring isomorphisms $e : K \xrightarrow{\sim} K'$?
2. *The representation-level polynomial parametrization on the automorphic side (`PositivityTheory.Stage1.PM.greenCuspidal`, `HarishChandraModules.lean:12`, `GreenCuspidal.lean:303`).* In `EveryCharacterOfLiteratureOfVWin.lean:397–402, 668, 728`, `GlobalTheory.Published.GreenCuspidal` (`GreenCuspidalIff.lean:8`) is definitionally equal to `GlobalTheory.GLq.Green`, **but it is not supplied by `green_of_regular`**. Instead, `PM.greenCuspidal` builds a representation-level `CuspParam` (`GreenAll.cuspParam_all`, `LabelMapNonempty.lean:122`) directly on `FDRep (Gn g d) ℂ` and feeds three distinct downstream consumers: squarefree generic Harish-Chandra series (`GreenSeries.green_series`, `ProdFactorsOfMonic.lean:243`), arbitrary-generator cuspidal parametrizations (`cuspParam_of_green`, `CuspParamOfGreenParametrisation.lean:106`), and central Hecke idempotent permutations (`exists_perm_deg`, `exists_perm`, and `eSer_eq`, `AdmissibleLabelWeightsOfGreenCuspidalParametrisa.lean:50, 89, 233`).

Reading both production chains alongside their actual consumers exposes a clean structural division of labor. On the local Langlands side, orbit uniqueness is proved **not** by quoting injectivity of `GreenRegularCharacters`, but by an $L^2$-Parseval support bound on $K^\times$ (`UpperTheory.Zero.LLC.pin`, `PairCheckThreeTwo.lean:177`) supplemented at the four small pairs $(g,n)\in\{(2,2),(3,2),(2,4),(2,6)\}$ by a Fourier shift-invariance test. On the automorphic side, **existence (+ degree)**, **injectivity**, and **exhaustion** of polynomial labels draw on genuinely different supplies — Newton's symmetric-polynomial identities give injectivity for *all* $q \ge 2$ without touching exhaustion or $g \ge 5$, and `green_series` explicitly discards the exhaustion clause at `ProdFactorsOfMonic.lean:251`.

#### Worked examples

**Example 13.36 ($\mathbb F_8 / \mathbb F_2$ on $\mathrm{GL}_3(\mathbb F_2)$: odd-degree positivity, minimal generic `Pin` slack, ring-model transport, and fixed `rootC` vs. generator re-choice).** [Expository; verified in exact cyclotomic arithmetic over $\mathbb Q(\zeta_{21})$ across all $168$ matrices of $\mathrm{GL}_3(\mathbb F_2)$ by `verify_green_label_laws.py`] Set $g = 2$, $d = 3$, and $N = 2^3 - 1 = 7$, so $\lvert\mathrm{GL}_3(\mathbb F_2)\rvert = (8 - 1)(8 - 2)(8 - 4) = 168$ and every cuspidal character has degree $(2 - 1)(2^2 - 1) = 3$. Because $d = 3$ is odd, Theorem 13.31(3) (§13.4.10) says that the unsigned invariant-subspace Möbius inverse $\psi_{s_k}$ is already a genuine positive character $\tau_k = (-1)^{3-1}\psi_{s_k} = +\psi_{s_k}$ when $k \not\equiv 0 \pmod 7$ (whereas at the non-regular exponent $k = 0$, $\psi_{s_0} = \mathbf 1 - \chi_{(2,1)} + \mathrm{St}$ has positive value $1 - 6 + 8 = 3$ at $I_3$ yet normalized squared norm $1^2 + (-1)^2 + 1^2 = 3$).

1. *Regular Frobenius orbits and minimal generic `Pin` slack.* Multiplication by $g = 2$ modulo $7$ partitions $(\mathbb Z/7\mathbb Z)\setminus\{0\}$ into two regular orbits of length $3$, corresponding to the two monic irreducible cubics over $\mathbb F_2$:
   $$A = \{1, 2, 4\} \longleftrightarrow P_1(X) = X^3 + X + 1, \qquad B = \{3, 6, 5\} \longleftrightarrow P_2(X) = X^3 + X^2 + 1.$$
   Fixing $\zeta_7 = e^{2\pi i/7}$, the two Gaussian periods are
   $$\eta_1 = \zeta_7 + \zeta_7^2 + \zeta_7^4 = \frac{-1 + i\sqrt{7}}{2}, \qquad \eta_2 = \zeta_7^3 + \zeta_7^6 + \zeta_7^5 = \overline{\eta_1} = \frac{-1 - i\sqrt{7}}{2},$$
   with $\eta_1 + \eta_2 = -1$, $\eta_1 \eta_2 = 2$, and $\lvert\eta_1 - \eta_2\rvert^2 = \lvert i\sqrt{7}\rvert^2 = 7$. In $\mathbb F_8^\times$, the proper-subfield locus $D = \{z \in \mathbb F_8^\times : \deg_{\mathbb F_2}(z) \neq 3\}$ is just $\mathbb F_2^\times = \{1\}$, of cardinality $\#D = \mathrm{bd}(2, 3) = 2^{3/3} - 1 = 1$. Thus $(g, n) = (2, 3)$ sits at the sharpest non-exceptional threshold of `PinNum.two_bd`:
   $$2 n \cdot \mathrm{bd}(2, 3) + 1 = 2 \cdot 3 \cdot 1 + 1 = 7 < 8 = 2^3.$$
   Indeed, for a root $u$ of $P_1$, the orbit-sum difference $\mathrm{dif}(z) = \sum_{a \in A} \theta_1(z)^a - \sum_{b \in B} \theta_1(z)^b$ (where $\theta_1(u) = \zeta_7$) vanishes at $z = 1 \in D$, equals $\eta_1 - \eta_2 = i\sqrt{7}$ on $\{u, u^2, u^4\}$, and equals $\eta_2 - \eta_1 = -i\sqrt{7}$ on $\{u^3, u^6, u^5\}$. Its $L^2$ sum is $0 + 6 \cdot 7 = 42 = 7 \cdot (3 + 3) = \lvert\mathbb F_8^\times\rvert(\#A + \#B)$, whereas if $\mathrm{dif}$ vanished outside $D = \{1\}$ the Cauchy–Schwarz bound on $D$ could reach at most $\lvert\mathrm{dif}(1)\rvert^2 \le (3 + 3)^2 = 36 < 42$. On $\mathrm{GL}_3(\mathbb F_2)$, the $48$ elliptic matrices split into $24$ of characteristic polynomial $P_1$ (where $\tau_{\{1,2,4\}} = \eta_1$ and $\tau_{\{3,6,5\}} = \eta_2$) and $24$ of characteristic polynomial $P_2$ (where the two values swap).
2. *Coordinate-free ring-model transport (`NameLaws` Clauses 4, 2, 3).* Compare the two concrete models $K = \mathbb F_2[u]/(u^3 + u + 1)$ and $K' = \mathbb F_2[w]/(w^3 + w^2 + 1)$. Since $(w^{-1})^3 + w^{-1} + 1 = w^{-3}(1 + w^2 + w^3) = 0$ and $w^{-1} = w^6 = w^2 + w$, there are three bare ring isomorphisms $e : K \xrightarrow{\sim} K'$, determined by $e(u) \in \{w^6, w^5, w^3\}$ (automatically $\mathbb F_2$-linear because $\mathbb Z/2\mathbb Z$ has a unique ring homomorphism into any ring, `RingHom.ext_zmod`). Take $e(u) = w^6 = w^2 + w$, and let $\tau$ be the simple cuspidal module with character $\tau_{\{1,2,4\}}$, named over $K$ by $\theta_1(u) = \zeta_7$. Over $K'$, Clause 1 (`hNex`) supplies a regular name $\theta' : (K')^\times \to \mathbb C^\times$ of the **same** $\tau$, for instance $\theta'_6(w) = \zeta_7^6$. Pulling back along $e$ via Clause 4 (`hNtr`) shows that $\theta'_6 \circ e$ also names $\tau$ over $K$; explicitly, $(\theta'_6 \circ e)(u) = \theta'_6(w^6) = \zeta_7^{36} = \zeta_7 = \theta_1(u)$, while choosing $\theta'_3(w) = \zeta_7^3$ or $\theta'_5(w) = \zeta_7^5$ pulls back to $\theta_1^2$ or $\theta_1^4$ in the same Frobenius orbit $\{1, 2, 4\}$ (Clause 2, `hNuniq`). Consequently Clause 3 (`hNchar`) identifies $\chi_{\tau'} = \chi_\tau$ whenever $\tau'$ is named over $K'$ by any $\theta' \in \{\theta'_3, \theta'_6, \theta'_5\}$, without fixing primitive generators of $K^\times$ or $(K')^\times$.
3. *Fixed `rootC 7` vs. explicit generator re-choice, and Newton recovery at $j = 1, 2, 3$.* Compare two conventions on $K = \mathbb F_2[u]/(u^3 + u + 1)$:
   - Under `labelChar` (§13.4.9, Proposition 13.23), where the archive's canonical complex $7$th root `rootC 7` is kept fixed and only the Teichmüller embedding is changed by $\iota' = \iota^a$ ($a \in (\mathbb Z/7\mathbb Z)^\times$), a root parameter $x$ moves to $x' = x^{a^{-2}}$. Because $(\mathbb Z/7\mathbb Z)^{\times 2} = \{1^2, 2^2, 3^2\} \bmod 7 = \{1, 4, 2\} = \langle 2 \rangle$, the exponent $a^{-2} \bmod 7$ lies in the Frobenius group $\langle 2 \rangle$ for **every** $a \in (\mathbb Z/7\mathbb Z)^\times$! Thus every change of Teichmüller lift with fixed `rootC 7` acts trivially on the polynomial labels $\{P_1, P_2\}$.
   - Under two `LabelDatum 2` structures $L = (\iota, \mathrm{gen})$ and $L' = (\iota^a, \mathrm{gen}^b)$ with independent generator choices $\mathrm{gen}(3) = u$ and $\mathrm{gen}'(3) = u^b$ ($a, b \in (\mathbb Z/7\mathbb Z)^\times$), matching the same elliptic trace $\iota'(x')^{m'} = \iota(x)^m$ on $z = u^m = (u^b)^{b^{-1}m}$ gives $(x')^{a b^{-1}} = x$, i.e. $x' = x^{a^{-1} b}$ (`GoodCharsCompare.exists_beta`, §13.4.9). Taking $a = 1, b = 3$ ($\mathrm{gen}'(3) = u^3$, root of $P_2$) sends $u \mapsto u^3$ and **swaps** $P_1 \leftrightarrow P_2$: the same $3$-dimensional cuspidal module $W$ (with trace $\eta_1$ on $P_1$-matrices) has $L$-label $P_1$ and $L'$-label $P_2$, linked by the transposition $\sigma(P_2) = P_1$ of `exists_perm_deg`.
   - Finally, `hasCuspLabel_unique` recovers $P_1$ from $W$ alone by evaluating $\chi_W$ on elliptic matrices with eigenvalues $u^j$ for $j = 1, 2, 3$ (each $j \le 3$ is regular modulo $7$ by `reg_small_lemma_4`, since $u, u^2$ have roots in $P_1$ and $u^3$ in $P_2$). For $W = W(P_1)$, the three traces give the complexified power sums $(p_1, p_2, p_3) = (\eta_1, \eta_1, \eta_2)$ of $\{\iota(u), \iota(u^2), \iota(u^4)\} = \{\zeta_7, \zeta_7^2, \zeta_7^4\}$ (since $(-1)^{3-1} = +1$), whereas $W(P_2)$ gives $(\eta_2, \eta_2, \eta_1)$. Newton's identities (`MvPolynomial.mul_esymm_eq_sum`) recover the elementary symmetric values
     $$e_1 = p_1 = \eta_1, \qquad e_2 = \frac{e_1 p_1 - p_2}{2} = \frac{\eta_1^2 - \eta_1}{2} = \eta_2, \qquad e_3 = \frac{e_2 p_1 - e_1 p_2 + p_3}{3} = \frac{2 - (\eta_2 + 2) + \eta_2}{3} = 1,$$
     pinning down the multiset $\{\zeta_7, \zeta_7^2, \zeta_7^4\}$ and, by injectivity of $\iota$, the polynomial $P_1$.

**Example 13.37 ($\mathbb F_{25} / \mathbb F_5$ on $\mathrm{GL}_2(\mathbb F_5)$ and $\mathrm{GL}_3(\mathbb F_5)$, with the $(3, 2)$ and $(2, 6)$ boundary checks for `Pin`).** [Expository; verified in exact cyclotomic arithmetic over $\mathbb Q(\zeta_{24})$ by `verify_green_label_laws.py`] Set $g = 5$ — the smallest prime meeting the $5 \le g$ threshold of `eSer_eq` — with $d = 2$ and $N = 5^2 - 1 = 24$. Realize $\mathbb F_{25} = \mathbb F_5[v]/(v^2 + 2v + 3)$ ($v^2 = 3v + 2$); then $v$ has multiplicative order $24$, its norm $v^{1+5} = v^6 = 3$ generates $\mathbb F_5^\times$, and we take norm-compatible generators $\mathrm{gen}(2) = v$, $\mathrm{gen}(1) = 3$, with $\iota(v) = \zeta_{24} = e^{2\pi i/24}$ and $\iota(3) = \zeta_{24}^6 = i$.

1. *The $10$ regular Frobenius orbits in $\mathbb F_{25}^\times$ and cuspidal characters of $\mathrm{GL}_2(\mathbb F_5)$.* Modulo $24$, multiplication by $5$ fixes the $4$ multiples of $6$, namely $\{0, 6, 12, 18\}$ corresponding to $D = \mathbb F_5^\times$ ($\#D = \mathrm{bd}(5, 2) = 4$, where $2 \cdot 2 \cdot 4 + 1 = 17 < 25 = 5^2$). The remaining $20$ residues split into $10$ regular orbits $\{t, 5t \bmod 24\}$, parametrizing the $10$ monic irreducible quadratics over $\mathbb F_5$ and the $10$ orthonormal cuspidal characters $\tau_P$ of degree $5 - 1 = 4$ on $\mathrm{GL}_2(\mathbb F_5)$ (order $480$):

   | Orbit $\{t, 5t \bmod 24\}$ | Root order in $\mathbb F_{25}^\times$ | Monic irreducible $P(X) = (X - v^t)(X - v^{5t}) \in \mathbb F_5[X]$ | Image under $x \mapsto x^7$ |
   |---|---:|---|---|
   | $\{1, 5\}$ | $24$ | $P_A(X) = X^2 + 2X + 3$ | $P_B(X) = X^2 + X + 2$ ($\{7, 11\}$) |
   | $\{7, 11\}$ | $24$ | $P_B(X) = X^2 + X + 2$ | $P_A(X) = X^2 + 2X + 3$ ($\{1, 5\}$) |
   | $\{13, 17\}$ | $24$ | $X^2 + 3X + 3$ | $X^2 + 4X + 2$ ($\{19, 23\}$) |
   | $\{19, 23\}$ | $24$ | $X^2 + 4X + 2$ | $X^2 + 3X + 3$ ($\{13, 17\}$) |
   | $\{2, 10\}$ | $12$ | $X^2 + X + 4$ | $X^2 + 2X + 4$ ($\{14, 22\}$) |
   | $\{14, 22\}$ | $12$ | $X^2 + 2X + 4$ | $X^2 + X + 4$ ($\{2, 10\}$) |
   | $\{3, 15\}$ | $8$ | $X^2 + 2$ | $X^2 + 3$ ($\{9, 21\}$) |
   | $\{9, 21\}$ | $8$ | $X^2 + 3$ | $X^2 + 2$ ($\{3, 15\}$) |
   | $\{4, 20\}$ | $6$ | $X^2 + 4X + 1$ | **fixed** ($\{4, 20\}$, since $28 \equiv 4 \pmod{24}$) |
   | $\{8, 16\}$ | $3$ | $P_C(X) = X^2 + X + 1$ | **fixed** ($\{8, 16\}$, since $56 \equiv 8 \pmod{24}$) |

   *(For instance, on $\{3, 15\}$, $v^2 = 3v + 2$ gives $v^3 = v + 1$ and $v^{15} = (v + 1)^5 = v^5 + 1$; since $v + v^5 = -2 \equiv 3 \pmod 5$ and $v^6 = 3$, we have $v^3 + v^{15} \equiv 3 + 2 \equiv 0 \pmod 5$ and $v^3 v^{15} = v^{18} = 3^3 \equiv 2 \pmod 5$, giving $X^2 + 2$, while $\{9, 21\}$ gives $X^2 + 3$.)*

2. *Contrast between `rootC 24` invariance and generator re-choice $v' = v^7$.* Because $(\mathbb Z/24\mathbb Z)^\times = \{1, 5, 7, 11, 13, 17, 19, 23\} \cong (\mathbb Z/2\mathbb Z)^3$ has exponent $2$, $a^{-2} \equiv 1 \pmod{24}$ for **every** $a \in (\mathbb Z/24\mathbb Z)^\times$: changing the Teichmüller lift while keeping `rootC 24` fixed (`labelChar`) fixes *every single one* of the $10$ quadratic labels! Now keep $\iota$ fixed ($a = 1$) and switch to the norm-compatible generator system $\mathrm{gen}'(2) = v' := v^7$, $\mathrm{gen}'(1) = (v^7)^6 = 3^3 \equiv 2 \pmod 5$ ($b_2 = 7 \in (\mathbb Z/24\mathbb Z)^\times$, $b_1 = 3 \in (\mathbb Z/4\mathbb Z)^\times$). A fixed cuspidal module $W$ with $L$-root $x \in \mathbb F_{25}^\times$ has $L'$-root $x' = x^7$ (since $7^{-1} \equiv 7 \pmod{24}$). Because $7t \equiv t \pmod{24} \iff 4 \mid t$, the non-primitive regular orbits $\{8, 16\}$ ($P_C(X) = X^2 + X + 1$, order $3$) and $\{4, 20\}$ ($X^2 + 4X + 1$, order $6$) are **fixed**, whereas the remaining $8$ quadratics swap in four $2$-cycles: $P_A(X) = X^2 + 2X + 3 \leftrightarrow P_B(X) = X^2 + X + 2$, $X^2 + 3X + 3 \leftrightarrow X^2 + 4X + 2$, $X^2 + X + 4 \leftrightarrow X^2 + 2X + 4$, and $X^2 + 2 \leftrightarrow X^2 + 3$. In degree $1$, $x_1 \mapsto x_1^3$ swaps $X + 2 = X - 3 \leftrightarrow X + 3 = X - 2$. At $j = 1, 2$ (`reg_small_lemma_4`), the elliptic traces $-( \iota(x)^j + \iota(x^5)^j )$ on matrices with eigenvalues $v, v^2$ recover $p_1 = \iota(x) + \iota(x)^5$ and $p_2 = \iota(x)^2 + \iota(x)^{10}$, from which $e_1 = p_1$ and $e_2 = \frac{1}{2}(p_1^2 - p_2) = \iota(x)^6$ uniquely separate all $10$ orbits.

3. *Comparing `green_series` and `eSer_eq` on the same character of $\mathrm{GL}_3(\mathbb F_5)$.* Consider the degree-$3$ squarefree monic polynomial
   $$f(X) = (X + 2)\,P_A(X) = (X + 2)(X^2 + 2X + 3) \in \mathrm{sqSet}(5, 3).$$
   - In `GreenSeries.green_series` (`ProdFactorsOfMonic.lean:243–351`), which unpacks **only existence + degree and injectivity** of `PM.greenCuspidal` (discarding exhaustion at `:251`), the Levi block $(1, 2)$ carries $\chi_{X+2} \boxtimes \tau_{P_A}$ of degree $1 \cdot 4 = 4$. Since $[\mathrm{GL}_3(\mathbb F_5) : P_{1,2}] = \frac{(125 - 1)(125 - 5)(125 - 25)}{4 \cdot (24 \cdot 20) \cdot 25} = 31$, parabolic induction produces a generic character $\tau_L(f) = \mathrm{hc}_{1,2}(\chi_{X+2} \boxtimes \tau_{P_A})$ of degree $31 \cdot 4 = 124$, satisfying `degHcL`:
     $$\tau_L(f)(1) \cdot \mathrm{torusCard}(5, f) = 124 \cdot (5^1 - 1)(5^2 - 1) = 124 \cdot 96 = 11{,}904 = (5 - 1)(5^2 - 1)(5^3 - 1).$$
   - In `eSer_eq` (`AdmissibleLabelWeightsOfGreenCuspidalParametrisa.lean:233–250`), which consumes **all three clauses** (existence, injectivity, and exhaustion) together with $5 \le g$, compare $L = (\iota, \mathrm{gen})$ against $O := \mathrm{greenLab}(L')$ for $L' = (\iota, \mathrm{gen}')$. Under $O$, the **exact same** $124$-dimensional induced character and the **exact same** central Harish-Chandra series idempotent in $\mathbb C[\mathrm{GL}_3(\mathbb F_5)]$ are indexed not by $f$, but by $f'(X) = (X + 3)\,P_B(X) = (X + 3)(X^2 + X + 2)$. Because $\sigma_1(X + 3) = X + 2$ and $\sigma_2(P_B) = P_A$, the multiplicative extension $\operatorname{ext}\sigma$ (`AdmissibleLabelWeights…:116`) sends $f' \mapsto (X + 2)P_A = f$, and `eSer_eq` certifies $\mathrm{eSerO}(O, 3, f') = \mathrm{eSerC}(L, 3, \operatorname{ext}\sigma(f')) = \mathrm{eSerC}(L, 3, f)$.

4. *Why `Pin` needs a shift test at $(3, 2)$ and $(2, 6)$.* At $(g, n) = (3, 2)$, $N = 3^2 - 1 = 8$ and $\#D = \lvert\mathbb F_3^\times\rvert = 2$, so $2 n \cdot \#D = 2 \cdot 2 \cdot 2 = 8 = g^n - 1$: the pure Parseval bound $g^n - 1 \le \#D(\#A + \#B)$ is an **equality** and cannot by itself rule out two disjoint regular orbits $A, B$ whose difference vanishes outside $D$! `PairCheckThreeTwo.exc` breaks the tie with the shift $e = 2$ (divisible by $3^{2/2} - 1 = 2$): any character of $\mathbb F_9^\times$ raised to the $8$th power is $1$, and for the generator $\eta_0$ of $\widehat{\mathbb F_9^\times}$, $\eta_0^2\rvert_D \equiv 1$ because $z^2 = 1$ on $\mathbb F_3^\times$. By `PinChar.mul_mem`, if $\mathrm{dif}(A, B) = 0$ outside $D$, then $\mathrm{dif}(A, B) \cdot \eta_0^2 = \mathrm{dif}(A, B)$ everywhere on $\mathbb F_9^\times$, forcing both $A$ and $B$ to be closed under $+2 \bmod 8$ (`Cl 3 2 8 2 t`). Yet the three regular orbits modulo $8$ are $\{1, 3\}$, $\{5, 7\}$, and $\{2, 6\}$, and shifting by $+2 \bmod 8$ sends $3 \mapsto 5 \notin \{1, 3\}$, $7 \mapsto 1 \notin \{5, 7\}$, and $6 \mapsto 0 \notin \{2, 6\}$: **zero** regular orbits survive! Even more instructively, at $(g, n) = (2, 6)$ ($N = 63$, $\mathrm{bd}(2, 6) = (2^3 - 1) + (2^2 - 1) = 10$, $e = 21$), shifting modulo $63$ by $+21$ eliminates $8$ of the $9$ regular orbits of size $6$ and leaves the **single** surviving orbit $\{7, 14, 28, 56, 49, 35\}$ (the six primitive $9$th roots of unity in $\mathbb F_{64}^\times$, which form the union of the two cosets $7 + 21\mathbb Z$ and $14 + 21\mathbb Z$ modulo $63$); hence any two surviving regular orbits coincide, again contradicting $A \cap B = \emptyset$ (`Pair 2 6 63 21`).

---

#### Definitions

**Definition 13.8 (Coordinate-free naming predicates, representation-level cuspidal parametrizations, and `GreenSeriesSt`).** [Lean, read] Let $g$ be a prime (`Fact g.Prime`) and $n, d \ge 1$.

1. *Coordinate-free naming on the local Langlands side (`src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/RecTTransport.lean:23–25, 99–124`).* Fix a finite field extension $K$ of $\mathbb F_g = \mathrm{ZMod}\,g$ of degree $\dim_{\mathbb F_g} K = n$, a multiplicative character $\theta : K^\times \to \mathbb C^\times$, and a finite-dimensional complex representation $\tau : \mathrm{FDRep}(\mathrm{GL}_n(\mathbb F_g), \mathbb C)$:
   - `Names g n θ τ` (`:23–25`) holds if for every matrix $y \in \mathrm{GL}_n(\mathbb F_g)$ whose characteristic polynomial is irreducible over $\mathbb F_g$ and every root $z \in K^\times$ of $\operatorname{charpoly}(y)$,
     $$\chi_\tau(y) = (-1)^{n-1} \sum_{j=0}^{n-1} \theta\!\left(z^{g^j}\right).$$
   - `Pin` (`:99–106`) asserts, for every prime $g$, $n > 0$, degree-$n$ extension $K/\mathbb F_g$, and regular $\theta : K^\times \to \mathbb C^\times$ (`IsRegularChar g n θ`, §13.3.1): **(i)** there exists $z \in K^\times$ with $\deg\operatorname{minpoly}_{\mathbb F_g}(z) = n$ and $\sum_{j < n} \theta(z^{g^j}) \neq 0$; and **(ii)** if $\theta' : K^\times \to \mathbb C^\times$ is also regular and $\sum_{j < n}\theta(z^{g^j}) = \sum_{j < n}\theta'(z^{g^j})$ for every $z \in K^\times$ of minimal-polynomial degree $n$, then $\theta' = \theta^{g^j}$ for some $j < n$.
   - `NameLaws` (`:108–117`) asserts four clauses for all such $(g, n, K)$: **(1) existence (`hNex`):** every cuspidal $\tau$ (`IsCusp τ.character`) admits a regular $\theta$ with `Names g n θ τ`; **(2) orbit uniqueness (`hNuniq`):** if regular $\theta, \theta'$ both name $\tau$, then $\theta' = \theta^{g^j}$ for some $j < n$; **(3) character determination (`hNchar`):** if cuspidal $\tau, \tau'$ are named by regular $\theta$ and by $\theta^{g^j}$ ($j \in \mathbb N$), then $\chi_{\tau'} = \chi_\tau$; and **(4) ring-isomorphism transport (`hNtr`):** for any ring isomorphism $e : K \simeq^{+*} K'$ into another $\mathbb F_g$-extension $K'$ and any $\theta' : (K')^\times \to \mathbb C^\times$, `Names g n θ' τ` implies `Names g n (θ'.comp (Units.map e)) τ`, and regularity of $\theta'$ implies regularity of $\theta' \circ e$.
   - `NameCentral` (`:119–124`) asserts that if $\tau$ is simple (`CategoryTheory.Simple τ`) and `Names g n θ τ` holds for a regular $\theta$, then every scalar matrix $c I_n$ ($c \in \mathbb F_g^\times$) acts on $\tau$ by $\theta(\iota_{K}(c))\,\mathrm{id}_\tau$.

2. *Representation-level cuspidal labels and `GreenCuspidal` (`src/Formalism/PadicSubsetSums/CentralIdempotents/IsConstituent.lean:135–214` and `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenCuspidalIff.lean:8`).*
   - A **label convention** `C : LabelConv F` (`IsConstituent.lean:135–146`) over a finite field $F$ of cardinality $q$ packages an algebraically closed extension $\bar F$, an injective multiplicative lift $\iota : \bar F^\times \hookrightarrow \mathbb C^\times$, and norm-compatible cyclic generators $\mathrm{gen}(d) \in \bar F^\times$ of order $q^d - 1$ ($\mathrm{gen}(1) = \mathrm{gen}(d)^{(q^d-1)/(q-1)}$ for $d \ge 1$). Every `L : LabelDatum g` induces `conv L : LabelConv (ZMod g)` (`GreenCuspidal.lean:60–114`).
   - For $W : \mathrm{FDRep}(\mathrm{GL}_d(F), \mathbb C)$ and $P \in F[X]$, `HasCuspLabel C d W P` (`IsConstituent.lean:148–160`) requires $d > 0$, `Simple W`, module-level cuspidality `IsCuspidal W` (vanishing of Jacquet fixed subspaces on all proper parabolic unipotent radicals), `IsPrimeLab P` ($P$ monic irreducible of degree $d$ with $P(0) \neq 0$), and the elliptic trace formula $\chi_W(x) = (-1)^{d-1}\sum_{a < d} \iota(r^{q^a})^k$ whenever $\operatorname{charpoly}(x)$ is irreducible of degree $d$ with root $\mathrm{gen}(d)^k$ and $r \in \bar F^\times$ is a root of $P$.
   - `CuspParam C d Wmap` (`:183–192`) means: **(i)** `HasCuspLabel C d (Wmap P) P` for every $P$ with `IsPrimeLab P` and $\deg P = d$; and **(ii)** every simple cuspidal $W$ is isomorphic (`Nonempty (W ≅ Wmap P)`) to `Wmap P` for a **unique** prime label $P$ of degree $d$. Choosing such `Wmap` for all $d \ge 1$ defines a `LabelMap F C` (`:194–207`) and abstract central Harish-Chandra series idempotents `eSerO O n f` (`:209–214`).
   - `GlobalTheory.Published.GreenCuspidal : Prop` (`GreenCuspidalIff.lean:8`) is defined literally as `GlobalTheory.GLq.Green` (`LabelDatum.lean:108`, Definition 13.1).
   - `GlobalTheory.Published.GreenSeriesSt : Prop` (`GreenSeriesSt.lean:7–9`) asserts that for every prime $g$, `L : LabelDatum g`, and $N \ge 1$, there is an assignment $f \mapsto \tau(f)$ on squarefree degree-$N$ monic polynomials $f \in \mathrm{sqSet}(g, N)$ ($f(0) \neq 0$) such that each $\tau(f)$ is an irreducible generic character of $\mathrm{GL}_N(\mathbb F_g)$ (`IsIrr` and `IsGeneric`), $\tau(f)(1)\cdot\mathrm{torusCard}(g, f) = \prod_{i=1}^N (g^i - 1)$, and $\tau(f) = \tau(f') \implies f = f'$.

---

#### Lemmas and conditional main theorem

**Lemma 13.38 (Elliptic Parseval pinning `UpperTheory.Zero.LLC.pin` and the central scalar law `nameCentral`).** [Lean, read] *Both `Pin` (`PairCheckThreeTwo.lean:177–179`) and `NameCentral` (`NameCentral.lean:54–108`) hold unconditionally in the archive (using only Mathlib finite-field, character-orthogonality, and matrix-trace lemmas).*

*Proof.* Fix a prime $g$, $n > 0$, and a degree-$n$ extension $K/\mathbb F_g$, so $\lvert K^\times\rvert = g^n - 1$ (`card_unitsK`, `PairCheckThreeTwo.lean:47–49`).

*Step 1: Proper-subfield locus $D$ and numerical bounds (`PinFld.lean:54–194`, `PinNum.lean:7–253`).* Let $D := \{z \in K^\times : \deg\operatorname{minpoly}_{\mathbb F_g}(z) \neq n\}$. If $z \in D$, its minimal polynomial divides $X^{g^d} - X$ where $d = \deg\operatorname{minpoly}_{\mathbb F_g}(z)$ strictly divides $n$; picking a prime $p \mid (n/d)$, we have $d \mid (n/p)$ and hence $z^{g^{n/p} - 1} = 1$ (`pow_of_deg`, `PinFld.lean:54–94`). Therefore $D$ is contained in $\bigcup_{p \mid n} \{z \in K^\times : z^{g^{n/p} - 1} = 1\}$; since a polynomial of degree $g^{n/p} - 1$ over the field $K$ has at most $g^{n/p} - 1$ roots,
$$\#D \le \mathrm{bd}(g, n) := \sum_{p \in \mathrm{primeFactors}(n)} \left(g^{n/p} - 1\right) \le 2 g^{\lfloor n/2 \rfloor}$$
(`exists_D`, `PinFld.lean:96–138`; `bd_le`, `PinNum.lean:16–45`, bounding the largest prime-divisor term $g^{\lfloor n/2\rfloor} - 1$ plus at most $\lfloor n/2\rfloor$ smaller powers $\le g^{\lfloor n/2\rfloor - 1}$). Elementary induction in `PinNum.lean` then establishes two strict inequalities:
- `one_bd` (`:240–253`): $n \cdot \mathrm{bd}(g, n) + 1 < g^n$ for **every** $g \ge 2$ and $n \ge 1$;
- `two_bd` (`:211–238`, via `big` at `:47–209`): $2 n \cdot \mathrm{bd}(g, n) + 1 < g^n$ for every prime $g$ and $n \ge 1$ **except** the four pairs $(g, n) \in \{(2, 2), (3, 2), (2, 4), (2, 6)\}$.

*Step 2: Parseval vs. $L^\infty$ support inequality (`PinChar.lean:10–109`).* For disjoint subsets $A, B \subseteq \operatorname{Hom}(K^\times, \mathbb C^\times)$, define $\mathrm{dif}(A, B)(z) := \sum_{\chi \in A} \chi(z) - \sum_{\chi \in B} \chi(z)$ (`:33–35`). Every unit character takes values on the unit circle ($\lvert\chi(z)\rvert = 1$, `norm_char`, `:10–21`), and character orthogonality on the finite abelian group $K^\times$ gives $\sum_{z \in K^\times} \chi_1(z)\overline{\chi_2(z)} = \lvert K^\times\rvert\,\delta_{\chi_1, \chi_2}$ (`sum_mul_conj`, `:22–31`). Because $A \cap B = \emptyset$, expanding $\sum_{z \in K^\times} \lvert\mathrm{dif}(A, B)(z)\rvert^2$ kills all cross terms and yields exact Parseval norm (`parseval`, `:52–85`):
$$\sum_{z \in K^\times} \lvert\mathrm{dif}(A, B)(z)\rvert^2 = (g^n - 1)\,(\#A + \#B).$$
If $\mathrm{dif}(A, B)(z) = 0$ for every $z \notin D$ and $\#A + \#B > 0$, then the entire $L^2$ mass sits on $D$, where the triangle inequality bounds each summand by $\lvert\mathrm{dif}(A, B)(z)\rvert \le \#A + \#B$. Hence $(g^n - 1)(\#A + \#B) \le \#D \cdot (\#A + \#B)^2$; canceling $\#A + \#B > 0$ gives (`card_le`, `:87–109`):
$$g^n - 1 \le \#D \cdot (\#A + \#B).$$

*Step 3: Proof of `Pin.1` and `Pin.2` (`PairCheckThreeTwo.lean:51–179`).* For a regular character $\theta$, its Frobenius orbit $A = \mathrm{cj}(\theta) := \{\theta^{g^j} : j < n\}$ has cardinality $\#A = n$ (`card_cj`, `PinFld.lean:147–153`).
- Applying Step 2 with $B = \emptyset$: if $\sum_{j < n}\theta(z^{g^j}) = 0$ for all $z \notin D$, then $g^n - 1 \le n\,\#D \le n\,\mathrm{bd}(g, n)$, contradicting `one_bd` ($n\,\mathrm{bd}(g, n) + 1 < g^n$). This proves `Pin.1` (`main` first branch, `PairCheckThreeTwo.lean:104–120`).
- Suppose next that regular $\theta, \theta'$ have identical orbit sums outside $D$, and assume for contradiction that $\theta' \notin \mathrm{cj}(\theta)$. Then $A = \mathrm{cj}(\theta)$ and $B = \mathrm{cj}(\theta')$ are **disjoint** orbits of size $n$ (`disj_cj`, `PinFld.lean:176–194`), so $\#A + \#B = 2n$ and $\mathrm{dif}(A, B)$ vanishes outside $D$. Whenever $(g, n) \notin \{(2, 2), (3, 2), (2, 4), (2, 6)\}$, Step 2 gives $g^n - 1 \le 2n\,\#D \le 2n\,\mathrm{bd}(g, n)$, contradicting `two_bd` (`PairCheckThreeTwo.lean:121–150`).
- At the four exceptional pairs $(2, 2), (3, 2), (2, 4), (2, 6)$, `exc` (`:51–99`) chooses a generator $\eta_0$ of the cyclic dual group $\operatorname{Hom}(K^\times, \mathbb C^\times)$ (`exists_gen_char`, `PinFld.lean:9–52`) and sets $e := 1, 2, 3, 21$ respectively. In each case $(g^{n/p} - 1) \mid e$ for every prime $p \mid n$, so $\eta_0^e(z) = 1$ on $D$ by `pow_of_deg`. Since $\mathrm{dif}(A, B)(z) = 0$ outside $D$, we have $\mathrm{dif}(A, B)(z)\,\eta_0^e(z) = \mathrm{dif}(A, B)(z)$ for **all** $z \in K^\times$! Taking the inner product against $\chi \cdot \eta_0^e$ for $\chi \in A$ (`mul_mem`, `PinChar.lean:110–133`) gives $\langle \mathrm{dif}(A, B), \chi \cdot \eta_0^e\rangle = \langle \mathrm{dif}(A, B)\,\eta_0^e, \chi \cdot \eta_0^e\rangle = \langle \mathrm{dif}(A, B), \chi\rangle = 1 \neq 0$, which forces $\chi \cdot \eta_0^e \in A$ (since elements of $B$ have inner product $-1$ and others $0$). Writing $\theta = \eta_0^t$ and $\theta' = \eta_0^{t'}$, both $t$ and $t'$ satisfy `Reg g n (g^n-1) t ∧ Cl g n (g^n-1) e t` (shift closure under $+e \bmod (g^n - 1)$). Finite kernel evaluation (`pairCheck_two_two`, `pairCheck_three_two`, `pairCheck_two_four`, `pairCheck_two_six`, `:29–41`) verifies `Pair`: for $(2, 2), (3, 2), (2, 4)$ no regular exponent is $+e$-closed, while for $(2, 6)$ only the single orbit $\{7, 14, 28, 56, 49, 35\} \bmod 63$ is $+21$-closed, so in all four cases $t' \equiv t g^j \pmod{g^n - 1}$, proving `Pin.2`.

*Step 4: Proof of `nameCentral` from `Pin.1` (`NameCentral.lean:15–108`).* Let $\tau$ be simple and named by a regular $\theta : K^\times \to \mathbb C^\times$, and let $c \in \mathbb F_g^\times$. Because $c I_n$ lies in the center of $\mathrm{GL}_n(\mathbb F_g)$, $\tau(c I_n)$ is a $\mathrm{GL}_n(\mathbb F_g)$-equivariant endomorphism of the simple module $\tau$; over the algebraically closed field $\mathbb C$, Schur's lemma (`schur_scalar`, `:15–24`) gives $\tau(c I_n) = \alpha\,\mathrm{id}_\tau$ for some scalar $\alpha \in \mathbb C$. Choose an $\mathbb F_g$-basis $b$ of $K$, so left multiplication on $K$ defines an injective homomorphism $L : K^\times \to \mathrm{GL}_n(\mathbb F_g)$ whose characteristic polynomial on $x \in K^\times$ equals the algebra characteristic polynomial of $x$ (`charpoly_lmul`, `:26–34`). By `Pin.1`, pick $z \in K^\times$ with $\deg\operatorname{minpoly}_{\mathbb F_g}(z) = n$ and $S := \sum_{j < n}\theta(z^{g^j}) \neq 0$. Scaling by $c \in \mathbb F_g^\times$ preserves minimal-polynomial degree (`natDegree_smul`, `:36–52`), so both $L(z)$ and $L(c z) = (c I_n)\,L(z)$ have irreducible degree-$n$ characteristic polynomials with roots $z$ and $c z$. On the one hand, $\tau(L(c z)) = \tau(c I_n)\,\tau(L(z)) = \alpha\,\tau(L(z))$ has trace $\alpha\,\chi_\tau(L(z)) = \alpha\,(-1)^{n-1} S$. On the other hand, `Names` applied to $L(c z)$ and $(c z)^{g^j} = c\,z^{g^j}$ ($c \in \mathbb F_g^\times$) gives
$$\chi_\tau(L(c z)) = (-1)^{n-1} \sum_{j < n} \theta(c)\,\theta\!\left(z^{g^j}\right) = \theta(c)\,(-1)^{n-1} S.$$
Since $(-1)^{n-1} S \neq 0$, canceling it yields $\alpha = \theta(c)$, i.e. $\tau(c I_n) = \theta(c)\,\mathrm{id}_\tau$. $\square$

**Lemma 13.39 (Small-exponent regularity and Newton power-sum label uniqueness for all $q \ge 2$).** [Lean, read] *Let $F$ be any finite field of cardinality $q \ge 2$, let $C : \mathrm{LabelConv}\,F$, and let $d \ge 1$.*

1. *(`reg_small_lemma_4`, `CuspidalLabelUnique.lean:278–309`; `natDegree_minpoly_gen_pow`, `CuspidalLabelPolynomialUniqueAllPrimes.lean:53–101`.) For every integer $1 \le j \le d$, the power $\mathrm{gen}(d)^j \in \bar F^\times$ is regular over $F$, so its minimal polynomial over $F$ is monic irreducible of degree $d$ and occurs as the characteristic polynomial of an elliptic matrix $y_j \in \mathrm{GL}_d(F)$ (`exists_elliptic`, `CuspidalLabelUnique.lean:209–242`).*
2. *(`hasCuspLabel_unique`, `CuspidalLabelUnique.lean:360–406`, and `LabelUniqueAll.label_eq`, `CuspidalLabelPolynomialUniqueAllPrimes.lean:103–153`.) If $\mathrm{HasCuspLabel}\,C\,d\,W\,P$ and $\mathrm{HasCuspLabel}\,C\,d\,W'\,P'$ satisfy $\chi_W = \chi_{W'}$ (in particular when $W = W'$), then $P = P'$. No restriction $q \ge 5$ and no cuspidal exhaustion hypothesis are used.*

*Proof.* (1) Suppose $(\mathrm{gen}(d)^j)^{q^e} = \mathrm{gen}(d)^j$ for some $1 \le e < d$. Because $\mathrm{gen}(d)$ has multiplicative order $q^d - 1$, this means $j q^e \equiv j \pmod{q^d - 1}$. In `reg_small_lemma_4` (`CuspidalLabelUnique.lean:278–309`), if $2 e > d$, multiplying both sides by $q^{d - e}$ and using $q^d \equiv 1 \pmod{q^d - 1}$ gives $j q^{d - e} \equiv j \pmod{q^d - 1}$ with $1 \le d - e$ and $2(d - e) \le d$ (equivalently, in `natDegree_minpoly_gen_pow`, `CuspidalLabelPolynomialUniqueAllPrimes.lean:65–101`, $e_0 := \deg\operatorname{minpoly}_{\mathbb F_g}(\mathrm{gen}(d)^j)$ properly divides $d$, so $2 e_0 \le d$ directly). Thus we have an integer $e'$ with $1 \le e'$ and $2 e' \le d$ such that $(q^d - 1) \mid j(q^{e'} - 1) > 0$. Since $q \ge 2$ and $d \le 2(d - e') \le 2^{d - e'} \le q^{d - e'}$, we have $d q^{e'} \le q^d$, whence
$$0 < j\!\left(q^{e'} - 1\right) \le d\!\left(q^{e'} - 1\right) = d q^{e'} - d \le q^d - d < q^d - 1,$$
contradicting $(q^d - 1) \mid j(q^{e'} - 1)$ (`small_lt_lemma_3`, `:244–276`). Hence the $d$ Frobenius conjugates $(\mathrm{gen}(d)^j)^{q^a}$ ($a < d$) are pairwise distinct (`regular_iff_degree`, `:118–177`), giving a degree-$d$ monic irreducible minimal polynomial realized as the characteristic polynomial of an elliptic matrix $y_j \in \mathrm{GL}_d(F)$ (`exists_elliptic`, `:209–242`).

(2) Let $r, r' \in \bar F^\times$ be roots of $P$ and $P'$ (`exists_root`, `:179–207`), and set $u_a := \iota(r^{q^a})$, $v_a := \iota((r')^{q^a}) \in \mathbb C$ for $0 \le a < d$. Evaluating $\chi_W(y_j) = \chi_{W'}(y_j)$ via `HasCuspLabel` at $k = j$ for each $1 \le j \le d$ and canceling $(-1)^{d-1} \neq 0$ equates the first $d$ power sums:
$$\sum_{a=0}^{d-1} u_a^j = \sum_{a=0}^{d-1} v_a^j \qquad (1 \le j \le d).$$
Specializing Mathlib's multivariate Newton recurrence `MvPolynomial.mul_esymm_eq_sum` (`Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean:225`) over the characteristic-zero field $\mathbb C$ expresses $m \cdot e_m(u_0, \dots, u_{d-1})$ for each $1 \le m \le d$ inductively in terms of $e_0, \dots, e_{m-1}$ and the power sums $p_1, \dots, p_m$ (`esymm_eq_of_psum_eq`, `CuspidalLabelPolynomialUniqueAllPrimes.lean:17–27`; `multiset_eq_of_psum_lemma_5`, `CuspidalLabelUnique.lean:311–358`). Dividing by $m \neq 0$ in $\mathbb C$ gives $e_m(u) = e_m(v)$ for all $1 \le m \le d$, hence $\prod_{a < d} (X - u_a) = \prod_{a < d} (X - v_a)$ in $\mathbb C[X]$. Evaluating at $X = u_0 = \iota(r)$ gives $0 = \prod_{a < d} (\iota(r) - \iota((r')^{q^a}))$, so $\iota(r) = \iota((r')^{q^a})$ for some $a < d$. Injectivity of $\iota : \bar F^\times \hookrightarrow \mathbb C^\times$ implies $r = (r')^{q^a}$; since $P$ and $P'$ are monic irreducible over $F$ and $(r')^{q^a}$ is a root of $P'$, we conclude $P = \operatorname{minpoly}_F(r) = \operatorname{minpoly}_F((r')^{q^a}) = P'$. $\square$

**Theorem 13.40 (Conditional main theorem: coordinate-free `nameLaws`, representation-level `PM.greenCuspidal`, convention re-choice, and consumer ledger).** [Lean, read] *Let $g$ be prime, inheriting `PM.greenRegularCharacters` (`GreenCuspidalCharsByRegularCharsProof.lean:137`), `isCharacter_cuspidal_rootSum_regular`, `(I1)`–`(I2)`, and `(I4)`–`(I9)` at the conditional depths established in Sections 13.4.4–13.4.11.*

- **(A) Coordinate-free naming laws and local Langlands wiring (`NameLaws.lean:78–123`, `CentralUnit.lean:39–202`, `ParUniq.lean:15–53`).** *`UpperTheory.Zero.LLC.nameLaws` holds (consuming only `PM.greenRegularCharacters` and Lemma 13.38). Downstream in the depth-zero local Langlands chain for Chapter 12 (`P15`), `parEx` consumes Clauses 1, 4, 2 of `nameLaws` together with `nameCentral` (proving that the local parameter `TypeAt y V` is independent of the auxiliary unramified extension $D$), while `parUniq` consumes Clauses 1 and 3 (proving uniqueness and injectivity of the cuspidal Weil–Deligne parameter).*
- **(B) Representation-level `PM.greenCuspidal` and exact three-clause dependency split (`HarishChandraModules.lean:12`, `GreenCuspidal.lean:268–304`, `LabelMapNonempty.lean:18–127`).** *Assume in addition the four named statement-level interfaces `[Lean]`: **(U1)** converse regular-exponent existence `GlobalTheory.CuspFormula.exists_regular` (`ExistsLabel.lean:49`), **(U2)** elliptic determination of cuspidal characters `GlobalTheory.CuspGL.cuspElliptic_statement` (`IrrCharEqOneOfSubsingleton.lean:45`), **(U3)** character-to-module Jacquet vanishing `isCuspidal_of_sum_char` plus `harishChandra_induction_character_properties`, and **(U4)** central idempotent orthogonality `zIdemOrthogonal_holds` / `central_idempotent_properties`. Then for every `L : LabelDatum g` and $d \ge 1$, `GreenAll.cuspParam_all (conv L) d` builds `Wmap` satisfying `CuspParam (conv L) d Wmap`, and `PM.greenCuspidal` proves `GlobalTheory.Published.GreenCuspidal` (`= GlobalTheory.GLq.Green`) with the following clause-by-clause consumption:*
  1. **Existence (+ degree)** *(`h1 : IsCuspOf L P (τ P)`): existence of a simple cuspidal module with label $P$ (`exists_cuspidal_label`, `ExistsCuspidalWithLabel.lean:57–135`) consumes generator-power regularity (§13.4.9) and `isCharacter_cuspidal_rootSum_regular` (§§13.4.4, 13.4.10–13.4.11); the degree identity $\dim W(P) = \prod_{i=1}^{d-1}(g^i - 1)$ on this representation-level path (`finrank_of_simple_cuspidal`, `CuspidalParametrization.lean:50–72`) consumes `(I2)` (`psi_one`, §13.4.10) together with **(U1)** `exists_regular` (whereas on the `green_of_regular` path of §§13.4.1 and 13.4.4, existence + degree come directly from `exists_cusp_of_regular` without **(U1)**).*
  2. **Injectivity** *(`h2 : τ P = τ P' → P = P'`): proved in `GreenCuspidal.lean:286–290` from `hasCuspLabel_of_character` (`:258–266`, using **(U3)**) and Lemma 13.39 (`hasCuspLabel_unique`). It consumes **neither** **(U1)**, **nor** **(U2)**, **nor** **(U4)**, **nor** $g \ge 5$, **nor** exhaustion.*
  3. **Exhaustion** *(`h3 : IsCusp σ → ∃ P, σ = τ P`): proved in `GreenCuspidal.lean:291–301` via `isCuspidal_of_isCusp` (`:168`, using **(U3)**), `exists_label` (`LabelMapNonempty.lean:18–81`, using **(U1)** and `exists_cuspidal_label`), and `iso_of_label` (`:83–120`, using **(U2)** and **(U4)**).*
- **(C) Re-choice well-definedness and downstream `GreenCuspidal` consumers.** *Changing the residue-field model $e : K \xrightarrow{\sim} K'$ pulls regular Frobenius orbits back via $\theta' \mapsto \theta' \circ e$ while fixing the character $\chi_\tau$ (Part A). Changing a concrete datum $L = (\iota, \mathrm{gen})$ to $L' = (\iota^a, \mathrm{gen}^b)$ ($a, b \in (\mathbb Z/(g^d - 1)\mathbb Z)^\times$) moves a label root by $x' = x^{a^{-1} b}$ (`exists_beta`, §13.4.9; specializing to $x' = x^{a^{-2}}$ when `rootC` is held fixed so $b \equiv a^{-1}$), and more generally between **any** abstract `(C, O : LabelMap (ZMod g) C)` and `L : LabelDatum g`, `exists_perm_deg` / `exists_perm` (`AdmissibleLabelWeights…:50–114`) constructs a degree-preserving bijection $\sigma$ on prime labels such that $O.\mathrm{lab}(d, P)$ and `τ_L (σ P)` afford the **same** cuspidal character. Across the three main-path consumers of `PM.greenCuspidal`:*
  1. `GreenSeries.green_series` *(`ProdFactorsOfMonic.lean:243–351`, supplying `green_series_st_of_literature` at `EveryCharacterOfLiteratureOfVWin.lean:401, 728, 790`) **discards exhaustion** (`:251`), consuming only **existence + degree and injectivity** (plus named Mackey/Whittaker interfaces `[Lean]`) to prove `GreenSeriesSt` for all primes $g$.*
  2. `cuspParam_of_green` *(`CuspParamOfGreenParametrisation.lean:106–138`) **discards `h2`** (`:110`), combining **existence + degree, exhaustion, and Lemma 13.39 (`LabelUniqueAll.label_eq`)** to construct `CuspParam` for arbitrary `(t, ζ)` (`IsGenSys ζ`), aligning `eSerC = eSerO` in `ExistsGreenCuspidalLabellingSameGenerators.lean:33` and `ExistsTameGeneratorsGreenCuspidalLabelling.lean:40`.*
  3. `exists_perm_deg`, `exists_perm`, and `eSer_eq` *(`AdmissibleLabelWeights…:50–250`, fed by `green_cuspidal_of_literature` at `EveryCharacterOfLiteratureOfVWin.lean:397, 668`) consume **all three clauses** (existence, injectivity, and exhaustion) at `:56` to build $\sigma$ for all primes $g$, and then invoke the named series-label uniqueness interface `harishChandraSeriesLabel_exists_unique_GLn` (`[Lean]`, requiring $5 \le g$) at `:216` to transport central Harish-Chandra idempotents via $\mathrm{eSerO}(O, r, f) = \mathrm{eSerC}(L, r, \operatorname{ext}\sigma(f))$.*

*Proof.* **Part (A) (`NameLaws.lean:11–123`).** Unpack `⟨τF, hτ1, hτ2, hτ3⟩ := PM.greenRegularCharacters g n hn K hK` (`:81`) and `hpin := UpperTheory.Zero.LLC.pin` (`:90`, Lemma 13.38).
- *Helper 1 (`exists_elt`, `:11–36`):* Given any $z \in K^\times$ with $\deg\operatorname{minpoly}_{\mathbb F_g}(z) = n$, the power basis of $\mathbb F_g[z] = K$ transports left multiplication by $z$ via `Algebra.leftMulMatrix` to a matrix $y \in \mathrm{GL}_n(\mathbb F_g)$ whose characteristic polynomial equals $\operatorname{minpoly}_{\mathbb F_g}(z)$, which is irreducible with root $z$.
- *Helper 2 (`regular_pow`, `:37–76`):* Since $\lvert K^\times\rvert = g^n - 1$, Fermat/Lagrange gives $\theta^{g^n} = \theta$ (`pow_period`, `:37–49`), so $\theta^{g^j} = \theta^{g^{j \bmod n}}$ (`pow_mod`, `:57–61`) and $\theta^{g^j}$ remains regular whenever $\theta$ is regular (`:62–76`).
- *Clause 2 (`huniq`, `:87–94`):* Suppose regular $\theta, \theta'$ both satisfy `Names g n _ τ`. For every $z \in K^\times$ of minimal-polynomial degree $n$, `exists_elt` produces an elliptic $y \in \mathrm{GL}_n(\mathbb F_g)$ with root $z$, so $(-1)^{n-1}\sum_{j < n}\theta(z^{g^j}) = \chi_\tau(y) = (-1)^{n-1}\sum_{j < n}\theta'(z^{g^j})$. Canceling $(-1)^{n-1} \neq 0$ and applying `hpin.2` (Lemma 13.38) yields $j < n$ with $\theta' = \theta^{g^j}$.
- *Clause 1 (`hNex`, `:102–103`) and Clause 3 (`hNchar`, `:94–100, 104–105`):* By exhaustion `hτ3`, for every cuspidal $\tau$ there is a regular $\theta_0$ with `τ.character = τF θ_0`; since `(hτ1 θ_0 hθ_0).2.2` gives the elliptic trace formula for `τF θ_0`, $\theta_0$ names $\tau$, proving Clause 1. Next, the key internal step `hchar` (`:94–100`) shows that **any** regular $\theta$ naming a cuspidal $\tau$ satisfies `τ.character = τF θ`: pick $\theta_0$ from `hτ3` with `τ.character = τF θ_0`; then both $\theta$ and $\theta_0$ name $\tau$, so `huniq` (`hpin.2`) gives $\theta_0 = \theta^{g^j}$ for some $j < n$, and the **reverse** orbit implication `(hτ2 θ θ_0 hθ hθ_0).mpr ⟨j, hj, hθ_0⟩` gives `τF θ = τF θ_0 = τ.character` (note that `hτ2.mp` is never invoked!). If now cuspidal $\tau, \tau'$ are named by regular $\theta$ and $\theta^{g^j}$ ($j \in \mathbb N$), reducing $j \bmod n$ via `pow_mod` and `regular_pow` makes $\theta^{g^{j \bmod n}}$ regular, `hchar` gives `τ.character = τF θ` and `τ'.character = τF (θ^{g^{j \bmod n}})`, and `hτ2.mpr` equates them, proving Clause 3.
- *Clause 4 (`hNtr`, `:106–123`):* Let $e : K \simeq^{+*} K'$ be a bare ring isomorphism. By `RingHom.ext_zmod` (`Mathlib/Data/ZMod/Basic.lean:1096`), $e$ automatically commutes with `algebraMap (ZMod g) _` (`:108–109`), turning $e$ into an $\mathbb F_g$-algebra equivalence $e_A : K \simeq_A K'$. Thus any root $z \in K^\times$ of irreducible $\operatorname{charpoly}(y)$ maps to a root $e(z) \in (K')^\times$ of the same polynomial over $\mathbb F_g$, and `e(z^{g^j}) = e(z)^{g^j}` transports the elliptic sum of $\theta'$ on $K'$ to that of $\theta' \circ e$ on $K$; similarly $(\theta' \circ e)^{g^i} = (\theta' \circ e)^{g^j}$ pushes forward along surjective `Units.map e` to $(\theta')^{g^i} = (\theta')^{g^j}$, giving $i = j$.
- *Downstream wiring into `parEx` and `parUniq`:* In `CentralUnit.lean:76–77`, `parEx` instantiates `nameLaws` on the residue fields of two auxiliary unramified extensions $D_1, D_2$ of degree $n$: Clause 1 names the finite-level cuspidal Bushnell–Kutzko type, `nameCentral` (`:133`) identifies its central restriction on residue units with $\theta\rvert_{\mathbb F_g^\times}$ so it glues to the uniformizer action, and when comparing $D_1$ with $D_2$ along a residue isomorphism (`:188–189`), Clause 4 (`hNtr`) pulls the second regular name back to the first residue field where Clause 2 (`hNuniq`) places both names in one Frobenius orbit, proving well-definedness of `TypeAt y V`. In `ParUniq.lean:27–53`, if two representations share the same `TypeAt` parameter, `parUniq` unpacks Clause 1 (`:29`) to name their depth-zero cuspidal types, matches Frobenius orbits of regular characters on residue units and central uniformizers, and invokes Clause 3 (`hNchar`, `:46`) to deduce equality of cuspidal characters and equivalence of representations. Both feed `GoodMap.lean:144` → `CuspEx.lean:168` → `RecTExists.lean:20` (Chapter 12, `P15`).

**Part (B) (`GreenCuspidal.lean:60–304`, `LabelMapNonempty.lean:18–127`, `ExistsCuspidalWithLabel.lean:57–135`, `CuspidalParametrization.lean:50–72`).** Given `L : LabelDatum g`, `conv L` (`GreenCuspidal.lean:60–114`) packages `L.teich` and `L.gen` into a `LabelConv (ZMod g)`, and `thetaOf_gen_pow` (`:198–220`) verifies `L.thetaOf d (L.gen d ^ k) z = (L.teich z) ^ k` by expanding $z = \mathrm{gen}(d)^m$ and commuting powers in $\mathbb C$.
1. *Existence + degree (`h1`):* For any degree-$d$ prime label $P$, choosing a root $r = \mathrm{gen}(d)^t$ of $P$, `exponent_regular_of_natDegree_minpoly_generator_pow` (§13.4.9) certifies regularity of $t$, and `exists_cuspidal_label` (`ExistsCuspidalWithLabel.lean:57–135`) feeds $t$ into `isCharacter_cuspidal_rootSum_regular` (§§13.4.4, 13.4.10–13.4.11) and `fixed_eq_zero` (`GreenCuspidal.lean:37–58`, averaging a representation over a subgroup of zero character sum) to produce a simple cuspidal module `Wmap P` satisfying `HasCuspLabel (conv L) d (Wmap P) P`. Then `isCuspOf_character` (`GreenCuspidal.lean:222–256`) converts module-level `HasCuspLabel` to character-level `IsCuspOf L P (Wmap P).character`, where the degree $\dim_{\mathbb C}(\mathrm{Wmap}\,P) = \prod_{i=1}^{d-1}(g^i - 1)$ is supplied by `finrank_of_simple_cuspidal` (`CuspidalParametrization.lean:50–72`), which applies **(U1)** `exists_regular` to express $\chi_{\mathrm{Wmap}\,P}$ as $(-1)^{d-1}\psi_{s_k}$ and evaluates at $1$ via `(I2)` (`psi_one`, §13.4.10).
2. *Injectivity (`h2`):* Define `τ P := if hP : IsPrimeLab P ∧ P.natDegree = d then (Wmap P).character else 0` (`GreenCuspidal.lean:274`). If $P, P'$ are degree-$d$ prime labels with `τ P = τ P'`, then `(Wmap P).character = (Wmap P').character`; `hasCuspLabel_of_character` (`:258–266`) transports `HasCuspLabel (conv L) d (Wmap P) P'` onto the single module `Wmap P` (since `HasCuspLabel` depends on `Wmap P'` only through simplicity, cuspidality, and character values), and Lemma 13.39 (`hasCuspLabel_unique`) gives $P = P'$.
3. *Exhaustion (`h3`):* In `LabelMapNonempty.lean`, given any simple cuspidal module $W$, `exists_label` (`:18–81`) invokes **(U1)** `exists_regular` to find a regular exponent $k$ matching $\chi_W$ on elliptic classes, takes $P := \operatorname{minpoly}_{\mathbb F_g}(\mathrm{gen}(d)^k)$, and shows `HasCuspLabel (conv L) d W P`; next, `iso_of_label` (`:83–120`) compares $W$ and `Wmap P` (which share the same elliptic trace formula for $P$), invokes **(U2)** `cuspElliptic_statement` to deduce $\chi_W = \chi_{\mathrm{Wmap}\,P}$, and upgrades character equality of simple modules to an isomorphism $W \cong \mathrm{Wmap}\,P$ via **(U4)** central idempotent orthogonality (`zIdemOrthogonal_holds`). Back in `GreenCuspidal.lean:291–301`, any character $\sigma$ satisfying `IsCusp σ` comes from a simple module $V$ whose character sums vanish on proper unipotent radicals (`res_eq_zero_iff`, `:146–156`, via **(U3)** `harishChandra_induction_character_properties`), whence **(U3)** `isCuspidal_of_sum_char` (`:179`) yields `IsCuspidal V`; `cuspParam_all` then gives $V \cong \mathrm{Wmap}\,P$, so $\sigma = \chi_V = \tau(P)$.

**Part (C) (Convention re-choice and the three `GreenCuspidal` consumers).**
1. *`GreenSeries.green_series` (`ProdFactorsOfMonic.lean:243–351`):* Given `hG : GreenCuspidal`, line `:251` writes `obtain ⟨τ, h1, h2, -⟩ := hG.green g L d hd`, **explicitly dropping the third (exhaustion) component**. To each squarefree degree-$N$ monic polynomial $f \in \mathrm{sqSet}(g, N)$ ($f(0) \neq 0$), `Q f` orders the distinct monic irreducible factors $P_1, \dots, P_r$ of $f$ (`Prod.lean`), attaches the cuspidal characters $\tau_{d_i}(P_i)$ from `h1`, and forms the parabolically induced character $\mathrm{hcL}(Q(f), N)$. Using the named Whittaker and Mackey interfaces `[Lean]` (`wh_cusp_eq_one`, `wh_hcT`, `ip_hcL_cusp`, `hc_degree`), `whHcL` (`:112–137`) shows that $\mathrm{hcL}(Q(f), N)$ has Whittaker dimension $1$, while `genericOfWh` (`:67–98`) shows that for *distinct* prime factors (`Pairwise Ne` from squarefreeness of $f$) the Mackey self-pairing is $1$, so $\mathrm{hcL}(Q(f), N)$ is **irreducible and generic**! Its degree satisfies `degHcL` (`:139–187`) by multiplying the cuspidal degrees $\prod_{j < d_i}(g^j - 1)$ from `h1` against $[\mathrm{GL}_N(\mathbb F_g) : P_{d_1,\dots,d_r}]$. Finally, if $\mathrm{hcL}(Q(f), N) = \mathrm{hcL}(Q(f'), N)$, `labelsOfEq` (`:189–241`, using Mackey intertwining `ip_hcL_cusp` and **injectivity `h2`** on each cuspidal block) proves that the multisets of prime factors coincide; since $f$ and $f'$ are monic and squarefree, $f = \prod P_i = f'$. Wrapped via `PositivityTheory.Prw.greenSeriesSt_of` (`BridgesAut.lean:49`), this supplies `green_series_st_of_literature` (`EveryCharacterOfLiteratureOfVWin.lean:401, 728, 790`).
2. *`cuspParam_of_green` (`CuspParamOfGreenParametrisation.lean:106–138`):* Given any embedding $t : \overline{\mathbb F_g}^\times \hookrightarrow \mathbb C^\times$ and norm-compatible generator system $\zeta$ (`IsGenSys ζ`), `datum t hζ` (`:20–68`) packages `(t, ζ)` into a `LabelDatum g`. Line `:110` unpacks `obtain ⟨τ, hτ, -, hall⟩ := hgreen g (datum t hζ) d hd` — **dropping `h2`** — chooses a simple module `Wmap P` realizing `τ P` from `hτ`, proves `HasCuspLabel` via `hasCuspLabel_iff` (`:70–93`), gets existence of a matching $P$ for any simple cuspidal $W$ from **exhaustion `hall`** (`:118–121`) + `nonempty_iso_of_character` (`:95–104`), and recovers uniqueness of $P$ directly from **Lemma 13.39 (`LabelUniqueAll.label_eq`, `:125`)**! This feeds `exists_greenLab` (`ExistsGreenCuspidalLabellingSameGenerators.lean:33`) and `exists_tame_generators_cuspidal_labelling` (`ExistsTameGeneratorsGreenCuspidalLabelling.lean:40`).
3. *`exists_perm_deg`, `exists_perm`, and `eSer_eq` (`AdmissibleLabelWeightsOfGreenCuspidalParametrisa.lean:50–250`):* Let $C : \mathrm{LabelConv}(\mathrm{ZMod}\,g)$, $O : \mathrm{LabelMap}(\mathrm{ZMod}\,g)\,C$, and $L : \mathrm{LabelDatum}\,g$. In `exists_perm_deg` (`:50–87`), line `:56` unpacks **all three clauses** `⟨τ, h1, h2, h3⟩ := hG g L d hd`:
   - For each degree-$d$ prime label $P$ on the $O$-side, `O.lab d P` is simple and cuspidal, so `(O.lab d P).character` satisfies `IsCusp`; **exhaustion `h3`** produces an $L$-prime label $Q$ with `(O.lab d P).character = τ Q`, defining a map $f_{\mathrm{fwd}} : P \mapsto Q$.
   - Conversely, for each degree-$d$ prime label $Q$ on the $L$-side, **existence `h1`** gives `IsCusp (τ Q)`, realising `τ Q = V.character` for a simple cuspidal module $V$; `O.param d` gives a unique $P$ with $V \cong O.\mathrm{lab}\,d\,P$, so `(O.lab d P).character = τ Q`.
   - On `f_fwd P = f_fwd P'`, `(O.lab d P).character = (O.lab d P').character` gives $O.\mathrm{lab}\,d\,P \cong O.\mathrm{lab}\,d\,P'$ (`iso_of_char`, `:33–48`) and hence $P = P'$ by uniqueness in `O.param`; on the return side, `(O.lab d P).character = τ Q` and `(O.lab d P).character = τ Q'` give `τ Q = τ Q'`, whence **injectivity `h2`** gives $Q = Q'$!
   Gluing these finite bijections across all degrees $d \ge 1$ defines the degree-preserving permutation $\sigma := e^{-1}$ (`exists_perm`, `:89–114`) satisfying `(O.lab P.natDegree P).character = τ_L (σ P)`, and `ext σ` (`:116–128`) extends $\sigma$ multiplicatively across prime factorizations. Finally, when $5 \le g$, `exists_labelO` (`:210–231`) invokes the named interface `harishChandraSeriesLabel_exists_unique_GLn` (`[Lean]`, `:216`) and transports `HasLabel L r χ g₀` to $O$-labels via $\sigma$, proving in `eSer_eq` (`:233–250`, using central idempotent summation over constituents) that for every monic polynomial $f$ of degree $r$ with $f(0) \neq 0$,
   $$\mathrm{eSerO}(O, r, f) = \mathrm{eSerC}\!\left(L, r, \operatorname{ext}\sigma(f)\right). \qquad \square$$

---

#### Remarks

1. *Comparison with Green (1955), §§7–8 (`[Green1955]`, printed pp. 437–445).* In Green's paper, a degree-$k$ Frobenius orbit in $\mathbb F_{q^k}^\times$ is called a *$k$-simplex* $\mathfrak f$ (`Definition 7.3`, p. 438; roots of a monic irreducible polynomial $f \in \mathbb F_q[X]$ of degree $k$ are dual to $k$-simplexes via `Lemma 7.6`, pp. 439–440). Green defines the *primary irreducible* (cuspidal) character $(-1)^{k-1} J_k(1) = (-1)^{k-1} I_k^1[\{1\}]$ in `Theorem 12` (p. 439) and `Lemma 7.7` (p. 441): it vanishes on every class whose characteristic polynomial involves two or more distinct irreducible factors, whereas on any elliptic element of irreducible degree-$k$ characteristic polynomial $g$ with root $\xi \in \mathbb F_{q^k}^\times$ it takes the Frobenius-orbit sum $(-1)^{k-1}\sum_{j < k}\theta(\xi^{q^j})$ (generally nonzero even when $g$ differs from the label polynomial; see Example 13.42 in [§13.4.13](#13413-elliptic-character-formulas-and-determination-of-cuspidal-characters-on-regular-elliptic-elements)). In `Theorem 13` (pp. 441–442) and `§8` (`Lemma 8.3`, `Theorem 14`, pp. 443–444), Green constructs all irreducible characters of $\mathrm{GL}_n(\mathbb F_q)$ by forming parabolic "compound characters" $\chi_1 \circ \dots \circ \chi_h$ indexed by partition-valued functions $\nu(\mathfrak f)$ with $\sum_{\mathfrak f} k(\mathfrak f)\lvert\nu(\mathfrak f)\rvert = n$. Notice how `GreenSeries.green_series` (`ProdFactorsOfMonic.lean:243`) carves out the exact **squarefree generic slice** of Green's Theorem 14 where every $\nu(\mathfrak f)$ has size $0$ or $1$: when the cuspidal blocks $P_1, \dots, P_r$ are pairwise distinct (`f ∈ sqSet g N`), the parabolic compound character $\tau(P_1) \circ \dots \circ \tau(P_r) = \mathrm{hcL}(Q(f), N)$ is **already irreducible** without needing Green's $S$-function decomposition of repeated blocks, and requires only existence + degree and injectivity of cuspidal labels!
2. *Why `NameLaws` avoids `LabelDatum` (`[BushnellKutzko1993]`).* In Bushnell–Kutzko's classification of depth-zero supercuspidal representations of $\mathrm{GL}_n(E_w)$ (`[BushnellKutzko1993]`, Chs. 5–6), a maximal unramified elliptic torus $E'/E_w$ inside $\mathrm{GL}_n(E_w)$ embeds $\mathcal O_{E'}^\times / (1 + \mathfrak p_{E'}) \cong K^\times$ into $\mathrm{GL}_n(\mathbb F_g)$ only up to $\mathrm{GL}_n(\mathbb F_g)$-conjugacy and $\mathrm{Gal}(K/\mathbb F_g)$-automorphisms, and two models $D_1, D_2$ of the degree-$n$ unramified extension have canonically isomorphic residue fields only up to Frobenius twists. By phrasing `Names`, `Pin`, `NameLaws`, and `NameCentral` directly over an arbitrary degree-$n$ extension $K/\mathbb F_g$ without a chosen cyclic generator, `CentralUnit.parEx` (`CentralUnit.lean:188–189`) can compare $D_1$ and $D_2$ along any bare ring isomorphism $e : K_1 \xrightarrow{\sim} K_2$ (`RingHom.ext_zmod`) and absorb the ambiguity into a single $\mathrm{Gal}(K_1/\mathbb F_g)$-orbit via `hNtr` and `hNuniq`.
3. *Where $g \ge 5$ does — and does not — enter.* Neither `NameLaws` (Lemma 13.38 and Theorem 13.40(A)), nor `PM.greenCuspidal` (Lemma 13.39 and Theorem 13.40(B)), nor `GreenSeries.green_series`, nor `cuspParam_of_green`, nor the permutation construction `exists_perm_deg` / `exists_perm` uses any lower bound on the prime $g$: both the Parseval-plus-shift argument of `Pin` and the small-exponent Newton identity of `hasCuspLabel_unique` / `LabelUniqueAll.label_eq` hold for **every** prime $g \ge 2$ (including $g = 2, 3$). The hypothesis $5 \le g$ enters **only** at the last step `exists_labelO` (`AdmissibleLabelWeights…:210–231`) of `eSer_eq`, when assigning a unique Harish-Chandra series support multiset to an arbitrary irreducible constituent via `harishChandraSeriesLabel_exists_unique_GLn`.

**Table 13.4.12 (source-to-text map for §13.4.12; full file SHA-256s in `SOURCE-MAP.md`).**

| Reading / tag | Declaration(s) | Archive or Mathlib path and lines | Role in §13.4.12 |
|---|---|---|---|
| Definitions / `[Lean, read]` | `Names`, `Pin`, `NameLaws`, `NameCentral`; `LabelConv`, `HasCuspLabel`, `CuspParam`, `LabelMap`, `eSerO`; `GreenCuspidal`; `GreenSeriesSt` | `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/RecTTransport.lean:23–25, 99–124`; `src/Formalism/PadicSubsetSums/CentralIdempotents/IsConstituent.lean:135–214`; `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenCuspidalIff.lean:8–11`; `src/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/GreenSeriesSt.lean:7–9` | Definition 13.8 |
| R3 / `[Lean, read]` | `bd`, `bd_le`, `big`, `two_bd`, `one_bd`; `exists_gen_char`, `pow_of_deg`, `exists_D`, `cj`, `card_cj`, `sum_cj`, `disj_cj`; `norm_char`, `sum_mul_conj`, `dif`, `parseval`, `card_le`, `mul_mem`; `Reg`, `Cl`, `Pair`, `pairCheck_*`, `exc`, `main`, `UpperTheory.Zero.LLC.pin` | `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/PinNum.lean:7–253`; `…/PinFld.lean:9–194`; `…/PinChar.lean:10–133`; `…/PairCheckThreeTwo.lean:8–179` | Lemma 13.38 (Steps 1–3) |
| R3 / `[Lean, read]` | `schur_scalar`, `charpoly_lmul`, `natDegree_smul`, `UpperTheory.Zero.LLC.nameCentral` | `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/NameCentral.lean:15–108` | Lemma 13.38 (Step 4) |
| R3 / `[Lean, read]` | `exists_elt`, `pow_period`, `pow_mod`, `regular_pow`, `UpperTheory.Zero.LLC.nameLaws`; consumers `parEx` and `parUniq` | `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/NameLaws.lean:11–123`; `…/CentralUnit.lean:39–202`; `…/ParUniq.lean:15–53` | Theorem 13.40(A) |
| R3 / `[Lean, read]` | `regular_iff_degree`, `exists_root`, `exists_elliptic`, `reg_small_lemma_4`, `multiset_eq_of_psum_lemma_5`, `hasCuspLabel_unique`; `esymm_eq_of_psum_eq`, `natDegree_minpoly_gen_pow`, `LabelUniqueAll.label_eq` | `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean:118–406`; `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CuspidalLabelPolynomialUniqueAllPrimes.lean:17–159` | Lemma 13.39 |
| R3 / `[Lean, read]` | `PM.greenCuspidal`; `conv`, `res_eq_zero_iff`, `isCuspidal_of_isCusp`, `thetaOf_gen_pow`, `isCuspOf_character`, `hasCuspLabel_of_character`, `green`, `greenCuspidal`; `exists_label`, `iso_of_label`, `cuspParam_all`, `greenLab`; `exists_cuspidal_label`; `finrank_of_simple_cuspidal` | `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/HarishChandraModules.lean:12–13`; `src/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/GreenCuspLabels/GreenCuspidal.lean:12–304`; `src/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/LabelMapNonempty.lean:18–132`; `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCuspidalWithLabel.lean:57–135`; `…/CuspidalParametrization.lean:22–72` | Theorem 13.40(B) |
| R3 / `[Lean, read]` | Consumers `genericOfWh`, `whHcL`, `degHcL`, `labelsOfEq`, `GreenSeries.green_series`, `greenSeriesSt_of`; `datum`, `hasCuspLabel_iff`, `cuspParam_of_green`; `iso_of_char`, `exists_perm_deg`, `exists_perm`, `ext`, `exists_labelO`, `eSer_eq`; top literature wiring | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdFactorsOfMonic.lean:67–351`; `src/Development/WeilBound/CoreStatements/AbelianHeightsDuality/PublishedTheoremStatements/BridgesAut.lean:49–50`; `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CuspParamOfGreenParametrisation.lean:20–138`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AdmissibleLabelWeightsOfGreenCuspidalParametrisa.lean:33–250`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:397–402, 668, 728, 790` | Theorem 13.40(C) |
| Inherited `R3` | `PM.greenRegularCharacters`, `isCharacter_cuspidal_rootSum_regular`, `(I1)`–`(I2)`, `(I4)`–`(I9)`, `exponent_regular_of_natDegree_minpoly_generator_pow`, `exists_beta`, `labelChar`, virtual integral expansion | Sections 13.4.1 and 13.4.4–13.4.11 | Consumed by citation without re-proof |
| `[Lean]` (Mathlib, pin `0df444a`) | `Multiset.esymm`, `MvPolynomial.esymm`, `MvPolynomial.psum`; `MvPolynomial.mul_esymm_eq_sum`; `RingHom.ext_zmod` | `Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean:70, 195, 344`; `Mathlib/RingTheory/MvPolynomial/Symmetric/NewtonIdentities.lean:225`; `Mathlib/Data/ZMod/Basic.lean:1096` | Lemma 13.39 and Theorem 13.40(A) |
| R2 / `[Lean]` named interfaces (`(U2)` upgraded to `R3` in [§13.4.13](#13413-elliptic-character-formulas-and-determination-of-cuspidal-characters-on-regular-elliptic-elements), `(U1)` in [§13.4.14](#13414-converse-regular-label-existence-exists_regular)) | **(U1)** `CuspFormula.exists_regular` (read at `R3` in §13.4.14); **(U2)** `CuspGL.cuspElliptic_statement` (read at `R3` in §13.4.13); **(U3)** `isCuspidal_of_sum_char`, `harishChandra_induction_character_properties`; **(U4)** `zIdemOrthogonal_holds`; Mackey/Whittaker `ip_hcL_cusp`, `wh_cusp_eq_one`, `wh_hcT`, `hc_degree`; `harishChandraSeriesLabel_exists_unique_GLn` ($5 \le g$); remaining `LocalCentralUnits` $p$-adic type supplies | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLabel.lean:49`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrrCharEqOneOfSubsingleton.lean:45` (§13.4.13); statement wrappers in `GreenCuspidal.lean:146, 179`, `LabelMapNonempty.lean:105`, `ProdFactorsOfMonic.lean:44, 72, 128, 146`, `AdmissibleLabelWeights…:216` | Retained as named statement-level interfaces (`(U2)` discharged in §13.4.13, `(U1)` in §13.4.14) |
| Our check | `verify_green_label_laws.py`: 2,728 exact assertions covering all 29 archive files, `PinNum`/`PairCheckThreeTwo` bounds, and Examples 13.36–13.37 | Run certificate (`sources/SOURCES.md`) | Exact computational verification |

---

### 13.4.13 Elliptic character formulas and determination of cuspidal characters on regular elliptic elements

**Motivation.** In Section 13.4.12 (Theorem 13.40(B)), the representation-level parametrization `PM.greenCuspidal` rested on two character-theoretic interfaces on $\mathrm{GL}_d(F)$ that were retained at statement level (`R2 / [Lean]`): **(U1)** converse regular-orbit existence `GlobalTheory.CuspFormula.exists_regular` (`ExistsLabel.lean:49`), and **(U2)** elliptic character determination `GlobalTheory.CuspGL.cuspElliptic_statement` (`IrrCharEqOneOfSubsingleton.lean:45`). At first sight one might assume that **(U2)** simply quotes **(U1)**: if every cuspidal character is already known to be a signed single-orbit root sum $(-1)^{d-1}\sum_{i=0}^{d-1}\theta(z^{q^i})$, then two cuspidal characters agreeing on elliptic classes have identical orbit sums and hence coincide.

Reading the pinned production chain of `cuspElliptic_statement` reveals the **exact opposite dependency direction**: `cuspElliptic_statement` does **not** import or invoke `exists_regular` at all — instead, `ExistsLabel.lean:22` imports `EqOfIsPrimitiveOfEqOnEllipticFiniteGL` in reverse! Without knowing single-orbit concentration, how can the archive evaluate an arbitrary cuspidal character $\chi$ on elliptic conjugacy classes and prove that elliptic traces determine $\chi$ everywhere on $\mathrm{GL}_d(F)$ for **every** finite field $F$ ($q = \lvert F\rvert \ge 2$) and **every** rank $d \ge 0$?

The formal proof proceeds in four self-contained stages that expose two distinct tiers of the elliptic character formula:

1. *From standard unipotent blocks to endomorphism-ring primitivity (`isPrimitive_of_isCuspChar`, Lemma 13.43).* Matrix-level cuspidality `CuspElliptic.IsCuspChar` assumes only that $\chi$ vanishes when summed over each **standard** upper-right unipotent radical `unipBlock d a` ($0 < a < d$). Three elementary linear-algebra and representation-theory lemmas — the bijection $u \mapsto u - 1$ onto the subspace nilradical `nilRad(lowSub F d a)`, vanishing of the characteristic-zero averaging idempotent $P_H = \lvert H\rvert^{-1}\sum_{u \in H}\rho(u)$ from $\operatorname{tr}(P_H) = 0$, and invariance $\operatorname{charpoly}(g + h) = \operatorname{charpoly}(g)$ along $h \in \mathrm{nilRad}(A)$ (which keeps singular stabilizer maps non-invertible!) — upgrade subgroup vanishing to full nilradical vanishing `IsPrimitive (extZero χ)` across `Module.End F (Fin d → F)`.
2. *Integer Gram vectors and the degree-and-sign law (`exists_int_coeff_of_isPrimitive` and `sum_coef_mul_eq_pair`, Lemma 13.44).* Pairing `extZero χ` against the virtual root-power-sum functions $R_k$ (`(I6)`, §13.4.5) attaches a Frobenius-invariant integer vector $(a_k)_{0 \le k < q^d - 1} \in \mathbb Z^{q^d - 1}$ satisfying $\sum_{k=0}^{q^d-2} a_k b_k = d\,\langle \chi, \chi'\rangle_{\mathrm{GL}_d(F)}$ and, by evaluating at the identity via `(I2)` (§13.4.10),
   $$d\,\chi(1) = \left(\sum_{k=0}^{q^d-2} a_k\right)\prod_{i=1}^{d-1}\left(1 - q^i\right).$$
   Because $\chi(1) > 0$ and $\prod_{i=1}^{d-1}(1 - q^i)$ has sign $(-1)^{d-1}$, **every** cuspidal character's integer vector has total sum $\sum_{k=0}^{q^d-2} a_k$ strictly of sign $(-1)^{d-1}$.
3. *Two-tier elliptic character formula (`character_elliptic_eq_coeff_sum_lemma` vs. `exists_regular`, Theorem 13.46(A)).* On any elliptic element $x \in \mathrm{GL}_d(F)$ whose irreducible characteristic polynomial has root $\zeta^j$ ($\omega = \theta_0(\zeta)$ a primitive $(q^d - 1)$-st root of unity in $\mathbb C$), the invariant-subspace Möbius inverse $\psi_{s_k}(x)$ collapses to its top term $\sum_{i=0}^{d-1}\omega^{j q^i k}$, and Frobenius invariance $a_{k q^i \bmod (q^d-1)} = a_k$ folds the $d$ conjugates into the **unconditional-on-`exists_regular` discrete Fourier formula**
   $$\chi(x) = \sum_{k=0}^{q^d-2} a_k\,\omega^{j k}.$$
   When the named `R2 [Lean]` input `exists_regular` (`ExistsLabel.lean:49`) is adjoined, $a_k$ concentrates with value $(-1)^{d-1}$ on a single regular Frobenius orbit $\{k_0 q^i \bmod (q^d - 1) : 0 \le i < d\}$, turning the Fourier sum into Green's signed Galois-orbit formula $\chi(x) = (-1)^{d-1}\sum_{i=0}^{d-1}\theta(z^{q^i})$ and yielding the central-twist law $\chi(c x) = \theta(c)\,\chi(x)$ ($c \in F^\times$).
4. *Orthogonal integer separation modulo $q^d - 1$ (`orthogonal_int_vectors_not_agree_on_regular`, Lemma 13.45).* If two distinct cuspidal characters $\chi \neq \chi'$ agreed on all elliptic elements, their difference vector $c_k = a_k - b_k \in \mathbb Z$ would satisfy $\sum_{k=0}^{N-1} c_k^2 = 2d$ ($N = q^d - 1$), would have its zero-frequency sum compressed by the **same-sign law** $(\sum a_k)(\sum b_k) > 0$ to $\lvert\sum_{k=0}^{N-1} c_k\rvert \le d - 1$, and would have vanishing discrete Fourier transform on every regular residue $j \bmod N$. Parseval's identity refutes this immediately for **every** pair $(q, d)$ ($q \ge 2, d \ge 2$, **including** $(2, 2)$ and $(3, 2)$!) except $(2, 4)$ ($N = 15$) and $(2, 6)$ ($N = 63$), which are eliminated by Vandermonde annihilation and modulo-$63$ Fourier inversion.

Throughout this subsection we do **not** re-prove `nameLaws` (§13.4.12), Green virtuality `(I6)`/`(I7)` or virtual integral expansions (§§13.4.5, 13.4.7, 13.4.11), or positive-degree sign selection `(I8)` (§13.4.10), and we keep `GlobalTheory.CuspFormula.exists_regular` (`ExistsLabel.lean:49`) explicitly as a named `R2 [Lean]` input. Its production proof is read at `R3` in [§13.4.14](#13414-converse-regular-label-existence-exists_regular) (Theorem 13.54), which removes the hypothesis of Theorem 13.46(A2).

#### Worked examples

**Example 13.41 ($\mathrm{GL}_2(\mathbb F_2) \cong \mathfrak S_3$: genuine elliptic matrices, unipotent-block and nilradical vanishing, trivial central twist, and the sign $(-1)^{2-1} = -1$).** [Expository; verified in exact cyclotomic arithmetic over $\mathbb Q(\zeta_3)$ across all $16$ matrices of $M_2(\mathbb F_2)$ by `verify_elliptic_character.py`] Set $q = 2$, $d = 2$, and $N = 2^2 - 1 = 3$, so $\lvert M_2(\mathbb F_2)\rvert = 16$ and $\lvert\mathrm{GL}_2(\mathbb F_2)\rvert = (4 - 1)(4 - 2) = 6$.

1. *Explicit elliptic matrices and conjugacy class size.* Over $\mathbb F_2$, the unique monic irreducible quadratic is $P(X) = X^2 + X + 1$. Its companion matrix and inverse (equal to its Frobenius square in $\mathbb F_2[y] \cong \mathbb F_4$) are
   $$y = \begin{pmatrix} 0 & 1 \\ 1 & 1 \end{pmatrix}, \qquad y^2 = y^{-1} = \begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}, \qquad y^3 = I_2.$$
   The centralizer of $y$ inside $\mathrm{GL}_2(\mathbb F_2)$ is the embedded field torus $\mathbb F_2[y]^\times = \{I_2, y, y^2\} \cong \mathbb F_4^\times$ of order $2^2 - 1 = 3$, so the unique elliptic conjugacy class $C(y) = \{y, y^2\}$ has size $\lvert\mathrm{GL}_2(\mathbb F_2)\rvert / \lvert\mathbb F_4^\times\rvert = 6/3 = 2$. The remaining $4$ invertible matrices have split characteristic polynomial $X^2 + 1 = (X + 1)^2$ and form the central identity class $\{I_2\}$ (size $1$) and the unipotent involution class $C(u_0) = \left\{\begin{pmatrix}1&1\\0&1\end{pmatrix}, \begin{pmatrix}1&0\\1&1\end{pmatrix}, \begin{pmatrix}0&1\\1&0\end{pmatrix}\right\}$ (size $3$).
2. *Regular Frobenius orbit vs. the alternating character (and why $\det$ is not cuspidal here).* Realize $\mathbb F_4 = \mathbb F_2[\alpha]/(\alpha^2 + \alpha + 1)$ and fix $\theta_0(\alpha) = \omega_3 := e^{2\pi i/3}$ ($\omega_3^2 + \omega_3 + 1 = 0$). Modulo $N = 3$, the residue $k = 0$ is fixed by $\times 2 \bmod 3$ ($\deg_{\mathbb F_2}(\alpha^0) = 1$), whereas $k = 1, 2$ form a **single** regular Frobenius orbit $\{1, 2\} \bmod 3$, giving the pair of conjugate regular characters $\theta_1(\alpha) = \omega_3$ and $\theta_2(\alpha) = \theta_1(\alpha^2) = \omega_3^2$. Because $\mathbb F_2^\times = \{1\}$, every matrix in $\mathrm{GL}_2(\mathbb F_2)$ has determinant $1$, so $\det \equiv \mathbf 1$ is the trivial character! Instead, $\mathrm{GL}_2(\mathbb F_2)$ permutes the $3$ projective lines $\mathbb P^1(\mathbb F_2) = \{\langle(1,0)\rangle, \langle(0,1)\rangle, \langle(1,1)\rangle\}$ as $\mathfrak S_3$: its unique cuspidal irreducible character (of degree $q - 1 = 1$, noted by Green `[Green1955]`, §8 Remark 3, pp. 444–445 as $-I_2^1[1]$) is the **alternating sign character** $\epsilon$, taking $\epsilon(I_2) = +1$, $\epsilon(u_0) = -1$ on the $3$ transpositions, and $\epsilon(y) = \epsilon(y^2) = +1$ on the $2$ elliptic $3$-cycles.
3. *Unipotent-block vanishing (`Lemma 13.43`), integer Gram vector, central twist, and the sign $(-1)^{2-1} = -1$.*
   - At $a = 1$, `lowSub(F_2, 2, 1)` is the coordinate line $A = \mathbb F_2 e_0$, whose stabilizer $\mathrm{stab}(A)$ consists of the $8$ upper-triangular matrices in $M_2(\mathbb F_2)$. The standard unipotent radical `unipBlock 2 1` is $H = \{I_2, u_0\}$, mapped bijectively by $u \mapsto u - I_2$ onto $\mathrm{nilRad}(A) = \left\{\begin{pmatrix}0&0\\0&0\end{pmatrix}, \begin{pmatrix}0&1\\0&0\end{pmatrix}\right\}$. Since $\epsilon(I_2) + \epsilon(u_0) = 1 + (-1) = 0$, the $1 \times 1$ averaging idempotent is $P_H = \frac{1}{2}(1 + (-1)) = 0$, killing $\epsilon(g) + \epsilon(g u_0) = 0$ on the $2$ invertible elements $g \in \{I_2, u_0\} = \mathrm{stab}(A) \cap \mathrm{GL}_2(\mathbb F_2)$; on the $6$ singular upper-triangular matrices $g = \begin{pmatrix}d_1 & b \\ 0 & d_2\end{pmatrix}$ ($d_1 d_2 = 0$), `charpoly_block` gives $\operatorname{charpoly}(g + N) = X^2 - (d_1 + d_2)X$, so both $g$ and $g + \begin{pmatrix}0&1\\0&0\end{pmatrix}$ are singular and $\operatorname{extZero}\epsilon(g) + \operatorname{extZero}\epsilon(g + N) = 0 + 0 = 0$.
   - Pairing $\epsilon$ against $R_k$ ($k = 0, 1, 2$) over $\mathrm{GL}_2(\mathbb F_2)$ (where $(X + 1)^2$ has root sum $1 + 1 = 2$ and $X^2 + X + 1$ has root sum $\alpha^k + \alpha^{2k} \mapsto \omega_3^k + \omega_3^{2k}$) gives
     $$a_0 = \frac{1\cdot 2 + 3(-1)\cdot 2 + 2(1)\cdot 2}{6} = 0, \qquad a_1 = a_2 = \frac{1\cdot 2 + 3(-1)\cdot 2 + 2(1)(\omega_3 + \omega_3^2)}{6} = \frac{2 - 6 - 2}{6} = -1.$$
     Thus $a = (0, -1, -1) \in \mathbb Z^3$, satisfying $\sum_{k=0}^2 a_k^2 = 2 = d$ and the degree-and-sign law $d\,\epsilon(I_2) = 2 = (0 - 1 - 1)(1 - 2)$.
   - For $k_0 = 1$, the unsigned Möbius function $\psi_{s_1}$ takes $\psi_{s_1}(I_2) = 1 - 2 = -1$, $\psi_{s_1}(u_0) = 2 - 1 = +1$ ($u_0$ stabilizes the single $\mathbb F_2$-line $\mathbb F_2 e_0$ with eigenvalue $1$), and $\psi_{s_1}(y) = \omega_3 + \omega_3^2 = -1$. Multiplying by the root-sum sign $(-1)^{d-1} = (-1)^{2-1} = -1$ flips all three values to
     $$\epsilon(I_2) = +1, \qquad \epsilon(u_0) = -1, \qquad \epsilon(y) = (-1)^{2-1}\!\left(\theta_1(\alpha) + \theta_1(\alpha^2)\right) = -(\omega_3 + \omega_3^2) = +1 = \sum_{k=0}^2 a_k\,\omega_3^k.$$
   - The center $Z(\mathrm{GL}_2(\mathbb F_2)) = \{I_2\}$ is trivial, matching $\epsilon(1 \cdot x) = \theta_1(1)\epsilon(x) = 1 \cdot \epsilon(x)$, and the Parseval separation bound of Lemma 13.45 has strict slack $(d - 1)^2 + 4 d^2(2^1 - 2) = 1 < 12 = 2 \cdot 2 \cdot (2^2 - 1)$.

**Example 13.42 ($\mathrm{GL}_2(\mathbb F_3)$: three elliptic classes, explicit $2 \times 2$ matrix idempotent $P_U = 0$, central twist by $-I_2$, self-conjugate elliptic class $C(y_3)$, and sign $(-1)^{2-1} = -1$).** [Expository; verified in exact cyclotomic arithmetic over $\mathbb Q(\zeta_8)$ across all $81$ matrices of $M_2(\mathbb F_3)$ and $48$ matrices of $\mathrm{GL}_2(\mathbb F_3)$ by `verify_elliptic_character.py`] Set $q = 3$, $d = 2$, and $N = 3^2 - 1 = 8$, so $\lvert M_2(\mathbb F_3)\rvert = 81$, $\lvert\mathrm{GL}_2(\mathbb F_3)\rvert = (9 - 1)(9 - 3) = 48$, and the center is $Z = \{\pm I_2\} \cong \mathbb F_3^\times$. Realize $\mathbb F_9 = \mathbb F_3[\zeta]/(\zeta^2 + \zeta + 2)$ ($\zeta^2 = 2\zeta + 1$, multiplicative order $8$, with $\zeta^4 = 2 \equiv -1 \pmod 3$), and fix $\theta_0(\zeta) = \omega_8 := e^{2\pi i/8}$, so $\omega_8^2 = i$, $\omega_8^4 = -1$, and $\omega_8 + \omega_8^3 = i\sqrt{2}$.

1. *The three genuine elliptic conjugacy classes and the three regular Frobenius orbits.* Modulo $8$, multiplication by $q = 3$ fixes the $2$ non-regular residues $D = \{0, 4\}$ ($\mathbb F_3^\times = \{1, \zeta^4\} = \{1, -1\}$) and partitions the remaining $6$ residues into **three** regular orbits of size $2$:
   $$\{1, 3\} \longleftrightarrow P_1(X) = X^2 + X + 2, \qquad \{5, 7\} \longleftrightarrow P_2(X) = X^2 + 2X + 2, \qquad \{2, 6\} \longleftrightarrow P_3(X) = X^2 + 1.$$
   Taking the companion matrix $y_1$ of $P_1$ in the power basis $(1, \zeta)$ of $\mathbb F_9/\mathbb F_3$ yields explicit representatives for all three elliptic classes:
   $$y_1 = \begin{pmatrix} 0 & 1 \\ 1 & 2 \end{pmatrix}, \qquad y_2 = -y_1 = y_1^5 = \begin{pmatrix} 0 & 2 \\ 2 & 1 \end{pmatrix}, \qquad y_3 = y_1^2 = \begin{pmatrix} 1 & 2 \\ 2 & 2 \end{pmatrix}.$$
   Each $y_r$ has centralizer $\mathbb F_3[y_r]^\times = \mathbb F_3[y_1]^\times \cong \mathbb F_9^\times$ of order $8$, so each elliptic conjugacy class $C(y_r)$ has size $48/8 = 6$ ($18$ elliptic matrices in total; the $5$ non-elliptic classes are $\{I_2\}$ of size $1$, $\{-I_2\}$ of size $1$, unipotent $C(u_1)$ and $-C(u_1)$ with $u_1 = \begin{pmatrix}1&1\\0&1\end{pmatrix}$ of size $8$ each, and split regular semisimple $C(\operatorname{diag}(1, 2))$ of size $12$). Moreover, in the basis $(1, \zeta)$, the Frobenius involution $\mathrm{Frob}_3(\zeta) = \zeta^3 = 2 + 2\zeta$ is represented by $g = \begin{pmatrix}1 & 2 \\ 0 & 2\end{pmatrix} \in \mathrm{GL}_2(\mathbb F_3)$ ($g^2 = I_2$), which satisfies
   $$g\,y_1\,g^{-1} = y_1^3 \qquad \text{and} \qquad g\,y_3\,g^{-1} = y_1^6 = -y_3 = \begin{pmatrix} 2 & 1 \\ 1 & 1 \end{pmatrix}.$$
   Thus multiplication by the central element $-I_2$ **interchanges** $C(y_1) \leftrightarrow C(y_2)$ while mapping $C(y_3)$ **onto itself** ($-y_3 \sim y_3$).
2. *Explicit $2 \times 2$ cuspidal representations and $P_U = 0$ (`char_coset_sum_eq_zero`).* All three cuspidal irreducible representations of $\mathrm{GL}_2(\mathbb F_3)$ have degree $q - 1 = 2$ and can be realized explicitly over $\mathbb Q(\omega_8)$: sending the generators $u_1 = \begin{pmatrix}1&1\\0&1\end{pmatrix}$ and $s = \begin{pmatrix}0&2\\2&0\end{pmatrix}$ to $\rho_{P_1}(u_1) = \frac{1}{2}\begin{pmatrix}-1+i & 1+i \\ -1+i & -1-i\end{pmatrix}$ and $\rho_{P_1}(s) = \frac{i}{\sqrt{2}}\begin{pmatrix}i & 1 \\ -1 & -i\end{pmatrix}$ (with $s u_1 = \begin{pmatrix}0&2\\2&2\end{pmatrix} \in C(y_1)$ of trace $-i\sqrt{2}$) defines $\rho_{P_1}$, twisting by $\det : \mathrm{GL}_2(\mathbb F_3) \to \{\pm 1\}$ gives $\rho_{P_2} = \det \otimes \rho_{P_1}$, and letting $\mathrm{GL}_2(\mathbb F_3)$ permute the $3$ pairings of $\mathbb P^1(\mathbb F_3)$ via $\mathrm{PGL}_2(\mathbb F_3) \cong \mathfrak S_4 \twoheadrightarrow \mathfrak S_3$ defines $\rho_{P_3}$. On the standard unipotent radical $U = \{I_2, u_1, u_1^2\} = \mathrm{unipBlock}(2, 1)$, direct matrix addition gives $\rho_{P_r}(I_2) + \rho_{P_r}(u_1) + \rho_{P_r}(u_1^2) = \begin{pmatrix}0&0\\0&0\end{pmatrix}$, so the averaging idempotent $P_U = \frac{1}{3}\sum_{u \in U}\rho_{P_r}(u)$ vanishes identically as a $2 \times 2$ matrix, and every nilradical sum over $\mathrm{stab}(\mathrm{lowSub}(\mathbb F_3, 2, 1))$ ($27$ upper-triangular matrices: $12$ units and $15$ singular) equals $0$.
3. *Complete character values, central twists by $-I_2$, sign $(-1)^{2-1} = -1$, and integer Gram vectors.* Writing $\theta_k(\zeta^m) = \omega_8^{k m}$ for $k \in \{1, 5, 2\}$, the central scalar on $-I_2$ ($-1 = \zeta^4$) is $\theta_k(-1) = \omega_8^{4k} = (-1)^k$, giving $-1, -1, +1$ for $\tau_{P_1}, \tau_{P_2}, \tau_{P_3}$:

   | Cuspidal character | Orbit | $I_2$ ($1$) | $-I_2$ ($1$) | $u_1$ ($8$) | $-u_1$ ($8$) | $\operatorname{diag}(1,2)$ ($12$) | $y_1$ ($6$, $P_1$) | $y_2 = -y_1$ ($6$, $P_2$) | $y_3 = y_1^2$ ($6$, $P_3$) |
   |---|---|---:|---:|---:|---:|---:|---:|---:|---:|
   | $\tau_{P_1}$ | $\{1, 3\}$ | $2$ | $-2$ | $-1$ | $1$ | $0$ | $-i\sqrt{2}$ | $+i\sqrt{2}$ | $0$ |
   | $\tau_{P_2}$ | $\{5, 7\}$ | $2$ | $-2$ | $-1$ | $1$ | $0$ | $+i\sqrt{2}$ | $-i\sqrt{2}$ | $0$ |
   | $\tau_{P_3}$ | $\{2, 6\}$ | $2$ | $2$ | $-1$ | $-1$ | $0$ | $0$ | $0$ | $+2$ |

   Check every sign and central twist term by term:
   - *Sign $(-1)^{2-1} = -1$ at $I_2$ and on elliptic classes:* At $I_2$, the unsigned subspace Möbius value is $\psi_{s_k}(I_2) = 1 - 3 = -2$, negated by $(-1)^{2-1} = -1$ to $\tau_{P_r}(I_2) = +2$. On $y_1$ (roots $\zeta, \zeta^3$), the raw orbit sum of $\theta_1$ is $\omega_8 + \omega_8^3 = +i\sqrt{2}$, negated by $(-1)^{2-1} = -1$ to $\tau_{P_1}(y_1) = -i\sqrt{2}$; on $y_3$ (roots $\zeta^2, \zeta^6$), the raw orbit sum of $\theta_2$ is $\omega_8^4 + \omega_8^{12} = -1 + (-1) = -2$, negated by $(-1)^{2-1} = -1$ to $\tau_{P_3}(y_3) = +2$!
   - *Central twist $\tau_{P_r}(-x) = \theta_{k_r}(-1)\,\tau_{P_r}(x)$ and non-vanishing off the label class:* For $\tau_{P_1}$ ($k_1 = 1$, $\theta_1(-1) = -1$), $\tau_{P_1}(y_2) = \tau_{P_1}(-y_1) = -\tau_{P_1}(y_1) = +i\sqrt{2} = -(\omega_8^5 + \omega_8^7)$: in particular, $\tau_{P_1}$ is **nonzero** on the elliptic class $C(y_2)$ even though $\operatorname{charpoly}(y_2) = P_2 \neq P_1$! By contrast, on the self-conjugate elliptic class $C(y_3)$ ($-y_3 \sim y_3$), the central-twist law $\tau_{P_1}(-y_3) = -\tau_{P_1}(y_3)$ together with class invariance $\tau_{P_1}(-y_3) = \tau_{P_1}(y_3)$ **forces** $\tau_{P_1}(y_3) = 0$ (and likewise $\tau_{P_2}(y_3) = 0$), matching $-(\omega_8^2 + \omega_8^6) = -(i - i) = 0$. For $\tau_{P_3}$ ($k_3 = 2$, $\theta_2(-1) = +1$), $\tau_{P_3}(-x) = +\tau_{P_3}(x)$ on every conjugacy class, and $\tau_{P_3}(y_1) = \tau_{P_3}(y_2) = -(\omega_8^2 + \omega_8^6) = 0$.
   - *Integer Gram vectors and Parseval separation slack:* Pairing $\tau_{P_1}, \tau_{P_2}, \tau_{P_3}$ against $R_0, \dots, R_7$ over $\mathrm{GL}_2(\mathbb F_3)$ yields
     $$a^{(1)} = (0, -1, 0, -1, 0, 0, 0, 0), \quad a^{(2)} = (0, 0, 0, 0, 0, -1, 0, -1), \quad a^{(3)} = (0, 0, -1, 0, 0, 0, -1, 0),$$
     satisfying $\sum_{k=0}^7 a^{(r)}_k a^{(s)}_k = 2\,\delta_{rs}$, $d\,\tau_{P_r}(I_2) = 4 = (-2)(1 - 3)$ (all three vectors have negative sum $-2$), and for any pair $r \neq s$ the difference $c = a^{(r)} - a^{(s)}$ has $\sum_{k=0}^7 c_k^2 = 4 = 2d$ and $\sum_{k=0}^7 c_k = (-2) - (-2) = 0$ ($\lvert\sum c_k\rvert \le d - 1 = 1$). Consequently Lemma 13.45 separates all cuspidal characters of $\mathrm{GL}_2(\mathbb F_3)$ purely by the numerical Parseval inequality $(2 - 1)^2 + 4 \cdot 2^2 \cdot (3^1 - 2) = 17 < 32 = 2 \cdot 2 \cdot (3^2 - 1)$, without needing the extra shift check that `Pin` required at $(3, 2)$ in Example 13.37(4)!

---

#### Definitions

**Definition 13.9 (Matrix-level cuspidality predicates, low-index unipotent blocks, and `CuspElliptic.Statement`).** [Lean, read] Let $F$ be a finite field of cardinality $q = \lvert F\rvert \ge 2$ and let $d \in \mathbb N$.

1. *The `CuspElliptic` interface (`src/Formalism/UnipotentAdelicQuotients/CuspEllipticValues.lean:7–26`).* For a finite group $G$ and a function $\chi : G \to \mathbb C$:
   - `CuspElliptic.IsChar χ` (`:7–9`) asserts the existence of $n \in \mathbb N$ and a matrix group homomorphism $\rho : G \to^* \mathrm{GL}(\mathrm{Fin}\,n, \mathbb C)$ such that $\chi(g) = \operatorname{tr}(\rho(g))$ for all $g \in G$.
   - `CuspElliptic.IsIrrChar χ` (`:10–13`) means `CuspElliptic.IsChar χ` together with unit $L^2$-norm $\sum_{g \in G} \chi(g)\,\overline{\chi(g)} = \lvert G\rvert$.
   - For $G = \mathrm{GL}(\mathrm{Fin}\,d, F)$ and $a \in \mathbb N$, the **standard upper-right unipotent block** `CuspElliptic.unipBlock d a` (`:15–17`) is the subset
     $$\mathrm{unipBlock}(d, a) := \left\{u \in \mathrm{GL}_d(F) : \forall\,i, j \in \mathrm{Fin}\,d,\; u_{i j} = \delta_{i j} \;\lor\; (i < a \le j)\right\}.$$
   - `CuspElliptic.IsCuspChar χ` (`:18–20`) means `CuspElliptic.IsIrrChar χ` together with $\sum_{u \in \mathrm{unipBlock}(d, a)} \chi(u) = 0$ for every proper block size $0 < a < d$.
   - `CuspElliptic.Statement : Prop` (`:22–26`) asserts that for every finite field $F$, every $d \in \mathbb N$, and any $\chi, \chi' : \mathrm{GL}_d(F) \to \mathbb C$ satisfying `IsCuspChar χ` and `IsCuspChar χ'`, if $\chi(x) = \chi'(x)$ for every $x \in \mathrm{GL}_d(F)$ whose characteristic polynomial $\operatorname{charpoly}(x) \in F[X]$ is irreducible, then $\chi = \chi'$.
2. *Coordinate-subspace nilradicals (`ExistsStandardUnipotentRadicalBijOnNilradical.lean:11–15`).* Set $\mathrm{lowSub}(F, d, a) := \{v \in F^d : v_i = 0 \text{ for all } a \le i < d\}$ (the $F$-subspace spanned by the first $a$ standard basis vectors). Recall from Definition 13.3 (§13.4.4, `InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:17–20`) that for any submodule $A \le F^d$, $\mathrm{stab}(A) = \{g \in \operatorname{End}_F(F^d) : g(A) \subseteq A\}$, $\mathrm{nilRad}(A) = \{h \in \operatorname{End}_F(F^d) : \operatorname{im}(h) \subseteq A \text{ and } h\rvert_A = 0\}$, and `IsPrimitive f` means $\sum_{h \in \mathrm{nilRad}(A)} f(g + h) = 0$ for every proper subspace $0 < \dim_F A < d$ and every $g \in \mathrm{stab}(A)$.
3. *Exact alignment with §13.4.12's representation-level predicates (`IsConstituent.lean:148–192`, `CuspidalParametrization.lean:22–48`).* For a finite field $K$, a convention $C : \mathrm{LabelConv}\,K$, a representation $\tau : \mathrm{FDRep}\,\mathbb C\,(\mathrm{GL}(\mathrm{Fin}\,d, K))$, and $P \in K[X]$, recall that `HasCuspLabel C τ P` (`IsConstituent.lean:148–160`) records the polynomial conditions ($P$ monic irreducible of degree $d$ with $P \neq X$) and the elliptic trace identity $\chi_\tau(\gamma) = (-1)^{d-1}\sum_{i=0}^{d-1} C.\iota(x)^{m\,\lvert K\rvert^i}$ whenever $P(x) = 0$ and $\gamma \in \mathrm{GL}_d(K)$ has irreducible characteristic polynomial with root $z = C.\mathrm{gen}(d)^m$, while simplicity (`Simple τ`) and module-level cuspidality (`IsCuspidal K τ`) are passed as separate hypotheses into `CuspParam K C : Prop` (`:183–192`), `exists_label`, and `iso_of_label` (`LabelMapNonempty.lean:18, 83`), bridged to `CuspElliptic.IsCuspChar τ.character` by `isCuspChar_character` (`CuspidalParametrization.lean:22`).

---

#### Lemmas and conditional main theorem

**Lemma 13.43 (Elementary block-matrix and trace-zero idempotent lemmas: `isPrimitive_of_isCuspChar`).** [Lean, read] *Let $F$ be a finite field and $d \in \mathbb N$. Inheriting `extZero_spec` (`GeneralLinearFunctionExtendZeroEndProperties.lean:87`, §13.4.10):*

1. *(`exists_unip_bijOn_nilRad`, `ExistsStandardUnipotentRadicalBijOnNilradical.lean:62–159`.) For $a \le d$, $\dim_F \mathrm{lowSub}(F, d, a) = a$, $\mathrm{unipBlock}(d, a)$ is a subgroup $H \le \mathrm{GL}_d(F)$, and $u \mapsto \operatorname{toLin}'(u) - 1$ is a bijection from $H$ onto $\mathrm{nilRad}(\mathrm{lowSub}(F, d, a))$ with inverse $f \mapsto 1 + \operatorname{toMatrix}'(f)$.*
2. *(`char_coset_sum_eq_zero`, `CharacterCosetSumEqZeroOfSubgroupSum.lean:10–44`.) For any group $G$, genuine complex character $\chi : G \to \mathbb C$ (`BI.IsChar ℂ ℂ χ`), finite subgroup $H \le G$ with $\sum_{u \in H} \chi(u) = 0$, and $x \in G$, every left coset sum vanishes: $\sum_{u \in H} \chi(x u) = 0$.*
3. *(`charpoly_eq_restrict_mul_mapQ` and `charpoly_block`, `CharpolyBlockAndInvariantUnderStabilizerNilradic.lean:10–55`.) For any finite-dimensional $F$-vector space $V$, submodule $A \le V$, $g \in \mathrm{stab}(A)$, and $h \in \mathrm{nilRad}(A)$, we have $g + h \in \mathrm{stab}(A)$ and*
   $$\operatorname{charpoly}(g + h) = \operatorname{charpoly}\!\left(g\rvert_A\right)\cdot\operatorname{charpoly}\!\left(\bar g_{V/A}\right) = \operatorname{charpoly}(g).$$
4. *(`isPrimitive_extZero_of_sum_unipotent`, `IsPrimitiveExtendZeroOfSumUnipotentRadical.lean:12–100`, and `isPrimitive_of_isCuspChar`, `IrrCharEqOneOfSubsingleton.lean:34–43`.) Every $\chi : \mathrm{GL}_d(F) \to \mathbb C$ satisfying `CuspElliptic.IsCuspChar χ` has `IsPrimitive (extZero χ)`.*

*Proof.* **(1)** Projection onto the last $d - a$ coordinates $\{i \in \mathrm{Fin}\,d : a \le i\}$ is surjective with kernel $\mathrm{lowSub}(F, d, a)$, so rank-nullity gives $\dim_F \mathrm{lowSub}(F, d, a) = d - (d - a) = a$ (`finrank_lowSub_of_le`, `:62–71`). Evaluating on standard basis vectors $\mathrm{Pi.single}\,j\,1$ shows that $\operatorname{toLin}'(N) \in \mathrm{nilRad}(\mathrm{lowSub}(F, d, a))$ if and only if $N_{i j} = 0$ whenever $i \ge a$ or $j < a$, i.e. $N_{i j} = 0 \lor (i < a \le j)$ (`toLin'_mem_nilRad_lowSub_iff`, `:87–120`). Thus $u \in \mathrm{unip}(\mathrm{lowSub}(F, d, a)) \iff \operatorname{toLin}'(u) - 1 \in \mathrm{nilRad} \iff u \in \mathrm{unipBlock}(d, a)$ (`:130–139`), which is closed under $1$, multiplication $(u - 1)v + (v - 1)$, and inversion (`unip`, `:14–45`). Injectivity of $u \mapsto \operatorname{toLin}'(u) - 1$ follows from injectivity of $\operatorname{toLin}'$ and subtraction (`:140`); for surjectivity (`:141–158`), any $f \in \mathrm{nilRad}$ maps $F^d$ into $\mathrm{lowSub}$ and vanishes on $\mathrm{lowSub}$, so its matrix $N = \operatorname{toMatrix}'(f)$ satisfies $N^2 = 0$, giving $(1 + N)(1 - N) = (1 - N)(1 + N) = 1$, i.e. $u := \langle 1 + N, 1 - N\rangle \in H$ with $\operatorname{toLin}'(u) - 1 = f$.

**(2)** Unpack a witness representation $\rho : G \to^* \operatorname{End}_{\mathbb C}(\mathbb C^n)$ with $\chi(g) = \operatorname{tr}(\rho(g))$, and form the group-algebra average $P_H := \lvert H\rvert^{-1}\sum_{u \in H} \rho(u) \in \operatorname{End}_{\mathbb C}(\mathbb C^n)$ (`:16`). Reindexing $v \mapsto u^{-1}v$ for each $u \in H$ gives $\sum_{v \in H} \rho(u)\rho(v) = \sum_{v \in H}\rho(v)$, whence $P_H^2 = \lvert H\rvert^{-1}\sum_{u \in H}\lvert H\rvert^{-1}\sum_{v \in H}\rho(u v) = P_H$, i.e. `IsIdempotentElem P_H` (`:17–32`). By linearity of trace, $\operatorname{tr}(P_H) = \lvert H\rvert^{-1}\sum_{u \in H}\chi(u) = 0$ (`:33–36`). Over a characteristic-zero field, an idempotent endomorphism of a free finite-rank module has trace equal to the rank of its image, so Mathlib's `IsIdempotentElem.trace_eq_zero_iff` (`Mathlib/LinearAlgebra/Trace.lean:340`) forces $P_H = 0$ (`:36`)! Multiplying on the left by $\rho(x)$ and taking traces yields $\sum_{u \in H}\chi(x u) = \operatorname{tr}\!\left(\rho(x)\sum_{u \in H}\rho(u)\right) = \operatorname{tr}(\rho(x)\cdot \lvert H\rvert P_H) = 0$ (`:37–44`).

**(3)** Choose an $F$-basis $b_A$ of $A$ and lift an $F$-basis $b_Q$ of $V/A$ along a linear section of $V \twoheadrightarrow V/A$ to build a direct-sum basis $b$ of $V$ (`charpoly_eq_restrict_mul_mapQ`, `:14–21`). Because $g(A) \subseteq A$, the matrix of $g$ in $b$ is block upper-triangular $\begin{pmatrix}M_{11} & M_{12} \\ 0 & M_{22}\end{pmatrix}$ with $M_{11} = [g\rvert_A]_{b_A}$ and $M_{22} = [\bar g_{V/A}]_{b_Q}$ (`:22–31`), so `Matrix.charpoly_fromBlocks_zero₂₁` (`Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean:187`) gives $\operatorname{charpoly}(g) = \operatorname{charpoly}(g\rvert_A)\operatorname{charpoly}(\bar g_{V/A})$ (`:32–34`). Now let $h \in \mathrm{nilRad}(A)$ (`charpoly_block`, `:36–55`): since $h(V) \subseteq A$, $g + h \in \mathrm{stab}(A)$; since $h\rvert_A = 0$, $(g + h)\rvert_A = g\rvert_A$; and since $h(V) \subseteq A = \ker(V \twoheadrightarrow V/A)$, $\overline{g + h}_{V/A} = \bar g_{V/A}$. Applying the block formula to both $g + h$ and $g$ gives $\operatorname{charpoly}(g + h) = \operatorname{charpoly}(g)$.

**(4)** Given `CuspElliptic.IsCuspChar χ`, converting matrix traces via `matrixChar_iff_isChar` (`MatrixTraceIffIsCharacterOverSubfieldComplex.lean:7`, choosing a basis of $\mathbb C^n$) gives `BI.IsChar ℂ ℂ χ` (`IrrCharEqOneOfSubsingleton.lean:36`). Let $B \le F^d$ be any subspace with $0 < a := \dim_F B < d$, and let $A := \mathrm{lowSub}(F, d, a)$ and $H := \mathrm{unipBlock}(d, a)$ from (1). First check $\sum_{h \in \mathrm{nilRad}(A)} \operatorname{extZero}\chi(g + h) = 0$ for every $g \in \mathrm{stab}(A)$ (`finsum_nilRad_extZero_eq_zero`, `IsPrimitiveExtendZeroOfSumUnipotentRadical.lean:33–70`), unpacking **Clauses 1, 2, and 3** of `extZero_spec`:
- *Case 1 ($g$ is a unit in $\operatorname{End}_F(F^d)$, `:45–54`):* By Clause 3 of `extZero_spec`, $g = \operatorname{toLin}'(x)$ for some $x \in \mathrm{GL}_d(F)$. Since left multiplication by $x$ is a bijection on $\mathrm{nilRad}(A)$ (`x⁻¹ h ∈ nilRad A` because $h(F^d) \subseteq A$ and $g(A) = A \implies x^{-1}(A) \subseteq A$), composing with the bijection $u \mapsto \operatorname{toLin}'(u) - 1$ of (1) reindexes $h = \operatorname{toLin}'(x)(\operatorname{toLin}'(u) - 1) = \operatorname{toLin}'(x u) - g$ over $u \in H$. Clause 1 of `extZero_spec` rewrites $\operatorname{extZero}\chi(\operatorname{toLin}'(x u)) = \chi(x u)$, and (2) gives $\sum_{u \in H}\chi(x u) = 0$.
- *Case 2 ($g$ is **not** a unit in $\operatorname{End}_F(F^d)$, `:55–70`):* On finite-dimensional $F^d$, non-invertibility of $g$ means $\ker(g) \neq 0$, so $0$ is an eigenvalue and $\operatorname{eval}_0(\operatorname{charpoly}(g)) = 0$. For **every** $h \in \mathrm{nilRad}(A)$, (3) gives $\operatorname{charpoly}(g + h) = \operatorname{charpoly}(g)$, so $\operatorname{eval}_0(\operatorname{charpoly}(g + h)) = 0$ and $g + h$ is also non-invertible! Clause 2 of `extZero_spec` therefore gives $\operatorname{extZero}\chi(g + h) = 0$ **term by term**, so the sum is $0$.

Finally, because $\dim_F B = a = \dim_F A$, extending bases of $B$ and $A$ to bases of $F^d$ produces $e \in \mathrm{GL}(F^d)$ mapping $A$ onto $B$ (`exists_linearEquiv_mem_iff_of_finrank_eq`, `:12–31`). Conjugation $f \mapsto e^{-1} f e$ maps $\mathrm{stab}(B)$ into $\mathrm{stab}(A)$ and bijects $\mathrm{nilRad}(B)$ onto $\mathrm{nilRad}(A)$, while **Clause 4** of `extZero_spec` (conjugation invariance of `extZero χ`, since $\chi$ is a class function) identifies $\operatorname{extZero}\chi(g_B + h_B) = \operatorname{extZero}\chi(e^{-1}g_B e + e^{-1}h_B e)$, reducing $B$ to $A$ (`:83–100`). $\square$

**Lemma 13.44 (Regular-root characterization, integer Gram vectors, and the degree-and-sign and inner-product laws).** [Lean, read] *Let $F$ be a finite field of cardinality $q = \lvert F\rvert \ge 2$ and let $d \ge 1$.*

1. *(`regular_iff_natDegree_and_exists_elliptic`, `RegularIffNatDegreeAndExistsEllipticGL.lean:8–85`.) Let $z \in \bar F$ satisfy $z^{q^d - 1} = 1$. Then $(\forall\,1 \le e < d,\;z^{q^e} \neq z)$ holds if and only if $\deg\operatorname{minpoly}_F(z) = d$; under this condition, there exists $x \in \mathrm{GL}_d(F)$ with $\operatorname{charpoly}(x) = \operatorname{minpoly}_F(z)$.*
2. *(`finsum_mul_star_virt_int` and `exists_int_coeff_of_isPrimitive`, `VirtualCharacterInnerEqIntMulCard.lean:11–40`, `FiniteGroupFunctionPairingAddNatPosSymm.lean:7–54`, `ExistsIntCoeffPrimitiveGLCharacter.lean:17–67`.) Assume `(I2)` (§13.4.10), `(I5)` (§13.4.6), and `(I6)` (§13.4.5), and fix an injective multiplicative lift $\theta_0 : \bar F^\times \hookrightarrow \mathbb C^\times$ (extended by $\theta_0(0) = 0$). For every genuine character $\chi : \mathrm{GL}_d(F) \to \mathbb C$ with `IsPrimitive (extZero χ)`, there exists a sequence $a : \mathbb N \to \mathbb Z$ such that $\mathrm{ipGL}(\mathrm{extZero}\,\chi, R_k) = a_k\,\lvert\mathrm{GL}_d(F)\rvert$ for all $k \in \mathbb N$ and*
   $$d\,\chi(1) = \left(\sum_{k=0}^{q^d-2} a_k\right) \prod_{i=1}^{d-1}\left(1 - q^i\right).$$
3. *(`sum_coef_mul_eq_pair` and `torus_orthogonality`, `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:33–100`, `FrobeniusTorusCharacterOrthogonality.lean:9–92`.) Assuming in addition `(I4)` (§13.4.6) and `(I8)` (`star_virt_eq_inv`, §13.4.10), if $\chi, \chi' : \mathrm{GL}_d(F) \to \mathbb C$ are genuine characters with `IsPrimitive (extZero χ)` and `IsPrimitive (extZero χ')` and integer sequences $a, b : \mathbb N \to \mathbb Z$ as in (2), then*
   $$\sum_{k=0}^{q^d-2} a_k\,b_k = d\,\langle \chi, \chi'\rangle_{\mathrm{GL}_d(F)} := \frac{d}{\lvert\mathrm{GL}_d(F)\rvert}\sum_{x \in \mathrm{GL}_d(F)} \chi(x)\,\overline{\chi'(x)}.$$

*Proof.* **(1)** Fix an algebraic closure $\bar F$; for any $e \ge 1$, the roots of $X^{q^e} - X$ in $\bar F$ form the unique subfield $E_e := \mathrm{GaloisField}(p, f e)$ of cardinality $q^e$ ($q = p^f$), which is an $F$-extension of degree $e$ (`pow_card_pow_eq_iff_natDegree_minpoly_dvd`, `:12–23`). If $z^{q^e} = z$, $F(z)$ embeds as an $F$-subalgebra into $E_e$, so $\deg\operatorname{minpoly}_F(z) = [F(z) : F]$ divides $[E_e : F] = e$ (`:24–29`); conversely, if $m := \deg\operatorname{minpoly}_F(z)$ divides $e$, then $z \in F(z)$ satisfies $z^{q^m - 1} = 1$ ($z \neq 0$ since $z^{q^d - 1} = 1$), hence $(q^m - 1) \mid (q^e - 1)$ gives $z^{q^e} = z$ (`:30–37`). Applying this at $e = d$ to $z^{q^d} = z$ shows $m \mid d$, so $m = d$ is equivalent to $m \nmid e$ for all $1 \le e < d$, i.e. $z^{q^e} \neq z$ for all $1 \le e < d$ (`:65–79`). When $m = d$, `PowerBasis.equivOfMinpoly` identifies $F[z] \cong F^d$ and transports left multiplication by $z \in F[z]^\times$ to $x \in \mathrm{GL}_d(F)$ whose characteristic polynomial equals $\operatorname{charpoly}_{F[z]/F}(z) = \operatorname{minpoly}_F(z)$ by `Algebra.charpoly_leftMulMatrix` (`Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean:75`; `exists_GL_charpoly_eq_minpoly`, `:39–60`).

**(2)** For any two genuine characters $\alpha, \beta$ on a finite group $G$, `character_pairing_eq_finrank_hom` (`FiniteGroupFunctionPairingAddNatPosSymm.lean:7–20`, via Mathlib's `FDRep.scalar_product_char_eq_finrank_equivariant` and `star_virt_eq_inv`) equates $\sum_{g \in G} \alpha(g)\,\overline{\beta(g)} = \dim_{\mathbb C}\operatorname{Hom}_G(V_\beta, V_\alpha) \cdot \lvert G\rvert \in \mathbb N \cdot \lvert G\rvert$. Writing any two virtual characters $u, v \in \mathrm{Virt}(\mathbb C, \mathbb C, G)$ as differences $u = \alpha_1 - \alpha_2$, $v = \beta_1 - \beta_2$ (`mem_virt_iff_sub`, §13.4.11) expands $\sum_{g \in G} u(g)\,\overline{v(g)}$ into four natural multiples of $\lvert G\rvert$, giving an integer multiple $m\,\lvert G\rvert$ (`finsum_mul_star_virt_int`, `VirtualCharacterInnerEqIntMulCard.lean:23–40`). Specializing to $G = \mathrm{GL}_d(F)$, $u = \chi$, and $v(x) = R_k(\operatorname{charpoly}(x))$ — which lies in $\mathrm{Virt}(\mathbb C, \mathbb C, \mathrm{GL}_d(F))$ by `(I6)` (`rootPowerSum_charpoly_mem_virtualCharacters_GL`, §13.4.5) — and rewriting the $\mathrm{GL}_d(F)$-sum as `ipGL (extZero χ) R_k` via `extZero_spec` Clause 3 produces $a_k \in \mathbb Z$ with $\mathrm{ipGL}(\mathrm{extZero}\,\chi, R_k) = a_k\,\lvert G\rvert$ (`ExistsIntCoeffPrimitiveGLCharacter.lean:28–37`). Substituting this into the primitive expansion `(I5b)` (`expand_primitive`, §13.4.6) at the identity endomorphism $1 \in \operatorname{End}_F(F^d)$,
$$\lvert G\rvert\,d\,\chi(1) = \sum_{k=0}^{q^d-2} \left(a_k\,\lvert G\rvert\right)\psi_{s_k}(1),$$
rewriting $\psi_{s_k}(1) = \prod_{i=1}^{d-1}(1 - q^i)$ for every $k$ by `(I2)` (`psi_one`, §13.4.10), and canceling $\lvert G\rvert \neq 0$ gives the degree-and-sign identity (`:41–67`).

**(3)** Set $N := q^d - 1$. Expanding both `extZero χ` and `extZero χ'` via `(I5b)` inside $\lvert G\rvert\,d^2\,\mathrm{ipGL}(\mathrm{extZero}\,\chi, \mathrm{extZero}\,\chi')$ and substituting $\mathrm{ipGL}(\mathrm{extZero}\,\chi, R_k) = a_k\lvert G\rvert$ and $\mathrm{ipGL}(\mathrm{extZero}\,\chi', R_\ell) = b_\ell\lvert G\rvert$ yields a double sum of $a_k b_\ell\,\mathrm{ipGL}(\psi_{s_k}, \psi_{s_\ell})$ (`EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:51–68`). By the Gram identity `(I4)` (`invertibleEndomorphism_innerProduct_primitive_mobiusInverse`, §13.4.6) combined with character orthogonality on the cyclic torus of order $N$ (`torus_orthogonality`, `FrobeniusTorusCharacterOrthogonality.lean:66–92`),
$$\mathrm{ipGL}\!\left(\psi_{s_k}, \psi_{s_\ell}\right) = \lvert G\rvert \sum_{j=0}^{d-1} \mathbf 1_{\,k \equiv \ell q^j \pmod N}.$$
Meanwhile, `(I5)` (`ipGL_rootSum_eq_of_modEq`, §13.4.6) gives $b_{\ell q^j \bmod N} = b_\ell$; thus for each $0 \le k < N$ and each $0 \le j < d$, multiplication by $q^j$ modulo $N$ (coprime to $N$) hits a unique $\ell \in \{0, \dots, N-1\}$ with $\ell q^j \equiv k \pmod N$, contributing $b_\ell = b_k$ (`:69–91`). Summing the $d$ identical copies of $\sum_{k=0}^{N-1} a_k b_k$ and canceling $\lvert G\rvert^2 d \neq 0$ leaves $\sum_{k=0}^{N-1} a_k b_k = d\,\langle \chi, \chi'\rangle_G$ (`:92–100`). $\square$

**Lemma 13.45 (Parseval separation of orthogonal same-sign integer vectors and finite-Fourier elimination of $(2, 4)$ and $(2, 6)$).** [Lean, read] *(`orthogonal_int_vectors_not_agree_on_regular`, `OrthogonalIntVectorsNotAgreeOnRegular.lean:21–61`.) Let $q \ge 2$ and $d \ge 1$ be integers, set $N := q^d - 1$, and let $\omega \in \mathbb C$ be a primitive $N$-th root of unity. There do **not** exist integer sequences $a, b : \mathbb N \to \mathbb Z$ satisfying simultaneously:*
$$\sum_{k=0}^{N-1} a_k^2 = d, \qquad \sum_{k=0}^{N-1} b_k^2 = d, \qquad \sum_{k=0}^{N-1} a_k b_k = 0, \qquad \left(\sum_{k=0}^{N-1} a_k\right)\!\left(\sum_{k=0}^{N-1} b_k\right) > 0,$$
*and $\sum_{k=0}^{N-1} a_k \omega^{j k} = \sum_{k=0}^{N-1} b_k \omega^{j k}$ for every regular residue $0 \le j < N$ ($\forall\,1 \le e < d,\; N \nmid j(q^e - 1)$).*

*Proof.* Assume such $a, b$ exist and set $c_k := a_k - b_k \in \mathbb Z$ and $\widehat c(j) := \sum_{k=0}^{N-1} c_k \omega^{j k}$. Expanding $\sum_{k=0}^{N-1} (a_k - b_k)^2 = d - 0 + d$ gives $\sum_{k=0}^{N-1} c_k^2 = 2d$ (`:27–31`). Because $\lvert z\rvert \le z^2$ for every $z \in \mathbb Z$, we have $\lvert\sum_{k=0}^{N-1} a_k\rvert \le \sum_{k=0}^{N-1} a_k^2 = d$ and $\lvert\sum_{k=0}^{N-1} b_k\rvert \le d$ (`abs_sum_le_sum_sq_int`, `:13–19`). Since the two integer sums $S_a := \sum_{k < N} a_k$ and $S_b := \sum_{k < N} b_k$ have **strictly positive product** $S_a S_b > 0$, they are nonzero integers of the **same sign** satisfying $1 \le \lvert S_a\rvert, \lvert S_b\rvert \le d$; subtracting two integers in $[1, d]$ (or in $[-d, -1]$) gives (`:32–38`)
$$\left\lvert\sum_{k=0}^{N-1} c_k\right\rvert = \lvert S_a - S_b\rvert \le d - 1.$$
If $d = 1$, every residue $0 \le j < N$ is vacuously regular ($\neg\,\exists\,e,\,1 \le e < 1$), so $\widehat c(j) = 0$ for all $0 \le j < N$ and Parseval below gives $2(q - 1) = 0$, contradicting $q \ge 2$ (`:56–60`). Assume $d \ge 2$.

*Step 1: Discrete Parseval bound on the non-regular locus (`parsevalSep_bound`, `ParsevalBoundIntegerVectorSmallFourierSupport.lean:8–112`; `card_nonregular_residues_le`, `CardNonregularResiduesModPowSubOneLe.lean:8–64`).* Orthogonality $\sum_{j=0}^{N-1} \omega^{j(k - \ell)} = N\,\delta_{k, \ell}$ (`parsevalSep_orth`, `:8–33`) gives the exact Parseval identity (`parsevalSep_identity`, `:35–58`):
$$\sum_{j=0}^{N-1} \lvert\widehat c(j)\rvert^2 = N \sum_{k=0}^{N-1} c_k^2 = 2 d N.$$
By hypothesis, $\widehat c(j) = 0$ unless $j = 0$ or $j \in B := \{1 \le j < N : \exists\,1 \le e < d,\; N \mid j(q^e - 1)\}$. At $j = 0$, $\lvert\widehat c(0)\rvert^2 = \lvert\sum_{k < N} c_k\rvert^2 \le (d - 1)^2$. At any $j \in B$, since $\lvert c_k\rvert \le c_k^2$ for $c_k \in \mathbb Z$, the triangle inequality gives $\lvert\widehat c(j)\rvert \le \sum_{k < N}\lvert c_k\rvert \le \sum_{k < N} c_k^2 = 2d$, so $\lvert\widehat c(j)\rvert^2 \le 4 d^2$ (`:78–104`). Meanwhile, if $N \mid j(q^e - 1)$ with $1 \le e < d$, setting $g_0 := \gcd(e, d) < d$ and picking a prime $p \mid (d/g_0)$ gives $N \mid j(q^{d/p} - 1)$, i.e. $j$ is one of the $(q^{d/p} - 2)$ nonzero multiples of $N/(q^{d/p} - 1)$ in $\{1, \dots, N - 1\}$ (`CardNonregularResiduesModPowSubOneLe.lean:15–56`). Union-bounding over prime divisors of $d$ gives $\lvert B\rvert \le \sum_{p \mid d}(q^{d/p} - 2)$ (`:57–64`) and hence
$$2 d\left(q^d - 1\right) \le (d - 1)^2 + 4 d^2 \sum_{p \in \mathrm{primeFactors}(d)} \left(q^{d/p} - 2\right).$$

*Step 2: Numerical elimination of all $(q, d) \notin \{(2, 4), (2, 6)\}$ (`sep_numerical_ineq`, `SeparationNumericalIneqCuspidalGL.lean:8–117`).* For prime $d$, $\mathrm{primeFactors}(d) = \{d\}$ and $(d - 1)^2 + 4 d^2(q - 2) < 2 d(q^d - 1)$ holds for all $q \ge 2$ and primes $d \ge 2$ (`:73–86`; e.g. at $(2, 2)$ we get $1 < 12$, and at $(3, 2)$ we get $17 < 32$). For composite $d = 2 k \ge 8$ (or odd composite $d \ge 9$), bounding $\sum_{p \mid d}(q^{d/p} - 2) < q^{\lfloor d/2\rfloor} + \lfloor d/2\rfloor q^{\lfloor d/2\rfloor - 1}$ (`sepIneq_sum_lt`, `:13–32`) against $q^d \ge 2^{\lceil d/2\rceil} q^{\lfloor d/2\rfloor}$ (`sepIneq_large`, `:34–60`) refutes the inequality; for $d = 4$ ($9 + 16(q^2 - 2) < 8(q^4 - 1)$ for $q \ge 3$) and $d = 6$ ($25 + 144(q^3 + q^2 - 4) < 12(q^6 - 1)$ for $q \ge 3$), direct algebra leaves **only** $(q, d) = (2, 4)$ ($137 \ge 120$) and $(q, d) = (2, 6)$ ($1177 \ge 756$) (`:87–117`).

*Step 3: Elimination of $(q, d) = (2, 4)$, $N = 15$ (`no_norm_eight_of_fourier_vanishing_order_fifteen`, `NoNormEightOfFourierVanishingOrderFifteen.lean:8–58`).* Here $\sum_{k=0}^{14} c_k^2 = 8$, and every $j \in \{0, \dots, 14\}$ not divisible by $5$ is regular ($15 \nmid j(2^2 - 1) = 3j$). When $5 \mid j$, $\omega^{3j} = (\omega^{15})^{j/5} = 1$; hence $(\omega^{3j} - 1)\widehat c(j) = 0$ for **every** $0 \le j < 15$ (`:18–26`). Reindexing $(\omega^{3j} - 1)\sum_{k=0}^{14} c_k \omega^{j k} = \sum_{k=0}^{14} (c_{(k+12)\bmod 15} - c_k)(\omega^j)^k = 0$ across the $15$ pairwise distinct evaluation points $1, \omega, \dots, \omega^{14}$ and invoking Mathlib's Vandermonde annihilation theorem `Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero` (`Mathlib/LinearAlgebra/Vandermonde.lean:248`) forces $c_{(k+12)\bmod 15} = c_k$, i.e. $c$ has period $3$ (`:27–49`). Summing over the five period-$3$ blocks gives $8 = \sum_{k=0}^{14} c_k^2 = 5(c_0^2 + c_1^2 + c_2^2)$, impossible in $\mathbb Z$ (`:50–58`).

*Step 4: Elimination of $(q, d) = (2, 6)$, $N = 63$ (`no_norm_twelve_order_sixtythree`, `NoNormTwelveOrderSixtythree.lean:8–218`).* Here $\sum_{k=0}^{62} c_k^2 = 12$, and $\widehat c(j) = 0$ whenever $21 \nmid j$ and $9 \nmid j$ (since $2^3 - 1 = 7$ and $2^2 - 1 = 3$). By discrete Fourier inversion $\frac{1}{63}\sum_{j=0}^{62}\omega^{-j m}\widehat c(j) = c_m$ (`fourier_inv_sixtythree`, `:22–45`):
- Since $(\omega^{-21 j} - 1)\widehat c(j)$ vanishes on multiples of $3$ (and every $j$ with $21 \mid j$ or $9 \mid j$ is a multiple of $3$!), $c_{n + 21} = c_n$ for all $n < 42$ (`apply_add_21_eq_of_fourier_vanish_order_63`, `:87–105`), reducing $12 = 3\sum_{k=0}^{20} c_k^2 \implies \sum_{k=0}^{20} c_k^2 = 4$ (`:126–136, 170–171`).
- Since $(\omega^{-7 j} - 1)(\omega^{-3 j} - 1)\widehat c(j)$ vanishes both when $9 \mid j$ ($\omega^{-63(j/9)} = 1$) and when $21 \mid j$ ($\omega^{-63(j/21)} = 1$), expanding the four shifts yields $c_{m+10} - c_{m+3} - c_{m+7} + c_m = 0$ (`mixed_diff_sixtythree`, `:47–85`), so $c_{m+7} - c_m$ depends **only on $m \bmod 3$** (`hD`, `:114–125`).
Write $(x, y, z) := (c_7 - c_0, c_8 - c_1, c_9 - c_2)$; by period $21$, $x + y + z = (c_7 - c_0) + (c_{14} - c_7) + (c_{21} - c_{14}) = 0$ (`:178–183`). For each $0 \le b < 7$, as $m$ runs over $\{b, b + 7, b + 14\}$, $m \bmod 3$ permutes $\{0, 1, 2\}$, so
$$x^2 + y^2 + z^2 = (c_{b+7} - c_b)^2 + (c_{b+14} - c_{b+7})^2 + (c_b - c_{b+14})^2 \le 3\left(c_b^2 + c_{b+7}^2 + c_{b+14}^2\right)$$
by $(c_b + c_{b+7} + c_{b+14})^2 \ge 0$ (`hcol`, `:146–169`). Summing over $0 \le b < 7$ gives $7(x^2 + y^2 + z^2) \le 3\sum_{k=0}^{20} c_k^2 = 12$; substituting $z = -x - y$ gives $14(x^2 + x y + y^2) \le 12$ (`:172–190`). Because $4(x^2 + x y + y^2) = (2x + y)^2 + 3 y^2 \ge 0$ for $x, y \in \mathbb Z$, this forces $x = y = z = 0$, so $c_{b+7} = c_b$ everywhere and $4 = \sum_{k=0}^{20} c_k^2 = 3\sum_{b=0}^6 c_b^2$, impossible in $\mathbb Z$ (`:191–218`). $\square$

**Theorem 13.46 (Accurately conditioned elliptic character formulas, `cuspElliptic_statement`, and payment to §13.4.12's representation-level consumers).** [Lean, read] *Let $F$ be a finite field of cardinality $q = \lvert F\rvert \ge 2$, inheriting `(I1)` (§13.4.9), `(I2)` (§13.4.10), `(I3b)` (§13.4.4), `(I4)`–`(I6)` (§§13.4.5–13.4.6), `(I8)` (`irr_of_norm_one`, `star_virt_eq_inv`, `extZero_spec`, §13.4.10), virtual integral expansions (§13.4.11), and Mathlib's finite-group Schur/orthonormality interfaces (`[Lean]`).*

- **(A) Two-tier elliptic character formula on $\mathrm{GL}_d(F)$ ($d \ge 1$).** *Fix an injective multiplicative lift $\theta_0 : \bar F^\times \hookrightarrow \mathbb C^\times$ and a primitive $(q^d - 1)$-st root of unity $\zeta \in \bar F^\times$ with $\omega := \theta_0(\zeta)$, and let $\chi : \mathrm{GL}_d(F) \to \mathbb C$ satisfy `CuspElliptic.IsCuspChar χ`:*
  1. **Direct Frobenius-invariant Fourier formula (without `exists_regular`; `character_elliptic_eq_coeff_sum_lemma`, `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:127–210`).** *The integer Gram sequence $(a_k)_{k \ge 0}$ of Lemma 13.44 satisfies $a_{k q^i \bmod (q^d - 1)} = a_k$, $\sum_{k=0}^{q^d-2} a_k^2 = d$, $\operatorname{sgn}(\sum_{k=0}^{q^d-2} a_k) = (-1)^{d-1}$, and for every elliptic matrix $x \in \mathrm{GL}_d(F)$ whose irreducible characteristic polynomial equals $\operatorname{minpoly}_F(\zeta^j)$ ($\deg\operatorname{minpoly}_F(\zeta^j) = d$),*
     $$\chi(x) = \sum_{k=0}^{q^d-2} a_k\,\omega^{j k}.$$
  2. **Signed single-orbit root-sum formula and central twist (explicitly conditioned on the named `R2 [Lean]` input `GlobalTheory.CuspFormula.exists_regular`, `ExistsLabel.lean:49`).** *Assume in addition `exists_regular`. Then there exists a regular exponent $k_0 \in \{0, \dots, q^d - 2\}$ ($\forall\,1 \le e < d,\; (q^d - 1) \nmid k_0(q^e - 1)$) such that $\chi = (-1)^{d-1}\psi_{s_{k_0}}$ on $\mathrm{GL}_d(F)$, i.e. $a_k = (-1)^{d-1}$ on the $d$-element Frobenius orbit $\{k_0 q^i \bmod (q^d - 1) : 0 \le i < d\}$ and $a_k = 0$ elsewhere. Writing $\theta(z) := \theta_0(z)^{k_0}$ on the embedded degree-$d$ field units $\mathbb F_{q^d}^\times = \langle \zeta\rangle$, every elliptic element $x \in \mathrm{GL}_d(F)$ with eigenvalue $z \in \mathbb F_{q^d}^\times$ satisfies*
     $$\chi(x) = (-1)^{d-1} \sum_{i=0}^{d-1} \theta\!\left(z^{q^i}\right),$$
     *and every central scalar $c \in F^\times \subseteq \mathbb F_{q^d}^\times$ satisfies $\chi(c x) = \theta(c)\,\chi(x)$ on elliptic classes (and on all of $\mathrm{GL}_d(F)$ via Schur's lemma as in `nameCentral`, Lemma 13.38).*
- **(B) Elliptic determination of cuspidal characters (`GlobalTheory.CuspGL.cuspElliptic_statement : CuspElliptic.Statement`, `IrrCharEqOneOfSubsingleton.lean:45–52` — proved without `exists_regular`).** *Under the hypotheses of Part (A1) alone (without invoking `exists_regular`), `CuspElliptic.Statement` holds for **every** finite field $F$ and **every** $d \ge 0$: if $\chi, \chi' : \mathrm{GL}_d(F) \to \mathbb C$ satisfy `CuspElliptic.IsCuspChar` and $\chi(x) = \chi'(x)$ whenever $\operatorname{charpoly}(x) \in F[X]$ is irreducible, then $\chi = \chi'$ on all of $\mathrm{GL}_d(F)$.*
- **(C) Payment to §13.4.12's representation-level consumers (`LabelMapNonempty.lean:18–127`, `CuspidalParametrization.lean:50–72`).** *Let $K$ be a finite field, $C : \mathrm{LabelConv}\,K$, and $d \ge 1$:*
  1. *In `LabelMapNonempty.iso_of_label` (`:83–120` — the **unique** consumer of `cuspElliptic_statement` in the archive, at `:94`), given simple cuspidal representations $\tau, \tau' : \mathrm{FDRep}\,\mathbb C\,(\mathrm{GL}(\mathrm{Fin}\,d, K))$ sharing `HasCuspLabel C τ P` and `HasCuspLabel C τ' P`, expressing any root $z \in \bar K^\times$ of an irreducible $\operatorname{charpoly}(\gamma)$ ($\gamma \in \mathrm{GL}_d(K)$) as $C.\mathrm{gen}(d)^m$ equates $\chi_\tau(\gamma) = \chi_{\tau'}(\gamma)$ on all elliptic elements; Part (B) (`cuspElliptic_statement`) upgrades elliptic agreement to global character equality $\chi_\tau = \chi_{\tau'}$ on $\mathrm{GL}_d(K)$, which **(U4)** (`zIdemOrthogonal_holds`, `:108–120`) upgrades to $\tau \cong \tau'$. Consequently, interface **(U2)** of Table 13.4.12 is discharged to conditional `R3 [Lean, read]`.*
  2. *In `LabelMapNonempty.exists_label` (`:18–81`) and `finrank_of_simple_cuspidal` (`CuspidalParametrization.lean:50–72`), the bridges `isIrrChar_of_norm_one` (`IrrCharEqOneOfSubsingleton.lean:26–32`), `isPrimitive_of_isCuspChar` (Lemma 13.43(4)), and `regular_iff_natDegree_and_exists_elliptic` (Lemma 13.44(1)) supply all surrounding hypotheses to **(U1)** `exists_regular` (`ExistsLabel.lean:49`), leaving **(U1)** as the sole remaining character-formula `R2 [Lean]` input on the exhaustion and representation-degree legs of `cuspParam_all` $\to$ `PM.greenCuspidal` (discharged at `R3` by Theorem 13.54 in §13.4.14).*

*Proof.* **Part (A1) (`EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:127–210`).** By `isIrrChar_of_norm_one` (`IrrCharEqOneOfSubsingleton.lean:26–32`, combining `matrixChar_iff_isChar` with `(I8)` `irr_of_norm_one`), `CuspElliptic.IsIrrChar χ` implies `BI.IsIrrChar ℂ ℂ χ`, and Lemma 13.43(4) gives `IsPrimitive (extZero χ)`. Lemma 13.44(2)–(3) supplies $a : \mathbb N \to \mathbb Z$ with $\sum_{k=0}^{m-1} a_k^2 = d\,\langle \chi, \chi\rangle_G = d$ ($m := q^d - 1$, using Schur self-pairing $\langle \chi, \chi\rangle_G = 1$) and $\operatorname{sgn}(\sum_{k=0}^{m-1} a_k) = (-1)^{d-1}$ since $\chi(1) > 0$. Now let $x \in \mathrm{GL}_d(F)$ satisfy $\operatorname{charpoly}(x) = \operatorname{minpoly}_F(\zeta^j)$ of degree $d$. Applying `(I5b)` (`expand_primitive`) at the unit $\operatorname{toLin}'(x)$ and Clause 1 of `extZero_spec` gives $\lvert G\rvert\,d\,\chi(x) = \sum_{k=0}^{m-1} (a_k\lvert G\rvert)\,\psi_{s_k}(\operatorname{toLin}'(x))$ (`:150–155`). Because $\operatorname{charpoly}(x)$ is irreducible, `(I3b)` (`psi_of_irreducible_charpoly`, §13.4.4) kills all proper invariant-subspace terms of $\psi_{s_k}$ and evaluates $\psi_{s_k}(\operatorname{toLin}'(x)) = R_k(\operatorname{minpoly}_F(\zeta^j)) = \sum_{i=0}^{d-1} \omega^{j q^i k}$ (`:156–169`). Exchanging the sums over $0 \le k < m$ and $0 \le i < d$, since $\gcd(q^i, m) = 1$, multiplication by $q^i \bmod m$ permutes $\{0, \dots, m - 1\}$ (`sum_range_apply_mul_mod_eq_of_coprime`, `:109–125`), and `(I5)` (`ipGL_rootSum_eq_of_modEq`) gives $a_{k q^i \bmod m} = a_k$ (`:183–188`). Therefore each of the $d$ inner sums over $k$ equals $\sum_{k=0}^{m-1} a_k \omega^{j k}$ (`:178–193`); adding the $d$ identical copies and canceling $\lvert G\rvert\,d \neq 0$ yields $\chi(x) = \sum_{k=0}^{m-1} a_k \omega^{j k}$ (`:194–210`).

**Part (A2) (`LabelMapNonempty.lean:22–81`).** Adjoining the named `R2 [Lean]` interface `GlobalTheory.CuspFormula.exists_regular` (`ExistsLabel.lean:49`) to `isIrrChar_of_norm_one` and `isPrimitive_of_isCuspChar` produces a regular exponent $k_0$ with $\chi(x) = (-1)^{d-1}\psi_{s_{k_0}}(\operatorname{toLin}'(x))$ for all $x \in \mathrm{GL}_d(F)$ (`LabelMapNonempty.lean:22–23`). On any elliptic $x$ whose irreducible characteristic polynomial $Q$ has root $z = \zeta^j \in \mathbb F_{q^d}^\times$, `(I3b)` again collapses $\psi_{s_{k_0}}(\operatorname{toLin}'(x))$ to $R_{k_0}(Q) = \sum_{i=0}^{d-1} \theta_0(z^{q^i})^{k_0} = \sum_{i=0}^{d-1} \theta(z^{q^i})$ (`:60–65`), giving the signed single-orbit root sum. For $c \in F^\times$, scaling $x \mapsto c x$ scales its eigenvalues $z^{q^i} \mapsto (c z)^{q^i} = c\,z^{q^i}$ ($c^q = c$), factoring out $\theta(c)$ term by term (`NameCentral.lean:36–108`, Lemma 13.38).

**Part (B) (`IrrCharEqOneOfSubsingleton.lean:12–52` and `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:213–302`).** Split on whether $d = 0$:
- *Degenerate rank $d = 0$ (`irrChar_eq_one_of_subsingleton`, `IrrCharEqOneOfSubsingleton.lean:12–24`):* When $d = 0$, $\mathrm{GL}_0(F)$ is a subsingleton $\{1\}$ of cardinality $1$. For any `CuspElliptic.IsIrrChar χ` with matrix witness of rank $n \in \mathbb N$, $\chi(1) = n$ and unit norm reads $n^2 = 1$, forcing $n = 1$ and $\chi(x) = \chi(1) = 1 = \chi'(x)$ (`:46–49`).
- *Positive rank $d > 0$ (`eq_of_isPrimitive_of_eq_on_elliptic`, `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:213–302`):* By `isIrrChar_of_norm_one` and Lemma 13.43(4), both $\chi$ and $\chi'$ satisfy `BI.IsIrrChar ℂ ℂ` and `IsPrimitive (extZero _)`. Assume for contradiction that $\chi \neq \chi'$ (`:222`). By `(I1)` (`TeichEmb.exists_teichmuller`, §13.4.9), choose an injective multiplicative lift $\theta_0 : \bar F^\times \hookrightarrow \mathbb C^\times$, and pick a generator $\zeta$ of the cyclic group $\{z \in \bar F^\times : z^{q^d - 1} = 1\}$ so $\omega := \theta_0(\zeta)$ is a primitive $(q^d - 1)$-st root of unity in $\mathbb C$ (`:223–251`). Let $a, b : \mathbb N \to \mathbb Z$ be the integer Gram sequences of $\chi, \chi'$ from Lemma 13.44(2). Because $\chi$ and $\chi'$ are distinct irreducible characters, Schur orthogonality (`finiteGroupFunctionPairing_self_irreducible_algClos` and `finiteGroupFunctionPairing_eq_zero_of_distinct_irredu`, §13.4.10) gives $\langle \chi, \chi\rangle_G = \langle \chi', \chi'\rangle_G = 1$ and $\langle \chi, \chi'\rangle_G = 0$, so Lemma 13.44(3) yields $\sum_{k=0}^{N-1} a_k^2 = d$, $\sum_{k=0}^{N-1} b_k^2 = d$, and $\sum_{k=0}^{N-1} a_k b_k = 0$ (`:253–269`). By Lemma 13.44(2) and positivity of degrees $\chi(1), \chi'(1) \in \mathbb Z_{>0}$ (`isCharacterOverSubfield_restrict_classFunction_one`, §13.4.10), both $\sum_{k=0}^{N-1} a_k$ and $\sum_{k=0}^{N-1} b_k$ carry the exact sign of $\prod_{i=1}^{d-1}(1 - q^i)$, hence $(\sum_{k=0}^{N-1} a_k)(\sum_{k=0}^{N-1} b_k) > 0$ (`:270–284`). Finally, for every regular residue $0 \le j < N$, $\zeta^j$ satisfies $(\zeta^j)^{q^e} \neq \zeta^j$ for $1 \le e < d$, so Lemma 13.44(1) (`regular_iff_natDegree_and_exists_elliptic`) supplies an elliptic matrix $x_j \in \mathrm{GL}_d(F)$ with $\operatorname{charpoly}(x_j) = \operatorname{minpoly}_F(\zeta^j)$ of degree $d$ (`:285–297`). Part (A1) together with the hypothesis $\chi(x_j) = \chi'(x_j)$ gives $\sum_{k=0}^{N-1} a_k \omega^{j k} = \chi(x_j) = \chi'(x_j) = \sum_{k=0}^{N-1} b_k \omega^{j k}$ for every regular $j$, contradicting Lemma 13.45 (`:298–302`).

**Part (C) (`LabelMapNonempty.lean:18–127` and `CuspidalParametrization.lean:50–72`).**
1. In `iso_of_label` (`LabelMapNonempty.lean:83–120`), fix a root $x \in \bar K^\times$ of $P$ (`:89`). For any $\gamma \in \mathrm{GL}_d(K)$ with irreducible $\operatorname{charpoly}(\gamma)$, $\det(\gamma) \neq 0$ rules out $\operatorname{charpoly}(\gamma) = X$ (`:97–101`), so any root $z \in \bar K^\times$ of $\operatorname{charpoly}(\gamma)$ satisfies $z^{\lvert K\rvert^d - 1} = 1$ (`:102–103`) and hence $z = C.\mathrm{gen}(d)^m$ for some $m \in \mathbb N$ (`:104–105`). Applying the elliptic trace clauses of `h : HasCuspLabel C τ P` and `h' : HasCuspLabel C τ' P` at $(x, \gamma, z, m)$ equates $\chi_\tau(\gamma) = (-1)^{d-1}\sum_{i < d} C.\iota(x)^{m\,\lvert K\rvert^i} = \chi_{\tau'}(\gamma)$ (`:106`). Passing `isCuspChar_character τ hs hc` and `isCuspChar_character τ' hs' hc'` into `cuspElliptic_statement` (`:94–95`, Part B) produces `heq : τ.character = τ'.character` on all of $\mathrm{GL}_d(K)$. Lines `:107–120` then deduce `zIdem τ = zIdem τ'` from `heq` (`finrank` at $1$ and values at $\gamma^{-1}$) and invoke **(U4)** `zIdemOrthogonal_holds` to conclude `Nonempty (τ ≅ τ')`.
2. In `exists_label` (`:18–81`, and identically at the start of `finrank_of_simple_cuspidal`, `CuspidalParametrization.lean:54–57`), `h := isCuspChar_character τ hs hc` is converted by `isIrrChar_of_norm_one` (`:23`) and `isPrimitive_of_isCuspChar` (`:23`, Lemma 13.43(4)) into the exact premises of `exists_regular`, producing a regular $k$ with $\chi_\tau = (-1)^{d-1}\psi_{s_k}$; line `:36` then invokes `regular_iff_natDegree_and_exists_elliptic` (Lemma 13.44(1)) to certify $\deg\operatorname{minpoly}_K(C.\mathrm{gen}(d)^k) = d$, and lines `:51–81` verify `HasCuspLabel C τ (minpoly K (C.gen d ^ k))` by reindexing $C.\iota(z^{\lvert K\rvert^i})^k = C.\iota(x_0^{\lvert K\rvert^i})^m$ on $z = C.\mathrm{gen}(d)^m$ and $x_0 = C.\mathrm{gen}(d)^k$. $\square$

---

#### Remarks

1. *Classical provenance: Green (1955) and S. I. Gelfand (1970).* In Green's original paper `[Green1955]`, cuspidal ("primary irreducible") characters $(-1)^{d-1} I_d^1[\{1\}]$ are constructed first as explicit virtual combinations of characters induced from centralizers (Theorem 12, p. 439, and Lemma 7.7, p. 441), so single-orbit concentration is built into their definition before completeness of the full character table (Theorem 14, p. 444) proves exhaustion; Green explicitly records the smallest case $\mathrm{GL}(2, 2) \cong \mathfrak S_3$ and its linear cuspidal character $-I_2^1[1]$ in §8 Remark 3 (pp. 444–445, matching our Example 13.41). The intrinsic representation-theoretic characterization of cuspidal modules via vanishing of unipotent-radical invariants (`IsCuspChar` / `IsCuspidal`) and their determination by character values on the regular elliptic (anisotropic) torus were placed at the center of the finite-$\mathrm{GL}_n$ theory by S. I. Gelfand `[Gelfand1970]` (*Mat. Sb.* **83(125)** (1970), 15–41; *Math. USSR-Sb.* **12**(1) (1970), 13–39, §§2–6). Notice how the archive blends both viewpoints: it uses Green's invariant-subspace Möbius basis $\psi_{s_k}$ (`(I4)`–`(I6)`) to expand Gelfand's unipotent-vanishing characters into integer Fourier modes $a_k$ and separates them directly by Parseval before `exists_regular` is ever proved.
2. *Why $(2, 2)$ and $(3, 2)$ are exceptions in §13.4.12's `Pin` (`PairCheckThreeTwo.lean`) yet pass automatically in Lemma 13.45 (`SeparationNumericalIneqCuspidalGL.lean`).* Both §13.4.12 (`Pin.2`) and Lemma 13.45 bound the discrete Fourier energy of an integer vector supported on non-regular residues modulo $q^d - 1$, and both isolate $(2, 4)$ ($N = 15$) and $(2, 6)$ ($N = 63$). Why did `Pin.2` also have to treat $(2, 2)$ and $(3, 2)$ by hand, whereas `sep_numerical_ineq` handles $(2, 2)$ ($1 < 12$) and $(3, 2)$ ($17 < 32$) with room to spare? Because `Pin.2` works purely on the torus $K^\times$ without knowing the ambient $\mathrm{GL}_d(F)$ identity value `(I2)`, so it treats the $j = 0$ residue uniformly alongside all other residues in $D$ with the worst-case bound $\lvert\mathrm{dif}(1)\rvert \le 2d$ (which actually vanishes for two orbit indicator vectors, though `PinChar.card_le` bounds every point of $D$ uniformly by $(2d)^2 = 16$!). By contrast, `orthogonal_int_vectors_not_agree_on_regular` works with **arbitrary** orthogonal norm-$d$ integer vectors $a, b$ (not yet known to lie in $\{0, \pm 1\}$), so on nonzero non-regular residues $j \in B$ it still pays $(2d)^2 = 4 d^2$, **but** at $j = 0$ the degree-and-sign law $d\,\chi(1) = (\sum a_k)\prod_{i=1}^{d-1}(1 - q^i)$ forces $S_a$ and $S_b$ to have the **same sign**, compressing $\lvert\widehat c(0)\rvert^2 = (S_a - S_b)^2$ from $(2d)^2 = 16$ down to $(d - 1)^2 = 1$ at $d = 2$! At $(2, 2)$ ($B = \emptyset$) that drops the upper bound from $16$ to $1 < 12$, and at $(3, 2)$ ($\lvert B\rvert = 1$, $j = 4$) from $32$ to $1 + 16 = 17 < 32$.
3. *Where all four clauses of `extZero_spec` do work.* In Section 13.4.10 (Remark 13.4.10(4) and the `proof-map` note), the positive-sign path `isChar_psi_rootSum_of_regular` needed only Clause 3 of `extZero_spec` (equating unit-sum pairings on $\operatorname{End}_F(F^d)$ with $\mathrm{GL}_d(F)$-pairings). Lemma 13.43(4) and Theorem 13.46(A1) explain why `GeneralLinearFunctionExtendZeroEndProperties.lean` proved all **four** clauses: `finsum_nilRad_extZero_eq_zero` uses **Clause 1** on invertible cosets and **Clause 2** (vanishing on singular endomorphisms, combined with `charpoly_block`) on singular stabilizer elements, while `isPrimitive_extZero_of_sum_unipotent` and `character_elliptic_eq_coeff_sum_lemma` use **Clause 4** (conjugation invariance on $\operatorname{End}_F(F^d)$) to transport nilradicals across arbitrary proper subspaces and expand primitive class functions.

**Table 13.4.13 (source-to-text map for §13.4.13; full per-file byte SHA-256s in `SOURCE-MAP.md`).** Paths are relative to `lean/` in the pinned archive (`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`); `CT/` denotes `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/`.

| Reading / tag | Declaration(s) | Archive or Mathlib path and lines | Role in §13.4.13 |
|---|---|---|---|
| Definitions / `[Lean, read]` | `IsChar`, `IsIrrChar`, `unipBlock`, `IsCuspChar`, `CuspElliptic.Statement`; `lowSub`, `unip` | `src/Formalism/UnipotentAdelicQuotients/CuspEllipticValues.lean:7–26`; `CT/ExistsStandardUnipotentRadicalBijOnNilradical.lean:11–15` | Definition 13.9 |
| R3 / `[Lean, read]` | `finrank_lowSub_of_le`, `toLin'_mem_nilRad_lowSub_iff`, `exists_unip_bijOn_nilRad`; `char_coset_sum_eq_zero`; `charpoly_eq_restrict_mul_mapQ`, `charpoly_block`; `exists_linearEquiv_mem_iff_of_finrank_eq`, `finsum_nilRad_extZero_eq_zero`, `isPrimitive_extZero_of_sum_unipotent`; `matrixChar_iff_isChar`, `isPrimitive_of_isCuspChar` (+ `*Statement.lean` wrappers) | `CT/ExistsStandardUnipotentRadicalBijOnNilradical.lean:62–159`; `CT/CharacterCosetSumEqZeroOfSubgroupSum.lean:10–44`; `CT/CharpolyBlockAndInvariantUnderStabilizerNilradic.lean:10–55`; `CT/IsPrimitiveExtendZeroOfSumUnipotentRadical.lean:12–100`; `CT/MatrixTraceIffIsCharacterOverSubfieldComplex.lean:7–28`; `CT/IrrCharEqOneOfSubsingleton.lean:34–43` | Lemma 13.43 |
| R3 / `[Lean, read]` | `pow_card_pow_eq_iff_natDegree_minpoly_dvd`, `exists_GL_charpoly_eq_minpoly`, `regular_iff_natDegree_and_exists_elliptic`; `character_pairing_eq_finrank_hom`, `pair_add_nat_pos_symm`, `finsum_mul_star_virt_int`; `exists_int_coeff_of_isPrimitive`; `torus_orthogonality`, `sum_coef_mul_eq_pair` (+ `*Statement.lean` wrappers) | `CT/RegularIffNatDegreeAndExistsEllipticGL.lean:8–85`; `CT/FiniteGroupFunctionPairingAddNatPosSymm.lean:7–54`; `CT/VirtualCharacterInnerEqIntMulCard.lean:11–40`; `CT/ExistsIntCoeffPrimitiveGLCharacter.lean:17–67`; `CT/FrobeniusTorusCharacterOrthogonality.lean:9–92`; `CT/EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:33–100` | Lemma 13.44 |
| R3 / `[Lean, read]` | `abs_sum_le_sum_sq_int`, `orthogonal_int_vectors_not_agree_on_regular`; `parsevalSep_orth`, `parsevalSep_identity`, `parsevalSep_bound`; `card_nonregular_residues_le`; `sepIneq_sum_lt`, `sepIneq_large`, `sep_numerical_ineq`; `no_norm_eight_of_fourier_vanishing_order_fifteen`; `fourier_inv_sixtythree`, `mixed_diff_sixtythree`, `apply_add_21_eq_of_fourier_vanish_order_63`, `no_norm_twelve_order_sixtythree` (+ `*Statement.lean` wrappers) | `CT/OrthogonalIntVectorsNotAgreeOnRegular.lean:13–61`; `CT/ParsevalBoundIntegerVectorSmallFourierSupport.lean:8–112`; `CT/CardNonregularResiduesModPowSubOneLe.lean:8–64`; `CT/SeparationNumericalIneqCuspidalGL.lean:8–117`; `CT/NoNormEightOfFourierVanishingOrderFifteen.lean:8–58`; `CT/NoNormTwelveOrderSixtythree.lean:8–218` | Lemma 13.45 |
| R3 / `[Lean, read]` | `sum_range_apply_mul_mod_eq_of_coprime`, `character_elliptic_eq_coeff_sum_lemma`, `eq_of_isPrimitive_of_eq_on_elliptic`; `irrChar_eq_one_of_subsingleton`, `isIrrChar_of_norm_one`, `cuspElliptic_statement`; consumer calls in `exists_label`, `iso_of_label`, `finrank_of_simple_cuspidal` | `CT/EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:109–302`; `CT/IrrCharEqOneOfSubsingleton.lean:12–32, 45–52`; `src/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/LabelMapNonempty.lean:18–127`; `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalParametrization.lean:50–72` | Theorem 13.46(A)–(C) |
| `[Lean, read]` (Mathlib, pin `0df444a`) | `IsIdempotentElem.trace_eq_zero_iff`; `Matrix.charpoly_fromBlocks_zero₂₁`; `Algebra.charpoly_leftMulMatrix`; `Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero` | `Mathlib/LinearAlgebra/Trace.lean:340`; `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean:187`; `Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean:75`; `Mathlib/LinearAlgebra/Vandermonde.lean:248` | Lemmas 13.43(2)–(3), 13.44(1), and 13.45(Step 3) |
| Inherited `R3` | `(I1)` `TeichEmb.exists_teichmuller`, `(I2)` `psi_one`, `(I3b)` `psi_of_irreducible_charpoly`, `(I4)`–`(I6)` (`ipGL` Gram, `expand_primitive`, `ipGL_rootSum_eq_of_modEq`, `rootPowerSum_charpoly_mem_virtualCharacters_GL`), `(I8)` (`irr_of_norm_one`, `star_virt_eq_inv`, `extZero_spec`), `mem_virt_iff_sub`, `nameCentral`, `PM.greenCuspidal` | Sections 13.4.4–13.4.12 | Consumed by citation without re-proof |
| R2 / `[Lean]` named interfaces | **(U1)** `GlobalTheory.CuspFormula.exists_regular` (`ExistsLabel.lean:49`; read at `R3` in §13.4.14); **(U4)** `zIdemOrthogonal_holds` (`LabelMapNonempty.lean:108`); deeper monomial-basis/trace-comparison inputs inside `(I6)` (§13.4.5); Mathlib `FDRep.scalar_product_char_eq_finrank_equivariant` / `char_orthonormal` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLabel.lean:49`; `src/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/LabelMapNonempty.lean:108` | Retained as named statement-level inputs here; Theorem 13.46(A2) is conditioned explicitly on `exists_regular` (hypothesis removed by Theorem 13.54 in §13.4.14), whereas Theorem 13.46(A1) & (B) do **not** depend on `exists_regular` |
| Our check | `verify_elliptic_character.py` (`85725745…daf2`): 6,210 exact assertions covering all 39 archive files, Examples 13.41–13.42 over $\mathbb Q(\zeta_3)$ and $\mathbb Q(\zeta_8)$, and `sep_numerical_ineq` + $N \in \{15, 63\}$ Fourier bounds | Run certificate (`sources/SOURCES.md`) | Exact computational verification |

### 13.4.14 Converse regular-label existence: `exists_regular`

**Motivation.** After Section 13.4.13 one character-theoretic interface of the representation-level parametrization `PM.greenCuspidal` was still held at statement level: **(U1)** `GlobalTheory.CuspFormula.exists_regular` (`ExistsLabel.lean:49`). It is the converse of Proposition 13.6. There a regular exponent $k$ modulo $N := q^d - 1$ (that is, $k q^i \not\equiv k \pmod N$ for $0 < i < d$) was given, and the signed invariant-subspace Möbius inverse $(-1)^{d-1}\psi_{s_k}$ was shown to be an irreducible character of $\mathrm{GL}_d(F)$. Here an irreducible character $\chi$ whose zero extension is primitive is given, and a regular $k$ with $\chi = (-1)^{d-1}\psi_{s_k}$ has to be *found*. Section 13.4.12 uses the answer twice, in the exhaustion leg `exists_label` and in the degree formula $\dim W(P) = \prod_{i=1}^{d-1}(q^i - 1)$ of `finrank_of_simple_cuspidal` (Theorem 13.40(B), items 3 and 1). Section 13.4.13 used it once more, as the hypothesis of Theorem 13.46(A2).

Three statements about labels must be kept apart. The archive proves them in different files, and its consumers take them separately.

- **(Q1) A label exists for a given character.** For every irreducible $\chi$ with `IsPrimitive (extZero χ)` there is some regular $k$ with $\chi = (-1)^{d-1}\psi_{s_k}$. This is `exists_regular`, the subject of this subsection. The quantifiers are $\forall \chi\ \exists k$. Nothing is said about how many $k$ work, or about which regular $k$ occur.
- **(Q2) The label is unique up to Frobenius.** If $(-1)^{d-1}\psi_{s_k} = (-1)^{d-1}\psi_{s_{k'}}$ with $k, k'$ regular, then $k' \equiv k q^i \pmod N$ for some $i < d$. At character level this is the orbit equivalence of Proposition 13.6, Step 7, which pairs both sides with $R_{k'}$ and applies `(I4)`. For polynomial labels it is `hasCuspLabel_unique` and `LabelUniqueAll.label_eq` (Lemma 13.39). For modules, two simple cuspidal modules with the same label are isomorphic by `iso_of_label`, which combines Theorem 13.46(B) with **(U4)**. We only cite these results.
- **(Q3) Every regular label is realized.** For every regular $k$ the function $(-1)^{d-1}\psi_{s_k}$ is an irreducible character (`isCharacter_cuspidal_rootSum_regular`, Proposition 13.6, Step 3). We only cite this result, but it enters the proof of (Q1) at the last step.

The proof of (Q1) is arithmetic on the Gram vector. Lemma 13.44 attaches to $\chi$ the integer vector $a = (a_l)_{l \bmod N}$ with $a_l = \langle \chi, R_l\rangle_G$, which is Frobenius-invariant and satisfies $\sum_l a_l^2 = d$. If $a$ has a nonzero entry $a_k$ at a regular residue $k$, Schur orthogonality against the irreducible character $(-1)^{d-1}\psi_{s_k}$ forces $\chi = (-1)^{d-1}\psi_{s_k}$. The difficulty is to exclude a Gram vector supported on non-regular residues. Example 13.48(5) shows that Frobenius invariance, length $d$, the sign law, norm one, positive degree and primitivity do not exclude it. Integrality of a second family of pairings does. The elementary symmetric functions $e_s$ of the $k$-th powers of the lifted eigenvalues are virtual characters (Lemma 13.50); this is the load-bearing new proof of this subsection, and its classical counterpart is the stability of $R(G)$ under the $\lambda$-operations. On primary classes $d\,e_s$ is a sum of root power sums (Lemma 13.51), so pairing with $\chi$ gives $d \mid \sum_{\lvert I\rvert = s} a_{k\sum_{i \in I} q^i}$. An orbit-stabilizer argument on subsets of $\mathbb Z/d$ turns this into $s \mid a_l$ whenever the period of $l$ divides $d/s$ (Lemma 13.52). A non-regular residue in the support then carries more squared length than $d$ (Lemma 13.53).

The label is a statement about the Gram vector, which is indexed by exponents. It does not say on which elliptic elements $\chi$ lives. On an elliptic $x$ with eigenvalue $\xi$ the conclusion gives $\chi(x) = (-1)^{d-1}\sum_{i<d}\theta_0(\xi)^{k q^i}$. This is a sum of $d$ roots of unity, and in general it is nonzero also when $\operatorname{charpoly}(x)$ is not the label polynomial. Example 13.48(6) counts the zero and nonzero values on $\mathrm{GL}_2(\mathbb F_3)$.

We do **not** re-prove: Lemma 13.44 (integer Gram vectors, degree-and-sign law, inner-product law), the integrality of pairings of virtual characters (`virtualCharacter_inner_eq_int_mul_card`, Lemma 13.44(2)), `(I2)`, `(I5)`, the Frobenius covariance of Section 13.4.6, Green virtuality `(I6)`, `(I8)`, Lemmas 13.28 and 13.30, the realization (Q3), and the elliptic formulas and elliptic determination of Theorem 13.46. Everything read at `R3` here is listed in Table 13.4.14.

#### Worked examples

**Example 13.47 ($\mathrm{GL}_2(\mathbb F_2) \cong \mathfrak S_3$: the one regular orbit, an eigenvalue cancellation, and the esymm divisibility).** [Expository; exact arithmetic over $\mathbb Q(\zeta_3)$ in `verify_regular_label_existence.py`] Keep the notation of Example 13.41: $q = d = 2$, $N = 3$, $\mathbb F_4 = \mathbb F_2[\alpha]$, $\theta_0(\alpha) = \omega_3$, the classes $\{I_2\}$, $C(u_0)$ (the three transpositions of $\mathbb P^1(\mathbb F_2)$) and $C(y)$ (the two $3$-cycles), the Steinberg character $\mathrm{St} = (2, 0, -1)$ and the sign character $\epsilon = (1, -1, 1)$ on these classes, with Gram vector $a = (a_0, a_1, a_2) = (0, -1, -1)$.

1. *Residues.* Multiplication by $2$ on $\mathbb Z/3$ fixes $0$ and swaps $1$ and $2$. The orbit $\{1, 2\}$ is the only regular one. For $q = 2$ the length condition alone excludes non-regular support, because a Gram vector supported on $\{0\}$ would need $a_0^2 = 2$.
2. *The cancellation behind $R_1$.* The class function $R_1 = s_1 \circ \operatorname{charpoly}$ takes the values $(2, 2, \omega_3 + \omega_3^2) = (2, 2, -1)$, and
   $$R_1 = \operatorname{Ind}_B^G \mathbf 1 - \epsilon = \mathbf 1 + \mathrm{St} - \epsilon,$$
   where $B$ is the upper triangular subgroup and $\operatorname{Ind}_B^G \mathbf 1 = \mathbf 1 + \mathrm{St}$ is the permutation character of $G$ on the three lines. Thus $R_1$ is a virtual character but not a character. At the level of eigenvalues, let $x(g) = \{\theta_0(\alpha_1), \theta_0(\alpha_2)\}$ be the lifted roots of $\operatorname{charpoly}(g)$, let $A(g)$ be the eigenvalues of the $3 \times 3$ permutation matrix of $g$, and let $B(g) = \{\epsilon(g)\}$. Then $x(g) + B(g) = A(g)$ as multisets:

   | $g$ | $x(g)$ | $B(g)$ | $A(g)$ |
   |---|---|---|---|
   | $I_2$ | $\{1, 1\}$ | $\{1\}$ | $\{1, 1, 1\}$ |
   | $u_0$ | $\{1, 1\}$ | $\{-1\}$ | $\{1, 1, -1\}$ |
   | $y$ | $\{\omega_3, \omega_3^2\}$ | $\{1\}$ | $\{1, \omega_3, \omega_3^2\}$ |

   This is the kind of decomposition $\varphi = \chi_A - \chi_B$ that Step 3 of Lemma 13.50 produces for an arbitrary virtual character, here for $\varphi = R_1$, $\chi_A = \mathbf 1 + \mathrm{St}$ and $\chi_B = \epsilon$. In particular $R_1(g^j) + p_j(B(g)) = p_j(A(g))$ for all $g$ and all $j \ge 1$, where $p_j$ is the $j$-th power sum.
3. *Solving for $e_2$.* Step 4 of Lemma 13.50 computes $e_2(x(g)) = e_2(A(g)) - e_1(x(g))\,e_1(B(g)) - e_0(x(g))\,e_2(B(g))$. Here $e_2(B) = 0$, $e_2(A)$ is the character of $\Lambda^2(\mathbf 1 + \mathrm{St})$, namely $\mathrm{St} + \epsilon = (3, -1, 0)$, and $e_1(x)\,e_1(B) = R_1\,\epsilon = \epsilon + \mathrm{St} - \mathbf 1 = (2, -2, -1)$. Hence $e_2(x) = \mathbf 1$. The characters $\mathrm{St}$ and $\epsilon$ cancel, and what remains is $\theta_0(\det)^1 = \mathbf 1$, since $\det \equiv 1$ on $\mathrm{GL}_2(\mathbb F_2)$.
4. *The esymm divisibility.* All three classes are primary. Lemma 13.51 reads $2 e^{(k)}_1 = R_k + R_{2k}$ and $2 e^{(k)}_2 = R_{3k} = R_0$. Pairing with $\epsilon$ gives $a_k + a_{2k} = 2\langle \epsilon, e^{(k)}_1\rangle$ and $a_0 = 2\langle \epsilon, \mathbf 1\rangle = 0$. For $k = 1$, $a_1 + a_2 = -2 = 2\langle \epsilon, \mathbf 1 + \mathrm{St} - \epsilon\rangle$.
5. *Conclusion.* The coefficient $a_1 = -1$ at the regular residue $1$ is nonzero, and $\epsilon = (-1)^{2-1}\psi_{s_1}$ (Example 13.41). The orthogonality sum of Step 6 of Theorem 13.54 is $\sum_g \epsilon(g)\,\epsilon(g^{-1}) = (-1)^{2-1} a_1 \lvert G\rvert = 6$. The only elliptic class is $C(y)$, whose characteristic polynomial $X^2 + X + 1$ is the label, so $\mathrm{GL}_2(\mathbb F_2)$ cannot show values off the label class. The next example does.

**Example 13.48 ($\mathrm{GL}_2(\mathbb F_3)$: three regular orbits, a principal-series cancellation, a non-virtual impostor, and values off the label class).** [Expository; exact arithmetic over $\mathbb Q(\zeta_8)$ in `verify_regular_label_existence.py`] Keep the notation of Example 13.42: $q = 3$, $d = 2$, $N = 8$, $\mathbb F_9 = \mathbb F_3[\zeta]$ with $\zeta^2 + \zeta + 2 = 0$, $\theta_0(\zeta) = \omega_8$, the eight classes $I_2$, $-I_2$, $u_1$, $-u_1$, $\operatorname{diag}(1, 2)$, $y_1$, $y_2$, $y_3$ of sizes $1, 1, 8, 8, 12, 6, 6, 6$, the cuspidal characters $\tau_{P_1}, \tau_{P_2}, \tau_{P_3}$ with Gram vectors $a^{(1)}, a^{(2)}, a^{(3)}$, and the quadratic character $\mathrm{sgn} := \theta_0 \circ \det$ ($\theta_0(-1) = \omega_8^4 = -1$).

1. *Residues and periods.* Multiplication by $3$ on $\mathbb Z/8$ fixes $0$ and $4$ and has the three regular orbits $\{1, 3\}$, $\{5, 7\}$ and $\{2, 6\}$. Lemma 13.52 with $s = 2$, $e = 1$ predicts $2 \mid a_0$ and $2 \mid a_4$ for the Gram vector of every primitive irreducible character, and indeed $a^{(r)}_0 = a^{(r)}_4 = 0$ for $r = 1, 2, 3$. Unlike the case $q = 2$, length alone does not decide this: $b_0 = b_4 = \pm 1$ gives $b_0^2 + b_4^2 = 2 = d$.
2. *The cancellation behind $R_1$.* Let $B$ be the upper triangular subgroup and let $\pi := \operatorname{Ind}_B^G(\mathbf 1 \otimes \mathrm{sgn})$ be induced from $\begin{pmatrix} a & b \\ 0 & c\end{pmatrix} \mapsto \theta_0(c)$. It is irreducible of degree $4$ with values $4, -4, 1, -1, 0, 0, 0, 0$ on the eight classes, and
   $$R_1 = \pi - \tau_{P_1}.$$
   On the eight classes the right side is $4 - 2$, $-4 + 2$, $1 + 1$, $-1 - 1$, $0$, $0 + i\sqrt 2$, $0 - i\sqrt 2$, $0$, which are the values of $R_1$. The cuspidal character of the orbit $\{1, 3\}$ enters with coefficient $-1 = (-1)^{d-1}$, and this is $a^{(1)}_1 = -1$. Directly from the character table,
   $$48\,\langle \tau_{P_1}, R_1\rangle = 2 \cdot 2 + (-2)(-2) + 8(-1)(2) + 8(1)(-2) + 0 + 6(-i\sqrt 2)\overline{(i\sqrt 2)} + 6(i\sqrt 2)\overline{(-i\sqrt 2)} + 0 = 4 + 4 - 16 - 16 - 12 - 12 = -48.$$
3. *The esymm identity holds on primary classes only.* For every $x$, $e^{(k)}_2(x) = \theta_0(\det x)^k = \mathrm{sgn}(x)^k$. On primary classes Lemma 13.51 reads $2 e^{(k)}_2 = R_{4k}$ and $2 e^{(k)}_1 = R_k + R_{3k}$. For example, on $y_1$ (roots $\zeta$ and $\zeta^3$), $2 e^{(1)}_2(y_1) = 2\omega_8^4 = -2 = \omega_8^4 + \omega_8^{12} = R_4(y_1)$. On the non-primary class of $\operatorname{diag}(1, 2)$ the identity fails: $2 e^{(1)}_2 = 2\,\mathrm{sgn}(2) = -2$, whereas $R_4 = \theta_0(1)^4 + \theta_0(-1)^4 = 2$. The failure does no harm because a primitive class function vanishes on non-primary classes (`classFn_eq_zero_of_charpoly_not_irreducible_pow`, used in Step 3 of the proof of Theorem 13.54), and indeed $\tau_{P_r}(\operatorname{diag}(1, 2)) = 0$.
4. *Integer pairings.* For $s = 1$, $\langle \tau_{P_1}, e^{(1)}_1\rangle = \langle \tau_{P_1}, R_1\rangle = -1$ and $a^{(1)}_1 + a^{(1)}_3 = -2 = 2 \cdot (-1)$. For $s = 2$, $\langle \tau_{P_1}, \mathrm{sgn}\rangle = 0$ (an irreducible character of degree $2$ against a linear character), so $a^{(1)}_4 = 2 \cdot 0$. The certificate checks $\sum_{\lvert I\rvert = s} a_{k\sum_{i \in I} 3^i} = 2\,\langle \chi, e^{(k)}_s\rangle$ for every $k < 8$, every $s \le 2$ and every cuspidal $\chi$.
5. *A non-virtual impostor.* For the non-regular exponents, $-\psi_{s_0} = \mathrm{St} - \mathbf 1$ and $-\psi_{s_4} = (\mathrm{St} - \mathbf 1)\,\mathrm{sgn}$ are virtual characters of norm $2$. Put
   $$\varphi_b := -\tfrac12\left(\psi_{s_0} + \psi_{s_4}\right) = \tfrac12\left(\mathrm{St} - \mathbf 1\right)\left(\mathbf 1 + \mathrm{sgn}\right).$$
   Then $\varphi_b$ is a primitive class function with $\langle \varphi_b, \varphi_b\rangle = 1$ and $\varphi_b(1) = 2$, and its Gram vector is $b = -(e_0 + e_4)$, that is, $b_0 = b_4 = -1$ and $b_l = 0$ otherwise. This vector is Frobenius-invariant, $\sum_l b_l^2 = 2 = d$, and $d\,\varphi_b(1) = 4 = (\sum_l b_l)(1 - 3)$. So $\varphi_b$ passes every test that Lemma 13.44 places on the Gram vector of a cuspidal character, and yet it is not $\pm\psi_{s_k}$ for any regular $k$. It is not a virtual character, since $\langle \varphi_b, \mathbf 1\rangle = -\tfrac12$. Accordingly it fails the esymm divisibility, because $\sum_{\lvert I\rvert = 2} b_{1 \cdot (1 + 3)} = b_4 = -1$ is odd (equivalently, $2\langle \varphi_b, \mathrm{sgn}\rangle = -1$), and it fails the period divisibility $2 \mid b_0$. It is the integrality supplied by Lemma 13.50, not the bookkeeping on Gram vectors, that pushes the support onto regular residues.
6. *Values off the label class.* By Theorem 13.46(A2), which Theorem 13.54(C) makes unconditional, a cuspidal $\tau$ with label orbit $\{k, 3k\}$ takes on an elliptic $x$ with eigenvalue $\zeta^j$ the value
   $$\tau(x) = -\left(\omega_8^{kj} + \omega_8^{3kj}\right) = -\omega_8^{kj}\left(1 + \omega_8^{2kj}\right),$$
   which vanishes exactly when $\omega_8^{2kj} = -1$, that is, when $kj \equiv 2 \pmod 4$. In the table of Example 13.42 there are $3 \times 12 = 36$ pairs $(\tau, x)$ with $x$ elliptic and $\operatorname{charpoly}(x)$ different from the label of $\tau$. The $12$ pairs in $\tau_{P_1} \times C(y_2)$ and $\tau_{P_2} \times C(y_1)$ have value $\pm i\sqrt 2 \neq 0$. The other $24$, namely $\tau_{P_1} \times C(y_3)$, $\tau_{P_2} \times C(y_3)$ and $\tau_{P_3} \times (C(y_1) \cup C(y_2))$, have value $0$. These zeros come from two roots of unity cancelling, and they are unrelated to the label. For $q = 5$, with $\zeta$ a generator of $\mathbb F_{25}^\times$ and $\theta_0(\zeta) = \omega_{24}$, the regular exponent $k = 3$ (orbit $\{3, 15\}$ modulo $24$) gives the value $-(\omega_{24}^{9} + \omega_{24}^{45}) = -\omega_{24}^{9}(1 + \omega_{24}^{12}) = 0$ on the label class itself, whose elements have eigenvalues $\zeta^3$ and $\zeta^{15}$; the general criterion for $d = 2$ and odd $q$ is $kj \equiv (q+1)/2 \pmod{q + 1}$, and here $3 \cdot 3 \equiv 3 \pmod 6$. This is why `HasCuspLabel` (Definition 13.8(2)) prescribes $\chi_\tau$ on every elliptic class by the orbit formula instead of imposing a support condition, and why `exists_label` needs the full identity $\chi = (-1)^{d-1}\psi_{s_k}$ rather than only $a_k \neq 0$.

**Example 13.49 ($(q, d) = (2, 4)$: the orbit-stabilizer bookkeeping of Lemma 13.52 on $2$-subsets of $\mathbb Z/4$).** [Expository; checked by `verify_regular_label_existence.py`] Here $N = 15$, and the residues $l$ with $l \cdot 2^2 \equiv l \pmod{15}$ are $l \in \{0, 5, 10\}$, all of the form $l = 5k = k(1 + 2^2)$. Take $s = 2$, $e = 2$. The six $2$-subsets $I \subseteq \mathbb Z/4$ and their exponents $\sum_{i \in I} 2^i$ are
$$\{0, 2\} \mapsto 5, \quad \{1, 3\} \mapsto 10, \quad \{0, 1\} \mapsto 3, \quad \{1, 2\} \mapsto 6, \quad \{2, 3\} \mapsto 12, \quad \{0, 3\} \mapsto 9.$$
Under translation by $\mathbb Z/4$ the first two form one orbit $O$ with stabilizer $\{0, 2\} = \mathrm{killed}(4, 2)$ of order $2$. The remaining four form one orbit with trivial stabilizer, and their exponents $3k, 6k, 12k, 9k \equiv 3k \cdot 2^i \pmod{15}$ lie in one Frobenius orbit, so by invariance they all carry the coefficient $a_{3k}$. The hypothesis $4 \mid \sum_{\lvert I\rvert = 2} a_{k\sum_{i \in I} 2^i}$ therefore reads $4 \mid a_{5k} + a_{10k} + 4 a_{3k}$. Since $10k \equiv 5k \cdot 2$ gives $a_{10k} = a_{5k}$, this is $4 \mid 2 a_{5k}$, that is, $2 \mid a_{5k}$, as Lemma 13.52 asserts for $s = 2$. Lemma 13.53 then excludes a nonzero coefficient at a residue of period $2$: $a_{5} \neq 0$ would force $a_{5}^2 \ge 4$, and the two residues $5$ and $10$ of its orbit alone would contribute $2 \cdot 4 = 8 > 4 = d$ to $\sum_l a_l^2$. The residue $0$ has period $1$, and the case $s = 4$ of the hypothesis is $4 \mid a_0$ directly.

---

#### Definitions

**Definition 13.10 (esymm class functions, periods, killed subgroups, and the predicates of the third consumer).** [Lean, read] Let $F$ be a finite field with $q = \lvert F\rvert$ elements, $d \ge 1$, $N := q^d - 1$, $G := \mathrm{GL}_d(F)$, and let $\theta_0 : \bar F \to \mathbb C$ be multiplicative and injective on $\bar F^\times$ (the hypothesis `hθ` of `exists_regular`: $\theta_0 x = \theta_0 y$ with $x, y \neq 0$ forces $x = y$). Write $s_k := $ `rootSum θ₀ k`, so $s_k(f) = \sum_\alpha \theta_0(\alpha)^k$ over the roots of $f$ in $\bar F$ with multiplicity, and $R_k := s_k \circ \operatorname{charpoly}$.

1. *Esymm class functions (`ExistsLabel.lean:38–41`).* For $x \in G$ let $E_k(x)$ be the multiset of the $\theta_0(\alpha)^k$, where $\alpha$ runs over the roots of $\operatorname{charpoly}(x)$ in $\bar F$ with multiplicity, so that $\lvert E_k(x)\rvert = d$. For $s \in \mathbb N$ put $e^{(k)}_s(x) := e_s(E_k(x))$, the $s$-th elementary symmetric function (`Multiset.esymm`, `Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean:70`). Thus $e^{(k)}_0 = 1$, $e^{(k)}_1 = R_k$, $e^{(k)}_d = \theta_0(\det)^k$, and $e^{(k)}_s = 0$ for $s > d$.
2. *Regular residues and periods.* A residue $k$ is regular if $k q^i \not\equiv k \pmod N$ for $0 < i < d$; this is the predicate `Reg (Nat.card F) d k` (`OrthSubrepresentation.lean:150`). Green calls such $k$ *$d$-primitive* and their Frobenius orbits $\{k, kq, \dots, kq^{d-1}\}$ *$d$-simplexes* (`[Green1955]`, display (42), p. 439). The *period* of $l$ is the least $e \ge 1$ with $l q^e \equiv l \pmod N$; it divides $d$ (`hmod`, `ExistsRegularExponentOfSumSqEq.lean:39–46`).
3. *Killed subgroups (`DvdOfPeriodOfDvdSumPowersetCard.lean:10–88`).* For $s e = d$ put $\mathrm{killed}(d, s) := \{x \in \mathbb Z/d : s x = 0\}$. It equals $\{e j : 0 \le j < s\}$ (`killed_eq_image`), has $s$ elements (`card_killed`), and satisfies $\sum_{x \in \mathrm{killed}(d, s)} q^{x} = \sum_{j < s}(q^e)^j$ (`sum_killed`), where exponents use the representative $x \in \{0, \dots, d - 1\}$. Every subgroup $H \le \mathbb Z/d$ equals $\mathrm{killed}(d, \lvert H\rvert)$ (`mem_iff_mem_killed`).
4. *The predicates of the third consumer (`ResEmbCompat.lean:108–111`, `OrthSubrepresentation.lean:150, 184–190`).* `CuspChar` asserts the following. For every finite field $F$, every multiplicative $\theta$ with `Inj θ`, every $m > 0$, and every irreducible representation $\kappa$ of $\mathrm{GL}_m(F)$ on a finite-dimensional complex space with `FinCusp κ`, there is $k$ with `Reg (Nat.card F) m k` and $\operatorname{tr}\kappa(x) = \mathrm{cusp}\,\theta\,m\,k\,x$ for all $x$, where $\mathrm{cusp}\,\theta\,m\,k\,x := (-1)^{m-1}\psi_{s_k}(\operatorname{toLin}'x)$ (through `psiG`). These are literally the two conclusions of `exists_regular`.

---

#### Lemmas and the main theorem

**Lemma 13.50 (elementary symmetric functions of eigenvalue powers are virtual characters: `esymm_mem_virt`).** [Lean, read] *Let $G$ be a finite group, let $\varphi \in \mathrm{Virt}(\mathbb C, \mathbb C, G)$ be a virtual character, and let $x : G \to \mathrm{Multiset}\,\mathbb C$ satisfy, for all $g \in G$ and all $j \ge 1$,*
$$\varphi(g^j) = \sum_{z \in x(g)} z^j .$$
*Then $g \mapsto e_s(x(g))$ is a virtual character of $G$ for every $s \in \mathbb N$ (`GlobalTheory.EsymmVirt.esymm_mem_virt`, `EsymmMemVirtualCharactersOfPowerSumEigenvalues.lean:110–129`; wrapper `T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues`, `EsymmMemVirtualCharactersOfPowerSumEigenvaluesStatement.lean:7`).*

*In the application (`CuspFormula.esymm_mem_virt`, `ExistsLabel.lean:38–47`), $G = \mathrm{GL}_d(F)$, $\varphi = R_k$, which is virtual by `(I6)` (`T.rootPowerSum_charpoly_mem_virtualCharacters_GL`, `:42`), and $x(g) = E_k(g)$. The hypothesis holds because the roots of $\operatorname{charpoly}(g^j)$ are the $j$-th powers of the roots of $\operatorname{charpoly}(g)$ (`T.roots_charpoly_pow_eq_map_pow`, `:43–44`, whose proof `RootsCharpolyPowEqMapPow.lean:10–79` was read in Section 13.4.5). Hence $R_k(g^j) = \sum_\alpha \theta_0(\alpha^j)^k = \sum_{z \in E_k(g)} z^j$, and every $e^{(k)}_s$ is a virtual character of $\mathrm{GL}_d(F)$.*

*Proof.* The argument is the classical one behind the $\lambda$-operations on $R(G)$ (Remark 1), carried out on multisets in four steps.

*Step 1: the generating function and the addition formula (`esymm_cons_succ`, `coeff_prod_one_add`, `esymm_add`, `:16–37`).* For a multiset $S$ of complex numbers, $e_{n+1}(a :: S) = e_{n+1}(S) + a\,e_n(S)$, by splitting the $(n+1)$-subsets of $a :: S$ according to whether they contain $a$ (`Multiset.powersetCard_cons`, `Mathlib/Data/Multiset/Powerset.lean:260`). Induction on $S$ then gives $\prod_{a \in S}(1 + aT) = \sum_n e_n(S)\,T^n$ in $\mathbb C[T]$. The product of the generating functions of $S$ and $S'$ is the generating function of $S + S'$, and comparing coefficients gives
$$e_n(S + S') = \sum_{i=0}^{n} e_i(S)\,e_{n-i}(S').$$

*Step 2: equal power sums give equal elementary symmetric functions (`esymm_eq_of_psum_eq`, `:39–56`).* Suppose $p_j(S) = p_j(S')$ for all $j \ge 1$; we show $e_n(S) = e_n(S')$ by strong induction on $n$. For $n = 0$ both sides are $1$. For $n \ge 1$ Newton's identity in multiset form (`multiset_newton_psum`, `MultisetPowerSumNewtonIdentity.lean:28`, read in Section 13.4.5) reads
$$p_n(S) = (-1)^{n+1} n\, e_n(S) - \sum_{0 < i < n} (-1)^i e_i(S)\, p_{n-i}(S).$$
Write it for $S$ and for $S'$. The power sums agree by hypothesis and $e_i(S) = e_i(S')$ for $0 < i < n$ by induction (`h3`), so subtracting the two identities (`linear_combination h2 - h1 + h n hn + h3`) gives $(-1)^{n+1} n\,(e_n(S) - e_n(S')) = 0$. The factor $(-1)^{n+1} n$ is nonzero in $\mathbb C$ (`h4`) and cancels. This declaration is distinct from the `esymm_eq_of_psum_eq` for $d$-tuples read with Lemma 13.39 (`CuspidalLabelPolynomialUniqueAllPrimes.lean:17`), which goes through Mathlib's multivariate Newton identity. Here the division by $n$ happens pointwise in $\mathbb C$, never in $R(G)$.

*Step 3: a virtual character is a difference of eigenvalue multisets (`exists_multisets`, `:74–108`).* For every $\varphi \in \mathrm{Virt}(\mathbb C, \mathbb C, G)$ there are $A, B : G \to \mathrm{Multiset}\,\mathbb C$ such that $g \mapsto e_s(A(g))$ and $g \mapsto e_s(B(g))$ are virtual characters for all $s$, and $\varphi(g^j) + p_j(B(g)) = p_j(A(g))$ for all $g$ and all $j \ge 1$. First, the constant empty multiset is admissible (`h0`, `:78–87`): $e_0(\varnothing) = 1$ is the trivial character, which is virtual by the last clause of `virt_mul_comap_conj_ind_linear` (linear characters are virtual) applied to the trivial homomorphism (`one_mem_virt`, `:60–61`), and $e_{s}(\varnothing) = 0$ for $s \ge 1$. Then induct over the additive closure that defines $\mathrm{Virt}$ (`AddSubgroup.closure_induction`, `:88`).
- *A genuine character $\varphi$ (`:89–95`).* Realize it by a matrix representation $\rho : G \to \mathrm{GL}_n(\mathbb C)$ (`matrixChar_iff_isChar`, read in Section 13.4.13). Take $A(g) :=$ the roots of $\operatorname{charpoly}(\rho(g))$ and $B(g) := \varnothing$. Then $e_s(A(\cdot))$ is the character of the $s$-th exterior power, represented by the compound matrix (`isChar_esymm_roots_charpoly`, `IsCharacterEsymmRootsCharpoly.lean:70`, read in Section 13.4.5), hence virtual (`isChar_mem_virt_complex`, which is `AddSubgroup.subset_closure`). Finally $\varphi(g^j) = \operatorname{tr}\rho(g)^j = p_j(A(g))$ by `Matrix.trace_eq_sum_roots_charpoly` and the power rule for roots (`CharpolyPow.roots_charpoly_pow`).
- *Zero (`:96`).* Take $A = B = \varnothing$.
- *Sums (`:97–103`).* For $\varphi + \varphi'$ take $A + A'$ and $B + B'$. By the addition formula of Step 1, $e_s(A(g) + A'(g)) = \sum_{i \le s} e_i(A(g))\,e_{s-i}(A'(g))$ is a sum of products of virtual characters, hence virtual, because $\mathrm{Virt}$ is closed under products (first clause of `virt_mul_comap_conj_ind_linear`, read in Section 13.4.5; `esymm_add_mem_virt`, `:63–72`). Power sums are additive.
- *Negatives (`:104–108`).* For $-\varphi$ exchange $A$ and $B$.

*Step 4: solving for $e_s(x(g))$ (`esymm_mem_virt`, `:110–129`).* Fix $A, B$ for $\varphi$ as in Step 3. For every $g$, the multisets $x(g) + B(g)$ and $A(g)$ have the same power sums, since $p_j(x(g)) + p_j(B(g)) = \varphi(g^j) + p_j(B(g)) = p_j(A(g))$. By Step 2, $e_n(x(g) + B(g)) = e_n(A(g))$ for all $n$ (`he`, `:115–117`). Expand the left side by Step 1 and isolate the term $e_s(x(g))\,e_0(B(g)) = e_s(x(g))$:
$$e_s(x(g)) = e_s(A(g)) - \sum_{i=0}^{s-1} e_i(x(g))\, e_{s-i}(B(g)) \qquad (\text{`:120–126`}).$$
By strong induction on $s$ (`:118`), each $e_i(x(\cdot))$ with $i < s$ is already virtual, and $e_{s-i}(B(\cdot))$ and $e_s(A(\cdot))$ are virtual by Step 3. Closure of $\mathrm{Virt}$ under products, sums and differences (`sub_mem`, `sum_mem`, `:127–129`) finishes the induction. $\square$

**Lemma 13.51 (the esymm identity on primary classes: `natDegree_mul_esymm_roots_pow`).** [Lean, read] *Let $F$ be finite, $\theta_0$ as above, $f \in F[X]$ monic irreducible, $m \in \mathbb N$, and $n := \deg(f^m)$. For all $k, s \in \mathbb N$,*
$$n \cdot e_s\left(\{\theta_0(\alpha)^k : \alpha \text{ a root of } f^m \text{ with multiplicity}\}\right) = \sum_{I \subseteq \{0, \dots, n-1\},\ \lvert I\rvert = s} s_{k\sum_{i \in I} q^i}\left(f^m\right)$$
*(`NatDegreeMulEsymmRootsPow.lean:36–59`; wrapper `T.natDegree_mul_esymm_roots_pow'`, `NatDegreeMulEsymmRootsPowStatement.lean:7`). In particular, if $x \in \mathrm{GL}_d(F)$ has $\operatorname{charpoly}(x) = f^m$, then $d\,e^{(k)}_s(x) = \sum_{\lvert I\rvert = s} R_{k\sum_{i \in I} q^i}(x)$.*

*Proof.* Let $\alpha \in \bar F$ be any root of $f^m$. As $f$ is monic irreducible with $f(\alpha) = 0$, $f = \operatorname{minpoly}_F(\alpha)$, the roots of $f$ are $\alpha, \alpha^q, \dots, \alpha^{q^{\deg f - 1}}$ without repetition (`roots_minpoly_eq_map_range`, `FrobeniusTorusMinpolyDegreeRootPowerSum.lean:33`, read in Section 13.4.6), and $\alpha^{q^{\deg f}} = \alpha$ (`minpoly_natDegree_dvd_iff_pow`, `:14`). The roots of $f^m$ are those of $f$ taken $m$ times (`Polynomial.roots_pow`, `Mathlib/Algebra/Polynomial/Roots.lean:282`). Since $i \mapsto \alpha^{q^i}$ has period $\deg f$, the multiset $m \cdot \{\alpha^{q^i} : i < \deg f\}$ equals $\{\alpha^{q^i} : i < m \deg f = n\}$ (`map_range_mul_of_periodic`, `roots_pow_eq_map_range`, `:10–34`). Hence
$$e_s\left(\{\theta_0(\alpha^{q^i})^k\}_{i < n}\right) = \sum_{\lvert I\rvert = s} \prod_{i \in I} \theta_0(\alpha)^{k q^i} = \sum_{\lvert I\rvert = s} \theta_0(\alpha)^{k\sum_{i \in I} q^i}$$
(`Finset.esymm_map_val`, `Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean:73`, and `Finset.prod_pow_eq_pow_sum`; `key`, `:41–52`). The left side does not depend on the root $\alpha$ chosen. Summing the identity over the $n$ roots $\alpha$ of $f^m$ with multiplicity gives $n \cdot e_s(\dots)$ on the left and $\sum_{\lvert I\rvert = s}\sum_\alpha \theta_0(\alpha)^{k\sum_{i \in I} q^i} = \sum_{\lvert I\rvert = s} s_{k\sum_{i \in I} q^i}(f^m)$ on the right (`h2`, `Multiset.sum_map_sum`, `:53–59`). $\square$

**Lemma 13.52 (from the esymm divisibility to period divisibility: `dvd_of_period_of_dvd_sum_powersetCard`).** [Lean, read] *Let $q \ge 2$, $d \ge 1$, $N := q^d - 1$, and let $a : \mathbb N \to \mathbb Z$ be Frobenius-invariant: $k q^i \equiv l \pmod N$ implies $a_k = a_l$. Assume*
$$d \ \Big|\ \sum_{I \subseteq \{0, \dots, d-1\},\ \lvert I\rvert = s} a_{k\sum_{i \in I} q^i} \qquad \text{for all } k, s \in \mathbb N.$$
*Then $s \mid a_l$ for all $s, e, l$ with $s e = d$ and $l q^e \equiv l \pmod N$ (`DvdOfPeriodOfDvdSumPowersetCard.lean:184–280`; wrapper `T.dvd_of_period_of_dvd_sum_powersetCard'`, `DvdOfPeriodOfDvdSumPowersetCardStatement.lean:5`). Its only input outside Mathlib is the orbit-sum lemma `card_dvd_sum_of_invariant_of_card_stabilizer_dvd` (`CardDvdSumOfInvariantOfCardStabilizerDvd.lean:5–34`): if a finite additive group $\Gamma$ acts on a finite set $X$ and $h : X \to \mathbb Z$ is $\Gamma$-invariant with $\lvert\mathrm{Stab}_\Gamma(x)\rvert \mid h(x)$ for all $x$, then $\lvert\Gamma\rvert \mid \sum_{x \in X} h(x)$.*

*Proof.* *The orbit-sum lemma.* Group the sum by orbits (`Finset.sum_fiberwise` over `AddAction.orbitRel`, `:10–12`). On the orbit of $x$ the function is constant equal to $h(x)$ (`hconst`), so the orbit contributes $\lvert\Gamma x\rvert\,h(x)$ (`hcard`). Orbit-stabilizer, $\lvert\Gamma\rvert = \lvert\Gamma x\rvert \cdot \lvert\mathrm{Stab}(x)\rvert$ (`hG`, `:30–32`, through `AddAction.orbitEquivQuotientStabilizer`, `Mathlib/GroupTheory/GroupAction/Quotient.lean:174`, and `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup`, `Mathlib/GroupTheory/Coset/Card.lean:52–53`), together with $\lvert\mathrm{Stab}(x)\rvert \mid h(x)$ gives $\lvert\Gamma\rvert \mid \lvert\Gamma x\rvert\,h(x)$ (`:33–34`).

*Set-up.* The theorem is proved by strong induction on $s$, with $e$ and $l$ generalized (`Nat.strong_induction_on`, `:191`). Fix $s e = d$ and $l$ with $l q^e \equiv l \pmod N$. Write $q^e = m + 1$ with $m \ge 1$. Then $N = (\sum_{j < s}(m + 1)^j)\,m$ by `geom_sum_mul_add` (`Mathlib/Algebra/Ring/GeomSum.lean:109`), and $N \mid l(q^e - 1) = l m$ gives $\sum_{j < s}(m + 1)^j \mid l$, that is,
$$l = k \sum_{j=0}^{s-1}(q^e)^j = k \sum_{x \in \mathrm{killed}(d, s)} q^{x} \qquad \text{for some } k \in \mathbb N$$
(`exists_eq_mul_geom`, `:163–178`; `sum_killed`, `:64–68`). Let $\Gamma := \mathbb Z/d$ act by translation on the set $X$ of subsets of $\mathbb Z/d$, and put $h(I) := a_{k\sum_{x \in I} q^x}$ if $\lvert I\rvert = s$ and $h(I) := 0$ otherwise (`:196–197`).

*Invariance of $h$ (`hmod`, `hhinv`, `:198–206`).* Since $q^d \equiv 1 \pmod N$, we have $q^{(x + g) \bmod d} \equiv q^{x + g} \pmod N$ (`pow_mod_modEq`, `:90–95`), so $(\sum_{x \in I} q^x)\,q^g \equiv \sum_{y \in g + I} q^y \pmod N$ (`sum_vadd_modEq`, `:97–103`). Frobenius invariance of $a$ gives $h(g + I) = h(I)$.

*The total sum (`htot`, `:207–210`).* Under the bijection between $s$-subsets of $\{0, \dots, d-1\}$ and $s$-subsets of $\mathbb Z/d$ (`sum_finset_zmod`, `:137–161`), the hypothesis at $(k, s)$ says $d \mid \sum_{I \in X} h(I)$.

*The orbit of the killed subgroup (`hon`, `:251–261`).* Let $O$ be the orbit of $\mathrm{killed}(d, s)$. Every $I \in O$ has $\lvert I\rvert = s$ and, by invariance, $h(I) = h(\mathrm{killed}(d, s)) = a_l$. Hence $\sum_{I \in O} h(I) = \lvert O\rvert\,a_l$.

*The other orbits (`hoff`, `:212–250`).* Apply the orbit-sum lemma to $h' := h \cdot \mathbf 1_{X \setminus O}$, which is invariant because $O$ is. Let $I \notin O$ with $\lvert I\rvert = s$, let $H := \mathrm{Stab}_\Gamma(I)$, and write $d = \lvert H\rvert\,e'$ (`card_stabilizer_dvd`, `:114–117`). For $x \in I$ we have $x + \mathrm{killed}(d, \lvert H\rvert) = x + H \subseteq I$ (`vadd_killed_subset`, `:105–112`), so $\lvert H\rvert \le s$. If $\lvert H\rvert = s$, then $I = x + \mathrm{killed}(d, s) \in O$, which is excluded (`:245–250`). So $\lvert H\rvert < s$. The element $e' \in \mathbb Z/d$ lies in $H = \mathrm{killed}(d, \lvert H\rvert)$, hence $e' + I = I$ and $(k\sum_{x \in I} q^x)\,q^{e'} \equiv k\sum_{x \in I} q^x \pmod N$ (`:239–244`). The induction hypothesis at $s' = \lvert H\rvert < s$, with $e'$ and $l' = k\sum_{x \in I} q^x$, gives $\lvert H\rvert \mid a_{l'} = h(I)$ (`:238`). Thus $\lvert\mathrm{Stab}(I)\rvert \mid h'(I)$ for every $I$, trivially when $h'(I) = 0$, and the orbit-sum lemma gives $d \mid \sum_I h'(I)$.

*Conclusion (`:262–280`).* Subtracting, $d \mid \lvert O\rvert\,a_l$ (`h1`). By orbit-stabilizer $d = \lvert O\rvert \cdot \lvert\mathrm{Stab}(\mathrm{killed}(d, s))\rvert$ (`hG`, `:268–270`), and $\lvert O\rvert \neq 0$ (`hO0`), so $\lvert\mathrm{Stab}(\mathrm{killed}(d, s))\rvert \mid a_l$. Finally $\mathrm{Stab}(\mathrm{killed}(d, s))$ has exactly $s$ elements (`le_card_stabilizer_killed`, `:119–135`): it contains the subgroup $\mathrm{killed}(d, s)$, and by `vadd_killed_subset` at $x = 0$ it is contained in it. Hence $s \mid a_l$. $\square$

**Lemma 13.53 (length $d$ forces a regular support: `exists_regular_exponent_of_sum_sq_eq`).** [Lean, read] *Let $q \ge 2$, $d \ge 1$, $N := q^d - 1$, and let $a : \mathbb N \to \mathbb Z$ be Frobenius-invariant with $\sum_{k=0}^{N-1} a_k^2 = d$ and with $s \mid a_l$ whenever $s e = d$ and $l q^e \equiv l \pmod N$. Then there is $k$ with $a_k \neq 0$ and $k$ regular (`ExistsRegularExponentOfSumSqEq.lean:5–84`; wrapper `T.exists_regular_exponent_of_sum_sq_eq'`, `ExistsRegularExponentOfSumSqEqStatement.lean:5`). The proof shows more: every $k$ with $a_k \neq 0$ is regular.*

*Proof.* Since $\sum_k a_k^2 = d > 0$, some $a_k \neq 0$ (`:18–22`); the proof keeps this $k$ and shows that it is regular (`:23`). Suppose $k q^i \equiv k$ for some $0 < i < d$, and let $e$ be the least such exponent, so that $0 < e < d$ (`Nat.find`, `:24–30`). Then $k q^{e m} \equiv k$ for all $m$ (`hmul`, `:31–38`). Writing $d = e\lfloor d/e\rfloor + (d \bmod e)$ and using $k q^d \equiv k$, one gets $k q^{d \bmod e} \equiv k$, and minimality of $e$ forces $d \bmod e = 0$ (`hmod`, `:39–46`). Put $s := d/e$, so $s \ge 2$ (`:47–52`). By hypothesis $s \mid a_k$, hence $a_k^2 \ge s^2$ (`hsq`, `:53–55`). On the other hand the residues $k q^i \bmod N$ for $0 \le i < e$ are pairwise distinct: if $k q^i \equiv k q^j$ with $i < j < e$, multiplying by $q^{e-j}$ gives $k q^{i + e - j} \equiv k$ with $0 < i + e - j < e$, against minimality (`key`, `hinj`, `:56–68`). Each of them carries the coefficient $a_k$ by invariance, so
$$e\,a_k^2 = \sum_{i < e} a_{k q^i \bmod N}^2 \le \sum_{l < N} a_l^2 = d = e\,s$$
(`hle2`, `heq`, `:69–80`), hence $a_k^2 \le s$. With $a_k^2 \ge s^2$ and $s \ge 2$ this is impossible (`nlinarith`, `:81–84`). $\square$

**Theorem 13.54 (existence of a regular label: `GlobalTheory.CuspFormula.exists_regular`, its exact supply to the consumers, and the consequences for §§13.4.12–13.4.13).** [Lean, read] *Let $F$ be a finite field with $q = \lvert F\rvert \ge 2$ elements, $d \ge 1$, $N := q^d - 1$, $G := \mathrm{GL}_d(F)$, and let $\theta_0 : \bar F \to \mathbb C$ be multiplicative and injective on $\bar F^\times$ (`(I1)`, Section 13.4.9, supplies one). The theorem inherits, at the reading levels recorded where they are read: `(I2)` (Section 13.4.10); `(I3)` and `(I4)` (used only in part (C)(1)), `(I5)` and the Frobenius covariance `ipGL_rootSum_eq_of_modEq` (Section 13.4.6); `(I6)` (Section 13.4.5); `(I8)` together with Lemmas 13.28 and 13.30 (Section 13.4.10); Lemma 13.44 (Section 13.4.13); vanishing of primitive class functions off primary classes (`classFn_eq_zero_of_charpoly_not_irreducible_pow`, whose proof `EqZeroOfNotPrimary.lean` is read in Section 13.4.6); the realization (Q3) (Proposition 13.6); and the Schur relations for irreducible characters, `pair_self_of_isIrrChar_algClosed` and `pair_eq_zero_of_isIrrChar_ne` (Section 13.4.10; the second rests on Mathlib's `Representation.char_orthonormal`).*

- **(A) Statement (`ExistsLabel.lean:49–54`).** *Let $\chi : G \to \mathbb C$ be an irreducible character (`IsIrrChar ℂ ℂ χ`) with `IsPrimitive (extZero χ)`. Then there is a regular $k \in \mathbb N$ such that for all $x \in G$*
  $$\chi(x) = (-1)^{d-1}\,\psi_{s_k}\left(\operatorname{toLin}'(x)\right).$$
- **(B) Exact supply to the three call sites.** *`exists_regular` is called exactly three times in the archive:*
  1. *`LabelMapNonempty.exists_label` (`LabelMapNonempty.lean:18–81`), the exhaustion leg of Theorem 13.40(B), item 3. The call at `:22–23` takes $\theta_0 = $ `C.ι` with `C.ι_inj`, $\chi = $ `τ.character`, irreducibility from `isIrrChar_of_norm_one _ h.1` and primitivity from `isPrimitive_of_isCuspChar _ h` (Lemma 13.43(4)), where `h := isCuspChar_character τ hs hc`. **Both conclusions are used.** The regularity `hreg` gives $\deg\operatorname{minpoly}_K(C.\mathrm{gen}(d)^k) = d$ at `:35–41`, through Lemma 13.44(1), and the identity `hchar` gives the elliptic clause of `HasCuspLabel C τ (minpoly K (C.gen d ^ k))` at `:51–81`.*
  2. *`finrank_of_simple_cuspidal` (`CuspidalParametrization.lean:50–71`), the degree in Theorem 13.40(B), item 1. The call at `:55–56` has the same arguments for an arbitrary lift $\theta$ and **discards the regularity** (`obtain ⟨k, -, hk⟩`). Only the value of the identity at $x = 1$ is used (`:57`), together with `(I2)` and the additivity of $s_k$ (`:61–62`) and the sign identity $(-1)^{d-1}\prod_{i=1}^{d-1}(1 - q^i) = \prod_{i=1}^{d-1}(q^i - 1)$ (`:63–67`), to obtain $\dim\tau = \prod_{i=1}^{d-1}(q^i - 1)$. Any $k$, regular or not, would serve here.*
  3. *`UpperTheory.Gal.InertialTypesAlt.cuspChar : CuspChar` (`PCuspChar.lean:55–83`; Definition 13.10(4)). Irreducibility comes from `T.isCharacterOverSubfield_of_representation` (`hc.2 hirr`, `:59, 79`; Section 13.4.11). Primitivity is built from `FinCusp κ` (`hprim`, `:60–78`): for each $0 < a < m$, Lemma 13.43(1) supplies $H = \mathrm{unipBlock}(m, a)$; `rad_le` (`:40–53`) shows that the unipotent radical of the two-block parabolic `stdBlocks ![a, m - a]` lies in $H$; an $H$-fixed vector is therefore fixed by that radical and vanishes by `FinCusp κ` (`hfix`, `:72–73`); `sum_char_eq_zero` gives $\sum_{u \in H}\operatorname{tr}\kappa(u) = 0$ (`:74–78`); and the statement wrapper of Lemma 13.43(4), `T.isPrimitive_extendZero_of_sum_unipotentRadical`, converts these vanishing sums into `IsPrimitive (extZero χ)` (`:62`). **Both conclusions are used verbatim**, as `Reg (Nat.card F) m k` and as the trace formula `cusp θ m k x` (`:79–83`). The predicate `CuspChar` is consumed in turn by `lblOf_holds` (`TypeOfLblHolds.lean:111–112`), which we do not read.*
- **(C) Consequences for Sections 13.4.12–13.4.13.** *(1) With $k$ as in (A), the Gram vector of $\chi$ is $a_l = (-1)^{d-1}$ for $l$ in the Frobenius orbit $\{k q^i \bmod N : i < d\}$, which has $d$ elements, and $a_l = 0$ otherwise. One may take $k < N$. (2) Theorem 13.46(A2), the signed single-orbit root sum and the central twist, holds without its hypothesis, relative to the inputs listed above. (3) Interface **(U1)** of Tables 13.4.12 and 13.4.13 is discharged to conditional `R3 [Lean, read]`. The interfaces **(U3)** and **(U4)** of Table 13.4.12 are not affected.*

*Proof of (A).* We follow `ExistsLabel.lean:55–128`.

*Step 0: bookkeeping (`:55–62`).* $\chi$ is a genuine character (`isCharacter_of_isIrreducibleCharacter_complex`, which drops irreducibility; `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:22–24`), hence a virtual character (`hv`). From Lemma 13.30 (`T.generalLinearFunctionExtendZeroEnd_properties`, `:58`) we use part (1), $\operatorname{extZero}\chi(\operatorname{toLin}'x) = \chi(x)$ (`hval`); part (3), $\mathrm{ipGL}(\varphi, \varphi') = \sum_{x \in G}\varphi(\operatorname{toLin}'x)\,\overline{\varphi'(\operatorname{toLin}'x)}$ (`hip`); and part (4), which makes `extZero χ` a class function (`hc`, `:59`) because $\chi$ is one (`T.isCharacterOverSubfield_restrict_classFunction_one`, Section 13.4.10). Moreover $\dim_F F^d = d$ (`hr`), $\lvert G\rvert \neq 0$ in $\mathbb C$ (`hg`, `generalLinearGroupCardComplex_finiteField_ne_zero`, `EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:27–29`), and $q \ge 2$ (`hq`).

*Step 1: the Gram vector and its length (`:63–65`).* Lemma 13.44(2) (`T.exists_int_coeff_primitive_GL_character`) gives $a : \mathbb N \to \mathbb Z$ with $\mathrm{ipGL}(\operatorname{extZero}\chi, R_k) = a_k\,\lvert G\rvert$ for all $k$ (`ha`). Lemma 13.44(3) (`sum_coef_mul_eq_pair`) with $\chi' = \chi$ and $b = a$ gives $\sum_{k < N} a_k^2 = d \cdot \mathrm{pair}(\chi, \chi)$, and Schur's lemma over $\mathbb C$ gives $\mathrm{pair}(\chi, \chi) = 1$ (`T.finiteGroupFunctionPairing_self_irreducible_algClosed`). Hence $\sum_{k < N} a_k^2 = d$ (`haa`).

*Step 2: Frobenius invariance (`hinv`, `:66–70`).* If $k q^i \equiv l \pmod N$, the Frobenius covariance (`T.innerProduct_rootPowerSum_eq_of_frobenius_modEq`, lemma `CuspGL.ipGL_rootSum_eq_of_modEq`, Section 13.4.6), applied to the primitive class function `extZero χ` on $F^d$ with $\dim F^d = d > 0$, gives $a_k\,\lvert G\rvert = a_l\,\lvert G\rvert$, hence $a_k = a_l$.

*Step 3: the esymm divisibility (`hdvd`, `:71–99`).* Fix $k$ and $s$. By Lemma 13.50 in the form stated after it, $e^{(k)}_s$ is a virtual character, so the integrality of pairings of virtual characters (`T.virtualCharacter_inner_eq_int_mul_card`, Lemma 13.44(2)) gives $m \in \mathbb Z$ with $\sum_{x \in G}\chi(x)\,\overline{e^{(k)}_s(x)} = m\,\lvert G\rvert$ (`hm`, `:73`). We claim
$$\Big(\sum_{\lvert I\rvert = s} a_{k\sum_{i \in I} q^i}\Big)\,\lvert G\rvert = d \cdot m\,\lvert G\rvert \qquad (\text{`key`, `:76–97`}).$$
Expand each $a_{k\sum_{i \in I} q^i}\,\lvert G\rvert$ by `ha` and part (3) of Lemma 13.30, interchange the two sums (`Finset.sum_comm`), and compare the summands at each $x \in G$. On the left the summand is $\chi(x)\,\overline{\sum_{\lvert I\rvert = s} R_{k\sum_{i \in I} q^i}(x)}$. If $\operatorname{charpoly}(x) = f^{m'}$ is primary, with $f$ monic irreducible and $m' > 0$ (`hx`, `:86–94`), then Lemma 13.51 with $\deg f^{m'} = d$ turns the inner sum into $d\,e^{(k)}_s(x)$. Otherwise `classFn_eq_zero_of_charpoly_not_irreducible_pow`, applied to the primitive class function `extZero χ` (`:95–97`), gives $\chi(x) = \operatorname{extZero}\chi(\operatorname{toLin}'x) = 0$, and both summands vanish. Summing over $x$, the left side equals $d\sum_x \chi(x)\,\overline{e^{(k)}_s(x)} = d\,m\,\lvert G\rvert$. Cancelling $\lvert G\rvert$ proves $d \mid \sum_{\lvert I\rvert = s} a_{k\sum_{i \in I} q^i}$ (`:98–99`).

*Step 4: a nonzero regular coefficient (`:100–102`).* Lemma 13.52, with Steps 2 and 3 as hypotheses, gives $s \mid a_l$ whenever $s e = d$ and $l q^e \equiv l \pmod N$. Lemma 13.53, with Steps 1 and 2 and this divisibility, produces $k$ with $a_k \neq 0$ and $k$ regular (`hk0`, `hk`). This $k$ is the label.

*Step 5: $(-1)^{d-1}\psi_{s_k}$ is an irreducible character (`:103–110`).* By (Q3) (`T.isCharacter_cuspidal_rootSum_regular`), $\chi' := (-1)^{d-1}\psi_{s_k} \circ \operatorname{toLin}'$ is a genuine character (`h'`) and $\mathrm{ipGL}(\psi_{s_k}, \psi_{s_k}) = \lvert G\rvert$ (`hn`). Since the two signs cancel (`hsq`), $\sum_x \chi'(x)\,\overline{\chi'(x)} = \lvert G\rvert$, and `(I8)` in the form of Lemma 13.29(3) (`T.irreducible_of_virtualCharacter_norm_one`, second clause, for the genuine character $\chi'$) gives `IsIrrChar ℂ ℂ χ'` (`hi'`).

*Step 6: $\chi = \chi'$ by orthogonality (`:111–128`).* Suppose $\chi \neq \chi'$. Distinct irreducible characters are orthogonal: $\mathrm{pair}(\chi, \chi') = \lvert G\rvert^{-1}\sum_x \chi(x)\,\chi'(x^{-1}) = 0$ (`T.finiteGroupFunctionPairing_eq_zero_of_distinct_irreducible`, the wrapper of `pair_eq_zero_of_isIrrChar_ne`, Section 13.4.10). As $\lvert G\rvert^{-1} \neq 0$, the sum vanishes (`:115–117`). On the other hand `(I5)` (`T.invertibleEndomorphismInnerProduct_primitive_mobiusInverse`), applied to the additive function $s_k$ (`T.rootPowerSumCharacter_additive_and_X_sub_one_pow`, first clause) and the primitive `extZero χ`, gives $\mathrm{ipGL}(\operatorname{extZero}\chi, \psi_{s_k}) = \mathrm{ipGL}(\operatorname{extZero}\chi, R_k) = a_k\,\lvert G\rvert$ (`h1`, `:113–114`). By Lemma 13.28 (`T.star_virtualCharacter_eq_apply_inv`), $\chi'(x^{-1}) = \overline{\chi'(x)}$ for the virtual character $\chi'$, so
$$\sum_{x \in G}\chi(x)\,\chi'(x^{-1}) = (-1)^{d-1}\sum_{x \in G}\operatorname{extZero}\chi(\operatorname{toLin}'x)\,\overline{\psi_{s_k}(\operatorname{toLin}'x)} = (-1)^{d-1}\,a_k\,\lvert G\rvert \qquad (\text{`h2`, `:118–126`}).$$
This is nonzero because $a_k \neq 0$ and $\lvert G\rvert \neq 0$ (`:128`), a contradiction. Hence $\chi = \chi'$. $\square$

*Proof of (B).* The three call sites were read at the lines given in the statement: `LabelMapNonempty.lean:18–81`, `CuspidalParametrization.lean:50–71` and `PCuspChar.lean:40–83`. A search of the archive's `src/` tree for `CuspFormula.exists_regular` returns exactly these three calls and the definition. The other declarations named `exists_regular` in the archive belong to unrelated namespaces. `CuspFormula.exists_label` (`ExistsLabel.lean:187–202`), in the same file, does not call `exists_regular`: it turns a regular $k$ into a root $x$ with $\theta_0(x) = \mathrm{rootC}^k$ and $\deg\operatorname{minpoly}(x) = d$, and it is not used in this subsection. $\square$

*Proof of (C).* (1) By `(I4)`, $\mathrm{ipGL}(\psi_{s_k}, R_l) = \lvert G\rvert \cdot \#\{i < d : k q^i \equiv l \pmod N\}$, and part (3) of Lemma 13.30 identifies $\mathrm{ipGL}$ with the pairing on $G$. For regular $k$ the residues $k q^i$ with $i < d$ are pairwise distinct: if $k q^i \equiv k q^j$ with $i < j < d$, multiplying by $q^{d-j}$ gives $k q^{i + d - j} \equiv k$ with $0 < i + d - j < d$. So the count is $1$ on the orbit and $0$ elsewhere. Reducing $k$ modulo $N$ changes neither the regularity condition nor $\psi_{s_k}$ on $G$. Both $\psi_{s_k}$ and $\psi_{s_{k \bmod N}}$ are primitive by `(I3)`, since $s_k$ is additive, so both vanish off primary classes. On a primary class the eigenvalues lie in $\mathbb F_{q^{\deg f}}^\times$ with $\deg f \mid d$, so they have order dividing $N$. (2) Theorem 13.46(A2) obtained $\chi = (-1)^{d-1}\psi_{s_{k_0}}$ from `exists_regular` (`LabelMapNonempty.lean:22–23`), and its remaining steps used only `(I3b)` and Lemma 13.38. (3) follows from (A), (B) and the reading levels of the inherited inputs. $\square$

---

#### Remarks

1. *Classical provenance: Adams operations and Serre's Exercises 9.2–9.4.* Lemma 13.50 is the finite-group case of a classical fact. Serre `[SerreLinearReps]`, Chapter 9, Exercise 9.3 (p. 69), sets $\psi^k(f)(s) := f(s^k)$ for a class function $f$, introduces the generating series $\sigma_T(\chi)$ and $\lambda_T(\chi)$ of the symmetric and exterior powers of a representation $\rho$ with character $\chi$, asks for $\sigma_T(\chi)(s) = 1/\det(1 - \rho(s)T)$ and $\lambda_T(\chi)(s) = \det(1 + \rho(s)T)$, and deduces Newton-type formulas that express $n\,\lambda^n(\chi)$ through $\psi^1(\chi), \dots, \psi^n(\chi)$ and lower $\lambda$'s. Part (b) concludes that $R(G)$ is stable under every $\psi^k$. Exercise 9.2 is the classical form of `(I8)`: an element of $R(G)$ is an irreducible character if and only if it has norm one and its degree is not negative. Exercise 9.4(a) adds that $\psi^n(\chi)$ is irreducible when $n$ is prime to $\lvert G\rvert$. Serre's formulas recover the $\psi^k$ from the $\lambda$'s with integer coefficients. The opposite recursion, which Lemma 13.50 needs, divides by $n$. The archive avoids this division inside $R(G)$: Step 2 divides pointwise in $\mathbb C$, and Step 4 then has integer coefficients once $\varphi$ is written as $\chi_A - \chi_B$ in Step 3. In the language of $\lambda$-rings (the $\lambda$-ring $R(G)$ is the subject of `[AtiyahTall1969]`, which we cite as a bibliographic pointer only and have not read), Lemma 13.50 says that the $\lambda$-operations of the $\lambda$-ring $R(G)$ are computed by elementary symmetric functions of any multiset-valued function whose power sums reproduce the Adams images of a virtual character. In the application $R_k(g) = R_1(g^k)$, so $R_k = \psi^k(R_1)$, and Serre's Exercise 9.3(b) would derive `(I6)` for every $k$ from the case $k = 1$. The archive instead proves `(I6)` uniformly in $k$ (Proposition 13.11).
2. *Green's route to (Q1): completeness by counting.* In `[Green1955]` the cuspidal characters occur among the primary irreducible characters of Theorem 12 (p. 439). That every irreducible character, in particular every cuspidal one, is in Green's list is part of Theorem 13 (stated on p. 439). It is proved by counting on p. 440: Lemmas 1.1 and 7.7 give exactly as many of the constructed characters as conjugacy classes, so it suffices to show that they are irreducible and distinct, and then there can be no others. Theorem 14 (pp. 443–444) collects the classification. In Green's account, (Q1) is therefore a consequence of the completeness of the whole character table. `exists_regular` proves (Q1) without counting classes or knowing the rest of the character table. It uses the Gram vector of the one character $\chi$, the integrality of its pairings with the esymm virtual characters, and the realization (Q3) for the single exponent it finds.
3. *Why Lemma 13.52 needs its orbit-stabilizer detour.* For $d$ prime the lemma is almost trivial. The only subgroups of $\mathbb Z/d$ are $0$ and $\mathbb Z/d$, every $s$-subset with $0 < s < d$ has trivial stabilizer and an orbit of size $d$, and the only nontrivial case $s = d$, $e = 1$ is the hypothesis at $s = d$ itself, $d \mid a_{k(1 + q + \dots + q^{d-1})}$. For composite $d$ (Example 13.49) subsets with intermediate stabilizers occur, and their coefficients are controlled only through the induction hypothesis at the smaller $s' = \lvert\mathrm{Stab}(I)\rvert$. This is why the formal proof is a strong induction on $s$ with $e$ and $l$ generalized (`:191`).
4. *How Sections 13.4.13 and 13.4.14 divide the work.* Both sections start from the Gram vector of Lemma 13.44 and use it for different statements. Section 13.4.13 proves determination: two cuspidal characters that agree on elliptic classes coincide (Theorem 13.46(B)). Its proof uses Parseval separation and no esymm divisibility. This section proves existence (Q1), using esymm divisibility and no Parseval separation. `ExistsLabel.lean:22` imports `EqOfIsPrimitiveOfEqOnEllipticFiniteGL` only for three helpers: `isCharacter_of_isIrreducibleCharacter_complex`, `generalLinearGroupCardComplex_finiteField_ne_zero`, and the inner-product law `sum_coef_mul_eq_pair` of Lemma 13.44(3), used at `:56`, `:61` and `:64`. The file does not mention `eq_of_isPrimitive_of_eq_on_elliptic` or `cuspElliptic_statement`. Conversely, Theorem 13.46(A2) is a corollary of Theorem 13.54. Nothing in the two sections is circular.
5. *What stays at statement level.* The following stay at statement level: the interfaces **(U3)** and **(U4)** and the Mackey and Whittaker interfaces of Table 13.4.12; on the path of the third consumer, `FinCusp`, `sum_char_eq_zero`, `CuspMax.mem_unipRad_iff_entries`, `CuspMax.unipRad_ne_bot_iff`, and the consumer `lblOf_holds` with the inertial-type chain behind it; and the deeper monomial-basis and trace-comparison inputs inside `(I6)`, which remain the named `[Lean]` / `[Open]` items of Section 13.4.5. Of the other theorems of `ExistsLabel.lean`, `cuspVal_eq_psi` (`:132–185`) was read in Section 13.4.9, and `CuspFormula.exists_label` (`:187–202`) is off the path of this subsection. Reading the source and building the book is not a Lean kernel check. The `R3` tag records that the prose was checked against the pinned proof text, and every inherited input keeps the reading level recorded where it is read.

**Table 13.4.14 (source-to-text map for §13.4.14; per-file byte SHA-256s in `SOURCE-MAP.md`).** Paths are relative to `lean/` in the pinned archive (`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`); `DP/` denotes `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/` and `CT/` denotes `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/`.

| Reading / tag | Declaration(s) | Archive or Mathlib path and lines | Role in §13.4.14 |
|---|---|---|---|
| Definitions / `[Lean, read]` | `killed`, `mem_killed`, `killed_eq_image`, `val_mul`, `injOn_mul`, `card_killed`, `sum_killed`, `mem_iff_mem_killed`; `Reg`, `psiG`, `cusp`; `CuspChar` | `DP/DvdOfPeriodOfDvdSumPowersetCard.lean:10–88`; `src/Development/AbelianVarietyTheory/Definitions/Divisors/OrthSubrepresentation.lean:150, 184–190`; `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/RegularSemisimpleFibres/ResEmbCompat.lean:108–111` | Definition 13.10 |
| R3 / `[Lean, read]` | `esymm_zero'`, `esymm_cons_succ`, `coeff_prod_one_add`, `esymm_add`, `esymm_eq_of_psum_eq`, `one_mem_virt`, `esymm_add_mem_virt`, `exists_multisets`, `EsymmVirt.esymm_mem_virt`; `CuspFormula.esymm_mem_virt` (+ wrapper); `isChar_mem_virt_complex` | `DP/EsymmMemVirtualCharactersOfPowerSumEigenvalues.lean:13–129`; `DP/EsymmMemVirtualCharactersOfPowerSumEigenvaluesStatement.lean:7`; `DP/ExistsLabel.lean:38–47`; `CT/VirtualCharactersMulComapConjIndLinear.lean:11–13` | Lemma 13.50 |
| R3 / `[Lean, read]` | `map_range_mul_of_periodic`, `roots_pow_eq_map_range`, `natDegree_mul_esymm_roots_pow` (+ wrapper) | `DP/NatDegreeMulEsymmRootsPow.lean:10–59`; `DP/NatDegreeMulEsymmRootsPowStatement.lean:7` | Lemma 13.51 |
| R3 / `[Lean, read]` | `card_dvd_sum_of_invariant_of_card_stabilizer_dvd`; `pow_mod_modEq`, `sum_vadd_modEq`, `vadd_killed_subset`, `card_stabilizer_dvd`, `le_card_stabilizer_killed`, `sum_finset_zmod`, `exists_eq_mul_geom`, `dvd_of_period_of_dvd_sum_powersetCard` (+ wrapper) | `DP/CardDvdSumOfInvariantOfCardStabilizerDvd.lean:5–34`; `DP/DvdOfPeriodOfDvdSumPowersetCard.lean:90–280`; `DP/DvdOfPeriodOfDvdSumPowersetCardStatement.lean:5` | Lemma 13.52 |
| R3 / `[Lean, read]` | `exists_regular_exponent_of_sum_sq_eq` (+ wrapper) | `DP/ExistsRegularExponentOfSumSqEq.lean:5–84`; `DP/ExistsRegularExponentOfSumSqEqStatement.lean:5` | Lemma 13.53 |
| R3 / `[Lean, read]` | `GlobalTheory.CuspFormula.exists_regular`; helpers `isCharacter_of_isIrreducibleCharacter_complex`, `generalLinearGroupCardComplex_finiteField_ne_zero`; call sites in `LabelMapNonempty.exists_label`, `finrank_of_simple_cuspidal`, `InertialTypesAlt.cuspChar` (with `blk_two`, `blk_lt_iff`, `rad_le`) | `DP/ExistsLabel.lean:49–128`; `CT/EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:22–29`; `src/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/LabelMapNonempty.lean:18–81`; `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalParametrization.lean:50–71`; `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/RegularSemisimpleFibres/PCuspChar.lean:15–83` | Theorem 13.54 |
| `[Lean]` (Mathlib, pin `0df444a`) | `Multiset.esymm`, `Finset.esymm_map_val`; `Multiset.powersetCard_cons`; `Polynomial.roots_pow`; `geom_sum_mul_add`; `MulAction.orbitEquivQuotientStabilizer` (additive form); `Subgroup.card_eq_card_quotient_mul_card_subgroup` (additive form); `Representation.char_orthonormal` | `Mathlib/RingTheory/MvPolynomial/Symmetric/Defs.lean:70, 73`; `Mathlib/Data/Multiset/Powerset.lean:260`; `Mathlib/Algebra/Polynomial/Roots.lean:282`; `Mathlib/Algebra/Ring/GeomSum.lean:109`; `Mathlib/GroupTheory/GroupAction/Quotient.lean:174`; `Mathlib/GroupTheory/Coset/Card.lean:52–53`; `Mathlib/RepresentationTheory/Character.lean:134` | Lemmas 13.50–13.52, Theorem 13.54 (Step 6) |
| Inherited `R3` | `(I2)`, `(I3)`, `(I4)`, `(I5)`, Frobenius covariance `ipGL_rootSum_eq_of_modEq`, `(I6)` (with `isChar_esymm_roots_charpoly`, `multiset_newton_psum`, `roots_charpoly_pow`, `virt_mul_comap_conj_ind_linear`, `matrixChar_iff_isChar`, `roots_minpoly_eq_map_range`, `minpoly_natDegree_dvd_iff_pow`), `(I8)`, Lemmas 13.28 and 13.30, `classFn_eq_zero_of_charpoly_not_irreducible_pow`, `isCharacter_cuspidal_rootSum_regular`, Lemma 13.44, `T.isCharacterOverSubfield_of_representation`, `isIrrChar_of_norm_one`, `isPrimitive_of_isCuspChar`, `isPrimitive_extZero_of_sum_unipotent` | Sections 13.4.4–13.4.13 | Cited without re-proof |
| Statement level / `[Lean]` | **(U3)**, **(U4)** and the Mackey and Whittaker interfaces (Table 13.4.12); `FinCusp`, `sum_char_eq_zero`, `CuspMax.mem_unipRad_iff_entries`, `CuspMax.unipRad_ne_bot_iff`, `lblOf_holds`; deeper inputs inside `(I6)` (Section 13.4.5) | `LabelMapNonempty.lean:108`; `PCuspChar.lean:44, 68, 74`; `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/RegularSemisimpleFibres/TypeOfLblHolds.lean:111–112` | Named inputs kept; **(U1)** itself is discharged by Theorem 13.54 |
| Our check | `verify_regular_label_existence.py`: 28,301 exact assertions covering the 44 cited archive files and their declaration lines, Examples 13.47–13.49 over $\mathbb Q(\zeta_3)$ and $\mathbb Q(\zeta_8)$, primitivity on $\operatorname{End}(\mathbb F_q^2)$, and the $\mathbb Z/d$ orbit bookkeeping for $(d, q) \in \{(4, 2), (6, 2), (4, 3)\}$ | Run certificate (`sources/SOURCES.md`, Part I §7) | Exact computational check (not a Lean kernel check) |

## 13.5 Remarks, formalization notes, and Masullo's counterpart

### 13.5.1 Ongoing community pruning and dead-code removal

Because `OpenLiteratureStatements` was assembled during rapid AI-assisted iteration (`remark.pdf` pp. 2–4
[Paper]), it carries visible evolutionary scaffolding: unused `True` slots (`UnusedSlot72` plus seven
internal `True` predicates outside `Published`), discarded hypotheses (`BlochKatoLocal` and `GreenbergWiles`
introduced as `_` in two closing lemmas), and thin wrapper files (`[Community]`, `LUMI doc 07`). Look at
the community repository `leanprover-community/riemann-hypothesis` (`CONTRIBUTIONS.md` [Community]):
recall James Shore's kernel-term walk showing that `src/Main.lean` uses **146,287 of 175,187 files (83.5%)**
and **61.8% of source lines**, and active pull requests (through issue/PR #59 as of 2026-11-22 00:02 UTC, and PR #65 by 03:30 UTC) are
already pruning unreferenced declarations and collapsing 24,000+ single-declaration re-export wrappers
without changing a single kernel axiom!

### 13.5.2 Masullo's counterpart: 396 pages of human-written Appendices A–E

How does Masullo's 940-page human-written manuscript *The Music of the Primes* handle its foundational
literature layer [Paper; Masullo pp. 5, 537–932]? By devoting **Appendices A through E (pp. 537–932 —
396 pages, or 42.1% of the entire manuscript!)** to background expositions and customized foundational
preparations:

- **Appendix A ("Preparations from Algebraic Number Theory", pp. 537–586):** Topology of $\mathbb A_F$
  and $\mathrm{GL}_1(\mathbb A_F)$, fundamental domains, Tamagawa measures, Dirichlet's $S$-unit theorem
  by lattice point counting, and an idelic Hardy–Littlewood maximal / Lebesgue differentiation theorem;
- **Appendix B ("Preparations from Analytic Number Theory", pp. 587–654):** Phragmén–Lindelöf convexity
  bounds, asymptotic Cauchy and residue theorems, Weil explicit formulas for Hecke $L$-functions,
  Kronecker–Weyl equidistribution, classical zero-free regions, and partial Euler products on $\Re s = 1$;
- **Appendix C ("Preparations on locally convex topological vector spaces", pp. 655–742):** Strict
  LF-spaces, Grothendieck nuclearity and nuclear operators, Pettis integration, and vector-valued
  meromorphic functions;
- **Appendix D ("Schwartz–Bruhat functions", pp. 743–822):** Bruhat's theory on locally compact abelian
  groups, modulated groups, and $I$-exponentially decaying Schwartz–Bruhat spaces $\mathcal S_I(G)$;
- **Appendix E ("Topological stacks", pp. 823–932):** Compactly generated weakly Hausdorff spaces,
  topological groupoids, and $2$-categorical stacks (used for periodic-orbit bookkeeping in Chapter 8).

Notice the mirror-image trade-off between the two releases (which we will compare systematically in
Part IV, Chapters 14–16) [Expository]: Masullo cites classical monographs (such as Cassels–Fröhlich,
Iwaniec–Kowalski, and Treves) for standard theorems while writing 396 pages of human prose to adapt
functional-analytic and stack-theoretic preliminaries (currently undergoing community Lean formalization
and errata logging in `mccorvie/riemann-masullo`, `ERRATA.md` [Community]); Alpöge's archive contains
zero prose, proves all ~182 named `GlobalTheory.Published.*` propositions from Mathlib inside a
151,285-module machine-checked cone, and leaves human mathematicians the task of reading and extracting
what it proved!

---

## 13.6 Lean counterpart for this chapter

| Declaration | File:line | Mathematical content / role in Sections 13.3–13.4 | Tag |
|---|---|---|---|
| `Gn`, `Mt`, `ip`, `zOf`, `InPar`, `hc`, `res`, `hcL`, `IsCusp`, `LabelDatum`, `thetaOf`, `IsPrimeLab`, `IsCuspOf`, `HasLabel`, `eSerC`, `GlobalTheory.GLq.Green`, `ESerTie` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LabelDatum.lean:11,13,22,27,36,45,47,55,64,81,88,91,93,98,102,108,114` | Definition 13.1: finite $\mathrm{GL}_n(\mathbb F_g)$ Harish-Chandra induction, Jacquet restriction, cuspidality, Teichmüller labels, and Green's classification predicate `Green` (import cone 199). | [Lean, read] |
| `IsRegularChar`, `GlobalTheory.Published.GreenRegularCharacters` | `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:10,13` | Section 13.2.2 & Proposition 13.1: regular characters $\theta : \mathbb F_{g^d}^\times \to \mathbb C^\times$ ($\theta^{g^i} \neq \theta^{g^j}$) and Green's cuspidal character parameterization over $\mathbb F_g$ (cone 200). | [Lean, read] |
| `exists_unit_gen`, `orderOf_uu`, `th`, `th_pow`, `th_inj`, `th_surj`, `pow_inj`, `rootOf`, `root_unit`, `regular_iff`, `sum_range_eq_roots`, `thetaOf_pow`, `GlobalTheory.GreenBridge.green_of_regular` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumRangeEqRoots.lean:53,83,119,137,142,148,180,187,197,207,213,218,225` | Proposition 13.1: complete formal proof deriving polynomial-labeled `Green` from `GreenRegularCharacters` via Galois-orbit symmetry (cone 232). | [Lean, read] |
| `GlobalTheory.greenRegularCharacters_holds`, `family`, `factor_lab`, `prod_factors`, `count` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProof.lean:18,23,35,48,56,137` | Proposition 13.8: the producer of `GreenRegularCharacters`; exhaustion by counting cuspidal multisets against the $g^d - g^{d-1}$ monic polynomials with nonzero constant term (the conditional bound is read in §13.4.8). | [Lean, read] |
| `GlobalTheory.GreenRegular.exists_cusp_of_regular`; `GlobalTheory.ParamLabel.isCusp_psi`; `GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:65`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean:92` | Proposition 13.6: $\tau_\theta = (-1)^{d-1}\psi_{s_k}$, the invariant-subspace Möbius inverse of a root power sum; cuspidality, degree, elliptic values and orbit equivalence from the inputs (I1)–(I8), with (I6), (I4)–(I5), (I7), and (I1) read at the conditional depths of §§13.4.5–13.4.7 and §13.4.9. | [Lean, read] |
| `CuspGL.TeichEmb.exists_teichmuller`; `WittVector.teichmuller`; `ParamLabel.isCuspOf_cuspOn`; `GoodCharsCompare.exists_beta`, `exists_ext`; `GLq.Model.datumOf` | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:24`; `Mathlib/RingTheory/WittVector/Teichmuller.lean:93`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:102`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspidalCharacterFormula.lean:74,312`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemRootsBarXSubC.lean:209` | Section 13.4.9: conditional `(I1)` Witt-vector Teichmüller supply, zero-extension, `ParamLabel` bridges, and label permutations under change of embedding (`WittVector.instIsDomain`/`equiv`/`IsAlgClosed.lift` [Lean]; `cuspVal_eq_psi` conditional on the inputs in Table 13.4.9). | [Lean, read] |
| `GlobalTheory.CuspGL.psi_one`, `QBinomialSum.sum_gaussian_mul_prod`, `SubspaceNumber.card_subspaces_mul`; `GlobalTheory.BI.irr_of_norm_one`, `BI.virt_expand`; `GlobalTheory.CuspGL.star_virt_eq_inv`; `GlobalTheory.CuspGL.extZero_spec`; `BI.exists_irrChar_add`, `BI.isChar_zero_and_add` | `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIco.lean:74`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumGaussianMulProd.lean:63`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/CardSubspacesOfFinrankMulCardBases.lean:32`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrreducibleOfVirtualCharacterNormOne.lean:57`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/VirtualCharacterIrreducibleExpansionNormSq.lean:67`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/StarVirtualCharacterEqApplyInv.lean:10`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/GeneralLinearFunctionExtendZeroEndProperties.lean:87`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsIrrCharAdd.lean:47`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterOverSubfieldZeroAndAdd.lean:27` | Sections 13.4.10–13.4.11: the identity value $\prod_{i=1}^{d-1}(1-q^i)$, the virtual-character integral expansion (Proposition 13.35), the norm-one lattice fact, inverse equals conjugate, `extZero_spec`, and selection of the positive sign (Theorem 13.31). | [Lean, read] |
| `UpperTheory.Zero.LLC.nameLaws`, `UpperTheory.Zero.LLC.pin`, `UpperTheory.Zero.LLC.nameCentral`, `parEx`, `parUniq`; `PM.greenCuspidal`, `GreenAll.cuspParam_all`, `exists_cuspidal_label`, `hasCuspLabel_unique`, `LabelUniqueAll.label_eq`; `GreenSeries.green_series`, `cuspParam_of_green`, `exists_perm_deg`, `exists_perm`, `eSer_eq` | `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/NameLaws.lean:78`; `…/PairCheckThreeTwo.lean:177`; `…/NameCentral.lean:54`; `…/CentralUnit.lean:39`; `…/ParUniq.lean:15`; `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/HarishChandraModules.lean:12`; `src/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/GreenCuspLabels/GreenCuspidal.lean:303`; `src/Development/WeilBound/CoreStatements/FiniteTypeHarishChandra/LabelMapNonempty.lean:122`; `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCuspidalWithLabel.lean:57`; `…/CuspidalLabelUnique.lean:360`; `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CuspidalLabelPolynomialUniqueAllPrimes.lean:103`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdFactorsOfMonic.lean:243`; `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/CuspParamOfGreenParametrisation.lean:106`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/AdmissibleLabelWeightsOfGreenCuspidalParametrisa.lean:50,89,233` | Section 13.4.12: coordinate-free naming laws and Parseval-plus-shift pinning for Chapter 12 (`P15`), representation-level `GreenCuspidal`, all-primes Newton power-sum uniqueness, convention-change permutations, and exact three-clause dependency split across `green_series`, `cuspParam_of_green`, and `eSer_eq` (named interfaces in Table 13.4.12; `(U2)` discharged in §13.4.13). | [Lean, read] |
| `CuspElliptic.Statement`, `GlobalTheory.CuspGL.cuspElliptic_statement`, `isIrrChar_of_norm_one`, `isPrimitive_of_isCuspChar`; `exists_unip_bijOn_nilRad`, `char_coset_sum_eq_zero`, `charpoly_block`, `isPrimitive_extZero_of_sum_unipotent`; `regular_iff_natDegree_and_exists_elliptic`, `exists_int_coeff_of_isPrimitive`, `sum_coef_mul_eq_pair`, `character_elliptic_eq_coeff_sum_lemma`, `eq_of_isPrimitive_of_eq_on_elliptic`; `orthogonal_int_vectors_not_agree_on_regular`, `parsevalSep_bound`, `sep_numerical_ineq`, `no_norm_eight_of_fourier_vanishing_order_fifteen`, `no_norm_twelve_order_sixtythree` | `src/Formalism/UnipotentAdelicQuotients/CuspEllipticValues.lean:22`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IrrCharEqOneOfSubsingleton.lean:26,34,45`; `…/ExistsStandardUnipotentRadicalBijOnNilradical.lean:124`; `…/CharacterCosetSumEqZeroOfSubgroupSum.lean:10`; `…/CharpolyBlockAndInvariantUnderStabilizerNilradic.lean:36`; `…/IsPrimitiveExtendZeroOfSumUnipotentRadical.lean:72`; `…/RegularIffNatDegreeAndExistsEllipticGL.lean:62`; `…/ExistsIntCoeffPrimitiveGLCharacter.lean:17`; `…/EqOfIsPrimitiveOfEqOnEllipticFiniteGL.lean:33,127,213`; `…/OrthogonalIntVectorsNotAgreeOnRegular.lean:21`; `…/ParsevalBoundIntegerVectorSmallFourierSupport.lean:60`; `…/SeparationNumericalIneqCuspidalGL.lean:68`; `…/NoNormEightOfFourierVanishingOrderFifteen.lean:8`; `…/NoNormTwelveOrderSixtythree.lean:107` | Section 13.4.13: from standard unipotent-block vanishing (`unipBlock`) via trace-zero idempotents and block characteristic-polynomial invariance to `IsPrimitive (extZero χ)`, Frobenius-invariant integer Gram vectors, two-tier elliptic character formulas, Parseval/Vandermonde/Fourier separation proving `cuspElliptic_statement` without `exists_regular`, and payment to `LabelMapNonempty` (`exists_regular` read in §13.4.14, Table 13.4.14). | [Lean, read] |
| `GlobalTheory.CuspFormula.exists_regular`, `CuspFormula.esymm_mem_virt`; `GlobalTheory.EsymmVirt.esymm_eq_of_psum_eq`, `exists_multisets`, `esymm_mem_virt`; `GlobalTheory.CuspGL.natDegree_mul_esymm_roots_pow`; `GlobalTheory.dvd_of_period_of_dvd_sum_powersetCard`, `card_dvd_sum_of_invariant_of_card_stabilizer_dvd`, `exists_regular_exponent_of_sum_sq_eq`; `UpperTheory.Gal.InertialTypesAlt.cuspChar` | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLabel.lean:38,49`; `…/DivisorProofs/EsymmMemVirtualCharactersOfPowerSumEigenvalues.lean:39,74,110`; `…/DivisorProofs/NatDegreeMulEsymmRootsPow.lean:36`; `…/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean:184`; `…/DivisorProofs/CardDvdSumOfInvariantOfCardStabilizerDvd.lean:5`; `…/DivisorProofs/ExistsRegularExponentOfSumSqEq.lean:5`; `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/RegularSemisimpleFibres/PCuspChar.lean:55` | Section 13.4.14: existence of a regular label for every primitive irreducible character of $\mathrm{GL}_d(F)$ via esymm virtual characters, the primary-class esymm identity, orbit-stabilizer period divisibility and the length argument, closed by Schur orthogonality against (Q3); exact supply to `exists_label`, `finrank_of_simple_cuspidal` and `cuspChar`; **(U1)** discharged. | [Lean, read] |
| `GlobalTheory.CuspGL.psi`, `rootSum`, `IsAdditive`, `IsPrimitive`, `ipGL`; `PrimeLabOrbit.primeLab_to_regularChar`; `GrPolys.card_monic_coeff_zero_ne_zero` | `src/Development/AbelianVarietyTheory/Definitions/CommutativeAlgebra/InvariantSubspaceMobiusInverseRecEqOfFinrankLt.lean:35,65,21,17,83`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MonicIrreducibleInjectRegularCharacterOrbits.lean:125`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardMonicNatDegreeCoeffZeroNeZero.lean:38` | Definition 13.3, Lemma 13.7, Proposition 13.8 (Step 2). | [Lean, read] |
| `OpenLiteratureStatements`, `global_artin_reciprocity_of_literature`, `siegel_eisenstein_simple_pole`, `literature_local`, `literature_automorphy`, `literature_cohomology`, `published_results_eigen`, `green_regular_characters_of_literature`, `published_results_first`, `published_results_arithmetic`, `every_character_of_literature_of_vWin` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215,243,505,589,609,626,666,399,727,781,810` | Definition 13.2 & Proposition 13.2: 3-field root `OpenLiteratureStatements` (`Row`, `RecTExists`, `Row`), 195 literature theorems, bundle assemblers, and master bridge to `EveryCharacter` (top definitions `R3`; 151,285-module proof cone `[Lean]` / `[Open]`). | [Lean, read] |
| `OpenImageCondition`, `global_artin_reciprocity_of_open`, `green_regular_characters_of_open` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207,225,285` | Definition 13.2(1–2): 1-field `VWin`-side root `OpenImageCondition` (`RowT`) and 62 `*_of_open` literature theorems (cone 146,662; internal proofs `[Lean]` / `[Open]`). | [Lean, read] |
| `DoublingMethodLocalZetaIntegrals`, `GlobalTheory.Published.UnusedSlot72`, `BaseChangeIsobaricTransfer`, `BaseChangeDefiniteUnitaryGroup` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:6,7,8,9` | Section 13.2.2(3): exhibits `UnusedSlot72 : Prop := True` alongside genuine `ResidueKilled.DM` and base-change abbreviations. | [Lean, read] |
| `GlobalTheory.Published.GlobalArtinReciprocity` (`Prop`); `globalArtinReciprocity`, `rayClassFieldSt`, `heckeLAdicCharacter` (wrappers) | `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70`; `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8,11,14` | Section 13.2.2(2) & **Chapter 18**: states `IsGlobalArtin` (`:25–39`) and wraps `CompanionTheory.FamInh.globalArtin` (`[Lean]` / `[Open]`) into `GlobalArtinReciprocity`, `RayClassFieldSt`, and `HeckeLAdicCharacter`. | [Lean, read] |

**Summary of the chapter.** Over a finite field $\mathbb F_q$, Harish-Chandra
parabolic induction from proper Levi subgroups misses the cuspidal characters, which Green `[Green1955]`
constructed from Frobenius orbits of regular characters $\theta : \mathbb F_{q^d}^\times \to \mathbb C^\times$
(worked out explicitly on $\mathrm{GL}_2(\mathbb F_q)$ and $\mathrm{GL}_2(\mathbb F_3)$ in Section 13.2.1).
In node **P16**, `SumRangeEqRoots.lean` (Proposition 13.1) proves `GlobalTheory.GLq.Green` in 306 lines
of clean Galois theory from `GlobalTheory.Published.GreenRegularCharacters` [Lean, read], supplying
finite-level irreducibility to Part II (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopShape.lean:33`) and depth-zero supercuspidal inertia to
Chapter 12 (`TypeLaw`). More broadly, node **P18** (`EveryCharacterOfLiteratureOfVWin.lean` and
`DenseThresholdCases/TemperedProductOfSquareIntegrable.lean`) derives 257 named literature theorems inside a 151,285-module
cone from `Row0b` and `RecTExists` alone `[Lean]`. Because every `GlobalTheory.Published.*` proposition
is proved inside the archive without axioms, narrowed or even `True`-valued slots (`UnusedSlot72`)
cannot undermine the logical soundness of `src/Main.lean` (Proposition 13.2); meanwhile, statement-fidelity
audits (`LUMI doc 07` `[Community]` and our 14 `R3` worked case studies in **Chapter 18** `[Lean, read]`)
chart what has been formalized and what remains `[Open]`. Next, in **Chapter 17**, we close Part III by
opening the additive-combinatorial Behrend sphere engine inside `HostOfField`, before turning in **Part IV
(Chapters 14–16 and 18)** to examine Masullo's trace-formula draft on its own terms, compare the two
proofs side by side, and assemble the master verification ledgers and `Published`-layer case studies!
