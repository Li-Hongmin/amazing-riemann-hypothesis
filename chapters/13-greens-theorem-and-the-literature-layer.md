# Chapter 13. Green's theorem and the literature layer

> **Status tags used in this chapter:** `[Lean, read]` for declarations and `sorry`-free proof
> bodies read line by line in `LabelDatum.lean`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean`,
> `SumRangeEqRoots.lean`, `DiscreteSpectrumResidualClassification.lean`,
> `StandardTheoremStatements/GlobalArtinReciprocity.lean`,
> `EveryCharacterOfLiteratureOfVWin.lean` (`OpenLiteratureStatements` and top assembly), and
> `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean` (`OpenImageCondition`) (`R3`), and, in Section 13.4.4, the producer of
> `GreenRegularCharacters` (`ExistsCuspidalCharacterOfRegularCharacterGLn.lean`,
> `IsCharacterCuspidalRootSumRegular.lean`, `GreenCuspidalCharsByRegularCharsProof.lean` and the
> definitions they unfold, `R3`); `[Lean]` for the existence
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
> for the inputs (I1)–(I9) listed before Proposition 13.6. Paths are relative to `lean/` in the pinned
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
  `CuspGL.TeichEmb.exists_teichmuller`, `…/CharacterTheory/ExistsTeichmullerMapAlgebraicClosureFiniteField.lean:24`).
- (I2) If $\dim V > 0$ and $s((X - 1)^j) = j$ for all $j$, then
  $\psi_s(V, 1) = \prod_{i \in [1, \dim V)}(1 - q^i)$ (`T.invariantSubspaceMobiusInverse_one_prod_Ico`,
  `…/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIcoStatement.lean:6`; lemma `CuspGL.psi_one`,
  `…/CharacterTheory/InvariantSubspaceMobiusInverseOneProdIco.lean:74`).
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
  special case of Green's Theorem 1 (Remark 13.4.4(1)).
- (I7) Parabolic induction preserves virtual characters (`ParabVirt.parab_virt`,
  `…/CharacterTheory/ParabolicInductionTrivialPreservesVirtualCharact.lean:193`): if $\Phi$ is invariant under
  transport by linear isomorphisms and $x \mapsto \Phi(F^a, x)$ is virtual on $\mathrm{GL}_a(F)$, then
  $x \mapsto \sum_{W\ x\text{-invariant},\ \dim W = a}\Phi(W, x|_W)$ is virtual on $\mathrm{GL}_n(F)$.
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
  simple if and only if $\sum_{g \in G}\chi_V(g)\chi_V(g^{-1}) = \lvert G\rvert$.
- (I9) (exhaustion only) A finite set of distinct multisets of cuspidal characters of total degree $n$ has at
  most $g^n - g^{n-1}$ elements (`T.card_cuspidal_multisets_total_degree_le`,
  `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardCuspidalMultisetsTotalDegreeLeStatement.lean:8`).
  We read its assembly `CuspMultisetCount.card_le` (`…/InertiaEigenvalues/CardCuspidalMultisetsTotalDegreeLe.lean:30–61`):
  each multiset is sent to an irreducible constituent of its Harish-Chandra induction with a nonzero
  Whittaker functional, distinct multisets give distinct constituents, and there are at most
  $g^n - g^{n-1}$ such generic irreducible characters. Its main inputs
  (`T.exists_generic_constituent_harishChandra_cuspidal`, `IpCuspProd.ip_hcL_cusp`,
  `T.ncard_generic_irreducible_characters_GLn_le`) are unread [Open].

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
some $\rho : G \to \mathrm{GL}_n(\mathbb C)$. This is `isChar_psi_rootSum_of_regular` (`:92–184`; statement
wrapper `T.isCharacter_cuspidal_rootSum_regular`,
`…/CharacterTheory/IsCharacterCuspidalRootSumRegularStatement.lean:7–8`).

*Step 4 (`IsCusp`;*
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18–48`*).*
Irreducibility (`:25–38`): the representation `FDRep.of ρ` has character $\tau_\theta$; by Mathlib's
criterion (I8) it is simple if and only if $\sum_x \tau_\theta(x)\tau_\theta(x^{-1}) = \lvert G\rvert$; since
$\overline{\tau_\theta(x)} = \tau_\theta(x^{-1})$ for virtual characters (I8) and $((-1)^{d-1})^2 = 1$, this is
Step 2, rewritten as a sum over $G$ by the bookkeeping identity of (I8). Jacquet vanishing
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
   exhaustion from counting (I9). The difficulty of the textbook theorem now sits in (I6) and (I9), both
   unread [Open].
5. *Other readers of the producer.* Besides the two main-path read sites of the Motivation,
   `PM.greenRegularCharacters` is called directly in the partial local Langlands construction (`nameLaws`,
   `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/NameLaws.lean:81`,
   Chapter 12). The bundle `UnitaryGroupThirdPlaceHypotheses` also carries `greenCuspidal : GreenCuspidal`,
   filled by a separate proof `PositivityTheory.Stage1.PM.greenCuspidal`
   (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:397–398, 668`).
   We located these but did not read them [Lean].

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
| inputs (I1)–(I8): `T.*` statement wrappers and the `CuspGL`/`BI`/`ParabVirt` lemmas they name; `card_cuspidal_multisets_total_degree_le` (I9; assembly `card_le` read) | files listed with (I1)–(I9) before Proposition 13.6 | Propositions 13.6 and 13.8 | [Lean] statement; proofs [Open] |
| `FDRep.simple_iff_char_is_norm_one` (Mathlib) | `Mathlib/RepresentationTheory/FinGroupCharZero.lean:121` (commit `0df444a`) | Proposition 13.6, Step 4 | [Lean] (Mathlib; statement read) |

---

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
| `GlobalTheory.greenRegularCharacters_holds`, `family`, `factor_lab`, `prod_factors`, `count` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GreenCuspidalCharsByRegularCharsProof.lean:18,23,35,48,56,137` | Proposition 13.8: the producer of `GreenRegularCharacters`; exhaustion by counting cuspidal multisets against the $g^d - g^{d-1}$ monic polynomials with nonzero constant term (the bound `card_cuspidal_multisets_total_degree_le` is [Lean], its inputs [Open]). | [Lean, read] |
| `GlobalTheory.GreenRegular.exists_cusp_of_regular`; `GlobalTheory.ParamLabel.isCusp_psi`; `GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCuspidalCharacterOfRegularCharacterGLn.lean:65`; `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GreenCuspidalCharIsCuspidalOfMinpolyOfParam.lean:18`; `src/Development/AbelianVarietyTheory/Proofs/CharacterTheory/IsCharacterCuspidalRootSumRegular.lean:92` | Proposition 13.6: $\tau_\theta = (-1)^{d-1}\psi_{s_k}$, the invariant-subspace Möbius inverse of a root power sum; cuspidality, degree, elliptic values and orbit equivalence from the inputs (I1)–(I8), whose statements are [Lean] and whose proofs are [Open]. | [Lean, read] |
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
