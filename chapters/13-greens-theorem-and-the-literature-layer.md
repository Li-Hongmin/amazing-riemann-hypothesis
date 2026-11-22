# Chapter 13. Green's theorem and the literature layer

> **Status tags used in this chapter:** `[Lean, read]` for declarations and `sorry`-free proof
> bodies read line by line in `LabelDatum.lean`, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean`,
> `SumRangeEqRoots.lean`, `DiscreteSpectrumResidualClassification.lean`,
> `StandardTheoremStatements/GlobalArtinReciprocity.lean`,
> `EveryCharacterOfLiteratureOfVWin.lean` (`OpenLiteratureStatements` and top assembly), and
> `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean` (`OpenImageCondition`) (`R3`); `[Lean]` for the existence
> and proved status of individual `UpperTheory.LiteratureTheorems.*` and `GlobalTheory.Published.*`
> declarations (`R1` / `R2`); `[Paper]` for citations to Alpöge's `remark.pdf` and Masullo's draft;
> `[Community]` for public statement-fidelity reviews (notably LUMI's four-batch review of 105
> statements); `[Expository]` for classical Green character theory on $\mathrm{GL}_d(\mathbb F_q)$,
> worked $\mathrm{GL}_2(\mathbb F_q)$ / $\mathrm{GL}_2(\mathbb F_3)$ calculations, and audit
> methodology; `[Open]` for unreviewed named literature `Prop` definitions and unread proof cones.

In Chapter 12 (`MainConclusion.lean:7–11`) [Lean, read], we saw that once `Row0b recT` (`P14`) and
`RecTExists` (`P15`) are supplied, the final bridge to `UpperTheory.EveryCharacter` passes through
two remaining nodes of our proof map (`notes/proof-map.md`):

1. **Node P16 (`GlobalTheory.GLq.Green`, `LabelDatum.lean:108`, proved from `GreenRegularCharacters` in `SumRangeEqRoots.lean:225`):**
   J. A. Green's 1955 classification `[Green1955]` of the complex cuspidal irreducible characters of
   the finite general linear group $\mathrm{GL}_d(\mathbb F_g)$ ($g$ prime): they are parametrized
   bijectively by degree-$d$ monic irreducible polynomials $P \in \mathbb F_g[X]$ ($P(0) \neq 0$),
   have exact degree $\prod_{i=1}^{d-1}(g^i - 1)$, and take the Galois-orbit trace value
   $(-1)^{d-1}\sum_{i=0}^{d-1}\theta_x(z^{g^i})$ on elliptic elements of irreducible characteristic
   polynomial!
2. **Node P18 (`OpenLiteratureStatements` and `OpenImageCondition`, `EveryCharacterOfLiteratureOfVWin.lean:215–813`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207–343`):**
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
   `eSerC L n f`, `ESerTie D` in `LabelDatum.lean:27,102,114` [Lean, read]) requires knowing:
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

2. **What Harish-Chandra induction (`hc 1 1 α β 2`, `LabelDatum.lean:45`) produces — and what it misses:**
   Let $B = \bigl\{\begin{pmatrix} h_1 & v \\ 0 & h_2 \end{pmatrix}\bigr\} = M U \subset G$ be the
   upper-triangular Borel subgroup (`InPar 1`, `LabelDatum.lean:36`), of order $q(q - 1)^2$ and index
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
   - **Jacquet restriction (`res 1 1 τ_θ`, `LabelDatum.lean:47–49, 64–65`) vanishes identically:**
     For any $h_1, h_2 \in \mathbb F_q^\times$, `res 1 1 τ_θ h₁ h₂` averages $\tau_\theta\begin{pmatrix} h_1 & b \\ 0 & h_2 \end{pmatrix}$
     over the $q$ unipotent entries $b \in \mathbb F_q$:
     - if $h_1 \neq h_2$, every $\begin{pmatrix} h_1 & b \\ 0 & h_2 \end{pmatrix}$ has distinct eigenvalues
       $h_1, h_2 \in \mathbb F_q^\times$, hence is conjugate to $s_{h_1, h_2}$, where $\tau_\theta = 0$!
     - if $h_1 = h_2 = a$, then $b = 0$ gives $c_a$ (contributing $(q - 1)\theta(a)$) while the $q - 1$
       nonzero values $b \in \mathbb F_q^\times$ are all conjugate via $\operatorname{diag}(1, b)$ to $u_a$
       (each contributing $-\theta(a)$), so
       $$\mathrm{res}_{1, 1}(\tau_\theta)(a, a) = \frac{1}{q}\Bigl((q - 1)\theta(a) + (q - 1)\bigl(-\theta(a)\bigr)\Bigr) = 0!$$
   - **Schur inner product (`ip τ_θ τ_θ`, `LabelDatum.lean:22–23`) equals $1$:**
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
archive (`PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:13`,
`PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70` alongside its proof wrapper
`StandardTheoremStatements/GlobalArtinReciprocity.lean:8`, and
`DiscreteSpectrumResidualClassification.lean:6–7`) [Lean, read]:

1. **A faithful special case (`GlobalTheory.Published.GreenRegularCharacters`, `PublishedTheorems/GaloisCohomology₂/GreenRegularCharacters.lean:13–20`):**
   Quantifies over `∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ K [Field K] [Algebra (ZMod g) K], finrank (ZMod g) K = d → ...`.
   Every mathematical clause (cuspidality, degree $\prod_{i=1}^{d-1}(g^i - 1)$, elliptic trace
   $(-1)^{d-1}\sum_{i=0}^{d-1}\theta(z^{g^i})$, Frobenius orbit equivalence $\theta' = \theta^{g^i}$,
   and exhaustion of `IsCusp`) matches Green `[Green1955]`, specialized to **prime base fields
   $\mathbb F_g = \mathrm{ZMod}\,g$** (because the archive only reduces $\mathbb Z_g$-lattices at split
   degree-$1$ places $E_w \cong \mathbb Q_g$!).
2. **A full classical statement (`GlobalTheory.Published.GlobalArtinReciprocity`, `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70–72`):**
   States `IsGlobalArtin E Ω art` (`:25–40`: open quotient map $\mathbb A_E^\times \twoheadrightarrow G_E^{\mathrm{ab}}$
   with kernel $\overline{E^\times (E_\infty^\times)^\circ}$, inertia image $\overline{\mathrm{art}(\mathcal O_v^\times)}$,
   and geometric Frobenius on uniformizers) over **every** number field $E$, proved unconditionally via
   the wrapper `PositivityTheory.Stage1.PM.globalArtinReciprocity`
   (`src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8–15`,
   invoking `CompanionTheory.FamInh.globalArtin` `[Lean]`), used in Chapter 10 (`CutCoreUnit.main`),
   and audited line by line at `R3` in **Chapter 18** (`Section 18.2`) [Lean, read]!
3. **A `True` placeholder fossil (`GlobalTheory.Published.UnusedSlot72`, `DiscreteSpectrumResidualClassification.lean:7`):**
   Literally defined as:
   ```lean
   abbrev GlobalTheory.Published.DoublingMethodLocalZetaIntegrals : Prop := ResidueKilled.DM
   abbrev GlobalTheory.Published.UnusedSlot72 : Prop := True
   ```
   and "proved" in `EveryCharacterOfLiteratureOfVWin.lean:505–506` [Lean, read] by:
   ```lean
   theorem UpperTheory.LiteratureTheorems.siegel_eisenstein_simple_pole
       (O : OpenLiteratureStatements) : GlobalTheory.Published.UnusedSlot72 :=
     trivial
   ```
   As we verified directly in Chapter 7 (Section 7.5.1), `siegelEisensteinSimplePole` is stored as field
   #52 of `UnitaryGroupThirdPlaceHypotheses` and **never projected anywhere downstream**! Meanwhile its
   neighbor `DoublingMethodLocalZetaIntegrals` (`:6`) is **not** `True` — it proves the global doubling
   identity `ResidueKilled.DM` (`doubling_method`, `EveryCharacterOfLiteratureOfVWin.lean:371–372`) —
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

**Definition 13.2 (Architecture of the literature layer, `EveryCharacterOfLiteratureOfVWin.lean:215–813` and `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207–343`).** [Lean, read]

1. **The two root `Prop` structures (`:215` and `:207`):**
   - On the main `EveryCharacter` branch (`EveryCharacterOfLiteratureOfVWin.lean:215–218`),
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
`GlobalTheory.GLq.Green` (`LabelDatum.lean:108`) holds.*
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
   a follow-up check located `exists_locPrime_tied` (`ExistsLocalPrimeAinf.lean:281`), confirming
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
| `OpenLiteratureStatements`, `global_artin_reciprocity_of_literature`, `siegel_eisenstein_simple_pole`, `literature_local`, `literature_automorphy`, `literature_cohomology`, `published_results_eigen`, `green_regular_characters_of_literature`, `published_results_first`, `published_results_arithmetic`, `every_character_of_literature_of_vWin` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:215,243,505,589,609,626,666,694,727,781,810` | Definition 13.2 & Proposition 13.2: 3-field root `OpenLiteratureStatements` (`Row`, `RecTExists`, `Row`), 195 literature theorems, bundle assemblers, and master bridge to `EveryCharacter` (top definitions `R3`; 151,285-module proof cone `[Lean]` / `[Open]`). | [Lean, read] |
| `OpenImageCondition`, `global_artin_reciprocity_of_open`, `green_regular_characters_of_open` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207,225,285` | Definition 13.2(1–2): 1-field `VWin`-side root `OpenImageCondition` (`RowT`) and 62 `*_of_open` literature theorems (cone 146,662; internal proofs `[Lean]` / `[Open]`). | [Lean, read] |
| `DoublingMethodLocalZetaIntegrals`, `GlobalTheory.Published.UnusedSlot72`, `BaseChangeIsobaricTransfer`, `BaseChangeDefiniteUnitaryGroup` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/DiscreteSpectrumResidualClassification.lean:6,7,8,9` | Section 13.2.2(3): exhibits `UnusedSlot72 : Prop := True` alongside genuine `ResidueKilled.DM` and base-change abbreviations. | [Lean, read] |
| `GlobalTheory.Published.GlobalArtinReciprocity` (`Prop`); `globalArtinReciprocity`, `rayClassFieldSt`, `heckeLAdicCharacter` (wrappers) | `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70`; `src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8,11,14` | Section 13.2.2(2) & **Chapter 18**: states `IsGlobalArtin` (`:25–40`) and wraps `CompanionTheory.FamInh.globalArtin` (`[Lean]` / `[Open]`) into `GlobalArtinReciprocity`, `RayClassFieldSt`, and `HeckeLAdicCharacter`. | [Lean, read] |

**Summary of the chapter.** Over a finite field $\mathbb F_q$, Harish-Chandra
parabolic induction from proper Levi subgroups misses the cuspidal characters, which Green `[Green1955]`
constructed from Frobenius orbits of regular characters $\theta : \mathbb F_{q^d}^\times \to \mathbb C^\times$
(worked out explicitly on $\mathrm{GL}_2(\mathbb F_q)$ and $\mathrm{GL}_2(\mathbb F_3)$ in Section 13.2.1).
In node **P16**, `SumRangeEqRoots.lean` (Proposition 13.1) proves `GlobalTheory.GLq.Green` in 306 lines
of clean Galois theory from `GlobalTheory.Published.GreenRegularCharacters` [Lean, read], supplying
finite-level irreducibility to Part II (`ThirdPlaceSeries/TopShape.lean:33`) and depth-zero supercuspidal inertia to
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
