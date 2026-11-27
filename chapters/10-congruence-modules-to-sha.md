# Chapter 10. From congruence modules to Tate–Shafarevich groups

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs read
> line by line in `DivinNOfHypV.lean`, `IdempotentChoiceDepthZero.lean`,
> `LengthHeckeValueIdealLeDeterminantBound.lean`, `LengthHeckeValueIdealLeDeterminantBoundStatement.lean`,
> `GlobalCongruenceCountOfRootDifferenceUnit.lean`, `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean`,
> `ChosenTwistAnnihilatesSelmerGroups.lean`, `LinkNAlongFamilyOfLocalBounds.lean`,
> `ThirdPlaceSeries/LinkEta.lean`, and `GaloisCohomology/Statement.lean` (`R3`), and, in §§10.4.5–10.4.6,
> for the imported DVR determinant lemma, block-determinant lemmas, GMA Fitting step, peeling lemma,
> cyclotomic-block $Ш^1$ bound, class-number bound, $\rho$-block Selmer comparison and
> `twist_kills_selmer` (`R3`), for the main-path twist construction and Chebotarev producer read in §10.4.7,
> the lattice-specialization transport read in §10.4.7.1, the toric supply and level selection read in §10.4.7.2,
> the theta Euler-factor supply `propE` and the isotypic-lattice supplier `admInt_of_sup` read in §10.4.7.3,
> the joint supply of one auxiliary-place family with the Selmer polynomials read in §10.4.7.4,
> the two order-bound production wrappers and initial assemblies read in §10.4.7.5,
> the initial positive-order seed `StartInd.start_of_resBound` with its scalar-descent, unused-left-place, tame-scalar and ramified-subgroup suppliers read in §10.4.7.6,
> the [lattice lifting criterion](#104711-lifting-residual-cocycles-to-the-blochkato-lattice) and [integral annihilator theorem](#104712-integral-local-duality-and-the-two-finite-condition-annihilators) in §§10.4.7.11–12,
> the [compatible Tate generator](#10414-a-compatible-tate-generator-for-torsion-coefficients) and its local top-degree consumer in §10.4.14,
> and for the local and conditional matrix proofs in
> §§10.4.8–10.4.13, including the global invariant sum read in §10.4.11.1. Each subsection records its reading boundary.
> `[Lean]` marks the remaining statement-level sub-lemmas at the
> end of §10.4.5 and for the deeper inputs listed in §10.4.7; `[Paper]` for citations to Alpöge's `remark.pdf` and Masullo's
> draft; `[Community]` for public community reports; `[Expository]` for classical Hida/Ribet/Bellaïche–Chenevier
> background and worked examples; `[Open]` for unread proof cones and unverified fidelity of named
> `GlobalTheory.Published.*` hypotheses (specifically `GlobalArtinReciprocity`).

At the end of Chapter 9 we arrived at the central tension of the entire arithmetic engine. In an
ideal world where every theta lift $T_j : \mathcal E_{j-1} \to \mathcal E_j$ preserved integral
Hecke eigen-decompositions without denominators, $m \asymp \sqrt{x}$ lifts would deliver $m$ units of
`ASK` divisibility against a single archimedean height cost $x$, proving the Riemann Hypothesis
without ever mentioning Galois representations or Tate–Shafarevich groups!

In reality (`remark.pdf` p. 4, item 14: *"11/15/26: precise computation of the 'cost' of each lift,
showing that one would stop at $2/3$ a priori, attempt to get a main term and transfer constant to a
function field or kill via twisting, need for 'division'"*) [Paper; remark p. 4], projecting an
integral theta-lifted form onto the desired cuspidal Hecke eigenspace $\pi_j$ **loses integrality**
whenever $\pi_j$ is congruent modulo primes $\ell$ to other automorphic forms (in particular, to
endoscopic / Eisenstein / abelian packets built from cyclotomic characters!). Those congruence
denominators subtract from the $\mathfrak p_w$-adic divisibility of Chapter 8 and inflate the height
budget of Chapter 9.

Node **P11** of the Lean archive solves this congruence-loss problem in three decisive steps:

1. **Hida congruence modules $\to$ Generalized Matrix Algebra (GMA) Fitting ideals (`CutDetOrd.main`):**
   Following Ribet `[Ribet1976]`, Hida `[Hida1981]`, `[Hida1988]`, and Bellaïche–Chenevier
   `[BellaicheChenevier2009]`, the $\ell$-adic valuation of the Hecke congruence ideal of each lift
   $\pi$ is bounded by the $\mathcal O$-length of $1$-cocycles on the off-diagonal blocks of a GMA
   Galois representation: one cuspidal $\rho$-block plus $t = R.t$ scalar cyclotomic blocks!
2. **Galois cohomology + character twisting (`CutCoreUnit.main` & `TwistingCharacterExistence`):**
   Twisting the lift by a well-chosen character (`TwistingCharacterExistence`, `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:166`;
   `twist_kills_selmer`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:8`) **bounds the cuspidal
   $\rho$-Selmer piece**, while global Artin reciprocity and Bloch–Kato-type local conditions
   `[BlochKato1990]`, `[Rubin2000]` (with inflation into $Ш^1$, without Poitou–Tate duality; §10.4.5) bound the $t$ cyclotomic blocks by the **host class number
   $v_\ell(h_E)$** ($c = 0$) plus the **cyclotomic Tate–Shafarevich lengths**
   $\sum_{1 \le e < R.t} \operatorname{len}_{\mathbb Z_\ell} Ш^1(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e))$
   ($1 \le c < t$) plus tame ramification (`CutCoreUnit.main`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:44`) [Lean, read]!
3. **Bridging `HypV` to the linear-in-$m$ chain budget `DIVinN` (`divinN_of_hypV`):** Once `HypV`
   (supplied by Chapter 11's `VWin`) bounds that $\log \ell$-weighted $Ш^1$ sum across all primes
   $\ell$ by $\sqrt{b} = \exp(x^\varepsilon / 2)$ and `SmallLevelRankEq` equates per-step kernel
   ranks `dZ0 j` to the base rank `D0`, `divinN_of_hypV` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:117`, read 100% line by
   line) proves `DIVinN` with per-lift budget $B_0 = f m b x^\varepsilon$ — avoiding the $x^{2/3}$
   trap and hitting $x^{1/2 + O(\varepsilon)}$ in Chapter 5's `SZ.T3` [Lean, read]!

---

## 10.1 Motivation: why congruences between eigenforms cost denominators

Why does projecting onto a Hecke eigenform ever create $\ell$-adic denominators [Expository]?

Suppose an integral lattice $M \cong \mathbb Z_\ell^2$ carries a commuting family of self-adjoint
Hecke operators $\mathbb T \subset \operatorname{End}_{\mathbb Z_\ell}(M)$ with two distinct
$\mathbb Z_\ell$-valued eigenforms $f_1, f_2 \in M$ (primitive in $M$, spanning $M \otimes \mathbb Q_\ell$).
If $f_1$ and $f_2$ are **not** congruent modulo $\ell$, then $M = \mathbb Z_\ell f_1 \oplus \mathbb Z_\ell f_2$
splits integrally, and projecting any $v \in M$ onto $\mathbb Q_\ell f_1$ lands inside
$\mathbb Z_\ell f_1$ with **zero denominator**.

Now suppose instead that $f_1$ and $f_2$ have **congruent Hecke eigenvalues modulo $\ell^k$**: for
every $T \in \mathbb T$, $\lambda_1(T) \equiv \lambda_2(T) \pmod{\ell^k}$! Then $f_1 - f_2$ can be
divisible by $\ell^k$ in $M$: say $M$ is generated over $\mathbb Z_\ell$ by $e_1 = f_1$ and
$e_2 = \frac{f_1 - f_2}{\ell^k}$! Watch what happens when we expand $e_2 \in M$ in the eigenbasis
$(f_1, f_2)$:
$$e_2 = \frac{1}{\ell^k}\,f_1 - \frac{1}{\ell^k}\,f_2!$$
Projecting the **integral** lattice element $e_2 \in M$ onto the $\pi_1$-eigenspace $\mathbb Q_\ell f_1$
produces $\frac{1}{\ell^k} f_1 \notin \mathbb Z_\ell f_1$: **an $\ell^k$ denominator appears out of
nowhere, eating $k \log \ell$ of our global Arakelov slope bound!** As Hida proved `[Hida1981]`,
`[Hida1988]`, the exact worst-case denominator $\ell^k$ is measured by the **congruence module**
(or congruence ideal $I_{\mathrm{cong}} \subseteq \mathbb Z_\ell$) between $\pi_1$ and its
complementary Hecke algebra!

How do we bound $k = v_\ell(I_{\mathrm{cong}})$? By **Ribet's converse to Herbrand's theorem**
`[Ribet1976]` and **Bellaïche–Chenevier's GMA theory** `[BellaicheChenevier2009]`! Over the localized
Hecke ring $\mathbb T$, the pseudorepresentation / Galois representation attached to the glued packet
("cuspidal $\pi_1$ congruent mod $\ell^k$ to a sum of characters $1 \oplus \chi \oplus \cdots \oplus \chi^t$")
lives in a **Generalized Matrix Algebra**
$$\mathcal A = \begin{pmatrix} M_r(\mathcal O) & B \\ C & \operatorname{Diag}_t(\mathcal O) \end{pmatrix}$$
whose off-diagonal multiplication $B \otimes_{\mathcal O} C \to \mathcal O$ lands inside the
congruence ideal $I_{\mathrm{cong}}$! Modulo $I_{\mathrm{cong}}$, that multiplication is **zero**, so
the off-diagonal entries of the Galois representation become **$1$-cocycles** defining genuine
nontrivial Galois cohomology classes in $H^1(G_{E, S}, \text{block})$. Therefore:
$$\text{size of congruence denominator } I_{\mathrm{cong}}
\ \le\ \text{size of } H^1_{\mathrm{Sel}}(\text{cuspidal }\rho\text{-block})
\ +\ \sum_{c = 1}^t \text{size of } H^1_{\mathrm{Sel}}(\text{cyclotomic }\chi^c\text{-block})!$$

---

## 10.2 Worked examples

Let us check both algebraic steps — Hida's congruence ideal and Bellaïche–Chenevier's GMA determinant
bound — by explicit hand calculation [Expository].

### 10.2.1 Hida's congruence ideal on the glued ring $R_k \subset \mathbb Z_\ell \times \mathbb Z_\ell$

Fix a prime $\ell$ and an integer $k \ge 1$, and consider the commutative $\mathbb Z_\ell$-subalgebra
$$R_k := \bigl\{(a, b) \in \mathbb Z_\ell \times \mathbb Z_\ell : a \equiv b \pmod{\ell^k}\bigr\}
= \mathbb Z_\ell\cdot(1, 1) \oplus \mathbb Z_\ell\cdot(0, \ell^k).$$
Think of $R_k$ as the Hecke algebra generated by operators acting with eigenvalue $a$ on our target
cuspidal form $\pi$ (first coordinate $\lambda_\pi : R_k \twoheadrightarrow \mathbb Z_\ell$,
$(a, b) \mapsto a$) and eigenvalue $b \equiv a \pmod{\ell^k}$ on a complementary Eisenstein/endoscopic
form $\pi_{\mathrm{comp}}$ (second coordinate $(a, b) \mapsto b$).

Compute the idempotent denominator and congruence ideal by hand:

1. Over $\mathbb Q_\ell$, $R_k \otimes_{\mathbb Z_\ell} \mathbb Q_\ell = \mathbb Q_\ell \times \mathbb Q_\ell$
   has orthogonal idempotents $\varepsilon_\pi = (1, 0)$ and $\varepsilon_{\mathrm{comp}} = (0, 1)$.
2. What is the **congruence ideal** $I_{\mathrm{cong}}(\pi) := \lambda_\pi\bigl(R_k \cap \ker\lambda_{\mathrm{comp}}\bigr) \subseteq \mathbb Z_\ell$
   (`ccOff` in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:15`)? An element $(a, b) \in R_k$ lies in
   $\ker\lambda_{\mathrm{comp}}$ if and only if $b = 0$; since $a \equiv b \pmod{\ell^k}$, that forces
   $\ell^k \mid a$, and $(\ell^k u, 0) \in R_k$ for all $u \in \mathbb Z_\ell$. Hence
   $$I_{\mathrm{cong}}(\pi) = \ell^k \mathbb Z_\ell,
   \qquad
   \operatorname{len}_{\mathbb Z_\ell}\bigl(\mathbb Z_\ell / I_{\mathrm{cong}}(\pi)\bigr) = k!$$
3. Simultaneously, $\ell^k \varepsilon_\pi = (\ell^k, 0) \in R_k$ is the **smallest** $\mathbb Z_\ell$-multiple
   of $\varepsilon_\pi$ lying inside $R_k$! Thus for *any* $R_k$-module $M$ torsion-free over
   $\mathbb Z_\ell$, multiplying by $\ell^k \varepsilon_\pi \in R_k$ maps $M$ integrally into
   $M[\pi] = \varepsilon_\pi M \cap M$, bounding the projection denominator by $\ell^k$, i.e. by
   $\operatorname{len}_{\mathbb Z_\ell}(\mathbb Z_\ell / I_{\mathrm{cong}}(\pi)) = k$!

### 10.2.2 A $2 \times 2$ Generalized Matrix Algebra and why $BC = I_{\mathrm{cong}}$ bounds $k$ by cocycle lengths

Now watch how a GMA representation forces $\operatorname{len}_{\mathcal O}(\mathcal O / I_{\mathrm{cong}}) \le \operatorname{len}_{\mathcal O}(Z^1 / B^1)$
(`CutDetOrd.main`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:59`)! Let $\mathcal O = \mathbb Z_\ell$,
let $I = \ell^k \mathbb Z_\ell$ be a nonzero proper ideal, and consider the $2 \times 2$ GMA
$$\mathcal A := \begin{pmatrix} \mathcal O & B \\ C & \mathcal O \end{pmatrix},
\qquad\text{equipped with }\mathcal O\text{-bilinear multiplication } m : B \times C \longrightarrow I \subseteq \mathcal O.$$
Suppose $G$ is a group and $\tau : G \to \mathcal A^\times$ is a multiplicative representation
$$\tau(g) = \begin{pmatrix} a(g) & b(g) \\ c(g) & d(g) \end{pmatrix}$$
such that:

- on the diagonal, modulo $I$ we have $a(g) \equiv \rho(g) \pmod I$ and $d(g) \equiv \chi(g) \pmod I$
  for characters $\rho, \chi : G \to \mathcal O^\times$;
- the off-diagonal images $\{b(g) : g \in G\}$ and $\{c(g) : g \in G\}$ generate $B$ and $C$ over
  $\mathcal O$, and $m(B, C) = I = \ell^k \mathcal O$.

Check the matrix multiplication $\tau(g_1 g_2) = \tau(g_1)\tau(g_2)$ by hand:

1. Looking at the $(1, 2)$ entry gives $b(g_1 g_2) = a(g_1) b(g_2) + b(g_1) d(g_2)$, and looking at
   the $(2, 1)$ entry gives $c(g_1 g_2) = c(g_1) a(g_2) + d(g_1) c(g_2)$. Because $m(b, c) \in I$,
   look at the $(1, 1)$ entry **modulo $I$**:
   $$a(g_1 g_2) = a(g_1) a(g_2) + m\bigl(b(g_1), c(g_2)\bigr) \equiv a(g_1) a(g_2) \pmod I.$$
2. Now take $B = \mathcal O$ and $C = \mathcal O$ (torsion-free of rank $1$ over $\mathcal O$, as in
   the generic irreducible representation over $\operatorname{Frac}(\mathcal O)$) with off-diagonal
   pairing $m(x, y) = \ell^k x y \in I$, and suppose the local/global cocycle quotients modulo
   coboundaries have bounded $\mathcal O$-lengths $L_1$ and $L_2$ independent of $k$. Why can $k$
   not exceed $L_1 + L_2$? Because $b(G)$ generates $B = \mathcal O$, some $g_0 \in G$ has
   $b(g_0) \in \mathcal O^\times$. Modulo $\ell^k$, $a(g) \equiv \rho(g)$ and $d(g) \equiv \chi(g)$
   turn $\bar b : G \to (\mathcal O / \ell^k \mathcal O)(\rho \chi^{-1})$ into a **$1$-cocycle**.
   Since the cocycle quotient is annihilated by $\ell^{L_1}$, $\ell^{L_1} \bar b$ is a coboundary
   modulo $\ell^k$: there exists $x \in \mathcal O$ with $\ell^{L_1} b(g) \equiv (\rho(g) - \chi(g)) x \pmod{\ell^k}$
   for all $g \in G$. Evaluating on the GMA relation module `Rel` (after fixing the gauge on an
   idempotent-splitting element where $\rho - \chi$ vanishes or is controlled) bounds the torsion
   exponent of the $B$-quotient by $L_1$ and symmetrically of the $C$-quotient by $L_2$, so the DVR
   determinant lemma (`CutDetOrd.main`) concludes
   $$k = \operatorname{len}_{\mathcal O}(\mathcal O / I) \le L_1 + L_2
   = \operatorname{len}_{\mathcal O}\bigl(H^1_{\mathrm{f}}(G, \rho\chi^{-1})\bigr)
   + \operatorname{len}_{\mathcal O}\bigl(H^1_{\mathrm{f}}(G, \chi\rho^{-1})\bigr)!$$
   Every single ingredient of `CutDetOrd.main` and `CutCoreUnit.main` is already in that calculation!

---

## 10.3 Definitions

We now record the exact Lean declarations of node **P11**.

### 10.3.1 Orthogonal idempotent decompositions of GMAs (`IdempotentChoiceDepthZero.lean`)

**Definition 10.1 (`IsOrthogonalIdempotentDecomposition`, `src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:18`).**
Over a discrete valuation ring $\mathcal O = N.\mathcal O(i)$ above $\ell = N.\ell(i)$, an orthogonal
idempotent decomposition of depth zero for rank tuple `R` (`r := R.r`, `t := R.t`, ambient dimension
`R.nV`) equips the Hecke/Galois algebra with [Lean, read]:

1. mutually orthogonal idempotents `S.eB` of **rank $t = R.t$** (`((S.eB x).map (toK N i)).rank = R.t`,
   `:22`) — the **cyclotomic block idempotent**, diagonalized by `S.X0` (`:36–38`) at a distinguished
   inertia element `S.g0` into the $t = R.t$ scalar characters $\chi_{c+1}$ = `chiU N i (c + 1)`
   ($c \in \mathrm{Fin}\,R.t$). After the twist by $\chi_1^{-1}$ built into the cocycles, the $c$-th
   slot carries $\chi_{c+1}\chi_1^{-1} = \chi_{\mathrm{cyc}}^{-c}$ (Lemma 10.10 below) — and `S.e1` of **rank $1$** (`:22`),
   together with the splitting `S.e` (`:24–29`) decomposing the `R.nV`-dimensional representation into
   the $r \times r$ cuspidal representation block `rhoO` (`Fin R.r`) and the $t$ scalar cyclotomic
   coordinates (`Fin R.t`); and
2. a distinguished rank-$1$ projector element `Eel` (`:56–60`) satisfying $\mathrm{Eel}^2 = \delta_{51}\cdot\mathrm{Eel}$
   with $\delta_{51} \in \mathcal O^\times$ (`IsUnit del51`), projecting onto the $c = 0$ cyclotomic
   slot to extract the off-diagonal pairing values feeding the congruence ideal `ccOff(π)`
   (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:15`).

### 10.3.2 Integral Hecke lattices and `TwistingCharacterExistence` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean`)

**Definition 10.2 (Ramification-normalized length, signed lattice index, and character-twisting existence, `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:64,68,81,98,166,219,233`).**

1. **Ramification-normalized module length and signed lattice index (`lenR` and `sIdx`, `:64, 68`).**
   Over a DVR $R$ above a prime $\ell$, `lenR R l M` (`:64`) divides the $R$-module length
   `(Module.length R M).toNat` by the $\ell$-ramification index `(IsDiscreteValuationRing.addVal R l).toNat`
   (normalizing $\mathcal O$-lengths back to $\mathbb Z_\ell$-scale!), and for two commensurable
   $R$-lattices $\Lambda_1, \Lambda_2$, `sIdx Λ₁ Λ₂ := lenR(Λ₁ / (Λ₁ ∩ Λ₂)) - lenR(Λ₂ / (Λ₁ ∩ Λ₂))`
   (`:68`) is the additive signed index measuring denominator loss when passing from one integral
   structure to another [Lean, read].
2. **Admissible twisting characters and Selmer annihilation (`TwOK`, `TwistingCharacterExistence`, `GoodTw`, `TwistTheoremAtIndex`, `:81, 166, 219, 233`).**
   `TwistingCharacterExistence : Prop` (`:166`) asserts that at each nonzero-index place $i$
   (under `SetHyp`), for every $\varepsilon' > 0$, every lattice family satisfying `ABHyp` and every
   finite set $A_0$ of places, there is a character $\psi'$ of the ray class group $\mathrm{RCG}(Q)$
   for an auxiliary set $Q$, satisfying `PsiOk` and the error clauses `partAT`, `partC`, `partD`, `partAB`
   (`:170–173`). `GoodTw` (`:219`) bundles the same clauses with the lattice conditions, and
   `TwistTheoremAtIndex` (`:233`) asserts that a `GoodTw` twist exists [Lean, read]. The twist is
   used in §10.4.3; where its existence comes from is discussed in §10.4.6.

### 10.3.3 Galois cohomology `Sha`, `LinkN`, `DIVinN`, and `HypV`

**Definition 10.3 (`Sha`, `shaLen`, `vvTerm`, `LinkN`, `SmallLevelRankEq`, `DIVinN`, and `HypV`, `src/Formalism/GaloisCohomology/Statement.lean:67,75,78`, `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:31,36,40,45,49,52,59,62`, and `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10`).**

1. **Cyclotomic Tate–Shafarevich group and length (`qzTw`, `Sha`, `shaLen`, `src/Formalism/GaloisCohomology/Statement.lean:67, 75, 78`).**
   For a number field $E$, a prime $\ell$, and an integer twist $e \in \mathbb N$, let
   $\mathbb Q_\ell / \mathbb Z_\ell(-e)$ (`qzTw`, `:67`) denote the discrete $G_{E, S_\ell}$-module on
   which $G_{E, S_\ell}$ acts via $\chi_{\mathrm{cyc}}^{-e}$, and let
   $$Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)
   := \ker\Bigl(H^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)
   \longrightarrow \prod_{v \in S_\ell} H^1\bigl(G_{E_v}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)\Bigr)$$
   (`Sha`, `:75`), with $\mathbb Z_\ell$-corank/length $\mathrm{shaLen}(E, \ell, e)$ (`:78`) [Lean, read].
2. **Single-step congruence-to-$Ш^1$ link (`vvTerm`, `etaSum`, `LinkN_at`, `LinkN`, `SmallLevelRankEq`, `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:31, 36, 40, 45, 52`) and chain budget (`DIVinN_at`, `DIVinN`, `:59, 62`).**
   At chain datum $D$ (with host $E = D.\mathrm{host}.E$, $f = D.R.f = 2\lvert \varphi.A \rvert$,
   $m = D.R.m$ steps, rank cutoff $R.t$, $b = \exp(x^\varepsilon)$, $L = x^\varepsilon$, and
   $B_0 = f m b x^\varepsilon$), define for each $l \in \mathbb N$ (`vvTerm`,
   `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:31`) [Lean, read]
   $$\mathrm{vvTerm}(D, l) := \begin{cases} (\log l)\sum_{1 \le e < R.t} \mathrm{shaLen}(l, e) & \text{if } l\text{ is prime}, \\ 0 & \text{otherwise,}\end{cases}$$
   and let `etaSum L j` (`:36`) be the weighted sum of step-$j$ congruence losses across active places $w$:
   - `LinkN_at L j C` (`:40–43`) is the **single-step** implication at lift $j \in \{1, \dots, m\}$:
     $$\mathrm{Summable}\bigl(\mathrm{vvTerm}(D)\bigr) \implies
     \mathrm{etaSum}(L, j) \le d_{Z_0}(j)\,\Bigl(C\,\bigl(f m b L^2 + (\log x)^2 N_c\bigr) + \sum'_l \mathrm{vvTerm}(D, l)\Bigr),$$
     and `LinkN Fm` (`:45`) asserts that `LinkN_at (Fm.L x i) j C` holds eventually for all $j \in \{1, \dots, m\}$
     whenever `ShaFinOdd` (`:25`) holds.
   - `SmallLevelRankEq Fm` (`:52–53`) asserts that eventually $(Fm.L\,x\,i).d_{Z_0}(j) = (Fm.D\,x\,i).\mathrm{what}_2.D_0$
     for every $j \in \{1, \dots, m\}$ (proved in `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Link.lean:20` as `link_alt_alt_alt`).
   - `DIVinN_at L j C` (`:59–60`) is the deterministic single-step inequality
     $$\mathrm{etaSum}(L, j) \le D_0 \cdot C\,x^\varepsilon\,(B_0 + N_c)$$
     (where $B_0 = f m b x^\varepsilon$ is the fixed field of `SizeData₂` feeding Chapter 5's `SZ.T3`!),
     and `DIVinN Fm` (`:62`) asserts `DIVinN_at` eventually across all lifts $j \in \{1, \dots, m\}$!
3. **The global $Ш^1$ hypothesis (`UpperTheory.Top.HypV`, `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10`).** `HypV Fm : Prop`
   asserts that eventually for large window scales $x$ along the family `Fm`, every datum $D = \mathrm{Fm}.D(x, i)$
   satisfies `VVle D.host D.R.t (Real.sqrt D.b)` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12`, where $\sqrt{b} = \exp(x^\varepsilon / 2)$)
   [Lean, read]!

---

## 10.4 Lemmas and proofs

We now walk through the `R3`-verified proofs of node **P11**: first the GMA determinant bound
`CutDetOrd.main` and the Galois cohomology congruence bound `CutCoreUnit.main`, then Selmer
annihilation `twist_kills_selmer`, and finally the 100%-read proof of `divinN_of_hypV`.

### 10.4.1 The GMA determinant bound (`CutDetOrd.main`)

**Proposition 10.1 (Bounding the congruence ideal by cuspidal + cyclotomic cocycle lengths: `CutDetOrd.main`).**
*Let $\mathcal O$ be the discrete valuation ring above $\ell$ attached to a lift $\pi$ at step $i$,
with off-diagonal congruence ideal $\mathrm{ccOff}(\pi) \subseteq \mathcal O$. Away from the
exceptional locus `Z i`, there exists a vector $\eta$ and group element $\gamma$ whose off-diagonal
matrix action `(yg ... γ x').mulVec η` is nonzero (`exists_ne_zero`, `:37`), feeding `value_mem_ccOff`
(`:15`) and the GMA determinant inequality*
$$\operatorname{len}_{\mathcal O}\bigl(\mathcal O / \mathrm{ccOff}(\pi)\bigr)
\le \operatorname{len}_{\mathcal O}\bigl(\mathrm{cocRho}(\pi)\bigr)
+ \sum_{c \in \mathrm{Fin}\,t} \operatorname{len}_{\mathcal O}\bigl(\mathrm{cocChi}(\pi, c)\bigr),$$
*where $\mathrm{cocRho}(\pi)$ is the off-diagonal $1$-cocycle quotient for the cuspidal $\rho$-block
and $\mathrm{cocChi}(\pi, c)$ ($0 \le c < t$) are the $1$-cocycle quotients for the $t = R.t$
cyclotomic blocks.*
*(Lean: `GlobalTheory.CutDetOrd.main`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:59`,
and wrapper `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBoundStatement.lean:8`.)* [Lean, read]

*Proof.* First (`value_mem_ccOff` at `:15` and `exists_ne_zero` at `:37`), using the rank-$1$ projector
`Eel` and unit $\delta_{51}$ of `IsOrthogonalIdempotentDecomposition` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:18`)
together with `NoChiOff` away from `Z i` produces $\eta$ and $\gamma$ with nonzero off-diagonal
action `(yg ... γ x').mulVec η ≠ 0`. Next (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:59–140`),
the proof constructs the GMA relation module `Rel` pairing the off-diagonal column module $B$ against
the off-diagonal row module $C$ into $\mathcal O$. By the block determinant polynomial identity
`BlockDetPoly.main` (Lemma 10.6, `[Lean, read]`), the coefficients of the block generic
determinants of relations lie in $\mathrm{ccOff}(\pi)$ (the Fitting inclusion, Proposition 10.7),
while each block solution module embeds into a restriction of $\mathrm{cocRho}(\pi)$ or
$\mathrm{cocChi}(\pi, c)$ (Lemma 10.8). Applying the DVR determinant-length lemma
`determinantLemma_discreteValuationRing_quotientLength_bound` (Lemma 10.5, `[Lean, read]`) bounds
$\operatorname{len}_{\mathcal O}(\mathcal O / \mathrm{ccOff}(\pi))$ by the sum of lengths of
$\mathrm{cocRho}(\pi)$ and the $t$ summands $\mathrm{cocChi}(\pi, c)$. The complete argument is
written out in §10.4.5. $\square$

### 10.4.2 From cyclotomic cocycles to class numbers and $Ш^1$ (`CutCoreUnit.main`)

Now open `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean`
(`R3`, 176 lines read in full) and watch what happens to each of the $t$ cyclotomic indices
$c \in \{0, 1, \dots, t - 1\}$ — representing the characters $\chi_{c+1}=\chi_1\chi_{\mathrm{cyc}}^{-c}$
for $c + 1 \in \{1, 2, \dots, t\}$ [Lean, read]!

**Theorem 10.2 (Congruence valuation bounded by Selmer + $Ш^1$ + class number + tame ramification: `CutCoreUnit.main`).**
*Assume `GlobalTheory.Published.GlobalArtinReciprocity` (`[Lean]` / `[Open]`). Let $D$ be a step-$i$
unit datum over host field $E = D.\mathrm{host}$ at prime $\ell$, with DVR extension index
$L = \operatorname{len}_{\mathcal O}(\mathcal O / (\ell)) \ge 1$ and tame auxiliary prime set $Q_i$.
Then the normalized $\ell$-adic congruence valuation `D.nd.vcc i π` satisfies*
$$D.\mathrm{nd}.\mathrm{vcc}(i, \pi)
\le \mathrm{sPi}(i, \pi)
+ \sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)
+ v_\ell(h_E)
+ R.t \sum_{q \in Q_i} \mathrm{lenUnit}_\ell\bigl(\mathcal O / (\zeta_q - 1)\bigr),$$
*where $\mathrm{sPi}(i, \pi)$ is the $\rho$-Selmer length bound and $h_E = \lvert \mathrm{Cl}(\mathcal O_E) \rvert$
is the class number of $E$.*
*(Lean: `GlobalTheory.CutCoreUnit.main`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:44`.)* [Lean, read]

*Proof.* Start from Proposition 10.1 (`CutDetOrd.main`, via `ccOff_univ` at `:24`), which bounds
$\operatorname{len}_{\mathcal O}(\mathcal O / \mathrm{ccOff}(\pi))$ before dividing by $L = \operatorname{len}_{\mathcal O}(\mathcal O / (\ell))$:

1. **The cuspidal $\rho$-block (`cocRho`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:56–66`):** the local–global Selmer comparison
   (`CountL.main`, `LocalGlobalSelmer.main`, `SelClass.main`; Lemma 10.9 and the discussion after
   it, §10.4.5) bounds $\operatorname{len}_{\mathcal O}(\mathrm{cocRho}(\pi))$ by
   $\operatorname{len}_{\mathcal O}\mathrm{selPi}$, that is, by $L \cdot \mathrm{sPi}(i, \pi)$. This
   block has **no** tame term.
2. **Why $c = 0$ gives the class number $v_\ell(h_E)$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:89–102`):**
   For the first scalar block $c = 0 \in \mathrm{Fin}\,t$, the block character is
   $\chi_1\chi_1^{-1} = 1$ (`chiRatO … 1`). Its $1$-cocycles are therefore continuous homomorphisms
   $G_E \to K/\mathcal O$, and no duality is needed. First peel off ramification at $Q_i$
   (`Peel.main`, Lemma 10.9), at a cost of $\operatorname{len}(\mathcal O/(\zeta_q - 1))$ per
   $q \in Q_i$. The remaining homomorphisms are unramified at every place: at $w \mid \ell$ by
   `CutTrivIne.main`, and elsewhere by `QuadAt`/`PolyAt` and `UnrOut`. Invoking the explicit
   hypothesis `hA : GlobalTheory.Published.GlobalArtinReciprocity` (`:44–45`),
   `GlobalTheory.UnramHom.length_le_classNumber hA` (Lemma 10.11, `[Lean, read]`) bounds their
   length by $L \cdot v_\ell(h_E)$. After dividing by $L$, the block contributes
   $v_\ell(h_E) + \sum_{q \in Q_i} \mathrm{lenUnit}_\ell\bigl(\mathcal O / (\zeta_q - 1)\bigr)$.
3. **Why $1 \le c < t$ gives $\sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)$ (`:103–114`):**
   For every $c \in \mathrm{Fin}\,t$ with $c \ge 1$, set $e := (c : \mathbb N) \in \{1, \dots, t - 1\} = \mathrm{Ioo}(0, R.t)$
   (reindexed in Lean via `Nat.add_sub_cancel`, since $(c + 1) - 1 = c$). The block character is
   $\chi_{c+1}\chi_1^{-1} = \chi_{\mathrm{cyc}}^{-e}$. After peeling $Q_i$, the cocycles are local
   coboundaries above $\ell$ and unramified elsewhere. Inflation then maps them, coordinatewise,
   into $Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e)\bigr)$ itself (no Poitou–Tate
   duality). `length_cyclotomic_block_cocycles_le_sha` (Lemma 10.10, `[Lean, read]`) bounds the
   $c$-th block, divided by $L$, by
   $$\mathrm{shaLen}(E, \ell, e) + \sum_{q \in Q_i} \mathrm{lenUnit}_\ell\bigl(\mathcal O / (\zeta_q - 1)\bigr).$$
4. **Summing over $c \in \{0, 1, \dots, t - 1\}$:** Adding $c = 0$ and $1 \le e < R.t$ collects the
   $t$ copies of $\sum_{q \in Q_i} \mathrm{lenUnit}_\ell(\mathcal O / (\zeta_q - 1))$ into
   $R.t \sum_{q \in Q_i} \dots$ and yields the exact inequality of Theorem 10.2! $\square$

*(Fidelity note on `GlobalArtinReciprocity` `[Lean]` + `[Open]`.)* Notice our strict adherence to the
book's tagging rules (`notes/proof-map.md`, node `P18`): `CutCoreUnit.main` takes
`hA : GlobalTheory.Published.GlobalArtinReciprocity` as an explicit `Prop` hypothesis (discharged
upstream in `EveryCharacterOfLiteratureOfVWin.lean` `[Lean]`). That `CutCoreUnit.main` proves
Theorem 10.2 from `hA` is `[Lean, read]`; in **Chapter 18** (`Section 18.2`), we also read the
`Prop` definition `GlobalTheory.Published.GlobalArtinReciprocity`
(`src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70–72`)
line by line (`R3` / `[Lean, read]`), confirming that it states full idèlic global Artin reciprocity
over every number field $E$, while its `1,015`-module upstream proof cone
(`src/Development/WeilBound/CoreStatements/StandardPublishedResults/StandardTheoremStatements/GlobalArtinReciprocity.lean:8`)
remains `[Open]`.

### 10.4.3 Killing the $\rho$-Selmer term by twisting (`twist_kills_selmer` & `LinkFam.main`)

What happens to the cuspidal Selmer term $\mathrm{sPi}(i, \pi)$ on the right-hand side of Theorem 10.2?
Unlike the cyclotomic $Ш^1$ terms — which depend **only on the fixed CM host field $E$** and not on
which step $j \in \{1, \dots, m\}$ we are at! — an uncontrolled cuspidal Selmer group $\mathrm{sPi}(i, \pi)$
could depend on the $j$-th automorphic packet and accumulate uncontrollably!

**Proposition 10.3 (Killing $\mathrm{sPi}$ via character twisting and summing over $\ell$: `twist_kills_selmer` and `LinkFam.main`).**

1. **Selmer bound at a chosen good twist (`twist_kills_selmer`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:8`).**
   *If the chosen twist is good at every twisted place (`TwGoodAt`, i.e. it satisfies `GoodTw`,
   `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:219`), and the
   Selmer length of each $\pi$ is bounded by that of its twist (`SignatureChoiceCondition`), then
   `KillAt` holds: $\mathrm{sPi}(i, \pi) \le \nu_L(\ell) + \varepsilon_L(\ell)$, and the tame sum
   over $Q_i$, multiplied by $t$, is at most $\varepsilon_L(\ell)$.* [Lean, read] "Killing" thus means
   bounding by $\nu_L + \varepsilon_L$, not literal annihilation. The existence of a good twist is a
   separate input: `TwistingCharacterExistence`
   (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:166`), a `Prop`
   inside the bundle `admitted` (Proposition 10.12 and §10.4.6).
2. **Summing $\log \ell \cdot \mathrm{vcc}$ across all primes $\ell$ and closing `LinkEta` (`GlobalTheory.LinkFam.main`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean:11`, and `closed_linkEta_of_duty`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEta.lean:13`).**
   *Multiplying Theorem 10.2 (at the chosen Selmer-killing twist) by $\log \ell$ and summing over all
   rational primes $\ell$ converts:*
   - $\sum_\ell (\log \ell)\,v_\ell(h_E) = \log h_E$ *(controlled within $(\log x)^2 N_c$ alongside
     tame ramification)*;
   - $\sum_\ell \log \ell \sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e) = \sum'_\ell \mathrm{vvTerm}(D, \ell)$; *and*
   - *the finite tame cyclotomic-unit sum over $q \in Q_i$, establishing `LinkN` (`LinkFam.main`,
     `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean:11`), while `closed_linkEta_of_duty` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEta.lean:13`)
     closes the companion local twisting-cover predicate `LinkEta` (`LocsCoverTw`,
     `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:49`).* [Lean, read]

*(Reading boundary.)* We read `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean` (207-module cone; it contains definitions only),
`ChosenTwistAnnihilatesSelmerGroups.lean`, `LinkNAlongFamilyOfLocalBounds.lean`, and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEta.lean`
in full (`R3` / `[Lean, read]`). §10.4.6 follows `TwistingCharacterExistence` one level further. It
enters `Stmt` as the hypothesis `adm2`. Its producers in the archive (`admissibleBounds_of_all`,
`abstract_form_of_lattice_run`, `admAB_of_toric_parts`) are discussed there, where the Chebotarev
input `GlobalTheory.TwSys.Cheb` is also located. Section 10.4.7 traces the all-coprime-powers witness
used on the path from `src/Main.lean`, and §10.4.7.1 reads the lattice transport and the index steps
of the producers. The motivating notes are in
`remark.pdf` p. 4, items 14–15, 17 [Paper].

### 10.4.4 Complete proof of `divinN_of_hypV`: how $\sqrt{b} = \exp(x^\varepsilon/2)$ closes `DIVinN`

To finish Chapter 10, let us prove `divinN_of_hypV` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:1–130`,
leaf-inclusive import cone **311** modules, read 100% line by line at `R3`) — the exact bridge from
`HypV`, `LinkN`, and `SmallLevelRankEq` to `DIVinN` [Lean, read]!

**Theorem 10.4 (From `HypV`, `LinkN`, and `SmallLevelRankEq` to `DIVinN`: `divinN_of_hypV`).**
*Let `Fm : FamP eps` ($\varepsilon > 0$). Assume the three family hypotheses:*

1. `(hV : HypV Fm.toFamCore)` *(`VVle D.host.E D.R.t (sqrt L.sc.b)` eventually along `Fm`);*
2. `(hN : LinkN Fm)` *(`∃ C, LinkN_at (Fm.L x i) j C` eventually along `Fm` whenever `ShaFinOdd` holds); and*
3. `(hR : SmallLevelRankEq Fm)` *(`(Fm.L x i).dZ0 j = (Fm.D x i).what₂.D0` eventually for all $j \in \{1, \dots, m\}$, supplied by `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Link.lean:20`).*

*Then `DIVinN Fm` holds with constant $\lvert C \rvert + 1$: eventually for all $x \ge x_0$, all family
indices $i$, and all lifts $j \in \{1, \dots, m\}$, `DIVinN_at (Fm.L x i) j (|C| + 1)` holds at the
chain parameters $B_0 = f\,m\,b\,x^\varepsilon$ and $L = x^\varepsilon$.*
*(Lean: `vvRecord`, `log_sq_le_rpow`, `divinN_at`, and `UpperTheory.Top.divinN_of_hypV`,
`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:17,59,76,117`.)* [Lean, read]

*Proof.* Fix $\varepsilon > 0$ and choose $x \ge \max(\max(x_1, \max(x_3, x_4)), \max(x_6, \mathrm{Fm}.x_1 + 1))$
(`:123`) large enough that $(\log x)^2 \le x^\varepsilon$ (`log_sq_le_rpow`, `:59`, since $\log x = o(x^{\varepsilon/2})$)
and `HypV`, `LinkN`, and `SmallLevelRankEq` all hold for $D = \mathrm{Fm}.D(x, i)$ and
$L_{\mathrm{sz}} = \mathrm{Fm}.L(x, i)$ ($b = L_{\mathrm{sz}}.\mathrm{sc}.b = \exp(x^\varepsilon) \ge 1$).

1. **Deduce `ShaFinOdd`, summability, and $\sum'_l \mathrm{vvTerm}(D, l) \le \sqrt{b}$ (`vvRecord`, `:17–57`):**
   Recall from Chapter 4 (Definition 4.4(4)) that `VVle E R.t B` ($B = \sqrt{b} \ge 0$) states that
   odd-twist `Sha` is finite and for **every** finite set $S$ of primes $\ell$,
   $$\sum_{\ell \in S} \log \ell \sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e) \le \sqrt{b}.$$
   - First, `VVle` explicitly carries finiteness of odd-twist `Sha` at every prime $\ell$, directly
     supplying `hf : ShaFinOdd D` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:22–30, 54–57`).
   - Second, since every term $\mathrm{vvTerm}(D, l) \ge 0$ and every finite partial sum
     $\sum_{l \in S} \mathrm{vvTerm}(D, l)$ is bounded above by $\sqrt{b}$, Mathlib's
     `summable_of_sum_le` gives `hs : Summable (vvTerm D)` and `Real.tsum_le_of_sum_le` gives
     $$\sum'_l \mathrm{vvTerm}(D, l) \le \sqrt{b} \le b$$
     (using $b = \exp(x^\varepsilon) \ge 1$ so $\sqrt{b} \le b$, `:127–128`)!
2. **Rewrite $d_{Z_0}(j) = D_0$ via `SmallLevelRankEq` and close `DIVinN_at` (`divinN_at`, `:76–115`):**
   Feed `hf : ShaFinOdd D` and `hs : Summable (vvTerm D)` into `hN` at step $j \in \{1, \dots, m\}$,
   and apply the third hypothesis `hR : SmallLevelRankEq Fm` (`hd : L.dZ0 j = D.what₂.D0` at `:78, 95`)
   together with the definitional identities `L.B0 = f * m * b * x^eps` (`:92`) and `L.sc.L = x^eps`
   (`:93`). Setting $y := x^\varepsilon \ge 1$, we have $f m b y^2 = y B_0$ (`:105`),
   $(\log x)^2 N_c \le y N_c$ (`:106`), and $\sum'_l \mathrm{vvTerm}(D, l) \le b \le B_0 \le y(B_0 + N_c)$
   (`:100, 112`). Hence
   $$\mathrm{etaSum}(L_{\mathrm{sz}}, j)
   \le D_0\,\Bigl(\lvert C \rvert\,y(B_0 + N_c) + y(B_0 + N_c)\Bigr)
   = D_0 \cdot (\lvert C \rvert + 1)\,x^\varepsilon\,(B_0 + N_c),$$
   which is literally `DIVinN_at L_sz j (|C| + 1)` (`:96–115`), proving `DIVinN Fm` (`:117–131`)! $\square$

Pause and look at what Theorem 10.4 just accomplished! Remember Chapter 5's `SZ.T3`
(`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:53`): to prevent the congruence error from stopping at $x^{2/3}$, the
chain needed $B_0 \ll n\,m\,b\,x^\varepsilon$ (remember $f = 2\lvert\varphi.A\rvert \asymp n$!).
Because `divinN_of_hypV` achieves **$B_0 = f\,m\,b\,x^\varepsilon$** as soon as
$$\sum_\ell \log \ell \sum_{1 \le e < R.t} \operatorname{len}_{\mathbb Z_\ell}\,Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e)\bigr)
\le \sqrt{b} = \exp\bigl(x^\varepsilon / 2\bigr),$$
**we do NOT even need a polynomial bound on $Ш^1(E)$ — a subexponential bound $\exp(x^\varepsilon / 2)$
is already strong enough to beat $b = \exp(x^\varepsilon)$ and close `TopG`!** Proving that
subexponential window bound `VWin` across our cyclotomic CM host fields $E$ is the sole remaining piece
of Part II — and the subject of **Chapter 11**!

### 10.4.5 The DVR determinant lemma and block cocycle lengths

Sections 10.4.1–10.4.2 used four imported lemmas as black boxes: a determinant–length inequality over
a discrete valuation ring, a block-determinant identity, a "peeling" lemma for auxiliary primes, and
a bound of cyclotomic cocycles by $Ш^1$. This section opens all four, together with the Fitting-ideal
step inside `CutDetOrd.main` that connects them. Everything below was read line by line in the
pinned archive, down to Mathlib or to the definitions named in each proof, except where a
declaration is explicitly tagged `[Lean]`.

**Motivation [Expository].** The congruence ideal $\mathrm{ccOff}(\pi)$ is an ideal of a DVR
$\mathcal O$, so its size is a single number $\operatorname{len}_{\mathcal O}(\mathcal O/\mathrm{ccOff}(\pi))$.
The cocycle side is a module. The bridge between a number and a module is a determinant. If a square
matrix $\Theta$ over $\mathcal O$ has all its "relations" inside a module $S$, then
$v(\det\Theta) \le \operatorname{len}_{\mathcal O} S$. If every determinant one can form from relations
lies in an ideal $I$, then $I$ is no bigger than $(\det\Theta)$ for the best $\Theta$, and
$\operatorname{len}(\mathcal O/I) \le v(\det\Theta)$. The idea that a congruence ideal is bounded by a
module of Galois cohomology classes goes back to Ribet's modular construction of unramified
extensions `[Ribet1976]` and to Mazur–Wiles `[MazurWiles1984]`. The lattice-and-cocycle form closest to
the archive is Skinner–Urban's "Constructing coycles" [sic] (`[SkinnerUrban2014]`, §4). There each functional
$\varphi$ on a lattice gives a cocycle $c_\varphi(g) = \varphi(\chi^{-1}(g)\sigma(g)\bar\epsilon^* - \bar\epsilon^*)$
(their map (4.4.3.a)). Lemma 10.8 below builds the cocycles $\gamma \mapsto \varphi(y_\gamma)$ in the same
way. The archive cites none of these papers; the comparison is ours.

#### A worked example over $\mathbb Z_p$

**Example 10.5 (one $2 \times 2$ block) [Expository].** Let $\mathcal O = \mathbb Z_p$,
$K = \mathbb Q_p$, $A = M_2(\mathbb Z_p)$, and let $\psi = \mathrm{id} : A \to M_2(\mathbb Z_p)$ (one
block, $d = 2$, one generator, $g = 1$). Let the relation module be the left ideal
$\mathrm{Rel} = A\,M$ generated by
$M = \begin{pmatrix} p & 1 \\ 0 & p^2 \end{pmatrix}$, $\det M = p^3$.

1. *Solution module.* The solution module of Lemma 10.5 below is
   $\mathrm{Sol} = \{y \in (\mathbb Q_p/\mathbb Z_p)^2 : \theta y = 0 \text{ for all } \theta \in \mathrm{Rel}\} = \ker\bigl(M : (\mathbb Q_p/\mathbb Z_p)^2 \to (\mathbb Q_p/\mathbb Z_p)^2\bigr)$.
   The equations are $p y_1 + y_2 = 0$ and $p^2 y_2 = 0$. They give $y_2 = -p y_1$ and $p^3 y_1 = 0$,
   so $\mathrm{Sol} \cong p^{-3}\mathbb Z_p/\mathbb Z_p \cong \mathbb Z/p^3$ is cyclic of length $3$.
2. *Fitting-type coefficients.* Every element of $\mathrm{Rel}$ has the form $C M$ with
   $C \in M_2(\mathbb Z_p)$. For $\theta_k = C_k M$ we get
   $\det\bigl(\sum_k X_k \theta_k\bigr) = \det\bigl(\sum_k X_k C_k\bigr) \cdot p^3$, so every coefficient
   lies in $I = p^3\mathbb Z_p$. Lemma 10.5 then gives
   $3 = \operatorname{len}(\mathbb Z_p/p^3) \le \operatorname{len}\mathrm{Sol} = 3$, with equality.
3. *What the proof does here.* The row vectors occurring as rows of elements of $\mathrm{Rel}$ form
   $N = \mathbb Z_p^2 M$. The proof chooses generators of $N$ (here the rows $(p, 1)$, $(0, p^2)$ of
   $M$), takes $\Theta = M$, and computes the content of the one-variable polynomial
   $\det(X_1 M) = p^3 X_1^2$. The content is $p^3$ and the primitive part is $X_1^2$.
4. *Only $v(\det)$ matters.* For $M' = \operatorname{diag}(p, p^2)$ one gets
   $\mathrm{Sol} \cong \mathbb Z/p \oplus \mathbb Z/p^2$. The elementary divisors differ, but the length
   is again $3 = v(\det M')$.
5. *Degenerate case.* For $M_0 = \begin{pmatrix} p & 1 \\ 0 & 0 \end{pmatrix}$ ($\det M_0 = 0$), the
   solution module contains $\{(y_1, -p y_1)\} \cong \mathbb Q_p/\mathbb Z_p$ and has infinite length.
   The inequality holds trivially, which is the branch $\det = 0$ in the proof of Lemma 10.5.
6. *Two scalar blocks.* Take $A = \mathbb Z_p \times \mathbb Z_p$ with the two projections as blocks
   ($d_1 = d_2 = 1$) and $\mathrm{Rel} = p^a\mathbb Z_p \times p^b\mathbb Z_p$. Then
   $\mathrm{Sol}_1 \cong \mathbb Z/p^a$ and $\mathrm{Sol}_2 \cong \mathbb Z/p^b$. The product of the two
   generic $1 \times 1$ determinants has all coefficients in $p^{a+b}\mathbb Z_p$, and the bound reads
   $\operatorname{len}(\mathbb Z_p/I) \le a + b$. Block lengths add. This is the shape of
   Proposition 10.1: one $\rho$-block plus $t$ scalar blocks.

For $p = 3$ we counted the $p^N$-torsion of the three solution modules by brute force ($N \le 5$). The
counts stabilise at $3^3$ for $M$ and $M'$ and grow like $3^N$ for $M_0$. We also checked the
divisibility claims in items 2 and 6 on 2,000 random integer instances each (script `check_example.py`
in the run directory). This is a local consistency check, not part of the formal record.

#### The determinant–length inequality

**Lemma 10.5 (DVR determinant lemma).** *Let $\mathcal O$ be a DVR with fraction field $K$, let $A$ be
an $\mathcal O$-algebra (not necessarily commutative), let $J$ be a finite set, and let
$\psi_j : A \to M_{d_j}(\mathcal O)$ ($j \in J$) be surjective $\mathcal O$-algebra maps. Let
$g \ge 0$, let $\mathrm{Rel} \subseteq A^g$ be a left $A$-submodule, and let $I \subseteq \mathcal O$ be
an ideal. For $\theta \in M_g(A)$ write $\psi_j(\theta)$ for the $g d_j \times g d_j$ matrix with
$((p, a), (q, b))$-entry $\psi_j(\theta_{pq})_{ab}$. Assume that for every $n$, every
$\theta_1, \dots, \theta_n \in M_g(A)$ whose rows lie in $\mathrm{Rel}$, and every monomial, the
corresponding coefficient of $\prod_{j \in J} \det\bigl(\sum_{k} X_k\, \psi_j(\theta_k)\bigr) \in \mathcal O[X_1, \dots, X_n]$
lies in $I$. Then*
$\operatorname{len}_{\mathcal O}(\mathcal O/I) \le \sum_{j \in J} \operatorname{len}_{\mathcal O} \mathrm{Sol}_j$,
*where $\mathrm{Sol}_j = \{(y_q)_{q} \in ((K/\mathcal O)^{d_j})^g : \sum_q \psi_j(\theta_q)\, y_q = 0 \text{ for all } \theta \in \mathrm{Rel}\}$.*
*(Lean: `GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DeterminantLemmaDiscreteValuationRingQuotientLenStatement.lean:6`,
a one-line wrapper around `GlobalTheory.DetGen.length_quot_le_sum_length`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DeterminantLemmaDiscreteValuationRingQuotientLen.lean:259`.)* [Lean, read]

*Reading against Lean.* The hypothesis is universal: $\forall n\ \forall \theta\ \forall m$, over all
families of relation matrices and all monomials. Lemma 10.5 is therefore strong on the hypothesis side
and has no existential in its conclusion. Lengths are `Module.length`, valued in $\mathbb N_\infty$. If
some $\mathrm{Sol}_j$ has infinite length, the inequality holds trivially. $\mathrm{Sol}_j$ is written
in Lean as
`⨅ θ ∈ Rel, LinearMap.ker (∑ q, (matKO (ψ j (θ q))).comp (LinearMap.proj q))` on
$(\mathtt{KOG}\ \mathcal O\ d_j)^g$, where `KOG O d` is $K^d/\mathcal O^d$
(`src/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean:651`) and `matKO`
is matrix multiplication on it
(`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GlobalCore.lean:10`). All lengths
are $\mathcal O$-lengths, so no ramification factor $L$ appears yet. In the solution module,
$\mathrm{Sol}_j \cong \operatorname{Hom}_A(A^g/\mathrm{Rel}, (K/\mathcal O)^{d_j})$, with $A$ acting on
$(K/\mathcal O)^{d_j}$ through $\psi_j$.

*Proof.* Four steps, all in `DeterminantLemmaDiscreteValuationRingQuotientLen.lean`.

1. *Gauss's lemma over a DVR (`exists_C_mul_primitive`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DeterminantLemmaDiscreteValuationRingQuotientLen.lean:20`; `length_quot_le_of_coeff_prod`, `:47`).*
   Write each polynomial as $F_j = c_j G_j$, where $c_j$ is a coefficient of minimal valuation. Then
   $G_j$ has a unit coefficient, and its reduction modulo the maximal ideal is nonzero. The residue
   polynomial ring is a domain, so $\prod_j G_j$ has a unit coefficient. The matching coefficient of
   $\prod_j F_j$ is $(\prod_j c_j) \cdot \text{unit} \in I$, hence $(\prod_j c_j) \subseteq I$. This
   gives $\operatorname{len}(\mathcal O/I) \le v(\prod_j c_j) = \sum_j v(c_j) \le \sum_j v(F_j(x_j))$
   for any evaluation points $x_j$, because $c_j \mid F_j(x_j)$.
2. *A determinant is at most the length of its "integral preimages" (`addVal_det_le_length`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DeterminantLemmaDiscreteValuationRingQuotientLen.lean:76`).*
   Let $M$ be a square matrix over $\mathcal O$, $\pi : K^\iota \to V$ a map whose kernel consists of
   integral vectors, and $S \subseteq V$ a submodule containing $\pi(y)$ whenever $My$ is integral.
   Then $v(\det M) \le \operatorname{len} S$. If $\det M \ne 0$, the map $u \mapsto \pi(M^{-1}u)$ sends
   $\mathcal O^\iota$ into $S$ with kernel inside $M\mathcal O^\iota$. Since
   $\operatorname{len}(\mathcal O^\iota/M\mathcal O^\iota) = v(\det M)$, the bound follows. If
   $\det M = 0$, a kernel vector $v$ with $v_i \ne 0$ gives the elements
   $\pi(v/(v_i\varpi^n)) \in S$, whose annihilators shrink to $(\varpi^n)$. Hence
   $\operatorname{len} S = \infty = v(0)$.
3. *One relation matrix realises the bound (`exists_family_span`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DeterminantLemmaDiscreteValuationRingQuotientLen.lean:165`; `exists_relations`, `:187`).*
   Let $N \subseteq \mathcal O^{g \times d}$ be the module of row vectors $v$ such that, for every
   row index $a$, some $\theta \in \mathrm{Rel}$ has $\psi(\theta)$ equal to $v$ in row $a$ and zero
   elsewhere. Surjectivity of $\psi$ shows that every row of every $\psi(\theta)$, $\theta \in \mathrm{Rel}$,
   lies in $N$: multiply $\theta$ on the left by a preimage of a matrix unit. By Smith normal form,
   $N$ is spanned by $g d$ vectors. Assembling their realisers gives one $\Theta$ with rows in
   $\mathrm{Rel}$ and $\psi(\Theta)$ equal to the matrix of these generators. Step 2, applied with
   $\pi$ the projection $K^{g \times d} \to ((K/\mathcal O)^d)^g$, gives
   $v(\det\psi(\Theta)) \le \operatorname{len}\mathrm{Sol}$.
4. *Assembly (`length_quot_le_sum_length`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DeterminantLemmaDiscreteValuationRingQuotientLen.lean:259–271`).* Choose $\Theta_j$ by Step 3 for each block.
   Apply the hypothesis with $n = |J|$ and $\theta_k = \Theta_{j(k)}$. Evaluate the $j$-th factor at
   the indicator vector of $k = j$, which gives $\det \psi_j(\Theta_j)$, and apply Step 1. $\square$

The two standard facts used in Steps 1–2 were also read:
$\operatorname{len}(\mathcal O^\iota/M\mathcal O^\iota) = v(\det M)$
(`length_quotient_range_mulVecLin_eq_addVal_det`,
`src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableSpanSpanOfDetNeZero.lean:89`,
reducing via `:67` to Smith normal form in `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthQuotientSpanSingleton.lean:25`
and to the infinite-length case in `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsDualNeZeroCompEqZero.lean:26`),
and additivity of $v$ over finite products (`addVal_finset_prod`, `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableSpanSpanOfDetNeZero.lean:32`,
proved in `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/Imports.lean:7`). Below
them is Mathlib (`Submodule.smithNormalForm`, `Mathlib/LinearAlgebra/FreeModule/PID.lean:538`;
`IsDiscreteValuationRing.length_quotient_pow_maximalIdeal`, `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:555`),
which we did not reread.

#### Block determinants stay Hecke-valued

**Lemma 10.6 (block determinants; `GlobalTheory.BlockDet.main` and `GlobalTheory.BlockDetPoly.main`).**
*Let $T$ be an $\mathcal O$-subalgebra of functions $X \to \mathcal O$, and let $R$ be an
$\mathcal O$-subalgebra of functions $X \to M_n(\mathcal O)$. Assume that for all
$a_1, \dots, a_m \in R$, every coefficient function $x \mapsto \operatorname{coeff}_d \det\bigl(\sum_k X_k\, a_k(x)\bigr)$
lies in $T$. Then for every $g \times g$ array $\Theta$ of elements of $R$, the function
$x \mapsto \det\bigl(\text{the } gn \times gn \text{ block matrix } \Theta(x)\bigr)$ lies in $T$
(`BlockDet.main`). More generally, the coefficient functions of
$\det\bigl(\sum_k X_k\,\Theta_k(x)\bigr)$ for families $\Theta_1, \dots, \Theta_m$ lie in $T$
(`BlockDetPoly.main`).*
*(Lean: `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetOneAddSmulBlkMem.lean:89` and
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CMemCoeffSub.lean:99`; $\mathcal O$ is
any commutative ring here.)* [Lean, read]

The hypothesis says that the determinant is a $T$-valued polynomial law on $R$. This is the
determinant point of view of Chenevier and the pseudo-character point of view of Bellaïche–Chenevier
`[BellaicheChenevier2009]` [Expository].

*Proof.* (`BlockDet.main`.) Work over $B = (X \to \mathcal O)[\varepsilon]/(\varepsilon^{N+1})$,
where $N = gn$, and let $S \subseteq B$ be the image of $T[\varepsilon]$. The $S$-span of $R$ is an
algebra all of whose determinants lie in $S$ (`det_sum_smul_mem`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetOneAddSmulBlkMem.lean:60`). Since $\varepsilon$ is
nilpotent, $1 + \varepsilon\Theta_{00}$ is a unit of that algebra. The Schur complement turns
$\det(1 + \varepsilon\,\mathrm{blk}\,\Theta)$ into
$\det(1 + \varepsilon\Theta_{00}) \cdot \det\bigl(1 + \varepsilon\,\mathrm{blk}(\Theta_{pq} - \varepsilon\,\Theta_{p0}u\Theta_{0q})\bigr)$,
where $u = (1 + \varepsilon\Theta_{00})^{-1}$. Induction on $g$ (`det_one_add_smul_blk_mem`, `:21`)
gives $\det(1 + \varepsilon\,\mathrm{blk}\,\Theta) \in S$. Finally, the coefficient of $\varepsilon^N$
in $\det(\varepsilon M + 1)$ is $\det M$ (Mathlib `coeff_det_X_add_C_card`,
`Mathlib/LinearAlgebra/Matrix/Polynomial.lean:72`), so $\det M \in T$. (`BlockDetPoly.main`.) Apply
`BlockDet.main` after extending scalars to $\mathcal O[X_1, \dots, X_m]$. The subalgebra `coeffSub`
(`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CMemCoeffSub.lean:8`) of functions all of whose coefficients lie in $T$ inherits the hypothesis
(`C_mem_coeffSub`, `:29`; `det_comb_mem`, `:42`). $\square$

#### The Fitting-ideal step: relations force determinants into the congruence ideal

Recall the objects of `CutDetOrd.main`
(`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:59`).

- $X'$ is a finite set of "points" mapping to eigensystems by $p$, and $T'$ is the Hecke algebra as
  functions on $X'$.
- $A = \mathtt{spanAlg}(T', r \circ p)$ is the $\mathcal O$-algebra of functions $X' \to M_{n_V}(\mathcal O)$
  spanned by $T'$-multiples of the representation matrices
  (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:321`).
- $y_\gamma = (\chi_1(\gamma)^{-1} r(\gamma) - 1) \cdot E$ are the "cocycle generators". Here $E$ is
  the rank-one element `Eel` (`src/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean:467,551`).
- By Noetherianity, finitely many $\gamma_1, \dots, \gamma_g$ generate all $A$-combinations of the
  $y_\gamma$ (`exists_gens`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:346`).
- $\mathrm{Rel} \subseteq A^g$ is the module of $\theta$ with $\sum_q \theta_q y_{\gamma_q}$ vanishing
  on $p^{-1}(X_s)$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:75–83`).
- At the distinguished point $\pi'$, conjugation by $P, Q$ (`exists_conj`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:167`) puts every
  $a \in A$ into block-diagonal form $\operatorname{diag}(\psi_\rho(a), \psi_{\chi,1}(a), \dots, \psi_{\chi,t}(a))$
  (component 3 of Definition 10.1, `src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:27–29`).
  Block-diagonality makes the blocks $\mathcal O$-algebra maps (`exists_homs`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:196`). They are
  surjective: the $\rho$-block by component 4 (`src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:30`), and the scalar
  blocks trivially. They are packaged as `blockHom` over the index set $\{\rho\} \sqcup \{1, \dots, t\}$
  (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:365,369`).

**Proposition 10.7 (Fitting inclusion).** *For every $n$, every family $\theta_1, \dots, \theta_n$ of
$g \times g$ matrices over $A$ with rows in $\mathrm{Rel}$, and every monomial, the coefficient of
$\det\bigl(\sum_k X_k \psi_\rho(\theta_k)\bigr) \cdot \prod_{c=1}^{t} \det\bigl(\sum_k X_k \psi_{\chi,c}(\theta_k)\bigr)$
lies in $\mathrm{ccOff}(i, X_s, \pi)$.* In other words, the product of the block Fitting ideals of
$A^g/\mathrm{Rel}$ lies in the congruence ideal.
*(Lean: the third argument of `determinantLemma…` inside `CutDetOrd.main`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:99–133`.)* [Lean, read]

*Proof.*

1. *Hecke-valuedness.* The first clause of component 12 of Definition 10.1
   (`CharpolyCoeffsInSubalgebra`, `src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:62`;
   `src/Formalism/SharpRestriction/LevelLetterCocycles/QuotientHomNonvanishingBound.lean:431`) is exactly the hypothesis of Lemma 10.6 for $R = A$ and
   $T = T'$. By `BlockDetPoly.main` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:101`), the function
   $f(x') = \operatorname{coeff}_m \det\bigl(\sum_k X_k \theta_k(x')\bigr)$ lies in $T'$.
2. *Vanishing away from $Z$.* Take $x'$ with $p(x') \in X_s \setminus Z$. `exists_ne_zero` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:37`)
   produces $\eta$ and $s$ with $y_s(x')\eta \ne 0$. Its proof uses that $E(x')$ has rank one and
   that `NoChiOff` forbids nonzero fixed vectors of the twisted representation. The vectors
   $v_q = y_{\gamma_q}(x')\eta$ are then not all zero, since $y_s$ is an $A$-combination of the
   $y_{\gamma_q}$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:107–114`). The relation property gives $\sum_q \theta_{k,p,q}(x')\, v_q = 0$ for
   every $k$ and $p$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:115–119`). The generic matrix $\sum_k X_k \theta_k(x')$ therefore has a nonzero
   kernel vector over $K[X]$, and its determinant vanishes (`det_generic_eq_zero`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:295`). So $f(x') = 0$.
3. *Into the congruence ideal.* An element of $T'$ that vanishes on $p^{-1}(X_s \setminus Z)$ takes
   its value at $\pi'$ in $\mathrm{ccOff}(i, X_s, \pi)$ (`value_mem_ccOff`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:15`). Here $\mathrm{ccOff}$ is the ideal generated by
   the values at $\pi$ of Hecke operators vanishing on $X_s \setminus Z$
   (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GlobalCore.lean:21`). The proof
   writes $f$ in the unique $T$-basis of $T'$ supplied by component 8 of Definition 10.1 and checks
   coordinatewise.
4. *Block factorisation at $\pi'$.* Conjugating by $1 \otimes P$ (`det_blocks`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:144`;
   `det_generic_blocks`, `:254`) turns $f(\pi')$ into the product of the $\rho$-block generic
   determinant and the $t$ scalar ones (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:120–133`).
   $\square$

**Lemma 10.8 (solutions are restrictions of cocycles; `GlobalTheory.CutDet.length_sol_le`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:77`).** *Each solution module $\mathrm{Sol}_j$ of
Lemma 10.5 for the data above has length at most that of the cocycle module
$\mathtt{cocW}(\psi_j)$, that is, $\mathrm{cocRho}$ for $j = \rho$ and $\mathrm{cocChi}(c)$ for
$j = c$ (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GlobalCore.lean:31,39,41`).* [Lean, read]

*Proof.* $(K/\mathcal O)^d$ is injective over the PID $\mathcal O$ (Baer's criterion, `baer_KOG`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:20`). Given a solution $w$, the map $\theta \mapsto \sum_q \psi(\theta_q) w_q$ factors through
$\theta \mapsto \sum_q \theta_q y_{\gamma_q}$, because its kernel lies in $\mathrm{Rel}$. It therefore
extends to an $\mathcal O$-linear $\varphi$ on all of $X' \to M_{n_V}(\mathcal O)$ (`exists_ext`,
`:40`). This $\varphi$ is $\psi$-semilinear on $A$-multiples and kills combinations vanishing on
$p^{-1}(X_s)$, so $\gamma \mapsto \varphi(y_\gamma)$ is one of the spanning cocycles of
$\mathtt{cocW}(\psi)$, with values $w_q$ at $\gamma_q$. Hence $\mathrm{Sol} \subseteq$ (restriction of
$\mathtt{cocW}$ to $\{\gamma_q\}$), and restriction does not increase length. $\square$

Proposition 10.1 is now completely proved. Lemma 10.5 is applied with $I = \mathrm{ccOff}$
(`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:90`), its hypothesis is Proposition 10.7, and
Lemma 10.8 bounds each block (`:134–140`).

#### From block cocycles to Selmer, class group and $Ш^1$

The proof of Theorem 10.2 (`CutCoreUnit.main`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:44`)
bounds the $1 + t$ cocycle modules of Proposition 10.1 one at a time.

**Lemma 10.9 (peeling ramification at auxiliary primes; `GlobalTheory.Cut.Peel.main`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthEqInfKerAddMap.lean:52`).**
*For every $\mathcal O$-submodule $C$ of maps $G_E \to (K/\mathcal O)^k$ and every finite set $Q$ of
places, there is $C' \le C$ whose restrictions to the inertia groups at all $q \in Q$ vanish, with
$\operatorname{len} C \le \operatorname{len} C' + \sum_{q \in Q} \operatorname{len}(C|_{I_q})$.* [Lean, read]

*Proof.* Use induction on $Q$ (`exists_le_map_eq_bot`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthEqInfKerAddMap.lean:23`). At each step, apply additivity of
length on $0 \to C_0 \cap \ker f \to C_0 \to f(C_0) \to 0$ for the restriction $f$ to $I_q$
(`length_eq_inf_ker_add_map`, `:8`, via Mathlib `Module.length_eq_add_of_exact`,
`Mathlib/RingTheory/Length.lean:171`). Then use
$f(C_0) \subseteq f(C)$. $\square$

Lemma 10.9 is a bookkeeping lemma, not a local–global comparison. The output is existential ($\exists C'$),
and the cost $\sum_q \operatorname{len}(C|_{I_q})$ is bounded in `CutCoreUnit.main` by
$\operatorname{len}(\mathcal O/(\zeta_q - 1))$ per block and per $q$
(`inertiaCocycleBlock_length_le_of_quadraticRelation`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:87–88`) [Lean].
The two calls apply it to scalar blocks (`:73` and
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthQuotEqZeroIff.lean:109`). The **local–global Selmer comparison** for
the $\rho$-block is a separate chain (`:56–66`), read in full.

1. First, `CountL.main` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthGlobalCocyclesLeSumPlacesOver.lean:102`)
   is applied place by place over $w \mid \ell$ with local defect $e = 0$. It returns $C' \le \mathrm{cocRho}$
   whose local classes all lie in the Bloch–Kato finite part, and costs
   $\#\{w \mid \ell\} \cdot 0 \cdot \operatorname{len}(\mathcal O/\ell) = 0$.
2. Next, `LocalGlobalSelmer.main` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalGlobalSelmer.lean:7`)
   shows these cocycles are unramified outside $\ell$, $S$ and $Q$. Its proof writes
   $y_\gamma = (\tilde r(\gamma) - 1)E$ and uses `UnrOut`.
3. Then `SelClass.main` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCocyclesLeCoboundariesAddSelmer.lean:81`)
   maps $C'$ to $H^1$. The kernel consists of coboundaries, and the image lies in the Selmer group
   `selPi`, with the Bloch–Kato condition at $w \mid \ell$, no condition at $S \cup Q$, and the
   unramified condition elsewhere (`mk_mem_selG`, `:48`).
4. Finally, the coboundary part has length $0$ because $\delta_{51}$ is a unit (`:64–66`; the bound
   `length_cutCoboundaryModule_le_unitDelta` is [Lean]).

So $\operatorname{len}\mathrm{cocRho} \le \operatorname{len}\mathrm{selPi}$, and the $\rho$-block
carries **no** tame term.

**Lemma 10.10 (cyclotomic blocks are controlled by $Ш^1$;
`GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCyclotomicBlockCocyclesLeShaStatement.lean:6`,
wrapper around `GlobalTheory.Cut.ShaBound.main`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCyclotomicBlockCocyclesLeSha.lean:372`).**
*Let $2 \le c \le t$, and let $C$ be an $\mathcal O$-module of continuous $1$-cocycles
$G_E \to K/\mathcal O$ for the character $\chi_c\chi_1^{-1}$. Assume that at every place $w \mid \ell$
the local restriction of every $f \in C$, transported through the local bridge, lies in `BD`, the
module of coboundaries $g \mapsto g v - v$
(`src/Formalism/WeaklyAdmissibleFiltrations/StatementTor.lean:119`); so $f$ is locally a
coboundary at $w$. Assume also that every $f \in C$ vanishes on the inertia groups at
all $v \nmid \ell$. Then*
$\operatorname{len}_{\mathcal O} C \le \operatorname{len}_{\mathcal O}(C \cap B^1) + \operatorname{len}_{\mathcal O}(\mathcal O/\ell) \cdot \operatorname{len}_{\mathbb Z_\ell} Ш^1\bigl(G_{E,S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-(c-1))\bigr)$.
[Lean, read]

*Proof.*

1. *The block character is a negative cyclotomic power.* $\chi_c\chi_1^{-1} = \chi_{\mathrm{cyc}}^{-(c-1)}$
   (`chiRatO_apply`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCyclotomicBlockCocyclesLeSha.lean:360`).
2. *Coordinates.* A $\mathbb Z_\ell$-basis of $\mathcal O$ gives a $\mathbb Z_\ell$-linear bijection
   $K/\mathcal O \cong (\mathbb Q_\ell/\mathbb Z_\ell)^{f}$ with $f = \operatorname{rank}_{\mathbb Z_\ell}\mathcal O$
   (`exists_coord`, `:100`). It intertwines the block action with the twist by
   $\chi_{\mathrm{cyc}}^{-(c-1)}$ (`:375–379`).
3. *Each coordinate is a Selmer-trivial cocycle.* Every coordinate $a_j(f)$ satisfies `LocTriv`
   (`:206`; checked at `:386–404`, the local part via `cob_of_bridge`, `:333`). That is, it is a
   cocycle for $\mathbb Q_\ell/\mathbb Z_\ell(-(c-1))$, unramified outside $\ell$, and a coboundary
   on each decomposition group above $\ell$.
4. *Inflation lands in $Ш^1$.* Such a cocycle vanishes on the closed normal subgroup generated by
   inertia outside $S_\ell$ (`LocTriv.vanish`, `:212`). It is therefore inflated from $G_{E,S_\ell}$
   (`LocTriv.mem_range`, `:262`), and its class lies in $Ш^1$ (`mk_mem_Sha`, `:273`). This yields
   linear maps $\Psi_j : C \to Ш^1$ (`exists_toSha`, `:286`).
5. *Joint kernel.* If $\Psi_j(f) = 0$ for all $j$, then $f$ is a global coboundary (`:406–412`).
6. *Length count (`length_le`, `:71`).* We have
   $\operatorname{len}_{\mathcal O} C = \operatorname{len}_{\mathcal O} B + \operatorname{len}_{\mathcal O}(C/B)$
   and $\operatorname{len}_{\mathbb Z_\ell}(C/B) \le f \cdot \operatorname{len}_{\mathbb Z_\ell} Ш^1$.
   Since $\operatorname{len}_{\mathbb Z_\ell} = \operatorname{len}_{\mathcal O} \cdot [k_{\mathcal O} : \mathbb F_\ell]$
   (Mathlib `IsLocalRing.length_restrictScalars`, `Mathlib/RingTheory/LocalRing/Length.lean:54`) and
   $f = \operatorname{len}_{\mathbb Z_\ell}(\mathcal O/\ell)$ (`length_quot`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCyclotomicBlockCocyclesLeSha.lean:27`), the residue
   degree cancels. $\square$

*Reading against Lean, and corrections to §10.4.2.*

- **Twist index.** The twist is $e = c - 1$. In `CutCoreUnit.main` the lemma is called with
  $c = c' + 1$ for $c' \in \{1, \dots, t-1\}$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:106`).
  This is why Theorem 10.2 sums $\mathrm{shaLen}(E, \ell, e)$ over $1 \le e < t$.
- **No duality.** No Poitou–Tate duality is used. The cocycles map directly into $Ш^1$ of the same
  module $\mathbb Q_\ell/\mathbb Z_\ell(-e)$.
- **$L$ factor.** The factor $\operatorname{len}_{\mathcal O}(\mathcal O/\ell)$ is the ramification
  index of $\mathcal O/\mathbb Z_\ell$. It is the $L$ of Theorem 10.2 and is divided out by `lenUnit`
  (`src/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:32`).
- **Coboundary term.** $\operatorname{len}_{\mathcal O}(C \cap B^1)$ is `lenCob`
  (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/LenCob.lean:15`). It vanishes in
  the application because $\delta_{51}$ is a unit (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:111–113`).
- **$\mathbb N_\infty$ lengths.** Products and lengths live in $\mathbb N_\infty$. If
  $\mathrm{shaLen} = \infty$, the bound is empty.

**Lemma 10.11 (the trivial block and the class number; `GlobalTheory.UnramHom.length_le_classNumber`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexDvdClassNumber.lean:172`).**
*Assume `GlobalArtinReciprocity`. If $C$ is an $\mathcal O$-module of cocycles for the trivial block
character $\chi_1\chi_1^{-1} = 1$ (so they are homomorphisms $G_E \to K/\mathcal O$) that vanish on
every inertia group, then*
$\operatorname{len}_{\mathcal O} C \le \operatorname{len}_{\mathcal O}(\mathcal O/\ell) \cdot v_\ell(h_E)$.
[Lean, read]

*Proof.* Artin reciprocity for the CM, hence totally complex, host field gives a global Artin map
`art`. An everywhere-unramified homomorphism is trivial on the image under `art` of the kernel of
"ideles $\to$ class group" (`eq_one_of_class`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexDvdClassNumber.lean:117`). That image has index dividing $h_E$
(`index_dvd_classNumber`, `:152`). Then use strong induction on the index (`length_le`, `:18`). Peel
off an element of prime order $p$. Its evaluation lands in the $p$-torsion of $K/\mathcal O$, which is
$0$ for $p \ne \ell$ and has length at most $\operatorname{len}(\mathcal O/\ell)$ for $p = \ell$
(`length_torsionBy_le`, `:82`). $\square$

In `CutCoreUnit.main` the hypothesis "unramified everywhere" for the trivial block is assembled from
`CutTrivIne.main` at $w \mid \ell$
(`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ActDEqOfEqOne.lean:48`, read) and from
the peeled module elsewhere (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:98–102`). Again no
duality is involved. The class-field-theory input is the named Prop `GlobalArtinReciprocity`, whose
statement Chapter 18 compares with the literature; its proof cone remains [Open].

**Assembly of Theorem 10.2 (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:138–174`).**

- Proposition 10.1 gives
  $\operatorname{len}(\mathcal O/\mathrm{ccOff}) \le s + \sum_{c} \bigl(L \cdot (h \text{ or } \mathrm{shaLen}) + \sum_{q \in Q}\operatorname{len}(\mathcal O/(\zeta_q - 1))\bigr)$.
  Here $s = \operatorname{len}\mathrm{selPi}$, $L = \operatorname{len}(\mathcal O/\ell)$, and
  $h = v_\ell(h_E)$ occurs for $c = 0$.
- Summing over $c$ collects $L(h + \sum_{1 \le e < t}\mathrm{shaLen})$ and $t$ copies of the tame sum
  (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:142–146`).
- Dividing by $L$ gives the rational inequality of Theorem 10.2. The tame term is
  $t\sum_{q}\mathrm{lenUnit}$, and $\mathrm{sPi} = s/L$.
- Because `lenUnit` uses `toNat` (and `toNat ⊤ = 0`), the proof needs the finiteness hypotheses
  `Br.sFin` (finite Selmer length, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:44,54`) and $\mathrm{shaLen}(e) < \infty$ (`:121–123`) before
  converting.

#### What remains `[Lean]` or `[Open]` in this section

These are cited at statement level only:

- `inertiaCocycleBlock_length_le_of_quadraticRelation`;
- `inertia_restriction_polynomial_condition_second_form`;
- `localCocycles_aboveEll_inCut_unitDelta`;
- `finiteQuotientCocycleSpans_le_continuousCocycles`;
- `length_cutCoboundaryModule_le_unitDelta`;
- `cutVal_coord_eq_zero` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CutValueMemHeckeValueIdealOffSupport.lean:27`);
- the local bridge API `Br.*`;
- the Galois-group facts `normal_NS`, `isClosed_NS` and `exists_smul_eq_of_isPlaceOver`
  (used at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCyclotomicBlockCocyclesLeSha.lean:233,237,242`).

They remain [Lean]. The proof cone of `GlobalArtinReciprocity` remains [Open].

### 10.4.6 Twist existence: how the Selmer-killing character is chosen

**Motivation [Expository].** Lemmas 10.9–10.11 control every block except the cuspidal Selmer length
$\mathrm{sPi}(i, \pi)$, which depends on the lift. Twisting the lift by a finite-order character
$\psi$, ramified only at a set $Q$ of auxiliary split primes, changes the Selmer group. The price is
paid at $Q$, through the tame terms $\operatorname{len}(\mathcal O/(\zeta_q - 1))$. The archive needs a
twist for which the Selmer length, the tame price and several lattice indices are all small at once.
The construction has two separate parts. A **bookkeeping lemma** uses a twist once chosen. An
**existence statement** says that such a twist exists.

**Proposition 10.12 (what `twist_kills_selmer` proves).** *Let $C$ be a choice of twists (`NChoice`)
tied to the chain (`NChTie`), and suppose the chosen twist is good at every twisted place (`TwGoodAt`,
`src/Formalism/SharpRestriction/LevelLetterCocycles/TwGood.lean:196`). That is, at every twisted
place it satisfies `GoodTw` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:219`).
Suppose also that the Selmer length of each $\pi$ is bounded by the Selmer length of its twist, and
the tame sum by the twist's tame valuations (`SignatureChoiceCondition`,
`src/Formalism/SharpRestriction/LevelLetterCocycles/JointConditionsZpowers/CommutingEndomorphismCondition.lean:33`).
Then `KillAt` holds (`:45`): for every twisted local datum $i$ and every good $\pi$, the Selmer group
is finite and $\mathrm{sPi}(i, \pi) \le \nu_L(\ell) + \varepsilon_L(\ell)$. Moreover,
$t \cdot \sum_{q \in Q_i}\mathrm{lenUnit}(\mathcal O/(\zeta_q - 1)) \le \varepsilon_L(\ell)$.*
*(Lean: `GlobalTheory.NLink.twist_kills_selmer`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:8`;
wrapper `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroupsStatement.lean:7`;
consumed at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsHubDataFamily.lean:49`.)* [Lean, read]

*Proof (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:10–32`).* `TwGoodAt` at the place $w(i)$ supplies
nonnegative errors $\varepsilon_T(s)$. Their sum over signatures is at most the twist budget
$\varepsilon_{\mathrm{tw}}$, and they bound the twisted Selmer lengths by
$\nu + \varepsilon_T(s)$ (`:14`, `:20–22`). Combined with `SignatureChoiceCondition` and the
identities $\varepsilon_{\mathrm{tw}} = \varepsilon_L(\ell)$ (`:16–17`) and
$\nu = \nu_L(\ell)$ (`:29`), this gives the Selmer bound. The tame bound is the `partD` clause of
`GoodTw` multiplied by $t$ (`:31–32`). $\square$

So "kills" means "bounds by $\nu_L + \varepsilon_L$". The lemma constructs nothing; the twist and its
goodness are inputs. This sharpens Proposition 10.3(1).

**Where existence lives.**

- `TwistTheoremAtIndex` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:233`) asserts that a `GoodTw` twist
  $(Q, k', \psi')$ exists at a nonzero-index place.
- It is the conclusion `aux₃` of `Stmt` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:329`), which `GlobalTheory.export_of_inputs` proves for
  all data
  (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:493`,
  top-level proof read).
- The proof takes the bundle `admitted` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:324`) as a hypothesis. Its second
  component `adm2` (`:305`) is **`TwistingCharacterExistence`** (`:166`). It quantifies over every
  nonzero-index place $i$ satisfying the Bloch–Kato set hypothesis `SetHyp`, every
  $\varepsilon' > 0$, every lattice family $F$ satisfying `ABHyp` (`:125`) and every finite set $A_0$
  of places. For these it provides $Q$, $k'$ and a ray-class character
  $\psi' : \mathrm{RCG}(Q) \to \mathcal O_{k'}^\times$ (`:170`). That character satisfies `PsiOk`,
  the three error clauses `partAT`, `partC`, `partD`, and the lattice-index bound
  `partAB` (`:150`, `:171–173`).
- `export_at_setting` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:456`) transports such a character to a `GoodTw` twist.
  Its body and its helpers `export_at` and `abHyp_fam` are read in §10.4.7.1 [Lean, read].

**What a good character must satisfy.** The clauses are defined in
`src/Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean:289–330`; we read these
definitions [Lean, read].

- `PsiOk` (`:289`). Every $P \in Q$ is split (`IsSplitPl`), of residue degree $1$, with
  ramification index `eWL` equal to $1$. $Q$ is disjoint from $S_0 \cup A_0$, and $k' \ge 1$. The
  character $\psi' \circ \mathrm{art}$ has open kernel and satisfies the conjugation condition
  `AntiHom`. It takes values in the cyclic group generated by `zk i k'`, is ramified exactly at $Q$
  (`RamExactly`), and is trivial above $\ell$ (`TrivAbove`).
- `partAT` (`:304`). There are errors $\varepsilon_T(s) \ge 0$ with $\sum_s \varepsilon_T(s) \le \varepsilon'$
  such that every good signature $s$ has twisted Selmer length at most $\nu + \varepsilon_T(s)$.
- `partC` (`:317`). Every theta evaluation at the twist is nonzero, with $\ell$-adic valuation in
  $[-N_0, c_0 + \varepsilon']$.
- `partD` (`:323`). The tame price satisfies $t \sum_{P \in Q} \mathrm{tameVal}(P) \le \varepsilon'$.
- `SetHyp` (`:327`). The side conditions that do not depend on the twist: `SelfDual` and `NoJump`
  for good signatures, nonvanishing theta sums, `SOk`, $100 \le r$, and $2r \le g_k$.

Proposition 10.12 uses only `partAT`, which gives the Selmer bound, and `partD`, which gives the
tame bound (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:14`).
The remaining clauses of `GoodTw` are discarded there.

Twist existence is therefore a Prop-valued hypothesis of `Stmt`, not a theorem of
`IntegralHeckeForms.lean`. That file contains only definitions. Section 10.4.7 traces the all-powers witness used on the path from `src/Main.lean`.

**How the archive constructs a twist when it does.** Three producers of `TwistingCharacterExistence`
occur in the archive.

1. `admissibleBounds_of_all`
   (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TypePreservedOfAdmissibleIntegral.lean:25`,
   read) only specialises the "all coprime powers" version to the power $1$.
2. `abstract_form_of_lattice_run`
   (`src/Formalism/SharpRestriction/LevelLetterCocycles/LinearIndependentSmulOfNeZero.lean:2183`)
   derives it from `SelmerSeriesChoice` and `Pack.Main`. Its `partAB` step is read in §10.4.7.1;
   the two inputs stay [Lean].
3. `admAB_of_toric_parts`
   (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:355`;
   top-level proof read, with its `partAB` step in §10.4.7.1; deeper dependencies not) shows the shape
   of an actual construction.
   - Take a tame inertia element $z$.
   - From `GaloisSideTwistedSelmerAuxiliaryPrimes`
     (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:70`),
     take $2R$ auxiliary places $P$ that avoid a prescribed finite set and satisfy Frobenius
     conditions inside an open normal subgroup. This hypothesis also supplies Selmer polynomials, one
     of whose low-degree coefficients has valuation at most $v(\ell^{\nu})$.
   - Close $P$ under conjugation to get $Q$ (`exists_isQ`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:52`).
   - Choose a level $M$ and exponents $e_q$ so that the Selmer polynomials, evaluated at
     $\zeta^{\ell^{e_q}} - 1$, have small valuation (`exists_level`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:321`).
   - Take $\chi(x) = \prod_q \zeta^{\ell^{e_q} x_q}$ on the $\ell$-power quotient of
     $\prod_{q \in Q}(\mathcal O_E/q)^\times$ (`prodChar`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:178`). Factor it through the ray class
     group, $\psi' = \chi \circ \phi$ (`exists_factor`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:283`).
   - Check `PsiOk` and `partD` (`psiOk_partD`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:230`) and the remaining clauses.

   Section 10.4.7 follows the main-path call to the all-powers construction.

**The Chebotarev and class-group inputs, with their source levels.**

| Input | Where it enters | Archive form | Level here |
|---|---|---|---|
| Chebotarev (degree-one primes with prescribed Frobenius, avoiding a finite set) | auxiliary twist primes; `PsiOk` asks for split degree-one primes outside $S_0 \cup A_0$ | `GlobalTheory.TwSys.Cheb` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:11`), equivalent to the Published Prop `ChebotarevDegreeOne` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:12,20`) and supplied to the literature layer by `cheb_of_literature` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:559`) | definition read here; statement fidelity "safe weakening" in Chapter 18; **not named** in `admAB_of_toric_parts`, where the primes come from the hypothesis `GaloisSideTwistedSelmerAuxiliaryPrimes`, whose main-path producer is traced in §10.4.7 |
| Ray class groups and the Artin map | the twist $\psi'$ lives on $\mathrm{RCG}(Q)$ and is pulled back by `art` | data fields of the twist datum `NTw`; factorisation `exists_factor` | [Lean] |
| Class number $h_E$ | trivial block $c = 0$ of Theorem 10.2 | `GlobalArtinReciprocity` hypothesis of `CutCoreUnit.main`, used by Lemma 10.11 | Lemma 10.11 [Lean, read]; Prop compared in Chapter 18; proof cone [Open] |

*Remark [Expository].* Choosing auxiliary primes by Chebotarev so that a twist or a deformation
condition cuts down a Selmer group is the familiar device of Kolyvagin systems and Taylor–Wiles
primes. The archive's version is quantitative. Each choice must keep three costs below a prescribed
$\varepsilon$: the twisted Selmer lengths, the tame price $\sum_q \operatorname{len}(\mathcal O/(\zeta_q - 1))$,
and the lattice-index changes (`partAB`). All three costs are booked in `GoodTw`.

### 10.4.7 Where does `adm2` come from?

**Motivation [Expository].** Proposition 10.12 starts with a chosen twist. To use its bound, we
need auxiliary places and a character for which the Selmer and theta estimates, the tame
cost, and the lattice estimates hold simultaneously. The main proof constructs one choice
that works for every integral power coprime to $\ell$. Keeping the same choice under these
powers matters when the character is used with different embeddings of its coefficient field.

**Example 10.6 [Expository].** Take $\ell=3$, and send the generator of $\mathbb Z/9\mathbb Z$
to a primitive ninth root $\zeta$. For $3\nmid a$, raising this character to the power $a$
permutes the six primitive roots. Their product of differences from $1$ is
$\Phi_9(1)=1+1+1=3$, so each difference has normalized valuation $1/6$ for $v(3)=1$.
Sending the generator to $\zeta^3$ instead gives a root of order $3$, with valuation
$1/2$ by $\Phi_3(1)=3$. A local budget of $1/4$ allows the first choice for every coprime
power and excludes the second. This models the factor $\ell^{e_q}/\varphi(\ell^k)$ in the
tame estimate with $k=2$ and $e_q=0,1$. It checks one local ingredient of the construction.

**Definitions [Lean, read].** The single-character quantifiers are those of
`TwistingCharacterExistence` in §10.4.6. At the same inputs $i,\varepsilon',F,A_0$,
`admissibleIndexBoundAllPowers` chooses $(Q,k',\psi')$ **before** quantifying over
$a\in\mathbb Z$ with $\gcd(a,\ell)=1$. All five clauses must hold for $(\psi')^a$.
`goodTwistExistsAllCoprimePowers` makes the same change to the conclusion of
`TwistTheoremAtIndex`, with the full-rank and basis inputs fixed.
`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AdmissibleIndexBoundAllPowers.lean:14–30`.

**Lemma 10.13 (the twist used by the main proof).** The term on the route from
`riemannHypothesis` constructs the all-coprime-powers witness and passes it directly
to the all-powers lattice export. At the constructed Bloch–Kato setting, its pre-export
witness implies the single-character assertion of `adm2` by taking $a=1$.

*Proof.*

1. **Find the call that needs the twist.** `src/Main.lean:4` uses `rhOfAll`.
   `src/Supplements/Kernels/MainTheorems.lean:7,9` passes `allChi` to `rh_of_every`.
   The latter specializes `EveryCharacter` to the trivial character modulo $1$
   (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:29–32`). The proof of
   `EveryCharacter` starts from the constructed row and passes the literature bundle
   and `vwin_of_row h` together.
   `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:7–11`.

2. **Read the export actually passed to the member construction.** The literature assembly
   calls `every_character_of_theta_integrals_local_matching`, whose last argument to
   `every_character_of_green_v_win` is the definite-side existence theorem.
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810–813`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:68–73`.
   In the latter proof the route runs through `hypotheses_nonempty_of_unramified_exponents_alt`,
   which unpacks the large-exponent bundle as ⟨hP, hMem, hEx⟩ and hands on `hMem`.
   Its producer obtains ⟨hE, –, –, hL', hN⟩ and passes `hE` to the base-lattice theorem.
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/HypothesesNonemptyOfUnramifiedExponents.lean:41–61`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/MemberBundlesLargeUnramifiedExponents.lean:59–63,69–70`.
   The base-lattice proof passes `hE.e1` as the first argument to
   `automorphy_of_hypotheses_alt_alt` and supplies its result `exp` to member closing.
   The export runs through `exportF_isBuiltE_alt_alt` and the two realization wrappers to
   `exportAt_of_bundles_alt`.
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExistsBaseLatticeOfPrime.lean:49–55,70–72,80–81`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/AutomorphyOfHyp.lean:27–32,44–45`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SExport.lean:20–32`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExportAtBundlesStatement.lean:16–17`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExportAtBundles.lean:16–23`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExportAtOfBundlesStatement.lean:16–17`.

3. **Supply Chebotarev and the Galois-side bound.** `hE.e1` is `hCheb`, the first
   component obtained from `twist_front_inputs`.
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ThetaLiftHypothesesOfNonvanishing.lean:34–44`.
   The packet puts the closed theorem `GlobalTheory.Published.cheb_holds` in that slot.
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistFrontInputs.lean:13–14`.
   Its proof applies the forward direction of `chebotarevDegreeOne_iff_cheb` to the archive
   theorem `chebotarevDegreeOne'`. That theorem lifts the prescribed automorphism,
   chooses a cyclotomic crossing field, excludes the finite bad set and restricts a
   prime-norm Frobenius back to the base field. The equivalence takes the fixed field
   of the open normal subgroup, adds the finitely many base-ramified primes to the
   excluded set and identifies the Frobenius congruence with a kernel condition.
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean:17–67`,
   `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ChebotarevDegreeOneIffCheb.lean:20–47`.

   At the twist call, `exportAt_of_bundles_alt` obtains ⟨N0, hI⟩ and fills the
   all-powers component of `ExportAt` with
   `twistAllPowers_of_galoisCohomology_classField`. Its lines 25–27 pass `hCh`
   to the matrix presentation and both order-bound theorems. The presentation
   discards that argument in its first `intro`. The residual branch forwards it to
   `exists_auxiliary_primes_prescribed_frobenius`, and the positive branch calls
   the same implementation, `ChosenPrimes.stepAB`, directly. There `exists_picks`
   uses `exists_pick`, which applies `hC` to the open normal subgroup and the
   finite set enlarged by conjugates.
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerPresentationMatrixOfGaloisCohomology.lean:20–35`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21–31`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BoundModTwoUniformizerAtTwoOfChebotarev.lean:25–35`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAuxiliaryPrimesPrescribedFrobeniusStatement.lean:9–10`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAuxiliaryPrimesPrescribedFrobenius.lean:207–246,344,378`.
   The call supplying these three inputs is recorded here.
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExportAtOfBundles.lean:17–35`,
   `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/AmbientBaseHeq.lean:36–40`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistAllPowersOfGaloisCohomologyClassField.lean:20–30`.

4. **Choose the primes and the character.** `twistTheorem_allPowers_of_selmer_supLattice`
   constructs `hX : GaloisSideTwistedSelmerAuxiliaryPrimes` by calling
   `galois_twisted_selmer_auxprimes_of_matrix_and_bounds` with those three inputs and
   the determinant evaluation theorem. The producer splits on $\nu=0$ and $\nu>0$,
   obtains ⟨R, Dd, M₀, hM₀⟩ and replaces $M_0$ by $\max(M_0,1)$. For each permitted
   $M$ and finite avoided set, the bound gives a common family $P$ of $2R$ auxiliary
   places. For each signature in the specified set and each $Q$ satisfying `IsQ P Q`,
   the presentation gives ⟨a, Φ, hΦ, –⟩, and surjectivity of `toLam` lifts $\det\Phi$
   to $F$. The determinant evaluation proves `SelPoly`; the selected-place bound
   certifies one coefficient of degree at most $Dd$ and valuation at most
   $v(\ell^{\nu})$.
   `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:46–77`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisTwistedSelmerAuxprimesOfMatrixAndBounds.lean:11–63`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:30–40`.

   The next call constructs `hAB` by `admissibleIndexBoundAllPowers_of_conditions`.
   It introduces $i,\varepsilon',F,A_0$, with their hypotheses, and takes $T$ to be
   the good signatures when it unpacks `hX` as ⟨R, Dd, M₀, hM₀, hR⟩.
   It intersects the finitely many open normal subgroups from the theta and lattice
   bounds, and enlarges $A_0$ by the corresponding finite excluded sets.
   It feeds the Selmer, theta, and lattice polynomials to `exists_level` with
   $\varepsilon=\varepsilon'/C$. That call chooses $M,k,e$ before the primitive root
   is specified. The witness $\psi_0$ is the product character factored through the
   ray class group. Only then does the proof introduce $a$ and its coprimality
   hypothesis, use the primitive root $\zeta^a$, and finish the five clauses.
   The tame bound uses $\lvert Q\rvert\le 4R$ and the individual valuation bound
   illustrated in Example 10.6.
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:38–90,92–222`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:321–353`.

5. **See which witness is read.** Line 40 of `TwistTheoremAllPowersOfSelmerSupLattice.lean`
   supplies `hAB` directly to `exportAll_of_six_inputs`. The transport first chooses
   the lattice family, then obtains ⟨Q, k, ψ₀, hall⟩ from `hAB` with
   `levs Y i S ∪ A` as the excluded set. For every coprime $a$ it reads
   `hall a ha`, unpacks the five clauses (including the existential data in
   `partAB`), and uses the lattice inclusion and signed-index bound to return
   `GoodTw` for $(\psi_0)^a$.
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExportAllOfSixInputs.lean:9–14`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:17–53`.
   The receiver actually uses the witness. In the second pass, the exported proposition
   goes through `exists_pre_point_with_henselian_level` into `nonempty_seed_of_kept`.
   There the proof obtains ⟨N0, S, hp, hs⟩, invokes `hp` at the transported place with
   the full-rank, basis and avoidance inputs, then uses `hG0 a ha'` to transfer the
   good twist for any coprime power into the new coefficient setting.
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/FiniteLevelAndSecond.lean:80–88`,
   `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExistsSeed.lean:26–35`,
   `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TwistDataAgreeAcrossCoefficientsSymm.lean:133–168`.

   The single-power `export_of_inputs` unpacks `admitted` and
   hands its second field to `export_at_setting`; the all-powers wrapper
   `exportAll_of_inputs` even discards that second field and takes a separate
   all-powers proof. The six-input export takes those inputs directly.
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:456–489,493–496`,
   `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:59–64`.
   The separate lemma `admissibleBounds_of_all` introduces the same inputs,
   obtains ⟨Q, k', ψ', h1⟩ and returns the witness with `h1 1 isCoprime_one_left`.
   `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TypePreservedOfAdmissibleIntegral.lean:25–28`. $\square$

**Status.** On the traced route the archive proves the stronger twist existence statement
and consumes it directly. The single-character `adm2` is a consequence at that setting.
There is no `admitted` argument at this call site. Chebotarev comes from a proved
theorem in the `Published` namespace. Both the matrix-and-bounds producer of the
auxiliary primes and the application of its result to all good signatures were read
line by line. [Lean, read]

The twist call also takes `PoitouTateTotallyComplex`, `CohDimTwo`, `TameLocal`,
`LocalFiniteness`, `LocalTateDuality`, `LocalEulerChar`, `GlobalFiniteness`,
`GlobalEulerChar`, `UnramifiedOrthogonality`, `ArchimedeanSignatureMatching` and
`GreenbergWiles`, followed by `RayCharacterArtin` and the hypotheses projected from
`hI`. Among the latter, `hI.a2` supplies the distinct `BlochKatoReduction.adm2`
used in `AdmACD`. The dependency claim about the single-power package concerns
`IntegralHeckeForms.adm2`.
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExportAtOfBundles.lean:19–28`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:93–103`.

**Dependency evidence.** The SHA-256-verified DeDeo export of the five main theorems
contains `admissibleIndexBoundAllPowers_of_conditions`, `exportAll_of_six_inputs`,
`galois_twisted_selmer_auxprimes_of_matrix_and_bounds` and `GlobalTheory.Published.cheb_holds`.
The full-name declaration scan finds no `IntegralHeckeForms.Stmt`,
`IntegralHeckeForms.admitted`, `TwistingCharacterExistence`, `export_of_inputs` or
`admissibleBounds_of_all` in that export. The scan is a closure check for the five
roots together. Reachability alone does not establish consumption. The proof
applications above identify where the witness is passed and read.
[DeDeo export, SOURCES V8](../sources/SOURCES.md#v8)

**Remark.** §10.4.8 gives the conditional first-order proof used by both order bounds.
Section 10.4.12 supplies the conditional global Selmer presentation. The cyclotomic prime-norm existence inputs to `chebotarevDegreeOne'` remain [Open] for a full reading;
§10.4.7.1 reads the lattice-specialization transport, and §10.4.7.2 reads the toric supply `PropABCD`
(`propABCD_of_rel`) together with the level-and-exponent lemma behind `exists_level`; §10.4.7.3 reads the theta supply `propE`
and the integrality supplier `admInt_of_sup`; §10.4.7.4 reads the producer of the auxiliary-place family and the Selmer polynomials, `galois_twisted_selmer_auxprimes_of_matrix_and_bounds`, with the `partAT` step. The applications above identify these inputs
and their quantifiers.

The [lattice lifting criterion](#104711-lifting-residual-cocycles-to-the-blochkato-lattice) and [integral annihilator theorem](#104712-integral-local-duality-and-the-two-finite-condition-annihilators) explain the conditional local Selmer input used upstream of the order bounds.

#### 10.4.7.1 Lattice specialization: one index bound for every coprime power

##### Motivation [Expository]

Besides the Selmer, theta and tame clauses used by Proposition 10.12, the predicate `GoodTw` contains three lattice clauses for every block $(j,b)$ with $1\le j\le m$ and $b\in\{\mathrm{true},\mathrm{false}\}$. The twisted theta module must be a lattice, it must lie in a prescribed integral module, and its index may exceed that of the untwisted theta module by at most an error $\varepsilon_{j,b}$, after any further extension of the coefficient ring. The producers of twist existence prove a different statement, the clause `partAB`. It says that every lattice containing the specialized universal theta vectors has bounded index measured from one reference lattice $B$. This subsection reads the transport from `partAB` to the three clauses and traces where `partAB` comes from.

Three features of the transport recur below. The reference lattice is fixed before the twist is chosen, so one $B$ serves every power $\psi_0^a$. The idempotent that cuts out the relevant subspace has a denominator; it is cleared by the same scalar on both sides of each inequality. Indices are normalized by the valuation of $\ell$, so they do not change in the ramified extensions $O\subset O_k\subset O'$ in which the twisted vectors live.

##### Example 10.13a. A specialized rank-two lattice over $\mathbb Z_3[\zeta_9]$ [Expository]

Let $O=\mathbb Z_3$, $V=\mathbb Q_3^2$ and $B=\mathbb Z_3^2$. Let $\zeta$ be a primitive ninth root of unity and $O_k=\mathbb Z_3[\zeta]$. This is a DVR, totally ramified of degree $\varphi(9)=6$ over $\mathbb Z_3$, with uniformizer $\pi=\zeta-1$, so $v_\pi(3)=6$. Model a universal family by the vectors $w_1=(1,0)$ and $w_2=(1,T)$ over $O[T]$, where $T$ plays the role of $[\gamma]-1$ for a generator $\gamma$ of $\mathbb Z/9\mathbb Z$. The character $\gamma\mapsto\zeta^a$ specializes $T$ to $\zeta^a-1$ and gives

$$\Theta_a=\operatorname{span}_{O_k}\{(1,0),\ (1,\zeta^a-1)\}.$$

The coordinate matrix in the standard basis of $B_{O_k}=O_k^2$ is triangular with determinant $\zeta^a-1$, so $O_k^2/\Theta_a\cong O_k/(\zeta^a-1)$. Dividing lengths by $v_\pi(3)=6$ gives three cases.

1. If $3\nmid a$, then $\zeta^a$ is again a primitive ninth root and $\zeta^a-1$ is a uniformizer. Hence $\operatorname{sIdx}(B_{O_k},\Theta_a)=1/6$ for all six residues $a$. This is the lattice form of Example 10.6.
2. If $a\in\{3,6\}$, then $\zeta^a$ has order $3$. From $\Phi_3(1)=3$ we get $v_\pi(\zeta^a-1)=3$, and the index is $1/2$.
3. If $9\mid a$, then $T\mapsto 0$ and $\Theta_0=O_k\cdot(1,0)$ has rank one, so it is not a lattice. The lattices $T_n=\Theta_0+\pi^nB_{O_k}=\operatorname{span}\{(1,0),(0,\pi^n)\}$ contain $\Theta_0$, and $\operatorname{sIdx}(B_{O_k},T_n)=n/6$ is unbounded.

Enlarging a lattice lowers its index from a fixed reference. In case 1, every lattice $T\supseteq\Theta_a$ therefore satisfies $\operatorname{sIdx}(B_{O_k},T)\le 1/6$. Take the untwisted theta module to be $\Theta=B$, so that $\operatorname{sIdx}(B,\Theta)=0$. Then the statement "every lattice containing the specialized vectors has index at most $\operatorname{sIdx}(B,\Theta)+\varepsilon$" holds with $\varepsilon=1/6$ for all coprime $a$ at once. With $\varepsilon=1/4$ it excludes $a=3$, and at $9\mid a$ it fails for every $\varepsilon$. Lemma 10.13d shows that the last failure is forced: a uniform bound over all lattices containing a finitely generated module makes that module a lattice.

##### Example 10.13b. Clearing a denominator and extending scalars over $\mathbb Z_2$ [Expository]

Let $\ell=2$ and $O=\mathbb Z_2$. Let a group of order $c_G=2$ act on $W=\mathbb Q_2^2\oplus\mathbb Q_2^2$ by swapping the summands. The idempotent $e=\tfrac12(1+\sigma)$ projects onto the diagonal $V\cong\mathbb Q_2^2$, and its integral multiple is $A=c_Ge=1+\sigma$. Put the untwisted theta vectors in the first summand: $\theta_s=(u_s,0)$ with $u_1=(1,0)$ and $u_2=(0,1)$. In diagonal coordinates $A\theta_s=u_s$ and $e\theta_s=\tfrac12u_s$. With $B=\mathbb Z_2^2$ we get $A\Theta=B$ and $e\Theta=\tfrac12B$, so

$$\operatorname{sIdx}(B,A\Theta)=0,\qquad \operatorname{sIdx}(B,e\Theta)=-2 .$$

Over $O_k=\mathbb Z_2[i]$, with uniformizer $1-i$ and $v(2)=2$, let the twisted vectors give $A\Theta_\psi=\operatorname{span}\{(1,0),(1,i-1)\}$ and $e\Theta_\psi=\tfrac12A\Theta_\psi$. Then

$$\operatorname{sIdx}(B_{O_k},A\Theta_\psi)=\tfrac12,\qquad \operatorname{sIdx}(B_{O_k},e\Theta_\psi)=-\tfrac32,\qquad \operatorname{sIdx}\bigl((e\Theta)_{O_k},e\Theta_\psi\bigr)=\tfrac12 .$$

The scalar $2$ contributes $\operatorname{rank}\cdot v(2)/v(2)=2$ to both indices measured from $B_{O_k}$ and cancels in the difference. Now pass to $O'=\mathbb Z_2[\zeta_8]$, with uniformizer $\pi'=\zeta_8-1$ and $v_{\pi'}(2)=4$. Since $v_{\pi'}(i-1)=2$,

$$\operatorname{sIdx}(O'^2,O'e\Theta_\psi)=\frac{2-8}{4}=-\frac32,\qquad \operatorname{sIdx}\bigl(O'^2,(e\Theta)_{O'}\bigr)=-\frac84=-2 .$$

The difference is again $1/2$. For the other reference $M=\operatorname{span}\{(1,0),(0,\pi')\}$ the two indices are $-7/4$ and $-9/4$, and the difference is still $1/2$. These are the three moves of Theorem 10.13g below. Both sides are measured from one reference, the common scalar is removed, and the coefficient ring is changed with an arbitrary reference.

##### Definitions [Lean, read]

Fix a nonzero-index place $i$. Let $O$ be the coefficient DVR `X.O i`, with fraction field $K$, and let $\ell$ be the prime `X.l i`. It is a nonzero nonunit in $O$ and in every $O_k$ = `X.Ok i k` (`natCast_l_ne_zero`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:362–369`). Each $O_k$ is a DVR with $O\to O_k$ injective and finite (`X.Ok_inj`, `X.Ok_fin`). Integrality makes this map local. For a block $(j,b)$ write $W$ for the $K$-space `Y.Fm i j b` and $W_0$ for `Fm0`, the subspace on which the unipotent group acts through the type character. Write $e$ for `eG`, the endomorphism given by the idempotent `Y.eAlg i b`, and $V=e(W_0)$ for `V0`. Finally $c_G$ is `restRowsFiniteGroupCard`, and $A=c_G\,e$ is `AO` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:16–37`).

1. **Normalized length and signed index** (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:64–70`). For a DVR $R$ and an $R$-module $M$ put $\lambda_\ell(M)=\operatorname{len}_R(M)/v_R(\ell)$, and for submodules
   $$\operatorname{sIdx}(M,N)=\lambda_\ell\bigl(M/(M\cap N)\bigr)-\lambda_\ell\bigl(N/(M\cap N)\bigr).$$
   Lengths are converted from $\mathbb N\cup\{\infty\}$ with `toNat`, so an infinite length is recorded as $0$. The definition is used only for two lattices in one space, where both lengths are finite.
2. **Lattices** (`:72–73`). `IsLatIn M V` means that $M$ is finitely generated, $M\subseteq V$, and every $x\in V$ has a nonzero multiple in $M$. The last condition says that $M$ and $V$ agree after localization at $R\setminus\{0\}$. In this subsection $V$ is the restriction of scalars of a $K$-subspace or a base change of one.
3. **Theta modules** (`:44–62`). $\Theta=$ `Th Sg` is the $O$-span of the theta vectors $\theta_a$, $a\in Sg$, and $e\Theta=$ `eTh`. For a character $\psi$ of the Galois group with values in $O_k^\times$, $\Theta_\psi=$ `ThPsi` is the $O_k$-span of the twisted theta vectors in $O_k\otimes_OW$, and $e\Theta_\psi=$ `eThPsi` is its image under $e\otimes1$. The module `eThPMt` is the image of the integral structure `MtLat`.
4. **The three lattice clauses** (`:201–215`, used in `GoodTw` at `:226–230`). `IdxAt` $(\varepsilon)$ says: for every DVR $O'$ with an injective finite map $O_k\to O'$ compatible with $O$, and every lattice $M$ of $O'\otimes V$,
   $$\operatorname{sIdx}\bigl(M,\ O'\cdot e\Theta_\psi\bigr)\le\operatorname{sIdx}\bigl(M,(e\Theta)_{O'}\bigr)+\varepsilon .$$
   The second clause says that $e\Theta_\psi$ is a lattice of $O_k\otimes V$. `InclAt` says $e\Theta_\psi\subseteq$ `eThPMt`.
5. **The index clause of twist existence** (`:150–162`). The specialization `specU χ` evaluates the universal theta series `thU`, whose coefficients lie in the group algebra of the finite group `DelQM`, at a character $\chi$ of that group (`:90–96`). For $b\in\{\mathrm{true},\mathrm{false}\}$ put $\chi_b=$ `psiAt b χ`, which is $\chi$ or $\chi^{-1}$ (`src/Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean:87–88`). Then `partAB F ψ' eps'` asserts: there are $M$ and $\chi$ with $\psi'\circ\mathrm{art}=\chi\circ\mathrm{delU}$, and errors $\varepsilon_{j,b}\ge0$ with $\sum_{j,b}\varepsilon_{j,b}\le\varepsilon'$, such that for each block and each lattice $T_\psi$ of $(\operatorname{span}_KF.B)_{O_k}$ containing the vectors $(F.A\otimes1)(\mathrm{specU}\,\chi_b(\mathrm{thU}\,a))$ for $a\in F.S$,
   $$\operatorname{sIdx}\bigl((F.B)_{O_k},T_\psi\bigr)\le\operatorname{sIdx}(F.B,F.\mathrm{Th})+\varepsilon_{j,b}.$$
6. **The reference family** (`fam`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:282–284`). Its fields are the ambient module `Mall` $=$ `Bsup` $\cap\,W_0$ (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:242–243`), an integral lift $z_b$ of $c_G\cdot$`eAlg`, the reference lattice $B=$ `Mall` $\cap\,V$, and the given finite basis sets $S$.

##### Lemma 10.13c (signed-index calculus) [Lean, read]

*Let $R$ be a DVR, $\ell\in R$ a nonzero nonunit and $V$ an $R$-submodule of $W$.*

1. *If $L_1,L_2,L_3$ are lattices in $V$, then $\operatorname{sIdx}(L_1,L_3)=\operatorname{sIdx}(L_1,L_2)+\operatorname{sIdx}(L_2,L_3)$, and $L_3\subseteq L_2$ implies $\operatorname{sIdx}(L_1,L_2)\le\operatorname{sIdx}(L_1,L_3)$.*
2. *An injective linear map $f$ preserves $\operatorname{sIdx}$ and sends lattices of $V$ to lattices of $f(V)$. If $c\ne0$ and $M$ is a lattice in $V$, so is $cM$.*
3. *A finitely generated $L$ in a $K$-space is a lattice in $\operatorname{span}_K L$ (restricted to $R$). Conversely, a lattice in the restriction of a $K$-subspace $V$ spans $V$ over $K$.*
4. *If $R\to S$ is an injective local homomorphism of DVRs and $L_1,L_2$ are lattices in $V$, then $L_1\otimes S$ is a lattice in $V\otimes S$ and $\operatorname{sIdx}_S(L_1\otimes S,L_2\otimes S)=\operatorname{sIdx}_R(L_1,L_2)$.*

*(Lean: `sIdx_add_and_mono`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCommensurableOfIsLatIn.lean:54–70`; `sIdx_map`, `isLatIn_map`, `isLatIn_smul`, `isLatIn_of_span`, `span_of_isLatIn`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:17–61`; `isLatIn_baseChange`, `lenR_baseChange_subquotient`, `sIdx_baseChange`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LenRBaseChangeSubquotient.lean:14–75`.)*

*Proof.* (1) For lattices $M,N$ in $V$ the quotient $M/(M\cap N)$ is finitely generated, and each element has a nonzero multiple in $N$. A finitely generated torsion module over a DVR has finite length, so lattices are length-commensurable, and $\operatorname{sIdx}$ is their signed length divided by $v(\ell)$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCommensurableOfIsLatIn.lean:16–49`). Signed length is additive on commensurable modules and nonnegative when the second module is contained in the first. These are `LengthCommensurable.signedLength_eq_add` and `signedLength_nonneg` [Lean]; the assembly is at `:61–70`. (2) Both relative lengths are preserved by an injective map (`relLength_map_of_injective` [Lean]). An image of a lattice stays finitely generated and contained, and $f(cx)=cf(x)$ transports saturation. If $dx\in M$ with $d\ne0$, then $(cd)x\in cM$ and $cd\ne0$. (3) An element of $\operatorname{span}_KL$ has a nonzero multiple in $L$, by clearing denominators of a finite $K$-combination (`multiple_mem_span_of_mem_localization_span`, Mathlib). Conversely $x=c^{-1}(cx)$ lies in $\operatorname{span}_KL$. (4) For a pure tensor $s\otimes v$ with $cv\in L_1$, the multiple $c\cdot(s\otimes v)=s\otimes cv$ lies in $L_1\otimes S$. Sums and multiples are handled by multiplying the constants (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LenRBaseChangeSubquotient.lean:14–44`). For the index, the $S$-length of $(L_1\otimes S)/(L_1\otimes S\cap L_2\otimes S)$ is $e(S/R)$ times the $R$-length of $L_1/(L_1\cap L_2)$ (`length_baseChange_subquotient_dvr` [Lean]). Also $v_S(\ell)=e(S/R)\,v_R(\ell)$ (`addVal_algebraMap`, `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean:123–132`). The ramification index cancels (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LenRBaseChangeSubquotient.lean:49–75`). $\square$

##### Lemma 10.13d (bounded index forces full rank) [Lean, read]

*Let $R$ be a DVR, $\ell\in R$ a nonzero nonunit, $B$ a lattice in $V$, $T\subseteq V$ a finitely generated submodule and $C\in\mathbb R$. If every lattice $T'$ of $V$ with $T\subseteq T'$ satisfies $\operatorname{sIdx}(B,T')\le C$, then $T$ is a lattice in $V$.*
*(Lean: `isLatIn_of_index_le`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:164–219`.)*

*Proof.* Put $P_n=\ell^nB$. Each $P_n$ is a lattice by Lemma 10.13c(2). So is $T+P_n$: it is finitely generated, lies in $V$, and every $x\in V$ has a nonzero multiple in $P_n\subseteq T+P_n$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:168–172`). Since $P_{n+1}\subseteq\ell P_n\subseteq P_n$, the lattices $T+P_n$ decrease (`:173–179`). Suppose $T$ is not a lattice. If $T+P_n=T+P_{n+1}$ for some $n$, then $P_n\subseteq T+\ell P_n$. The module $P_n$ is finitely generated and $\ell$ lies in the maximal ideal, which is the Jacobson radical of $R$. Nakayama's lemma gives $P_n\subseteq T$, and then the saturation of $P_n$ makes $T$ a lattice (`:181–188`). Hence each inclusion $T+P_{n+1}\subsetneq T+P_n$ is strict. Its quotient has length at least $1$, so $\operatorname{sIdx}(T+P_n,T+P_{n+1})\ge1/v(\ell)$, where $v(\ell)>0$ because $\ell$ is a nonzero nonunit (`:189–205`). By additivity, $\operatorname{sIdx}(B,T+P_n)\ge\operatorname{sIdx}(B,T+P_0)+n/v(\ell)$ (`:206–214`). Taking $n>\bigl(C-\operatorname{sIdx}(B,T+P_0)\bigr)v(\ell)$ and $T'=T+P_n$ contradicts the hypothesis (`:215–219`). $\square$

In Example 10.13a, case 3, the lattices $T+P_n$ are exactly the $T_n$ with index $n/6$.

##### Lemma 10.13e (removing a common scalar) [Lean, read]

*Let $W$ be torsion-free over the DVR $R$, let $B,T,L$ be lattices in $V$ and $c\in R\setminus\{0\}$. If $\operatorname{sIdx}(B,cL)\le\operatorname{sIdx}(B,cT)+\varepsilon$, then $\operatorname{sIdx}(T,L)\le\varepsilon$.*
*(Lean: `index_unscale`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:153–162`.)*

*Proof.* Multiplication by $c$ is injective on $W$. Lemma 10.13c(1) for the lattices $B,cT,cL$ gives $\operatorname{sIdx}(B,cL)=\operatorname{sIdx}(B,cT)+\operatorname{sIdx}(cT,cL)$. Lemma 10.13c(2) gives $\operatorname{sIdx}(cT,cL)=\operatorname{sIdx}(T,L)$. $\square$

##### Lemma 10.13f (passing to a larger coefficient ring) [Lean, read]

*Let $O\to R\to S$ be a tower of algebras with $R,S$ DVRs and $R\to S$ injective and finite. Let $T,V\subseteq W$ be $O$-submodules with $T\otimes R$ a lattice of $V\otimes R$, let $L$ be a lattice of $V\otimes R$, and suppose $\operatorname{sIdx}_R(T\otimes R,L)\le\varepsilon$. Then every lattice $M$ of $V\otimes S$ satisfies $\operatorname{sIdx}_S(M,S\cdot L)\le\operatorname{sIdx}_S(M,T\otimes S)+\varepsilon$, where $S\cdot L$ is the $S$-span of the image of $L$ in $S\otimes_OW$.*
*(Lean: `index_extend`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:130–151`.)*

*Proof.* The map $R\to S$ is local, being finite and injective. The canonical isomorphism $S\otimes_R(R\otimes_OW)\cong S\otimes_OW$ sends $(T\otimes R)\otimes S$ to $T\otimes S$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:115–126`) and $L\otimes S$ to $S\cdot L$ (`:95–113`). By Lemma 10.13c(2),(4), both are lattices of $V\otimes S$, and $\operatorname{sIdx}_S(T\otimes S,S\cdot L)=\operatorname{sIdx}_R(T\otimes R,L)\le\varepsilon$ (`:139–149`). Additivity with the third lattice $M$ gives $\operatorname{sIdx}(M,S\cdot L)=\operatorname{sIdx}(M,T\otimes S)+\operatorname{sIdx}(T\otimes S,S\cdot L)$ (`:150–151`). $\square$

##### Theorem 10.13g (the lattice-index bridge from `partAB` to the twist clauses) [Lean, read]

*Fix $(i,j,b)$ with $i$ a nonzero-index place and $1\le j\le m$, a finite set $S$, and $k,Q,\psi$ with `TwOK` and `UnrG`. Assume `IsotypicPartsInternalDirectSum`, `admT4`, `FullRk` for $Sg=$ `SgJ` and `BasisOf` for $(Sg,S)$. Let $\Theta=$ `Th SgJ`, $\Theta_\psi=$ `ThPsi SgJ` and $B=$ `Mall` $\cap\,V$. Let $\varepsilon\in\mathbb R$ and suppose*

*(H) every lattice $T$ of $O_k\otimes V$ with $(A\otimes1)\Theta_\psi\subseteq T$ satisfies $\operatorname{sIdx}(B_{O_k},T)\le\operatorname{sIdx}(B,A\Theta)+\varepsilon$.*

*Then `IdxAt` $(\varepsilon)$ holds, $e\Theta_\psi$ is a lattice of $O_k\otimes V$, and `InclAt` holds.*
*(Lean: `GlobalTheory.ExportFromInputs.export_at`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:371–450`.)*

*Proof.* **Step 0 (the untwisted side).** By `IsotypicPartsInternalDirectSum`, `Mall` is finitely generated and spans $W_0$ over $K$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:385`). Then $B$ is a lattice of $V$: it is finitely generated as a submodule of `Mall` over the Noetherian ring $O$, it lies in $V$, and any $x\in V\subseteq W_0$ has $c\ne0$ with $cx\in$ `Mall` $\cap\,V$ (`isLatIn_B`, `:286–291`; `goodPart_le_typeSubspace`, `src/Development/AbelianVarietyTheory/Counterexamples/NonGaloisSurvey/MemTypeSubspaceIffUnipotentCharacter.lean:80–84`). By `FullRk` and `BasisOf`, $A\Theta$ is spanned by the finitely many $A\theta_a$, $a\in S$, and spans $V$ over $K$. So $A\Theta$ is a lattice of $V$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:424–427`). Next $A\Theta=c_G\cdot e\Theta$, and $c_G\ne0$ in the characteristic-zero domain $O$ (`:228–236`). Hence $e\Theta$ is finitely generated, because multiplication by $c_G$ is injective on $W$. It lies in $V$ because $\Theta\subseteq W_0$ by the equivariance of the base theta vectors, and it inherits saturation from $A\Theta\subseteq e\Theta$ (`:428–442`). Base change gives lattices $B_{O_k}$ and $(e\Theta)_{O_k}$ of $O_k\otimes V$ (`:389–390`, `:443`).

**Step 1 (the twisted module is a lattice).** The last clause of `IsotypicPartsInternalDirectSum`, applied with `TwOK` and `UnrG`, puts the twisted theta vectors in $(W_0)_{O_k}$. Hence $e\Theta_\psi\subseteq(eW_0)_{O_k}=O_k\otimes V$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:406–413`). By `admT4`, $e\Theta_\psi$ lies in the image of the finitely generated module `MtLat`. It is therefore finitely generated over the Noetherian ring $O_k$, and this inclusion is `InclAt` (`:391–392`, `:404–405`). Since $A\otimes1=c_G(e\otimes1)$, we have $(A\otimes1)\Theta_\psi\subseteq e\Theta_\psi$ (`:397–402`, `:414–418`). Every lattice $T'\supseteq e\Theta_\psi$ thus satisfies (H). Lemma 10.13d with reference $B_{O_k}$ shows that $e\Theta_\psi$ is a lattice (`:419–422`).

**Step 2 (one application of (H)).** Apply (H) to $T=(A\otimes1)\Theta_\psi=c_G\cdot e\Theta_\psi$. It is a lattice by Step 1 and Lemma 10.13c(2) (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:444`). Rewrite the right side over $O_k$. By Lemma 10.13c(4), $\operatorname{sIdx}(B,A\Theta)=\operatorname{sIdx}(B_{O_k},(A\Theta)_{O_k})$, and $(A\Theta)_{O_k}=(A\otimes1)\Theta_{O_k}=c_G\cdot(e\Theta)_{O_k}$ (`:445–446`). Hence
$$\operatorname{sIdx}\bigl(B_{O_k},c_G\,e\Theta_\psi\bigr)\le\operatorname{sIdx}\bigl(B_{O_k},c_G\,(e\Theta)_{O_k}\bigr)+\varepsilon .$$

**Step 3 (removing the denominator).** The module $O_k\otimes_OW$ is torsion-free over $O_k$: $W$ is a $K$-vector space, hence flat over $O$, and tensoring the injection given by a nonzero $c\in O_k$ stays injective (`torsionFree_tensor`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:75–88`, `:393–394`). Lemma 10.13e with $c=c_G$ gives $\operatorname{sIdx}((e\Theta)_{O_k},e\Theta_\psi)\le\varepsilon$ (`:447`).

**Step 4 (all further coefficient rings).** Lemma 10.13f with $R=O_k$, $T=e\Theta$ and $L=e\Theta_\psi$ is `IdxAt` $(\varepsilon)$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:448–450`). $\square$

Only two instances of (H) are used: lattices containing $e\Theta_\psi$, in Step 1, and the module $(A\otimes1)\Theta_\psi$ itself, in Step 2. The hypothesis is stated for all lattices containing the specialized vectors because the producer of the bound does not know $e\Theta_\psi$. Example 10.13a, case 3, shows that it fails when the specialized module drops rank.

##### Proposition 10.13h (the reference family satisfies `ABHyp`) [Lean, read]

*Assume `IsotypicPartsInternalDirectSum`, `GroupAlgebraIntegrality` and `GoodLatticePoints`. Let $z_b\in O[G_0]$ map to $c_G\cdot$`eAlg` in $K[G_0]$, as provided by the first clause of `GroupAlgebraIntegrality`. For `FullRk` and `BasisOf` data $S$, the family `fam z S` satisfies `ABHyp` at every block. Its operator is $F.A=A$ and its theta lattice is $F.\mathrm{Th}=A\Theta$.*
*(Lean: `abHyp_fam`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:297–360`; `zO_eq`, `:245–252`; the identity $F.\mathrm{Th}=A\Theta$ at `:470–472`.)*

*Proof.* The twelve conjuncts of `ABHyp` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:125–148`) are checked in order (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:325–360`). `Mall` is finitely generated and Hecke stable by `IsotypicPartsInternalDirectSum`. The operator $A$ maps `Mall` into `Mall` $\cap\,V$. It lands in $V$ because $A=c_Ge$ and $V=e(W_0)$. It preserves `Bsup` because `Bsup` is stable under the group and $A$ is an $O$-linear combination of group elements (`zO_mem`, `:266–280`; the inclusion at `:310–314`). The $K$-span of $A(\mathrm{Mall})=c_G\,e(\mathrm{Mall})$ is $e(W_0)=V$ (`:317–322`), and $B$ is a lattice there (`:327–329`). The vectors $A\theta_a$, $a\in S$, are linearly independent, and they span over $K$ the same space as $B$ (`:338–340`). The element $z_b$ is central, because its image $c_G\cdot$`eAlg` is central and $O[G_0]\to K[G_0]$ is injective (`central_of_map`, `:254–264`). $A$ commutes with the Hecke operators because the group action does (`:341–345`), and $B$ is Hecke stable (`:330–337`). The integrality of the universal series is made uniform over $S$. Each $a\in S$ has an exponent $c_a$ with $\ell^{c_a}\,\mathrm{thU}(a)$ integral over `Mall`. Take $c=\max_{a\in S}c_a$ and multiply by $\ell^{c-c_a}$ (`:346–360`). The last conjunct is `GoodLatticePoints`. $\square$

##### Theorem 10.13i (lattice clauses at every coprime power) [Lean, read]

*Assume `admissibleIndexBoundAllPowers`, `IsotypicPartsInternalDirectSum`, `GroupAlgebraIntegrality`, `admT4`, `TwistedSeriesSpecialisation` and `GoodLatticePoints`. Let $i$ be a nonzero-index place satisfying `SetHyp`. Let $\varepsilon'>0$, assume `FullRk` at all blocks, and let $S$ be a family of bases and $A_0$ a finite set of places. Then there are $Q$, $k$ and $\psi_0:\mathrm{RCG}(Q)\to O_k^\times$ such that, for every $a\in\mathbb Z$ coprime to $\ell$, `GoodTw` holds for $\psi_0^a$ with excluded set `levs S` $\cup A_0$. The lattice clauses at $(a,j,b)$ are the conclusions of Theorem 10.13g for $\psi=$ `psiAt b` $(\psi_0^a\circ\mathrm{art})$ and $\varepsilon=\varepsilon^{(a)}_{j,b}$. The reference family $F=$ `fam z S` is the same for all $a$.*
*(Lean: `twistModule_all_character_powers_of_admissible`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:17–53`; single character: `export_at_setting`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:456–489`.)*

*Proof.* Choose $z$ from `GroupAlgebraIntegrality` and form $F=$ `fam z S`. It satisfies `ABHyp` by Proposition 10.13h (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:22–23`). Apply `admissibleIndexBoundAllPowers` once, to $(i,\varepsilon',F,\ \texttt{levs }S\cup A_0)$, and obtain $(Q,k,\psi_0)$ together with the clauses for all powers (`:24`). Fix $a$ coprime to $\ell$ and put $\psi'=\psi_0^a$ (`:25–27`). The clauses at $a$ give `PsiOk`, `partAT`, `partC`, `partD` and `partAB` for $\psi'$. The last comes with its own $(M,\chi,\varepsilon^{(a)})$ (`:28`). For each block, `twOK_of_psiOk` turns `PsiOk` into `TwOK` and `UnrG` for $\psi=$ `psiAt b` $(\psi'\circ\mathrm{art})$, and into the disjointness of $Q$ from `levs S` $\cup A_0$ (`:30`; `src/Development/AbelianVarietyTheory/Counterexamples/NonGaloisSurvey/MemTypeSubspaceIffUnipotentCharacter.lean:86–110`).

It remains to derive (H) from `partAB` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:32–52`). Let $T$ be a lattice of $O_k\otimes V$ containing $(A\otimes1)\Theta_\psi$. First, $T$ is a lattice of the space named in `partAB`, since $\operatorname{span}_KF.B=V$ by Lemma 10.13c(3) (`:39–41`). Second, $T$ contains the vectors named in `partAB`. Let $a'\in S$. The relation $\psi'\circ\mathrm{art}=\chi\circ\mathrm{delU}$ and `psiAt_comp` give $\psi=\chi_b\circ\mathrm{delU}$. The set $Q$ avoids the level of $a'$, because `Y.lev a'` $\subseteq$ `levs S` (`:44–48`). `TwistedSeriesSpecialisation` then puts $\mathrm{specU}\,\chi_b(\mathrm{thU}\,a')$ in `ThPsi` $\{a'\}\subseteq\Theta_\psi$, since $S\subseteq$ `SgJ`. Applying $A\otimes1$ lands in $T$ (`:49–52`). Third, $F.\mathrm{Th}=A\Theta$ by `BasisOf` (`:35–37`). The inequality of `partAB` is therefore (H) with $\varepsilon=\varepsilon^{(a)}_{j,b}$. Theorem 10.13g gives `IdxAt`, the lattice property and `InclAt`. With $\sum_{j,b}\varepsilon^{(a)}_{j,b}\le\varepsilon'$ these are the second and third components of `GoodTw`; the other components are `PsiOk`, `partAT`, `partC` and `partD` at $a$ (`:53`).

`export_at_setting` is the same argument for one character. It applies `adm2` to $F$ without a power quantifier and runs the identical step for each block (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:460–489`). $\square$

**Quantifier order and witness dependence.** The family $F$ is fixed first: it depends on $z$ and on $S$, hence neither on $\varepsilon'$ nor on the twist. The triple $(Q,k,\psi_0)$ depends on $(i,\varepsilon',F,\texttt{levs }S\cup A_0)$ but not on $a$. The data $(M,\chi,\varepsilon^{(a)})$ of `partAB` are extracted after $a$. On the main path they are $M$ independent of $a$, $\chi=\chi_0^a$ and $\varepsilon^{(a)}_{j,b}=\varepsilon'/C$ (Proposition 10.13j). The output of Theorem 10.13g depends on $a$ only through $\psi$. The excluded set is enlarged by `levs S` exactly so that `TwistedSeriesSpecialisation` applies to every $a'\in S$. The receiver `nonempty_seed_of_kept` reads the resulting clause at each coprime $a$ (§10.4.7, step 5).

##### Proposition 10.13j (where the index bound comes from on the main path) [Lean, read for the displayed step]

*In `admissibleIndexBoundAllPowers_of_conditions`, the clause `partAB` for $\psi_0^a$ holds with $M$ independent of $a$, with $\chi=\chi_0^a$, and with $\varepsilon_{j,b}=\varepsilon:=\varepsilon'/C$ for all $a$ and all blocks, where $C=\lvert\mathrm{SigG}\rvert+2m+4tR+1$. The index inequality is the toric bound `PropABCD` evaluated at a primitive root, and `exists_level` controls the valuation excess.*
*(Lean: `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:92–222`; `PropABCD`, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:119–139`; `exists_level`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:321–353`.)*

*Proof of the displayed step.* For each block $y=(j,b)$, `PropABCD` applied to $F$ supplies an open normal subgroup $H_y$, a finite set of places $A_y$ and integers $v_y,n_y$. For every admissible level $M$, place family $P$ and finite set $Q$ with `IsQ P Q` (the places over those of $P$) it supplies a polynomial $f_y$ over $O$ satisfying `OrdHyp` $(v_y,n_y)$. Its index statement reads as follows. Let $u$ be a root datum with $u_q^{\ell^M}=1$, let $\chi$ be the character $x\mapsto\prod_qu_q^{x_q}$ of `DelQM`, and suppose $f_y(u-1)\ne0$. Then every lattice $T_\psi$ of $(\operatorname{span}_KF.B)_{O_k}$ containing the specialized $A$-images satisfies
$$\operatorname{sIdx}\bigl(B_{O_k},T_\psi\bigr)\le\operatorname{sIdx}(B,F.\mathrm{Th})+\operatorname{nval}\bigl(f_y(u-1)\bigr)-\frac{v_y}{v(\ell)}$$
(`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:119–139`; used at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:104–105`, `:120–122`). The auxiliary places avoid every $A_y$, and their Frobenius steps lie in every $H_y$ (`:106–115`). `exists_level` chooses $M$, $k$ and exponents $e_q<k$ with $\ell^{e_q}/\varphi(\ell^k)\le\varepsilon$. For every primitive $\ell^k$-th root $\zeta$ and every $y$, it makes $f_y(\zeta^{\ell^{e_q}}-1)\ne0$ with $\operatorname{nval}\le v_y/v(\ell)+\varepsilon$ (`:133–144`). The character $\chi_0=\prod_q(\zeta_k^{\ell^{e_q}})^{x_q}$, with $\zeta_k=$ `X.zk i k`, and the witness $\psi_0=\chi_0\circ\phi$ are formed before $a$ (`:153–161`). For $a$ coprime to $\ell$, $\zeta=\zeta_k^a$ is primitive (`zpow_prim`, `:31–36`). $\chi_0^a$ is the character attached to $u_q=\zeta^{\ell^{e_q}}$ (`:164–171`). On the side $b=\mathrm{false}$ the root is $\zeta^{-1}$, also primitive (`side_root`, `:24–29`). Therefore $\operatorname{nval}(f_y(u-1))-v_y/v(\ell)\le\varepsilon$, and the displayed bound becomes $\operatorname{sIdx}(B_{O_k},T_\psi)\le\operatorname{sIdx}(B,F.\mathrm{Th})+\varepsilon$ (`:218–222`). Finally $\sum_{j,b}\varepsilon=2m\varepsilon\le\varepsilon'$ because $2m\le C$ (`:216–217`). $\square$

One constant $C$ serves all clauses: it is large enough that $\lvert\mathrm{SigG}\rvert\,\varepsilon$ (Selmer errors), $4tR\,\varepsilon$ (tame price) and $2m\,\varepsilon$ (lattice errors) each stay below $\varepsilon'$. The uniformity in $a$ has one source: `exists_level` fixes $M$, $k$ and $e$ before the root is chosen, and its estimate holds for every primitive root. In Example 10.13a this is the equality of $v_\pi(\zeta^a-1)$ for all $a$ prime to $3$.

The two other producers named in §10.4.6 obtain `partAB` as follows.

- `admAB_of_toric_parts` performs the same step for the single root $\zeta_k$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:433–434`, `:461–467`).
- `abstract_form_of_lattice_run` argues by monotonicity (`src/Formalism/SharpRestriction/LevelLetterCocycles/LinearIndependentSmulOfNeZero.lean:2183–2198`). For each block, `SelmerSeriesChoice` and `Pack.Main` provide the lattice $Y_l$ spanned by the specialized $A$-images, with
  $$\operatorname{sIdx}(B_{O_k},Y_l)=\operatorname{nval}(\mathrm{ev})-c\lvert S\rvert\le\operatorname{sIdx}(B,\mathrm{Th})+\varepsilon_{j,b}$$
  (`run_packs`, `:2039–2099`; `Pack.Main`, `:263–270`; `SelmerSeriesChoice`, `src/Formalism/SharpRestriction/LevelLetterCocycles/LatticeVariant.lean:177–188`). Any $T_\psi$ containing the specialized vectors contains $Y_l$, and `sIdx_mono'` gives the bound for $T_\psi$ (`src/Formalism/SharpRestriction/LevelLetterCocycles/LinearIndependentSmulOfNeZero.lean:2013–2035`, `:2161–2181`).

Neither of these two producers is called on the path from `src/Main.lean` (§10.4.7).

##### Example 10.13k. Re-choosing a lattice breaks the transport [Expository]

1. **A reference chosen after the twist.** In Example 10.13a, replace the reference on the twisted side by $B'_a=\Theta_a$, chosen once the power is known. The inequality $\operatorname{sIdx}(B'_a,T)\le\operatorname{sIdx}(B,\Theta)+0$ then holds at $T=\Theta_a$ for every $a$, including $a=3$, because both sides vanish. But $\operatorname{sIdx}(\Theta_{O_k},\Theta_a)$ is $1/6$ or $1/2$. If the reference may depend on the twist, every lattice passes, so the inequality says nothing about the twist. The order "for all $F$, there exist $(Q,k,\psi_0)$, for all $a$" in `admissibleIndexBoundAllPowers` excludes this, because $B$ is a field of $F$.
2. **Different scalars on the two sides.** In Example 10.13b, compare $e\Theta_\psi$ with $A\Theta$ instead of $A\Theta_\psi$ with $A\Theta$. The mixed inequality $\operatorname{sIdx}(B_{O_k},e\Theta_\psi)=-3/2\le0=\operatorname{sIdx}(B,A\Theta)$ holds with $\varepsilon=0$, yet $\operatorname{sIdx}((e\Theta)_{O_k},e\Theta_\psi)=1/2$. The cancellation in Lemma 10.13e needs the same $c$ on both sides.
3. **Different references in `IdxAt`.** Over $O'$ in Example 10.13b, put $M=O'^2$ on the left and $M'=\operatorname{span}\{(1,0),(0,\pi')\}$ on the right. Then $\operatorname{sIdx}(M,O'e\Theta_\psi)=-3/2$ and $\operatorname{sIdx}(M',(e\Theta)_{O'})=-9/4$, so the inequality needs $\varepsilon\ge3/4$, although the true excess is $1/2$. In the opposite assignment it already holds with $\varepsilon=1/4$. `IdxAt` therefore uses one $M$ on both sides.

##### Remarks and reading boundary

*Remark [Expository].* The signed index is Serre's lattice invariant $\chi(X_1,X_2)=\chi(X_1/X_3)\,\chi(X_2/X_3)^{-1}$, $X_3\subseteq X_1\cap X_2$, read through a valuation and normalized by $v(\ell)$. Serre's Proposition 1(a),(b) is the additivity in Lemma 10.13c(1), and Proposition 2, $\chi(X,uX)=(\det u)$, is the determinant formula used in Examples 10.13a and 10.13b ([SerreLocalFields](../sources/SOURCES.md#6-literature), Ch. III, §1, pp. 47–48). Normalizing by $v(\ell)$ rather than by the valuation of a uniformizer makes the index invariant under the ramified extensions $O_k\subset O'$ (Lemma 10.13c(4)). That invariance is what lets `IdxAt` quantify over all further coefficient rings.

| Item | Source | Level here |
|---|---|---|
| Lemmas 10.13c–10.13f, Theorem 10.13g, Proposition 10.13h, `export_at_setting`, `export_of_inputs` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:17–496` | [Lean, read] |
| signed-index assembly and base change | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCommensurableOfIsLatIn.lean:16–70`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LenRBaseChangeSubquotient.lean:14–75` | [Lean, read] |
| signed-length additivity and positivity, `relLength_map_of_injective`, `length_baseChange_subquotient_dvr`, finite length of torsion modules | `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableIffOfLeOfLe.lean:168`; `src/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean:179,362`; `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthBaseChangeQuotientOfMapMaximalIdeal.lean:143`; `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthLocalizedModuleEqZeroOfNotAnnihilatorLe.lean:13` | [Lean] |
| Theorem 10.13i, `twOK_of_psiOk`, type-subspace lemmas | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:17–64`; `src/Development/AbelianVarietyTheory/Counterexamples/NonGaloisSurvey/MemTypeSubspaceIffUnipotentCharacter.lean:61–110` | [Lean, read] |
| `partAB` step of the main-path producer; `exists_level` top level; `PropABCD`, `SelmerSeriesChoice`, `Pack.Main` definitions | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:92–222`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:321–353,433–467`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:119–139` | [Lean, read] |
| `partAB` step of `abstract_form_of_lattice_run` | `src/Formalism/SharpRestriction/LevelLetterCocycles/LinearIndependentSmulOfNeZero.lean:2013–2035,2039–2099,2161–2198` | [Lean, read] |
| toric supply `propABCD_of_rel` and level lemma `GlobalTheory.T.exists_level_order_exponents_small_valuation_determinants` (read in §10.4.7.2); `Pack.main`; producers of `SelmerSeriesChoice` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:293`; called at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:343`; `src/Formalism/SharpRestriction/LevelLetterCocycles/LinearIndependentSmulOfNeZero.lean:2219` | [Lean] here; first two [Lean, read] in §10.4.7.2 |
| main-path suppliers of `IsotypicPartsInternalDirectSum`, `GroupAlgebraIntegrality` and `GoodLatticePoints`; the hypotheses `admT4` and `TwistedSeriesSpecialisation` | `admInt_of_sup_laws`, `admALG_of_commG_var`, `admT3_of_hecke_semisimple` at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:38–40`; hypotheses at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistAllPowersOfGaloisCohomologyClassField.lean:21–30` | [Lean] here; `admInt_of_sup_laws` read in §10.4.7.3 [Lean, read] |
| downstream readers of `IdxAt` and `InclAt` after `goodTw_transfer` | `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TwistDataAgreeAcrossCoefficientsSymm.lean:133–168` and later | not traced here |

The reading in §10.4.7.1 upgrades the transport in §10.4.6 from statement level to a read proof without upgrading the integrality inputs; §10.4.7.2 next reads the toric supply `propABCD_of_rel` and the level-exponent lemma `exists_level_order_exponents_small_valuation_determinants`, and §10.4.7.3 reads `propE` and `admInt_of_sup`.

#### 10.4.7.2 Toric Hecke relations and simultaneous level-exponent selection

##### Motivation [Expository]

Proposition 10.13j reduced the main-path lattice bound `partAB` across all coprime powers $\psi_0^a$ ($\gcd(a,\ell)=1$) to two `[Lean]` supplies left unread at the end of §10.4.7.1:

1. the toric determinant producer `GlobalTheory.TwistDet.propABCD_of_rel`, which turns universal theta specializations at split auxiliary places into a polynomial $f_y\in O[X]$ satisfying `OrdHyp` $(v_y,n_y)$ and bounding $\operatorname{sIdx}(B_{O_k},T_\psi)-\operatorname{sIdx}(B,F.\mathrm{Th})$ by $\operatorname{nval}_{O_k}(f_y(u-1))-v_y/v_O(\ell)$;
2. the level-and-exponent selector `GlobalTheory.T.exists_level_order_exponents_small_valuation_determinants` (invoked inside `exists_level`), which chooses one group-ring level $M$, one cyclotomic order $k$, and one tuple of place exponents $e_q<k$ before any character power $a$ is introduced, so that evaluating at $u_q=\zeta^{\ell^{e_q}}$ keeps both the Selmer determinants and the lattice determinants $f_y$ within $\varepsilon$ of their untwisted baselines for *every* primitive $\ell^k$-th root $\zeta$.

Each supply resolves an obstruction that would otherwise break uniformity across powers. On the toric side, the universal theta series $\mathrm{thU}_Q(a)$ lands in the integral module only after clearing a common $\ell$-power denominator $x=\ell^c$. If the twisted and untwisted coordinates were measured against different reference lattices—or if the baseline $v_y$ were chosen after $(M,Q)$—an uncancelled multiple of $\operatorname{nval}(x^n)$ would shift the signed index by an $O(1)$ error independent of $k$. Fixing a single $O$-basis of $B=F.B(j,b)$ up front makes $\operatorname{nval}_{O_k}(x^n)=\operatorname{nval}_O(x^n)$ cancel identically, while peeling the left places $J_1$ and right places $J_2$ along `ThURel` factors $\det m_Q$ modulo the toric augmentation ideal $\mathfrak I_M=\langle X_{\mathrm{inr}(r)},(1+X_{\mathrm{inl}(r)})^{\ell^M}-1\rangle$ into a right Hecke determinant $D_d(X_{\mathrm{inl}})$ times an intermediate determinant $g$ whose constant term differs from $\det m_0$ by an $O$-unit.

On the level-selection side, two degeneracies threaten evaluation at $\zeta^{\ell^{e_q}}-1$. First, the polynomial family $(F_{M,x},f_{M,y})$ varies with $M$, and unseparated exponents $e_q$ allow distinct monomials to collide and cancel modulo $\varpi^{\nu+1}$. Passing to a Tychonoff cluster point of the coefficient-divisibility tables stabilizes a reverse-lexicographically minimal witnessing multi-index, while super-increasing exponents $e(\mathrm{inl}\,r)=a r$, $e(\mathrm{inr}\,r)=a(r+R)+E$ isolate that witness in univariate degree and push the $\mathfrak I_M$ remainder into high $\varpi$-divisibility via prime-power binomial divisibility. Second, even for a single univariate polynomial with a low-degree witness $w$, evaluating at $\zeta_{\ell^k}-1$ (normalized valuation $1/\varphi(\ell^k)$) can blow up at finitely many levels $k$ where two Newton-polygon slopes tie. Bounding the number of tie levels uniformly in $M$ lets Pigeonhole pick $k$ outside all tie sets at once; restricting to $\gcd(a,\ell)=1$ keeps $\zeta_k^a$ at the same primitive order $\ell^k$, whereas non-coprime powers drop to lower cyclotomic orders that can land inside an excluded tie level.

##### Example 10.13l. Toric Hecke peeling, denominator cancellation, and failure under a lattice switch [Expository]

Take $\ell=5$, base DVR $O=\mathbb Z_5$ ($v_5(5)=1$, residue field $\mathbb F_5$), cyclotomic level $k=2$ with $O_2=\mathbb Z_5[\zeta_{25}]$ of ramification degree $\varphi(25)=20$, and uniformizer $\pi=\zeta_{25}-1$ satisfying $\operatorname{nval}_{O_2}(\pi)=1/20$ and $\operatorname{nval}_{O_2}(5)=1$. Fix a rank-two space $V=\mathbb Q_5 b_1\oplus\mathbb Q_5 b_2$ with reference lattice $B=\mathbb Z_5 b_1\oplus\mathbb Z_5 b_2$, Hecke degree $r=1$, and $R=1$ pair of auxiliary places $(\mathrm{inl}\,0,\mathrm{inr}\,0)$ at group-ring level $M=2$ ($\ell^M=25$).

Suppose the untwisted projected theta generators $\theta_1,\theta_2\in V$ require the universal denominator $x=5^2=25$ to land in $B$:
$$25\,\theta_1 = 5 b_1 + 2 b_2,\qquad 25\,\theta_2 = 5 b_2,\qquad m_0 = \begin{pmatrix}5 & 0\\ 2 & 5\end{pmatrix}\in M_2(\mathbb Z_5).$$
Here $\det m_0=25\ne 0$, giving baseline valuation $v_B=v_5(\det m_0)=2$, while $\operatorname{nval}_{\mathbb Z_5}(x^2)=v_5(25^2)=4$. For $L_0=\mathbb Z_5\theta_1+\mathbb Z_5\theta_2$, Lemma 10.13n(2) gives
$$\operatorname{sIdx}_{\mathbb Z_5}(B,L_0)=\operatorname{nval}_{\mathbb Z_5}(\det m_0)-\operatorname{nval}_{\mathbb Z_5}(25^2)=2-4=-2.$$

Take commuting upper-triangular Hecke matrices on $(b_1,b_2)$:
$$t_{\mathrm{inl}}=\begin{pmatrix}2 & 1\\ 0 & 3\end{pmatrix},\quad M_{\mathrm{inl}}(Y)=I_2-t_{\mathrm{inl}}Y=\begin{pmatrix}1-2Y & -Y\\ 0 & 1-3Y\end{pmatrix},\qquad t_{\mathrm{inr}}=\begin{pmatrix}1 & 1\\ 0 & 6\end{pmatrix},\quad M_{\mathrm{inr}}(Y)=I_2-t_{\mathrm{inr}}Y=\begin{pmatrix}1-Y & -Y\\ 0 & 1-6Y\end{pmatrix}.$$
At the left place, the residual eigenvalues $\overline{2},\overline{3}\in\mathbb F_5$ avoid $\overline{1}$ (illustrating the open subgroup $H_y$ of Lemma 10.13o(1)), so $\det M_{\mathrm{inl}}(1)=(-1)(-2)=2\in\mathbb Z_5^\times$. At the right place, the residual eigenvalues are $\overline{1},\overline{6}=\overline{1}\in\mathbb F_5$, and with negative reciprocity sign (`sg = true`) the inverse exponent on $\mu_{25}$ is represented by $\varepsilon_0=25-1=24$. Peeling $J_1=\{\mathrm{inl}\,0\}$ gives $g(X_{\mathrm{inl}},X_{\mathrm{inr}})=\det M_{\mathrm{inl}}(1+X_{\mathrm{inl}})\det m_0 = 25(1-2(1+X_{\mathrm{inl}}))(1-3(1+X_{\mathrm{inl}}))$, with $g(0,0)=50$ of $5$-adic valuation $v_5(50)=2=v_B$. Setting
$$D_d(X_{\mathrm{inl}})=\det M_{\mathrm{inr}}\bigl((1+X_{\mathrm{inl}})^{24}\bigr)=\bigl(1-(1+X_{\mathrm{inl}})^{24}\bigr)\bigl(1-6(1+X_{\mathrm{inl}})^{24}\bigr)$$
and $f(X_{\mathrm{inl}},X_{\mathrm{inr}})=\det M_{\mathrm{inr}}((1+X_{\mathrm{inl}})^{24}(1+X_{\mathrm{inr}}))\det M_{\mathrm{inl}}((1+X_{\mathrm{inl}})(1+X_{\mathrm{inr}}))\cdot 25$, the difference $f-D_d g$ vanishes on every grid point $\{(\zeta-1,0):\zeta^{25}=1\}$, hence lies in $\mathfrak I_2=\langle X_{\mathrm{inr}},(1+X_{\mathrm{inl}})^{25}-1\rangle$. Modulo $5$, $\overline{D_d}(X_{\mathrm{inl}})=(1-(1+X_{\mathrm{inl}})^{24})^2 = w(X_{\mathrm{inl}})X_{\mathrm{inl}}^2$ with $\nu_0=2\le r n=2$ and $w(0)=(-\binom{24}{1})^2=576\equiv 1\not\equiv 0\pmod 5$.

Evaluate at $(X_{\mathrm{inl}},X_{\mathrm{inr}})=(\pi,0)$ in $O_2=\mathbb Z_5[\zeta_{25}]$, so $1+X_{\mathrm{inl}}=\zeta_{25}$ and $(1+X_{\mathrm{inl}})^{24}=\zeta_{25}^{-1}$:

1. $g(\pi,0)=25(1-2\zeta_{25})(1-3\zeta_{25})\equiv 50\pmod{\pi O_2}$, so $\operatorname{nval}_{O_2}(g(\pi,0))=2=v_B$.
2. In $D_d(\pi)=(1-\zeta_{25}^{-1})(1-6\zeta_{25}^{-1})$, the first factor $-\zeta_{25}^{-1}\pi$ has normalized valuation $1/20$, and the second factor $(1-\zeta_{25}^{-1})-5\zeta_{25}^{-1}$ has normalized valuation $\min(1/20,1)=1/20$ by the strict ultrametric inequality. Hence $\operatorname{nval}_{O_2}(D_d(\pi))=1/10$ and $\operatorname{nval}_{O_2}(f(\pi,0))=2+1/10=21/10$.
3. **Same-lattice cancellation.** Let $L_\chi\subset V\otimes_{\mathbb Z_5}\mathbb Q_5(\zeta_{25})$ be the specialized lattice cleared by the same scalar $x=25$ against $B_{O_2}$. Then
   $$\operatorname{sIdx}_{O_2}(B_{O_2},L_\chi)=\frac{21}{10}-\operatorname{nval}_{O_2}(25^2)=-\frac{19}{10},\qquad \operatorname{sIdx}_{O_2}(B_{O_2},L_\chi)-\operatorname{sIdx}_{\mathbb Z_5}(B,L_0)=-\frac{19}{10}-(-2)=\frac{1}{10}.$$
   The denominator contribution $4=\operatorname{nval}(25^2)$ cancels identically, so for tolerance $\varepsilon=1/5$ the inequality $\operatorname{sIdx}_{O_2}(B_{O_2},L_\chi)\le\operatorname{sIdx}_{\mathbb Z_5}(B,L_0)+\varepsilon$ holds ($-19/10\le -9/5$).
4. **Failure under switching the reference lattice.** Replace the reference lattice on the twisted side by $B''=\tfrac{1}{5}B=\mathbb Z_5(\tfrac{1}{5}b_1)\oplus\mathbb Z_5(\tfrac{1}{5}b_2)$ while keeping the untwisted baseline $\operatorname{sIdx}_{\mathbb Z_5}(B,L_0)=-2$ on $B$. Relative to the basis $(\tfrac{1}{5}b_1,\tfrac{1}{5}b_2)$ of $B''$, the exact same coordinate matrices $m_0$ and $m_Q$ clear denominators with $x''=5$ instead of $x=25$ ($5\theta_1=5(\tfrac{1}{5}b_1)+2(\tfrac{1}{5}b_2)$, $5\theta_2=5(\tfrac{1}{5}b_2)$), so $\operatorname{nval}_{O_2}((x'')^2)=2$ and
   $$\operatorname{sIdx}_{O_2}(B''_{O_2},L_\chi)=\frac{21}{10}-2=+\frac{1}{10}\not\le -2+\frac{1}{5}=-\frac{9}{5}.$$
   Leaving $\operatorname{nval}(25^2)-\operatorname{nval}(5^2)=2$ uncancelled shifts the index difference from $1/10$ to $21/10$, violating the upper bound for every $\varepsilon<21/10$. Likewise, rescaling $B$ after $(M,Q)$ is chosen destroys the uniform constant $v_B$ before `exists_level` is invoked.

##### Example 10.13m. Separated exponents, Newton-polygon ties, and failure at non-coprime powers [Expository]

Take $\ell=3$, $O=O_0=\mathbb Z_3$ ($\varpi=3$, $v_3(3)=1$), $R=1$ variable pair $(X_{\mathrm{inl}},X_{\mathrm{inr}})$, tolerance $\varepsilon=1/4$, one Selmer polynomial $F_M(X_{\mathrm{inl}},X_{\mathrm{inr}})=9+3X_{\mathrm{inl}}^3-3X_{\mathrm{inr}}$ of degree $D=3$ with bound $\mu_\star=1$ ($\mathrm{coeff}_{(3,0)}(F_M)=3$ has $v_3(3)=1\le\mu_\star$), and one lattice polynomial at level $M\ge 2$:
$$D_d(X_{\mathrm{inl}})=X_{\mathrm{inl}}^2+3X_{\mathrm{inl}}+3=\Phi_3(1+X_{\mathrm{inl}}),\quad g=3,\quad f_M(X_{\mathrm{inl}},X_{\mathrm{inr}})=3(X_{\mathrm{inl}}^2+3X_{\mathrm{inl}}+3)+9X_{\mathrm{inr}}+\bigl((1+X_{\mathrm{inl}})^{3^M}-1\bigr),$$
satisfying `OrdHyp` $(v_*,n_{\max})=(1,2)$ because $f_M-D_d g\in\mathfrak I_M$, $v_3(g(0))=1\le 1$, and $\overline{D_d}(X_{\mathrm{inl}})=X_{\mathrm{inl}}^2$ in $\mathbb F_3[X_{\mathrm{inl}}]$.

1. **Exponent collision vs. Kronecker separation.** For $e=(e_{\mathrm{inl}},e_{\mathrm{inr}})$, the univariate substitution $S_e$ sends $X_q\mapsto (1+T)^{3^{e_q}}-1$. At the insufficiently separated pair $e=(0,1)$, $(1+T)^3-1=T^3+3T^2+3T\equiv T^3\pmod 3$ makes $-3X_{\mathrm{inr}}$ collide modulo $9$ with $3X_{\mathrm{inl}}^3$:
   $$S_{(0,1)}(F_M)(T)=9+3T^3-3(T^3+3T^2+3T)=9-9T^2-9T\equiv 0\pmod 9,$$
   erasing every witness not divisible by $9$. Separating the exponents to $e=(0,2)$ ($3^{e_{\mathrm{inr}}}=9>3$) gives $S_{(0,2)}(F_M)(T)=9+3T^3-3((1+T)^9-1)$, whose $T^3$-coefficient is $3-3\binom{9}{3}=3-252=-249$ with $v_3(-249)=1\le\mu_\star$ because $3\mid\binom{9}{3}=84$. On the lattice side, at $M=4$ ($3^4=81$), prime-power binomial divisibility gives $9\mid\binom{81}{1}=81$ and $9\mid\binom{81}{2}=3240$, so the remainder $9((1+T)^9-1)+((1+T)^{81}-1)$ has all coefficients of degree $\le 2$ divisible by $9$, preserving $v_3(\mathrm{coeff}_2(S_{(0,2)}(f_4)))=v_3(3+9\binom{9}{2}+\binom{81}{2})=v_3(3567)=1\le v_*$.
2. **Newton-polygon tie at $k=1$ vs. uniform bound at $k=4$ for all coprime powers.** In $3\Phi_3(1+T)=9+9T+3T^2$, evaluating at $T=\zeta_{3^k}-1$ ($\operatorname{nval}_3(T)=1/\varphi(3^k)$) pits the constant term $9$ (valuation $2$) against $3T^2$ (valuation $1+2/\varphi(3^k)$). These two terms tie when $2=1+2/\varphi(3^k)$, i.e. $\varphi(3^k)=2$, placing $k=1$ in the bad tie set $\mathrm{BB}$. Indeed, at $k=1$ ($T=\zeta_3-1$), $\Phi_3(\zeta_3)=0$, $\zeta_3^9-1=0$, and $\zeta_3^{81}-1=0$, so $S_{(0,2)}(f_4)(\zeta_3-1)=0$ ($\operatorname{nval}_3=+\infty$). Moving to $M=4$, $k=4\notin\mathrm{BB}$ ($\varphi(81)=54$), for *every* integer $a$ with $\gcd(a,3)=1$, the power $\zeta=\zeta_{81}^a$ is a primitive $81$-st root of unity with $\operatorname{nval}_3(\zeta-1)=1/54$ and $\operatorname{nval}_3(\zeta^9-1)=1/\varphi(9)=1/6$, yielding strict unique ultrametric minima
   $$\operatorname{nval}_3\bigl(f_4(\zeta_{81}^a-1,\zeta_{81}^{9a}-1)\bigr)=1+\frac{2}{54}=\frac{28}{27}\le 1+\frac{1}{4}=\frac{5}{4},\qquad \operatorname{nval}_3\bigl(F_4(\zeta_{81}^a-1,\zeta_{81}^{9a}-1)\bigr)=1+\frac{3}{54}=\frac{19}{18}\le\frac{5}{4}$$
   across all $54$ coprime residue classes $a\bmod 81$.
3. **Failure when omitting $\gcd(a,3)=1$.** Keep the same triple $(M,k,e)=(4,4,(0,2))$ and drop coprimality:
   - At $a=9$ ($3\mid a$), $\zeta_{81}^9=\zeta_9$ has order $9$ ($\varphi(9)=6$), inflating the valuations to $\operatorname{nval}_3(f_4(\zeta_9-1,0))=4/3>5/4$ and $\operatorname{nval}_3(F_4(\zeta_9-1,0))=3/2>5/4$.
   - At $a=27$ ($3^3\mid a$), $\zeta_{81}^{27}=\zeta_3$ drops straight back into the excluded tie level $k_{\mathrm{eff}}=1\in\mathrm{BB}$: $f_4(\zeta_{81}^{27}-1,\zeta_{81}^{243}-1)=f_4(\zeta_3-1,0)=0$ has valuation $+\infty$, while $F_4(\zeta_3-1,0)=9+3(\zeta_3-1)^3$ has valuation $\min(2,1+3/2)=2>5/4$.
   - At $a=81$, $\zeta_{81}^{81}=1$ gives $f_4(0,0)=F_4(0,0)=9$ of valuation $2>5/4$.

##### Definitions [Lean, read]

Fix a nonzero-index place $i$, base DVR $O_0=$ `X.O0` with uniformizer $\varpi_0$ and residue field $k_{O_0}$, place DVR $O=$ `X.O i` with uniformizer $\varpi$ and algebraically closed residue field $k_O$, cyclotomic extensions $O_k=$ `X.Ok i k`, and prime $\ell=$ `X.l i`, a nonzero nonunit in $O_0$, $O$, and every $O_k$ (`l_ne_zero`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:267–272`). For an auxiliary batch size $R\ge 0$, write $\sigma_R=\mathrm{Fin}\,R\oplus\mathrm{Fin}\,R$ for the variable index set of $O[X]=O[X_{\mathrm{inl}(0)},\dots,X_{\mathrm{inl}(R-1)},X_{\mathrm{inr}(0)},\dots,X_{\mathrm{inr}(R-1)}]$.

1. **Toric augmentation ideal and `OrdHyp`** (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:155–169`). At level $M\ge 1$, write $\mathfrak I_M\subset O[X]$ for the ideal generated by $X_{\mathrm{inr}(r)}$ and $(1+X_{\mathrm{inl}(r)})^{\ell^M}-1$ ($r\in\mathrm{Fin}\,R$). A polynomial $f\in O[X]$ satisfies `OrdHyp` $(v,n_{\max})$ at level $M$ if there exist $g,D_d\in O[X]$ such that:
   - $f-D_d g\in\mathfrak I_M$;
   - $v_O(\mathrm{coeff}_0(g))\le v$ (in particular $g(0)\ne 0$);
   - in $k_O[X]$, there exist $w\in k_O[X]$ with $w(0)\ne 0$ and exponents $0\le\nu_r\le n_{\max}$ such that $\overline{D_d}-w\prod_{r\in\mathrm{Fin}\,R}X_{\mathrm{inl}(r)}^{\nu_r}\in\langle X_q^{\ell^M}:q\in\sigma_R\rangle$.
   For $v\le v'$, `OrdHyp` $(v,n_{\max})$ implies `OrdHyp` $(v',n_{\max})$ (`ordHyp_mono`, `:165–169`).
2. **Signed Hecke polynomial and universal coordinates** (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:14–39,80–85`). Given $A_1,\dots,A_r\in M_n(S)$ over a commutative ring $S$, set $\mathrm{polyMat}_r(A_\bullet,Y)=I_n+\sum_{m=1}^r Y^m A_m\in M_n(S[Y])$. On a fixed $O$-basis $\mathrm{bs}=(\mathrm{bs}_1,\dots,\mathrm{bs}_n)$ of $B=F.B(j,b)$ with Hecke matrices $t_{m,P}\in M_n(O)$, the signed Hecke polynomial at $P$ is
   $$M_P(Y)=\mathrm{PqF}_P(Y):=I_n+\sum_{m=1}^r (-1)^m N(P)^{m(m-1)/2}\,Y^m\,t_{m,P}\in M_n(O[Y]).$$
   For an enumeration $e:\mathrm{Fin}\,n\xrightarrow{\sim}F.S(j,b)$, scalar $x\in O\setminus\{0\}$, finite split set $Q$, level $M$, cyclotomic layer $k$, and character $\chi:\mathrm{Del}_{Q,M}\to O_k^\times$, `Coord` $(A,\mathrm{bs},e,x,Q,M,k,\chi,m)$ (`:35–39`) asserts that $m\in M_n(O_k)$ satisfies
   $$x\cdot A_{O_k}\bigl(\operatorname{specU}(\chi)(\mathrm{thU}_Q(e_a))\bigr)=\sum_{c=1}^n m_{ca}\,(1\otimes\mathrm{bs}_c)\qquad(1\le a\le n).$$
   Injectivity of $O\to O_k$ preserves linear independence of $1\otimes\mathrm{bs}$ (`linearIndependent_one_tmul`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexSpanMatrixEqValDet.lean:266–270`), making $m$ unique (`Coord.unique`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:43–48`).
3. **Univariate cyclotomic substitution and truncated congruence ideal** (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLevelOrderExponentsSmallValuationDetermina.lean:28–35,140–145`). For $e:\sigma_R\to\mathbb N$, let $S_e:O[X]\to O[T]$ be the $O$-algebra homomorphism sending $X_q\mapsto (1+T)^{\ell^{e(q)}}-1$; for any $O$-algebra $O'$ and $\zeta\in O'$, evaluating $S_e(f)$ at $T=\zeta-1$ coincides with evaluating $f$ at $X_q=\zeta^{\ell^{e(q)}}-1$ (`aeval_subst`, `:28–35`). For $c\in O$ and $W\in\mathbb N$, put $\mathrm{lowIdeal}(c,W)=\{P\in O[T]:\forall i\le W,\ c\mid\mathrm{coeff}_i(P)\}$ (`:140–145`).

##### Lemma 10.13n (toric grid vanishing and same-lattice determinant index bound) [Lean, read]

*Keep the notation above.*

1. **Grid vanishing criterion.** *Let $O\hookrightarrow O'$ be an injective homomorphism into a domain $O'$ containing a primitive $\ell^M$-th root of unity ($M\ge 1$), and let $h\in O[X]$ satisfy $h(u-1)=0$ for every unit tuple $u:\sigma_R\to (O')^\times$ with $u_q^{\ell^M}=1$ and $u_{\mathrm{inr}(r)}=1$ ($r\in\mathrm{Fin}\,R$). Then $h\in\mathfrak I_M$.*
2. **Same-lattice coordinate comparison.** *Let $O\to O'$ be an injective local homomorphism of DVRs, $\mathrm{bs}$ an $O$-basis of a lattice $B\subseteq V$, $x\in O\setminus\{0\}$, $\theta_1,\dots,\theta_n\in V$ with $x\cdot\theta_a=\sum_c (m_0)_{ca}\mathrm{bs}_c$ and $\det m_0\ne 0$, and $w_1,\dots,w_n\in T$ inside a lattice $T$ of $V_{O'}$ with $x\cdot w_a=\sum_c m_{ca}(1\otimes\mathrm{bs}_c)$ and $\det m\ne 0$. Then $\operatorname{span}_O\{\theta_a\}$ is a lattice in $V$, $\operatorname{span}_{O'}\{w_a\}$ is a lattice in $V_{O'}$,*
   $$\operatorname{sIdx}_O\bigl(B,\operatorname{span}_O\{\theta_a\}\bigr)=\operatorname{nval}_O(\det m_0)-\operatorname{nval}_O(x^n),$$
   *and every such lattice $T$ satisfies*
   $$\operatorname{sIdx}_{O'}(B_{O'},T)\le\operatorname{sIdx}_O\bigl(B,\operatorname{span}_O\{\theta_a\}\bigr)+\operatorname{nval}_{O'}(\det m)-\operatorname{nval}_O(\det m_0).$$
3. **Toric determinant peeling.** *Under `Rel` (the coordinate form of `ThURel`), let $J,J_0\subseteq\iota$ be disjoint finite sets of split pair indices, and let $u:\iota\to O_k^\times$ satisfy $u_q^{\ell^M}=1$ for all $q$ and $u_q=1$ for all $q\notin J_0$. Peeling the conjugate split pairs over $J$ multiplies the determinant on $J_0$ by the product of local Hecke determinants:*
   $$\det m_{J_0\cup J}(u)=\Bigl(\prod_{q\in J}\det M_{P'_q}(y_q)\Bigr)\det m_{J_0}(u),$$
   *where $y_q=\operatorname{sgnProd}(\mathrm{sg},u,d(P_\bullet)(\sigma_q))$. When $\iota=\sigma_R$, $J_0=\mathrm{inl}(\mathrm{Fin}\,R)$, $J=\mathrm{inr}(\mathrm{Fin}\,R)$, and $u_{\mathrm{inr}(r)}=1$ for all $r$, reciprocity (`Steps.2` and `AntiHom` with `exists_frob_of_conj`) reduces each right-hand argument to $y_{\mathrm{inr}(r)}=u_{\mathrm{inl}(r)}^{\varepsilon_r}$ with $\varepsilon_r\in\{1,\ell^M-1\}$, whose image in $k_O$ is $\pm 1\ne 0$.*

*(Lean: `mem_span_of_aeval_eq_zero`, `index_span_matrix_eq_val_det`, `sIdx_span_of_smul_eq`, `sIdx_le_of_coords`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexSpanMatrixEqValDet.lean:23–96,157–315`; `Coord.step`, `det_factor`, `exists_exponent`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:99–258`; `exists_frob_of_conj`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsPlaceOverMoveValCc.lean:164–175`.)*

*Proof.* (1) Endow $\sigma_R$ with a linear order and $O[X]$ with `MonomialOrder.degLex` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexSpanMatrixEqValDet.lean:17–20`). For $n=\ell^M\ge 1$, the generators $b_{\mathrm{inl}(r)}=(1+X_{\mathrm{inl}(r)})^n-1$ and $b_{\mathrm{inr}(r)}=X_{\mathrm{inr}(r)}$ are monic with `degLex` multidegrees $n\,e_{\mathrm{inl}(r)}$ and $1\,e_{\mathrm{inr}(r)}$ (`:33–53`). Multivariate division `MonomialOrder.div` writes $h=\sum_q g_q b_q + r_0$ with $\deg_{X_{\mathrm{inl}(r)}}(r_0)<n$ and $\deg_{X_{\mathrm{inr}(r)}}(r_0)<1$ (`:54–59`). Map $r_0$ into $O'[X]$ along $O\hookrightarrow O'$. Because $O'$ is a domain containing a primitive $n$-th root of unity $\zeta$, the shifted root set $S_{\mathrm{inl}}=\{\xi-1:\xi\in\mu_n(O')\}$ has cardinality $n$, while $S_{\mathrm{inr}}=\{0\}$ has cardinality $1$ (`:65–71`). Both $h$ and every $b_q$ vanish on $\prod_{q\in\sigma_R}S_q$, hence so does the image of $r_0$; since its degree in each variable $q$ is strictly below $|S_q|$, `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` forces the image of $r_0$ in $O'[X]$ to vanish, and injectivity of $O\hookrightarrow O'$ gives $r_0=0$, so $h\in\mathfrak I_M$ (`:63–96`).

(2) For $N=\operatorname{span}_O\{\sum_c m_{ca}\mathrm{bs}_c\}\subseteq B$, identifying $B\simeq O^n$ via `bs` identifies $B/N$ with the cokernel of $m$, whose $O$-length is $v_O(\det m)$ by `length_quotient_span_eq_addVal_det` (wrapping `LengthQuotientSpanValuation.main` [Lean], `:184–196`); dividing by $v_O(\ell)$ gives $\operatorname{sIdx}_O(B,N)=\operatorname{nval}_O(\det m)$ (`index_span_matrix_eq_val_det`, `:157–197`). Now let $L=\operatorname{span}_O\{w_a\}$ with $x\cdot w_a=\sum_c m_{ca}\mathrm{bs}_c$ and $\det m\ne 0$. Nonvanishing of $\det m$ makes $w_1,\dots,w_n$ $O$-linearly independent (`:205–218`), and Cramer's adjugate identity $(\det m)\mathrm{bs}_c=\sum_a(\operatorname{adj} m)_{ac}(x\cdot w_a)\in x L\subseteq L$ shows that every element of $V$ has a nonzero multiple in $x L$ and in $L$, establishing `IsLatIn` for both (`:222–248`). Applying `index_span_matrix_eq_val_det` to $(B,x L)$ (matrix $m$) and to $(L,x L)$ (matrix $x I_n$, determinant $x^n$) and subtracting via signed-index additivity Lemma 10.13c(1) gives $\operatorname{sIdx}_O(B,L)=\operatorname{nval}_O(\det m)-\operatorname{nval}_O(x^n)$ (`sIdx_span_of_smul_eq`, `:249–259`). In `sIdx_le_of_coords` (`:272–315`), apply this formula to $(B,\operatorname{span}_O\{\theta_a\})$ over $O$ and to $(B_{O'},\operatorname{span}_{O'}\{w_a\})$ over $O'$. Base-change invariance Lemma 10.13c(4) applied to $(B,x B)$ gives $\operatorname{nval}_{O'}(x^n)=\operatorname{sIdx}_{O'}(B_{O'},x B_{O'})=\operatorname{sIdx}_O(B,x B)=\operatorname{nval}_O(x^n)$ (`:293–313`). Subtracting cancels $\operatorname{nval}(x^n)$ across the *same* lattice $B$, and monotonicity $\operatorname{span}_{O'}\{w_a\}\subseteq T\implies\operatorname{sIdx}_{O'}(B_{O'},T)\le\operatorname{sIdx}_{O'}(B_{O'},\operatorname{span}_{O'}\{w_a\})$ (`:291–292`) completes the proof (`:314–315`).

(3) Adjoining one conjugate split pair $\{P'_q,(P'_q)^c\}$ disjoint from $Q_0$ and specializing `Rel` at a character with $u_q=1$ rewrites the specialized vector on $Q_0\cup\{P'_q,(P'_q)^c\}$ as $M_{P'_q}(y_q)$ times the $Q_0$-vector, multiplying the coordinate matrix on the left by $M_{P'_q}(y_q)$ (`Coord.step`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:99–119`). Induction on $|J|$ with `Matrix.det_mul` yields `det_factor` (`:142–208`). At a right-hand place $P(\mathrm{inr}\,r)$, `Steps.2` gives Kronecker pairing $d_{\mathrm{inl}(s)}(\sigma_0)=\delta_{rs}$ (`:218–225`), while `exists_frob_of_conj` transports Frobenius to the conjugate place $P'_q$ with inverted character values under `AntiHom` (`:228–244`). When $u_{\mathrm{inr}}\equiv 1$, only the $s=r$ factor survives in $y_{\mathrm{inr}(r)}$, giving $u_{\mathrm{inl}(r)}^1$ or $u_{\mathrm{inl}(r)}^{-1}=u_{\mathrm{inl}(r)}^{\ell^M-1}$ since $u_{\mathrm{inl}(r)}^{\ell^M}=1$ (`:245–257`). Because $\ell$ lies in $\mathfrak m_O$, its residue in $k_O$ is $0$, so $\ell^M-1$ maps to $-1\ne 0$ in $k_O$ for $M\ge 1$ (`:252–256`). $\square$

##### Lemma 10.13o (unit left Hecke determinants and residual right factorization) [Lean, read]

1. **Open Galois subgroup avoiding residual eigenvalue $1$.** *Under `AllGood`, `adm8`, and `OffRange` at a nonzero-index place $i$ with $\delta(z)^2-1\in O_0^\times$, there exists an open normal subgroup $H_y\trianglelefteq\mathrm{Gal}(\overline{E}/E)$ such that at every split place $P$ outside the finite bad locus whose Frobenius lies in $H_y$, no residual eigenvalue of the local parameter equals $1$; consequently, for any commuting family of $O$-endomorphisms on $B=\operatorname{span}_O(\mathrm{bs})$ satisfying the eigenvalue law `T3` at $P$, $\det M_P(1)\in O^\times$.*
2. **Residual power extraction on the right.** *Let $k$ be a field, $t_1,\dots,t_r\in M_n(k)$, and $e\in\mathbb N$ with $(e:k)\ne 0$. In $k[X]$, the determinant $\det(I_n+\sum_{m=1}^r ((1+X_q)^e)^m t_m)$ factors as $w\cdot X_q^\nu$ with $w(0)\ne 0$ and $\nu\le r n$. Taking $k=k_O$ and multiplying over $r\in\mathrm{Fin}\,R$ writes $\overline{D_d}=w\prod_{r\in\mathrm{Fin}\,R}X_{\mathrm{inl}(r)}^{\nu_r}$ with $w(0)\ne 0$ and $\nu_r\le r n$.*

*(Lean: `exists_subgroup_isUnit`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSubgroupIsUnit.lean:75–186`; `exists_common_eigenvector_mem`, `src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean:7–34`; `det_eq_mul_X_pow`, `isUnit_det_of_eigen`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexSpanMatrixEqValDet.lean:99–154,319–420`; `residue_prod_det`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:278–292`.)*

*Proof.* (1) For each spectral piece $s$, `adm8` (`characterTwistExists` [Lean]) supplies a continuous Galois representation $W_s$ whose residual kernel $K_s$ is open normal (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSubgroupIsUnit.lean:93–122`). Intersecting the $K_s$ with the splitting subgroup `exists_splitK` (`:37–72`) gives $H_0$, and setting $H_y=H_0\cap c_{\mathrm{conj}}^{-1}(H_0)$ preserves openness and normality (`isOpen_comap_cConj`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsPlaceOverMoveValCc.lean:176–199`; `ExistsSubgroupIsUnit.lean:123–145`). When Frobenius at $P$ lies in $H_y$, `AllGood` and $\delta(z)^2-1\in O_0^\times$ force $1-\lambda\in O^\times$ for every local parameter $\lambda$ (`:146–185`). Over the algebraically closed residue field $k_O$, every nonzero invariant subspace of $k_O^n$ contains a minimal nonzero invariant subspace, on which a commuting family acts by scalars (`exists_common_eigenvector_mem`, `src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean:7–34`). Induction on $n$ triangularizes the commuting reductions $\overline{t_{m,P}}$, expressing $\overline{\det M_P(1)}$ as the product of $1+\sum_{m=1}^r(-1)^m N(P)^{m(m-1)/2}\mu_m$ over joint residual eigenvalue tuples $\mu_\bullet$, each nonzero in $k_O$ by `T3` and the $H_y$ condition (`isUnit_det_of_eigen`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexSpanMatrixEqValDet.lean:319–420`). Nonvanishing modulo $\mathfrak m_O$ gives $\det M_P(1)\in O^\times$.

(2) Consider the univariate matrix polynomial $A(Y)=I_n+\sum_{m=1}^r Y^m t_m\in M_n(k[Y])$ (`det_eq_mul_X_pow`, `:104–112`). Its determinant $P(Y)=\det A(Y)\in k[Y]$ satisfies $P(0)=\det I_n=1\ne 0$ and $\deg P\le r n$, since every entry of $A(Y)$ has degree $\le r$ (`:113–131`). Factoring out the root multiplicity $\nu=\operatorname{rootMultiplicity}_1(P)\le\deg P\le r n$ at $Y=1$ gives $P(Y)=(Y-1)^\nu p(Y)$ with $p(1)\ne 0$ (`:132–137`). Substituting $Y=(1+X_q)^e$ and applying the geometric-sum identity $(1+X_q)^e-1=s(X_q)X_q$ with $s(X_q)=\sum_{i=0}^{e-1}(1+X_q)^i$ yields $P((1+X_q)^e)=w_q(X_q)X_q^\nu$, where $w_q(X_q)=s(X_q)^\nu p((1+X_q)^e)$ has constant term $w_q(0)=s(0)^\nu p(1)=(e:k)^\nu p(1)\ne 0$ (`:138–153`). Multiplying over $r\in\mathrm{Fin}\,R$ gives `residue_prod_det` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:278–292`). $\square$

##### Theorem 10.13p (conditional toric supply for `PropABCD`) [Lean, read]

*Assume `ThURel Y`, `HeckeLaws Y` (supplied on the main path by `heckeLaws_of_range` from `HkComm` and `OffRange`), `AllGood Y`, and `BlochKatoReduction.Gen.adm8 X Y`. Then `PropABCD Y` holds: for every nonzero-index place $i$, every family $F$ satisfying `ABHyp`, every block $y=(j,b)$ with $1\le j\le m$, and every $z$ with $\delta(z)^2-1\in O_0^\times$, there exist an open normal subgroup $H_y\trianglelefteq\mathrm{Gal}(\overline{E}/E)$, a finite set of places $A_y$, and integers $v_y,n_y\in\mathbb N$—all determined by $B=F.B(j,b)$ and $F.\mathrm{Th}$ before $(M,R,P,d,Q)$—such that for every level $M\ge 1$, batch size $R$, auxiliary place family $P$ avoiding $A_y$ with Frobenius steps in $H_y$, reciprocity datum $d$, and split set $Q$ with `IsQ P Q`, there exists $f_y\in O[X]$ satisfying `OrdHyp` $(v_y,n_y)$ at level $M$ and the index bound of Proposition 10.13j:*
$$\operatorname{sIdx}_{O_k}(B_{O_k},T_\psi)\le\operatorname{sIdx}_O(B,F.\mathrm{Th})+\operatorname{nval}_{O_k}\bigl(f_y(u-1)\bigr)-\frac{v_y}{v_O(\ell)}$$
*whenever $u_q^{\ell^M}=1$, $f_y(u-1)\ne 0$, and $T_\psi$ is any lattice of $(\operatorname{span}_K B)_{O_k}$ containing the specialized $A$-images for $\chi(x)=\prod_q u_q^{x_q}$.*
*(Lean: `GlobalTheory.TwistDet.propABCD_of_rel`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:293–466`; `heckeLaws_of_range` and main-path call, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:16–37`.)*

*Proof.* Unpack `ABHyp` at $(i,j,b)$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:297`): $B=F.B(j,b)$ is a Hecke-stable lattice, the finite set $F.S(j,b)$ of cardinality $n$ indexes linearly independent untwisted vectors $\theta_a=F.A(j,b)(Y.\mathrm{th}(e_a))$ spanning the same $K$-space as $B$, and a single exponent $c\in\mathbb N$ makes $x=\ell^c\ne 0$ clear denominators of $\mathrm{thU}_Q(e_a)$ into $F.\mathrm{Ball}(j,b)$ for every disjoint split set $Q$ (`:301–312,327–332`). Since $B$ is finitely generated torsion-free over $O$ of rank $n$, `exists_basis_fin` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexSpanMatrixEqValDet.lean:421–444`) chooses an $O$-basis $\mathrm{bs}=(\mathrm{bs}_1,\dots,\mathrm{bs}_n)$ of $B$ together with Hecke matrices $t_{m,P}\in M_n(O)$ (`AevalOneSubOne.lean:313–325`). At $Q=\varnothing$ and $M=0$, `exists_coord` yields the untwisted coordinate matrix $m_0\in M_n(O)$ satisfying $x\cdot\theta_a=\sum_c (m_0)_{ca}\mathrm{bs}_c$, with $\det m_0\ne 0$ by linear independence of $\theta_\bullet$ (`:333–351`).

Fix—before $(M,R,P,d,Q)$—the open normal subgroup $H_y$ from Lemma 10.13o(1) (`:300`), the finite excluded set $A_y=\mathrm{placesOver}(q)\cup\mathrm{placesOver}(d)\cup\bigcup_{a\in F.S(j,b)}\mathrm{lev}(a)$ (`:357–362`), the baseline valuation $v_y=v_O(\det m_0)$, and $n_y=r n$ (`:363`). Given an admissible tuple $(M,R,P,d,Q)$ (`:364`), partition $Q=Q_1\sqcup Q_2$ over $J_1=\mathrm{inl}(\mathrm{Fin}\,R)$ and $J_2=\mathrm{inr}(\mathrm{Fin}\,R)$. Applying `exists_coord` (`:59–78`, built from `exists_coords`, `IndexSpanMatrixEqValDet.lean:468–510`) to $Q$ and $Q_1$ produces polynomial matrices $m_Q,m_1\in M_n(O[X])$ whose evaluations at $u-1$ satisfy `Coord` for $Q$ and $Q_1$; set $f_y=\det m_Q$ and $g=\det m_1$ (`AevalOneSubOne.lean:366–380`). By Lemma 10.13n(3), for every $r\in\mathrm{Fin}\,R$ there is $\varepsilon_r\in\{1,\ell^M-1\}$ with $\overline{\varepsilon_r}\ne 0$ in $k_O$ such that on every unit tuple $u$ in $O_M$ (containing the primitive $\ell^M$-th root `X.zk i M`) with $u_{\mathrm{inl}(r)}^{\ell^M}=1$ and $u_{\mathrm{inr}(r)}=1$, peeling $J_2$ from $J_1\cup J_2$ gives $f_y(u-1)=D_d(u-1)g(u-1)$ for $D_d(X)=\prod_r\det M_{P'_{\mathrm{inr}(r)}}((1+X_{\mathrm{inl}(r)})^{\varepsilon_r})$ (`:381–399`). Lemma 10.13n(1) with $O'=O_M$ yields $f_y-D_d g\in\mathfrak I_M$ (`:400–405`).

Peeling $J_1$ from $\varnothing\cup J_1$ at $k=0$ and $u\equiv 1$ via Lemma 10.13n(3) gives $g(0)=(\prod_{r\in\mathrm{Fin}\,R}\det M_{P'_{\mathrm{inl}(r)}}(1))\det m_0$ (`:406–424`). Because the left Frobenius elements lie in $H_y$ and the Hecke operators commute by `HkComm`, Lemma 10.13o(1) makes every factor $\det M_{P'_{\mathrm{inl}(r)}}(1)$ a unit in $O^\times$, whence $v_O(g(0))=v_O(\det m_0)=v_y$ (`:425–443`). Lemma 10.13o(2) gives $\overline{D_d}=w\prod_r X_{\mathrm{inl}(r)}^{\nu_r}$ with $w(0)\ne 0$ and $\nu_r\le r n=n_y$ (hence congruent modulo $\langle X_q^{\ell^M}\rangle$ with zero remainder), completing `OrdHyp` $(v_y,n_y)$ (`:444–446`). Finally, whenever $f_y(u-1)=\det m_Q(u-1)\ne 0$ in $O_k$, Lemma 10.13n(2) applied to the *same* basis `bs` of $B$ across $O\hookrightarrow O_k$ yields
$$\operatorname{sIdx}_{O_k}(B_{O_k},T_\psi)\le\operatorname{sIdx}_O(B,F.\mathrm{Th})+\operatorname{nval}_{O_k}\bigl(f_y(u-1)\bigr)-\operatorname{nval}_O(\det m_0),$$
and $\operatorname{nval}_O(\det m_0)=v_O(\det m_0)/v_O(\ell)=v_y/v_O(\ell)$ (`:447–466`). $\square$

##### Lemma 10.13q (compactness limit and Kronecker-separated low-degree witnesses) [Lean, read]

*Let $O_0$ be a DVR with uniformizer $\varpi_0$ and prime $\ell\in\mathfrak m_{O_0}$, $I$ a finite index set, $D,M_0\in\mathbb N$, $\mu:I\to\mathbb N$, and $(F_{M,x})_{M\ge M_0,\,x\in I}$ a family in $O_0[X]$ ($2R$ variables) such that for every $M\ge M_0$ and $x\in I$ there is a multi-index $m$ of total degree $\le D$ with $\varpi_0^{\mu_x+1}\nmid\mathrm{coeff}_m(F_{M,x})$. Identify $\sigma_R\simeq\mathrm{Fin}(2R)$ via $\tau$. Then there exists a gap $a\in\mathbb N$ such that for every exponent tuple $e:\sigma_R\to\mathbb N$ satisfying $e(\tau(i'))+a\le e(\tau(i))$ whenever $i'<i$, there exists $W_1\in\mathbb N$ with the property that for every threshold $M_1\in\mathbb N$, some $M\ge M_1$ gives for every $x\in I$ an index $w_x\le W_1$ with $\varpi_0^{\mu_x+1}\nmid\mathrm{coeff}_{w_x}(S_e(F_{M,x}))$.*
*(Lean: `exists_limit_family_of_finite_coefficients`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLimitFamilyOfFiniteCoefficients.lean:7–26`; `exists_exponent_strictly_least_weight`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsExponentStrictlyLeastWeight.lean:9–48`; `not_dvd_coeff_aeval_oneAddX_pow_sub_one`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotDvdCoeffAevalOneAddXPowSubOne.lean:38–94`; `exists_low_coeff_of_limit`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLevelOrderExponentsSmallValuationDetermina.lean:43–139`.)*

*Proof.* Set $K=\max_{x\in I}\mu_x$. Record for each $M$ the binary divisibility table $\mathbf 1[\varpi_0^r\mid\mathrm{coeff}_m(F_{M,x})]$ in the product space $\{0,1\}^{I\times(\sigma_R\to_0\mathbb N)\times\mathrm{Fin}(K+2)}$, which is compact by Tychonoff's theorem (`exists_clusterPt_of_compactSpace`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLimitFamilyOfFiniteCoefficients.lean:7–26`). Choosing a cluster point $G$ along `Filter.atTop` yields the finite-window stabilization property (`hG`, `ExistsLevelOrderExponentsSmallValuationDetermina.lean:55–68`): for every degree cutoff $N\in\mathbb N$ and every $M_1\in\mathbb N$, there exists $M\ge M_1$ such that $\varpi_0^r\mid\mathrm{coeff}_m(F_{M,x})\iff G(x,m,r)$ simultaneously for all $x\in I$, all $\deg m\le N$, and all $r\le K+1$.

Instantiate `hG` once at $(N,M_1)=(D,M_0)$: the hypothesis on $(F_{M,x})$ shows that for each $x\in I$ there exists $m$ with $\neg G(x,m,\mu_x+1)$ (`:69–73`). Let $\nu_x=\operatorname{Nat.find}\{j:\exists m,\ \neg G(x,m,j+1)\}\le\mu_x$ be the minimum non-divisibility level in $G$, and apply `exists_least_weight_exponent` (`ExistsExponentStrictlyLeastWeight.lean:9–48`) to pick the reverse-lexicographically minimal multi-index $m_0(x)$ satisfying $\neg G(x,m_0(x),\nu_x+1)$ (`:74–92`). Because $I$ and $\sigma_R$ are finite, $B=\max_{x\in I,q\in\sigma_R}m_0(x)_q$ is finite; set $a=2RB$ (`:93–95`).

Now let $e:\sigma_R\to\mathbb N$ satisfy $e(\tau(i'))+a\le e(\tau(i))$ for $i'<i$. Since $2RB<\ell^{2RB}$, the weights $c_q=\ell^{e(q)}$ satisfy the super-increasing inequality $\sum_{i'<i}m_0(x)_{\tau(i')}c_{\tau(i')}<c_{\tau(i)}$ (`:101–121`), so $m_0(x)$ achieves the *strictly smallest* weighted degree $w_x=\sum_q m_0(x)_q\ell^{e(q)}$ among all $m$ with $\neg G(x,m,\nu_x+1)$ (`:76–78`). Put $W_1=\max_{x\in I}w_x$ (`:96–97`). Given any $M_1$, invoke `hG` at $(N,M_1)=(W_1,M_1)$ to obtain $M\ge M_1$ agreeing with $G$ on *all* multi-indices of total degree $\le W_1$ (`:99`). Any monomial $X^m$ contributing to $\mathrm{coeff}_{\le W_1}(S_e(F_{M,x}))$ satisfies $\deg m\le\sum_q m_q\ell^{e(q)}\le W_1$ (`degree_le_weight`, `:23–27,126–138`), so at this $M$: (i) every $m$ with $\deg m\le W_1$ satisfies $\varpi_0^{\nu_x}\mid\mathrm{coeff}_m(F_{M,x})$; (ii) $\varpi_0^{\nu_x+1}\nmid\mathrm{coeff}_{m_0(x)}(F_{M,x})$; and (iii) every $m\ne m_0(x)$ of weighted degree $\le w_x$ satisfies $\varpi_0^{\nu_x+1}\mid\mathrm{coeff}_m(F_{M,x})$. Under $X_q\mapsto (1+T)^{\ell^{e(q)}}-1=T^{\ell^{e(q)}}+\sum_{j=1}^{\ell^{e(q)}-1}\binom{\ell^{e(q)}}{j}T^j$, every lower binomial coefficient is divisible by $\ell\in\varpi_0 O_0$, so multiplying by $\mathrm{coeff}_m(F_{M,x})\in\varpi_0^{\nu_x}O_0$ sends every non-leading cross-term into $\varpi_0^{\nu_x+1}O_0$. Only the leading term of $m_0(x)$ survives modulo $\varpi_0^{\nu_x+1}$ at degree $w_x$, yielding $\varpi_0^{\nu_x+1}\nmid\mathrm{coeff}_{w_x}(S_e(F_{M,x}))$ and hence $\varpi_0^{\mu_x+1}\nmid\mathrm{coeff}_{w_x}(S_e(F_{M,x}))$ (`not_dvd_coeff_aeval_oneAddX_pow_sub_one`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotDvdCoeffAevalOneAddXPowSubOne.lean:38–94`; `ExistsLevelOrderExponentsSmallValuationDetermina.lean:124–139`). $\square$

##### Lemma 10.13r (truncated toric congruence division and finite Newton-polygon tie exclusion) [Lean, read]

1. **Low-degree witness for `OrdHyp` polynomials.** *Let $O$ be a DVR with uniformizer $\varpi$ and prime $\ell\in\mathfrak m_O$, $J$ a finite set, $v:J\to\mathbb N$ with $V=\max_{y\in J}v_y$, and $s\in\mathbb N$. Put $m_0=R n_{\max}\ell^s$, $W_2=(V+1)m_0$, and $E=V+1+W_2$. If $e:\sigma_R\to\mathbb N$ satisfies $e(\mathrm{inl}\,r)\le s$ and $e(\mathrm{inr}\,r)\ge E$ for all $r\in\mathrm{Fin}\,R$, then for every $M\ge E$ and every $f_{M,y}\in O[X]$ satisfying `OrdHyp` $(v_y,n_{\max})$ at level $M$, there exists $w_y\le W_2$ such that $\varpi^{v_y+1}\nmid\mathrm{coeff}_{w_y}(S_e(f_{M,y}))$.*
2. **Primitive root valuation and finite tie set.** *Let $(h_y)_{y\in J}$ be a finite family in $O[T]$ such that for each $y\in J$ there is $w_y\le W$ with $\varpi^{v_y+1}\nmid\mathrm{coeff}_{w_y}(h_y)$. Put $N=\sum_{y\in J}(W+v_y)$ (independent of the polynomials $h_y$). Then there exists a finite tie set $\mathrm{BB}\subset\mathbb N$ of cardinality $|\mathrm{BB}|\le N$ such that for every $k\ge 1$ with $k\notin\mathrm{BB}$, every local injective DVR extension $O\hookrightarrow O'$, every primitive $\ell^k$-th root of unity $\zeta\in O'$, and every $y\in J$, one has $h_y(\zeta-1)\ne 0$ and*
   $$\operatorname{nval}_{O'}\bigl(h_y(\zeta-1)\bigr)\le\frac{v_y}{v_O(\ell)}+\frac{W}{\varphi(\ell^k)}.$$

*(Lean: `pow_sub_dvd_choose_prime_pow_of_lt`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubDvdChoosePrimePowOfLt.lean:6–35`; `coeff_aeval_one_add_X_pow_sub_one_ne_zero`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffAevalOneAddXPowSubOneNeZero.lean:23–55`; `exists_low_coeff_not_dvd_of_congr_mul`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLowCoeffNotDvdOfCongrMul.lean:12–66`; `exists_low_coeff_of_factor`, `exists_levels`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLevelOrderExponentsSmallValuationDetermina.lean:184–277`; `nval_primitiveRoot_prime_pow_sub_one`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedValuationPrimitiveRootPrimePowSubOne.lean:23–52`; `nval_algebraMap_eq`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedValuationAlgebraMapEq.lean:41–49`; `card_double_min`, `value_at_root_sub_one`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationPolynomialAtRootOfUnitySubOne.lean:10–82,138–193`.)*

*Proof.* (1) For $a>c\ge 0$ and $1\le i<\ell^{c+1}$, writing $i=\ell^u q$ with $\ell\nmid q$ and $u\le c$ in $i\binom{\ell^a}{i}=\ell^a\binom{\ell^a-1}{i-1}$ yields $\ell^{a-c}\mid\binom{\ell^a}{i}$ (`pow_sub_dvd_choose_prime_pow_of_lt`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubDvdChoosePrimePowOfLt.lean:6–35`). Since $W_2<\ell^{W_2}$ and both $M$ and $e(\mathrm{inr}\,r)$ are $\ge E=(V+1)+W_2$, every generator $X_{\mathrm{inr}(r)}$ and $(1+X_{\mathrm{inl}(r)})^{\ell^M}-1$ of $\mathfrak I_M$ maps under $S_e$ into $\mathrm{lowIdeal}(\ell^{V+1},W_2)\subseteq\mathrm{lowIdeal}(\varpi^{V+1},W_2)$ (`pow_sub_one_mem_lowIdeal`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLevelOrderExponentsSmallValuationDetermina.lean:146–165`), whence $S_e(f_{M,y}-D_d g)\in\mathrm{lowIdeal}(\varpi^{v_y+1},W_2)$ (`:210–222`). Modulo $\mathfrak m_O$, $(1+T)^{\ell^{e(q)}}-1=T^{\ell^{e(q)}}$ in $k_O[T]$, while $X_q^{\ell^M}\mapsto T^{\ell^{e(q)+M}}$ vanishes in degrees $\le W_2<\ell^M$, so $\overline{S_e(D_d)}(T)$ has lowest nonzero term $w(0)T^{\nu_{\mathrm{tot}}}$ at degree $\nu_{\mathrm{tot}}=\sum_r\nu_r\ell^{e(\mathrm{inl}\,r)}\le R n_{\max}\ell^s=m_0$ (`coeff_aeval_one_add_X_pow_sub_one_ne_zero`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffAevalOneAddXPowSubOneNeZero.lean:23–55`). Meanwhile $\mathrm{coeff}_0(S_e(g))=g(0)$ is not divisible by $\varpi^{v_y+1}$ (`coeff_zero_subst`, `:166–173`). If $\varpi^{v_y+1}$ divided $\mathrm{coeff}_j(S_e(f_{M,y}))$ for all $j\le (v_y+1)m_0\le W_2$, it would divide $\mathrm{coeff}_j(S_e(D_d)S_e(g))$ in that range; double induction on $v_y$ and degree (`exists_low_coeff_not_dvd_of_congr_mul`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLowCoeffNotDvdOfCongrMul.lean:12–66`) cancels the unit $w(0)$ modulo $\varpi$ to deduce $\varpi\mid\mathrm{coeff}_j(S_e(g))$ for $j\le v_y m_0$ and divides out $\varpi$ repeatedly until contradicting $\varpi^{v_y+1}\nmid g(0)$ (`ExistsLevelOrderExponentsSmallValuationDetermina.lean:223–248`).

(2) In any DVR $O'$ with a primitive $\ell^k$-th root $\zeta$ ($k\ge 1$), all $\varphi(\ell^k)$ differences $\zeta^a-1$ ($\gcd(a,\ell)=1$) are $O'$-associates of $\zeta-1$, and their product is $\pm\Phi_{\ell^k}(1)=\pm\ell$, giving $\operatorname{nval}_{O'}(\zeta-1)=1/\varphi(\ell^k)$ (`nval_primitiveRoot_prime_pow_sub_one`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedValuationPrimitiveRootPrimePowSubOne.lean:23–52`), while $\operatorname{nval}_{O'}(c)=\operatorname{nval}_O(c)=v_O(c)/v_O(\ell)$ for $c\in O\setminus\{0\}$ (`nval_algebraMap_eq`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedValuationAlgebraMapEq.lean:41–49`).

Fix $h=h_y$ with witness $w=w_y\le W$ and $a_w=v_O(\mathrm{coeff}_w(h))\le v_y$. Put $\mathcal A=\operatorname{supp}(h)$, $a_i=v_O(\mathrm{coeff}_i(h))\in\mathbb N$, and $q(k)=v_O(\ell)/\varphi(\ell^k)$, which is strictly positive and strictly decreasing for $k\ge 1$ (`ValuationPolynomialAtRootOfUnitySubOne.lean:140–154`). Write $M_k(i)$ when $i\in\mathcal A$ minimizes $a_m+m q(k)$ on $\mathcal A$, and let $\mathrm{BB}_y=\{k\ge 1:\exists I_k<J_k,\ M_k(I_k)\wedge M_k(J_k)\}$ (`:16–24`). Two monotonicity facts govern minimizers (`:26–47`):
- (`hA'`) if $M_k(i)$ and $m\in\mathcal A$ satisfies $m<i$, then $a_i+i q(k)\le a_m+m q(k)$ and $m q(k)<i q(k)$ imply $a_i<a_m$;
- (`hB`) if $1\le k<k'$ (so $q(k')-q(k)<0$), $M_k(m)$, and $M_{k'}(m')$, adding $a_m+m q(k)\le a_{m'}+m' q(k)$ and $a_{m'}+m' q(k')\le a_m+m q(k')$ gives $(m-m')(q(k)-q(k'))\le 0$, whence $m\le m'$.

Define $\varphi:\mathrm{BB}_y\to\mathbb N$ by $\varphi(k)=I_k$ if $I_k<w$, and $\varphi(k)=w+a_{J_k}$ if $I_k\ge w$ (`:48`). When $I_k\ge w$, we have $w<J_k$, so (`hA'`) gives $a_{J_k}<a_w$ and $\varphi(\mathrm{BB}_y)\subseteq\{0,\dots,w+a_w-1\}$ (`:49–56`). For $k<k'$ in $\mathrm{BB}_y$, (`hB`) applied to $J_k$ and $I_{k'}$ gives $I_k<J_k\le I_{k'}<J_{k'}$, and (`hA'`) at $k'$ gives $a_{J_{k'}}<a_{J_k}$; thus $\varphi(k)\ne\varphi(k')$ in all four branch pairs, proving $|\mathrm{BB}_y|\le w+a_w\le W+v_y$ (`card_double_min`, `:57–82`). For $k\notin\mathrm{BB}_y$, $a_m+m q(k)$ has a *strict* unique minimum $i_0$ on $\mathcal A$, so the strict ultrametric triangle inequality (`sum_unique_min`, `:119–135`) gives $h_y(\zeta-1)\ne 0$ and
$$\operatorname{nval}_{O'}\bigl(h_y(\zeta-1)\bigr)=\frac{a_{i_0}+i_0 q(k)}{v_O(\ell)}\le\frac{a_w}{v_O(\ell)}+\frac{w}{\varphi(\ell^k)}\le\frac{v_y}{v_O(\ell)}+\frac{W}{\varphi(\ell^k)}$$
(`value_at_root_sub_one`, `:138–193`). Taking $\mathrm{BB}=\bigcup_{y\in J}\mathrm{BB}_y$ gives $|\mathrm{BB}|\le\sum_{y\in J}(W+v_y)=N$ (`exists_levels`, `ExistsLevelOrderExponentsSmallValuationDetermina.lean:249–277`). $\square$

##### Theorem 10.13s (simultaneous level, order, and exponent selection) [Lean, read]

*Let $O_0\to O$ be a local injective homomorphism of DVRs (with $[Finite\ k_{O_0}]$ in the formal signature), $\ell$ a prime that is a nonzero nonunit in $O_0$, $R,D,n_{\max},M_0\in\mathbb N$, $I,J$ finite index sets, $\mu:I\to\mathbb N$, $v:J\to\mathbb N$, and $\varepsilon>0$. Suppose that for every $M\ge M_0$:*

- *for every $x\in I$, $F_{M,x}\in O_0[X]$ has some multi-index $m$ of total degree $\le D$ with $v_{O_0}(\mathrm{coeff}_m(F_{M,x}))\le\mu_x$;*
- *for every $y\in J$, $f_{M,y}\in O[X]$ satisfies `OrdHyp` $(v_y,n_{\max})$ at level $M$.*

*Then there exist $M\ge M_0$, $1\le k\le M$, and $e:\sigma_R\to\mathbb N$ such that $e(q)<k$ and $\ell^{e(q)}/\varphi(\ell^k)\le\varepsilon$ for all $q\in\sigma_R$, and for every local injective DVR extension $O\hookrightarrow O'$ and every primitive $\ell^k$-th root of unity $\zeta\in O'$:*

1. *for every $x\in I$, $F_{M,x}(\zeta^{\ell^{e(\cdot)}}-1)\ne 0$ and $\operatorname{nval}_{O'}(F_{M,x}(\zeta^{\ell^{e(\cdot)}}-1))\le\mu_x/v_{O_0}(\ell)+\varepsilon$;*
2. *for every $y\in J$, $f_{M,y}(\zeta^{\ell^{e(\cdot)}}-1)\ne 0$ and $\operatorname{nval}_{O'}(f_{M,y}(\zeta^{\ell^{e(\cdot)}}-1))\le v_y/v_O(\ell)+\varepsilon$.*

*(Lean: `GlobalTheory.T.exists_level_order_exponents_small_valuation_determinants`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLevelOrderExponentsSmallValuationDeterminaStatement.lean:5–6`; `GlobalTheory.OrderEval.order_eval`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLevelOrderExponentsSmallValuationDetermina.lean:278–377`; main-path wrapper `exists_level`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:321–353`.)*

*Proof.* Apply Lemma 10.13q to $(F_{M,x})$ to obtain the separation gap $a=2RB$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLevelOrderExponentsSmallValuationDetermina.lean:294–297`). Put $V=\max_{y\in J}v_y$ (`:298`) and let $(E,W_2)$ be the cutoff pair from Lemma 10.13r(1) for $s=aR$ (`:299`). Fix the exponent tuple $e:\sigma_R\to\mathbb N$ *first* by
$$e(\mathrm{inl}\,r)=a\,r,\qquad e(\mathrm{inr}\,r)=a(r+R)+E\qquad(r\in\mathrm{Fin}\,R),$$
which satisfies adjacent separation $\ge a$ across $\mathrm{Fin}(2R)\simeq\sigma_R$, $e(\mathrm{inl}\,r)\le aR$, and $e(\mathrm{inr}\,r)\ge E$ (`:300–323`).

With $e$ fixed, Lemma 10.13q produces $W_1\in\mathbb N$ and arbitrarily large witnessing levels $M$ (`:324`). Let $N_1=\sum_{x\in I}(W_1+\mu_x)$ and $N_2=\sum_{y\in J}(W_2+v_y)$ be the uniform tie-set cardinal bounds from Lemma 10.13r(2) (`:325–326`), set $C=\max_q\ell^{e(q)}$, and pick $k_1\in\mathbb N$ with $k_1\ge (C+W_1+W_2)/\varepsilon$ (`:327–329`). Use Lemma 10.13q to choose a single level
$$M\ge M_0 + E + k_1 + C + 1 + N_1 + N_2$$
at which every $S_e(F_{M,x})$ has a witness $w_x\le W_1$ with $\varpi_0^{\mu_x+1}\nmid\mathrm{coeff}_{w_x}(S_e(F_{M,x}))$ (`:330`). Because $M\ge E$, Lemma 10.13r(1) simultaneously supplies $w_y\le W_2$ with $\varpi^{v_y+1}\nmid\mathrm{coeff}_{w_y}(S_e(f_{M,y}))$ for every $y\in J$ (`:332–336`). Lemma 10.13r(2) at this $M$ yields finite bad sets $B_1,B_2\subset\mathbb N$ with $|B_1\cup B_2|\le N_1+N_2$ (`:331–336`). By Pigeonhole (`Finset.exists_mem_notMem_of_card_lt_card`), the interval $[k_1+C+1,\ k_1+C+1+N_1+N_2]$ of $N_1+N_2+1$ integers contains some $k\notin B_1\cup B_2$ (`:337–343`). Since $k\le\varphi(\ell^k)$ for $k\ge 1$ (`le_totient_pow`, `:36–42`), any $c\le C+W_1+W_2$ satisfies $c/\varphi(\ell^k)\le c/k_1\le\varepsilon$ (`:344–355`); in particular $e(q)<\ell^{e(q)}\le C<k\le M$ and $\ell^{e(q)}/\varphi(\ell^k)\le\varepsilon$ (`:356–361`). For any local injective extension $O\hookrightarrow O'$ (which composes with $O_0\hookrightarrow O$ to a local injective extension $O_0\hookrightarrow O'$, `:365–369`) and any primitive $\ell^k$-th root $\zeta\in O'$, rewriting via `aeval_subst` and applying Lemma 10.13r(2) gives (1) and (2) (`:362–377`). In `exists_level` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:321–353`), `isLocalHom_O` (`:109–126`) and `isLocalHom_Ok` (`:95–99`) supply the local maps $O_0\to O\to O_k$. $\square$

##### Corollary 10.13t (closing the two inputs of Proposition 10.13j across all coprime powers) [Lean, read]

*In `twist_theorem_all_powers_of_selmer_sup_lattice` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:24–38`) and `admissibleIndexBoundAllPowers_of_conditions` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:92–222`), Theorems 10.13p and 10.13s supply `PropABCD` and `exists_level` with exact quantifier and coprime-power compatibility:*

1. *Fix $(i,\varepsilon',F,A_{\mathrm{excl}})$ with $F$ satisfying `ABHyp` (Proposition 10.13h). Theorem 10.13p extracts $(H_y,A_y,v_y,n_y)$ from the single reference lattice $B=F.B(j,b)$ before $(M,R,P,d,Q)$. Setting $n_{\max}=2+\sum_y n_y$, $v=\mathrm{Sum.elim}\,v_E\,v_y$, $\mu_x=\nu(X,i)v_{O_0}(\ell)$, and $\varepsilon=\varepsilon'/C$, Theorem 10.13s selects $(M,k,e)$ before any character power $a$ is introduced (`AdmissibleIndexBoundAllPowersOfConditions.lean:104–144`).*
2. *Form $\chi_0(x)=\prod_q(\zeta_k^{\ell^{e(q)}})^{x_q}$ and $\psi_0=\chi_0\circ\phi$ at the fixed primitive root $\zeta_k=$ `X.zk i k` $\in O_k$ (`:153–161`). For every $a\in\mathbb Z$ with $\gcd(a,\ell)=1$ and either sign branch $b\in\{\mathrm{true},\mathrm{false}\}$, the root $\zeta=(\zeta_k^a)^{\pm 1}$ remains a primitive $\ell^k$-th root of unity in $O_k$ (`zpow_prim`, `side_root`, `:24–36`), so Theorem 10.13s(2) gives $\operatorname{nval}_{O_k}(f_y(u-1))-v_y/v_O(\ell)\le\varepsilon$ and Theorem 10.13p delivers `partAB` on the fixed lattice $B$, whence Theorems 10.13g and 10.13i yield `GoodTw` for $\psi_0^a$ (`:164–222`).*

##### Remarks, source map, and reading boundary

*Remark 1 (classical precedents and an unused finiteness hypothesis) [Expository].* Three classical results underlie the local algebra read above:
- Lemma 10.13n(1) (`mem_span_of_aeval_eq_zero`) is the toric specialization of Noga Alon's Combinatorial Nullstellensatz ([Alon1999](../sources/SOURCES.md#6-literature), Theorem 1.1 and Lemma 2.1, pp. 7–9): dividing $h\in O[X]$ by the monic family $b_q(X_q)\in\{(1+X_{\mathrm{inl}(r)})^{\ell^M}-1,\,X_{\mathrm{inr}(r)}\}$ under `degLex` leaves a remainder of coordinate degree $<\deg b_q$, which vanishes identically once $h$ vanishes on the Cartesian root grid (`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`).
- Lemma 10.13n(2) (`sIdx_span_of_smul_eq`, `sIdx_le_of_coords`) expresses Serre's determinant formula $\chi(X,uX)=(\det u)$ ([SerreLocalFields](../sources/SOURCES.md#6-literature), Ch. III, §1, Proposition 2, p. 48) after clearing denominators by $x=\ell^c$ on one fixed basis so that $\operatorname{nval}(x^n)$ cancels between $O$ and $O'$.
- Lemma 10.13r(2) (`nval_primitiveRoot_prime_pow_sub_one`) is the cyclotomic ramification formula $(p)=(1-\zeta_{p^k})^{\varphi(p^k)}$ from $\Phi_{p^k}(1)=p$ ([Washington1997](../sources/SOURCES.md#6-literature), Lemma 1.4 and Proposition 2.1, pp. 3, 9–10), paired with the discrete Newton-polygon tie bound `card_double_min`. Notice a minor signature curiosity at `IsAuxiliaryPlaceFamilyAtLevelMono.lean:340` and `ExistsLevelOrderExponentsSmallValuationDetermina.lean:278–279`: `exists_level` supplies `twistBaseCoefficientRing_residueField_finite` (`[Finite (ResidueField O₀)]`) to `order_eval`, which binds that instance to `_` and never uses finiteness of $k_{O_0}$, because Tychonoff compactness is applied to the binary divisibility space $\{0,1\}^{I\times(\sigma_R\to_0\mathbb N)\times\mathrm{Fin}(K+2)}$ rather than to $O_0$-coefficients directly.

*Remark 2 (scope of verification).* Reading these Lean declarations line by line and running `mdbook build` checks mathematical and source-level fidelity against the pinned archive `lean.tar.gz` (SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`); neither source inspection nor book compilation is a Lean kernel verification. Only the two direct supply chains read in this subsection are marked `[Lean, read]` (`R3`); all deeper twisting, reciprocity, cohomology, and Smith-normal-form inputs remain at their `[Lean]` boundaries.

| Item | Pinned archive source | Level here |
|---|---|---|
| `propABCD_of_rel`, `polyMat`, `Coord`, `exists_coord`, `Coord.step`, `det_factor`, `exists_exponent`, `residue_prod_det`; `heckeLaws_of_range` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:14–466`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:16–37` | [Lean, read] |
| `mem_span_of_aeval_eq_zero`, `det_eq_mul_X_pow`, `index_span_matrix_eq_val_det`, `sIdx_span_of_smul_eq`, `sIdx_le_of_coords`, `isUnit_det_of_eigen`, `exists_basis_fin`, `exists_coords` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexSpanMatrixEqValDet.lean:17–510` | [Lean, read] |
| `exists_subgroup_isUnit`, `exists_splitK`, `IsSub.*`; `exists_frob_of_conj`, `isOpen_comap_cConj`; `exists_common_eigenvector_mem` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSubgroupIsUnit.lean:37–267`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsPlaceOverMoveValCc.lean:16–199`; `src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean:7–34` | [Lean, read] |
| `exists_level_order_exponents_small_valuation_determinants`, `order_eval`, `exists_low_coeff_of_limit`, `pow_sub_one_mem_lowIdeal`, `exists_low_coeff_of_factor`, `exists_levels`; `exists_level`, `ordHyp_mono`, `isLocalHom_O`, `isLocalHom_Ok` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLevelOrderExponentsSmallValuationDeterminaStatement.lean:5–6`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLevelOrderExponentsSmallValuationDetermina.lean:15–377`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:95–169,321–353` | [Lean, read] |
| Tychonoff limit, Kronecker weight separation, binomial congruence, Weierstrass cancellation, root-of-unity valuation, and Newton-polygon tie bound (`card_double_min`, `value_at_root_sub_one`) | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLimitFamilyOfFiniteCoefficients.lean:7–26`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsExponentStrictlyLeastWeight.lean:9–48`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotDvdCoeffAevalOneAddXPowSubOne.lean:38–94`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowSubDvdChoosePrimePowOfLt.lean:6–35`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffAevalOneAddXPowSubOneNeZero.lean:23–55`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLowCoeffNotDvdOfCongrMul.lean:12–66`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedValuationPrimitiveRootPrimePowSubOne.lean:23–52`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalizedValuationAlgebraMapEq.lean:41–49`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationPolynomialAtRootOfUnitySubOne.lean:10–193` | [Lean, read] |
| Inherited lattice transport (`export_at`, `abHyp_fam`, all-coprime-powers assembly, Proposition 10.13j body) | §§10.4.7–10.4.7.1 (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:17–496`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:17–64`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:92–222`) | [Lean, read] (inherited) |
| Deep twisting, Hecke, SNF, and Selmer inputs (`ThURel`, `AllGood`, `HkComm`, `OffRange`, `adm8`/`characterTwistExists`, `LengthQuotientSpanValuation.main`, `twistBaseCoefficientRing_residueField_finite`, `DelUTie`, `AdmACD`, `GaloisSideTwistedSelmerAuxiliaryPrimes`, `admALG_of_commG_var`, `admT3_of_hecke_semisimple`); `propE` and `admInt_of_sup_laws` are read in §10.4.7.3 | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:12–139`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OffRange.lean:1`; `src/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthCommensurableSpanSpanOfDetNeZero.lean:1`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:39–40` | [Lean] (retained boundary) |

#### 10.4.7.3 Theta Euler factors and the isotypic lattice: where non-divisibility comes from

##### Motivation [Expository]

Corollary 10.13t closed the lattice clause `partAB` of Proposition 10.13j. Two inputs of the same main-path proof were left at `[Lean]` in the table above.

1. `GlobalTheory.ToricFactor.propE` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PropEOfAdmissible.lean:420–561`) is called once for every $\lambda\in$ `abelian₂ i` at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:103`. Its polynomials $f_E(\lambda)$ enter the same call of `exists_level` as the lattice polynomials $f_y$ of Theorem 10.13p (`:133–144`). There the index set is $J=$ `abelian₂ i` $\sqcup\{\text{blocks}\}$, the baselines are $v=\mathrm{Sum.elim}\,v_E\,v_B$ and the residual exponent bound is $n_{\max}=2+\sum_y n_y$. The polynomials $f_E$ produce the theta clause `partC` of `GoodTw` (`:198–208`).
2. `GlobalTheory.IntSup.admInt_of_sup` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmIntOfSupLaws.lean:31–51`) is called through the wrapper `admInt_of_sup_laws` at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:38`. It produces `IsotypicPartsInternalDirectSum`, the integrality hypothesis of Theorem 10.13g, Proposition 10.13h and Theorem 10.13i.

Both proofs are short. They are easiest to follow if three statements about a $G$-module are kept apart.

- **(R) Rational isotypic decomposition.** Over $K=\operatorname{Frac}O$ the space $\mathrm{Fm}$ carries an action of a group containing $U$, and $W_0=$ `Fm0` is the $\psi_U$-eigenspace $\bigcap_{u\in U}\ker(\mathrm{actG}(u)-\psi_U(u))$. When $U$ is finite this is one summand of the canonical decomposition, and the projection onto it has denominator $\lvert U\rvert$. Nothing integral is involved.
- **(I) Integral lattice decomposition.** Over $O$ one may ask whether a lattice $B$ splits as $\bigoplus_\chi(B\cap\mathrm{Fm}_\chi)$. This holds when the projections preserve $B$, for instance when $B$ is $U$-stable and $\lvert U\rvert\in O^\times$, and fails in general (Example 10.13v). The archive never uses it. It works with the single isotypic lattice `Mall` $=B\cap W_0$, and it records denominators as exponents of $\ell$: $c$ in `UnivSup`, $N_0$ in `adm9`, $c_G$ in `GroupAlgebraIntegrality`.
- **(N) Nonzero after reduction.** An element $a\in O$ is a unit if and only if its residue $\bar a\in k_O$ is nonzero. On the theta side this is the only source of an exact valuation, that is, of a non-divisibility $\varpi^{v+1}\nmid g(0)$. It is applied to the Euler factors at the left auxiliary places. Their residues are $(1-\bar x)(1-\bar x^{-1})$ with $\bar x=\bar\lambda(\mathrm{Frob})$, and $\bar x\ne1$ is exactly the inertia-eigenvalue condition: `Steps` puts the left Frobenius elements into a conjugate of $zH$ with $H=\ker\bar\lambda$, and a tame inertia element $z$ at a twist prime has $\bar\lambda(z)\ne1$.

Two uniformities make (N) usable. The first is one coefficient ring: the polynomials $f$, $g$ and $D_d$ of Theorem 10.13y all lie in $O[X]$ for the same $O=$ `X.O i`, residues are taken in the same $k_O$, and evaluations go through the fixed injection $O\to O_k$. The second is one normalization: $f$ and $g$ are lifts with the same exponent $N_0(i)$, because `adm9` holds with one $N_0(i)$ for every admissible $Q$. The congruence $f\equiv D_dg$ modulo $\mathfrak I_M$ therefore needs no correcting power of $\ell$. On the lattice side the same $B=$ `Bsup` serves every $(Q,M)$, and one exponent $c$ serves each datum $a$.

##### Example 10.13u. A split rank-two example over $\mathbb Z_3$, and the left-Frobenius condition [Expository]

This example models the algebra of Theorems 10.13y and 10.13z; it is not an instance of the archive's data `NTw`. Every number below was recomputed in exact rational arithmetic by the run's script `check_examples.py` (198 checks, 0 failures; norms from $\mathbb Q(\zeta_{3^k})$ to $\mathbb Q$ are determinants of multiplication matrices).

**(a) Lattice side.** Let $\ell=3$, $O=\mathbb Z_3$, $K=\mathbb Q_3$, $\mathrm{Fm}=K^2$, $U=\{1,\sigma\}$ with $\sigma(x,y)=(y,x)$, $\psi_U(\sigma)=-1$, and $B=\mathbb Z_3^2$.

1. *(R).* The projections are $e_\pm=(1\pm\sigma)/2$, so $K^2=K(1,1)\oplus K(1,-1)$ and $W_0=K(1,-1)$.
2. *`Mall`.* A vector $(t,-t)$ lies in $\mathbb Z_3^2$ if and only if $t\in\mathbb Z_3$. Hence $\mathrm{Mall}=\mathbb Z_3(1,-1)$, which is finitely generated and spans $W_0$.
3. *(I).* The lattice $\mathbb Z_3(1,1)\oplus\mathbb Z_3(1,-1)$ has index $v_3(\det\begin{pmatrix}1&1\\1&-1\end{pmatrix})=v_3(-2)=0$ in $B$, so it equals $B$. Equivalently, $e_-(1,0)=(1/2,-1/2)\in\mathbb Z_3^2$, and the reductions $(1,1)$, $(1,2)$ are independent in $\mathbb F_3^2$.
4. *Group stability.* $\sigma(B)=B$.
5. *Hecke stability.* An operator $T=\begin{pmatrix}a&b\\b&a\end{pmatrix}$ commutes with $\sigma$, and $T(1,-1)=(a-b)(1,-1)\in\mathrm{Mall}$; for $(a,b)=(5,2)$ this is $(3,-3)$. The operator $T'=\operatorname{diag}(1,2)$ does not commute with $\sigma$, and $T'(1,-1)=(1,-2)\notin W_0$ because $\sigma(1,-2)=(-2,1)\ne-(1,-2)$. Clause 4 of Theorem 10.13z needs `CommG`.
6. *Universal series.* If every coefficient vector $\Xi_\delta$ already lies in $\mathrm{Mall}$, then $c=0$ works in clause 5.

**(b) Theta side.** Take one pair of auxiliary places ($R=1$), levels $M=1,2,3$, $s=1$, and norms $(N_L,N_R)=(7,13)$, $(37,19)$, $(163,109)$. Each is $\equiv1\pmod{2\cdot3^M}$. Put $w_L=1/N_L$ and $w_R=1/N_R$. Then $wN=1$ and $w\equiv1\pmod 3$, as Lemma 10.13w(1) requires. Let the Frobenius eigenvalues be $x_L=\lambda(\sigma_L)=2$ and $x_R=\lambda(\sigma_R)\in\{2,4\}$, and let the untwisted theta sum be $t_0=\sum_\delta\mathrm{th}(\varnothing,\lambda,\delta)=9$. Then $c_0=2$, $N_0=0$ and $v=v_3(9)=2$.

1. *First endpoint.* $v/v_3(3)=2=c_0+N_0$.
2. *Left factor.* $E_L=\mathrm{eR}(2,1/2,w_L,N_L)=(1-2w_L)(1-w_L/2)+(N_L-1)w_L^2$ equals $11/14$, $71/74$, $323/326$ for $M=1,2,3$. Its residue is $(1-2)(1-2^{-1})=1\in\mathbb F_3$, so $E_L\in\mathbb Z_3^\times$. Hence $g(0)=3^{N_0}t_0E_L$ has $v_3(g(0))=2=v$, that is, $3^3\nmid g(0)$.
3. *Right factor.* Put $n=3^M$ and $D_d(X)=\mathrm{eR}(x_R(1+X),x_R^{-1}(1+X)^{n-1},w_R,N_R)$. Modulo $3$ we have $\bar N_R=1$ and $\bar w_R=1$, so the last term of $\mathrm{eR}$ vanishes and $\overline{D_d}=(1-\bar x_R(1+X))(1-\bar x_R^{-1}(1+X)^{n-1})$. For $x_R=2$ this is $u\,X^0$ with $u(0)=(1-2)(1-2)=1$, so $e=0$. For $x_R=4$, where $\bar x_R=1$, it equals $X^2\sum_{j<n-1}(1+X)^j$, so $e=2$ and $u(0)=n-1\equiv-1$. The bound $e\le2=n_{\max}$ is attained.
4. *The congruence.* Take $g=3^{N_0}t_0E_L$ (a constant) and $f=g\,P(1+X)$ with $P(x)=1+N_Rw_R^2-x_Rw_Rx-x_R^{-1}w_Rx^{n-1}$. Then
   $$f-D_dg=-g\,w_R^2\bigl((1+X)^{n}-1\bigr)\in\mathfrak I_M .$$
   The coefficients of $f$ in the powers of $1+X$ play the role of the vectors $\ell^{N_0}\mathrm{th}(Q,\lambda,\cdot)$. For $M=1$ and $x_R=4$ they are $99/13$, $-198/91$, $-99/728$, all $3$-integral, as `adm9` requires.
5. *Evaluation.* At a primitive $3^k$-th root $\zeta$ with $k=M$ we get $f(\zeta-1)=g\,P(\zeta)$, and $P(\zeta)=\mathrm{eq}'(x_R\zeta,w_R,N_R)$ is the Euler factor at the right place, as in `adm10`. Exact norms give $\operatorname{nval}(P(\zeta))=0$ for $x_R=2$. For $x_R=4$ they give $1$, $1/3$, $1/9$ at $k=1,2,3$. The value is the same for all $\varphi(3^k)$ conjugates $\zeta^a$. In each case it equals $2/\varphi(3^k)$, the residual exponent $e=2$ times $\operatorname{nval}(\zeta-1)=1/\varphi(3^k)$.
6. *Endpoints of `partC`.* Here $v_K(\mathrm{thEval})=\operatorname{nval}(f(\zeta-1))-N_0=2+\operatorname{nval}(P(\zeta))$. The lower endpoint $-N_0=0$ holds because $f$ is integral. The upper endpoint $c_0+\varepsilon=2+\varepsilon$ holds at every $k$ for $x_R=2$. For $x_R=4$ it holds exactly when $2/\varphi(3^k)\le\varepsilon$, so only after `exists_level` (Theorem 10.13s) has chosen $k$ large.

**(c) Failure when the left Frobenius is residually trivial.** Replace $x_L=2$ by $x_L=4\equiv1\pmod3$, which the inertia-eigenvalue condition forbids. Then $E_L=15/28$, $135/148$, $639/652$, with $v_3(E_L)=1,3,2$, because the residue is $(1-1)(1-1)=0$. Now $v_3(g(0))=3,5,4>v=2$, so clause (b) of `OrdHyp` fails at $v=c_0+N_0$. Moreover, with $x_R=4$, $v_K(\mathrm{thEval})-c_0=2$, $10/3$, $19/9$, at least $1$ for every $k$. The upper endpoint of `partC` fails for every $\varepsilon<1$, however $k$ is chosen.

##### Example 10.13v. Non-unit denominators: the lattice at $\ell=2$ and a theta sum $t_0=1/3$ [Expository]

The same script certifies the following.

1. *The integral decomposition fails at $\ell=2$.* Run Example 10.13u(a) over $O=\mathbb Z_2$. Now $\det\begin{pmatrix}1&1\\1&-1\end{pmatrix}=-2$ has $v_2=1$, so $\operatorname{sIdx}(B,\mathrm{Mall}_+\oplus\mathrm{Mall}_-)=1$. The reductions of $(1,1)$ and $(1,-1)$ coincide in $\mathbb F_2^2$, and $e_-(1,0)=(1/2,-1/2)\notin\mathbb Z_2^2$, so (I) fails. Nevertheless $\mathrm{Mall}=\mathbb Z_2(1,-1)$ is finitely generated and spans $W_0$, $B$ is $\sigma$-stable, and every $T$ commuting with $\sigma$ preserves $\mathrm{Mall}$. Clauses 1–4 of Theorem 10.13z hold. The operator $A=c_Ge_-$ with $c_G=2$ is $1-\sigma:(x,y)\mapsto(x-y)(1,-1)$. It is integral with $A(B)=\mathrm{Mall}$, at $\ell=2$ as at $\ell=3$. The denominator of $e_-$ is cleared by $c_G$, not inverted.
2. *A universal denominator.* Let $\Xi=\ell^{-1}(1,-1)\in W_0\setminus B$. The least $c$ with $\ell^c\Xi\in\mathrm{Mall}$ is $c=1$ (for $\ell=2,3$). This is the exponent of `UnivSup`, and clause 5 holds with $c=1$: $\ell\,\Xi\otimes[\delta]\in\mathrm{Mall}\otimes O[\Delta]$. With $c=0$ it fails.
3. *A theta sum with a denominator.* Keep Example 10.13u(b) but put $t_0=1/3$, so $c_0=-1$. With $N_0=0$ the theta coefficients are not $3$-integral; for $M=1$, $x_R=4$ they are $11/39$, $-22/273$, $-11/2184$. The least uniform exponent is $N_0=1$, which gives $11/13$, $-22/91$, $-11/728$. Then $\sum_\delta y_\delta=1$, $v=0$ and $v/v_3(3)=0=c_0+N_0$. The left factor is the unit of Example 10.13u, and $v_3(g(0))=0=v$. The window of `partC` is $[-N_0,c_0+\varepsilon]=[-1,-1+\varepsilon]$. For $x_R=2$ we get $v_K(\mathrm{thEval})=-1$ for every $k$: the lower endpoint is attained, and so is the upper one up to $\varepsilon$, so the window has its smallest possible width. For $x_R=4$ we get $v_K(\mathrm{thEval})=0,-2/3,-8/9$ at $k=1,2,3$. The lower endpoint holds strictly, and the upper endpoint holds exactly when $2/\varphi(3^k)\le\varepsilon$.

##### Definitions [Lean, read]

Keep the notation of §10.4.7.2: $i$ is a nonzero-index place, $O=$ `X.O i` is a DVR with maximal ideal $\mathfrak m$, residue field $k_O$ and $K=\operatorname{Frac}O$, $O_k=$ `X.Ok i k`, $\ell=$ `X.l i`, and $\mathfrak I_M$ is the toric augmentation ideal. Write $\lambda_G=$ `X.lamG i lam` $:G\to O^\times$ for $\lambda\in$ `abelian₂ i`.

1. **Theta values and valuations** (`src/Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean:211–259`).
   - The evaluation is $\mathrm{thEval}(Q,\lambda,k,\psi)=\sum_{\delta\in\mathrm{RCG}(Q)}\mathrm{th}(Q,\lambda,\delta)\,\psi(\delta)\in\operatorname{Frac}O_k$.
   - For $a\in O\setminus\{0\}$, $\operatorname{nval}(a)=v_O(a)/v_O(\ell)$; for $x=a/b\in K^\times$, $v_K(x)=\operatorname{nval}(a)-\operatorname{nval}(b)$.
   - The baseline is $c_0(\lambda)=v_K\bigl(\sum_\delta\mathrm{th}(\varnothing,\lambda,\delta)\bigr)$.
   - `QOk Q` says that the places of $Q$ are split, avoid $S_0$, and are closed under conjugation; `SOk` $\lambda\,s$ says $s_2(\lambda)=2s$ and $1\le s\le\mathrm{NFun}+1$.
2. **Integral normalization `adm9 X N0`** (`:427–430`). For every admissible $Q$, every $\lambda$ with `SOk` and every $\delta$, $\ell^{N_0(i)}\mathrm{th}(Q,\lambda,\delta)\in O$. The exponent does not depend on $Q$.
3. **Euler-factor removal `adm10 X`** (`:432–448`). Put $\mathrm{eq}'(Y,X,q)=(1-YX)(1-Y^{-1}X)+(q-1)X^2=1-(Y+Y^{-1})X+qX^2$. Let $Q$ be admissible and let $P\ne\bar P$ be conjugate split places in $Q$. For every $k$, every $\psi$ on $\mathrm{RCG}(Q\setminus\{P,\bar P\})$ and every Frobenius $\sigma$ at $P$,
   $$\mathrm{thEval}(Q,\lambda,k,\psi\circ\mathrm{res})=E_P\cdot\mathrm{thEval}(Q\setminus\{P,\bar P\},\lambda,k,\psi),$$
   where $E_P=\mathrm{eq}'\bigl(X_v(P)\,\psi(\mathrm{art}\,\sigma),N(P)^{-s},N(P)\bigr)$.
   The polynomial version is $\mathrm{eR}(Y,Y',w,q)=(1-Yw)(1-Y'w)+(q-1)w^2$ (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PropEOfAdmissible.lean:106`).
4. **Residual character** (`:344–357`). $\bar\lambda=$ `resChar i lam` is $\lambda_G$ followed by reduction to $k_O^\times$. Its kernel is open, as the preimage of the open set $1+\mathfrak m$ (`O_adic`, `lamG_cont`).
5. **Tame inertia element at a twist prime** (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTameInertiaElementAtTwistPrime.lean:13–17`). The element $z$ lies in an inertia group above some $v\in$ `pD i`, $\delta(z)^2-1\in O_0^\times$, and for every open normal $U$ some $n$ prime to $\ell N(v)$ has $z^n\in U$.
6. **Auxiliary families** (`:32–44`). `SlopeTestRemainingChoices X i M ∅ P d` asks four things of the places $v$ over every $P(q)$: they are split, of degree one and of absolute ramification index one at the underlying rational prime; they lie outside $S_0$; they satisfy $N(v)\equiv1\pmod{2\ell^M}$; and distinct indices give non-conjugate places. Each $d_q$ must also be a good character at $P(q)$. `Steps X i M H z P d` has two clauses:
   - (S1) every Frobenius at a left place $P(\mathrm{inl}\,a)$ is conjugate to an element of $zH$;
   - (S2) every Frobenius $\sigma$ at a right place $P(\mathrm{inr}\,a)$ has $d_{\mathrm{inl}\,b}(\sigma)=\delta_{ab}$.

   `IsQ P Q` says that $Q$ is the set of places over the $P(q)$.
7. **`OrdHyp` and `PropE`.** `OrdHyp` is Definition 1 of §10.4.7.2. `PropE X N0` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:31–42`) is the conclusion of Theorem 10.13y below, with $n_{\max}=2$.
8. **Lattice side** (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean`).
   - $W_0=$ `Fm0` $=\bigcap_{u\in U}\ker(\mathrm{actG}(u)-\psi_U(u))$ (`:32–34`), and $V=$ `V0` $=e(W_0)$ (`:36–37`).
   - $\mathrm{Mall}=B\cap W_0$ with $B=$ `Bsup` (`:242–243`).
   - `IsotypicPartsInternalDirectSum` is the conjunction of the six clauses of Theorem 10.13z (`:245–258`).
   - The sup laws are in `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OffRange.lean:14–27`. `SupG`: $B$ is stable under every $\mathrm{actG}(g)$. `SupFull`: $B$ is finitely generated and spans $\mathrm{Fm}$ over $K$. `SupHk`: $B$ is stable under $\mathrm{hkF}(k,P)$ whenever `HkIdx` $k\,P$. `UnivSup E`: for each $a\in$ `Dat0` there is $c$ such that, for all split $Q$ in `ClsQ` avoiding $S_0$ and `lev a` and all $M$, $\mathrm{thU}(Q,M,a)=\sum_\delta\Xi_\delta\otimes[\delta]$ with $\Xi_\delta\in W_0$ and $\ell^c\Xi_\delta\in B$.
   - `TypeKept E` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AdmissibleIndexBoundAllPowers.lean:55–58`) puts the twisted theta vectors in $(W_0)_{O_k}$.
   - `CommG` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/HeckeSplitOne.lean:82–84`) says that every $\mathrm{actG}(g)$ commutes with every $\mathrm{hkF}(k,P)$.

##### Lemma 10.13w (nonzero after reduction: the inertia-eigenvalue condition) [Lean, read]

*Let $O$ be a DVR with residue field $k_O$, and let $\ell\in\mathfrak m$ be a nonzero integer.*

1. *(Auxiliary norms.) If $M\ge1$ and $q\equiv1\pmod{2\ell^M}$, then $\bar q=1$ in $k_O$. For every $n$ there is $w\in O$ with $wq^n=1$ and $\bar w=1$.*
2. *(Residual inertia eigenvalue.) If $z$ is a tame inertia element at a twist prime, then $\bar\lambda(z)\ne1$ for every $\lambda$.*
3. *(Unit left Euler factors.) Let $\sigma$ be conjugate to an element of $z\ker\bar\lambda$, let $x=\lambda_G(\sigma)$, let $q\equiv1\pmod{2\ell^M}$ with $M\ge1$, and let $w$ be as in (1) with $n=s$. Then $E=\mathrm{eR}(x,x^{-1},w,q)$ is a unit of $O$, with residue $(1-\bar x)(1-\bar x^{-1})$.*
4. *(Residual right factor.) Let $k$ be a field, $n\ge1$ with $n=0$ in $k$, and $x\in k^\times$. In $k[X]$,*
   $$(1-x(1+X))\bigl(1-x^{-1}(1+X)^{n-1}\bigr)=u\,X^{e},\qquad u(0)\ne0,\quad e\in\{0,2\}.$$
   *Here $e=2$ exactly when $x=1$, and then $u=\sum_{j=0}^{n-2}(1+X)^j$ with $u(0)=n-1=-1$.*

*(Lean: `residue_pow_l`, `residue_norm`, `exists_w`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PropEOfAdmissible.lean:394–416`; `resChar_ne_one`, `:359–383`; the unit step inside `propE`, `:531–546`; `eR_res`, `:112–125`.)*

*Proof.* (1) Write $q=2\ell^Mm+1$. Since $\ell\in\mathfrak m$ (`O_l`), $\bar\ell=0$, so $\bar q=1$ (`:394–405`). Hence $q$ is a unit (`IsLocalRing.residue_ne_zero_iff_isUnit`), $q^n$ has an inverse $w$, and $\bar w=\bar w\,\bar q^{\,n}=1$ (`:407–416`).

(2) Unpack the definition: there are $v\in$ `pD i`, a place $A$ over $v$ with $z\in\mathrm{Ine}(A)$, the unit $\delta(z)^2-1\in O_0^\times$, and the prime-to-$\ell N(v)$ property (`:361`). The structure field `lamG_pD` (`src/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:373–376`) gives $n$ with $\bigl(\lambda_G(z)\,\delta(z)^{\mp1}\bigr)^{N(v)^n}=1$, the sign fixed by `sideL`. Let $\phi:O_0^\times\to k_O^\times$ be reduction through $O_0\to O$, and suppose $\bar\lambda(z)=1$. Then $\phi(\delta(z))^{N(v)^n}=1$ (`:368–375`). The prime-to property applied to $U=\ker\delta$, which is open (`delta_open`), gives $m$ prime to $\ell N(v)$ with $z^m\in\ker\delta$, hence $\phi(\delta(z))^m=1$ (`:363–367`). As $\gcd(m,N(v)^n)=1$, $\phi(\delta(z))=1$ (`:376–379`). Then $\delta(z)^2-1$ has residue $0$, contradicting $\delta(z)^2-1\in O_0^\times$ (`:380–383`).

(3) If $g\sigma g^{-1}z^{-1}\in\ker\bar\lambda$, then $\bar\lambda(\sigma)=\bar\lambda(z)$, because $k_O^\times$ is commutative. By (2), $\bar x\ne1$, and so $\bar x^{-1}\ne1$. By (1), $\bar q=1$ and $\bar w=1$, so the residue of $E$ is $(1-\bar x)(1-\bar x^{-1})+0\ne0$, and $E\in O^\times$ (`:534–546`).

(4) If $x\ne1$, take $e=0$ and let $u$ be the product itself; then $u(0)=(1-x)(1-x^{-1})\ne0$. If $x=1$, the geometric-sum identity $(1+X)^{n-1}-1=X\sum_{j<n-1}(1+X)^j$ (`mul_geom_sum`) turns $(-X)\bigl(1-(1+X)^{n-1}\bigr)$ into $X^2\sum_{j<n-1}(1+X)^j$. Its constant coefficient is $n-1=-1\ne0$ in $k$ (`:115–121`). $\square$

##### Lemma 10.13x (one coefficient ring, one lattice) [Lean, read]

*Keep the notation. Let $Q$ be admissible, let $\lambda$ satisfy `SOk` $\lambda\,s$, and assume `adm9 X N0`.*

1. *(Integral lift.) For every finite $\iota$ and every family $d:\iota\to(G\to\mathbb Z/\ell^M)$ there is $f\in O[X_q:q\in\iota]$ with the following property. For every $k$, every $u:\iota\to O_k^\times$ and every $\psi$ on $\mathrm{RCG}(Q)$ with $\psi(\mathrm{art}\,g)=\prod_qu_q^{d_q(g)}$,*
   $$f(u-1)=\ell^{N_0(i)}\,\mathrm{thEval}(Q,\lambda,k,\psi)\quad\text{in }\operatorname{Frac}O_k .$$
   *Explicitly, $f=\sum_\delta y_\delta\prod_q(1+X_q)^{d_q(g_\delta)}$, where $y_\delta=\ell^{N_0}\mathrm{th}(Q,\lambda,\delta)\in O$ and $\mathrm{art}(g_\delta)=\delta$.*
2. *(Characters with prescribed root values.) Under `SlopeTestRemainingChoices`, let $T\subseteq\iota$, let $Q_T$ be the set of places over $P(q)$ for $q\in T$, and let $u_q$ be units with $u_q^{\ell^M}=1$ and $u_q=1$ for $q\notin T$. Then there is $\psi$ on $\mathrm{RCG}(Q_T)$ with $\psi(\mathrm{art}\,g)=\prod_qu_q^{d_q(g)}$.*
3. *(Peeling Euler factors.) Assume `adm10` and `SlopeTestRemainingChoices`. Let $T,W\subseteq\iota$ be disjoint, let $Q_0$ be the set of places over $T$ and $Q$ the set of places over $T\cup W$, and let $\psi$ on $\mathrm{RCG}(Q)$ satisfy $\psi\circ\mathrm{art}=\psi_0\circ\mathrm{art}$ for some $\psi_0$ on $\mathrm{RCG}(Q_0)$. Then*
   $$\mathrm{thEval}(Q,\psi)=\prod_{q\in W}\mathrm{eq}'\bigl(X_v(P_q)\,\psi_0(\mathrm{art}\,\sigma_q),N(P_q)^{-s},N(P_q)\bigr)\cdot\mathrm{thEval}(Q_0,\psi_0).$$
   *If $wq^s=1$, then $\mathrm{eq}'(xt,q^{-s},q)=\mathrm{eR}(xt,x^{-1}t^{-1},w,q)$.*
4. *(Toric grid vanishing.) Let $O\hookrightarrow O'$ be injective into a domain containing a primitive $\ell^M$-th root of unity. If $h\in O[X]$ vanishes at $u-1$ for all $u$ with $u_q^{\ell^M}=1$ and $u_{\mathrm{inr}}=1$, then $h\in\mathfrak I_M$.*
5. *(Isotypic lattice.) (a) If $B$ spans $V$ over $K$ and $M=B\cap W$ for a $K$-subspace $W$, then $\operatorname{span}_KM=W$. (b) Let $\varphi$ be a $K$-linear endomorphism of $\mathrm{Fm}$ with $\varphi(B)\subseteq B$ that commutes with every $\mathrm{actG}(g)$. Then $\varphi(\mathrm{Mall})\subseteq\mathrm{Mall}$.*
6. *(Valuation bookkeeping.) If $x\ne0$ and $xb=a$ in $K$ with $b\ne0$ (so that $a\ne0$), then $v_K(x)=\operatorname{nval}(a)-\operatorname{nval}(b)$; the hypothesis $x\ne0$ cannot be dropped, because for $x=a=0$ the right side would depend on $b$. If $a\ne0$ and $a=\ell^nx$ in $\operatorname{Frac}S$ for a DVR $S$, then $x\ne0$ and $v_K(x)=\operatorname{nval}(a)-n$.*

*(Lean: `exists_lift`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PropEOfAdmissible.lean:299–319`; `exists_char`, `:271–292`; `thEval_remove`, `:209–269`, with `qOk_of_auxiliary_set`, `hom_ext`, `res_art'` and the conjugation lemmas, `:139–207`; `eq'_eq`, `:321–342`; `mem_span_of_vanish`, `mem_span_of_vanish_roots`, `:16–104`; `span_inf_of_span_top`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanInfOfSpanTop.lean:15–34`; `mall_map_le`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmIntOfSupLaws.lean:16–29`; `vK_eq`, `src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ToNatAddValMul.lean:14–49`; `vK_bounds`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:309–321`.)*

*Proof.* (1) Choose $y_\delta$ by `adm9` and lifts $g_\delta$ by `art_surj` (`:307–308`). Then $f(u-1)=\sum_\delta y_\delta\prod_qu_q^{d_q(g_\delta)}=\sum_\delta y_\delta\,\psi(\delta)$, and $y_\delta=\ell^{N_0}\mathrm{th}(Q,\lambda,\delta)$ after `kMap` (`:311–319`). The sum is $\ell^{N_0}\mathrm{thEval}$.

(2) For $q\in T$, the structure field `art_univ` factors the character $\chi_{u_q}\circ d_q$ through $\mathrm{RCG}(Q_T)$. Three of its hypotheses come from `GoodChar`: open kernel, `AntiHom`, and unramifiedness outside the places over $P(q)$. The fourth, that no place of $Q_T$ lies above $\ell$, holds because these places avoid $S_0$, which contains the places above $\ell$ (`:279–289`). For $q\notin T$ take the trivial character, and multiply over $q$ (`:290–292`).

(3) Induct on $W$ (`:222–269`). Adding $q$ to $W$ adds the pair $\{P_q,\bar P_q\}$, where $P_q\ne\bar P_q$ because $P_q$ is split (`ne_of_split`). Removing that pair from $Q$ leaves the places over $T\cup(W\setminus\{q\})$ (`:236–256`). Apply `adm10` to the restricted character and use the induction hypothesis (`:260–269`). For the last assertion, $w\mapsto q^{-s}$ under $O\to\operatorname{Frac}O_k$ because $wq^s=1$, and $(xt)^{-1}=x^{-1}t^{-1}$ (`:321–342`).

(4) This is the argument of Lemma 10.13n(1), repeated in this file (`:16–104`). Divide by the monic generators under `degLex`, then apply `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` on the grid $\{\xi-1:\xi^{\ell^M}=1\}\times\{0\}$.

(5)(a) The inclusion $\operatorname{span}_KM\subseteq W$ holds because $M\subseteq W$. Conversely, let $f\in W$. Since $\operatorname{span}_KB=V$, the Mathlib lemma `multiple_mem_span_of_mem_localization_span` gives $t\in O\setminus\{0\}$ with $tf\in\operatorname{span}_OB=B$. Then $tf\in B\cap W=M$, and $f=t^{-1}(tf)\in\operatorname{span}_KM$ (`SpanInfOfSpanTop.lean:20–34`). (b) Let $f\in\mathrm{Mall}$. Then $\varphi f\in B$. For $u\in U$, $\mathrm{actG}(u)(\varphi f)=\varphi(\mathrm{actG}(u)f)=\varphi(\psi_U(u)f)=\psi_U(u)\,\varphi f$ by commutation and $K$-linearity, so $\varphi f\in W_0$ (`AdmIntOfSupLaws.lean:19–29`).

(6) Cross-multiply two representations of $x$ and use the additivity of $\operatorname{nval}$ on products (`nval_mul`, `toNat_addVal_mul`, `ToNatAddValMul.lean:14–49`); the hypothesis $x\ne0$ (`hx` at `:24`) is what makes $a$ and the numerator of the chosen representation nonzero (`:35–42`), so that `nval_mul` applies. For the second assertion use $\operatorname{nval}(\ell^n)=n$ (`nval_l_pow`) and observe that $x=0$ would force $a=0$ (`IsAuxiliaryPlaceFamilyAtLevelMono.lean:309–321`). $\square$

##### Theorem 10.13y (`propE`: toric factorization of theta evaluations with a unit constant term) [Lean, read]

*Assume `adm9 X N0` and `adm10 X`. Let $i$ be a nonzero-index place, $\lambda\in$ `abelian₂ i` and $z\in G$, and suppose:*

- *(i) `SOk` $\lambda\,s$ for some $s$;*
- *(ii) $\sum_\delta\mathrm{th}(\varnothing,\lambda,\delta)\ne0$;*
- *(iii) $z$ is a tame inertia element at a twist prime.*

*Let $y_\delta=\ell^{N_0}\mathrm{th}(\varnothing,\lambda,\delta)\in O$, $H=\ker\bar\lambda$ and $v=v_O(\sum_\delta y_\delta)$. Then $H$ is open and normal and*
$$\frac{v}{v_O(\ell)}=c_0(\lambda)+N_0(i).$$
*Let $M\ge1$ and $R$ be integers, and let $P:\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,R\to$ places, characters $d$ and a set $Q$ satisfy `SlopeTestRemainingChoices` $(M,\varnothing)$, `Steps` $(M,H,z)$ and `IsQ P Q`. Then there is $f\in O[X]$ with the following four properties.*

- *(a) $f-D_dg\in\mathfrak I_M$. Here $g$ is the lift of Lemma 10.13x(1) for the set $Q_1$ of places over the left indices, and, with $x_a=\lambda_G(\sigma_{\mathrm{inr}\,a})$,*
  $$D_d=\prod_a\mathrm{eR}\bigl(x_a(1+X_{\mathrm{inl}\,a}),\ x_a^{-1}(1+X_{\mathrm{inl}\,a})^{\ell^M-1},\ w_{\mathrm{inr}\,a},\ N(P_{\mathrm{inr}\,a})\bigr).$$
- *(b) $g(0)=\bigl(\prod_aE_L(a)\bigr)\sum_\delta y_\delta$, where each $E_L(a)=\mathrm{eR}(\lambda_G(\sigma_{\mathrm{inl}\,a}),\lambda_G(\sigma_{\mathrm{inl}\,a})^{-1},w_{\mathrm{inl}\,a},N(P_{\mathrm{inl}\,a}))$ is a unit. Hence $v_O(g(0))=v$; in particular $\varpi^{v+1}\nmid g(0)$.*
- *(c) $\overline{D_d}=\prod_au_a\,X_{\mathrm{inl}\,a}^{e_a}$ in $k_O[X]$, with $u_a(0)\ne0$ and $e_a\in\{0,2\}$.*
- *(d) For every $k$, every $u$ with $u_q^{\ell^M}=1$ and every $\psi'$ on $\mathrm{RCG}(Q)$ with $\psi'(\mathrm{art}\,g)=\prod_qu_q^{d_q(g)}$, $f(u-1)=\ell^{N_0}\,\mathrm{thEval}(Q,\lambda,k,\psi')$.*

*In particular `PropE X N0` holds, with `OrdHyp` $(v,2)$ at every level.*
*(Lean: `GlobalTheory.ToricFactor.propE`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PropEOfAdmissible.lean:420–561`; wrapper `GlobalTheory.T.propE_of_admissible`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PropEOfAdmissibleStatement.lean:7–8`.)*

*Proof.* **Step 0 (the untwisted constant).** The empty set is admissible (`:426`). `adm9` at $Q=\varnothing$ gives $y_\delta$, and summing gives $\sum y=\ell^{N_0}\sum\mathrm{th}(\varnothing)$ in $K$ (`:427–431`). Since $\ell\ne0$ in $O$ (`l_ne_zero`, `:385–392`) and (ii) holds, $\sum y\ne0$ (`:432–437`). $H$ is open (`isOpen_ker_resChar`) and normal, being a kernel (`:438–439`). Lemma 10.13x(6) with $x=\sum\mathrm{th}(\varnothing)$, which is nonzero by (ii), $a=\sum y$, $b=\ell^{N_0}$ gives $c_0=v/v_O(\ell)-N_0$. Here $v_O(\ell)\ne0$ because $\ell$ is a nonzero nonunit (`:440–455`).

**Step 1 (Frobenius data).** For each index $q$ choose a Frobenius $\sigma_q$ at $P_q$ (`exists_isFrob`, `src/ReciprocityTheory/GaloisValuations/Global.lean:345`, `[Lean]`). By `Xv_def`, $X_v(P_q)=\lambda_G(\sigma_q)$ (`:459–461`). Moreover $N(P_q)\equiv1\pmod{2\ell^M}$, and Lemma 10.13w(1) gives $w_q$ with $w_qN(P_q)^s=1$ and $\bar w_q=1$ (`:462–463`).

**Step 2 (two lifts with one exponent).** Let $Q_1$ be the set of places over the left indices (`:464–469`). Both $Q$ and $Q_1$ are admissible (`qOk_of_auxiliary_set`). Lemma 10.13x(1) gives $f$ for $Q$ and $g$ for $Q_1$, with the same $N_0$ (`:470–471`). Define $D_d$ as in (a) (`:472–474`). Clause (d) is the defining property of $f$ (`:474`).

**Step 3 (clause (a)).** By Lemma 10.13x(4) with $O'=O_M$, which contains the primitive root `X.zk i M` (`zk_prim`, `Ok_inj`), it suffices to show that $(f-D_dg)(u-1)=0$ whenever $u_q^{\ell^M}=1$ and $u_{\mathrm{inr}}=1$ (`:475`). Lemma 10.13x(2) gives characters $\psi$ on $\mathrm{RCG}(Q)$ and $\psi_1$ on $\mathrm{RCG}(Q_1)$ with these root values (`:476–480`). Lemma 10.13x(3), with $T$ the left indices and $W$ the right indices, gives
$$\mathrm{thEval}(Q,\psi)=\prod_a\mathrm{eq}'\bigl(\lambda_G(\sigma_{\mathrm{inr}\,a})\,\psi_1(\mathrm{art}\,\sigma_{\mathrm{inr}\,a}),N^{-s},N\bigr)\,\mathrm{thEval}(Q_1,\psi_1)$$
(`:481–487`). By (S2) and $u_{\mathrm{inr}}=1$, $\psi_1(\mathrm{art}\,\sigma_{\mathrm{inr}\,a})=\prod_bu_{\mathrm{inl}\,b}^{\delta_{ab}}=u_{\mathrm{inl}\,a}$ (`:488–496`). Multiply by $\ell^{N_0}$ and use $u^{-1}=u^{\ell^M-1}$ together with Lemma 10.13x(3). Each factor becomes the factor of $D_d$ evaluated at $X_{\mathrm{inl}\,a}=u_{\mathrm{inl}\,a}-1$, so $f(u-1)=D_d(u-1)\,g(u-1)$ (`:497–509`).

**Step 4 (clause (b)).** Apply Lemma 10.13x(3) with $T=\varnothing$, $Q_0=\varnothing$, $\psi_0=1$, $k=0$ and $W$ the left indices. This gives $\mathrm{thEval}(Q_1,1)=\prod_a\mathrm{eq}'(\lambda_G(\sigma_{\mathrm{inl}\,a}),N^{-s},N)\,\mathrm{thEval}(\varnothing,1)$ (`:510–513`). Evaluating $g$ at $u=1$ gives $g(0)=\ell^{N_0}\mathrm{thEval}(Q_1,1)$, and $\mathrm{thEval}(\varnothing,1)=\sum\mathrm{th}(\varnothing)$. With Lemma 10.13x(3) this yields $g(0)=\prod_aE_L(a)\cdot\sum y$ (`:514–530`). By (S1), each $\sigma_{\mathrm{inl}\,a}$ is conjugate into $zH$, so Lemma 10.13w(3) makes $E_L(a)$ a unit (`:531–546`). Therefore $v_O(g(0))=v_O(\sum y)=v$ (`:547–549`).

**Step 5 (clause (c)).** Reduce $D_d$ modulo $\mathfrak m$. Since $\bar N=1$ (Lemma 10.13w(1)), the term $(N-1)w^2$ vanishes, and $\bar w=1$. Each factor becomes $(1-\bar x_a(1+X))(1-\bar x_a^{-1}(1+X)^{\ell^M-1})$ with $\bar x_a=\bar\lambda(\sigma_{\mathrm{inr}\,a})$. Lemma 10.13w(4) with $n=\ell^M$, which is $0$ in $k_O$ (`residue_pow_l`), writes this factor as $u_aX_{\mathrm{inl}\,a}^{e_a}$ (`:550–561`). The product $u=\prod u_a$ has $u(0)\ne0$, and $\overline{D_d}-u\prod X^{e_a}=0$ lies in $\langle X_q^{\ell^M}\rangle$. $\square$

The two kinds of auxiliary places are treated asymmetrically. The left factors are evaluated at the trivial character, and they must be units. That is where (S1) and the inertia element enter. The right factors are polynomials in the left variables. Only the shape of their reduction is controlled, and no condition on $\bar\lambda(\sigma_{\mathrm{inr}\,a})$ is imposed; Example 10.13u(b)3 attains $e_a=2$.

##### Theorem 10.13z (`admInt_of_sup`: the isotypic lattice from the sup laws) [Lean, read]

*Let $D$ be a `D7` datum and $E$ an `XD D`. Assume `SupG`, `SupFull`, `SupHk`, `UnivSup E`, `TypeKept E` and `CommG`. Then `IsotypicPartsInternalDirectSum D.nexp E` holds. That is, for every nonzero-index place $i$, every $1\le j\le m$ and every $b$:*

1. *$B=$ `Bsup` is stable under every $\mathrm{actG}(g)$;*
2. *$\mathrm{Mall}=B\cap W_0$ is finitely generated over $O$;*
3. *$\operatorname{span}_K\mathrm{Mall}=W_0$;*
4. *$\mathrm{hkO}(k,P)(\mathrm{Mall})\subseteq\mathrm{Mall}$ whenever `HkIdx` $k\,P$;*
5. *for every $a\in$ `Dat0` there is $c$ such that $\ell^c\,\mathrm{thU}(Q,M,a)$ lies in the image of $\mathrm{Mall}\otimes O[\Delta_{Q,M}]$, for every split $Q$ in `ClsQ` avoiding $S_0$ and `lev a`, and every $M$;*
6. *the twisted theta vectors lie in $(W_0)_{O_k}$ (`TypeKept`).*

*No splitting $B=\bigoplus_\chi(B\cap\mathrm{Fm}_\chi)$ is asserted or used.*
*(Lean: `GlobalTheory.IntSup.admInt_of_sup`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmIntOfSupLaws.lean:31–51`; wrapper `GlobalTheory.T.admInt_of_sup_laws`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmIntOfSupLawsStatement.lean:7–8`; main-path call, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:38`.)*

*Proof.* Fix $(i,j,b)$. `SupFull` gives that $B$ is finitely generated and that $\operatorname{span}_KB=\mathrm{Fm}$ (`:34`).

1. The image of $f\in B$ under $\mathrm{actG}(g)$ lies in $B$ by `SupG` (`:39–40`).
2. $\mathrm{Mall}\subseteq B$, and $O$ is Noetherian, so $\mathrm{Mall}$ is finitely generated (`Submodule.FG.of_le`, `:41`).
3. Apply Lemma 10.13x(5)(a) with $W=W_0$ and $M=\mathrm{Mall}$; membership in $\mathrm{Mall}$ is membership in both (`:36`).
4. Apply Lemma 10.13x(5)(b) with $\varphi=\mathrm{hkF}(k,P)$: `SupHk` gives $\varphi(B)\subseteq B$ and `CommG` gives the commutation (`:37`).
5. `UnivSup` gives $c$ and $\mathrm{thU}=\sum_\delta\Xi_\delta\otimes[\delta]$ with $\Xi_\delta\in W_0$ and $\ell^c\Xi_\delta\in B$ (`:42–45`). Since $W_0$ is a $K$-subspace, $\ell^c\Xi_\delta\in W_0$ as well, so $\ell^c\Xi_\delta\in\mathrm{Mall}$ (`:48–49`). Hence $\ell^c\mathrm{thU}=\sum_\delta(\ell^c\Xi_\delta)\otimes[\delta]$ (`smul_tmul'`) is the image of $\sum_\delta\langle\ell^c\Xi_\delta\rangle\otimes[\delta]\in\mathrm{Mall}\otimes O[\Delta]$ (`:46–51`).
6. This is `TypeKept` (`:38`). $\square$

Of the three statements in the Motivation, only (R) occurs here: it is the definition of $W_0$, used in clauses 3–5. Statement (I) is absent. Statement (N) is absent too: the lattice side carries its denominators as the exponent $c$ and never reduces modulo $\mathfrak m$. The non-divisibility used downstream is produced only in Theorem 10.13y(b).

##### The `partC` step, and the return to Proposition 10.13j and `GoodTw` [Lean, read]

The two theorems are consumed in `admissibleIndexBoundAllPowers_of_conditions` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:92–222`) and in Theorem 10.13i.

1. *Inputs.* The element $z$ comes from `exists_tameInertiaElementAtAuxiliaryPrime` (`:100`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTameInertiaElementAtAuxiliaryPrime.lean:85`, `[Lean]`). For each $\lambda$, Theorem 10.13y gives $(H_E(\lambda),v_E(\lambda))$ and the polynomial family $f_E$ (`:103`).
2. *One subgroup, one family of places.* $H=\bigcap_\lambda H_E(\lambda)\cap\bigcap_yH_B(y)$ is open, as a finite intersection, and normal (`:106–112`). The auxiliary families supplied by `GaloisSideTwistedSelmerAuxiliaryPrimes` (`[Lean]`) have their Frobenius steps in $H$ and avoid $A_0\cup\bigcup_yA_y$ (`:113–117`). The lemmas `steps_mono` ($H\le H_E(\lambda)$) and `isAuxiliaryPlaceFamilyAtLevel_mono` ($\varnothing\subseteq A$) make Theorem 10.13y applicable at every level (`:118–119`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:170–176`).
3. *One call of `exists_level`.* Theorem 10.13s is applied once, with $J=$ `abelian₂ i` $\sqcup\{\text{blocks}\}$, $v=\mathrm{Sum.elim}\,v_E\,v_B$ and $n_{\max}=2+\sum_yn_y$. The bound `OrdHyp` $(v_E,2)$ of Theorem 10.13y is weakened to $n_{\max}$ by `ordHyp_mono` (`:133–144`).
4. *`partC`* (`:198–208`). Fix $\lambda$ and the root $\zeta$ or $\zeta^{-1}$, chosen by `sideL` $\lambda$ (`side_root`). Theorem 10.13s(2) gives $f_E(u-1)\ne0$ and $\operatorname{nval}(f_E(u-1))\le v_E/v_O(\ell)+\varepsilon$. Theorem 10.13y(d) gives $f_E(u-1)=\ell^{N_0}\mathrm{thEval}(Q,\lambda,k,\texttt{psiAt}(\texttt{sideL}\,\lambda)\,\psi')$. Lemma 10.13x(6), second assertion with $a=f_E(u-1)\ne0$, gives $\mathrm{thEval}\ne0$ and $v_K(\mathrm{thEval})=\operatorname{nval}(f_E(u-1))-N_0$. With $v_E/v_O(\ell)=c_0+N_0$ this yields
   $$-N_0\ \le\ v_K(\mathrm{thEval})\ \le\ c_0+\varepsilon\ \le\ c_0+\varepsilon' ,$$
   because $\operatorname{nval}\ge0$ and $\varepsilon=\varepsilon'/C$ with $C\ge1$.
5. *Into `GoodTw`.* Theorem 10.13i passes `partC` unchanged into `GoodTw` as its fifth conjunct (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:219–231`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:28,53`). On the lattice side, the conclusion of Theorem 10.13z is the hypothesis `h3` of Theorem 10.13i (`:17`). It is used by Proposition 10.13h (`abHyp_fam`, `:23`) and by Theorem 10.13g (`export_at` and `isLatIn_B`, `:31–41`), which give the second and third conjuncts of `GoodTw`. It is also an input of `admT3_of_hecke_semisimple`, which supplies `GoodLatticePoints` (`TwistTheoremAllPowersOfSelmerSupLattice.lean:40`, `[Lean]`).

The theta clause is uniform in the power $a$ for the same reason as the lattice clauses. The data $(H_E,v_E,f_E)$ are fixed before $(M,k,e)$, and the power $a$ enters only through $\zeta=\zeta_k^a$. In Examples 10.13u and 10.13v the lower endpoint $-N_0$ is the integrality of $f$, that is, `adm9` at $Q$. The upper endpoint $c_0+\varepsilon$ is the exact valuation of Theorem 10.13y(b) combined with the choice of $k$ in Theorem 10.13s. Example 10.13u(c) shows that the upper endpoint is lost when the inertia-eigenvalue condition is dropped.

##### Remarks, source map, and reading boundary

*Remark 1 (classical comparisons) [Expository].*

- *Canonical decomposition.* Serre's canonical decomposition of a representation of a finite group of order $g$ ([SerreLinearReps](../sources/SOURCES.md#6-literature), §2.6, Theorem 8, pp. 21–22) writes $V=V_1\oplus\cdots\oplus V_h$, with projection $p_i=\frac{n_i}{g}\sum_{t\in G}\overline{\chi_i(t)}\,\rho_t$. His example following Theorem 8 is the group $\{1,s\}$, for which $V=V^+\oplus V^-$ splits into symmetric and antisymmetric elements. Example 10.13u(a) is that example over $\mathbb Q_3$ with the lattice $\mathbb Z_3^2$. Example 10.13v(1) shows that over $\mathbb Z_2$ the denominator $g=2$ of the projections obstructs the integral splitting. `Fm0` is one canonical summand, for the character $\psi_U$, and `Mall` replaces the projection by an intersection.
- *Euler-system relation.* The relation `adm10` has the shape of the Euler-system norm relation ([Rubin2000](../sources/SOURCES.md#6-literature), Definition 2.1.1, in the restatement of [LoefflerZerbes2017](../sources/SOURCES.md#6-literature), Definition 2.2): $\mathrm{cores}^{F'}_F(c_{F'})=\bigl(\prod_{q\in\Sigma(F'/F)}P_q(\sigma_q^{-1})\bigr)c_F$, where $P_q(X)=\det(1-X\,\mathrm{Frob}_q^{-1}\mid T^\vee(1))$ on the Tate dual $T^\vee(1)$. In both, enlarging the set of auxiliary primes multiplies by a local Euler factor evaluated at a Frobenius; in `adm10` the factor is the degree-two polynomial $\mathrm{eq}'(Y,X,q)=1-(Y+Y^{-1})X+qX^2$. The comparison is one of shape only. `adm10` is a hypothesis about the archive's theta values, not a statement about cohomology classes. We have read the restatement, not Rubin's page.
- *Mathlib inputs.* `multiple_mem_span_of_mem_localization_span` (`Mathlib/RingTheory/Localization/Finiteness.lean:96–118` at the pinned commit) clears the denominator in Lemma 10.13x(5)(a). `IsLocalRing.residue_ne_zero_iff_isUnit` (`Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean:41–42`) is the unit criterion behind Lemma 10.13w and Theorem 10.13y(b).

*Remark 2 (the name `IsotypicPartsInternalDirectSum`).* None of its six clauses says that $B$ or $\mathrm{Fm}$ is an internal direct sum of isotypic parts. Example 10.13v(1) satisfies clauses 1–4 while $B\ne\mathrm{Mall}_+\oplus\mathrm{Mall}_-$. When comparing with the classical literature, read the predicate as follows: `Mall` is a Hecke-stable lattice in the $\psi_U$-isotypic part, the universal series has bounded denominators, and the twisted vectors have the right type.

*Remark 3 (scope of verification).* We read these declarations line by line against the pinned archive `lean.tar.gz` (SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`) and built the book with `mdbook build`. Neither source reading nor book compilation is a Lean kernel verification. The examples are certified by exact arithmetic in our script, not by Lean.

| Item | Pinned archive source | Level here |
|---|---|---|
| `propE`; `exists_lift`, `thEval_remove`, `exists_char`, `eq'_eq`, `eR`, `map_eR`, `eR_res`, `chi`; `resChar`, `isOpen_ker_resChar`, `resChar_ne_one`; `l_ne_zero`, `residue_pow_l`, `residue_norm`, `exists_w`; `mem_span_of_vanish`, `mem_span_of_vanish_roots`; `qOk_of_auxiliary_set`, `hom_ext`, `res_art'`, `kMap_algebraMap` and the conjugation lemmas | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PropEOfAdmissible.lean:16–561` | [Lean, read] |
| `propE_of_admissible`, `admInt_of_sup_laws` (wrappers) | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PropEOfAdmissibleStatement.lean:7–8`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmIntOfSupLawsStatement.lean:7–8` | [Lean, read] |
| `admInt_of_sup`, `mall_map_le`; `span_inf_of_span_top` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmIntOfSupLaws.lean:16–51`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanInfOfSpanTop.lean:15–34` | [Lean, read] |
| `vK_eq`, `nval_mul`, `toNat_addVal_mul`; `vK_bounds` | `src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ToNatAddValMul.lean:14–49`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:309–321` | [Lean, read] |
| The `propE` call, the common subgroup, the `exists_level` call and the `partC` step of the main-path producer | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:100–144,198–208` | [Lean, read] |
| Definitions `PropE`, `OrdHyp`; `IsTameInertiaElementAtTwistPrime`, `Over`, `SlopeTestRemainingChoices`, `Steps`, `IsQ`; `thEval`, `nval`, `vK`, `c0`, `QOk`, `SOk`, `partC`, `adm9`, `eq'`, `adm10`; `Fm0`, `V0`, `Mall`, `IsotypicPartsInternalDirectSum`, `GoodTw`; `SupG`, `SupFull`, `SupHk`, `UnivSup`, `TypeKept`, `CommG` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:16–42`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTameInertiaElementAtTwistPrime.lean:13–44`; `src/Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean:211–259,317–321,427–448`; `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:32–37,219–258`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OffRange.lean:14–27`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AdmissibleIndexBoundAllPowers.lean:55–58`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/HeckeSplitOne.lean:82–84` | [Lean, read] (definitions) |
| Structure fields of `NTw` used as data: `lamG_pD`, `lamG_cont`, `Xv_def`, `O_l`, `O_adic`, `delta_open`, `zk_prim`, `Ok_inj`, `art_surj`, `art_univ` | `src/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:288–403` | [Lean] (fields, not proofs) |
| Named inputs kept at their boundary: `exists_isFrob`; `exists_tameInertiaElementAtAuxiliaryPrime`; `GaloisSideTwistedSelmerAuxiliaryPrimes` and its producer `galois_twisted_selmer_auxprimes_of_matrix_and_bounds` (read in §10.4.7.4); the producers of `AdmACD` (`adm9`, `adm10`) and of the sup laws, which are hypotheses of the main-path theorem; `admALG_of_commG_var`; `admT3_of_hecke_semisimple`; the readers of the `partC` conjunct after `GoodTw` | `src/ReciprocityTheory/GaloisValuations/Global.lean:345`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTameInertiaElementAtAuxiliaryPrime.lean:85`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:70`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisTwistedSelmerAuxprimesOfMatrixAndBounds.lean:47`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:24–40`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CentralIdempotentOfCommStatement.lean:8`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmT3OfHeckeSemisimpleStatement.lean:7` | [Lean] (retained boundary) |
| Toric determinant, simultaneous level selection, lattice-index specialization | §§10.4.7.1–10.4.7.2 | [Lean, read] (inherited, cited only) |

#### 10.4.7.4 One family of auxiliary places for the Selmer polynomials and the theta steps

##### Motivation [Expository]

Sections 10.4.7.2 and 10.4.7.3 read the polynomials that enter the single call of `exists_level` in the main-path producer: the lattice polynomials $f_y$ of Theorem 10.13p, and the theta polynomials $f_E(\lambda)$ of Theorem 10.13y. Both were produced *for a given family* $P$ of auxiliary places and *for given* characters $d$ on them. The third kind of polynomial in that call, the Selmer polynomials $F_s$, and the family $P$ itself were left at `[Lean]`. This subsection reads their producer, `galois_twisted_selmer_auxprimes_of_matrix_and_bounds`, and the consumer step that turns the Selmer polynomials into the clause `partAT` of `GoodTw`.

The point to understand is a question of bookkeeping, not of depth. The twist clause `partAT` bounds the twisted Selmer lengths of all good signatures $s$ by $\nu+\varepsilon_T(s)$. The theta clause `partC` needs, at the left auxiliary places, Frobenius elements that are conjugate into $zH$; the lattice clause `partAB` needs the same at the subgroup $H_B$. All three clauses are stated for **one** set $Q$ of places and **one** character $\psi'$ on $\mathrm{RCG}(Q)$. So the places must be chosen once, for all three purposes, and their characters $d_q$ must be the ones that both the Selmer presentation and the theta identity see. The archive does this in a single theorem whose conclusion lists, for one family $P$:

- the local conditions on the places (`SlopeTestRemainingChoices`), avoiding a finite set $A$ that the consumer chooses;
- the Frobenius conditions `Steps` at a subgroup $H'$ that the consumer chooses;
- for every signature $s$ in a set $T$, a polynomial $F_s$ in the variables $X_q$ ($q\in\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,R$) that computes the twisted Selmer lengths at every character built from the $d_q$ (`SelPoly`), together with one coefficient of bounded degree and bounded valuation.

The last item is the Selmer-side non-divisibility: $\ell^{\nu+1}$ does not divide some coefficient of $F_s$ of degree at most $D_d$. It must be kept apart from the theta-side non-divisibility of Theorem 10.13y(b), which is a statement about the constant term $g(0)$ of a different polynomial. Both are consumed by the same lemma `exists_level`, which is why they must be stated for the same variables; but they are proved by different theorems and bound different quantities.

Two features of the producer deserve attention before the proof. First, the Selmer polynomial is not produced directly. The Selmer theorem `ThmS` gives a square matrix $\Phi$ over the group ring $\Lambda=O_0[\Delta]$, $\Delta=(\mathbb Z/\ell^M)^{2R}$, and the determinant $\det\Phi\in\Lambda$ is lifted to a polynomial by the surjection $O_0[X_q]\to\Lambda$, $X_q\mapsto[\gamma_q]-1$. The lift is not unique; the coefficient bound is a statement about *every* lift (it is quantified over all $F$ with $\mathrm{toLam}\,F=\det\Phi$ in `OrdBound`), so any lift serves. Second, the level $M_0$ returned by the order bounds may be $0$, while `ThmS` is stated for $M\ge1$; the producer replaces $M_0$ by $\max(M_0,1)$.

##### Example 10.13aa. One grid, two outputs over $\mathbb Z_3[\zeta_{27}]$ [Expository]

This example models the algebra of Theorem 10.13ae and Proposition 10.13af with $R=1$; it is not an instance of the archive's data `NTw`. All numbers were recomputed in exact rational arithmetic by the run's script `check_examples.py` (40 checks, 0 failures; valuations in $\mathbb Q(\zeta_{27})$, $\mathbb Q(\zeta_8)$ and $\mathbb Q(\zeta_{24})$ are read off from norms, $\operatorname{nval}(\alpha)=v_p(N(\alpha))/[K:\mathbb Q]$ whenever a unique prime lies above $p$).

**The common input.** Take $\ell=3$, $O_0=O=\mathbb Z_3$, $\nu=0$, $R=1$ and $M=3$. The family $P$ consists of a left place $P_L$ and a right place $P_R$ with norms $N_L=163$ and $N_R=109$; both are $\equiv1\pmod{2\cdot3^3}$ as `SlopeTestRemainingChoices` requires. The characters $d_L,d_R:G\to\mathbb Z/27$ are the good characters at these places. Let $\Delta=(\mathbb Z/27)^2$ with generators $\gamma_L,\gamma_R$, $\Lambda=\mathbb Z_3[\Delta]$, and $X_L=[\gamma_L]-1$, $X_R=[\gamma_R]-1$. The level lemma (Theorem 10.13s) is modelled by the choice $k=3$, $e_L=e_R=0$, $\zeta=\zeta_{27}$, so the grid point is $u_L=u_R=\zeta$, that is $X_q\mapsto\zeta-1$ with $\operatorname{nval}(\zeta-1)=1/\varphi(27)=1/18$. The character is $\psi'(\mathrm{art}\,g)=\zeta^{d_L(g)}\zeta^{d_R(g)}$.

**Output 1 (Selmer).** Model the presentation matrix by the $1\times1$ matrix $\Phi=(3+X_L)$. Its entry is a non-unit of $\Lambda$: modulo $3$ it is $X_L$, and $X_L^{27}=[\gamma_L^{27}]-1=0$ by Frobenius in characteristic $3$. The powers of $X_L$ below degree $27$ are nonzero by the group-basis argument below, so its nilpotence index is exactly $27$. The lift is $F=3+X_L\in\mathbb Z_3[X_L,X_R]$. Its coefficient at the monomial $X_L$ (degree $1\le D_d$) is $1$, of valuation $0=v(3^{\nu})$; this is the coefficient bound of `OrdBound`. At the grid point,
$$F(u-1)=3+(\zeta-1)=2+\zeta,\qquad \operatorname{nval}(2+\zeta)=\tfrac1{18},$$
because $\operatorname{nval}(3)=1>1/18$. Hence `SelPoly` gives $\operatorname{sLen}(s,k,Q,\psi')=1/18$, and `partAT` holds with $\varepsilon_T(s)=1/18$: the bound is $\nu+\varepsilon_T=0+1/18$. The level clause of Theorem 10.13s, $\ell^{e_L}/\varphi(\ell^k)=1/18\le\varepsilon$, is exactly what is needed. Had the level been $M=k=1$, the same $F$ at $u_L=\zeta_3$ gives $\operatorname{nval}(2+\zeta_3)=1/2$: the Selmer length would be $1/2$, and $\varepsilon\ge1/2$ would be forced. This is why the producer may only promise a level $M_0$, and the consumer must be free to go higher.

**Output 2 (theta), same input.** With the same $P$, $d$, $Q$, $k$, $\zeta$ and $u$, Example 10.13u(b) at $M=3$ applies. The left Frobenius value $x_L=2$ (forced residually by `Steps`(S1) and the inertia eigenvalue) gives the unit $E_L=323/326$, so $v_3(g(0))=v_3(9\cdot E_L)=2=v$. The right Euler factor, evaluated at the **left** variable through `Steps`(S2), is $P(\zeta)=\mathrm{eq}'(x_R\zeta,1/109,109)$ with $\operatorname{nval}(P(\zeta))=0$ for $x_R=2$ and $=1/9$ for $x_R=4$. Hence $v_K(\mathrm{thEval})=c_0+\{0,1/9\}$, and `partC` holds with $\varepsilon\ge1/9$. The same grid point $\zeta-1$ that produced the Selmer length $1/18$ produces the theta valuation; neither computation knows about the other, but both are evaluations of polynomials in $X_L,X_R$ at the same point.

##### Example 10.13ab. A ramified coefficient grid and $\nu=1$ over $\mathbb Z_2[\zeta_3]$ [Expository]

Take $\ell=2$, $O_0=O=\mathbb Z_2[\zeta_3]$ (residue field $\mathbb F_4$, so that a residually nontrivial inertia eigenvalue exists), $\nu=1$, $R=1$, $M=3$, $k=3$, $\zeta=\zeta_8$, and the exponents $e_L=0$, $e_R=1$, so $u_L=\zeta_8$ and $u_R=\zeta_8^2=i$. Then $\operatorname{nval}(u_L-1)=1/4$ and $\operatorname{nval}(u_R-1)=1/2$; the level clause reads $2^{e_q}/\varphi(8)\in\{1/4,1/2\}\le\varepsilon$. The auxiliary norms $N_L=17$, $N_R=97$ are $\equiv1\pmod{2\cdot2^3}$.

**Output 1 (Selmer, $\nu=1$).** Take $F=4+2X_L+X_LX_R$. Two coefficients satisfy the bound of `OrdBound` with $\mu=v(2^{\nu})=v(2)$: the coefficient $2$ of $X_L$ (degree $1$) and the coefficient $1$ of $X_LX_R$ (degree $2$). At the grid point the three terms have $\operatorname{nval}=2,\ 5/4,\ 3/4$, so
$$\operatorname{nval}\bigl(F(u-1)\bigr)=\tfrac34\le\nu+\varepsilon=1+\varepsilon .$$
Here the bound $\nu+\varepsilon$ holds with room to spare; the role of $\nu$ is to allow Selmer lengths up to $1$ at every good signature. With $e_R=0$ instead, $X_R\mapsto X_L$ and $F(u-1)=\zeta_8^2+3$ has $\operatorname{nval}=1/2$.

**Output 2 (theta), same input.** Let the left Frobenius value be $x_L=\zeta_3$, whose residue in $\mathbb F_4^\times$ has order $3$ and so is $\ne1$. Then $E_L=\mathrm{eR}(\zeta_3,\zeta_3^{-1},1/17,17)=19/17$ is a $2$-adic unit, as Lemma 10.13w(3) predicts. Replacing $x_L$ by $3\equiv1\pmod 2$ gives $E_L'=44/51$ with $v_2(E_L')=2$: the inertia-eigenvalue condition is what keeps the constant term exact. For the right factor at $u_L=\zeta_8$, computed in $\mathbb Q(\zeta_{24})$, $x_R=\zeta_3$ gives $\operatorname{nval}=0$ and $x_R=3$ gives $\operatorname{nval}=1/2=2\cdot\operatorname{nval}(\zeta_8-1)$, the residual exponent $e=2$ of Lemma 10.13w(4) times the valuation of the grid point.

##### Example 10.13ac. Two families chosen separately [Expository]

Suppose the Selmer polynomials were produced for one family $P$ and the theta polynomials for another family $P'$, each with its own characters. Three things go wrong, and the first is fatal.

1. **No common character.** `SelPoly` evaluates $F_s$ at $u_q$ for characters $\psi$ with $\psi(g)=\prod_q u_q^{d_q(g)}$ built from the characters $d$ of $P$; Theorem 10.13y(d) evaluates $f_E$ at $u'_{q'}$ for characters built from the $d'$ of $P'$. The clause `GoodTw` needs one $Q$ and one $\psi'$. The lemma `exists_level` takes all polynomials in the *same* variables $X_q$, $q\in\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,R$, and returns one $(M,k,e,\zeta)$; it cannot be applied to polynomials in two unrelated sets of variables.
2. **Merging the places changes the Selmer side.** If one tries to take $Q=Q_P\cup Q_{P'}$, the relaxed set in `selOn` grows, and the original Selmer group embeds into the group with relaxed conditions. In a toy model where the extra places contribute a diagonal factor $X_{L'}$ to the determinant, the length at $u_{L'}=\zeta_{27}$ grows by $1/18$ and at $\zeta_3$ by $1/2$. The matrix $\Phi$ of `ThmS` computes the Selmer functor of its own $Q$ only.
3. **Merging the places changes the theta side.** The theta evaluation at $Q$ acquires the Euler factors at the places of $P$, evaluated at Frobenius values that `Steps` for $P'$ does not control. If the left place of $P$ has $x=4\equiv1\pmod3$ at $N=7$ ($M=1$), the extra factor at the trivial character is $15/28$, and at $u=\zeta_3$ it has $\operatorname{nval}=3/2$; at $N=163$, $M=3$, $u=\zeta_{27}$ it has $\operatorname{nval}=1/9$. At each of these fixed levels, an extra factor of that valuation can exceed the available tolerance $\varepsilon$. The residue zero also removes the original constant-term unit witness. In the same mechanism with $M\ge2$, $N\equiv1\pmod{2\cdot3^M}$ and primitive $\zeta$ of order $3^M$, write $y=4\zeta$. Then $NE=(N-1)-(y-1)^2/y$. The two terms have valuations at least $M$ and exactly $2/\varphi(3^M)$, respectively, so the latter is the valuation of the extra factor. It tends to zero as $M$ increases.

The producer of Theorem 10.13ae avoids all three by choosing $P$ once, with `Steps` at the subgroup $H'=\bigcap_\lambda H_E(\lambda)\cap\bigcap_yH_B(y)$ that the consumer passes in.

##### Definitions [Lean, read]

Keep the notation of §§10.4.7.2–10.4.7.3. The Selmer coefficient ring is $O_0=$ `X.O0 i`, a DVR with $O_0\hookrightarrow O\hookrightarrow O_k$; $\ell=$ `X.l i` is prime; $\nu=$ `nu X i` is a natural number attached to $i$ (`src/Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean:247–248`). A signature is $s\in$ `X.Sig i`; `GalHyp bkP i s` bundles its isotypic, stability, self-duality, no-jump, `adm3` and rank hypotheses (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTameInertiaElementAtTwistPrime.lean:119–120`).

1. **The group ring and its toric presentation** (`:46–59`). For a finite index type $\iota$, $\mathrm{Del}=\Delta_\iota=(\iota\to\mathbb Z/\ell^M)$ written multiplicatively, $\Lambda=$ `abelian₂ X i M ι` $=O_0[\Delta_\iota]$, and
   $$\mathrm{toLam}:O_0[X_q:q\in\iota]\to\Lambda,\qquad X_q\mapsto[e_q]-1,$$
   where $e_q$ is the generator $\mathrm{ofAdd}(\mathrm{Pi.single}\,q\,1)$. The family $d:\iota\to(G\to\mathbb Z/\ell^M)$ assembles to $\mathrm{delAll}\,d:G\to\Delta_\iota$, and $\mathrm{delInv}\,d:G\to\Lambda^\times$ is the inverse of its image under $g\mapsto[g]$.
2. **Computing the Selmer functor** (`:96–107`). For a square matrix $\Phi$ over $\Lambda$, `Computes bkP i s M d Q Φ` says: for every discrete $\Lambda$-module $B$ that is $\ell$-power torsion there is a $\Lambda$-linear isomorphism $e_B:\ker(\Phi\mid B^a)\cong\mathrm{selOn}(s,\mathrm{delInv}\,d,B,Q)$, the Selmer submodule of $H^1(G,\rho_s\otimes\mathrm{delInv}\,d\otimes B)$ with Bloch–Kato conditions above $\ell$ and relaxed conditions at the places of `Spl i` $\cup Q$, and these isomorphisms are compatible with $\Lambda$-linear maps $B\to B'$ on cocycle representatives.
3. **Selmer polynomials** (`:112–117`). `SelPoly bkP i s M d Q F` says: for every $k$, every $u:\iota\to O_k^\times$ with $u_q^{\ell^M}=1$ and every $\psi:G\to O_k^\times$ with $\psi(g)=\prod_qu_q^{d_q(g)}$,
   $$\operatorname{sLen}(s,k,Q,\psi)=\mathrm{valE}\bigl(F(u-1)\bigr),$$
   where $\operatorname{sLen}$ is the $O_k$-length of the twisted Selmer group `selT` divided by $v(\ell)$ (`BlochKatoPhases.lean:184–195`), $F(u-1)$ is `eval₂ (phiK X i k) (u - 1) F`, and $\mathrm{valE}(x)=v(x)/v(\ell)\in[0,\infty]$ (`:109–110`).
4. **The four hypotheses** (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:46–68`).
   - `ThmS bkP`: for $s$ with `GalHyp`, $M\ge1$, any finite $\iota$, $P$, $d$ with `SlopeTestRemainingChoices` $(M,\varnothing)$ and $Q$ with `IsQ P Q`, there are $a$ and $\Phi\in M_a(\Lambda)$ with `Computes` and with no unit entry.
   - `SelmerLengthsByDeterminant bkP`: under the same hypotheses, `Computes` $\Phi$ and $\mathrm{toLam}\,F=\det\Phi$ imply `SelPoly` $F$.
   - `OrdBound bkP i μ`: for every $T\subseteq$ `Sig i` with `GalHyp` on $T$ there are $R,D_d,M_0$ such that for $M\ge M_0$, every `AdmFam` $(H,S,d)$, every tame inertia element $z$, every open normal $H'$ and every finite $A$, there is $P:\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,R\to$ places with `SlopeTestRemainingChoices` $(M,A,P,d\circ P)$, `Steps` $(M,H',z,P,d\circ P)$, and: for all $s\in T$, $Q$ with `IsQ`, $\Phi$ with `Computes` and $F$ with $\mathrm{toLam}\,F=\det\Phi$, some monomial $m$ with $\deg m\le D_d$ has $v_{O_0}(F_m)\le\mu$.
   - `ResidualBoundOddPrimes bkP` $:=\forall i,\ \nu=0\Rightarrow$ `OrdBound` $0$; `ThmC bkP` $:=\forall i,\ \nu>0\Rightarrow$ `OrdBound` $v_{O_0}(\ell^{\nu})$.
5. **The conclusion** `GaloisSideTwistedSelmerAuxiliaryPrimes bkP` (`:70–77`) is `OrdBound` with three changes: $1\le M_0$ is asserted; the quantification over $\Phi$ and over lifts $F$ is replaced by $\exists F$; and the coefficient bound is stated with $\mu=v_{O_0}(\ell^{\nu})$ and together with `SelPoly` $F$:
   $$\forall s\in T,\ \forall Q,\ \mathrm{IsQ}\,P\,Q\Rightarrow\exists F,\ \mathrm{SelPoly}(s,M,d\circ P,Q,F)\wedge\exists m,\ \deg m\le D_d\wedge v_{O_0}(F_m)\le v_{O_0}(\ell^{\nu}).$$
6. **`partAT`** (`BlochKatoPhases.lean:304–308`): there is $\varepsilon_T:\mathrm{Sig}\to\mathbb R_{\ge0}$ with $\sum_{s\in\mathrm{SigG}}\varepsilon_T(s)\le\varepsilon'$ and, for every good $s$, $\operatorname{sLen}\bigl(s,k',Q,\mathrm{psiAt}(\mathrm{side}\,s)(\psi'\circ\mathrm{art})\bigr)\le\nu+\varepsilon_T(s)$. It is the fourth conjunct of `GoodTw` (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:219–231`) and the second of `admissibleIndexBoundAllPowers` (`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AdmissibleIndexBoundAllPowers.lean:14–21`).

##### Lemma 10.13ad (the toric presentation of the group ring, and two weakenings) [Lean, read]

1. *For any commutative ring $O$, $n\ge1$ and finite $\iota$, the $O$-algebra map $O[X_q]\to O[(\iota\to\mathbb Z/n)]$, $X_q\mapsto[e_q]-1$, is surjective. In particular `toLam X i M ι` is surjective for every $M$.*
2. *`SlopeTestRemainingChoices X i M A P d` implies `SlopeTestRemainingChoices X i M ∅ P d`.*
3. *(Inherited.) `Steps` is monotone in the subgroup, and `SlopeTestRemainingChoices` is antitone in the avoided set.*

*(Lean: `aeval_gen_sub_one_surjective`, `toLam_surjective`, `SlopeTestRemainingChoices.empty`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisTwistedSelmerAuxprimesOfMatrixAndBounds.lean:11–45`; `steps_mono`, `isAuxiliaryPlaceFamilyAtLevel_mono`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:170–176`.)*

*Proof.* (1) Let $\phi$ be the map. For $g\in\iota\to\mathbb Z/n$, write $g=\prod_qe_q^{g_q}$ with $g_q\in\{0,\dots,n-1\}$ the representative `(toAdd g q).val`; this is checked coordinatewise after `toAdd`, where it becomes $\sum_q g_q\cdot\mathrm{Pi.single}\,q\,1=g$ (`:19–24`). Then $\phi\bigl(\prod_q(X_q+1)^{g_q}\bigr)=\prod_q[e_q]^{g_q}=[g]$ (`:18,25–27`). So every basis element $[g]$ is in the image. The image is a subalgebra, and `MonoidAlgebra.induction_on` reduces to the cases $[g]$, sums, and scalar multiples (`:28–33`). For `toLam`, $n=\ell^M\ne0$ because $\ell$ is prime (`:37`).

(2) Each place $v$ over $P_q$ satisfies six conditions, of which the fifth is $v\notin A$; drop it (`:43–45`).

(3) `steps_mono` replaces $H$ by a larger $H'$ in clause (S1); `isAuxiliaryPlaceFamilyAtLevel_mono` replaces $A$ by a subset $A'$ in the fifth condition. $\square$

The kernel of the map in (1) is generated by $((1+X_q)^n-1)$ for all coordinates $q$. Reduce by these monic polynomials one variable at a time. The remaining monomials have exponents between $0$ and $n-1$ in each coordinate. Their images $\prod_q([e_q]-1)^{a_q}$ give a basis, since binomial expansion is triangular with diagonal $1$ in the group basis $\prod_q[e_q]^{a_q}$. This proves the kernel assertion. The toric ideal $\mathfrak I_M$ of §10.4.7.2 is the kernel after also setting the right group generators equal to $1$. For example, when $R=1$ and $n>1$, $X_R$ lies in $\mathfrak I_M$ and maps to the nonzero element $[e_R]-1$ in the full group ring. In one variable the generator difference agrees with the familiar coordinate on the completed Iwasawa algebra. [Expository] [Sharifi, *Iwasawa Theory*, PDF pp. 6, 78](../sources/SOURCES.md#6-literature).

##### Theorem 10.13ae (one family of auxiliary places supplies the Selmer polynomials and the Frobenius steps) [Lean, read]

*Assume `ThmS bkP`, `SelmerLengthsByDeterminant bkP`, `ResidualBoundOddPrimes bkP` and `ThmC bkP`. Then `GaloisSideTwistedSelmerAuxiliaryPrimes bkP` holds. Explicitly: let $i$ be a twist index and $T\subseteq$ `Sig i` a set of signatures satisfying `GalHyp`. Then there are $R,D_d,M_0$ with $M_0\ge1$ such that for every $M\ge M_0$, every admissible family $(H,S,d)$ at level $M$, every tame inertia element $z$ at a twist prime, every open normal subgroup $H'\le G$ and every finite set $A$ of places, there is a family $P:\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,R\to$ places such that*

- *(a) `SlopeTestRemainingChoices` $(M,A,P,d\circ P)$: the places over each $P_q$ are split, of degree one, of absolute ramification index one at the underlying rational prime, outside $S_0\cup A$, of norm $\equiv1\pmod{2\ell^M}$, pairwise non-conjugate across indices, and $d_{P_q}$ is a good character at $P_q$;*
- *(b) `Steps` $(M,H',z,P,d\circ P)$: every Frobenius at a left place is conjugate into $zH'$, and every Frobenius $\sigma$ at the right place $P_{\mathrm{inr}\,a}$ has $d_{P_{\mathrm{inl}\,b}}(\sigma)=\delta_{ab}$;*
- *(c) for every $s\in T$ and every $Q$ with `IsQ P Q` there is $F_s\in O_0[X_q]$ with `SelPoly` $(s,M,d\circ P,Q,F_s)$ and a monomial $m$ with $\deg m\le D_d$ and $v_{O_0}\bigl((F_s)_m\bigr)\le v_{O_0}(\ell^{\nu})$.*

*The data $(R,D_d,M_0)$ depend on $(i,T)$ only; the family $P$ depends on $(M,H,S,d,z,H',A)$ but not on $s$; the polynomial $F_s$ depends on $s$ and $Q$.*
*(Lean: `GlobalTheory.TwSys.galois_twisted_selmer_auxprimes_of_matrix_and_bounds`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisTwistedSelmerAuxprimesOfMatrixAndBounds.lean:47–63`.)*

*Proof.* Fix $i$, $T$ and the hypothesis $h_T$ that every $s\in T$ satisfies `GalHyp` (`:50`).

**Step 0 (one order bound for zero and positive $\nu$).** We claim `OrdBound bkP i μ` with $\mu=v_{O_0}(\ell^{\nu})$. If $\nu=0$, then $\ell^{\nu}=1$ and $v_{O_0}(1)=0$ (`IsDiscreteValuationRing.addVal_one`), so the claim is `ResidualBoundOddPrimes` at $i$ (`:52–54`). If $\nu>0$, the claim is `ThmC` at $i$ (`:55`). In both cases the hypothesis is applied with the same $\mu$, so the rest of the proof does not see the case split (`:51`).

**Step 1 (the family and the level).** Apply the order bound to $T$ and $h_T$: it returns $R$, $D_d$, $M_0$ and the clause $h_{M_0}$ (`:56`). Return $R$, $D_d$ and $\max(M_0,1)$; the first conjunct $1\le\max(M_0,1)$ is immediate (`:57`). Let $M\ge\max(M_0,1)$, $(H,S,d)$, $z$, $H'$ and $A$ be given. Then $M\ge1$ (`:58`) and $M\ge M_0$, so $h_{M_0}$ gives $P$ with (a), (b), and the clause $h_P$: for all $s\in T$, $Q$ with `IsQ`, $a$, $\Phi$ with `Computes`, and $F$ with $\mathrm{toLam}\,F=\det\Phi$, some $m$ of degree $\le D_d$ has $v_{O_0}(F_m)\le\mu$ (`:59`). Return this $P$; (a) and (b) are $h_P$'s first two components (`:60`).

**Step 2 (the matrix).** Let $s\in T$ and $Q$ with `IsQ P Q`. Apply `ThmS` at $s$ (with `GalHyp` from $h_T$), $M$, $\iota=\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,R$, $P$, $d\circ P$, $Q$, using $1\le M$ and Lemma 10.13ad(2) to pass from (a) with $A$ to the hypothesis with $\varnothing$. It returns $a$, $\Phi\in M_a(\Lambda)$ and `Computes bkP i s M (d∘P) Q Φ`; the non-unit clause is discarded (`:61`).

**Step 3 (the lift).** By Lemma 10.13ad(1), choose $F\in O_0[X_q]$ with $\mathrm{toLam}\,F=\det\Phi$ (`:62`).

**Step 4 (the two conclusions for $F$).** `SelmerLengthsByDeterminant` at the same $(s,M,P,d\circ P,Q)$, with $1\le M$, (a) weakened to $\varnothing$, `IsQ`, `Computes` and $\mathrm{toLam}\,F=\det\Phi$, gives `SelPoly` $F$. The clause $h_P$ at the same data gives the coefficient bound $v_{O_0}(F_m)\le\mu=v_{O_0}(\ell^{\nu})$ (`:63`). $\square$

Three remarks on what was and was not used. The non-unit clause of `ThmS` is not consumed here; it is used by the order-bound producers themselves. The coefficient bound in `OrdBound` is quantified over *every* lift $F$ of $\det\Phi$, which is why Step 3 may choose any preimage. And the family $P$ is produced before $s$ is chosen, so the same $P$ serves all signatures in $T$; this is the "one family" of the title.

##### Proposition 10.13af (one grid for the Selmer, theta and lattice polynomials; the `partAT` step) [Lean, read]

*In `admissibleIndexBoundAllPowers_of_conditions`, the hypothesis `GaloisSideTwistedSelmerAuxiliaryPrimes` is applied with $T=\{s:\texttt{goodS}\,s\}$. For every $M\ge M_0$ the resulting family $P_M$ and its characters $d_M\circ P_M$ are used for all of the following at once:*

1. *`Steps` at $H'=\bigcap_\lambda H_E(\lambda)\cap\bigcap_yH_B(y)$ and avoidance of $A_0\cup\bigcup_yA_B(y)$, weakened by Lemma 10.13ad(3) to the subgroup and avoided set of each theta and lattice theorem;*
2. *the Selmer polynomials $F_{M,s}$ of Theorem 10.13ae(c), for every good $s$, at the set $Q_M$ of places over $P_M$, which has $\lvert Q_M\rvert\le4R$;*
3. *the theta polynomials $f_{E,M}(\lambda)$ of Theorem 10.13y and the lattice polynomials $f_{B,M}(y)$ of Theorem 10.13p.*

*All three families of polynomials live in the variables $X_q$, $q\in\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,R$, and are passed to one call of `exists_level` with $I=\{s:\texttt{goodS}\,s\}$, $J=$ `abelian₂ i` $\sqcup\{\text{blocks}\}$, $\mu=\nu\cdot v_{O_0}(\ell)$, baselines $v=\mathrm{Sum.elim}\,v_E\,v_B$ and $n_{\max}=2+\sum_yn_y$. The call returns $M\ge M_0$, $k\le M$, exponents $e_q<k$ with $\ell^{e_q}/\varphi(\ell^k)\le\varepsilon$, and, for every primitive $\ell^k$-th root $\zeta$ and $u_q=\zeta^{\ell^{e_q}}$:*
$$F_{M,s}(u-1)\ne0,\quad \operatorname{nval}\bigl(F_{M,s}(u-1)\bigr)\le\nu+\varepsilon\quad(s\text{ good});\qquad f(u-1)\ne0,\quad\operatorname{nval}\bigl(f(u-1)\bigr)\le\frac{v_f}{v_O(\ell)}+\varepsilon\quad(f=f_E(\lambda),f_B(y)).$$
*The witness is $(Q_M,k,\psi'=(\chi_0\circ\varphi)^a)$ with $\chi_0(x)=\prod_q(\zeta_k^{\ell^{e_q}})^{x_{P_q}}$. For every $a$ coprime to $\ell$, `partAT` holds with $\varepsilon_T\equiv\varepsilon=\varepsilon'/C$, where $C=\lvert\mathrm{SigG}\rvert+2m+4Rt+1$.*
*(Lean: `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:96–144,152–197`; `exists_isQ`, `IsAuxiliaryPlaceFamilyAtLevelMono.lean:52–75`; `valE_eq`, `:147–155`; `addVal_l_pow`, `:138–141`; `nval_nonneg`, `:143–145`.)*

*Proof.* **Inputs.** The signature hypotheses `SetHyp` and the admissibility package `AdmACD` are unpacked (`:98–99`); the tame inertia element $z$ is obtained (`:100`, `[Lean]`). The hypothesis `hX` is applied to $T=\{s\mid\texttt{goodS}\,s\}$, with `GalHyp` assembled from `adm1`, `adm2`, self-duality, no-jump, `adm3` and $100\le r$ (`:101–102`); it returns $R$, $D_d$, $M_0$, $1\le M_0$ and the clause $h_R$. The theta data $(H_E,v_E)$ and the lattice data $(H_B,A_B,v_B,n_B)$ are chosen for each $\lambda$ and each block $y$ (`:103–105`); the intersection $H'$ is open and normal (`:106–112`).

**One family per level.** For each $M\ge M_0$: `DelUTie` gives an admissible family $(H_0,S_0,d_M)$ coordinated with `delU` (`:113`); $h_R$ at $(M,H_0,S_0,d_M,z,H',A_0\cup\bigcup_yA_B(y))$ gives $P_M$ with (a) $h_{Pa}$, (b) $h_{Ps}$ and (c) $h_{PF}$ (`:114–115`); `exists_isQ` gives $Q_M$ with `IsQ` and $\lvert Q_M\rvert\le2\cdot\lvert\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,R\rvert=4R$ (`:116`). Then:

- *Selmer.* For each good $s$, $h_{PF}$ at $(s,Q_M)$ gives $F_{M,s}$ with `SelPoly` ($h_{Fs}$) and the coefficient bound ($h_{Fc}$) (`:117`).
- *Theta.* Theorem 10.13y at $(M,R,P_M,d_M\circ P_M,Q_M)$ needs `SlopeTestRemainingChoices` with $\varnothing$ and `Steps` at $H_E(\lambda)$; both follow from (a), (b) by Lemma 10.13ad(3), since $\varnothing\subseteq A$ and $H'\le H_E(\lambda)$ (`:118–119`).
- *Lattice.* Theorem 10.13p at the same data needs avoidance of $A_B(y)$ and `Steps` at $H_B(y)$; both follow in the same way (`:120–122`).

**One call of `exists_level`.** The constant $C$ and $\varepsilon=\varepsilon'/C$ are fixed (`:123–131`). The call (`:133–144`) takes $F=(M,h)\mapsto(s\mapsto F_{M,s})$ and $f=(M,h)\mapsto\mathrm{Sum.elim}\,f_{E,M}\,f_{B,M}$. Its hypothesis `hF` is the coefficient bound: $h_{Fc}$ gives $v_{O_0}(F_m)\le v_{O_0}(\ell^{\nu})$, and `addVal_l_pow` rewrites the right side as $\nu\cdot v_{O_0}(\ell)=\mu$ (`:137–139`). Its hypothesis `hf` is `OrdHyp` for each $f$, weakened to $n_{\max}$ by `ordHyp_mono` (`:140–144`). The output is $(M,k,e)$ and the evaluation clause $H_{ev}$, uniform in the primitive root $\zeta$.

**The character.** With $\zeta_k=$ `X.zk i k`, the product character $\chi_0$ on $\Delta_{Q_M,M}$ sends $x$ to $\prod_q(\zeta_k^{\ell^{e_q}})^{x_{P_q}}$ (`:153–157`); `exists_factor` factors `delU` through $\mathrm{RCG}(Q_M)$ by a map $\varphi$ (`:158–160`). The witness is $(Q_M,k,\chi_0\circ\varphi)$ (`:161`). For coprime $a$, $\zeta=\zeta_k^a$ is again primitive (`:162`), and $\psi'=(\chi_0\circ\varphi)^a$ satisfies $\psi'(\mathrm{art}\,g)=\prod_q(\zeta^{\ell^{e_q}})^{d_M(P_q)(g)}$ by the coordination `IsCoord` (`:164–185`). This is the hypothesis of `SelPoly` for the character $\mathrm{psiAt}(\mathrm{side}\,s)(\psi'\circ\mathrm{art})$, after `psiAt_prod` replaces $\zeta$ by $\zeta$ or $\zeta^{-1}$ according to the side (`:193`, `IsAuxiliaryPlaceFamilyAtLevelMono.lean:295–299`); the root $\zeta^{\pm1}$ is primitive by `side_root`.

**The `partAT` step** (`:188–197`). Take $\varepsilon_T(s)=\varepsilon$ for all $s$ (`:188`). Nonnegativity is $\varepsilon\ge0$. The sum over `SigG` is $\lvert\mathrm{SigG}\rvert\cdot\varepsilon\le C\varepsilon=\varepsilon'$ because $\lvert\mathrm{SigG}\rvert\le C$ (`:190–191`). For a good $s$: `SelPoly` ($h_{Fs}$) at $k$, $u_q=(\zeta^{\pm1})^{\ell^{e_q}}$ (with $u_q^{\ell^M}=1$ because $k\le M$, `:146–151`) and the character above rewrites $\operatorname{sLen}$ as $\mathrm{valE}(F_{M,s}(u-1))$ (`:193`). The evaluation clause $H_{ev}$ at $\zeta^{\pm1}$ gives $F_{M,s}(u-1)\ne0$ and $\operatorname{nval}(F_{M,s}(u-1))\le\mu/v_{O_0}(\ell)+\varepsilon$ (`:192`). Since the value is nonzero, `valE_eq` turns $\mathrm{valE}$ into $\mathrm{ofReal}(\operatorname{nval})$ (`:194`), and $\mu/v_{O_0}(\ell)=\nu\cdot v_{O_0}(\ell)/v_{O_0}(\ell)=\nu$ because $v_{O_0}(\ell)>0$ (`e_pos`, `:132,197`). Hence $\operatorname{sLen}\le\mathrm{ofReal}(\nu+\varepsilon)$ (`:195–196`), which is `partAT`.

The `partC` step (`:198–208`) was read in §10.4.7.3 and the `partAB` step (`:216–222`) in §10.4.7.1; `PsiOk` and `partD` come from `psiOk_partD_root` at the same $P_M$, $Q_M$ and $\zeta$ (`:186–187`), with the tame sum bounded by $\lvert Q_M\rvert\varepsilon\le4R\varepsilon$ (`:209–215`). $\square$

##### Return to `GoodTw` [Lean, read]

The all-powers transport `twistModule_all_character_powers_of_admissible` obtains $(Q,k,\psi_0,\texttt{hall})$ from `admissibleIndexBoundAllPowers` and, for each coprime $a$, unpacks `hall a` as $\langle\texttt{hok},\texttt{ha},\texttt{hc},\texttt{hd},M,\chi,\ldots\rangle$. The component `ha` is `partAT` for $\psi_0^a$; it is passed unchanged into `GoodTw` as its fourth conjunct, next to `partC` (`hc`, fifth) and `partD` (`hd`, sixth) (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:24–28,53`). The main-path call that produces the hypothesis of Theorem 10.13ae is `twistTheorem_allPowers_of_selmer_supLattice`, which passes `ThmS`, the closed theorem `twisted_selmer_lengths_eq_determinant_valuation`, `ResidualBoundOddPrimes` and `ThmC` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:31–33`); one level up, the three hypotheses other than the closed theorem are supplied by `selmerPresentationMatrix_of_galois_cohomology`, `residualSelmerBound_of_auxiliaryPrimes_odd` and `boundModTwoUniformizerAtTwo_of_chebotarev` from the literature-layer propositions (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistAllPowersOfGaloisCohomologyClassField.lean:24–27`). Their proof bodies are read in §§10.4.8–10.4.13 at the indicated boundaries; here they are inputs.

The closed theorem `twisted_selmer_lengths_eq_determinant_valuation` has no hypotheses beyond the data. Its proof (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedSelmerLengthsEqDeterminantValuation.lean:375–385`) makes $K/O_k$ (`KmodO`) a $\Lambda$-module through the character $u$ (`lamChar`), checks that $\psi$ is trivial on decomposition groups above $\ell$ because each $d_q$ is, and rewrites $\operatorname{sLen}$ by `length_selT` as the valuation of $\det\Phi$ acting on $K/O_k$, which is $F(u-1)$ by `lamChar_toLam`. We read the statement and this final assembly only; the supporting lemmas of that file (lines 1–374) remain `[Lean]`.

##### Remarks, source map, and reading boundary

*Remark 1 (two non-divisibilities) [Expository].* The clause `partAT` is an upper bound on Selmer lengths. Its source is the coefficient bound of Theorem 10.13ae(c): some coefficient of $F_s$ of degree at most $D_d$ has $v_{O_0}$ at most $v_{O_0}(\ell^\nu)$. This implies indivisibility by $\ell^{\nu+1}$. The latter alone gives only $v_{O_0}<(\nu+1)v_{O_0}(\ell)$, which can be a weaker bound when $O_0$ is ramified. The lemma `exists_level` turns a low-degree coefficient of controlled valuation into a bound $\nu+\varepsilon$ on $\operatorname{nval}(F_s(u-1))$ at a suitable grid point; §10.4.7.2 reads how. The clause `partC` is a two-sided window on theta evaluations. Its source is the exact valuation of a constant term, Theorem 10.13y(b), which is a unit times $\sum y_\delta$; §10.4.7.3 reads how. The two statements are about different polynomials, proved by different theorems, and neither implies the other. What they share is the family $P$, the characters $d\circ P$, the variables $X_q$ and the grid point $u$; this sharing is the content of Theorem 10.13ae and Proposition 10.13af.

*Remark 2 (where the coefficient bound comes from) [Lean].* The producers of `OrdBound` in the two cases $\nu=0$ and $\nu>0$ are `residual_bound_of_components` (via `residualSelmerBound_of_auxiliaryPrimes_odd`) and `thmC_of_parts` (via `boundModTwoUniformizerAtTwo_of_chebotarev`). [§10.4.7.5](#10475-odd-prime-and-mod-two-production-of-the-selmer-coefficient-bound) reads the two production wrappers and their common `OrdBound` assembly, and [§10.4.7.6](#10476-producing-the-initial-adjugate-seed-scalar-descent-unused-left-places-and-the-ramified-ideal-threshold) reads the production proof of the initial positive-order seed `StartInd.start_of_resBound` together with its `TameScalar` and `Small2` suppliers; the first-order tame relation and `ResBound` are read in §10.4.8, the positive-order `Step`/`Grow` recurrence in §10.4.9, the global Selmer presentation in §10.4.12, and the two-batch choice of auxiliary places in §10.4.13. The present subsection reads how their common output is consumed.

*Remark 3 (Mathlib inputs).* `MonoidAlgebra.induction_on` (`Mathlib/Algebra/MonoidAlgebra/Defs.lean`, approx. lines 732–738 at the pinned commit `0df444a3`; hypotheses named `of`, `add`, `smul`) is the induction behind Lemma 10.13ad(1); `IsDiscreteValuationRing.addVal_one` is the $\nu=0$ branch of Theorem 10.13ae, Step 0.

*Remark 4 (scope of verification).* We read these declarations line by line against the pinned archive `lean.tar.gz` (SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, rechecked 2026-11-25) and built the book with `mdbook build`. Neither source reading nor book compilation is a Lean kernel verification. The examples are certified by exact arithmetic in our script, not by Lean; they model the algebra and are not instances of `NTw`.

| Item | Pinned archive source | Level here |
|---|---|---|
| `galois_twisted_selmer_auxprimes_of_matrix_and_bounds`; `aeval_gen_sub_one_surjective`, `toLam_surjective`, `SlopeTestRemainingChoices.empty` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisTwistedSelmerAuxprimesOfMatrixAndBounds.lean:11–63` | [Lean, read] |
| The `hX` application, the per-level choices ($d_M$, $P_M$, $Q_M$, $F_{M,s}$, $f_{E,M}$, $f_{B,M}$), the `exists_level` call, the character and the `partAT` step of `admissibleIndexBoundAllPowers_of_conditions` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:96–144,146–197` | [Lean, read] |
| `exists_isQ`, `conjCl_of_isQ`, `addVal_l_pow`, `nval_nonneg`, `valE_eq`, `nval_l_pow`, `ordHyp_mono`, `isAuxiliaryPlaceFamilyAtLevel_mono`, `steps_mono`, `exists_factor`, `psiAt_prod`; statement of `exists_level` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:52–82,138–176,283–299,321–337` | [Lean, read] |
| `twisted_selmer_lengths_eq_determinant_valuation` (statement and final assembly) | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedSelmerLengthsEqDeterminantValuation.lean:375–385` | [Lean, read] (assembly); `[Lean]` for `length_selT`, `lamChar`, `lamChar_toLam` and lines 1–374 |
| Main-path call sites | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:31–33`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistAllPowersOfGaloisCohomologyClassField.lean:24–27`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:24–28,53` | [Lean, read] |
| Definitions `ThmS`, `SelmerLengthsByDeterminant`, `OrdBound`, `ResidualBoundOddPrimes`, `ThmC`, `GaloisSideTwistedSelmerAuxiliaryPrimes`; `Del`, `abelian₂`, `delAll`, `toLam`, `delInv`, `Computes`, `valE`, `SelPoly`, `GalHyp`, `AdmFam`, `GoodChar`; `selT`, `lenN`, `sLen`, `nu`, `PsiOk`, `partAT`; `admissibleIndexBoundAllPowers`; `GoodTw` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:46–77`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTameInertiaElementAtTwistPrime.lean:21–30,46–59,86–120`; `src/Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean:90–94,184–195,247–248,289–297,304–308`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/AdmissibleIndexBoundAllPowers.lean:14–21`; `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:219–231` | [Lean, read] (definitions) |
| Producers of `ThmS`, `ResidualBoundOddPrimes`, `ThmC` (`selmerPresentationMatrix_of_galois_cohomology`, `residualSelmerBound_of_auxiliaryPrimes_odd`, `boundModTwoUniformizerAtTwo_of_chebotarev` and their bodies `oneMatrix_of_galoisCohomology`, `residual_bound_of_parts`, `bound_mod_two_of_hypothesis`); `exists_tameInertiaElementAtAuxiliaryPrime`; `DelUTie`, `PropABCD`, `AdmACD` as hypotheses | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerPresentationMatrixOfGaloisCohomology.lean:20–35`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21–31`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BoundModTwoUniformizerAtTwoOfChebotarev.lean:25–35`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTameInertiaElementAtAuxiliaryPrime.lean:85`; `AdmissibleIndexBoundAllPowersOfConditions.lean:92–93` | [Lean] (retained boundary; parts read in §§10.4.8–10.4.13) |
| `propE`, `exists_level`, `propABCD_of_rel`, `export_at`, the `partC` and `partAB` steps | §§10.4.7.1–10.4.7.3 | [Lean, read] (inherited, cited only) |

#### 10.4.7.5 Odd-prime and mod-two production of the Selmer coefficient bound

##### Motivation [Expository]

A square Selmer presentation at one signature gives a determinant. To specialize all signatures on a common grid, Theorem 10.13ae needs a stronger assertion: choose the place family $P$ first, and obtain a low-degree coefficient of valuation at most $v_{O_0}(\ell^\nu)$ from *every* polynomial lifting the determinant of *every* compatible presentation. The zero-order route ($\nu=0$) achieves this in one batch using the corank-zero half of `ResBound` (Proposition 10.15 in §10.4.8) together with the two-batch Frobenius selector `ChosenPrimes.stepAB` (§10.4.13). The positive-order route ($\nu>0$) pre-allocates $t=\lvert T\rvert$ extra left places, extracts an initial adjugate unit seed `NFit` at corank one via `Start` (whose production proof is read in §10.4.7.6), and runs the simultaneous `Step`/`Grow` recurrence of Proposition 10.18 (§10.4.9, illustrated in Example 10.16) to turn that seed into determinant tests outside the ramified ideal $I=(\ell^\nu)\mathfrak m_{O_0}$.

##### Two finite-level models [Expository]

In both models use two coordinates $L,R$, the group $(\mathbb Z/\ell^M)^2$, and put $X_q=u_q-1$ at evaluation. Each model has one signature and a $1\times1$ presentation over the group ring given by the image of the displayed polynomial $F$. A second polynomial $B$ illustrates the use of the same grid for a separate constant-term test. These are algebraic models (`GalHyp` requires $r\ge100$); interpreting their determinant valuations as Selmer lengths requires the length identity of §10.4.7.4.

**Zero order.** Over $\mathbb Z_3$ take $\nu=0$, $M=3$, $F=3+X_L$, $B=1+X_R$. In the residue group ring both $X_L^{27}$ and $X_R^{27}$ vanish, so the degree-one coefficient $1$ survives for every lift. With $\zeta$ primitive of order $27$, put $(u_L,u_R)=(\zeta,\zeta^3)$. The polynomial $\Phi_{27}(1+T)$ is Eisenstein at $3$ of degree $18$, and $\zeta^3$ has order $9$, whose corresponding polynomial is Eisenstein of degree $6$. For $v(3)=1$ this gives
$$
v\bigl(F(u-1)\bigr)=\min(1,1/18)=1/18,\qquad v\bigl(B(u-1)\bigr)=v(\zeta^3)=0.
$$
The minimum is strict in the sum for $F$. Swapping the grid coordinates gives $v(F)=1/6$, while $B$ remains a unit. For $\varepsilon=1/10$, the first grid meets $v(F)\le\nu+\varepsilon$ and the swapped grid exceeds it. A degree cut of zero would also fail for the original lift, whose constant coefficient is $3$.

**Positive order over a ramified base.** Take $O_0=\mathbb Z_2[\pi]$, $\pi^2=2$, $\nu=1$, and $M=3$. Normalize $v_\pi(\pi)=1$. Following the notation of §10.4.9, the production test is exclusion from $I=(2)\mathfrak m_{O_0}=(\pi^3)$, or $v_\pi(c)\le2$. Set $F=4+2X_L+X_L X_R$ and $B=2(1+X_R)$. The coefficient at $X_LX_R$ is a unit for every lift: modulo $\pi$ the kernel is generated by the eighth powers, so no coefficient in degree two changes. With $v_2=v_\pi/2$ on the base and its extension to the field of evaluation, take $\zeta$ primitive of order $8$ and $(u_L,u_R)=(\zeta,\zeta^2)$. Eisenstein at $2$ gives $v_2(\zeta-1)=1/4$ and $v_2(\zeta^2-1)=1/2$. The three summands of $F(u-1)$ have valuations $2,5/4,3/4$. Thus $v_2(F(u-1))=3/4$ and $v_2(B(u-1))=1$. With the order-two grid $(u_L,u_R)=(-1,-1)$, the same $F$ evaluates to $4-4+4=4$, of valuation $2$, and $B$ has valuation $1$. The Selmer estimate at tolerance $1/4$ therefore depends on the grid.

Dropping the ideal test $c\notin I$ also loses the guarantee even if every lift has a coefficient indivisible by $2^{\nu+1}$. Replace $F$ by the constant $\pi^3$, whose constant term is unchanged by any lift since the group-ring kernel vanishes at the origin. Then $\pi^3\notin(4)=(\pi^4)$, yet $\pi^3\in I=(\pi^3)$. On every grid it has normalized valuation $3/2>1+1/4$.

##### Definitions [Lean, read]

Fix the archive data $D,N,X,\mathrm{bkP}$, a twist index $i$, and abbreviate $r=D.R.r$, $\ell=X.l(i)$, $\nu=\mathrm{nu}(X,i)$ and $O_0=X.O0(i)$. Write $v_0$ for the additive DVR valuation on $O_0$, extended by $v_0(0)=\infty$. Consistently with §10.4.9, put $e=v_0(\ell^\nu)$, $I=\mathrm{idl}(i)=(\ell^\nu)\mathfrak m_{O_0}$, and $J=\ell^{M-\nu-1}$. The integer $e$ is finite (`e_lt_top`, `AddValLeOfNotMem.lean:16–26`) because $\ell\ne0$ in $O_0$ via its characteristic-zero field embedding (`SmallSub.l_ne_zero`). If $\varpi$ is a uniformizer of $O_0$, then $I=(\varpi^{e+1})$, so $c\notin I$ is equivalent to $v_0(c)\le e$ (`addVal_le_of_notMem`, `:73–85`, inherited from Proposition 10.18).

The predicates `NF`, `NFit`, `PiLocalization₂`, and `Ext` (`Small2.lean:20–39`) are those of §10.4.9 (and are written out with all quantifiers in §10.4.7.6 below): `NF` $(P,c)$ asserts a determinant-lift coefficient outside $I$ of degree $<c$, while `NFit` $(P,c)$ asserts either matrix size $a=0$ or an adjugate entry whose lifts all have a unit coefficient of degree $<c$ supported away from unused left slots $\mathrm{inl}\,j$ ($j\ge n$). Both predicates are monotone in $c$.

##### Theorem 10.13ag (a common order bound from the two production routes) [Lean, read]

*Assume the archived propositions `GreenbergWiles`, `Cheb`, `PoitouTateTotallyComplex`, `CohDimTwo`, `TameLocal`, `LocalFiniteness`, `LocalTateDuality`, `LocalEulerChar`, `GlobalFiniteness`, `GlobalEulerChar`, `UnramifiedOrthogonality` and `Gen.ArchimedeanSignatureMatching` (only the odd-prime wrapper takes `GreenbergWiles` as an argument). Fix $i$ and any set $T\subseteq\mathrm{Sig}(i)$ with `GalHyp` at every $s\in T$.*

*Then `OrdBound bkP i e` holds with $e=v_0(\ell^\nu)$ and $M_0\ge1$: there are natural numbers $R,D_d,M_0$ ($M_0\ge1$) serving all of $T$ such that for every $M\ge M_0$, every admissible $(H,S,d)$ at level $M$, every tame inertia element $z$ at a twist prime, every open normal $H'\le G$ and every finite forbidden set $A$, there is a single place family $P:I_R\to\mathrm{Pl}_E$, $I_R=\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,R$, satisfying `SlopeTestRemainingChoices` $(M,A,P,d\circ P)$ and `Steps` $(M,H',z,P,d\circ P)$ such that for every $s\in T$, every $Q$ with `IsQ P Q`, every $a$, every $\Phi\in M_a(O_0[(\mathbb Z/\ell^M)^{I_R}])$ satisfying `Computes`, and every $F\in O_0[X_q:q\in I_R]$ with $\mathrm{toLam}\,F=\det\Phi$, some multi-index $m$ satisfies*
$$
\lvert m\rvert\le D_d,\qquad v_0\bigl([X^m]F\bigr)\le v_0(\ell^\nu).
$$
*The index $m$ may depend on $F$; the family $P$ is chosen before $(s,Q,\Phi,F)$.*
*(Lean: `residualSelmerBound_of_auxiliaryPrimes_odd`, `ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21–31`; `OddBound.residual_bound_of_parts`, `ResidualBoundOfComponents.lean:14–57`; `boundModTwoUniformizerAtTwo_of_chebotarev`, `BoundModTwoUniformizerAtTwoOfChebotarev.lean:25–35`; `TwoBound.thmC_of_parts`, `AddValLeOfNotMem.lean:87–144`.)*

*Proof.* **Residual inputs ($\nu=0$).** The outer body `GlobalTheory.ResSel.residual_bound_of_parts` (`ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21–31`) obtains `EqDim` at every good signature from `residual_selmer_finrank_eq_dual`, feeds it with `cocycleFormsSpan_oddResidueChar` and `span_two_of_galois_hypothesis` into `exists_elements_selmerForms_small_corank` to obtain `ChooseH`, and gets `StepAB` from `exists_auxiliary_primes_prescribed_frobenius` (`ChosenPrimes.stepAB`, §10.4.13). First-half local vanishing feeds `reciprocity_auxiliaryPlaces_secondHalf`, and together with `EqDim` they feed `residual_selmer_determinant_order_bound` (`ResOrder.resBound`, Proposition 10.15 in §10.4.8) to produce `ResBound`. The wrapper's `GreenbergWiles` argument is unused in this body.

**Zero-order assembly (`OddBound.residual_bound_of_parts`, `ResidualBoundOfComponents.lean:28–57`).** `ChooseH` for $T$ fixes $R$. Take $D_d=4rR$ and $M_0=4rR+2\ge1$; since $\ell\ge2$, $4rR+2<\ell^M$ for $M\ge M_0$. Choose an open normal $L\le H$, small for every $s\in T$ and fixing roots of order dividing $2\ell^M$ (`exists_openNormalSubgroup_under_inertia`). `ChooseH` gives targets $h_a\in L$ and an open normal $U\le L$ witnessing `Corank` $0$ for right Frobenii conjugate to $h_a$ modulo $U$. Apply `StepAB` (§10.4.13) at $U\cap H'$ and forbidden set $A$ to obtain $P$; monotonicity weakens `Steps` to both $H'$ and $L$. For the chosen right Frobenius $\phi_a$, $g_a\phi_a g_a^{-1}h_a^{-1}\in U\cap H'\le L$ and normality of $L$ put $\phi_a\in L$, while right inertia lies in $U\cap H'\le L$. Because inertia and the powers of Frobenius generate a dense subgroup of $\mathrm{Dec}$ modulo inertia and $L$ is open (hence closed), $\mathrm{Dec}\le L$ (`dec_le_of_frob_mem`, `:14–26`). Smallness of $L$ gives residual triviality on these decomposition groups across $T$, supplying `Position`, while `ChooseH` supplies `Corank` $0$. The first clause of `ResBound` (Proposition 10.15) then yields a unit coefficient of degree $\le 4rR$, so $v_0([X^m]F)=0=e$.

**Positive-order inputs ($\nu>0$).** The outer body `bound_mod_two_of_hypothesis` (`BoundModTwoUniformizerAtTwoOfChebotarev.lean:25–35`) obtains $h_S=$ `oneMatrix_of_galoisCohomology` (§10.4.12) and the same `EqDim`, span, `ChooseH`, `StepAB`, and `ResBound` supplies. For each good signature, `StartInd.start_of_resBound` receives `ScalarFrob.firstPlace` and `ResBound` to produce `Start` (the `firstPlace` argument is discarded inside `start_of_resBound`; §10.4.7.6 reads the complete proof). Meanwhile `Growth.grow` and `NewPrime.step` receive $h_S$ to supply `Grow` and `Step` (§§10.4.9–10.4.11); this upstream use of $h_S$ leaves `OrdBound`'s universal quantification over all `Computes` matrices intact.

**Initial family and simultaneous recurrence (`TwoBound.thmC_of_parts`, `AddValLeOfNotMem.lean:87–144`).** Enumerate $T$ by $f:\mathrm{Fin}\,t\to\mathrm{Sig}(i)$ with range $T$, let `ChooseH` supply $R_0$, and set $w_0=4rR_0$, $w_{j+1}=2(e+1)w_j+2+2r$, $R=R_0+t$, $D_d=w_t$, and $M_0=w_t+\nu+3\ge1$ (`:87–108`). For $M\ge M_0$, $\ell\ge2$ and $w_0\le w_t$ give $4rR_0+2<\ell^M$, $\nu+2\le M$, and $w_t\le J=\ell^{M-\nu-1}$. Choose $L\le H$ via `SmallSub.exists_small` (read in Lemma 10.13ak(2) below) fixing $(2\ell^M)$-th roots of unity and satisfying `Small2` (entrywise in $I$) for all $s\in T$ (`:110–112`). Choose $(U,h)$ via `ChooseH`, append $t$ identity targets on the right, apply `StepAB` at $U\cap H'$, and restrict the right half to $\mathrm{Fin}\,R_0$ while keeping all $R_0+t$ left places (`:113–122`). By `dec_le_of_frob_mem` and restriction of the auxiliary-place and Kronecker conditions, this starting family $P_0:\mathrm{Fin}(R_0+t)\sqcup\mathrm{Fin}\,R_0\to\mathrm{Pl}_E$ satisfies `PiLocalization₂`, and the retained right Frobenii satisfy `Corank` $1$ (`:123–135`). Applying `Start` to each $f(j)$ gives $\mathrm{NFit}_{f(j)}(P_0,w_0+1)$ (`:136–137`). Proposition 10.18 (§10.4.9, `AddValLeOfNotMem.lean:28–85`) now runs $t$ steps of `Step` and `Grow` from $P_0$ to a balanced family $P_t:I_R\to\mathrm{Pl}_E$ satisfying `PiLocalization₂` (hence `SlopeTestRemainingChoices` at $A$ and right Kronecker equations, while the unchanged left places retain their initial `Steps` congruences modulo $U\cap H'\le H'$, `:138–142`) and $\mathrm{NF}_{f(j)}(P_t,w_t+1)$ for every $j$, hence a coefficient of degree $\le w_t=D_d$ outside $I=(\varpi^{e+1})$, i.e. $v_0([X^m]F)\le e$ (`:73–85, 143–144`). $\square$

##### Remarks and reading boundary

The two wrappers dispatch at Theorem 10.13ae, Step 0 according to $\nu=0$ versus $\nu>0$; for each eligible level $M\ge M_0$ their family $P$ serves all of $T$ prior to the analytic specialization `exists_level` (§10.4.7.2). Under `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/` in archive A2 (`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`), the declarations newly read for this subsection are `ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21–31`, `ResidualBoundOfComponents.lean:14–57` (including `dec_le_of_frob_mem`), `BoundModTwoUniformizerAtTwoOfChebotarev.lean:25–35`, and the finiteness and initial-family assembly `AddValLeOfNotMem.lean:14–26,87–144`, together with the definitions in `Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:56–68`, `IsDualDualRep.lean:118–146`, and `Small2.lean:13–57`. The recurrence, `Step`/`Grow` induction step, cutoff monotonicity, and valuation exit `AddValLeOfNotMem.lean:28–85` are **inherited** from Proposition 10.18 (§10.4.9, `[Lean, read]`), just as `ResOrder.resBound` is inherited from Proposition 10.15 (§10.4.8) and `ChosenPrimes.stepAB` from §10.4.13. In §10.4.7.6 we open `StartInd.start_of_resBound` and its `TameScalar` and `SmallSub` suppliers in full; `EqDim`, `SpanOdd`, `SpanTwo`, `ChooseH`, `FirstHalf` local vanishing, `Recip`, `Grow`, `Step`, and `ThmS` retain their established boundaries.

#### 10.4.7.6 Producing the initial adjugate seed: scalar descent, unused left places, and the ramified ideal threshold

##### Motivation [Expository]

In Theorem 10.13ag, the positive-order route ($\nu>0$) faces a structural mismatch at step $j=0$ that does not exist when $\nu=0$. Because each step of Proposition 10.18 (§10.4.9) appends one right-hand auxiliary place for one signature $f(j)$ while keeping the left-hand places fixed, `TwoBound.thmC_of_parts` pre-allocates $R=R_0+t$ left places alongside only $n=R_0$ initial right places ($n\le R$). At $j=0$, any presentation matrix $\Phi\in M_a(\Lambda_{R,n})$ satisfying `Computes` lives over the unbalanced group ring
$$
\Lambda_{R,n}=O_0\bigl[(\mathbb Z/\ell^M)^{\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n}\bigr],
$$
with relaxed Selmer set $Q$ covering all $R+n$ place orbits of $P_0$. Yet the first-order corank-one adjugate theorem `ResBound` (Proposition 10.15 in §10.4.8) only applies to balanced families indexed by $\iota'=\mathrm{Fin}\,n\sqcup\mathrm{Fin}\,n$, over $\Lambda_{n,n}=O_0[(\mathbb Z/\ell^M)^{\iota'}]$, with relaxed set $Q'\subseteq Q$ restricted to the retained $2n$ orbits.

Producing the initial seed `Start` (`StartInd.start_of_resBound`) therefore requires transporting `Computes` down the slot-restriction quotient $\pi=\mathrm{resLam}:\Lambda_{R,n}\twoheadrightarrow\Lambda_{n,n}$, applying `ResBound` to $\pi(\Phi)$, and lifting the resulting unit adjugate coefficient back to $\Lambda_{R,n}$ — all **on the exact same matrix $\Phi$** that `Step` and `Grow` will later reduce modulo the ramified DVR ideal $I=(\ell^\nu)\mathfrak m_{O_0}=(\varpi^{e+1})$. Four mechanisms make this compatible:

1. **Non-flat scalar descent via cocycle pullback.** Killing the unused left group-ring generators $[e_{\mathrm{inl}\,b}]-1$ ($n\le b<R$) is a quotient map $\pi:\Lambda_{R,n}\twoheadrightarrow\Lambda_{n,n}$, **not** a flat base change: $\operatorname{Tor}_1^{\Lambda_{R,n}}(\Lambda_{n,n},-)\ne0$, so naive tensoring of a free resolution does not commute with Galois cohomology. Instead, `StartInd` reverses the direction on test modules: given any discrete $\ell$-power torsion $\Lambda_{n,n}$-module $B$, it pulls scalars back along $\pi$ to view the *same* underlying abelian group $B$ as a $\Lambda_{R,n}$-module $B_\pi$. Because $\pi(\mathrm{delInv}\,d(g))=\mathrm{delInv}(d\circ e)(g)$, the two twisted Galois actions on $B^r$ are pointwise identical (`repOn_eq`). Continuous $1$-cocycles push forward along $\mathrm{id}_B$ (`z1Ch`, `h1Ch`) and pull back verbatim (`continuousCocycleChangeScalarsBack`), while **surjectivity** of $\pi$ both preserves the local Bloch–Kato span above $\ell$ (`chLoc_mem_bkOn`, since $\Lambda_{n,n}$-spans equal $\Lambda_{R,n}$-spans on $B_\pi$) and upgrades $\Lambda_{R,n}$-linearity of the kernel isomorphism $e_{B_\pi}$ to $\Lambda_{n,n}$-linearity (`exists_equiv_of_surjective`).
2. **Automatic unramifiedness at unused left places.** After scalar descent, `Computes` on $B_\pi$ still lands in $\mathrm{selOn}(d',B,Q)$, whereas `ResBound` requires $\mathrm{selOn}(d',B,Q')$. Every place $v\in Q\setminus Q'$ lies over an unused left place $P(\mathrm{inl}\,b)$ ($n\le b<R$), either directly or as its CM conjugate. Outside $S_0$ and the retained places $P(e(q'))$, the untwisted representation $T_s$ and the retained characters $d'=d\circ e$ act **identically trivially** on $\mathrm{Ine}(v)$, turning restricted cocycles into continuous homomorphisms $\mathrm{Ine}(v)\to B^r$ into $\ell$-power torsion. Meanwhile `PiLocalization₂` conjugates Frobenius at $P(\mathrm{inl}\,b)$ into $zL$. By `TameScalar`, $T_s(z)=d_z I_r$ with $d_z^2-1\in O_0^\times$ (so $\bar d_z\ne\pm1$), and conjugate self-duality (`SelfDual`) transports the residual Frobenius eigenvalue at the conjugate place to $\bar d_z^{-1}\ne1$ (`tbar_frob`). Raising the Frobenius action relation $U(\phi)m=N(v)m$ (supplied on the pro-$\ell$ tame inertia generator by `TameQuotient_holds`) to the $\ell^M$-th power kills the $\ell$-power character factor $\mathrm{delInv}\,d'(\phi)^{\ell^M}=1$ and leaves $Y=T_s(\phi)^{\ell^M}-N(v)^{\ell^M}I_r\in M_r(O_0)$, whose residue $(\bar d_z^{\pm\ell^M}-1)I_r$ is invertible over $k_{O_0}$ because $x\mapsto x^{\ell^M}$ is injective on differences in characteristic $\ell$. Thus $Y\in\mathrm{GL}_r(O_0)$ forces $m=0$, proving $\mathrm{unrAt}=\top$ on $Q\setminus Q'$ and $\mathrm{selOn}(d',B,Q')=\mathrm{selOn}(d',B,Q)$ (`unr_first`, `selOn_eq`). Because `StartInd` proves this internally for arbitrary $\ell$-power torsion $B$, the external `FirstPlace` hypothesis passed to `start_of_resBound` is unused!
3. **Functorial adjugate slicing.** Cofactor expansion commutes with every ring homomorphism (`RingHom.map_adjugate`), so $\pi(\operatorname{adj}\Phi)_{b_1,b_2}=(\operatorname{adj}\pi(\Phi))_{b_1,b_2}$. For *any* polynomial lift $F\in O_0[X_q:q\in\iota]$ of $(\operatorname{adj}\Phi)_{b_1,b_2}$, applying Mathlib's coordinate slice `MvPolynomial.killCompl` (setting $X_{\mathrm{inl}\,b}=0$ for $b\ge n$) produces a valid lift $F'$ of $(\operatorname{adj}\pi(\Phi))_{b_1,b_2}$ (`resLam_toLam`). The unit coefficient of $F'$ guaranteed by `ResBound` at multi-index $m'$ is literally the coefficient of $F$ at $e_*(m')$, which has degree $\lvert m'\rvert<4rn+1$ and zero exponent in every unused left variable!
4. **Compatibility with the ramified DVR ideal threshold on the same matrix.** Why must `NFit` demand a **unit** coefficient ($v_0(F_m)=0$), whereas `Small2` and `NF` use the much smaller ramified ideal $I=(\ell^\nu)\mathfrak m_{O_0}=(\varpi^{e+1})$? First, `SmallSub.exists_small` constructs a single open normal subgroup $L$ with $T_s(g)-I_r\in M_r(I)$ (`Small2`); since $I\subseteq\mathfrak m_{O_0}$ (`idl_le_max`), the very same $L$ satisfies residual triviality `Small` ($T_s(g)\equiv I_r\pmod{\mathfrak m_{O_0}}$), feeding `Start` and `Step`/`Grow` simultaneously. Second, on a presentation $\Phi$ whose restricted determinant $\det\pi(\Phi)$ already has all coefficients inside $I$ (so `NF` fails at $j=0$), corank-one `ResBound` still finds an adjugate entry with a *unit* coefficient. When `Step` (§10.4.9) specializes that **same** $\Phi$ into $A=(O_0/I)[t]/(t^h)$, reducing modulo $I$ kills $I$ while keeping $\ell^\nu\notin I$ ($v_0(\ell^\nu)=e<e+1$) nonzero, and Weierstrass division (`unit_mul_pow_of_deg`) requires the leading low-degree coefficient of the specialized adjugate entry to be a **unit** of $O_0/I$ (equivalently, of $O_0$, since $\sqrt{I}=\mathfrak m_{O_0}$) so that the adjugate entry divides $t^{(e+1)w}$ in $A$ without annihilating $\ell^\nu t^{2(e+1)w+1}\ne0$.

##### Worked examples and strict counterexamples [Expository]

The next two examples execute every step of `TameScalar`, `Small2`, `unr_first`, `resLam`, `killCompl`, and the `I=(\ell^\nu)\mathfrak m_{O_0}` threshold on concrete rank-$2$ free modules $M_0=O_0^2$ over an unramified DVR and a ramified DVR, followed by strict counterexamples when each hypothesis group is dropped. They are finite/local-profinite **algebraic models** (`GalHyp` in the archive requires $r\ge100$, so $4rn+2\ge402$ in global instances); every identity below is verified in exact arithmetic by `verify_start_seed.py` (11,943 assertions, 0 failures).

###### Example 10.13ah. Unramified DVR $O_0=\mathbb Z_3[i]$: tame scalar $i$, unused left inertia killing, and adjugate slicing

Over $\mathbb Z_3$ itself, the residue field $\mathbb F_3$ has $\mathbb F_3^\times=\{\pm1\}$, so every unit satisfies $u^2-1\equiv0\pmod3$ and **no** element can satisfy the `IsTameInertiaElementAtTwistPrime` condition $d_z^2-1\in O_0^\times$! Adjoining $i$ ($i^2=-1$) gives the unramified quadratic DVR $O_0=\mathbb Z_3[i]$ at $\ell=3$, with uniformizer $\varpi=3$, additive valuation $v_3(3)=1$, and residue field $k_{O_0}=\mathbb F_9=\mathbb F_3(\bar i)$. Take $\nu=1$, so $e=v_3(3^1)=1$ and the threshold ideal is $I=(3)\mathfrak m_{O_0}=(9)$. Take rank $r=2$ ($M_0=O_0^2$), $n=R_0=1$, $t=1$, $R=2$, and level $M=3$; then $4rn+2=10<27=3^3$ holds literally, with index sets $\iota=\{L_0,L_1,R_0\}$ ($\mathrm{Fin}\,2\sqcup\mathrm{Fin}\,1$) and $\iota'=\{L_0,R_0\}$ ($\mathrm{Fin}\,1\sqcup\mathrm{Fin}\,1$).

1. **Tame scalar and `Small2` on $M_0=O_0^2$.** Let $z$ act by $T(z)=iI_2$, i.e. $d_z=i\in O_0^\times$. Then
   $$d_z^2-1=-2\in O_0^\times,\qquad d_z-1=-1+i\in O_0^\times\quad\bigl(N(-1+i)=2\not\equiv0\pmod3\bigr),$$
   matching Lemma 10.13ak(1). Let $g_L\in L$ act by $T(g_L)=\begin{pmatrix}10&9i\\0&1\end{pmatrix}=I_2+9\begin{pmatrix}1&i\\0&0\end{pmatrix}$. Every entry of $T(g_L)-I_2$ has $v_3\ge2$, hence lies in $I=(9)$ (`Small2`) and vanishes modulo $3$ (`Small`).
2. **Killing inertia at the unused left place $P(L_1)$.** Take norm $q_1=109=1+2\cdot54\equiv1\pmod{2\cdot3^3}$ and Frobenius $\phi_1=g_L z\in zL$, so
   $$T(\phi_1)=T(g_L)T(z)=\begin{pmatrix}10i&-9\\0&i\end{pmatrix}\equiv\bar i I_2\pmod3,$$
   while at the conjugate place $\bar v_1$ self-duality gives residual scalar $\bar i^{-1}=-\bar i\ne1$. Let $B=(O_0/(27))^2$ with $\mathrm{delInv}\,d'$ of order dividing $27$ at $\phi_1$ and trivial on $\mathrm{Ine}(v_1)$ (since $v_1$ does not lie over $L_0$ or $R_0$). On a tame inertia generator $\gamma_1$ with $\phi_1\gamma_1\phi_1^{-1}=\gamma_1^{109}$ in the pro-$3$ tame quotient, any continuous $1$-cocycle $c$ satisfies $\mathrm{repOn}(\phi_1)\,c(\gamma_1)=109\,c(\gamma_1)$. Iterating $27$ times kills $\mathrm{delInv}\,d'(\phi_1)^{27}=1$ and yields $Y\,c(\gamma_1)=0$ for
   $$Y=T(\phi_1)^{27}-109^{27}I_2\in M_2(\mathbb Z_3[i]).$$
   Modulo $3$, $\bar i^{27}=\bar i^3=-\bar i$ and $\overline{109}^{27}=1$, so $\bar Y=(-\bar i-1)I_2\equiv(2+2\bar i)I_2\pmod3$ has $\det\bar Y=(2+2\bar i)^2=8\bar i\equiv2\bar i\in\mathbb F_9^\times$. Hence $\det Y\in O_0^\times$, $Y\in\mathrm{GL}_2(\mathbb Z_3[i])$, and $c(\gamma_1)=0$.
3. **Why `NF` fails while `NFit` succeeds on the same $2\times2$ matrix $\Phi$.** Over $\Lambda_{2,1}=O_0[(\mathbb Z/27)^3]$ (writing $X_q=[e_q]-1$), consider
   $$\Phi=\begin{pmatrix}3+X_{L,0}+X_{L,1}&X_{L,1}\\9iX_{R,0}&9+X_{L,1}\end{pmatrix},\qquad \bar\Phi=\mathrm{resLam}(\Phi)=\begin{pmatrix}3+X_{L,0}&0\\9iX_{R,0}&9\end{pmatrix}.$$
   Every entry of $\Phi$ reduces modulo $(3,X_{L,0},X_{L,1},X_{R,0})$ to $0$, so no entry is a unit. The restricted determinant is $\det\bar\Phi=27+9X_{L,0}$: **every** coefficient lies in $I=(9)$, so `NF` fails at $j=0$. Now form the $2\times2$ adjugate on $\Lambda_{2,1}$:
   $$\operatorname{adj}\Phi=\begin{pmatrix}9+X_{L,1}&-X_{L,1}\\-9iX_{R,0}&3+X_{L,0}+X_{L,1}\end{pmatrix},\qquad \mathrm{resLam}(\operatorname{adj}\Phi)=\begin{pmatrix}9&0\\-9iX_{R,0}&3+X_{L,0}\end{pmatrix}=\operatorname{adj}\bar\Phi.$$
   Notice why `NFit` must forbid positive exponents at $X_{L,1}$: $(\operatorname{adj}\Phi)_{0,0}=9+X_{L,1}$ has a unit coefficient $1$ at $X_{L,1}$ of degree $1$, yet setting $X_{L,1}=0$ via `killCompl` leaves $9\notin O_0^\times$, which is useless when `Step` specializes $X_{L,1}\mapsto0$! By contrast, $(\operatorname{adj}\Phi)_{1,1}=3+X_{L,0}+X_{L,1}$ slices under `killCompl` to $3+X_{L,0}$, whose degree-$1$ coefficient at $X_{L,0}$ ($1<4rn+1=9$, exponent $0$ at $X_{L,1}$) is $1\in O_0^\times$. Adding any element of $\ker(\mathrm{toLam})=\bigl((1+X_q)^{27}-1\bigr)_{q\in\iota}$ changes $[X_{L,0}]F$ by a multiple of $\binom{27}{1}=27\in(3)$, so $[X_{L,0}]F\equiv1\pmod3$ remains a unit in $O_0$ for **every** lift $F$.

###### Example 10.13ai. Ramified DVR $O_0=\mathbb Z_2[\zeta_3,\pi]$ ($\pi^2=2$): the ideal gap $(\pi^4)\subsetneq(\pi^3)\subsetneq(\pi)$ and compatibility with `Step`

At $\ell=2$, $\mathbb Z_2[\sqrt2]$ has residue field $\mathbb F_2$, whose sole unit $1$ again fails $\bar d_z\ne1$. Adjoining $\zeta_3$ ($\zeta_3^2+\zeta_3+1=0$) and $\pi=\sqrt2$ ($\pi^2=2$) gives the ramified DVR $O_0=\mathbb Z_2[\zeta_3,\pi]$ of absolute ramification index $v_\pi(2)=2$ and residue field $k_{O_0}=\mathbb F_4=\mathbb F_2(\bar\zeta_3)$. Take $\nu=1$, so $e=v_\pi(2^1)=2$ and
$$I=(2)\mathfrak m_{O_0}=(\pi^3),\qquad (4)=(\pi^4)\subsetneq I=(\pi^3)\subsetneq\mathfrak m_{O_0}=(\pi).$$
Here $2=\pi^2\notin I$ ($v_\pi(2)=2\le e$), whereas $\pi^3\in I\setminus(4)$ ($v_\pi(\pi^3)=3>e$, yet $4\nmid\pi^3$). Take $r=2$ ($M_0=O_0^2$), $n=1$, $R=2$, and $M=5$, so both `Start`'s threshold $4rn+2=10<32=2^5$ and `Step`'s threshold $J=2^{5-1-1}=8$ hold simultaneously.

1. **Tame scalar, `Small2`, and Frobenius $32$-nd power.** Set $T(z)=\zeta_3 I_2$ ($d_z=\zeta_3\in O_0^\times$). Modulo $\pi$, $\overline{d_z^2-1}=\bar\zeta_3^2+1=\bar\zeta_3\in\mathbb F_4^\times$ and $\overline{d_z-1}=\bar\zeta_3+1=\bar\zeta_3^2\in\mathbb F_4^\times$, so $d_z^2-1,d_z-1\in O_0^\times$ (in characteristic $2$, $d_z-1$ and $d_z+1$ have the *same* nonzero residue $\bar\zeta_3^2$!). For $g_L\in L$ with $T(g_L)=\begin{pmatrix}1+\pi^3&\pi^3\zeta_3\\0&1+\pi^3\end{pmatrix}$, $T(g_L)-I_2\in M_2((\pi^3))$ satisfies `Small2` and reduces to $0\pmod\pi$. At an unused left place of norm $q_1=65\equiv1\pmod{64}$ with $\phi_1=g_L z$, the $2^5$-th power matrix $Y=T(\phi_1)^{32}-65^{32}I_2$ reduces modulo $\pi$ to $(\bar\zeta_3^{32}-1)I_2=(\bar\zeta_3^2-1)I_2=\bar\zeta_3 I_2$ with $\det\bar Y=\bar\zeta_3^2\in\mathbb F_4^\times$, so $Y\in\mathrm{GL}_2(O_0)$ kills $\mathrm{Ine}(v_1)$ on every $2$-power torsion module.
2. **Adjugate seed vs. ramified determinant threshold.** Over $\Lambda_{2,1}=O_0[(\mathbb Z/32)^3]$, set
   $$\Phi=\begin{pmatrix}\pi+X_{L,0}+\zeta_3 X_{L,1}&\pi X_{L,1}+\pi^3 X_{R,0}\\\pi^3&\pi^3+X_{L,1}\end{pmatrix},\qquad \bar\Phi=\begin{pmatrix}\pi+X_{L,0}&\pi^3 X_{R,0}\\\pi^3&\pi^3\end{pmatrix}.$$
   Then $\det\bar\Phi=\pi^4+\pi^3 X_{L,0}-\pi^6 X_{R,0}$: its linear coefficient $\pi^3$ is **not** divisible by $2^{\nu+1}=4$, yet $\pi^3\in I=(\pi^3)$, so every coefficient of $\det\bar\Phi$ lies in $I$ and `NF` fails! Meanwhile `NFit` rejects $(\operatorname{adj}\Phi)_{0,0}=\pi^3+X_{L,1}\mapsto\pi^3\notin O_0^\times$ and selects $(\operatorname{adj}\Phi)_{1,1}=\pi+X_{L,0}+\zeta_3 X_{L,1}\mapsto\pi+X_{L,0}$, whose $[X_{L,0}]$ coefficient is $1\in O_0^\times$ across all lifts (since $\binom{32}{b}\equiv0\pmod2$ for $1\le b\le31$).
3. **Why `Step` needs both the unit in `NFit` and the ideal $I=(\pi^3)$ on this same $\Phi$.** For witness degree $d_0=1$, `Step` (§10.4.9) sets $b=(e+1)d_0=3$ and $h=2b+2=8\le J=8$, and maps $\Phi$ to $A=(O_0/(\pi^3))[t]/(t^8)$ along $X_{L,0}\mapsto t$, $X_{L,1}\mapsto0$, $X_{R,0}\mapsto0$. Under this specialization, $(\operatorname{adj}\Phi)_{1,1}$ becomes $\pi+t\in A$, which **divides $t^3$** in $A$ because $\pi^3=0$ in $O_0/I$:
   $$(\pi+t)(t^2-\pi t+\pi^2)=t^3+\pi^3\equiv t^3\pmod{\pi^3},$$
   while the witness scalar $2t^{2b+1}=\pi^2 t^7\not\equiv0\pmod{\pi^3}$ survives because $v_\pi(2)=2<3$! Had $I$ been $(2)=(\pi^2)$, $2t^7$ would vanish identically; conversely, had `NFit` only guaranteed $[X_{L,0}]\notin I$ (say $\pi$, of valuation $1\le2$), the specialized entry $\pi+\pi t\in(\pi)A$ would vanish modulo $\pi$ and could never divide $t^3$.

###### Example 10.13aj. Strict counterexamples when dropping each precondition group

1. **Dropping common action / same-matrix compatibility (`repOn_eq`).** Let $G=\mathbb Z/3\mathbb Z$ act on $B=\mathbb F_3$, with $\rho(g)=1$ and $\rho'(1)=2\equiv-1\pmod3$. The map $z(g)=g\bmod3$ lies in $Z^1(G,\rho)$, yet $z(1+1)=2\ne z(1)+2z(1)=0\pmod3$, so `continuousCocycleChangeScalarsBack` does not even land in $Z^1(G,\rho')$. Likewise, if `Start` and `Step` did not quantify universally over the *same* `Computes` matrix $\Phi$, $\Phi_1=I_2$ and $\Phi_2=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ both present the zero module ($a=2$), yet the unit diagonal index $(1,1)$ of $\operatorname{adj}\Phi_1=I_2$ has entry $0$ in $\operatorname{adj}\Phi_2$.
2. **Dropping the residual corank-one bound (`ResBound` / `Corank` $\le1$).** Over $O_0=\mathbb Z_3[i]$ ($a=2\ne0$), the corank-two matrix $\Phi_{\mathrm{cor\,2}}=\operatorname{diag}(3,3)$ computes a rank-$2$ $3$-torsion Selmer group at trivial twist and has $\operatorname{adj}\Phi_{\mathrm{cor\,2}}=\operatorname{diag}(3,3)$. Every lift of every adjugate entry has all coefficients below degree $27$ divisible by $3$, so `NFit` is false.
3. **Dropping the descent/pullback preconditions (`Surjective π` and $u\ne1$).**
   - *Without `Surjective π`:* take the non-surjective inclusion $\pi:\mathbb F_3\hookrightarrow\Lambda'=\mathbb F_3[t]/(t^2)$ and $B=\Lambda'$. First, in `chLoc_mem_bkOn`, the $\mathbb F_3$-span of $1\in B$ has size $3$ whereas its $\Lambda'$-span is all of $B$ (size $9$, containing $t\notin\mathbb F_3\cdot1$), so local Bloch–Kato spans are not preserved. Second, in `exists_equiv_of_surjective`, the $\mathbb F_3$-linear bijection $e(u+vt)=v+ut$ satisfies $e(t\cdot1)=e(t)=1\ne0=t\cdot t=t\cdot e(1)$, failing $\Lambda'$-linearity.
   - *Without $u\ne1$ at an unused left place (`unr_first`):* let $D_{v_1}=\langle\phi_1,\gamma_1\mid\phi_1^3=\gamma_1^{27}=1,\ \phi_1\gamma_1\phi_1^{-1}=\gamma_1^{19}\rangle$ ($q_1=19\equiv1\pmod{18}$, $19^3\equiv1\pmod{27}$) act trivially ($u=1$) on $B=\mathbb F_3$. Then $c(\phi_1^a\gamma_1^b)=b\bmod3$ satisfies $c(\phi_1^{a_1}\gamma_1^{b_1}\cdot\phi_1^{a_2}\gamma_1^{b_2})=b_1+19^{a_1}b_2\equiv b_1+b_2\pmod3$, giving a continuous $1$-cocycle with $c(\gamma_1)=1\ne0$ while all coboundaries vanish. Thus $\mathrm{unrAt}(v_1)\ne\top$ and shrinking $Q$ to $Q'$ strictly shrinks $\mathrm{selOn}$.

##### Definitions [Lean, read]

Keep the archive data $D,N,X,\mathrm{bkP}$, twist index $i$, signature $s\in\mathrm{Sig}(i)$, rank $r=D.R.r$, prime $\ell=X.l(i)$, $\nu=\mathrm{nu}(X,i)$, and DVR $O_0=X.O0(i)$ with maximal ideal $\mathfrak m_{O_0}$ and residue field $k_{O_0}$.

1. **Ramified ideal and small subgroups** (`Small2.lean:13–17`, `IsDualDualRep.lean:21–24`). Put $I=\mathrm{idl}(i)=(\ell^\nu)\mathfrak m_{O_0}\trianglelefteq O_0$.
   - `Small i s L z` asserts that $L\le G$ is open, normal, and stable under complex conjugation $\iota=\mathrm{cConj}$, every commutator $gzg^{-1}z^{-1}$ lies in $L$, and for all $g\in L$, $T_{\mathrm{mat}}(i,s)(g)\equiv I_r\pmod{\mathfrak m_{O_0}}$ and $\varepsilon_0(g)\equiv1\pmod{\mathfrak m_{O_0}}$.
   - `Small2 i s M L z` conjoins `Small i s L z`, action triviality of $L$ on all $(2\ell^M)$-th roots of unity in $\Omega$, and the stronger integral congruence $(T_{\mathrm{mat}}(i,s)(g)-I_r)_{ab}\in I$ for all $g\in L$ and $a,b\in\mathrm{Fin}\,r$.
2. **Unbalanced localization and the exact quantifiers of `NF`, `NFit`, and `Start`** (`Small2.lean:20–45`). Let $P:\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n\to\mathrm{Pl}_E$ and $d:\mathrm{Pl}_E\to(G\to(\mathbb Z/\ell^M)^\times)$ (written multiplicatively via `Multiplicative (ZMod (\ell^M))`).
   - `PiLocalization₂ i M d A L z P` (`:20–25`) conjoins: (i) `SlopeTestRemainingChoices` $(M,A,P,d\circ P)$; (ii) for every left index $a\in\mathrm{Fin}\,R$, all inertia subgroups above $P(\mathrm{inl}\,a)$ lie in $L$, and every Frobenius $\sigma$ at $P(\mathrm{inl}\,a)$ has $g\sigma g^{-1}z^{-1}\in L$ for some $g\in G$; and (iii) for every right index $a\in\mathrm{Fin}\,n$, $\mathrm{Dec}_v(P(\mathrm{inr}\,a))\le L$, and for every $b\in\mathrm{Fin}\,R$ and Frobenius $\sigma$ at $P(\mathrm{inr}\,a)$, $d_{P(\mathrm{inl}\,b)}(\sigma)=\mathrm{ofAdd}(\delta_{a.1,b.1})$.
   - `NFit bkP i s M d P c` (`:32–35`) states:
     $$\forall Q,\ \mathrm{IsQ}\,P\,Q\implies\forall a\in\mathbb N,\ \forall\Phi\in M_a(\Lambda_{R,n}),\ \mathrm{Computes}(s,M,d\circ P,Q,\Phi)\implies$$
     $$a=0\ \vee\ \exists b_1,b_2\in\mathrm{Fin}\,a,\ \forall F\in O_0[X_q],\ \mathrm{toLam}\,F=(\operatorname{adj}\Phi)_{b_1,b_2}\implies$$
     $$\exists m:(\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n)\to_0\mathbb N,\quad \lvert m\rvert<c\ \wedge\ \bigl(\forall j\in\mathrm{Fin}\,R,\ n\le j.1\implies m(\mathrm{inl}\,j)=0\bigr)\ \wedge\ \mathrm{IsUnit}(F_m).$$
     By contrast, `NF bkP i s M d P c` (`:27–30`) quantifies over lifts $\mathrm{toLam}\,F=\det\Phi$ and asks for $\lvert m\rvert<c$ and $F_m\notin I$ (without coordinate support restriction).
   - `Start bkP i s` (`:40–44`) states: for all $M,R,n,d,A,L,z$, $P:\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n\to\mathrm{Pl}_E$, and $\phi,\phi':\mathrm{Fin}\,n\to G$, if $n\le R$, $4rn+2<\ell^M$, `IsTameInertiaElementAtTwistPrime X i z`, `Small i s L z`, `PiLocalization₂ i M d A L z P`, each $(\phi_a,\phi'_a)$ is a right Frobenius pair (`IsFrob` and `IsCj`), and `Corank bkP i s φ φ' 1` holds, then `NFit bkP i s M d P (4rn+1)` holds.
3. **Scalar-change cocycle operations and group-ring restriction** (`ContinuousCocycleChangeScalarsBack.lean:80–196, 228–232, 339–354`).
   - Given continuous $G$-representations $\rho$ (over $R$) and $\rho'$ (over $R'$) on the *same* discrete topological additive group $A$ with $\rho(g)=\rho'(g)$ as maps $A\to A$, `z1Ch` and its inverse `continuousCocycleChangeScalarsBack` (`:80–125`) transport `cocycles1` along $\mathrm{id}_A$, inducing `h1Ch` $:H^1(G,\rho)\to H^1(G,\rho')$ (`:99–100`). For $\pi:\Lambda\to\Lambda'$ and a $\Lambda'$-module $B$ with $\Lambda$-pullback $B_\pi=\mathrm{Module.compHom}\,B\,\pi$, `ch` and `chLoc` (`:160–178`) instantiate `h1Ch` globally and on decomposition groups $D_v$ for $\mathrm{repOn}$.
   - `tbar i s` $:G\to M_r(k_{O_0})$ (`:228–232`) is entrywise reduction of $T_{\mathrm{mat}}(i,s)$ modulo $\mathfrak m_{O_0}$.
   - For $e:\iota'\to\iota$, `resLam i M e` $:\Lambda_\iota\to\Lambda_{\iota'}$ (`:339–345`) is the $O_0$-algebra map `MonoidAlgebra.mapDomainAlgHom` induced on $\Delta_\iota=(\iota\to\mathbb Z/\ell^M)$ by precomposition $x\mapsto x\circ e$.

##### Lemmas and main theorem [Lean, read]

###### Lemma 10.13ak (tame inertia scalar and existence of the ramified `Small2` subgroup) [Lean, read]

1. *(`TameScalar`.) Assume `IsotypicValuationAtRing bkP i s` (the first conjunct of `GalHyp bkP i s`) and `IsTameInertiaElementAtTwistPrime X i z`. Setting $d_z=\chi_s(z)^{-1}\in O_0^\times$, we have $T_{\mathrm{mat}}(i,s)(z)=d_z I_r$, $d_z^2-1\in O_0^\times$, $d_z-1\in O_0^\times$, and $\varepsilon_0(z)=1$.*
2. *(`SmallSub`.) For every twist index $i$, $\ell\ne0$ in $O_0$, $\ell\in\mathfrak m_{O_0}$, and every nonzero ideal of $O_0$ — in particular $I=\mathrm{idl}(i)=(\ell^\nu)\mathfrak m_{O_0}\subseteq\mathfrak m_{O_0}$ — is open in the $\mathfrak m_{O_0}$-adic topology. For every $T\subseteq\mathrm{Sig}(i)$ satisfying `GalHyp`, every $z$ satisfying `IsTameInertiaElementAtTwistPrime X i z`, every $M\in\mathbb N$, and every open normal $H\le G$ containing $\mathrm{Ine}(A)$ for all $A$ over $v\in\mathrm{pD}(i)$ (as supplied by `AdmFam`), there exists an open normal subgroup $L\le H$ such that `Small2 i s M L z` (and hence `Small i s L z`) holds for every $s\in T$.*

*(Lean: `TameScalar.not_mem_placesOver`, `isUnit_inv_sq_sub_one`, `isUnit_sub_one`, `exists_scalar_tmat_of_tame_inertia`, `TameInertiaElementActsByScalar.lean:8–62`, wrapper `TameInertiaElementActsByScalarStatement.lean:7`; `SmallSub.exists_fix_roots`, `normal_of_comm`, `comm_mem_ker`, `isOpen_ideal`, `l_ne_zero`, `l_mem`, `exists_eps`, `pD_not_mem`, `exists_kerT`, `exists_small`, `ExistsOpenNormalSubgroupUnderInertia.lean:15–185`, wrapper `ExistsOpenNormalSubgroupUnderInertiaStatement.lean:7`.)*

*Proof.* (1) Unpack $z$ (`:31`): there are $v\in\mathrm{pD}(i)$ and a valuation ring $A$ over $v$ with $z\in\mathrm{Ine}(A)$ and $\delta(z)^2-1\in O_0^\times$. By `pD_eq`, $v$ lies above the auxiliary rational prime `pde` or `pde'`, which is prime and distinct from $\ell$ and from every $D.\mathrm{host}.g(k)$; since distinct rational primes generate coprime ideals in $\mathcal O_E$, no prime ideal $v$ lies above both (`not_mem_placesOver`, `:8–16`), giving $v\notin\mathrm{placesOver}(\ell)$ and $v\notin\mathrm{placesOver}(g(k))$ (`:33–46`). Unramifiedness of $\rho_s$ (`h.1`) then forces $\rho_s(z)=1$ (`:47`), while `twistCharacterFamily_at_auxiliaryPlaces` evaluates $\chi_s(z)$ to $\delta(z)$ or $\delta(z)^{-1}$ according to `side i s` (`:48–49`). Setting $d_z=\chi_s(z)^{-1}\in\{\delta(z)^{-1},\delta(z)\}$, the identity $(u^{-1})^2-1=-(u^{-1})^2(u^2-1)$ shows $d_z^2-1\in O_0^\times$ in both branches (`isUnit_inv_sq_sub_one`, `:17–22,50–54`), and $d_z^2-1=(d_z-1)(d_z+1)\in O_0^\times$ implies $d_z-1\in O_0^\times$ (`isUnit_sub_one`, `:24–27,55`). Moreover $T_{\mathrm{mat}}(i,s)(z)=\chi_s(z)^{-1}\rho_s(z)=d_z I_r$ (`:56`), and on $\mathrm{Ine}(A)$ away from $\ell$, `cycZ_toZModPow_eq` at $q=1$ gives $\mathrm{cycZ}(z)=1$ mod every $\ell^n$, hence $\mathrm{cycZ}(z)=1$ in $\mathbb Z_\ell^\times$ and $\varepsilon_0(z)=1$ (`:57–61`).

(2) Evaluating $O_0\xrightarrow{\mathrm{phiK}(i,1)}O_1$ at the primitive $\ell$-th root `zk_prim i 1` (`NeZero (\ell^1)`) proves $\ell\ne0$ in $O_0$ (`l_ne_zero`, `:53–59`), and mapping to $O$ via `X.O_l i` puts $\ell\in\mathfrak m_{O_0}$ (`l_mem`, `:61–65`). In any adic DVR $O$, a nonzero ideal $J'\ne\bot$ equals $(\varpi^n)$ (`ideal_eq_span_pow_irreducible`) and is therefore open (`isOpen_ideal`, `:44–50`). Next construct three open normal commutator-absorbing subgroups of $G$:
- Choose a primitive $(2\ell^M)$-th root of unity $\xi\in\Omega$. Every $a\in G$ sends $\xi\mapsto\xi^{j_a}$, so $a(b(\xi))=\xi^{j_a j_b}=b(a(\xi))$ for all $a,b\in G$; hence $K_1=\operatorname{Stab}_G(\xi)$ is open (`stabilizer_isOpen_of_isIntegral`), contains all commutators $aba^{-1}b^{-1}$ (so is normal by `normal_of_comm`), and fixes every $(2\ell^M)$-th root $\zeta=\xi^k$ (`exists_fix_roots`, `:15–40`).
- $K_2=\ker(\overline{\varepsilon_0}:G\to k_{O_0}^\times)$ contains all commutators (`comm_mem_ker`) and contains the open preimage of $\{\lVert u-1\rVert_\ell<1\}=1+\ell\mathbb Z_\ell$ under `continuous_cycZ` because $\ell\in\mathfrak m_{O_0}$ (`exists_eps`, `:67–80`).
- Because $\ell\ne0$ and $O_0$ is not a field (`IsDiscreteValuationRing.not_a_field`), $I=(\ell^\nu)\mathfrak m_{O_0}\ne\bot$ (`:143–144`). For each $s$, let $K_s=\ker\bigl(G\xrightarrow{T_{\mathrm{gl}}}\mathrm{GL}_r(O_0)\to\mathrm{GL}_r(O_0/I)\bigr)$ (`exists_kerT`, `:99–131`): $K_s$ is normal, open as the finite intersection over $a,b\in\mathrm{Fin}\,r$ of preimages of the open ideal $I$ under continuous $g\mapsto(T_{\mathrm{mat}}(g)-I_r)_{ab}$ (`:114–123`), and whenever $\rho_s(w)=1$, $T_{\mathrm{gl}}(w)=\chi_s(w)^{-1}I_r$ is scalar and central (`scalGL_comm`), so $T_{\mathrm{gl}}(gwg^{-1}w^{-1})=I_r$ and $gwg^{-1}w^{-1}\in K_s$ (`:124–130`).

Since `X.Sig i` is finite, $H_0=H\cap K_1\cap K_2\cap\bigcap_{s\in T}K_s$ is open and normal (`:148–155`). Set $L=H_0\cap\iota^{-1}(H_0)$, which is open, normal, $\iota$-stable, and $\le H$ (`:160–169`). For $z\in\mathrm{Ine}(A)$ above $v\in\mathrm{pD}(i)$, normality of $H$ and $\mathrm{Ine}(A)\le H$ put $gzg^{-1}z^{-1}\in H$, `c₁` and `c₂` put it in $K_1\cap K_2$, and `pD_not_mem` (`:88–97`) gives $\rho_s(z)=1$ for $s\in T$, putting $gzg^{-1}z^{-1}\in K_s$ (`:156–159`); applying the identical argument at the conjugate twist place $v'\in\mathrm{pD}(i)$ via `isPlaceOver_moveVal_cc` and `cConj_mem_ine` puts $\iota(gzg^{-1}z^{-1})\in H_0$, so $gzg^{-1}z^{-1}\in L$ (`:170–178`). Finally, `Ideal.mul_le_right` ($I\subseteq\mathfrak m_{O_0}$) reduces $(T_{\mathrm{mat}}(g)-I_r)_{ab}\in I$ modulo $\mathfrak m_{O_0}$ to $\bar T_s(g)=I_r$, proving both `Small` and `Small2` on $L$ (`:179–185`). $\square$

###### Lemma 10.13al (non-flat scalar descent of `Computes` along a surjective ring map) [Lean, read]

*Let $\pi:\Lambda\twoheadrightarrow\Lambda'$ be a **surjective** $O_0$-algebra homomorphism, let $d:\iota\to(G\to(\mathbb Z/\ell^M)^\times)$ and $d':\iota'\to(G\to(\mathbb Z/\ell^M)^\times)$ satisfy $\pi(\mathrm{delInv}\,d(g))=\mathrm{delInv}\,d'(g)$ for all $g\in G$, and let $Q'\subseteq Q$ be finite sets of places.*

1. *For every discrete $\Lambda'$-module $B$ with $\Lambda$-pullback $B_\pi=\mathrm{Module.compHom}\,B\,\pi$, we have $\mathrm{repOn}(T_{\mathrm{gl}},\,\mathrm{delInv}\,d,\,B_\pi)=\mathrm{repOn}(T_{\mathrm{gl}},\,\mathrm{delInv}\,d',\,B)$ pointwise on $G\times B^r$, and `ch` induces an additive isomorphism $H^1(G,B_\pi^r)\xrightarrow{\sim}H^1(G,B^r)$ carrying $\mathrm{selOn}(s,\mathrm{delInv}\,d,B_\pi,Q)$ bijectively onto $\mathrm{selOn}(s,\mathrm{delInv}\,d',B,Q)$.*
2. *Suppose that for every discrete $\ell$-power torsion $\Lambda'$-module $B$, $\mathrm{selOn}(s,\mathrm{delInv}\,d',B,Q')=\mathrm{selOn}(s,\mathrm{delInv}\,d',B,Q)$. Then for every $a\in\mathbb N$ and every $\Phi\in M_a(\Lambda)$,*
   $$\mathrm{Computes}(s,M,d,Q,\Phi)\implies\mathrm{Computes}\bigl(s,M,d',Q',\pi(\Phi)\bigr).$$

*(Lean: `exists_equiv_of_surjective`, `z1Ch`, `h1Ch`, `h1Ch_bijective`, `continuousCocycleChangeScalarsBack`, `mulVec_map`, `repOn_eq`, `ch`, `ch_res`, `chLoc`, `chLoc_mem_bkOn`, `ch_mem_selOn`, `computes_map`, `ContinuousCocycleChangeScalarsBack.lean:64–223`.)*

*Proof.* (1) By definition of $B_\pi$, $r\cdot_\Lambda b=\pi(r)\cdot_{\Lambda'}b$, so $\mathrm{delInv}\,d(g)\cdot_\Lambda T_s(g)m=\pi(\mathrm{delInv}\,d(g))\cdot_{\Lambda'}T_s(g)m=\mathrm{delInv}\,d'(g)\cdot_{\Lambda'}T_s(g)m$ (`repOn_eq`, `:149–158`). Whenever two continuous actions $\rho,\rho'$ on the same discrete additive group $A$ agree pointwise, pushing $1$-cocycles along $\mathrm{id}_A$ (`z1Ch`, `:84–88`) and pulling them back verbatim (`continuousCocycleChangeScalarsBack`, `:121–125`) are mutually inverse maps on `cocycles1`; `h1Map_id` and `h1Map_comp` (`H1MapSubgroup.lean:16–30`) show the induced maps `h1Ch` on $H^1$ compose to $\mathrm{id}$ in both directions (`h1Ch_bijective`, `:105–119`). On local classes, restriction to any subgroup commutes with `h1Ch` (`ch_res`, `:167–172`), preserving unramifiedness away from $\ell$ and $\mathrm{Spl}(i)\cup Q$. At a place $v\mid\ell$, `bkOn` is the $\Lambda$-span (resp. $\Lambda'$-span) of the local finite/crystalline image $S_v(B_\pi)$ (resp. $S_v(B)$) (`BlochKatoPhases.lean:64–70`). Because `chLoc` maps $S_v(B_\pi)$ bijectively onto $S_v(B)$ and $\pi:\Lambda\twoheadrightarrow\Lambda'$ is **surjective**, the $\Lambda'$-submodule spanned by $S_v(B)$ restricts along $\pi$ to the $\Lambda$-submodule spanned by $S_v(B)$; applying Mathlib's `Submodule.apply_mem_span_image_iff_mem_span` to the $\Lambda$-linear equivalence `chLoc` gives $\mathrm{chLoc}(x_v)\in\mathrm{bkOn}(B)\iff x_v\in\mathrm{bkOn}(B_\pi)$ (`chLoc_mem_bkOn`, `:181–196`). Applying `ch_mem_selOn` (`:198–208`) in both directions (viewing $\pi$ and $\mathrm{id}_{\Lambda'}$ symmetrically via `h1Ch` for `repOn_eq.symm`) gives the bijection on `selOn` at $Q$.

(2) Let $B$ be a discrete $\ell$-power torsion $\Lambda'$-module; then $B_\pi$ is also $\ell$-power torsion because $(n\cdot 1_\Lambda)\cdot_\Lambda b=(n\cdot 1_{\Lambda'})\cdot_{\Lambda'}b$. On $B^a$, $\pi(\Phi)x=\Phi\cdot_\Lambda x$ (`mulVec_map`, `:132–135`), so $\ker(\pi(\Phi)\mid B^a)=\ker(\Phi\mid B_\pi^a)$. Composing the $\Lambda$-linear equivalence $e_{B_\pi}:\ker(\Phi\mid B_\pi^a)\xrightarrow{\sim}\mathrm{selOn}(d,B_\pi,Q)$ from `Computes` with `ch` and using $\mathrm{selOn}(d',B,Q)=\mathrm{selOn}(d',B,Q')$ yields an additive bijection $e'_B:\ker(\pi(\Phi)\mid B^a)\xrightarrow{\sim}\mathrm{selOn}(d',B,Q')$ that is $\Lambda$-linear (`:214–219`). Given any $r'\in\Lambda'$, surjectivity of $\pi$ supplies $r\in\Lambda$ with $\pi(r)=r'$, so $e'_B(r'x)=e'_B(r\cdot_\Lambda x)=r\cdot_\Lambda e'_B(x)=\pi(r)e'_B(x)=r'e'_B(x)$, upgrading $e'_B$ to a $\Lambda'$-linear equivalence (`exists_equiv_of_surjective`, `:64–77`). Compatibility with $\Lambda'$-linear maps $f:B\to B'$ holds on cocycle values because `ch` acts as $\mathrm{id}$ on underlying functions (`:220–222`). $\square$

###### Lemma 10.13am (unramifiedness at unused left places and `selOn` invariance) [Lean, read]

*Assume `TameQuotient_holds` (`ExistsCoprimePowOfMemIneKer.lean:598`, `[Lean]`). Let `GalHyp bkP i s`, `IsTameInertiaElementAtTwistPrime X i z`, `Small i s L z`, and `PiLocalization₂ i M d A L z P` hold for $P:\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n\to\mathrm{Pl}_E$ with $n\le R$ and $M\ge1$. Let $e:\mathrm{Fin}\,n\sqcup\mathrm{Fin}\,n\hookrightarrow\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n$ be $\mathrm{Sum.map}\,(\mathrm{Fin.castLE}\,h_{n\le R})\,\mathrm{id}$, let $d'=(d\circ P)\circ e$, let $Q$ satisfy `IsQ P Q`, and let $Q'=\{v\in Q:\exists q',\ \mathrm{Over}(P(e(q')),v)\}$. Then for every discrete $\ell$-power torsion $\Lambda_{n,n}$-module $B$:*

1. *For every $v\in Q\setminus Q'$, $\mathrm{unrAt}\bigl(\mathrm{repOn}(T_{\mathrm{gl}},\mathrm{delInv}\,d',B),\,A_v\bigr)=\top$.*
2. *$\mathrm{selOn}(s,\mathrm{delInv}\,d',B,Q')=\mathrm{selOn}(s,\mathrm{delInv}\,d',B,Q)$.*

*(Lean: `unrAt_eq_top`, `ContinuousCocycleChangeScalarsBack.lean:18–78`; `tbar_frob`, `eq_zero_of_scalar`, `:239–332`; `delInv_pow`, `:367–374`; `unr_first`, `selOn_eq`, `:406–450`.)*

*Proof.* (1) Any $v\in Q$ lies over $P(q)$ for some $q\in\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n$. If $q=\mathrm{inr}\,b$, then $q=e(\mathrm{inr}\,b)$, contradicting $v\notin Q'$; hence $q=\mathrm{inl}\,b$ with $n\le b<R$ (`:475–481`). By `SlopeTestRemainingChoices`, $v\notin S_0$ (so $v\nmid\ell$ and $v$ avoids the exceptional places of $D$ and $X$, `:414–415,422`), and $N(v)\equiv1\pmod{2\ell^M}$, which implies $\overline{N(v)}=1$ in $k_{O_0}$ since $M\ge1$ and $\ell\in\mathfrak m_{O_0}$ (`:416–419`).

First verify **exact inertia triviality** on $B^r$ (`:421–431`): for $\sigma\in\mathrm{Ine}(A_v)$, `GalHyp` (`hG.1.1`) gives $\rho_s(\sigma)=I_r$ and `twistCharacterFamily_unramified` gives $\chi_s(\sigma)=1$, so $T_{\mathrm{mat}}(i,s)(\sigma)=I_r$. Moreover, for every $q'\in\iota'$, $v$ does not lie over $P(e(q'))$ (since $v\notin Q'$), so `GoodChar` makes $d_{P(e(q'))}(\sigma)=1$, hence $\mathrm{delInv}\,d'(\sigma)=1$. Thus $\rho_B=\mathrm{repOn}(T_{\mathrm{gl}},\mathrm{delInv}\,d',B)$ fixes $B^r$ pointwise on $\mathrm{Ine}(A_v)$, and $B^r$ is $\ell$-power torsion because $\mathrm{Fin}\,r$ is finite (`:432–435`).

Next verify **residual scalar Frobenius action** (`tbar_frob`, `:239–288`): Lemma 10.13ak(1) gives $T_s(z)=d_z I_r$ with $u=\bar d_z\in k_{O_0}^\times\setminus\{1\}$ and $\varepsilon_0(z)=1$. For any Frobenius $\sigma_0$ at $P(\mathrm{inl}\,b)$, `PiLocalization₂` supplies $g\in G$ with $g\sigma_0 g^{-1}z^{-1}\in L$, so `Small` gives $\bar T_s(\sigma_0)=uI_r$ and $\bar\varepsilon_0(\sigma_0)=1$ (`:253–263`). If $v=P(\mathrm{inl}\,b)$, this applies directly (`:264–265`). If $v=\overline{P(\mathrm{inl}\,b)}$ is the CM-conjugate place, `exists_frob_of_conj` (`IsPlaceOverMoveValCc.lean:160`, `[Lean]`) writes $\phi=g\iota(\sigma_0)g^{-1}$ for a Frobenius $\sigma_0$ at $P(\mathrm{inl}\,b)$, `cycZ_of_isFrob` (`ContinuousCycMod.lean:175`, `[Lean]`) gives $\bar\varepsilon_0(\iota(\sigma_0))=\overline{N(v)}=1$, and conjugate self-duality (`hG.2.2.1`, `Tdual`) conjugates $T_s(\iota(\sigma_0))^{-1}$ to $(T_s(\sigma_0))^{\mathsf T}$ up to $\varepsilon_0$-powers that reduce to $1$, yielding $\bar T_s(\phi)=u^{-1}I_r$ with $u^{-1}\ne1$ (`:266–288`).

Now apply **Frobenius $\ell^M$-th power elimination** (`eq_zero_of_scalar`, `:290–332`): suppose $\rho_B(\phi)m=N(v)m$ for $m\in B^r$ and a Frobenius $\phi$ at $v$ with $\bar T_s(\phi)=\tilde u I_r$ ($\tilde u\in\{u,u^{-1}\}$, $\tilde u\ne1$). Set $k=\ell^M$; then $\rho_B(\phi^k)m=N(v)^k m$, while $\mathrm{delInv}\,d'(\phi)^k=1$ because $\Delta_{\iota'}$ has exponent $\ell^M$ (`delInv_pow`, `:367–374`). Thus the $O_0$-matrix $Y=T_{\mathrm{mat}}(i,s)(\phi^k)-N(v)^k I_r$ annihilates $m$ (`:323–330`). Modulo $\mathfrak m_{O_0}$, $\bar Y=(\tilde u^k-1)I_r$ (`:300–308`). Since $\operatorname{char}(k_{O_0})=\ell$ (`SmallSub.l_mem`), Mathlib's `sub_pow_char_pow` gives $\tilde u^{\ell^M}-1=(\tilde u-1)^{\ell^M}\ne0$, so $\det\bar Y=(\tilde u^k-1)^r\ne0$, $\det Y\in O_0^\times$, $Y\in\mathrm{GL}_r(O_0)$, and left-multiplying $Ym=0$ by $Y^{-1}$ forces $m=0$ (`:309–332`).

Finally, **tame inertia closure** (`unrAt_eq_top`, `:18–78`): let $c\in Z^1_{\mathrm{cont}}(\mathrm{Dec}(A_v),B^r)$. Because $\rho_B\mid_{\mathrm{Ine}(A_v)}=\mathrm{id}$, $f=\mathrm{ofAdd}\circ c\mid_{\mathrm{Ine}(A_v)}:\mathrm{Ine}(A_v)\to B^r$ is a continuous group homomorphism into a discrete $\ell$-power torsion group, so $\ker f$ is clopen of finite $\ell$-power index (`:36–50`) and contains the prime-to-$\ell$ inertia kernel $\mathrm{ineKer}(A_v,\ell)$ (`:51–54`). By `TameQuotient_holds` and `exists_isFrob`, $\mathrm{Ine}(A_v)$ is topologically generated modulo $\mathrm{ineKer}(A_v,\ell)$ by a single element $\gamma$ satisfying $\phi\gamma\phi^{-1}\gamma^{-N(v)}\in\mathrm{ineKer}(A_v,\ell)\le\ker f$ (`:29–30,58–62`). Expanding the cocycle law on $\phi\gamma\phi^{-1}$ using $\rho_B(\gamma)=\mathrm{id}$ gives $c(\phi\gamma\phi^{-1})=\rho_B(\phi)c(\gamma)$ (`:64–68`), hence $\rho_B(\phi)c(\gamma)=N(v)c(\gamma)$, which forces $c(\gamma)=0$ by the previous paragraph (`:69`). Since $\ker f$ is closed and contains both $\langle\gamma\rangle$ and $\mathrm{ineKer}(A_v,\ell)$, $\mathrm{Ine}(A_v)\le\ker f$, so $c\mid_{\mathrm{Ine}(A_v)}=0=\delta(0)$ (`:70–78`).

(2) In `selOn_eq` (`:439–450`), `SelAll` intersects local conditions `bkCond` across all places $v$ (`Formalism/GaloisCohomology/Statement.lean:45–63`): above $\ell$ it imposes `bkOn`, on $(\mathrm{Spl}(i)\cup Q)\setminus\{v\mid\ell\}$ it imposes $\top$, and elsewhere it imposes `unrAt`. Since $Q'\subseteq Q$, the local conditions for $Q'$ and $Q$ agree everywhere except at $v\in Q\setminus(Q'\cup\mathrm{Spl}(i)\cup\{v\mid\ell\})$, where part (1) gives $\mathrm{unrAt}=\top$, matching $Q$'s relaxed condition $\top$. $\square$

###### Lemma 10.13an (surjective group-ring slot restriction and `killCompl`) [Lean, read]

*Let $e:\iota'\hookrightarrow\iota$ be an **injective** map of finite index types (`Fintype`). Then:*

1. *$\mathrm{resLam}(i,M,e):\Lambda_\iota\to\Lambda_{\iota'}$ is surjective (`resLam_surjective`), and satisfies $\mathrm{resLam}(i,M,e)\bigl(\mathrm{delInv}\,d(g)\bigr)=\mathrm{delInv}(d\circ e)(g)$ for all $g\in G$ (`resLam_delInv`).*
2. *For every $F\in O_0[X_q:q\in\iota]$, $\mathrm{toLam}_{\iota'}\bigl(\mathrm{MvPolynomial.killCompl}\,h_e\,F\bigr)=\mathrm{resLam}(i,M,e)\bigl(\mathrm{toLam}_\iota\,F\bigr)$ (`resLam_toLam`).*

*(Lean: `resLam`, `resLam_of`, `resLam_delAll`, `resLam_delInv`, `resLam_gen_eq`, `resLam_toLam`, `resLam_surjective`, `ContinuousCocycleChangeScalarsBack.lean:339–403`.)*

*Proof.* (1) Given $y\in\Delta_{\iota'}=(\iota'\to\mathbb Z/\ell^M)$, extend $y$ to $x\in\Delta_\iota$ by $x(e(q'))=y(q')$ on $\operatorname{range}(e)$ (well-defined because $e$ is injective) and $x(q)=0$ outside $\operatorname{range}(e)$; then $x\circ e=y$, so $\mathrm{resLam}([x])=[y]$, and `MonoidAlgebra.induction_on` extends surjectivity to all of $\Lambda_{\iota'}$ (`:395–403`). On group elements, $(\mathrm{delAll}\,d(g))\circ e=\mathrm{delAll}(d\circ e)(g)$, and `resLam` preserves inverses (`:356–365`).

(2) Both sides are $O_0$-algebra homomorphisms $O_0[X_q:q\in\iota]\to\Lambda_{\iota'}$, so `MvPolynomial.algHom_ext` reduces the identity to generators $X_q$ (`:384–386`). If $q=e(q')$, `killCompl` sends $X_{e(q')}\mapsto X_{q'}$ (`killCompl_rename_app`), which `toLam` maps to $[e_{q'}]-1=\mathrm{resLam}([e_{e(q')}]-1)$ by injectivity of $e$ (`:376–380,387–390`). If $q\notin\operatorname{range}(e)$, `killCompl` sends $X_q\mapsto0$, while $(e_q\circ e)(q')=0$ for all $q'\in\iota'$, so $\mathrm{resLam}([e_q]-1)=[1]-1=0$ (`:381–382,391–393`). $\square$

###### Theorem 10.13ao (production of the initial positive-order seed `StartInd.start_of_resBound`) [Lean, read]

*Assume `TameQuotient_holds` (`[Lean]`). For every signature $s\in\mathrm{Sig}(i)$ satisfying `GalHyp bkP i s` and `ResBound bkP i s`, `Start bkP i s` holds (`start_of_galHyp`, and hence `start_of_resBound`, which ignores its `FirstPlace i s` argument).*

*Explicitly: let $n\le R$, $4rn+2<\ell^M$, `IsTameInertiaElementAtTwistPrime X i z`, `Small i s L z`, `PiLocalization₂ i M d A L z P` for $P:\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n\to\mathrm{Pl}_E$, right Frobenius pairs $(\phi_a,\phi'_a)$ ($a\in\mathrm{Fin}\,n$), and `Corank bkP i s φ φ' 1` hold. Then for every $Q$ with `IsQ P Q`, every $a>0$, every $\Phi\in M_a(\Lambda_{R,n})$ satisfying `Computes(s,M,d\circ P,Q,\Phi)`, there exist $b_1,b_2\in\mathrm{Fin}\,a$ such that every lift $F\in O_0[X_q]$ of $(\operatorname{adj}\Phi)_{b_1,b_2}$ has a multi-index $m$ with $\lvert m\rvert<4rn+1$, $m(\mathrm{inl}\,j)=0$ for all $n\le j<R$, and $F_m\in O_0^\times$.*

*(Lean: `StartInd.start_of_galHyp`, `StartInd.start_of_resBound`, `ContinuousCocycleChangeScalarsBack.lean:452–498`.)*

*Proof.* Set $e=\mathrm{Sum.map}\,(\mathrm{Fin.castLE}\,h_{n\le R})\,\mathrm{id}:\mathrm{Fin}\,n\sqcup\mathrm{Fin}\,n\hookrightarrow\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n$, which is injective (`:455–456`). Since $\ell\ge2$ and $4rn+2<\ell^M$, $M\ne0$ (`:457–460`). Filter $Q$ to $Q'=\{v\in Q:\exists q',\ \mathrm{Over}(P(e(q')),v)\}$; because `IsQ P Q` holds and $e$ maps into $\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n$, `IsQ` $(P\circ e,Q')$ holds (`:461–464`).

**Step 1 (`Position` for the restricted family).** Restricting `PiLocalization₂` along $e$ gives `Position i s M (P∘e) (d∘P∘e) φ φ'` (`:465–471`): `SlopeTestRemainingChoices` at $\varnothing$ drops $v\notin A$ and uses injectivity of $e$ for pairwise non-conjugacy; left Frobenius congruences into $zL$ restrict to $\mathrm{Fin}\,n$; for $a,b'\in\mathrm{Fin}\,n$, $(\mathrm{castLE}\,b').1=b'.1$ preserves the Kronecker equation $d_{P(\mathrm{inl}(\mathrm{castLE}\,b'))}(\sigma)=\mathrm{ofAdd}(\delta_{a,b'})$; and $\mathrm{Dec}_v(P(\mathrm{inr}\,a))\le L$ together with `Small` gives residual triviality on the $n$ right decomposition groups.

**Step 2 (Scalar descent of `Computes`).** By Lemma 10.13an(1), $\pi=\mathrm{resLam}(i,M,e):\Lambda_{R,n}\twoheadrightarrow\Lambda_{n,n}$ is surjective and maps $\mathrm{delInv}(d\circ P)$ to $\mathrm{delInv}(d\circ P\circ e)$. By Lemma 10.13am, $\mathrm{selOn}$ is unchanged on shrinking $Q$ to $Q'$ for every discrete $\ell$-power torsion $\Lambda_{n,n}$-module $B$. Lemma 10.13al(2) therefore gives `Computes` $\bigl(s,M,d\circ P\circ e,Q',\pi(\Phi)\bigr)$ (`:472–481`).

**Step 3 (Applying corank-one `ResBound` and lifting via `killCompl`).** With $4rn+2<\ell^M$, `Position`, `IsQ` $(P\circ e,Q')$, `Computes` for $\pi(\Phi)$, and `Corank` $1$, the second conjunct of `ResBound` (Proposition 10.15 in §10.4.8) yields $a=0$ or indices $b_1,b_2\in\mathrm{Fin}\,a$ such that every lift $F'\in O_0[X_{q'}:q'\in\iota']$ of $(\operatorname{adj}\pi(\Phi))_{b_1,b_2}$ has a multi-index $m'$ with $\lvert m'\rvert<4rn+1$ and $F'_{m'}\in O_0^\times$ (`:482`). Given any lift $F\in O_0[X_q:q\in\iota]$ with $\mathrm{toLam}_\iota\,F=(\operatorname{adj}\Phi)_{b_1,b_2}$, Lemma 10.13an(2) and `RingHom.map_adjugate` give
$$\mathrm{toLam}_{\iota'}\bigl(\mathrm{killCompl}\,h_e\,F\bigr)=\mathrm{resLam}\bigl((\operatorname{adj}\Phi)_{b_1,b_2}\bigr)=\bigl(\operatorname{adj}\pi(\Phi)\bigr)_{b_1,b_2}$$
(`:483–485`). Thus $F'=\mathrm{killCompl}\,h_e\,F$ has a unit coefficient $F'_{m'}\in O_0^\times$ with $\lvert m'\rvert<4rn+1$. Push $m'$ forward to $m=m'.\mathrm{mapDomain}\,e:(\mathrm{Fin}\,R\sqcup\mathrm{Fin}\,n)\to_0\mathbb N$ (`:486`). Then:
- $\lvert m\rvert\le\lvert m'\rvert<4rn+1$ (`Finsupp.degree_mapDomain`, `:487–488`);
- for $j\in\mathrm{Fin}\,R$ with $n\le j.1$, $\mathrm{inl}\,j\notin\operatorname{range}(e)$ (since $(\mathrm{castLE}\,q).1=q.1<n\le j.1$ and $\mathrm{inr}\,q\ne\mathrm{inl}\,j$), so $m(\mathrm{inl}\,j)=0$ (`Finsupp.mapDomain_of_notMem_range`, `:489–494`);
- by Mathlib's `MvPolynomial.coeff_killCompl`, $F_m=(\mathrm{killCompl}\,h_e\,F)_{m'}=F'_{m'}\in O_0^\times$ (`:495`).

Finally, `start_of_resBound` (`:497–498`) is the one-line wrapper `fun D N X bkP i s hG _ hRB => start_of_galHyp D N X bkP i s hG hRB`. $\square$

##### Return to `TwoBound.thmC_of_parts`, `OrdBound`, and Theorem 10.13ae [Lean, read]

Tracing the output back up the main-path spine closes the positive-order seed link left open in §10.4.7.5:

1. In `bound_mod_two_of_hypothesis` (`BoundModTwoUniformizerAtTwoOfChebotarev.lean:32`), `StartInd.start_of_resBound` is curried with `ScalarFrob.firstPlace` (ignored) and `ResOrder.resBound` (supplied by `ScalarFrob.firstHalf`, `ResRecip.reciprocity`, and `EqDim`) to pass $\forall s,\ \mathrm{GalHyp}\,s\Rightarrow\mathrm{Start}\,s$ into `TwoBound.thmC_of_parts`.
2. In `TwoBound.thmC_of_parts` (`AddValLeOfNotMem.lean:110–137`), Lemma 10.13ak(2) (`SmallSub.exists_small`, wrapped by `exists_openNormalSubgroup_under_inertia`) produces the single subgroup $L\le H$ satisfying `Small2 i (f j) M L z` for every signature $f(j)$ in the enumerated set $T$. Its first conjunct `(hL (f j) ...).1` is `Small i (f j) L z`, which feeds Theorem 10.13ao (`Start`) at $n=R_0$ and $R=R_0+t$ to produce $\mathrm{NFit}_{f(j)}(P_0,4rR_0+1)$, while the full `Small2` certificate (with $(T_s(g)-I_r)_{ab}\in I$) is passed unchanged to `Step` and `Grow` in Proposition 10.18 (§10.4.9).
3. After $t$ steps of Proposition 10.18, `TwoBound.thmC_of_parts` delivers `ThmC bkP` (`OrdBound bkP i (v_0(\ell^\nu))` for $\nu>0$), which Theorem 10.13ae (`§10.4.7.4`) combines with `ResidualBoundOddPrimes bkP` ($\nu=0$), `ThmS`, and `SelmerLengthsByDeterminant` to produce `GaloisSideTwistedSelmerAuxiliaryPrimes bkP`, feeding `partAT` and `GoodTw` in Proposition 10.13af.

##### Remarks, source map, and reading boundary

*Remark 1 (classical comparisons) [Expository].*

- *Non-flat base change vs. Shapiro/pullback.* For a quotient $\pi:\Lambda\twoheadrightarrow\Lambda'$ with nonzero kernel $\mathfrak a$, a presentation $\Lambda^a\xrightarrow{\Phi}\Lambda^a\to\mathcal M\to0$ restricts on $\Lambda'$-modules $B$ via $\operatorname{Hom}_\Lambda(\mathcal M,B)\cong\ker(\Phi\mid B_\pi^a)=\ker(\pi(\Phi)\mid B^a)$, avoiding the $\operatorname{Tor}_1^\Lambda(\Lambda',-)$ obstruction to flat base change ([Stacks Project, §10.39, Tag 00H9](https://stacks.math.columbia.edu/tag/00H9)). On continuous Galois cohomology ([NeukirchSchmidtWingberg2008](../sources/SOURCES.md#6-literature), Ch. I, §2 and Ch. II), this corresponds to functoriality in discrete coefficient modules whose underlying continuous $G$-sets coincide; the one place where surjectivity of $\pi$ does genuine work beyond additive functoriality is preserving the local Bloch–Kato $\Lambda$-submodule span above $\ell$ (`chLoc_mem_bkOn`) and upgrading module linearity (`exists_equiv_of_surjective`).
- *Tame inertia relation and Frobenius eigenvalues.* The commutator congruence $\phi\gamma\phi^{-1}\equiv\gamma^{N(v)}$ modulo prime-to-$\ell$ inertia in `unrAt_eq_top` is the pro-$\ell$ projection of classical tame ramification ([SerreLocalFields](../sources/SOURCES.md#6-literature), Ch. IV, §2, Corollaries 1–4, and [NeukirchSchmidtWingberg2008](../sources/SOURCES.md#6-literature), Theorem 7.5.3). Raising $\phi$ to $\ell^M$ eliminates the finite $\ell$-power character twist $\mathrm{delInv}\,d'(\phi)$ without destroying $\bar d_z\ne1$, because the $p$-power Frobenius endomorphism of a characteristic-$p$ field is injective (`sub_pow_char_pow`).
- *Adjugates and Fitting ideals.* Functoriality of $\operatorname{adj}\Phi$ under arbitrary commutative ring maps (`RingHom.map_adjugate`) and the identity $\Phi\cdot\operatorname{adj}\Phi=(\det\Phi)I_a$ over non-reduced rings such as $A=(O_0/I)[t]/(t^h)$ follow from universal polynomial identities over $\mathbb Z[x_{ij}]$ ([Stacks Project, Lemma 10.15.5, Tag 07DQ](https://stacks.math.columbia.edu/tag/07DQ)), matching the presentation-invariant first Fitting ideal $\operatorname{Fit}_1$ generated by $(a-1)\times(a-1)$ minors ([Stacks Project, §15.8, Tag 07Z6](https://stacks.math.columbia.edu/tag/07Z6)).

*Remark 2 (Mathlib inputs).* At the pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`, `StartInd` calls `RingHom.map_adjugate` and `AlgHom.map_adjugate` (`Mathlib/LinearAlgebra/Matrix/Adjugate.lean:327–339`), `MvPolynomial.killCompl`, `killCompl_rename_app`, and `coeff_killCompl` (`Mathlib/Algebra/MvPolynomial/Rename.lean:132–144,184–197`), `Submodule.apply_mem_span_image_iff_mem_span` (`Mathlib/LinearAlgebra/Span/Basic.lean:268–271`), `sub_pow_char_pow` (`Mathlib/Algebra/CharP/Lemmas.lean:263`), and `Finsupp.mapDomain_of_notMem_range` (`Mathlib/Data/Finsupp/Basic.lean:285–288`).

*Remark 3 (scope of verification).* We read every line of `ContinuousCocycleChangeScalarsBack.lean` (`1–502`), `TameInertiaElementActsByScalar.lean` (`1–63`), and `ExistsOpenNormalSubgroupUnderInertia.lean` (`1–188`), together with their statement wrappers and definitions, against the pinned archive `lean.tar.gz` (SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, re-verified byte-for-byte on 2026-11-25) and built the book with `mdbook build`. Neither source reading nor `mdbook build` is a Lean kernel verification; the examples in Examples 10.13ah–10.13aj are algebraic models certified by exact arithmetic (`verify_start_seed.py`), not instances of `NTw`.

| Item | Pinned archive source | Level here |
|---|---|---|
| `unrAt_eq_top`, `exists_equiv_of_surjective`, `z1Ch`, `h1Ch`, `h1Ch_bijective`, `continuousCocycleChangeScalarsBack`, `mulVec_map`, `repOn_eq`, `ch`, `ch_res`, `chLoc`, `chLoc_mem_bkOn`, `ch_mem_selOn`, `computes_map`, `tbar`, `tbar_of_conj`, `tbar_frob`, `eq_zero_of_scalar`, `resLam`, `resLam_delInv`, `delInv_pow`, `resLam_toLam`, `resLam_surjective`, `unr_first`, `selOn_eq`, `start_of_galHyp`, `start_of_resBound` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousCocycleChangeScalarsBack.lean:18–500` | [Lean, read] (new full R3) |
| `TameScalar.not_mem_placesOver`, `isUnit_inv_sq_sub_one`, `isUnit_sub_one`, `exists_scalar_tmat_of_tame_inertia`; wrapper `tameInertiaElement_acts_by_scalar` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TameInertiaElementActsByScalar.lean:8–62`; `TameInertiaElementActsByScalarStatement.lean:7` | [Lean, read] (new full R3) |
| `SmallSub.exists_fix_roots`, `normal_of_comm`, `comm_mem_ker`, `isOpen_ideal`, `l_ne_zero`, `l_mem`, `exists_eps`, `pD_not_mem`, `exists_kerT`, `exists_small`; wrapper `exists_openNormalSubgroup_under_inertia` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOpenNormalSubgroupUnderInertia.lean:15–185`; `ExistsOpenNormalSubgroupUnderInertiaStatement.lean:7` | [Lean, read] (new full R3) |
| `h1Map`, `h1Map_id`, `h1Map_comp` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/H1MapSubgroup.lean:16–30` | [Lean, read] |
| Definitions `idl`, `Small2`, `PiLocalization₂`, `NF`, `NFit`, `Ext`, `Start`, `Grow`, `Step`; `Small`, `Position`, `Corank`, `ResBound`, `FirstPlace`; `bkOn`, `selOn`, `unrAt`, `bkCond`, `SelAll` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/Small2.lean:13–57`; `IsDualDualRep.lean:21–24,118–158`; `src/Formalism/SharpRestriction/LevelLetterCocycles/BlochKatoPhases.lean:64–95`; `src/Formalism/GaloisCohomology/Statement.lean:38–63` | [Lean, read] (definitions) |
| Inherited consumers and propositions (`TwoBound.thmC_of_parts` recurrence `AddValLeOfNotMem.lean:28–85`, `ResOrder.resBound`, `ChosenPrimes.stepAB`, `galois_twisted_selmer_auxprimes_of_matrix_and_bounds`) | §§10.4.7.4–10.4.7.5, §10.4.8 (Prop. 10.15), §10.4.9 (Prop. 10.18), §10.4.13 | [Lean, read] (inherited, cited only) |
| Named inputs kept at their boundary: `TameQuotient_holds`; `exists_isFrob`; `exists_frob_of_conj`, `isPlaceOver_moveVal_cc`, `cConj_mem_ine`; `cycZ_of_isFrob`, `cycZ_toZModPow_eq`, `continuous_cycZ`; `Growth.grow`, `NewPrime.step`, `ChooseH`, `EqDim`, `SpanOdd`, `SpanTwo`, `ScalarFrob.firstHalf`/`firstPlace`, `ResRecip.reciprocity`, `oneMatrix_of_galoisCohomology` (`ThmS`) | `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsCoprimePowOfMemIneKer.lean:598`; `src/ReciprocityTheory/GaloisValuations/Global.lean:345`; `IsPlaceOverMoveValCc.lean:119,137,160`; `ContinuousCycMod.lean:102,155,175`; `BoundModTwoUniformizerAtTwoOfChebotarev.lean:25–35` | [Lean] (retained boundary; `Grow`/`Step` in §§10.4.9–10.4.11, `ThmS` in §10.4.12) |

#### 10.4.7.11 Lifting residual cocycles to the Bloch–Kato lattice

##### Motivation [Expository]

The residual Selmer comparison in the [auxiliary-twist argument](#1047-where-does-adm2-come-from) needs exact orthogonal complements at every place $v\mid\ell$. The original and Tate-dual local conditions $\mathrm{bkOn}_k$ and $\mathrm{bkOn}'_k$ are spans of reductions of integral Bloch–Kato finite cocycles in their respective $H^1$ spaces. Their cup takes values in $H^2(G_v,k(\bar\epsilon_0))$. The residual equal-dimension manuscript (§10.4.7.10) uses `bkOn_orthogonal` and `mem_bkOn_of_orthogonal` for the two inclusions. Both call the integral lifting criterion proved below. The [source map](../sources/SOURCES.md#chapter-10-blochkato-lattice-lifting-and-integral-annihilators) identifies the four intervening manuscripts and the sources of these calls.

Write $W'=V^\ast(1)/L^\ast(1)$ for the quotient of the Tate dual by the full dual lattice. In residue characteristic $p$ with $p$-adic coefficients, Bloch and Kato define the rational finite condition by the crystalline-period kernel and the integral condition by inverse image. Their Proposition 3.8 gives the finite-condition annihilators under local Tate duality with $V$ de Rham. Rubin uses the rational image to define the divisible condition, then identifies its inverse image on $W'[\varpi]\simeq L^\ast(1)/\varpi L^\ast(1)$ with the reduction image of the integral finite condition. His integral and finite torsion orthogonality statements at $p$ assume rational orthogonality. Here the task is to produce an actual integral cocycle representing the specified residue cocycle. [Bloch–Kato, (3.7.2)–(3.7.3) and Proposition 3.8](https://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKTamagawa.pdf) · [Rubin, Remark 1.3.6, Lemma 1.3.8(i), and Proposition 1.4.3(c)(i)–(ii)](https://wstein.org/people/rubin/book/hEulerSystems.pdf)

The lift uses the same DVR $O$ on both sides. Divide a coordinate lift $y$ by a uniformizer $\varpi$ and reduce in the full quotient $V'/L'$. The residual cocycle identity becomes an exact locally constant cocycle identity in that quotient. Clause `.1` of `bkBCore` detects its finite condition by a cup test against every integral finite cocycle on the original side. Absorbing a quotient coboundary into a rational finite cocycle $z$ gives the pointwise integral error $t=\varpi^{-1}y-z$. Multiplying back gives the desired finite representative $y'=y-\varpi t=\varpi z$. The [following subsection](#104712-integral-local-duality-and-the-two-finite-condition-annihilators) explains the conditional supply of `bkBCore`. The residual consumer invokes `LocalH2Injective.h2_inj` after the lift criterion.

##### Example 10.13eg. An odd-prime rank-two DVR lattice with nonzero residual local $H^0$ [Expository]

Let $H = \langle \sigma, \tau \mid \sigma^3 = \tau^3 = 1,\ \sigma\tau = \tau\sigma \rangle \cong C_3 \times C_3$, $O = \mathbb Z_{(3)} \subset LL = \mathbb Q$ with uniformizer $\varpi = 3$, maximal ideal $\mathfrak m_O = 3O$, residue field $k = \mathbb F_3$, divisible quotient $\mathrm{KmodO}(O) = \mathbb Q/\mathbb Z_{(3)}$, rank $r = 2$, and trivial character $\chi = 1$. On $g = \sigma^a \tau^b$ ($a, b \in \{0, 1, 2\}$), set $M(\sigma^a \tau^b) = A^a$ and $M'(\sigma^a \tau^b) = B^a$, where
$$
A = \begin{pmatrix} 1 & 1 \\ -3 & -2 \end{pmatrix}, \qquad
A^2 = \begin{pmatrix} -2 & -1 \\ 3 & 1 \end{pmatrix}, \qquad
B = A^{-t} = \begin{pmatrix} -2 & 3 \\ -1 & 1 \end{pmatrix}, \qquad
B^2 = \begin{pmatrix} 1 & -3 \\ 1 & -2 \end{pmatrix}.
$$
Since $\operatorname{tr}(A) = -1$ and $\det(A) = 1$, Cayley–Hamilton gives $A^2 + A + I_2 = 0$, hence $A^3 = B^3 = I_2$ and $M(g)^t M'(g) = I_2 = \chi(g)I_2$. Over $\mathbb Q$, $\det(A - I_2) = \det(B - I_2) = 3 \ne 0$, so $H^0(H, \mathbb Q^2(M)) = H^0(H, \mathbb Q^2(M')) = 0$. Modulo $3$, however, $\overline A = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$ and $\overline B \equiv \begin{pmatrix} 1 & 0 \\ 2 & 1 \end{pmatrix}$, while $\tau$ acts trivially, so *both* local residual invariant spaces are nonzero of dimension $1$:
$$
H^0(H, \mathbb F_3^2(\overline M)) = \mathbb F_3 \begin{pmatrix} 1 \\ 0 \end{pmatrix}, \qquad
H^0(H, \mathbb F_3^2(\overline{M'})) = \mathbb F_3 \begin{pmatrix} 0 \\ 1 \end{pmatrix}.
$$

Because $|H| = 9$ is invertible in $\mathbb Q$, $Z^1(H, \mathbb Q^2) = B^1(H, \mathbb Q^2)$ has $\mathbb Q$-dimension $2$ on each side; take $Z^1_f = B^1(H, \mathbb Q^2)$ ($d_v = 0$). For $m = (m_1, m_2)^t \in \mathbb Q^2$, $(A - I_2)m = (m_2, -3(m_1 + m_2))^t \in O^2$ if and only if $m_1 \in \frac{1}{3}O$ and $m_2 \in O$. Hence the integral finite cocycle lattice $Z^1_f(H, L) = O d_1 \oplus O d_2$ is generated by the non-coboundary torsion cocycle $d_1(\sigma^a \tau^b) = (A^a - I_2)(\frac{1}{3}, 0)^t$ — taking values $(0, 0)^t, (0, -1)^t, (-1, 1)^t$ for $a = 0, 1, 2$ — and the integral coboundary $d_2(\sigma^a \tau^b) = (A^a - I_2)(0, 1)^t$ — taking values $(0, 0)^t, (1, -3)^t, (-1, 0)^t$. Notice $\dim_{\mathbb F_3}\mathrm{bkOn}_k = 2 - (2 - 1) = 1$, spanned by $[\bar d_1]$, matching $\dim_k L_v(k) - h^0(H, M_k) = 1 - 1 = 0$. Dually, $(B - I_2)m' = (3(m'_2 - m'_1), -m'_1)^t \in O^2$ gives $Z^1_f(H, L') = O y'_1 \oplus O y'_2$ with $y'_1(\sigma^a \tau^b) = (B^a - I_2)(0, \frac{1}{3})^t$ — taking values $(0, 0)^t, (1, 0)^t, (-1, -1)^t$ for $a = 0, 1, 2$ — and $y'_2(\sigma^a \tau^b) = (B^a - I_2)(1, 0)^t$ — taking values $(0, 0)^t, (-3, -1)^t, (0, 1)^t$. Across all $27$ cocycles in $Z^1(H, \mathbb F_3^2(\overline{M'}))$ ($\dim_{\mathbb F_3} Z^1 = 3$), exactly $9$ ($\dim_{\mathbb F_3} = r + d_v = 2$) lift to $Z^1_f(H, L')$. On $W' = (\mathbb Q/\mathbb Z_{(3)})^2$, surjectivity of $B - I_2$ absorbs $c(\sigma)$ into $\mathrm{BD}(L')$, while $\sigma\tau = \tau\sigma$ and $\tau^3 = 1$ force $c(\tau) \in \{0, \frac{1}{3}, \frac{2}{3}\} e_2$, Each quotient cocycle is thus uniquely a multiple of $[\varpi^{-1}y_{mathrm{bad}}]$ modulo divisible coboundaries, where $y_{mathrm{bad}}(sigma^a	au^b)=b e_2$. Testing that multiple against $d_1$ detects its coefficient by the antisymmetric cup value computed below. The divisible coboundaries pair to coboundaries: for $c=delta\bar m$, the cup is the differential of $gmapsto-[d(g)cdot M'(g)m]$. This gives the first annihilator identity for this finite model.

Now test a genuine mod-$3$ cochain $y_{\mathrm{good}} = y'_{\mathrm{exact}} + 3 u$, where $y'_{\mathrm{exact}}(g) = y'_1(g) + y'_2(g) = (B^a - I_2)(1, \frac{1}{3})^t$ takes values $(0, 0)^t, (-2, -1)^t, (-1, 0)^t$ for $a = 0, 1, 2$, and $u(\tau) = (0, 1)^t$, $u(\sigma\tau) = (1, -1)^t$, $u(g) = (0, 0)^t$ otherwise. Thus $y_{\mathrm{good}}(\tau) = (0, 3)^t$, $y_{\mathrm{good}}(\sigma) = y_{\mathrm{good}}(\sigma\tau^2) = (-2, -1)^t$, $y_{\mathrm{good}}(\sigma\tau) = (1, -4)^t$, $y_{\mathrm{good}}(\sigma^2\tau^b) = (-1, 0)^t$, and $y_{\mathrm{good}}(1) = y_{\mathrm{good}}(\tau^2) = (0, 0)^t$. It is *not* an exact $O$-cocycle: at $(\sigma, \tau)$,
$$
y_{\mathrm{good}}(\sigma\tau) - \bigl(y_{\mathrm{good}}(\sigma) + B y_{\mathrm{good}}(\tau)\bigr)
= \begin{pmatrix} 1 \\ -4 \end{pmatrix} - \begin{pmatrix} 7 \\ 2 \end{pmatrix}
= \begin{pmatrix} -6 \\ -6 \end{pmatrix} \in 3O^2 \setminus \{0\}.
$$
Dividing by $\varpi = 3$ sends $(-6, -6)^t$ to $(-2, -2)^t \in O^2$, so $c(g) = [\frac{1}{3}y_{\mathrm{good}}(g)] = [z(g)] \in W'$ is an exact divisible cocycle with rational finite witness $z(\sigma^a \tau^b) = \frac{1}{3}y'_{\mathrm{exact}}(\sigma^a \tau^b) = (B^a - I_2)(\frac{1}{3}, \frac{1}{9})^t$. For $d_k(g) = (M(g) - I_2)m_k$, the perturbation $3u$ contributes $d_k(g)\cdot M'(g)u(h) \in O$, which vanishes in $\mathrm{KmodO}(O)$, and $M(g)^t M'(g) = I_2$ yields the exact $\mathrm{KmodO}(O)$-coboundaries $f^{(k)}(g) = [m_k \cdot z(g)]$:
$$
f^{(1)}(\sigma^a \tau^b) = \begin{cases} 0 & a = 0, \\ \frac{7}{9} & a = 1, \\ \frac{8}{9} & a = 2, \end{cases}
\qquad
f^{(2)}(\sigma^a \tau^b) = \begin{cases} 0 & a = 0, \\ \frac{2}{3} & a = 1, \\ 0 & a = 2. \end{cases}
$$
At $(g, h) = (\sigma, \sigma)$, $[\frac{1}{3} d_1(\sigma)\cdot B y_{\mathrm{good}}(\sigma)] = [\frac{1}{3}(0, -1)\cdot(1, 1)^t] = \frac{2}{3}$, matching $f^{(1)}(\sigma) - f^{(1)}(\sigma^2) + f^{(1)}(\sigma) = \frac{7}{9} - \frac{8}{9} + \frac{7}{9} = \frac{2}{3}$. Crucially, $f^{(1)}$ requires *$9$-torsion* in $\mathrm{KmodO}(O)$: for any $3$-torsion cochain $f_0 : H \to \frac{1}{3}\mathbb Z/\mathbb Z$, $\sum_{a=0}^2 (d^1 f_0)(\sigma^a, \sigma) = 3 f_0(\sigma) \equiv 0 \pmod 1$, whereas $\sum_{a=0}^2 [\frac{1}{3} d_1(\sigma^a)\cdot B^a y_{\mathrm{good}}(\sigma)] = 0 + \frac{2}{3} + \frac{2}{3} \equiv \frac{1}{3} \ne 0$. Subtracting $\varpi$ times $t(g) = \frac{1}{3}y_{\mathrm{good}}(g) - z(g) = u(g) \in O^2$ recovers $y'(g) = y_{\mathrm{good}}(g) - 3 t(g) = y'_{\mathrm{exact}}(g) \in Z^1_f(H, L')$. By contrast, the residual cocycle $y_{\mathrm{bad}}(\sigma^a \tau^b) = (0, b)^t$ satisfies the mod-$3$ cocycle law because $B e_2 = (3, 1)^t \equiv e_2 \pmod 3$, yet $[\frac{1}{3} d_1(\sigma)\cdot B y_{\mathrm{bad}}(\tau)] - [\frac{1}{3} d_1(\tau)\cdot y_{\mathrm{bad}}(\sigma)] = \frac{2}{3} - 0 = \frac{2}{3} \ne 0$ in $\mathrm{KmodO}(O)$, while every coboundary on abelian $H$ with $\chi = 1$ is symmetric on $(\sigma, \tau)$; correspondingly, every $y' \in Z^1_f(H, L')$ has $y'(\tau) = (0, 0)^t \not\equiv (0, 1)^t \pmod 3$.

##### Example 10.13eh. A dyadic twisted DVR lattice with nontrivial cyclotomic character [Expository]

Use the finite Galois quotient $H = \operatorname{Gal}(\mathbb Q_2(i, \sqrt{5})/\mathbb Q_2) = \langle \sigma, \tau \rangle \cong C_2 \times C_2$, where $\sigma(i) = -i$, $\sigma(\sqrt{5}) = \sqrt{5}$ and $\tau(i) = i$, $\tau(\sqrt{5}) = -\sqrt{5}$. Over $O = \mathbb Z_{(2)} \subset LL = \mathbb Q$ with $\varpi = 2$, $k = \mathbb F_2$, $\mathrm{KmodO}(O) = \mathbb Q/\mathbb Z_{(2)}$, and $r = 1$, the action on fourth roots of unity, the unramified quadratic character, and its dual twisted by that fourth-root action give the sign characters
$$
\chi(\sigma^a \tau^b) = (-1)^a, \qquad
M(\sigma^a \tau^b) = (-1)^b, \qquad
M'(\sigma^a \tau^b) = (-1)^{a+b},
$$
so $M(g) M'(g) = \chi(g)$ with $\chi(\sigma) = -1 \ne 1$. Again $H^0(H, \mathbb Q(M)) = H^0(H, \mathbb Q(M')) = 0$, whereas modulo $2$ both local residual $H^0$ spaces equal $\mathbb F_2 \ne 0$. On $(1, \sigma, \tau, \sigma\tau)$, $Z^1_f(H, L) = O d_0$ is generated by $d_0 = (0, 0, 1, 1) = (M - 1)(-\frac{1}{2})$, and $Z^1_f(H, L') = O y'_0$ by $y'_0 = (0, -1, -1, 0) = (M' - 1)(\frac{1}{2})$; across all $4$ residual cocycles in $Z^1(H, \mathbb F_2)$, exactly $2$ lift to $Z^1_f(H, L')$.

Perturb $y'_0$ by $2 u$ with $u = (1, 1, 0, 1)$ to obtain $y_{\mathrm{good}} = (2, 1, -1, 2)$, whose integral cocycle defect at $(1,1)$ is $y_{\mathrm{good}}(1) - 2 y_{\mathrm{good}}(1) = -2 \in 2O \setminus \{0\}$. At $(\sigma,\sigma)$ the integral defect is $2$. The integral coboundaries on the original side are $2O d_0$. Dividing by $\varpi = 2$ yields $z = \frac{1}{2}y'_0 = (0, -\frac{1}{2}, -\frac{1}{2}, 0) = (M' - 1)(\frac{1}{4})$ and the *$4$-torsion* $\chi$-coboundary witness $f = (0, \frac{1}{4}, \frac{1}{4}, 0)$ in $\mathrm{KmodO}(O)$:
- at $(g, h) = (\tau, \sigma)$, where $\chi(\tau) = +1$, $[\frac{1}{2} d_0(\tau) M'(\tau) y_{\mathrm{good}}(\sigma)] = [\frac{1}{2}\cdot 1 \cdot (-1)\cdot 1] = \frac{1}{2}$ and $\chi(\tau)f(\sigma) - f(\sigma\tau) + f(\tau) = \frac{1}{4} - 0 + \frac{1}{4} = \frac{1}{2}$;
- at $(g, h) = (\sigma\tau, \sigma)$, where $\chi(\sigma\tau) = -1$, $[\frac{1}{2} d_0(\sigma\tau) M'(\sigma\tau) y_{\mathrm{good}}(\sigma)] = \frac{1}{2}$ and $\chi(\sigma\tau)f(\sigma) - f(\tau) + f(\sigma\tau) = -\frac{1}{4} - \frac{1}{4} + 0 \equiv \frac{1}{2} \pmod 1$;
- at $(g, h) = (\sigma, \tau)$, where $\chi(\sigma) = -1$, $[\frac{1}{2}\cdot 0] = 0$ and $\chi(\sigma)f(\tau) - f(\sigma\tau) + f(\sigma) = -\frac{1}{4} - 0 + \frac{1}{4} = 0$.

No $2$-torsion cochain $f_0 : H \to \frac{1}{2}\mathbb Z/\mathbb Z$ can solve this, since $\chi = \pm 1$ acts trivially on $\frac{1}{2}\mathbb Z/\mathbb Z$, so its differential is symmetric in $(\tau,\sigma)$ and $(\sigma,\tau)$. The displayed cup values there differ by $1/2$. The integral error $t = \frac{1}{2}y_{\mathrm{good}} - z = (1, 1, 0, 1)$ reconstructs $y' = y_{\mathrm{good}} - 2 t = (0, -1, -1, 0) \in Z^1_f(H, L')$. Meanwhile, for the unliftable cocycle $y_{\mathrm{bad}} = (0, 0, 1, 1)$, expanding $d^1_\chi f(g, h) = \chi(g)f(h) - f(gh) + f(g)$ shows that
$$
\mathcal I_\chi(w) := w(\tau, \tau) + w(\sigma, \sigma\tau) + w(\sigma\tau, \sigma) - w(\sigma, \sigma)
$$
vanishes identically on every $\chi$-coboundary $d^1_\chi f$, whereas $\mathcal I_\chi([\frac{1}{2} d_0(\cdot)M'(\cdot)y_{\mathrm{bad}}(\cdot)]) = \frac{1}{2} + 0 + 0 - 0 = \frac{1}{2} \ne 0$ in $\mathrm{KmodO}(O)$. Every integral finite cocycle is a multiple of $y'_0$ and vanishes at $\sigma\tau$, where $y_{\mathrm{bad}}$ takes the residue $1$.

##### Definitions [Lean, read]

Fix `PeriodData G Qp K₀ K B BdR` (`PD`), packaging a group $G$, fields $Qp \subseteq K_0 \subseteq K$ finite-dimensional over $Qp$, period rings $B$ ($B_{\mathrm{cris}}$) and $BdR$ ($B_{\mathrm{dR}}$) with $G$-actions `actB`, `actdR`, Frobenius $\varphi$, filtration `Fil`, and the cyclotomic character $\mathrm{PD}.\chi : G \to Qp^\times$ (`src/Formalism/WeaklyAdmissibleFiltrations/Statement.lean:75–112`). For a field extension $LL$ of $Qp$, `cycLL PD LL : G →* LLˣ` maps $\mathrm{PD}.\chi(g)$ into $LL^\times$ via $Qp \to LL$ (`src/Formalism/SharpRestriction/LevelLetterCocycles/LocCoh.lean:25–26`), and `charRep (cycLL PD LL)` is the rank-one $LL$-representation where $g$ scales by `cycLL PD LL g`.

1. **Coefficient package `GoodO Qp LL O` and $\mathrm{KmodO}(O)$.** For a commutative domain $O$ with maximal ideal $\mathfrak m_O = \mathrm{maximalIdeal}(O)$, write $\mathrm{residue}_O : O \to O/\mathfrak m_O$ for the residue map and $\mathrm{KmodO}(O) := \operatorname{Frac}(O)/\operatorname{im}(O \to \operatorname{Frac}(O))$ for the divisible torsion $O$-module with quotient map `Submodule.Quotient.mk` (`src/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:38–40`). Given a topological field $Qp$, a topological $Qp$-algebra field $LL$, and an $O$-algebra structure on $LL$, `GoodO (Qp := Qp) LL O` asserts that $O$ is a domain with `IsDiscreteValuationRing O` and `IsFractionRing O LL`, together with `FiniteDimensional Qp LL`, `IsModuleTopology Qp LL`, `IsTopologicalRing LL`, and `IsOpen (Set.range (algebraMap O LL))` (`LocCoh.lean:28–32`). Write $\iota : O^r \to LL^r$ for coordinatewise $\operatorname{algebraMap} O\,LL$ (`BKLatticeCochain.incl`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LiftBlochKatoCocycleIffOrthogonalLattice.lean:23–25`).
2. **Lattices, Bloch–Kato finite cocycles, de Rham dimension, and perfect integral pairing.** For an $LL$-linear $G$-representation $\rho$ on $V$ (bundled with $LL$-module topology and orbit continuity $\forall x,\ \mathrm{Continuous}(g \mapsto \rho(g)x)$ inside `GRep G Qp LL O`, `LocCoh.lean:36–54`), `finiteCocycles PD ρ` ($Z^1_f(\mathrm{PD}, \rho)$) is the $LL$-submodule of `continuousCocycles ρ` consisting of continuous cocycles $z : G \to V$ such that $\exists w \in V \otimes_{Qp} B,\ \forall g,\ z(g) \otimes 1 = \mathrm{actVB}_{\mathrm{PD},\rho}(g)w - w$ (`Statement.lean:125–126, 173–202`), and `IsDR PD ρ` means $\operatorname{finrank}_{LL} D_{\mathrm{dR}}(\mathrm{PD}, \rho) = \operatorname{finrank}_{Qp} K \cdot \operatorname{finrank}_{LL} V$ (`Statement.lean:134–135`; `LocCoh.lean:21–23`). An $O$-lattice $L : \mathrm{Lattice}\,(O := O)\,\rho$ is a $G$-stable, finitely generated, $O$-free submodule $L.T \subseteq V$ whose $LL$-span equals $\top$ (`Statement.lean:220–225`). Given lattices $L, L'$ in $\rho, \rho'$ and an $LL$-bilinear pairing $P : V \to_{LL} V' \to_{LL} LL$, `IsDualLat1 PD L L' P` (`LocCoh.lean:81–89`) asserts:
   - `IsDual1 PD ρ ρ' P`: $\chi$-equivariance $P(\rho(g)x, \rho'(g)y) = \mathrm{cycLL}\,\mathrm{PD}\,LL(g)\cdot P(x, y)$, left and right rational nondegeneracy on $V \times V'$, and $\operatorname{finrank}_{LL} V = \operatorname{finrank}_{LL} V'$; and
   - exact integral unimodularity: $\forall y \in V',\ y \in L'.T \iff \forall x \in L.T,\ \exists a \in O,\ P(x, y) = \operatorname{algebraMap} O\,LL(a)$.
3. **Divisible cohomology, section cup product, and `bkBCore`.** Write `latticeCocycles L` for continuous cocycles valued in $L.T$, `latticeFiniteCocycles PD L` for `latticeCocycles L ⊓ finiteCocycles PD ρ` (`Statement.lean:230–239`), `divisibleCocycles L'` for locally constant cocycles $c : G \to V'/L'.T$, `BD L'` for divisible coboundaries $g \mapsto \mathrm{actD}_{L'}(g)\bar m - \bar m$ ($\bar m \in V'/L'.T$), and `HfD PD L'` for the submodule sum $\operatorname{im}(Z^1_f(\mathrm{PD}, \rho') \to (G \to V'/L'.T)) \sqcup \mathrm{BD}(L')$ (`src/Formalism/WeaklyAdmissibleFiltrations/StatementTor.lean:103–128`). Using the non-canonical quotient section `liftD L' : V'/L'.T → V'` (`(Submodule.Quotient.mk_surjective L'.T c).choose`, `LocCoh.lean:111–112`), define the raw $LL$-valued section cup cochain
   $$
   \mathrm{cupLD}(L', P, d, c)(g, h) := P\bigl(d(g), \rho'(g)\,\mathrm{liftD}_{L'}(c(h))\bigr),
   $$
   and for an $O$-lattice $L_1$ in `charRep (cycLL PD LL)` write `CobO PD L1 z` when $(g, h) \mapsto [z(g, h)]_{LL/L_1.T}$ lies in `ReciprocityTheory.Def.B2 (repD L1) ⊤`, i.e., equals $\mathrm{repD}_{L_1}(g) f_G(h) - f_G(gh) + f_G(g)$ for a locally constant $f_G : G \to LL/L_1.T$ (`LocCoh.lean:99–109, 133–141`; `src/ReciprocityTheory/BasicDefinitions/AdRep.lean:10–15, 27–31, 45–46`). The deep local duality premise `bkBCore PD` asserts, for every $(LL, O)$ satisfying `GoodO`, every $L_1$ with $L_1.T = \operatorname{im}(\operatorname{algebraMap} O\,LL)$, every `A, A' : GRep G Qp LL O` with `IsDR PD A.ρ`, and every `IsDualLat1 PD LA LA' P`, both:
   - clause `.1`: $\forall c \in \mathrm{divisibleCocycles}(LA'),\ c \in \mathrm{HfD}(\mathrm{PD}, LA') \iff \forall d \in \mathrm{latticeFiniteCocycles}(\mathrm{PD}, LA),\ \mathrm{CobO}(\mathrm{PD}, L_1, \mathrm{cupLD}(LA', P, d, c))$;
   - clause `.2`: the dual characterization of `latticeFiniteCocycles PD LA` against `HfD PD LA'` (`LocCoh.lean:161–169`).
4. **Global-to-local bridge (`bkP`, `IsFCoc`).** In the global setup $(D, N, X, \mathrm{bkP})$ at twist $i$ and place $v \in \mathrm{placesOver}(E, \ell)$ (`hv`, $\ell = X.l(i)$, $O = X.O0(i)$), `Bw := bkP.br i v hv` is a `LocBridge` on the decomposition subgroup $\mathrm{DecV}\,N\,v = \operatorname{Dec}(N.\mathrm{plOm}_1(v)) \le G_E$: it provides finite extensions `Bw.Kw, Bw.LL : FinExt l` of $\mathbb Q_\ell$, period data $\mathrm{PD}_v = (D.\mathrm{loc}\,\ell).\mathrm{PD}(\mathrm{Bw.Kw})$ on $\mathrm{GK}(\mathrm{Bw.Kw})$, a topological group isomorphism `Bw.e : DecV N v ≃* GK(Bw.Kw)` intertwining the embedding `Bw.j : Ω →+* Om l` (`Bw.e_comm`), and a topological $\mathbb Z_\ell$-algebra isomorphism `Bw.eO : O ≃+* OL(Bw.LL)` (`Bw.eO_alg`, `Bw.eO_cont`, `Bw.eO_symm_cont`), inducing `Bw.toLL : O →+* Bw.LL.1` (`src/Formalism/SharpRestriction/LevelLetterCocycles/DataNLoc.lean:527–592, 710–711`; `BlochKatoPhases.lean:90–93, 126–134`). For $\sigma : G_E \to^\ast \mathrm{GL}_r(O)$, `repV bkP i v hv σ` acts on `Bw.LL.1^r` via `Bw.toLL` and `Bw.e.symm`, and `IsFCoc bkP i v hv σ y` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsFCocIff.lean:17–18`) is defined directly as $(g, a) \mapsto \mathrm{Bw.toLL}(y(\mathrm{Bw.e}^{-1}(g))_a) \in \mathrm{finiteCocycles}(\mathrm{PD}_v, \mathrm{repV}\,\sigma)$.

##### Lemma 10.13ei. Uniformizer division and saturation on standard lattices [Lean, read]

Assume `IsDomain O`, `IsDiscreteValuationRing O`, and `hinj : Function.Injective (algebraMap O LL)`, and let $\varpi \in O$ satisfy `Irreducible ϖ`.

1. $\operatorname{algebraMap} O\,LL(\varpi) \ne 0$, and for every representation $\rho$ of $G$ on $LL^r$ realized pointwise by integral matrices $M_g \in \mathrm{Mat}_r(O)$, the submodule $\operatorname{im}(\iota) \subseteq LL^r$ defines a valid lattice `stdLattice` ($G$-stable, finitely generated, $O$-free, with $LL$-span $\top$).
2. For every $u \in O^r$, $(\operatorname{algebraMap} O\,LL(\varpi))^{-1} \iota(u) \in \operatorname{im}(\iota)$ if and only if $u_a \in \mathfrak m_O$ for all $a \in \mathrm{Fin}\,r$. Consequently, for $u, u' \in O^r$, $[\varpi^{-1}\iota(u)] = [\varpi^{-1}\iota(u')]$ in $LL^r/\operatorname{im}(\iota)$ if and only if $u_a - u'_a \in \mathfrak m_O$ for all $a$.

*Proof.* Injectivity of $\operatorname{algebraMap} O\,LL$ makes $\iota$ injective and sends $\varpi \ne 0$ to a nonzero element of $LL$. Since $\iota(M_g z) = (M_g)_{LL}\,\iota(z)$ (`incl_mulVec`), $\operatorname{im}(\iota)$ is $G$-stable; it is finitely generated as the image of $O^r$, free via `LinearEquiv.ofInjective` on $\iota$, and spans $LL^r$ over $LL$ because each standard basis vector `Pi.single a 1` lies in $\operatorname{im}(\iota)$ (`mem_range_incl`). For claim 2, `hϖ.maximalIdeal_eq` gives $\mathfrak m_O = (\varpi)$. Coordinatewise, $(\operatorname{algebraMap} O\,LL(\varpi))^{-1}\operatorname{algebraMap} O\,LL(u_a) = \operatorname{algebraMap} O\,LL(o_a)$ holds in $LL$ if and only if $\operatorname{algebraMap} O\,LL(u_a) = \operatorname{algebraMap} O\,LL(\varpi o_a)$ (clearing $\operatorname{algebraMap} O\,LL(\varpi) \ne 0$), which by `hinj` is equivalent to $u_a = \varpi o_a \in \mathfrak m_O$. Applying this to $u - u'$ yields the quotient equivalence (`key`). (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LiftBlochKatoCocycleIffOrthogonalLattice.lean:23–76, 206–210`.) $\square$

##### Lemma 10.13ej. Absorption of divisible coboundaries into rational Bloch–Kato cocycles [Lean, read]

Let $\rho'$ be an $LL$-linear representation of $G$ on a topological $LL$-module $V'$ (`IsScalarTower Qp LL V'`, `ContinuousAdd V'`, `ContinuousConstSMul LL V'`) satisfying orbit continuity $\forall m \in V',\ \mathrm{Continuous}(g \mapsto \rho'(g)m)$. Then:

1. For every $m \in V'$, the rational coboundary $g \mapsto \rho'(g)m - m$ belongs to `finiteCocycles PD ρ'`.
2. For every $O$-lattice $L'$ in $\rho'$ and every $c : G \to V'/L'.T$, we have $c \in \mathrm{HfD}(\mathrm{PD}, L')$ if and only if there exists a *single* cocycle $z \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho')$ such that $c(g) = [z(g)]_{V'/L'.T}$ for all $g \in G$.

*Proof.* Writing $\rho'(g)m - m = \rho'(g)m + (-m)$ shows continuity from orbit continuity at $m$, and $\rho'(g)(\rho'(h)m - m) + (\rho'(g)m - m) = \rho'(gh)m - m$ gives the cocycle law. In $V' \otimes_{Qp} B$, take the explicit period element $w := m \otimes_{Qp} 1$; since `PD.actB g 1 = 1`, we have $\mathrm{actVB}_{\mathrm{PD},\rho'}(g)(m \otimes 1) - (m \otimes 1) = (\rho'(g)m - m) \otimes 1$, proving claim 1 (`coboundary_mem_blochKatoCocycles`). Now any $c \in \mathrm{HfD}(\mathrm{PD}, L')$ decomposes by `Submodule.mem_sup` as $[z_0] + b$ with $z_0 \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho')$ and $b \in \mathrm{BD}(L')$. Choosing $m \in V'$ lifting the divisible coboundary generator $\bar m \in V'/L'.T$ of $b$, we have $b(g) = [\rho'(g)m - m]$, so $z(g) := z_0(g) + (\rho'(g)m - m)$ lies in the subspace `finiteCocycles PD ρ'` by claim 1 and projects pointwise to $c(g)$. The converse takes $b = 0$ (`Submodule.mem_sup_left`). (Same file, `:85–106`.) $\square$

##### Lemma 10.13ek. Section-lift independence and $\mathrm{KmodO}(O)$ transport of the divided cup test [Lean, read]

Assume `IsDomain O` and `IsFractionRing O LL`, let $e : H \simeq^\ast G$ be a topological group isomorphism (`he`, `he'`), let $L_1$ be an $O$-lattice in `charRep (cycLL PD LL)` with $L_1.T = \operatorname{im}(\operatorname{algebraMap} O\,LL)$, and let $\chi : H \to O$ satisfy $\operatorname{algebraMap} O\,LL(\chi(g)) = \mathrm{cycLL}\,\mathrm{PD}\,LL(e(g))$. Let $L'$ be the stable standard lattice $\iota(O^r)$ in the representation $\rho'$ realized on $e(g)$ by the integral matrices $M'(g)$. Suppose $\varpi \in O$ maps to a nonzero element of $LL$, $y, d : H \to O^r$, $c(e(h)) = [\varpi^{-1}\iota(y(h))]_{LL^r/\iota(O^r)}$, and $d_G = \iota \circ d \circ e^{-1}$. Then `CobO PD L1 (cupLD L' (dotProductBilin LL LL) d_G c)` holds if and only if there exists a locally constant $f : H \to \mathrm{KmodO}(O)$ such that for all $g, h \in H$,
$$
\bigl[\varpi^{-1}\bigl(d(g) \cdot M'(g) y(h)\bigr)\bigr]_{\mathrm{KmodO}(O)} = \chi(g)\cdot f(h) - f(gh) + f(g).
$$

*Proof.* By `(Submodule.Quotient.mk_surjective L'.T (c (e h))).choose_spec`, $\mathrm{liftD}_{L'}(c(e(h))) - \varpi^{-1}\iota(y(h)) \in L'.T = \iota(O^r)$, so write $\mathrm{liftD}_{L'}(c(e(h))) = \varpi^{-1}\iota(y(h)) + \iota(t_{g,h})$ with $t_{g,h} \in O^r$. Applying $\rho'(e(g))\iota(v) = \iota(M'(g)v)$ and $\iota(u)\cdot\iota(v) = \operatorname{algebraMap} O\,LL(u\cdot v)$ (`incl_dot`), the raw section cup value in $LL$ equals
$$
d_G(e(g)) \cdot \rho'(e(g))\,\mathrm{liftD}_{L'}(c(e(h)))
= \operatorname{FractionRing.algEquiv}_{O,LL}\!\bigl(\varpi^{-1}(d(g)\cdot M'(g)y(h))\bigr) + \operatorname{algebraMap} O\,LL\bigl(d(g)\cdot M'(g)t_{g,h}\bigr).
$$
Since $d(g)\cdot M'(g)t_{g,h} \in O$, its image lies in $L_1.T$ and vanishes in $LL/L_1.T$, proving complete independence from the `Classical.choose` section `liftD`. Next, `FractionRing.algEquiv O LL : FractionRing O ≃ₐ[O] LL` maps $\operatorname{im}(O \to \operatorname{Frac}(O))$ onto $L_1.T$, inducing by `Submodule.Quotient.equiv` an $O$-linear bijection $q : \mathrm{KmodO}(O) \simeq_O LL/L_1.T$ intertwining the scalar action $\chi(g)\cdot x$ with $\mathrm{repD}_{L_1}(e(g))(q(x))$. Composing locally constant cochains with $q$ (or $q^{-1}$) and the homeomorphism $e$ (or $e^{-1}$) preserves `IsLocallyConstant` and transports the coboundary identity in both directions (`cobO_iff`). (Same file, `:112–150, 231–243`; `TateH2IffAllFiniteExtensions.lean:257–275`.) $\square$

##### Lemma 10.13el. Local bridge supplies at places above $\ell$ [Lean, read]

Under the global assumptions of $(D, N, X, \mathrm{bkP})$ and `GalHyp bkP i s` at a place $v \in \mathrm{placesOver}(E, \ell)$ (`hv`), with `Bw := bkP.br i v hv` and $O = X.O0(i)$:

1. `Bw.eO : O ≃+* OL(Bw.LL)` transports `LocalIntegers.good_integers l Bw.LL` to `GoodO (Qp := ℚ_[l]) Bw.LL.1 O`.
2. For both $\sigma = \mathrm{Tgl}\,i\,s$ and any $\rho$ satisfying `IsDual i s ρ`, the local representation `repV bkP i v hv σ` has continuous orbits on `Bw.LL.1^r`, and the integral matrices $T(g) = \mathrm{Tmat}\,i\,s\,g$ and $T'(g) = \mathrm{Tdual}\,i\,s\,g$ satisfy $T(g)^t T'(g) = \epsilon_0(g) I_r$.
3. On $g \in \mathrm{DecV}\,N\,v$, $\mathrm{Bw.toLL}(\epsilon_0(g.1)) = \mathrm{cycLL}\,\mathrm{PD}_v\,\mathrm{Bw.LL.1}(\mathrm{Bw.e}(g))$.

*Proof.* In `IsDiscreteValuationRingIntegralClosurePadicInt.lean:115–124, 166–186`, the integral closure `OL(Bw.LL)` of $\mathbb Z_\ell$ in `Bw.LL` is finite over $\mathbb Z_\ell$, a DVR with fraction field `Bw.LL`, and characterized inside `PadicAlgCl l` by spectral norm $\|x\| \le 1$ (`mem_integralClosure_padicInt_iff`). Hence `LocalIntegers.isOpen_integers` (`FiniteQuotientPow.lean:27–36`) writes $\operatorname{im}(\mathrm{OL}(\mathrm{Bw.LL}) \to \mathrm{Bw.LL.1})$ as the preimage under the continuous subspace inclusion $\mathrm{Bw.LL.1} \hookrightarrow \mathrm{PadicAlgCl}\,l$ of the ultrametric closed unit ball `Metric.closedBall 0 1`, which is open by `IsUltrametricDist.isOpen_closedBall`; combined with `isModuleTopologyOfFiniteDimensional` from the induced continuous $\mathbb Q_\ell$-action, `good_integers` (`:37–47`) gives `GoodO (Qp := ℚ_[l]) Bw.LL.1 OL(Bw.LL)`. Transporting along the ring equivalence `Bw.eO` via `IsFractionRing.of_ringEquiv_left` and `Bw.eO.surjective.range_comp` yields claim 1 (`LiftBlochKatoCocycleIffOrthogonalLattice.lean:282–290`).

For claim 2, `PrimeToInertia.continuous_Tmat` and `continuous_Tdual` (`ContinuousAlgebraMapPadicInt.lean:232–244, 365–389`) prove $\mathfrak m_O$-adic continuity of $T$ and $T'$ on $G_E$ (using `(l : O) ∈ m_O` to get continuity of $\mathbb Z_\ell \to O$, hence of $\epsilon_0$). Next, `BKDimNoInv.toLL_continuous` and `rep_continuous` (`LocalGaloisRepInvariantsFromFractionRing.lean:18–34`) compose $r \circ \mathrm{Bw.e}^{-1}$ with `Bw.eO_cont` and the subspace inclusion $\mathrm{OL}(\mathrm{Bw.LL}) \hookrightarrow \mathrm{Bw.LL.1}$ to obtain continuous matrix action on `Bw.LL.1^r`. Since `Tgl i s g` lies in $\mathrm{GL}_r(O)$, $\det T(g)$ is a unit in $O$, and `Tdual` (`BlochKatoPhases.lean:274–275`) gives $T(g)^t T'(g) = \epsilon_0(g)(T(g)^{-1}T(g))^t = \epsilon_0(g) I_r$ (`:299–304, 311–313`).

For claim 3, `CrystallineCharacterRatio.chi_eq_cyc` (`CrystallineCharacterRatio.lean:28–73`) proves $(D.\mathrm{loc}\,\ell).\chi_Q(\mathrm{Bw.e}(g)) = \mathrm{cycZ}(\ell, g.1)$ in $\mathbb Q_\ell$: for every $m \ge 0$, picking a primitive $\ell^m$-th root of unity $\zeta \in \Omega$, `Bw.e_comm` intertwines the actions of $\mathrm{Bw.e}(g)$ on $\mathrm{Bw.j}(\zeta)$ and $g.1$ on $\zeta$, forcing their exponents to agree modulo $\ell^m$ so the $\ell$-adic norm of the difference is at most $\ell^{-m}$; letting $m \to \infty$ gives equality. Combining with `PD_χ` and `Bw.eO_alg` yields claim 3 (`:305–310`). $\square$

##### Theorem 10.13em. Cup-product orthogonality criterion for Bloch–Kato lattice lifting [Lean, read]

1. **(Abstract DVR criterion, `BKLatticeCochain.lift_iff`.)** Let $e : H \simeq^\ast G$ be a topological group isomorphism (`he`, `he'`), `PD : PeriodData G Qp K₀ K B BdR`, `GoodO (Qp := Qp) LL O`, and `hBK : bkBCore PD`. Let $\rho, \rho'$ be $LL$-linear representations of $G$ on $LL^r$ with continuous orbits (`cρ`, `cρ'`), realized on $e(g)$ ($g \in H$) by integral matrix maps $M, M' : H \to \mathrm{Mat}_r(O)$ satisfying $M(g)^t M'(g) = \chi(g) I_r$ (`hM`), where $\chi : H \to O$ lifts `cycLL PD LL ∘ e`. Assume `hdR : IsDR PD ρ`, let $\varpi \in O$ satisfy `Irreducible ϖ`, and let $y : H \to O^r$ satisfy:
   - (`hy`) for every coordinate $a \in \mathrm{Fin}\,r$, $g \mapsto \mathrm{residue}_O(y(g)_a)$ is locally constant on $H$;
   - (`hyc`) for all $g, h \in H$ and $a \in \mathrm{Fin}\,r$, $y(gh)_a - (y(g)_a + (M'(g)y(h))_a) \in \mathfrak m_O$.

   Then there exists $y' : H \to O^r$ such that $(\iota \circ y' \circ e^{-1}) \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho')$ and $y'(g)_a - y(g)_a \in \mathfrak m_O$ for all $g, a$ if and only if for every $d : H \to O^r$ with $(\iota \circ d \circ e^{-1}) \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho)$, there exists a locally constant $f : H \to \mathrm{KmodO}(O)$ such that for all $g, h \in H$,
   $$
   \bigl[\varpi^{-1}\bigl(d(g) \cdot M'(g) y(h)\bigr)\bigr]_{\mathrm{KmodO}(O)} = \chi(g)\cdot f(h) - f(gh) + f(g).
   $$
2. **(Global-to-local specialization, `T.lift_blochKatoCocycle_iff_orthogonal_lattice`.)** For every $(D, N, X, \mathrm{bkP})$, twist $i : X.\mathrm{Tw}$, signature $s : X.\mathrm{Sig}(i)$ satisfying `GalHyp bkP i s`, dual action $\rho$ satisfying `IsDual i s ρ`, place $v \in \mathrm{placesOver}(D.\mathrm{host}.E, X.l(i))$ (`hv`), uniformizer $\varpi \in O = X.O0(i)$ with `Irreducible ϖ`, and cochain $y : \mathrm{DecV}\,N\,v \to O^r$ with locally constant coordinates modulo $\mathfrak m_O$ and mod-$\mathfrak m_O$ cocycle defect $y(gh)_a - (y(g)_a + (\mathrm{Tdual}\,i\,s\,g.1 \cdot y(h))_a) \in \mathfrak m_O$, there exists $y' : \mathrm{DecV}\,N\,v \to O^r$ satisfying `IsFCoc bkP i v hv ρ y'` and $y'(g)_a - y(g)_a \in \mathfrak m_O$ for all $g, a$ if and only if for every $d : \mathrm{DecV}\,N\,v \to O^r$ satisfying `IsFCoc bkP i v hv (Tgl i s) d`, the $\varpi^{-1}$-divided cup cochain $(g, h) \mapsto [\varpi^{-1}(d(g)\cdot (\mathrm{Tdual}\,i\,s\,g.1)\,y(h))]_{\mathrm{KmodO}(O)}$ is the $\epsilon_0$-coboundary of a locally constant $f : \mathrm{DecV}\,N\,v \to \mathrm{KmodO}(O)$.

*Proof.* We first prove part 1 (`LiftBlochKatoCocycleIffOrthogonalLattice.lean:160–273`) in five steps, then deduce part 2 (`:278–316`; exported at `LiftBlochKatoCocycleIffOrthogonalLatticeStatement.lean:9–10`).

**Step 1: Standard lattices and perfect integral duality (`:178–203`).** From `GoodO`, `IsFractionRing.injective O LL` gives injectivity `hinj` of $\operatorname{algebraMap} O\,LL$. By Lemma 10.13ei(1), $\iota(O^r) \subseteq LL^r$ gives $O$-lattices $L$ in $\rho$ and $L'$ in $\rho'$, while `TateTopCompare.rangeLattice` gives the rank-one lattice $L_1$ in `charRep (cycLL PD LL)` with $L_1.T = \operatorname{im}(\operatorname{algebraMap} O\,LL)$. Pair $LL^r \times LL^r \to LL$ by `dotProductBilin LL LL`. For $g = e(h) \in G$,
$$
(\rho(g)x)\cdot(\rho'(g)x') = (M_{LL}(h)x)\cdot(M'_{LL}(h)x') = x \cdot \bigl(M_{LL}(h)^t M'_{LL}(h) x'\bigr) = \operatorname{algebraMap} O\,LL(\chi(h))\,(x\cdot x') = \mathrm{cycLL}\,\mathrm{PD}\,LL(g)\,(x\cdot x'),
$$
using `hM`. Evaluating against standard basis vectors `Pi.single a 1` proves left and right rational nondegeneracy, while $\operatorname{finrank}_{LL}(LL^r) = \operatorname{finrank}_{LL}(LL^r)$ is `rfl`. If $x \in \iota(O^r)$ and $x' \in \iota(O^r)$, `incl_dot` gives $x\cdot x' \in \operatorname{im}(\operatorname{algebraMap} O\,LL)$; conversely, if $\forall x \in \iota(O^r),\ \exists o \in O,\ x\cdot x' = \operatorname{algebraMap} O\,LL(o)$, testing $x = \iota(\mathbf e_a)$ exhibits $x'_a = \operatorname{algebraMap} O\,LL(o_a)$ for each $a$, so $x' \in \iota(O^r) = L'.T$ by `mem_range_incl`. This establishes `hD : IsDualLat1 PD L L' (dotProductBilin LL LL)`.

**Step 2: $\varpi^{-1}$-division into `divisibleCocycles L'` (`:204–228`).** Define $c : G \to LL^r/L'.T$ by
$$
c(g) := \bigl[(\operatorname{algebraMap} O\,LL(\varpi))^{-1}\iota\bigl(y(e^{-1}(g))\bigr)\bigr]_{LL^r/L'.T}.
$$
By Lemma 10.13ei(2) (`key`), $c(e(g)) = c(e(g'))$ if and only if $\mathrm{residue}_O(y(g)_a) = \mathrm{residue}_O(y(g')_a)$ for all $a \in \mathrm{Fin}\,r$. Because `Fin r` is finite, `Filter.eventually_all` intersects the $r$ open neighborhoods supplied by `hy`, and composing with `he'` (`Continuous e.symm`) proves `IsLocallyConstant c`. For $g = e(h)$ and $g' = e(h')$, linearity of the quotient map and $\rho'(e(h))\iota(v) = \iota(M'(h)v)$ give
$$
c(gg') - \bigl(c(g) + \mathrm{actD}_{L'}(g)c(g')\bigr)
= \bigl[\varpi^{-1}\iota\bigl(y(hh') - (y(h) + M'(h)y(h'))\bigr)\bigr]_{LL^r/L'.T} = 0
$$
by `hyc` and `key`. Hence $c \in \mathrm{divisibleCocycles}(L')$.

**Step 3: Invoking `bkBCore.1` and section-lift independence (`:152–157, 229–243, 260–273`).** Since `Fin r → LL` carries the $LL$-module topology under `GoodO`, `vecRep ρ cρ` and `vecRep ρ' cρ'` inhabit `GRep G Qp LL O`. Applying clause `.1` of `hBK` at `(LL, O, hG, L1, rfl, vecRep ρ cρ, vecRep ρ' cρ', L, L', dotProductBilin LL LL, hdR, hD)` to $(c, \mathrm{hc})$ yields
$$
c \in \mathrm{HfD}(\mathrm{PD}, L') \iff \forall d_G \in \mathrm{latticeFiniteCocycles}(\mathrm{PD}, L),\ \mathrm{CobO}\bigl(\mathrm{PD}, L_1, \mathrm{cupLD}(L', \mathrm{dotProductBilin}\,LL\,LL, d_G, c)\bigr).
$$
Clause `.2` of `bkBCore` is never called. Any $d_G \in \mathrm{latticeFiniteCocycles}(\mathrm{PD}, L)$ takes values in $L.T = \iota(O^r)$, so choosing $t(g) \in O^r$ with $\iota(t(g)) = d_G(g)$ sets $d(h) := t(e(h))$ with $d_G = \iota \circ d \circ e^{-1} \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho)$; conversely, any $d_G := \iota \circ d \circ e^{-1} \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho)$ is already a continuous cocycle valued in $\iota(O^r)$, hence lies in `latticeFiniteCocycles PD L`. Lemma 10.13ek rewrites `CobO PD L1 (cupLD ... d_G c)` as the $\mathrm{KmodO}(O)$ $\chi$-coboundary condition on the right-hand side of part 1.

**Step 4: Equivalence between $c \in \mathrm{HfD}(\mathrm{PD}, L')$ and integral finite lifts (`:244–260`).** By Lemma 10.13ej(2), $c \in \mathrm{HfD}(\mathrm{PD}, L')$ holds if and only if $c(g) = [z(g)]_{LL^r/L'.T}$ for a single $z \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho')$.
- *($\Rightarrow$, from lift $y'$ to $z$):* Suppose $y' : H \to O^r$ satisfies $y'_G := \iota \circ y' \circ e^{-1} \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho')$ and $y'(h)_a - y(h)_a \in \mathfrak m_O$. Since `finiteCocycles PD ρ'` is an $LL$-submodule and $\operatorname{algebraMap} O\,LL(\varpi) \ne 0$, $z := (\operatorname{algebraMap} O\,LL(\varpi))^{-1} y'_G$ belongs to `finiteCocycles PD ρ'`, and $[z(g)] = [\varpi^{-1}\iota(y'(e^{-1}(g)))] = [\varpi^{-1}\iota(y(e^{-1}(g)))] = c(g)$ by `key`.
- *($\Leftarrow$, from $z$ to lift $y'$):* Suppose $z \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho')$ satisfies $[z(g)] = c(g)$ for all $g \in G$. Pointwise equality in $LL^r/\iota(O^r)$ means $\varpi^{-1}\iota(y(e^{-1}(g))) - z(g) \in \iota(O^r)$ for each $g$; choose any pointwise preimage $t(g) \in O^r$ (`Classical.choose`) so that $\iota(t(g)) = \varpi^{-1}\iota(y(e^{-1}(g))) - z(g)$, and define
  $$
  y'(h) := y(h) - \varpi\,t(e(h)) \in O^r.
  $$
  Immediately $y'(h)_a - y(h)_a = -\varpi\,t(e(h))_a \in (\varpi) = \mathfrak m_O$. Furthermore, for every $g \in G$,
  $$
  \iota\bigl(y'(e^{-1}(g))\bigr) = \iota\bigl(y(e^{-1}(g))\bigr) - \varpi\bigl(\varpi^{-1}\iota(y(e^{-1}(g))) - z(g)\bigr) = (\operatorname{algebraMap} O\,LL(\varpi))\,z(g).
  $$
  Because `finiteCocycles PD ρ'` is closed under $LL$-scalar multiplication (`smul_mem`), $\iota \circ y' \circ e^{-1} = \varpi z \in \mathrm{finiteCocycles}(\mathrm{PD}, \rho')$. In particular, $y'$ inherits continuity, the exact $O$-cocycle law, and the $B_{\mathrm{cris}}$-trivialization from $\varpi z$, even though $t$ was chosen pointwise without any topological hypothesis. Combining Steps 3 and 4 completes part 1.

**Step 5: Specialization across `bkP` (`:278–316`).** Fix `Bw := bkP.br i v hv` and endow `Bw.LL.1` with the $O$-algebra structure `Bw.toLL.toAlgebra`. Apply part 1 to `PDv bkP i v hv`, $e = \mathrm{Bw.e} : \mathrm{DecV}\,N\,v \simeq^\ast \mathrm{GK}(\mathrm{Bw.Kw})$, $M(g) = \mathrm{Tmat}\,i\,s\,g.1$, $M'(g) = \mathrm{Tdual}\,i\,s\,g.1$, and $\chi(g) = \epsilon_0(X, i, g.1)$. Lemma 10.13el supplies `GoodO`, matrix realization (`Tgl_coe` and `hρ : IsDual i s ρ`), orbit continuity, cyclotomic character alignment, and $M(g)^t M'(g) = \chi(g)I_r$. From `GalHyp` (`IsTameInertiaElementAtTwistPrime.lean:119–120`; `BlochKatoPhases.lean:351–399`), `(h.2.2.2.2.2.1 (X.l i) Bw.Kw).2.2` extracts `bkBCore (PDv bkP i v hv)` from `Gen.adm3 D`, while `(h.1.2.1 v hv (Tgl i s) (Or.inr rfl)).1` gives `Bw.IsdRW`, which rewrites via `Module.finrank_fin_fun` to `IsDR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))`. Finally, under `Bw.toLL.toAlgebra`, the condition `(fun g a => algebraMap O LL (w (e.symm g) a)) ∈ finiteCocycles ...` is definitionally identical to `IsFCoc bkP i v hv σ w` (`IsFCocIff.lean:17–18`). $\square$

##### Failure boundaries when saturation or unimodularity is dropped [Expository]

The following changes to Example 10.13eg show what the integral finite condition and the two directions of lattice duality do.

1. **Failure Boundary 10.13en (Dropping saturation of the integral finite cocycle module).** In Step 4, the reverse direction uses $\varpi z \in Z^1_f(\mathrm{PD}, \rho')$ and forward division uses $\varpi^{-1} y'_G \in Z^1_f(\mathrm{PD}, \rho')$, which makes $Z^1_f(L') = Z^1_f(\mathrm{PD}, \rho') \cap C^1(G, L'.T)$ $\varpi$-saturated in $Z^1(G, L'.T)$. In Example 10.13eg, replace $Z^1_f(H, L') = O y'_1 \oplus O y'_2$ by its finite-index integral coboundary submodule $N' := B^1(H, O^2(M')) = O(3 y'_1) \oplus O y'_2 \subsetneq Z^1_f(H, L')$. Because $\mathbb Q \cdot N' = Z^1_f(H, \mathbb Q^2(M'))$ is unchanged, the divisible image $\mathrm{HfD}(L')$ and the entire $\mathrm{KmodO}(O)$ cup-orthogonality condition on the right-hand side remain unchanged, and $y = y'_1$ satisfies both $3 y'_1 \in N'$ and the full cup-coboundary test against $Z^1_f(H, L)$. Yet every $u \in N'$ satisfies $u(\sigma) = (B - I_2)(u_1, u_2)^t = (3(u_2 - u_1), -u_1)^t \equiv (0, -u_1)^t \pmod 3$, whereas $y'_1(\sigma) = (1, 0)^t \notin 3O \times O$; hence $y'_1$ admits *no* mod-$3$ lift in $N'$.
2. **Failure Boundary 10.13eo (Dropping perfect integral pairing in `IsDualLat1`).** Rational nondegeneracy and $\chi$-equivariance of $P$ do not suffice without the exact integral unimodularity $x' \in L'.T \iff \forall x \in L.T,\ P(x, x') \in \operatorname{im}(\operatorname{algebraMap} O\,LL)$:
   - *Sub-unimodular pairing ($P(L, L') \subseteq \mathfrak m_O$):* Keep $L.T = L'.T = O^2$ in Example 10.13eg and replace the dot product by $P_3(x, x') := 3(x\cdot x')$ (equivalently, test only against the index-$9$ sublattice $3O^2 \subsetneq L.T$). For the unliftable residual cocycle $y_{\mathrm{bad}}(\sigma^a \tau^b) = (0, b)^t$ and *every* $d \in Z^1_f(H, L)$, $[\frac{1}{3} P_3(d(g), M'(g)y_{\mathrm{bad}}(h))]_{\mathrm{KmodO}(O)} = [d(g)\cdot M'(g)y_{\mathrm{bad}}(h)]_{\mathrm{KmodO}(O)} = 0$, so $y_{\mathrm{bad}}$ passes the cup-coboundary test with $f = 0$, yet has no lift in $Z^1_f(H, L')$.
   - *Super-integral lattice ($P(L, L') \not\subseteq O$):* Dually, if $L.T$ is enlarged to $\frac{1}{3}O^2$ while $L'.T = O^2$ under $x\cdot x'$, shifting the non-canonical section $\mathrm{liftD}_{L'}(c(h))$ by $(1, 0)^t \in L'.T$ against $(\frac{1}{3}, 0)^t \in L.T$ changes $\mathrm{cupLD}$ by $\frac{1}{3} \notin O$, so the reduced section cup itself can depend on the section. This computation tests the section comparison in Lemma 10.13ek.

##### Literature comparison, bidirectional consumer contract, and scope remarks [Lean, read]

Rubin's diagram (1.3) gives a lift of a cohomology class. The cochain proof here uses Lemma 10.13ej to absorb quotient coboundaries and returns the exact `IsFCoc` representative. In the residual Selmer comparison the forward consumer starts from reductions of lattice cocycles, and the reverse consumer starts from annihilation of all original-side finite testers. For the first consumer the residue-field primitive is transported to a discrete `IsRes` extension and multiplied by the two generator coefficients $b,b'$. For the second, surjectivity is available at $k=O/\mathfrak m_O$, which is where the equal-dimension producer applies it. Its later base-change result supplies the passage to other `IsRes` fields. [Rubin, Lemma 1.3.8(i)](https://wstein.org/people/rubin/book/hEulerSystems.pdf) · [Source map](../sources/SOURCES.md#chapter-10-blochkato-lattice-lifting-and-integral-annihilators)

| Direction or component | Exact interface and consumer/supplier role |
|---|---|
| Forward direction (`.1`, lift $\Rightarrow$ divided cup coboundary) | Consumed by `ResidualBlochKatoLatticeDualOrthogonal.lean:186–187` (`bkOn_orthogonal` in the residual equal-dimension manuscript (§10.4.7.10)). Given integral finite cocycles $d$ for `Tgl i s` and $d'$ for $\rho$, it uses `IsFCoc.continuous` (`IsFCocIff.lean:36–44`) and openness of $\mathfrak m_O$ to check local constancy of $d' \bmod \mathfrak m_O$, uses `IsFCoc.cocycle` (`:46–58`) to pass $y = d'$ with lift $y' = d'$ itself ($d' - d' = 0 \in \mathfrak m_O$), and obtains a $\mathrm{KmodO}(O)$-coboundary for $\varpi^{-1}(d \cup d')$. Then `LocalH2Injective.h2_inj` (under `LocalTateDuality`, `exists_residue_embedding`, and `kmod_torsion`) injects $H^2(\mathrm{DecV}\,N\,v, k(\bar\epsilon_0))$ into $H^2(\mathrm{DecV}\,N\,v, \mathrm{KmodO}(O)(\epsilon_0))$ via $a \bmod \mathfrak m_O \mapsto [\varpi^{-1}a]$, concluding that the reduced cup over $k$ (and via $k \hookrightarrow K$ over any discrete `IsRes` field $K$) is a coboundary. |
| Reverse direction (`.2`, divided cup coboundary $\Rightarrow$ lift) | Consumed by `MemDualBlochKatoOfOrthogonalResidual.lean:66–68` (`mem_bkOn_of_orthogonal` in the residual equal-dimension manuscript (§10.4.7.10), used at $K = k$ where `Surjective (algebraMap O K)` holds). Given a residual cocycle $y : \mathrm{DecV}\,N\,v \to K^r$ annihilating `bkOn`, it lifts $y$ coordinatewise to $\hat y : \mathrm{DecV}\,N\,v \to O^r$, reduces each `IsFCoc` cocycle $d$ to $K^r$ via `IsFCoc.continuous` and `IsFCoc.cocycle`, lifts each $K$-coboundary witness $f_K$ along $O \twoheadrightarrow K$, and applies `divMap ϖ` ($a \mapsto [\varpi^{-1}a]_{\mathrm{KmodO}(O)}$, killing $\mathfrak m_O$ by `divMap_eq_zero`). Theorem 10.13em(2)`.2` produces an `IsFCoc` cocycle $y'$ congruent to $\hat y$ mod $\mathfrak m_O$, unpacked via `isFCoc_iff` (`IsFCocIff.lean:22–34`) with scalar $b = 1$ to witness $[y] \in \mathrm{bkOn}$. |
| Auxiliary lattice helpers (`stdLattice`, `incl`, `incl_dot`, `mem_range_incl`) | Consumed directly by `ContinuousDualMat.lean:54` (`latDual`) and `DualLatticeRankBound.lean:22–30, 91` (`isDualLat1_dual`, `latDual_bounded`). |
| Representative independence summary | Independent of: (i) `liftD` section in `cupLD` (differs by $O$, vanishes in $LL/L_1.T$); (ii) coordinate lifts $\hat y \mapsto \hat y + \varpi u$ (changes $\varpi^{-1}(d\cdot M'\hat y)$ by $d\cdot M'u \in O$); (iii) the choice of lift of each value of a $K$-coboundary witness before applying `divMap ϖ`; and (iv) shifting $d$ or $y$ by integral/residual coboundaries (by the cup-coboundary identities in the residual equal-dimension manuscript (§10.4.7.10)). |
| Named inputs and later uses | `bkBCore` (`Gen.adm3 D` in `GalHyp`, routed supplied by §10.4.7.12 conditional on `IntegralDuality`); `LocalTateDuality` and `LocalH2Injective.h2_inj` (used in `bkOn_orthogonal`, not here); $p$-adic Hodge comparison / `IsotypicValuationAtRing` production supplying `IsdRW` / `IsDR`; and compiled-environment reachability from `Main.riemannHypothesis`. |

**Scope.** The local source reading covers `LiftBlochKatoCocycleIffOrthogonalLattice.lean:13–317` and the direct supplies listed in the source ledger. The conditional result has an independent expository audit. The finite-group DVR examples check the cochain and lattice algebra, with nonzero residual $H^0$ on both sides. The dyadic model uses the cyclotomic action on fourth roots of unity. Full arithmetic period data, `GalHyp` production, compiled reachability from `Main.riemannHypothesis`, Lean kernel replay and peer review have separate scopes. [Source ledger](../sources/SOURCES.md#chapter-10-blochkato-lattice-lifting-and-integral-annihilators)

#### 10.4.7.12 Integral local duality and the two finite-condition annihilators

**Motivation.** The [lattice-lifting theorem](#104711-lifting-residual-cocycles-to-the-blochkato-lattice) asks whether a quotient cocycle cups to a coboundary against every integral finite cocycle. Its input `bkBCore` makes that test exact. The archive starts with Bloch–Kato integral duality over $\mathbb Z_\ell$ and supplies the same test over the coefficient DVR of the representation. The new issue is that a scalar-valued trace test can kill a nonzero quotient class. One needs a family of tests and an integral reconstruction of their coboundary witnesses.

**Example (a first cup test).** Over $O=\mathbb Z_{(2)}$, let $s$ generate $C_2$ and act by $-1$ on the integral side. A cocycle with $d(s)=1$ is rationally the coboundary of $-1/2$. If the quotient side is trivial and $c(s)=1/2+O$, the cup at $(s,s)$ is $1/2+O$. With the sign twist on the target, the differential at $(s,s)$ of a normalized one-cochain is zero. Thus a rational coboundary on the integral side can give a nonzero pairing after passing to integral cohomology. The full calculations below identify the annihilators.

**Definitions.** Fix a prime $\ell$, a local datum $\mathcal P:\mathrm{LocPrime}(\ell)$, and a finite extension $K:\mathrm{FinExt}(\ell)$, with $G=G_K$, $k_0=\mathbb Q_\ell$, and $R=\mathbb Z_\ell$. Use exactly $\mathrm{PD}=\mathcal P.\mathrm{PD}(K)$. Its period algebras $B,B_{\mathrm{dR}}$ have diagonal actions on the tensor products over $k_0$, fixed rings $K_0,K$, compatible Frobenius on $B$ and embedding into the filtered $B_{\mathrm{dR}}$, and an invertible period $t$ of character $\chi$ with $\varphi(t)=\ell t$ and filtration degree one. The full datum includes the filtration and fundamental-period axioms of `PeriodData`. The cyclotomic compatibility of $\mathcal P$ supplies the $R$-valued character, with unit values by applying integrality also to $g^{-1}$. In the classical comparison take $B=B_{\mathrm{cris}}$ and the usual de Rham period algebra. [A2, `Statement.lean:75–140`; `DataNLoc.lean:527–559`; `RationalDualityOfAllCoefficients.lean:66–97`.]

Take any coefficient field $F$ and ring $O$ satisfying `GoodO`: $O$ is a DVR with fraction field $F$, the latter is finite-dimensional over $k_0$ with its $k_0$-module topology and topological ring structure, and the image of $O$ in $F$ is open. Identify $O$ with its image. Take any two bundles `GRep` $A,A'$ over these coefficients, with spaces $V,V'$, finite $F$-dimensions, module topologies, compatible $k_0$ and $O$ scalar structures, continuous addition and constant scalar multiplication, and orbit-continuous actions $\rho,\rho'$. Take stable finite free spanning lattices $L,L'$ and the cyclotomic lattice $L_1$ in $F(\chi)$ with carrier exactly $O$. Require
$$
\operatorname{finrank}_F (V\otimes_{k_0}B_{\mathrm{dR}})^G
=[K:k_0]\dim_F V.
$$
This is `IsDR PD A.ρ`. The theorem asks for this equality on $V$. Require a bilinear $P:V\times V'\to F$ satisfying $P(gx,gy)=\chi(g)P(x,y)$, zero left and right radicals, and equal $F$-ranks. In addition require, for **every** $y\in V'$,
$$
 y\in L' \quad\Longleftrightarrow\quad P(x,y)\in O\ \text{for every }x\in L.
$$
These are exactly `IsDual1` and `IsDualLat1`. [A2, `LocCoh.lean:21–90,161–170`; `Statement.lean:220–225`.]

Write $Z_f^1(V)$ for the continuous cocycles $z$ satisfying, for one $w\in V\otimes_{k_0} B$ and every $g$, $z(g)\otimes1=g w-w$. Write $Z^1(L)$ for the continuous $V$-valued cocycles with values in $L$ and $Z_f^1(L)=Z^1(L)\cap Z_f^1(V)$. Put $D'=V'/L'$. Write $Z^1(D')$ for the locally constant cocycles and
$$
 \mathcal F(D')=\operatorname{im}(Z^1_f(V')\longrightarrow C^1(G,D'))+B^1(D'),
 \qquad B^1(D')=\{g\mapsto g\bar v-\bar v:\bar v\in D'\},
$$
where the image and sum are in the space of all functions. Membership is equivalent to $c(g)=[z(g)+g v-v]$ for some $z\in Z_f^1(V')$ and $v\in V'$, uniformly for all $g$. At use, the quotient cocycle hypothesis is explicit. Here “finite” designates a local condition; the quotient coefficients can be divisible. [A2, `Statement.lean:190–202,227–239`; `StatementTor.lean:103–130`.]

The torsion stages of $D'$ are $D'[\varpi^m]=\varpi^{-m}L'/L'$, identified $G$-equivariantly with $L'/\varpi^mL'$ by division, where $\varpi$ is a uniformizer of $O$. Every locally constant cochain in degree one or two has finite image because $G$ and $G\times G$ are compact. Its values therefore lie in a common torsion stage of the relevant quotient. A primitive of a stage-valued cup is allowed to live in a larger stage: `CobO` asks for vanishing in the full quotient. The producer does its tests there, while the preceding section treats residual division explicitly.

For $d$ with values in $L$ and $c$ with values in $D'$, put $u(d,c)(g,h)=[P(d(g),g\,s(c(h)))]\in F/O$, where $s$ is any set-theoretic section. Replacing $s$ changes the lift by an element of $L'$, which stays there under $g$ and pairs integrally with $d(g)$. Thus $u$ is a well-defined bilinear cochain. On locally constant patches for $c(h)$, choose a fixed representative $y$; orbit continuity, continuity of $d$, and continuity of finite-dimensional bilinear operations show that reduction modulo the open $O$ is locally constant. For cocycles the usual cup differential cancels by the two cocycle laws and equivariance. Define $\partial f(g,h)=\chi(g)f(h)-f(gh)+f(g)$ in $(F/O)(\chi)$. The archive's `CobO` requires one **locally constant** $f$ with $\partial f=u$ at every pair. This is continuity with discrete quotient coefficients. No regularity of a fractional section is used. [A2, `LocCoh.lean:91–141`; `AdRep.lean:10–50`.]

##### Lemma (scalar coordinates detect quotient coboundaries) [Lean, read]
 There are a $k_0$-linear functional $\lambda:F\to k_0$ and finitely many $e_i,f_i\in O$ with
$$
 R\subset O,\qquad \lambda(O)\subset R,\qquad
 a=\sum_i e_i\lambda(f_i a)\quad(a\in F).
$$
Consequently an $F$-valued two-cochain $z$ reduces to a coboundary modulo $O$ if and only if $\lambda(o z)$ reduces to a coboundary modulo $R$ for every $o\in O$. The reverse test needs only the $f_i$.

**Proof.** The coefficient-ring lemma identifies the image of $O$ with the integral closure of $R$ in $F$. It is finite free over $R$. Choose a basis $e_i$ and trace-dual basis $b_i$. The trace dual of $O$ is $\sum_i R b_i$. It is an $O$-submodule since $\operatorname{Tr}(abx)$ tests $b$ against $ax\in O$ for $a,x\in O$. Clear a common nonzero denominator $D\in O$ in the $b_i$. Multiplying the trace dual by $D$ gives an ideal of $O$, with generator $g$. Thus the trace dual is $\delta O$ for $\delta=g/D$. Choose $f_i$ by $b_i=\delta f_i$ and use $\lambda(a)=\operatorname{Tr}(\delta a)$. Trace duality supplies the reconstruction. In particular, $a\in O$ exactly when all $\lambda(f_i a)$ belong to $R$.

The maps $[a]\mapsto[\lambda(o a)]$ are well defined and commute with $\chi(g)$ because $\chi(g)$ is a base scalar. The reconstruction map sends a finite tuple $([b_i])_i$ to $[\sum_i e_i b_i]$ and is well defined since $R\subset O$. These maps commute with $\partial$. Compose a given witness with each scalar map to prove necessity. For sufficiency, choose one locally constant witness for each $f_i$ and apply the reconstruction map pointwise. It is locally constant by a finite intersection of neighborhoods, and its differential is $[z]$ by reconstruction. This argument also applies to two-cochains before any cocycle condition is checked. [A2, `ExistsIntegralDualFunctional.lean:10–142`; `CoboundaryModIffForallTraceFormCoboundary.lean:11–111`.]

##### Theorem (integral local duality with general coefficients) [Lean, read]
 For every $\ell,\mathcal P,K$ as above, assume `Published.BlochKato.IntegralDuality (P.PD K)`: for the standard rank-one cyclotomic $R$-lattice and every pair of finite-dimensional continuous $k_0$-representations with stable finite free spanning $R$-lattices, original-side de Rham and the same rational and exact lattice duality conditions over $R$, the following two clauses hold over $R$. Then for every $F,O,L_1,A,A',L,L',P$ satisfying the stated hypotheses, both clauses hold over $O$:
$$
\begin{aligned}
 \forall c\in Z^1(D'),\quad
 c\in\mathcal F(D') &\iff \forall d\in Z_f^1(L),\ \exists f\text{ locally constant},\ \partial f=u(d,c),\\
 \forall d\in Z^1(L),\quad
 d\in Z_f^1(L) &\iff \forall c\in Z^1(D')\cap\mathcal F(D'),\
 \exists f\text{ locally constant},\ \partial f=u(d,c).
\end{aligned}
$$
The witness takes values in $(F/O)(\chi)$ and can depend on the tested pair. The two equivalences identify the exact annihilators inside their respective cocycle domains. [A2, `RationalDualityOfAllCoefficients.lean:41–57`; `BlochKatoAnnihilatorOfIntegralLocalDuality.lean:259–340`.]

**Proof.** Restrict scalars on both representations to $k_0$. A finite $F$-basis identifies the original topology with the product topology on copies of $F$, hence also gives the $k_0$-module topology. Addition and constant $k_0$-scalar multiplication are continuous, and the orbit maps are unchanged. The two diagonal period actions on tensors over $k_0$ are unchanged on simple tensors and hence everywhere. The same $w$ witnesses the finite condition. The underlying de Rham invariant vectors are unchanged, and restricting scalars multiplies both sides of the de Rham dimension equality by $[F:k_0]$.

Keep the same subsets $L,L'$ as $R$-lattices. An $O$-generating family $t_j$ becomes the $R$-generating family $e_i t_j$, by the reconstruction formula and $\lambda(O)\subset R$. The lattice is torsion-free over the DVR $R$, so finite free. Its $k_0$-span is stable under every scalar $a\in F$ since $at=\sum_i\lambda(f_i a)e_i t$ for $t$ in the lattice. Therefore it spans over $k_0$. Stability under $G$ is unchanged. The two quotient constructions are identified by the additive bijection $q$ carrying the class of every vector to the class of that same vector. It intertwines the actions, preserves local constancy in both directions, and transports the formula $c(g)=[z(g)+gv-v]$ with the very same $z,v$. Integral cocycle membership and integral finite membership also agree because the lattice predicates and the finite criterion agree.

The restricted pairing is $P_R(x,y)=\lambda(P(x,y))$. Its twist character is unchanged by base linearity. If $x$ pairs to zero under $P_R$ with all $y$, test also against $f_i y$ and reconstruct $P(x,y)=0$ for all $y$. Testing $f_i x$ proves the other radical vanishes by the same calculation. Ranks multiply by $[F:k_0]$. If $y\in L'$, then $P_R(L,y)\subset R$. Conversely, if $P_R(L,y)\subset R$, test against $f_i x\in L$ for each $x\in L$. Reconstruction gives $P(L,y)\subset O$ and exact duality gives $y\in L'$. These checks allow application of the assumed $R$-theorem, with its standard cyclotomic lattice. [A2, `BlochKatoAnnihilatorOfIntegralLocalDuality.lean:16–57,62–141,259–297`; `ZlLatticeOfCoefficientLattice.lean:10–109`; `DualLatticeRestrictScalarsTraceForm.lean:9–76`; `DeRhamPotSemistable.lean:20–52`.]

For an integral $d$, the $R$-cup of $d$ and $q c$ is the image of $u(d,c)$ under the scalar quotient map for $o=1$. Indeed the two sections differ by a vector of the common lattice and the resulting scalar difference is in $\lambda(O)\subset R$. More generally the test for $o$ is the $R$-cup with $o d,q c$, or with $d,q(o c)$. In the latter description the representative of $o c(h)$ can differ from $o$ times the representative of $c(h)$ by a lattice vector, which has zero effect in the quotient. All these comparisons are pointwise before testing for a single locally constant coboundary witness.

For the first clause, if $c$ is finite, then $q c$ is finite and for each $o\in O$ and finite integral $d$, $o d$ is still finite integral. The $R$-theorem therefore gives the $o$-test. The scalar-coordinate lemma reconstructs the required witness over $O$. Conversely, if every finite integral $d$ has an $O$-witness, project it by $\lambda$ (the test for $1$). Every $R$-finite integral cocycle has the same function as an $O$-finite integral cocycle. The reverse implication of the first $R$-clause gives finiteness of $q c$, hence of $c$.

For the second clause, if $d$ is finite, take each tested finite quotient cocycle $c$ and every $o\in O$. The cocycle $o c$ remains in both $Z^1(D')$ and $\mathcal F(D')$. Apply the second $R$-clause with $q(o c)$ and reconstruct the witness. Conversely, assume all the $O$-witnesses for $d$ exist. Any tested finite quotient $R$-cocycle pulls back via $q^{-1}$ to a finite quotient $O$-cocycle. Project the resulting witness by $\lambda$. The second $R$-clause now gives integral finiteness of $d$. [A2, `BlochKatoAnnihilatorOfIntegralLocalDuality.lean:152–204,298–340`.]

**Remarks on the arithmetic input.** Bloch and Kato define the rational $f$-condition by the crystalline-period kernel at $\ell=p$ and the integral condition by inverse image. Proposition 3.8 supplies exact annihilators in the local Tate pairing, with original-side de Rham at $\ell=p$ and the other side its cyclotomic dual. Passing from classes to the displayed cocycle test uses the image on the divisible side, whose inverse image among cocycles includes all quotient coboundaries. Rubin's Remark 1.3.6 explains the at-$p$ convention, Lemma 1.3.8(i) identifies the relevant finite-level images, and Proposition 1.4.3(c)(i)–(ii) uses rational finite conditions already known to be exact orthogonal complements at $p$. The finite-level torsion group there is separate from the full divisible quotient here. A perfect pairing alone places no constraint on two independently assigned subgroups. Applying the classical result in a particular period model requires comparison to its classical cohomology and period rings. The archive's `IntegralDuality` is an explicit input for its chosen datum. [Bloch–Kato, pp. 353–354](https://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKTamagawa.pdf) · [Rubin, pp. 14–19](https://wstein.org/people/rubin/book/hEulerSystems.pdf)

The arithmetic coefficient and dual-lattice hypotheses have nonzero-rank examples in the classical setting. Take $V=k_0$ trivial, $V'=k_0(1)$, $L=R$, $L'=R(1)$, standard multiplication, and $F=k_0$. The trivial representation has $D_{\mathrm{dR}}=K$ by the fixed-ring condition and hence satisfies the required dimension identity. The standard cyclotomic lattice is stable and the duality condition reads $y\in R$ exactly when $Ry\subset R$. In the archive this specialization still takes the declared `IntegralDuality` input. Zero cocycles are always available on both sides. The finite examples below establish sharper nonemptiness and strict failures for the algebra of the tests.

**Connection to the lifting criterion.** The direct caller `bkAll_of_blochKatoLocal` extracts `hInt` from `BlochKatoLocal` and invokes `T.blochKato_annihilator_of_integralLocalDuality` to supply `hB`. In the same caller `hRat` separately supplies `bkACore`, and `LocalTateDualityK` and `LocalEulerCharK` enter the separate Part C assembly. In §10.4.7.11 the specialization of `lift_iff` reads `bkBCore` from the local slot of `GalHyp` and calls only its first clause on the divided residual cocycle against all integral finite testers. The uniformizer step and `IsFCoc` identification are those of that subsection. `LocalH2Injective.h2_inj` enters the later residual descent in `bkOn_orthogonal`. The production of deep local Tate duality and of the abstract arithmetic input, and the dependency path to `Main`, remain separate verification questions. [A2, `BlochKatoLocalAllPrimesOfBlochKato.lean:18–30`; `LiftBlochKatoCocycleIffOrthogonalLattice.lean:229–230,278–316`; `ResidualBlochKatoLatticeDualOrthogonal.lean:94–134,176–193`; LUMI Frontier K §1.8.]
**Hand calculations [Expository].** Use the following two finite groups to isolate the cochain algebra. The sign character in these models is a twist of the coefficient module. For the rational finite condition take all rational cocycles, which are all coboundaries by averaging in characteristic zero. This is also the tensor-period kernel for the auxiliary choice of base field with trivial action as the tensor algebra. These models certify the algebra of the tests independently of the local-field period hypotheses.

For both groups let $G=C_n=\langle s\rangle$, $n$ even, and put $\epsilon_i=(-1)^i$ and $I_i=(1-\epsilon_i)/2$. On $V=F^2$ let $s$ act as $\operatorname{diag}(-1,1)$ and on $V'=F^2$ as $\operatorname{diag}(1,-1)$. Use the dot product with sign target and $L=L'=O^2$, exactly dual by the two standard basis tests. Write $D=F/O$. A cocycle is determined by its value at $s$. Summing the orbit of that value for the relation $s^n=1$ gives the complete parametrization
$$
 d(s^i)=(I_i a,0),\quad a\in O,\qquad
 c(s^i)=(i b,I_i v),\quad b\in D[n],\ v\in D.
$$
Indeed $na_2=0$ in $O$ forces the second integral coordinate to vanish, and the norm in each sign coordinate is zero. The rational coboundary of $(-a/2,0)$ gives $d$, so $Z^1_f(L)=Z^1(L)$. For the quotient function to be finite, its first coordinate must vanish since rational cocycles into the trivial coordinate and all quotient coboundaries there are zero. For every $v$ in the second coordinate choose a lift $w$ and take the rational coboundary of $(0,-w/2)$ to obtain that coordinate. Thus the finite quotient group is precisely $b=0$, with arbitrary $v$.

The reduced cup is $U(i,j)= I_i a j b$. For any normalized sign-valued two-cocycle $U$ with values in $D$, the obstruction is
$$
 S(U)=\sum_{i=0}^{n-1} U(i,1).
$$
For a coboundary this sum vanishes by telescoping and $\sum_i\epsilon_i=0$. Conversely, if $S(U)=0$, take $f(0)=f(1)=0$ and set $f(i+1)=f(i)-U(i,1)$, which closes at $i=n$. Now $U-\partial f$ vanishes at $(i,1)$ and is normalized. The two-cocycle identity at $(i,j,1)$ makes its value at $(i,j+1)$ equal to that at $(i,j)$, so it vanishes identically. For the displayed cup the obstruction is $(n/2)ab$.

**First calculation.** Take $n=2$, $F=\mathbb Q$, and $O=\mathbb Z_{(2)}$. Here $D[2]=\{0,1/2+O\}$. With $a=1$, $b=1/2+O$, and $v=0$, the cup has the single nonzero entry $U(1,1)=1/2+O$. Thus the left tests force $b=0$ and every such quotient cocycle gives the zero cochain. The other annihilator is all of $Z^1(L)$, as required. For a nonzero finite quotient cocycle take $v=1/4+O$. Its representative in the rational coboundary is $(0,-1/8)$ and the cup with every integral cocycle is zero. Over cohomology the first-coordinate pairing is the perfect multiplication pairing between $O/2O$ and $D[2]$.

**Second calculation.** Take $n=2$, $F=\mathbb Q(\pi)$, $\pi^2=2$, and $O=\mathbb Z_{(2)}[\pi]$. The Eisenstein DVR has uniformizer $\pi$. Explicitly for $a+b\pi$ the two summands have distinct normalized valuations $2v_2(a)$ and $2v_2(b)+1$, and their minimum detects membership in $O$. With $R=\mathbb Z_{(2)}$, the trace-dual basis to $(1,\pi)$ is $(1/2,\pi/4)$, and $\delta=\pi/4$ generates its $O$-span. Hence $\lambda(a+b\pi)=b$, and $f_0=\pi,f_1=1$ give $x=\lambda(\pi x)+\pi\lambda(x)$.

Here $D[2]$ consists of the four classes represented by $0,1/2,\pi/2,(1+\pi)/2$. For $a=1$ the obstruction is $b$ itself. For example, $b=1/2+O$ gives a single nonzero entry, and its two scalar tests for $1,\pi$ have obstructions $0,1/2+R$, respectively. Thus the quotient annihilator has exactly $b=0$ with arbitrary $v$, and the integral annihilator is all integral cocycles. With $v=\pi/4+O$ a nonzero finite quotient cocycle comes from the rational coboundary of $(0,-\pi/8)$ and cups to zero. The cohomological pairing of $O/2O$ and $D[2]$ is perfect: writing $b=B/2+O$ identifies $D[2]$ with $O/2O$, and testing against the unit in each slot detects every nonzero class. The induced map into the $O$-linear dual with values in $D$ is surjective because such a functional is determined by the image of $1$, which can be any element of $D[2]$.

**A $C_4$ failure and an exact nonzero cup.** Keep the second DVR and take $n=4$. Choose $a=1$, $b=\pi/4+O$ and $v=0$. The two odd rows have entries $0,\pi/4,\pi/2,3\pi/4$ modulo $O$, and the even rows vanish. The obstruction is $\pi/2+O\ne0$. For another nonzero cup take $b=1/2+O$. Its obstruction is $1+O=0$, and the primitive given by the recursion has values $(0,0,-1/2,-1/2)$ modulo $O$. The full first annihilator for the chosen finite condition is $b\in D[2]$, since testing $a=1$ forces $2b=0$, and $2b=0$ suffices for every $a$. This is strictly larger than the finite subgroup $b=0$. The second annihilator is again all integral cocycles. Thus the arithmetic input of the theorem cannot be supplied by the finite group and the dual lattices in this model.

For the scalar test itself choose $a=1$, $b=1/4+O$. The obstruction is $1/2+O$, but $\lambda$ kills every entry. The test for $\pi$ recovers the rational entries and obstruction $1/2+R$. Conversely, for the exact cup with $b=1/2+O$ the scalar witnesses for $\pi$ and $1$ are respectively $(0,0,-1/2,-1/2)$ and zero, so combining the two via $(1,\pi)$ recovers the displayed primitive. These computations distinguish the trivial scalar test from the full family.

**Failure boundaries.** In the first model, keep the perfect cohomological pairing and designate the full quotient cocycle module as finite while leaving the integral finite module unchanged. The two chosen finite subgroups then pair nontrivially, witnessed by $a=1$ and $b=1/2+O$. This refutes the inference from abstract perfect duality to independently assigned local conditions. In the second model, the exact arithmetic annihilator input fails even with the tensor-kernel definition just described. Neither example tests whether the de Rham hypothesis can be removed in the classical arithmetic theorem.

Finally, in the first model replace the dot product by half the dot product and keep both lattices. This retains equivariance and both rational nondegeneracy tests, but loses integrality on the pair of lattices. Use $a=1$ and $c(s)=(1/2+O,0)$. Changing the section at this quotient value from $(1/2,0)$ to $(3/2,0)$ changes the cup at $(s,s)$ by $1/2+O$. Both lifts are genuine sections there, so even the reduced cochain depends on the section. The theorem uses the forward integrality implication to avoid this failure and the reverse lattice implication separately in transporting exact duality.

##### What these examples check in the Selmer argument [Expository]

The residual local condition above $\ell$ uses reductions from the saturated integral finite cocycles on the chosen DVR. The odd-prime and dyadic examples in §10.4.7.11 show why the residual local invariant space may contribute even when the rational invariants vanish, and why a residual cup can require a primitive in a larger torsion stage. The saturation example changes the image defining the local condition, the pairing scaled by $3$ loses a tester, and the enlarged lattice loses the integral section comparison. The two $C_2$ models here illustrate both annihilators, the $C_4$ model distinguishes the arithmetic input from the algebra of restriction of scalars, and the trace and section examples show where the full scalar family and the integral lattice pairing enter.

In `ResidualSelmerFinrankEqDual.lean:219–249`, the two residual consumers give the exact local annihilator at $v\mid\ell$. This is the local comparison used in the conditional Greenberg–Wiles count. The resulting `EqDim` is passed to `ChooseH` and to the first-order determinant bound in the odd-prime and dyadic wrappers. Those wrappers supply the Selmer coefficient bounds for the auxiliary-place family in §10.4.7.4, which the all-powers twist construction in §10.4.7 consumes. The two uses of `adm2` there have distinct interfaces. `BlochKatoReduction.adm2` is valuation stability, and its value enters `GalHyp` through `AdmACD`. The `bkBCore` projection comes from `Gen.adm3`. `IntegralHeckeForms.adm2` is the single-character witness obtained by taking $a=1$ in the all-powers construction. [Auxiliary-twist argument](#1047-where-does-adm2-come-from) · [Source ledger](../sources/SOURCES.md#chapter-10-blochkato-lattice-lifting-and-integral-annihilators)

### 10.4.8 From tame inertia to the order of a Selmer determinant

#### Motivation

Choosing auxiliary places gives two kinds of control. At a second-half place the residual representation is trivial on the decomposition group, so a residual cocycle is additive there. Meanwhile the first-half characters give prescribed coordinates on the second-half Frobenius. The first-order twist combines these facts: Frobenius conjugation of inertia forces a linear relation between the leading values of a liftable cocycle. A matrix computing continuous Selmer cohomology transfers that relation to its first-order kernel. This section follows that supply chain for both order bounds of §10.4.7. The scalar quadratic-relation estimate in §10.4.5 belongs to the congruence-length calculation in Theorem 10.2.

#### Example 10.7. A finite DVR module and a first-order kernel

Over $O=\mathbb Z_3$, let
$$
A(T)=\begin{pmatrix}3+T&0\\0&9+T^2\end{pmatrix}.
$$
At $T=0$ take coefficients in $O/(27)$. The equations $3x=0$ and $9y=0$ give
$x\in 9O/27O$, $y\in 3O/27O$. There are $3\cdot9=27$ solutions and the length is $1+2=3$.
The integral cokernel is $O/(3)\oplus O/(9)$, with the same length $v_3(27)=3$.
Here $\operatorname{len}_O(O/(3))=1$, so division by this factor gives normalized length $3$.

On the residual polynomial line in characteristic $3$ the matrix is $\operatorname{diag}(T,T^2)$.
A leading vector $x_0$ admits a lift $x_0+Tx_1$ to the kernel modulo $T^2$ exactly when its first coordinate vanishes.
Thus the space of leading vectors is one-dimensional, although the constant matrix has a two-dimensional
kernel. The determinant has order $3$ and the adjugate $\operatorname{diag}(T^2,T)$ has an entry of order $1$.
For comparison, $\operatorname{diag}(T,T)$ has zero space of liftable leading vectors and determinant
of order $2$. This arithmetic model illustrates both matrix tests. The finite specialization and
the residual line measure different quantities.

#### Definitions and hypotheses

Write $O_0=X.O0(i)$, $k=O_0/\mathfrak m$, $r=D.R.r$, and $I_R=\mathrm{Fin}(R)\sqcup\mathrm{Fin}(R)$.
The group ring $\Lambda$ is $O_0[(\mathbb Z/\ell^M)^{I_R}]$. The map `toLam` sends $X_q$ to the
$q$-th group generator minus $1$. The twisting factor is the **inverse** of the joint
character $d=(d_q)_q$. `IsRes` means the scalar map kills $\mathfrak m$.

For a discrete coefficient module $B$ with the indicated Galois action, $Z^1(G,B)$ consists
of the continuous functions satisfying $z(gh)=z(g)+g z(h)$. The submodule $B^1(G,B)$ consists of
$g\mapsto gm-m$. The source uses $H^1=Z^1/B^1$ and imposes the local conditions on **classes**
in that quotient. At an element acting as the identity, evaluation on $H^1$ is well-defined
because every coboundary evaluates to zero there. On a whole residually trivial decomposition
group the restriction of a residual cocycle is additive. For discrete coefficients continuity
is equivalent to local constancy. Finite image on a profinite group follows by compactness,
and finite module length in a DVR calculation requires a separate torsion bound.
`src/Formalism/GaloisCohomology/Statement.lean`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerDeterminantOrderBound.lean:25–32`.

The hypotheses of the order argument are the archive's `TameLocal`, `GalHyp`, `FirstHalf`,
`Recip`, and `EqDim`, with `Position`, `IsQ` and `Computes` for the chosen data.
`TameLocal.1` gives `TameQuotient`. `Position` supplies two disjoint families up to conjugacy,
the norm congruence and character conditions, the `Steps` coordinates, and residual
triviality on each second-half decomposition group with Frobenius $\phi_a$ and conjugate
$\phi'_a$. `IsQ` identifies $Q$ with the places over the selected pairs. `FirstHalf` gives
vanishing of local $H^0,H^1,H^2$ at first-half places for the specified twisted torsion
coefficients and both representations. `Computes` is a functorial identification of the
matrix kernel over each discrete $\ell$-power-torsion coefficient module with the
$Q$-relaxed Selmer submodule of $H^1$. It applies to $k$ and to the discrete dual numbers.
`EqDim` records finite-dimensional unrelaxed residual Selmer spaces of equal dimension for
the representation and its dual. The public wrapper takes it, and its proof uses the
separately supplied `Corank` condition at the matrix stage.
`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsDualDualRep.lean:23–35,65–140`,
`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTameInertiaElementAtTwistPrime.lean:92–110`.

#### Lemma 10.14. The tame relation on a dual-number cocycle

Assume `TameQuotient` at a place $v\nmid\ell$ with chosen place above it, $M\ge1$ and
$q=Nv\equiv1\pmod{2\ell^M}$. Let $d$ be a character to the additive cyclic group
$\mathbb Z/\ell^M$ with open kernel and surjective restriction to inertia $I$.
Fix a Frobenius $\phi$ at the chosen place. There is $\gamma\in I$ with $d(\gamma)=1$
in additive notation such that the following holds for every field $K$ of characteristic
$\ell$ and $K$-module $W$. If $z_0$ is locally constant and additive on the decomposition
group $D_v$, then $z_0(\gamma)=0$ implies $z_0|_I=0$. If $\lambda$ and $z_1$ are also
locally constant, with $\lambda$ additive on $D_v$ and
$$
z_1(gh)=z_1(g)+z_1(h)+\lambda(g)z_0(h)\qquad(g,h\in D_v),
$$
then $\lambda(\gamma)z_0(\phi)=\lambda(\phi)z_0(\gamma)$.
[Lean, read]
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TameLocalRelationDualNumberCocycleStatement.lean:9–10`.

*Proof.* Let $J$ be the kernel of the pro-$\ell$ tame inertia quotient. The source hypothesis
gives an inertia lift $\gamma_0$ whose powers together with $J$ are dense in $I$, and
$\phi\gamma_0=\gamma_0^q j\phi$ for some $j\in J$. Every open normal subgroup of $J$ has
index prime to $\ell$. A homomorphism from $J$ with open kernel to a group of exponent
$\ell^n$ is trivial: the order of each image divides both the kernel index and $\ell^n$.
This kills $d$ on $J$ and kills any locally constant additive $K$-valued or $W$-valued
map on $J$. The preimage under $d$ of the subgroup generated by $d(\gamma_0)$ is open
because it contains the open kernel. It is also closed, contains $J$ and the powers of
$\gamma_0$, and hence contains $I$. By surjectivity there is an integer $b$ with
$b\,d(\gamma_0)=1$ in $\mathbb Z/\ell^M$. Use $\gamma=\gamma_0^b$. Reduction of this
identity in $K$ gives $b\ne0$ in $K$. Additivity gives
$z_0(\gamma)=b z_0(\gamma_0)$, so vanishing at $\gamma$ gives vanishing on the dense
subgroup generated by $\gamma_0$ and $J$. The zero fiber of a locally constant map
is closed, which proves vanishing on $I$.

For the second conclusion, $\lambda$ vanishes on $J$, and $z_1$ is additive there since
$z_0|_J=0$. Hence $z_1|_J=0$ as well. Induction, using
$\lambda(\gamma_0^n)=n\lambda(\gamma_0)$ and the binomial recursion, gives
$$
z_1(\gamma_0^n)=n z_1(\gamma_0)+\binom{n}{2}\lambda(\gamma_0)z_0(\gamma_0).
$$
The constant at $n=0$ is zero by the cocycle law at the identity. Since $q-1$ is a
multiple of $2\ell^M$, $q$ becomes $1$ in $K$ and the integer $\binom{q}{2}$ becomes $0$.
The factor $2$ in the congruence gives this conclusion also in characteristic two.
Now expand $z_1(\phi\gamma_0)$ as $z_1(\gamma_0^q j\phi)$. After cancelling the two
$z_1$ values the identity is $\lambda(\phi)z_0(\gamma_0)=\lambda(\gamma_0)z_0(\phi)$.
Multiplication by $b$ gives the result. $\square$
`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean:116–133`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TameLocalRelationDualNumberCocycle.lean:13–159`.

#### Proposition 10.15. From the local relation to the two order bounds

Assume the named hypotheses above, with $4rR+2<\ell^M$ and an $a\times a$ matrix
$\Phi$ over $\Lambda$ satisfying `Computes`. With `Corank` at $e=0$, every polynomial
lift of $\det\Phi$ through `toLam` has a unit coefficient of total degree at most $4rR$.
With `Corank` at $e=1$, either $a=0$ or there is an entry of $\operatorname{adj}\Phi$
for which every polynomial lift has such a coefficient. Here `Corank` at $e$ asserts
that suitable coefficients in the Frobenius pairings against all unrelaxed dual Selmer
classes cut the possible independent unrelaxed classes down to at most $e$.
[Lean, read] for the conditional argument.
`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsDualDualRep.lean:126–142`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerDeterminantOrderBound.lean:118–350`.

*Proof.* Lift $\Phi$ entrywise through the surjection `toLam`. Let $V$ be its kernel over
$k$ via augmentation. The residual transfer of `Computes` gives an injection
$E:V\hookrightarrow H^1$, with image satisfying the relaxed local conditions, and supplies
the compatible cocycle representatives used below. The dual representation in `Recip` is
the inverse transpose of the original, scaled by `eps0`. Choose $\gamma_a$ by Lemma 10.14
for each second-half character. Let $c_a\in k^\times$ be the reciprocity weights at the
pairs $(\gamma_a,\phi_a)$ and their conjugates, and $c^0_a\in k$ the `Corank` weights at
$(\phi_a,\phi_a)$ and their conjugates. On $V$ put $t$ equal to evaluation of $E$ at
$\gamma_a,\gamma'_a$, and $u$ equal to evaluation at $\phi_a,\phi'_a$ scaled by
$s_a=c^0_a/c_a$. Both maps have target $U=(k^r\times k^r)^R$. These evaluations
descend through coboundaries by residual triviality, also at the conjugate elements.

Suppose $t x_0=0$ and $t x_1=u x_0$. The first equality and Lemma 10.14 remove the
second-half inertia values, including at the conjugate places. The relaxed-to-unrelaxed
transfer, using `FirstHalf`, puts $E x_0$ in unrelaxed Selmer. In the reciprocity sum
for a representative of $E x_1$, the second equality replaces each inertia evaluation
by $s_a$ times the corresponding Frobenius evaluation of $E x_0$. The factor
$c_a s_a=c^0_a$ yields exactly the `Corank` sum for $E x_0$ against every unrelaxed
dual class. Therefore no $e+1$ independent $x_0$ can satisfy these equations, since
$E$ is injective. On $\ker t$ consider $u$ modulo $\operatorname{im}t$. Its kernel has
dimension at most $e$, and its image has dimension at most $\dim U-\dim\operatorname{im}t$.
Rank–nullity gives $\dim V\le 2rR+e$. After extension of scalars the constant matrix
kernel still has dimension at most this value, since independent columns in the
original image remain independent.
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerDeterminantOrderBound.lean:131–197`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankKerMapLeOfFirstOrderKernelExt.lean:5–70`.

Use $K=k((\sigma))$, represented by Hahn series with integer exponents, and
$\beta_a=\sigma s_a$. Specialize the polynomial entries along $X_q=b_qT$, with
$b_{\mathrm{inr}(a)}=\beta_a$ and
$$
b_{\mathrm{inl}(a)}=1-\sum_j\beta_j\,\overline{d_{\mathrm{inr}(j)}(\phi_a)}.
$$
Bars on characters denote additive coordinates reduced to $K$. Modulo $T^2$ this
sends each group element $\delta$ to $1+T\sum_q b_q\bar\delta_q$. It is multiplicative
because $T^2=0$, has augmentation as constant term, and evaluation of a polynomial
retains just its constant and linear coefficients. The inverse twisting character
has linear coefficient $\lambda(g)=-\sum_q b_q\overline{d_q(g)}$. It is locally
constant by the open kernels, additive, and changes sign under conjugation by the
CM involution because the characters are anticyclotomic.

Write $\Psi=A+TB+\cdots$ for the resulting polynomial matrix. A vector
$x_0+T x_1$ in its kernel modulo $T^2$ satisfies exactly
$$A x_0=0,\qquad B x_0+A x_1=0.$$
The transfer of `Computes` represents it by a continuous twisted cocycle
$w=w_0+T w_1$. At the second-half decomposition group the base action is the
identity after reduction, so its cocycle law is the law of Lemma 10.14 with $z_j=w_j$.
The `Steps` Kronecker coordinates give $\lambda(\phi_a)=-1$ by the choice of
$b_{\mathrm{inl}(a)}$. At $\gamma_a$ only the character of its own place is nonzero,
and its additive value is $1$, giving $\lambda(\gamma_a)=-\beta_a$.
Lemma 10.14 now gives $w_0(\gamma_a)=\beta_a w_0(\phi_a)$. Apply it also to
the cocycle composed with complex conjugation. Both $\lambda$ values change
sign, giving the same ratio for the conjugate pair.

For each $k$-linear functional $p:K\to k$, compose constant-term projection
on the dual numbers with $p$, and separately with $p(\sigma\,\cdot)$. These
are module maps for the augmented action. Functorial transfer gives vectors
$x,x'\in V$ whose coordinates are $p(x_0)$ and $p(\sigma x_0)$, with classes
represented by $p(w_0)$ and $p(\sigma w_0)$. The two local relations then give
$t x=u x'$. The property of admitting these pairs for all $p$ is stable
under $K$-scaling (precompose $p$ with multiplication) and subtraction.
Normalize a nonzero leading vector by its coordinate of smallest series
order so that this coordinate is $1$ and all coordinates have nonnegative
order. With $p$ equal to coefficient extraction at $0$ we get $t x=0$,
since the constant coefficient of $\sigma x_0$ vanishes. With $p$ equal
to extraction at $1$ we get a witness $y$ with $t y=u x$. The reduction
$x$ has a coordinate $1$. If there are two independent leading vectors,
subtract a multiple of the first from the second to zero its pivot
coordinate before normalizing the second. Their reductions are independent
because the second retains its zero at the first pivot and has a $1$
at another coordinate. In either case $e=0,1$, this contradicts the
bound over $k$ on independent leading vectors.
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerDeterminantOrderBound.lean:198–322`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentDegenerationFirstOrderKernel.lean:6–124`.

Finally put $\nu=\dim\ker A$. For $e=0$, diagonalize $A$ over $K$ using constant
determinant-one row and column operations. Use the resulting column basis to
factor $T$ from each of the $\nu$ columns with zero constant term. The
constant matrix after division has trivial kernel: a kernel vector splits
into the coordinates of those $\nu$ columns and the remaining coordinates,
giving a leading vector and a correction satisfying the two first-order
equations. The leading vector must vanish. The remaining columns have
independent constant terms, so the correction vanishes. Thus the determinant
has order $\nu\le 2rR$, which gives the weaker bound $4rR$ used by `resBound`.

For $e=1$ and $a>0$, set $m=2rR$. If $m=0$, $\nu\le1$ gives a nonzero
constant cofactor. Otherwise use determinant-one row and column operations
to diagonalize $A$ and divide the $\nu$ zero constant **rows** by $T$.
The new constant matrix has nullity at most one: each kernel vector
vanishes in the nonzero diagonal coordinates, and its linear-coefficient
image vanishes on the zero rows. On each nonzero row choose the correction
as minus that linear-coefficient value divided by the diagonal entry.
This produces a first-order lift, so two independent kernel vectors are
excluded. A square matrix of nullity at most one has a nonzero cofactor
(diagonalize and omit the possible zero diagonal entry). This includes the
$1\times1$ case with empty minor $1$. Restoring the row factors adds at most
$\nu$ to that cofactor's order, since only rows retained by the minor add
a factor of $T$. If every original adjugate entry were divisible by
$T^{2m+1}$, the same would hold after constant changes of basis, contradicting
this entry's order at most $\nu\le m+1\le2m$.
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotXPowSuccDvdDetOfFirstOrderKernelEqZero.lean:6–130`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean:10–237`.

Apply the order test with $n=4rR+1$. In $K[T]/(T^n)$, $(1+b_qT)^{\ell^M}=1$
by characteristic $\ell$ and $n\le\ell^M$. Taking products of powers of these
elements therefore defines an algebra map from the group ring, and its composite
with `toLam` is exactly the line substitution modulo $T^n$. Two polynomial lifts
of the same determinant or selected adjugate entry thus have the same image.
If every coefficient of degree below $n$ in a lift belonged to $\mathfrak m$,
these coefficients would reduce to zero and higher terms would be divisible by
$T^n$. This contradicts the order test. A coefficient outside the maximal ideal
is a unit, as asserted. $\square$
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitCoeffOfNotXPowDvdLine.lean:9–80`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerDeterminantOrderBound.lean:324–350`.

#### What the two order bounds read from stepAB

[Section 10.4.13](#10413-choosing-the-auxiliary-primes-in-a-common-galois-quotient) proves the two-batch selection and the conjugacy test for Selmer evaluations.

`stepAB` first selects left places with Frobenius represented by the designated tame
element $z$ modulo the open normal subgroup $W$ (intersection of the requested
subgroup, the admissible subgroup, and the root-fixing subgroup). The left characters are
surjective at their own inertia and trivial at the other selected left inertias.
Products of these inertia elements correct each right-hand target $h_a$ inside $W$
so that its left-character values are the Kronecker coordinates. The second selection
uses $W\cap\bigcap_b\ker d_{\mathrm{inl}(b)}$, preserving these coordinates at the
right Frobenius even after conjugation, since the characters are abelian.
The root-fixing constraint supplies $Nv\equiv1\bmod 2\ell^M$.
The output also keeps the auxiliary places distinct up to conjugacy, places all
their inertias inside the requested subgroup, and specifies the right Frobenius
congruence to the original $h_a$. Chebotarev and the good-character conditions are inputs
to this selection argument.
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAuxiliaryPrimesPrescribedFrobenius.lean:274–418`.

- With $\nu(X,i)=0$, the residual branch reads the chosen places, inertia and
  Frobenius congruences to put the right decomposition groups in the small subgroup
  $L$ and build `Position`. The `ChooseH` witness supplies `Corank` at $0$.
  It applies the determinant half of `ResBound`, and the unit coefficient has DVR
  valuation zero.
  `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualBoundOfComponents.lean:28–57`.
- With $\nu(X,i)>0$, the other branch appends identity targets for the finite list of
  signatures, retains the first $R_0$ right places for the initial test and uses the
  other left places in its induction. `StartInd.start_of_galHyp` restricts the group
  ring to the retained coordinates and uses first-half unramifiedness to transport
  `Computes`. The chosen Frobenius congruences supply `Corank` at $1$ and `Position`
  for the adjugate half of `ResBound`. The resulting coefficient extends back with
  zero exponent on the discarded coordinates ([§10.4.7.6](#10476-producing-the-initial-adjugate-seed-scalar-descent-unused-left-places-and-the-ramified-ideal-threshold) reads the full production proof of `StartInd.start_of_galHyp` / `start_of_resBound` and its `TameScalar` and `SmallSub` suppliers). `Start` then feeds the separate `Grow`
  and `Step` induction, whose determinant coefficient is bounded in valuation.
  `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValLeOfNotMem.lean:87–144`,
  `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousCocycleChangeScalarsBack.lean:452–498`,
  `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BoundModTwoUniformizerAtTwoOfChebotarev.lean:25–35`.

#### Remarks on units, length and the reading boundary

The unit in Proposition 10.15 is detected by a nonzero residue of a coefficient.
The unit root-difference input `IsUnit (del51 ...)` in the GMA calculation is a
different hypothesis: it normalizes the rank-one quasi-idempotent $E_{\mathrm{el}}$
with $E_{\mathrm{el}}^2=\delta_{51}E_{\mathrm{el}}$ and gives the zero coboundary-length
term where used in Theorem 10.2. The familiar two-root unit-discriminant test is
$\operatorname{disc}((X-\alpha)(X-\beta))=(\alpha-\beta)^2$ is a unit exactly when
$\alpha-\beta$ is a unit, for example $1,-1$ over $\mathbb Z_3$. The local argument
of Lemma 10.14 requires the tame norm congruence and the indicated action on the
cocycle, and has no unit-discriminant hypothesis. In the neighboring scalar
`QuadAt` calculation the torsion budget uses $\zeta_v-1$, which can be a nonunit.
`src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:56–62`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:61–88`.

For a square matrix over a DVR $O$ with nonzero determinant, elementary divisors
$u_j\varpi^{n_j}$ give both cokernel length $\sum_j n_j$ and the same kernel length
on $(\operatorname{Frac}(O)/O)^a$ by taking $\varpi^{n_j}$-torsion in each coordinate.
With zero determinant a zero diagonal factor contributes infinite length in
this divisible module. Finite length permits ordinary integer lengths and
normalization by the positive factor $\operatorname{len}_O(O/(\ell))=v_\varpi(\ell)$.
The residual order along $T$ is a polynomial order. Upon specializing the twisting
characters to roots of unity, the determinant becomes the evaluation at their values
minus $1$. The equality between its normalized valuation and twisted Selmer length
uses `Computes` and
`twisted_selmer_lengths_eq_determinant_valuation` [Lean]. This is separate from the
finite-length arithmetic of Example 10.7.
`src/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean:32–33`,
`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTameInertiaElementAtTwistPrime.lean:109–116`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedSelmerLengthsEqDeterminantValuation.lean:330–385`.

Classical background is Serre's *Local Fields*, Chapter IV, “Ramification Groups”
[SerreLocalFields]. The first-order cocycle argument above follows the archive.
The upstream `TameQuotient` producer, `matrixComputesTwistedSelmer_residual_transfer`,
`relaxedResidualSelmer_mem_unrelaxed`, `ChooseH`, `Recip`, `FirstHalf`, and the
positive-order `Grow`/`Step` producers retain their [Lean] interfaces here. The
global Selmer presentation is supplied in §10.4.12. The deeper reciprocity and finiteness cones remain [Open]
for a full reading. The reading grade applies to the local proof and the
conditional matrix argument, including their linear algebra.

---

### 10.4.9 Positive-order induction and the determinant coefficient bound

At the end of `Start`, every positive-size presentation for each signature
has an adjugate entry whose lifts all have low-degree unit coefficients. The remaining
problem is to obtain a low-degree determinant coefficient of valuation at
most $v_\varpi(\ell^\nu)$ for every signature at **the same family of places**.
A place chosen for the next signature must also preserve the bounds for the
ones already treated. The archive handles these two requirements with
`Step` and `Grow`, respectively.

#### Example 10.16. Coefficient tests over a DVR [Expository]

Work over $\mathbb Z_3$ with $\nu=1$, $e=1$ and $I=(9)$. Take two left
variables $x_0,x_1$, and append right variables $y_0,y_1$ in that order.
For two signatures take square presentations $\operatorname{diag}(D,1)$
with the following determinants.

| Number of right variables | First signature | Second signature |
|---|---|---|
| 0 | $0$ | $0$ |
| 1 | $3y_0$ | $0$ |
| 2 | $3x_1^2 y_0+9y_1$ | $3y_1$ |

In every adjugate the upper left entry is $1$, which remains $1$ on setting
all unused left variables to zero. The first extension supplies the
degree-one coefficient $3$ in $y_0$ for the first signature. In comparing
old and new presentations, set the appended right variable $y_0$ to zero
and work modulo $9$. For the second extension set $y_1=0$. The first
signature then has restricted determinant $x_1^2(3y_0)$, which exhibits
the comparison with exponent $2$ and raises the total order modulo $9$
from one to three. The coefficient $3$ still has valuation one. At
$x_1=y_0=3, y_1=0$ the determinant changes from $9$ to $81$, exhibiting
two additional powers of $3$ from the factor $x_1^2$. This particular
specialization need not meet the eventual Selmer estimate. For the second
signature, $3y_1$ supplies a fresh witness at the second extension.
The adjugate test after the first extension kills the unused left
coordinate $x_1$, whereas the second comparison kills the newly appended
right coordinate $y_1$. Both operations will occur in the proof with
different purposes.

At the second comparison the displayed determinants fail the single-factor kernel test for Grow. To see this, pass to $T=(\mathbb Z/9)[x_1,y_0]/(x_1^2,y_0^2)$. The two cokernels become $T$ and $T/(3y_0)$. Any surjection between them has kernel $(3y_0)$. The prescribed inertia factor has the form $u=(1+x_1)(1+y_0)^a-1$, so $u(3y_0)=3x_1y_0\ne0$. A kernel annihilated by $u$ would remain so after taking its image under base change, by right exactness. Thus the table illustrates numerical coefficient behavior. The proof of Grow below supplies the comparison for the Selmer presentations.

One can use $r=1$, $R_0=0$, and $w_0=0$ to follow the numerical bounds in
this toy chain. They are $w_1=4$ and $w_2=20$, with strict working cutoffs
$1,5,21$. With $\ell=3$ and $M=5$ the level allows these cutoffs because
$w_2\le 3^{5-1-1}$. The table illustrates coefficient tests and the comparison
identities for the displayed lifts. The number-field existence argument
below uses Selmer presentations and arithmetic supplies in addition.

The nilpotent test in Step also has a small hand calculation. In
$A=(\mathbb Z/9)[t]/(t^6)$ take $w=1$, so $b=2$ and $h=6$.
For a sliced adjugate polynomial specializing to $3+t$,
$(3+t)(t-3)=t^2$ and $3t^5\ne0$. In the augmented ring
$A[u,v]/(u^2,v^2)$, degree seven can survive, for example $3t^5uv$,
whereas degree eight cannot. These are the same exponents as
$h+2r=8$ for $r=1$.

#### Definitions and the two transitions

Fix the archive data $D,N,X,\mathrm{bkP},i$. Write $O=X.O0(i)$,
$\ell=X.l(i)$, $\nu=\nu(X,i)>0$, $r=D.R.r$, $\lambda=\ell^\nu$,
$e=v_\varpi(\lambda)$, and $I=(\lambda)\mathfrak m_O=(\varpi^{e+1})$.
At level $M$ put $J=\ell^{M-\nu-1}$ and
$\Lambda_n=O[(\mathbb Z/\ell^M)^{\mathrm{Fin}(R)\sqcup \mathrm{Fin}(n)}]$.
The map `toLam` sends a variable to its group generator minus $1$.
Write $P$ for the family with $R$ left and $n$ right places. In `IsQ`,
$Q$ is exactly the union of the places over the designated auxiliary
primes, including their conjugates. All coefficient assertions below
range over **every** such $Q$ and **every** square presentation $\Phi$
satisfying `Computes` for that signature and those characters.

- $\mathrm{NF}_s(P,c)$ requires every lift of $\det\Phi$ to have a
  coefficient outside $I$ in total degree $<c$.
- $\mathrm{NFit}_s(P,c)$ allows matrix size zero. Otherwise it requires
  a fixed adjugate entry for which every polynomial lift has a unit
  coefficient in total degree $<c$, with exponent zero on all left
  variables indexed by $j\ge n$. The witnessing monomial may depend on
  the lift.
- `Ext` fixes all left places and all old right places. The full
  `PiLocalization₂` condition includes `SlopeTestRemainingChoices`,
  the left orbit inertia inclusions in $L$, left Frobenius conjugate to
  $z$ modulo $L$, and the right decomposition inclusions in $L$.
  At right index $a$, the left character values in additive coordinates
  are $\delta_{ab}$ for every $b$ and every Frobenius representative.
  `Small2` requires `Small`, trivial action of $L$ on the
  $2\ell^M$-th roots of unity, and $T_s(g)-1$ entrywise in $I$ for $g\in L$.

These are the predicates in
`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/Small2.lean:13–57`.
The index $n$ increases by one per extension, and $\dim T_s=r$ is fixed.
The square presentation sizes $a,a'$ are independent. In particular
there is no asserted corank decrement. `Grow` can use a positive-size
old matrix by replacing an empty presentation by the one-by-one identity,
which represents the same zero kernel.

**Lemma 10.17 (transport through one extension) [Lean, read].**
Assume `GalHyp`, `ThmS`, `TameLocal`, $n<R$, $\nu+2\le M$,
$c+2r\le J$, the tame element condition on $z$, `Small2`, and
`PiLocalization₂` for an extension $P'$ of $P$. Both $\mathrm{NF}_s$
and $\mathrm{NFit}_s$ at cutoff $c$ pass from $P$ to $P'$ at cutoff
$c+2r$.

*Proof.* Put $k=2r$ and restrict $\Lambda_{n+1}\to\Lambda_n$ by
forgetting the new right group coordinate. On polynomial lifts this sets
the corresponding variable equal to zero. For any new presentation,
choose an old one from `ThmS`, taking the old $Q$ by filtering the new
one to the old auxiliary orbits. Over $\Lambda_n/I\Lambda_n$ the two
presentations represent the old and new relaxed Selmer functors with
the same inverse character. Indeed the two ring maps are surjective,
the inverse characters agree under restriction, and $\ell^{\nu+1}$
annihilates the quotient. The change of scalars in `represents_of_computes`
uses these facts to identify the cohomology classes and preserve
naturality for all discrete coefficient modules.

Let $p$ be the new right place and $\phi$ one of its Frobenius elements.
For the old tuple of characters $\delta$, put
$u=\prod_q(1+X_q)^{\delta_q(\phi)}-1$, using least nonnegative
representatives. This polynomial has zero constant coefficient and
coefficient $1$ at the single left variable with index $n$.
The extra relaxed places are $p$ and its conjugate. In the comparison
ring the representation is trivial on their decomposition groups
before twisting. The old characters are unramified there, and their
Frobenius values at the conjugate are inverse to those at $p$.
The two local evaluations of the relaxed cocycle on inertia give $2r$
scalar coordinates. By the tame generator test, their common vanishing
is exactly the old Selmer condition. Each is killed by the image of $u$:
the Frobenius twist minus $1$ at either place is an associate of that
image. These evaluation maps commute with coefficient maps, since
inertia acts trivially and coboundaries evaluate to zero there.

For a square matrix $\Psi$ write $C(\Psi)=\operatorname{coker}(\Psi^t)$.
The kernel functor on a module $B$ is $\operatorname{Hom}(C(\Psi),B)$.
Evaluating the $2r$ inertia coordinates on the universal vector of the
new cokernel gives $2r$ elements killed by the image of $u$. Quotient
by their span. The resulting module represents the old kernel functor:
maps out of it are exactly those whose universal vectors have zero
inertia evaluations. Evaluating this identification on the two
representing modules and their identity maps gives inverse maps. Thus
the new cokernel surjects onto the old with kernel generated by these
$2r$ elements. All matrices here are reduced and the new one is
restricted first.

For clarity, the Fitting comparison follows by lifting the old
generators into the new cokernel and adding the $k$ kernel generators.
This gives a surjection from a free module, with a square matrix of
relations of the form
$\begin{pmatrix}u1_k&-C\\0&\Phi^t\end{pmatrix}$, where $u1_k$
denotes $u$ times the identity. The off-diagonal block records how
the lifted old relations land in the kernel. The determinant is
$u^k\det\Phi$. The bottom-right adjugate block is $u^k\operatorname{adj}(\Phi^t)$
when the old size is positive. To compare with the actual new
presentation, take the sum of the free modules for the actual and
lifted generators. Changing generators by a block unitriangular matrix
shows that the kernel of the combined surjection is the image of the
actual new presentation stabilized by an identity. The stabilized
matrix of lifted relations has columns in that image and factors
through it. Taking determinants and using the adjugate product
identity gives the inclusions in the determinant and adjugate ideals
of the new presentation. For the adjugate, identity stabilization
contributes only the actual adjugate entries and copies of its
determinant, which belongs to their span by cofactor expansion when
the actual new size is positive. Transposition just interchanges the
adjugate indices. Size zero on the new side is allowed immediately
by $\mathrm{NFit}$.

Here is the coefficient descent which makes these ideal inclusions
effective. For an ideal $I'\supseteq I$ and a set $K$ of forbidden
variables, kill $K$ and reduce modulo $I'$. Vanishing in degrees
$<d$ is an ideal condition, since multiplications never decrease
total degree. A relation in the group ring modulo $I$ lifts to this
condition, for $d\le J$, if its generators have lifts satisfying it.
To see this, work modulo $I$ and all monomials of degree at least $J$.
Each $1+X_q$ has $\ell^M$-th power $1$ there. In the binomial
expansion terms of degree $\ge J$ vanish, and for $0<b<J$ the
identity $b\binom{\ell^M}{b}=\ell^M\binom{\ell^M-1}{b-1}$ gives
$v_\ell\binom{\ell^M}{b}\ge M-v_\ell(b)\ge \nu+1$.
Thus the polynomial quotient factors through the reduced group ring.
Choose polynomial lifts of the multipliers (the group-ring map is
surjective). Their sum times the lifted generators satisfies the
ideal condition, and the difference from the specified lift has
coefficients in $I$ below $J$. This proves the descent for every lift.

Finally, after killing $K$, vanishings for $u^k F$ below degree $c+k$
imply vanishings for $F$ below $c$ provided the distinguished variable
$q$ of $u$ survives. For one factor, take the coefficient at $m+1_q$
for $|m|<c$. The term $u_{1_q}F_m$ has unit multiplier. All other
nonzero terms have an index of $F$ of degree $\le |m|$ and smaller
weight, assigning weight $1$ to $q$ and $2$ to every other variable.
The constant term of $u$ is zero and its only monomial of weight
one is $X_q$. Induction on weight therefore gives $F_m=0$ in the
coefficient quotient. Iterate this argument for $k$ factors.

For $\mathrm{NF}$ take $I'=I$, $K=\varnothing$. A counterexample
lift at $P'$ vanishes below $c+k$ modulo $I$ after restriction.
Descent and cancellation contradict the old witness. For
$\mathrm{NFit}$ take $I'=\mathfrak m_O$ and $K$ the left variables
with index $\ge n+1$. If no new entry works, choose a counterexample
lift for each entry and restrict each lift. The distinguished variable
at index $n$ survives, so descent and cancellation force the chosen
old entry to vanish below $c$ modulo $\mathfrak m_O$ on this slice.
The old witness avoided even the variables of index $\ge n$, hence
also survives this slice, a contradiction. $square$

Proof locations for the comparison and descent are
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevInductionGrowBoundOfPresentation.lean:96–149,157–221,225–293,301–451,455–502`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RepresentsOfComputes.lean:117–187`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CokEquivOfExact.lean:89–143`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetMemSpanAdjugate.lean:64–153,160–247`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffMemOfToLamMem.lean:33–76`,
and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffMemOfPowMul.lean:7–92`.

#### How a signature gets its first determinant bound

The production proof is `NewPrime.step` [Lean, read], with the
suppliers below as inputs. With the ambient hypotheses of Lemma 10.17, it starts from
`PiLocalization₂` for $P$ and takes `AdmFam`
for $H,S,d$, $L\le H$, $v_\varpi(\lambda)=e$, and $\mathrm{NFit}_s(P,w+1)$.
For this step set $b=(e+1)w$, $h=2b+2$, and require $h+2r\le J$.
The output is an extension satisfying full `PiLocalization₂` and
$\mathrm{NF}_s(P',h+2r)$.

If $\mathrm{NF}_s(P,h)$ already holds, the prime-selection routine
takes target $1$ modulo $L$, with $U=L$. Apply `Grow` at cutoff $h$.
Otherwise take the bad determinant lift $F_0$ and its presentation
$\Phi$. The size cannot be zero: evaluation at all variables zero
over $O/I$ would give both zero (by its constant coefficient) and
one (the empty determinant). The hypothesis then gives the lift $F_1$
of an adjugate entry with a unit coefficient of degree $\le w$
avoiding the unused left set $K=\{j\text{ on the left}:j\ge n\}$.

The finite local ring construction [Lean] evaluates variables at
$a_q t$, with $a_q=0$ exactly on $K$ and units elsewhere. The ring
$A$ kills $I$ and has $t^h=0$, $\lambda t^{h-1}\ne0$ and
$F_1(a_qt)\mid t^b$. Here is the divisibility argument within that
construction. Pass to a finite extension of the residue field
where the indicated homogeneous part on the coordinate slice is
nonzero at a point with all surviving coordinates nonzero. Such a
point exists over the infinite algebraic closure, and its finitely
many coordinates lie in a finite extension. Lift to a finite
coefficient ring over $O/I$ with injective structure map and
residue kernel generated by $\varpi$, as in `exists_lift`. The
evaluated polynomial in $t$ is $\varpi A_1(t)+t^{d_0}V(t)$
where $d_0\le w$ is the first degree with nonzero residue and $V(0)$
is a unit. After truncation by $t^h$, $V$ is a unit. In the quotient
by the evaluated polynomial, $t^{d_0}V=-\varpi A_1$, whose
$(e+1)$-st power is zero. Hence $t^b$ vanishes there. The truncation is
free in degrees $0,\ldots,h-1$ over the coefficient ring, so
$\lambda t^{h-1}\ne0$ follows from injectivity and $\lambda\notin I$.
The construction is used at
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsFiniteLocalRingPolyDividesVarPow.lean:65–119,121–198,200–280,282–430`.

The evaluation factors through $\Lambda_n$ because $t^h=0$ with
$h\le J$, and the binomial argument of Lemma 10.17 applies. It gives a specialized
matrix $\Psi$ and a universal cocycle. The bad low coefficients
force $\det\Psi=0$, since degrees $\ge h$ also vanish. The indicated
adjugate entry divides $t^b$ and its column is in the kernel.
In the dual-class selection call the scalar is $\lambda t^b$ and
the auxiliary factor is $t$. The required nonannihilation of the
entry follows because multiplying a putative vanishing by the
complementary factor in the divisibility $F_1(a_qt)\mid t^b$ gives
$\lambda t^{2b+1}=0$. This is the source of the exponent $2b+2$.

The arithmetic supplies give a dual Selmer class and a
nonzero cocycle pairing at a target element of
$L'=L\cap \bigcap_{q\notin K}\ker d(P(q))$. They also provide an
open normal $U\le L'$ preserving that pairing on the prescribed
conjugacy class. The unused left inertias lie in $U$ by the
first-half vanishing input for the two cocycles. The prime-selector
proof first corrects the target by an element of $U$ to set the
unused left character values to the next coordinate vector.
It uses inertia generators of those unused left places, which
have trivial cross-values at the other left coordinates.
It then applies the supplied Chebotarev theorem modulo the
intersection of $U$ with all left character kernels, avoiding the
finite excluded set and old orbits. Finally it multiplies the
chosen Frobenius by inertia at the new place to make its own
character value $1$ without changing the required conjugacy
modulo $U$. This yields the required extension and a Frobenius
with nonzero pairing. The prime-selector body is
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNewPlaceFrobeniusConjugateModOpenNormalSub.lean:12–126`.

Take any new presentation and any determinant lift $F'$.
Use $B=A[x_1,x_2]/(x_1^2,x_2^{2r})$ with augmentation onto $A$.
Multiplication by $x_1x_2^{2r-1}$ detects the augmented coefficient
because the surviving monomials form an $A$-basis. Use $x_1$ at
the new right coordinate, $x_2$ at the left coordinate $n$, and
$a_qt$ at every other old coordinate. Reduction to $A$ gives the
old evaluation since the left coordinate $n$ belongs to $K$. Each
substituted element has $J$-th power zero by the cutoff inequality,
so the same binomial argument gives the map from the extended group
ring. Inertia at the new right place
tests $x_1$, and its chosen Frobenius tests $x_2$ by the coordinate
condition and the vanishing of the other character factors.
The determinant nonvanishing test takes the two conjugate sets
of $r$ local rows. The local row relation gives $x_1$ times the
Frobenius rows equal to $x_2$ times the inertia rows up to the
unit factors specified by the twist, modulo the new presentation
rows. The comparison supplies lifts of the old presentation
relations modulo the new relations and the inertia rows. By
reciprocity the dual combination of the inertia rows is itself a
relation after reduction. Here are the relation lifts explicitly. Write $x=x_1$, $y=x_2$, and
let $G$ consist of lifts of the old comparison rows $E$ followed by the
new inertia rows multiplied by their unit factors $\eta_j$. These
generate modulo the rows of $\Phi'$: they do so modulo $(x,y)$ by the
comparison, and the quotient by their span plus the new rows then
equals its own multiple by the nilpotent ideal $(x,y)$, so it is zero.
Consequently any relation or expression among the reduced generators
lifts with its prescribed coefficients modulo $(x,y)$. Indeed, lift the
coefficients and the multiple of the new rows first. Express the
remaining error as $x p+y q$ and express $p,q$ in the generators and the
new rows. This corrects the lift without changing its reduction.

Write $U_j$ for the old Frobenius rows and $k_j$ for the signed dual
coordinates. For the top rows of a square relation matrix take lifts
$D$ of $(\Psi,C)$, where $C$ accounts for the inertia correction,
except that at the column index $l_0$ of the tested adjugate column
the row is replaced by $(0,k)$ using reciprocity. For each new
Frobenius row choose its expression modulo the new relations, with
coefficient row $W_j$ reducing to $(U_j,\sigma_j)$ for some
inertia correction $\sigma_j$. With $e_j^{\mathrm{right}}$ denoting the
basis row of the $j$-th inertia generator, the bottom rows
$y e_j^{\mathrm{right}}-xW_j$ are relations by the local row identity. In its block expansion the coefficient of
$x_1x_2^{2r-1}$, reduced to $A$, is the nonzero pairing with
that column, up to sign. Indeed exactly one of the $2r$ bottom
rows must contribute the $x_1$ part, and the other $2r-1$ must
contribute the $x_2$ identity parts. In the reduced summand for bottom row $j$, swap that row with the
row at $l_0$. The matrix is block triangular. Its top left block is
$\Psi$ with row $l_0$ replaced by $-U_j$. Its bottom right block is the
identity with row $j$ replaced by $k$. The sign of the swap and
cofactor expansion give $k_j\sum_c U_{jc}\operatorname{adj}(\Psi)_{c l_0}$.
Summing gives precisely the signed pairing used in the comparison. If the new determinant were zero,
the lifted square relation matrix would have determinant zero:
its rows are relations on a generating list for the new
cokernel, so the stabilized relation comparison gives divisibility
by the new determinant. The augmentation test now gives the
contradiction.

If all coefficients of $F'$ of degree $<h+2r$ lay in $I$, its
evaluation would be zero. Low terms vanish because the ring kills
$I$. Any monomial of degree at least $h+2r$ is divisible after
evaluation by $t^h$, $x_1^2$, or $x_2^{2r}$, since the maximum
sum of the three surviving exponents is
$(h-1)+1+(2r-1)=h+2r-1$. Evaluation commutes with the determinant.
The nonzero specialized determinant therefore proves
$\mathrm{NF}_s(P',h+2r)$ with the universal quantifiers intact.

The producer and the determinant argument are in
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntiOfKer.lean:46–83,85–151,153–352`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetNeZeroOfLowestFormNeZeroPresentation.lean:12–47,49–109,118–230,234–372`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean:22–71`,
and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalEqZeroLowCoeffThreeNilpotents.lean:8–64`.
The dual class, the nonzero pairing, reciprocity and the local row
relations are imported arithmetic supplies [Lean]. In particular
the existence of the pairing does not follow from the formal
nonvanishing test.

#### Proposition 10.18. The positive-order recurrence [Lean, read]

Fix $D,N,X,\mathrm{bkP},i$, an enumeration $f:\mathrm{Fin}(t)\to X.\mathrm{Sig}(i)$,
and assume $\nu>0$. Take `Grow` and `Step` for every $f(j)$,
with the hypotheses detailed above when these are supplied by their
actual producers. Fix level $M$, $H,S,d,A,L,z$, with
`AdmFam`, $L\le H$, the tame element condition on $z$, and
`Small2` for every $f(j)$. Set $R=R_0+t$ and assume
$e=v_\varpi(\lambda)$ is finite, $\nu+2\le M$, and $w_t\le J$, where
$w_0=w$ and
$w_{k+1}=2(e+1)w_k+2+2r$.
Suppose $P_0$ has $R$ left and $R_0$ right places, satisfies
`PiLocalization₂`, and has $\mathrm{NFit}_{f(j)}(P_0,w+1)$ for
every $j$. Then for every $0\le k\le t$ there is an iterated extension
$P_k$ with $R_0+k$ right places, the original left places, and
`PiLocalization₂`. At $P_k$ the cutoff $w_k+1$ works for every
adjugate test, and for the determinant tests at indices $j<k$.
In particular for each $j$ at $P_t$, every determinant lift has
a coefficient of degree $\le w_t$ and valuation $\le e$.

*Proof.* At $k=0$ the adjugate tests are the hypotheses and the
determinant list is empty. If $k<t$, then $R_0+k<R$. Both
$w_k+1+2r\le w_{k+1}$ and $w_k\le w_{k+1}$ follow directly
from the recurrence. In particular $w_{k+1}\le w_t\le J$.
Apply `Step` to $f(k)$ with input $w_k$ and get a single
extension and its new determinant bound at strict cutoff $w_{k+1}$.
Apply `Grow` to this same extension for all adjugate tests and
all earlier determinant tests, at cutoff $w_k+1$. Their new cutoff
$w_k+1+2r$ is at most $w_{k+1}$. Enlarge the cutoffs to
$w_{k+1}+1$, preserving every witness. The left tuple and all
previous right positions persist by `Ext`. Thus $t-k$ is the
remaining number of steps, while $R-(R_0+k)$ is exactly the
available number of right slots. At $k=t$ every signature has
$\mathrm{NF}$. A degree $<w_t+1$ is at most $w_t$, and outside
$(\varpi^{e+1})$ means nonzero with valuation at most $e$.
$square$

The recurrence, its monotonicity, the proof of the invariant and
the valuation exit are
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValLeOfNotMem.lean:28–85`.
The assembly at lines 87–144 uses `ChooseH` and `StepAB` as in
§10.4.8. It starts with $w=4rR_0$ and outputs the constants
$R=R_0+t$, $D_d=w_t$, $M_0=w_t+\nu+3$. The extra level margin
ensures $w_t\le J$ and leaves the strict starting inequality
$4rR_0+2<\ell^M$ for `Start`. The final tuple also satisfies `Steps` for the requested open normal
subgroup $H'$: the left data come from the initial selection and the right
character coordinates from the final localization condition. The
residual branch enters the consumer at $\nu=0$.

#### Selmer consumption and reading boundary

In the positive case, `ThmC` supplies the `OrdBound` at
$v_\varpi(\ell^\nu)$. The consumer takes its $R,D_d,M_0$,
replaces $M_0$ by $\max (M_0,1)$, and takes the actual final
place family. For every good signature and every `IsQ`, `ThmS`
supplies a square presentation. Surjectivity gives a determinant
lift $F$. The same $F$ carries both the bound
$\exists m, |m|\le D_d, v_\varpi(F_m)\le e$ and the evaluation
identity supplied by `SelmerLengthsByDeterminant`. The coefficient
assertion enters the simultaneous `exists_level` evaluation
argument together with the other required toric bounds. For the
chosen root evaluations with $X_q=u_q-1$ and $u_q=\zeta^{\ell^{\eta_q}}$
for the selected exponents $\eta_q$ and each primitive root $\zeta$
of the chosen order (taking the side root for each signature)
that argument gives a nonzero value and normalized valuation at
most $\nu+\varepsilon$. The consumer applies the presentation's
length identity to this very value and uses $v_\varpi(\ell)>0$
to cancel the factor in $v_\varpi(\ell^\nu)=\nu v_\varpi(\ell)$.
This gives the Selmer length bound with the chosen error budget
for every coprime power in the existing admissible-index theorem.
A low coefficient alone gives no bound at an arbitrary
specialization.

The exact call sites are
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BoundModTwoUniformizerAtTwoOfChebotarev.lean:25–35`,
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisTwistedSelmerAuxprimesOfMatrixAndBounds.lean:47–63`,
and
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:92–122,133–145,161–197`.
The relevant statements are
`src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:46–77` and
`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:321–337`.
`SelmerLengthsByDeterminant` and `exists_level` enter here as
[Lean] supplies. The positive-order top assembly takes `Cheb`,
`PoitouTateTotallyComplex`, `CohDimTwo`, `TameLocal`,
`LocalFiniteness`, `LocalTateDuality`, `LocalEulerChar`,
`GlobalFiniteness`, `GlobalEulerChar`, `UnramifiedOrthogonality`,
and `Gen.ArchimedeanSignatureMatching`. These inputs and the
arithmetic cones for the dual-class and pairing selection remain
outside the R3 boundary [Open] for full reading. Classical Fitting
terminology and presentation invariance are described in the Stacks
Project, §15.8 [StacksFitting].

Archive pin for this subsection (A2, joined SHA-256)
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

### 10.4.10 From an adjugate entry to a Frobenius witness

#### Motivation

In the branch of `Step` that needs an arithmetic witness, the finite local specialization has an element $\lambda t^{2B+1}\ne0$, with $\lambda=\ell^\nu$ in the coefficient ring and $B=(e+1)w$. Here $B$ is the exponent called $b$ in the expression $\lambda t^{2b+1}$, and Lean's argument named `b` is a matrix index. The goal is to choose an auxiliary prime whose Frobenius detects an original Selmer cocycle against a dual Selmer cocycle. There are three steps. Finite duality supplies a comparison of matrix kernels. Galois cohomology turns that comparison into a global dual class and a nonzero evaluation on a subgroup. Chebotarev realizes a conjugacy class in a finite quotient at a prime. The output is the nonzero scalar consumed by the determinant argument.

#### Example. Nonzero values over a finite local ring [Expository]

Take $A=\mathbb Z/9\mathbb Z$ with maximal ideal $(3)$. Call a vector in a free module primitive if its reduction modulo the maximal ideal is nonzero. For an element of $A$ this means it is a unit. The balanced pairing $P(u,v)=3uv$ has radical $(3)$ on each side. It takes the nonzero value $3$ on $(1,1)$, yet $P(3,v)=0$ for every $v$, and the entire pairing reduces to zero modulo $(3)$. The multiplication pairing $P(u,v)=uv$ is perfect. It detects $3$ by pairing it with $1$, but every value on $3$ still reduces to zero. For an illustration in rank two, the perfect dot product pairs the primitive vectors $(1,0)$ and $(3,1)$ to $3$. A primitive vector for this dot product admits a partner giving a unit, by testing a unit coordinate against its basis vector. A specified partner can give a nonzero nonunit or even zero. The scalar sought by `Step` is merely nonzero in $A$.

#### Definitions

Fix the archive's twist index $i$ and signature. Write $G=G_E$, $\ell$ for the twist prime, $O_0$ for the base coefficient ring, $N_0=\ell^{\nu+1}$ and $C=\mathbb Z/N_0\mathbb Z$. Let $A$ be a finite commutative local $O_0$-algebra with discrete topology killing the ideal $(\ell^\nu)\mathfrak m_{O_0}$ (`Kills`). In particular $N_0 A=0$, since $\ell\in\mathfrak m_{O_0}$. Use the archive's `Setup` for the twist $\kappa$ and the finite set $Q$, and `IsDual` for $\rho$. In matrix terms, if $T_0(g)$ is the untwisted original action and $\epsilon_0$ is the cyclotomic character in $O_0$, then $\rho(g)=\epsilon_0(g)(T_0(g)^{-1})^{\mathsf T}$. The setup includes `GalHyp` (the isotypic valuation, valuation stability, self-duality, no-jump and `adm3` conditions, and the rank bound $r\ge100$), a local coefficient map with $A$ finite as an $O_0$-module, an open kernel and pointwise $\ell$-power order for $\kappa$, triviality of $\kappa$ above $\ell$ and on inertia outside $Q$, and $Q$ disjoint from the places above $\ell$. On $V^r$ and $W^r$ for coefficient modules $V,W$ write $\pi$ for the original action twisted by $\kappa$ and $\pi'$ for the cyclotomic dual action twisted by $\kappa^{-1}$.

A biadditive $\beta:V\times W\to C$ is balanced if $\beta(av,w)=\beta(v,aw)$. The archive calls it perfect if it is balanced and has zero radicals on both sides. Its coordinate sum gives the local cup pairing with the cyclotomic action on $C$. Write $\mathcal S(V)$ for the original Selmer group with the relaxation at $\operatorname{Spl}(i)\cup Q$, and $\mathcal D(\beta)$ for the dual classes. A dual representative is a continuous cocycle $y$ that vanishes on inertia outside the primes over $\ell$, $\operatorname{Spl}(i)$ and $Q$, restricts to a coboundary at $\operatorname{Spl}(i)\cup Q$, and pairs by cup product to a coboundary with every class in the original local condition at each prime above $\ell$. A coboundary on a group with action $\pi'$ has the form $g\mapsto \pi'(g)m-m$. The two coefficient modules can vary while the actions and the local conditions are transported as in the archive. `NoInvDual` requires zero global dual invariants for **every** coefficient module, including quotients.

A square matrix $\Psi$ of size $a$ and rectangular matrices $Z(g)$ satisfy `Univ` if, on every discrete coefficient module $V$, a vector $u\in\ker(\Psi:V^a\to V^a)$ yields a Selmer cocycle $g\mapsto Z(g)u$, this cocycle is a coboundary only for $u=0$, and every Selmer class is represented this way. Thus $|\ker\Psi_V|=|\mathcal S(V)|$ for finite $V$. Injectivity follows by applying the zero criterion to the difference of two representatives. Surjectivity is the last clause of `Univ`. The proof of base change uses the quotient of the free row module by the span of the rows of $\Psi$. The images of the standard basis give a universal kernel vector. Lift the corresponding cocycle's coordinates to rows of $Z(g)$ and evaluate those rows against any kernel vector. The natural presentation and the transfer of Selmer conditions then give all three clauses.

Write $L_v$ for the original local condition above $\ell$. The order formula used below applies to every finite perfect coefficient pair and reads $|\mathcal S(V)|=|\mathcal D(\beta)|\prod_{v\in Q}|H^0(G_v,W^r)|$, with $\mathcal D(\beta)$ finite. Here $G_v$ denotes the chosen decomposition group. In its conditional proof, local Tate duality identifies the perpendicular conditions: the relaxed conditions at $\operatorname{Spl}(i)\cup Q$ have zero perpendicular, and above $\ell$ the perpendicular is given by the cup test. The Greenberg–Wiles formula expresses the ratio of orders by global invariants, local orders and the archimedean term. The global invariants vanish on both sides. More explicitly, write $H_v$ and $H'_v$ for the original and dual invariants. With $S$ the union of the places above $\ell$ and the relaxed places, the formula reduces to
$|\mathcal S(V)|\,|V^r|^{r_2(E)}\prod_{v\in S}|H_v|=|\mathcal D(\beta)|\prod_{v\mid\ell}|L_v|\prod_{v\in\operatorname{Spl}(i)\cup Q}|H^1(G_v,V^r)|$.
Above $\ell$, the supplied product for $|L_v|$ is $|V^r|^{r_2(E)}\prod_{v\mid\ell}|H_v|$. At the relaxed places, local duality and the local Euler characteristic give $|H^1(G_v,V^r)|=|H_v||H'_v|$. Cancel the common positive integer factors. The dual invariants at $\operatorname{Spl}(i)$ are zero as modules, so their cardinalities are one. This leaves exactly the factors indexed by $Q$. The calculation uses the named duality, finiteness, Euler characteristic and signature inputs listed below.

#### Lemma. Dual selection under the Step hypotheses [Lean, read]

Keep `Setup`, `Kills`, `IsDual`, `NoInvDual`, the order formula and `Univ` as above. The lifting of the local condition under a surjective coefficient map and the cup pairing equivariance used below are consequences of these arithmetic hypotheses in the cited suppliers. Take a finite discrete module $Y$ and a perfect $\beta:Y\times A\to C$. Suppose $t$ kills the invariants of the dual action on $A^r$ at every $v\in\operatorname{Spl}(i)\cup Q$. Let $c\in A$ and let $u_0$ be a row with $u_0\Psi=0$. If $ct(u_0)_j\ne0$ for some $j$, there exists a dual Selmer cocycle $y$ with $c[y]\ne0$ in global $H^1$.

**Proof.** Put $s=ct$, $\bar Y=Y/sY$ and $A[s]=\{u\in A:su=0\}$. Pair $\bar Y$ against $A[s]$ by $\bar\beta(\bar v,u)=\beta(v,u)$. Balance makes this well-defined and gives balance on the quotient. The right radical is zero by testing all lifts of $\bar v$. To see that the left radical is zero, compose with the faithful additive character of $C$ in $\mathbb C^\times$. This embeds $A[s]$ into the character group of $\bar Y$. The same construction with the original pairing reversed embeds $Y[s]$ into the character group of $A/sA$. Finite abelian groups and their character groups have the same order, and multiplication by $s$ on a finite module has kernel and cokernel of equal order. Hence $|A[s]|\le|\bar Y|=|Y[s]|\le|A/sA|=|A[s]|$. The first embedding is bijective and characters separate points, giving the left radical assertion.

Assume $c[y]=0$ for all dual Selmer classes. Write $cy=\delta m$. Modulo $cA$, the vector $m$ is globally invariant. Apply `NoInvDual` to $A/cA$ to write $m=cm'$ with $m'\in A^r$. Then $y-\delta m'$ takes values killed by $c$, hence in $A[s]^r$. It defines a continuous cocycle $y_s$ there. Indeed, the coefficient inclusion is injective and equivariant, so the cocycle identity descends, and discrete values give continuity from the locally constant image.

Verify each dual condition for $y_s$. At an unramified prime in the defining inertia condition, $y$ vanishes on inertia and the action on $A^r$ is trivial there, so $y_s$ also vanishes. At $v\in\operatorname{Spl}(i)\cup Q$, write $y|_{G_v}=\delta m_v$. Then $c(m_v-m')$ is fixed by $G_v$, so $tc(m_v-m')=0$. Thus the coboundary witness $m_v-m'$ belongs to the smaller module. At a prime over $\ell$, use the surjective-coefficient comparison of the original local conditions to lift the tested class for $\bar Y$ to one for $Y$. The resulting cocycle and the pushforward of its lift differ by a coboundary. Cup-coboundary membership is unchanged on replacing either argument by a cohomologous representative. Explicitly, for the coordinate pairing $P$ and cocycles $x,y$, the change when replacing $x$ by $x+\delta w$ is the differential of $g\mapsto P(w,y(g))$. When replacing $y$ by $y-\delta m'$ the change is the differential of $g\mapsto P(x(g),\pi'(g)m')$. Both follow by expanding the cocycle identities and using cyclotomic equivariance of $P$. The identity defining $\bar\beta$ identifies the cup expression on the two coefficient pairs. This proves the required condition above $\ell$.

The images of the classes for $\bar\beta$ therefore include all classes for $\beta$, giving $|\mathcal D(\beta)|\le|\mathcal D(\bar\beta)|$ without requiring injectivity on cohomology. At each $v\in Q$ every invariant in $A^r$ is killed by $t$ and hence by $s$. The inclusion of $A[s]^r$ therefore gives a bijection on those invariants. Applying the two order formulas and `Univ` yields $|\ker\Psi_Y|\le|\ker\Psi_{\bar Y}|$.

For an endomorphism of a finite module the order of its kernel equals that of its cokernel. The quotient $Y\to\bar Y$ induces a surjection on the cokernels of the two matrix actions, and the inequality just proved makes it bijective. In particular $sY^a\subseteq\operatorname{im}\Psi_Y$. For each $v\in Y$, choose a preimage under $\Psi_Y$ of the vector with $sv$ in position $j$ and zero elsewhere. Applying $u_0$ gives $s(u_0)_j v=0$ because $u_0\Psi=0$. Balance gives $\beta(v,s(u_0)_j)=\beta(s(u_0)_j v,1)=0$ for all $v$. The right radical is zero, contradicting the hypothesis. $\square$

#### Lemma. From the class to a nonzero subgroup evaluation [Lean, read]

Use the positive-order setting $\nu>0$, $M\ge\nu+1$, the tame element $z$ and the subgroup $L_*$ satisfying `Small2`. Assume $\kappa$ is anticyclotomic and trivial on $L_*$ and $z$. Write $\iota g$ for conjugation by the chosen complex conjugation. The two actions are trivial on $L_*$, which is open, normal, and $\iota$-stable, and $[g,z]\in L_*$ for every $g$. These action statements follow from the congruence on the original matrices and the roots of unity fixed by $L_*$, which also make the cyclotomic factor trivial in $A$. At $z$ the actions are scalars $d,d^{-1}$ with $d^2-1$ a unit. In particular both $d-1$ and $d^{-1}-1$ are units. Set $x(g)=Z(g)x_0$ for a right kernel vector $x_0$. If $(x_0)_j\mid q$ and $\lambda q[y]\ne0$, there is $h\in L_*$ with
$\mathcal B(h)=x(h)\cdot y(h)-x(\iota h)\cdot y(\iota h)\ne0$ in $A$.

**Proof.** A cocycle $f$ vanishing on $L_*$ in a representation trivial there and scalar $D$ at $z$ satisfies $f(gz)=f(zg)$, since $gz=[g,z]zg$. The two cocycle expansions give $(D-1)f(g)=\pi(g)f(z)-f(z)$. If $D-1$ is a unit, $f$ is the coboundary of $(D-1)^{-1}f(z)$. Apply this first to the original cocycle modulo the ideal $J$ generated by all coordinates of $x(h)$, $h\in L_*$. The coordinatewise reduction of $x_0$ is in the kernel, and the resulting universal cocycle is zero on $L_*$. It is a coboundary by the scalar argument, so `Univ` over the coefficient module $A/J$ forces $x_0$ to be zero modulo $J$. Hence $(x_0)_j\in J$ and $q\in J$.

Suppose $\mathcal B$ vanishes on $L_*$. The archive's two-cocycle vanishing lemma gives $\lambda x(h)_a y(h')_b=0$ for all subgroup elements $h,h'$ and all coordinates $a,b$. Its proof uses the original and dual matrix actions $T,T'$ and the conjugate-dual relation $T'(\iota g)=J_0(\chi(g)T(g))J_0^{-1}$, where $J_0$ is invertible and $\chi$ is the indicated power of the cyclotomic character. On $L_*$ both cocycles are additive. Polarizing the diagonal identity at $uv$ gives equality of the two sums of mixed terms for $u,v\in L_*$. Now replace $u$ by $zuz^{-1}$. Its two values scale by $d,d^{-1}$, and the two conjugated values by $d^{-1},d$. For the conjugate scalars, apply the conjugate-dual relation at $z$ and $\iota z$ with $\chi(z)=\chi(\iota z)=1$. Subtract $d$ times the first identity from the second and cancel the unit $d-d^{-1}$. This gives $x(v)\cdot y(u)=x(\iota u)\cdot y(\iota v)$. Replacing one argument by a $G$-conjugate now gives the trace comparison
$\operatorname{tr}(T(g)U)=\chi(g)\operatorname{tr}(T(g)U')$, with $U=x(h)y(h')^{\mathsf T}$ and $U'=J_0^{-1}y(\iota h)x(\iota h')^{\mathsf T}J_0$.

For the trace comparison, extend $T$ and $\chi T$ to maps $f,f'$ from the group algebra onto the full matrix algebra, using the full matrix span and the units $\chi(g)$. Put $I=\operatorname{Ann}_A(U)$. If $f'(b)=0$, apply the trace identity to $p b q$, where $f(p)=E_{ki}$ and $f(q)=E_{jl}$ are matrix units. The left trace is $f(b)_{ij}U_{lk}$ and the right trace is zero. Thus every entry of $f(b)$ belongs to $I$. The case $I=A$ gives $U=0$ immediately. Otherwise choose preimages $s_{ij}$ of the matrix units under $f'$. They define an $A/I$-linear map by taking $E_{ij}$ to $f(s_{ij})$ modulo $I$. Subtracting the linear combination of the $s_{ij}$ representing $f'(b)$ shows that the map carries $f'(b)$ to $f(b)$ modulo $I$. Surjectivity of $f'$ and multiplicativity of $f,f'$ make this a unital algebra endomorphism. The supplied local matrix-algebra determinant invariance gives $\det T(g_0)=\chi(g_0)^r\det T(g_0)$ modulo $I$. Cancel the unit determinant to get $(\chi(g_0)^r-1)U=0$. Here $\chi(g)$ is the image of $\epsilon_0(g)^{D.R.t}$ in $A$, where $\epsilon_0$ is the cyclotomic character in $O_0$ and $D.R.t$ is the archive's fixed rank parameter. The cyclotomic image supplies $g_0$ with $\chi(g_0)^r-1$ equal to $\ell^\nu$ times a unit. This gives the stated coordinate annihilation.

Extend the coordinate annihilation by linearity from the generators of $J$ to $q\in J$. Then $\lambda q y$ vanishes on $L_*$. The same scalar argument for the dual action, with $D=d^{-1}$, makes it a global coboundary, a contradiction. In this argument the point is supplied by restrictions of global cocycles and the tame and conjugate-dual hypotheses.

#### The actual arguments of Step

Let $q=t^B$ and $\Psi$ be the specialized presentation of determinant zero. Write $A_{\rm adj}=\operatorname{adj}(\Psi)$ and let $(i_0,j_0)$ be the selected entry, with $a_*= (A_{\rm adj})_{i_0j_0}$ dividing $q$. Step takes the row $u_0=(A_{\rm adj})_{i_0,*}$ and the column $x_0=(A_{\rm adj})_{*,j_0}$. The identities $A_{\rm adj}\Psi=\Psi A_{\rm adj}=0$ give the two kernel equations. If $q=a_*v$, then $\lambda t^{2B+1}=(\lambda q)t a_*v$, so $c=\lambda q$ meets the lemma's test $ct(u_0)_{j_0}\ne0$. The resulting class has $\lambda q[y]\ne0$. The column satisfies $(x_0)_{i_0}\mid q$, as the subgroup lemma requires. The original class comes from `Univ` at this column and is nonzero because the column has a nonzero coordinate and `Univ` detects coboundaries.

In this application $\beta$ is evaluation on $Y=\operatorname{Hom}_{\mathbb Z}(A,C)$ with $(a\phi)(b)=\phi(ab)$. Characters detect nonzero elements since $N_0 A=0$. The same character module also gives the row criterion passed to the determinant argument. If a row $v$ lies outside the span of the rows of $\Psi$, choose an additive character on their quotient that detects the image of $v$. Pull it back to $F:A^a\to C$ and set $u_j(b)=F(be_j)$, where $e_j$ is the $j$-th basis row. For each row $w$, $(\sum_j w_j u_j)(b)=F(bw)$. For the rows of $\Psi$ this is zero, so $u\in\ker\Psi_Y$. For $w=v$ and $b=1$ it is nonzero. Thus a row annihilating the whole kernel belongs to the row span.

The no-invariants hypothesis is supplied by the tame scalar with nontrivial residual eigenvalue and a twist of $\ell$-power order. For the local annihilator test, the invariants vanish at $\operatorname{Spl}(i)$ and at the old left places by the respective local vanishing and scalar Frobenius tests. At a place in $Q$ lying over an old right coordinate, choose an inertia element on which its own auxiliary character has additive coordinate $1$. All other auxiliary characters are trivial there, as is the untwisted dual action. The action on that element is therefore multiplication by $1+a_qt$ with $a_q$ a unit. Invariance gives $a_qtm=0$ and then $tm=0$.

Step forms $L_*$ by intersecting its original $L$ with the kernels of the characters at all coordinates outside the unused left coordinates. Those unused coordinates have zero coefficients in the specialization. The intersection therefore kills $\kappa$, and `Small2` persists by the character constraints. The proof uses this $L_*$ for $\mathcal B$ and uses the original $L$ in the prime-selection call.

#### From the subgroup element to a prime [Lean, read conditional on Chebotarev]

Inside $L_*$ take $U$ to be the common zero subgroup of $x,y,x\circ\iota,y\circ\iota$. Each ordinary zero subgroup is open by continuity and normal because $f(khk^{-1})=\pi(k)f(h)$ for $h\in L_*$, by the cocycle law and triviality of the action there. Taking the two inverse images under $\iota$ and intersecting gives the asserted open normal subgroup. If $k\sigma k^{-1}h^{-1}\in U$, the same conjugation formula gives $x(\sigma)=\pi(k^{-1})x(h)$ and the corresponding formula for $y$, and likewise for the conjugate terms. The dot products both scale by the same cyclotomic unit, since the twists cancel and the cyclotomic character is invariant under $\iota$. Thus $\mathcal B(\sigma)\ne0$.

The first-half inertia-vanishing supplier gives all four vanishings on each unused left inertia subgroup. The vanishing uses the Frobenius test on an inertia generator. The action on inertia is trivial and any continuous cocycle there is additive. The tame quotient supplies a generator for maps to the finite $\ell$-power torsion module. Frobenius sends this generator to its norm power in that quotient, and the norm is $1$ modulo $N_0$. Thus the cocycle value on the generator is fixed by Frobenius. The nontrivial residual scalar of Frobenius forces the value to vanish, since the twist has $\ell$-power order and reduces to $1$. Apply the same argument at the conjugate place, using anticyclotomicity for triviality of the twist on conjugate inertia.

Those inertia groups are in $L_*$ by the old left inertia inclusion in $L$ and the triviality there of the characters outside the unused left coordinates. So they are in $U$. The already used left characters are trivial on $h$. Multiply $h$ on the left by an element of $U$ to set the unused left coordinates to the required vector, with coordinate $1$ at the next left index and $0$ elsewhere in additive notation. The elements that change one coordinate at a time come from the corresponding inertia groups. Their product gives the adjustment $\eta\in U$ and leaves the used coordinates fixed.

Apply the degree-one Chebotarev input to $\eta h$ modulo the intersection of $U$ with all left character kernels. Exclude the existing places, the prescribed bad sets, places ramified modulo $U$, and the other finite exclusions in the selector. The input chooses a place and a Frobenius at a prolongation. Transport to the fixed prolongation by conjugacy and use agreement of Frobenius lifts modulo inertia. This preserves both the left coordinates and the conjugacy requirement modulo $U$. The finite splitting exception and the degree-one and unramified tests give the required split condition. Since Frobenius belongs to $L$, it fixes the roots of unity of order $2\ell^M$, giving $\operatorname{Norm}(p)\equiv1\pmod{2\ell^M}$. Inertia lies in $U\subseteq L$, so it and Frobenius give the decomposition-group inclusion in $L$. The admissible family supplies the good character at this split place, using the exclusion of its bad set and the inclusion of the decomposition group in $L\subseteq H$. The new character is surjective on its inertia, which yields an inertia element $\gamma$ of additive coordinate $1$. Right-multiply the initial Frobenius by an inertia element whose new character is the inverse of that initial Frobenius value. The adjusted Frobenius has trivial new character. Every Frobenius lift at the chosen prolongation has the same required old left coordinates, by the congruence in the smaller quotient. The enlarged family retains the old places and their conditions, and the exclusion of their places and conjugates gives the required distinctness. Since this adjustment is in $U$, normality preserves the congruence $k\sigma k^{-1}h^{-1}\in U$. The resulting $\sigma$ lies in $L_*$ because it is conjugate to $h$ modulo $U\subseteq L_*$ and $L_*$ is normal. It gives the required $\mathcal B(\sigma)\ne0$ at the new place.

#### Remarks and reading boundary

The determinant argument receives $\sigma,\gamma$, the dual Selmer representative $y$, the universal original cocycle at the specified column, and the nonzero value $\mathcal B(\sigma)$. Its comparison of inertia rows uses reciprocity and the twisted local relation as separate arithmetic inputs. In particular, the evaluation pairing $\beta$ belongs to the order comparison, whereas $\mathcal B$ takes values in $A$ and detects the arithmetic witness. On $L_*$, changes by global coboundaries leave both evaluations in $\mathcal B$ unchanged, since the actions are trivial there and $\iota L_*=L_*$.

All archive references below are to A2, joined SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
The read claims are conditional on the suppliers listed below. Neukirch, Schmidt and Wingberg give the classical cohomological context. Sutherland's Theorem 28.9 gives classical Chebotarev for a finite Galois extension and a conjugacy-stable set. The proof above uses the archive's degree-one interface with finite exclusions. [Cohomology of Number Fields](https://doi.org/10.1007/978-3-540-37889-1) · [MIT 18.785, Lecture 28](https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf).

##### [Lean] Definitions and hypotheses

- `Setup` and the restrictions on the twist. `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/H1MapSubgroup.lean:38–42`.
- `IsDual`, residual triviality and `Small`. `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsDualDualRep.lean:17–24`.
- `GalHyp`. `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTameInertiaElementAtTwistPrime.lean:119–120`.
- `Small2`, `PiLocalization₂` and the `Step` statement. `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/Small2.lean:13–25,51–57`.

##### [Lean, read] Conditional proof bodies and consumed segments

- Pairing, Selmer and output definitions. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/VecPairApply.lean:21–40,47–62,72–93,103–113`.
- Finite pairing, kernel comparison and complete dual-class selection. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsDualSelmerClassNotKilled.lean:11–38,42–81,83–126,133–153,157–167,169–197`.
- Cup coboundary identities and complete coefficient descent. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DualSelmerClassFromCoeffsKilledByMul.lean:20–39,43–46,48–124`.
- Surjective local-condition comparison conditional on the local lift. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BkOnLeMapOfSurjective.lean:9–21`.
- Conditional local-to-global order formula and its specialization. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerOrderFormulaDualSelmer.lean:19–40,51–146,150–185`.
- Universal cocycle from the natural presentation and scalar transfer. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniversalSelmerCocycleBaseChange.lean:12–38,41–48,50–110`.
- Character pairing and the row criterion handed to the determinant argument. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PerfectPairingFiniteModuleRowsCriterion.lean:12–17,21–44,52–108`.
- Global dual invariants on every coefficient module. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NoInvDualOfSetup.lean:12–30`.
- The three local invariant cases. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalInvariantsKilled.lean:11–17,20–34,36–85`.
- Conditional tame inertia vanishing on both conjugate places. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InertiaVanishingNoInvariantsFirstHalfPlaces.lean:76–139`.
- Scalar restriction argument and detection through the right kernel column. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallSubgroupCocycleFormNeZero.lean:11–37,39–95`.
- Triviality after killing the twist on the subgroup. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedRepresentationKillsSmallSubgroup.lean:10–27,29–43,45–79`.
- Tame and conjugate-dual comparison and cyclotomic annihilation. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwoMulCocycleValuesZeroOnSmallSubgroup.lean:16–47,49–122`.
- Polarization and trace identity. `src/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/PolarTraceMulVecMulVecEq.lean:8–26,28–89`.
- Trace argument modulo the annihilator of the outer product. `src/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/TwistTrace.lean:6–76,78–111`.
- Common zero subgroup and invariance of nonvanishing. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOpenNormalSubgroupTwoCocycles.lean:16–48,50–66,68–91`.
- Independent character values and transport from a Chebotarev prolongation. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAuxiliaryPrimesPrescribedFrobenius.lean:173–191,195–235`.
- Extension of the auxiliary family and both inertia choices. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNewPlaceFrobeniusConjugateModOpenNormalSub.lean:12–126`.
- Actual Step arguments and handoff. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntiOfKer.lean:153–229,230–260,301–309`.

##### [Lean] Named inputs and downstream interfaces

- Exported dual selection wrapper. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsDualSelmerClassNotKilledStatement.lean:6–7`.
- Exported order formula wrapper. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerOrderFormulaDualSelmerStatement.lean:6–7`.
- Greenberg–Wiles ratio, Poitou–Tate, global finiteness and Euler characteristic. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GreenbergWilesPairStatement.lean:6`.
- Local Tate pairing, local finiteness and Euler characteristic. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalDualityPerfectPairFiniteModulesStatement.lean:6`.
- Order of the finite local conditions. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalConditionOrderAboveLFiniteModulesStatement.lean:6`.
- Local saturation. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalConditionAboveLSaturatedOfSelmerSetup.lean:257`.
- Local count and archimedean signature matching. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalCountOfSetup.lean:491`.
- Surjective lift of the local Bloch–Kato condition. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerObstructionLeResidualSelmerSimpleExtension.lean:466`.
- Vanishing at the exceptional places in `Spl`. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousAlgebraMapPadicInt.lean:439`.
- Continuity, unramified actions and equivariance of the cup pairing. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PairingEquivariant.lean:54`.
- Scalar transfer of the Selmer condition. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerCocyclesScalarChangeTransferStatement.lean:6`.
- Square presentation and its naturality. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerPresentationMatrixOfGaloisCohomology.lean:20`.
- Tame scalar and its unit differences. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TameInertiaElementActsByScalar.lean:29`.
- Residual scalar test on a finite local algebra with an ℓ-power twist. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FirstHalfLocalCohomologyVanishingOfLocalDualityT.lean:156`.
- Full span of the twisted matrices. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanTopOfResidue.lean:70`.
- Cyclotomic image at the prescribed order. `src/Development/AutomorphicArithmetic/CyclotomicBounds/CyclotomicOrders/ExistsCycZPowNeOne.lean:21`.
- Determinant invariance under a matrix algebra endomorphism over a local ring. `src/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/CyclotomicTotient/SkolemNoether.lean:126`.
- Degree-one Chebotarev input `Cheb`. `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:11–13`.
- Closed `cheb_holds` supplier traced in §10.4.7. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean:66–67`.
- Downstream global reciprocity for the new inertia rows. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ReciprocityRelaxedSelmerDualSelmerNewPlace.lean:190`.
- Downstream twisted local relation. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UniversalCocycleRowsRelationNewPlace.lean:37`.
- Downstream determinant argument, covered in §10.4.9. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetNeZeroOfLowestFormNeZeroPresentation.lean:234`.

### 10.4.11 The local presentation at the new pair of places

#### Motivation

The witness in `10.4.10 evaluates a cocycle from the old Selmer presentation. The determinant in `10.4.9 belongs to the enlarged presentation. To transfer the witness, we need equations on the enlarged presentation and a comparison with the old one. Over the lifted coefficient ring, the tame relation ties the new inertia rows to the new Frobenius rows. After reducing coefficients, imposing the two inertia evaluations as relations restores the old Selmer conditions and identifies the Frobenius evaluations.

#### Example 10.19. Two local characters over a quotient of $\mathbb Z_3$ [Expository]

Take $\nu=1$, $M=3$, $A=\mathbb Z/9\mathbb Z$ and $B=A[x,y]/(x^2,y^4)$. At a place of norm $q=163\equiv1\pmod{54}$ the pro-$3$ tame relation $\sigma\gamma\sigma^{-1}=\gamma^q$ becomes commutation after imposing $\gamma^{27}=\sigma^{27}=1$. Put $h=(1+y)^{-1}=1-y+y^2-y^3$. The scalar actions on $(\gamma,\sigma)$ are $(1-x,h)$ on the first copy and $(1+x,1+y)$ on the conjugate copy. Give the cocycle values $(x,yh)$ and $(x,y)$ respectively. These define affine maps $v\mapsto R(g)v+f(g)$ on $B$. On the first copy both maps fix $1$, and on the second both fix $-1$. Thus each pair commutes because their scalar parts commute. The $27$th powers are the identity since $x^2=y^4=0$ and $\binom{27}{j}$ is divisible by nine for $1\le j\le3$.

The first equality is $x(yh)=yh\cdot x$ and the conjugate equality is $xy=y\cdot x$. Dropping $h$ from the first right-hand side gives a difference $-xy^2+xy^3\ne0$. Both actions become trivial under $x=y=0$. This calculation uses cocycles of the stated finite local tame quotient, one scalar coordinate at a time.

#### Example 10.20. Imposing the inertia rows over a quotient of $\mathbb Z_2$ [Expository]

Take $A=\mathbb Z/8\mathbb Z$, $\nu=2$, $M=4$ and $q=97\equiv1\pmod{32}$. With trivial action the tame quotient obtained by imposing $\gamma^{16}=\sigma^{16}=1$ is $(\mathbb Z/16\mathbb Z)^2$. On two copies use the cocycles into $A^4$ with values $e_1,e_2,e_3,e_4$ on $\gamma,\sigma,\gamma^c,\sigma^c$, respectively. These are homomorphisms since $16A=0$. Imposing the inertia evaluations as relations gives $A^4/(Ae_1+Ae_3)$, free on the classes of $e_2,e_4$. In these coordinates the Frobenius rows are $(1,0)$ and $(0,1)$. Changing lifts to $\sigma\gamma^5$ and $\sigma^c(\gamma^c)^7$ adds $5e_1$ and $7e_3$ to the rows and preserves their images. The quotient cocycles vanish on all inertia. This is the comparison for a local functor with trivial action. The global comparison must also preserve the Selmer conditions at the other places.

#### Definitions and coefficient data

Keep the twist index $i$ and signature $s$ fixed. Write $O_0=X.O0(i)$, $\ell=X.l(i)$, $\nu=\nu(X,i)>0$, $I=(\ell^\nu)\mathfrak m_{O_0}$ and $N_0=\ell^{\nu+1}$. The coefficient algebras annihilate $I$ (`Kills`), so $N_0$ annihilates their modules. Over a DVR with uniformizer $\varpi$ and $e=v_\varpi(\ell^\nu)$ this means factoring through $O_0/(\varpi^{e+1})$. The character exponent group is $\mathbb Z/\ell^M\mathbb Z$, where $M\ge\nu+2$. The finite dual pairing takes values in $\mathbb Z/N_0\mathbb Z$.

Use `Small2` and `NewPl`. The new place $p$ lies in a split pair $p,p^c$ outside the exceptional set, hence away from $\ell$. Its norm $q$ satisfies $q\equiv1\pmod{2\ell^M}$. Its chosen decomposition group lies in the $c$-stable subgroup $L$, where $g^c$ denotes `cConj` applied to $g$. The arithmetic Frobenius $\sigma$ acts on residue classes by the $q$th power. The continuous exponent character $d$ has $d(\gamma)=1$ on the chosen inertia element $\gamma$. Write $[d(\tau)]$ for the representative in $[0,\ell^M-1]$. At the transported conjugate prolongation use $\sigma^c,\gamma^c$. On $L$ the original untwisted action is the identity after coefficient reduction by `Small2`. The `IsDual` action before twisting is also the identity there, since the cyclotomic factor is trivial modulo $N_0$.

Let $A$ be the finite local specialization in `Step` and $B=A[x,y]/(x^2,y^{2r})$ with $r=D.R.r>0$. Let $\pi:B\to A$ be augmentation and use a bar for reduction. The new right slot $q_0$ is evaluated at $x$, the newly used left slot $q_1$ at $y$, and the other slots at the images of their old $a_0(v)t$. The old value of $q_1$ was zero. The product rule is $\kappa'(g)\prod_v(1+\xi_v)^{[d_v(g)]}=1$ and reduces to the rule for $\kappa$. On new inertia only the new right character contributes. At $\sigma$ its exponent is zero, the newly used left exponent is one, and the other factors are one by the kernel and zero-slot conditions. Hence $\kappa'(\tau)(1+x)^{[d(\tau)]}=1$ on inertia and $\kappa'(\sigma)(1+y)=1$. The characters invert under $c$, and $\kappa$ is trivial on the new decomposition group. [Lean, read] (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntiOfKer.lean:64–83,261–352`.)

Write $\operatorname{row}(H)$ for the span of the rows of $H$. An archive `Univ` pair $(H,Z_H)$ takes each solution $v$ of $Hv=0$ in any discrete coefficient module to the Selmer cocycle $g\mapsto Z_H(g)v$. It represents every Selmer class this way and detects zero classes by $v=0$. Use the old pair $(\Psi,Z)$ over $A$ for $Q$ and the lifted pair $(\Phi',Z')$ over $B$ for $Q'=Q\cup\{p,p^c\}$. The pair $(\bar\Phi',\bar Z')$ is universal over $A$ for $Q'$. Restrict scalars through $\pi$ and use `selmerCocycles_scalarChange_transfer` to identify actions, coboundaries and Selmer conditions before applying the three clauses of `Univ`. This transfer uses the archive local conditions, including the condition at $\ell$. The square presentations before specialization and the universal cocycles of the specialized matrices come from `exists_universalSelmerCocycle_baseChange` as used in `Step`. [Lean, read]. The scalar-transfer proof is Lemma 10.27. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/VecPairApply.lean:16–21,47–79,101–117` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UniversalSelmerCocycleMapAlgHom.lean:10–22`.)

#### Lemma 10.21. Tame inertia with square-zero increment [Lean, read]

Let $W$ be discrete and killed by $N_0$. Suppose the action is $1+[d(\tau)]b$ on inertia and $1+a$ on $\sigma$, with $b^2=0$. Then every continuous cocycle $f$ satisfies $a f(\gamma)=b f(\sigma)$. If $b=0$, vanishing on $\gamma$ implies vanishing on inertia.

*Proof.* `TameQuotient` gives the pro-$\ell$ inertia quotient with kernel $J$ whose open normal subgroups have index prime to $\ell$. The character $d$ kills $J$ by coprime order. The action is then trivial there, so $f|_J$ is additive with open kernel. Its image is killed both by the prime-to-$\ell$ index and by $N_0$, hence vanishes. Write $\sigma\gamma=\gamma^q j\sigma$ with $j\in J$. Iterating the cocycle identity gives $f(\gamma^q)=q f(\gamma)+\binom q2 b f(\gamma)$ and the action $1+qb$ on $\gamma^q$. The congruence $q\equiv1\pmod{2N_0}$ ensures both $q=1$ on $W$ and $N_0\mid\binom q2$, including at $\ell=2$. The two expressions for the cocycle on $\sigma\gamma$ thus give $(1+a)f(\gamma)+f(\sigma)=f(\gamma)+(1+b)f(\sigma)$. Finally the image of $\gamma$ generates $\mathbb Z_\ell$ topologically because $d(\gamma)=1$ modulo $\ell$ excludes divisibility by $\ell$ there. If $b=0$, the continuous inertia restriction is additive, and vanishes once it vanishes on $J$ and $\gamma$. $\square$

A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TameRelationCocycleSquareZeroInertia.lean:11–96`. The local-field background is the description by prime-to-residue-characteristic roots of a uniformizer after unramified extension. The precise quotient in the proof is the named archive input. [Sutherland, MIT 18.785, Lecture 11, Theorem 11.10, p. 3](https://math.mit.edu/classes/18.785/2021fa/LectureNotes11.pdf)

#### Theorem 10.22. Conditional local presentation and determinant transfer [Lean, read]

Assume the coefficient, character and universal-presentation data above, `TameLocal` and the archive scalar transfer. Index the new rows by $j=(b,c)\in\{0,1\}\times\{1,\ldots,r\}$, writing $g_0=g$ and $g_1=g^c$. Let $u_j=Z'(\sigma_b)_c$, $T_j=Z'(\gamma_b)_c$, $U_j=Z(\sigma_b)_c$, and set $\eta_{0,c}=\kappa'(\sigma)$ and $\eta_{1,c}=1$. Put $W=\operatorname{row}(\bar\Phi')+\operatorname{span}_A\{\bar T_j\}$. Then:

1. Over $B$, $x u_j-y\eta_j T_j\in\operatorname{row}(\Phi')$.
2. Over $A$ there is an $a$ by $a'$ matrix $E$, where $a,a'$ are the sizes of $\Psi,\Phi'$. Its rows generate $A^{a'}/W$, the rows of $\Psi E$ belong to $W$, and $\bar u_j-U_j E\in W$. The induced map $A^a/\operatorname{row}(\Psi)\to A^{a'}/W$ is an isomorphism [Expository].
3. Assume `Setup`, `IsDual`, an old dual Selmer cocycle $f^\vee$ with coefficients in $A$, and a balanced perfect pairing $\beta:Y\times A\to\mathbb Z/N_0\mathbb Z$ with the finite row criterion over $A$. This criterion says that a row annihilating all solutions in $Y$ belongs to the span of the matrix rows over $A$. Assume the named reciprocity identity below for the split pair. With $k_{0,c}=f^\vee(\sigma)_c$ and $k_{1,c}=-f^\vee(\sigma^c)_c$, we have $\sum_j k_j\bar T_j\in\operatorname{row}(\bar\Phi')$. If $\sum_j k_j U_j\operatorname{adj}(\Psi)_{\bullet l_0}\ne0$ for some column $l_0$, then $\det\Phi'\ne0$.

*Lifted relations.* In the direct case the increments are $-x[d(\tau)]$ and $-y\kappa'(\sigma)$, by $x^2=0$ and the inverse character formula. In the conjugate case they are $x[d(\tau)]$ and $y$. Lemma 10.21 gives $x f(\sigma)=y\kappa'(\sigma)f(\gamma)$ and $x f(\sigma^c)=y f(\gamma^c)$. Take $B^{a'}/\operatorname{row}(\Phi')$ as coefficient module. The standard basis images solve the equations of $\Phi'$, so `Univ` supplies a cocycle on these images. Evaluation of a row gives precisely its class in the quotient. The two equalities give the asserted row membership. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UniversalCocycleRowsRelationNewPlace.lean:15–122`.)

*Reduced comparison.* The action over $A$ is trivial on the new decomposition group and its conjugate. Vanishing on $\gamma,\gamma^c$ restores the unramified condition by Lemma 10.21. If a chosen prolongation differs from the transported one, conjugating an inertia element where $f$ vanishes by $g$ gives a coboundary with witness $-f(g)$. Thus the unramified class is valid at the chosen prolongation as well. The condition above $\ell$ is unchanged. The same holds at $\operatorname{Spl}(i)\cup Q$ and outside $\operatorname{Spl}(i)\cup Q'$.

Take the coefficient module $A^{a'}/W$. Its basis images give a relaxed cocycle with zero new inertia. Its class is represented by an old solution vector, whose entries lift to rows of $E$. The equations for this vector give the rows of $\Psi E$ in $W$. The coboundary relating the two representatives vanishes on $\sigma_b$ because its action is trivial, yielding $\bar u_j-U_j E\in W$. Quotient further by the images of the rows of $E$. The relaxed cocycle becomes a coboundary there, forcing all basis images to vanish by the zero test of `Univ`. Thus the rows of $E$ generate. For the isomorphism, in every discrete $A$-module the old classes are exactly the relaxed classes with both inertia evaluations zero. The converse uses that an unramified class restricts to a coboundary on inertia, which is zero under trivial action. These evaluations are invariant under coboundaries. The map induced by $E$ therefore gives a bijection on homomorphisms into every discrete $A$-module, so it is an isomorphism. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerUnramifiedOfVanishInertiaGenerators.lean:18–65` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ComparisonCocycles.lean:24–117`.)

*Signed row.* The input `reciprocity_relaxedSelmer_dualSelmer_newPlace` equates $\sum_c\beta(f(\gamma)_c,f^\vee(\sigma)_c)$ and its conjugate evaluation for each reduced relaxed cocycle $f$. In `NewRecip.reciprocity` the two local cup invariants are a common unit times the evaluations with opposite signs. Conjugation inverts the chosen primitive $N_0$th root, giving the minus sign by the transport rule for the invariants. Old and exceptional places contribute zero by the dual local conditions, and outside the support the cup product is unramified. The sum-of-invariants input gives equality after cancelling the unit. This uses `sum_local_inv_eq_zero_of_unramified_cocycle_pow` with `PoitouTateTotallyComplex`, `pairing_equivariant_alt` and `tame_cupProduct_invariant_unramified_hom`. The sum-of-invariants input and the assembly of the invariant two-cocycle are read in §10.4.11.1.

Apply the identity to the cocycle from $cv$ for any solution $v$ of $\bar\Phi'v=0$ in $Y$ and any $c\in A$. Balancing gives $\beta(\sum_j k_j\bar T_j v,c)=0$ for all $c$. Perfection gives zero in $Y$. The row criterion puts the combination in $\operatorname{row}(\bar\Phi')$ itself, before adjoining the inertia rows. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ReciprocityRelaxedSelmerDualSelmerNewPlace.lean:126–184,190–315` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntiOfKer.lean:117–151`.)

*Determinant.* Let $G$ have top rows lifting $E$ and bottom rows $\eta_jT_j$. Since $\bar\eta_j=1$, the rows generate modulo $\operatorname{row}(\Phi')$ by the comparison and Nakayama for the nilpotent ideal $(x,y)$. An equation modulo $(x,y)$ on these generators lifts to one modulo $\operatorname{row}(\Phi')$ with the prescribed reduced coefficients. Lift its coefficients, write the residual error as $xv+yw$ after subtracting a row combination of $\Phi'$, and express $v,w$ in the generators modulo $\operatorname{row}(\Phi')$ to correct the coefficients.

For instance, if $(\Psi E)_b$ is congruent to $\sum_j R_{bj}\bar T_j$ modulo $\operatorname{row}(\bar\Phi')$, its coefficient row on the reduced generators is $(\Psi_b,-R_b)$. The old equations give top coefficient rows reducing to $(\Psi,C)$, where $C$ is minus the coefficients expressing $\Psi E$ in the inertia rows modulo $\bar\Phi'$. Replace row $l_0$ by a lift of $(0,k)$ using the signed relation. Lift the Frobenius comparison to rows $V_j$ with $\bar V_j=(U_j,S_j)$ for some $S_j$ and $u_j-V_jG\in\operatorname{row}(\Phi')$. Use $y(0,e_j)-xV_j$ as the new bottom coefficient rows. Their products with $G$ are relations by claim 1. The determinant of this square relation matrix belongs to the zeroth Fitting ideal of $B^{a'}/\operatorname{row}(\Phi')$, which is $(\det\Phi')$. [Stacks Project, Lemma 15.8.2 and proof](https://stacks.math.columbia.edu/tag/07Z8)

Terms with at least two lower rows from $-xV$ vanish by $x^2=0$. The term with none vanishes by $y^{2r}=0$. Factor out $xy^{2r-1}$. This monomial annihilates $(x,y)$, so compute the coefficient over $A$. In the term from lower row $j$, exchange it with row $l_0$. The row exchange contributes a minus sign. The new top row has left part $-U_j$, contributing a second minus in the cofactor expansion. In the lower right block, the identity with row $j$ replaced by $k$ has determinant $k_j$. The result is $xy^{2r-1}\sum_j k_j U_j\operatorname{adj}(\Psi)_{\bullet l_0}$. The monomial is part of a free $A$-basis, so its nonzero coefficient forces $\det\Phi'\ne0$. $\square$ (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetNeZeroOfLowestFormNeZeroPresentation.lean:12–372` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsRingSqZeroNilpotentAugmented.lean:22–71`.)

#### Remarks on the Step interface

The old equations come from $\Psi$ through the comparison, with one row replaced by the signed inertia relation. Old inertia enters separately in the prime choice. At the first unused left place, the specialized twist is trivial on inertia. The tame relation says the tame cocycle value is Frobenius-fixed since the norm is one modulo $N_0$. Frobenius has residual scalar different from one there (or its inverse for the dual), and an $\ell$-power twist leaves that residual scalar unchanged. Frobenius minus one is invertible, so the tame cocycle value vanishes on both sides of the split pair, for the original and dual cocycles. This permits the open normal subgroup in the selection to contain that inertia. The lifted coordinate $y$ is then read by the new Frobenius. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InertiaVanishingNoInvariantsFirstHalfPlaces.lean:38–139` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntiOfKer.lean:241–260,301–347`.)

The scalar in the theorem is the signed evaluation in §10.4.10 on the old right kernel column. It can be a nonunit. In the bad branch the old determinant is zero under the specialization, with $t^h=0$ for $h=2(e+1)w+2$. Each variable in the lifted evaluation is a multiple of $t$, or is $x$ or $y$. The largest possible surviving degree is $(h-1)+1+(2r-1)$. If all coefficients below degree $h+2r$ belonged to $I$, the lift's determinant would vanish in $B$, contradicting the theorem. This is the return to the existing `Step` coefficient bound. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntiOfKer.lean:188–229,261–352`.)

The reading covers the local relation, the unramified comparison, the reciprocity assembly under its named inputs, and the passage to the determinant. Section 10.4.12 supplies the square Selmer presentation and scalar transfer. The global invariant sum is read in §10.4.11.1 (Theorem 10.22f and Proposition 10.22g). The suppliers of the local cup invariant, of `PoitouTateTotallyComplex` and of the deeper global duality of §10.4.10 retain their reading boundaries. The examples compute local rules on finite tame quotients.

#### 10.4.11.1 The global invariant sum in the new-place reciprocity

##### Motivation [Expository]

The signed row of Theorem 10.22 rests on one global identity. For a reduced relaxed Selmer cocycle $x$ and an old dual Selmer cocycle $y$, the two local cup invariants at the new split pair $p,p^c$ are a common unit times the evaluations $\sum_c\beta(x(\gamma)_c,y(\sigma)_c)$ and $-\sum_c\beta(x(\gamma^c)_c,y(\sigma^c)_c)$, and their sum vanishes. The vanishing is the content of the archive theorem `sum_local_inv_eq_zero_of_unramified_cocycle_pow`, which §10.4.11 cited but did not open. This subsection reads its direct producer and shows exactly which part of global duality it consumes.

Two facts have to be separated. The first is a statement about one-dimensional coefficients only: for a continuous $2$-cocycle on $G_F$ with values in $\mu_{\ell^n}$ that is invariant under the subgroup generated by the inertia groups outside a finite set $S$ of places containing those above $\ell$, the sum over $S$ of the local invariants of its restrictions is zero. This is the Brauer–Hasse–Noether reciprocity in cohomological form, read off from the degree-two tail of the Poitou–Tate sequence for the cyclotomic character. The second is a statement about the actual coefficient pairing of the Step argument: the cup product of a Selmer cocycle with values in $Y^r$ and a dual cocycle with values in $Y'^r$, paired coordinatewise by a balanced $\beta$ into $\mathbb Z/N_0\mathbb Z$, is such an invariant $2$-cocycle, and all its local invariants vanish except at $p$ and $p^c$. The first fact is Theorem 10.22f, the second is Proposition 10.22g. Neither uses the Selmer order formula of §10.4.10 nor the obstruction count of §10.4.12; Remark 10.22h records the differences.

In the two examples below, $F=\mathbb Q(i)$ is totally complex, $\ell=3$, $n=1$ and $N_0=3$. We take $x$ to be a cubic character $\chi$ of $G_F$ with trivial action on $\mathbb Z/3\mathbb Z$, and $y$ to be the Kummer cocycle $\delta b$ of an element $b\in F^\times$, with values in $\mu_3$. The pairing is $P(a,\zeta^k)=ak$ for a fixed primitive cube root of unity $\zeta$. It satisfies $P(a,g\cdot\zeta^k)=\omega(g)P(a,\zeta^k)$ for the mod-$3$ cyclotomic character $\omega$, which is the equivariance required of $\beta$ in the archive. The cup product $\chi\cup\delta b$ lies in $H^2(F,\mu_3)=\operatorname{Br}(F)[3]$ and its local invariant at $v$ is the local Artin symbol $\chi_v(b)$, written additively in $\mathbb Z/3\mathbb Z$ through $\omega\mapsto1$. This is the classical case $r=1$ of the archive pairing, with the real coefficient pairing and real cocycles, not an abstract Brauer class.

##### Example 10.22a. Two places, and what happens when one is deleted [Expository]

Let $\chi$ be the cubic character of $\mathbb Q$ of conductor $7$, restricted to $G_{\mathbb Q(i)}$. The cubes in $(\mathbb Z/7\mathbb Z)^\times$ are $\{1,6\}$, and $3$ is a generator with $3^k$ running through $3,2,6,4,5,1$. Put $\chi_7(3)=\omega$, so that $\chi_7(5)=\omega^5=\omega^2$. Take $b=2+i$, of norm $5$. The places of $F$ where the invariant of $\chi\cup\delta b$ can be nonzero are those where $\chi$ ramifies, namely the inert place $(7)$ with $q=49$, and those where $b$ is not a unit, namely $(2+i)$ with $q=5$. The set $S$ must also contain the inert place $(3)$ above $\ell$.

1. At $(2+i)$ the character is unramified and $b$ is a uniformizer, so $\chi_v(b)=\chi(\operatorname{Frob}_v)$. The residue degree is one, so $\operatorname{Frob}_v$ restricts to $\operatorname{Frob}_5$ on the cubic field, and $\chi_v(b)=\chi_7(5)=\omega^2$. Invariant $2$.
2. At $(7)$ the local field is $\mathbb Q_7(i)=\mathbb Q_{49}$, unramified quadratic over $\mathbb Q_7$, and $\chi$ restricted to it is still totally ramified of order three. Local reciprocity is compatible with norms, so $\chi_v(b)=\chi_{\mathbb Q_7}(N(2+i))=\chi_{\mathbb Q_7}(5)$. For the rational element $5$, global reciprocity over $\mathbb Q$ gives $\chi_5(5)\chi_7(5)_{\mathrm{loc}}=1$ since $5$ is a unit at every other finite prime and $\chi$ is even. As $\chi_5(5)=\chi(\operatorname{Frob}_5)=\omega^2$, we get $\chi_{\mathbb Q_7}(5)=\omega$. Invariant $1$.
3. At $(3)$, at $(2-i)$ and at $(1+i)$ the character is unramified and $b$ is a unit. Invariant $0$.

The tuple of invariants over $S=\{(3),(7),(2+i),(2-i),(1+i)\}$ is $(0,1,2,0,0)$, with sum $3\equiv0$. It is globally realized by $\chi\cup\delta b$. Now delete the nonzero place $(7)$: the tuple $(0,0,2,0,0)$ has sum $2\ne0$. By Theorem 10.22f no $2$-cocycle on $G_F$ with values in $\mu_3$ that is invariant under the inertia groups outside $S$ restricts to it. No choice of $\chi$ and $b$, and more generally no global class, produces an invariant at $(2+i)$ alone. The place $(7)$ carries the compensating value because $\chi$ ramifies there, which is exactly how the new inertia evaluation enters Theorem 10.22.

The archive computes the invariant at $(7)$ through the tame formula of `tame_cupProduct_invariant_unramified_hom`, as $u\cdot x(\gamma)\,y(\varphi)$ with $u$ a unit fixed by the normalisation, $\gamma$ a tame inertia generator with $d(\gamma)=1$ and $\varphi$ a Frobenius. Here $y(\varphi)$ is the cubic residue symbol of $b$ in $\mathbb F_{49}=\mathbb F_7(i)$. Since $(2+i)^7=2-i$ by Frobenius and $(2+i)(2-i)=5$, we get $(2+i)^8=5$ and $(2+i)^{16}=25\equiv4$. As $4=2^2$ with $2$ a primitive cube root of unity in $\mathbb F_7$, the residue symbol is $2$. The value $1$ computed above then forces $u\,x(\gamma)\equiv2$. Only the product $u\,x(\gamma)$ is determined, and this is the only place where the unspecified unit enters.

##### Example 10.22b. A conjugate split pair with opposite invariants [Expository]

Let $\chi$ now be the cubic character of $\mathbb Q$ of conductor $13$, restricted to $G_{\mathbb Q(i)}$. Since $13\equiv1\pmod{12}$, the prime $13=(3+2i)(3-2i)$ splits in $F$ and each factor has $q=13\equiv1\pmod 3$, so both local fields are $\mathbb Q_{13}$ and $\chi$ is totally ramified at $p=(3+2i)$ and at $p^c=(3-2i)$. The cubes in $(\mathbb Z/13\mathbb Z)^\times$ form the subgroup $\{1,5,8,12\}$, and $2$ is a generator with powers $2,4,8,3,6,12,11,9,5,10,7,1$. Put $\chi_{13}(2)=\omega$, so $\chi_{13}(7)=\omega^{11}=\omega^2$ and $\chi_{13}(10)=\omega^{10}=\omega$.

Take again $b=2+i$. From $3+2i\equiv0$ we get $i\equiv-3\cdot2^{-1}\equiv5\pmod p$ and $i\equiv8\pmod{p^c}$, so $b\equiv7\pmod p$ and $b\equiv10\pmod{p^c}$.

1. At $p$ the element $b$ is a unit and $\chi$ is totally ramified, so $\chi_p(b)=\chi_{\mathbb Q_{13}}(7)=\chi_{13}(7)^{-1}=\omega$ by the same rational reciprocity argument as in Example 10.22a. Invariant $1$.
2. At $p^c$ likewise $\chi_{p^c}(b)=\chi_{13}(10)^{-1}=\omega^2$. Invariant $2$.
3. At $(2+i)$ the character is unramified and $b$ is a uniformizer, so the invariant is $\chi(\operatorname{Frob}_5)=\chi_{13}(5)$. Since $5$ is a cube modulo $13$, this is $0$.
4. At $(3)$, $(2-i)$ and $(1+i)$ the invariant is $0$.

The tuple is $(1,2)$ at $(p,p^c)$ and zero elsewhere, with sum $0$. The two nonzero entries are negatives of each other, which is the shape used in Theorem 10.22: deleting either breaks the identity, and the equality of the two signed evaluations is the whole content of the sum. In the tame formula, $x(\gamma)=x(\gamma^c)$ because $\chi$ comes from $\mathbb Q$, and the residue symbols are $7^4\equiv9$ and $10^4\equiv3=9^2$ in $\mathbb F_{13}$, that is $1$ and $2$ with respect to $\zeta\equiv9$. The sign in the archive's conjugate formula comes from transporting the place and the root of unity by complex conjugation, which inverts $\zeta$; with this transport the two invariants are read as $u\,x(\gamma)\,y(\varphi)$ and $-u\,x(\gamma^c)\,y(\varphi^c)$ with equal absolute values, as the formula in `local_pair` asserts. One checks that $7\cdot10=70\equiv5$ is a cube, which is the residue-field form of the same cancellation.

##### Definitions [Lean, read]

Fix a totally complex number field $F$, an algebraic closure $\Omega$, and write $G=\operatorname{Aut}_F(\Omega)$ with the Krull topology. For a valuation subring $A\subset\Omega$ write $\operatorname{Dec}(A)$ for its decomposition group and $\operatorname{Ine}(A)$ for the inertia subgroup, the elements of $\operatorname{Dec}(A)$ moving every $A$-integral element by something of valuation less than one. The subring $A$ lies over the finite place $v$ if $A$-integrality of $x\in\mathcal O_F$ with valuation less than one is equivalent to $x\in v$. Fix a prime $\ell$ and $n\ge1$. The mod $\ell^n$ cyclotomic character $\omega_n:G\to(\mathbb Z/\ell^n\mathbb Z)^\times$ is the reduction of the $\ell$-adic cyclotomic character. (A2, `src/ReciprocityTheory/GaloisValuations/Global.lean:15,45,106`; `src/Formalism/ConjugateSelfDual/Statement.lean:20–25`.)

For a continuous representation $\rho$ of a topological group $\Gamma$ on a discrete module $M$, the archive's $Z^2(\rho)$ is the module of continuous maps $w:\Gamma\times\Gamma\to M$ with $\rho(g)w(h,k)-w(gh,k)+w(g,hk)-w(g,h)=0$, $B^2(\rho)$ is the module of differentials $d^1c(g,h)=\rho(g)c(h)-c(gh)+c(g)$ of continuous $c:\Gamma\to M$, and $H^2(\rho)=Z^2/B^2$. (A2, `src/ReciprocityTheory/NeutralLocalFields/Duality.lean:73–107`; `src/ReciprocityTheory/GaloisValuations/SeparatedDvrSecondCohomologyMem.lean:97–107`.) For a character $\mu:\Gamma\to R^\times$, $\operatorname{charRep}(\mu)$ is $R$ with $g$ acting by multiplication by $\mu(g)$. The global coefficient module is $\mu\mathrm{Rep}=\operatorname{charRep}(\omega_n)$ on $\mathbb Z/\ell^n\mathbb Z$, and for $A$ over $v$ the local module $\mu\mathrm{Loc}(A)$ is its restriction to $\operatorname{Dec}(A)$. (A2, `src/ReciprocityTheory/Hypotheses/GalCohDefs.lean:21,141`; `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean:17–19`.)

An invariant family is a choice, for every valuation subring $A$, of a linear map $\operatorname{inv}_A:H^2(\mu\mathrm{Loc}(A))\to\mathbb Z/\ell^n\mathbb Z$. Given a primitive $\ell^n$th root of unity $\zeta\in\Omega$, the family is a family of local invariants, `IsLocalInvariants`, if for every $A$ over a finite $v$ the map $\operatorname{inv}_A$ is bijective and normalised, and the family is conjugation compatible. Normalised means that the class of the cocycle $(g,h)\mapsto\kappa(g)\chi(h)$ has invariant $1$ whenever $\kappa$ records the action on an $\ell^n$th root of a uniformizer of $v$ through $g(y)=\zeta^{\kappa(g)}y$, and $\chi$ is an additive character of $\operatorname{Dec}(A)$ that kills inertia and takes the value $1$ on Frobenius elements. Conjugation compatible means that for every ring automorphism $\sigma$ of $\Omega$ covering an automorphism of $F$, with $\sigma(\zeta)=\zeta^c$ and $\sigma(A)=A'$, the invariants of corresponding cocycles on $A$ and $A'$ agree after multiplying the transported cocycle by $c$. (A2, same file, :23–53.) These are the two properties used by `local_pair` in §10.4.11: bijectivity is handed to the tame formula, and conjugation compatibility with $c=-1$ produces the minus sign at $p^c$.

For a finite set $S$ of finite places, $N_S$ is the closed normal subgroup of $G$ generated by the inertia groups $\operatorname{Ine}(A)$ for all $A$ over places outside $S$, and $G_S=G/N_S$. A continuous cocycle on $G_S$ is the same as one on $G$ invariant under right translation of both arguments by $N_S$. The set $S$ contains the places above $\ell$ if every $v$ with $\ell\in v$ lies in $S$. (A2, `src/ReciprocityTheory/GaloisValuations/Global.lean:128–145`; `src/ReciprocityTheory/Hypotheses/GalCoh.lean:141–142`.)

The deep input `PoitouTateTotallyComplex` asserts, for every totally complex $F$, every $\ell$, $n\ge1$ and $\zeta$, the existence of a family of local invariants $\operatorname{inv}$ such that for every $S$ containing the places above $\ell$, every choice $A_v$ of valuation subrings over $v\in S$, every lift $\mu:G_S\to(\mathbb Z/\ell^n\mathbb Z)^\times$ of $\omega_n$ and every finite discrete continuous $G_S$-module $M$, the nine-term sequence
$$0\to H^0(M)\to\prod_{v\in S}H^0_v(M)\to H^2(M^\vee)^\ast\to H^1(M)\to\prod_{v\in S}H^1_v(M)\to H^1(M^\vee)^\ast\to H^2(M)\to\prod_{v\in S}H^2_v(M)\to H^0(M^\vee)^\ast\to0$$
is exact, where $M^\vee$ is the $\mu$-twisted dual and the maps out of the local products are sums over $v$ of local cup products followed by $\operatorname{inv}_{A_v}$; and that the Tate–Shafarevich kernels in degrees one and two are finite and dual with equal orders. (A2, same file, :150–175, :288–301.) The reading here concerns only the exactness at the eighth position, from $\prod_{v\in S}H^2_v(M)$ to $H^0(M^\vee)^\ast$, for the one-dimensional $M=\operatorname{charRep}(\mu)$.

##### Lemma 10.22c. Descent of an invariant cochain to the quotient [Lean, read]

Let $\Gamma$ be a topological group, $N$ a subgroup, and $w:\Gamma\times\Gamma\to M$ continuous with $w(gn,hn')=w(g,h)$ for all $n,n'\in N$. Then there is a unique $W:(\Gamma/N)\times(\Gamma/N)\to M$ with $W(\bar g,\bar h)=w(g,h)$, and $W$ is continuous.

*Proof.* Define $W$ on cosets by choosing representatives; the invariance hypothesis is exactly independence of the choice, since $g$ and $g'$ lie in the same left coset when $g'=gn$. The quotient map $\Gamma\to\Gamma/N$ is an open quotient map, hence so is its product with itself, and a function out of a quotient is continuous when its composite with the quotient map is. $\square$ (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumInvEqZeroOfUnramifiedCocycle.lean:9–20`.)

##### Lemma 10.22d. The descended cochain is a cocycle for the lifted character [Lean, read]

In the setting of the Definitions, let $S$ contain the places above $\ell$. Then $\omega_n$ kills $N_S$ and factors through a continuous $\mu:G_S\to(\mathbb Z/\ell^n\mathbb Z)^\times$. If $w\in Z^2(\mu\mathrm{Rep})$ is invariant under $N_S$ in both arguments, its descent $W$ of Lemma 10.22c lies in $Z^2(\operatorname{charRep}(\mu))$.

*Proof.* For $\sigma$ in an inertia group at a place $v$ not above $\ell$, the $\ell$-adic cyclotomic character is trivial, because the $\ell$-power roots of unity are unramified at $v$; the archive proves this as `cyc_eq_one_of_mem_Ine` and passes it through the reduction $\mathbb Z_\ell\to\mathbb Z/\ell^n\mathbb Z$. The kernel of $\omega_n$ is a closed normal subgroup containing these inertia groups, hence contains their normal closure and its closure, which is $N_S$. The quotient map $\mu$ exists by the universal property of $G_S$. For the cocycle identity, lift the three arguments to $G$; the identity for $W$ at the lifts is the identity for $w$ after rewriting $W(\bar g\bar h,\bar k)=w(gh,k)$ and $\mu(\bar g)=\omega_n(g)$. Continuity is Lemma 10.22c. $\square$ (A2, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean:254–280`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumInvEqZeroOfUnramifiedCocyclePow.lean:12–22`.)

##### Lemma 10.22e. The degree-two tail at the identity invariant [Lean, read; conditional on `PoitouTateTotallyComplex`]

Assume `PoitouTateTotallyComplex` and keep $S$, $A_v$, $\mu$ as above. Let $\operatorname{inv}$ be the family it supplies. Then for every class $x\in H^2(\operatorname{charRep}(\mu))$,
$$\sum_{v\in S}\operatorname{inv}_{A_v}\bigl(\operatorname{res}_v x\bigr)=0,$$
where $\operatorname{res}_v$ restricts along $\operatorname{Dec}(A_v)\to G_S$ and the local class is viewed in $H^2(\mu\mathrm{Loc}(A_v))$ through the identification of $\operatorname{charRep}(\mu)$ restricted to $\operatorname{Dec}(A_v)$ with $\mu\mathrm{Loc}(A_v)$.

*Proof.* Apply the nine-term exactness to $M=\operatorname{charRep}(\mu)$, which is finite and has continuous action because $\omega_n$ is continuous. Exactness at the eighth position says that the composite of the localization $H^2(M)\to\prod_vH^2_v(M)$ with the transgression $\prod_vH^2_v(M)\to H^0(M^\vee)^\ast$ is zero. The twisted dual $M^\vee$ is $\operatorname{Hom}(M,\mathbb Z/\ell^n\mathbb Z)$ with $g$ acting by $\mu(g)\cdot\phi\circ\mu(g)^{-1}$, which is trivial for $M=\operatorname{charRep}(\mu)$; so the identity map is an invariant element $\iota\in H^0(M^\vee)$. The transgression evaluated at $\iota$ is $\sum_v\operatorname{inv}_{A_v}$ of the local cup products $\operatorname{res}_vx\cup\iota$, and cupping a degree-two class with the identity functional returns the class itself. Hence the sum of the local invariants of $\operatorname{res}_vx$ is zero. The identification of the restricted $\operatorname{charRep}(\mu)$ with $\mu\mathrm{Loc}(A_v)$ is the equality $\mu(\bar g)=\omega_n(g)$ on decomposition groups, implemented by a bijective map on $H^2$ with the identity on cochains. $\square$ (A2, `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean:64–99,196–220,305–337`.)

The lemma uses one direction of one exactness statement. The other direction, that a tuple of local classes with vanishing invariant sum is the restriction of a global class, is also part of the nine-term exactness but is not used by the producer read here.

##### Theorem 10.22f. The finite invariant sum [Lean, read; conditional on `PoitouTateTotallyComplex`]

Assume `PoitouTateTotallyComplex`. Let $F$ be totally complex, $\ell$ prime, $n\ge1$, and $\zeta\in\Omega$ a primitive $\ell^n$th root of unity. There is a family of local invariants $\operatorname{inv}$ for $\zeta$ with the following property. For every finite set $S$ of places containing those above $\ell$, every choice of $A_v$ over $v$ for all finite $v$, every $w\in Z^2(\mu\mathrm{Rep})$ with $w(gu,hu')=w(g,h)$ for all $u,u'\in N_S$, and every family of local cocycles $w_v\in Z^2(\mu\mathrm{Loc}(A_v))$ with $w_v(g,h)=w(g,h)$ on $\operatorname{Dec}(A_v)$,
$$\sum_{v\in S}\operatorname{inv}_{A_v}([w_v])=0 .$$

*Proof.* Take $\operatorname{inv}$ from Lemma 10.22e. Fix $S$, $A$, $w$ and $(w_v)$. Lemma 10.22d produces $\mu$ and the class $[W]\in H^2(\operatorname{charRep}(\mu))$ of the descent of $w$. Lemma 10.22e gives $\sum_{v\in S}\operatorname{inv}_{A_v}(\operatorname{res}_v[W])=0$. It remains to identify $\operatorname{res}_v[W]$ with $[w_v]$ for each $v\in S$. Both are classes of cocycles on $\operatorname{Dec}(A_v)$ with the same action, and the cochains agree pointwise: $(\operatorname{res}_vW)(g,h)=W(\bar g,\bar h)=w(g,h)=w_v(g,h)$. The sum over the finite set $S$ is rewritten as a sum over the subtype $S$ to match the indexing of the nine-term sequence. $\square$ (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumInvEqZeroOfUnramifiedCocyclePow.lean:8–29`; the exported wrapper is `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumInvEqZeroOfUnramifiedCocyclePowStatement.lean:6–7`, and the $n=1$ predecessor with the same proof is `SumInvEqZeroOfUnramifiedCocycle.lean:22–43`.)

The theorem asks nothing of $w$ at the places in $S$. The invariance under $N_S$ is a condition only outside $S$, and it is what makes $w$ a cocycle of $G_S$. In Example 10.22a the cocycle $\chi\cup\delta b$ is invariant under $N_S$ because $\chi$ is unramified outside $\{(7)\}$, $b$ is a unit outside $\{(2+i)\}$, and $\mu_3$ is unramified outside $\{(3)\}$; the condition fails for the smaller set obtained by deleting $(7)$, and so does the conclusion.

##### Proposition 10.22g. The coefficient pairing produces an invariant cocycle with two surviving places [Lean, read]

Keep the hypotheses of Theorem 10.22(3) in §10.4.11: `Setup`, `Kills`, `IsDual`, the anti-invariant twist $\kappa$ trivial on the new decomposition group, $Q'=Q\cup\{p,p^c\}$, discrete $A$-modules $Y,Y'$ with a balanced $\beta:Y\times Y'\to\mathbb Z/N_0\mathbb Z$, a dual Selmer cocycle $y$ for $Q$ with values in $Y'^r$ and action $\kappa^{-1}\rho$, and a relaxed Selmer cocycle $x$ for $Q'$ with values in $Y^r$ and action $\kappa T_{\mathrm{gl}}$. Let $\langle\cdot,\cdot\rangle$ be the coordinate sum of $\beta$, and let $\pi,\pi'$ be the two actions. Define
$$w(g,h)=\langle x(g),\pi'(g)\,y(h)\rangle .$$
Let $S$ be the union of the places above $\ell$, the exceptional places $\operatorname{Spl}(i)$, and $Q'$, and let $A_v$ be the chosen prolongations, except that at $p^c$ the transported conjugate prolongation of $p$ is used. Then:

1. $w\in Z^2(\mu\mathrm{Rep})$ for $n=\nu+1$;
2. $w(gu,hu')=w(g,h)$ for all $u,u'\in N_S$;
3. for every $v\in S$ other than $p,p^c$, the local class $[w|_{\operatorname{Dec}(A_v)}]$ is zero;
4. hence, under `PoitouTateTotallyComplex`, $\operatorname{inv}_{A_p}([w|_p])+\operatorname{inv}_{A_{p^c}}([w|_{p^c}])=0$.

*Proof of (1).* The pairing is continuous since all modules are discrete, and $w$ is continuous because $x,y$ are continuous and $\pi'$ acts continuously, the latter being the first clause supplied by `pairing_equivariant_alt`. The cocycle identity for $w$ follows from the two cocycle identities and the equivariance $\langle\pi(g)a,\pi'(g)b\rangle=\omega_n(g)\langle a,b\rangle$, the third clause of the same supplier. Explicitly, $\omega_n(g)w(h,k)=\langle\pi(g)x(h),\pi'(gh)y(k)\rangle$, and expanding $x(gh)=x(g)+\pi(g)x(h)$ and $y(hk)=y(h)+\pi'(h)y(k)$ in $w(gh,k)$ and $w(g,hk)$ makes the four terms cancel. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ReciprocityRelaxedSelmerDualSelmerNewPlace.lean:22–31`.)

*Proof of (2).* Let $K_x$ be the set of $g$ with $x(g)=0$ and $\pi(g)=1$, and $K_y$ likewise for $y$ and $\pi'$. Each is a closed normal subgroup: closed by continuity, a subgroup by the cocycle identity, normal because $x(gng^{-1})=\pi(g)x(n)$ when $\pi(n)=1$ and $x(n)=0$. For $v\notin S$ and $\tau$ in the inertia at any prolongation of $v$, the fourth clause of `pairing_equivariant_alt` gives $\pi(\tau)=\pi'(\tau)=1$, and the Selmer conditions make $x$ and $y$ coboundaries on that inertia; with trivial action a coboundary is zero. Hence both inertia groups lie in $K_x\cap K_y$. Since $K_x\cap K_y$ is closed and normal, it contains $N_S$. For $u,u'\in N_S$ now compute $w(gu,hu')=\langle x(g)+\pi(g)x(u),\pi'(g)\pi'(u)(y(h)+\pi'(h)y(u'))\rangle=\langle x(g),\pi'(g)y(h)\rangle$. (A2, same file, :59–74 and :268–289; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CocycleUnramifiedOutsideVanishOnKernel.lean:41–85`.)

*Proof of (3).* At $v$ above $\ell$, the dual Selmer condition on $y$ says that cupping with every cocycle in the original local condition gives a coboundary, and $x$ restricted to $\operatorname{Dec}(A_v)$ satisfies that condition; this is the third clause of `DualSel` applied to the restriction of $x$. At $v\in\operatorname{Spl}(i)\cup Q$, the dual condition says $y|_{\operatorname{Dec}(A_v)}=\pi'(\cdot)m-m$ for some $m\in Y'^r$. Then $c(g)=-\langle x(g),\pi'(g)m\rangle$ is a continuous $1$-cochain on $\operatorname{Dec}(A_v)$ whose differential is $w$: using the cocycle identity for $x$ and the equivariance once more,
$$\omega_n(g)c(h)-c(gh)+c(g)=\langle x(g),\pi'(g)(\pi'(h)m-m)\rangle=\langle x(g),\pi'(g)y(h)\rangle .$$
(A2, same file, :82–95 and :290–311.) Note that $Q'\setminus Q=\{p,p^c\}$, so these two cases exhaust $S\setminus\{p,p^c\}$.

*Proof of (4).* Theorem 10.22f with $w_v=w|_{\operatorname{Dec}(A_v)}$, which is a cocycle for $\mu\mathrm{Loc}(A_v)$ by restriction, gives $\sum_{v\in S}\operatorname{inv}_{A_v}([w_v])=0$, and by (3) only the two terms at $p$ and $p^c$ survive. (A2, same file, :282–312.) $\square$

The identity of Theorem 10.22(3) is now the combination of (4) with the tame evaluations: `local_pair` writes the term at $p$ as $u\langle x(\gamma),y(\sigma)\rangle$ and the term at $p^c$ as $-u\langle x(\gamma^c),y(\sigma^c)\rangle$ for a unit $u$, using bijectivity of $\operatorname{inv}_{A_p}$ in the tame formula, conjugation compatibility with $\sigma(\zeta)=\zeta^{-1}$ at $p^c$, the vanishing of $y$ on both new inertia groups, and the triviality of both actions and of $\omega_n$ on the new decomposition groups. Cancelling $u$ gives the signed row. (A2, same file, :126–184 and :313–315.) The tame formula itself, `tame_cupProduct_invariant_unramified_hom`, and the equivariance supplier `pairing_equivariant_alt` are used as named inputs here and remain [Lean].

##### Remark 10.22h. Three different uses of global duality in §§10.4.10–10.4.12 [Expository]

All three subsections invoke `PoitouTateTotallyComplex`, but at different positions of the nine-term sequence and for different coefficient modules.

- §10.4.10 compares the orders of the original and dual Selmer groups. This is the Greenberg–Wiles ratio, obtained from the alternating orders along the whole sequence for the $r$-dimensional module $V(k)$, together with local duality and Euler characteristics. No individual local invariant is computed.
- §10.4.12 counts the obstruction to lifting a Selmer class across a simple coefficient extension. It uses the eighth position for $M=V(k)$, where the dual invariants $H^0(M^\vee)$ vanish by the commutator hypothesis, so that the degree-two localization is surjective onto the product at $S$, and the kernel $D_2$ of localization above $\ell$ enters the count.
- This subsection uses the eighth position for the one-dimensional $M=\operatorname{charRep}(\mu)$, where $H^0(M^\vee)=\mathbb Z/\ell^n\mathbb Z$ is as large as possible and the identity element is evaluated. Here the composite being zero is the only thing used, and it is a statement about one specific cocycle, the cup product of the two Selmer cocycles.

Classically, the third item is the reciprocity law for the Brauer group of a number field with no real places, and the first two are the finiteness and duality statements of Poitou–Tate; the nine-term sequence packages them together. The archive keeps the three uses apart in three different consumers, and the reading levels differ accordingly.

##### Source map and reading boundary

All archive references are to A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

[Lean, read] in this subsection: the producer `GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle_pow` (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumInvEqZeroOfUnramifiedCocyclePow.lean:8–29`), its exported wrapper (`SumInvEqZeroOfUnramifiedCocyclePowStatement.lean:6–7`), the descent lemma `exists_descend_pair_quotient` and the $n=1$ version (`SumInvEqZeroOfUnramifiedCocycle.lean:9–43`), the lift `exists_lift_cycMod`, the continuity `contAction_charRep`, the identity invariant `idInv`, the tail evaluation `NineTermExact.sum_eq_zero`, the local identification `toMuLoc_bijective` and the unpacking `PoitouTateTotallyComplex.annihilators` (`src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean:64–99,196–280,305–340`), and the whole consumer file `ReciprocityRelaxedSelmerDualSelmerNewPlace.lean:22–315`, namely `cupZ`, `locZ`, `conj_root`, `ine_le_of_normal`, `NS_le`, `loc_eq_zero`, `sq_eq_zero`, `local_pair` and `NewRecip.reciprocity`, together with `kerSub` and its normality and closedness (`CocycleUnramifiedOutsideVanishOnKernel.lean:41–85`).

[Lean], named inputs not read here: the proposition `PoitouTateTotallyComplex` itself (`PoitouTateNineTermTransgressionZeroApply.lean:288–301`) and whatever produces it on the main path; `tame_cupProduct_invariant_unramified_hom` (`TameCupProductInvariantUnramifiedHomStatement.lean:6`); `pairing_equivariant_alt` (`PairingEquivariantStatement.lean:6`); `twisted_representation_kills_small_subgroup`; the cup-product constructions `cup20`, `cupH1H1TwistedDual` and `cupProductH2H0` (`src/ReciprocityTheory/Hypotheses/GalCohDefs.lean:100–112`; `src/ReciprocityTheory/GaloisValuations/ContinuousConstSMulQuotient.lean:134`); and the unramifiedness of the cyclotomic character at places not above $\ell$, `cyc_eq_one_of_mem_Ine`. The examples are classical computations with the local Artin symbol and are [Expository]; the cohomological form of reciprocity they illustrate is Theorem 8.6.10 of Neukirch, Schmidt and Wingberg and Theorem I.4.10 of Milne, both cited in `sources/SOURCES.md`.

### 10.4.12 A square presentation of the global Selmer functor

#### Motivation

The local evaluations in §§10.4.8–10.4.11 give relations on global classes. To apply those relations to a determinant we first need a square matrix representing the global Selmer functor, with the same matrix used on every torsion coefficient module. The arithmetic estimate responsible for squareness bounds the obstruction to lifting a global class across an extension with simple kernel.

#### Example 10.23. A non-saturated condition [Expository]

Let $O$ be a DVR with uniformizer $p$. Model restriction by the identity on $Y$ and impose the condition $pY$. In the coefficient sequence
$$0\longrightarrow O/p\xrightarrow{1\mapsto p}O/p^2
  \xrightarrow{\mathrm{red}}O/p\longrightarrow 0,$$
the selected submodules are $0,pO/p^2,0$. The middle term has length one and maps to zero, yet the left term supplies no preimage of its generator. The class of $1$ fails the condition at the source and its image satisfies it. The integral condition $pO\subset O$ has quotient of length one, whereas saturating it gives $O$ with quotient of length zero. The same difference occurs modulo $p^2$. The failed reflection along the coefficient injection prevents any natural matrix-kernel representation of this functor.

#### Example 10.24. Flat extension and ramified lengths [Expository]

Take $O=k[[p]]$, $O'=k[[t]]$, and $p=t^2$. Separating even and odd terms gives $O'=O\oplus tO$, hence this extension is free. For
$$A=\begin{pmatrix}p&p\\0&p^2\end{pmatrix}$$
subtracting the first column from the second gives diagonal entries $p,p^2$. The cokernel is $O/p\oplus O/p^2$. On $(k((p))/O)^2$ the diagonal kernel is $p^{-1}O/O\oplus p^{-2}O/O$. Both lengths are three. Over $O'$ the diagonal entries are $t^2,t^4$. The cokernel is $O'/t^2\oplus O'/t^4$ and the kernel on $(k((t))/O')^2$ is $t^{-2}O'/O'\oplus t^{-4}O'/O'$. Both lengths are six, the valuation of $t^6$. Flatness preserves exactness, while the ramification index converts the lengths.

After the nonflat reduction $O\to k$, however, $A$ becomes zero and its kernel on $k^2$ is all of $k^2$. The kernel on $O^2$ was zero. The cokernel presentation survives by right exactness. This also explains the failure of injectivity after tensoring $0\to O\xrightarrow{p}O$ with $k$.

#### The global object and its coefficient modules

Fix $D,N,X,\mathrm{bkP}$ and then $i,s$ satisfying `GalHyp`. Fix $M\ge1$, a finite index set $\iota$, places $P$, characters $d$ satisfying `SlopeTestRemainingChoices` with empty forbidden set, and $Q$ satisfying `IsQ P Q`. Put $O=X.O0\,i$, $\Lambda=O[(\mathbb Z/\ell^M)^\iota]$, and let $\kappa=\mathrm{delInv}(i,M,d)$ be the inverse tautological character. For discrete coefficients $B$, set $V(B)=B^r$ with action $\kappa T_{\mathrm{gl}}(i,s)$. The functor $\mathcal S(B)$ is the submodule of continuous $H^1(G_E,V(B))$ satisfying all local conditions. Above $\ell$ the condition is `bkOn`. At the other places in $\mathrm{Spl}(i)\cup Q$ it is full, and elsewhere it is the kernel of restriction to inertia. Above $\ell$ the generators are classes of continuous cocycles with coordinates $c(g)_j b$ for $b\in B$ and integral crystalline coordinates $c$ transported to the chosen decomposition group. The scalar action in this formula comes from $O$. (A2, `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTameInertiaElementAtTwistPrime.lean:69–111`.)

The group ring is finite free over the complete DVR $O$. Its reduction is a truncated polynomial ring on the generator differences, each killed by its $\ell^M$th power. The reduction is local with nilpotent maximal ideal, so finiteness gives locality, and the maximal ideal powers and powers of $\ell$ are cofinal. It follows that $\Lambda$ is complete Noetherian local with finite residue field and that elementwise $\ell$-power torsion agrees with elementwise maximal-ideal-power torsion.

#### Lemma 10.25. The arithmetic inputs to the relation count

The interface of `oneMatrix_of_galoisCohomology` lists `Cheb`, `PoitouTateTotallyComplex`, `CohDimTwo`, `TameLocal`, `LocalFiniteness`, `LocalTateDuality`, `LocalEulerChar`, `GlobalFiniteness`, `GlobalEulerChar`, `UnramifiedOrthogonality` and `Gen.ArchimedeanSignatureMatching`. Its body discards Chebotarev, the tame input and unramified orthogonality. It obtains `Setup` from the auxiliary data, including the triviality of $\kappa$ above $\ell$ and the unramified action at the places with unramified conditions. The local saturation wrapper uses triviality above $\ell$. The local count uses the signature input. The obstruction calculation directly uses totally complex Poitou–Tate, local and global finiteness, and local and global Euler characteristics. The obstruction wrapper also takes `CohDimTwo`, local Tate duality and saturation as arguments. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerPresentationMatrixOfGaloisCohomology.lean:20–35`.)

Under these hypotheses the following properties hold.

1. Coefficient maps act on Selmer classes and $\mathcal S$ is left exact. Global $H^0$ vanishes on torsion coefficients, so the long exact sequence gives injectivity and exactness at global $H^1$. For a sequence exact at the middle term whose second map is arbitrary, factor the second map through its image and use vanishing of invariants on the remaining quotient to get injectivity on $H^1$ of the image. A global lift belongs to $\mathcal S$ by reflection along the coefficient injection. At crystalline places this is `LocSat`, at relaxed places membership is automatic, and at unramified places inertia acts trivially, so vanishing of the restricted class is vanishing of the cocycle on inertia.
2. Every element of $\mathcal S(B)$ comes from a finite coefficient submodule. A representative has finite image by compactness and discreteness. Its coordinates generate a submodule killed by a common power of the maximal ideal, finite because the residue field is finite. Matrix multiplication defines the action on its coordinate vectors. Reflection as in (1) shows that the resulting class satisfies the local conditions.
3. For every short exact sequence $0\to k\to B\to C\to0$ of torsion coefficients with $k$ the residue field, the quotient $\mathcal S(C)/\operatorname{im}\mathcal S(B)$ is finite with cardinality at most $|\mathcal S(k)|$, which is finite. Every simple coefficient module is isomorphic to $k$.

*Proof of (3).* Write $W=V(k)$ and $h=|W|^{r_2(E)}$, with $r_2(E)$ the number of complex places. Use the Galois group $G_{E,S}$ unramified outside the finite set of places above $\ell$ and the relaxed places. The actions factor through it. Selmer cocycles vanish on the inertia groups outside $S$ and descend to this quotient. Indeed they vanish on the conjugates of those inertia groups by the cocycle identity and inertia's trivial action, then on the closed normal subgroup they generate by continuity. Inside $S$ only the crystalline conditions constrain the classes. Use $H^j_v$ for cohomology at the chosen decomposition group and write
$$D_2=\ker\bigl(H^2(G_{E,S},W)\to\prod_{v\mid\ell}H^2_v(W)\bigr),\qquad
 C_1=\operatorname{coker}\bigl(H^1(G_{E,S},W)\to
       \prod_{v\mid\ell}H^1_v(W)/L_v(k)\bigr).$$
The commutator hypothesis on the residual representation eliminates invariants of the twisted dual: such a functional transforms by a scalar character and consequently kills every difference $ghw-hgw$. The last dual invariant term of the Poitou–Tate sequence therefore vanishes. Degree-two localization is surjective onto the product at $S$, hence onto the subproduct above $\ell$. [Milne, Arithmetic Duality Theorems, I.4.10](https://www.jmilne.org/math/Books/ADTnot.pdf#page=57)

The local and global finiteness inputs give finite groups for the count. Vanishing of global invariants and the global Euler formula give
$$|H^1(G_{E,S},W)|=|H^2(G_{E,S},W)|h.$$
The local Euler formulas and the sum of local degrees give
$$\prod_{v\mid\ell}|H^1_v(W)|
 =\prod_{v\mid\ell}|H^0_v(W)|\,\prod_{v\mid\ell}|H^2_v(W)|\,h^2.$$
Here $\sum_{v\mid\ell}[E_v:\mathbb Q_\ell]=2r_2(E)$. The signature-based `LocCount` supplies
$$\prod_{v\mid\ell}|L_v(k)|=\prod_{v\mid\ell}|H^0_v(W)|\,h,$$
with $|W|=|k|^r$ and $r_2(E)=D.R.f$. In the local count, if $d_v$ is the fraction-field dimension of crystalline $H^1$, the finite free lattice of integral crystalline cocycles has rank $r+d_v$ by vanishing of rational local invariants and the dimension of the coboundaries. Saturation injects its reduction into the space of residue-valued cochains: an integral combination vanishing pointwise modulo the uniformizer divides by the uniformizer in the lattice. Extending scalars between residue fields preserves linear independence of a finite list of cocycles, as can be checked by choosing finitely many coordinates that detect that list. Thus the corresponding cocycle span has order $|k|^{r+d_v}$. Its coboundaries have order $|k|^r/|H^0_v(W)|$ by the first isomorphism theorem. Dividing gives $|L_v(k)|=|H^0_v(W)||k|^{d_v}$. The signature calculation expresses $\sum_v d_v$ as a sum over $2D.R.f$ embeddings. The contributions at conjugate embeddings sum to $r$ by the filtration relation, giving $\sum_v d_v=D.R.f\,r$. This uses the crystalline dimension and embedding inputs of the archive. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalCountOfSetup.lean:30–85,195–314,447–516`.) Thus the first localization target, modulo the local conditions, has order $h\prod_{v\mid\ell}|H^2_v(W)|$. Taking orders of kernels and images and using surjectivity in degree two gives
$$|\mathcal S(k)|=|D_2|\,|C_1|.$$

A class $x\in\mathcal S(C)$ has connecting class in $D_2$. Above $\ell$ its allowed local classes lift across $B\to C$ by lifting the coefficient in each crystalline generator, so its local connecting classes vanish. Fix a representative $x_0$ of each nonempty fiber of the connecting map. For $x$ in that fiber choose a global lift $a_x$ of $x-x_0$. At each crystalline place choose an allowed local lift of the same difference. Subtract this from the restriction of $a_x$. The difference maps to zero over $C$ and hence comes from a residual local class $p_{x,v}$. Record the tuple of these classes modulo the image of global residual localization and the residual local conditions, that is, in $C_1$.

If $x,x'$ have equal records in both $D_2$ and $C_1$, then the difference of their residual tuples is the restriction of one global residual class modulo the local conditions. Subtract the image of that global residual class from $a_x-a_{x'}$. The corrected lift satisfies the crystalline conditions by functoriality of the local submodules and satisfies the other conditions by construction over $G_{E,S}$. It maps to $x-x'$. Choosing a representative of each coset now injects the obstruction quotient into $D_2\times C_1$. This proves (3). $\square$

The calculation follows A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerObstructionLeResidualSelmerSimpleExtension.lean:61–290,327–363,390–454,466–486,521–561`. The vanishing of the dual invariant term is used in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/H0TwDualEqZero.lean:13–81`.

The saturation used in (1) has a concrete proof. The integral crystalline lattice is the inverse image of a fraction-field vector subspace, hence dividing an integral cochain by a nonzero scalar preserves the condition whenever the result is integral. To reflect its coefficient span along an injection $B'\hookrightarrow B$, write the image of a cochain as a finite sum $\sum_i c_i b_i$. If $c_1\ne0$, choose a coordinate of $c_1$ of least valuation and divide $c_1$ by that coordinate to get a lattice element $d$ taking value $1$ there. Subtract $d$ times the value of the original $B'$-cochain at that coordinate. In the expression over $B$ this eliminates the first term and replaces each remaining $c_i$ by $c_i-c_i(g)_j d$, still in the lattice. Induction eliminates the finite list. Coboundaries are in the same span, since they are combinations of the columns of $T_{\mathrm{gl}}(g)-1$ at the places where $\kappa=1$. The reflected span therefore gives the claimed reflection on classes. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalConditionAboveLSaturatedOfSelmerSetup.lean:19–92,100–132,137–156,216–260`.)

#### Theorem 10.26. Conditional finite square presentation

Let $(\Lambda,\mathfrak m,k)$ be complete Noetherian local with finite residue field. Let $F$ be an additive $\Lambda$-linear functor from elementwise $\mathfrak m$-power torsion modules to $\Lambda$-modules. Assume (i) left exactness, (ii) every class comes from a finite coefficient submodule and (iii) the finite obstruction bound in Lemma 10.25(3) for every short exact sequence with simple kernel. Then a finitely generated module $H$ has a presentation
$$\Lambda^a\xrightarrow{\Phi^{\mathsf T}}\Lambda^a\longrightarrow H\longrightarrow0,\qquad
   \Phi_{ij}\in\mathfrak m,$$
with $F(B)\cong\operatorname{Hom}_\Lambda(H,B)=\ker(\Phi:B^a\to B^a)$ naturally for every torsion $B$.

*Proof.* Apply (iii) with $B=k$ and $C=0$ to get finiteness of $F(k)$. Put $a=\dim_k F(k)$. Fix $n\ge1$. Call $(D,x)$, with $D$ finite killed by $\mathfrak m^n$ and $x\in F(D)$, minimal if $F(f)x=0$ implies $f=0$ for maps from $D$ to torsion modules. Any pair has a minimal supporting submodule. Choose a submodule of least cardinality whose image under $F$ contains $x$, with a lift there. If a map from this submodule kills the lift, left exactness puts the lift on its kernel, so the kernel is the entire submodule. For a minimal pair, evaluation at $x$ injects $\operatorname{Hom}_\Lambda(D,k)$ into $F(k)$ by linearity and minimality. Thus $D$ has at most $a$ generators by Nakayama and $|D|\le|\Lambda/\mathfrak m^n|^a$. The quotient ring is finite since its successive maximal ideal quotients are finite dimensional over $k$.

Choose a maximal-cardinality minimal pair $(H_n,x_n)$, allowing the zero pair. If $B$ is finite killed by $\mathfrak m^n$ and $y\in F(B)$, choose a minimal support inside $H_n\oplus B$ for $(x_n,y)$ via additivity. The support projects onto $H_n$: the quotient by its image kills $x_n$ under $F$, and minimality forces the quotient map to vanish. Maximality of $|H_n|$ makes the projection an isomorphism. Composing its inverse with the other projection gives a map to $B$ evaluating to $y$. Uniqueness follows from minimality. This gives a linear natural representation at level $n$.

The map $H_{n+1}\to H_n$ sending the universal element to $x_n$ induces $H_{n+1}/\mathfrak m^n H_{n+1}\cong H_n$. Both sides represent the same finite-level functor, and evaluating at their universal elements gives mutually inverse maps. In particular $H_1\cong k^a$. Lift a basis compatibly and use Nakayama to obtain compatible surjections $P=\Lambda^a\to H_n$. Their kernels $R_n$ contain $\mathfrak m^nP$ and satisfy $R_n=R_{n+1}+\mathfrak m^nP$. Put $R=\bigcap_n R_n$. Starting with $v\in R_n$, choose successive $v_j\in R_j$ with $v_n=v$ and $v_{j+1}-v_j\in\mathfrak m^jP$. The limit exists by completeness and lies in each $R_j$, which is closed since it contains $\mathfrak m^jP$. Hence $R_n=R+\mathfrak m^nP$. Set $H=P/R$, with $R\subseteq\mathfrak mP$.

A map $H\to B$ into a torsion module has finite image killed by some $\mathfrak m^n$, and yields an element of $F(B)$ by evaluating $x_n$ via the induced map from $H_n$. This is independent of $n$ by compatibility, and is linear and natural. It is injective by testing differences at a common level using minimality, and surjective by finite coefficient support and finite-level representation.

To count relations, take $j$ with $R\cap\mathfrak m^jP\subseteq\mathfrak m R$ by Artin–Rees. Every $\lambda:R\to k$ therefore factors through the image of $R$ in $P/\mathfrak m^jP$. Embed $k$ in an injective module $J$ and let $I=J[\mathfrak m^\infty]$. Injectivity extends the composite functional to $P/\mathfrak m^jP\to J$, with image in $I$ since $\mathfrak m^j$ kills the source. Write $u_\lambda:P\to I$ for the resulting map. For $q:I\to I/k$, the composite $q u_\lambda$ kills $R$ and induces $H\to I/k$. Its class in $F(I/k)/\operatorname{im} F(I)$ is independent of the extension, because two choices differ by a map vanishing on $R$. If the classes for $\lambda$ and $\mu$ coincide, subtract from $u_\lambda-u_\mu$ the map through $H$ furnished by the equality. The remainder takes values in $k$. Every map $P\to k$ kills $R\subseteq\mathfrak mP$, hence $\lambda=\mu$. By (iii),
$$|\operatorname{Hom}_\Lambda(R,k)|\le |F(k)|=|k|^a.$$
The relation module is finitely generated by Noetherianity, so Nakayama gives at most $a$ generators. Pad to $a$ rows with zeros, including the empty case. With those rows as $\Phi$, maps $H\to B$ are exactly solutions of the row equations. $\square$

This follows the construction in A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LeftExactFunctorRepresentableTorsionModules.lean:21–151`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionLeftExactFunctorKernelSquareMatrix.lean:110–458` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTorsionModuleExtendingResidueMaps.lean:35–82`. Artin–Rees is used only for the displayed containment. [Stacks Project, Algebra §10.51](https://stacks.math.columbia.edu/tag/00IN)

For $F=\mathcal S$ the theorem supplies `ThmS`. The choice of $a,\Phi$ follows $i,s,M,\iota,P,d,Q$ and precedes every $B,B'$ and coefficient map in `Computes`. Its naturality applies to coefficient maps on cocycle representatives modulo coboundaries. Conversely, the representation on finite levels determines the compatible reductions of $H$, hence $H$ up to unique isomorphism compatible with the representation, by completeness of finite modules. Its zeroth Fitting ideal is therefore independent of the presentation. Squareness permits zero rows and does not assert injectivity of $\Phi^{\mathsf T}$. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerTheoremOfLocalComponents.lean:204–228,286–300`.)

#### Lemma 10.27. Scalar transport on the same coefficient module

Let $\phi:A\to A'$ be an $O$-algebra map and let $\kappa'=\phi\kappa$. Let $Y$ be a discrete $A'$-module, with $A$-action through $\phi$. For every $Q$ and every function $f:G_E\to Y^r$, membership in `SelC` is equivalent for the two scalar actions.

*Proof.* The action formulas agree term by term in $\kappa T_{\mathrm{gl}}$, since both the character and each matrix entry act through the prescribed scalar maps. Thus continuity, the cocycle equation and the set of coboundaries agree. The identity on representatives gives a bijective semilinear map on $H^1$ commuting with restrictions. Full and unramified local conditions are preserved and reflected. Above $\ell$ each generating cocycle has the same integral crystalline data and the same coefficient $b$; its underlying function is identical on both sides. The forward map carries the $A$-span into the $A'$-span. For the reverse, an $A'$-multiple $a' c(g)_j b$ can be represented in the source by taking the coefficient $a'b\in Y$. By addition every element of the target span has a preimage in the source span. Bijectivity gives reflection and hence the equivalence on global classes and cocycle representatives. $\square$

[Lean, read] A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerCocyclesScalarChangeTransfer.lean:20–190` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelmerCocyclesScalarChangeTransferStatement.lean:6–7`. There is no flatness hypothesis. For tensor extension of modules, right exactness presents $H\otimes_A A'$ by $\phi(\Phi)^{\mathsf T}$. If $A'$ is flat, tensoring also preserves a matrix kernel, by exactness at the source of the matrix map. Comparing a tensor-defined cohomology theory would require a separate comparison of its local conditions. [Stacks Project, Algebra §10.39](https://stacks.math.columbia.edu/tag/00H9)

#### Determinant lengths and the Step/Grow consumers

For a specialization to a DVR $O'$ with fraction field $K'$ put $A'=\phi(\Phi)$. Smith reduction by invertible matrices diagonalizes it, permitting zero diagonal entries. An entry of valuation $b$ gives $O'/\pi^b$ in the cokernel and $\pi^{-b}O'/O'$ in the kernel on the fraction field quotient, each of length $b$ by the uniformizer filtration. A zero entry gives $O'$ and $K'/O'$ respectively, both of infinite length. Transposition preserves the diagonal invariants. Hence
$$\operatorname{len}_{O'}\ker(A':(K'/O')^a\to(K'/O')^a)
 =\operatorname{len}_{O'}\operatorname{coker}((A')^{\mathsf T})
 =v_{O'}(\det A'),$$
where $v_{O'}(0)=\infty$. In the archive `lamChar` specializes to `X.Ok i k` and sends $\kappa$ to $\psi^{-1}$. Naturality for multiplication by every receiving DVR scalar makes the specialized isomorphism linear over that DVR. The actual proof compares the local crystalline conditions by the two generator inclusions and uses triviality of $\psi$ above $\ell$. It then divides both sides by $v_{O'}(\ell)$ in `SelPoly`. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedSelmerLengthsEqDeterminantValuation.lean:329–385`.)

In Step the receiving algebra satisfies `Kills`, which forces all its modules to be $\ell$-power torsion. Take as coefficient module the row cokernel of the specialized matrix. Its basis classes form a universal solution of the row equations. Applying `Computes` gives a global Selmer class there. Choose a representative and lift its coordinates to rows over the receiving algebra. Every solution in any discrete receiving module is obtained from the universal solution by a unique evaluation map. Naturality identifies evaluation of the lifted rows with the associated global class. The zero test and surjectivity concern classes modulo coboundaries. Lemma 10.27 transports this identification and any further specialized universal pair, even into the nonflat nilpotent rings used in the signed determinant argument of §10.4.11. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniversalSelmerCocycleBaseChange.lean:18–110` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UniversalSelmerCocycleMapAlgHom.lean:10–23`.)

`AntiOfKer.step` feeds the supplier of `ThmS` to Grow. For each allowable new $Q'$, Grow chooses the matching old $Q$ and invokes `ThmS` there. It compares with **any** supplied `Computes` presentation at $Q'$. The tame relation uses the local group construction `TameQuotient_holds` with its valuation and tame-generator inputs. The local row comparisons then propagate the determinant and adjugate bounds. At each permitted signature and $Q$, the auxiliary-prime theorem picks a presentation, lifts its determinant to a polynomial, and applies the order bound and `SelmerLengthsByDeterminant` to the very same lift. Evaluating that polynomial at a good character bounds the length of the global Selmer group. (A2, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntiOfKer.lean:105,153–166,193–194,299`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevInductionGrowBoundOfPresentation.lean:462–502`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisTwistedSelmerAuxprimesOfMatrixAndBounds.lean:47–63` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistAllPowersOfGaloisCohomologyClassField.lean:20–30`.)

#### Reading boundary

A2 has joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The square-matrix assembly, scalar transport and the indicated segments of the consumer proofs are [Lean, read]. The hand proofs and examples explain the conditional implications. `PoitouTateTotallyComplex`, `GlobalFiniteness`, `LocalFiniteness`, `GlobalEulerChar`, `LocalEulerChar`, `ArchimedeanSignatureMatching` and the underlying residual and crystalline inputs remain separately supplied [Lean]. Degree-two localization in the obstruction count is a different use of global duality from the global sum of cup invariants in §10.4.11.1 and the dual Selmer order formula in §10.4.10; see Remark 10.22h.

---

### 10.4.13 Choosing the auxiliary primes in a common Galois quotient

#### Motivation

The two order bounds in §10.4.8 start with left and right places. A left Frobenius must resemble the designated tame element $z$. A right Frobenius with index $a$ must resemble the preselected element $h_a$ and have left-character coordinates equal to the $a$-th basis vector. The construction uses left inertia to make these requirements compatible before asking Chebotarev for a right prime.

#### Example 10.28. Splitting and inertia in a quadratic field [Expository]

In $\mathbb Q(i)$ the ring of integers is $\mathbb Z[i]$. Exclude $2$ and, for illustration, $3$. At $5$, $X^2+1=(X-2)(X+2)$ in $\mathbb F_5[X]$. The two primes have norm $5$, and Frobenius is the identity since $i^5=i$. At $7$ the squares are $0,1,2,4$, so the polynomial is irreducible. Its single prime has norm $49$, and Frobenius over the rational prime acts by $i\mapsto i^7=-i$. Both target classes in the group of order two are singletons. If the base field is instead $\mathbb Q(i)$, the prime over $7$ fails the requirement of degree one over $\mathbb Q$. The degree-one condition in the selector concerns the **base** prime, independently of its splitting in the extension defining the quotient.

#### Example 10.29. A nonabelian quotient and its evaluation [Expository]

Let $L$ be the splitting field of $X^3-2$ over $\mathbb Q$. Eisenstein at $2$ gives an irreducible cubic. The real root generates a real cubic field, and adjoining a primitive cube root of unity doubles the degree. The faithful permutation action on the roots therefore identifies the group with $S_3$. The discriminant is $-108$. At $5$ and $7$ the reductions of the three roots are distinct, so inertia, which fixes each reduced root, fixes every root. Frobenius permutes the reduced roots in cycles of lengths equal to the irreducible factor degrees, since a root of degree $d$ has orbit of length $d$ under residue Frobenius.

At $5$ the factorization is $(X-3)(X^2+3X+4)$. The quadratic discriminant is $3$ modulo $5$, outside the squares $0,1,4$. Frobenius is a transposition. At $7$ the cubes are $0,1,-1$, so the cubic is irreducible and Frobenius is a three-cycle. Sign gives $-1$ and $+1$ respectively. It detects the quadratic subfield $\mathbb Q(\sqrt{-3})$, because a transposition negates the product of the root differences whose square is $-108$. The request “transposition and sign $+1$” has no representative in this common quotient.

For a vector-valued example let $r=(123)$, $s=(12)$ and let the group act on $\mathbb F_3$ by the sign. Every element is $r^a s^b$, uniquely with exponents modulo $3$ and $2$. The relation $srs^{-1}=r^{-1}$ gives the multiplication rule $(a,b)(c,d)=(a+(-1)^b c,b+d)$. Hence $f(r^a s^b)=a$ is a cocycle. At $7$, the representatives $r,r^{-1}$ give values $1,-1$ and conjugation by $s$ exchanges them. Nonvanishing survives the change of representative, while the value transforms by the action.

#### Definitions and the degree-one selection lemma

Let $E$ be the number field of the host, $G=\operatorname{Gal}(\overline E/E)$, and $O(v)=\{v,\bar v\}$ the orbit under the host involution. This is the archive's `Over` relation. It concerns primes of $E$. At a prolongation $B$ of $v$ to $\overline E$ write $D_B,I_B$ for decomposition and inertia. An arithmetic Frobenius lift acts on the residue field by $x\mapsto x^{Nv}$, where $Nv$ is the absolute norm. Changing this prolongation is a separate operation from replacing $v$ by $\bar v$.

**Lemma 10.30 (selection and transport).** Assume qualitative Chebotarev density for finite Galois extensions of number fields. Given an open normal subgroup $V\subseteq G$, a target $g\in G$ and a finite set $T$ of primes of $E$, there exists a prime $v$ such that every member of $O(v)$ avoids $T$ and has residue degree and ramification index one over $\mathbb Q$. At every prolongation $B$ of $v$, $I_B\subseteq V$, and every Frobenius lift $\sigma$ at $B$ satisfies $k\sigma k^{-1}g^{-1}\in V$ for some $k\in G$. For a finite list of targets in the same quotient the orbits of the chosen primes can be taken pairwise disjoint.

**Proof.** Saturate $T$ under the involution and exclude the finitely many primes ramified over $\mathbb Q$. Apply Chebotarev in $\overline E^V/E$ to the class of $gV$. If $s>1$, primes of residue degree at least two contribute at most $[E:\mathbb Q]\sum_p p^{-2s}$ to the Dirichlet sum, since each lies over a rational prime $p$ and has norm at least $p^2$. This bound stays finite as $s\downarrow1$. The discarded primes, including the finite exclusions, contribute density zero. The remaining set has positive density and is infinite. The involution preserves residue fields up to isomorphism and preserves absolute ramification indices.

At the chosen $v$ inertia is trivial in $G/V$. The Galois action on prolongations is transitive, and changing a prolongation conjugates the Frobenius because the induced residue-field isomorphism commutes with the $Nv$-power map. We can thus take a prolongation $B_0$ where the image of a lift $\sigma_0$ is exactly $gV$. At any other prolongation $B=t B_0$, $t^{-1}\sigma t$ is a lift at $B_0$, so $\sigma_0^{-1}t^{-1}\sigma t\in I_{B_0}\subseteq V$. In the quotient this says $t^{-1}\sigma tV=gV$. For a list, fix its targets first and add the earlier choices to $T$ at each selection. Saturation excludes the whole orbit of each earlier choice. The empty list gives the empty family. $\square$

The archive assumes the degree-one existence input `Cheb` with a witness at some prolongation. Its own supplier is traced in §10.4.7. The transport and finite-list proof are `exists_pick` and `exists_picks`. The density deduction here explains why the degree-one requirement is compatible with the class. [Sutherland, Lecture 28, §28.5, Theorem 28.9](https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf)

#### Theorem 10.31. The two batches of StepAB [Lean, read]

Fix a prime $\ell$, an integer $M\ge1$, $m=2\ell^M$, and the additive group $C=\mathbb Z/\ell^M\mathbb Z$. Write $J$ for the subgroup fixing all $m$-th roots of unity. Fix open normal subgroups $H,U\subseteq G$, finite sets of primes $A,S,S_0$, and characters $d_P:G\to C$ indexed by the primes $P$. Use the host splitting test that a split prime has $P\ne\bar P$ over the fixed field of the involution. Primes of absolute degree one outside a finite set $A_0$ pass this test.

Assume the following admissibility condition. Whenever $P$ is split, $P\notin S$, and $D_B\subseteq H$ at the fixed prolongation of $P$, the character $d_P$ has open kernel, is anticyclotomic and trivial on the decomposition groups above $\ell$, is trivial on inertia away from $O(P)$, and maps inertia onto $C$ at every prolongation over $O(P)$. Anticyclotomic means the involution negates the character. Fix $z\in H$ lying in inertia at a designated twist prime away from $m$. Finally fix $R\ge0$ and $h_a\in H\cap J$ for $0\le a<R$. Assume the degree-one selection input of Lemma 10.30.

There exist left primes $P_b$ and right primes $Q_a$ for $0\le a,b<R$, with all $2R$ orbits pairwise disjoint. Every member $v$ of an orbit is split, has absolute residue degree and ramification index one, avoids $A\cup S\cup S_0$, satisfies $Nv\equiv1\pmod m$, and has inertia in $U$ at every prolongation. The characters are good at the selected primes, meaning they satisfy all five character conditions above. At the fixed prolongations, every left lift is conjugate to $z$ modulo $U$, every right lift $\tau$ at $Q_a$ satisfies $d_{P_b}(\tau)=\delta_{ab}$, and at each $Q_a$ there is a Frobenius lift conjugate to $h_a$ modulo $U$.

**Proof.** Reduction away from $m$ is injective on $\mu_m$, the group of $m$-th roots of unity. In fact, if a root $\zeta\ne1$ reduces to $1$, reducing $1+\zeta+\cdots+\zeta^{m-1}=0$ gives $m=0$ in the residue field. Apply this to the quotient of any two roots with equal reduction. Consequently inertia away from $m$ fixes $\mu_m$ and arithmetic Frobenius acts on it by the $Nv$-power map. Thus $z\in J$. The designated primes in the archive lie over rational primes distinct from $2$ and $\ell$. Since $\mu_m$ generates a finite Galois extension, $J$ is open normal.

Before choosing any prime put $W=U\cap H\cap J$ and fix
$$
T=A\cup S\cup S_0\cup A_0\cup
\{v:e(v/\mathbb Q)\ne1\}\cup
\operatorname{Ram}(\overline E^U/E)\cup
\operatorname{Ram}(\overline E^H/E)\cup\{v:v\mid m\}.
$$
Both fixed fields are finite extensions, so their relative ramification sets are finite. Away from $T$, inertia belongs to $W$ by the two relative ramification exclusions and the root calculation. For the finite splitting exception, take an integral $b$ with $\bar b-b\ne0$, for example the archive's $b=\sqrt{-d}$. If the involution fixes a degree-one prime, it acts trivially on its prime residue field $\mathbb F_p$, so the prime divides $\bar b-b$. This happens at only finitely many primes.

In either batch, if the quotient kernel lies in $H\cap J$ and the target belongs to $H\cap J$, every lift at the fixed prolongation belongs to $H\cap J$. Indeed the congruence puts its conjugate inside this subgroup, which is normal. A primitive $m$-th root then gives $m\mid Nv-1$. The conjugate prime has the same norm. Also, $D_B$ is topologically generated by its inertia and one Frobenius lift, since the quotient is procyclic with the residue Frobenius as a topological generator. As $H$ is closed, $D_B\subseteq H$. Together with splitting and avoidance of $S$, this gives the good character. This argument applies whenever the prime has degree one and its orbit avoids $T$.

Choose the $R$ left primes with target the class of $zW$ in $G/W$ and exclusion $T$, enlarged by earlier choices. Then set $d_b=d_{P_b}$. On inertia of $P_b$ the character $d_b$ is surjective, while each $d_j$ with $j\ne b$ vanishes because the orbits are disjoint. These inertia groups lie in $W$. Consequently $W\to C^R$, $w\mapsto(d_b(w))_b$, is onto. Given a vector, choose for each coordinate an element of that left inertia attaining its value. Their product lies in $W$ and has the requested vector by additivity. This proves the coordinate correction used by `exists_values`.

For each $a$ choose $\epsilon_a\in W$ with $d_b(\epsilon_a)=\delta_{ab}-d_b(h_a)$ and put $\gamma_a=h_a\epsilon_a$. Then $\gamma_a\in H\cap J$, $\gamma_a U=h_a U$, and $d_b(\gamma_a)=\delta_{ab}$. Now, before any right choice, fix
$$
V_2=W\cap\bigcap_{b<R}\ker d_b,\qquad T_2=T\cup\{P_b:0\le b<R\}.
$$
The intersection is open normal because each kernel is open normal and the list is finite. Choose right primes in $G/V_2$ with targets the classes of $\gamma_a V_2$, excluding $T_2$ and the earlier right choices. Saturation enforces disjointness across the two batches. The common prime and character conditions follow from the preceding implication.

Every right lift $\tau$ satisfies $k\tau k^{-1}\gamma_a^{-1}\in V_2$ for some $k$. Applying $d_b$ gives $0=d_b(\tau)-d_b(\gamma_a)$ since an abelian character is constant on conjugacy classes. Also
$$
k\tau k^{-1}h_a^{-1}
=(k\tau k^{-1}\gamma_a^{-1})(h_a\epsilon_a h_a^{-1})\in U
$$
by $V_2\subseteq U$ and normality of $U$. Any lift at the fixed prolongation provides the existential witness. On the left, $W\subseteq U$ gives the required congruence for every lift. These are the auxiliary-place, `Steps`, inertia and right Frobenius fields of `StepAB`. $\square$

The right quotient depends on the chosen left places. In each call the quotient, target and finite exclusions precede the prime. Each right call uses a single compatible class in one quotient. The coordinate correction proves that the requested left-character values and the original congruence modulo $U$ have a common lift. The nonabelian example shows why independently chosen values on quotient projections can be incompatible. For the same reason, a norm congruence and a Frobenius class imposed separately must agree on the intersection of their fields.

#### Lemma 10.32. The conjugacy test for Selmer evaluations [Lean, read]

Let $L_*$ be open normal in $G$ and stable under the automorphism $\iota$ of $G$ induced by complex conjugation. Suppose $x,y$ are continuous cocycles in discrete modules for a representation $R$ on a finite free module over a commutative ring $\Lambda$ and its dual twisted by a unit character $\chi$. Suppose both actions are trivial on $L_*$ and $\chi\circ\iota=\chi$. Using the evaluation pairing, put
$$
\mathcal B(g)=\langle x(g),y(g)\rangle-\langle x(\iota g),y(\iota g)\rangle.
$$
There is an open normal subgroup $U_*\subseteq L_*$ such that for $h\in L_*$ and $k\sigma k^{-1}h^{-1}\in U_*$,
$$
\mathcal B(\sigma)=\chi(k^{-1})\mathcal B(h).
$$
Thus nonvanishing gives a conjugacy-invariant test in $G/U_*$. If $I_B\subseteq U_*$, both cocycles give unramified local classes at $B$. At such a prime with $\sigma\in L_*$ the test evaluates the local classes on Frobenius, with both conjugate evaluations included.

**Proof.** For either cocycle $f$ with action $\rho$, $f(1)=0$, and on $L_*$ its restriction is an additive homomorphism. For $g\in L_*$ the cocycle law gives
$$
f(kgk^{-1})=f(k)+\rho(k)f(g)+\rho(kg)f(k^{-1})=\rho(k)f(g),
$$
since $\rho(kg)=\rho(k)$ and $f(kk^{-1})=0$. Its kernel in $L_*$ is therefore normal in $G$. It is open by continuity and discreteness. Intersect the two kernels and their inverse images under $\iota$ to obtain $U_*$. If $k\sigma k^{-1}=uh$ with $u\in U_*$, then $\sigma\in L_*$ by normality and $f(uh)=f(h)$ since $f(u)=0$ and $\rho(u)=1$. Thus $f(\sigma)=\rho(k^{-1})f(h)$. Apply this also to $\iota(\sigma),\iota(h),\iota(k)$.

In dual bases the action matrices are $R(k)$ and $\chi(k)R(k)^{-\mathsf T}$. The pairing therefore scales by $\chi(k)$, with reciprocal twists $\kappa,\kappa^{-1}$ cancelling in the archive's application. Both terms in $\mathcal B$ acquire the same multiplier because $\chi\circ\iota=\chi$. A unit preserves nonvanishing over any coefficient ring. When $I_B\subseteq U_*$, the actions and the cocycles are trivial on inertia, so the restrictions descend to $D_B/I_B$. This also holds at the conjugate prolongation by $\iota$-stability. Changing a lift by an inertia factor preserves the value. A coboundary at $g$ is $\rho(g)v-v$, which vanishes on $\sigma$ and $\iota(\sigma)$ because both lie in $L_*$. $\square$

For a general unramified cocycle the value on Frobenius is interpreted modulo the image of $\rho(\sigma)-1$, precisely the ambiguity from changing representative by a coboundary. Here that image is zero. Transport to another prolongation can still change vector coordinates, as in the $S_3$ example. Chebotarev can realize a representative by allowing the prolongation to be chosen along with the prime. At a fixed prolongation it supplies the conjugacy test, and one cannot prescribe arbitrary non-conjugacy-invariant coordinates of the local evaluation this way.

#### The actual Step and Grow interfaces

In the residual branch, `ChooseH` supplies $h_a$ in a small normal subgroup $L$ and an open congruence subgroup inside $L$. The call to `StepAB` intersects that subgroup with the caller's subgroup. Therefore both the chosen right Frobenius and its inertia lie in $L$, which puts its decomposition group in $L$ for `Position`. The chosen Frobenius and its host conjugate enter the `ChooseH` test giving `Corank` at zero. In positive order, `thmC_of_parts` appends one identity target per signature, selects both batches, then keeps all left places and only the initial right places. The restricted character matrix and the decomposition test supply `PiLocalization₂`. The retained right Frobenius witnesses give `Corank` at one. `Start` uses these inputs for the initial adjugate test before the induction of §10.4.9.

For a subsequent induction step, `AntiOfKer` receives a subgroup witness $h\in L_*$ with $\mathcal B(h)\ne0$ from the universal and dual Selmer cocycles. The first-half inertia vanishing places every unused left inertia inside $U_*$ of Lemma 10.32. The old, used coordinates already vanish on $h$. The one-place selector corrects $h$ on the left by a product in $U_*$ from the unused inertias, setting the next left coordinate to $1$ and the other unused coordinates to $0$. The used coordinates stay zero by off-orbit triviality. It fixes the corrected class modulo $U_*\cap\bigcap_b\ker d_{P_b}$ and the exclusion of old orbits and finite arithmetic exceptions before calling `exists_pick`. At the new prime, inertia lies in $U_*$ and all old left characters vanish there. Its own character is onto on inertia, giving one inertia element with coordinate $1$ and another that cancels its own character on the Frobenius lift. Multiplication by the second inertia element preserves the Frobenius residue action, all old left coordinates and the congruence to $h$ modulo $U_*$. Write $\eta$ for the first correction. If $k\sigma k^{-1}(\eta h)^{-1}\in U_*$ and $\tau$ is the correcting inertia element, then $k(\sigma\tau)k^{-1}h^{-1}$ is the product of $(k\sigma)\tau(k\sigma)^{-1}$, the old congruence discrepancy, and $\eta$. All three belong to $U_*$. Lemma 10.32 transports the nonvanishing to this adjusted lift, which enters the new local row argument.

`Step` returns `Ext P P'`, the enlarged `PiLocalization₂` and the new determinant test. `Grow` takes the extension and its localization data as inputs. For each presentation at the new places it chooses a compatible old place set and presentation and transfers the prior coefficient and adjugate bounds. The single-prime call in `Step` shares the general selection helper with the initial two-batch call. See §§10.4.9–10.4.12 for the determinant, local relations and square presentation.

#### Source map and reading boundary

Archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Paths are relative to the extracted `lean/` root.

- **R3, conditional production bodies.** Root fixing, norm and decomposition tests, finite exclusions, list and character constructions, `exists_pick` and `stepAB`. `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAuxiliaryPrimesPrescribedFrobenius.lean:26–138,142–191,195–246,250–272,274–418`. The split-prime exception is `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DenseFrobeniusSplitPlaces.lean:12–73`.
- **R3, evaluation and one-place production, also mapped in §10.4.10.** `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsOpenNormalSubgroupTwoCocycles.lean:16–91` and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNewPlaceFrobeniusConjugateModOpenNormalSub.lean:12–126`.
- **[Lean], statements.** `GoodChar`, `AdmFam`, `SlopeTestRemainingChoices` and `Steps` in `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTameInertiaElementAtTwistPrime.lean:13–42`. `StepAB` and `ChooseH` in `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsDualDualRep.lean:118–124,142–146`. `Cheb` in `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:11–14`.
- **[Lean], consumer slices.** `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualBoundOfComponents.lean:29–57`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValLeOfNotMem.lean:110–137`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AntiOfKer.lean:221–260`, and `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevInductionGrowBoundOfPresentation.lean:462–482`.
- **Named inputs.** The degree-one supplier retains its reading scope in §10.4.7. The deeper inputs are §10.4.7’s cyclotomic irreducibility (`exists_prime_dvd_sub_one_cyclotomic_irreducible_over`), crossing-field construction (`exists_cyclotomic_crossing_field_deciding_frobenius`), prime norm existence (`exists_prime_absNorm_eq_of_irreducible_cyclotomic'`) and restriction of Frobenius (`isFrob_restrictScalars_of_prime_absNorm'`), called at lines 22–40 of `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean`. Valuation transport uses `exists_smul_eq_of_isPlaceOver` and `inv_mul_mem_Ine_of_isFrob` in `src/ReciprocityTheory/GaloisValuations/Global.lean:340,239` and `isFrob_smul` in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsPlaceOverMoveValCc.lean:148`. The decomposition test uses `closure_frob_sup_Ine` in `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ExistsCoprimePowOfMemIneKer.lean:188`. The finite-ramification and degree/norm suppliers are `finite_ramified` in `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinitePlacesInertiaNotFixingFiniteExtension.lean:62` and `absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified` in `src/Development/AbelianVarietyTheory/Proofs/FoundationProofs/AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified.lean:8`. The construction of `AdmFam`, the joint `ChooseH` test, small-subgroup actions, first-half inertia vanishing, reciprocity and Poitou–Tate remain inputs with the reading boundaries of the preceding subsections.

Positive density gives existence with the stated finite exclusions. A bound on the least eligible norm would need an effective Chebotarev estimate for these extensions and quantitative control of the exclusions. The argument makes no bounded-norm claim.

### 10.4.14 A compatible Tate generator for torsion coefficients

The finite-coefficient descent used in the residual Bloch–Kato pairing compares a cocycle and a primitive at one common bounded level. Here the object is a single representative that can be evaluated on coefficients of any $\ell$-power order. Two generators chosen separately can differ by a unit in cohomology and by a coboundary as functions. The construction corrects these two differences at each step. It then gives the local top-degree isomorphism used by the period-data interface. [A2, CobOfGen.lean:68–108; H2EquivOfTorsionCharacter.lean:159–305,464–504]

For a preview, put $\ell=3$ and suppose a generator modulo $9$ reduces modulo $3$ to $2C+\delta B$, where $C$ is the chosen lower generator. Multiplying by $2$ matches the class of $C$ because $2\cdot2\equiv1\pmod3$. Subtracting $\delta(2B)$ matches the function $C$. Both operations can be performed upstairs. The first hand calculation below gives this discrepancy on an actual Galois group.

#### Cochains and the finite input [Lean, read]

Let $\ell$ be prime, $R=\mathbb Z_\ell$ and $R_r=R/\ell^rR$. Let $G$ be a group with a topology and continuous multiplication, and let $\chi:G\to R^\times$ be a homomorphism whose values are continuous as an $R$-valued function. For an $R$-module $T$ use the scalar action $g\cdot t=\chi(g)t$. In cochains with torsion coefficients the coefficient set is discrete. Write
$$
\begin{aligned}
(\delta b)(g,h)&=\chi(g)b(h)-b(gh)+b(g),\\
(d_2z)(g,h,k)&=\chi(g)z(h,k)-z(gh,k)+z(g,hk)-z(g,h).
\end{aligned}
$$
A 2-cocycle is a locally constant function on $G\times G$ with $d_2z=0$. The group $H^2$ is the quotient of these cocycles by the differentials of locally constant 1-cochains. For $\ell^r T=0$, $\delta b$ is locally constant because $\chi$ acts through the locally constant reduction $\chi_r$ and multiplication in $G$ is continuous. Expanding $d_2\delta b$ cancels all terms, using $\chi(g)\chi(h)=\chi(gh)$. For a pointwise $\ell$-primary torsion $T$, the action on discrete $T$ is continuous: near $(g,t)$ keep $t$ fixed and take a neighbourhood of $g$ on which $\chi$ has constant residue modulo a power killing $t$. The same argument applied to the three terms of $\delta b$ gives local constancy in this case. These are the cochains of $\mathrm{H2}(\pi,\top)$ in the archive when $\pi$ is the scalar representation. [A2, H2EquivOfTorsionCharacter.lean:70–115; ContinuousFixingSubgroupEquiv.lean:169–186; AdRep.lean:10–49]

For a function $C:G\times G\to R$, the condition $\operatorname{Gen}(\chi,r,C)$ consists of three clauses for **every finite** $R$-module $T$ killed by $\ell^r$.

1. For every $x\in T$, $Cx$ is a 2-cocycle, where $(Cx)(g,h)=C(g,h)x$.
2. Every 2-cocycle $z$ in $T$ has the form $z=Cx+\delta b$ for some $x\in T$ and a locally constant $b:G\to T$.
3. If $Cx=\delta b$ for a locally constant $b$, then $x=0$.

Thus one function supplies all finite modules of the given exponent. The arithmetic input for the construction is $\forall r\ge1\ \exists C\ \operatorname{Gen}(\chi,r,C)$, with the same $G$ and $\chi$ throughout. In A2, the first and last fields of the named finite local Tate duality supply this input through the finite generator lemma. The decomposition-group input is `LocalTateDuality`, and the completed-field consumer below uses `LocalTateDualityK`. The first field identifies $H^2(G,R_r(\chi_r))$ with $R_r$. The last field detects degree-two classes by the degree-zero invariants of the twisted dual. On scalar-twist coefficients every $R_r$-linear functional belongs to those invariants, since $\chi_r(g)\phi(\chi_r(g)^{-1}m)=\phi(m)$. Thus a representative of the class of $1$ works simultaneously for all finite modules by finite biduality. This is the finite supply already used for descent. [A2, H2EquivOfTorsionCharacter.lean:77–82,334–416; GalCoh.lean:22–34,201–205; LocalTateDualityK.lean:32–35,47–55]

#### Lemma. Correcting one step [Lean, read]

If $C$ satisfies $\operatorname{Gen}(\chi,r,C)$ and $D$ satisfies $\operatorname{Gen}(\chi,r+1,D)$, there is a function $D'$ satisfying $\operatorname{Gen}(\chi,r+1,D')$ and $D'\equiv C\pmod{\ell^r}$ pointwise.

**Level zero.** At $r=0$ the finite test module is zero because $\ell^0=1$. All three clauses are automatic, and congruence modulo $1$ is automatic. Take $D'=D$. No unit needs to be extracted at this step.

**Positive levels and the unit.** Let $r>0$. Every module killed by $\ell^r$ is also killed by $\ell^{r+1}$, so $D$ satisfies the lower-level clauses. On $T=R_r$, the first clause for $C$ makes its residue $\bar C$ a cocycle. The second clause for $D$ gives
$$
\bar C=\bar D x+\delta b,\qquad x\in R_r,\quad b:G\to R_r\ \text{locally constant}.
$$
If $x$ were divisible by $\ell$ in $R_r$, multiplication by $y=\ell^{r-1}\bmod\ell^r$ would give $\bar C y=\delta(yb)$, since $yx=0$. The third clause for $C$ would give $y=0$, contrary to $r>0$. Hence the representative $u$ of $x$ in $\{0,\ldots,\ell^r-1\}$ is prime to $\ell$, so it is a unit of $R$. The $r=1$ test uses $y=1$.

**Sign and preservation.** Lift $b$ by the same integer representatives to a locally constant $\beta:G\to R$ and set $D'=uD+\delta\beta$. Its reduction is exactly $\bar C$. On a finite module $T$ killed by $\ell^{r+1}$,
$$
D' t=D(ut)+\delta(\beta t).
$$
This is a cocycle by the first clause for $D$. If $z=Dx+\delta a$, put $t=u^{-1}x$ and obtain $z=D't+\delta(a-\beta t)$. If $D't=\delta a$, then $D(ut)=\delta(a-\beta t)$, so $ut=0$ and $t=0$. These are the three clauses at level $r+1$. The comparison equation has $+\delta b$, so the correction has $+\delta\beta$. In an example where the **unadjusted upper** representative already has an added coboundary $\delta B$, the correct $\beta$ cancels its scaled contribution with the opposite sign. [A2, H2EquivOfTorsionCharacter.lean:86–157,159–193]

#### Theorem. A single generator and the top-degree quotient [Lean, read]

Assume the finite input for $(G,\chi)$ above. There is a single $c:G\times G\to R$ satisfying $\operatorname{Gen}(\chi,r,c)$ for every $r\ge0$. Its reductions are locally constant and it is a continuous $R$-valued 2-cocycle for the $\ell$-adic topology.

If $G$ is compact, let $O$ be any commutative ring and let $M$ be an $R$-module and an $O$-module on the same additive group, with commuting scalar actions. Assume
$$
\forall m\in M\ \exists r\ge0\quad \ell^r m=0.
$$
Let $\pi$ be an $O$-linear representation of $G$ on $M$ such that $\pi(g)m=\chi(g)m$ for every $g,m$. For this **same** $c$, the assignment $x\mapsto[cx]$ is an $O$-linear isomorphism $M\to H^2(G,M(\chi))$. Its inverse sends $[z]$ to the unique $x$ for which $z=cx+\delta b$ with a locally constant $b:G\to M$. In particular it is the direction $H^2(G,M(\chi))\to M$ returned by the local top-degree interface.

**Proof of the common representative.** Start with $C_0=0$. Inductively use one supplied generator at level $r+1$ and apply the lemma with the already chosen $C_r$. The corrected $C_{r+1}$ generates at its own level and satisfies $C_{r+1}-C_r\in\ell^rR$ pointwise. For each pair $p=(g,h)$, telescoping gives $C_m(p)-C_n(p)\in\ell^nR$ whenever $m\ge n$. The sequence is Cauchy for the $\ell$-adic norm, so completeness gives a limit $c(p)$. Every coset of $\ell^nR$ is closed, so $c(p)-C_n(p)\in\ell^nR$. Separation gives uniqueness for this chosen sequence. Two functions congruent modulo $\ell^n$ act identically on every module killed by $\ell^n$, so all three clauses for $C_n$ carry to $c$. In the formal proof the Cauchy sequence uses the least integer representatives of $C_n(p)\bmod\ell^n$ and gives the same residues.

Testing the first clause on $1\in R_n$ shows that $c\bmod\ell^n$ is locally constant and satisfies the twisted cocycle identity at every $n$. Since the residue cosets form a basis of $R$, their open preimages give continuity of $c$ into $R$ with its $\ell$-adic topology. The value of $d_2c$ at each triple is in every $\ell^nR$ and hence zero. For a torsion element $x$, choose $n$ killing $x$. Then $cx$ is obtained by postcomposing $c\bmod\ell^n$ with $a\mapsto ax$. Each coefficient calculation therefore has the requisite local constancy using its own level. The neighbourhood used for a torsion evaluation may depend on its exponent. [A2, H2EquivOfTorsionCharacter.lean:124–132,195–227,277–279; Mathlib, PadicIntegers.lean:166–188,470–480; RingHoms.lean:447–459,713–718,733–779]

**Finite spans.** A locally constant function on a compact space has finite image, since its open fibres cover the space and admit a finite subcover. This applies to $G$ and $G\times G$. For a finite subset $S$ of $M$, choose a common killing exponent $r$ by taking the maximum of the individual exponents, with $0$ sufficient for the zero span. The $R$-span $T$ of $S$ is a quotient of $(R_r)^S$. It is finite, killed by $\ell^r$, and stable under the scalar action. We need only its $R$-module structure. For any cochain whose values lie in $T$, its local constancy carries to the restricted cochain because inclusion is injective. The cocycle and coboundary identities also carry to $T$ by that injection. [A2, H2EquivOfTorsionCharacter.lean:229–259; Mathlib, Topology/LocallyConstant/Basic.lean:154–158,176–181]

**Surjectivity and the quotient.** Let $[z]$ be any class, and take $T=\operatorname{span}_R z(G\times G)$. Use its exponent $r$ and the second generator clause on the restricted $z$. It gives $z=cx+\delta b$ in $T$, hence in $M$ by inclusion. The quotient test for $[z]=[cx]$ is $z-cx\in B^2$. With the order $[cx]=[z]$ the difference is $cx-z=\delta(-b)$. Both give the desired preimage.

**Injectivity and linearity.** If $[cx]=0$, choose a locally constant $b:G\to M$ with $\delta b=cx$ and take $T=\operatorname{span}_R(\{x\}\cup b(G))$. Both sides of the equality lie in this finite $T$. Applying the third clause once in $T$ gives $x=0$. Pointwise, $c\,(x+y)=cx+cy$ and $c\,(ax)=a(cx)$ for $a\in O$, the latter by commutation of the two scalar actions. Passage to the quotient is $O$-linear because $\pi$ and the differentials are $O$-linear. This proves that $x\mapsto[cx]$ is a bijective $O$-linear map. Its inverse is $O$-linear as well, and injectivity gives exactly the claimed independence of the coordinate from the representative and primitive. [A2, H2EquivOfTorsionCharacter.lean:261–305; Mathlib, LinearAlgebra/Quotient/Defs.lean:81–98,207–234]

**Bounded and unbounded torsion.** A global bound $\ell^rM=0$ would allow one fixed level for all finite spans, even for an infinite bounded module. In $M=\mathbb Q_\ell/\mathbb Z_\ell$, the elements $\ell^{-n}+\mathbb Z_\ell$ have order $\ell^n$, and no such bound exists. The span for surjectivity depends on a representative. The span for injectivity depends on the particular primitive as well as the element. The generator remains the same in both arguments.

#### Two computations on decomposition groups [Expository]

Take the decomposition group of a prolongation of the $p$-adic place from $\mathbb Q$ to $\overline{\mathbb Q}$ and use its identification with $G_{\mathbb Q_p}$. The identification comes from finite decomposition groups of completions and Krasner approximation, followed by the inverse limit. In each computation $\ell=3$ and $p\in\{19,7\}$. For $n=3^r$ choose compatible primitive $n$th roots of unity $\zeta_n$ and compatible roots $\alpha_n=p^{1/n}$. Write $i_n(g)$ for the unramified character sending arithmetic Frobenius to $1$ modulo $n$, and $j_n(g)$ for the exponent of $\zeta_n$ in $g(\alpha_n)/\alpha_n$.

Since $p\equiv1\pmod3$, iterating the cubing identity for $1+3a$ gives $p^{3^r}\equiv1\pmod{3^r}$. The unramified extension of degree $n$ therefore contains $\mu_n$: all roots occur in its residue field and lift uniquely by Hensel's lemma because $p\nmid n$. Over this extension $X^n-p$ is Eisenstein, and its roots are the $\zeta_n^j\alpha_n$. The compositum is Galois over $\mathbb Q_p$ of degree $n^2$. Frobenius on the unramified field extends to a lift $s$ fixing $\alpha_n$, by applying Frobenius to the coefficients in the presentation by $X^n-p$. Choose $t$ in the relative Galois group taking $\alpha_n$ to $\zeta_n\alpha_n$. Thus $(i,j)=(i_n(g),j_n(g))$ runs over all residues in $(\mathbb Z/n)^2$, with $s=(1,0)$, $t=(0,1)$ and
$$
(i,j)(i',j')=(i+i',\,j+p^i j'),\qquad \chi_n(i,j)=p^i\bmod n.
$$
In additive notation the cup of $i_n$ with the Kummer class of $p$ is
$$
U_n\big((i,j),(i',j')\big)=i\,p^i j'\pmod n.
$$
The character $i_n$ adds under multiplication, while $j_n(gh)=j_n(g)+\chi_n(g)j_n(h)$. Substitution of these two identities in $d_2U_n$ gives
$\chi_n(g)\chi_n(h)\big(i_n(h)-i_n(gh)+i_n(g)\big)j_n(k)=0$.
The roots and unramified characters are compatible, so the $U_n$ reduce to each other. Local reciprocity gives their invariant $1/n$ in $\mathbb Q/\mathbb Z$ since the unramified character sends the Artin symbol of the uniformizer to $1$. Thus these are actual generators on $G_{\mathbb Q_p}$. For a cyclic coefficient $R_m$ of exponent $3^m$ with $m\le r$, evaluation by the representative at level $r$ is evaluation by its reduction $U_{3^m}$. The invariant identifies $H^2(G,R_m(\chi_m))$ with the cyclic group generated by this class. Every finite $R$-module killed by $3^r$ is a finite direct sum of these cyclic modules, and the cochain operations and quotients are coordinatewise. This proves the three finite generator clauses for these representatives. The finite quotients give explicit values of the representatives. [Milne, Algebraic Number Theory, §7, Proposition 7.60 and the approximation argument, pp. 131–133, and §8, Proposition 8.10, p. 139](https://www.jmilne.org/math/CourseNotes/ANT.pdf) · [Milne, Class Field Theory, I §1, pp. 19–23, and III §3, Proposition 3.6 and Lemma 3.7, and §4, Steps 2–3, pp. 109–113](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

**First calculation. Two levels with trivial reduced action.** Take $p=19$, so $\chi_3=\chi_9=1$, and use $C=U_3$ downstairs. Upstairs put $D=5U_9+\delta B$ with $B(i,j)=i^2\bmod9$. On the degree-$9^2$ quotient, the differential is $-2ii'\bmod9$, since squaring respects reduction modulo $9$. The lower reduction is $2U_3+\delta\bar B$, so $C=2\bar D+\delta(-2\bar B)$. Set $u=2$ and lift the primitive by the integer function $-2i^2$ with $i\in\{0,\ldots,8\}$. The corrected residue is
$$
D'=2D+\delta(-2B)=10U_9=U_9\bmod9.
$$
At $(s,t)$ the lower value is $1$ and the raw upper value is $5$, giving raw residue $2$ modulo $3$. At $(s,s)$ the lower value is $0$ and the raw upper value is $-2=7\bmod9$. Scaling alone gives $2\cdot7=5\bmod9$, still $2\bmod3$. The correction adds $4\bmod9$, making the value $0$. Multiplying a normalized generator by $3$ destroys the generator property. In $\mathbb Z/9$ the nonzero coordinate $3$ gives $(3U_9)3=0=\delta 0$. The invariant of $3U_9$ is $1/3$, so the generated classes miss the class of invariant $1/9$. If one tries to use $3U_9$ as the lower representative and $U_{27}$ upstairs, the comparison coordinate is $3$ modulo $9$. Every level-three generator restricts to a level-two generator by monotonicity. Therefore no corrected level-three generator can have $3U_9$ as its residue.

**Second calculation. A nontrivial twist and a tower.** Take $p=7$, and use $C=U_9$ and $D=2U_{27}+\delta B$ with $B(i,j)=j^2\bmod27$. The full twisted formula is
$$
(\delta B)((i,j),(i',j'))=7^i(j')^2-(j+7^i j')^2+j^2\pmod{27}.
$$
In particular the term $\chi(s) B(t)$ is $7$, and $\delta B(s,t)=12$. At $(t,t)$ it is $-2$. Use $u=5$, a lift of $2^{-1}\bmod9$, and use $\beta=-5B$ with integer representatives of $B$. Then $D'=5D+\delta\beta$ is $10U_{27}$ modulo $27$, reducing to $U_9$ modulo $9$. At $(s,t)$, $U_{27}=7$, $D=26$ and $D'=5\cdot26-5\cdot12=70=16\bmod27$. This reduces to $7\bmod9$. At $(t,t)$, scaling alone gives $-10\bmod27$, which is $8\bmod9$ while $C(t,t)=0$. Using the wrong sign $\beta=+5B$ gives $-20$, which is $7\bmod9$ there. The two residues detect omission of the coboundary and reversal of its sign.

Take the residues $U_3$, $U_9$, and $10U_{3^r}$ for $r\ge3$. They agree successively. With $i=\lim i_{3^r}$ and $j=\lim j_{3^r}$ the common representative is $c(g,h)=10i(g)\chi(g)j(h)$. On $M=\mathbb Q_3/\mathbb Z_3$ the element $x_r=3^{-r}+\mathbb Z_3$ produces the cocycle with numerator $10U_{3^r}$ over $3^r$. At $(s,t)$ its values for $r=1,2,3$ are respectively $1/3$, $7/9$ and $16/27$ modulo $\mathbb Z_3$. Its class has order $3^r$ by the invariant of $U_{3^r}$ and the isomorphism just proved. The full $R$-valued $c$ has infinite image: fix $g$ with $i(g)=1$, then $j(h)$ ranges over $\mathbb Z_3$ by compactness and surjectivity at each level. A globally locally constant $c$ on the compact square would have finite image. Here every fixed torsion evaluation $cx_r$ is locally constant despite this infinite image.

**Omitting the correction.** On the $p=19$ group one can choose the genuine generators $U_3$ and $5U_9+\delta B$ independently. At $(s,t)$ their residues modulo $3$ are $1$ and $2$. No $3$-adic function can have both as its prescribed residues. A coboundary alone also fails, since the two lower classes have invariants $1/3$ and $2/3$. Even after multiplication by the unit, the discrepancy at $(s,s)$ witnesses failure without the coboundary correction. The $p=7$ computation gives the corresponding discrepancy with nontrivial reduced action. These failures concern representative matching and preservation of generation.

#### The completed-field consumer and the arithmetic boundary

In the local period-data interface, take a prime $\ell$, a finite extension $K/\mathbb Q_\ell$ inside the chosen algebraic closure, and the group denoted `GK K` on the period side. The archive compares it with the absolute group over $K$ by the bicontinuous group isomorphism $\Phi=\texttt{K.1.fixingSubgroupEquiv}$. The cyclotomic character $\chi_Z$ on the absolute group agrees, after transport and inclusion into $\mathbb Q_\ell$, with the period character by cyclotomic uniqueness. Consequently it is continuous as a $\mathbb Z_\ell$-valued function. Pullback along $\Phi$ carries the all-level generator to the period group, which is compact by the continuous inverse map from the compact absolute group. This pullback carries the cochain formulas and their local constancy in both directions, as in `Gen.transport`. [A2, ContinuousFixingSubgroupEquiv.lean:286–305; H2EquivOfTorsionCharacter.lean:307–332,464–483]

The coefficient field $L$ and ring $O$ satisfy `GoodO`. Here $L$ is finite over $\mathbb Q_\ell$ with its module topology and is a topological ring. The DVR $O$ has fraction field $L$ and open image in $L$. The rank-one cyclotomic lattice $L_1$ in the interface has $L_1.T$ equal to the image of $O$. The target module is $M=L/L_1.T$, with the quotient representation `repD L1`. Here is how the consumer pays the scalar hypotheses.

- Openness at zero shows that for any $x\in L$ and sufficiently large $m$, the entire set $\ell^m R x$ lies in the image of $O$. Indeed $a\mapsto ax$ is continuous from $\mathbb Q_\ell$ into $L$, and the sets $\ell^mR$ form a neighbourhood basis of zero. In particular each class $[x]$ is killed by $\ell^m$.
- Apply the same argument to $x=1$. Any $a\in R$ is the sum of an integer representative modulo $\ell^m$ and an element of $\ell^mR$. Both summands have images in $O\subset L$. Fraction-field injectivity then gives the ring map $R\to O$, with composite equal to the given map into $L$. The scalar actions commute because multiplication in $O$ is commutative.
- The quotient action on $[x]$ is multiplication by the image of the period character. Its equality in $L$ with the image of $\chi_Z(\Phi g)$ gives the pointwise scalar identity required by the theorem.

Thus the inverse of $x\mapsto[cx]$ yields $H^2(\texttt{repD}\,L_1,\top)\simeq_O L/L_1.T$. The call passes the same $c$ at every level after transport. The choice $K=L=\mathbb Q_\ell$, $O=R$, and $L_1.T=R$ is legal for this coefficient interface: $R$ is an open DVR with fraction field $\mathbb Q_\ell$, and the cyclotomic units and their inverses preserve it. For example at $\ell=3$, the compatible cups of the unramified characters with the Kummer classes of $3$ again have invariants $1/3^r$ by the same reciprocity formula. This witnesses the positive finite input on the actual absolute local group in residue characteristic $\ell$, where the finite tame presentation used in the two calculations is unnecessary. The coefficient quotient already has unbounded exponent in this choice. [A2, LocCoh.lean:25–32,99–109,171–175; LocalSituation.lean:609–611; H2EquivOfTorsionCharacter.lean:425–460,477–504; TateH2OfFiniteDuality.lean:11–12; TateDualityH2FiniteCoefficients.lean:147–188]

The next call is in the assembly `Bk.forms`. It passes the resulting `LocalTateTopDegree`, together with its separate `CobLO` input, to `h2_line_of_tate_h2_and_coboundaries`. This identifies the exact use of the quotient equivalence in the local Bloch–Kato chain. [A2, BkMain.lean:126–139]

Tate's finite local theorem supplies the arithmetic comparison with the dual. Hilbert 90 and Kummer identify the cohomology of roots of unity with the corresponding Brauer torsion. The passage through finite spans is the cochain argument for the classical commutation with directed unions of discrete coefficients. The representative-level normalization here follows A2. The full finite arithmetic suppliers `LocalTateDuality` and `LocalTateDualityK` retain their named scopes, including the completed-field, roots-of-unity and cohomology comparisons and the Tate core. [Tate, ICM Stockholm 1962, §2, Theorem 2.1, p. 289](https://www.mathunion.org/fileadmin/ICM/Proceedings/ICM1962.1/ICM1962.1.ocr.pdf) · [Milne, Arithmetic Duality Theorems, I §2, Corollary 2.3, p. 28](https://www.jmilne.org/math/Books/ADTnot.pdf) · [Milne, Class Field Theory, II §4, Proposition 4.4, p. 88](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

**Reading scope.** The construction and quotient proof above are author-level R3 on A2. The predecessor's same-source preliminary review applies to its bounded descent. Kernel replay, compiled reachability from `Main.riemannHypothesis`, independent adjudication of this section and peer review are separate open checks. The two hand calculations are expository. [Pinned declarations and reading record](../sources/SOURCES.md#chapter-10-10414-a-compatible-tate-generator-for-torsion-coefficients)

### 10.4.15 Finite first cohomology for the fundamental local cocycle

The fundamental local cocycle carries two kinds of information. Its degree-two coordinates use the compatible representative of [§10.4.14](#10414-a-compatible-tate-generator-for-torsion-coefficients). Its last field gives finite first cohomology at every positive reduction of the same character. This second assertion is used when choosing compatible primitives across levels. The two assertions draw on different fields of local Tate duality. [Source notes](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

#### Two local computations [Expository]

Use coefficient prime $\ell=3$ and level $r=2$. In either local field below, choose a primitive ninth root $\zeta$ in the chosen separable closure. Writing $g\zeta=\zeta^{\chi_2(g)}$ identifies the positive cyclotomic module $\mathbb Z/9(\chi_2)$ with $\mu_9$ by $i\mapsto\zeta^i$. For $a\in K^\times$, choose $b^9=a$ and write $g(b)/b=\zeta^{f_a(g)}$. Then
$$
 f_a(gh)=f_a(g)+\chi_2(g)f_a(h).
$$
Changing $b$ to $\zeta^j b$ adds the coboundary $g\mapsto(\chi_2(g)-1)j$. The cochains are continuous because the roots involved lie in finite extensions. The Kummer sequence and Hilbert 90 give the isomorphism $a\mapsto[f_a]$ from $K^\times/(K^\times)^9$ onto $H^1_{\mathrm{cts}}(G_K,\mathbb Z/9(\chi_2))$. Both fields have characteristic zero. [Milne, Arithmetic Duality Theorems, I §2, pp. 26–28](https://www.jmilne.org/math/Books/ADTnot.pdf)

**Residue characteristic equal to the coefficient prime.** For $K=\mathbb Q_3$, put $U_j=1+3^j\mathbb Z_3$ for $j\ge1$. The valuation and the sign of the residue give $\mathbb Q_3^\times=3^{\mathbb Z}\times\{1,-1\}\times U_1$. Ninth powers are bijective on the sign factor. For $j\ge1$,
$$
 (1+3^j x)^3=1+3^{j+1}\bigl(x+3^j x^2+3^{2j-1}x^3\bigr).
$$
For each $y\in\mathbb Z_3$, the equation $x+3^j x^2+3^{2j-1}x^3=y$ has one solution modulo $3$ and derivative $1$ modulo $3$. Simple-root Hensel lifting gives a unique solution in $\mathbb Z_3$. Thus $U_j^3=U_{j+1}$ and $U_1^9=U_3$. Reduction modulo $27$ identifies $U_1/U_3$ with the nine residues congruent to $1$ modulo $3$. The class of $4$ generates them because $4^3\equiv10$ and $4^9\equiv1\pmod{27}$. The independent classes of $3$ and $4$ give
$$
 H^1_{\mathrm{cts}}(G_{\mathbb Q_3},\mathbb Z/9(\chi_2))\simeq(\mathbb Z/9)^2.
$$
The coordinates are the valuation modulo $9$ and the unique $j\bmod 9$ for which the principal-unit part equals $4^j\bmod 27$. Both are attained, so the order is $81$. On the coefficients, $\Phi_9(1+X)=X^6+6X^5+15X^4+21X^3+18X^2+9X+3$ is Eisenstein at $3$. The extension $\mathbb Q_3(\zeta)/\mathbb Q_3$ is therefore totally ramified of degree six. Its six automorphisms act by the six unit exponents modulo $9$. Inertia has full image on the coefficient module. Multiplication by $2$ has only zero as a fixed vector, so the coefficient invariants vanish. [Serre, Local Fields, I §6 and III §5](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Serre-Local.pdf)

**Residue characteristic prime to the coefficient prime.** For $K=\mathbb Q_2$, every unit $u$ has a unique ninth root in $\mathbb Z_2^\times$. Indeed $X^9-u$ has the simple root $1$ modulo $2$, with derivative $9$ at that residue. Every class of $\mathbb Q_2^\times/(\mathbb Q_2^\times)^9$ is represented uniquely by $2^i$, $0\le i<9$. Thus the Kummer class of $2$ generates $H^1_{\mathrm{cts}}(G_{\mathbb Q_2},\mathbb Z/9(\chi_2))$, of order $9$. The ninth roots lift uniquely from the residue algebraic closure. The order of $2$ modulo $9$ is six since $2^3\equiv-1$ and $2^2\equiv4$. The roots generate the unramified degree-six extension. The coefficient action is trivial on inertia and multiplication by $2$ on arithmetic Frobenius, again with zero invariants. The Kummer class of $2$ detects inertia even here. Over that unramified field $X^9-2$ is Eisenstein and its splitting field has an automorphism sending $2^{1/9}$ to $\zeta\,2^{1/9}$. This gives inertia value $1$ for $f_2$. Coboundaries restrict to zero there. For the finite quotient used in the arithmetic check, write $L=\mathbb Q_2(\zeta)$ and $\beta=2^{1/9}$. Over $L$, the basis $1,\beta,\dots,\beta^8$ comes from the Eisenstein polynomial. Frobenius on $L$ extends to $s$ fixing $\beta$ by acting on the coefficients in this basis, since $\beta^9=2$ is rational. If $t(\beta)=\zeta\beta$ and $t$ fixes $L$, then $sts^{-1}=t^2$. Consequently $t^js^i$ has character $2^i\bmod9$ and Kummer coordinate $j\bmod9$, in agreement with the crossed-homomorphism formula on the absolute group. [Milne, Class Field Theory, I §1 and III §3](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

#### The local input and the two adjoints [Lean, read]

Fix a prime $\ell$, an intermediate field $K$ finite over $\mathbb Q_\ell$ inside $\Omega=\overline{\mathbb Q_\ell}$, and $G=\operatorname{Gal}(\Omega/K)$ with its Krull topology. Write $\chi_Z:G\to\mathbb Z_\ell^\times$ for the positive cyclotomic character. At a fixed integer $r>0$ let $n=\ell^r$, $R_r=\mathbb Z/n$ and $\chi_r=\chi_Z\bmod n$. Let $M$ be a finite $R_r$-module with the discrete topology and a continuous $R_r$-linear action $\rho$. Its twisted dual is $M^\dagger=\operatorname{Hom}_{R_r}(M,R_r)$, discrete, with action
$$
 (g\lambda)(m)=\chi_r(g)\lambda(\rho(g^{-1})m).
$$
Evaluation satisfies $(g\lambda)(\rho(g)m)=\chi_r(g)\lambda(m)$. In particular for $M=R_r(\chi_r)$ the dual is the constant $R_r$. All cohomology here uses continuous cochains. [A2, GalCohDefs.lean:21–81,100–111](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

The input `LocalTateDualityK` gives five fields at these arguments. For $C=H^2(G,R_r(\chi_r))$, field 1 gives an $R_r$-linear isomorphism $\eta:C\to R_r$. Field 2 gives the adjoint from $H^0(G,M)$ into the linear dual of $H^2(G,M^\dagger)$ with values in $C$. Fields 3 and 4 give both adjoints of
$$
 b:H^1(G,M^\dagger)\times H^1(G,M)\longrightarrow C
$$
as bijections. This is the cup in the displayed order, with the flipped evaluation on coefficients. Field 5 gives a bijective map $H^2(G,M)\to\operatorname{Hom}_{R_r}(H^0(G,M^\dagger),C)$. The source composes the representations in the cup maps with the identity homomorphism on $G$, which preserves the action. [A2, LocalTateDualityK.lean:32–35,47–61](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

#### Lemma. Two bijective adjoints force finite modules [Lean, read]

Let $n>0$ and $R=\mathbb Z/n$. Suppose $A,B$ are $R$-modules and $C\simeq_R R$. If both adjoints of an $R$-bilinear pairing $A\times B\to C$ are bijections onto the full $R$-linear duals with target $C$, then $A$ and $B$ are finite.

**Proof.** First show that any infinite abelian group $X$ killed by $n$ satisfies
$$
 |X|<|\operatorname{Hom}_{\mathbb Z}(X,\mathbb Z/n)|.
$$
For $n=1$ there is no infinite $X$. When $n=p$ is prime, choose a basis $I$ over $\mathbb F_p$. Since vectors have finite support over a finite field, $|X|=|I|$ for infinite $X$. Arbitrary values on $I$ give all linear functionals, including the $2^{|I|}$ distinct assignments with values in $\{0,1\}$. Cantor's theorem gives the strict inequality. This is the cardinal consequence used by A2, whose prime step calls the pinned Mathlib Erdős–Kaplansky lemmas.

For general $n>1$, factor $n=pm$ for a prime $p$ and induct on $n$. Set $P=pX$ and $Q=X/P$. Choosing coset representatives gives $|X|=|P||Q|$. Since $X$ is infinite and both factors are at most $|X|$, at least one factor has cardinal $|X|$. If $|P|=|X|$, then $P$ is killed by $m$ and induction applies to $P$. If $|P|<|X|$, then $|Q|=|X|$, $Q$ is killed by $p$, and the prime step applies to $Q$. Use the surjection $x\mapsto px$ onto $P$ in the first case and the quotient map onto $Q$ in the second. For the corresponding divisor $a=m$ or $a=p$, multiplication by $n/a$ embeds $\mathbb Z/a$ into $\mathbb Z/n$. Precomposing with the surjection and postcomposing with this injection embeds the larger character set of $P$ or $Q$ into the character set of $X$. This proves the inequality.

Now assume that $A$ is infinite. The adjoint from $B$ gives $|B|=|\operatorname{Hom}_R(A,R)|>|A|$, since additive maps between $R$-modules respect scalar multiplication by integer residues. Thus $B$ is infinite, and the other adjoint gives $|A|>|B|$, a contradiction. If $B$ is infinite, the adjoint from $A$ forces $A$ infinite and gives the same contradiction. [A2, FiniteOfPerfectPairingZmod.lean:7–151 and pinned Mathlib](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

#### Theorem. Finite $H^1$ and $H^2$ on the same layer [Lean, read]

Under the local hypotheses and `LocalTateDualityK` above, $H^1(G,M)$ and $H^2(G,M)$ are finite.

**Proof.** Field 1 gives $|C|=n$. Apply the lemma to fields 3 and 4 with $A=H^1(G,M^\dagger)$ and $B=H^1(G,M)$. A2 takes the second member of the resulting finiteness pair. In degree two, $\operatorname{Hom}_{R_r}(M,R_r)$ embeds in the finite function set from $M$ to $R_r$. Its fixed submodule $H^0(G,M^\dagger)$ is finite. Field 5 injects $H^2(G,M)$ into the linear maps from this submodule to $C$, hence into a finite function set. In particular,
$$
 |H^2(G,M)|\le n^{|H^0(G,M^\dagger)|}\le n^{\,n^{|M|}}.
$$
The proof uses the duality fields and bounded-exponent character algebra. The separate `LocalEulerCharK` gives a cardinality formula with factor $|M|^{[K:\mathbb Q_\ell]}$ once the groups are finite. The Euler characteristic identity and finite generation of $G$ play no role in this deduction. Compactness gives finite images for individual cochains, with no bound on the number of classes. [A2, FiniteH1H2Local.lean:8–25 and FiniteH1H2LocalStatement.lean:6–7](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

For $M=R_r(\chi_r)$, field 5 has target $\operatorname{Hom}_{R_r}(R_r,C)\simeq C$ by evaluation at $1$. Thus $|H^2|=9$ in each example. Independently, the Euler characteristic formula gives $|H^1|=|H^0||H^2|[\mathcal O_K:9\mathcal O_K]$. Here $|H^0|=1$, and the last index is $9$ in $\mathbb Q_3$ and $1$ in $\mathbb Q_2$. This agrees with the direct Kummer calculations. [Tate, ICM 1962, §2, Theorems 2.1–2.2](https://math.stanford.edu/~conrad/BSDseminar/refs/TateICM.pdf)

#### Lemma. Transport with the same action [Lean, read]

Let $D=K.\mathrm{fixingSubgroup}\subseteq\operatorname{Gal}(\Omega/\mathbb Q_\ell)$. The map $\Phi:D\to G$ called `fixingSubgroupEquiv` views the same automorphism of $\Omega$ as an automorphism over $K$. Both directions are continuous. To check $\Phi^{-1}$ at the identity, test against the pointwise stabilizer of a finite extension $E/\mathbb Q_\ell$ inside $\Omega$, a basic neighborhood in the ambient Krull group. Its preimage contains the stabilizer of $KE/K$, a finite extension because generators of $E$ over $\mathbb Q_\ell$ remain algebraic over $K$. Translations give continuity everywhere. The compact Krull group $G$ maps bijectively to the Hausdorff space $D$, yielding continuity of $\Phi$. [A2, ContinuousFixingSubgroupEquiv.lean:286–305](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

For a bicontinuous group isomorphism $\Phi:D\to G$, use the same discrete $R$-module $M$ and suppose $\rho'(d)m=\rho(\Phi d)m$. Precomposition sends a continuous crossed homomorphism $f$ to $f\circ\Phi$, since
$$
 (f\circ\Phi)(d_1d_2)=(f\circ\Phi)(d_1)+\rho'(d_1)(f\circ\Phi)(d_2).
$$
The coboundary of $m$ pulls back to $d\mapsto\rho'(d)m-m$, the coboundary of the same $m$. Precomposition with $\Phi^{-1}$ respects the inverse action equation, and the two composites are identities on representatives and quotients. This proves the degree-one component of `contCohomology_transport_mulEquiv`. In degree two the pullback evaluates $f$ at $(\Phi d_1,\Phi d_2)$. Each term of the differential commutes with pullback by multiplicativity and the action equation, including the differential of a continuous primitive. Precomposition with the inverse again gives the inverse on the quotient. [A2, ContCohomologyTransportMulEquiv.lean:25–54 and SeparatedDvrSecondCohomologyMem.lean:217–242](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

#### The last field of the fundamental cocycle [Lean, read]

Fix the original `LocPrime` datum $P$ and the same $K$. Set $\chi=\chi_Z\circ\Phi$. The root-of-unity specifications of $P.\chi_Q$ and $\chi_Z$ determine the same exponents modulo $\ell^s$ on a primitive $\ell^s$th root for every $s>0$. The defining $\ell$-adic approximations then give equal values in $\mathbb Q_\ell$. Thus `PD_χ` identifies $\chi$ with the period character $(P.\mathrm{PD}\,K).\chi$ after inclusion in $\mathbb Q_\ell$. The scalar map $\chi_Z$ is continuous since each finite reduction acts on roots of unity in a finite Galois extension and the open residue cosets form a basis. The reduced action on the discrete coefficient module is jointly continuous. Pullback commutes with reduction:
$$
 (\chi\bmod \ell^r)(d)=(\chi_Z\bmod\ell^r)(\Phi d).
$$

The proof of `exists_fundamental_cocycle_loc` obtains the compatible representative on $G$ by the earlier generator construction, using fields 1 and 5 separately at each $r+1$. It pulls the representative back along $\Phi$. The tuple records compactness, continuity, equality with the period character and the inherited `Gen` properties. For its last field, take any $r>0$. In `finite_H1_H2_local` use the original $K$, the same `redChar χZ r`, and $M=R_r$ with that scalar action. Its first projection supplies finite $H^1$ on $G$. The first projection of `contCohomology_transport_mulEquiv` sends that group to the $H^1$ of the scalar representation of the reduction of $\chi$ on $D$. The action equation above is definitional in the call. The conclusion by `Finite.of_equiv` is
$$
 \forall r>0,\qquad \#H^1(D,R_r(\chi\bmod\ell^r))<\infty .
$$
This field depends on the character and the level. Its proof is independent of the choice of the compatible representative. The whole datum supplies `GlobalTheory.InvLine.spanQ` and `GlobalTheory.IntTateTop.admH2_of_duality`. At `IntegralTateH2Top.lean:101`, `int_span` uses this finiteness in `mem_coboundaries_of_forall_pow` when passing from finite-level primitives to a continuous integral coboundary. That passage enters here as a named input. [A2, ExistsFundamentalTwoCocycleOfLocalTateDuality.lean:16–55 and consumers](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

The $\mathbb Q_3$ example realizes the original signature with the bottom intermediate field of $\overline{\mathbb Q_3}/\mathbb Q_3$ and a $P$ supplied by the named `GlobalTheory.MemLoc.exists_locPrime_tied 3`. The two Kummer coordinates therefore belong to the transported finite group in the last field. The $\mathbb Q_2$ computation with coefficient prime $3$ uses the classical local theorem with distinct primes, as does A2's broader `dualityFor_absGal` interface. The fundamental-cocycle signature requires a field finite over $\mathbb Q_\ell$, hence its residue characteristic is $\ell$. [A2, ExistsLocalPrimeAinf.lean:281–285 and DualityForAbsGal.lean:17–54](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

#### Failure boundaries and attribution

**Remove the local-field hypothesis.** Keep $\ell=3$, $r=2$, the positive cyclotomic action and continuous cochains, but take $K=\mathbb Q$ with its absolute Galois group. Kummer theory identifies $H^1$ with $\mathbb Q^\times/(\mathbb Q^\times)^9$. The prime valuations modulo nine give one independent cyclic summand of order nine for every rational prime. Unique factorization and the fact that both signs are ninth powers give the direct sum of these cyclic summands. This group is infinite although the absolute Galois group is profinite and the coefficient module is finite discrete.

**Remove inverse continuity in the transport.** Let $V$ be the additive group of measurable $\mathbb F_2$-valued functions on $[0,1]$ modulo equality almost everywhere, with the translation-invariant metric $d(f,h)=\mu\{f\ne h\}$ for Lebesgue measure $\mu$. Addition is continuous by the union bound. The path $t\mapsto f1_{[0,t]}$ joins zero to $f$ and has distance at most $|s-t|$ between times $s,t$. Thus $V$ is path connected and its continuous $H^1$ with trivial discrete $\mathbb F_2$ coefficients is zero, since a continuous homomorphism to a discrete group is constant on paths. Give the same additive group the discrete topology to obtain $D_0$. The identity $D_0\to V$ is continuous and its inverse is discontinuous, as shown by the indicators of intervals of positive lengths tending to zero. The indicators of infinitely many disjoint intervals of positive measure are linearly independent. Extend them to a basis. Assigning values independently on those indicators gives infinitely many homomorphisms, all continuous on $D_0$. Coboundaries vanish for both groups. This example also gives infinite degree-one cohomology on $V$ if all algebraic cochains are allowed.

**Keep only zero radicals.** With $R=\mathbb Z/n$, $n>1$, the finite-support module $R^{(\mathbb N)}$ pairs with itself by the dot product into $R$. Testing coordinate vectors gives zero radicals. The functional adding all coordinates takes $1$ on every coordinate vector. A dot product with a fixed finite-support vector vanishes on almost all such vectors, so neither adjoint hits this functional. Mere nondegeneracy with a finite target permits infinite modules.

Tate's 1962 Theorem 2.1 includes finiteness and the local cup dualities for finite Galois modules of order invertible in the field, over a complete discretely valued field with finite residue field in the nonarchimedean case. Each finite $R_r$-module here has $\ell$-power order, which is invertible in the characteristic-zero field even when the residue characteristic is $\ell$. Under $R_r(\chi_r)\simeq\mu_{\ell^r}$, the dual in the theorem is $\operatorname{Hom}(M,\Omega^\times)=\operatorname{Hom}(M,\mu_{\ell^r})$. Kummer and Hilbert 90 identify the degree-two target with the $\ell^r$-torsion of the Brauer group, and the local invariant gives $\tfrac{1}{\ell^r}\mathbb Z/\mathbb Z$. A2's fields use those coordinates in degrees $(1,1)$ and $(2,0)$. Milne also gives a proof of finiteness starting from the Kummer power quotient and finite Galois dévissage. The classical theorem covers the local conclusion, and A2 contains the cardinal argument and its assembly. The textbook follows that assembly through the actual last field and works out the two arithmetic examples. [Tate, ICM 1962, §§1–2](https://math.stanford.edu/~conrad/BSDseminar/refs/TateICM.pdf) · [Milne, I §2, Theorem 2.1 and Corollary 2.3](https://www.jmilne.org/math/Books/ADTnot.pdf)

The deeper supplier `Gcoh.top_tate` itself invokes `finite_cohomology_galois_top` for an auxiliary first-cohomology input to `tate_core`. The present deduction runs from the completed duality package to its finite cyclic-coordinate interface. [A2, GcohTate.lean:9–18,46–73 and GcohTop.lean:11](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

The local R3 reading covers the bounded-exponent cardinal proof, the extraction of the four duality fields, the degree-one and degree-two cochain and quotient maps, and the actual positive-layer call. `LocalTateDualityK`, the period datum and the later passage to integral primitives are named inputs. The compatible generator and the bounded-layer comparison retain their earlier reading and review scopes. This reading records a static declaration trace. Lean kernel replay, declaration-level reachability from `Main.riemannHypothesis`, independent audit and peer review have separate evidence. [Pinned declarations](../sources/SOURCES.md#chapter-10-finite-first-cohomology-for-the-fundamental-local-cocycle)

### 10.4.16 One integral primitive from coboundaries at every level

A class can vanish modulo every power of $\ell$ even when the primitives chosen at successive powers disagree. The last field in [§10.4.15](#10415-finite-first-cohomology-for-the-fundamental-local-cocycle) gives finite first cohomology for each positive reduction of one representation. In the archive this makes the set of primitives at each level finite. Compactness then gives a family that agrees under reduction, and the reductions together show that its integral primitive is continuous. [Source notes](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

#### Two cochain calculations [Expository]

Write $R=\mathbb Z_3$. First let $G=\mathbb Z/3$ be discrete, with trivial action, and take $i(g)\in\{0,1,2\}$ to be the digit representing $g$. The differential of $i$ is $z(g,h)=3\lfloor(i(g)+i(h))/3\rfloor$, with rows $(0,0,0),(0,0,3),(0,3,3)$ in digit order. For any coefficient ring here the equation at the identity pair forces a primitive of $z$ to vanish at the identity. Subtracting $i$ leaves an additive map. Thus at level $r>0$, all primitives have the form
$$
 b_{r,k}(g)=i(g)+k3^{r-1}i(g)\pmod{3^r},\qquad k\in\{0,1,2\}.
$$
Indeed the value at $1$ of an additive map is killed by $3$ and determines its values everywhere. Modulo $3$ the rows of primitive values, indexed by $k$, are $(0,1,2),(0,2,1),(0,0,0)$. Modulo $9$ they are $(0,1,2),(0,4,8),(0,7,5)$. Modulo $27$ they are $(0,1,2),(0,10,20),(0,19,11)$. For every $r$, reduction from $r+1$ sends all three solutions to $b_{r,0}$. In particular the level-one zero solution has no level-two lift. The surviving family is $b_{r,0}$ at every level and recovers the integral digit function $i$. Over $R$ every homomorphism from this finite group is zero, so this primitive is unique. At each level $B^1=0$ and $H^1$ has exactly three elements, as required.

For a nontrivial action, use $G=G_{\mathbb Q_7}$ with the positive $3$-adic cyclotomic character. Take $t:G\to\mathbb Z_3$ from the maximal unramified quotient, sending arithmetic Frobenius to $1$. All $3^r$-th roots of unity are unramified. In residue degree $3^r$ they are the simple roots of $X^{3^r}-1$ lifted from the residue field, since $7^{3^r}\equiv 1\pmod{3^r}$. Arithmetic Frobenius raises each to its seventh power, by uniqueness of the lift. The congruence $7^{3^r}\equiv1\pmod{3^r}$ makes the reductions of the powers compatible, so $\chi(g)=7^{t(g)}$ on the original group. The power on the right is the continuous extension of $7^i$ from nonnegative integers. For $i=t(g)$ and $j=t(h)$, set $b(g)=i^2$. Then
$$
 z(g,h)=\delta b(g,h)=(7^i-1)j^2-2ij .
$$
All of these are continuous cochains. In particular $z$ is a cocycle by $d_2\delta=0$. Tate's finite local theorem gives the required finite $H^1$ on $G$ with exactly this reduced action. [Milne, *Class Field Theory*, I §1, pp. 21–23](https://www.jmilne.org/math/CourseNotes/CFT.pdf#page=30) · [Tate, ICM 1962, Theorem 2.1](https://math.stanford.edu/~conrad/BSDseminar/refs/TateICM.pdf)

Here solutions on the unramified quotient already give a compatible family. For $i\ge0$ put $S_i=\sum_{a=0}^{i-1}7^a$, including $S_0=0$. Since $v_3(7^{3^r}-1)=r+1$, $S_{3^r}$ is divisible by $3^r$. The valuation follows by induction from $v_3(7-1)=1$ and $v_3((1+u)^3-1)=v_3(u)+1$ for $3\mid u$ and $u\ne0$, by expanding the cube. The identity $S_{i+j}=S_i+7^iS_j$ shows that $S_i\bmod 3^r$ is periodic in $i$ with period $3^r$ and is a twisted cocycle. At level $r$, every primitive on the unramified quotient of degree $3^r$ is
$$
 b_{r,a}(i)=i^2+aS_i\pmod{3^r},\qquad a\in\mathbb Z/3^r .
$$
To see this, subtract the square and iterate the cocycle identity along the image of Frobenius. Its value there is $a$ because $S_1=1$. Conversely the identity and periodicity prove the equation for all pairs, including sums that wrap around. In these coordinates the transition is $a\mapsto a\bmod3^r$. Choosing $a=1$ at level one and $a=0$ at level two would give different values at Frobenius after reduction. Choosing $a=4\bmod 3^r$ at each level instead gives, at exponents $0,1,2,3$, the integral values $(0,5,36,237)$. Their reductions are $(0,2,0,0)$, $(0,5,0,3)$ and $(0,5,9,21)$ at levels one, two and three. At $(1,1)$ the differential is $7\cdot5-36+5=4$ and at $(1,2)$ it is $7\cdot36-237+5=20$. These give residues $(1,4,4)$ and $(2,2,20)$, respectively, through the three levels. The continuous integral primitive is $b+4S_{t(-)}$, with $S_i=(7^i-1)/6$ also valid for $i\in\mathbb Z_3$ by continuity. The formula describes the unramified solutions used in this calculation. At the completed-field consumer the proof uses the entire absolute group, including inertia.

#### The coefficient lattice and the differential [Lean, read]

Now let $\ell$ be any prime. Give $R=\mathbb Z_\ell$ its metric topology, and $R_r=\mathbb Z/\ell^r$ the discrete topology. Write $q_r:R\to R_r$ for reduction and $q_{s,r}:R_s\to R_r$ for the induced map when $s\ge r$. Thus $q_r=q_{s,r}q_s$. The kernel of $q_r$ is $\ell^rR$ and the cosets of these ideals form a neighbourhood basis. Two elements with the same residues at every positive level are equal. [A2, PadicCoboundaryOfDivisible.lean:7–36; Mathlib, PadicIntegers.lean:263–264,470–484 and RingHoms.lean:447–499,713–718](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

Let $G$ be a group with a topology. Use an $R$-linear representation $\rho$ on the one fixed lattice $R$, and $R_r$-linear representations $\rho_r$ satisfying $q_r(\rho(g)x)=\rho_r(g)q_r(x)$ for all $r,g,x$. We use inhomogeneous cochains, with $G^j$ in its product topology and continuity into the specified coefficient space. The degree-one differential is
$$
 \delta b(g,h)=\rho(g)b(h)-b(gh)+b(g).
$$
Write $Z^j$ for continuous cocycles and $B^2$ for the image of the continuous 1-cochains under $\delta$. Also $B^1$ is the image of $m\mapsto(g\mapsto\rho(g)m-m)$. The source defines $H^1$ using the intersection of $B^1$ with $Z^1$ inside all functions. For continuous actions $B^1$ is already contained in $Z^1$. Keeping the intersection makes the separation proof valid without an additional continuity hypothesis on the action. [A2, SeparatedDvrSecondCohomologyMem.lean:33–102](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

#### Lemma. Closed sets of finite-level primitives [Lean, read]

Suppose $H^1(G,R_r(\rho_r))$ is finite for a positive $r$. For any function $u:G^2\to R_r$, the set $P_r(u)=\{b:G\to R_r\mid b\text{ continuous},\ \delta_r b=u\}$ is finite and closed in the product $R_r^G$.

The image $B^1$ of the finite set $R_r$ is finite. Its intersection with $Z^1$ is finite, and the quotient of $Z^1$ by that intersection is finite. Each coset is a translate of the intersection, so $Z^1$ is finite. An empty $P_r(u)$ is closed. Otherwise choose one primitive $c_r$. Subtracting $c_r$ from any other primitive gives a continuous map with differential zero, precisely the degree-one cocycle identity. Conversely adding any such cocycle to $c_r$ gives a primitive of $u$. Thus $P_r(u)=c_r+Z^1$. This finite subset of a Hausdorff product is closed. It also has the discrete subspace topology. [A2, PadicCoboundaryOfDivisible.lean:38–65; Mathlib, QuotientGroup/Finite.lean:59–66 and Separation/Basic.lean:395–399](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

#### Theorem. Integral separation in degree two [Lean, read]

Assume $H^1(G,R_r(\rho_r))$ is finite for every $r>0$. Let $z\in Z^2(G,R(\rho))$. If every $q_r z$ has a continuous primitive, then there is one continuous $b:G\to R$ with $\delta b=z$. The archive invokes the theorem with the premise
$$
 \forall r\ge0\quad \exists w_r\in Z^2(G,R(\rho))\quad z-\ell^r w_r\in B^2(G,R(\rho)).
$$
This premise supplies the reduced coboundaries directly. Under joint continuity of the action and continuity of multiplication in $G$, the two premises are equivalent.

**Reduction and transitions.** With $\delta_r$ defined by $\rho_r$, applying $q_r$ to the three terms of $\delta$ gives $q_r\delta b=\delta_r(q_r b)$ for every function $b$. The coefficient maps $q_{s,r}$ intertwine the reduced actions, since each coefficient at level $s$ lifts to $R$ and both compositions agree there. They are continuous maps of discrete spaces. Hence pointwise reduction gives continuous transitions $P_s(q_s z)\to P_r(q_r z)$, whose graphs are closed in the finite products of the solution sets. These maps compose by reduction and need not be surjective, as the first calculation shows. A witness $c_n$ with $\delta c_n=z-\ell^n w_n$ gives a solution at every $1\le r\le n$, because precisely these lower powers divide $\ell^n$. [A2, PadicCoboundaryOfDivisible.lean:67–80,86–95](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

**Compact intersection.** Let $X=R^G$ have the topology of pointwise convergence on all functions. The continuous cochain group $C(G,R)$ is the subspace of continuous maps when equipped with this topology. The proof takes its intersection in $X$. The space $R$ is compact: the residue representatives give finite nets at every scale, and the closed unit ball in the complete field $\mathbb Q_\ell$ is complete. Tychonoff's theorem then gives compactness of $X$, even if $G$ itself is noncompact. For $n\ge1$, set
$$
 T_n=\bigcap_{1\le r\le n}(q_r^G)^{-1}\bigl(P_r(q_r z)\bigr),
$$
where $q_r^G$ acts on functions by composition. This map is continuous in the product topology by evaluation in each coordinate. The sets $T_n$ are closed by the lemma and decrease with $n$. Choose one solution at the highest level $n$. Lift it by the section taking least nonnegative representatives in $R$. The section is continuous because $R_n$ is discrete. Reduction of the lift to lower levels is the transition of the same solution, so the lift belongs to $T_n$. In the archive the supplied $c_n$ from the displayed divisibility premise already serves as this lift. Thus the $T_n$ have the finite intersection property. The nested-closed-set theorem, applied to $T_1$ and the closed subsets $T_n$, provides $b\in\bigcap_{n\ge1}T_n$. Its reductions are the compatible primitives. [A2, PadicCoboundaryOfDivisible.lean:81–101; Mathlib, Padics/ProperSpace.lean:42–58 and Compactness/Compact.lean:340–347,1165–1187](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

**Continuity and the differential at the limit.** For any $g\in G$ and $\epsilon>0$, choose $r>0$ with $\ell^{-r}<\epsilon$. The continuous map $q_r b$ is constant on a neighbourhood of $g$. On this neighbourhood $\lVert b(g')-b(g)\rVert\le\ell^{-r}$, so $b$ is continuous in the original metric topology. At a fixed $(g,h)$ every term of $\delta b$ is obtained by evaluation at $g,h,gh$ and continuous linear operations on $R$, including the fixed action $\rho(g)$. Consequently this expression commutes with a pointwise limit. The archive checks it residue by residue: for every $r>0$, $q_r(\delta b(g,h))=\delta_r(q_r b)(g,h)=q_r(z(g,h))$. Separation gives the integral equality. At $r=0$ the coefficient ring is the zero ring, so its equality is automatic. [A2, PadicCoboundaryOfDivisible.lean:21–36,100–113](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

**From a reduced primitive to divisibility.** For the converse under the stated continuity assumptions, lift a primitive of $q_r z$ by the section of $q_r$ to a continuous $c_r:G\to R$. Then $z-\delta c_r$ is a continuous cocycle, since the action and multiplication make $\delta c_r$ continuous and $d_2\delta=0$. Its values lie in $\ell^rR$. Multiplication by $\ell^r$ is a homeomorphism from $R$ to that ideal with its subspace topology. Dividing gives a continuous $w_r$ with $d_2 w_r=0$ by linearity and cancellation of $\ell^r$. This gives exactly the displayed premise. At $r=0$ take $w_0=z$. [A2, PadicIntTwoCocycleEqPowSmulOfReductionCoboundary.lean:7–45](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

#### The integral Tate coordinate [Lean, read]

In `int_span` fix the same $G$, continuous character $\chi:G\to R^\times$, positive scalar action $\rho(g)a=\chi(g)a$, common generator $c$ of §10.4.14 and finite $H^1$ of §10.4.15. For a continuous cocycle $w$, the generator at each level writes $q_r w=q_r(c)x_r+\delta_r b_r$. Reduce a level-$s$ expression to $r\le s$ and subtract the level-$r$ expression. Injectivity of the generator at level $r$ forces $q_{s,r}(x_s)=x_r$. It leaves $b_r-q_{s,r}b_s$ free to be a cocycle. The least integer representatives of the scalar coordinates form a Cauchy sequence, because their differences from level $r$ onward belong to $\ell^rR$. Completeness yields $x\in R$ with these residues. The function $z=w-xc$ is a continuous cocycle. The $b_r$ witness that $q_r z$ is a coboundary, so the division lemma supplies the exact divisibility premise and the intersection proof supplies one $f$ with $\delta f=w-xc$. The scalar coordinate is unique by the finite generator tests, while primitives with that coordinate differ by a continuous 1-cocycle. [A2, IntegralTateH2Top.lean:21–118](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

The consumer `tateH2OAt_of_fund` works on the period group `GK K` for a finite $K/\mathbb Q_\ell$. It keeps the same character under inclusion into the coefficient field $L_f$. The coefficient lattice $O=O_{L_f}$ is finite free over $R$. Choose an $R$-basis of $O$ and extend it to a $\mathbb Q_\ell$-basis of $L_f$. Ambient field continuity of the $O$-valued cocycle implies continuity of every integral coordinate, by the field coordinate maps and the embedding $R\hookrightarrow\mathbb Q_\ell$. Each coordinate sees the same $\chi$, $c$ and $H^1$ supply. Apply `int_span` coordinate by coordinate and reassemble the scalar $a\in O$ and primitive $f:G\to O$ in the original basis. A finite sum of the continuous coordinates times basis vectors is continuous in $L_f$, and the equation survives by scalar linearity and the embedding of $O$. The separate `int_inj` applies to each coordinate if $ac$ is an integral coboundary, so $a=0$ in that case. The resulting $O$-linear equivalence from integral degree-two cohomology to $O$ is the inverse of $a\mapsto[ac]$. The wrapper `admH2_of_duality` passes one fundamental tuple for the original $K$, together with the coefficient extension of the given place. [A2, IntegralTateH2Top.lean:107–118,126–138,145–294](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

For a nonzero witness in this signature, take $K=L_f=\mathbb Q_3$ and the named period datum at $3$. Let $i$ denote the continuous unramified quotient to $\mathbb Z_3$, with arithmetic Frobenius sent to $1$, and use the actual positive cyclotomic character on the whole group. Put $b(g)=i(g)^2$ and $w=c+\delta b$ for the supplied generator $c$. Then the unique scalar is $1$ and $b$ is an integral primitive of $w-c$. For any lift $s$ of arithmetic Frobenius, $(w-c)(s,s)=\chi(s)-3$, a unit of $R$. This uses only that $\chi(s)$ is a unit. At residue characteristic $3$ the unramified quotient supplies the argument of $b$. Its differential uses the full cyclotomic character, including the action of inertia. [A2, ExistsLocalPrimeAinf.lean:281–285 and ExistsFundamentalTwoCocycleOfLocalTateDuality.lean:16–55](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

#### What the hypotheses do [Expository]

**Without the finite-layer closedness supply.** Let $G=\prod_{n\ge1}\mathbb Z/3^n$ with the product topology and trivial action on $\mathbb Z_3$. Write $i_n(g)$ for the least nonnegative integer representing the $n$th coordinate. The cocycle
$$
 z(g,h)=\sum_{n\ge1}3^n\left\lfloor\frac{i_n(g)+i_n(h)}{3^n}\right\rfloor
$$
is continuous because the sum converges uniformly. Each summand is $\delta i_n$. Modulo $3^r$, the finite sum $\sum_{n<r}i_n$ is a primitive of the reduction. The tail divided by $3^r$ is again a continuous cocycle, so the divisibility premise also holds. On the $n$th cyclic subgroup any integral primitive must equal $i_n$, since the difference is a homomorphism from a finite group into the torsion-free lattice. In particular its value on the $n$th coordinate generator is $1$ and its value at zero is $0$. Those generators converge to zero in $G$, ruling out a continuous primitive. The coordinate maps to $\mathbb Z/3$ give infinitely many distinct classes in $H^1$ since $B^1=0$. Closedness also fails at level one: the partial sums $\sum_{n\le m}i_n\bmod3$ lie in $P_1(0)$, and a cluster point in the compact function product takes value $1$ at each coordinate generator and $0$ at zero. This example retains both the compact group and the compact coefficient lattice.

**Without completion of the coefficient lattice.** Replace $R$ by $A=\mathbb Z_{(3)}$ with its $3$-adic metric and use $G=\mathbb Z[1/3]$ discrete with trivial action. Let $a\in\mathbb Z_3$ be the root of $a^2=7$ with $a\equiv1\pmod3$, obtained by lifting the simple root modulo $3$. It is irrational since $7$ is not a rational square. If $a_n$ is its least representative modulo $3^n$, define $\bar b(m/3^n)$ in $\mathbb Z_3/A$ as $m(a-a_n)/3^n+A$. Enlarging $n$ by one changes the representative by an integer multiple of $m$, because $a_{n+1}-a_n$ is divisible by $3^n$. Addition at a common denominator shows that $\bar b$ is a homomorphism. Pick a lift $B:G\to\mathbb Z_3$ with $B(1)=a$ (use denominator $1$ there) and set $z=\delta B$. Its values lie in $A$ and all cochains on this discrete group are continuous. Reduction of $B$ gives a primitive at each level, and lifting the reduced primitive to $A$ and dividing the remaining cocycle by $3^r$ also gives an $A$-valued divisibility witness. Every finite $H^1$ here is zero, since $G$ is $3$-divisible and the coefficients are killed by $3^r$. If $b:G\to A$ were an integral primitive then $B-b$ would be a homomorphism into $\mathbb Z_3$. Its values lie in every $3^r\mathbb Z_3$ by $3$-divisibility, so $b(1)=a$, impossible. This is failure of completion in a totally bounded coefficient ring with the same finite quotients. The compactness of the coefficient lattice in the archive includes that completion. [Milne, *Algebraic Number Theory*, §7, Proposition 7.31](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

**Without the topology detected by the reductions.** Take $G=\mathbb Z_3$ with its usual topology and trivial action, and let $i(g)$ be its first digit. The carry $z(g,h)=\lfloor(i(g)+i(h))/3\rfloor$ has compatible locally constant primitives modulo $3^r$ from the function $(i(g)-g)/3$. Its differential is exactly $z$. If the target $\mathbb Z_3$ is given the discrete topology, a continuous primitive would factor through some $\mathbb Z/3^N$ with $N\ge1$. Indeed the open constant neighbourhoods give a finite coset cover of the compact domain, which can be refined by one common modulus. Summing its differential at $(k,1)$ over this quotient telescopes to $3^N b(1)$. The sum of the carries is $3^{N-1}$. This would force $3b(1)=1$, impossible in $\mathbb Z_3$. The reduced solution sets are finite since continuous homomorphisms from $\mathbb Z_3$ to $\mathbb Z/3^r$ are determined by the dense generator $1$. Lifting each reduced primitive by integer digits and dividing the remaining locally constant cocycle still gives the divisibility witnesses with the discrete target. The example shows why continuity into the integral target must be recovered using its actual topology.

#### Attribution and scope

For a profinite $G$ with continuous action, Jannsen's Theorem 2.2 identifies continuous cochain cohomology for the inverse limit of a Mittag–Leffler system of discrete modules with the derived cohomology of that system. Here the coefficient transitions are surjective, and finiteness of $H^1$ at a fixed level makes the descending images into that group stabilize. Jannsen's sequence (2.1) and Lemma 1.15 therefore identify $H^2_{\mathrm{cont}}(G,R(\chi))$ with the inverse limit of the finite-layer $H^2$. This covers injectivity in the arithmetic setting of this section. The archive gives the primitive directly by a compact intersection and works at that step with an arbitrary topological space on the group and compatible actions. The local finiteness on the cyclotomic layers is the input from Tate, with the order of each finite module invertible in the characteristic-zero field, even at residue characteristic $\ell$. [Jannsen, *Continuous étale cohomology*, pp. 213, 215–216](https://epub.uni-regensburg.de/26684/1/jannsen12.pdf) · [Tate, ICM 1962, Theorem 2.1, p. 289](https://math.stanford.edu/~conrad/BSDseminar/refs/TateICM.pdf)

The reading here covers the separation proof, its direct topological supplies, the division lemma and the integral coordinate consumer at author-level local R3. Finite local $H^1/H^2$, the same-positive-level descent, the common generator, and local Tate duality enter with their existing scopes. Independent audit, kernel replay, compiled reachability from `Main.riemannHypothesis` and peer review have separate evidence requirements. Part C and the full supply of `LocalH2Injective.h2_inj` remain outside this local result. [Pinned declarations](../sources/SOURCES.md#chapter-10-compatible-integral-primitives)

### 10.4.17 Recovering invariant length from torsion-level counts

In a finite-coefficient duality calculation the right-hand side is often a count of invariants, while the integral calculation needs a module length. The comparison uses two filtrations. On the integral side we take quotients by successive powers of the prime. On the torsion side we take the elements killed by those powers inside one fixed invariant module. The source behind §10.4.16 supplies separation for the integral cohomology module as part of its finite-generation argument. The compactness proof, the continuous division lemma and the integral coordinate result `int_span` are available in that subsection. Here we start with the resulting module and the counts required by the length comparison. [Pinned source ledger](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length)

#### Two calculations over the 3-adic integers

Write $R=\mathbb Z_3$, $C_j=R/3^jR$ with $C_0=0$, and $B=\mathbb Q_3/R$. Use the discrete infinite cyclic group with generator $s$. In both examples the generator acts on the three coordinates by $(x,y,z)\mapsto(x,4y,-z)$. Since $4$ and $-1$ are units, these formulas define actions of the whole group. Fix $u_r=2$ for odd $r$ and $u_r=1$ for even $r$.

**Finite mixed torsion.** Take $A=C_3\oplus C_2\oplus C_1$, $X=C_3\oplus C_1$, and set $a=\min(r,3)$, $b=\min(r,2)$, $c=\min(r,1)$. Use $N_r=C_a\oplus C_b\oplus C_c$ with the displayed action, and embed it by
$$
 \iota_r(i,j,k)=(u_r3^{3-a}i,\ 3^{2-b}j,\ 3^{1-c}k).
$$
In $C_d$, the elements killed by $3^r$ are the multiples of $3^{d-\min(r,d)}$. Multiplication by the displayed factor embeds the corresponding smaller cyclic module, and $u_r$ is invertible. This verifies injectivity, the full image and equivariance, including the zero module at $r=0$. The fixed-point equations on $N_r$ are $3j=0$ and $2k=0$. Thus $j$ is a multiple of $3^{b-\min(1,b)}$ and $k=0$, while $i$ is arbitrary. For $r>0$ the image on fixed points is exactly the set of triples $(x,3t,0)$ with $3^r x=0$ in $C_3$ and $t\bmod 3$. In particular at $r=1,2,3$ the first coordinates range over multiples of $9,3,1$ in $C_3$ respectively (the odd-level multiplier $2$ permutes the residues). The fixed-point counts are $9,27,81$, staying at $81$ for $r\ge3$. On the left, $X/3^rX\simeq C_a\oplus C_c$, with those same counts for every positive $r$. The original fixed module is $C_3\oplus 3C_2\oplus 0$, of length $3+1=4$, as is $X$. Each $C_j$ has $j$ successive quotients of order $3$ in its chain of powers of $3$.

**A free summand on the quotient side.** Take $A=B\oplus C_2\oplus C_1$ and $X=R\oplus C_1$. Use $N_r=C_r\oplus C_b\oplus C_c$ and
$$
 \iota_r(i,j,k)=(u_ri/3^r+R,\ 3^{2-b}j,\ 3^{1-c}k).
$$
The first component is unchanged by a different representative modulo $3^r$ and is zero in $B$ exactly when $i=0$ in $C_r$. A coset $x+R$ belongs to $B[3^r]$ exactly when $3^rx$ is integral, so the first image is the whole $B[3^r]$. The other two images and the action are as in the finite example. The fixed coordinates are again arbitrary $i$, $3j=0$ and $k=0$, so the positive layer count is $3^{r+1}$, giving $9,27,81,243$ at $r=1,2,3,4$. Its image is $B[3^r]\oplus 3C_2\oplus0$. On the left $X/3^rX\simeq C_r\oplus C_1$ for every $r>0$. The strictly falling chain of powers in the free summand and the strictly growing chain $B[3^r]$ show that both lengths are infinite. The two generators of $X$ generate it as an $R$-module, and its free summand has infinitely many elements.

#### The fixed objects and the length comparison [Lean, read]

Let $\ell$ be prime, $R=\mathbb Z_\ell$ and $R_r=\mathbb Z/\ell^r\mathbb Z$ for $r\ge0$. Let $\Gamma$ be a group, with the topology carried in the archive's ambient signature. Only its action enters the argument. Use one finitely generated $R$-module $X$ and one $R$-module $A$ with an $R$-linear action $\sigma$ of $\Gamma$. Require that each $a\in A$ be killed by some $\ell^r$, where the exponent can depend on $a$. Put $A[\ell^r]=\{a\in A:\ell^ra=0\}$. For every natural $r$, take a finite $R_r$-module $N_r$, an $R_r$-linear action $\tau_r$ of the same group, and an injective additive homomorphism $\iota_r:N_r\to A$. The two map requirements are
$$
 \operatorname{im}\iota_r=A[\ell^r],\qquad
 \iota_r(\tau_r(g)n)=\sigma(g)\iota_r(n)\quad(g\in\Gamma,\ n\in N_r).
$$
Here $H^0$ denotes the submodule fixed by all $g\in\Gamma$, and $\operatorname{lpow}(X,r)$ is the image $\ell^r X$ of multiplication by $\ell^r$. Suppose that for every **positive** $r$,
$$
 \#(X/\ell^rX)=\#H^0(N_r).
$$
Then $\operatorname{length}_R X=\operatorname{length}_R H^0(A)$. Length here is Lean's `Module.length`, valued in the extended natural numbers $\mathbb N\cup\{\infty\}$, with zero length for the zero module. `Nat.card` uses $0$ on infinite types. In this hypothesis the right side is a finite count of a submodule containing zero, so it is at least $1$. The equality in Lean therefore gives a genuine finite quotient count on the left. The level $r=0$ has zero coefficient ring and yields singleton modules where relevant. [A2, LengthEqLengthInvariantsOfTorsionLevels.lean:28–48,137–157](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length)

**Proof, first compare invariants at each level.** Write $Y=H^0(A)$ and $P_r=Y[\ell^r]$. Send $n\in H^0(N_r)$ to $\iota_r(n)$. Equivariance makes the image fixed, and its membership in $\operatorname{im}\iota_r$ gives $\ell^r\iota_r(n)=0$. For $a\in P_r$, the full image condition gives an $n\in N_r$ with $\iota_r(n)=a$. For each $g$, equivariance gives $\iota_r(\tau_r(g)n)=\sigma(g)a=a=\iota_r(n)$. Injectivity forces $\tau_r(g)n=n$. The unique preimage defines the inverse, and each composite returns the original element. This gives an additive bijection at each $r$. Thus $P_r$ is finite and its count equals $\#(X/\ell^rX)$ for every $r>0$. The two filtrations used below are already defined on $X$ and $Y$. The proof only uses the given map at the exponent being compared. The exact images would also allow one to transport inclusions through $\iota_s^{-1}\iota_r$ for $r\le s$ on the corresponding images if transition maps were desired. The odd-level multipliers in the examples illustrate the freedom to choose coordinates independently at each level. [A2, same file:147–157](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length)

**Next, check the filtrations.** The submodules $\ell^r X$ decrease because $\ell^s=\ell^r\ell^{s-r}$ for $s\ge r$. Their intersection is zero by Krull's intersection theorem, as used by `lpow_sep`. The ring $R$ is a Noetherian local ring with maximal ideal $(\ell)$, and $X$ is finitely generated. Thus the powers of this proper ideal applied to $X$ have intersection zero. The $P_r$ increase by the same divisibility of powers. Their union is $Y$ because the elementwise torsion hypothesis applies to every fixed element of $A$. Both separation and exhaustion hold on any tail of levels by monotonicity. [A2, same file:30–48,147–150](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length) · [Stacks Project, Lemma 10.51.4](https://stacks.math.columbia.edu/tag/00IP)

**Finally, use the counts.** The general production lemma uses a decreasing separated family $L_r$ on $X$, an increasing exhaustive family $P_r$ on $Y$, and equality of the finite counts $\#(X/L_r)=\#P_r$ for every $r\ge c$. Here $L_r=\ell^rX$ and $c=1$. If those counts are bounded, their nonempty set of integer values has a maximum, achieved at some $r_0\ge c$. For any $s\ge r_0$ the inclusion $P_{r_0}\hookrightarrow P_s$ is injective, so $\#P_s\ge\#P_{r_0}$. Maximality gives equality. The inclusion is bijective by finiteness, and exhaustion now gives $P_{r_0}=Y$. The projection $X/L_s\to X/L_{r_0}$ is surjective between finite modules of equal cardinality. It is therefore injective, and its kernel $L_{r_0}/L_s$ vanishes. Hence $L_s=L_{r_0}$ at every $s\ge r_0$, and separation gives $L_{r_0}=0$. At this one level the counts are the cardinalities of $X$ and $Y$ themselves.

Every simple $R$-module is $R/(\ell)\simeq\mathbb F_\ell$. Indeed a nonzero element generates a simple module, and its annihilator is maximal. A finite module has a composition series because its lattice of submodules is finite. For any finite-length module a series with $d$ simple quotients gives a finite underlying set of size $\ell^d$, by counting the cosets at every step starting with the singleton zero module. The number $d$ is the module length. Thus the bounded case gives equal finite lengths by injectivity of the powers of $\ell$. If the counts are unbounded, a finite $X$ would bound the quotient sizes by $\#X$ and a finite $Y$ would bound the subgroup sizes by $\#Y$. Both modules are therefore infinite sets. The composition-series calculation forces both lengths to be $\infty$. This proves the comparison on the entire range of `Module.length`. [A2, PadicIntLengthEqOfCardQuotientEqCardSubmodule.lean:8–87 and ExistsLengthEqAndCardEqPowOfIsFiniteLength.lean:5–36](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length)

#### Which hypotheses carry the comparison

In the finite example keep $A,\sigma,N_r,\tau_r,\iota_r$ and replace $X$ by $C_2\oplus C_1$. Its counts at $r=1,2$ are still $9,27$, but at $r=3$ its count stays $27$ while the fixed-point count rises to $81$. The lengths are $3$ and $4$. More generally, at any prescribed positive layer $m$ the cyclic modules $C_m$ and $C_{m+1}$ give the same count $3^m$ on the quotient and torsion sides, with trivial action and the full kernel embedding $i\mapsto 3^{m+1-\min(r,m+1)}i$ into $C_{m+1}$. Their lengths are $m$ and $m+1$.

Keep $X=C_2\oplus C_1$ and the original finite $A$ and action, but replace $N_r$ by the submodule of the original $N_r$ cut out by $3^{\min(r,2)}i=0$ in its first coordinate. Restrict the original $\iota_r$ and $\tau_r$ to it. The first-coordinate image is contained in $3C_3$ and still supplies exactly $3^{\min(r,2)}$ choices at every positive $r$. The other fixed coordinates have $3$ choices in total. All positive count equalities now hold, and the maps are injective and equivariant. At $r=3$, the fixed point $(1,0,0)\in A[27]$ lies outside the image. The lengths remain $3$ and $4$. This is the lifting step in the proof that uses the full image equality.

#### Where the archive uses the length [Lean, read]

Both direct consumers use $A=\mathbb Q_\ell/\mathbb Z_\ell$ with scalar action $\chi^{-e}$. Here $\chi$ is the integral cyclotomic character in the original data $D$, $e$ is an integer, and $N_r$ is the $R_r$-linear dual of the rank-one coefficient module with character $\chi^{e+1}\bmod\ell^r$, equipped with the cyclotomic twist. Its action on a functional $\varphi$ sends its value at $m$ to $\bar\chi(g)\varphi(\bar\chi(g)^{-(e+1)}m)$. Evaluation at $1$ gives an additive coordinate on the dual, because $\varphi(m)=m\varphi(1)$. The original map is
$$
  \iota_r(\varphi)=\widetilde{\varphi(1)}/\ell^r+\mathbb Z_\ell .
$$
Changing the lift changes this fraction by an element of $R$. The denominator calculation from the second example, with $\ell$ in place of $3$, gives the exact image and injectivity. The scalar at evaluation is $\bar\chi^{-e}$, giving equivariance. All cosets of $A$ are killed by some power of $\ell$ because each representative has finite negative valuation or is integral. [A2, QzTorsionZmodEmbedding.lean:42–99 and LengthEqLengthInvariantsOfTorsionLevels.lean:165–198,263–264](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length)

- In `local_tate_duality_h2_limit`, restrict the same representations to the decomposition group at the chosen $v\mid\ell$. The module $X$ is integral $H^2$ with twist $e+1$ at that place. `local_lim` supplies finite generation and the surjective reduction map with kernel $\ell^rX$. The quotient count is the count of finite-coefficient $H^2$, which `local_zr` identifies with the count of fixed points of the finite twisted dual. The named inputs are `LocalFinitenessK` and `LocalTateDualityK`. In the reduction argument the former supplies finite $H^1$ at all positive levels, finite $H^2$ at level one, and vanishing $H^3$ at level one. The separated-module argument uses the continuous primitive theorem of §10.4.16. [A2, LengthEqLengthInvariantsOfTorsionLevels.lean:75–135,202–229,265–302](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length)
- In `ptCokerAt`, $X$ is the cokernel of the integral localization map from global $H^2$ of twist $e+1$ to the product over the places in $D.S$. The product is finitely generated by `finite_pi`, and so is its quotient. The group on $A$ and all $N_r$ is now the same global group $G_S$. The quotient comparison in `cok_ker` and the exact, surjective end of the finite nine-term sequence give the count in `card_cok`, using the size of the finite dual. The wrapper retains `PTCase` ($\ell\ne2$ or the field is totally imaginary), the two local inputs, the positive-layer `NineTermExact` and `ShaDual` inputs, and the global degree-three vanishing input at level one. Both length results are passed to `vFormula_of_classicalTheorems`. That formula takes a separate $\mathrm{Sha}$ length equality. [A2, same file:327–397; GaloisCohomologyLength/Formula.lean:15–24](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length)

For an instance on the original arithmetic coefficients, choose $\ell=3$, $F=\mathbb Q$, an algebraic closure and the resulting data $D$ with $S=\{(3)\}$. Take $e=0$ and the local consumer at $(3)$, with its named local inputs. Then $A=\mathbb Q_3/\mathbb Z_3$ has trivial twist on the entire decomposition group, and the twisted action on each original dual $N_r$ is also trivial by the evaluation formula. The class $1/3^r+\mathbb Z_3$ is the image of the functional with value $1$ at $1$ and has order $3^r$. Local duality and reduction on the original $X=H^2$ of twist $1$ give $\#(X/3^rX)=3^r$. Both lengths are infinite. The layer count at $r=1$ already ensures $X$ is nonzero. [A2, Statement.lean:54–73,104–106; LdataNonempty.lean:12–50 and LengthEqLengthInvariantsOfTorsionLevels.lean:175–198,278–302](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length)

The local count and the finite global exact-sequence tail are classical Tate and Poitou–Tate inputs. The algebra uses Krull separation and the Jordan–Hölder length calculation. The two-filtration proof here follows Alpöge and Claude's archive, at author-level local R3 for the stated bodies and handoffs. The exact examples and the two hypothesis tests are the book's exposition. The source ledger records the retained arithmetic inputs and the separate evidence status of independent audit, Lean kernel replay, compiled reachability from the Main declaration and peer review. [Tate, ICM 1962, Theorems 2.1 and 3.1](https://math.stanford.edu/~conrad/BSDseminar/refs/TateICM.pdf) · [Source ledger](../sources/SOURCES.md#chapter-10-torsion-level-counts-and-invariant-length)

## 10.5 Remarks, formalization notes, and Masullo's counterpart

### 10.5.1 Import-cone anatomy of node P11

Our exact transitive import-cone audit (`notes/proof-map.md`) reveals a clean three-tier split inside
node **P11**:

| File | Import cone | Reading level & tag | Role |
|---|---|---|---|
| `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean` | **207** | `R3` (`[Lean, read]`) | Defines ramification-normalized lengths `lenR`, signed lattice indices `sIdx`, and states `TwistingCharacterExistence`. |
| `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean` | **311** | `R3` (`[Lean, read]`) | Proves `vvRecord` and `divinN_of_hypV`, converting `HypV` + `LinkN` + `SmallLevelRankEq` into `DIVinN`. |
| `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean` | **3,287** | `R3` (`[Lean, read]` for this file, `CutDetOrd.main`, and `GlobalArtinReciprocity`'s `Prop` in Ch. 18; `R3` for the imported DVR determinant, block-determinant, GMA Fitting, peeling, $\rho$-block Selmer, cyclotomic-$Ш^1$ and class-number lemmas of §10.4.5; `R2` `[Lean]` for the statement-level sub-lemmas listed at the end of §10.4.5; `[Open]` for `globalArtinReciprocity`'s 1,015-module proof cone) | Proves `CutCoreUnit.main`, reducing congruence valuation to $\mathrm{sPi} + \sum \mathrm{shaLen} + v_\ell(h_E) + \text{tame}$. |

### 10.5.2 Why cyclotomic twists $\mathbb Q_\ell / \mathbb Z_\ell(-e)$ appear up to $e < R.t \le \lfloor x^{400} \rfloor$

Readers who wondered in Chapter 4 why `VVle E ⌊x^400⌋₊ (exp(x^eps / 2))` summed over $1 \le e < \lfloor x^{400} \rfloor$
now have the exact structural explanation [Expository]:

- In the chain of $m \asymp x^{1/2}$ theta lifts over a host field of degree $[E : \mathbb Q] \asymp x^{2+8\varepsilon}$
  and word parameter $k \asymp x^{9/2 + 10\varepsilon}$, the Hodge–Tate / endoscopic cyclotomic block
  dimension $t = R.t$ grows polynomially in $x$ — bounded in
  `src/Development/AutomorphicArithmetic/CharacterBoxes/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5` (Chapter 4, Section 4.2.2) by $10{,}708\,x^{399.67} \le \lfloor x^{400} \rfloor$
  whenever $\varepsilon < 1/52$ [Lean, read]!
- Each of the $t - 1$ nontrivial cyclotomic blocks $1 \le e < R.t$ in `CutCoreUnit.main` contributes
  one summand $\mathrm{shaLen}(E, \ell, e)$, which is why `VWin` must control twists all the way up
  to $\lfloor (x')^{401} \rfloor$!

### 10.5.3 Masullo's counterpart

Masullo's draft *The Music of the Primes* has **no counterpart** to Hecke congruence modules,
generalized matrix algebras, Galois representations, Bloch–Kato Selmer groups, class numbers $h_E$, or
Tate–Shafarevich groups $Ш^1$ [Expository]. Masullo works purely in complex/functional analysis on
$\mathbb A_F^\times / F^\times$ without $\ell$-adic coefficients or Galois cohomology; the appearance
of $Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e)\bigr)$ inside a proof of the classical
Riemann Hypothesis is unique to Alpöge's arithmetic Stepanov engine.

---

## 10.6 Lean counterpart for this chapter

| Declaration | File:line | Mathematical content / role in Sections 10.3–10.4 | Tag |
|---|---|---|---|
| `IsOrthogonalIdempotentDecomposition` | `src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:18` | Definition 10.1: orthogonal idempotents `S.eB` (cyclotomic block of rank $t = R.t$) and `S.e1` (rank $1$), splitting `S.e` into cuspidal `rhoO` (`Fin R.r`) + $t$ cyclotomic slots, and rank-$1$ projector `Eel` with unit `del51`. | [Lean, read] |
| `value_mem_ccOff`, `exists_ne_zero`, `GlobalTheory.CutDetOrd.main`; statement wrapper | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:15,37,59`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBoundStatement.lean:8` | Proposition 10.1: produces a nonzero off-diagonal matrix evaluation away from `Z i` (`exists_ne_zero`) and bounds $\operatorname{len}_{\mathcal O}(\mathcal O/\mathrm{ccOff}(\pi))$ by cuspidal + cyclotomic $1$-cocycle lengths via GMA `Rel`. | [Lean, read] |
| `ccOff_univ`, `GlobalTheory.CutCoreUnit.main` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:24,44` | Theorem 10.2: bounds congruence valuation `vcc` by $\mathrm{sPi} + \sum_{1 \le e < R.t} \mathrm{shaLen} + v_\ell(h_E) + \text{tame}$ (assuming `GlobalArtinReciprocity`; import cone 3,287). | [Lean, read] |
| `lenR`, `sIdx`, `TwOK`, `RFam`, `ABHyp`, `partAB`, `TwistingCharacterExistence`, `GoodTw`, `TwistTheoremAtIndex`, `admitted`, `Stmt` | `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:64,68,81,98,125,150,166,219,233,324,329` | Definition 10.2: ramification-normalized DVR lengths `lenR`, signed lattice index `sIdx`, and `TwistingCharacterExistence` (import cone 207). | [Lean, read] |
| `twist_kills_selmer` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:8` | Proposition 10.3(1) and Proposition 10.12: at a chosen twist satisfying `TwGoodAt`, bounds $\mathrm{sPi}$ by $\nu_L + \varepsilon_L$ and the tame sum (`KillAt`). | [Lean, read] |
| `GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound`; `GlobalTheory.DetGen.exists_C_mul_primitive`, `length_quot_le_of_coeff_prod`, `addVal_det_le_length`, `exists_family_span`, `exists_relations`, `length_quot_le_sum_length` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DeterminantLemmaDiscreteValuationRingQuotientLenStatement.lean:6`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DeterminantLemmaDiscreteValuationRingQuotientLen.lean:20,47,76,165,187,259` | Lemma 10.5: DVR determinant–length inequality (Gauss content, Smith normal form, solution modules). | [Lean, read] |
| `det_one_add_smul_blk_mem`, `GlobalTheory.BlockDet.main`; `GlobalTheory.BlockDetPoly.main` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetOneAddSmulBlkMem.lean:21,89`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CMemCoeffSub.lean:99` | Lemma 10.6: Hecke-valued determinants pass to block matrices (nilpotent Schur-complement induction). | [Lean, read] |
| `GlobalTheory.CutDet.length_sol_le`, `det_blocks`, `exists_conj`, `exists_homs`, `det_generic_blocks`, `det_generic_eq_zero`, `spanAlg`, `exists_gens`, `blockHom` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeQuotientLeCocycleSpanDeterminant.lean:77,144,167,196,254,295,321,346,369` | Proposition 10.7 (Fitting inclusion into $\mathrm{ccOff}$) and Lemma 10.8 (solutions inside cocycle modules). | [Lean, read] |
| `GlobalTheory.Cut.Peel.main`; `GlobalTheory.Cut.CountL.main`; `GlobalTheory.Cut.SelClass.main`; `GlobalTheory.Proof.LocalGlobalSelmer.main` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthEqInfKerAddMap.lean:52`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthGlobalCocyclesLeSumPlacesOver.lean:102`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCocyclesLeCoboundariesAddSelmer.lean:81`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocalGlobalSelmer.lean:7` | Lemma 10.9 (peeling $Q_i$) and the $\rho$-block local–global Selmer comparison. | [Lean, read] |
| `GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha`; `GlobalTheory.Cut.ShaBound.main`; `GlobalTheory.UnramHom.length_le_classNumber` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCyclotomicBlockCocyclesLeShaStatement.lean:6`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCyclotomicBlockCocyclesLeSha.lean:372`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IndexDvdClassNumber.lean:172` | Lemma 10.10 (block $e = c - 1$ into $Ш^1$, factor $\operatorname{len}(\mathcal O/\ell)$) and Lemma 10.11 (trivial block bounded by $v_\ell(h_E)$). | [Lean, read] |
| `TwGoodAt`; `SignatureChoiceCondition`, `KillAt`; `GlobalTheory.TwSys.Cheb`, `GaloisSideTwistedSelmerAuxiliaryPrimes` | `src/Formalism/SharpRestriction/LevelLetterCocycles/TwGood.lean:196`; `src/Formalism/SharpRestriction/LevelLetterCocycles/JointConditionsZpowers/CommutingEndomorphismCondition.lean:33,45`; `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:11,70` | §10.4.6: the good-twist hypothesis, the Selmer-bound conclusion, and the Chebotarev and auxiliary-prime `Prop`s. | [Lean, read] (definitions and top-level proofs) |
| `GlobalTheory.export_of_inputs`; `admAB_of_toric_parts`; `abstract_form_of_lattice_run`; `export_at_setting` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:493`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:355`; `src/Formalism/SharpRestriction/LevelLetterCocycles/LinearIndependentSmulOfNeZero.lean:2183`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:456` | §10.4.6: producers and transport of `TwistingCharacterExistence`; §10.4.7.1 reads the transport with its helpers and the producers' `partAB` steps. | [Lean, read] (transport, `partAB` steps); [Lean] (`PropABCD`, `SelmerSeriesChoice`, `Pack.Main`) |
| `export_at`; `isLatIn_of_index_le`; `index_unscale`; `index_extend`; `abHyp_fam` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLatInOfIndexLe.lean:371,164,153,130,297` | §10.4.7.1: Theorem 10.13g, Lemmas 10.13d–10.13f, Proposition 10.13h. | [Lean, read] |
| `sIdx_add_and_mono`; `sIdx_baseChange` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthCommensurableOfIsLatIn.lean:54`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LenRBaseChangeSubquotient.lean:70` | §10.4.7.1: Lemma 10.13c. | [Lean, read] |
| `twistModule_all_character_powers_of_admissible` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistModuleAllCharacterPowersOfAdmissible.lean:17` | §10.4.7.1: Theorem 10.13i, the lattice clauses at every coprime power. | [Lean, read] |
| `PropABCD`; `propABCD_of_rel` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:119`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:293` | §10.4.7.1: Proposition 10.13j (definition); §10.4.7.2: Theorem 10.13p (producer). | [Lean, read] |
| `PropE`; `GlobalTheory.ToricFactor.propE` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:31`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PropEOfAdmissible.lean:420` | §10.4.7.3: Theorem 10.13y, the theta clause `partC` with a unit constant term. | [Lean, read] |
| `IsotypicPartsInternalDirectSum`; `GlobalTheory.IntSup.admInt_of_sup` | `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:245`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmIntOfSupLaws.lean:31` | §10.4.7.3: Theorem 10.13z, the isotypic lattice `Mall` from the sup laws. | [Lean, read] |
| `GaloisSideTwistedSelmerAuxiliaryPrimes`; `galois_twisted_selmer_auxprimes_of_matrix_and_bounds` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:70`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisTwistedSelmerAuxprimesOfMatrixAndBounds.lean:47` | §10.4.7.4: Theorem 10.13ae, one family of auxiliary places for `Steps` and the Selmer polynomials. | [Lean, read] |
| `SelmerLengthsByDeterminant`; `twisted_selmer_lengths_eq_determinant_valuation`; the `partAT` step of `admissibleIndexBoundAllPowers_of_conditions` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:51`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistedSelmerLengthsEqDeterminantValuation.lean:375`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdmissibleIndexBoundAllPowersOfConditions.lean:188–197` | §10.4.7.4: Proposition 10.13af, one grid for the Selmer, theta and lattice polynomials. | [Lean, read] (statement and final assembly; `partAT` step) |
| `residualSelmerBound_of_auxiliaryPrimes_odd`, `OddBound.residual_bound_of_parts`, `dec_le_of_frob_mem`; `boundModTwoUniformizerAtTwo_of_chebotarev`, `TwoBound.thmC_of_parts` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerBoundOfAuxiliaryPrimesOdd.lean:21`; `ResidualBoundOfComponents.lean:14,28`; `BoundModTwoUniformizerAtTwoOfChebotarev.lean:25`; `AddValLeOfNotMem.lean:16,87` | §10.4.7.5: Theorem 10.13ag, odd-prime and mod-two `OrdBound` wrappers and initial assemblies (recurrence `:28–85` inherited from Proposition 10.18). | [Lean, read] |
| `Start`, `NFit`, `Small2`, `idl`; `StartInd.start_of_galHyp`, `StartInd.start_of_resBound`, `computes_map`, `continuousCocycleChangeScalarsBack`, `unrAt_eq_top`, `unr_first`, `selOn_eq`, `resLam`; `TameScalar.exists_scalar_tmat_of_tame_inertia`; `SmallSub.exists_small` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/Small2.lean:13–45`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ContinuousCocycleChangeScalarsBack.lean:18–498`; `TameInertiaElementActsByScalar.lean:29`; `ExistsOpenNormalSubgroupUnderInertia.lean:140` | §10.4.7.6: Lemmas 10.13ak–10.13an and Theorem 10.13ao, producing the initial positive-order adjugate seed `Start` (conditional on `TameQuotient_holds` and `ResBound`). | [Lean, read] |
| `GlobalTheory.LinkFam.main`; `closed_linkEta_of_duty` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean:11`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEta.lean:13` | Proposition 10.3(2): sums $\log \ell \cdot \mathrm{vcc}$ over primes $\ell$ (`LinkFam.main` proving `LinkN`) and closes local twisting cover `LinkEta` (`closed_linkEta_of_duty`). | [Lean, read] |
| `qzTw`, `Sha`, `shaLen`, `PTShaAt`, `VFormula`, `selLen` | `src/Formalism/GaloisCohomology/Statement.lean:67,75,78,101,138,169` | Definition 10.3(1): discrete cyclotomic twist $\mathbb Q_\ell/\mathbb Z_\ell(-e)$, Tate–Shafarevich kernel `Sha`, and $\mathbb Z_\ell$-length `shaLen`. | [Lean, read] |
| `vvTerm`, `etaSum`, `LinkN_at`, `LinkN`, `LinkEta`, `SmallLevelRankEq`, `DIVinN_at`, `DIVinN`; `UpperTheory.Top.HypV`, `vvRecord`, `log_sq_le_rpow`, `divinN_at`, `UpperTheory.Top.divinN_of_hypV` | `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:31,36,40,45,49,52,59,62`; `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10,17,59,76,117` | Definition 10.3(2)–(3) and Theorem 10.4: defines `vvTerm`, single-step `LinkN_at`/`DIVinN_at`, and `SmallLevelRankEq`, and proves `DIVinN` from `HypV` + `LinkN` + `SmallLevelRankEq` at $B_0 = f m b x^\varepsilon$ (import cone 311). | [Lean, read] |
| `GlobalTheory.Published.GlobalArtinReciprocity` (`Prop` & hypothesis at `CutCoreUnit.main`) | `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70` (used at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:45`) | Named literature `Prop` used at $c = 0$ to bound unramified homomorphisms by $v_\ell(h_E)$ (`Prop` verified faithful in **Chapter 18** `[Lean, read]`; upstream 1,015-module proof cone `[Open]`). | [Lean, read] |
| `ChosenPrimes.stepAB` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAuxiliaryPrimesPrescribedFrobenius.lean:274–418` | §10.4.13 proves the conditional production of both batches. §10.4.8 summarizes both consumers. | [Lean, read] |
| `TameRel.tame_relation` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TameLocalRelationDualNumberCocycle.lean:105–159` | Lemma 10.14. Continuous local cocycles and the first-order Frobenius relation. | [Lean, read] |
| `GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle_pow`; `exists_descend_pair_quotient`; `NineTermExact.sum_eq_zero`, `idInv`, `exists_lift_cycMod`, `PoitouTateTotallyComplex.annihilators` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumInvEqZeroOfUnramifiedCocyclePow.lean:8–29`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumInvEqZeroOfUnramifiedCocycle.lean:9–20`; `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean:196–220,254–280,305–340` | §10.4.11.1, Lemmas 10.22c–10.22e and Theorem 10.22f: the finite invariant sum from the degree-two tail of the nine-term sequence at the identity invariant. | [Lean, read], conditional on `PoitouTateTotallyComplex` |
| `NewRecip.cupZ`, `locZ`, `NS_le`, `loc_eq_zero`, `local_pair`, `NewRecip.reciprocity` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ReciprocityRelaxedSelmerDualSelmerNewPlace.lean:22–31,39–41,68–74,82–95,126–184,190–315` | §10.4.11.1, Proposition 10.22g: the coefficient pairing gives an $N_S$-invariant two-cocycle whose local classes vanish away from the new split pair. | [Lean, read] |
| `PoitouTateTotallyComplex`; `IsLocalInvariants`, `InvFam` | `src/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/PoitouTateNineTermTransgressionZeroApply.lean:288–301,23–53` | §10.4.11.1: the nine-term exactness and Sha duality input, and the normalised conjugation-compatible local invariants. Definitions read; producer not read. | [Lean] |
| `ResOrder.core`, `ResOrder.resBound` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidualSelmerDeterminantOrderBound.lean:118–350` | Proposition 10.15. Conditional first-order matrix, determinant and adjugate argument. | [Lean, read] |
| Main-path all-powers witness and Chebotarev | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/ExportAtOfBundles.lean:19–28`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChebotarevDegreeOne.lean:17–67` | §10.4.7 traces the used applications, with deeper producers named there. | [Lean] |

**Summary of the chapter.** Projecting integral theta lifts onto cuspidal eigenspaces loses
denominators governed by Hecke congruence ideals `[Ribet1976]`, `[Hida1981]`, `[Hida1988]`. Using an
orthogonal idempotent GMA decomposition (`src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:18`), `CutDetOrd.main`
(Proposition 10.1) bounds each congruence ideal by off-diagonal Galois $1$-cocycle lengths
`[BellaicheChenevier2009]`, and `CutCoreUnit.main` (Theorem 10.2) reduces those cocycles to the
cuspidal Selmer length $\mathrm{sPi}$ (bounded at a good twist by `twist_kills_selmer`, Proposition
10.3; §10.4.7 traces the all-coprime-powers witness and §10.4.8 its first-order Selmer input), the class-number valuation $v_\ell(h_E)$ ($c = 0$), tame
cyclotomic units, and the cyclotomic Tate–Shafarevich lengths $\sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)$
($1 \le e < R.t$) [Lean, read]. Finally, `divinN_of_hypV` (Theorem 10.4) proves that combining `HypV`
($\sum'_\ell \mathrm{vvTerm} \le \sqrt{b} = \exp(x^\varepsilon / 2)$), `LinkN`, and `SmallLevelRankEq`
($d_{Z_0}(j) = D_0$) yields `DIVinN` at the linear-in-$m$ chain budget $B_0 = f m b x^\varepsilon$
[Lean, read] — leaving only the global window theorem `VWin` (`P12`, Chapter 11) to complete Part II!
