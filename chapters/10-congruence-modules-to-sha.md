# Chapter 10. From congruence modules to Tate–Shafarevich groups

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs read
> line by line in `DivinNOfHypV.lean`, `IdempotentChoiceDepthZero.lean`,
> `LengthHeckeValueIdealLeDeterminantBound.lean`, `LengthHeckeValueIdealLeDeterminantBoundStatement.lean`,
> `GlobalCongruenceCountOfRootDifferenceUnit.lean`, `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean`,
> `ChosenTwistAnnihilatesSelmerGroups.lean`, `LinkNAlongFamilyOfLocalBounds.lean`,
> `ThirdPlaceSeries/LinkEta.lean`, and `GaloisCohomology/Statement.lean` (`R3`), and, in §§10.4.5–10.4.6,
> for the imported DVR determinant lemma, block-determinant lemmas, GMA Fitting step, peeling lemma,
> cyclotomic-block $Ш^1$ bound, class-number bound, $\rho$-block Selmer comparison and
> `twist_kills_selmer` (`R3`), and for the main-path twist construction and Chebotarev producer read in §10.4.7
> and the lattice-specialization transport read in §10.4.7.1.
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

**Dependency evidence.** The SHA-256-verified DeDeo export of the five main theorems
contains `admissibleIndexBoundAllPowers_of_conditions`, `exportAll_of_six_inputs`,
`galois_twisted_selmer_auxprimes_of_matrix_and_bounds` and `GlobalTheory.Published.cheb_holds`.
The full-name declaration scan finds no `IntegralHeckeForms.Stmt`,
`IntegralHeckeForms.admitted`, `TwistingCharacterExistence`, `export_of_inputs` or
`admissibleBounds_of_all` in that export. The scan is a closure check for the five
roots together. Reachability alone does not establish consumption. The proof
applications above identify where the witness is passed and read.
[DeDeo export, SOURCES V8](../sources/SOURCES.md#v8)

**Remark [Open].** The deeper cohomology and determinant arguments behind the Selmer presentation
and the two order bounds, the cyclotomic prime-norm existence inputs to `chebotarevDegreeOne'`, and the
toric supply `PropABCD` with the level lemma behind `exists_level` remain to be read. Section 10.4.7.1
reads the lattice-specialization transport. The applications above identify these inputs and their
quantifiers.

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
| toric supply `propABCD_of_rel`; level lemma `GlobalTheory.T.exists_level_order_exponents_small_valuation_determinants`; `Pack.main`; producers of `SelmerSeriesChoice` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:293`; called at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsAuxiliaryPlaceFamilyAtLevelMono.lean:343`; `src/Formalism/SharpRestriction/LevelLetterCocycles/LinearIndependentSmulOfNeZero.lean:2219` | [Lean] |
| main-path suppliers of `IsotypicPartsInternalDirectSum`, `GroupAlgebraIntegrality` and `GoodLatticePoints`; the hypotheses `admT4` and `TwistedSeriesSpecialisation` | `admInt_of_sup_laws`, `admALG_of_commG_var`, `admT3_of_hecke_semisimple` at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistTheoremAllPowersOfSelmerSupLattice.lean:38–40`; hypotheses at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TwistAllPowersOfGaloisCohomologyClassField.lean:21–30` | [Lean] |
| downstream readers of `IdxAt` and `InclAt` after `goodTw_transfer` | `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TwistDataAgreeAcrossCoefficientsSymm.lean:133–168` and later | not traced here |

The reading upgrades the transport in §10.4.6 from statement level to a read proof. It does not upgrade the toric supply, the level lemma or the integrality inputs. The lattice clauses are proved from those named inputs.


---

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
| `PropABCD`; `propABCD_of_rel` | `src/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/GaloisSideTwistedSelmerAuxiliaryPrimes.lean:119`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AevalOneSubOne.lean:293` | §10.4.7.1: Proposition 10.13j (definition read; producer not read). | [Lean] |
| `GlobalTheory.LinkFam.main`; `closed_linkEta_of_duty` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean:11`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEta.lean:13` | Proposition 10.3(2): sums $\log \ell \cdot \mathrm{vcc}$ over primes $\ell$ (`LinkFam.main` proving `LinkN`) and closes local twisting cover `LinkEta` (`closed_linkEta_of_duty`). | [Lean, read] |
| `qzTw`, `Sha`, `shaLen`, `PTShaAt`, `VFormula`, `selLen` | `src/Formalism/GaloisCohomology/Statement.lean:67,75,78,101,138,169` | Definition 10.3(1): discrete cyclotomic twist $\mathbb Q_\ell/\mathbb Z_\ell(-e)$, Tate–Shafarevich kernel `Sha`, and $\mathbb Z_\ell$-length `shaLen`. | [Lean, read] |
| `vvTerm`, `etaSum`, `LinkN_at`, `LinkN`, `LinkEta`, `SmallLevelRankEq`, `DIVinN_at`, `DIVinN`; `UpperTheory.Top.HypV`, `vvRecord`, `log_sq_le_rpow`, `divinN_at`, `UpperTheory.Top.divinN_of_hypV` | `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:31,36,40,45,49,52,59,62`; `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10,17,59,76,117` | Definition 10.3(2)–(3) and Theorem 10.4: defines `vvTerm`, single-step `LinkN_at`/`DIVinN_at`, and `SmallLevelRankEq`, and proves `DIVinN` from `HypV` + `LinkN` + `SmallLevelRankEq` at $B_0 = f m b x^\varepsilon$ (import cone 311). | [Lean, read] |
| `GlobalTheory.Published.GlobalArtinReciprocity` (`Prop` & hypothesis at `CutCoreUnit.main`) | `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70` (used at `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:45`) | Named literature `Prop` used at $c = 0$ to bound unramified homomorphisms by $v_\ell(h_E)$ (`Prop` verified faithful in **Chapter 18** `[Lean, read]`; upstream 1,015-module proof cone `[Open]`). | [Lean, read] |

**Summary of the chapter.** Projecting integral theta lifts onto cuspidal eigenspaces loses
denominators governed by Hecke congruence ideals `[Ribet1976]`, `[Hida1981]`, `[Hida1988]`. Using an
orthogonal idempotent GMA decomposition (`src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:18`), `CutDetOrd.main`
(Proposition 10.1) bounds each congruence ideal by off-diagonal Galois $1$-cocycle lengths
`[BellaicheChenevier2009]`, and `CutCoreUnit.main` (Theorem 10.2) reduces those cocycles to the
cuspidal Selmer length $\mathrm{sPi}$ (bounded at a good twist by `twist_kills_selmer`, Proposition
10.3; the existence of the twist is the `Prop` `TwistingCharacterExistence`, §10.4.6), the class-number valuation $v_\ell(h_E)$ ($c = 0$), tame
cyclotomic units, and the cyclotomic Tate–Shafarevich lengths $\sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)$
($1 \le e < R.t$) [Lean, read]. Finally, `divinN_of_hypV` (Theorem 10.4) proves that combining `HypV`
($\sum'_\ell \mathrm{vvTerm} \le \sqrt{b} = \exp(x^\varepsilon / 2)$), `LinkN`, and `SmallLevelRankEq`
($d_{Z_0}(j) = D_0$) yields `DIVinN` at the linear-in-$m$ chain budget $B_0 = f m b x^\varepsilon$
[Lean, read] — leaving only the global window theorem `VWin` (`P12`, Chapter 11) to complete Part II!
