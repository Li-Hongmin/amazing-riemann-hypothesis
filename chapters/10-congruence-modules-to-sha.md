# Chapter 10. From congruence modules to Tate–Shafarevich groups

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs read
> line by line in `DivinNOfHypV.lean`, `IdempotentChoiceDepthZero.lean`,
> `LengthHeckeValueIdealLeDeterminantBound.lean`, `LengthHeckeValueIdealLeDeterminantBoundStatement.lean`,
> `GlobalCongruenceCountOfRootDifferenceUnit.lean`, `IntegralHeckeForms.lean`,
> `ChosenTwistAnnihilatesSelmerGroups.lean`, `LinkNAlongFamilyOfLocalBounds.lean`,
> `ThirdPlaceSeries/LinkEta.lean`, and `GaloisCohomology/Statement.lean` (`R3`); `[Lean]` for
> statement-level inspections of imported DVR determinant, cyclotomic-cocycle, class-group, and
> twisting-existence lemmas (`R2`); `[Paper]` for citations to Alpöge's `remark.pdf` and Masullo's
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
   Twisting the lift by a well-chosen character (`TwistingCharacterExistence`, `IntegralHeckeForms.lean:166`;
   `twist_kills_selmer`, `ChosenTwistAnnihilatesSelmerGroups.lean:8`) **annihilates the cuspidal
   $\rho$-Selmer piece**, while global Artin reciprocity and Poitou–Tate / Bloch–Kato Selmer theory
   `[BlochKato1990]`, `[Rubin2000]` bound the $t$ cyclotomic blocks by the **host class number
   $v_\ell(h_E)$** ($c = 0$) plus the **cyclotomic Tate–Shafarevich lengths**
   $\sum_{1 \le e < R.t} \operatorname{len}_{\mathbb Z_\ell} Ш^1(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e))$
   ($1 \le c < t$) plus tame ramification (`CutCoreUnit.main`,
   `GlobalCongruenceCountOfRootDifferenceUnit.lean:44`) [Lean, read]!
3. **Bridging `HypV` to the linear-in-$m$ chain budget `DIVinN` (`divinN_of_hypV`):** Once `HypV`
   (supplied by Chapter 11's `VWin`) bounds that $\log \ell$-weighted $Ш^1$ sum across all primes
   $\ell$ by $\sqrt{b} = \exp(x^\varepsilon / 2)$, `divinN_of_hypV` (`DivinNOfHypV.lean:117`, read
   100% line by line) proves `DIVinN` with per-lift budget $B_0 = f m b x^\varepsilon$ — avoiding the
   $x^{2/3}$ trap and hitting $x^{1/2 + O(\varepsilon)}$ in Chapter 5's `SZ.T3` [Lean, read]!

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
   (`ccOff` in `LengthHeckeValueIdealLeDeterminantBound.lean:15`)? An element $(a, b) \in R_k$ lies in
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
(`CutDetOrd.main`, `LengthHeckeValueIdealLeDeterminantBound.lean:59`)! Let $\mathcal O = \mathbb Z_\ell$,
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
Over a discrete valuation ring $\mathcal O$ above $\ell$ (with uniformizer $\varpi$ and finite length
$L = \operatorname{len}_{\mathcal O}(\mathcal O / (\ell))$), an orthogonal idempotent decomposition of
depth zero for rank tuple `R` (`t := R.t`) equips the Hecke/Galois algebra with [Lean, read]:

1. mutually orthogonal idempotents separating an $r \times r$ cuspidal block $e_B$ from $t = R.t$
   rank-$1$ cyclotomic character blocks $e_{1, c}$ ($c \in \mathrm{Fin}\,t$, corresponding to powers
   $1, 2, \dots, t$ of the cyclotomic character $\chi_{\mathrm{cyc}}$!); and
2. a distinguished rank-$1$ off-diagonal projector element `Eel` satisfying $\mathrm{Eel}^2 = \delta_{51}\cdot\mathrm{Eel}$
   with $\delta_{51} \in \mathcal O^\times$ (`IsUnit del51`), which extracts the off-diagonal pairing
   ideals feeding the congruence ideal `ccOff(π)` (`LengthHeckeValueIdealLeDeterminantBound.lean:15`).

### 10.3.2 Integral Hecke lattices and `TwistingCharacterExistence` (`IntegralHeckeForms.lean`)

**Definition 10.2 (Signed lattice index and character-twisting existence, `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:64,68,81,98,166,219,233`).**

1. **Module length and signed lattice index (`lenR` and `sIdx`, `:64, 68`).** Over a DVR $R$, `lenR`
   records finite $R$-module length, and for two commensurable $R$-lattices $\Lambda_1, \Lambda_2$,
   `sIdx Λ₁ Λ₂ := lenR(Λ₁ / (Λ₁ ∩ Λ₂)) - lenR(Λ₂ / (Λ₁ ∩ Λ₂))` (`:68`) is the additive signed index
   measuring exact denominator loss when passing from one integral structure to another [Lean, read].
2. **Admissible twisting characters and Selmer annihilation (`TwOK`, `TwistingCharacterExistence`, `GoodTw`, `TwistTheoremAtIndex`, `:81, 166, 219, 233`).**
   `TwistingCharacterExistence : Prop` (`:166`) asserts that at each chain step index $i$, there exists
   an admissible finite-order character $\eta$ (`TwOK` at `:81`, unramified outside controlled auxiliary
   primes $Q_i$ of bounded root-of-unity cost) whose twist `GoodTw` (`:219`) simultaneously preserves
   the local inert-prime kernel conditions of Chapter 8 and **reduces the cuspidal $\rho$-Selmer length
   to the controlled bound required by `TwistTheoremAtIndex` (`:233`)** [Lean, read].

### 10.3.3 Galois cohomology `Sha`, `LinkN`, `DIVinN`, and `HypV`

**Definition 10.3 (`Sha`, `shaLen`, `LinkN`, `DIVinN`, and `HypV`, `src/Formalism/GaloisCohomology/Statement.lean:67,75,78`, `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:40,45,59,62`, and `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10`).**

1. **Cyclotomic Tate–Shafarevich group and length (`qzTw`, `Sha`, `shaLen`, `GaloisCohomology/Statement.lean:67, 75, 78`).**
   For a number field $E$, a prime $\ell$, and an integer twist $e \in \mathbb N$, let
   $\mathbb Q_\ell / \mathbb Z_\ell(-e)$ (`qzTw`, `:67`) denote the discrete $G_{E, S_\ell}$-module on
   which $G_{E, S_\ell}$ acts via $\chi_{\mathrm{cyc}}^{-e}$, and let
   $$Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)
   := \ker\Bigl(H^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)
   \longrightarrow \prod_{v \in S_\ell} H^1\bigl(G_{E_v}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)\Bigr)$$
   (`Sha`, `:75`), with $\mathbb Z_\ell$-corank/length $\mathrm{shaLen}(E, \ell, e)$ (`:78`) [Lean, read].
2. **Congruence-to-$Ш^1$ link (`LinkN_at`, `LinkN`, `GlobalTheoremInputs.lean:40, 45`) and chain budget (`DIVinN_at`, `DIVinN`, `:59, 62`).**
   At chain datum $D$ (with host $E = D.\mathrm{host}$, $f = 2\lvert \varphi.A \rvert$, $m$ steps,
   rank cutoff $R.t$, and $b = \exp(x^\varepsilon)$), define for each prime $\ell$ (`vvTerm`,
   `DivinNOfHypV.lean:14`) [Lean, read]
   $$\mathrm{vvTerm}(D, \ell) := \log \ell \sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e).$$
   - `LinkN_at C D` (`GlobalTheoremInputs.lean:40`) asserts that if odd `Sha` groups are finite and
     $\sum'_\ell \mathrm{vvTerm}(D, \ell) \le B$, then the total congruence loss across the $m$ lifts
     is bounded by a constant $C$ times $(B + \log h_E + \text{tame/twist terms})$ bounded within
     $f m b (\log x)^2$ plus $m B$!
   - `DIVinN_at C₁ D` (`:59`) asserts that **unconditionally on $B$** (once $B$ has been supplied!),
     there exist chain loss parameters $B_0 \le C_1\,f m b x^\varepsilon$ (feeding Chapter 5's `SZ.T3`!)
     and $2$-adic level parameter $L = x^\varepsilon$ satisfying all congruence-loss clauses of `SizeData₂`!
3. **The global $Ш^1$ hypothesis (`UpperTheory.Top.HypV`, `DivinNOfHypV.lean:10`).** `HypV Fm : Prop`
   asserts that eventually for large window scales $x$ along the family `Fm`, every datum $D = \mathrm{Fm}.D(x, i)$
   satisfies `VVle D.host D.R.t (Real.sqrt D.b)` (`ExistsPageN.lean:12`, where $\sqrt{b} = \exp(x^\varepsilon / 2)$)
   [Lean, read]!

---

## 10.4 Lemmas and proofs

We now walk through the `R3`-verified proofs of node **P11**: first the GMA determinant bound
`CutDetOrd.main` and the Galois cohomology congruence bound `CutCoreUnit.main`, then Selmer
annihilation `twist_kills_selmer`, and finally the 100%-read proof of `divinN_of_hypV`.

### 10.4.1 The GMA determinant bound (`CutDetOrd.main`)

**Proposition 10.1 (Bounding the congruence ideal by cuspidal + cyclotomic cocycle lengths: `CutDetOrd.main`).**
*Let $\mathcal O$ be the discrete valuation ring above $\ell$ attached to a lift $\pi$ at step $i$,
with off-diagonal congruence ideal $\mathrm{ccOff}(\pi) \subseteq \mathcal O$. Then $\mathrm{ccOff}(\pi) \neq 0$
(`exists_ne_zero`, `:37`), and its quotient $\mathcal O$-length satisfies*
$$\operatorname{len}_{\mathcal O}\bigl(\mathcal O / \mathrm{ccOff}(\pi)\bigr)
\le \operatorname{len}_{\mathcal O}\bigl(\mathrm{cocRho}(\pi)\bigr)
+ \sum_{c \in \mathrm{Fin}\,t} \operatorname{len}_{\mathcal O}\bigl(\mathrm{cocChi}(\pi, c)\bigr),$$
*where $\mathrm{cocRho}(\pi)$ is the off-diagonal $1$-cocycle quotient for the cuspidal $\rho$-block
and $\mathrm{cocChi}(\pi, c)$ ($0 \le c < t$) are the $1$-cocycle quotients for the $t = R.t$
cyclotomic blocks.*
*(Lean: `GlobalTheory.CutDetOrd.main`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:59`,
and wrapper `…/LengthHeckeValueIdealLeDeterminantBoundStatement.lean:8`.)* [Lean, read]

*Proof.* First (`value_mem_ccOff` at `:15` and `exists_ne_zero` at `:37`), evaluating the off-diagonal
pairing against the unit $\delta_{51}$ of `IsOrthogonalIdempotentDecomposition` (`IdempotentChoiceDepthZero.lean:18`)
over the generic fiber shows that $\mathrm{ccOff}(\pi)$ is a nonzero ideal of the DVR $\mathcal O$, so
$\mathcal O / \mathrm{ccOff}(\pi)$ has finite $\mathcal O$-length. Next (`LengthHeckeValueIdealLeDeterminantBound.lean:59–165`),
the proof constructs the GMA relation module `Rel` pairing the off-diagonal column module $B$ against
the off-diagonal row module $C$ into $\mathcal O$. By the block determinant polynomial identity
`BlockDetPoly.main` (`[Lean]`), the Fitting/determinant ideal of the GMA presentation is contained in
$\mathrm{ccOff}(\pi)$ while the presentation quotients surject onto $\mathrm{cocRho}(\pi)$ and
$\bigoplus_{c \in \mathrm{Fin}\,t} \mathrm{cocChi}(\pi, c)$. Applying the DVR determinant-length lemma
`determinantLemma_discreteValuationRing_quotientLength_bound` (`[Lean]`) immediately bounds
$\operatorname{len}_{\mathcal O}(\mathcal O / \mathrm{ccOff}(\pi))$ by the sum of lengths of
$\mathrm{cocRho}(\pi)$ and the $t$ summands $\mathrm{cocChi}(\pi, c)$. $\square$

### 10.4.2 From cyclotomic cocycles to class numbers and $Ш^1$ (`CutCoreUnit.main`)

Now open `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean`
(`R3`, 160 lines read in full) and watch what happens to each of the $t$ cyclotomic indices
$c \in \{0, 1, \dots, t - 1\}$ — representing the cyclotomic characters $\chi_{\mathrm{cyc}}^{c + 1}$
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

1. **The cuspidal $\rho$-block (`cocRho`):** Local-global Selmer comparison (`Peel.main` `[Lean]`)
   bounds $\frac{1}{L}\operatorname{len}_{\mathcal O}(\mathrm{cocRho}(\pi))$ by $\mathrm{sPi}(i, \pi)$
   plus the tame inertia contribution at $Q_i$.
2. **Why $c = 0$ gives the class number $v_\ell(h_E)$ (`GlobalCongruenceCountOfRootDifferenceUnit.lean:88–112`):**
   Look at the first cyclotomic block $c = 0 \in \mathrm{Fin}\,t$, where the Hodge–Tate/cyclotomic
   shift is $(c : \mathbb N) + 1 = 1$. By Kummer / Poitou–Tate duality between $\mathbb Q_\ell/\mathbb Z_\ell(1)$
   and the **trivial** Galois module $\mathbb Q_\ell/\mathbb Z_\ell(0)$, everywhere-unramified
   $1$-cocycles for the $c = 0$ block are simply continuous **unramified homomorphisms**
   $\operatorname{Gal}(E^{\mathrm{ur}}/E) \to \mathcal O / \varpi^N$! Invoking the explicit hypothesis
   `hA : GlobalTheory.Published.GlobalArtinReciprocity` (`:45`), `GlobalTheory.UnramHom.length_le_classNumber hA`
   (`[Lean]`) identifies $\operatorname{Gal}(E^{\mathrm{ur},\mathrm{ab}}/E) \cong \mathrm{Cl}(\mathcal O_E)$
   and bounds the unramified cocycle length (divided by $L$, plus tame inertia at $Q_i$) by
   $$v_\ell(h_E) + \sum_{q \in Q_i} \mathrm{lenUnit}_\ell\bigl(\mathcal O / (\zeta_q - 1)\bigr)!$$
3. **Why $1 \le c < t$ gives $\sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)$ (`:113–148`):**
   For every $c \in \mathrm{Fin}\,t$ with $c \ge 1$, set $e := (c : \mathbb N) \in \{1, \dots, t - 1\} = \mathrm{Ioo}(0, R.t)$
   (reindexed in Lean via `Nat.add_sub_cancel`, since $(c + 1) - 1 = c$!). Here Poitou–Tate duality
   identifies the unramified/crystallina quotient of $\chi_{\mathrm{cyc}}^{c+1} = \chi_{\mathrm{cyc}}^{e+1}$
   cocycles with Pontryagin dual classes in $Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e)\bigr)$,
   so `length_cyclotomic_block_cocycles_le_sha` (`[Lean]`) bounds the $c$-th block (divided by $L$) by
   $$\mathrm{shaLen}(E, \ell, e) + \sum_{q \in Q_i} \mathrm{lenUnit}_\ell\bigl(\mathcal O / (\zeta_q - 1)\bigr).$$
4. **Summing over $c \in \{0, 1, \dots, t - 1\}$:** Adding $c = 0$ and $1 \le e < R.t$ collects the
   $t$ copies of $\sum_{q \in Q_i} \mathrm{lenUnit}_\ell(\mathcal O / (\zeta_q - 1))$ into
   $R.t \sum_{q \in Q_i} \dots$ and yields the exact inequality of Theorem 10.2! $\square$

*(Fidelity note on `GlobalArtinReciprocity` `[Lean]` + `[Open]`.)* Notice our strict adherence to the
book's tagging rules (`notes/proof-map.md`, node `P18`): `CutCoreUnit.main` takes
`hA : GlobalTheory.Published.GlobalArtinReciprocity` as an explicit `Prop` hypothesis (discharged
upstream in `EveryCharacterOfLiteratureOfVWin.lean` `[Lean]`). That `CutCoreUnit.main` proves
Theorem 10.2 from `hA` is `[Lean, read]`; whether the archive's definition of
`GlobalTheory.Published.GlobalArtinReciprocity` matches the textbook statement of global Artin
reciprocity in full generality (as opposed to the abelian/unramified specialization actually needed
here!) belongs to the literature-fidelity audit of Chapter 13 and is tagged `[Open]`.

### 10.4.3 Killing the $\rho$-Selmer term by twisting (`twist_kills_selmer` & `LinkFam.main`)

What happens to the cuspidal Selmer term $\mathrm{sPi}(i, \pi)$ on the right-hand side of Theorem 10.2?
Unlike the cyclotomic $Ш^1$ terms — which depend **only on the fixed CM host field $E$** and not on
which step $j \in \{1, \dots, m\}$ we are at! — an uncontrolled cuspidal Selmer group $\mathrm{sPi}(i, \pi)$
could depend on the $j$-th automorphic packet and accumulate uncontrollably!

**Proposition 10.3 (Killing $\mathrm{sPi}$ via character twisting and summing over $\ell$: `twist_kills_selmer` and `LinkFam.main`).**

1. **Selmer annihilation (`twist_kills_selmer`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:8`).**
   *Choosing the admissible character twist supplied by `TwistingCharacterExistence`
   (`IntegralHeckeForms.lean:166`) annihilates the residual/torsion cuspidal Selmer classes in
   $\mathrm{sPi}(i, \pi_{\mathrm{tw}})$ outside the controlled auxiliary prime set $Q_i$.* [Lean, read]
2. **Summing $\log \ell \cdot \mathrm{vcc}$ across all primes $\ell$ (`GlobalTheory.LinkFam.main`, `…/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean:11`, and `closed_linkEta_of_duty`, `…/ThirdPlaceSeries/LinkEta.lean:13`).**
   *Multiplying Theorem 10.2 (at the chosen Selmer-killing twist) by $\log \ell$ and summing over all
   rational primes $\ell$ converts:*
   - $\sum_\ell (\log \ell)\,v_\ell(h_E) = \log h_E$ *(which by Brauer–Siegel / elementary Minkowski
     bounds on the degree-$O(x^{2+8\varepsilon})$ host field $E$ satisfies $\log h_E \ll [E : \mathbb Q]\log\lvert d_E \rvert^{1/[E:\mathbb Q]} \ll f\,x^\varepsilon (\log x)^2$!)*;
   - $\sum_\ell \log \ell \sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e) = \sum'_\ell \mathrm{vvTerm}(D, \ell) \le B$; *and*
   - *the finite tame cyclotomic-unit sum over $q \in Q_i$, establishing `LinkN` (`LinkEta.lean:13`).* [Lean, read]

*(Reading boundary `[Lean]`.)* We read `IntegralHeckeForms.lean` (195-module cone),
`ChosenTwistAnnihilatesSelmerGroups.lean`, `LinkNAlongFamilyOfLocalBounds.lean`, and `LinkEta.lean`
in full (`R3` / `[Lean, read]`); the upstream construction proving `TwistingCharacterExistence`
(using Chebotarev density / cyclic prime splitting to pick twists whose local Frobenius eigenvalues
break residual Selmer cocycles, `remark.pdf` p. 4, items 14–16) sits inside the deeper automorphic
cone (`R2` / `[Lean]`, proof body unread `[Open]`).

### 10.4.4 Complete proof of `divinN_of_hypV`: how $\sqrt{b} = \exp(x^\varepsilon/2)$ closes `DIVinN`

To finish Chapter 10, let us prove `divinN_of_hypV` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:1–134`,
import cone **301** modules, read 100% line by line at `R3`) — the exact bridge from `LinkN` and
`HypV` to `DIVinN` [Lean, read]!

**Theorem 10.4 (From `LinkN` and `HypV` to `DIVinN`: `divinN_of_hypV`).** *Let `Fm : FamP eps`
($\varepsilon > 0$). If `LinkN Fm` (`∃ C, LinkN_at C` eventually along `Fm`) and `HypV Fm`
(`VVle D.host D.R.t (sqrt D.b)` eventually along `Fm`) hold, then `DIVinN Fm` holds with constant
$\lvert C \rvert + 1$: eventually for all $x \ge x_0$ and all family indices $i$, `DIVinN_at (|C| + 1) (Fm.D x i)`
holds with per-lift loss budget $B_0 := f\,m\,b\,x^\varepsilon$ and level factor $L := x^\varepsilon$.*
*(Lean: `vvRecord`, `log_sq_le_rpow`, `divinN_at`, and `UpperTheory.Top.divinN_of_hypV`,
`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:17,59,76,117`.)* [Lean, read]

*Proof.* Fix $\varepsilon > 0$ and choose $x$ large enough that $(\log x)^2 \le x^\varepsilon$
(`log_sq_le_rpow`, `:59`, since $\log x = o(x^{\varepsilon/2})$) and both `LinkN_at C D` and
`VVle E R.t (sqrt b)` hold for $D = \mathrm{Fm}.D(x, i)$ ($E = D.\mathrm{host}$, $b = D.b = \exp(x^\varepsilon) \ge 1$).

1. **Deduce finiteness, summability, and $\sum'_\ell \mathrm{vvTerm}(D, \ell) \le \sqrt{b}$ (`vvRecord`, `:17–57`):**
   Recall from Chapter 4 (Definition 4.4(4)) that `VVle E R.t B` (`B = \sqrt{b} \ge 0`) states that
   for **every** finite set $S$ of primes $\ell$,
   $$\sum_{\ell \in S} \log \ell \sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e) \le \sqrt{b}.$$
   - First, `VVle` explicitly carries finiteness of odd-twist `Sha` at every prime $\ell$ on singleton
     sets $S = \{\ell\}$, directly supplying `ShaFinOdd D` (`DivinNOfHypV.lean:22–38`).
   - Second, since every term $\mathrm{vvTerm}(D, \ell) \ge 0$ and every finite partial sum
     $\sum_{\ell \in S} \mathrm{vvTerm}(D, \ell)$ is bounded above by $\sqrt{b}$, Mathlib's
     `summable_of_sum_le` immediately gives `Summable (vvTerm D)` and `hasSum_le` gives
     $$\sum'_\ell \mathrm{vvTerm}(D, \ell) \le \sqrt{b}!$$
2. **Feed $B = \sqrt{b}$ into `LinkN_at C D` (`divinN_at`, `:76–115`):**
   Since $b = \exp(x^\varepsilon) \ge 1$, we have $\sqrt{b} \le b$, and since $(\log x)^2 \le x^\varepsilon$,
   the class-number/tame term $f m b (\log x)^2$ and the $Ш^1$ term $m \sqrt{b} \le f m b x^\varepsilon$
   from `LinkN_at C D` are both absorbed into
   $$B_0 := f\,m\,b\,x^\varepsilon, \qquad L := x^\varepsilon,$$
   with constant $(\lvert C \rvert + 1)$ (`(|C| + 1) * f * m * b * x^ε`), setting the per-step divisor
   bound $d_{Z_0}(j) := D_0$ across $1 \le j \le m$ (`:95–114`). That inhabits `DIVinN_at (|C| + 1) D`
   for every $(x, i)$, proving `DIVinN Fm` (`:117–133`)! $\square$

Pause and look at what Theorem 10.4 just accomplished! Remember Chapter 5's `SZ.T3`
(`LipschitzWeightAndMinimum.lean:53`): to prevent the congruence error from stopping at $x^{2/3}$, the
chain needed $B_0 \ll n\,m\,b\,x^\varepsilon$ (remember $f = 2\lvert\varphi.A\rvert \asymp n$!).
Because `divinN_of_hypV` achieves **$B_0 = f\,m\,b\,x^\varepsilon$** as soon as
$$\sum_\ell \log \ell \sum_{1 \le e < R.t} \operatorname{len}_{\mathbb Z_\ell}\,Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e)\bigr)
\le \sqrt{b} = \exp\bigl(x^\varepsilon / 2\bigr),$$
**we do NOT even need a polynomial bound on $Ш^1(E)$ — a subexponential bound $\exp(x^\varepsilon / 2)$
is already strong enough to beat $b = \exp(x^\varepsilon)$ and close `TopG`!** Proving that
subexponential window bound `VWin` across our cyclotomic CM host fields $E$ is the sole remaining piece
of Part II — and the subject of **Chapter 11**!

---

## 10.5 Remarks, formalization notes, and Masullo's counterpart

### 10.5.1 Import-cone anatomy of node P11

Our exact transitive import-cone audit (`notes/proof-map.md`) reveals a clean three-tier split inside
node **P11**:

| File | Import cone | Reading level & tag | Role |
|---|---|---|---|
| `IntegralHeckeForms.lean` | **195** | `R3` (`[Lean, read]`) | Defines DVR lattice indices `sIdx` and states `TwistingCharacterExistence`. |
| `DivinNOfHypV.lean` | **301** | `R3` (`[Lean, read]`) | Proves `vvRecord` and `divinN_of_hypV`, converting `HypV` + `LinkN` into `DIVinN`. |
| `GlobalCongruenceCountOfRootDifferenceUnit.lean` | **2,958** | `R3` (`[Lean, read]` for this file and `CutDetOrd.main`; `R2` `[Lean]` for imported cocycle/DVR sub-lemmas; `[Open]` for `GlobalArtinReciprocity` literature match) | Proves `CutCoreUnit.main`, reducing congruence valuation to $\mathrm{sPi} + \sum \mathrm{shaLen} + v_\ell(h_E) + \text{tame}$. |

### 10.5.2 Why cyclotomic twists $\mathbb Q_\ell / \mathbb Z_\ell(-e)$ appear up to $e < R.t \le \lfloor x^{400} \rfloor$

Readers who wondered in Chapter 4 why `VVle E ⌊x^400⌋₊ (exp(x^eps / 2))` summed over $1 \le e < \lfloor x^{400} \rfloor$
now have the exact structural explanation [Expository]:

- In the chain of $m \asymp x^{1/2}$ theta lifts over a host field of degree $[E : \mathbb Q] \asymp x^{2+8\varepsilon}$
  and word parameter $k \asymp x^{9/2 + 10\varepsilon}$, the Hodge–Tate / endoscopic cyclotomic block
  dimension $t = R.t$ grows polynomially in $x$ — bounded in
  `EventuallyRankLeRpowOfLtOneDivFiftytwo.lean:5` (Chapter 4, Section 4.2.2) by $10{,}708\,x^{399.67} \le \lfloor x^{400} \rfloor$
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
| `IsOrthogonalIdempotentDecomposition` | `src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:18` | Definition 10.1: orthogonal idempotent decomposition of GMA into cuspidal $\rho$-block and $t = R.t$ cyclotomic blocks with unit `del51`. | [Lean, read] |
| `value_mem_ccOff`, `exists_ne_zero`, `GlobalTheory.CutDetOrd.main`; statement wrapper | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:15,37,59`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBoundStatement.lean:8` | Proposition 10.1: proves $\mathrm{ccOff}(\pi) \neq 0$ and bounds $\operatorname{len}_{\mathcal O}(\mathcal O/\mathrm{ccOff}(\pi))$ by cuspidal + cyclotomic $1$-cocycle lengths via GMA `Rel`. | [Lean, read] |
| `ccOff_univ`, `GlobalTheory.CutCoreUnit.main` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:24,44` | Theorem 10.2: bounds congruence valuation `vcc` by $\mathrm{sPi} + \sum_{1 \le e < R.t} \mathrm{shaLen} + v_\ell(h_E) + \text{tame}$ (assuming `GlobalArtinReciprocity`; import cone 2,958). | [Lean, read] |
| `lenR`, `sIdx`, `TwOK`, `RFam`, `ABHyp`, `partAB`, `TwistingCharacterExistence`, `GoodTw`, `TwistTheoremAtIndex`, `admitted`, `Stmt` | `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:64,68,81,98,125,150,166,219,233,324,329` | Definition 10.2: DVR module lengths, signed lattice index `sIdx`, and `TwistingCharacterExistence` (import cone 195). | [Lean, read] |
| `twist_kills_selmer` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:8` | Proposition 10.3(1): chosen admissible twist annihilates residual cuspidal Selmer classes. | [Lean, read] |
| `GlobalTheory.LinkFam.main`; `closed_linkEta_of_duty` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean:11`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEta.lean:13` | Proposition 10.3(2): sums $\log \ell \cdot \mathrm{vcc}$ over primes $\ell$ across the family to establish `LinkN`. | [Lean, read] |
| `qzTw`, `Sha`, `shaLen`, `PTShaAt`, `VFormula`, `selLen` | `src/Formalism/GaloisCohomology/Statement.lean:67,75,78,101,138,169` | Definition 10.3(1): discrete cyclotomic twist $\mathbb Q_\ell/\mathbb Z_\ell(-e)$, Tate–Shafarevich kernel `Sha`, and $\mathbb Z_\ell$-length `shaLen`. | [Lean, read] |
| `UpperTheory.Top.HypV`, `vvRecord`, `log_sq_le_rpow`, `divinN_at`, `UpperTheory.Top.divinN_of_hypV` | `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10,17,59,76,117` | Definition 10.3(3) and Theorem 10.4: proves `Summable (vvTerm D)` and $\sum'_\ell \mathrm{vvTerm} \le \sqrt{b}$ from `VVle`, and deduces `DIVinN` with $B_0 = f m b x^\varepsilon$ (import cone 301). | [Lean, read] |
| `GlobalTheory.Published.GlobalArtinReciprocity` (hypothesis at `CutCoreUnit.main`) | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:45` | Named literature `Prop` used at $c = 0$ to bound unramified homomorphisms by $v_\ell(h_E)$ (`[Lean]` proved in archive; literature-statement match `[Open]`). | [Open] |

**Summary of the chapter.** Projecting integral theta lifts onto cuspidal eigenspaces loses
denominators governed by Hecke congruence ideals `[Ribet1976]`, `[Hida1981]`, `[Hida1988]`. Using an
orthogonal idempotent GMA decomposition (`IdempotentChoiceDepthZero.lean:18`), `CutDetOrd.main`
(Proposition 10.1) bounds each congruence ideal by off-diagonal Galois $1$-cocycle lengths
`[BellaicheChenevier2009]`, and `CutCoreUnit.main` (Theorem 10.2) reduces those cocycles to the
cuspidal Selmer length $\mathrm{sPi}$ (killed by twisting via `TwistingCharacterExistence` and
`twist_kills_selmer`, Proposition 10.3), the class-number valuation $v_\ell(h_E)$ ($c = 0$), tame
cyclotomic units, and the cyclotomic Tate–Shafarevich lengths $\sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)$
($1 \le e < R.t$) [Lean, read]. Finally, `divinN_of_hypV` (Theorem 10.4) proves that bounding the
$\log \ell$-weighted $Ш^1$ sum by $\sqrt{b} = \exp(x^\varepsilon / 2)$ (`HypV`) yields the linear-in-$m$
chain budget $B_0 = f m b x^\varepsilon$ (`DIVinN`) [Lean, read] — leaving only the global window
theorem `VWin` (`P12`, Chapter 11) to complete Part II!
