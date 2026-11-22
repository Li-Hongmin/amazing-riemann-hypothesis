# Chapter 10. From congruence modules to Tate–Shafarevich groups

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs read
> line by line in `DivinNOfHypV.lean`, `IdempotentChoiceDepthZero.lean`,
> `LengthHeckeValueIdealLeDeterminantBound.lean`, `LengthHeckeValueIdealLeDeterminantBoundStatement.lean`,
> `GlobalCongruenceCountOfRootDifferenceUnit.lean`, `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean`,
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
   Twisting the lift by a well-chosen character (`TwistingCharacterExistence`, `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:166`;
   `twist_kills_selmer`, `ChosenTwistAnnihilatesSelmerGroups.lean:8`) **annihilates the cuspidal
   $\rho$-Selmer piece**, while global Artin reciprocity and Poitou–Tate / Bloch–Kato Selmer theory
   `[BlochKato1990]`, `[Rubin2000]` bound the $t$ cyclotomic blocks by the **host class number
   $v_\ell(h_E)$** ($c = 0$) plus the **cyclotomic Tate–Shafarevich lengths**
   $\sum_{1 \le e < R.t} \operatorname{len}_{\mathbb Z_\ell} Ш^1(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e))$
   ($1 \le c < t$) plus tame ramification (`CutCoreUnit.main`,
   `GlobalCongruenceCountOfRootDifferenceUnit.lean:44`) [Lean, read]!
3. **Bridging `HypV` to the linear-in-$m$ chain budget `DIVinN` (`divinN_of_hypV`):** Once `HypV`
   (supplied by Chapter 11's `VWin`) bounds that $\log \ell$-weighted $Ш^1$ sum across all primes
   $\ell$ by $\sqrt{b} = \exp(x^\varepsilon / 2)$ and `SmallLevelRankEq` equates per-step kernel
   ranks `dZ0 j` to the base rank `D0`, `divinN_of_hypV` (`DivinNOfHypV.lean:117`, read 100% line by
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
Over a discrete valuation ring $\mathcal O = N.\mathcal O(i)$ above $\ell = N.\ell(i)$, an orthogonal
idempotent decomposition of depth zero for rank tuple `R` (`r := R.r`, `t := R.t`, ambient dimension
`R.nV`) equips the Hecke/Galois algebra with [Lean, read]:

1. mutually orthogonal idempotents `S.eB` of **rank $t = R.t$** (`((S.eB x).map (toK N i)).rank = R.t`,
   `:22`) — the **cyclotomic block idempotent**, diagonalized by `S.X0` (`:36–38`) at a distinguished
   inertia element `S.g0` into the $t = R.t$ cyclotomic powers $\chi_{\mathrm{cyc}}^{c+1}$
   ($c \in \mathrm{Fin}\,R.t$, i.e. powers $1, 2, \dots, t$!) — and `S.e1` of **rank $1$** (`:22`),
   together with the splitting `S.e` (`:24–29`) decomposing the `R.nV`-dimensional representation into
   the $r \times r$ cuspidal representation block `rhoO` (`Fin R.r`) and the $t$ scalar cyclotomic
   coordinates (`Fin R.t`); and
2. a distinguished rank-$1$ projector element `Eel` (`:56–60`) satisfying $\mathrm{Eel}^2 = \delta_{51}\cdot\mathrm{Eel}$
   with $\delta_{51} \in \mathcal O^\times$ (`IsUnit del51`), projecting onto the $c = 0$ cyclotomic
   slot to extract the off-diagonal pairing values feeding the congruence ideal `ccOff(π)`
   (`LengthHeckeValueIdealLeDeterminantBound.lean:15`).

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
   `TwistingCharacterExistence : Prop` (`:166`) asserts that at each chain step index $i$, there exists
   an admissible finite-order character $\eta$ (`TwOK` at `:81`, unramified outside controlled auxiliary
   primes $Q_i$ of bounded root-of-unity cost) whose twist `GoodTw` (`:219`) simultaneously preserves
   the local inert-prime kernel conditions of Chapter 8 and **reduces the cuspidal $\rho$-Selmer length
   to the controlled bound required by `TwistTheoremAtIndex` (`:233`)** [Lean, read].

### 10.3.3 Galois cohomology `Sha`, `LinkN`, `DIVinN`, and `HypV`

**Definition 10.3 (`Sha`, `shaLen`, `vvTerm`, `LinkN`, `SmallLevelRankEq`, `DIVinN`, and `HypV`, `src/Formalism/GaloisCohomology/Statement.lean:67,75,78`, `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:31,36,40,45,49,52,59,62`, and `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10`).**

1. **Cyclotomic Tate–Shafarevich group and length (`qzTw`, `Sha`, `shaLen`, `GaloisCohomology/Statement.lean:67, 75, 78`).**
   For a number field $E$, a prime $\ell$, and an integer twist $e \in \mathbb N$, let
   $\mathbb Q_\ell / \mathbb Z_\ell(-e)$ (`qzTw`, `:67`) denote the discrete $G_{E, S_\ell}$-module on
   which $G_{E, S_\ell}$ acts via $\chi_{\mathrm{cyc}}^{-e}$, and let
   $$Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)
   := \ker\Bigl(H^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)
   \longrightarrow \prod_{v \in S_\ell} H^1\bigl(G_{E_v}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)\Bigr)$$
   (`Sha`, `:75`), with $\mathbb Z_\ell$-corank/length $\mathrm{shaLen}(E, \ell, e)$ (`:78`) [Lean, read].
2. **Single-step congruence-to-$Ш^1$ link (`vvTerm`, `etaSum`, `LinkN_at`, `LinkN`, `SmallLevelRankEq`, `GlobalTheoremInputs.lean:31, 36, 40, 45, 52`) and chain budget (`DIVinN_at`, `DIVinN`, `:59, 62`).**
   At chain datum $D$ (with host $E = D.\mathrm{host}.E$, $f = D.R.f = 2\lvert \varphi.A \rvert$,
   $m = D.R.m$ steps, rank cutoff $R.t$, $b = \exp(x^\varepsilon)$, $L = x^\varepsilon$, and
   $B_0 = f m b x^\varepsilon$), define for each $l \in \mathbb N$ (`vvTerm`,
   `GlobalTheoremInputs.lean:31`) [Lean, read]
   $$\mathrm{vvTerm}(D, l) := \begin{cases} (\log l)\sum_{1 \le e < R.t} \mathrm{shaLen}(l, e) & \text{if } l\text{ is prime}, \\ 0 & \text{otherwise,}\end{cases}$$
   and let `etaSum L j` (`:36`) be the weighted sum of step-$j$ congruence losses across active places $w$:
   - `LinkN_at L j C` (`:40–43`) is the **single-step** implication at lift $j \in \{1, \dots, m\}$:
     $$\mathrm{Summable}\bigl(\mathrm{vvTerm}(D)\bigr) \implies
     \mathrm{etaSum}(L, j) \le d_{Z_0}(j)\,\Bigl(C\,\bigl(f m b L^2 + (\log x)^2 N_c\bigr) + \sum'_l \mathrm{vvTerm}(D, l)\Bigr),$$
     and `LinkN Fm` (`:45`) asserts that `LinkN_at (Fm.L x i) j C` holds eventually for all $j \in \{1, \dots, m\}$
     whenever `ShaFinOdd` (`:25`) holds.
   - `SmallLevelRankEq Fm` (`:52–53`) asserts that eventually $(Fm.L\,x\,i).d_{Z_0}(j) = (Fm.D\,x\,i).\mathrm{what}_2.D_0$
     for every $j \in \{1, \dots, m\}$ (proved in `ThirdPlaceSeries/Link.lean:20` as `link_alt_alt_alt`).
   - `DIVinN_at L j C` (`:59–60`) is the deterministic single-step inequality
     $$\mathrm{etaSum}(L, j) \le D_0 \cdot C\,x^\varepsilon\,(B_0 + N_c)$$
     (where $B_0 = f m b x^\varepsilon$ is the fixed field of `SizeData₂` feeding Chapter 5's `SZ.T3`!),
     and `DIVinN Fm` (`:62`) asserts `DIVinN_at` eventually across all lifts $j \in \{1, \dots, m\}$!
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
and wrapper `…/LengthHeckeValueIdealLeDeterminantBoundStatement.lean:8`.)* [Lean, read]

*Proof.* First (`value_mem_ccOff` at `:15` and `exists_ne_zero` at `:37`), using the rank-$1$ projector
`Eel` and unit $\delta_{51}$ of `IsOrthogonalIdempotentDecomposition` (`IdempotentChoiceDepthZero.lean:18`)
together with `NoChiOff` away from `Z i` produces $\eta$ and $\gamma$ with nonzero off-diagonal
action `(yg ... γ x').mulVec η ≠ 0`. Next (`src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:59–140`),
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

1. **Selmer annihilation (`twist_kills_selmer`, `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:8`).**
   *Choosing the admissible character twist supplied by `TwistingCharacterExistence`
   (`src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:166`) annihilates the residual/torsion cuspidal Selmer classes in
   $\mathrm{sPi}(i, \pi_{\mathrm{tw}})$ outside the controlled auxiliary prime set $Q_i$.* [Lean, read]
2. **Summing $\log \ell \cdot \mathrm{vcc}$ across all primes $\ell$ and closing `LinkEta` (`GlobalTheory.LinkFam.main`, `…/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean:11`, and `closed_linkEta_of_duty`, `…/ThirdPlaceSeries/LinkEta.lean:13`).**
   *Multiplying Theorem 10.2 (at the chosen Selmer-killing twist) by $\log \ell$ and summing over all
   rational primes $\ell$ converts:*
   - $\sum_\ell (\log \ell)\,v_\ell(h_E) = \log h_E$ *(controlled within $(\log x)^2 N_c$ alongside
     tame ramification)*;
   - $\sum_\ell \log \ell \sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e) = \sum'_\ell \mathrm{vvTerm}(D, \ell)$; *and*
   - *the finite tame cyclotomic-unit sum over $q \in Q_i$, establishing `LinkN` (`LinkFam.main`,
     `LinkNAlongFamilyOfLocalBounds.lean:11`), while `closed_linkEta_of_duty` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEta.lean:13`)
     closes the companion local twisting-cover predicate `LinkEta` (`LocsCoverTw`,
     `GlobalTheoremInputs.lean:49`).* [Lean, read]

*(Reading boundary `[Lean]`.)* We read `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean` (207-module cone),
`ChosenTwistAnnihilatesSelmerGroups.lean`, `LinkNAlongFamilyOfLocalBounds.lean`, and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEta.lean`
in full (`R3` / `[Lean, read]`); the upstream construction proving `TwistingCharacterExistence`
(using Chebotarev density / cyclic prime splitting to pick twists whose local Frobenius eigenvalues
break residual Selmer cocycles, `remark.pdf` p. 4, items 14–15, 17) sits inside the deeper automorphic
cone (`R2` / `[Lean]`, proof body unread `[Open]`).

### 10.4.4 Complete proof of `divinN_of_hypV`: how $\sqrt{b} = \exp(x^\varepsilon/2)$ closes `DIVinN`

To finish Chapter 10, let us prove `divinN_of_hypV` (`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:1–130`,
leaf-inclusive import cone **311** modules, read 100% line by line at `R3`) — the exact bridge from
`HypV`, `LinkN`, and `SmallLevelRankEq` to `DIVinN` [Lean, read]!

**Theorem 10.4 (From `HypV`, `LinkN`, and `SmallLevelRankEq` to `DIVinN`: `divinN_of_hypV`).**
*Let `Fm : FamP eps` ($\varepsilon > 0$). Assume the three family hypotheses:*

1. `(hV : HypV Fm.toFamCore)` *(`VVle D.host.E D.R.t (sqrt L.sc.b)` eventually along `Fm`);*
2. `(hN : LinkN Fm)` *(`∃ C, LinkN_at (Fm.L x i) j C` eventually along `Fm` whenever `ShaFinOdd` holds); and*
3. `(hR : SmallLevelRankEq Fm)` *(`(Fm.L x i).dZ0 j = (Fm.D x i).what₂.D0` eventually for all $j \in \{1, \dots, m\}$, supplied by `ThirdPlaceSeries/Link.lean:20`).*

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
     supplying `hf : ShaFinOdd D` (`DivinNOfHypV.lean:22–30, 54–57`).
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
| `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean` | **207** | `R3` (`[Lean, read]`) | Defines ramification-normalized lengths `lenR`, signed lattice indices `sIdx`, and states `TwistingCharacterExistence`. |
| `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean` | **311** | `R3` (`[Lean, read]`) | Proves `vvRecord` and `divinN_of_hypV`, converting `HypV` + `LinkN` + `SmallLevelRankEq` into `DIVinN`. |
| `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean` | **3,287** | `R3` (`[Lean, read]` for this file, `CutDetOrd.main`, and `GlobalArtinReciprocity`'s `Prop` in Ch. 18; `R2` `[Lean]` for imported cocycle/DVR sub-lemmas; `[Open]` for `globalArtinReciprocity`'s 1,015-module proof cone) | Proves `CutCoreUnit.main`, reducing congruence valuation to $\mathrm{sPi} + \sum \mathrm{shaLen} + v_\ell(h_E) + \text{tame}$. |

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
| `IsOrthogonalIdempotentDecomposition` | `src/Formalism/SharpRestriction/LevelLetterCocycles/IdempotentChoiceDepthZero.lean:18` | Definition 10.1: orthogonal idempotents `S.eB` (cyclotomic block of rank $t = R.t$) and `S.e1` (rank $1$), splitting `S.e` into cuspidal `rhoO` (`Fin R.r`) + $t$ cyclotomic slots, and rank-$1$ projector `Eel` with unit `del51`. | [Lean, read] |
| `value_mem_ccOff`, `exists_ne_zero`, `GlobalTheory.CutDetOrd.main`; statement wrapper | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBound.lean:15,37,59`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LengthHeckeValueIdealLeDeterminantBoundStatement.lean:8` | Proposition 10.1: produces a nonzero off-diagonal matrix evaluation away from `Z i` (`exists_ne_zero`) and bounds $\operatorname{len}_{\mathcal O}(\mathcal O/\mathrm{ccOff}(\pi))$ by cuspidal + cyclotomic $1$-cocycle lengths via GMA `Rel`. | [Lean, read] |
| `ccOff_univ`, `GlobalTheory.CutCoreUnit.main` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GlobalCongruenceCountOfRootDifferenceUnit.lean:24,44` | Theorem 10.2: bounds congruence valuation `vcc` by $\mathrm{sPi} + \sum_{1 \le e < R.t} \mathrm{shaLen} + v_\ell(h_E) + \text{tame}$ (assuming `GlobalArtinReciprocity`; import cone 3,287). | [Lean, read] |
| `lenR`, `sIdx`, `TwOK`, `RFam`, `ABHyp`, `partAB`, `TwistingCharacterExistence`, `GoodTw`, `TwistTheoremAtIndex`, `admitted`, `Stmt` | `src/Formalism/SharpRestriction/LevelLetterCocycles/IntegralHeckeForms.lean:64,68,81,98,125,150,166,219,233,324,329` | Definition 10.2: ramification-normalized DVR lengths `lenR`, signed lattice index `sIdx`, and `TwistingCharacterExistence` (import cone 207). | [Lean, read] |
| `twist_kills_selmer` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ChosenTwistAnnihilatesSelmerGroups.lean:8` | Proposition 10.3(1): chosen admissible twist annihilates residual cuspidal Selmer classes. | [Lean, read] |
| `GlobalTheory.LinkFam.main`; `closed_linkEta_of_duty` | `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LinkNAlongFamilyOfLocalBounds.lean:11`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkEta.lean:13` | Proposition 10.3(2): sums $\log \ell \cdot \mathrm{vcc}$ over primes $\ell$ (`LinkFam.main` proving `LinkN`) and closes local twisting cover `LinkEta` (`closed_linkEta_of_duty`). | [Lean, read] |
| `qzTw`, `Sha`, `shaLen`, `PTShaAt`, `VFormula`, `selLen` | `src/Formalism/GaloisCohomology/Statement.lean:67,75,78,101,138,169` | Definition 10.3(1): discrete cyclotomic twist $\mathbb Q_\ell/\mathbb Z_\ell(-e)$, Tate–Shafarevich kernel `Sha`, and $\mathbb Z_\ell$-length `shaLen`. | [Lean, read] |
| `vvTerm`, `etaSum`, `LinkN_at`, `LinkN`, `LinkEta`, `SmallLevelRankEq`, `DIVinN_at`, `DIVinN`; `UpperTheory.Top.HypV`, `vvRecord`, `log_sq_le_rpow`, `divinN_at`, `UpperTheory.Top.divinN_of_hypV` | `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:31,36,40,45,49,52,59,62`; `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:10,17,59,76,117` | Definition 10.3(2)–(3) and Theorem 10.4: defines `vvTerm`, single-step `LinkN_at`/`DIVinN_at`, and `SmallLevelRankEq`, and proves `DIVinN` from `HypV` + `LinkN` + `SmallLevelRankEq` at $B_0 = f m b x^\varepsilon$ (import cone 311). | [Lean, read] |
| `GlobalTheory.Published.GlobalArtinReciprocity` (`Prop` & hypothesis at `CutCoreUnit.main`) | `src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ExistsUniqueHcharOfFiniteOrder.lean:70` (used at `…/GlobalCongruenceCountOfRootDifferenceUnit.lean:45`) | Named literature `Prop` used at $c = 0$ to bound unramified homomorphisms by $v_\ell(h_E)$ (`Prop` verified faithful in **Chapter 18** `[Lean, read]`; upstream 1,015-module proof cone `[Open]`). | [Lean, read] |

**Summary of the chapter.** Projecting integral theta lifts onto cuspidal eigenspaces loses
denominators governed by Hecke congruence ideals `[Ribet1976]`, `[Hida1981]`, `[Hida1988]`. Using an
orthogonal idempotent GMA decomposition (`IdempotentChoiceDepthZero.lean:18`), `CutDetOrd.main`
(Proposition 10.1) bounds each congruence ideal by off-diagonal Galois $1$-cocycle lengths
`[BellaicheChenevier2009]`, and `CutCoreUnit.main` (Theorem 10.2) reduces those cocycles to the
cuspidal Selmer length $\mathrm{sPi}$ (killed by twisting via `TwistingCharacterExistence` and
`twist_kills_selmer`, Proposition 10.3), the class-number valuation $v_\ell(h_E)$ ($c = 0$), tame
cyclotomic units, and the cyclotomic Tate–Shafarevich lengths $\sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)$
($1 \le e < R.t$) [Lean, read]. Finally, `divinN_of_hypV` (Theorem 10.4) proves that combining `HypV`
($\sum'_\ell \mathrm{vvTerm} \le \sqrt{b} = \exp(x^\varepsilon / 2)$), `LinkN`, and `SmallLevelRankEq`
($d_{Z_0}(j) = D_0$) yields `DIVinN` at the linear-in-$m$ chain budget $B_0 = f m b x^\varepsilon$
[Lean, read] — leaving only the global window theorem `VWin` (`P12`, Chapter 11) to complete Part II!
