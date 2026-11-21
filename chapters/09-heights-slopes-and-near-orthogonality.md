# Chapter 9. Heights, slopes, and near-orthogonality

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs read
> in full across `LatticeSlopes/`, `HarderNarasimhan/`, `DivisionHeightBoundStatement.lean`,
> `GlobalBoundRefinements.lean`, `GlobalTheoremInputs.lean`, `TieGlobal.lean`, `ThirdPlaceSeries/LinkG.lean`,
> `ThirdPlaceSeries/LinkAltAltBis.lean`, `GlobalInterpolation/LinkGl.lean`, and `ThirdPlaceSeries/Link.lean`
> (`R3`); `[Lean]` for statement-level inspections of deep period and archimedean sub-packages (`R2`);
> `[Paper]` for citations to Alpöge's `remark.pdf` and Masullo's draft; `[Community]` for public
> community guides; `[Expository]` for classical Arakelov/theta-period background and worked examples;
> `[Open]` for unread deep proof cones (`11,914` to `14,172` modules).

In Chapter 8 we saw how $m$ composed theta lifts accumulate high $\mathfrak p_w$-adic divisibility
at places $w$ of the CM host field $E$ lying over inert rational primes (`Conclusion1`,
`WeilJacquetShalikaLaw.lean:97`) [Lean, read]. Local divisibility by itself, however, proves nothing:
inside the completion $E_w$, the number $0$ is divisible by $\mathfrak p_w^N$ for every $N \ge 1$,
and even a nonzero global algebraic integer $x \in \mathcal O_E$ can be divisible by a huge prime
power if its archimedean absolute values $\lvert \sigma(x) \rvert_\infty$ are allowed to grow just as
fast!

To extract a global numerical inequality — bounding `ASK` from above by `MAIN` plus controlled errors
— we need the number-field analogue of $\sum_P \operatorname{ord}_P(\Phi) \le \deg(\Phi)$ in
Stepanov's polynomial proof. In the Lean archive, this local-to-global engine is split across two
nodes:

- **Node P9 (`SlopeIneq`, `height_chain`, `divisor_inequality_explicit`):** J.-B. Bost's Arakelov
  slope inequality `[Bost1996]`, `[Bost2001]` (building on Gillet–Soulé arithmetic intersection
  theory `[GilletSoule1990]`), formalized from scratch in `LatticeSlopes/` and `HarderNarasimhan/`
  with **tiny import cones (`1` to `742` modules) that we have read and verified in full (`R3`)**
  [Lean, read]!
- **Node P10 (`FrameHerm`, `LinkS`, `LinkG`):** the Hilbert–Schmidt near-orthogonality inequality on
  almost-orthogonal period frames (`StatementFrame.lean`, `R3`) and the global automorphic period
  inputs (`GlobalTheoremInputs.lean`, `R3` at interface level; `11,914`–`14,172` modules in the
  deep Rallis / Siegel–Weil / Chowla–Selberg proof cones, `R2`) [Lean, read] / [Lean].

---

## 9.1 Motivation: from the product formula $\prod_v \lvert x \rvert_v = 1$ to Bost's slope inequality

Start in rank $1$ over $\mathbb Q$ [Expository]. Suppose $x \in \mathbb Z$ is **nonzero**, satisfies
$p_1^{a_1}\cdots p_r^{a_r} \mid x$ at finite primes, and has archimedean size $\lvert x \rvert_\infty \le C$.
Taking logarithms of $\prod_i p_i^{a_i} \le \lvert x \rvert_\infty \le C$ immediately yields
**Liouville's fundamental inequality**:
$$\sum_{i=1}^r a_i \log p_i \le \log C.$$
Look at how Arakelov geometry rewrites this one-line inequality in the language of **Hermitian
lattices** `[GilletSoule1990]`, `[Bost1996]` [Expository]:

- Equip $V_1 = \mathbb R$ with the standard norm $\lVert 1 \rVert_1 = 1$ (lattice $L_1 = \mathbb Z$,
  covolume $1$, Arakelov degree $\widehat{\deg}(L_1) := -\log\operatorname{covol}(L_1) = 0$).
- Equip $V_2 = \mathbb R$ with the norm $\lVert 1 \rVert_2 = 1$, and let $M \subset L_2 = \mathbb Z$
  be the sublattice $M := N\mathbb Z$ where $N = \prod_i p_i^{a_i}$; its covolume is $N$, so its
  Arakelov degree is $\widehat{\deg}(M) = -\log N$, while $\widehat{\deg}(L_2) = 0$, or equivalently
  if we rescale the target lattice to $L_2' := N\mathbb Z$, multiplication by $x$ is a **nonzero**
  $\mathbb Z$-linear map $T : \mathbb Z \to N\mathbb Z$ ($1 \mapsto x \in N\mathbb Z$) of archimedean
  operator norm $\lVert T \rVert_{\mathrm{op}} = \lvert x \rvert_\infty \le C$.
- Comparing degrees of $L_1 = \mathbb Z$ ($\widehat{\deg} = 0$) and $L_2' = N\mathbb Z$
  ($\widehat{\deg} = -\log N$) says:
  $$\widehat{\deg}(L_1) \le \widehat{\deg}(L_2') + \log \lVert T \rVert_{\mathrm{op}}
  \iff 0 \le -\log N + \log C \iff \sum_{i=1}^r a_i \log p_i \le \log C!$$

Why can we **not** just write $\widehat{\deg}(L_1) \le \widehat{\deg}(L_2) + r \log\lVert T \rVert_{\mathrm{op}}$
when $T : L_1 \to L_2$ is a nonzero map between lattices of **rank $r > 1$**?

Try $r = 2$! Take $L_1 = \mathbb Z^2$ ($\widehat{\deg} = 0$) and $L_2 = p^{100}\mathbb Z \oplus p^{-1000}\mathbb Z$
($\widehat{\deg}(L_2) = -\log(p^{-900}) = 900\log p \gg 0$), and let $T(u, v) = (p^{100} u, 0)$ have
image inside the **tiny-degree** first summand $p^{100}\mathbb Z$ ($\widehat{\deg} = -100\log p$) while
completely missing the huge-degree second summand $p^{-1000}\mathbb Z$! Looking only at total degrees
$\widehat{\deg}(L_1)$ and $\widehat{\deg}(L_2)$ tells you nothing when $T$ drops rank or lands in an
unbalanced sublattice!

**Bost's slope inequality** (`[Bost1996]`, §4.1; `[Bost2001]`, §3.2; formalized as `Formalism.HN.SlopeIneq`
at `src/Formalism/HarderNarasimhan/Statement.lean:91`) [Lean, read] solves both problems at once by
introducing the **normalized slope** $\mu(L) := \frac{\widehat{\deg}(L)}{\operatorname{rk}(L)}$, the
**maximum sublattice slope** $\mu_{\max}(L) := \sup_{0 \neq S \subseteq L} \mu(S)$, and the **minimum
quotient slope** $\mu_{\min}(L) := \inf_{Q \neq 0} \mu(Q)$:

1. For **any** nonzero map $T : L_1 \to L_2$ of operator norm $\lVert T \rVert_{\mathrm{op}} \le K$,
   its image $\operatorname{im}(T) \subseteq L_2$ satisfies
   $$\mu_{\min}(L_1) - \log K \le \mu_{\min}\bigl(\operatorname{im}(T)\bigr) \le \mu\bigl(\operatorname{im}(T)\bigr) \le \mu_{\max}(L_2)$$
   (`SlopeIneq`, `HarderNarasimhan/Statement.lean:91`, and `imageStep`, `FinalCor.lean:9`) [Lean, read]!
2. Better yet, if we construct $u$ **nearly orthogonal** vectors $v_1, \dots, v_u \in \operatorname{im}(T)$
   whose Gram matrix $\bigl(\langle v_i, v_j \rangle\bigr)_{1 \le i, j \le u}$ has positive diagonal
   and exponentially tiny off-diagonal defect (`LinkS`), then those $u$ vectors **cannot collapse into
   a low-rank subspace** — they force $\operatorname{im}(T)$ to carry $u$ independent directions of
   controlled slope (`FrameHerm`, `StatementFrame.lean:11`), turning $u$ units of `ASK` divisibility
   into $u$ units of global height bound!

---

## 9.2 Worked examples

Let us work out two concrete rank-$2$ examples by hand, directly mirroring two explicit `example` /
test constructions built inside the Lean archive itself [Lean, read]!

### 9.2.1 The Harder–Narasimhan polygon of $L_x = \mathbb Z e_0 \oplus \mathbb Z(2 e_1)$ (`Example.lean`)

In `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean:18–351` [Lean, read], the
archive constructs a complete worked Euclidean lattice example `polygon_worked_example : Example`.
Equip $V = \mathbb R^2$ with its standard orthonormal basis $(e_0, e_1)$, and consider the rank-$2$
lattice
$$L_x := \mathbb Z\,e_0 \oplus \mathbb Z\,(2 e_1).$$

Compute its invariants by hand (`Example.lean:92–351`):

1. **Covolume, degree, and total slope:** The fundamental rectangle $[0, 1] \times [0, 2]$ has
   Euclidean volume $\operatorname{covol}(L_x) = 2$ (`covol_Lx`, `:92`), so
   $$\widehat{\deg}(L_x) = -\log 2, \qquad \mu(L_x) = \frac{\widehat{\deg}(L_x)}{2} = -\frac{1}{2}\log 2.$$
2. **Every nonzero saturated rank-$1$ sublattice $S \subset L_x$:** A primitive vector in $L_x$ has
   the form $v = a\,e_0 + b\,(2 e_1) = (a, 2b)$ with $(a, b) \in \mathbb Z^2 \setminus \{(0, 0)\}$ and
   $\gcd(a, b) = 1$. Its Euclidean length is $\lVert v \rVert = \sqrt{a^2 + 4 b^2} \ge 1$ (attained at
   $(a, b) = (\pm 1, 0)$, i.e., $S_1 = \mathbb Z\,e_0$), so
   $$\mu\bigl(\mathbb Z v\bigr) = \widehat{\deg}\bigl(\mathbb Z v\bigr) = -\log\sqrt{a^2 + 4b^2} \le 0,
   \qquad\text{with equality at } S_1 = \mathbb Z\,e_0.$$
   Hence **$\mu_{\max}(L_x) = 0$**, achieved uniquely by $S_1 = \mathbb Z\,e_0$!
3. **Quotient slope $\mu_{\min}(L_x)$ and Harder–Narasimhan filtration:** Orthogonal projection of
   $L_x$ onto $S_1^\perp = \mathbb R\,e_1$ gives the rank-$1$ quotient lattice $Q_1 = L_x / S_1 \cong \mathbb Z\,(2 e_1)$
   of covolume $2$ and slope $\mu(Q_1) = -\log 2$. For any other rank-$1$ quotient $L_x / \mathbb Z(a, 2b)$
   ($\gcd(a,b)=1$), exactness of covolumes $\operatorname{covol}(L_x) = \operatorname{covol}(S)\operatorname{covol}(L_x/S)$
   gives
   $$\mu(L_x / S) = \widehat{\deg}(L_x) - \widehat{\deg}(S) = -\log 2 + \frac{1}{2}\log(a^2 + 4b^2) \ge -\log 2$$
   (attained at $(a, b) = (\pm 1, 0)$). Thus **$\mu_{\min}(L_x) = -\log 2$**, and the
   Harder–Narasimhan filtration $0 \subsetneq \mathbb Z e_0 \subsetneq L_x$ has decreasing slopes
   $(0,\ -\log 2)$, whose sum $0 + (-\log 2) = -\log 2$ recovers $\widehat{\deg}(L_x)$
   (`polygon_worked_example`, `Example.lean:351`) [Lean, read]!

### 9.2.2 Rank-$2$ near-orthogonality versus collapse, and why metric ties cannot slip (`not_tied_two`)

Now test Bost's inequality on two rank-$2$ maps $T : \mathbb Z^2 \to 3^4 \mathbb Z^2$ from standard
$L_1 = \mathbb Z^2$ ($\mu_{\min}(L_1) = 0$) into $L_2 = 3^4 \mathbb Z^2$ ($\mu_{\max}(L_2) = -4\log 3$),
each sending the basis vectors $e_1, e_2$ to columns $v_1 = T(e_1), v_2 = T(e_2) \in 3^4 \mathbb Z^2$
of Euclidean length $\le C$ [Expository]:

- **Collapsed (collinear) columns:** Suppose $v_1 = v_2 = (81, 0)$ ($\lVert v_i \rVert = 81 = 3^4$).
  Here $\langle v_1, v_2 \rangle = 81^2$ is **not** small — the two columns are parallel! So
  $\operatorname{im}(T) = \mathbb Z\,(81, 0)$ has **rank $1$**, not rank $2$, and we extract only
  **one** copy of $4\log 3 \le \log C$, not two!
- **Nearly orthogonal columns:** Suppose $v_1, v_2 \in 3^4 \mathbb Z^2$ satisfy $\lVert v_1 \rVert, \lVert v_2 \rVert \le C$
  and $\lvert \langle v_1, v_2 \rangle \rvert \le \eta C^2$ with $\eta$ tiny (or better:
  $\lVert v_1 \rVert^2, \lVert v_2 \rVert^2 \ge b$ and $\lvert \langle v_1, v_2 \rangle \rvert \le \eta b$
  with $\eta < 1$). Then the $2 \times 2$ Gram determinant is
  $$\det\begin{pmatrix} \lVert v_1 \rVert^2 & \langle v_1, v_2 \rangle \\ \langle v_2, v_1 \rangle & \lVert v_2 \rVert^2 \end{pmatrix}
  \ge b^2(1 - \eta^2) > 0!$$
  Positivity of the Gram determinant **forces $\operatorname{rk}(\operatorname{im} T) = 2$**; even
  quantitatively, since $\operatorname{im}(T) \subseteq 3^4 \mathbb Z^2$ has covolume at least
  $(3^4)^2 = 3^8$, Hadamard's inequality $3^{16} \le \operatorname{covol}(\operatorname{im} T)^2 \le \lVert v_1 \rVert^2 \lVert v_2 \rVert^2 \le C^4$
  yields **$2 \times 4\log 3 = 8\log 3 \le 2\log C$** — **both** columns pay their full $3$-adic
  divisibility into the global bound!

*(Sanity check inside `DivisionHeightBoundStatement.lean:1425–1860`.)* At the bottom of
`DivisionHeightBoundStatement.lean`, the archive includes four concrete `R3` sanity checks over a
three-place model `K_3` [Lean, read]: `toyCoreOne_divClauses` (`:1425`) and `clauses_shift` (`:1589`)
verify that `DivClauses` is inhabited on a concrete lattice chain; `height_three` (`:1647`) checks a
$2$-step composite with step constants $K_0 = 2$ and $K_1 = 2^{-1}$ whose product $K_0 K_1 = 1$ adds
$\log 2 + (-\log 2) = 0$ to the slope; and `not_tied_two` (`:1816`) proves `IsEmpty (ChainTie ...)`
when an intermediate Hermitian metric is mis-scaled by a factor of $2$, confirming that `ChainTie`
genuinely enforces compatibility between consecutive steps!

---

## 9.3 Definitions

We now record the exact Lean definitions of nodes **P9** and **P10**.

### 9.3.1 Euclidean and Arakelov Hermitian lattices, $\mu_{\max}$, $\mu_{\min}$, and `SlopeIneq`

The archive develops Harder–Narasimhan and Bost slope theory cleanly in two stages: first for general
Euclidean lattices in finite-dimensional real inner-product spaces (`LatticeSlopes/` and
`HarderNarasimhan/Statement.lean`), and then over all places of a number field $E$ via restriction of
scalars (`HarderNarasimhan/StatementPl.lean`) [Lean, read].

**Definition 9.1 (Lattice degree, slopes $\mu_{\max}, \mu_{\min}$, and `SlopeIneq`, `src/Formalism/LatticeSlopes/Statement.lean:15,21,23,25` and `src/Formalism/HarderNarasimhan/Statement.lean:17,29,32,91`).**
Let $(V, \langle \cdot, \cdot \rangle)$ be a finite-dimensional real (or complex Hermitian) inner
product space, and let $L \subset V$ be a discrete $\mathbb Z$-submodule (`IsLat L`, `:17`, spanning
$\mathbb R \cdot L$ of rank $\operatorname{rk}(L) = \dim_{\mathbb R}(\mathbb R \cdot L)$):

1. **Covolume, Arakelov degree, and slope (`covol`, `rk`, `deg`, `slope`, `LatticeSlopes/Statement.lean:15, 21, 23, 25`).**
   With respect to any $\mathbb Z$-basis $(b_1, \dots, b_r)$ of $L$, set
   $\operatorname{covol}(L) := \sqrt{\det(\langle b_i, b_j \rangle)_{1 \le i,j \le r}} > 0$
   (with $\operatorname{covol}(0) = 1$), and define [Lean, read]
   $$\widehat{\deg}(L) := -\log\operatorname{covol}(L),
   \qquad
   \mu(L) := \begin{cases} \dfrac{\widehat{\deg}(L)}{\operatorname{rk}(L)} & \text{if } \operatorname{rk}(L) > 0, \\ 0 & \text{if } \operatorname{rk}(L) = 0.\end{cases}$$
2. **Maximum sublattice slope and minimum quotient slope (`muMax`, `muMin`, `HarderNarasimhan/Statement.lean:29, 32`).**
   For a nonzero lattice $L \neq 0$, define [Lean, read]:
   - $\mu_{\max}(L) := \sup\bigl\{\mu(S) : S \subseteq L\text{ nonzero sublattice}\bigr\}$ (attained by
     a unique maximal destabilizing saturated sublattice `hnStep L`, `HNStep` at `:64`);
   - $\mu_{\min}(L) := \inf\bigl\{\mu(L / S) : S \subsetneq L\text{ saturated proper sublattice}\bigr\}$,
     where the quotient lattice $L / S$ is equipped with the induced metric on $S^\perp \cap (\mathbb R \cdot L)$
     (`quot`, `LatticeSlopes/Statement.lean:35`; dual to $-\mu_{\max}(L^\vee)$ by `Duality`,
     `HarderNarasimhan/Statement.lean:119`).
3. **Bost's slope inequality (`Formalism.HN.SlopeIneq`, `src/Formalism/HarderNarasimhan/Statement.lean:91`, and number-field `SlopeIneqMean`, `src/Formalism/HarderNarasimhan/StatementPl.lean:148`).**
   `SlopeIneq : Prop` asserts that for every pair of nonzero lattices $L_1 \subset V_1$, $L_2 \subset V_2$,
   every $K > 0$, and every $\mathbb Z$-linear map $T : V_1 \to V_2$ with $T(L_1) \subseteq L_2$,
   $T(L_1) \neq \{0\}$, and operator norm $\lVert T(v) \rVert \le K \lVert v \rVert$ for all
   $v \in \mathbb R \cdot L_1$ [Lean, read]:
   $$\mu_{\min}(L_1) \le \mu_{\max}(L_2) + \log K,
   \qquad\text{and in fact}\qquad
   \mu_{\min}(L_1) - \log K \le \mu_{\min}\bigl(T(L_1)\bigr)$$
   (`imageStep`, `FinalCor.lean:9`). Over a number field $E$ of degree $d = [E : \mathbb Q]$,
   `StatementPl.lean` (`:29, 55, 60, 64, 67, 70, 133, 148`) equips projective $\mathcal O_E$-lattices
   with place-by-place local norms/valuations, defines the map height
   $\mathrm{htMap}(T) := \sum_v \log^+ \lVert T_v \rVert_{\mathrm{op}}$ (`:60`) and fractional-ideal
   `Twist` (`:133`), and states the normalized number-field Bost inequality `SlopeIneqMean` (`:148`)
   [Lean, read].

### 9.3.2 Composite $m$-step chains (`KerChain`, `ChainTie`, `DivClauses`)

**Definition 9.2 (Tied $m$-step operator chains and `DivClauses`, `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:248,321,553` and `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:44,63`).**

1. **Tied $m$-step chain (`KerChain` and `ChainTie`, `DivisionHeightBoundStatement.lean:248, 321`).**
   A `KerChain` specifies Hermitian $\mathcal O_E$-modules $\mathcal E_0, \mathcal E_1, \dots, \mathcal E_m$
   linked by $\mathcal O_E$-linear step operators $T_j : \mathcal E_{j-1} \to \mathcal E_j$
   ($1 \le j \le m$). A `ChainTie` (`:321`) witnesses that at every step $j$ and every place $v$, the
   domain metric on $\mathcal E_{j-1}$ used by $T_j$ agrees with the codomain metric produced by
   $T_{j-1}$ and satisfies $\lVert T_{j, v} \rVert_{\mathrm{op}} \le K_{j, v}$ [Lean, read].
2. **Global divisibility-and-height clauses (`Formalism.L2.DIV.DivClauses`, `:553`).** Packages the
   $m$-step composite map $T = T_m \circ \cdots \circ T_1 : \mathcal E_0 \to \mathcal E_m$ together
   with fractional-ideal divisibility $T(\Lambda_0) \subseteq I_u^{-1} \Lambda_m$ (supplied by
   Chapter 8's `Conclusion1`), the archimedean height bound $\mathrm{htMap}(T) \le \sum_{j=1}^m H_j$,
   and the resulting Arakelov quotient-slope inequality on $I_u \cdot T(\Lambda_0) \subseteq \Lambda_m$
   [Lean, read].

### 9.3.3 Almost-orthogonal frame bounds (`FrameHerm`) and global inputs (`LinkG`, `LinkS`)

**Definition 9.3 (`FrameHerm` and `LinkG`, `LinkS`, `src/Formalism/HarderNarasimhan/StatementFrame.lean:11,49` and `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:45,65,91,94,138,152,158`).**

1. **Almost-orthogonal frame slope inequality (`FrameHerm` and `FrameHermSharp`, `StatementFrame.lean:11, 49`).**
   Suppose $u$ vectors (or rank-$1$ period blocks) in a Hermitian lattice $L$ of maximum slope
   $\mu_{\max}(L)$ have diagonal norm scale controlled by $b$ against ambient trace budget $HH$, with
   off-diagonal Gram-matrix inner-product error bounded by $\eta$ and diagonal projection defect $e$.
   `FrameHerm` (`:11`) and `FrameHermSharp` (`:49`) bound the sum of slopes across the $u$-frame from
   below by [Lean, read]
   $$u\,\mu_{\max}(L)\text{ contribution} \ \ge\ \text{diagonal main term} - 4 u \log\Bigl(1 + \frac{HH}{u}\Bigr) - \bigl(2\eta + 4\sqrt{e}\bigr)\,HH.$$
2. **Global automorphic period inputs (`LinkG` and `LinkS`, `GlobalTheoremInputs.lean:138, 152`).**
   Inside `GlobalTheoremInputs` (`:158`, combining `LinkN` at `:45`, `BesselId` at `:65`, `LinkDIV` /
   `LinkDIVt` at `:91, 94`, `LinkG` at `:138`, and `LinkS` at `:152`) [Lean, read]:
   - **`LinkG` (`LinkG_at`, `:122, 138`):** supplies the archimedean period / logarithmic-derivative
     main term (`MAIN`, matching Chowla–Selberg CM periods `[ChowlaSelberg1967]`, Siegel genus masses
     `[Siegel1935b]`, and Rallis inner-product formulas `[Rallis1984b]`, `[Rallis1987]`) and lower
     bounds on the thick-place weights;
   - **`LinkS` (`LinkS_at`, `:145, 152`):** asserts that for distinct chain words on the $m$-step
     family, the normalized off-diagonal Gram defects $\eta_0, \eta_1$ and projection defect $\sqrt{e_0}$
     decay **stretched-exponentially** in the window scale $x$:
     $$\eta_0 \le \exp\bigl(-x^{\varepsilon/8}\bigr), \qquad
     \eta_1 \le \exp\bigl(-x^{\varepsilon/8}\bigr), \qquad
     \sqrt{e_0} \le \exp\bigl(-x^{\varepsilon/8}\bigr).$$

---

## 9.4 Lemmas and proofs

Because the archive's proofs of Bost's slope inequality (`LatticeSlopes/` and `HarderNarasimhan/`),
of the $m$-step composite height bound (`DivisionHeightBoundStatement.lean`), and of the explicit
divisor refinement (`GlobalBoundRefinements.lean`) are completely self-contained (`R3`), we present
their full mathematical proofs below!

### 9.4.1 Haar volume, Gram determinants, and orthogonal-projection rounding (`gram_det_le`, `norm_starProjection_le`)

Bost's slope inequality rests on two gems of elementary Euclidean geometry (`GramDetLe.lean` and
`HarderNarasimhanProofs/SlopeIneq.lean`) [Lean, read]:

**Lemma 9.1 (Full-rank determinant bound and nearest-integer projection bound).**

1. **Operator norm bounds covolume change (`normDet_le_pow_finrank` and `gram_det_le`, `src/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean:9, 81, 126`).**
   *Let $T : E \to F$ be a linear isomorphism between $r$-dimensional Euclidean spaces satisfying
   $\lVert T(v) \rVert \le K \lVert v \rVert$ ($K > 0$) for all $v \in E$. Then $\lvert \det T \rvert \le K^r$.
   Consequently, if $L_1 \subset E$ and $L_2 \subset F$ are full-rank lattices of rank $r$ with
   $T(L_1) \subseteq L_2$ and $T(L_1)$ of rank $r$, then*
   $$\operatorname{covol}(L_2) \le \operatorname{covol}\bigl(T(L_1)\bigr) \le K^r\,\operatorname{covol}(L_1),
   \qquad\text{i.e.,}\qquad
   \widehat{\deg}(L_1) \le \widehat{\deg}\bigl(T(L_1)\bigr) + r\log K \le \widehat{\deg}(L_2) + r\log K.$$
   [Lean, read]
2. **Bounding an operator on $\mathbb R \cdot L$ from lattice-point bounds via nearest-integer rounding (`norm_sum_smul_map_le_mul_of_bounded` and `norm_starProjection_le`, `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean:39, 141`).**
   *Let $L \subset V$ be a lattice generated over $\mathbb Z$ by vectors $s_1, \dots, s_m \in L$, and
   let $f : \mathbb R \cdot L \to W$ be an $\mathbb R$-linear map satisfying
   $\lVert f(g) \rVert \le K \lVert g \rVert$ for **every lattice element $g \in L$** (for example
   when $f = \pi_{S^\perp} \circ T$ where $\lVert T \rVert_{\mathrm{op}} \le K$ on $L$ and
   $\pi_{S^\perp}$ is an orthogonal projection of norm $\le 1$). Then
   $\lVert f(v) \rVert \le K \lVert v \rVert$ holds for **every real vector $v \in \mathbb R \cdot L$**!* [Lean, read]

*Proof.*

1. Let $B_E(0, 1)$ and $\overline{B}_F(0, K)$ denote the unit ball in $E$ and closed radius-$K$ ball
   in $F$, which have positive finite $r$-dimensional Lebesgue/Haar measures $\operatorname{vol}(B_E(0, 1)) = \operatorname{vol}(B_F(0, 1)) = \omega_r > 0$
   and $\operatorname{vol}(\overline{B}_F(0, K)) = K^r \omega_r$ (`GramDetLe.lean:25–78`). Since
   $\lVert T(v) \rVert \le K \lVert v \rVert$, we have $T(B_E(0, 1)) \subseteq \overline{B}_F(0, K)$.
   By the change-of-variables formula for Haar measure under a linear map,
   $$\lvert \det T \rvert\,\omega_r = \operatorname{vol}\bigl(T(B_E(0, 1))\bigr)
   \le \operatorname{vol}\bigl(\overline{B}_F(0, K)\bigr) = K^r\,\omega_r,$$
   so dividing by $\omega_r > 0$ gives $\lvert \det T \rvert \le K^r$! Applying this to a $\mathbb Z$-basis
   of $L_1$ (`det_gram_eq_normDet_sq`, `:81`) gives $\operatorname{covol}(T(L_1)) = \lvert \det T \rvert\,\operatorname{covol}(L_1) \le K^r \operatorname{covol}(L_1)$,
   and since $T(L_1) \subseteq L_2$ is a full-rank sublattice of finite index $[L_2 : T(L_1)] \ge 1$,
   $\operatorname{covol}(L_2) = [L_2 : T(L_1)]^{-1}\operatorname{covol}(T(L_1)) \le \operatorname{covol}(T(L_1))$.
   Taking $-\log$ gives the degree inequality (`:126`).
2. Look at the clever rounding trick in `HarderNarasimhanProofs/SlopeIneq.lean:39–75` (or rational
   density in `LatticeSlopesProofs/SlopeInequality.lean:73`): write any $v \in \mathbb R \cdot L$ as
   $v = \sum_{i=1}^m c_i s_i$ with $c_i \in \mathbb R$. For any integer $k \ge 1$, let
   $n_i := \lfloor k c_i + 1/2 \rfloor \in \mathbb Z$ (`round (k * c_i)`), so $\lvert k c_i - n_i \rvert \le \frac{1}{2}$
   and $g_k := \sum_{i=1}^m n_i s_i \in L$ is an **actual lattice element**! Because $\lVert f(g_k) \rVert \le K \lVert g_k \rVert$
   on $L$ and $k v - g_k = \sum_{i=1}^m (k c_i - n_i) s_i$ has norm bounded by
   $M := \frac{1}{2}\sum_{i=1}^m (\lVert f(s_i) \rVert + K \lVert s_i \rVert)$ **independent of $k$**,
   the triangle inequality gives
   $$k\,\lVert f(v) \rVert \le \lVert f(g_k) \rVert + \lVert f(k v - g_k) \rVert
   \le K\,\lVert g_k \rVert + \tfrac{1}{2}\sum_i \lVert f(s_i) \rVert
   \le K\,k\,\lVert v \rVert + M.$$
   Dividing by $k$ and letting $k \to \infty$ gives $\lVert f(v) \rVert \le K \lVert v \rVert$! In
   particular, for an orthogonal projection $\pi_{S^\perp}$ (`norm_starProjection_le`, `:141`),
   $\lVert \pi_{S^\perp}(T(g)) \rVert \le \lVert T(g) \rVert \le K \lVert g \rVert$ on $L_1$, hence on
   all of $\mathbb R \cdot L_1$. $\square$

### 9.4.2 Complete proof of Bost's slope inequality (`SlopeIneq`)

We can now prove Bost's slope inequality in full, following `slopeIneq_of` and
`slope_inequality_general` (`src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean:306, 507`)
[Lean, read]!

**Theorem 9.2 (Bost's slope inequality: `SlopeIneq`).** *Let $L_1 \subset V_1$ and $L_2 \subset V_2$
be nonzero Euclidean lattices, let $K > 0$, and let $T : V_1 \to V_2$ be a linear map such that
$T(L_1) \subseteq L_2$, $T(L_1) \neq \{0\}$, and $\lVert T(v) \rVert \le K \lVert v \rVert$ for all
$v \in \mathbb R \cdot L_1$. Then:*

1. $\mu_{\min}(L_1) - \log K \le \mu_{\min}\bigl(T(L_1)\bigr)$; *and*
2. $\mu_{\min}(L_1) \le \mu_{\max}(L_2) + \log K$.
*(Lean: `slope_inequality_general : SlopeIneq`, `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean:507`,
and `imageStep`, `src/Formalism/HarderNarasimhan/FinalCor.lean:9`; number-field form `slopeIneqMean`,
`src/Formalism/HarderNarasimhan/ShiftInvariance.lean:54`.)* [Lean, read]

*Proof.* First observe that (1) immediately implies (2): since $T(L_1) \subseteq L_2$ is a nonzero
sublattice of $L_2$, we have $\mu_{\min}(T(L_1)) \le \mu(T(L_1)) \le \mu_{\max}(L_2)$ by definition
of $\mu_{\min}$ (taking the improper quotient $T(L_1)/0$) and $\mu_{\max}$.

To prove (1) (`rank_range_eq_and_degree_le` at `:85` and `slopeIneq_of` at `:306`), let
$Q = T(L_1) / S_2$ be **any** nonzero quotient of $T(L_1)$ by a proper saturated sublattice
$S_2 \subsetneq T(L_1)$! Let $\pi : \mathbb R \cdot T(L_1) \to S_2^\perp \cap (\mathbb R \cdot T(L_1))$
be the orthogonal projection, so $Q = \pi(T(L_1))$ is a nonzero lattice of rank $q := \operatorname{rk}(Q) \ge 1$.
Now consider the composite map
$$F := \pi \circ T : \mathbb R \cdot L_1 \longrightarrow S_2^\perp \cap (\mathbb R \cdot T(L_1)).$$
Clearly $F(L_1) = \pi(T(L_1)) = Q \neq \{0\}$, and by Lemma 9.1(2) (`norm_starProjection_le`),
$\lVert F(v) \rVert \le K \lVert v \rVert$ for all $v \in \mathbb R \cdot L_1$.

Define the kernel sublattice $S_1 := L_1 \cap \ker F = \{x \in L_1 : F(x) = 0\}$. Check two facts:

- **$S_1$ is a proper saturated sublattice of $L_1$:** If $n x \in S_1$ for $n \in \mathbb Z \setminus \{0\}$
  and $x \in L_1$, then $n F(x) = F(nx) = 0$ in a real vector space, so $F(x) = 0$ and $x \in S_1$
  (saturation!). And $S_1 \neq L_1$ because $F(L_1) = Q \neq \{0\}$.
- **$F$ induces a linear bijection $\overline{F} : (\mathbb R \cdot L_1) / (\mathbb R \cdot S_1) \xrightarrow{\sim} \mathbb R \cdot Q$
  sending the quotient lattice $L_1 / S_1$ onto $Q$ with operator norm $\le K$:** First,
  $\operatorname{rk}(L_1 / S_1) = \operatorname{rk}(F(L_1)) = q$ by rank-nullity (`rank_range_eq_and_degree_le`, `:85`).
  Second, identify $L_1 / S_1$ metrically with the orthogonal projection $\pi_{S_1^\perp}(L_1) \subset S_1^\perp \cap (\mathbb R \cdot L_1)$.
  For any $u \in S_1^\perp \cap (\mathbb R \cdot L_1)$, $\overline{F}(u) = F(u)$ satisfies
  $\lVert \overline{F}(u) \rVert = \lVert F(u) \rVert \le K \lVert u \rVert$!

Now apply Lemma 9.1(1) (`gram_det_le`) to the full-rank map $\overline{F} : L_1 / S_1 \to Q$ of rank
$q \ge 1$ and operator norm $\le K$:
$$\widehat{\deg}(L_1 / S_1) \le \widehat{\deg}(Q) + q\log K.$$
Dividing both sides by $q = \operatorname{rk}(L_1 / S_1) = \operatorname{rk}(Q) > 0$ gives
$$\mu_{\min}(L_1) \le \mu(L_1 / S_1) \le \mu(Q) + \log K!$$
Look how clean that was — **no induction on Harder–Narasimhan steps was even needed once we passed to
the orthogonal quotient $L_1 / (L_1 \cap \ker F)$**! Since $Q$ was an arbitrary nonzero quotient of
$T(L_1)$, taking the infimum over $Q$ yields $\mu_{\min}(L_1) - \log K \le \mu_{\min}(T(L_1))$. $\square$

### 9.4.3 Composite $m$-step height bounds (`height_chain`, `divClauses_of`, `divisor_inequality_explicit`)

Applying Theorem 9.2 to a tied chain $T = T_m \circ \cdots \circ T_1$ whose output is divisible by a
fractional ideal $I_u^{-1}$ immediately produces the global height-and-divisor theorem of node **P9**!

**Theorem 9.3 ($m$-step composite height bound and explicit divisor inequality).**

1. **Tied $m$-step height additivity (`ChainTie.chain_le` and `height_chain`, `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:344, 641`).**
   *If $(T_1, \dots, T_m)$ is a tied chain (`ChainTie`) with local operator-norm bounds
   $\lVert T_{j, v} \rVert_{\mathrm{op}} \le K_{j, v}$ at each step $j$ and place $v$, then the
   composite $T = T_m \circ \cdots \circ T_1$ satisfies $\lVert T_v \rVert_{\mathrm{op}} \le \prod_{j=1}^m K_{j, v}$
   at every place $v$, so its global logarithmic height is subadditive across the $m$ steps:*
   $$\mathrm{htMap}(T) \le \sum_{j=1}^m \sum_v \log K_{j, v}.$$
   [Lean, read]
2. **From fractional-ideal divisibility and Bost's inequality to `DivClauses` and explicit constants (`divClauses_of`, `DivisionHeightBoundStatement.lean:752`, and `divisor_inequality_explicit`, `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:91`).**
   *When $T(\Lambda_0) \subseteq I_u^{-1} \Lambda_m$ ($I_u = \prod_{w \in \mathrm{supp}} \mathfrak p_w^{-\lfloor e_w \mathrm{sg}(u,w) \rfloor}$),
   rescaling by $I_u$ turns $T$ into an integral map $\Lambda_0 \to I_u^{-1}\Lambda_m$ whose
   Arakelov degree shift equals $\log N_{E/\mathbb Q}(I_u^{-1}) = \sum_{w \in \mathrm{supp}} f_w \lfloor e_w \mathrm{sg}(u, w) \rfloor \log p_w$!
   Combining Theorem 9.2 (`SlopeIneqMean`), part (1) (`height_chain`), and the constant refinement
   $(50 C_0 + 10)(c_e / C_0) \le 60 c_e$ for $C_0 \ge 1$ (`constant_factor_le_sixty`,
   `GlobalBoundRefinements.lean:58`) establishes `DivClauses` (`divClauses_of`, `:752`) and
   `divisor_inequality_explicit` (`GlobalBoundRefinements.lean:91`).* [Lean, read]

*Proof.*

1. Because `ChainTie` (`:321`) identifies the domain metric of $T_j$ with the codomain metric of
   $T_{j-1}$ at every place $v$, standard submultiplicativity of operator norms gives
   $\lVert (T_m \circ \cdots \circ T_1)_v \rVert_{\mathrm{op}} \le \prod_{j=1}^m \lVert T_{j,v} \rVert_{\mathrm{op}} \le \prod_{j=1}^m K_{j,v}$
   (`ChainTie.chain_le`, `:344`). Taking logarithms and summing over places (`height_chain`, `:641`)
   yields $\mathrm{htMap}(T) \le \sum_{j=1}^m \sum_v \log K_{j,v}$.
2. Twisting a rank-$1$ component of $\Lambda_m$ by $\mathfrak p_w^{n_w}$ ($n_w = \lfloor e_w \mathrm{sg}(u,w) \rfloor \ge 0$)
   multiplies its $\mathbb Z$-index covolume by $[\mathcal O_E : \mathfrak p_w^{n_w}] = p_w^{f_w n_w}$,
   subtracting $f_w n_w \log p_w$ from its Arakelov degree (`Twist`, `StatementPl.lean:133`). Notice
   what happens when $p_w = p$ is unramified ($e_w = 1$) or more generally when $e_w f_w$ is summed
   over all places $w \mid p$ in a CM class: up to the floor rounding error $\le f_w \log p_w$
   absorbed into `DataExtra`, $f_w e_w\,\mathrm{sg}(u, w)\log p$ recovers the exact logarithmic
   inert-prime gain `ASK`! Feeding this twisted lattice into Bost's `SlopeIneqMean` and simplifying
   the numerical prefactor $(50 C_0 + 10)\frac{c_e}{C_0} = 50 c_e + \frac{10 c_e}{C_0} \le 60 c_e$
   for $C_0 \ge 1$ (`constant_factor_le_sixty`, `GlobalBoundRefinements.lean:58`) completes
   `divIneqRecord_of` (`:63`) and `divisor_inequality_explicit` (`:91`). $\square$

### 9.4.4 Why near-orthogonality (`FrameHerm` & `LinkS`) and period gains (`LinkG`) close the loop

Finally, let us explain why `FrameHerm` (`StatementFrame.lean:11`) and `LinkS` / `LinkG`
(`GlobalTheoremInputs.lean:138, 152`) take the exact algebraic shapes we met in Chapter 5!

**Proposition 9.4 (Hilbert–Schmidt frame bound and stretched-exponential `LinkS` decay).**

1. **Where `-4 u log(1 + HH/u) - (2η + 4√e) HH` comes from (`FrameHerm`, `src/Formalism/HarderNarasimhan/StatementFrame.lean:11`).**
   *Suppose $v_1, \dots, v_u$ are $u$ period vectors in an ambient Hermitian space with trace budget
   $\sum_i \lVert v_i \rVert^2 \le HH$, normalized Gram matrix $G = I_u + \Delta$ satisfying
   off-diagonal operator/trace defect $\le \eta$ and quotient-projection defect $\le e$. Let $P_Q$ be
   the orthogonal projection onto any quotient $Q$ of rank $q$ inside the Harder–Narasimhan filtration.
   Then $\operatorname{tr}(P_Q G P_Q)$ is bounded below by the main diagonal trace minus
   $(2\eta + 4\sqrt{e})\,HH$ (by Cauchy–Schwarz $\lvert \langle P_Q v, (I - P_Q) \Delta v \rangle \rvert \le \sqrt{e}\,HH$),
   while AM–GM on the nonzero eigenvalues of $P_Q G P_Q$ bounds $-\sum \log \lambda_r$ using the
   concavity defect $4 u \log(1 + HH/u)$.* [Lean, read]
2. **Why `LinkS` ($\eta_0, \eta_1, \sqrt{e_0} \le \exp(-x^{\varepsilon/8})$) kills $x^{c_{HH}} b$ (`GlobalTheoremInputs.lean:152` and `TieGlobal.lean:97`).**
   *Look back at Chapter 5, Section 5.5.3 (`ErrWindows`, `ErrorFormsWeakWindowsFalse.lean:43`): the
   error bracket required*
   $$\bigl(\bar\eta + 4\sqrt{\bar e}\bigr)\,\bigl(x^{c_{HH}} b\bigr) \le K\,x^\varepsilon\,(n_T a).$$
   *Because the ambient Hilbert–Schmidt trace $HH \le x^{c_{HH}} b$ grows as a **large polynomial
   power $x^{c_{HH}}$** of the window scale $x$ (potentially $c_{HH} \gg 100$), a bounded defect
   $\bar\eta \le 1$ (`ErrWindowsWeak`) would blow up completely! Instead, `LinkS` proves
   $\bar\eta, \sqrt{\bar e} \le \exp(-x^{\varepsilon/8})$, and since $\exp(-x^{\varepsilon/8}) \cdot x^{c_{HH}} \to 0$
   faster than every power of $x$, the product $(\bar\eta + 4\sqrt{\bar e})\,x^{c_{HH}} b$ is
   effortlessly $\le K\,x^\varepsilon\,(n_T a)$ for all large $x$ (`TieGlobal.lean:84, 97`)!* [Lean, read]

*(Classical automorphic content of `LinkG` and `LinkS`, and our reading boundary `[Lean]` / `[Open]`.)*
How does the archive prove `LinkG` (`ThirdPlaceSeries/LinkG.lean:13`, import cone **11,914** modules)
and `LinkS` (`ThirdPlaceSeries/LinkAltAltBis.lean:16`, import cone **14,172** modules)?

- **`LinkG` (norms and main terms):** On the $0$-th step (CM torus / definite $U(1)$), the archimedean
  period of a CM theta/Eisenstein datum is governed by the **Chowla–Selberg formula**
  `[ChowlaSelberg1967]` (expressing CM periods in terms of $\Gamma$-values and $\frac{L'}{L}(1, \chi_{\mathrm{CM}})$,
  which is where the $\ell(\mathrm{ch}_C) = \frac{L'}{L}(1, \chi_{\mathrm{CM}})$ and Euler–Mascheroni
  $\gamma$ terms of Chapter 5's `MAIN` originate!) together with **Siegel's mass formula**
  `[Siegel1935b]` for definite Hermitian genera; across the $m$ lifts, norm growth is propagated by the
  **Rallis inner-product formula** `[Rallis1984b]`, `[Rallis1987]` and regularized Siegel–Weil first/second
  term identities `[KudlaRallis1994]` (`remark.pdf` p. 3, items 6–8, 12–13) [Paper; remark p. 3].
- **`LinkS` (near-orthogonality of distinct chain words):** Distinct words $w \neq w'$ in the Hecke/lift
  alphabet differ at some split auxiliary prime of norm $\approx x^\varepsilon$ (or distinct finite-field
  cuspidal Green labels, Chapter 13); self-adjointness / Hecke eigenvalue separation on definite
  unitary spaces (`RelevantZeroGramTerms.lean:23, 37, 72`: `IsURepOn`, `IsFdeg`, `IsDS`) [Lean] plus
  amplified word length $k \ge xm$ drives the off-diagonal inner products down to $\exp(-x^{\varepsilon/8})$.
- **Reading status:** We read `GlobalTheoremInputs.lean`, `TieGlobal.lean`, `ThirdPlaceSeries/LinkG.lean`,
  `ThirdPlaceSeries/LinkAltAltBis.lean`, `GlobalInterpolation/LinkGl.lean`, and `ThirdPlaceSeries/Link.lean`
  in full (`R3` / `[Lean, read]`), and inspected the statement headers of `linkG_concrete5`,
  `theoremS_transport_link_zero`, `famGLmin_of_realPlaceSecondLayer`, and `RelevantZeroGramTerms.lean`
  (`R2` / `[Lean]`), while the `11,914`–`14,172` internal proof modules of `LinkG` and `LinkS` remain
  unread by humans (`[Open]`).

---

## 9.5 Remarks, formalization notes, and Masullo's counterpart

### 9.5.1 A reusable Mathlib-grade gem inside the archive: `LatticeSlopes/` and `HarderNarasimhan/`

One striking discovery from computing import cones on **P9** is how cleanly modular the Arakelov
lattice library is [Lean, read]:

- `HarderNarasimhan/Statement.lean` has import cone **1** (`LatticeSlopes/Statement.lean`, which
  imports **only Mathlib**!);
- the entire proof of Harder–Narasimhan existence/uniqueness, duality, Bost's slope inequality
  `SlopeIneq`, the worked rank-$2$ example `polygon_worked_example`, and the number-field extension
  `ShiftInvariance.lean` sits inside **66 modules**, zero of which touch automorphic forms, theta
  lifts, or literature `Prop`s!

In Kim Morrison's post-verification digestion roadmap (`CONTRIBUTIONS.md`), extracting standalone,
Mathlib-ready theorems from the archive is a central community goal [Community]: `LatticeSlopes/` and
`HarderNarasimhan/` are prime candidates, and we have verified their key proofs at `R3` [Lean, read].

### 9.5.2 Masullo's counterpart

Masullo's draft has **no counterpart** to Hermitian lattices, Harder–Narasimhan filtrations, Bost's
slope inequality, Chowla–Selberg CM periods, or Rallis inner products on unitary groups [Expository]:

- In **Chapters 10–12 (pp. 441–520)** [Paper; Masullo pp. 441–520], Masullo computes traces of
  convolution/projection operators on Hardy–Sobolev completions over the **abelian idele class group
  $C_F = \mathbb A_F^\times / F^\times$** ($\mathrm{GL}_1$), where characters of compact abelian pieces
  are strictly orthogonal by Pontryagin duality — except along the zeros of $L(s, \chi)$ themselves,
  where close vertical pairs of zeros destroy uniform biorthogonal bounds (`chapters/02-the-story-so-far.md`,
  p. 451 after (10.3.1.18)) [Community]!
- Notice the ironic role reversal: Masullo needs exact spectral biorthogonality of zero-eigenmodes
  (which fails when zeros cluster on $\Re s = 1/2$), whereas the Lean archive works on **compact
  definite unitary spaces** (whose automorphic eigenbases are genuinely orthogonal in $L^2$) and only
  needs **approximate** orthogonality $\exp(-x^{\varepsilon/8})$ of concrete chain-word period vectors
  (`LinkS`), paying for non-exactness cleanly via `FrameHerm`!

---

## 9.6 Lean counterpart for this chapter

| Declaration | File:line | Mathematical content / role in Sections 9.2–9.4 | Tag |
|---|---|---|---|
| `covol`, `rk`, `deg`, `slope`, `muMax`, `IsSaturated`, `quot`, `GramDetLe`, `SlopeInequality` | `src/Formalism/LatticeSlopes/Statement.lean:15,21,23,25,30,32,35,59,75` | Definition 9.1(1): Euclidean lattice covolume, Arakelov degree $-\log\operatorname{covol}$, slope $\widehat{\deg}/\operatorname{rk}$, and orthogonal quotients. | [Lean, read] |
| `normDet_le_pow_finrank`, `det_gram_eq_normDet_sq`, `gram_det_le` | `src/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean:9,81,126` | Lemma 9.1(1): Haar unit-ball volume proof of $\lvert\det T\rvert \le K^r$ and full-rank covolume inequality. | [Lean, read] |
| `norm_sum_smul_le_of_int`, `slopeInequality_of` | `src/Formalism/LatticeSlopes/LatticeSlopesProofs/SlopeInequality.lean:73,111` | Rational-density proof of operator-norm extension and base slope inequality. | [Lean, read] |
| `IsLat`, `muMax`, `muMin`, `hnStep`, `slopeList`, `hnPoly`, `MuChar`, `HNStep`, `HNSlopes`, `SlopeIneq`, `Duality`, `Example` | `src/Formalism/HarderNarasimhan/Statement.lean:17,29,32,36,39,42,54,64,74,91,119,127` | Definition 9.1(2)–(3): Harder–Narasimhan filtration, $\mu_{\max}$, $\mu_{\min}$, duality, and `SlopeIneq` (import cone 1). | [Lean, read] |
| `muChar_of`, `slope_characterization` | `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/MuChar.lean:21,173` | Characterization of slopes via sublattices and quotients. | [Lean, read] |
| `norm_sum_smul_map_le_mul_of_bounded`, `rank_range_eq_and_degree_le`, `norm_starProjection_le`, `slopeIneq_of_lemma`, `slopeIneq_of`, `slope_inequality_general` | `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean:39,85,141,252,306,507` | Lemma 9.1(2) and Theorem 9.2: nearest-integer `round(k*c_i)` projection bound and complete proof of Bost's `SlopeIneq`. | [Lean, read] |
| `Lx`, `covol_Lx`, `example_of`, `polygon_worked_example` | `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean:18,92,228,351` | Section 9.2.1: worked rank-$2$ lattice $\mathbb Z e_0 \oplus \mathbb Z(2e_1)$ with $\mu_{\max} = 0$, $\mu_{\min} = -\log 2$. | [Lean, read] |
| `slopeIneq`, `slopeIneqMean`; `imageStep`, `hnCor` | `src/Formalism/HarderNarasimhan/ShiftInvariance.lean:43,54`; `src/Formalism/HarderNarasimhan/FinalCor.lean:9,33` | Theorem 9.2: metric-shift invariance, mean-normalized number-field `SlopeIneqMean` (import cone 66), and image-slope corollary. | [Lean, read] |
| `ht`, `opNormAt`, `htMap`, `muDef`, `muMaxDef`, `muMinDef`, `Twist`, `SlopeIneqMean` | `src/Formalism/HarderNarasimhan/StatementPl.lean:29,55,60,64,67,70,133,148` | Definition 9.1(3): number-field operator heights `htMap`, fractional-ideal `Twist`, and `SlopeIneqMean`. | [Lean, read] |
| `FrameHerm`, `FrameHermSharp` | `src/Formalism/HarderNarasimhan/StatementFrame.lean:11,49` | Definition 9.3(1) and Proposition 9.4(1): Hilbert–Schmidt almost-orthogonal $u$-frame slope bound producing `-4u log(1+HH/u) - (2η+4√e)HH`. | [Lean, read] |
| `RecNums.divIneq`, `complex_height_cast`, `KerChain`, `ChainTie`, `ChainTie.chain_le`, `ChainTie.chain`, `DivClauses`, `exists_cu`, `height_chain`, `divClauses_of`, `division_height_bound_statement`, `toyCoreOne_divClauses`, `clauses_shift`, `height_three`, `not_tied_two` | `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:131,209,248,321,344,358,553,585,641,752,991,1425,1589,1647,1816` | Definition 9.2, Section 9.2.2, and Theorem 9.3: tied $m$-step operator chains, `height_chain`, `divClauses_of`, and metric-mismatch counterexample `not_tied_two` (import cone 742). | [Lean, read] |
| `recAux`, `constant_factor_le_sixty`, `divIneqRecord_of`, `divisor_inequality_explicit`, `good_twisted_lattice` | `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:44,58,63,91,186` | Theorem 9.3(2): explicit constant simplification $(50 C_0 + 10)(c_e/C_0) \le 60 c_e$ and twisted-lattice divisor inequality (import cone 130). | [Lean, read] |
| `LinkV_at`, `LinkN_at`, `LinkN`, `DIVinN_at`, `DIVinN`, `BesselId`, `LinkDIV_at`, `LinkDIV`, `LinkDIVt`, `LinkG_at`, `LinkG`, `LinkS_at`, `LinkS`, `GlobalTheoremInputs`, `LinkGLOBAL` | `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:18,40,45,59,62,65,77,91,94,122,138,145,152,158,162` | Definition 9.3(2) and Proposition 9.4(2): global period/gain interface `LinkG`, stretched-exponential near-orthogonality `LinkS` ($\le \exp(-x^{\varepsilon/8})$), and `GlobalTheoremInputs` (import cone 296). | [Lean, read] |
| `ChainTied`, `tie_global` | `src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97,116` | Proposition 9.4(2): combines `GlobalTheoremInputs` (`LinkDIVt`, `LinkG`, `LinkS`, `DIVinN`) to produce `ChainTied`. | [Lean, read] |
| `closed_linkG_of_concrete5`; `closed_linkS_of_alt_bis`; `link_gl`; `closed_link` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkG.lean:13`; `…/ThirdPlaceSeries/LinkAltAltBis.lean:16`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkGl.lean:14`; `…/ThirdPlaceSeries/Link.lean:20` | Top wrapper proofs closing `LinkG`, `LinkS`, and `LinkGLOBAL` (`R3` for these wrapper files; their `11,914`–`14,172` imported automorphic/period modules are `R2` / `[Open]`). | [Lean, read] |
| `IsURepOn`, `IsFdeg`, `IsDS` | `src/Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean:23,37,72` | Statement-level (`R2`) unitary representation, formal-degree, and discrete-series predicates underlying Gram-matrix off-diagonal bounds. | [Lean] |

**Summary of the chapter.** Generalizing Liouville's rank-$1$ product-formula inequality to higher
rank requires Bost's Arakelov slope inequality $\mu_{\min}(L_1) - \log K \le \mu_{\min}(T(L_1)) \le \mu_{\max}(L_2)$
`[Bost1996]`, which the archive proves cleanly from Haar volume and nearest-integer orthogonal-projection
rounding in just 66 Mathlib-based modules (`SlopeIneq`, Theorem 9.2) [Lean, read]. Iterating across a
tied $m$-step chain (`height_chain`, `divClauses_of`, `divisor_inequality_explicit`, Theorem 9.3) and
controlling $u$ nearly orthogonal period vectors via `FrameHerm` and stretched-exponential Gram decay
`LinkS` ($\le \exp(-x^{\varepsilon/8})$, Proposition 9.4) turns Chapter 8's inert-prime divisibility
into the global `ASK - MAIN` chain inequality — *except* for one crucial algebraic loss at every lift:
the **Hecke congruence denominator**, to which we turn in Chapter 10!
