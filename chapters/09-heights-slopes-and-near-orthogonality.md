# Chapter 9. Heights, slopes, and near-orthogonality

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs read
> in full across `LatticeSlopes/`, `HarderNarasimhan/`, `DivisionHeightBoundStatement.lean`,
> `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean`, `GlobalTheoremInputs.lean`, `TieGlobal.lean`, `ThirdPlaceSeries/LinkG.lean`,
> `ThirdPlaceSeries/LinkAltAltBis.lean`, `GlobalInterpolation/LinkGl.lean`, and `ThirdPlaceSeries/Link.lean`
> (`R3`), and for the local translation and two-limit bodies cited in §9.4.26
> and the compact-dual coordinate-density chain cited in §9.4.27;
> `[Lean]` for statement-level inspections of deep period and archimedean sub-packages (`R2`);
> `[Paper]` for citations to Alpöge's `remark.pdf` and Masullo's draft; `[Community]` for public
> community guides; `[Expository]` for classical Arakelov/theta-period background and worked examples;
> `[Open]` for unread deep proof cones (`12,612` to `15,578` modules).

In Chapter 8 we saw how $m$ composed theta lifts accumulate high $\mathfrak p_w$-adic divisibility
at places $w$ of the CM host field $E$ lying over inert rational primes (`Conclusion1`,
`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97`) [Lean, read]. Local divisibility by itself, however, proves nothing:
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
  with **tiny import cones (`1` to `763` modules) that we have read and verified in full (`R3`)**
  [Lean, read]!
- **Node P10 (`FrameHerm`, `LinkS`, `LinkG`, `LinkDIV`):** the Hilbert–Schmidt near-orthogonality
  inequality on almost-orthogonal period frames (`StatementFrame.lean`, `R3`) and the global
  automorphic/gain interfaces (`GlobalTheoremInputs.lean`, `R3` at interface level; `12,612`–`15,578`
  modules in the deep Rallis / Siegel–Weil / Chowla–Selberg proof cones, `R2`) [Lean, read] / [Lean].

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
   (`SlopeIneq`, `src/Formalism/HarderNarasimhan/Statement.lean:91`, and `imageStep`, `src/Formalism/HarderNarasimhan/FinalCor.lean:9`) [Lean, read]!
2. Better yet, if we construct $u$ **nearly orthogonal** vectors $v_1, \dots, v_u \in \operatorname{im}(T)$
   whose Gram matrix $\bigl(\langle v_i, v_j \rangle\bigr)_{1 \le i, j \le u}$ has positive diagonal
   and exponentially tiny off-diagonal defect (`LinkS`), then those $u$ vectors **cannot collapse into
   a low-rank subspace** — they force $\operatorname{im}(T)$ to carry $u$ independent directions of
   controlled slope (`FrameHerm`, `src/Formalism/HarderNarasimhan/StatementFrame.lean:11`), turning $u$ units of `ASK` divisibility
   into $u$ units of global height bound!

---

## 9.2 Worked examples

Let us work out two concrete rank-$2$ examples by hand, directly mirroring two explicit `example` /
test constructions built inside the Lean archive itself [Lean, read]!

### 9.2.1 The Harder–Narasimhan polygon of $L_x = \mathbb Z e_0 \oplus \mathbb Z(2 e_1)$ (`src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean`)

In `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean:18–351` [Lean, read], the
archive constructs a complete worked Euclidean lattice example `polygon_worked_example : Example`.
Equip $V = \mathbb R^2$ with its standard orthonormal basis $(e_0, e_1)$, and consider the rank-$2$
lattice
$$L_x := \mathbb Z\,e_0 \oplus \mathbb Z\,(2 e_1).$$

Compute its invariants by hand (`src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean:92–351`):

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
   (`polygon_worked_example`, `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean:351`) [Lean, read]!

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

*(Sanity check inside `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:1425–1860`.)* At the bottom of
`DivisionHeightBoundStatement.lean`, the archive includes four concrete `R3` sanity checks over a
three-place model `K_3` [Lean, read]: `toyCoreOne_divClauses` (`:1425`) and `clauses_shift` (`:1589`)
verify that `DivClauses` is inhabited on a concrete lattice chain; `height_three` (`:1647`) checks a
$2$-step composite with operator scales $2$ and $2^{-1}$ bounded via the logarithmic bound vector
`![2, -1]` ($2^2 = 4 \le e^2$ and $(2^{-1})^2 = \frac{1}{4} \le e^{-1}$), whose sum $2 + (-1) = 1$
bounds the composite height; and `not_tied_two` (`:1816`) proves `IsEmpty (ChainTie ...)`
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

1. **Covolume, Arakelov degree, and slope (`covol`, `rk`, `deg`, `slope`, `src/Formalism/LatticeSlopes/Statement.lean:15, 21, 23, 25`).**
   With respect to any $\mathbb Z$-basis $(b_1, \dots, b_r)$ of $L$, set
   $\operatorname{covol}(L) := \sqrt{\det(\langle b_i, b_j \rangle)_{1 \le i,j \le r}} > 0$
   (with $\operatorname{covol}(0) = 1$), and define [Lean, read]
   $$\widehat{\deg}(L) := -\log\operatorname{covol}(L),
   \qquad
   \mu(L) := \begin{cases} \dfrac{\widehat{\deg}(L)}{\operatorname{rk}(L)} & \text{if } \operatorname{rk}(L) > 0, \\ 0 & \text{if } \operatorname{rk}(L) = 0.\end{cases}$$
2. **Maximum sublattice slope and minimum quotient slope (`muMax`, `muMin`, `src/Formalism/HarderNarasimhan/Statement.lean:29, 32`).**
   For a nonzero lattice $L \neq 0$, define [Lean, read]:
   - $\mu_{\max}(L) := \sup\bigl\{\mu(S) : S \subseteq L\text{ nonzero sublattice}\bigr\}$ (attained by
     a unique maximal destabilizing saturated sublattice `hnStep L`, `HNStep` at `:64`);
   - $\mu_{\min}(L) := \inf\bigl\{\mu(L / S) : S \subsetneq L\text{ saturated proper sublattice}\bigr\}$,
     where the quotient lattice $L / S$ is equipped with the induced metric on $S^\perp \cap (\mathbb R \cdot L)$
     (`quot`, `src/Formalism/LatticeSlopes/Statement.lean:35`; dual to $-\mu_{\max}(L^\vee)$ by `Duality`,
     `src/Formalism/HarderNarasimhan/Statement.lean:119`).
3. **Bost's slope inequality (`Formalism.HN.SlopeIneq`, `src/Formalism/HarderNarasimhan/Statement.lean:91`, and number-field `SlopeIneqMean`, `src/Formalism/HarderNarasimhan/StatementPl.lean:148`).**
   `SlopeIneq : Prop` asserts that for every pair of nonzero lattices $L_1 \subset V_1$, $L_2 \subset V_2$,
   every $K > 0$, and every $\mathbb Z$-linear map $T : V_1 \to V_2$ with $T(L_1) \subseteq L_2$,
   $T(L_1) \neq \{0\}$, and operator norm $\lVert T(v) \rVert \le K \lVert v \rVert$ for all
   $v \in \mathbb R \cdot L_1$ [Lean, read]:
   $$\mu_{\min}(L_1) \le \mu_{\max}(L_2) + \log K,
   \qquad\text{and in fact}\qquad
   \mu_{\min}(L_1) - \log K \le \mu_{\min}\bigl(T(L_1)\bigr)$$
   (`imageStep`, `src/Formalism/HarderNarasimhan/FinalCor.lean:9`). Over a totally complex number field $K$ with `nPl K` infinite
   places $v \in \mathrm{InfinitePlace}(K)$, `src/Formalism/HarderNarasimhan/StatementPl.lean` (`:29, 55, 60, 64, 67, 70, 133, 148`)
   equips finitely generated $\mathcal O_K$-submodules $L \subset V$ with Hermitian Gram matrices
   $X_v$ at the **archimedean** places $v \in \mathrm{InfinitePlace}(K)$, defines the mean
   archimedean logarithmic squared operator norm [Lean, read]
   $$\mathrm{htMap}(b, X, b', X', \varphi) := \frac{1}{\mathrm{nPl}(K)} \sum_{v \in \mathrm{InfinitePlace}(K)} \log\bigl(\mathrm{opNormAt}_v(\varphi)^2\bigr)$$
   (`:60`, summed over infinite places only, with no finite places and no $\log^+$!), records
   archimedean metric rescaling `Twist` (`:133–146`, where scaling $X_v' = c_v X_v$ for $c_v > 0$ at
   $v \in \mathrm{InfinitePlace}(K)$ shifts `slope` by $t = \frac{1}{\mathrm{nPl}(K)}\sum_v \log c_v$
   and `muDef` by $2t$), and states the normalized number-field Bost inequality `SlopeIneqMean`
   (`:148`) [Lean, read]. (Non-Archimedean fractional-ideal lattice shifting $I_u \cdot \Lambda$
   enters separately as `shiftLat Nu sg` in `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:555, 561`.)

### 9.3.2 Composite $m$-step chains (`KerChain`, `ChainTie`, `DivClauses`)

**Definition 9.2 (Tied $m$-step operator chains and `DivClauses`, `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:248,321,553,565,641` and `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:44,63`).**

1. **Tied $m$-step chain (`KerChain` and `ChainTie`, `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:248, 321`).**
   A `KerChain` specifies Hermitian $\mathcal O_K$-modules $\mathcal E_0, \mathcal E_1, \dots, \mathcal E_m$
   linked by $K$-linear step operators $T_j : \mathcal E_{j-1} \to \mathcal E_j$ ($1 \le j \le m$). A
   `ChainTie` (`:321–329`) records the algebraic and isometric step-compatibility identities (`hmm`,
   `coF`, `coL`, `metF`, `metL`, `kerF`, `kerC`) identifying the domain Hermitian metric of $T_j$
   with the codomain metric of $T_{j-1}$, while logarithmic step operator-norm bounds
   $\mathrm{opNormAt}_v(T_j)^2 \le \exp(B_{j,v})$ are supplied separately in `CBData` / `nK_of_cb`
   (`:565`) and combined with `ChainTie` in `height_chain` (`:641`) [Lean, read].
2. **Global divisibility-and-height clauses (`Formalism.L2.DIV.DivClauses`, `:553`, and `shiftLat`, `:555, 561`).**
   Packages the $m$-step composite map $T = T_m \circ \cdots \circ T_1$ together with the
   non-Archimedean fractional-ideal lattice twist `shiftLat Nu sg` (`:555, 561`, fed by Chapter 8's
   period divisibility at $I_u$), the archimedean height bound $\mathrm{htMap}(T)$, and the resulting
   Arakelov slope inequality [Lean, read].

### 9.3.3 Almost-orthogonal frame bounds (`FrameHerm`) and global inputs (`LinkG`, `LinkDIV`, `LinkS`)

**Definition 9.3 (`FrameHerm` and `LinkDIV`, `LinkG`, `LinkS`, `GlobalTheoremInputs`, `src/Formalism/HarderNarasimhan/StatementFrame.lean:11,49` and `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:65,77,91,94,122,138,145,152,158`).**

1. **Almost-orthogonal frame slope inequality (`FrameHerm` and `FrameHermSharp`, `src/Formalism/HarderNarasimhan/StatementFrame.lean:11, 49`).**
   Let $I$ be a finite non-empty index set parametrizing block maps $B_i : V_i \to W$ ($i \in I$) sending
   source lattices $N_i \subset V_i$ into a full-rank target lattice $\mathrm{cc} \subset W$. Let
   $s \in \mathbb R$ be a weighted mean lower bound on $\mathrm{muDef}(N_i) - \mathrm{htMap}(B_i)$
   (`:27`), let $u \in \mathbb R$ ($u > 0$) be the **continuous real slope-gap parameter** bounding
   $\mathrm{muMaxDef}(N_i) - \mathrm{htMap}(B_i) \le s + u$ (`:29`), and let $HH \in \mathbb R$
   ($HH \ge 0$) be an **upper bound on the Harder–Narasimhan slope span**
   $s - \mathrm{muMinDef}(b', X', \mathrm{cc}) \le HH$ (`:30`), with diagonal isometric defect
   $\le e \in [0, 1/4]$ (`:32–35`) and normalized frame Gram trace correlation $\le 1 + \eta$
   (`:36–45`). Then `FrameHerm` (`:11–47`) bounds the **total target slope** $\mathrm{muDef}(b', X', \mathrm{cc})$
   from below by [Lean, read]
   $$s - \log\lvert I \rvert - u\Bigl(1 + 4\log\Bigl(1 + \frac{HH}{u}\Bigr)\Bigr) - \bigl(2\eta + 4\sqrt{e}\bigr)\,HH \le \mathrm{muDef}(b', X', \mathrm{cc}),$$
   and `FrameHermSharp` (`:49–84`) establishes the sharpened form without $-\log\lvert I\rvert - u$:
   $$s - 4 u \log\Bigl(1 + \frac{HH}{u}\Bigr) - \bigl(2\eta + 4\sqrt{e}\bigr)\,HH \le \mathrm{muDef}(b', X', \mathrm{cc}).$$
2. **Global gain, period, and near-orthogonality inputs (`LinkG`, `LinkDIV`, `LinkS`, and `GlobalTheoremInputs`, `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:77, 91, 94, 122, 138, 145, 152, 158`).**
   `GlobalTheoremInputs Fm Cabs CH C0` (`:158–160`) conjoins the five family predicates
   `LinkG Fm ∧ LinkS Fm C0 ∧ LinkIRR Fm ∧ LinkDIV Fm Cabs CH ∧ LinkMu Fm` [Lean, read]:
   - **`LinkG` (`LinkG_at`, `:122–136, 138`):** supplies the **non-Archimedean inert-prime gain lower
     bound**, bounding $\bigl(\sum_{j=1}^m L.\mathrm{gain}(j, w)\bigr) - L.\tau(w)$ from below by
     $\sum_{j=1}^m \sum_{t \in \mathrm{TT}_w} \bigl(\mathrm{vonMangoldtClassSum}(j, t, p) - \mathrm{loG}(p)\bigr) - m\cdot\mathrm{flG}(p)$
     across inert places $w$;
   - **`LinkDIV` (`LinkDIV_at`, `:77–91`, deduced via `LinkDIVt` at `:94` from `LinkEta` and `DIVinN`):**
     carries `BesselId` (`:65`) and the **archimedean dual-slope / period main-term upper bound**
     $\mu_{\mathrm{Dual}} + h(u) - \mathrm{Fo} \le L.\mathrm{MAIN}(u) + \text{error}$ (`:82–84`, where
     Chowla–Selberg CM periods `[ChowlaSelberg1967]`, Siegel genus masses `[Siegel1935b]`, and Rallis
     inner-product formulas `[Rallis1984b]`, `[Rallis1987]` enter!);
   - **`LinkS` (`LinkS_at`, `:145, 152`):** asserts that for distinct chain words $u \neq u'$ on the
     $m$-step family, the normalized off-diagonal Gram defects $\eta_0, \eta_1$ and diagonal defect
     $\sqrt{e_0}$ decay **stretched-exponentially** in the window scale $x$:
     $$\eta_0 \le \exp\bigl(-x^{\varepsilon/8}\bigr), \qquad
     \eta_1 \le \exp\bigl(-x^{\varepsilon/8}\bigr), \qquad
     \sqrt{e_0} \le \exp\bigl(-x^{\varepsilon/8}\bigr).$$

---

## 9.4 Lemmas and proofs

Because the archive's proofs of Bost's slope inequality (`LatticeSlopes/` and `HarderNarasimhan/`),
of the $m$-step composite height bound (`DivisionHeightBoundStatement.lean`), and of the explicit
divisor refinement (`src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean`) are completely self-contained (`R3`), we present
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
   and $\operatorname{vol}(\overline{B}_F(0, K)) = K^r \omega_r$ (`src/Formalism/LatticeSlopes/LatticeSlopesProofs/GramDetLe.lean:25–78`). Since
   $\lVert T(v) \rVert \le K \lVert v \rVert$, we have $T(B_E(0, 1)) \subseteq \overline{B}_F(0, K)$.
   By the change-of-variables formula for Haar measure under a linear map,
   $$\lvert \det T \rvert\,\omega_r = \operatorname{vol}\bigl(T(B_E(0, 1))\bigr)
   \le \operatorname{vol}\bigl(\overline{B}_F(0, K)\bigr) = K^r\,\omega_r,$$
   so dividing by $\omega_r > 0$ gives $\lvert \det T \rvert \le K^r$! Applying this to a $\mathbb Z$-basis
   of $L_1$ (`det_gram_eq_normDet_sq`, `:81`) gives $\operatorname{covol}(T(L_1)) = \lvert \det T \rvert\,\operatorname{covol}(L_1) \le K^r \operatorname{covol}(L_1)$,
   and since $T(L_1) \subseteq L_2$ is a full-rank sublattice of finite index $[L_2 : T(L_1)] \ge 1$,
   $\operatorname{covol}(L_2) = [L_2 : T(L_1)]^{-1}\operatorname{covol}(T(L_1)) \le \operatorname{covol}(T(L_1))$.
   Taking $-\log$ gives the degree inequality (`:126`).
2. Look at the clever rounding trick in `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean:39–75` (or rational
   density in `src/Formalism/LatticeSlopes/LatticeSlopesProofs/SlopeInequality.lean:73`): write any $v \in \mathbb R \cdot L$ as
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

1. **Tied $m$-step height additivity (`ChainTie.chain_le` and `height_chain`, `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:344, 565, 641`).**
   *If $(T_1, \dots, T_m)$ is a tied chain (`ChainTie`, `:321`) equipped with archimedean step
   operator-norm bounds $\mathrm{opNormAt}_v(T_j)^2 \le \exp(B_{j, v})$ at each step $j$ and each
   infinite place $v \in \mathrm{InfinitePlace}(K)$ (`CBData`, `:565`), then the composite
   $T = T_m \circ \cdots \circ T_1$ satisfies
   $\mathrm{opNormAt}_v(T)^2 \le \exp\bigl(\sum_{j=1}^m B_{j, v}\bigr)$ at every $v \in \mathrm{InfinitePlace}(K)$,
   so its mean archimedean height is subadditive across the $m$ steps:*
   $$\mathrm{htMap}(T) \le \frac{1}{\mathrm{nPl}(K)} \sum_{j=1}^m \sum_{v \in \mathrm{InfinitePlace}(K)} B_{j, v}.$$
   [Lean, read]
2. **From fractional-ideal lattice shifts and Bost's inequality to `DivClauses` and explicit constants (`shiftLat` and `divClauses_of`, `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:555, 752`, and `divisor_inequality_explicit`, `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:91`).**
   *Shifting the source lattice by the fractional ideal $I_u = \prod_{w \in \mathrm{supp}} \mathfrak p_w^{-\lfloor e_w \mathrm{sg}(u,w) \rfloor}$
   via `shiftLat Nu sg` (`:555, 561`) changes its $\mathbb Z$-index covolume by
   $N_{K/\mathbb Q}(I_u)$ and shifts its Arakelov degree in proportion to
   $\sum_{w \in \mathrm{supp}} f_w \lfloor e_w \mathrm{sg}(u, w) \rfloor \log p_w$ (tracked in
   `LinkMu` / `NprimeMuR` at `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:69, 74`, whereas archimedean metric rescaling
   is `Twist` at `src/Formalism/HarderNarasimhan/StatementPl.lean:133`)! Combining Theorem 9.2 (`SlopeIneqMean`), part (1)
   (`height_chain`), and the constant refinement $(50 C_0 + 10)(c_e / C_0) \le 60 c_e$ for
   $C_0 \ge 1$ (`constant_factor_le_sixty`, `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:58`) establishes `DivClauses`
   (`divClauses_of`, `:752`) and `divisor_inequality_explicit` (`src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:91`).* [Lean, read]

*Proof.*

1. Because `ChainTie` (`:321`) identifies the domain Hermitian metric of $T_j$ with the codomain
   metric of $T_{j-1}$ at every infinite place $v \in \mathrm{InfinitePlace}(K)$, submultiplicativity
   of Euclidean operator norms gives $\mathrm{opNormAt}_v(T_m \circ \cdots \circ T_1) \le \prod_{j=1}^m \mathrm{opNormAt}_v(T_j)$
   (`ChainTie.chain_le`, `:344`). Squaring, taking logarithms, and averaging over $v \in \mathrm{InfinitePlace}(K)$
   (`height_chain`, `:641`) yields $\mathrm{htMap}(T) \le \frac{1}{\mathrm{nPl}(K)}\sum_{j=1}^m \sum_v B_{j,v}$.
2. Replacing a lattice component by its fractional-ideal multiple $\mathfrak p_w^{-n_w}\Lambda$
   ($n_w = \lfloor e_w \mathrm{sg}(u,w) \rfloor \ge 0$, `shiftLat` at `:555, 561`, using the index
   multiplicativity of `HtGram` at `src/Formalism/HarderNarasimhan/StatementPl.lean:83–91`) shifts its normalized Arakelov slope by
   the exact finite-place contribution $\mathrm{sz}(w, \mathrm{sg}(u, w))$ up to the rounding error
   bounded in `NprimeMuR` (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:69`), while any archimedean scalar adjustment of
   the Hermitian form shifts slopes additively by `Twist` (`src/Formalism/HarderNarasimhan/StatementPl.lean:133`). Up to the floor
   rounding error absorbed into `DataExtra`, summing $f_w e_w\,\mathrm{sg}(u, w)\log p_w$ over inert
   places recovers the logarithmic inert-prime gain `ASK`! Feeding this shifted lattice into Bost's
   `SlopeIneqMean` and simplifying $(50 C_0 + 10)\frac{c_e}{C_0} = 50 c_e + \frac{10 c_e}{C_0} \le 60 c_e$
   for $C_0 \ge 1$ (`constant_factor_le_sixty`, `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:58`) completes
   `divIneqRecord_of` (`:63`) and `divisor_inequality_explicit` (`:91`). $\square$

### 9.4.4 Why near-orthogonality (`FrameHerm` & `LinkS`), inert gains (`LinkG`), and period bounds (`LinkDIV`) close the loop

Finally, let us explain why `FrameHerm` / `FrameHermSharp` (`src/Formalism/HarderNarasimhan/StatementFrame.lean:11, 49`) and
`LinkG`, `LinkDIV`, `LinkS` (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:91, 138, 152`) take the exact algebraic shapes
we met in Chapter 5!

**Proposition 9.4 (Hilbert–Schmidt frame bound and stretched-exponential `LinkS` decay).**

1. **Where `-u(1 + 4 log(1 + HH/u)) - (2η + 4√e) HH` comes from (`FrameHerm` and `FrameHermSharp`, `src/Formalism/HarderNarasimhan/StatementFrame.lean:11, 49`).**
   *Let $(B_i)_{i \in I}$ be a finite family of nonzero block maps into $\mathrm{cc} \subset W$ with
   mean slope lower bound $s$, continuous slope-gap parameter $u > 0$
   ($\mathrm{muMaxDef}(N_i) - \mathrm{htMap}(B_i) \le s + u$), Harder–Narasimhan slope span
   $s - \mathrm{muMinDef}(\mathrm{cc}) \le HH$, normalized frame correlation $\le 1 + \eta$, and
   diagonal isometric defect $\le e \le 1/4$. Layer-cake / corank-share integration across Harder–Narasimhan
   steps (`CorankShare/StatementFR.lean` imported at `:3`) trades the maximum-slope excess $u$ against
   the slope span $HH$ at logarithmic cost $4 u \log(1 + HH/u)$ (plus $-\log\lvert I\rvert - u$ in the
   unsharpened form `FrameHerm` at `:46`, removed in `FrameHermSharp` at `:84`), while Cauchy–Schwarz
   bounds the off-diagonal and isometric trace defects by $(2\eta + 4\sqrt{e})\,HH$, yielding the lower
   bound on $\mathrm{muDef}(b', X', \mathrm{cc})$.* [Lean, read]
2. **Why `LinkS` ($\eta_0, \eta_1, \sqrt{e_0} \le \exp(-x^{\varepsilon/8})$) kills $x^{c_{HH}} b$ (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:152` and `src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97, 116`).**
   *Look back at Chapter 5, Section 5.5.3 (`ErrWindows`, `src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:43`): the
   error bracket required*
   $$\bigl(\bar\eta + 4\sqrt{\bar e}\bigr)\,\bigl(x^{c_{HH}} b\bigr) \le K\,x^\varepsilon\,(n_T a).$$
   *Because the Harder–Narasimhan slope span $HH \le x^{c_{HH}} b$ (`LinkDIV_at` at `:78`) can grow as
   a **large polynomial power $x^{c_{HH}}$** of the window scale $x$, a bounded defect $\bar\eta \le 1$
   (`ErrWindowsWeak`) would blow up completely! Instead, `LinkS` proves
   $\bar\eta, \sqrt{\bar e} \le \exp(-x^{\varepsilon/8})$, and since $\exp(-x^{\varepsilon/8}) \cdot x^{c_{HH}} \to 0$
   faster than every power of $x$, `GlobalTheory.Top.link_gl` (`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkGl.lean:14`)
   deduces `ChainTied` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97`) from `GlobalTheoremInputs`, and `ChainTied.core_of`
   (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:116`) packages `ChainTied` with `HostFacts` into `ChainCore`!* [Lean, read]

*(Classical automorphic content of `LinkG`, `LinkDIV`, and `LinkS`, and our reading boundary `[Lean]` / `[Open]`.)*
How does the archive discharge `GlobalTheoremInputs` across `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkG.lean:13`
(`GlobalTheory.Top.closed_linkG_of_duty`, leaf-inclusive import cone **12,612** modules),
`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkAltAltBis.lean:16` (`GlobalTheory.Top.link_alt_alt_bis`, import cone **15,578**
modules), `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:197` (`LinkDIVt`), and `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Link.lean:20`
(`GlobalTheory.Top.link_alt_alt_alt`, proving `SmallLevelRankEq`)?

- **`LinkG` (inert-prime valuation gains) and `LinkDIV` (periods and `MAIN`):** `LinkG` (`:122, 138`)
  establishes that the local formal-group / Kudla–Rallis valuation gains across inert primes dominate
  `vonMangoldtClassSum` minus `loG` and `m * flG`, while `LinkDIV` (`:77, 91`) establishes `BesselId`
  and bounds the dual-lattice / period height by `L.MAIN u`: on the $0$-th step (CM torus / definite
  $U(1)$), CM periods are governed by the **Chowla–Selberg formula** `[ChowlaSelberg1967]` (where the
  $\ell(\mathrm{ch}_C) = \frac{L'}{L}(1, \chi_{\mathrm{CM}})$ and Euler–Mascheroni $\gamma$ terms of
  Chapter 5's `MAIN` originate!) together with **Siegel's mass formula** `[Siegel1935b]`; across the
  $m$ lifts, norm growth is propagated by the **Rallis inner-product formula** `[Rallis1984b]`,
  `[Rallis1987]` and regularized Siegel–Weil first/second term identities `[KudlaRallis1994]`
  (`remark.pdf` p. 4, items 6–9, 12–13) [Paper; remark p. 4].
- **`LinkS` (near-orthogonality of distinct chain words):** Distinct words $u \neq u'$ in the Hecke/lift
  alphabet differ at auxiliary primes or finite-field cuspidal Green labels (Chapter 13);
  self-adjointness / Hecke eigenvalue separation on definite unitary spaces
  (`src/Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean:23, 37, 72`: `IsURepOn`, `IsFdeg`, `IsDS`) [Lean] plus amplified word
  length $k \ge xm$ drives the off-diagonal inner products down to $\exp(-x^{\varepsilon/8})$.
- **Reading status:** We read `GlobalTheoremInputs.lean` (import cone **306**), `TieGlobal.lean`,
  `ThirdPlaceSeries/LinkG.lean`, `ThirdPlaceSeries/LinkAltAltBis.lean`, `GlobalInterpolation/LinkGl.lean`,
  and `ThirdPlaceSeries/Link.lean` in full (`R3` / `[Lean, read]`), and inspected the statement headers
  of `linkG_concrete5`, `theoremS_transport_link_zero`, `famGLmin_of_realPlaceSecondLayer`, and
  `RelevantZeroGramTerms.lean` (`R2` / `[Lean]`), while the `12,612`–`15,578` internal proof modules of
  `LinkG` and `LinkAltAltBis` remain unread by humans (`[Open]`).

### 9.4.5 A positive-semidefinite bound for the period rows

**Motivation.** In the diagonal part of Theorem S, the squared norm of a sum of
operators expands into a double sum over a finite index set. The terms with
different indices can contribute positively, even if the individual squared
norms are known exactly. The archive bounds their combined contribution by
putting the coefficient matrix below a scalar multiple of the identity in
the positive-semidefinite order. This is the matrix estimate used inside
`LinkS`'s diagonal row bounds.

**A two-step Gram calculation [Expository].** Use the convention that the inner
product is conjugate-linear in the first variable. The vectors
$g_1=(\sqrt{2},0)$ and $g_2=(\mathrm{i}/\sqrt{2},\sqrt{3/2})$ have Gram matrix
$\Gamma=\begin{pmatrix}2&\mathrm{i}\\-\mathrm{i}&2\end{pmatrix}$.
Take $a_1,a_2$ in a complex inner-product space.

1. **Factor the slack.** With $c=3$ and $v=(1,\mathrm{i})$, the matrix
   $3I-\Gamma=\begin{pmatrix}1&-\mathrm{i}\\\mathrm{i}&1\end{pmatrix}$
   has entries $v_i\overline{v_j}$.
2. **Contract with the row-vector inner products.** Write
   $Q=\operatorname{Re}\sum_{i,j}\Gamma_{ij}\langle a_i,a_j\rangle$.
   The same slack now gives
   $3(\lVert a_1\rVert^2+\lVert a_2\rVert^2)-Q
   =\lVert a_1-\mathrm{i}a_2\rVert^2$.
   For $a_1=1$ and $a_2=-\mathrm{i}$ in $\mathbb C$, the diagonal terms
   contribute $4$, the two cross terms contribute $1$ each, and the
   slack is zero. The bound is attained at $Q=6$.

**Definition [Lean, read].** In `Terms`, each term $t$ has an operator
`op t`, an auxiliary vector `vec t`, and a row label `rowOf t`. The map
`io` sends each row label to a finite index set $I$. For a subset $S$ of
terms, `part S` is the sum of its operators and `vecPart S i` is the
sum $a_i$ of its vectors with index $i$. The predicate `NormExpansionOn S`
asserts $\lVert\mathrm{part}(S)\rVert^2=Q$ for $\Gamma=\mathrm{GG}$.
The reference sum `PhiEq S` is $\mathrm{Gam1}\sum_i\lVert a_i\rVert^2$.
The cone condition `GGBound Pg` is exactly
$(\mathrm{Pg}\cdot\mathrm{Gam1})I-\Gamma\succeq0$.
Here $M\succeq0$ means $M$ is Hermitian and every scalar quadratic form
$\overline z^{\,T}Mz$ is nonnegative.
Archive references use the joined SHA-256 pinned in [Sources §1](../sources/SOURCES.md#1-the-lean-archive-primary-source).
`src/Formalism/HermitianCurvature/StatementPB.lean:15,55,57,63,86,89`.

**Lemma [Lean, read].** For a finite $I$, any complex inner-product
space, any vectors $a_i$, and any complex coefficient matrix $\Gamma$,
if $cI-\Gamma\succeq0$, then
$$\operatorname{Re}\sum_{i,j}\Gamma_{ij}\langle a_i,a_j\rangle
\le c\sum_i\lVert a_i\rVert^2.$$
The statement is `GramSumLeOfPosSemidef`. Its proof is `t_EqualIota`,
exported as `equal_index`.
`src/Formalism/HermitianCurvature/StatementPB.lean:125`;
`src/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean:602,1279`.

**Proof [Lean, read].**

1. Lean names the matrix hypothesis `hM` and applies
   `Matrix.posSemidef_iff_eq_sum_vecMulVec` to obtain finitely many vectors
   $v_\ell$. The identity `hM'` is its entrywise form
   $(cI-\Gamma)_{ij}=\sum_\ell v_{\ell i}\overline{v_{\ell j}}$.
   The Mathlib factorization transports to a positive operator and uses
   an orthonormal eigenbasis with each eigenvector scaled by the square
   root of its nonnegative eigenvalue.
   `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean:604,605`.
   [Pinned Mathlib factorization, lines 544–566](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/InnerProductSpace/Positive.lean#L544-L566)
2. For each $\ell$, set $b_\ell=\sum_i\overline{v_{\ell i}}a_i$.
   In `hw`, expanding $\langle b_\ell,b_\ell\rangle$ conjugates the
   first scalar, giving the summand
   $v_{\ell i}\overline{v_{\ell j}}\langle a_i,a_j\rangle$.
   In `hsum`, Lean substitutes the factorization and switches the
   finite sums to recover $\sum_\ell\langle b_\ell,b_\ell\rangle$.
   The real part is nonnegative by `hnn`, which applies
   `inner_self_nonneg` to each $b_\ell$.
   `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean:609,616,623`.
3. The identity `hsplit` expands the same expression using
   $cI-\Gamma$. The $cI$ contribution survives only on the diagonal.
   In `hre`, its real part becomes $c\sum_i\lVert a_i\rVert^2$.
   Taking real parts in `hsplit` therefore identifies the difference
   $c\sum_i\lVert a_i\rVert^2-Q$ with the nonnegative sum
   $\sum_\ell\lVert b_\ell\rVert^2$. The last `linarith` uses that
   identity and `hnn` to finish.
   `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean:628,631,636,639`.

The immediate norm consequence `t_PriceOfIota` rewrites the squared norm
by `NormExpansionOn`, applies this lemma to `vecPart S` at
$c=\mathrm{Pg}\cdot\mathrm{Gam1}$, then reassociates multiplication.
It gives $\lVert\mathrm{part}(S)\rVert^2\le\mathrm{Pg}\cdot\mathrm{PhiEq}(S)$.
[Lean, read]
`src/Formalism/HermitianCurvature/StatementPB.lean:133`;
`src/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean:384,388,390,1283`.

**Boundary example [Expository].** Keep the same Gram matrix and vectors,
and try $c=2$. Although $\Gamma$ is positive definite and its diagonal
equals $c$, $2I-\Gamma$ has determinant $-1$. The proposed bound would
give $6\le4$. The cross terms exhaust the extra diagonal allowance when
$c=3$, so the semidefinite boundary suffices and the constant is sharp in
this example.

**From rows to heights.** The two diagonal row estimates consume the
cone lemma in different ways. For the degenerate part,
`kppDiag_of_pairs` bounds the norm by `Pg * PhiEq`, expands the latter
over same-row pairs, then uses an absolute pair bound. For the other
diagonal estimate, `diag_of_abstract` subtracts the identity term and
applies `PairBoundAbstract`. Its proof uses the cone bound separately for
the generic and nongeneric sums. The row estimates give coefficients
$\mathrm{Pg}(A+2\epsilon)$ and $\mathrm{Pg}(\epsilon+\epsilon')$ for their
squared norms relative to the common scale `dd`. The last triangle
inequality is applied to the norms, then squared, so it includes the
mixed term between those sums. The concrete `GGBound` is supplied to
both consumers by `ggBound`. [Lean]
`src/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean:35,72`;
`src/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean:464,500,505,514`;
`src/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/TermOpStmt.lean:135`;
`src/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RowsPos.lean:186,202,210,242`.

Those row estimates are transported as `ClKppDiag` and `ClDiag`.
In the size window, `diag_unproj` adds the degenerate part back to the
diagonal operator minus identity, charging both errors in `eF`.
This supplies the diagonal clause of `LinkS_at`. The distinct-word bound
and the count bound are separate inputs to `linkS_concl`. [Lean]
`src/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/LinkSPos.lean:21,57,126,158`;
`src/Formalism/SharpRestriction/CuspSpanNormBounds/StandingHypothesesHoldFamily.lean:144,186,628`;
`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:145,152`.

At the global interface, `linkGLOBAL_of` feeds `LinkS`, `LinkIRR`
and `LinkDIV`, with the chosen data, into the frame input. The resulting
archimedean frame estimates enter the loss term $(2\eta+4\sqrt e)HH$ of
`FrameHerm`. The height input has a separate source. In
`frameReal_at_of` the nonzero column map already comes with
$\mathrm{htMap}(B_k(u))\le \mathrm{div.h}(u)$. Section 9.4.3 explains how
the composite operator bound in `height_chain` controls such heights and
how the slope comparison uses height together with lattice inclusion and
finite-place gains. The cone lemma supplies one part of the frame estimate
in that comparison. [Lean]
`src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:853,858,871`;
`src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean:679,682`;
`src/Formalism/HarderNarasimhan/StatementFrame.lean:27,46`;
`src/Formalism/HarderNarasimhan/StatementPl.lean:148`;
`src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:641,653`.

**Reading scope.** The two conditional matrix-to-norm proofs above have
been read in full. The concrete arithmetic supplying the matrix bound,
the remaining estimates in the deep `LinkS` cone, and the deep gain
cone of `LinkG` remain [Lean] at cited interfaces and [Open] as
expository work.

---

### 9.4.26 Recovering the formal-degree constant from a translation ray

A ratio of two discrete-series degrees cancels their common Haar constant. In the size estimates of Chapter 9 the field `D.dsig` enters on its own. Its compact-dual normalization fixes the absolute scale of the Vandermonde factor used there. The archive recovers the constant by translating the Harish–Chandra parameter away from the root walls. On this ray, the compact-type dimension has a computable leading term, and a rescaling of the noncompact coordinates makes two coefficient estimates meet at the same Gaussian mass.

**First example.** Let the ordered signature be $(+,-)$ and take $\lambda=(101/2,1/2)$. Its sole gap is $50$, and translation gives $\lambda_t=(101/2+t,1/2)$. The lowest compact type is one-dimensional, of weight $(51+t,0)$. The exponential of the $2$ by $2$ off-diagonal Hermitian matrix with entries $z,\bar z$ has both diagonal entries equal to $\cosh r$, where $r=|z|$. Compact conjugation preserves $r$. The one-dimensional lowest-type compression thus has self-coefficient $(\cosh r)^{-(51+t)}$ by the principal-minor formula below. On the compact-dual Haar, the angular measures have mass one after multiplying the plane polar element $2\pi r\,dr$ by the Jacobian $\sinh(2r)/(2r)$ and the prefactor $1/\pi$. The squared coefficient integral is
$$
\int_0^\infty (\cosh r)^{-2(51+t)}\sinh(2r)\,dr
=\int_1^\infty u^{-51-t}\,du=\frac1{50+t},
\qquad u=\cosh^2 r.
$$
Schur orthogonality gives degree $50+t$. In particular $t/(50+t)\to1$. In the general proof the limit comes from the plane Gaussian of mass $\pi$ and the factor $1/\pi$. Here $\lambda_i-1/2$ is integral, and $h=50>\max\{3,32+8\sqrt2\}+1$ since $\sqrt 2<3/2$. The Vandermonde is $50+t$, the denominator $F_2$ is $1$, and the single step $e_0$ multiplies the degree by $(51+t)/(50+t)$. The lowest type is the torus character $(u,v)\mapsto u^{51+t}$, and the archived compressed family is available at every $t$ by the supplies described below. [Expository]

**Definitions.** Fix a sign pattern $\varepsilon$ on $0,\ldots,n-1$, with $p$ positive and $q$ negative entries, both at least one. Put $m=pq$, $q_0=\min(p,q)$ and $F_j=\prod_{i=0}^{j-1}i!$. Let $\mathcal C$ and $\mathcal N$ be the pairs $i<j$ of equal and unequal signs respectively, so $|\mathcal N|=m$. The archive's `PCoord` stores an unequal-sign pair in reverse order. We denote its coordinate by $z_{ij}$, and the Hermitian matrix $P(z)=\mathrm{pmat}(z)$ has that entry at $(j,i)$ and its conjugate at $(i,j)$, with all other entries zero. The real coordinate dimension is $2m$. For $G=U(\varepsilon)$, the group preserving the diagonal Hermitian form with signs $\varepsilon$, write the polar decomposition as $k\exp P(z)$, let $dk$ be probability Haar on $K=U(p)\times U(q)$, and give each complex coordinate ordinary plane Lebesgue measure. The compact-dual Haar $\mu_{\rm CD}$ on the full group is
$$
d\mu_{\rm CD}=c_{p,q}J(z)\,dz\,dk,\qquad
c_{p,q}=\frac{F_n}{\pi^m F_p F_q}.
$$
Here $J$ is the product over $i<j$ of $\operatorname{sinhc}$ of the eigenvalue differences of $P(z)$, with $\operatorname{sinhc}(0)=1$. The polar measure and its identification with the matched compact-dual density are measure inputs. [Lean] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/PmatIsHermitian.lean:19–25,40–43,75–92`, `HaarMirror.lean:14–42` and `HaarVolumes/OmegaDensityUnique.lean:298–337` under the same directory.

An archive Harish–Chandra parameter is strictly decreasing and satisfies $\lambda_i-(n-1)/2\in\mathbb Z$. Write $\rho_A$ for the half sum of the positive roots in a set $A$. Fix such a $\lambda$ with $|\lambda_i-\lambda_j|\ge h$ for every unequal-sign pair and
$$
h>1+\max\{npq+1,16nq_0+8\sqrt{2q_0}\}=\mathrm{thrStar}(\varepsilon)+1.
$$
Define $D_i=n-1-i$, $\lambda_t=\lambda+tD$ for $t\in\mathbb N$, and $V(\lambda)=\prod_{i<j}(\lambda_i-\lambda_j)$. The lowest compact weight is $\mathrm{lowK}_\varepsilon(\lambda)=\lambda+\rho_{\mathcal N}-\rho_{\mathcal C}$, where the two half sums are over $\mathcal N$ and $\mathcal C$. At each $t$ give an archive compact type $T_t$ at $\mathrm{lowK}_\varepsilon(\lambda_t)$. Its underlying space is finite-dimensional and complex, with a continuous irreducible unitary action of $K$, the complex-linear differential of that action, and a unit vector $w_t$ of the specified diagonal weight killed by the compact positive-root operators. Put $N_t=\dim_\mathbb C T_t$.

For a parameter vector $\mu$ put $\Phi_\mu(z)=\mathrm{Ph}(\mu,P(z))$. It is the sum for $1\le i\le n-1$ of $(\mu_{i-1}-\mu_i+1)\log\Delta_i(\exp P(z))$, where $\Delta_i$ is the leading $i$ by $i$ principal determinant. These determinants are positive because $\exp P(z)$ is positive definite. The operator $\mathcal F_t(z)$, called `fF` in the archive, is $N_t$ times the $dk$-average of the projector on $T_t(k)w_t$ weighted by $\exp[-\mathrm{Ph}(\lambda_t,k^{-1}P(z)k)]$. Write $a_t(z)=\langle w_t,\mathcal F_t(z)w_t\rangle$, with the inner product linear in the second slot. Set
$$
Q(y)=\sum_{(i,j)\in\mathcal N}(j-i)|y_{ij}|^2,\qquad
M=\prod_{(i,j)\in\mathcal N}(j-i),\qquad
\Pi=\frac{\pi^m}{M}.
$$
These are the quadratic form `Qf 0`, the noncompact slope product, and `PiW ε 0`, respectively. The zero in `Qf 0` labels a quadratic form. [Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/FdDefs.lean:15–19`, `PmatIsHermitian.lean:45–71,94–110` and `FdConst.lean:17–52` under the same directory.

**Theorem (conditional local calibration).** Let $d$ be a real function on all real parameter vectors. Assume, for every archive parameter $\mu$ and coordinate $s$,
$$
d(\mu+e_s)=d(\mu)\prod_{j\ne s}\frac{\mu_s+1-\mu_j}{\mu_s-\mu_j}
$$
whenever both endpoints have gap at least $h$ and the target is strictly decreasing. For all natural $t$ give complex Hilbert spaces $H_t$, matrix-to-operator maps $\sigma_t$ into bounded complex-linear operators, and continuous linear maps $j_t:T_t\to H_t$. Impose the following three conditions on an eventual tail of $t$.

1. `FData` holds. The restriction of $\sigma_t$ to the group is a strongly continuous unitary representation, $j_t$ is an isometric $K$-intertwiner, and $j_t^\dagger\sigma_t(\exp P(z))j_t=\mathcal F_t(z)$ for every $z$.
2. There are a complex inner-product space $H'_t$, a matrix-to-operator map $\sigma'_t$ into bounded complex-linear operators whose group restriction is a strongly continuous unitary representation, and a unit vector $w'_t$ in its smooth derived domain of compact highest weight $\mathrm{lowK}_\varepsilon(\lambda_t)$ and Casimir eigenvalue $\mathrm{casVal}(\lambda_t)$. Its self-coefficient on $\exp P(z)$ equals $a_t(z)$ for every $z$. This is the archive's `IsHWSmooth` witness. Assume the uniform tangent pairing estimate stated in the lower-bound proof, with $\mathrm{casVal}(\mu)=\sum_i\mu_i^2-\sum_i\rho_i^2$ and $\rho=\rho_{\mathcal C}+\rho_{\mathcal N}$.
3. `IsFdeg` holds for $\sigma_t$ on $\mu_{\rm CD}$ with degree $d(\lambda_t)$. For $d_t=d(\lambda_t)$ this means $d_t>0$ and for every $v,w,v',w'\in H_t$ the product in the integral below is integrable and satisfies
   $$
   \int_G \langle w,\sigma_t(g)v\rangle\overline{\langle w',\sigma_t(g)v'\rangle}\,d\mu_{\rm CD}(g)
   =\frac{\langle v',v\rangle\langle w,w'\rangle}{d_t}.
   $$

Then $d(\lambda_t)/V(\lambda_t)=d(\lambda)/V(\lambda)>0$ for every $t$, and
$$
\lim_{t\to\infty}\frac{t^mN_t}{d(\lambda_t)}
=c_{p,q}\Pi,\qquad
d(\lambda)=\frac{V(\lambda)}{F_n}=\mathrm{fdegHC}(\lambda).
$$
[Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/ThmFD.lean:21–103`.

**Proof of the translation assertion.** On the ray the $i,j$ gap increases by $(j-i)t$. More generally, adding any weakly decreasing vector $c$ of nonnegative integers maintains the order and shifted integrality and increases each ordered gap by $c_i-c_j\ge0$. Induct on $\sum_i c_i$ to reach $\lambda+c$ by legal unit steps. For a positive sum, let $s$ be the last index with $c_s>0$. Subtracting one there preserves weak decrease, since every entry to its right is zero and every entry to its left was at least $c_s$. The recurrence applies from this predecessor to $\lambda+c$. Each root factor incident to $s$ changes by the corresponding factor in the recurrence, including when $s$ is the second index, since negating both differences preserves their ratio. All other factors cancel. Both Vandermondes are positive, so the quotient by Vandermonde is invariant. Take $c=tD$. The Schur degree is positive at some index in the tail, so the constant quotient transports positivity to every index, including $0$. [Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/FdStep.lean:14–154` and `ProdSubLtEqFactorial.lean:88–158` under the same directory.

**Lemma (rescaled integral bounds).** Use nonnegative integrals, allowing $+\infty$, and set $s_t=t^{-1/2}$ for $t\ge1$. Then
$$
\begin{aligned}
\Pi
&\le \liminf_{t\to\infty} t^m\int |a_t(z)|^2J(z)\,dz,\\
\limsup_{t\to\infty}t^m\int e^{-2\Phi_{\lambda_t}(z)}J(z)\,dz
&\le\Pi.
\end{aligned}
$$

**Proof of the lower bound.** The `TangentPairingStatement` fixes $n,\varepsilon$, a real direction vector $D$, an initial compact weight $\Lambda_0$ and a real radius $R$ first. It gives a constant $C$ uniform in real $t\ge1$, the inner-product space, the representation and parameter and the smooth highest vector of compact weight $tD+\Lambda_0$, and every Lie-algebra direction $Y$ of squared Frobenius norm at most $R^2$. The self-coefficient on $\exp(s_tY)$, multiplied by $\exp(-\sqrt t\operatorname{tr}(\operatorname{diag}(D)Y))$, differs from $\exp(-\mathrm{qForm}(\varepsilon,D,Y)/2)$ by at most $C/\sqrt t$.

Take $\Lambda_0=\mathrm{lowK}_\varepsilon(\lambda)$ and $Y=P(y)$, with $R=\|P(y)\|_F^2+1$ for each fixed $y$. The matrix is Hermitian and anticommutes with the signature matrix, so it is a permitted Lie-algebra direction. Its diagonal vanishes, eliminating the phase. The quadratic form is $-\operatorname{tr}(\operatorname{diag}(D)[Y,\mathrm{partNM}(\varepsilon,D,Y)])$. The projection `partNM` keeps only the upper entry of each unequal-sign pair of $Y$. In the trace the product of lower and upper entries contributes $(D_i-D_j)|y_{ij}|^2=(j-i)|y_{ij}|^2$ once. Thus the coefficient agreement gives $a_t(s_ty)\to e^{-Q(y)/2}$ for every $y$ and $|a_t(s_ty)|^2\to e^{-Q(y)}$.

Each $a_t$ is continuous because the compact-average integrand is jointly continuous and is uniformly continuous on a compact neighborhood of a given $z$ times $K$. The real dilation $z=s_ty$ has determinant $s_t^{2m}=t^{-m}$. Every Jacobian factor is at least one, by $\sinh x\ge x$ for $x\ge0$ and evenness of $\operatorname{sinhc}$. Fatou's lemma then yields
$$
\int e^{-Q(y)}\,dy\le\liminf_t\int |a_t(s_ty)|^2\,dy
\le\liminf_t t^m\int |a_t(z)|^2J(z)\,dz.
$$
For $b=j-i>0$ the plane integral is $2\pi\int_0^\infty r e^{-br^2}\,dr=\pi/b$. Tonelli on the finite product gives $\int e^{-Q(y)}\,dy=\Pi$. [Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/FdPointwise.lean:16–169`, `FdLower.lean:18–72`, `FdLowerA.lean:17–100` and `FdScale.lean:14–33` under the same directory.

**Proof of the upper bound.** Write $k_0=\sqrt{2q_0}$ and $r(z)=\|P(z)\|_F$. To obtain the potential estimates, let $A$ be the first $i$ coordinate indices and write $P(z)=U\operatorname{diag}(\xi)U^\dagger$. Cauchy–Binet gives
$$
\Delta_i(e^{uP(z)})=\sum_{|S|=i} w_S e^{u y_S},\qquad
w_S=|\det U_{A,S}|^2,\qquad y_S=\sum_{j\in S}\xi_j.
$$
The weights sum to one by setting $u=0$. Define $P_{AA}$ to be the leading compression of $P=P(z)$. Comparing coefficients in the identical Cauchy–Binet expansion of $\det(I_A+uP_{AA})$ gives $\sum_S w_S y_S=\operatorname{tr}(P_{AA})=0$. The coefficient of $u^2$ is $\sum_S w_S\sum_{j<k\in S}\xi_j\xi_k=-\operatorname{tr}(P_{AA}^2)/2$. The linear coefficient for the same expansion with $P^2$ gives $\sum_S w_S\sum_{j\in S}\xi_j^2=\operatorname{tr}((P^2)_{AA})$. Hence the second moment is
$$
V_i=\sum_S w_S y_S^2=\operatorname{tr}((P^2)_{AA})-\operatorname{tr}(P_{AA}^2)
=\sum_{b<i\le a}|P_{ab}|^2.
$$
After grouping the signs, $P$ has off-diagonal blocks $B,B^\dagger$. Its nonzero eigenvalues are the positive and negative singular values of $B$, as is seen by applying it to the paired singular vectors. There are at most $q_0$ positive eigenvalues and their squares sum to $r(z)^2/2$. Therefore $|y_S|\le k_0r(z)/2$ for every $S$ by Cauchy–Schwarz.

The inequality $e^x\ge 1+x$ proves $\log\Delta_i(e^P)\ge0$. The log of the weighted exponential sum is convex as a function of $u$, since its second derivative is the variance under the weights proportional to $w_S e^{uy_S}$. Its value at zero is zero. This proves $\Phi_0(uz)\ge u\Phi_0(z)$ for $u\ge1$. For the local inequality assume $k_0r(z)\le e\le 1$. Taylor's formula with integral remainder gives $e^x\ge1+x+(1-e/2)x^2/2$ for $|x|\le e/2$, since $e^{vx}\ge1-e/2$ for $0\le v\le1$. Put $u_0=(1-e/2)V_i/2\le e^2/8$. Then
$$
\log\Delta_i(e^P)\ge \log(1+u_0)\ge u_0(1-u_0/2)
\ge (1-e)V_i/2.
$$
The middle inequality follows by integrating $1/(1+s)\ge 1-s$ on $[0,u_0]$. The last uses $e^2/16\le e/16$, so $(1-e/2)(1-e^2/16)\ge1-e/2-e/16\ge1-e$. Summing the $V_i$ counts each unequal-sign root $j-i$ times. This yields $2\Phi_0(z)\ge(1-e)Q(z)$, while $\Phi_\lambda\ge0$ follows from the nonnegative log determinants and positive adjacent-gap coefficients. The archive uses the same weighted moments with a cubic remainder bound. [Lean, read] A2, `EigenvectorUnitaryMulStar.lean:66–165`, `FiPmatEqFiOneSmulPmat.lean:18–73`, `LseConvexOn.lean:11–143`, `PSpecB.lean:272–318` and `SCoefGeTwoOfHc.lean:34–141,191–199` under `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/`.

If $k_0r(z)\le1/2$, then $Q(z)\ge r(z)^2/2$ gives $\Phi_0(z)\ge r(z)^2/8$. If $k_0r(z)>1/2$, apply the small-ball bound at $z/(2k_0r(z))$ and the scaling inequality. Together they give
$$
\Phi_0(z)\ge\frac1{16}\min\{r(z)^2,r(z)/k_0\}.
$$
The adjacent-gap coefficients give $\Phi_{\lambda_t}=\Phi_\lambda+t\Phi_0$. For each real $x$, $\operatorname{sinhc}(x)=\int_0^1\cosh(ux)\,du\le e^{|x|}$. Each eigenvalue occurs in $n-1$ pairwise differences, so the exponent is bounded by $(n-1)\sum_i|\xi_i|\le(n-1)k_0r(z)$ by the paired singular values above. This gives $J(z)\le\exp((n-1)k_0r(z))$. For fixed $y$, eventually $s_t\rho_P(y)\le1$. The local quadratic estimate and $ts_t^2=1$ thus bound $e^{-2\Phi_{\lambda_t}(s_ty)}J(s_ty)$ above by
$$
\exp\!\bigl(-(1-s_t\rho_P(y))Q(y)+(n-1)k_0s_tr(y)\bigr),
$$
whose limit is $e^{-Q(y)}$.

For a uniform majorant on the tail choose $T=16nq_0+1$, $X=\sqrt T$ and $a=X/k_0$. With $r=r(y)$ and $t\ge T$, the global bound gives
$$
2\Phi_{\lambda_t}(s_ty)\ge\tfrac18\min\{r^2,\sqrt t\,r/k_0\}
\ge \frac{ar}{8}-\frac{a^2}{32}.
$$
The last step uses $(r-a/2)^2\ge0$ for the first term and $\sqrt t\ge X$ for the second. Combining with the Jacobian bound and $s_t\le1/X$ gives an integrand at most $e^{a^2/32}e^{-br}$, where
$$
b=\frac{X}{8k_0}-\frac{(n-1)k_0}{X}=\frac{16q_0+1}{8Xk_0}>0.
$$
Each $|y_{ij}|\le r$, so $e^{-br}\le\prod_{\mathcal N}e^{-b|y_{ij}|/(m+1)}$. The product has finite integral since $\int_{\mathbb C}e^{-c|y|}\,dy=2\pi/c^2$ for $c>0$. The rescaled potential integrands are continuous and nonnegative. The majorant permits reverse Fatou on the shifted sequence starting at $T$. Indeed the integral of a tail supremum dominates the supremum of the tail integrals, and the decreasing tail suprema converge under the integral by domination. The pointwise upper limit, the Gaussian mass, and the same change of variables prove the second inequality. [Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/FdUpper.lean:22–136`, `FdUpperA.lean:14–77`, `FdUpperB.lean:17–206`, `FdCons.lean:14–32` and `HsEighthLeOfSmall.lean:27–93` under the same directory. The continuity and conjugation invariance of the polar Jacobian are used at their cited interfaces.

**Proof of the squeeze.** Put $S_t=t^mN_t/d(\lambda_t)$. The two finite-parameter Schur estimates give, eventually,
$$
c_{p,q}\,t^m\int |a_t(z)|^2 J(z)\,dz
\le S_t\le c_{p,q}\,t^m\int e^{-2\Phi_{\lambda_t}(z)}J(z)\,dz.
$$
To see the factors, sum the group Schur identity over the $N_t^2$ matrix entries on the embedded compact type. In polar coordinates the compact factor is unitary on the compression and drops from its Hilbert–Schmidt norm. This gives $N_t^2/d(\lambda_t)=c_{p,q}\int\|\mathcal F_t(z)\|_{\rm HS}^2J(z)\,dz$. For the rotated vector $v_k=T_t(k)w_t$, compact Schur gives $N_t\int|\langle v_k,v\rangle|^2dk=\|v\|^2$. Apply Cauchy–Schwarz to the product of $\langle u,v_k\rangle$ and $e^{-\mathrm{Ph}(\lambda_t,k^{-1}P(z)k)}\langle v_k,v\rangle$ in the compact average. Taking the supremum over unit $u$ and summing over an orthonormal basis of $v$ bounds the Hilbert–Schmidt square above by $N_t$ times the compact average of the squared potential factor. For the lower bound apply $|\langle v_k,\mathcal F_t(z)v_k\rangle|^2\le\|\mathcal F_t(z)v_k\|^2$, then average and use compact Schur to get $\|\mathcal F_t(z)\|_{\rm HS}^2/N_t$ on the right. Compact conjugation preserves $J(z)\,dz$ in both estimates. Equivariance moves the rotated vector back to $w_t$ in the lower integral. Divide by $N_t>0$. This accounts for the two inequalities using the existing Schur and polar identities. Hence
$$
c_{p,q}\Pi\le\liminf_t S_t\le\limsup_t S_t\le c_{p,q}\Pi.
$$
The archive uses extended nonnegative reals here. The sequence is nonnegative and the limit finite, so the same limit holds in real numbers. The eventual comparison with $S_t$ also bounds the lower integral's limsup and the upper integral's liminf. Thus each of the two rescaled integrals in the lemma converges to $\Pi$ under the theorem's hypotheses. [Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/ThmFD.lean:38–103`, `SumInnerBasisSqEqAdjoint.lean:77–157`, `SumNormAdjointSqEqHsOp.lean:52–166` and `IntegrableOfContinuousCompact.lean:239–359` under the same directory.

**Proof of uniqueness of the constant.** For $(i,j)\in\mathcal C$ let $b_{ij}$ count the opposite-sign indices strictly between $i$ and $j$. Write $g_{ij}(t)=\lambda_i-\lambda_j+t(j-i)$. The compact Weyl formula, applied block by block, gives
$$
N_t=\frac{\prod_{\mathcal C}(g_{ij}(t)+b_{ij})}{F_p F_q}.
$$
Indeed each opposite-sign index outside the interval contributes equally to $\rho_{\mathcal N}(i)$ and $\rho_{\mathcal N}(j)$, and each one inside contributes a difference of one. The compact Weyl shift cancels $-\rho_{\mathcal C}$ in the lowest weight. After dividing by $V(\lambda_t)$ each compact factor therefore contributes $(g_{ij}(t)+b_{ij})/g_{ij}(t)\to1$. Each noncompact factor contributes $t/g_{ij}(t)\to1/(j-i)$. The constant quotient gives
$$
S_t=\frac{V(\lambda)}{d(\lambda)F_pF_q}
\prod_{\mathcal C}\frac{g_{ij}(t)+b_{ij}}{g_{ij}(t)}
\prod_{\mathcal N}\frac{t}{g_{ij}(t)}
\longrightarrow \frac{V(\lambda)}{d(\lambda)F_pF_qM}.
$$
Equating this to $c_{p,q}\Pi=F_n/(F_p F_q M)$ gives $V(\lambda)/d(\lambda)=F_n$. All canceled factors are positive. The root denominator $\prod_{i<j}(j-i)$ is exactly $F_n$ by collecting the factors for each fixed $j$. [Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/RhoNSubNab.lean:15–55`, `FdConst.lean:78–153` and `ProdSubLtEqFactorial.lean:160–205` under the same directory.

**Second example.** Take $U(2,1)$ in ordered signature $(+,-,+)$ and $\lambda=(128,64,0)$. Its coordinates belong to the required shifted lattice. Set $h=64$, since $\mathrm{thrStar}+1=\max\{7,48+8\sqrt2\}+1<61<64$. For $\lambda_t=(128+2t,64+t,0)$ the gaps at $(0,1),(0,2),(1,2)$ are $64+t,128+2t,64+t$. The first and last are noncompact, so
$$
V(\lambda_t)=2(64+t)^3,\qquad
Q(y)=|y_{01}|^2+|y_{12}|^2,\qquad M=1,\qquad \Pi=\pi^2.
$$
The compact root $(0,2)$ passes over the negative coordinate, giving $b_{02}=1$. The two half sums agree, so $\mathrm{lowK}(\lambda_t)=\lambda_t$ and $N_t=129+2t$. Since $F_3=2$ and $F_2F_1=1$, the polar prefactor is $2/\pi^2$ and the squeezed limit is $2$. The root-side limit is $524288/d(\lambda)$. Thus $d(\lambda)=262144$ and $d(\lambda_t)=(64+t)^3$. Writing $u=64+t$, translation from $t$ to $t+1$ uses $e_0,e_0,e_1$ in order. The triples of gaps $(g_{01},g_{02},g_{12})$ are
$$
(u,2u,u),\quad (u+1,2u+1,u),\quad (u+2,2u+2,u),\quad (u+1,2u+2,u+1).
$$
Every noncompact gap stays at least $64$. Multiplying the changed root factors gives
$$
\frac{(u+1)(2u+1)}{u(2u)}\,
\frac{(u+2)(2u+2)}{(u+1)(2u+1)}\,
\frac{(u+1)^2}{(u+2)u}=\frac{(u+1)^3}{u^3}.
$$
The compact model here is $\operatorname{Sym}^{128+2t}(\mathbb C^2)$ on indices $0,2$ with the $U(1)$ character of weight $64+t$ on index $1$. The monomials of degree $128+2t$ give its dimension $129+2t$. In both examples the archive supplies the compact types and representation families at every $t$ by the following interfaces, since the rays have gap at least $h+t$. The examples concern the real-group theorem. The ambient $D7$ record has rank $n=D.R.r\ge6$. [Expository]

**The family and its consumers.** The function `fdcD` chooses an `IsDS` degree on $\mu_{\rm CD}$ at the parameter, with a zero fallback when no witness exists. `fdc_ds_exists` and `fdcGood_unique` supply existence and choice independence on the original gap domain. `fdc_step` chooses both representations and applies `fdeg_ratio_V` on the same Haar, then uses uniqueness at the target. The tensor argument in `Sandwich` supplies this ratio at its interface. The earlier conditional ratio derived from `HCFdeg` takes the numerical formula as input. Its unused producer and `up_G` are distinct from the calls traced here. The unit-bound application in `linkS_all` takes its ratio from `AllHyp.s47`. This is the boundary of the previous ratio audit.

For each $t$, `fdc_cd` uses the gap bound $h+t$, which exceeds $\mathrm{thrStar}+1$. This implies the standard gap threshold $npq+1$ and the seed's threshold $8nq_0$. `HW.kType_exists`, `fdc_model` and `fdc_ds_exists` supply the compact type, the explicit `PsiM` satisfying `IsPsiFor`, and a Hilbert model with degree. `anyF` gives the isometric compression. The identities `psiM_exp_pmat` and `psM_exp_pmat` identify the compressed operator with $\mathcal F_t(z)$. `Lap.Base.link` works in the right regular $L^2$ model. It divides the nonzero image of the seed highest vector by its norm and uses the smooth embedding derivative and the seed Casimir identity for `IsHWSmooth`. The coefficient formula cancels the squared norm against this normalization. `Lap.Base.b3` assembles the uniform tangent estimate from highest-weight bounds, conjugation, differentiation, a second-order bound, and infinitesimal unitarity. These deeper supplies are used at their named interfaces. [Lean, read] for the assembly. A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/FdConsA.lean:69–141`, `FdCons.lean:17–86` under the same directory, and `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/Imports.lean:12–13`, `ImportsAlt.lean:13–44`.

Choice independence and diagonal Schur give the degree of any supplied gapped `IsDS` base model. Here `IsDS` includes a complete nonzero Hilbert space, an irreducible strongly continuous unitary action, full-group square-integrability of every coefficient, and an irreducible compact type of highest weight $\mathrm{lowK}_\varepsilon(\mu)$, and minimality of $\|\mathrm{lowK}_\varepsilon(\mu)+2\rho_{\mathcal C}\|^2$ against $\|\eta+2\rho_{\mathcal C}\|^2$ for every occurring compact highest weight $\eta$. The all-parameter seed premise of `fdCons_cd` is supplied in `fdeg_gap` by `psiFor` at the fixed bound $h$. The body of `fdCons_cd` obtains its actual family from `fdc_cd`. In the `FlagMeasures` consumer, `fdeg_gap` identifies $\mu_{\rm CD}$ with $\mathrm{sc}(n,\varepsilon)\mu_G$ using the `CDHaar` compact probability and common exponential-coordinate density and the tie for every sign-respecting reindexing of every measurable set. For fixed signs, choose the reindexing that puts all positive indices first. The tied measure and the polar measure agree on each measurable set by their common `CDHaar` value under this reindexing. Measure extensionality gives equality. The scalar is positive because $\mu_{\rm CD}$ is nonzero. The full Schur identity on the scaled measure now has degree $\mathrm{fdegHC}(\lambda)$ by uniqueness of the diagonal degree.

For each $D$ of type `D7` keep all of `Ties D`, the original parameter $\lambda=\mathrm{lamSH}(D.R,D.\mathrm{hc}(\tau))$, signature $\varepsilon=\mathrm{epsSH}(D.R)$ and threshold $\mathrm{thrE}(\varepsilon)+1<h$. `dsExistsG_closed` supplies the base representation, `minpq_pos` gives both sign blocks, and `Ties.dsig_tie` identifies its degree with $D.\mathrm{dsig}(\tau)$. This is `dsig_eq_fdegHC_of_gap`, called by `DsigSize.dsigHC` and directly in `TypeFrameAllMembers.lean:42`. The size-stage normalization `vv_eq_vand_of_sizes` uses the exported wrapper at line 46. There $\mathrm{VV}(D,\tau)=D.\mathrm{dsig}(\tau)F_{D.R.r}$ and $D.R.r=2D.R.rS+D.R.k+1=n$, so the denominator cancels. A separate call in `DegLine.deg_eq_fdegHC` takes an existing `GoodS` datum. It conjugates between its two Cayley realizations and obtains the value of its field `A.deg` on the same scaled measure. The two Cayley actions are related by conjugation by $QP^{-1}\in U(\varepsilon)$, implemented by a unitary on the representation space. The four-vector formula keeps its degree under this transport, and evaluating it on a nonzero vector identifies the two degrees. The subsequent `deg_eq_near` uses the gap after an $\ell^1$ displacement and `deg_VandLine_of_gap` uses the two numerical values in the line comparison. Its wrapper is consumed in `RowAmplitudeBoundsUniformSingletonWidth.lean:104`. On $\mu_G$ the gapped degree is $\mathrm{sc}(n,\varepsilon)\mathrm{fdegHC}(\lambda)$. The universal `LowestKTypeMultiplicity.HCFdeg` asks for every signature and every regular parameter on $\mu_G$. Here the numerical supply covers the large-gap mixed-signature range. [Lean, read] for the handoff. A2, `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HarishChandraFormalDegreeCompactDualLargeGaps.lean:29–106`, `FormalDegreeEqHarishChandraOfGap.lean:11–35`, `ThrEAddOneLt.lean:38–41`, `NormalizedFormalDegreeEqVandermondeOfSizes.lean:41–46` and `FormalDegreeRatioEqVandermondeRatioAlongLine.lean:65–103` under the same directory.

**What the hypotheses control.** Replacing $\mu_{\rm CD}$ by $a\mu_{\rm CD}$ for $a>0$ divides every Schur degree by $a$, since all coefficient integrals are multiplied by $a$. The quotient is now $1/(aF_n)$ and the squeezed limit is $a c_{p,q}\Pi$. With $a=2$ the two base degrees become $25$ and $131072$. Using the old degree in the rescaled Schur identity gives twice the predicted integral.

To test the base gap, keep the recurrence domain at $h=50$ in signature $(+,-)$. Take the regular $\nu=(3/2,1/2)$ of gap $1$. Set $d(\mu)=V(\mu)$ for $\mu\ne\nu$ and set $d(\nu)=2$. The modified value appears in neither endpoint of a legal recurrence. On the ray $\nu_t$ the gap is $1+t$. For all $t\ge49$ the archive supplies the same eventual families and degrees $1+t$, and the two limiting bounds still meet at $1$ in compact-dual normalization. Yet $d(\nu)/V(\nu)=2$ and the tail quotient is $1$. This refutes the inference with the base-gap hypothesis removed and the recurrence domain fixed. For the small-gap disk representation at $\nu$, weight two gives degree one by the same radial integral. At a collision the parameter fails regularity itself, and the putative weight-one disk coefficient has squared integral $\int_1^\infty du/u=\infty$. [Expository]

**Classical attribution and scope.** Harish-Chandra's Theorem 16 gives a fixed-Haar constant times the absolute root product for the regular discrete series. The positive degree is defined by a coefficient integral in §37. Theorem 16 uses the connected reductive setting with compact Cartan from §7 and Part III, and the acceptability assumption retained from §38. [Paper] [Harish-Chandra, *Acta Mathematica* 116 (1966), pp. 87–88, 96–100](https://doi.org/10.1007/BF02392813)

Atiyah and Schmid's Theorem (8.1), p. 41, gives the positive-root product for connected real semisimple groups of finite center with compact Cartan and nonsingular shifted integral parameter. Their (3.15) and Theorem (3.16), p. 14, specify probability on the compact factor and a compact-dual symmetric space of volume one. Theorem (8.5), p. 42, gives the lowest-type weight $\lambda+\rho_{\mathcal N}-\rho_{\mathcal C}$. For the usual parameter convention on $U(p,q)$, restriction of the shifted weight to the compact torus of $SU(p,q)$ preserves shifted integrality because the weight lattice restricts and the roots restrict to the same type-$A$ roots. It preserves regularity and root differences, represented by subtracting the coordinate mean. With the order given by $\lambda$, pairing a root with the ordered $\rho$ gives $j-i$ in the same metric units as its pairing with $\lambda$. Multiplication $U(1)\times SU(p,q)\to U(p,q)$ is a finite covering of degree $n$. An irreducible unitary representation has scalar action on the central circle. The restricted $SU(p,q)$ representation is irreducible since the product map is onto and the circle acts by scalars. Push forward probability on the circle times the semisimple Haar under the covering. The squared coefficient magnitude is constant in the circle coordinate, so its integral equals the integral on $SU(p,q)$. On the compact side the corresponding covering of $U(n)$ also has degree $n$, and the compact-dual symmetric spaces identify with the same Grassmannian. The central circle lies in the compact subgroup. On the compact Grassmannian the quotient of probability Haar is the invariant measure of total mass one. Identify the tangent spaces using the shared off-block matrices $P(z)$, with $iP(z)$ on the compact side. The compact-dual match uses the same local exponential-coordinate density at the identity, with compact factors given probability. This is the normalization in `CDHaar` used above. Thus the classical theorem gives the same numerical root formula for the classical discrete series with the compact-dual normalization, including smaller regular gaps. Identifying the archive's lowest-type predicate with the classical parameter throughout the regular range is a separate representation-theoretic input. Atiyah and Schmid use the $L^2$ index and character translation. The archive uses the recurrence and two integral bounds above and identifies the concrete tied Haar. The textbook contribution is this reconstruction and the handoff to the tied degree. [Paper] [Atiyah–Schmid, pp. 5, 12–14, 41–46](https://www.math.utah.edu/~ptrapa/math-library/schmid/atiyah-schmid.pdf)

The indicated proof bodies have author-level local R3. The deeper family, smooth-domain and tangent-estimate proofs remain at the stated interfaces. Public archival compilation and kernel replay are separate from this source reading. Reachability from the corresponding Main exports, same-source initial review, different-source mathematical review, and peer review of the RH argument are separate open items for this exposition. [Source and verification record](../sources/SOURCES.md#chapter-9-translation-and-the-formal-degree-constant)

---

### 9.4.27 Paying the shared compact-dual Haar normalization from coordinate densities

In §9.4.26 the translation-ray limit fixed the discrete-series formal degree $d(\lambda) = V(\lambda)/F_n$ on the explicit polar measure $d\mu_{\rm CD} = c_{p,q} J(z)\,dz\,dk$, and then passed that value to the global period and flag-measure consumers through `muCD_eq_cd_vol`. Abstract Haar uniqueness on $U(\varepsilon) \cong U(P,Q)$ cannot supply that step on its own: left invariance relates two Haar measures on a noncompact group only up to an unknown positive constant, and scaling the measure by $a > 0$ divides every Schur formal degree by $a$. Worse, the two measures are normalized on different compact groups and in different coordinate charts. The polar measure $\mu_{\rm Polar}$ gives probability one to the maximal compact subgroup $K_\varepsilon \cong U(p) \times U(q)$ and integrates over flat noncompact coordinates $z \in \mathbb C^{pq}$, whereas the global Siegel and CM volume ties package a compact-dual family `CDHaar` that gives probability one to the *ambient* compact unitary group $U(P+Q)$ and transports normalization to $U(P,Q)$ by matching local exponential densities at the identity against the complexified Frobenius volume on $\mathfrak u(P,Q)$.

To prove that the prefactor $c_{p,q} = F_n / (\pi^{pq} F_p F_q)$ pays the exact ratio between these two normalizations, the archive computes three coordinate quantities from scratch and cancels them at the identity: first, the complexification Jacobian $\kappa_n = 2^{n(n-1)/2}$ comparing lower-triangular Lie coordinates with the intrinsic $\Omega$-Lebesgue measure on $\mathfrak u(P,Q)$; second, the Hurwitz–Macdonald volume $\mathrm{volU}(N) = 2^N \pi^{N(N+1)/2} / F_N$ of $U(N)$ via the complex QR Jacobian and matrix Gaussian integral; and third, the identity polar-to-exponential derivative showing that $J(z)\,dz\,dk$ has coordinate density $(\mathrm{volU}(p)\,\mathrm{volU}(q))^{-1}$. Multiplying by $c_{p,q} = \mathrm{volU}(p)\,\mathrm{volU}(q)/\mathrm{volU}(n)$ turns the product-block density into $\mathrm{volU}(n)^{-1}$, and dividing both sides by the same $\kappa_n$ matches the compact-dual $\Omega$-density across every legal sign-splitting chart.

**First worked example: $(P,Q)=(1,1)$ across ordered and swapped charts.** Take $n=2$ and $(P,Q)=(1,1)$, so $\dim_{\mathbb R}\mathfrak u(1,1) = 4$, $F_1 = F_2 = 1$, and $m = pq = 1$. In the ordered signature $\varepsilon = (+,-)$ on $\{0,1\}$, the sole strict-lower pair $(1,0)$ has opposite signs, so $|\mathcal C| = 0$, $|\mathcal N| = 1$, $\dim_{\mathbb R}\mathfrak k = 2$, and $\dim_{\mathbb R}\mathfrak p = 2$. Let us check the volumes, chart factor, and densities term by term.

On $\operatorname{Mat}_N(\mathbb C)$ the Gaussian integral $\int e^{-\operatorname{tr}(Z^\dagger Z)}\,dZ$ equals $\pi^{N^2}$. Under the QR decomposition $Z = k R$ with $k \in U(N)$ of probability Haar mass one and $R$ upper-triangular with positive real diagonal $t_0, \ldots, t_{N-1} > 0$, the Lebesgue Jacobian is $\prod_{j=0}^{N-1} t_j^{2(N-j)-1}$. For $N = 1$, $\int_0^\infty t_0 e^{-t_0^2}\,dt_0 = 1/2$ divides $\pi^1$ to give $\mathrm{volU}(1) = 2\pi$. For $N = 2$, writing $R = \begin{pmatrix} t_0 & u \\ 0 & t_1 \end{pmatrix}$ with $u \in \mathbb C$, the triangular Gaussian integral is
$$
\left(\int_0^\infty t_0^3 e^{-t_0^2}\,dt_0\right)
\left(\int_0^\infty t_1 e^{-t_1^2}\,dt_1\right)
\left(\int_{\mathbb C} e^{-|u|^2}\,du\right)
= \frac{1!}{2} \cdot \frac{0!}{2} \cdot \pi = \frac{\pi}{4}.
$$
Dividing $\pi^4$ by $\pi/4$ gives $\mathrm{volU}(2) = 4\pi^3$.

In Lie coordinates $(w_0, w_1, z) \in \mathbb R^2 \times \mathbb C$, a matrix in $\mathfrak u(+,-)$ has the form $\begin{pmatrix} i w_0 & \bar z \\ z & i w_1 \end{pmatrix}$. Complexifying $(w^{(1)}, z^{(1)}) + i(w^{(2)}, z^{(2)})$ multiplies the two diagonal complex combinations $w_a^{(1)} + i w_a^{(2)}$ by $i$ (real determinant $|i|^2 = 1$ each) and sends the off-diagonal pair $(z^{(1)}, z^{(2)}) \in \mathbb C^2$ to $(Z_{10}, \overline{Z_{01}}) = (z^{(1)} + i z^{(2)},\ z^{(1)} - i z^{(2)})$, followed by complex conjugation in the $(0,1)$ slot. Because $H_0 = \begin{pmatrix} 1 & i \\ 1 & -i \end{pmatrix}$ has $\det_{\mathbb C} H_0 = -2i$, its real determinant on $\mathbb R^4$ is $|-2i|^2 = 4$, and conjugation has unit Jacobian modulus. Thus complexification pushes coordinate Lebesgue measure forward with factor $4^{-1}$, forcing the $\Omega$-Lebesgue measure $\lambda_{1,1}$ to carry the chart-change factor $\kappa_2 = \sqrt{4} = 2^{2\cdot 1/2} = 2$ relative to $dw_0\,dw_1\,dz$. Equivalently, $\|\begin{pmatrix} i w_0 & \bar z \\ z & i w_1 \end{pmatrix}\|_F^2 = w_0^2 + w_1^2 + 2|z|^2$ has Riemannian volume element $\sqrt{1 \cdot 1 \cdot 2 \cdot 2}\,dw_0\,dw_1\,dx\,dy = 2\,dw_0\,dw_1\,dx\,dy$.

On compact $U(2)$, probability Haar has `UCo` coordinate density $1/\mathrm{volU}(2) = 1/(4\pi^3)$ and therefore $\Omega$-density
$$
c_\Omega(2) = \frac{1}{\kappa_2\,\mathrm{volU}(2)} = \frac{1}{2 \cdot 4\pi^3} = \frac{1}{8\pi^3}.
$$
On $U(+,-)$, at $z = 0$ the polar Jacobian is $J(0) = \operatorname{sinhc}(0) = 1$, and probability Haar on $K = U(1) \times U(1)$ has coordinate density $d = 1/\mathrm{volU}(1)^2 = 1/(4\pi^2)$. Multiplying by the polar constant $c_{1,1} = F_2 / (\pi^1 F_1 F_1) = 1/\pi$ and dividing by $\kappa_2 = 2$ gives
$$
\frac{c_{1,1}\,d}{\kappa_2} = \frac{(1/\pi)\cdot (1/(4\pi^2))}{2} = \frac{1}{8\pi^3} = c_\Omega(2).
$$
If instead we work in the swapped signature $\varepsilon' = (-,+)$, the unique sign-splitting bijection $e_{\rm swap} : \operatorname{Fin} 1 \oplus \operatorname{Fin} 1 \simeq \operatorname{Fin} 2$ sends $\mathrm{inl}\,0 \mapsto 1$ and $\mathrm{inr}\,0 \mapsto 0$. Pulling $\begin{pmatrix} i w'_0 & \overline{z'} \\ z' & i w'_1 \end{pmatrix}$ back by $e_{\rm swap}$ swaps the diagonal entries $(w'_0, w'_1) \mapsto (w'_1, w'_0)$ (determinant $-1$) and conjugates the off-diagonal coordinate $x' + i y' \mapsto x' - i y'$ (determinant $-1$), giving real $4 \times 4$ Jacobian determinant $(-1)(-1) = +1$ and preserving the $\ell^1$ ball norm $|w'_0| + |w'_1| + 2|z'|$. Both legal charts yield the same density $1/(8\pi^3)$. [Expository]

**Second worked example: interleaved $(P,Q)=(2,1)$ in signature $(+,-,+)$.** Take $n=3$, $(P,Q)=(2,1)$, and the interleaved sign pattern $\varepsilon = (+,-,+)$ from the second example of §9.4.26, paired with the non-identity sign-splitting bijection $e : \operatorname{Fin} 2 \oplus \operatorname{Fin} 1 \simeq \operatorname{Fin} 3$ defined by
$$
e(\mathrm{inl}\,0) = 0,\qquad e(\mathrm{inl}\,1) = 2,\qquad e(\mathrm{inr}\,0) = 1.
$$
Here $\dim_{\mathbb R}\mathfrak u(2,1) = 9$, $F_1 = F_2 = 1$, $F_3 = 0!\,1!\,2! = 2$, and $m = pq = 2$. Among the $\binom{3}{2} = 3$ strict-lower index pairs $(1,0), (2,0), (2,1)$, the pair $(2,0)$ has equal signs $+$ and forms $\mathrm{KPair}(\varepsilon)$ ($|\mathcal C| = 1$), while $(1,0)$ and $(2,1)$ have opposite signs and form $\mathrm{PCoord}(\varepsilon)$ ($|\mathcal N| = 2$). The compact Lie coordinate space $\mathrm{KCo}(\varepsilon)$ has real dimension $3 + 2(1) = 5 = \dim_{\mathbb R} U(2) + \dim_{\mathbb R} U(1) = 4 + 1$, and the noncompact space $\mathbb C^2$ has real dimension $4$, summing to $9$.

For $N = 3$, the matrix Gaussian has mass $\pi^9$. On $\mathrm{triPos}(3)$, the three positive diagonal entries $(t_0, t_1, t_2)$ carry QR exponents $2(3-j)-1 = 5, 3, 1$, while the three strict-upper complex entries contribute $\pi^3$:
$$
\pi^3 \prod_{j=0}^2 \int_0^\infty t_j^{2(2-j)+1} e^{-t_j^2}\,dt_j
= \pi^3 \cdot \frac{2!}{2} \cdot \frac{1!}{2} \cdot \frac{0!}{2}
= \frac{\pi^3}{4},
\qquad
\mathrm{volU}(3) = \frac{\pi^9}{\pi^3 / 4} = 4\pi^6 = \frac{2^3 \pi^6}{F_3}.
$$
Complexification acts by $i$ on the three diagonal $\mathbb C$-slots ($|i|^6 = 1$) and by $H_0$ on all $\binom{3}{2} = 3$ off-diagonal $\mathbb C^2$-slots, with real determinant $|-2i|^{2\cdot 3} = 4^3 = 64$, so the chart-change factor is $\kappa_3 = 2^{3\cdot 2/2} = 8$.

Write $(w_0, w_1, w_2;\ u_{20}+i v_{20};\ x_{10}+i y_{10},\ x_{21}+i y_{21}) \in \mathbb R^9$ for $\mathrm{GCo}(\varepsilon)$, representing
$$
\mathrm{gMat}(s) = \begin{pmatrix}
i w_0 & x_{10}-i y_{10} & -u_{20}+i v_{20} \\
x_{10}+i y_{10} & i w_1 & x_{21}-i y_{21} \\
u_{20}+i v_{20} & x_{21}+i y_{21} & i w_2
\end{pmatrix} \in \mathfrak u(+,-,+).
$$
Pulling back along $e$ transposes indices $1$ and $2$ to land in block-ordered $\mathfrak u(2,1)$: the diagonal coordinates permute as $(w_0, w_1, w_2) \mapsto (w_0, w_2, w_1)$ ($\det = -1$); the compact pair $(2,0)$ maps order-preservingly to $(\mathrm{inl}\,1, \mathrm{inl}\,0)$ as $(u_{20}, v_{20}) \mapsto (u_{20}, v_{20})$ ($\det = +1$); the mixed pair $(1,0)$ maps to $(\mathrm{inr}\,0, \mathrm{inl}\,0)$ as $(x_{10}, y_{10}) \mapsto (x_{10}, y_{10})$ ($\det = +1$); and the mixed pair $(2,1)$ reverses order because $e(\mathrm{inr}\,0) = 1 < 2 = e(\mathrm{inl}\,1)$, sending $(x_{21}, y_{21}) \mapsto (x_{21}, -y_{21})$ ($\det = -1$). The $9 \times 9$ real Jacobian matrix has determinant $(-1)(+1)(+1)(-1) = +1$ and preserves the $\ell^1$ entry sum.

Now check the constants: compact $U(3)$ probability Haar has $\Omega$-density $c_\Omega(3) = 1/(8 \cdot 4\pi^6) = 1/(32\pi^6)$. On the polar side, $J(0) = 1$ and $K_\varepsilon \cong U(2) \times U(1)$ gives coordinate density $d = (\mathrm{volU}(2)\,\mathrm{volU}(1))^{-1} = ((4\pi^3)(2\pi))^{-1} = 1/(8\pi^4)$. The polar prefactor is
$$
c_{2,1} = \frac{F_3}{\pi^{2\cdot 1} F_2 F_1} = \frac{2}{\pi^2} = \frac{8\pi^4}{4\pi^6} = \frac{\mathrm{volU}(2)\,\mathrm{volU}(1)}{\mathrm{volU}(3)},
$$
so $c_{2,1} d / \kappa_3 = (2/\pi^2)(1/(8\pi^4))/8 = 1/(32\pi^6) = c_\Omega(3)$. In §9.4.26's second example ($\lambda = (128,64,0)$, $\Pi = \pi^2$), this exact prefactor $c_{2,1} = 2/\pi^2$ multiplies $\Pi$ to give the limit $c_{2,1}\Pi = 2$, calibrating $d(128,64,0) = 262144$. [Expository]

**Definitions.** For $P, Q \in \mathbb N$, put $I_{P,Q} = \operatorname{Fin} P \oplus \operatorname{Fin} Q$ and $J_{P,Q} = \operatorname{diag}(I_P, -I_Q)$. The archive group `UpqT P Q` is $\{g \in \mathrm{GL}(I_{P,Q}, \mathbb C) : g^\dagger J_{P,Q} g = J_{P,Q}\}$ with the subspace Borel $\sigma$-algebra, and its real Lie algebra `lieU P Q` is $\{X \in \operatorname{Mat}_{I_{P,Q}}(\mathbb C) : X^\dagger J_{P,Q} + J_{P,Q} X = 0\}$. A Borel measure $\lambda$ on `lieU P Q` satisfies `IsOmegaLeb` if it is an additive Haar measure such that pushing $\lambda \times \lambda$ forward under complexification $(A, B) \mapsto A + i B$ yields standard complex Euclidean Lebesgue measure on $I_{P,Q} \times I_{P,Q} \to \mathbb C$. With the $\ell^1$ matrix-entry ball $\mathrm{ballU}(P,Q,r) = \{X \in \mathrm{lieU}(P,Q) : \sum_{a,b} \|X_{ab}\| < r\}$, a measure $\mu$ on `UpqT P Q` has `OmegaDensity μ c` ($c \in [0,\infty]$) if for some `IsOmegaLeb` measure $\lambda$,
$$
\lim_{r \to 0^+} \frac{\mu\bigl(\{g \in \mathrm{UpqT}(P,Q) : g.\mathrm{mat} \in \exp '' \mathrm{ballU}(P,Q,r)\}\bigr)}{\lambda(\mathrm{ballU}(P,Q,r))} = c.
$$
A datum `cd : CDHaar` assigns to every $(P,Q)$ a left Haar measure `cd.cd P Q` on `UpqT P Q` such that `cd.cd N 0` is a probability measure on compact $U(N)$ (`cd.prob N`) and, for every $(P,Q)$, there exists $c \in (0,\infty)$ satisfying both `OmegaDensity (cd.cd P Q) c` and `OmegaDensity (cd.cd (P+Q) 0) c` (`cd.trick P Q`). [Lean, read] A2, `src/Formalism/LocalRingCardinality/DataCD.lean:10–62`.

For $N \in \mathbb N$, let $\mathrm{UCo}(N) = \mathbb R^N \times \mathbb C^{\{(a,b) : b < a\}}$ parameterize skew-Hermitian matrices via `skMat` (diagonal $i x_a$, strict-lower $w_{ab}$, strict-upper $-\overline{w_{ab}}$), and let $\mathrm{TriCo}(N) = \mathbb R^N \times \mathbb C^{\{(a,b) : a < b\}}$ parameterize upper-triangular matrices via `upMat`, with open cone $\mathrm{triPos}(N) = \{t : \forall j,\ t_{1,j} > 0\}$. For a sign pattern $\varepsilon : \operatorname{Fin} n \to \mathrm{Bool}$ with $p$ positive and $q$ negative entries, set $\mathrm{KPair}(\varepsilon) = \{(a,b) : b < a,\ \varepsilon(a)=\varepsilon(b)\}$, $\mathrm{KCo}(\varepsilon) = \mathbb R^n \times \mathbb C^{\mathrm{KPair}(\varepsilon)}$, and $\mathrm{GCo}(\varepsilon) = \mathrm{KCo}(\varepsilon) \times \mathbb C^{\mathrm{PCoord}(\varepsilon)}$, mapped to $\mathfrak u(\varepsilon)$ by $\mathrm{gMat}(w,z) = \mathrm{kMat}(w) + P(z)$. Put
$$
\mathrm{volU}(N) = \prod_{i=0}^{N-1} \frac{2\pi^{i+1}}{i!} = \frac{2^N \pi^{N(N+1)/2}}{F_N},\qquad
\kappa_n = 2^{n(n-1)/2},\qquad
c_\Omega(N) = \frac{1}{\kappa_N\,\mathrm{volU}(N)}.
$$
A bijection $e : \operatorname{Fin} P \oplus \operatorname{Fin} Q \simeq \operatorname{Fin} n$ is *sign-splitting* for $\varepsilon$ if $\varepsilon(e(\mathrm{inl}\,i)) = \mathrm{true}$ for all $i$ and $\varepsilon(e(\mathrm{inr}\,j)) = \mathrm{false}$ for all $j$. Reindexing $g \mapsto \operatorname{reindex}_{e,e}(g.\mathrm{mat})$ embeds `UpqT P Q` onto `REAL.UJ ε`, and $\mu_{\rm CDtr}(e,\varepsilon)$ denotes the pullback of $\mu_{\rm CD}(\varepsilon) = c_{p,q}\mu_{\rm Polar}(\varepsilon)$ along this embedding. [Lean, read] A2, `TriDens.lean:13–49`, `DensOn.lean:13–35`, `Bridge.lean:15–26`, `OmegaDensityMuCDtr.lean:20–23` under `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/`, and `VolUFactProdMulLe.lean:14–62` in the parent directory.

**Lemma 1 ($\Omega$-Lebesgue uniqueness and the $\kappa_n$ coordinate factor).** For every $(P,Q)$ there is a unique measure $\lambda_{P,Q}$ on `lieU P Q` satisfying `IsOmegaLeb`. Consequently `OmegaDensity μ c` determines $c$ uniquely, and if $\mu(E)\,b = a\,\nu(E)$ for all measurable $E$ with `OmegaDensity μ c`, `OmegaDensity ν d`, $b \neq \infty$, and $d \neq 0$, then $c\,b = a\,d$. Moreover, for any sign-splitting bijection $e : \operatorname{Fin} P \oplus \operatorname{Fin} Q \simeq \operatorname{Fin} n$ of $\varepsilon$ (with $n = P+Q$) and coordinate map $\mathrm{gToLie}(e)(s) = \operatorname{reindex}_{e^{-1},e^{-1}}(\mathrm{gMat}\,s)$,
$$
\lambda_{P,Q} = \kappa_n\,\operatorname{map}\bigl(\mathrm{gToLie}(e)\bigr)\,\mathrm{volume}_{\mathrm{GCo}(\varepsilon)}.
$$
[Lean, read] A2, `OmegaDensityUnique.lean:216–294`, `OmegaPQA.lean:96–255`, `OmegaPQ.lean:69–127`, `OmegaA.lean:142–276` and `IntegralGaussEOmPhiOmE.lean:122–173` under `FormalDegree/HaarVolumes/`.

**Lemma 2 (Complex QR integration, unitary group volume, and compact $\Omega$-density).** Let $\mu_N$ be probability Haar on $U(N)$. For every measurable $f : \operatorname{Mat}_N(\mathbb C) \to [0,\infty]$,
$$
\int_{\operatorname{Mat}_N(\mathbb C)} f(Z)\,dZ
= \mathrm{volU}(N) \int_{U(N)} \int_{\mathrm{triPos}(N)} f\bigl(k\,\mathrm{upMat}(t)\bigr) \prod_{j=0}^{N-1} t_{1,j}^{2(N-j)-1}\,dt\,d\mu_N(k).
$$
Probability Haar $\mu_N$ has exponential coordinate density $\mathrm{volU}(N)^{-1}$ on $\mathrm{UCo}(N)$, and for every `cd : CDHaar` and $P, Q \in \mathbb N$ one has `OmegaDensity (cd.cd P Q) (cOmega (P+Q))`. [Lean, read] A2, `QRHaar.lean:17–102`, `LintegralGaussTri.lean:35–86`, `ChartWR.lean:15–89`, `VolUDensity.lean:16–137` and `Bridge.lean:28–37` under `FormalDegree/HaarVolumes/`.

**Lemma 3 (Polar-to-exponential identity derivative and noncompact $\Omega$-density).** For every sign pattern $\varepsilon : \operatorname{Fin} n \to \mathrm{Bool}$ with $p$ positive and $q$ negative entries, $\mu_{\rm Polar}(\varepsilon)$ has equal coordinate densities along shrinking exponential balls $\exp(\mathrm{gMat}\,S)$ and polar sets $\{\exp(\mathrm{kMat}\,w)\exp P(z) : (w,z) \in S\}$ on $\mathrm{GCo}(\varepsilon)$, given by $d = (\mathrm{volU}(p)\,\mathrm{volU}(q))^{-1}$. Since $c_{p,q} = \mathrm{volU}(p)\,\mathrm{volU}(q) / \mathrm{volU}(n)$, every sign-splitting bijection $e : \operatorname{Fin} P \oplus \operatorname{Fin} Q \simeq \operatorname{Fin} n$ for $\varepsilon$ satisfies `OmegaDensity (muCDtr e ε) (cOmega n)`. [Lean, read] A2, `HaarExp.lean:19–91`, `HaarPol.lean:14–94`, `KdMeasImageProd.lean:54–140` and `OmegaDensityMuCDtr.lean:66–239` under `FormalDegree/HaarVolumes/`.

**Theorem (compact-dual coordinate-density agreement).** Let `cd : CDHaar`, $n, P, Q \in \mathbb N$, $\varepsilon : \operatorname{Fin} n \to \mathrm{Bool}$, and $e : \operatorname{Fin} P \oplus \operatorname{Fin} Q \simeq \operatorname{Fin} n$ satisfy $\varepsilon(e(\mathrm{inl}\,i)) = \mathrm{true}$ for all $i$ and $\varepsilon(e(\mathrm{inr}\,j)) = \mathrm{false}$ for all $j$. Then for every measurable set $A \subseteq \mathrm{REAL.UJ}(\varepsilon)$,
$$
\mu_{\rm CD}(\varepsilon)(A)
= \mathrm{cd}.\mathrm{cd}(P,Q)\bigl(\{g \in \mathrm{UpqT}(P,Q) : \operatorname{reindex}_{e,e}(g.\mathrm{mat}) \in \mathrm{Subtype.val} '' A\}\bigr).
$$
[Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/OmegaDensityUnique.lean:298–337`.

**Proof of Lemma 1.** Because `lieU P Q` is a closed real linear subspace of $\operatorname{Mat}_{I_{P,Q}}(\mathbb C)$, any two additive Haar measures $\lambda, \lambda'$ satisfying `IsOmegaLeb` obey $\lambda = c\,\lambda'$ for some $c \in [0,\infty)$ (finiteness follows by evaluating on a bounded ball). Pushing $\lambda \times \lambda = c^2(\lambda' \times \lambda')$ forward under $(A,B) \mapsto A + i B$ gives $\mathrm{volume} = c^2\,\mathrm{volume}$ on $I_{P,Q}^2 \to \mathbb C$. Evaluating on the Euclidean unit ball, whose Lebesgue measure lies strictly between $0$ and $\infty$, yields $c^2 = 1$ and hence $c = 1$. Dividing $\mu(E_r)\,b = a\,\nu(E_r)$ on $E_r = \{g : g.\mathrm{mat} \in \exp '' \mathrm{ballU}(P,Q,r)\}$ by $\lambda_{P,Q}(\mathrm{ballU}(P,Q,r))$ and letting $r \to 0^+$ gives $c\,b = a\,d$.

For the coordinate pushforward, write $\mathrm{Qp}(n) = \{(a,b) \in (\operatorname{Fin} n)^2 : b < a\}$, which has cardinality $\binom{n}{2} = n(n-1)/2$ and is the disjoint union $\mathrm{KPair}(\varepsilon) \sqcup \mathrm{PCoord}(\varepsilon)$. Consider $\mathrm{pairMap}(\varepsilon) : \mathrm{GCo}(\varepsilon) \times \mathrm{GCo}(\varepsilon) \to (\operatorname{Fin} n \times \operatorname{Fin} n \to \mathbb C)$, $(s,t) \mapsto \mathrm{gMat}(s) + i\,\mathrm{gMat}(t)$. It factors as $\mathrm{Amap}(\varepsilon) \circ \mathrm{Gl}(\varepsilon) \circ \mathrm{Fmap}(\varepsilon)$: first $\mathrm{Fmap}(\varepsilon)$ pairs the two real diagonal vectors into $\mathbb C^n$ and merges $\mathrm{KPair}(\varepsilon)$ and $\mathrm{PCoord}(\varepsilon)$ into $\mathrm{Qp}(n) \to \mathbb C^2$, preserving Lebesgue measure; next the $\mathbb C$-linear isomorphism $\mathrm{Gl}(\varepsilon)$ multiplies each of the $n$ diagonal $\mathbb C$-coordinates by $i$ and applies $H_0 = \begin{pmatrix} 1 & i \\ 1 & -i \end{pmatrix}$ to each of the $\binom{n}{2}$ off-diagonal $\mathbb C^2$-blocks; finally $\mathrm{Amap}(\varepsilon)$ applies complex conjugation and sign $\mp 1$ (`sgc`, preserving plane Lebesgue measure) to the upper-triangular partner $\mp\overline{z^{(1)}} \pm i\overline{z^{(2)}} = \mp\overline{(z^{(1)} - i z^{(2)})}$ and places all $n + 2\binom{n}{2} = n^2$ entries into the matrix. Since restricting scalars from $\mathbb C$ to $\mathbb R$ squares complex determinant moduli,
$$
\det_{\mathbb R}\bigl(\mathrm{Gl}(\varepsilon)\bigr)
= \bigl|i^n (\det_{\mathbb C} H_0)^{\binom{n}{2}}\bigr|^2
= \bigl|i^n (-2i)^{\binom{n}{2}}\bigr|^2 = 4^{n(n-1)/2}.
$$
Pushing Lebesgue measure forward by a real linear isomorphism scales `volume` by $|\det_{\mathbb R}|^{-1}$, so $\operatorname{map}(\mathrm{pairMap}\,\varepsilon)\,\mathrm{volume} = 4^{-n(n-1)/2}\,\mathrm{volume}$. Reindexing matrix entries by $e^{-1}$ preserves `volume`, and multiplying each factor of $\operatorname{map}(\mathrm{gToLie}\,e)\,\mathrm{volume}$ by $\kappa_n = 2^{n(n-1)/2}$ multiplies their product pushforward by $\kappa_n^2 = 4^{n(n-1)/2}$, proving `IsOmegaLeb`. (On the compact side $Q = 0$, `OmegaA` and `IntegralGaussEOmPhiOmE` also check this factor by comparing $\int e^{-\|Z\|_F^2}\,dZ = \pi^{N^2}$ with $(\int_{\mathrm{UCo}(N)} e^{-\|\mathrm{skMat}\,x\|_F^2}\,dx)^2 = (\pi^{N/2}(\pi/2)^{\binom{N}{2}})^2 = \pi^{N^2} 4^{-\binom{N}{2}}$.) [Lean, read] A2, `OmegaDensityUnique.lean:216–294`, `OmegaPQA.lean:105–255` and `OmegaPQ.lean:69–127` under `FormalDegree/HaarVolumes/`.

**Proof of Lemma 2.** If $\det Z = 0$, one row of $Z$ lies in the $\mathbb C$-span of the remaining $N-1$ rows; slicing by Tonelli's theorem along those $N-1$ rows leaves a proper $\mathbb C$-subspace of $\mathbb C^N$ of Lebesgue measure zero, so $\{\det Z = 0\}$ is null (`DetNull.lean:32–107`). On $\mathrm{GL}_N(\mathbb C)$, Gram–Schmidt orthonormalization of columns expresses $Z = k\,\mathrm{upMat}(t)$ with $(k,t) \in U(N) \times \mathrm{triPos}(N)$, uniquely because an upper-triangular unitary matrix with positive real diagonal equals $I_N$ (`QrMapMeasurableSetImage.lean:81–265`).

Left or right multiplication by $g \in \mathrm{GL}_N(\mathbb C)$ on $\operatorname{Mat}_N(\mathbb C)$ has complex determinant $(\det g)^N$ and real determinant $|\det g|^{2N}$, making $\mathrm{gmMeas}(N) = |\det Z|^{-2N}\,dZ$ bi-invariant (`LeftMulMapEqTransposeConj.lean:43–154`). On `TriCo N`, right multiplication by $R_0 = \mathrm{upMat}(t_0) = U_0 \operatorname{diag}(d_0,\ldots,d_{N-1})$ factors into unipotent right multiplication `rmulL U_0`, whose difference from the identity is nilpotent so $\det_{\mathbb R}(\mathrm{rmulL}\,U_0) = 1$, followed by `scaleL d`, which scales column $j$'s real diagonal by $d_j$ and its $j$ strict-upper complex entries by $d_j$ (real factor $d_j^2$ each), giving $\det_{\mathbb R}(\mathrm{scaleL}\,d) = \prod_{j=0}^{N-1} d_j^{2j+1}$ (`TriHaarA.lean:95–183`). Thus $\mathrm{triMeas}(N) = (\prod_{j=0}^{N-1} t_{1,j}^{-(2j+1)})\,dt$ is right-invariant on `triPos N` (`TriHaar.lean:52–109`). Pulling $\mathrm{gmMeas}(N)$ back under `qrMap` and applying Haar uniqueness first on compact $U(N)$ and then on the opposite triangular group `TG N` identifies the pullback as $\mu_N \times (C\,\mathrm{triMeas}(N))$ for a constant $C \ge 0$ (`TriUniq.lean:113–256`, `QRHaarA.lean:181–312`). Restoring $|\det(k\,\mathrm{upMat}\,t)|^{2N} = \prod_{j=0}^{N-1} t_{1,j}^{2N}$ yields the QR weight $\prod_{j=0}^{N-1} t_{1,j}^{2(N-j)-1}$.

Evaluating this QR integral at $f(Z) = e^{-\operatorname{tr}(Z^\dagger Z)}$ gives $\pi^{N^2}$ on the left and, by unitary invariance $\operatorname{tr}((kR)^\dagger(kR)) = \sum_j t_{1,j}^2 + \sum_{a<b} |t_{2,ab}|^2$,
$$
C \cdot 1 \cdot \pi^{N(N-1)/2} \prod_{j=0}^{N-1} \int_0^\infty r^{2(N-1-j)+1} e^{-r^2}\,dr
= C\,\pi^{N(N-1)/2} \prod_{m=0}^{N-1} \frac{m!}{2}
= C\,\frac{\pi^{N(N-1)/2} F_N}{2^N}
$$
on the right, forcing $C = 2^N \pi^{N(N+1)/2} / F_N = \mathrm{volU}(N)$ (`GaussA.lean:60–116`, `GaussB.lean:33–115`, `LintegralGaussTri.lean:35–86`). Near $(0,0) \in \mathrm{UCo}(N) \times \mathrm{TriCo}(N)$, the map $\mathrm{chartWR}(x,t) = \exp(\mathrm{skMat}\,x)(I_N + \mathrm{upMat}\,t)$ has strict derivative $\mathrm{lamE}(x,t) = \mathrm{skMat}\,x + \mathrm{upMat}\,t$ (`ChartWRB.lean:39–72`). Because $(\mathrm{skMat}\,x + \mathrm{upMat}\,t)_{ab} = t_{2,ab} - \overline{x_{2,ba}}$ for $a < b$, `lamE` is the composition of a unipotent shear in the upper entries with a coordinate permutation, hence preserves Lebesgue measure ($|\det_{\mathbb R}(\mathrm{lamE})| = 1$, `ChartWRA.lean:109–184`, `ChartWR.lean:15–89`). Comparing `chartWR(B_r × ball(0,ρ))` with `qrMap(exp(skMat B_r) × ball(I,ρ))` where the QR weight tends to $1$, and canceling $0 < \mathrm{volume}(\mathrm{ball}(0,\rho)) < \infty$, yields $\mu_N(\exp(\mathrm{skMat}\,B_r))/\mathrm{volume}(B_r) \to \mathrm{volU}(N)^{-1}$ (`VolUDensity.lean:16–137`). Dividing by $\kappa_N$ from Lemma 1 gives `OmegaDensity (cd.cd N 0) (cOmega N)`, and `cd.trick P Q` with uniqueness in Lemma 1 transfers $c_\Omega(P+Q)$ to `cd.cd P Q` (`BridgeA.lean:64–336`, `Bridge.lean:28–37`).

**Proof of Lemma 3.** Using the local matrix logarithm inverse to $\exp$ near $I_n$, the translated map $y \mapsto \log(\exp(-x)\exp(x+y))$ has strict derivative $\mathrm{id}$ uniformly for small $x$, so the pullback of left-invariant $\mu_{\rm Polar}(\varepsilon)$ to $\mathrm{GCo}(\varepsilon)$ satisfies $(1-\delta)$-quasi-translation invariance near $0$ (`HaarExpB.lean:68–321`). Besicovitch differentiation on the finite-dimensional real vector space $\mathrm{GCo}(\varepsilon)$ then produces a positive finite exponential density $d > 0$ (`HaarExpA.lean:84–244`, `HaarExp.lean:19–91`). Next, the polar-to-exponential transition $\mathrm{Lm}(w,z) = \mathrm{cLin}(\varepsilon)(\log(\exp(\mathrm{kMat}\,w)\exp P(z)))$ satisfies $\mathrm{Lm}(0,0) = 0$ and has strict Fréchet derivative $\mathrm{id}_{\mathrm{GCo}(\varepsilon)}$ at $(0,0)$ by the chain rule on $d(\exp)_0 = \mathrm{id}$, $d(\log)_I = \mathrm{id}$, and matrix multiplication at $(I_n, I_n)$ (`HaarPolB.lean:85–147`). Shrinking polar balls are therefore sandwiched between $(1\mp\delta)$-rescaled exponential balls, giving $\mu_{\rm Polar}(\varepsilon)$ the same density $d$ on polar sets (`HaarPol.lean:14–94`).

On small product balls $B_r \times C_r \subseteq \mathrm{KCo}(\varepsilon) \times \mathbb C^{\mathrm{PCoord}(\varepsilon)}$, polar uniqueness factors the measure into $(\int_{C_r} J(z)\,dz)\cdot \mathrm{dk}(\varepsilon)(\exp(\mathrm{kMat}\,B_r))$ (`ContinuousMatrixExpCompact.lean:137–186`). At $z = 0$, $P(0) = 0$ has all eigenvalues zero, so $J(0) = \prod_{b<a}\operatorname{sinhc}(0) = 1$ and $(\int_{C_r} J(z)\,dz)/\mathrm{volume}(C_r) \to 1$ (`JacobianNearOneOfSmall.lean:15–48`). On the compact subgroup, block embedding $U(p) \times U(q) \simeq K_\varepsilon$ pushes $\mu_p \times \mu_q$ to probability Haar $\mathrm{dk}(\varepsilon)$ (`KDensA.lean:203–278`), while splitting $\mathrm{KCo}(\varepsilon)$ by sign into $\mathrm{UCo}(p) \times \mathrm{UCo}(q)$ permutes real and complex coordinates and preserves `volume` (`KDensB.lean:166–191`). Applying Lemma 2 to $U(p)$ and $U(q)$ gives $\mathrm{dk}(\varepsilon)(\exp(\mathrm{kMat}\,B_r))/\mathrm{volume}(B_r) \to (\mathrm{volU}(p)\,\mathrm{volU}(q))^{-1}$, hence $d = (\mathrm{volU}(p)\,\mathrm{volU}(q))^{-1}$ (`KdMeasImageProd.lean:54–140`, `OmegaDensityMuCDtr.lean:66–139`). Since $p+q=n$, $2^p 2^q = 2^n$, and $\frac{1}{2}(p(p+1)+q(q+1)-n(n+1)) = -pq$, we have
$$
\frac{\mathrm{volU}(p)\,\mathrm{volU}(q)}{\mathrm{volU}(n)} = \frac{F_n}{\pi^{pq} F_p F_q} = c_{p,q}
$$
(`VolUFactProdMulLe.lean:59–61`). Scaling $\mu_{\rm Polar}(\varepsilon)$ by $c_{p,q}$ yields coordinate density $c_{p,q} d = \mathrm{volU}(n)^{-1}$. Because reindexing by $e$ preserves the $\ell^1$ sum defining `ballU P Q r`, dividing by $\kappa_n$ from Lemma 1 proves `OmegaDensity (muCDtr e ε) (cOmega n)` (`OmegaDensityMuCDtr.lean:141–239`).

**Proof of the theorem.** Sign-splitting of $e$ forces $P = p$, $Q = q$, $P + Q = n$, and $\operatorname{reindex}_{e,e}(J_{P,Q}) = J_\varepsilon$, so matrix reindexing defines a topological group isomorphism `psiC e he1 he2 : UpqT P Q ≃ₜ* UJ ε` (`OmegaDensityUnique.lean:20–115`). Pushing `cd.cd P Q` forward gives a left Haar measure on `UJ ε`, which by Haar uniqueness against $\mu_{\rm Polar}(\varepsilon)$ is $s\,\mu_{\rm Polar}(\varepsilon)$ for some $s \in [0,\infty)$. Multiplying by $c_{p,q} \in (0,\infty)$ and pulling back along `upqMat e` yields $a = \mathrm{ENNR.ofReal}(s) \neq \infty$ such that $\mathrm{cd}.\mathrm{cd}(P,Q)(E)\,c_{p,q} = a\,\mu_{\rm CDtr}(e,\varepsilon)(E)$ for all measurable $E \subseteq \mathrm{UpqT}(P,Q)$ (`key`, `:187–215`). Lemmas 2 and 3 give both `cd.cd P Q` and $\mu_{\rm CDtr}(e,\varepsilon)$ the same $\Omega$-density $c_\Omega(n) \in (0,\infty)$. Applying Lemma 1 gives $c_\Omega(n)\,c_{p,q} = a\,c_\Omega(n)$, whence $a = c_{p,q}$ and $\mathrm{cd}.\mathrm{cd}(P,Q)(E) = \mu_{\rm CDtr}(e,\varepsilon)(E)$ since $0 < c_{p,q} < \infty$. Evaluating at $E = \{g : \operatorname{reindex}_{e,e}(g.\mathrm{mat}) \in \mathrm{Subtype.val} '' A\}$ completes the proof. [Lean, read] A2, `OmegaDensityUnique.lean:187–215,298–337`.

**Remarks: nonempty witnesses, consumer constant direction, counter-controls, and classical attribution.**

1. *Unconditional witnesses.* The `CDHaar` axioms are inhabited unconditionally by `Examples₂.CD.cdHaar` (`src/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean:207–225`): starting from base Haar measures $\mu_0(P,Q)$ with finite positive $\Omega$-densities $c_0(P,Q) \in (0,\infty)$ and compact total mass $m_N = \mu_0(N,0)(U(N)) \in (0,\infty)$, setting $\mathrm{cd}(P,Q) = \frac{c_0(P+Q,0)}{m_{P+Q}\,c_0(P,Q)}\,\mu_0(P,Q)$ normalizes $(N,0)$ to mass one and gives $(P,Q)$ and $(P+Q,0)$ the common density $c_0(P+Q,0)/m_{P+Q}$. Likewise `SignSplitEquivInl.lean:193–249` constructs for every $(n,\varepsilon)$ a canonical sign-splitting equivalence `e0 ε` and a strictly positive real scalar `cdScaleOf cd n ε > 0` satisfying `cdScaleTie` across all sign-splitting bijections. [Lean, read]
2. *Real consumers and direction of the scale constant.* Four archive wrappers call `muCD_eq_cd_vol` directly, each instantiating $e$ with a concrete sign-splitting bijection (`plusFirst ε`, `signEquiv ε`, or `e0 ε`) and combining the theorem with `cdScaleTie` via measure extensionality to obtain
   $$
   \mu_{\rm CD}(\varepsilon) = s(n,\varepsilon)\,\mu_G(n,\varepsilon),\qquad s(n,\varepsilon) > 0.
   $$
   Specifically: (i) `src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HarishChandraFormalDegreeCompactDualLargeGaps.lean:29–40,53–106` (`muCD_eq_scaled` $\to$ `fdeg_gap`, with `muCD_eq_scaled` also called in `src/Development/WeilBound/RepresentationTheoryGL/FormalDegree/FormalDegreeHilbert/NormIndOfSteps.lean:49`) feeds `FormalDegreeEqHarishChandraOfGap.lean:11–35` (`dsig_eq_fdegHC_of_gap`), supplying `D.dsig` and `A.deg` in §9.4.26; (ii) `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeGap/HCFdegRGapHolds.lean:16–35,83–112` (`muCD_eq_smul` $\to$ `hCFdegRGap_holds : HCFdegRGap`) supplies the universal large-gap degree package consumed in `src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/HCFdegRGap.lean:10–19`, `DimensionBoundOfGapUniform.lean:37–98` and `DimensionFamilyOfWeylMultiplicity.lean:41–108` in `FormalDegreeGap/`, and `src/Formalism/SharpRestriction/GlobalSchurBounds/TheoremThreeFamilyOfGappedMultiplicity.lean:67–206`, where the local Haar scale $s(n,\varepsilon)\mu_G$ cancels against the global CM/Siegel fundamental-domain volume built from $\prod_\rho \mathrm{cd}.\mathrm{cd}(P_\rho, Q_\rho)$ (`src/Development/AbelianVarietyTheory/Definitions/Foundations/CdScaleTieIff.lean:24–68`); and (iii)–(iv) `src/Formalism/LocalToGlobal/SiegelLatticeTheory/BesselDiscreteSeries/FdegUniqG.lean:38–63` (`muCD_eq_cdScale`) and `src/Formalism/LocalToGlobal/SiegelLatticeTheory/WeightedGaugeFactors/FactsFD.lean:15–22` (`cdScale_eq_muCD`) supply the Siegel–Bessel uniqueness and weighted gauge-factor bridges. Notice the direction of $s = s(n,\varepsilon)$: because $\int |\langle w,\sigma(g)v\rangle|^2\,d(s\mu_G) = s\int |\langle w,\sigma(g)v\rangle|^2\,d\mu_G$, multiplying $\mu_G$ by $s$ *divides* the Schur formal degree by $s$. On the scaled measure $s(n,\varepsilon)\mu_G = \mu_{\rm CD}$ the calibrated degree is $V(\lambda)/F_n$ with no extra factor; on unscaled $\mu_G$ it is $s(n,\varepsilon)\,V(\lambda)/F_n$. [Lean, read]
3. *What the nonsingularity, normalization, and sign-splitting premises control.*
   - *Dropping `cd.prob N`:* Scaling `cdHaar` by $\alpha > 0$ ($\alpha \neq 1$) preserves `haar` and `trick` (with shared density $\alpha\,c_\Omega(P+Q)$), but changes the compact mass to $\alpha$. Then $\mathrm{cd}_\alpha(P,Q) = \alpha\,\mu_{\rm CDtr}$, shifting $s(n,\varepsilon)\mu_G$ to $\alpha\,\mu_{\rm CD}$ and dividing every calibrated formal degree by $\alpha$ (for $\alpha = \mathrm{volU}(2) = 4\pi^3$ in the first example, $\lambda=(101/2,1/2)$ gets degree $50/(4\pi^3)$ instead of $50$).
   - *Dropping positivity or nondegeneracy:* Omitting $t_{1,j} > 0$ in `triPos N` while keeping invertibility lets diagonal signs $S \in \{\pm 1\}^N \le U(N)$ act via $(kS, SR)$, making `qrMap` $2^N$-to-$1$ and miscalibrating $C$ to $\mathrm{volU}(N)/2^N$ (or creating an infinite-measure $U(1)^N$ torus fiber for complex diagonals); omitting $\det Z \neq 0$ collapses $U(N) \times \{0\}$ onto $Z=0$ where $|\det Z|^{-2N}$ blows up; and omitting $d \neq 0$ or $b \neq \infty$ in Lemma 1 allows $0 = a \cdot 0$ or $\infty = \infty$ to hold for arbitrary $a > 0$.
   - *Dropping sign-splitting on $e$:* Even when $P + Q = n$, taking $P=2, Q=0$ against $\varepsilon = (+,-)$ maps $J_{2,0} = I_2$ to $I_2 \neq J_\varepsilon$, sending $\begin{pmatrix}0&1\\1&0\end{pmatrix} \in U(2)$ outside $U(1,1)$ while $\mu_{\rm CD}(+,-)(U(1,1)) = \infty \neq 1 = \mathrm{cd}(2,0)(U(2))$. Even at matching $(P,Q)=(2,1)$ and $\varepsilon=(+,-,+)$, the non-splitting map $\mathrm{inl}\,0\mapsto 0, \mathrm{inl}\,1\mapsto 1, \mathrm{inr}\,0\mapsto 2$ sends $J_{2,1}$ to $\operatorname{diag}(1,1,-1) \neq \operatorname{diag}(1,-1,1)$, so compact $0,1$ rotations leave $U(+,-,+)$. [Expository]
4. *Classical attribution and scope.* The invariant volume $\mathrm{volU}(N) = 2^N\pi^{N(N+1)/2}/F_N$ goes back to Hurwitz (1897) and is placed in the general Chevalley-exponent product by Macdonald (1980). Its evaluation by integrating the matrix Gaussian against the complex triangular Jacobian $\prod_{j=0}^{N-1} t_{jj}^{2(N-j)-1}$ appears explicitly in Edelman (1989, §3.2–3.3, Theorem 3.1). Matching noncompact and compact-dual Haar measures at the identity through $\mathfrak p \mapsto i\mathfrak p$ with probability on $K$ and unit-mass compact-dual symmetric space $M/K$ is the Hirzebruch proportionality normalization (Hirzebruch 1958; Atiyah–Schmid 1977, §3, (3.6)–(3.16)), combined with standard Cartan/Iwasawa Haar decompositions (Knapp 2002, Ch. V & VIII). No new measure-theoretic theorem is claimed; the archive contributes a self-contained Lean formalization tailored to the $\ell^1$-ball `OmegaDensity` interface and arbitrary sign-splitting reindexings via Besicovitch differentiation. [Paper] [Hurwitz, *Nachr. Ges. Wiss. Göttingen* (1897), 71–90](https://eudml.org/doc/58382) · [Hirzebruch (1958), pp. 129–144](https://www.math.uni-bonn.de/people/hirzebruch/publications/) · [Atiyah–Schmid, *Invent. Math.* 42 (1977), pp. 12–14](https://www.math.utah.edu/~ptrapa/math-library/schmid/atiyah-schmid.pdf) · [Macdonald, *Invent. Math.* 56 (1980), 93–95](https://doi.org/10.1007/BF01392542) · [Edelman (1989), pp. 31–35](https://dspace.mit.edu/handle/1721.1/14322) · [Knapp (2002), pp. 535–540](https://doi.org/10.1007/978-1-4757-2453-0)

Author-level local R3 covers `OmegaDensityUnique`, the entire `FormalDegree/HaarVolumes/` directory, `VolUFactProdMulLe`, `DataCD`, `HaarDensityNeZero`, `SignSplitEquivInl`, and the four direct consumer bridges listed above. Polar Haar invariance (§9.4.25) and the translation-ray calibration (§9.4.26) are consumed at their previously recorded scope, while universal `LowestKTypeMultiplicity.HCFdeg`, `AllHyp.s47`, full `GoodS` construction, and `Main` call-graph reachability remain unchanged. Community Lean kernel replay, same-source initial review, different-source mathematical audit, and peer review of the RH argument are accounted separately. [Source and verification record](../sources/SOURCES.md#chapter-9-compact-dual-coordinate-density-and-haar-normalization)

---

## 9.5 Remarks, formalization notes, and Masullo's counterpart

### 9.5.1 A reusable Mathlib-grade gem inside the archive: `LatticeSlopes/` and `HarderNarasimhan/`

One striking discovery from computing import cones on **P9** is how cleanly modular the Arakelov
lattice library is [Lean, read]:

- `HarderNarasimhan/Statement.lean` has import cone **1** (`LatticeSlopes/Statement.lean`, which
  imports **only Mathlib**!);
- the entire proof of Harder–Narasimhan existence/uniqueness, duality, Bost's slope inequality
  `SlopeIneq`, the worked rank-$2$ example `polygon_worked_example`, and the number-field extension
  `src/Formalism/HarderNarasimhan/ShiftInvariance.lean` sits inside **68 modules**, zero of which touch automorphic forms, theta
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
| `slopeIneq`, `slopeIneqMean`; `imageStep`, `hnCor` | `src/Formalism/HarderNarasimhan/ShiftInvariance.lean:43,54`; `src/Formalism/HarderNarasimhan/FinalCor.lean:9,33` | Theorem 9.2: metric-shift invariance, mean-normalized number-field `SlopeIneqMean` (import cone 68), and image-slope corollary. | [Lean, read] |
| `ht`, `opNormAt`, `htMap`, `muDef`, `muMaxDef`, `muMinDef`, `Twist`, `SlopeIneqMean` | `src/Formalism/HarderNarasimhan/StatementPl.lean:29,55,60,64,67,70,133,148` | Definition 9.1(3): mean archimedean operator height `htMap` over `InfinitePlace K`, archimedean metric rescaling `Twist`, and `SlopeIneqMean`. | [Lean, read] |
| `FrameHerm`, `FrameHermSharp` | `src/Formalism/HarderNarasimhan/StatementFrame.lean:11,49` | Definition 9.3(1) and Proposition 9.4(1): almost-orthogonal block-frame bound on `muDef b' X' cc` with continuous slope gap `u > 0` and HN span `HH`. | [Lean, read] |
| `RecNums.divIneq`, `complex_height_cast`, `KerChain`, `ChainTie`, `ChainTie.chain_le`, `ChainTie.chain`, `DivClauses`, `shiftLat`, `CBData`, `exists_cu`, `height_chain`, `divClauses_of`, `division_height_bound_statement`, `toyCoreOne_divClauses`, `clauses_shift`, `height_three`, `not_tied_two` | `src/Formalism/LocalToGlobal/Divisibility/DivisionHeightBoundStatement.lean:131,209,248,321,344,358,553,555,565,585,641,752,991,1425,1589,1647,1816` | Definition 9.2, Section 9.2.2, and Theorem 9.3: tied $m$-step chains, fractional-ideal shift `shiftLat`, `height_chain`, `divClauses_of`, and sanity checks `height_three`, `not_tied_two` (import cone 763). | [Lean, read] |
| `recAux`, `constant_factor_le_sixty`, `divIneqRecord_of`, `divisor_inequality_explicit`, `good_twisted_lattice` | `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean:44,58,63,91,186` | Theorem 9.3(2): explicit constant simplification $(50 C_0 + 10)(c_e/C_0) \le 60 c_e$ and twisted-lattice divisor inequality (import cone 133). | [Lean, read] |
| `LinkV_at`, `LinkN_at`, `LinkN`, `DIVinN_at`, `DIVinN`, `BesselId`, `LinkDIV_at`, `LinkDIV`, `LinkDIVt`, `LinkG_at`, `LinkG`, `LinkS_at`, `LinkS`, `GlobalTheoremInputs`, `LinkGLOBAL` | `src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:18,40,45,59,62,65,77,91,94,122,138,145,152,158,162` | Definition 9.3(2) and Proposition 9.4(2): inert-prime gain bound `LinkG`, period/dual-slope bound `LinkDIV` (`L.MAIN u`, `BesselId`), stretched-exponential near-orthogonality `LinkS`, and five-part `GlobalTheoremInputs` (import cone 306). | [Lean, read] |
| `ChainTied`, `ChainTied.core_of` | `src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97,116` | Proposition 9.4(2): defines `ChainTied` and combines `ChainTied` + `HostFacts` into `ChainCore` (`ChainTied.core_of`). | [Lean, read] |
| `GlobalTheory.Top.closed_linkG_of_duty`; `GlobalTheory.Top.link_alt_alt_bis`; `GlobalTheory.Top.link_gl`; `GlobalTheory.Top.link_alt_alt_alt` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkG.lean:13`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/LinkAltAltBis.lean:16`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LinkGl.lean:14`; `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/Link.lean:20` | Top wrapper proofs closing `LinkG` (`closed_linkG_of_duty`, cone 12,612), `LinkS` (`link_alt_alt_bis`, cone 15,578), `LinkGLOBAL` (`link_gl`), and `SmallLevelRankEq` (`link_alt_alt_alt`) (`R3` for wrappers; deep cones `R2` / `[Open]`). | [Lean, read] |
| `IsURepOn`, `IsFdeg`, `IsDS` | `src/Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean:23,37,72` | Statement-level (`R2`) unitary representation, formal-degree, and discrete-series predicates underlying Gram-matrix off-diagonal bounds. | [Lean] |

**Summary of the chapter.** Generalizing Liouville's rank-$1$ product-formula inequality to higher
rank requires Bost's Arakelov slope inequality $\mu_{\min}(L_1) - \log K \le \mu_{\min}(T(L_1)) \le \mu_{\max}(L_2)$
`[Bost1996]`, which the archive proves cleanly from Haar volume and nearest-integer orthogonal-projection
rounding in just 68 Mathlib-based modules (`SlopeIneq`, Theorem 9.2) [Lean, read]. Iterating across a
tied $m$-step chain (`height_chain`, `divClauses_of`, `divisor_inequality_explicit`, Theorem 9.3) and
controlling nearly orthogonal period blocks via `FrameHerm`/`FrameHermSharp` and stretched-exponential
Gram decay `LinkS` ($\le \exp(-x^{\varepsilon/8})$, Proposition 9.4) alongside `LinkG` and `LinkDIV`
turns Chapter 8's inert-prime divisibility into the global `ASK - MAIN` chain inequality — *except*
for one crucial algebraic loss at every lift: the **Hecke congruence denominator**, to which we turn
in Chapter 10!
