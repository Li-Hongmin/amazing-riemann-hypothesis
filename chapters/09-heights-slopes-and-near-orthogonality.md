# Chapter 9. Heights, slopes, and near-orthogonality

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs read
> in full across `LatticeSlopes/`, `HarderNarasimhan/`, `DivisionHeightBoundStatement.lean`,
> `src/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/GlobalBoundRefinements.lean`, `GlobalTheoremInputs.lean`, `TieGlobal.lean`, `ThirdPlaceSeries/LinkG.lean`,
> `ThirdPlaceSeries/LinkAltAltBis.lean`, `GlobalInterpolation/LinkGl.lean`, and `ThirdPlaceSeries/Link.lean`
> (`R3`), for the specified local polar and ratio bodies in §§9.4.6–7, and for the local translation and two-limit bodies cited in §9.4.26,
> the compact-dual coordinate-density chain cited in §9.4.27, the tensor comparison bodies cited in §9.4.28, and the polar weighted-integrability bodies cited in §9.4.29;
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

### 9.4.6 Polar Haar measure and the discrete-series integrability bound

The lowest-type coefficient estimate for the discrete-series construction is expressed in the logarithm of the positive factor of a matrix. Haar volume grows in that coordinate. For example, in $U(1,1)$ the logarithm has a single complex coordinate $b$. Writing $t=|b|$, its density is $\sinh(2t)/(2t)$. The flat radial factor $t\,dt$ becomes a constant times $\sinh(2t)\,dt$, which changes the critical exponent of a radial exponential.

**Coordinates and normalization.** Let $J=\operatorname{diag}(I_p,-I_q)$, $n=p+q\ge1$, $G=\{g:g^\dagger Jg=J\}$, and $K=G\cap U(n)=U(p)\times U(q)$. Here $\dagger$ denotes conjugate transpose. Let $\mathfrak p$ be the real vector space of Hermitian matrices satisfying $JXJ=-X$. In block coordinates set
$$
X(B)=\begin{pmatrix}0&B\\ B^\dagger&0\end{pmatrix},\qquad B\in\mathbb C^{p\times q},\qquad r=\|X(B)\|_F=\sqrt2\,\|B\|_F.
$$
Use probability Haar $dk$ on $K$ and entrywise real and imaginary Lebesgue measure $dB$. Put $q_0=\min(p,q)$, $c=\sqrt{2q_0}$ and $S(u)=\sinh(u)/u$ with $S(0)=1$. For the real eigenvalues $\xi_i$ of $X$, set $D(X)=\prod_{i<j}S(\xi_i-\xi_j)$.

**Polar measure and domination theorem.** For every Haar measure $\nu$ on $G$ there is a finite constant $C_\nu>0$ such that every nonnegative Borel $F$ satisfies
$$
\int_G F\,d\nu=C_\nu\int_{\mathbb C^{p\times q}}\int_K F(k e^{X(B)})\,dk\,D(X(B))\,dB.
$$
Moreover $1\le D(X)\le e^{(n-1)cr}$. If $q_0>0$ and $F(k e^X)\le M e^{-(nc+\delta)r}$ uniformly in $k$ for finite $M\ge0$ and $\delta>0$, then $F$ is integrable. For $q_0=0$ the block space is a point of mass one and the formula is compact Haar integration. In mixed signature the subgroup $K$ is the slice $B=0$ and has ambient Haar measure zero. It is the factor $dk$ that has probability mass one.

**Global chart.** For $g\in G$, the positive definite matrix $A=g^\dagger g$ satisfies $JAJ=A^{-1}$ by $g^{-1}=Jg^\dagger J$. Thus $X=\tfrac12\log A$ satisfies $JXJ=-X$. Also $e^X\in G$ since $Je^XJ=e^{-X}$, and $k=g e^{-X}$ is unitary and belongs to $G$. Uniqueness of the positive square root and Hermitian logarithm gives the inverse to $(k,X)\mapsto k e^X$. The logarithm is smooth on positive definite matrices, so the map is a diffeomorphism. The positive factor ranges over the part of the positive definite cone satisfying $JPJ=P^{-1}$, with the entire linear block space as its logarithm. The chart has multiplicity one. On an $m$-sheeted finite covering group, the pullback of the base density pushes forward to $m$ times that density, by local change of variables. Dividing by $m$ makes the normalizations compatible. When using singular values, ordering them removes the finite permutation multiplicity on the regular set. The angular variables still form a compact quotient by their stabilizer. [Paper] Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Proposition 1.143, pp. 116–117, gives the underlying global homeomorphism for adjoint-stable real algebraic matrix groups. [Author PDF](https://www.math.stonybrook.edu/~aknapp/download/Beyond2-clickable.pdf)

**Jacobian lemma.** Define the right action in logarithm coordinates by $a_g(X)=\tfrac12\log(g^\dagger e^{2X}g)$. Then
$$
|\det_{\mathbb R} da_g(X)|\,D(a_g(X))=D(X).
$$

**Proof.** Set $L_X(Y)=[X,Y]$ and $S(L_X)=\sum_{j\ge0}L_X^{2j}/(2j+1)!$. The differential of the matrix exponential at $2X$ in direction $Y$ is
$$
\int_0^1 e^{2(1-v)X}Y e^{2vX}\,dv=e^X S(L_X)(Y)e^X.
$$
Indeed, expanding under the integral gives the coefficient $2^{a+b}/(a+b+1)!$ of $X^aYX^b$, which agrees with the differentiated exponential series. Factoring out $e^X$ on both sides reduces the integral to that of $e^{(1-2v)L_X}$. Differentiating $e^{2a_{e^X}(Z)}=e^X e^{2Z}e^X$ at $Z=0$ and cancelling the outer factors and the scalar $2$ gives $S(L_X)\,da_{e^X}(0)=I$ on $\mathfrak p$.

In an orthonormal eigenbasis for $X$, the matrix units have $L_X$-eigenvalues $\xi_i-\xi_j$. The real determinant of $S(L_X)$ on the entire complex matrix space is therefore $\prod_{i,j}S(\xi_i-\xi_j)^2=D(X)^4$. To identify the contribution of $\mathfrak p$, decompose the real matrix space into $\mathfrak p$, $i\mathfrak p$, $\mathfrak k$, and $i\mathfrak k$, where $\mathfrak k$ is the space of skew-Hermitian matrices commuting with $J$. The operator $L_X$ interchanges $\mathfrak p$ and $\mathfrak k$ and likewise their multiples by $i$, since it reverses both the adjoint sign and the $J$-parity. In the real Frobenius inner product $L_X$ is self-adjoint by cyclicity of trace. On each positive eigenspace of $L_X^2$, $L_X$ identifies the portions in $\mathfrak p$ and $\mathfrak k$, with inverse given by $L_X$ divided by that eigenvalue. Thus the even series has equal determinants on these portions. The zero eigenspace contributes factors $1$. Multiplication by $i$ identifies the other two determinants. Taking the positive fourth root gives $\det_{\mathbb R}(S(L_X)|_{\mathfrak p})=D(X)$.

Write $e^Xg=k'e^Y$ where $Y=a_g(X)$. Since $a_{gh}=a_h\circ a_g$, this equality gives $a_g\circ a_{e^X}=a_{e^Y}\circ a_{k'}$. The action of $k'$ is conjugation by its inverse and fixes zero with determinant of absolute value one. Differentiating at zero and using $|\det da_{e^X}(0)|=1/D(X)$ and the same identity for $Y$ proves the lemma.

**From the Jacobian to Haar measure.** Change of variables gives invariance of $D(X)\,dB$ under $a_g$. Right translation replaces $(k,X)$ by $(kk',a_g(X))$, with $k'$ depending on $g,X$. Right invariance of compact Haar removes $k'$ in the inner integral. Inversion sends $(k,X)$ to $(k^{-1},-\operatorname{Ad}(k)X)$. At fixed $k$ the block transformation preserves Lebesgue measure, since it is orthogonal for the Frobenius norm, and preserves $D$, since conjugation preserves eigenvalues and $S$ is even. Compact Haar is inversion invariant. The resulting pushforward is therefore left invariant as well. It is finite on compact sets and positive on nonempty open sets by the global chart and positivity and continuity of $D$. Haar uniqueness now gives $C_\nu$. Tonelli and change of variables apply to nonnegative Borel functions with infinite integrals allowed.

In the archive, `dk` divides `muK` by its positive finite mass. `PCoord` chooses the lower-triangular entry for each opposite-sign pair in the original, possibly interleaved, signature order. The map `phiL` permutes complex coordinates and conjugates the entries whose representatives lie in the adjoint block. Hence it has real absolute determinant one in entrywise Lebesgue coordinates. With arbitrary additive Haar normalizations, its pushforward and the target volume differ by a positive finite constant. This is the equality underlying `lintegral_pmat_le`. The group measure `muPolar` is obtained by transferring the ambient matrix pushforward along the group embedding. The separate `muCD` includes the scalar `cPQ`. The measurable embedding and full-measure support justify integration on the group instead of the ambient matrix space. `IntMuCD.lean:122–146` gives `lintegral_muPolar` and `lintegral_muCD`. The latter is used in `SumInnerBasisSqEqAdjoint.lean:145`. The positive fourth-root calculation is read in `ProdShcSqEqJacPow.lean:20–67`, with `detPa`, `detPb` and `det_shcAdCL_pos` at their interfaces. The measure `muG` of the coefficient consumer is covered by Haar proportionality. [Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/PolarHaar.lean:16–40`, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/JacAll.lean:115–147`, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CorePInvInUJ.lean:38–62`, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/HaarPolar.lean:61–190`.

**Exponential bound and the actual coefficient.** Since $S(u)=\int_0^1\cosh(vu)\,dv$, we have $1\le S(u)\le e^{|u|}$. Each eigenvalue appears in $n-1$ pairs. Each off-diagonal block has rank at most $q_0$, so at most $2q_0$ eigenvalues are nonzero. Cauchy–Schwarz and $\sum_i\xi_i^2=r^2$ give
$$
\log D(X)\le\sum_{i<j}|\xi_i-\xi_j|\le(n-1)\sum_i|\xi_i|\le(n-1)cr.
$$
The archive relaxes $n-1$ to $n$. Under the domination hypothesis the remaining integral is bounded by a constant times $\int_0^\infty t^{d-1}e^{-\sqrt2\delta t}\,dt$, with $d=2pq$ and $t=\|B\|_F$. By substitution and integration by parts this is $(d-1)!/(\sqrt2\delta)^d$.

Take $F(g)=\|\Psi_M(g)\|^2$ where $\Psi_M$ is the archive’s continuous operator-valued function on $G$ for a lowest $K$-type $T$, with the shifted integral regular Harish-Chandra parameter and cross-sign gap at least $h$ used in the archive’s integrability theorem. Take as input the bound $\|\Psi_M(k e^X)\|\le \exp[-(h/8)\min(r^2,r/c)]$. The inequality $r^2\ge r/c-1/(4c^2)$ follows by completing the square, so its linearized bound is $\|\Psi_M(k e^X)\|\le A e^{-hr/(8c)}$, $A=e^{h/(32c^2)}$. The residual exponential rate is $\delta=h/(4c)-nc>0$ precisely when $h>8nq_0$. Continuity supplies measurability. This norm-square integral is the middle conjunct of `psiM_integrable` for each Haar measure. The archive carries it through `psiAll` and `psiExists` to the projection `(h6 μ hμ).2.1 h8`, which fills the Haar-quantified $L^2$ field of `IsPsiFor`. With its other hypotheses `dsExistsG` builds `sigLam` on `Hlam` using this witness. In `coef_memLp_all` the vector $w_0$ is the $L^2$ class `uniformisationL2 ε Ψ v₀ T.w`. The seed identity is $\langle w_0,\operatorname{sigLam}(g)w_0\rangle=\|w_0\|^2\langle T.w,\Psi_M(g)T.w\rangle$. It bounds the self-coefficient by $\|w_0\|^2\|T.w\|^2\|\Psi_M(g)\|$. The consumer obtains this seed on `muG` via `datumFunction_isSmoothL2` and uses the established all-vector argument in `sqInt_sigLam`. [Lean, read] A2, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/JacBound.lean:14–20`, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IntegrA.lean:85–144`, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/Integr.lean:67–87`, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/EqZeroOfDatumEmbeddingEqZero.lean:15–31,61–74`, `src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/SigLamMemLpOfNe.lean:33–105`.

**Rank one.** In $U(1,1)$ the eigenvalues are $t,-t$ with $t=|b|$. With the stipulated flat measure and compact probability measure the radial model $e^{-at}$ has integral, before multiplication by $C_\nu$,
$$
2\pi\int_0^\infty t S(2t)e^{-at}\,dt
=\frac{\pi}{2}\int_0^\infty(e^{-(a-2)t}-e^{-(a+2)t})\,dt
=\frac{2\pi}{a^2-4}\qquad(a>2).
$$
Near zero the density is of order $t$. At infinity the integrand is asymptotic to a positive multiple of $e^{-(a-2)t}$, so it diverges for $a\le2$. A squared profile $e^{-2\gamma t}$ therefore has critical exponent $\gamma=1$. For a locally integrable squared matrix coefficient, comparison of its compact angular average with the model by positive constants on the tail gives the same threshold. An upper comparison suffices for convergence in that range.

**Rank two.** In $U(2,2)$ let $t>s>0$ be the singular values of $B$. The eigenvalues of $X(B)$ are $t,s,-s,-t$, giving $D=S(2t)S(2s)S(t+s)^2S(t-s)^2$. For the flat radial factor write $B=U\operatorname{diag}(t,s)V^\dagger$. At the diagonal the real diagonal changes are $dt,ds$, and the imaginary diagonal changes are the relative phase directions scaled by $t,s$. If $u,v$ are the upper off-diagonal entries of the two infinitesimal skew-Hermitian matrices, the off-diagonal variations, with the lower entry conjugated, are $(su-tv,-tu+sv)$. Their complex determinant is $s^2-t^2$ and their real absolute determinant is $(t^2-s^2)^2$. The omitted common diagonal phases form the stabilizer. The compact action preserves flat volume, so the angular measure is invariant probability on the quotient up to a constant. The ordered chamber counts each regular orbit once, and zero or repeated singular values lie in polynomial zero sets of flat measure zero. To fix the constant with probability angular measure, integrate the flat Gaussian $e^{-\|B\|_F^2}$, whose entrywise integral is $\pi^4$. Substitute $a=t^2$, $b=s^2$ in the radial integral. It becomes $\frac14\int_{a>b>0} e^{-(a+b)}(a-b)^2\,da\,db=\frac14$, since the integral in $z=a-b$ is $\int_0^\infty z^2 e^{-z}\,dz=2$ and the $b$ integral is $1/2$. Thus the flat radial density is $4\pi^4 ts(t^2-s^2)^2$. After multiplying by $D$ the radial density is $\pi^4$ times
$$
\sinh(2t)\sinh(2s)\sinh^2(t+s)\sinh^2(t-s)\,dt\,ds.
$$
With $x=\cosh(2t)$ and $y=\cosh(2s)$, use $x-y=2\sinh(t+s)\sinh(t-s)$ to obtain $\frac{\pi^4}{16}(x-y)^2\,dx\,dy$ on $1\le y\le x$. For the radial model $(xy)^{-\beta}$ the group integral is $C_\nu\pi^4 I_\beta/16$, where
$$
I_\beta=\int_1^\infty\int_1^x (x-y)^2 x^{-\beta}y^{-\beta}\,dy\,dx.
$$
For $\beta>3$ substitute $u=y/x$ and reverse the order by Tonelli. Then
$$
I_\beta=\int_0^1 (1-u)^2u^{-\beta}\int_{1/u}^{\infty}x^{3-2\beta}\,dx\,du
=\frac{1}{2\beta-4}\int_0^1(1-u)^2u^{\beta-4}\,du
=\frac{2}{(2\beta-4)(\beta-3)(\beta-2)(\beta-1)}.
$$
The last equality follows by expanding the square and integrating three powers. For $\beta\le3$, on $1\le y\le2$, $x\ge4$ the integrand is bounded below by a positive constant times $x^{2-\beta}$. This gives divergence, logarithmic at $\beta=3$. Since $\cosh(2t)$ is comparable to $e^{2t}$ on $t\ge0$, the model has critical exponential rate $6$ in $t+s$. It defines a bi-$K$-invariant test function on the group. For an actual locally integrable squared coefficient the corresponding comparison must hold after averaging over the compact left factor and the angular orbit of the block. The critical exponents in these two examples concern the specified profiles.

**Scope.** The coefficient result uses the Casimir and representation inputs `psiM_casimir`, `closGen_stable` and `sigLam_irred` and the lowest-type inputs `HCMultDSG`, `LowKMultOneG` and `ffa_kmap_zero` at the construction and coefficient-identity interfaces. The separate weighted range takes `DiscreteSeriesDecayBound` and `volGrowthR` as inputs, and the comparison of degrees takes `FormalDegreeRatioAlt`. The use of the weighted family on the final RH path remains [Open]. The archive pin is A2, joined SHA-256 listed in [Sources](../sources/SOURCES.md#primary-sources-a).

**The measure in the next step.** For a nonzero vector in a model with a positive Schur degree, the diagonal integral on this Haar is inverted to obtain the degree. The same positive Haar scale must be used for both vectors in a degree comparison. The weighted seed and the two tensor directions have their own hypotheses. [§9.4.7](#947-formal-degree-ratios-under-a-shift-of-the-parameter) · [§9.4.29](#9429-polar-bounds-for-the-weighted-psim-kernel)

---

### 9.4.7 Formal-degree ratios under a shift of the parameter

A Bessel estimate can compare two local data $A$ and $A'$ whose discrete series have neighboring parameters. At a fixed real place the two normalizing degrees enter as $A'.\mathrm{deg}/A.\mathrm{deg}$. A numerical formula for each degree would involve a Haar constant. The comparison can be made with no evaluation of that constant, provided both degrees use the same Haar measure. The reason is that the parameter dependence is a product over roots, and a one-coordinate shift changes only the roots incident to that coordinate.

**First example: weights two and three for $U(1,1)$.** Use the holomorphic lowest-weight convention in which the unit lowest-type self-coefficient on the split radial element has magnitude $(\cosh t)^{-k}$. For the disk model the unit constant vector has self-coefficient $j(g^{-1},0)^{-k}$, where $j(g,z)=cz+d$ for the fractional linear action. On the split radial element the lower-right entry is $\cosh t$, and the compact angular factors act on the constant vector by phases. We use this disk coefficient and the Haar density of §9.4.6. With angular mass absorbed in a fixed $C>0$, the radial measure on the group, or on its scalar-center quotient with probability measure on the center, is $C\sinh(2t)\,dt$ for this integral. In fact, in the single complex polar coordinate of radius $t$, the density in §9.4.6 contributes $\sinh(2t)/(2t)$ and plane polar coordinates contribute $2\pi t\,dt$. Write $u=\cosh^2 t$, so $du=\sinh(2t)\,dt$. The squared coefficient has integral
$$
I_k=C\int_0^\infty(\cosh t)^{-2k}\sinh(2t)\,dt
=C\int_1^\infty u^{-k}\,du=\frac{C}{k-1}\qquad(k>1).
$$
By the diagonal case of Schur orthogonality, the two degrees are $1/C$ and $2/C$. Their ratio is $2$. In the archive's order, take the two parameters $(3/2,1/2)$ and $(5/2,1/2)$. In the basis with the weight-$k$ coordinate first the lowest-type weights are $(2,0)$ and $(3,0)$, since the compact root set is empty and $\rho_N=(1/2,-1/2)$. The sole root gap goes from $1$ to $2$.

Moving the second coordinate of $(3/2,1/2)$ up by one instead makes the entries equal. The corresponding weight-one radial calculation gives $C\int_1^R du/u=C\log R$, which diverges. The integral also illustrates the difference between ordinary and weighted square integrability. Along the radial element the squared Frobenius norm is $2\cosh(2t)=4u-2$. With the Frobenius factor inserted in the coefficient, the norm-square integral at weight two becomes $C\int_1^\infty(4/u-2/u^2)\,du$, which diverges although $I_2$ is finite. The example gives the ordinary degree ratio and illustrates why a consumer asking for the weighted hypothesis needs a separate range argument. [Expository] See the [polar Haar formula](#946-polar-haar-measure-and-the-discrete-series-integrability-bound). The archive's corresponding rank-one polynomial is computed in A2, source table below.

**Definitions and hypotheses.** Fix $G=U(p,q)$, $n=p+q\ge1$, with its signature signs assigned to the ordered diagonal coordinates, and let $m$ be a nonzero positive Haar measure on $G$. Its scalar center $Z=\{zI:|z|=1\}$ is compact. A unitary central character makes $|\langle v,\pi(g)v\rangle|^2$ constant on the cosets of $Z$, even when the coefficient itself acquires a phase along them. Give $Z$ probability Haar and take the compatible Haar $\bar m$ on $G/Z$, equivalently the pushforward of $m$. Quotient integration gives the same integral of this nonnegative function on $G$ and on $G/Z$. If the central Haar has mass $z_0>0$ and the quotient measure is made compatible with it, the group integral is $z_0$ times the quotient integral. Thus the quotient degree is then $z_0$ times the group degree. This convention also works when the two representations have different central characters. Haar quotient integration starts with compactly supported continuous functions and extends to nonnegative measurable functions by equality of the associated Radon measures. [Paper] Knapp, Theorem 8.36 and (8.37), p. 538. [Author PDF](https://www.math.stonybrook.edu/~aknapp/download/Beyond2-clickable.pdf)

A parameter $\lambda=(\lambda_1,\ldots,\lambda_n)$ in the archive satisfies $\lambda_1>\cdots>\lambda_n$ and $\lambda_i-(n-1)/2\in\mathbb Z$. It is already a Harish-Chandra parameter in the shifted lattice. A unit shift $\lambda+e_s$ increases coordinate $s$ by one, with the signature signs attached to their original coordinates. There is no further addition of $\rho$ in this operation. The complex root spaces are the off-diagonal matrix units, so their roots have evaluations $\lambda_i-\lambda_j$. Using one root from each pair of opposite roots, set
$$
V(\lambda)=\frac{\prod_{i<j}|\lambda_i-\lambda_j|}{\prod_{i<j}(j-i)}.
$$
Here $\rho_i=(n+1-2i)/2$ has differences $\rho_i-\rho_j=j-i$. Both compact and noncompact roots occur in the numerator. Root differences annihilate the scalar direction, so projecting the parameter onto the trace-zero hyperplane leaves $V$ unchanged. That projection in the root calculation is compatible with integrating coefficient magnitudes on $G/Z$, even for representations with nontrivial central character.

For a supplied irreducible unitary discrete series $\pi$, define $d_m(\pi)>0$ by the usual Schur orthogonality normalization. For each $v\ne0$ its diagonal formula reads
$$
d_m(\pi)=\frac{\|v\|^4}{\int_G|\langle v,\pi(g)v\rangle|^2\,dm(g)}.
$$
This is the archive's $\mathrm{fdegOf}$ whenever the positive formal-degree identity $\mathrm{IsFdeg}$ holds. The numerical hypothesis **HCFdeg** says there is one $c_m>0$ for the fixed group and measure, independent of the parameter and representation, such that $d_m(\pi_\lambda)=c_m V(\lambda)$ for every supplied discrete series with that parameter. In Lean the measure is $\mathrm{muG}(\varepsilon)$ and the hypothesis asserts the full $\mathrm{IsFdeg}$ identity. Existence and identification of the representations at the stated parameters are separate inputs to the comparison. Existence and parameter identification enter through the supplied representations. [Lean, read] A2, source table below.

For a classical example of the numerical formula with a common measure, see Knightly and Li, §A.6, p. 736, remark (1), for the symplectic case. [Paper] [Publisher PDF](https://ems.press/content/serial-article-files/26473)

**Theorem (conditional local ratio).** Suppose the numerical hypothesis holds and discrete series are supplied at the two regular parameters $\lambda$ and $\lambda+\delta$, on the same $G$ and with the same $m$. Then
$$
\frac{d_m(\pi_{\lambda+\delta})}{d_m(\pi_\lambda)}
=\prod_{i<j}\frac{|(\lambda_i-\lambda_j)+(\delta_i-\delta_j)|}{|\lambda_i-\lambda_j|}.
$$
In particular, when $\delta=e_s$ and both parameters satisfy the archive conditions, this simplifies to
$$
\frac{d_m(\pi_{\lambda+e_s})}{d_m(\pi_\lambda)}
=\prod_{t\ne s}\frac{\lambda_s+1-\lambda_t}{\lambda_s-\lambda_t}.
$$

**Proof.** Evaluate the full formal-degree identity with all four vectors equal to $v\ne0$. The coefficient times its complex conjugate is its squared magnitude and the numerator on the Schur side is $\|v\|^4$. The integral is finite and positive, giving the displayed diagonal formula with degree $c_mV(\lambda)$, and the same argument applies to any nonzero vector of the shifted series. Dividing cancels $c_m$ and the positive product $\prod_{i<j}(j-i)$. The original regularity makes every remaining denominator nonzero. Taking the quotient inside the finite product proves the first formula.

For the unit shift, a pair $i<j$ with neither index $s$ contributes $1$. If $i=s$, its factor is $|(\lambda_s-\lambda_j)+1|/|\lambda_s-\lambda_j|$. If $j=s$, negate both differences inside the absolute values to obtain $|(\lambda_s-\lambda_i)+1|/|\lambda_s-\lambda_i|$. These two classes cover each $t\ne s$ once. Now $a=\lambda_s-\lambda_t$ is an integer because the two coordinates belong to the same shifted lattice. Original and shifted regularity say $a\ne0$ and $a\ne-1$. If $a\ge1$, then $a$ and $a+1$ are positive. If $a\le-2$, both are negative. Thus $|a+1|/|a|=(a+1)/a>0$ for every factor, which gives the signed-looking formula with positive value. This is the cancellation used by the archive, including its treatment of pairs where $s$ is the second index. [Lean, read] A2, source table below.

**Second example: the three positive roots for $U(2,1)$.** Take signs $(+,+,-)$ and $\lambda=(5,2,-2)$. The shift lattice is integral here. The pairs $(1,2),(1,3),(2,3)$ have gaps $(3,7,4)$ and $\rho$-gaps $(1,2,1)$. Thus $V(\lambda)=3\cdot7\cdot4/2=42$. After raising coordinate two the gaps become $(2,7,5)$ and the degree polynomial becomes $35$. The ratio is
$$
\frac{35}{42}=\frac{2}{3}\cdot1\cdot\frac54
=\frac{2+1-5}{2-5}\cdot\frac{2+1-(-2)}{2-(-2)}=\frac56.
$$
One changed root is compact and one is noncompact. If we then raise coordinate one, the new gaps are $(3,8,5)$, giving $V(6,3,-2)=60$. This step gives $(3/2)(8/7)=12/7$ and the two steps give $(5/6)(12/7)=10/7=60/42$. The simultaneous shift of coordinates one and two keeps their mutual gap equal to $3$ and changes the other two gaps to $8$ and $5$. It gives $(8/7)(5/4)=10/7$ directly. These are conditional degree ratios when the corresponding series are supplied. Every subset shift of $(5,2,-2)$ has all ordered gaps at least two, so the tuple also witnesses the arithmetic part of the insertion-chain hypotheses. [Expository]

**Regularity and signs.** A collision at the starting parameter makes a root denominator vanish. A collision at the target gives a zero of the polynomial, outside the regular discrete-series hypothesis. The quotient of signed Vandermondes has the sign of the permutation of the target coordinates relative to the starting ordering if a more general shift crosses root walls. The absolute product removes that sign. The unit-step proof uses the integral lattice to rule out a crossing without a collision. To see the role of integrality, take the strictly decreasing real pair $\lambda=(0,-1/2)$ and raise coordinate two. The absolute root quotient is $1$, whereas the signed product is $-1$. Both tuples have distinct entries, but the gap crosses zero without a collision at either endpoint. A genuine failure of square integrability of the self-coefficient also rules out its use in the positive degree identity. Failure to meet a sufficient gap bound in §9.4.6 alone establishes neither divergence nor collision.

**Conditional producers and the actual unit-bound call.** The direct producer `formal_degree_ratio_of_HC_formula` uses the `ds` field of `TensorDS` at an index in `Sm` to obtain the shifted parameter and its discrete-series model. It applies `HCFdeg` twice and uses the diagonal identity and unit-shift lemma just proved. In full, `FormalDegreeRatioAlt D` ranges over every dimension and signature, every parameter and complete complex Hilbert space, each source model $\sigma$, and each `TensorDS` witness $X$. It assumes `IsHCParam`, `IsDS`, and $\operatorname{frob}(g)\operatorname{coefOn}(\sigma,v,w)(g)\in L^2(\mathrm{muG})$ for every pair of $K$-finite vectors. For every $s\in X.\mathrm{Sm}$ and every nonzero source and target vector, it gives the displayed unit quotient of the two `fdegOf` values on `muG`. The `HCFdeg` producer accepts the weighted hypothesis of this interface without using it. The insertion proof `deg_chain` supplies it at each intermediate parameter and uses `adm18` for the `TensorDS` witnesses and their permitted indices. For any subset $I$ let $1_I=\sum_{i\in I}e_i$. When every intermediate $\lambda+1_J$ has gaps at least two, adding a fresh coordinate leaves all ordered gaps positive and preserves shifted integrality. Choose one nonzero vector at each supplied step. For the empty subset the ratio is $1$. For an insertion, multiply the one-step ratio by the ratio already proved from the starting representation to the current one. All degree polynomials are positive, and the induction can divide by the current degree since its ratio to the positive starting degree is positive. Both the degree and the root-polynomial ratios telescope. The result is the comparison between the starting model and the final tensor-branch model at $\lambda+1_I$. [Lean, read] A2, source table below.

**Conditional comparison for `GoodS`.** Fix $D$, $W$, the signature `epsSH D.R` and dimension $2D.R.rS+D.R.k+1$. Take `adm18 D` and `FormalDegreeRatioAlt D`, a parameter $\lambda$ and a finite set $I$ of coordinates. Assume `AllGaps` at least $2$ for every subset shift $\lambda+1_J$. For every $J$ for which $\lambda+1_J$ is an `IsHCParam`, assume that every `IsDS` model at that parameter on any complete complex Hilbert space has Frobenius-weighted $L^2(\mathrm{muG})$ coefficients for all pairs of $K$-finite vectors. At $\lambda+1_I$ assume `GapAtLeast` for some $h_b>\mathrm{thrDS}$ in the original signature. Given $A,A'$ in the same `LocS W` satisfying `GoodS` at $\lambda,\lambda+1_I$, respectively, `up_G` gives the following comparison. Its proof uses the supplied gapped uniqueness at that threshold. In its setting the normalization of $A.\mathrm{deg}$ is $b\,\mathrm{muG}(\varepsilon)$ for $b=\mathrm{cdScale}(D,\varepsilon)>0$. The Cayley matrices in the discrete-series condition and the degree condition can differ. If they are $P'$ and $P$, respectively, then $Q=P(P')^{-1}$ preserves the same signature form since $P^\dagger JP=(P')^\dagger JP'$; conjugation by $Q$ on this group is implemented by the unitary Cayley realization of the representation. Its effect on a coefficient is to replace both vectors by their images under the same isometry. Their norms and inner products are preserved, so the Schur identity keeps its degree on the same measure. The unscaled degree of this Cayley model is consequently $bA.\mathrm{deg}$. A supplied gapped uniqueness isometry identifies the endpoint of the tensor chain with the Cayley model for $A'$. Intertwining gives pointwise identical self-coefficients after transporting the vector, so its unscaled degree is $bA'.\mathrm{deg}$. Cancel $b$ to obtain
$$
\frac{A'.\mathrm{deg}}{A.\mathrm{deg}}=\frac{V(\lambda+1_I)}{V(\lambda)}.
$$
The unit-bound consumer `degree_ratio_unit_bound_of_formal_degree_ratio` also uses the same one-step identity. Its `DegStep` input identifies the two degree ratios and supplies the tensor and weighted hypotheses, so the assumed `ProdBound` bounds the resulting root product. For a downward step it applies the upward bound to the reversed pair, then takes reciprocals of the positive endpoints. [Lean, read] A2, source table below.

**Calls in A2.** A2 has no call to `formal_degree_ratio_of_HC_formula` or `up_G`. The calls to `deg_chain` and `deg_datum` occur inside `up_G`. The actual family unit-bound call in `linkS_all` passes `h90`, `pStep` and `pProd` to `family_degree_ratio_unit_of_degree_and_prodBound`. Here `h90 x i = (h47 x i).2.2.2.2.1` is the fifth conjunct of `aux₃`, supplied through `AllHyp.s47`. Thus this call consumes `FormalDegreeRatioAlt` from a standing hypothesis. The unused `BesselShellOpenHypotheses.p90` is a further interface. [Open] The fulfillment of `AllHyp.s47`, full `GoodS` and declaration-level reachability from `Main` retain their separate proof obligations. [Source record](../sources/SOURCES.md#chapter-9-on-one-haar-measure)

**Classical scope.** Atiyah–Schmid, Theorem (8.1), p. 41, proves Harish-Chandra's formula for the connected semisimple finite-center setting with a compact Cartan, a nonsingular parameter in the shifted character lattice and a common Haar normalization. It multiplies over all roots positive for that parameter. In mixed signature $SU(p,q)$ has finite center and a compact diagonal Cartan. Restricting a unitary representation of $U(p,q)$ with scalar central character to $SU(p,q)$ preserves irreducibility because $U(p,q)=Z\,SU(p,q)$. The compact central factor and the finite overlap $Z\cap SU(p,q)$ are handled by compatible quotient Haar, giving a common normalization factor. The trace-zero restrictions preserve all root evaluations. Hence the numerical quotient here is a classical specialization for identified discrete series. The Lean assumption still names the identification with its own `IsDS` and the normalization on `muG`. [Paper] [Harish-Chandra (1966)](https://doi.org/10.1007/BF02392813) · [Atiyah–Schmid (1977)](https://www.math.utah.edu/~ptrapa/math-library/schmid/atiyah-schmid.pdf)

**Several real places.** On a finite product of real groups, take the product of the chosen quotient Haar measures and use the external Hilbert tensor product of the local discrete series. For a nonzero pure tensor the self-coefficient is the product of the local coefficients and its fourth power of the norm is the product of the fourth powers. Tonelli factors the squared integral into finite positive local integrals. Thus the degree on the product is the product of the local degrees. This conclusion also follows directly for the Schur identity, first on pure tensors by Fubini, then on finite sums by multilinearity and on the Hilbert tensor product by continuity of the resulting $L^2$ coefficient map and pointwise convergence of coefficients. If the finite product of places is denoted by $S_\infty$, the ratio is
$$
\prod_{v\in S_\infty}
\frac{d_{m_v}(\pi'_{v})}{d_{m_v}(\pi_v)}
=\prod_{v\in S_\infty}\frac{V(\lambda'_v)}{V(\lambda_v)}.
$$
Each place may have an independently chosen Haar normalization. Multiplying $m_v$ by $a_v>0$ divides each degree at that place by $a_v$, so it cancels if applied to both families. If one uses $a'_v m_v$ only for the numerator and $a_v m_v$ for the denominator, the ratio instead acquires $\prod_v a_v/a'_v$. A comparison of two different real groups carries their separate degree constants. This product observation concerns the chosen real measures, with no global volume formula assumed. [Expository]

**Source table and reading boundary.** All paths below start at the extraction root of A2. Its joined archive SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. [Archive record](../sources/SOURCES.md#primary-sources-a)

| Reading | Source | Role |
| --- | --- | --- |
| R3 | `src/Formalism/SharpRestriction/CuspSpanNormBounds/LowestKTypeMultiplicity.lean:2402–2445` | Statement of the numerical hypothesis `HCFdeg`. R3 covers the full bodies of `fdegOf_of_isFdeg`, `hc_int_diff` and `formal_degree_ratio_of_HC_formula`. |
| R3 | `src/Formalism/FormalDegreeBessel/FormalDegreeRatio/DSRatio.lean:10–96`; `src/Formalism/FormalDegreeBessel/FinalDS.lean:16` | Root-factor cancellation, integer sign argument, and the rank-one polynomial. `fdegRatio` calls the proved cancellation. |
| R2 | `src/Formalism/FormalDegreeBessel/StatementDS.lean:11–28,65–71`; `src/Formalism/SharpRestriction/CuspSpanNormBounds/RelevantZeroGramTerms.lean:29–45,72–77`; `src/Formalism/SharpRestriction/CuspSpanNormBounds/LeadMinorK.lean:189–207`; `src/Formalism/SharpRestriction/CuspSpanNormBounds/OnePlaceEstimates.lean:47–54,743–748` | Parameter, polynomial, square integrability, degree, shifted models and comparison interfaces. |
| R3 | `src/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/DegreeL2RangeHypothesis.lean:27–92`; `src/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/DegIsFdegCayley.lean:16–133` | Insertion induction, extraction of the datum degree, vector transport, Haar scaling and Cayley comparison. |
| R3 | `src/Formalism/SharpRestriction/CuspSpanNormBounds/FrobeniusCoefficientMemLp/DegIUp.lean:121–143`; `src/Formalism/SharpRestriction/CuspSpanNormBounds/AbsoluteAmplitudeSecondOfSource.lean:621–653` | The bodies of `up_G` and the unit-bound consumer. |
| R2 | `src/Formalism/SharpRestriction/CuspSpanNormBounds/NormalizedLocalScale.lean:137–148`; `src/Formalism/RealPlaceAnalysis/InstMeasurableSpaceUJ.lean:21` | `GoodS` and the underlying full-group Haar. |

The general Harish-Chandra classification and its identification with the archive's lowest-type predicate `IsDS` are inputs. The Harish-Chandra numerical formula `HCFdeg` is a separate input. The comparison reads `adm18`, `DegreeL2RangeHypothesis` or the supplied intermediate `hL2`, `deg_DSUniqG` via `BridgeDS3.discrete_series_unique_gapped`, and `DegStep` and `ProdBound` at their interfaces. The auxiliary datum positivity lemma `formal_degree_pos` is used by interface. The induction helper `deg_ind_up` and the positivity helper `deg_fdeg_pos` are also used by interface. The previous Schur, unimodularity, explicit $L^2$ and polar Haar supplies are cited at their existing scope. The derivation of those inputs and reachability of this comparison from the final RH theorem are outside the reading here [Open].

**Further local producers.** The large-gap translation ray computes the absolute degree on $\mu_{\rm CD}$ under its own family and tie hypotheses. The coordinate-density comparison identifies that Haar, the tensor sandwich supplies the recurrence under its named model and threshold inputs, and the weighted seed supplies the two tensor coefficient slots at $s=2$. These have their own direct calls and recorded scopes. [§9.4.26](#9426-recovering-the-formal-degree-constant-from-a-translation-ray) · [§9.4.27](#9427-paying-the-shared-compact-dual-haar-normalization-from-coordinate-densities) · [§9.4.28](#9428-how-the-tensor-sandwich-determines-a-one-step-formal-degree-ratio) · [§9.4.29](#9429-polar-bounds-for-the-weighted-psim-kernel)

---

### 9.4.21 Compact Pieri branching and the tensor step

**Motivation.** In a discrete-series tensor step, shifting one parameter coordinate asks for a compact intertwiner into a tensor product of the old lowest type and a finite-dimensional representation. A highest-vector calculation identifies the possible labels by testing a single tensor coordinate. A separate dimension identity decides which possibilities actually occur. Together these give the complete compact branching rule. [Lean, read]

**First example.** Let $x_1,x_2$ denote the standard basis in the symmetric algebra and put $V=\det^{-1}\operatorname{Sym}^2\mathbb C^2$, with label $(1,-1)$. Write $e_j$ for the standard tensor basis and $f_j$ for its dual. Suppress the common determinant factor. The raiser is $x_1\partial_{x_2}$ in the polynomial factor. On the standard factor it sends $e_2$ to $e_1$, and on the dual it sends $f_1$ to $-f_2$. Thus $x_1^2 e_1$ and $x_1^2 e_2-x_1x_2 e_1$ are highest, the latter by cancellation of $x_1^2 e_1$. In the dual tensor $x_1^2 f_2$ and $x_1^2 f_1+x_1x_2 f_2$ are highest, the latter by cancellation of $x_1^2 f_2$. All are nonzero by their displayed coordinates. The complete lists, with $\dim V_{(a,b)}=a-b+1$, are

| Factor | Labels in order of displayed vectors | Dimensions |
|---|---|---|
| Standard | $(2,-1),(1,0)$ | $4+2=3\cdot2$ |
| Dual | $(1,-2),(0,-1)$ | $4+2=3\cdot2$ |
| $\bigwedge^2$ | $(2,0)$, with vector $x_1^2(e_1\wedge e_2)$ | $3=3\cdot1$ |

The polynomial model is irreducible. Its monomial weights are distinct. A stable subspace containing any weight vector contains each of the three monomials by repeated application of $x_i\partial_{x_j}$. A stable subspace splits into its torus weight spaces by diagonal spectral projection. [Expository]

**Second example.** For $U(3)$ use $V=\det^{-1}\operatorname{Sym}^2\mathbb C^3$ of label $(1,-1,-1)$. Its six distinct monomial weights are connected by the same transfer operators, so the model is irreducible. Put $e_{ij}=e_i\wedge e_j$ for $i<j$. The simple raisers are $E_{12},E_{23}$, and $E_{13}=[E_{12},E_{23}]$. In the standard tensor take $x_1^2e_1$ and $x_1^2e_2-x_1x_2e_1$. The first raiser kills both by the same computation as in rank two, and the second has no nonzero action on their entries. The third candidate label $(1,-1,0)$ is forbidden. In the dual tensor take $x_1^2 f_3$ and $\sum_j x_1x_j f_j$. The contraction $\sum_j x_j f_j$ is invariant, because $E_{ab}$ acts on its polynomial factor by $x_a f_b$ and on its dual factor by $-x_a f_b$. The shift at index two gives $(1,-2,-1)$ and is forbidden.

For $\bigwedge^2$ take $x_1^2 e_{12}$ and
$$
x_1^2 e_{23}-x_1x_2 e_{13}+x_1x_3 e_{12}.
$$
The first vector is killed by both simple raisers. On the second, $E_{12}$ produces $x_1^2 e_{13}-x_1^2 e_{13}$, and $E_{23}$ produces $-x_1x_2 e_{12}+x_1x_2 e_{12}$. The omitted subset $\{1,3\}$ gives $(2,-1,0)$. The listed vectors have nonzero displayed coordinates, and vectors in each row have different torus weights. The three numerator factors in the rank-three dimension formula are $a-b+1$, $a-c+2$, $b-c+1$, with denominator $2$.

| Factor | Labels in order of displayed vectors | Dimensions |
|---|---|---|
| Standard | $(2,-1,-1),(1,0,-1)$ | $(4\cdot5\cdot1+2\cdot4\cdot2)/2=10+8=6\cdot3$ |
| Dual | $(1,-1,-2),(0,-1,-1)$ | $(3\cdot5\cdot2+2\cdot3\cdot1)/2=15+3=6\cdot3$ |
| $\bigwedge^2$ | $(2,0,-1),(1,0,0)$ | $(3\cdot5\cdot2+2\cdot3\cdot1)/2=15+3=6\cdot3$ |
| $\bigwedge^3$ | $(2,0,0)$, with vector $x_1^2(e_1\wedge e_2\wedge e_3)$ | $6=6\cdot1$ |

In both examples $\bigwedge^0$ gives the original type. The polynomial formula uses the standard unitary symmetric tensor inner product and the determinant character of modulus one. [Expository]

**Definitions.** Let $n\ge0$ and let $B_+,B_-$ partition the ordered set $\{1,\ldots,n\}$, possibly with empty blocks. Put $K=U(B_+)\times U(B_-)$ and use the original index order in each block. Write $\mathbf e_i$ for the $i$th unit weight. A label is dominant if $\mu_a\ge\mu_b$ whenever $a<b$ are in one block. For a finite-dimensional unitary representation the complexified matrix units $F_{ab}$ are used on this block domain, with $F_{ab}^\dagger=F_{ba}$ and the matrix-unit bracket. The highest space $H_\nu$ is the joint $\nu$-eigenspace of the diagonal units intersected with the kernels of the same-block $F_{ab}$ for $a<b$. An archive KType of label $\Lambda$ gives a unit highest vector $w$ spanning its highest line. The compact group supplies the same-block derived laws via `KType.kRel` and `KType.kUnit`. The highest-line input is `KType.hw_unique`: any nonzero compact highest vector in this cyclic record has label $\Lambda$ and lies in $\mathbb Cw$. These are named inputs from the separate, unpublished drafts on the compact derived action and the highest line. For a finite unitary tensor factor $Q$ with an orthonormal weight basis $(q_i)_{i\in I}$ of real weights $\gamma_i$, write a tensor as $(x_i)_{i\in I}$ with $x_i\in V$. The group acts by the tensor product and its differential is
$$
(F_{ab}x)_i=A_{ab}x_i+\sum_j M_{ab,ij}x_j.
$$
Indeed the group matrix acts by $\sum_j \rho(k)_{ij}\tau(k)x_j$, and differentiation at the identity splits the two factors. This is tensAct and the compact coordinate model of tensRep. [Lean, read]

**Lemma (highest coordinates).** For each real tuple $\nu$ the map
$$
H_\nu\longrightarrow\mathbb C^{\{i:\nu=\Lambda+\gamma_i\}},
\qquad x\longmapsto(\langle w,x_i\rangle)_i
$$
is injective. In particular a nonzero highest vector has an allowed shift and, for injective $\gamma$, its matching coordinate is a nonzero scalar multiple of $w$.

*Proof.* Give weights the order statistic $L(\gamma)=\sum_a a\gamma_a$. For $a<b$ in one block, the diagonal commutator implies $M_{ab,ij}\ne0$ only if $\gamma_i=\gamma_j+\mathbf e_a-\mathbf e_b$, so $L(\gamma_j)>L(\gamma_i)$. Choose $i$ maximizing $L(\gamma_i)$ among $x_i\ne0$. Every incoming tensor-factor term in the raising equation at $i$ vanishes by maximality. Thus $x_i$ is killed by the first-factor raisers and, by the diagonal equations, has weight $\nu-\gamma_i$. The inherited highest-line theorem gives $\nu-\gamma_i=\Lambda$ and $x_i=cw$ with $c\ne0$. Its inner product with $w$ in the displayed map is $c$. This proves triviality of the kernel and gives the dimension bound also when several basis vectors have the same weight. The archive uses zero-based indices in its statistic, with the same strict difference $b-a$. [Lean, read]

**Lemma (the finite-dimensional supply).** In the tensor representation there is an orthogonal decomposition into irreducible highest cyclic spans. Every nonzero stable subspace admits a nonzero highest vector. Indeed the diagonal units commute and are self-adjoint, so simultaneous diagonalization on the subspace gives real weights. Choose a weight maximizing $-\sum_a a\nu_a$. Each raiser would strictly increase this statistic, hence kills the chosen vector. Stable subspaces have stable orthogonal complements by the transpose adjoint law. In the cyclic span of a highest vector $x$, a nonzero stable subspace has a highest vector and the inherited cyclic highest-line theorem makes it a scalar multiple of $x$. Hence this cyclic span is irreducible. Split it off and repeat by induction on dimension, with the zero space giving the empty sum. Compact group invariance and derived stability agree by differentiation on `KType.op_curve` and the compact logarithm `exists_log` used in `KType.dτ_irred`, inherited from the unpublished compact-type draft. These arguments give the finite-dimensional supply used by compRed, with the normalized seed $x/\|x\|$ in kRepPiece. [Lean, read]

Any cyclic piece of highest label $\mu$ has integral dominant label. The diagonal group curve $\exp(itE_{aa})$ acts on its highest line by $\exp(it\mu_a)$, and identity at $2\pi$ forces integrality. For $a<b$ in one block the squared norm of $F_{ba}x$ is $(\mu_a-\mu_b)\|x\|^2$ by adjointness and the bracket. This proves dominance, also for any nonzero highest vector of the tensor. The same reasoning applies to $\Lambda$. The dimension input is the Weyl product
$$
D(\mu)=\prod_{B\in\{B_+,B_-\}}\prod_{a<b\text{ in }B}
\frac{(\mu_a+\rho_a)-(\mu_b+\rho_b)}{\rho_a-\rho_b},
\qquad
\rho_{b_j}=(|B|+1)/2-j
$$
for $b_1<\cdots<b_{|B|}$ in $B$. It is positive for dominant $\mu$. The archive's kType_finrank converts the factorial denominator in weylForK_closed to the product of compact root gaps. Within a block $\rho_{b_j}-\rho_{b_k}=k-j$, so the product is $\prod_{k=1}^{|B|}(k-1)!$. [Lean, read] for the adapter and finite-dimensional supply.

For the classical dimension input, apply Knapp's Theorem 5.84 to the restriction to $\bigoplus_B\mathfrak{sl}_{|B|}(\mathbb C)$. The complexified compact algebra is $\bigoplus_B\mathfrak{gl}_{|B|}(\mathbb C)$, and each block center acts by a scalar by irreducibility. Invariance under the semisimple differential therefore implies invariance under the whole differential and then the group, so the restriction is irreducible. Rank-zero summands contribute an empty product. The positive roots are the same-block differences $\mathbf e_a-\mathbf e_b$, and pairings with a root are differences of coordinates, with any common root normalization canceling in its quotient. Restricting $\mu$ to trace-zero diagonals removes a constant on each block and leaves those differences unchanged. This gives exactly $D(\mu)$. The proof below uses this classical dimension value. [§9.4.22](#9422-the-polynomial-model-behind-compact-weyl-dimensions) follows the polynomial-model supply used in A2. [Paper] [Knapp, second edition, p. 323, Theorem 5.84](https://www.math.stonybrook.edu/~aknapp/download/Beyond2-clickable.pdf)

**Proposition (dimension saturation).** Suppose $\gamma:I\to\mathbb R^n$ is injective, $D(\Lambda+\gamma_i)=0$ for each nondominant shift, and $\sum_iD(\Lambda+\gamma_i)=|I|D(\Lambda)$. Then for every real $\nu$, $H_\nu$ is one-dimensional exactly at the dominant shifts $\nu=\Lambda+\gamma_i$ and zero otherwise. Choosing any nonzero vector on each of those lines gives independent vectors and an orthogonal direct sum of their irreducible cyclic spans equal to $V\otimes Q$.

*Proof.* Decompose by the preceding lemma. Each piece has a nonzero highest vector, hence a dominant label and an index $i$ by the highest-coordinate test. Two orthogonal pieces with the same index would give two independent vectors in a highest space of dimension at most one. Therefore the labels inject into the dominant indices. Add their dimensions. The total is $|I|D(\Lambda)$ by the tensor dimension, and the hypothesized sum over all dominant indices has that same value. Each term is strictly positive, so every dominant index occurs. The nonzero seed for a given index can be taken from the orthogonal decomposition at that index, or uniquely scaled to $x_i=w$ using the coordinate test. Its cyclic span is the whole piece. The highest spaces for all other labels vanish by the coordinate and dominance tests. Orthogonality of the pieces proves independence and exhaustiveness. This construction through compact splitting and counting specifies a nonzero witness and allows normalization. A pure highest tensor works for the Cartan shift when the chosen factor vector is itself highest, since the two terms of each raising equation then vanish separately. [Lean, read] for the counting proof. [Expository] for coordinate normalization.

**Theorem (compact Pieri).** For every such $K$ and every KType $V_\Lambda$, the proposition applies to each of the following factors, with the indicated full weight list.

| Tensor factor $Q$ | Basis weights $\gamma$ | Source scope |
|---|---|---|
| $\mathbb C^n$ | $\mathbf e_i$ for all $i$ | pieriStd |
| $(\mathbb C^n)^\vee$ | $-\mathbf e_i$ for all $i$ | pieriDual |
| $\operatorname{Hom}(\mathbb C^{B_{-\beta}},\mathbb C^{B_\beta})$ for either sign $\beta$ | $\mathbf e_i-\mathbf e_j$ for $i\in B_\beta,\ j\in B_{-\beta}$ | pPlus |
| $\bigwedge^r\mathbb C^n$ for every integer $r\ge0$ | $\sum_{i\in S}\mathbf e_i$ for $|S|=r$ | Expository extension |

*Proof for the archive factors.* The matrices of the three actions on a basis of weight vectors are the standard matrix units, the negative transposed units, and the commutator on directed block matrix units. In the third case the group acts by $Z\mapsto k_\beta Z k_{-\beta}^{-1}$, preserving the Hilbert–Schmidt form. Its differential sends $Z$ to $X_\beta Z-ZX_{-\beta}$ and gives pAdM. In the dual case the unitary group action is entrywise conjugation and has complexified differential $X\mapsto-X^{\mathsf T}$. These are continuous unitary actions with pairwise distinct basis weights. The sign of each nonzero coordinate recovers its index in the directed block case.

Put $u_a=\Lambda_a+\rho_a$. On each block these coordinates are strictly decreasing. Shifting $u_s$ by $c$ changes the Weyl product by the factor
$$
R_s(c)=\prod_{b\ne s\text{ in its block}}\frac{u_s-u_b+c}{u_s-u_b}.
$$
This follows by dividing the factors involving $s$, reversing the signs of numerator and denominator when needed. For a block of size $m>0$, take $P(z)=\prod_{b\in B}(z-u_b)$. The leading coefficient of degree $m-1$ in $P(z+c)-P(z)$ is $mc$. At $z=u_s$ its value is $c\prod_{b\ne s}(u_s-u_b+c)$. Interpolating at the $m$ distinct $u_s$ and comparing the coefficient of $z^{m-1}$ gives $\sum_{s\in B}R_s(c)=m$ for $c=\pm1$. For the empty block the empty sum gives zero. This proves the dimension sum for standard and dual. For directed block matrix units the change factor is $R_i(1)R_j(-1)$, since there are no cross-block root factors. The sum factors and gives $|B_\beta||B_{-\beta}|D(\Lambda)$.

A nondominant shift has an inversion across consecutive entries within a block. The integral original difference is nonnegative and can decrease by at most one across that pair, so the original gap is zero and the shifted gap is $-1$. The compact $\rho$ gap is one for such a pair. The numerator vanishes. This proves the remaining hypothesis for each archive factor. [Lean, read]

*Proof for exterior powers.* Wedge monomials are an orthonormal weight basis for the exterior action and their subsets determine distinct weights. Differentiating on decomposable wedges gives the sum of $X$ acting on one slot at a time, which is a Lie action by the product rule. Any consecutive label gap in a block can decrease by at most one under a subset shift, so the same wall argument applies. For the sum, in a block of size $m$ use the Vandermonde determinant $P_B(u)=\det(u_{b_j}^{\,m-k})_{j,k=1}^m=\prod_{j<k}(u_{b_j}-u_{b_k})$. Sum all subset shifts with a formal marker $t$ per shifted row. Multilinearity makes this the determinant whose $j,k$ entry is $u_{b_j}^{m-k}+t(u_{b_j}+1)^{m-k}$. Each column is $(1+t)$ times the original column plus a linear combination of columns of lower degrees. The determinant thus equals $(1+t)^m P_B(u)$ as a polynomial in $t$. The empty determinant is one. Divide the two block determinants by their constant compact-root denominators, multiply and compare the coefficient of $t^r$. This gives $\sum_{|S|=r}D(\Lambda+\sum_{i\in S}\mathbf e_i)=\binom nrD(\Lambda)$, with the binomial coefficient taken as zero for $r>n$. This proves the rule for all exterior powers, including the determinant twists and the zero space. For a single block $\bigwedge^{n-1}\mathbb C^n\simeq\det\otimes(\mathbb C^n)^\vee$ by the wedge pairing. In one block, after a determinant twist to a partition, the subset condition adds a vertical strip, with at most one box per row. This is the dual Pieri rule for multiplying a Schur function by an elementary symmetric function. [Symmetric Functions Catalog, Pieri rule](https://www.symmetricfunctions.com/schur.htm#schurPieriRule) [Expository]

**Remarks on existence and the block boundary.** `kType_exists_of_dom` supplies a complete KType for each integral dominant label, including the scalar module in rank zero. Its construction is in the separate, unpublished integral dominant-type draft. For any such input the standard and dual tensors are nonzero exactly when $n>0$, the directed block tensor exactly when both blocks are nonempty, and the exterior tensor exactly when $r\le n$. Each nonzero case has a dominant shift by the positive dimension sum. The forbidden shift from $(0,0)$ to $(0,1)$ for $U(2)$ already has the formal dimension $0$. Its weight vector in the standard module is $e_2$ and $E_{12}e_2=e_1$. Also, the squared-norm identity would force a negative norm square for a highest vector of this label, so the required highest space is strictly zero. For signature $(+,-,+)$ and trivial $V$, the standard tensor has two highest lines, $\mathbb Ce_1$ and $\mathbb Ce_2$. The cross-block operator $E_{12}$ carries the latter to the former in the ambient standard model. Projection onto $\mathbb Ce_2$ commutes with the compact group and fails to commute with this operator on $e_2$. The block restriction in the isometry and embedding contracts is therefore essential.

The same interleaved signature illustrates both directed block tensors. Take $V$ standard in the plus block with basis $v_1,v_3$ and trivial on the minus block, giving label $(1,0,0)$. For the plus-oriented matrix units $u_i=E_{i2}$, the highest vectors are $v_1u_1$ and $v_1u_3-v_3u_1$. The raiser $E_{13}$ kills the first and cancels the two terms of the second. The labels are $(2,-1,0)$ and $(1,-1,1)$ of dimensions $3,1$. For the opposite orientation take $f_i=E_{2i}$. The same raiser sends $f_1$ to $-f_3$ and kills $f_3$. The highest vectors $v_1f_1+v_3f_3$ and $v_1f_3$ give $(0,1,0)$ and $(1,1,-1)$ of dimensions $1,3$. Each list sums to $4=2\cdot2$. [Expository]

**The discrete-series handoff.** In TensorRepresentations/ExistsKEquivariantMap, pieri_standard_embedding takes two actual KType records $T,T'$ with shifted labels $\Lambda'=\Lambda\pm\mathbf e_s$. Dominance comes from $T'$. The call projects only the existence field for that index from pieriStd or pieriDual. It turns the witness into a normalized cyclic piece and applies the pointed isometry `kType_unique` of two complete same-signature, equal-label records with chosen unit highest vectors. Its proof is supplied by the separate, unpublished compact-model comparison draft. Inclusion of the piece and removal of the Hilbert coordinate wrapper give a nonzero linear map $\iota_0:T'.V\to\prod_cT.V$ with
$$
\bigl(\iota_0(T'(k)v)\bigr)_c
=\sum_d \rho(k)_{cd} T(k)\bigl(\iota_0(v)_d\bigr).
$$
Here $\rho(k)$ is the compact matrix $k$ or its entrywise conjugate. The proof uses the group identity of the isometry. Its stated output only requires nonzero and equivariant. The shift identity lowWeight_shifted relates the two lowest-type labels because the fixed signature correction in lowK cancels. The call occB_pairing_ne uses this map in a positive trace pairing and obtains a nonzero coefficient pairing by contradiction with spreading of vanishing. CoefEmbed.occ_exists then uses that pairing with its other analytic hypotheses in the coefficient embedding and eigenvalue steps. [Lean, read]

The separate cns_cpt_dec consumes all three fields, together with an injective weight list, the dominant index set, and a model of the required label at every active index. Compact splitting and the same-label isometry give orthogonal isometric equivariant embeddings with spanning images. Its explicit standard and dual calls appear in ExceptionalGroupG2/TensorProductsG2/ConsumerD. The one-shift consumer above uses a different contract. [Lean, read]

The pinned source is Alpöge and Claude's archive A2, joined SHA-256 **9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc**. The paths in this table are relative to **src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/**.

| Source | Local reading |
|---|---|
| HighestWeights/PieriRules/KTypeIntDomStatement.lean:11–56,138–183 | Tensor coordinates and precise branching statements. |
| HighestWeights/PieriRules/LowComp.lean:11–106 and TensHW.lean:14–74 | Maximal support coordinate and its injectivity bound. |
| HighestWeights/PieriRules/CountNotTwoOfFinrankLeOne.lean:34–177 and CartanKType.lean:16–26 | Dimension saturation and main entry points. |
| HighestWeights/PieriRules/BlockSum.lean:7–96, WeylRatio.lean:117–173, WeylSum.lean:15–98 and WeylVanish.lean:49–176 | Local products, interpolation and wall vanishing. |
| HighestWeights/Finrank.lean:15–50 and WeylBridge.lean:21–23 | Direct dimension input and normalization. |
| HighestWeights/ContinuousRepresentations/Decomp.lean:12–43 and EntryEqZeroOfComm.lean:150–234 | Orthogonal decomposition and cyclic-piece packaging. |
| TensorRepresentations/ExistsKEquivariantMap.lean:13–83, OccBLowKShiftF.lean:23–31,72–90, CoefEmbed.lean:45–69 and ConsumerC.lean:17–153 | One-shift and full compact consumers. |

Local R3 covers the named compact production and the indicated consumer arguments. The same-source preliminary review upheld the compact branching proof and the textbook exterior-power extension. In the noncompact handoff, positivity and weighted square integrability are separate premises of `occB_pairing_ne` and `occ_exists`. The compact exhaustion concerns the finite tensor only. The actual weighted estimates in this route are discussed in [§9.4.29](#9429-polar-bounds-for-the-weighted-psim-kernel), and [§9.4.28](#9428-how-the-tensor-sandwich-determines-a-one-step-formal-degree-ratio) uses the two one-shift maps. General discrete-series classification and declaration-level `Main` reachability are [Open] in this reading.

[Source and review ledger](../sources/SOURCES.md#chapter-9-compact-pieri-weyl-model-and-physical-fock-degree) · [Contributions](../CONTRIBUTIONS.md#chapter-9-compact-pieri-weyl-model-and-physical-fock-degree)

---

### 9.4.22 The polynomial model behind compact Weyl dimensions

**Motivation.** The dimension-saturation argument of [§9.4.21](#9421-compact-pieri-branching-and-the-tensor-step) (`pieriCount_of_st`) needs two facts about every irreducible compact cyclic piece: its dimension equals the formal compact Weyl product `weylK`, and that product is strictly positive. Classical Lie theory obtains the formula by evaluating the Weyl character quotient via l'Hôpital's rule. Inside archive A2, the proof takes an algebraic-combinatorial route instead: cleared matrix coefficients map a single-block $U(n)$ type injectively onto a normalized square dual Weyl polynomial module $W_\nu$, column-lexicographic leading monomials index a basis of $W_\nu$ by semistandard exponent arrays, row-and-column deletion turns the array count into Gelfand–Tsetlin box summation, a falling-factorial Vandermonde identity evaluates that recursion, and a commutant-slice induction multiplies dimensions across the two signature blocks.

**Worked model calculations.** Use one-based row and column indices $1\le a,t\le n$ and write $X_{at}$ for the indeterminate at row $a$, column $t$. Let $\mathcal R(g)f(X)=f(g^{\mathsf T}X)$, which is a left action since $(gh)^{\mathsf T}X=h^{\mathsf T}(g^{\mathsf T}X)$.

* *A nontrivial negative label on $U(2)$.* Take $\Lambda=(-1,-4)$. Subtracting its last coordinate $d=\Lambda_2=-4$ gives the normalized column shape $\nu=\Lambda-d\mathbf 1=(3,0)$. (If matrix coefficients are first cleared by $K=5$ powers of the determinant, the unnormalized column shape is $\mu=\Lambda+5\mathbf 1=(4,1)$, its last entry is $c=\mu_2=d+K=1$, and $W_{(4,1)}=\det(X)W_{(3,0)}$.) A polynomial in $W_{(3,0)}$ has degree $3$ in column $1$ and degree $0$ in column $2$, so the single column-addition condition $X_{a2}\mapsto X_{a2}+uX_{a1}$ acts trivially. Thus $W_{(3,0)}$ has the four-element monomial basis $X_{11}^3,X_{11}^2X_{21},X_{11}X_{21}^2,X_{21}^3$. Under $\mathcal R(g)$, $(g^{\mathsf T}X)_{11}=g_{11}X_{11}+g_{21}X_{21}$ and $(g^{\mathsf T}X)_{21}=g_{12}X_{11}+g_{22}X_{21}$, which is $\operatorname{Sym}^3\mathbb C^2$. Twisting by $\det(g)^{-4}$ gives `sqAct` and shifts the four row weights $(3,0),(2,1),(1,2),(0,3)$ to $(-1,-4),(-2,-3),(-3,-2),(-4,-1)$. Distinct torus weights split any stable subspace, and the derived operators $X_{11}\partial_{X_{21}}$ and $X_{21}\partial_{X_{11}}$ connect adjacent monomials with nonzero coefficients $1,2,3$, so the model is irreducible with highest seed $X_{11}^3$. The interlacing condition $f_{12}\le 0$ and $f_{12}+f_{22}\le f_{11}$ with column sums $(3,0)$ forces $f_{12}=f_{22}=0$ and leaves the four arrays $\begin{pmatrix}\kappa_1&0\\3-\kappa_1&0\end{pmatrix}$ for $\kappa_1\in\{0,1,2,3\}$. Deleting row $2$ and column $2$ leaves $\kappa_1\in B((3,0))=\{0,1,2,3\}$, each extending uniquely from the empty array, so $A_2(3,0)=4$. The Weyl quotient is $((-1)-(-4)+1)/1=4$. [Expository]

* *A chamber-wall label on $U(3)$.* Take $\Lambda=(2,2,-1)$ on the wall $\Lambda_1=\Lambda_2$. Removing $d=-1$ gives $\nu=(3,3,0)$ (and with clearing $K=2$, $\mu=(4,4,1)$ factors as $\det(X)W_{(3,3,0)}$). Write $M_{ab}=X_{a1}X_{b2}-X_{b1}X_{a2}$ for $1\le a<b\le 3$. Each $M_{ab}$ has column degrees $(1,1,0)$ and is fixed by all three upper column additions $X_{\cdot t}\mapsto X_{\cdot t}+uX_{\cdot s}$ ($s<t$), so all $\binom{3+3-1}{3}=10$ degree-three monomials $M_{12}^p M_{13}^q M_{23}^r$ ($p+q+r=3$) lie in $W_{(3,3,0)}$. In three dimensions every alternating $3\times 3$ matrix has even rank at most $2$, so every bivector in $\bigwedge^2\mathbb C^3$ is a pure wedge of two columns; hence $(M_{12},M_{13},M_{23})$ surjects onto $\mathbb C^3$ and its degree-three monomials are linearly independent. Conversely, any product of initial minors of shape $(3,3,0)$ consists of three size-$2$ minors (aside from size-$0$ factors equal to $1$), so those $10$ monomials span $W_{(3,3,0)}$. Under $\det(g)^{-1}\mathcal R(g)\simeq\det^{-1}\otimes\operatorname{Sym}^3(\bigwedge^2\mathbb C^3)$, the minor weights $(1,1,0),(1,0,1),(0,1,1)$ give $10$ distinct twisted weights $(p+q-1,p+r-1,q+r-1)$, off-diagonal derivations transfer one factor between any two minors, and $M_{12}^3$ is highest of weight $(2,2,-1)$. For $r=0,1,2,3$, $(p,q)$ has $4,3,2,1$ choices. Equivalently, $B((3,3,0))=\{(3,b):0\le b\le 3\}$ and $B((3,b))=\{b,\ldots,3\}$ has $4-b$ elements, summing to $4+3+2+1=10$. The Weyl factors are $\frac{2-2+1}{1}=1$, $\frac{2-(-1)+2}{2}=\frac{5}{2}$, and $\frac{2-(-1)+1}{1}=4$, with product $10$: a zero adjacent label gap stays positive because the $\rho_C$ shift adds $1$. [Expository]

* *An interior weight of multiplicity two on $U(3)$.* Take $\Lambda=(1,0,-1)$, giving $d=-1$ and $\nu=(2,1,0)$. In a $3\times 3$ array $f$ of column sums $(2,1,0)$, column $3$ vanishes and $f_{12}=0$. If $(f_{12},f_{22},f_{32})=(0,1,0)$, then $f_{12}+f_{22}=1\le f_{11}$ allows $(f_{11},f_{21},f_{31})\in\{(2,0,0),(1,1,0),(1,0,1)\}$, giving $X_{11}M_{12}$, $X_{21}M_{12}$, $X_{31}M_{12}$. If $(f_{12},f_{22},f_{32})=(0,0,1)$, then $1\le f_{11}+f_{21}$ excludes only $(0,0,2)$ and gives $X_{11}M_{13}$, $X_{21}M_{13}$, $X_{31}M_{13}$, $X_{21}M_{23}$, $X_{31}M_{23}$. Two of these eight basis polynomials share row weight $(1,1,1)$ and hence twisted weight $(0,0,0)$, namely $b_1=X_{31}M_{12}=X_{11}X_{31}X_{22}-X_{21}X_{31}X_{12}$ (from interlacing row $\kappa=(1,1)$) and $b_2=X_{21}M_{13}=X_{11}X_{21}X_{32}-X_{21}X_{31}X_{12}$ (from $\kappa=(2,0)$). The remaining candidate $X_{11}M_{23}=X_{11}X_{21}X_{32}-X_{11}X_{31}X_{22}$ satisfies $\det(X_{\cdot 1},X_{\cdot 1},X_{\cdot 2})=X_{11}M_{23}-X_{21}M_{13}+X_{31}M_{12}=0$: its column-lexicographic leading monomial $X_{11}X_{21}X_{32}$ collides with that of $b_2$, and subtracting $b_2$ leaves $-b_1$. Summing $A_2(\kappa)=\kappa_1-\kappa_2+1$ over $\kappa\in B((2,1,0))=\{(2,1),(2,0),(1,1),(1,0)\}$ gives $2+3+1+2=8=\frac{2\cdot 4\cdot 2}{1\cdot 2\cdot 1}$. [Expository]

**Definitions and single-block statement.** Fix $n\in\mathbb N$, a complex inner-product space $H$ (conjugate-linear in the first slot and $\mathbb C$-linear in the second), an operator map $\sigma:M_n(\mathbb C)\to(H\to_L H)$, a $\mathbb C$-submodule $S\le H$, and $\Lambda\in\mathbb R^n$. Write $U(n)=\mathrm{Kset}(\mathrm{allPos}\ n)$ and $T(\theta)=\operatorname{diag}(e^{i\theta_1},\ldots,e^{i\theta_n})$. In `PI.UpqRep`, `IsURepOn U(n) σ` means $\sigma(1)=1$, $\sigma(gh)=\sigma(g)\circ\sigma(h)$ for $g,h\in U(n)$, $\|\sigma(g)x\|=\|x\|$ for $g\in U(n)$ and $x\in H$, and continuity of $g\mapsto\sigma(g)x$ on $U(n)$ for each $x\in H$. A vector $v\in H$ has torus weight $\eta\in\mathbb R^n$ (`IsWtOn`) if $\sigma(T(\theta))v=e^{i\sum_a\eta_a\theta_a}v$ for all $\theta\in\mathbb R^n$. The predicate `IsKTypeOf (allPos n) σ Λ S` requires five clauses: $S$ is finite-dimensional over $\mathbb C$; $S$ is $U(n)$-stable; $S$ has no proper nonzero $U(n)$-stable $\mathbb C$-submodule; there exists $v_0\in S$ with $v_0\ne 0$ of torus weight $\Lambda$; and every nonzero $v\in S$ of torus weight $\eta$ satisfies `CDom`, namely
$$
\Lambda-\eta=\sum_{1\le a<b\le n} c_{ab}(\mathbf e_a-\mathbf e_b)\qquad(c_{ab}\in\mathbb N).
$$
Notice that $\sigma$ is only used on $U(n)$, and $S=\mathbb C$ with the empty root sum satisfies `IsKTypeOf` when $n=0$.

For $\nu\in\mathbb N^n$, the square dual Weyl submodule $W_\nu=\mathrm{dualWeyl}\ \mathbb C\ n\ n\ \nu\le\mathbb C[X_{at}]_{1\le a,t\le n}$ consists of polynomials with column multi-degree $\nu_t=\sum_{a=1}^n\deg_{X_{at}}$ that lie in the kernel of $X_{aj}\mapsto X_{aj}+uX_{al}$ minus the inclusion into $\mathbb C[X_{at},u]$ for every $1\le l<j\le n$ (`colAddGen`). Over the infinite domain $\mathbb C$, `DualWeylPoint` identifies the second clause with $f(X(1+cE_{lj}))=f(X)$ for all $l<j$ and $c\in\mathbb C$. A `DomWeight n` is a weakly decreasing tuple $\lambda\in\mathbb Z^n$ (`Antitone`), with signed shift $d=\lambda_n$ if $n>0$ and $d=0$ if $n=0$ (`detShift`), normalized natural tuple $\nu=\lambda-d\mathbf 1\in\mathbb N^n$ (`natW`), module $\mathrm{nablaSq}\ \mathbb C\ n\ \lambda=W_\nu$, and $\mathrm{GL}_n(\mathbb C)$-action $\mathrm{sqAct}(\lambda,g)f=\det(g)^d\mathcal R(g)f$.

**Theorem (single-block compact Weyl dimension, `weylForU_closed`).** For every $n\in\mathbb N$, $\Lambda\in\mathbb R^n$, complex inner-product space $H$, $\sigma:M_n(\mathbb C)\to(H\to_L H)$, and $S\le H$, if `IsURepOn U(n) σ` and `IsKTypeOf (allPos n) σ Λ S` hold, then $\Lambda\in\mathbb Z^n$ is weakly decreasing, $\dim_{\mathbb C}S=\dim_{\mathbb C}W_{\Lambda-d\mathbf 1}$ (`modelIso_closed`), and
$$
\dim_{\mathbb C}S=D_n(\Lambda)
=\frac{\prod_{1\le a<b\le n}(\Lambda_a-\Lambda_b+b-a)}{\prod_{k=0}^{n-1}k!}
=\prod_{1\le a<b\le n}\frac{\Lambda_a-\Lambda_b+b-a}{b-a},
$$
with empty products equal to $1$ for $n\le 1$. [Lean, read]

**Lemma 1 (cleared polynomial matrix coefficients and monoid extension).** Assume `IsURepOn U(n) σ`, $\dim_{\mathbb C}S<\infty$, and $U(n)$-stability of $S$. Then there exist $K\in\mathbb N$ and $P:M_n(\mathbb C)\to\operatorname{End}_{\mathbb C}(S)$ (`IsPolyMon P`) such that $P(1)=\mathrm{id}_S$, $P(gh)=P(g)P(h)$ for all $g,h\in M_n(\mathbb C)$, every matrix coefficient $g\mapsto\langle y,P(g)x\rangle$ ($x,y\in S$) is a polynomial in $(g_{at})$, and $P(u)x=\det(u)^K\sigma(u)x$ for all $u\in U(n)$ and $x\in S$.

*Proof.* The archive feeds `polynomial_coefficients` (`PI.PolyCoef`) and `unitaryGroupDense_holds` (`PI.UnitaryDense`) into `polyExt_of` (`PolyExt.lean:10–112`). First we give the direct complex proof of the two inputs. On the compact space $U(n)$, restrictions of polynomials in $(u_{at})$ and $\det(u)^{-1}$ contain the constants, separate points, and are closed under complex conjugation because $\overline{u_{at}}=(u^{-1})_{ta}$ is a cofactor divided by $\det(u)$, so the Stone–Weierstrass theorem makes this algebra $\mathcal A$ uniformly dense in $C(U(n))$. Against normalized Haar measure $du$ on $U(n)$, define $T_a x=\int_{U(n)}a(u)\sigma(u)x\,du\in S$ for $a\in\mathcal A$ and $x\in S$. For any $w\in H$ and $g\in U(n)$, left invariance of $du$ gives
$$
\langle w,\sigma(g)T_a x\rangle=\int_{U(n)}a(g^{-1}z)\langle w,\sigma(z)x\rangle\,dz.
$$
By matrix multiplication and Cramer's rule, $a(g^{-1}z)$ is a finite sum $\sum_r b_r(g)c_r(z)$ with $b_r,c_r\in\mathcal A$, so $\langle w,\sigma(g)T_a x\rangle\in\mathcal A$. The subspace $S_0=\operatorname{span}\{T_a x:a\in\mathcal A,\,x\in S\}\le S$ equals $S$: if a linear functional $\ell:S\to\mathbb C$ vanishes on $S_0$, then $\int_{U(n)}a(u)\ell(\sigma(u)x)\,du=0$ for all $a\in\mathcal A$; uniform approximation of $\overline{\ell(\sigma(u)x)}$ gives $\int_{U(n)}|\ell(\sigma(u)x)|^2\,du=0$, and continuity plus full Haar support force $\ell(\sigma(u)x)=0$ at $u=1$, hence $\ell=0$ (matching `Ugood_eq_top` in `IsPositiveDefiniteMatrixCoefficientOfMemAlgA.lean:160–188`). Clearing $\det(u)^{-1}$ yields `PolyCoef`. Next, if $Q\in\mathbb C[X_{at}]$ vanishes on $U(n)$, fix unitaries $u,v$ and restrict $Q(u\operatorname{diag}(z_1,\ldots,z_n)v)$ to $|z_a|=1$: a single-variable polynomial vanishing on $S^1$ vanishes on $\mathbb C$, so coordinatewise induction gives $Q(u\operatorname{diag}(z)v)=0$ for all $z\in\mathbb C^n$, and singular value decomposition covers all $M_n(\mathbb C)$, proving `UnitaryDense`.

Now follow `polyExt_of`. Choose an orthonormal basis $(b_i)_{i=1}^r$ of $S$ ($r=\dim_{\mathbb C}S$) and clearing witnesses $\langle b_i,\sigma(u)b_j\rangle\det(u)^{k_{ij}}=P_{ij}(u)$ on $U(n)$. Set $K=\sum_{i,j}k_{ij}$ and $Q_{ij}=P_{ij}\det(X)^{K-k_{ij}}$, and define $P(g)\in\operatorname{End}_{\mathbb C}(S)$ in the basis $(b_i)$ by the matrix $(Q_{ij}(g))$. On $u\in U(n)$, orthonormal expansion gives $P(u)x=\det(u)^K\sigma(u)x$, so $P(1)=\mathrm{id}_S$ and $P(uv)=P(u)P(v)$ for $u,v\in U(n)$. Fix $v\in U(n)$; each entry of $g\mapsto P(gv)-P(g)P(v)$ is a polynomial in $g$ vanishing on $U(n)$, hence identically zero by `UnitaryDense`. Then fix arbitrary $g\in M_n(\mathbb C)$; each entry of $h\mapsto P(gh)-P(g)P(h)$ is a polynomial in $h$ vanishing on $U(n)$, hence zero for all $h\in M_n(\mathbb C)$. Linearity in $x$ and conjugate linearity in $y$ give polynomiality of $\langle y,P(g)x\rangle$. [Expository] for the Stone–Weierstrass and SVD inputs; [Lean, read] for `polyExt_of` and the `Ugood_eq_top` tail.

**Lemma 2 (integrality, dominance, and comparison with $W_{\lambda-d\mathbf 1}$).** Under the hypotheses of the theorem, $\Lambda$ equals a weakly decreasing tuple $\lambda\in\mathbb Z^n$, and $x\mapsto\det(X)^{-c}F_x(X)$ defines a $\mathbb C$-linear isomorphism $S\xrightarrow{\sim}W_{\lambda-d\mathbf 1}$ intertwining $\sigma(u)|_S$ with $\mathrm{sqAct}(\lambda,u)$ for $u\in U(n)$, where $F_x(X)=\langle v_0,P(X^{\mathsf T})x\rangle$ and $c=\lambda_n+K$ for $n>0$ ($c=0$ for $n=0$).

*Proof.* Evaluating `IsWtOn` at $\theta=2\pi\mathbf e_a$ gives $T(\theta)=1$, so $v_0=\sigma(1)v_0=e^{2\pi i\Lambda_a}v_0$; since $v_0\ne 0$, $e^{2\pi i\Lambda_a}=1$ and $\Lambda_a=\lambda_a\in\mathbb Z$ (`lambda_integrality`, `TorusEigenvalueFormula.lean:10–42`). Using unitarity $\langle v_0,\sigma(T(\theta))x\rangle=\langle\sigma(T(-\theta))v_0,x\rangle$ and $\det(T(\theta))=e^{i\sum_a\theta_a}$, we obtain for all $\theta\in\mathbb R^n$ and $x\in S$ (`torus_eigenvalue_formula`, lines 44–65)
$$
\langle v_0,P(T(\theta))x\rangle=e^{i\sum_a(\lambda_a+K)\theta_a}\langle v_0,x\rangle.
$$
Next fix $1\le a<b\le n$ (`lower_triangular_invariance`, `LowerInv.lean:155–268`). For each $y\in S$, $c\mapsto\langle v_0,P(1+cE_{ba})y\rangle$ is a polynomial $\sum_{m\ge 0}\psi_m(y)c^m$ with $\psi_m\in S^\vee$. Since $(1+cE_{ba})T(\theta)=T(\theta)(1+ce^{i(\theta_a-\theta_b)}E_{ba})$, multiplicativity of $P$ and the torus formula above give
$$
\psi_m(P(T(\theta))y)=e^{i\sum_r(\lambda_r+K)\theta_r+im(\theta_a-\theta_b)}\psi_m(y).
$$
Let $y_m\in S$ represent $\psi_m$ by $\langle y_m,z\rangle=\psi_m(z)$. Replacing $\theta$ by $-\theta$, cancelling $\det(T(-\theta))^K\ne 0$, and moving $\sigma(T(-\theta))$ to $y_m$ shows that $y_m$ has torus weight $\Lambda+m(\mathbf e_a-\mathbf e_b)$. If $m\ge 1$ and $\psi_m\ne 0$, then $y_m\ne 0$ and `CDom` writes $-m(\mathbf e_a-\mathbf e_b)=\sum_{p<q}c_{pq}(\mathbf e_p-\mathbf e_q)$ with $c_{pq}\in\mathbb N$; pairing with $\sum_{r=1}^n r\mathbf e_r$ gives $m(b-a)>0$ on the left and $\sum_{p<q}c_{pq}(p-q)\le 0$ on the right (`lowerInv_not_cdom`), a contradiction. Hence $\psi_m=0$ for all $m\ge 1$, and evaluating at $c=0$ gives $\langle v_0,P(1+cE_{ba})x\rangle=\langle v_0,x\rangle$.

Now define $F:S\to\mathbb C[X_{at}]$ by $F_x(X)=\langle v_0,P(X^{\mathsf T})x\rangle$ (`Fl` in `ModelMap.lean:131–226`). Linearity in the second inner-product slot makes $F$ $\mathbb C$-linear, and $F_{v_0}(1)=\langle v_0,v_0\rangle=\|v_0\|^2\ne 0$. Because $(g^{\mathsf T}X)^{\mathsf T}=X^{\mathsf T}g$ and $P(X^{\mathsf T}g)=P(X^{\mathsf T})P(g)$, we get $F_{P(g)x}=\mathcal R(g)F_x$. Because $(X(1+cE_{lj}))^{\mathsf T}=(1+cE_{jl})X^{\mathsf T}$, lower invariance for $l<j$ gives $F_x(X(1+cE_{lj}))=F_x(X)$. Because $(XT(\theta))^{\mathsf T}=T(\theta)X^{\mathsf T}$, scaling column $t$ by $e^{i\theta_t}$ multiplies $F_x$ by $e^{i\sum_a(\lambda_a+K)\theta_a}$; comparing each nonzero monomial $m$ at $\theta=\tau\mathbf e_t$ gives $e^{i\tau\sum_a m_{at}}=e^{i\tau(\lambda_t+K)}$ for all $\tau\in\mathbb R$, which forces $\sum_a m_{at}=\lambda_t+K$ (apply $\tau=\pi/\delta$ if the difference $\delta$ were nonzero, `real_eq_of_exp`). Since $F_{v_0}\ne 0$ has at least one monomial in its support, $\mu_t=\lambda_t+K\ge 0$ for every $t$, and $F(S)\le W_\mu$.

We establish dominance of $\mu$ and irreducibility of $W_\nu$. Suppose $f\in W_\mu$ is fixed by $\mathcal R(g)$ for all upper unitriangular $g$ ($g^{\mathsf T}$ lower unitriangular). On the nonempty Zariski-open locus where all leading principal minors $\Delta_j(X)$ ($1\le j\le n$, $\Delta_0=1$) are nonzero, Gaussian elimination writes $X=LDU$ with $L$ lower unitriangular, $D=\operatorname{diag}(\Delta_1/\Delta_0,\ldots,\Delta_n/\Delta_{n-1})$, and $U$ upper unitriangular. Right column invariance kills $U$ and left lower-unitriangular invariance ($\mathcal R((L^{-1})^{\mathsf T})f=f$) kills $L$, leaving $f(X)=f(D)=f(1)\prod_{j=1}^n(\Delta_j(X)/\Delta_{j-1}(X))^{\mu_j}$. Thus $f\ne 0$ implies $f(1)\ne 0$. If $\mu_j<\mu_{j+1}$ for some $j<n$, specialize $X$ to the matrix $X(t)$ obtained from $I_n$ by replacing the $\{j,j+1\}$ principal block with $\begin{pmatrix}t&1\\1&0\end{pmatrix}$: then $\Delta_k(X(t))=1$ for $k<j$, $\Delta_j(X(t))=t$, and $\Delta_k(X(t))=-1$ for $k>j$, so $f(X(t))=f(1)(-1)^{\mu_{j+1}}t^{\mu_j-\mu_{j+1}}$ for all $t\ne 0$, impossible for a polynomial with $f(1)\ne 0$. Conversely, for weakly decreasing $\mu$, $\mathrm{hw}(\mu)=\prod_{j=1}^n\Delta_j^{\mu_j-\mu_{j+1}}$ ($\mu_{n+1}=0$) lies in $W_\mu$, is fixed by upper unitriangular $\mathcal R(g)$, and satisfies $\mathrm{hw}(\mu)(1)=1$. Now let $0\ne M\le W_\mu$ be stable under $\mathcal R(\mathrm{GL}_n(\mathbb C))$. Since $\sum_{a,t}\deg_{X_{at}}=\sum_t\mu_t$, $W_\mu$ is finite-dimensional (`bC_fd`, `ConstructionB.lean:58–64`); diagonal torus projections decompose $M$ into row-weight spaces, and a nonzero vector $f\in M$ maximizing $-\sum_{a=1}^n a\,\mathrm{rowDeg}_a(f)$ is killed by all raising derivations $\sum_t X_{at}\partial_{X_{bt}}$ ($a<b$), hence fixed by $\mathcal R(1+uE_{ab})=\exp(u\sum_t X_{at}\partial_{X_{bt}})$ and therefore by all upper unitriangular $g$. By the elimination uniqueness above, $\mu$ is weakly decreasing — forcing $W_\mu=0$ whenever $\mu$ has an inversion (`dualWeylNonDom`) and hence $\lambda$ weakly decreasing (`Assembly.lean:58–74`) — and $f\in\mathbb C\,\mathrm{hw}(\mu)$ (`hwLine`), so $\mathrm{hw}(\mu)\in M$. Equip $\mathbb C[X_{at}]$ with the Fock pairing $\langle p,q\rangle_{\mathrm{Fock}}=\sum_m \overline{p_m}q_m\prod_{a,t}m_{at}!$ (matching `fockF` up to conjugation convention in `ConstructionB.lean:65–196`): it is positive definite, and $\mathcal R(g)^\dagger=\mathcal R(g^\dagger)$ because on homogeneous degree $r$ it agrees with $r!$ times the standard inner product on $(\mathbb C^{n\times n})^{\otimes r}_{\mathrm{sym}}$ (equivalently, $(X_{at}\partial_{X_{bt}})^\dagger=X_{bt}\partial_{X_{at}}$ on monomials). If $M<W_\mu$, its Fock orthogonal complement $P=M^\perp\cap W_\mu$ is nonzero by dimension counting and still $\mathcal R(\mathrm{GL}_n(\mathbb C))$-stable (since $g\mapsto g^\dagger$ permutes $\mathrm{GL}_n(\mathbb C)$), so $P$ would also contain $\mathrm{hw}(\mu)$, forcing $\langle\mathrm{hw}(\mu),\mathrm{hw}(\mu)\rangle_{\mathrm{Fock}}=0$, a contradiction. Twisting by the scalar $\det(g)^d$ preserves stability, proving the irreducibility clause of `HwIrred` on $W_\nu$.

Set $c=\mu_n=\lambda_n+K\in\mathbb N$ if $n>0$ and $c=0$ if $n=0$, so $\mu=\nu+c\mathbf 1$ with $\nu=\lambda-d\mathbf 1$ and $\nu_n=0$ when $n>0$. Lemma 3 below proves unconditionally over $\mathbb C$ that $W_\mu$ is spanned by products of initial minors $\det(X_{I_p,q})_{1\le p,q\le s_k}$ ($s_k\le n$) whose sizes satisfy $|\{k:s_k>t-1\}|=\mu_t$ (`standardMonomialSpanDomain`). For $n>0$, evaluating at $t=n$ gives $|\{k:s_k=n\}|=\mu_n=c$; each size-$n$ minor is $\pm\det(X)$ (`detSplit_fullMinor`, `DetSplit.lean:10–30`), while the remaining factors have column counts $\mu_t-c=\nu_t$ and stay in $W_\nu$ (`detSplit_prodMem`, lines 31–54), proving $W_\mu=\det(X)^c W_\nu$ (`determinant_splitting_formula`, lines 55–119; immediate for $n=0$ since $\det(X)^0=1$). Multiplication `mulD` by $\det(X)^c$ is injective because $\det(I_n)=1\ne 0$ (`detPoly_ne_zero`). Following `modelIso_of_steps` (`Assembly.lean:98–177`), put $U=\{f\in W_\nu:\det(X)^c f\in F(S)\}$. Because $F_{v_0}\ne 0$ writes as $\det(X)^c f_0$ with $0\ne f_0\in U$, $U\ne 0$. For $g\in\mathrm{GL}_n(\mathbb C)$ and $\det(X)^c f=F_x$, $\mathcal R(g)(\det(X)^c)=\det(g^{\mathsf T})^c\det(X)^c=\det(g)^c\det(X)^c$ (`rowAct_detPoly`), so
$$
\det(X)^c\,\mathrm{sqAct}(\lambda,g)f=\det(g)^{d-c}\mathcal R(g)(\det(X)^c f)=F_{\det(g)^{d-c}P(g)x}\in F(S),
$$
making $U$ $\mathrm{GL}_n(\mathbb C)$-stable under `sqAct` and forcing $U=W_\nu$ by irreducibility. Meanwhile $\ker F\le S$ is $U(n)$-stable since $F_{\sigma(u)x}=\det(u)^{-K}\mathcal R(u)F_x$ and $\det(u)\ne 0$, while $v_0\notin\ker F$, so irreducibility of $S$ gives $\ker F=0$. Since $d-c=-K$ for $n>0$ and $\det(u)=1$ for $n=0$, $\det(X)^{-c}F_x$ intertwines $\sigma(u)|_S$ with $\mathrm{sqAct}(\lambda,u)$ and gives $\dim_{\mathbb C}S=\dim_{\mathbb C}F(S)=\dim_{\mathbb C}U=\dim_{\mathbb C}W_\nu$. [Expository] for the Gaussian elimination step; [Lean, read] for `TorusEigenvalueFormula`, `LowerInv`, `ModelMap`, `DetSplit`, `ConstructionB`, and `Assembly`.

**Lemma 3 (column-lexicographic leading exponents and the semistandard basis).** For every $\nu\in\mathbb N^n$, $W_\nu$ has a $\mathbb C$-basis of initial-minor products indexed by the finite set $\mathrm{ssIdx}(n,n,\nu)$ of $n\times n$ arrays $f=(f_{at})\in\mathbb N^{n\times n}$ satisfying $\sum_{a=1}^n f_{at}=\nu_t$ ($1\le t\le n$) and
$$
\sum_{b\le a} f_{b,t+1}\le\sum_{b<a} f_{b,t}\qquad(1\le t<n,\ 1\le a\le n).
$$

*Proof.* Order variables by column first and row second (`cmIdx`: $(a,t)\mapsto a+n(t-1)$), and give exponent arrays the lexicographic monomial order `colLex` (`StatementC.lean:9–26`): $m\prec m'$ when $m_{at}<m'_{at}$ at the first pair $(t,a)$ (smallest $t$, then smallest $a$) where they differ, and write $\deg_{\mathrm{colLex}}(h)$ for the `colLex`-largest exponent in $\operatorname{supp}(h)$.

First we prove `leadInterlaced` (`LeadInterlaced.lean:30–63`, `TwoColumn.lean:47–214`, `PeelDecomp.lean:9–48`, `PeelHomog.lean:97–109`, `PeelLead.lean:32–88`, `EvalDeg.lean:10–40`, `PeelDegBound.lean:30–182`). Fix $1\le l<j=l+1\le n$ and write $\Phi:\mathbb C[X]\to\mathbb C[X,u]$ (`colAddGen`) for $X_{bj}\mapsto X_{bj}+uX_{bl}$ ($X_{bt}\mapsto X_{bt}$ for $t\ne j$). For $0\ne h\in W_\nu$, $\Phi(h)=h$ has $u$-degree $0$. Grade $\mathbb C[X]$ by `pairW`, recording $(m_{bt})_{t\notin\{l,j\}}$ together with the paired row sums $\omega_b=m_{bl}+m_{bj}$. Because $\Phi$ is homogeneous for this grading, taking the `pairW`-component $g$ of $h$ at the weight of $m=\deg_{\mathrm{colLex}}(h)$ preserves $m\in\operatorname{supp}(g)$ inside $\operatorname{supp}(h)$, so $g\ne 0$, $\deg_{\mathrm{colLex}}(g)=m$ (`LeadComp`), and $\deg_u\Phi(g)\le\deg_u\Phi(h)=0$ (`CompDeg`). We show by downward induction on $n+1-a_0$ ($1\le a_0\le n+1$) that for any $s\in\mathbb N$ and any nonzero `pairW`-homogeneous $g$ with $\omega_b=0$ for $b<a_0$ and $\deg_u\Phi(g)\le s$, its leading exponent $m=\deg_{\mathrm{colLex}}(g)$ satisfies $\sum_{b\le a}m_{bj}\le s+\sum_{b<a}m_{bl}$ for all $1\le a\le n$ (`lctwo_main`). For $a_0=n+1$, $\omega_b=0$ forces $m_{bj}=0$ everywhere. For $1\le a_0\le n$, let $K\le\omega_{a_0}$ be the largest value of $d_{a_0,l}$ among $d\in\operatorname{supp}(g)$ and put $e=\omega_{a_0}-K\ge 0$. Grouping monomials by $d_{a_0,l}=k$ writes
$$
g=\sum_{k=0}^K X_{a_0,l}^k X_{a_0,j}^{e+(K-k)}w_k,
$$
where no $w_k$ (`peel`) involves $X_{a_0,l}$ or $X_{a_0,j}$, each $w_k$ is `pairW`-homogeneous with $\omega_{a_0}$ erased to $0$, and $w_K\ne 0$. Since all $d\in\operatorname{supp}(g)$ agree in columns $<l$ and vanish at $(b,l)$ for $b<a_0$, `colLex` first maximizes $d_{a_0,l}$ to $K$ (fixing $d_{a_0,j}=e$) and then maximizes inside $w_K$, giving $m=K\mathbf e_{a_0,l}+e\mathbf e_{a_0,j}+m'$ with $m'=\deg_{\mathrm{colLex}}(w_K)$ (`sliceLeading`). Applying $\Phi$ gives $\Phi(g)=Y^e Q$ where $Y=X_{a_0,j}+uX_{a_0,l}$ and $Q=\sum_{k=0}^K X_{a_0,l}^k Y^{K-k}\Phi(w_k)$, with neither $X_{a_0,l}$ nor $X_{a_0,j}$ appearing in $\Phi(w_k)$. Specializing $\psi:X_{a_0,l}\mapsto 1$, $X_{a_0,j}\mapsto -u$ (fixing $u$ and all other variables) sends $Y\mapsto 0$, kills every $k<K$ summand of $Q$, and fixes $\Phi(w_k)$, so $\psi(Q)=\Phi(w_K)$. Evaluating $\Phi(w_K)$ at $u=0$ recovers $w_K\ne 0$, so $\Phi(w_K)\ne 0$ and $Q\ne 0$. Because $\mathbb C[X,u]$ is a domain and $\deg_u Y=1$, $e+\deg_u Q=\deg_u(Y^e Q)=\deg_u\Phi(g)\le s$, whence $e\le s$ and $\deg_u Q\le s-e$. On each monomial of $Q$, $\psi$ turns each $X_{a_0,j}$ into $-u$, so $\deg_u\psi(Q)\le\deg_u Q+\deg_{X_{a_0,j}}Q\le(s-e)+K$ (`evalDegree`, `peelDegBound_of`). Applying the induction hypothesis to $w_K$ at $a_0+1$ with $s'=s-e+K$ gives $\sum_{b\le a}m'_{bj}\le(s-e+K)+\sum_{b<a}m'_{bl}$. Since $m'_{bl}=m'_{bj}=0$ for $b\le a_0$, the partial sum $\sum_{b\le a}m_{bj}$ is $0$ for $a<a_0$, $e\le s$ for $a=a_0$, and $e+\sum_{b\le a}m'_{bj}\le e+(s-e+K)+\sum_{b<a}m'_{bl}=s+\sum_{b<a}m_{bl}$ for $a>a_0$ (using $e\le s$). Taking $a_0=1$ and $s=0$ proves $m\in\mathrm{ssIdx}(n,n,\nu)$.

Second, every $f\in\mathrm{ssIdx}(n,n,\nu)$ satisfies $0\le f_{at}\le\nu_t$, so $\mathrm{ssIdx}(n,n,\nu)$ is finite (`SSIdxFinite.lean:7–21`). Setting $a=n$ in the interlacing inequality gives $\nu_{t+1}\le\nu_t$, so the positive columns form an initial prefix $1,\ldots,h$ ($h\le n$). When $f\ne 0$, let $c_t=\min\{a:f_{at}>0\}$ for $1\le t\le h$: for $t<h$, $1\le f_{c_{t+1},t+1}\le\sum_{b\le c_{t+1}}f_{b,t+1}\le\sum_{b<c_{t+1}}f_{bt}$ produces some $b<c_{t+1}$ with $f_{bt}>0$, forcing $c_t\le b<c_{t+1}$. Subtracting $1$ at $(c_t,t)$ ($1\le t\le h$) preserves interlacing (in each column $t\le h$, the partial sum up to $S$ drops by $1$ if $c_t\in S$ and by $0$ if $c_t\notin S$, in which case the sum over $b\le\max S$ was already $0$) and reduces $\sum_t\nu_t$, so induction decomposes $f$ into strictly increasing column-index tuples $I^{(k)}$ on prefixes $1,\ldots,s_k$ (`SSYTPeel.lean:58–256`, `SSYTExists.lean:10–63`). For each initial minor $\det(X_{I_p,q})_{1\le p,q\le s}$ with $I_1<\cdots<I_s$, any permutation $\sigma\ne\mathrm{id}$ has a smallest $q_0$ with $\sigma(q_0)\ne q_0$, hence $\sigma(q_0)>q_0$ and $I_{\sigma(q_0)}>I_{q_0}$; its monomial matches the diagonal monomial $\prod_{q=1}^s X_{I_q,q}$ before column $q_0$ and above row $I_{q_0}$ in column $q_0$, and has exponent $0<1$ at $(I_{q_0},q_0)$ (`MinorExpLt.lean:102–155`). Thus each initial minor lies in $W_{(1^s,0^{n-s})}$ with `colLex`-leading exponent $\sum_{q=1}^s\mathbf e_{I_q,q}$ and leading coefficient $1$ (`ColLexInitMinor.lean:22–53`), and multiplying over $k$ gives $b_f\in W_\nu$ with $\deg_{\mathrm{colLex}}(b_f)=f$ and leading coefficient $1$ (`ColumnLexBideterminant.lean:11–28`). Distinct leading exponents give linear independence; if $h\in W_\nu$ were outside $\operatorname{span}(b_f)$, well-founded induction on `colLex` (finite since $0\le d_{at}\le\nu_t$) subtracts $\operatorname{lc}(h)b_{\deg_{\mathrm{colLex}}(h)}$ to strictly lower the `colLex` degree until reaching $0$ (`SSBasis.lean:10–68`, `SMSAssembly.lean:11–50`, both valid over any integral domain, supplying `standardMonomialSpanDomain` as well). [Lean, read]

**Lemma 4 (interlacing box recursion, `AdmissibleModel/WeylDim.lean:15–264`).** For $\mu\in\mathbb Z^n$, define $d_{\mathrm{GT}}(0,\mu)=1$ and, for $\mu\in\mathbb Z^{n+1}$,
$$
d_{\mathrm{GT}}(n+1,\mu)=\sum_{\kappa\in B(\mu)} d_{\mathrm{GT}}(n,\kappa),\qquad
B(\mu)=\{\kappa\in\mathbb Z^n:\mu_{i+1}\le\kappa_i\le\mu_i\text{ for }1\le i\le n\}.
$$
Then $\dim_K(\mathrm{dualWeyl}\ K\ n\ n\ \nu)=|\mathrm{ssIdx}(n,n,\nu)|=d_{\mathrm{GT}}(n,\nu)$ for every field $K$ and $\nu\in\mathbb N^n$.

*Proof.* By induction on $t$, interlacing forces $f_{at}=0$ whenever $a<t$ (`intl_zero`, lines 49–65): for $t=1$ this is vacuous, and if $f_{bt}=0$ for all $b<t$, then for any $a<t+1$ every $b<a$ satisfies $b<t$, so $\sum_{b\le a}f_{b,t+1}\le\sum_{b<a}f_{bt}=0$. For $\mu\in\mathbb Z_{\ge 0}^{n+1}$ and $f\in\mathrm{SSZ}(n+1,\mu)$ (the integer-sum curried form of `ssIdx` via `ssEquiv`), let $\rho(f)_{at}=f_{at}$ ($1\le a,t\le n$) delete row $n+1$ and column $n+1$. Its column sums $\kappa_t=\sum_{a=1}^n f_{at}$ satisfy $\kappa_t=\mu_t-f_{n+1,t}\le\mu_t$ and, by the row-$(n+1)$ interlacing inequality $\mu_{t+1}=\sum_{b\le n+1}f_{b,t+1}\le\sum_{b\le n}f_{bt}=\kappa_t$, lie in $B(\mu)$ (`restr_mem`, lines 77–95). Conversely, given $\kappa\in B(\mu)$ and $g\in\mathrm{SSZ}(n,\kappa)$, define $\operatorname{ext}(\mu,g)$ by keeping $g$ on $\{1,\ldots,n\}^2$, setting $f_{a,n+1}=0$ for $a\le n$ (matching `intl_zero` at column $n+1$), $f_{n+1,t}=\mu_t-\kappa_t\ge 0$ for $t\le n$, and $f_{n+1,n+1}=\mu_{n+1}\ge 0$. Because column $n+1$ vanishes on rows $\le n$ and $\mu$ determines the last row from the remaining column sums, $\rho$ and $\operatorname{ext}$ are mutually inverse bijections between $\mathrm{SSZ}(n+1,\mu)$ and $\bigsqcup_{\kappa\in B(\mu)}\mathrm{SSZ}(n,\kappa)$ (`rho_inj`, `rho_surj`, `fibEquiv`, lines 98–216). Induction from the unique empty array at $n=0$ gives $|\mathrm{SSZ}(n,\mu)|=d_{\mathrm{GT}}(n,\mu)$ whenever $\mu\ge 0$ (`card_SSZ`, lines 217–238), and Lemma 3 over $K$ gives $\dim_K(\mathrm{dualWeyl}\ K\ n\ n\ \nu)=d_{\mathrm{GT}}(n,\nu)$ (`finrank_dualWeyl`, lines 259–264). [Lean, read]

**Lemma 5 (falling-factorial Vandermonde evaluation and shift cancellation).** For every $n\in\mathbb N$ and every weakly decreasing $\mu\in\mathbb Z^n$, $d_{\mathrm{GT}}(n,\mu)=D_n(\mu)$.

*Proof.* Switch to zero-based indices $0\le i,j<n$ to match `Branch.lean:12–197` and `WeylGT.lean:105–120`. Set $z_i=i-\mu_i\in\mathbb R$, so $\prod_{0\le i<j<n}(\mu_i-\mu_j+j-i)=\prod_{0\le i<j<n}(z_j-z_i)=\det(z_i^j)_{0\le i,j<n}$. Replace $z^j$ in column $j$ by the monic degree-$j$ falling factorial $p_j(z)=\prod_{k=0}^{j-1}(z-k)$ ($p_0(z)=1$); unit upper-triangular column operations leave the determinant unchanged (`det_vandermonde_eq_ff`). Factoring $p_j(w)$ gives
$$
p_{j+1}(w+1)-p_{j+1}(w)=(w+1)p_j(w)-p_j(w)(w-j)=(j+1)p_j(w),
$$
so for integers $a\le b$ and $c\in\mathbb R$, telescoping $x\in[a,b]\cap\mathbb Z$ yields $(j+1)\sum_{x=a}^b p_j(c-x)=p_{j+1}(c+1-a)-p_{j+1}(c-b)$ (`ff_diff`, `sum_ff`, lines 16–56). Given weakly decreasing $\mu\in\mathbb Z^{n+1}$, $\mu_{i+1}\le\mu_i$ holds for each $0\le i<n$. Summing $\det(p_j(i-\kappa_i))_{0\le i,j<n}$ over $\kappa\in\prod_{i=0}^{n-1}[\mu_{i+1},\mu_i]$ by row multilinearity of the determinant (`sum_det`), then multiplying column $j$ by $j+1$ (total multiplier $\prod_{j=0}^{n-1}(j+1)=n!$), gives the $n\times n$ determinant with $(i,j)$-entry
$$
p_{j+1}(i+1-\mu_{i+1})-p_{j+1}(i-\mu_i)=p_{j+1}(z_{i+1})-p_{j+1}(z_i).
$$
In the $(n+1)\times(n+1)$ matrix $M_{r,s}=p_s(z_r)$ ($0\le r,s\le n$), column $0$ is all ones, so subtracting row $r$ from row $r+1$ from bottom to top and cofactor-expanding along column $0$ identifies $\det M$ with that $n\times n$ difference determinant (`det_diff`, `core`, lines 75–145). Dividing by $\prod_{0\le i<j\le n}(j-i)=n!\prod_{0\le i<j<n}(j-i)$ (`W_id_succ`, `denom_range`) proves $D_{n+1}(\mu)=\sum_{\kappa\in B(\mu)}D_n(\kappa)$ (`branchingDimensionFormula`). Because $\kappa\in B(\mu)$ implies $\kappa_i\ge\mu_{i+1}\ge\kappa_{i+1}$, every summand remains weakly decreasing, and induction from $D_0=1=d_{\mathrm{GT}}(0,\cdot)$ gives $d_{\mathrm{GT}}(n,\mu)=D_n(\mu)$ (`weyl_dim_eq_gelfand_tsetlin`, `weylQ`, `weyl_dualWeyl`, specialized to $K=\mathbb C$ in `nablaDim_closed`).

To close the single-block theorem (`weylForU_of` in `NatWCastReal.lean:60–96`), combine `modelIso_closed` ($\dim_{\mathbb C}S=\dim_{\mathbb C}W_\nu$ with $\nu=\lambda-d\mathbf 1$) and `nablaDim_closed` ($\dim_{\mathbb C}W_\nu=D_n(\nu)$ in $\mathbb Q$, cast to $\mathbb R$). For every pair $a<b$ in $\mathrm{Fin}\ n$ (vacuous when $n=0$), $\nu_a-\nu_b=(\lambda_a-d)-(\lambda_b-d)=\Lambda_a-\Lambda_b$ cancels $d$, and `denom_fin` rewrites $\prod_{a<b}(b-a)$ as $\prod_{k=0}^{n-1}k!$. Conversely, every weakly decreasing $\Lambda\in\mathbb Z^n$ is non-vacuously realized by $S=W_{\Lambda-d\mathbf 1}$ with the Fock inner product, unitary action $\mathrm{sqAct}(\Lambda)|_{U(n)}$, and nonzero highest vector $\mathrm{hw}(\Lambda-d\mathbf 1)$: each size-$s$ initial minor on rows $i_1<\cdots<i_s$ ($i_q\ge q$) has weight $\sum_{q=1}^s\mathbf e_{i_q}=\sum_{q=1}^s\mathbf e_q-\sum_{q=1}^s(\mathbf e_q-\mathbf e_{i_q})$, so every monomial in the standard-monomial span satisfies `CDom` before and after the uniform shift $d\mathbf 1$ (agreeing with the separate integral dominant-type supply `kType_exists_of_dom` in `HighestWeights/Exists.lean:15–43`). [Lean, read] for `Branch`, `WeylGT`, `WeylDim`, `NatWCastReal`, and `ExplicitFormulaCounts/WeylForU`; [Expository] for the direct Fock realization check.

**Two-block assembly and the Pieri positive-factor handoff.** Now let $\epsilon:\mathrm{Fin}\ N\to\mathrm{Bool}$ be any signature, with $p=\mathrm{nPl}(\epsilon)$ true indices and $q=\mathrm{nMi}(\epsilon)$ false indices enumerated in increasing order by $e_+:\mathrm{Fin}\ p\to\mathrm{Fin}\ N$ and $e_-:\mathrm{Fin}\ q\to\mathrm{Fin}\ N$ (`SMinus.lean:11–44`). Block diagonal embeddings $i_+:M_p(\mathbb C)\to M_N(\mathbb C)$ and $i_-:M_q(\mathbb C)\to M_N(\mathbb C)$ place the other block at the identity, so $s_+(\sigma)=\sigma\circ i_+$ and $s_-(\sigma)=\sigma\circ i_-$ define commuting unitary actions of $U(p)$ and $U(q)$ whose products exhaust $\mathrm{Kset}(\epsilon)=\{g\in U(N):gJ_\epsilon=J_\epsilon g\}$ (`Blocks`, used in `WeylForKOfSteps.lean:9–32`), even when $\epsilon$ interleaves signs.

Given `IsURepOn (Kset ε) σ` and `IsKTypeOf ε σ Λ S` with highest-weight witness $v\in S\setminus\{0\}$, restrict $v$ to $U(p)$ of weight $\Lambda_+=\Lambda\circ e_+$ (`isWtOn_sPl`) and pick a $U(p)$-stable subspace $X\le S$ of minimal `finrank` containing a nonzero vector $x$ of weight $\Lambda_+$ (`minimal_irreducible_exists`, `Weights.lean:186–246`). If $X'\le X$ is $U(p)$-stable, $X'^\perp\cap X$ is also $U(p)$-stable and decomposing $x=y+z$ orthogonally forces $(T_+(\theta)y-e^{i\Lambda_+\cdot\theta}y)+(T_+(\theta)z-e^{i\Lambda_+\cdot\theta}z)=0$ with orthogonal summands, so both $y$ and $z$ inherit weight $\Lambda_+$; minimality of $\dim_{\mathbb C}X$ forces $X'=0$ (if $y=0$) or $X'=X$ (if $y\ne 0$), proving $U(p)$-irreducibility of $X$. For `CDom` on $X$ (`typePl_of`, `TypePlOf.lean:51–105`), let $0\ne w\in X$ have $U(p)$-torus weight $\mu$. The full $U(p)$-weight space $W_\mu=\{u\in S:\forall\theta,\,s_+(\sigma)(T_+(\theta))u=e^{i\mu\cdot\theta}u\}$ is nonzero ($w\in W_\mu$) and stable under the full $N$-torus because diagonal matrices commute; finite-dimensional simultaneous diagonalization (`TorusWt`) produces $0\ne u\in W_\mu$ of full weight $\nu\in\mathbb R^N$. Restricting $\nu$ to the plus block matches $\mu$ by character uniqueness (`WtUniq`), and projecting $\Lambda-\nu=\sum_{a<b,\,\epsilon_a=\epsilon_b}c_{ab}(\mathbf e_a-\mathbf e_b)$ onto `ePl` drops the minus-block roots and preserves strict index order (`dominant_restriction_holds`), yielding `IsKTypeOf (allPos p) (sPl ε σ) Λ_+ X` and analogously `Y ≤ S` for $\Lambda_-=\Lambda\circ e_-$ (`typeMi_of`).

To prove $\dim_{\mathbb C}S=\dim_{\mathbb C}X\cdot\dim_{\mathbb C}Y$ (`DimStep.lean:35–46`, `DimStepA.lean:46–242`, `DimStepB.lean:13–237`), fix $x_0\in X\setminus\{0\}$ and $y_0\in Y\setminus\{0\}$, write $\rho,\rho'$ for the $U(p),U(q)$ actions, and define the commutant slice $\mathrm{slice}(\rho,x_0)=\{c(x_0):c\in\operatorname{End}_{\mathbb C}(H),\,\forall g,\,c\circ\rho(g)=\rho(g)\circ c\}$. First (`exists_hit`), for any nonzero $\rho$-stable $W\le S$ with orthogonal projection $P_W$ (which commutes with $\rho$ by unitarity), some $j\in U(q)$ has $(P_W\circ\rho'(j))(x_0)\ne 0$: otherwise irreducibility of $X$ kills $P_W\circ\rho'(j)$ on all of $X$ (`kill`), putting the joint span $\sum_j\rho'(j)(X)=S$ inside $\ker P_W$ and contradicting $W\ne 0$. Second (`schur2`), if $c,c'$ commute with $\rho$, send $x_0$ into a $\rho$-irreducible $W'$, and $c(x_0)\ne 0$, then $c|_X:X\to W'$ is a linear isomorphism, and an eigenvalue $\mu\in\mathbb C$ of $(c|_X)^{-1}\circ(c'|_X)$ kills $c'-\mu c$ on a nonzero eigenvector and hence on $X$, giving $c'(x_0)=\mu c(x_0)$. Third (`count`), strong induction on $\dim_{\mathbb C}W$ for $\rho$-stable $W\le S$ picks $c$ with $0\ne c(x_0)\in W$, splits $W=c(X)\oplus(c(X)^\perp\cap W)$, and uses `schur2` on $P_{c(X)}\circ d$ to split $\mathrm{slice}(\rho,x_0)\cap W=\mathbb C c(x_0)\oplus(\mathrm{slice}(\rho,x_0)\cap c(X)^\perp\cap W)$, yielding $\dim_{\mathbb C}W=\dim_{\mathbb C}X\cdot\dim_{\mathbb C}(\mathrm{slice}(\rho,x_0)\cap W)$. At $W=S$, put $U=\mathrm{slice}(\rho,x_0)\cap S$: $x_0=\mathrm{id}(x_0)\in U$ so $U\ne 0$, $\rho'$ preserves $U$ by postcomposition, and $U$ is $\rho'$-irreducible — if $0<U'<U$ were $\rho'$-stable, pick $0\ne w\in U'^\perp\cap U$; for any $z=d'(x_0)\in U'$ ($z\ne 0$), `schur2` gives $P_{d'(X)}w=\mu d'(x_0)\perp w$, forcing $\mu=0$, hence $w\perp d'(\rho(g)x_0)=\rho(g)z$ and $w\perp\sum_g\rho(g)(U')=S$, impossible. Swapping the roles of $(\rho,X)$ and $(\rho',Y)$ in `exists_hit` and `schur2` against the $\rho'$-irreducible $U$ gives $\dim_{\mathbb C}Y=\dim_{\mathbb C}U$, so $\dim_{\mathbb C}S=\dim_{\mathbb C}X\cdot\dim_{\mathbb C}Y$ (including $p=0$ or $q=0$, where $\dim_{\mathbb C}X=1$ or $\dim_{\mathbb C}Y=1$).

Applying `weylForU_closed` to $X$ and $Y$ (`weylForK_of_steps`, `WeylForKOfSteps.lean:42–47`) and rewriting $\rho_C(\epsilon)(e_\pm(i))=(|\text{block}|-1-2i)/2$ (`rhoC_ePl`, `rhoC_eMi`, `weyl_formula_compact` in `Formula.lean:128–195`) yields `weylForK_closed` (`ExplicitFormulaCounts/WeylForK.lean:4`):
$$
\dim_{\mathbb C}S=\frac{\prod_{a<b,\,\epsilon_a=\epsilon_b}((\Lambda_a+\rho_{C,a})-(\Lambda_b+\rho_{C,b}))}{\prod_{i=0}^{p-1}i!\,\prod_{j=0}^{q-1}j!}.
$$
In `HighestWeights/Finrank.lean:16–51`, `hwfin_weyl` applies `weylForK_closed` (via `WeylBridge.lean:20–21`) to `T.V` (`S = ⊤`) for any complete record `T : KType ε Λ`; `hwfin_denom` evaluates `hwfin_weyl` on the one-dimensional `trivialKType ε` ($\Lambda=0$) to equate $\prod_{i=0}^{p-1}i!\,\prod_{j=0}^{q-1}j!$ with $\prod_{a<b,\,\epsilon_a=\epsilon_b}(\rho_{C,a}-\rho_{C,b})$; and `kType_finrank` divides termwise to obtain $\dim_{\mathbb C}T.V=\mathrm{weylK}(\epsilon,\Lambda)$. Finally, `CountNotTwoOfFinrankLeOne.lean:68–103` defines `count_weylK_eq` as `kType_finrank T` and deduces `0 < weylK ε μ` (`count_weylK_pos`) from `T.w ≠ 0` (`Nontrivial T.V`), feeding both into lines 93–103 of `pieriCount_of_st` (and line 149 on the input type `T` in the ambient tensor dimension count) to supply the exact positive Weyl summands inherited in [§9.4.21](#9421-compact-pieri-branching-and-the-tensor-step). [Lean, read]

**Non-dominant boundaries and deleted-premise counterexamples.** Although $D_n(\Lambda)$ is defined as a polynomial with rational coefficients for all $\Lambda\in\mathbb R^n$, its dimension interpretation holds only on actual compact types:
1. *Non-dominant formal values (zero, negative, and positive).* On $U(2)$, $\Lambda=(0,1)$ has $D_2(0,1)=0$ and $\Lambda=(0,2)$ has $D_2(0,2)=-1$; on $U(3)$, the forbidden Pieri wall shift $\Lambda=(2,3,-1)$ has $D_3(2,3,-1)=0$ because $(\Lambda_1-\Lambda_2)+1=0$. Even formal positivity fails to detect dominance in rank $\ge 3$: at $\Lambda=(1,0,4)$ on $U(3)$, two negative numerator factors cancel signs to give $D_3(1,0,4)=\frac{2\cdot(-1)\cdot(-3)}{1\cdot 2\cdot 1}=3>0$. Yet for every integral tuple with $\Lambda_a<\Lambda_b$ ($a<b$), no `IsKTypeOf` exists, $W_{\Lambda-\min(\Lambda)\mathbf 1}=0$ by the $LDU$ pole argument, and $\mathrm{ssIdx}$ is strictly empty ($\nu_{t+1}\le\nu_t$ fails). (Vanishing at the specific one-step Pieri shifts is inherited from §9.4.21.)
2. *Deleting the positive-root cone premise (`CDom`) in `IsKTypeOf`.* Take the irreducible standard action of $U(2)$ on $S=\mathbb C^2$, which satisfies `IsURepOn`, finite dimension, stability, and irreducibility, but designate the lower weight vector $v_0=e_2\ne 0$ of torus weight $\Lambda=(0,1)$. Every clause of `IsKTypeOf` holds except `CDom` at $e_1$ (since $(0,1)-(1,0)=-(\mathbf e_1-\mathbf e_2)\notin\mathbb N(\mathbf e_1-\mathbf e_2)$): the model map sends $e_1\mapsto\langle e_2,X^{\mathsf T}e_1\rangle=X_{12}$, which fails column-addition invariance $X_{12}\mapsto X_{12}+cX_{11}$, and $\dim_{\mathbb C}S=2\ne 0=D_2(0,1)$.
3. *Deleting irreducibility of $S$ while keeping `CDom`.* Take $S=\operatorname{Sym}^2\mathbb C^2\oplus\det\mathbb C^2$ under $U(2)$ with designated vector $v_0=(e_1^2,0)\ne 0$ of dominant weight $\Lambda=(2,0)$. Every nonzero torus weight vector of $S$ has weight $(2,0)$, $(1,1)$, or $(0,2)$, whose differences from $(2,0)$ are $0$, $\mathbf e_1-\mathbf e_2$, and $2(\mathbf e_1-\mathbf e_2)$, so `FiniteDimensional`, `IsKStableOn`, $v_0\ne 0$ of weight $\Lambda$, and `CDom` on all of $S$ hold! Only irreducibility fails: the coefficient map $F_x(X)=\langle v_0,P(X^{\mathsf T})x\rangle$ kills the entire second summand $0\oplus\det\mathbb C^2$, and $\dim_{\mathbb C}S=3+1=4\ne 3=D_2(2,0)$. [Expository]

**Classical comparison and reading scope.** In Anthony W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Theorem 5.84, printed p. 323, $\dim V=\prod_{\alpha\in\Delta^+}\langle\lambda+\delta,\alpha\rangle/\langle\delta,\alpha\rangle$ is proved for an irreducible finite-dimensional representation of a complex semisimple Lie algebra $\mathfrak g$ with highest weight $\lambda$ by applying a directional derivative version of l'Hôpital's rule at $0$ to the Weyl character formula. Restricting a compact $K=U(p)\times U(q)$ representation to $\mathfrak{sl}_p(\mathbb C)\oplus\mathfrak{sl}_q(\mathbb C)$ preserves irreducibility because the block centers act by scalars and compact derived stability matches group stability by the inherited compact logarithm and differentiation on `KType.op_curve`; subtracting each block's trace mean leaves all same-block differences $\Lambda_a-\Lambda_b$ unchanged, and empty or size-$1$ blocks contribute empty products equal to $1$. Unlike Knapp's character limit, A2 proves the formula directly from matrix-coefficient embedding into $W_\nu$, `colLex` tableau bases, and falling-factorial Vandermonde summation. [Paper] [Knapp, author PDF](https://www.math.stonybrook.edu/~aknapp/download/Beyond2-clickable.pdf)

| Archive A2 source (relative to `lean/src/`) | Production read |
|---|---|
| `Formalism/PeriodIntegrals/WeylForU.lean:10–37`, `WeylForK.lean:9–21`, `UpqRep.lean:224–302`, `LocalRingCardinality/DataCoeff.lean:13–64` | Quantified interfaces `WeylForU`, `NablaDim`, `ModelIso`, `PolyCoef`, `WeylForK`, `IsKTypeOf`, `DomWeight`, `nablaSq`, `sqAct`. |
| `Formalism/PeriodIntegrals/ExplicitFormulaCounts/WeylForU.lean:7–11`, `WeylForK.lean:4`, `OrbitalBoundsConclusion/ModelIso.lean:8–13`, `WeylForU.lean:5`, `WeylForK.lean:7–10` | Closed single-block and two-block producers and their assembly calls. |
| `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/IsPolyMon.lean:14–76`, `PolyExt.lean:10–112`, `TorusEigenvalueFormula.lean:10–65`, `LowerInv.lean:10–268`, `ModelMap.lean:12–226`, `DetSplit.lean:10–119`, `Assembly.lean:10–177`, `HighestWeightIrreducible/Assembly.lean:10–32`, `ConstructionB.lean:10–196` | Monoid extension, torus integrality, lower-unipotent invariance, transposed model map, minor-counting determinant division, Fock complement irreducibility, and `ModelIso` assembly. |
| `Formalism/GradedWeylDivisibility/StatementA.lean:10–236`, `StatementC.lean:9–159`, `StatementD.lean:9–34`, `FinalC.lean:22–41`, `FinalD.lean:17–19`, `FockSpaceTableaux/LeadInterlaced.lean:10–63`, `CompDeg.lean:10–14`, `LeadComp.lean:11–33`, `TwoColumn.lean:9–214`, `PeelDecomp.lean:9–48`, `PeelHomog.lean:9–109`, `PeelLead.lean:10–88`, `EvalDeg.lean:10–40`, `PeelDegBound.lean:10–182`, `MinorExpLt.lean:11–155`, `ColLexInitMinor.lean:11–53`, `ColumnLexBideterminant.lean:11–28`, `ColSums.lean:9–22`, `SSYTPeel.lean:10–256`, `SSYTExists.lean:10–63`, `SMSAssembly.lean:11–50`, `SSBasis.lean:10–68`, `SSIdxFinite.lean:7–21` | Complete `colLex` leading-exponent interlacing proof, row peeling, initial-minor basis `sSBasis`, and `standardMonomialSpanDomain`. |
| `Formalism/PeriodIntegrals/AdmissibleModel/WeylDim.lean:15–312`, `ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/Branch.lean:12–197`, `WeylGT.lean:15–120`, `PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaUnitary/NatWCastReal.lean:10–96` | Deletion/extension bijection to `dGT`, falling-factorial Vandermonde recurrence, `weyl_dualWeyl`, shift cancellation, and factorial denominator. |
| `Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Assemble.lean:8–12`, `WeylForKOfSteps.lean:9–48`, `SMinus.lean:11–44`, `TypePlOf.lean:10–160`, `Weights.lean:186–246`, `DimStep.lean:9–46`, `DimStepA.lean:13–242`, `DimStepB.lean:13–237`, `Formula.lean:128–196`, `ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/WeylBridge.lean:10–22`, `Finrank.lean:14–51`, `PieriRules/CountNotTwoOfFinrankLeOne.lean:68–103` | Minimal irreducible block subspaces, full-torus weight lifting, commutant-slice multiplicity induction, $\rho_C$ product conversion, and exact Pieri positive-factor handoff. |

Archive A2 joined SHA-256 **9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc**; Mathlib revision **0df444a360eaa60ab8c11dca51a86af692955474** (`lean/lake-manifest.json:6–16`). Reading is local to the listed files; the archive's general frame-density and divided-power leaf developments (`UnitaryDensity/`, `CompactGroupIntegrability/` helpers, `HighestWeightIrreducible/ConstructionA.lean`, `DualWeylNonDom.lean`, and `WeylFormulaCompact/Blocks.lean`, `Weights.lean:1–185`) remain named at their interfaces without kernel replay.

The same-source preliminary review upheld the model comparison, the semistandard and counting arguments, and the two-block Pieri handoff. The model endpoint `PI.ModelIso` exports a dominant model label and an equality of dimensions. The pointed unitary comparison of two compact records is the separate `kType_unique` input.

[Source and review ledger](../sources/SOURCES.md#chapter-9-compact-pieri-weyl-model-and-physical-fock-degree) · [Contributions](../CONTRIBUTIONS.md#chapter-9-compact-pieri-weyl-model-and-physical-fock-degree)

---

### 9.4.23 The PRV extremal component and the highest-weight graph

**Motivation.** A highest vector in the first factor and a lowest vector in the second already have the desired sum of weights. Raising their tensor generally gives a nonzero contribution from the second factor. The archive constructs the correction terms by pairing two highest vectors in a different space. Their cyclic submodule becomes the graph of an intertwiner. Evaluating it on vectors supported in single coordinates produces the required tensor in the original space. [Expository]

**Two worked tensors.** We use one-based root indices, take all signs equal, and use the polynomial module itself as the ambient $M=V$ in both examples. On degree-$d$ polynomials the operators are $F_{ab}=x_a\partial_{x_b}$. The monomials are orthogonal with $\|x^\alpha\|^2=\alpha!/d!$, from the symmetrization of the orthonormal tensor basis. For $a\ne b$ and $\alpha_b>0$, put $\beta=\alpha+e_a-e_b$. The equality $\alpha_b\beta!=(\alpha_a+1)\alpha!$ proves $F_{ab}^\dagger=F_{ba}$ on monomial pairs. Both sides vanish when there is no matching transfer. The diagonals have real eigenvalues. The product rule gives the matrix-unit bracket. Each weight has a single monomial, and polynomial projections in the commuting diagonal operators recover each monomial component of a vector in a stable subspace. Transfers connect all degree-$d$ monomials with nonzero coefficients, so the symmetric power is irreducible.

1. **Two symmetric squares for $U(2)$.** Take the first square on the $x$ variables, with $w=x_1^2$. In the second square use the orthonormal basis $q_0=y_1^2$, $q_1=\sqrt2\,y_1y_2$, $q_2=y_2^2$. Raising sends $q_2$ to $\sqrt2\,q_1$, $q_1$ to $\sqrt2\,q_0$, and $q_0$ to zero. Lowering acts by transpose. The lowest column $f=(0,0,1)$ gives $\nu=(0,2)$, and the sum with $\Lambda=(2,0)$ is $(2,2)$, on the dominance wall. Its weight coordinates have the form $(A x_2^2,Bx_1x_2,Cx_1^2)$. Raising gives $(2A+\sqrt2 B)x_1x_2$ in row $0$, $(B+\sqrt2 C)x_1^2$ in row $1$, and zero in row $2$. Taking $C=1$ gives $A=1$ and $B=-\sqrt2$. The tensor is
   $$
   x_2^2y_1^2-2x_1x_2y_1y_2+x_1^2y_2^2=(x_1y_2-x_2y_1)^2.
   $$
   The auxiliary highest module can be taken to be the determinant square, with vector $p=1$. In its tensor with the dual, use the single-coordinate vectors $s_0,s_1,s_2$ with value $p$. The lowering operator sends $s_2$ to $-\sqrt2\,s_1$ and $s_1$ to $-\sqrt2\,s_0$. Starting from $(s_2,w)$, the first two lowered pairs are $(-\sqrt2\,s_1,2x_1x_2)$ and $(2s_0,2x_2^2)$. They and the starting pair span the graph over the entire auxiliary space. The three graph values recover the coordinates just computed.

2. **A symmetric square and an exterior square for $U(3)$.** Take $V=\operatorname{Sym}^2\mathbb C^3$ and $w=x_1^2$. In the second factor use the orthonormal basis $q_{12},q_{13},q_{23}$, where $q_{ij}=e_i\wedge e_j$. Acting on the two slots gives exactly one nonzero basis image for each raising operator: $G_{12}q_{23}=q_{13}$, $G_{23}q_{13}=q_{12}$, $G_{13}q_{23}=-q_{12}$. Lowering is by transpose, and $G_{aa}$ counts occurrences of $a$ in each pair. This action inherits the bracket from the two commuting slot actions on the tensor square. The lowering operators kill $q_{23}$ because $e_1$ is absent and replacing $e_2$ by $e_3$ repeats an exterior factor. The lowest column for $q_{23}$ gives $\nu=(0,1,1)$ and $\mu=(2,1,1)$ lies on the second wall. The full weight equations give coordinates $(A x_1x_3,Bx_1x_2,Cx_1^2)$. Raising by $12$ gives $(B+C)x_1^2$ in the $q_{13}$ row. Raising by $23$ gives $(A+B)x_1x_2$ in the $q_{12}$ row, and raising by $13$ gives $(A-C)x_1^2$ in that row. All other rows in these three tests vanish. Taking $C=1$ gives
   $$
   x_1x_3\otimes q_{12}-x_1x_2\otimes q_{13}+x_1^2\otimes q_{23}.
   $$
   In this case the auxiliary module can be $T=\det\otimes\mathbb C^3$, with $p=\det\otimes e_1$ in determinant-line notation. The volume pairing identifies $q_{12}^*,q_{13}^*,q_{23}^*$ with $e_3,-e_2,e_1$ tensored with the inverse determinant line. The determinants cancel in $P$, identifying it with $\mathbb C^3\otimes\mathbb C^3$. The generator $x_0$ becomes $e_1\otimes e_1$. Its cyclic span is the symmetric square by the monomial irreducibility argument above, and the alternating square is its orthogonal complement. Multiplication $e_a\otimes e_b\mapsto x_ax_b$ intertwines by the product rule. It sends $x_0$ to $w$ and kills the alternating complement, so its graph is exactly the extension in Lemma 1. Evaluating it on $s_{12},s_{13},s_{23}$ gives $x_1x_3,-x_1x_2,x_1^2$.

   Its lowest-column contraction is $w$, the graph normalization proved below. Adding $\tfrac12 I$ to every diagonal $F_{aa}$ gives another legal algebraic instance with the same coordinates and weight $(5/2,3/2,3/2)$. Here the auxiliary compact model has integral label $(2,1,1)$ and the proof shifts its derived action by $1/2$.

**Definitions.** Fix $n\ge0$ and a signature $\epsilon:\operatorname{Fin}n\to\{\mathrm{true},\mathrm{false}\}$. Call $(a,b)$ compact if $\epsilon_a=\epsilon_b$. Within these pairs, $a<b$ is raising and $b<a$ lowering. A ring-valued family $B$ satisfies `KRel` when for all $a,b,c,d$ with both pairs compact,
$$
[B_{ab},B_{cd}]=\delta_{bc}B_{ad}-\delta_{da}B_{cb}.
$$
A nonzero Kronecker term also has a compact pair. For an inner-product space with first slot conjugate linear, `KUnit` requires $\langle B_{ab}u,v\rangle=\langle u,B_{ba}v\rangle$ for every compact pair and every $u,v$. Weight $\lambda\in\mathbb R^n$ means $B_{aa}v=\lambda_a v$ for every $a$. The predicates `KHighest` and `IsKHWVec` add $B_{ab}v=0$ for every raising pair. Nonzero is a separate condition. Compact stability of a subspace means stability under every compact operator. Write $\operatorname{kSpan}(B,v)$ for the smallest compact-stable subspace containing $v$. We write the weight equations with real scalars acting through the inclusion $\mathbb R\subset\mathbb C$.

For a complex vector space $M$, `IsKIrrHW` at $(\epsilon,F,\Lambda,V)$ requires that $V\le M$ be finite-dimensional and compact-stable, that every compact-stable subspace $V'\le V$ be $0$ or $V$, and that some $w\in V$ be nonzero and satisfy `IsKHWVec` at $\Lambda$. The ambient $M$ is an algebraic complex vector space. Write DS for `ReciprocityTheory/ReductiveGroups/DiscreteSeries` and HW for `DS/HighestWeights`. See `Formalism/RealPlaceAnalysis/StatementKT.lean:10–34`, `StatementA.lean:26–32` and `DS/IsInfUnitary.lean:28–29,72–79`.

**Lemma 1 (the highest-weight graph, `highest_weight_graph_submodule`).** Let $P$ be a finite-dimensional complex inner-product space and $M$ a complex vector space. Suppose $E$ on $P$ satisfies `KRel` and `KUnit`, and $F$ on $M$ satisfies `KRel`. Assume `IsKIrrHW` at $(\epsilon,F,\Lambda,V)$. Take any nonzero highest vectors $x_0\in P$ and $w\in V$ for $E$ and $F$ of the same full weight $\Lambda$. Under $Q_{ab}(y,v)=(E_{ab}y,F_{ab}v)$ on $P\times M$, there is a compact-stable subspace $\Gamma\subseteq P\times V$ containing $(x_0,w)$, for which the first projection is onto $P$ and has zero kernel. Equivalently, $\Gamma$ is the graph of a complex-linear $L:P\to V$ with $Lx_0=w$ and $LE_{ab}=F_{ab}L$ for every compact pair.

*Proof.* The product family has `KRel` componentwise. Let $Z=\operatorname{kSpan}(E,x_0)$ and $\Gamma_0=\operatorname{kSpan}(Q,(x_0,w))$. The stable product $Z\times V$ contains the generator and hence $\Gamma_0$. The first projection image lies in $Z$, contains $x_0$ and is stable because the projection intertwines. By minimality its image is $Z$. The second projection likewise has stable image in $V$ containing $w$, so irreducibility makes it onto $V$.

Put $N=\{v\in M:(0,v)\in\Gamma_0\}$. It lies in $V$ and is stable by applying $Q_{ab}$ to $(0,v)$. Irreducibility gives $N=0$ or $N=V$. In the latter case $(0,w)$ has weight $\Lambda$ in $\Gamma_0$. Apply the previously established algebraic lemmas `compact_span_eq_lowering` and `lowering_span_weight_scalar` to the product action. Their hypotheses are the compact bracket and the full highest-weight equations of the paired generator. They identify the part of the cyclic span of weight $\Lambda$ with the line of the generator. See `Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean:178–222`. Thus $(0,w)=c(x_0,w)$. The first coordinate forces $c=0$, contradicting $w\ne0$ in the second.

For $z\in Z$, $y\in Z^\perp$, one has $\langle z,E_{ab}y\rangle=\langle E_{ba}z,y\rangle=0$. Thus the complement is stable. Finite dimension gives $P=Z\oplus Z^\perp$. Set $\Gamma=\Gamma_0+(Z^\perp\times\{0\})$. Lift $y=z+z'$ by choosing a lift $(z,v)\in\Gamma_0$ and adding $(z',0)$. If the resulting first coordinate is zero, the two first coordinates lie in $Z\cap Z^\perp=\{0\}$ and the second is zero by the result for $N$. The sum is stable, lies over $V$ and contains the pair. Subtracting lifts proves uniqueness of the value at each point of $P$. Taking linear combinations or applying a compact operator to a lift gives linearity and intertwining. In particular the cyclic graph already gives a surjective intertwiner $Z\to V$, which this construction extends by zero on $Z^\perp$. `HW/PRVComponents/ParthasarathyTensorMatrix.lean:20–141`. [Lean, read]

**Lemma 2 (finite root strings and central shifts).** Let $F$ satisfy the compact bracket law and let $w\ne0$ be highest of full weight $\Lambda$ in a finite-dimensional compact-stable $V\le M$. Let $G$ be a finite matrix family with `KRel` and $f\ne0$ a column of real diagonal weight $\nu$, killed by every compact lowering matrix. For all compact $a<b$, $\Lambda_a-\Lambda_b$ and $\nu_b-\nu_a$ are nonnegative integers. Thus for every compact pair, $(\Lambda+\nu)_a-(\Lambda+\nu)_b$ is integral.

*Proof.* Evaluating the bracket at a vector gives
$$
F_{ab}F_{cd}v=F_{cd}F_{ab}v+\delta_{bc}F_{ad}v-\delta_{da}F_{cb}v.
$$
For any ordered pair of distinct same-sign indices put $R=F_{ab}$, $S=F_{ba}$ and $H_j=F_{jj}$. Then $[R,S]=H_a-H_b$, $[H_a,S]=-S$, and $[H_b,S]=S$. If $u\ne0$ is killed by $R$ and has diagonal eigenvalues $\ell_a,\ell_b$, then $u_k=S^ku$ has eigenvalues $\ell_a-k,\ell_b+k$. For each $k\ge0$,
$$
Ru_{k+1}=(k+1)(\ell_a-\ell_b-k)u_k.
$$
At $k=0$ this is $RSu=(H_a-H_b)u$. For the induction, commute $R$ across the outer $S$ and use the formula at $k$ and the diagonal eigenvalues at $k+1$. The new coefficient is $(k+1)(\ell_a-\ell_b-k)+\ell_a-\ell_b-2(k+1)=(k+2)(\ell_a-\ell_b-k-1)$. If the string stays in a finite-dimensional subspace, distinct eigenvalues $\ell_a-k$ force a first zero $u_{m+1}$. The formula then gives $\ell_a-\ell_b=m$. Apply this to $w$ in $V$ and to $f$ in the full finite column space with $a,b$ exchanged. Reversing a pair negates its integer difference and equal indices give zero. This also proves the adjacent archive endpoint `kIrrHW_int`. The tensor proof calls the general root-string supplier. `HW/PRVComponents/CompactRelationsApplyComm.lean:14–106` and `HighestWeightDifferencesNat.lean:19–170`. [Lean, read]

Now suppose $\mu=\Lambda+\nu$ is blockwise dominant. Put $\lambda_a=\lfloor\mu_a\rfloor$ and $t_a=\mu_a-\lambda_a$. The root strings imply that $t$ is constant on each block. Floors preserve weak order. The integral dominant existence theorem `HW.kType_exists_of_dom` (`HW/Exists.lean:15–43`) supplies a compact model on a finite-dimensional inner-product space $T$ with nonzero highest vector $p$ of weight $\lambda$. Its derived family $B$ satisfies both laws by `KType.kRel` and `KType.kUnit` (`HW/HasDerivAtRealOfComplex.lean:254–281`). Put $A_{ab}=B_{ab}+\delta_{ab}t_aI$. The scalars commute, and the extra bracket term on the right is $\delta_{bc}\delta_{ad}(t_a-t_c)I$, zero because $b=c$ puts $c$ in the block of $a$. The real diagonal shifts preserve `KUnit` and give $p$ the full weight $\mu$, with raising still zero. `HW/PRVComponents/TensorActionLieRelations.lean:22–61` and `ParthasarathyTensorMatrix.lean:157–173`. [Lean, read]

**Theorem (matrix PRV existence, `parthasarathy_tensor_matrix`).** Let $M$ be any complex vector space, $F$ an endomorphism family satisfying `KRel`, and $\Lambda\in\mathbb R^n$ and $V\le M$ satisfy `IsKIrrHW` at $(\epsilon,F,\Lambda,V)$. Let $\iota$ be a finite index type with decidable equality and $G_{ab}\in\operatorname{Mat}_\iota(\mathbb C)$ satisfy `KRel` and $G_{ba}=G_{ab}^\dagger$ for every compact pair. Assume $\nu\in\mathbb R^n$ and $f\ne0$ satisfy
$$
G_{aa}f=\nu_a f\quad(\forall a),\qquad
G_{ab}f=0\quad(\forall a,b:\ b<a,\ \epsilon_a=\epsilon_b).
$$
Suppose $\mu=\Lambda+\nu$ satisfies $\mu_b\le\mu_a$ for every $a<b$ with $\epsilon_a=\epsilon_b$. Then there is a nonzero $x\in M^\iota$ with $x_i\in V$ for all $i$ such that
$$
\begin{aligned}
F_{aa}x_i+\sum_{j\in\iota}(G_{aa})_{ij}x_j&=\mu_a x_i
  &&(\forall a,\ \forall i\in\iota),\\
F_{ab}x_i+\sum_{j\in\iota}(G_{ab})_{ij}x_j&=0
  &&(\forall a<b,\ \epsilon_a=\epsilon_b,\ \forall i\in\iota).
\end{aligned}
$$

*Proof.* Choose the target $w$ and the auxiliary $(T,A,p)$ above. Define $D_{ab}=-G_{ab}^{\mathsf T}$ and $g=\overline f$ componentwise. Transposition reverses multiplication, hence $[D_{ab},D_{cd}]=-[G_{ab},G_{cd}]^{\mathsf T}$ and `KRel` transfers to $D$. The matrix adjoint premise gives $D_{ba}=D_{ab}^\dagger$ and $D_{ab}g=-\overline{G_{ba}f}$ for compact pairs. The latter identity follows by writing its $i$th component $-\sum_j(G_{ab})_{ji}\overline{f_j}$. Thus $g$ is nonzero of weight $-\nu$ for $D$, and the raising matrices kill it by the lowering equations for $f$.

Use $P=T^\iota$ with sum inner product (finite `PiLp 2` in Lean) and
$$
(E_{ab}y)_i=A_{ab}y_i+\sum_j(D_{ab})_{ij}y_j.
$$
The pointwise $A$ and matrix $D$ actions commute by complex linearity, so the commutator contains only the two separate commutators and gives `KRel`. In $\langle E_{ab}y,z\rangle$ the pointwise part equals $\sum_i\langle y_i,A_{ba}z_i\rangle$. The matrix part is $\sum_{i,j}\overline{(D_{ab})_{ij}}\langle y_j,z_i\rangle=\sum_j\langle y_j,\sum_i(D_{ba})_{ji}z_i\rangle$. This proves `KUnit`. Now $x_0=(g_i p)_i$ is nonzero because some $g_i\ne0$ and $p\ne0$. Each diagonal eigenvalue is $\mu_a-\nu_a=\Lambda_a$, and each summand of every raising operator kills $x_0$. Lemma 1 gives the graph and $Lx_0=w$.

Let $s_i$ have value $p$ in slot $i$ and zero elsewhere. If $A_{ab}p=cp$ for a compact pair, the $k$th coordinate of $E_{ab}s_i$ is $\delta_{ki}cp-(G_{ab})_{ik}p$. This explains the row index $i$ in the original tensor equations. Thus
$$
E_{ab}s_i=cs_i-\sum_j(G_{ab})_{ij}s_j.
$$
Put $x_i=L(s_i)\in V$. Applying the intertwining identity yields $F_{ab}x_i=c x_i-\sum_j(G_{ab})_{ij}x_j$. Take $c=\mu_a$ on the diagonal and $c=0$ for raising pairs. Finally,
$$
\sum_i\overline{f_i}x_i=L\Big(\sum_i g_i s_i\Big)=L(x_0)=w\ne0.
$$
The proof gives this normalization. The public wrapper exposes membership in $V$, nonvanishing and the coordinate equations. See `HW/PRVComponents/ParthasarathyTensorMatrix.lean:145–251`, `TensorActionLieRelations.lean:67–179` and `HW/PRVComponents.lean:16–27`. [Lean, read]

**Failure when dominance is deleted.** Keep the first symmetric square of the $U(2)$ example and take $\operatorname{Sym}^3\mathbb C^2$ in the second factor, with its symmetric-power inner product and lowest vector $y_2^3$. The proposed weight is $(2,3)$. In unnormalized monomials, its weight basis is $u_k=x_1^{2-k}x_2^k y_1^k y_2^{3-k}$ for $k=0,1,2$. At weight $(3,2)$ use $v_k=x_1^{2-k}x_2^k y_1^{k+1}y_2^{2-k}$. Raising sends $u_k$ to $(3-k)v_k+k v_{k-1}$ with the second term absent at $k=0$. The triangular matrix has diagonal $3,2,1$, so the proposed highest space is zero even though all other hypotheses hold. More generally, a negative compact gap forces zero, by the finite root-string calculation on $V^\iota$ with its tensor bracket.

Deleting `KUnit` from the graph lemma can also fail. For $n=1$ let $E_{11}e_2=e_1$ and $E_{11}e_1=0$ on $P=\mathbb C^2$, and let $F_{11}=0$ on $V=M=\mathbb C$. The bracket holds and $x_0=e_1,w=1$ have weight zero. An invariant graph on all of $P$ would give $L(e_1)=F_{11}L(e_2)=0$ despite $Lx_0=1$. The pair still generates a graph over the line $Z=\mathbb C e_1$.

**Zero-rank and empty-index cases.** If $n=0$, stability is automatic and irreducibility together with $w\ne0$ forces $V=\mathbb Cw$. The tuple with $w$ in any single slot and zero elsewhere satisfies the vacuous weight equations. Some slot exists since $f\ne0$. For empty $\iota$, the sole column is zero, so the premises cannot hold.

**Scope and consumers.** For two ordinary compact unitary representations the tensor cyclic span of the resulting vector is irreducible. Indeed, in any orthogonal stable splitting of this span, both projections of the generator have its diagonal weight. The same-weight part is its line by the lowering argument, so orthogonality forces one projection to vanish and cyclicity forces the other summand to be the whole span. Compact group stability follows from the derived action by exponentiation on the connected compact blocks. The wrapper gives the coordinate witness for the algebraic target $F$. The compact Pieri results in `HW/PieriRules/`, the Weyl dimension formula in `HW/Finrank.lean:14–51`, and the pointed isometry in `HW/Unique.lean:30–81` are separate suppliers with their own hypotheses.

The two direct archive calls use the matrices `lfMat` on the exterior Fock basis indexed by physical subsets. Their chosen column is supported on the wedge indexed by all modes $(i,j)$ with $\epsilon_i=\mathrm{true}$, $\epsilon_j=\mathrm{false}$ and $j<i$. The tuples $\rho_C$ and $\rho_N$ count, at each index, half the number of later indices minus half the number of earlier ones among equal and opposite signs, respectively. For $p$ true and $q$ false indices, $\rho_{\mathrm{Hol}}$ is $q/2$ on true indices and $-p/2$ on false ones. Counting occurrences with sign gives the wedge weight $\rho_{\mathrm{Hol}}-\rho_N$. In the positive block, a lowering move removes an occupied $(b,j)$ and inserts $(a,j)$ with $b<a$. Whenever the removal succeeds, $j<b<a$ and the new mode is already occupied. In the negative block the move is from $(i,a)$ to $(i,b)$, where $b<a<i$, with the same duplication. Failed removals and repeated insertions both give zero. This supplies all compact lowering equations. The matrix bracket and adjoint are the physical restrictions of the signed Fock action. `DS/TensorRepresentations/LowFockB.lean:108–159` and `LowFockC.lean:11–97`.

In `lowFock_exists` the full bracket `IsGlRep` restricts to `KRel`. Assume `StrictAnti lam`, meaning strict decrease over the full index order, and the given `IsKIrrHW` at $\operatorname{lowK}(\epsilon,\lambda)=\lambda+\rho_N-\rho_C$. For consecutive indices $a<b$ in a sign block, $\rho_{C,a}-\rho_{C,b}=1$ and $k=\rho_{N,a}-\rho_{N,b}$ counts the opposite-sign indices strictly between $a$ and $b$. Write $m=\operatorname{lowK}_a-\operatorname{lowK}_b$, an integer by the finite root string. Then $m+1-k=\lambda_a-\lambda_b>0$, so $m\ge k$. Since $\rho_{\mathrm{Hol}}$ is constant on each block, $m-k$ is exactly the gap in the desired tensor label. Summing consecutive gaps gives every required dominance comparison. In the second consumer the premise `BlockAnti ε lam` says $\lambda_a-\lambda_b\ge1$ for every compact $a<b$. It directly gives the nonnegative gap $\lambda_a-\lambda_b-1$ at consecutive pairs. `DS/TensorRepresentations/LowFockD.lean:59–106` and `DS/TraceGap/ExistsNonzeroPhysicalHighestWeightVectorTensFock.lean:12–36`.

The lift `lfLift` sends the output tuple to $\sum_S x_S\otimes b_S$ in the original Fock basis. Coefficient extraction recovers each $x_S$ and proves nonvanishing. The matrix action on each $b_S$ transports the tuple equations to the diagonal action on the tensor, and unphysical annihilators kill every participating $b_S$. Thus both calls give a nonzero point in `tensFock V` and `physicalSubspace ε` of weight $\lambda-\rho_C+\rho_{\mathrm{Hol}}$ killed by all compact raising operators. Then `line_exists` packages the first witness in its specified intersection. The subsequent `dirac_sharp` uses the second witness at $\lambda-\operatorname{phSum}(Ph)$, retaining tensor-range membership, nonvanishing and the compact highest-weight equations. Its hypotheses include `Gap3`, the full bracket, infinitesimal unitarity, a nonempty set of positive noncompact pairs and the scalar Casimir at the unshifted parameter on the entire shifted compact seed. The proof uses those fields with the square identity and positivity in the shifted-weight contradiction. `DS/TensorRepresentations/LowFock.lean:14–41`, `LowFockE.lean:37–105`, `DS/TraceGap/SignedActionTensor.lean:58–62`, `FockWeightWedgeLowerModes.lean:105–162`. [Lean]

**Classical context.** Parthasarathy, Ranga Rao and Varadarajan's 1966 announcement, §2, Theorem 1, p. 522, takes two dominant integral labels and restricts the corresponding irreducible two-factor representation to the diagonal $X\mapsto(X,X)$ specified in §1. In tensor-product notation its second restricted factor has lowest weight $-\mu_2^\ast$, where the star here denotes the highest weight of the dual. Equivalently this lowest weight is $w_0\mu_2$, with $w_0$ the longest Weyl element. The announced theorem gives multiplicity one for the dominant representative of the orbit of $\Lambda+w_0\mu_2$ in the complex semisimple setting. The matrix producer above treats an already dominant sum, allows a finite matrix family with a chosen lowest column, and accommodates blockwise real central shifts in the derived action. [Paper] [1966 announcement](https://doi.org/10.1090/S0002-9904-1966-11528-8) · [1967 paper](https://annals.math.princeton.edu/1967/85-3/p03)

**Review and scope.** The local proof reading is author-level R3. Same-source initial review R023 upheld the cyclic graph, the original-coordinate witness and the Fock dominance handoff, with the diagonal terminology correction incorporated above. Different-source review of this section is pending. [Source ledger](../sources/SOURCES.md#chapter-9-prv-extremal-component-and-dirac-kernel)

**From existence to degree.** On the witness of `line_exists`, [§9.4.24](#9424-the-exterior-degree-of-the-physical-fock-highest-weight-line) uses the tensor highest weight `gaW`, the first-factor compact type at `lowK`, physical membership, and the bracket and infinitesimal-unitarity hypotheses of `line_deg` to place the tensor in a single exterior degree. [§9.4.25](#9425-when-the-casimir-puts-the-physical-highest-weight-line-in-the-dirac-kernel) uses the same witness and an extra Casimir premise for Dirac annihilation.

---

### 9.4.24 The exterior degree of the physical Fock highest-weight line

**Motivation.** The extremal tensor of [§9.4.23](#9423-the-prv-extremal-component-and-the-highest-weight-graph) has a specified compact highest weight and lies in the physical subspace of a tensor product with the full exterior algebra. To see which wedge degrees occur, sum the diagonal operators over the positive signature block. The sum acts by one scalar throughout the compact type in the first factor. In the physical Fock factor it counts occupied modes, since each physical mode has exactly one positive endpoint. The difference between the total weight and the first-factor scalar counts the wedge factors in each surviving coordinate. [Expository]

**Worked signatures.** Use one-based indices and signs $+$ and $-$ for the two Boolean values. Write $b_{ij}$ for a mode generator, $b_s$ for an ordered wedge and $b_\varnothing=1$. A physical mode $(i,j)$ contributes the weight $e_i-e_j$ in the standard coordinate vectors.

1. **Signature $(-,+)$.** The sole physical mode is $(2,1)$, and $1<2$ gives $\mathrm{sDeg}=1$. Take $M=W=\mathbb C u$, $\|u\|=1$, and $E_{ab}=\delta_{ab}I$ on all pairs. The commutator is zero, and the two terms on the right of the matrix-unit law are both $\delta_{bc}\delta_{ad}I$. The real diagonal operators and zero off-diagonals give the signed adjoint law. The one-dimensional $W$ is irreducible of highest weight $(1,1)$. The counts are $\rho_C=(0,0)$, $\rho_N=(1/2,-1/2)$ and $\rho_{\mathrm{Hol}}=(-1/2,1/2)$. With $\lambda=(1/2,3/2)$ one obtains $\mathrm{lowK}=(1,1)$ and $\mathrm{gaW}=(0,2)$. The vacuum tensor has weight $(1,1)$ and $u\otimes b_{21}$ has weight $(1,1)+(-1,1)=(0,2)$. There are no compact raising pairs, and each forbidden contraction kills $b_{21}$. The positive coordinate equation reads $2=1+1$. The only nonzero coefficient is $u$ at $\{(2,1)\}$, and using the two factors in $W$ and the degree-one subspace gives an explicit preimage.
2. **Signature $(-,+,+)$.** Use the same trace character on $\mathbb C u$. The counts give $\rho_C=(0,1/2,-1/2)$, $\rho_N=(1,-1/2,-1/2)$ and $\rho_{\mathrm{Hol}}=(-1,1/2,1/2)$. Set $\lambda=(0,2,1)$, giving $\mathrm{lowK}=(1,1,1)$ and $\mathrm{gaW}=(-1,2,2)$. Both physical modes $(2,1),(3,1)$ count toward $\mathrm{sDeg}=2$. Their double wedge has weight $(-2,1,1)$ and hence total weight $(-1,2,2)$. The positive sum at indices $2,3$ reads $4=2+2$. The sole compact raising operator replaces $(3,1)$ by the already occupied $(2,1)$, so it kills the wedge. Forbidden contractions vanish. The double wedge is nonzero, and the tensor of the two factors in the subspaces gives the degree-two preimage.

These two examples realize the full algebraic and inner-product premises below. The statement has no global number-field or automorphic parameter. To see what two surviving slots can look like, take $(-,+,-)$ and the local compact model with basis $u_1,u_3$, standard matrix units on the negative block and $E_{22}=0$. Then $\rho_C=\rho_N=(1/2,0,-1/2)$ and $\rho_{\mathrm{Hol}}=(-1/2,1,-1/2)$. At $\lambda=(1,0,0)$ the labels are $\mathrm{lowK}=(1,0,0)$ and $\mathrm{gaW}=(0,1,0)$. The singleton Fock weights $(-1,1,0)$ and $(0,1,-1)$ require first-factor weights $(1,0,0)$ and $(0,0,1)$, respectively. Thus $u_1\otimes b_{21}+u_3\otimes b_{23}$ has the desired diagonal weight. The compact raising operator $A_{13}$ gives $-u_1\otimes b_{23}$ on the first term and $u_1\otimes b_{23}$ on the second. Each slot contributes one at index $2$ and the first factor contributes zero there. Only $(2,1)$ has second index less than first, so $\mathrm{sDeg}=1$ even though both singleton slots occur. The zero extension to mixed pairs fails $[E_{12},E_{21}]=E_{11}-E_{22}$ on $u_1$. This last example models the compact coordinate calculation. [Expository]

**Definitions.** Take $n\ge0$ and any $\epsilon:\operatorname{Fin}n\to\{\mathrm{true},\mathrm{false}\}$. Let $P=\mathrm{plusIdx}(\epsilon)$ and $Q=\mathrm{minusIdx}(\epsilon)$ be the true and false indices. Put $B=\mathbb C^{\operatorname{Fin}n\times\operatorname{Fin}n}$, $\mathrm{Fock}(n)=\bigwedge B$ and $F_d=\bigwedge^d B\subseteq\mathrm{Fock}(n)$. The archive labels pairs by $\mathrm{finProdFinEquiv}$ in $\operatorname{Fin}(n^2)$. A basis index $s$ ranges over all finite subsets of that type. We write $b_s=\mathrm{fockBasis}(n)(s)$ using the transported order, and identify sets of pairs with their images under the equivalence.

Write $c^+_{ij}$ for exterior multiplication by $b_{ij}$ on the left and $c^-_{ij}$ for contraction by its coordinate functional. The signed Fock operator $S_{ab}=\mathrm{sgE}(\epsilon,c^+,c^-)_{ab}$ is
$$
S_{ab}=\begin{cases}
\sum_{j\in Q}c^+_{aj}c^-_{bj} & a,b\in P,\\
-\sum_{i\in P}c^+_{ib}c^-_{ia} & a,b\in Q,\\
0 & \epsilon_a\ne\epsilon_b .
\end{cases}
$$
The diagonal action $\mathrm{diagE}(\epsilon,\mathrm{eT}(E),\mathrm{cpT},\mathrm{cmT})$ is $A_{ab}=E_{ab}\otimes 1+1\otimes S_{ab}$. The index set $\mathrm{lfPhysModes}(\epsilon)$ is $P\times Q$ in pair notation. The subspace $\mathrm{physicalSubspace}(\epsilon)$ is the intersection of the kernels of $1\otimes c^-_{ij}$ over all forbidden modes $(i,j)\notin P\times Q$. Define $\mathrm{modeWt}(\epsilon,(i,j))=e_i-e_j$ on $P\times Q$ and zero elsewhere. Then $\mathrm{fockWt}(\epsilon,s)=\sum_{m\in s}\mathrm{modeWt}(\epsilon,m)$.

Let $b_s^\vee$ denote the dual basis functional. Write $x_s=\mathrm{tcoef}(b_s^\vee)(z)$ for the coefficient in $M$. On $u\otimes f$ the coefficient is $b_s^\vee(f)u$. Linearity and the basis expansion on the second factor give $z=\sum_s x_s\otimes b_s$. The map $\iota_W:W\hookrightarrow M$ denotes the subspace inclusion, so $\mathrm{tensFock}(W)$ is the range of $\mathrm{TensorProduct.map}(\iota_W,\mathrm{id}_{\mathrm{Fock}(n)})$.

At index $a$, $\rho_C(\epsilon)_a$ is half the number of same-sign indices after $a$ minus half the number before $a$. The tuple $\rho_N$ uses opposite signs in the same count. The coordinate $\rho_{\mathrm{Hol}}(\epsilon)_a$ is $|Q|/2$ for $a\in P$ and $-|P|/2$ for $a\in Q$. Use
$$
\begin{aligned}
\mathrm{lowK}(\epsilon,\lambda)&=\lambda+\rho_N(\epsilon)-\rho_C(\epsilon),\\
\mathrm{gaW}(\epsilon,\lambda)&=\lambda-\rho_C(\epsilon)+\rho_{\mathrm{Hol}}(\epsilon),\\
\mathrm{sDeg}(\epsilon)&=|\{(i,j)\in P\times Q:j<i\}|.
\end{aligned}
$$
The predicate $\mathrm{IsKHWVec}(\epsilon,A,\gamma,z)$ imposes $A_{aa}z=\gamma_a z$ for all $a$ and $A_{ab}z=0$ for all same-sign $a<b$. Real labels act through $\mathbb R\hookrightarrow\mathbb C$. These simultaneous kernel conditions define $\mathrm{khwSub}(\epsilon,A,\gamma)$. The archive's $\mathrm{lineSub}(\epsilon,E,\lambda,W)$ is $(\mathrm{khwSub}(\epsilon,A,\mathrm{gaW}(\epsilon,\lambda))\cap\mathrm{tensFock}(W))\cap\mathrm{physicalSubspace}(\epsilon)$.

**Lemma (physical Fock degree concentration).** For every $n,\epsilon$ as above, every real tuple $\lambda$, every complex inner-product space $M$, and every family $E_{ab}$ of complex-linear endomorphisms of $M$, assume $\mathrm{IsGlRep}(E)$ and $\mathrm{IsInfUnitary}(\epsilon,E)$. The former is the matrix-unit bracket $[E_{ab},E_{cd}]=\delta_{bc}E_{ad}-\delta_{da}E_{cb}$ for all $a,b,c,d$. The latter means
$$
\langle E_{ab}u,v\rangle=\operatorname{adjSign}(\epsilon,a,b)\langle u,E_{ba}v\rangle
\qquad (a,b\in\operatorname{Fin}n,\ u,v\in M),
$$
where the sign is $1$ for equal signs and $-1$ for opposite signs. Let $W\le M$ satisfy $\mathrm{IsKIrrHW}(\epsilon,E,\mathrm{lowK}(\epsilon,\lambda),W)$. Thus $W$ is finite-dimensional, is stable under every same-sign $E_{ab}$, and its only subspaces stable under all these operators are $0$ and $W$. It contains a nonzero $w$ satisfying $\mathrm{IsKHWVec}(\epsilon,E,\mathrm{lowK}(\epsilon,\lambda),w)$.

For every $z\in\mathrm{lineSub}(\epsilon,E,\lambda,W)$ and every basis index $s$, if $x_s\ne0$ then $s\subseteq\mathrm{lfPhysModes}(\epsilon)$ and $|s|=\mathrm{sDeg}(\epsilon)$. In particular, with $d=\mathrm{sDeg}(\epsilon)$ and $\iota_d:F_d\hookrightarrow\mathrm{Fock}(n)$, there exists $y\in W\otimes_{\mathbb C}F_d$ satisfying
$$
\mathrm{TensorProduct.map}(\iota_W,\iota_d)(y)=z .
$$
The range membership is the formal conclusion of `line_deg`, and the coordinate equality is its intermediate assertion. [Lean, read]

**Proof.** Coefficient extraction commutes with a linear map on the left. A linear map $T$ on the right changes $b_s^\vee$ to $b_s^\vee\circ T$. These identities follow on pure tensors and extend by linearity. In particular $z\in\mathrm{tensFock}(W)$ implies $x_s\in W$: extract the coordinate of a preimage with values in $W$ and then apply $\iota_W$.

For a mode $m$ put $N_m=c_m^+c_m^-$. If $m$ occurs at position $r$ in an ordered wedge, contraction deletes it with sign $(-1)^{r-1}$, and reinserting it at the front and reordering contributes the same sign. If $m$ is absent, contraction is zero. Therefore $N_m b_t=\mathbf 1_{m\in t}b_t$, which implies $b_s^\vee N_m=\mathbf 1_{m\in s}b_s^\vee$ on the basis. For a forbidden $m$, physical membership implies $(1\otimes c_m^-)z=0$ and hence $(1\otimes N_m)z=0$. Extracting the $s$ coordinate gives $\mathbf 1_{m\in s}x_s=0$. If $x_s\ne0$ this excludes every forbidden mode. Conversely, wedges supported on physical modes are killed by every forbidden contraction.

For $a\in P$, $S_{aa}$ sums $N_{(a,j)}$ over $Q$. For $a\in Q$, it is the negative sum of $N_{(i,a)}$ over $P$. Thus $S_{aa}b_t=\mathrm{fockWt}(\epsilon,t)_a b_t$ even if $t$ contains forbidden modes. Applying $b_s^\vee$ gives $b_s^\vee S_{aa}=\mathrm{fockWt}(\epsilon,s)_a b_s^\vee$. This proves the tensor coefficient identity for all $a,s,z$:
$$
\mathrm{tcoef}(b_s^\vee)(A_{aa}z)=E_{aa}x_s+\mathrm{fockWt}(\epsilon,s)_a\,x_s .
$$
Applying it to the highest diagonal equation gives, for each $a$,
$$
E_{aa}x_s=\big(\mathrm{gaW}(\epsilon,\lambda)_a-\mathrm{fockWt}(\epsilon,s)_a\big)x_s .
$$

Set $Z_+=\mathrm{zPlus}(\epsilon,E)=\sum_{a\in P}E_{aa}$ and $C_W=\sum_{a\in P}\mathrm{lowK}(\epsilon,\lambda)_a$. The matrix-unit bracket yields $[Z_+,E_{ab}]=(\mathbf 1_{a\in P}-\mathbf 1_{b\in P})E_{ab}$. This vanishes for every same-sign pair. Therefore $W\cap\ker(Z_+-C_W I)$ is compact-stable. It contains $w\ne0$, by the diagonal weight of $w$. Irreducibility forces this intersection to be $W$, so $Z_+x_s=C_Wx_s$ for every $s$.

Fix $s$ with $x_s\ne0$. Summing the coordinate equations over $P$ gives a second scalar for $Z_+x_s$. Using injectivity of scalar multiplication on the fixed nonzero vector $x_s$ equates the two complex scalars. Injectivity of $\mathbb R\hookrightarrow\mathbb C$ gives the real identity
$$
\sum_{a\in P}\mathrm{fockWt}(\epsilon,s)_a
=\sum_{a\in P}\big(\mathrm{gaW}(\epsilon,\lambda)_a-\mathrm{lowK}(\epsilon,\lambda)_a\big).
$$
For each $(i,j)\in s$, physical support gives $\sum_{a\in P}(e_i-e_j)_a=1$. Interchanging finite sums therefore evaluates the left side as $|s|$. The difference of labels on the right is $\rho_{\mathrm{Hol}}-\rho_N$. For $a\in P$, partition $Q$ into the indices before and after $a$. The difference $|Q|/2-\rho_N(\epsilon)_a$ is exactly the number of $j\in Q$ with $j<a$. The right side counts each pair in $\mathrm{sModes}(\epsilon)$ once. Here `sModes` is the set of physical pairs with second index less than first. The natural numbers $|s|$ and $d$ have equal real casts, and hence are equal.

Finally, $b_s$ is the image of the ordered $|s|$ mode vectors under the alternating wedge map $\iota_{\mathrm{multi}}$, which takes values in $F_{|s|}$. For $x_s\ne0$ use $|s|=d$ and tensor $x_s$ as an element of $W$ with $b_s$ as an element of $F_d$. For a zero coefficient take zero in $W\otimes F_d$. Summing gives a preimage whose image, by the pure-tensor rule and linearity, is $\sum_s x_s\otimes b_s=z$. [Lean, read]

**Zero and empty cases.** The assertion includes $z=0$, with zero preimage and vacuous implications for its coefficients. If $P$ or $Q$ is empty, the only physical set is $\varnothing$ and $d=0$. For $n=0$ the exterior algebra is $\mathbb C$ in degree zero, there are no weight conditions and every $z\in\mathrm{tensFock}(W)$ is physical and highest. For a single sign in positive rank the two labels coincide and the vacuum tensor's highest equations are those on $W$. With both signs present one can still have $d=0$ when all positive indices precede all negative indices.

**Failure tests.** In the full $(-,+)$ trace model, delete physical membership and take $u\otimes(b_{21}+b_{\{(1,1),(2,1)\}})$. The forbidden mode $(1,1)$ has zero weight, so both terms have total weight $(0,2)$ and there are no compact raising pairs. Contraction at $(1,1)$ leaves a nonzero multiple of $u\otimes b_{21}$. The two nonzero coefficients have degrees $1$ and $2$. Any vector in a single-degree range has zero coordinates outside that degree, by the wedge basis and the pure-tensor rule. This mixed tensor misses the claimed range.

For the second deletion, when both blocks are present, express the diagonal constraints by their traceless parts in each block, the total trace and the positive-block trace. These equations recover the individual diagonals by taking block averages. In the same trace model retain the traceless equations, total trace, compact raising and physical conditions, and omit the positive-block trace constraint. Then $u\otimes(1+b_{21})$ has degrees $0$ and $1$. Both terms have total trace $2$, and there are no traceless or raising equations for these singleton blocks. The positive diagonal $A_{22}$ has eigenvalues $1$ and $2$ on the two terms respectively. Keeping all original individual diagonal equations would imply the omitted sum again by addition. [Expository]

**Use in the archive.** The compact raising equations and infinitesimal unitarity are retained in the original interface. The concentration calculation uses the diagonal equations, physical support and the scalar action on $W$. Existence of a nonzero $z$ comes separately from `line_exists` under its own $\mathrm{StrictAnti}(\lambda)$, $\mathrm{IsGlRep}$ and $\mathrm{IsKIrrHW}$ assumptions via the PRV construction of [§9.4.23](#9423-the-prv-extremal-component-and-the-highest-weight-graph).

The derived action provides `IsGlRep` and `IsInfUnitary` to this call. On its common witness the first-factor type supplies `lowK`, the tensor equations supply `gaW`, and physical membership restricts every nonzero wedge coordinate to $P\times Q$. The direct call is in `lean/src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TraceGap/GeneratedSubStable.lean:79–83`. It gets the witness from `line_exists`, uses `line_ker` separately with the Casimir hypothesis, and returns the range field from `line_deg` at line 191. `lean/src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TraceGap/SupTrace.lean:87,206–215` uses that field through `gradT_range_ext` for the parity factor $(-1)^d$, then transports parity through `gradT_kLowSpan` and the separately supplied kernel identification. [§9.4.25](#9425-when-the-casimir-puts-the-physical-highest-weight-line-in-the-dirac-kernel) gives the separate proof of `line_ker` with the prescribed Casimir scalar on all of $W$. The kernel identification used in the parity transport, including reverse inclusion and exhaustion, and a quantitative spectral gap are [Open] in this reading. [Lean]

**Sources and reading level.** Archive A2, joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The calculation is local R3 at `lean/src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TraceGap/SignedActionTensor.lean:20–52,64–118`, `lean/src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/CFPrimeB.lean:12–56,64–73,174–225`, `lean/src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TraceGap/MemHighestWeightSubIff.lean:12–20,123–133` and `lean/src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TraceGap/GsBasisPhys.lean:48–54,101–113`. The exterior basis also has a human proof in Keith Conrad, *Exterior Powers*, Theorem 4.2, pp. 11–12, for a free module with an ordered basis. [A2](../sources/SOURCES.md#a2) · [Conrad's notes](https://kconrad.math.uconn.edu/blurbs/linmultialg/extmod.pdf#page=11)

**Review.** Author-level local R3 for `line_deg` and the indicated production and parity bodies. The original examples and deletion tests passed 464 exact finite checks. Dedicated same-source and different-source proof reviews are pending. The review of the separate Dirac inclusion applies to §9.4.25.

[Source and review ledger](../sources/SOURCES.md#chapter-9-compact-pieri-weyl-model-and-physical-fock-degree) · [Contributions](../CONTRIBUTIONS.md#chapter-9-compact-pieri-weyl-model-and-physical-fock-degree)

---

### 9.4.25 When the Casimir puts the physical highest-weight line in the Dirac kernel

**Motivation.** The PRV construction in [§9.4.23](#9423-the-prv-extremal-component-and-the-highest-weight-graph) gives a physical highest-weight tensor. To use it in the Dirac trace, we need a second fact: the Dirac operator kills it. The square compares the ambient Casimir with a scalar computed from the tensor's compact weight. When the scalars agree, the tensor inner product converts the equation for the square into an equation for the operator itself. [Expository]

**Worked examples.** Use one-based indices and write $b_{ia}$ for a mode, with vacuum $1$.

1. **Rank two with nonzero Dirac action.** In signature $(-,+)$ take $M$ to consist of finite sums of $u_j$, $j\ge0$, with orthogonal squared norms $g_0=1$, $g_j=j(j+3)g_{j-1}$. Define
   $$
   \begin{aligned}
   E_{11}u_j&=(2+j)u_j,& E_{22}u_j&=-(2+j)u_j,\\
   E_{12}u_j&=u_{j+1},& E_{21}u_j&=-j(j+3)u_{j-1}.
   \end{aligned}
   $$
   The last term is zero at $j=0$. The diagonal commutators with $E_{12}$ have coefficients $1,-1$, those with $E_{21}$ have coefficients $-1,1$, and $[E_{12},E_{21}]u_j=((j+1)(j+4)-j(j+3))u_j=(4+2j)u_j$. The diagonals commute, which completes the matrix-unit check. The norm recursion gives $E_{12}^{\dagger}=-E_{21}$ as a pairing identity on $M$, and the real diagonals are symmetric. For $W=\mathbb C u_0$ and $\lambda=(3/2,-3/2)$, the shifts are $\rho_C=0$, $\rho_N=(1/2,-1/2)$ and $\rho_{\rm Hol}=(-1/2,1/2)$. The compact seed weight is $(2,-2)$ and the target weight is $(1,-1)$. The Casimir on $W$ is $8-4=4$, equal to $9/2-1/2$. The tensor $z=u_0\otimes b_{21}$ adds weight $(-1,1)$ to the seed, has no compact raising equations and is killed by every forbidden contraction. The compact Casimir at $z$ contributes $2$, and the holomorphic diagonal correction contributes $2$. Creation repeats the occupied mode, and the contraction term contains $E_{21}u_0=0$. To see that the operator acts elsewhere, set $x=u_0\otimes1$ and $y=u_1\otimes b_{21}$. Then $Dx=y$ and $Dy=4x$. The squared norms of $x,y$ are $1,4$, so $t(Dx,y)=t(x,Dy)=4$.
2. **Rank three with two occupied modes.** Take signature $(-,+,+)$, $M=W=\mathbb C u$ with $\|u\|=1$, and $E_{ab}=\delta_{ab}I$. The bracket has zero left side and equal right-hand terms. The real diagonals and zero off-diagonals satisfy the signed adjoint law. The seed has weight $(1,1,1)$. Here $\rho_C=(0,1/2,-1/2)$, $\rho_N=(1,-1/2,-1/2)$ and $\rho_{\rm Hol}=(-1,1/2,1/2)$. For $\lambda=(0,2,1)$ we get $\mathrm{lowK}=(1,1,1)$ and $\mathrm{gaW}=(-1,2,2)$. The tensor $z=u\otimes(b_{21}\wedge b_{31})$ adds weight $(-2,1,1)$. The sole compact raising operator replaces $(3,1)$ by the already occupied $(2,1)$, and forbidden contractions vanish. The ambient Casimir is $3I$ and $\mathrm{casVal}(\lambda)=5-2=3$. The compact Casimir at $z$ contributes $9$ and the diagonal correction contributes $-6$. Both Dirac terms vanish because every mixed matrix unit acts as zero.

Both examples realize the complete local representation hypotheses with the full exterior factor and a one-dimensional irreducible seed $W$. As an abstract illustration of the last positivity step, take the ordinary inner product on $\mathbb C^2$, $T=\begin{pmatrix}1&1\\1&1\end{pmatrix}$ and $v=(1,-1)$. Then $T$ is symmetric, $T^2=2T$, $T^2v=0$, and $\|Tv\|^2=\langle v,T^2v\rangle=0$. This third example concerns only the form and operator in that step. [Expository]

**Definitions.** Let $n\ge0$, $I=\operatorname{Fin}n$, $\epsilon:I\to\{\mathrm{true},\mathrm{false}\}$, and let $P,Q$ be the true and false sets of sizes $p,q$. Let $M$ be a complex inner-product space. Set $F=\mathrm{Fock}(n)=\bigwedge(\mathbb C^{I\times I})$ and $X=M\otimes_{\mathbb C}F$, with algebraic tensor product. On $X$ write $L_{ab}=E_{ab}\otimes1$, $P_{ia}=1\otimes c^+_{ia}$ and $Q_{ia}=1\otimes c^-_{ia}$ for the left action, exterior multiplication on the left by $b_{ia}$, and contraction by its coordinate functional, respectively. Products act right to left. Let
$$
S_{ab}=\begin{cases}
\sum_{j\in Q}P_{aj}Q_{bj}&a,b\in P,\\
-\sum_{i\in P}P_{ib}Q_{ia}&a,b\in Q,\\
0&\epsilon_a\ne\epsilon_b,
\end{cases}
\qquad A_{ab}=L_{ab}+S_{ab}.
$$
The archive's Dirac operator is $D=D_++D_-$, where
$$
D_+=\sum_{i\in P,\,a\in Q}L_{ai}P_{ia},\qquad
D_-=-\sum_{i\in P,\,a\in Q}L_{ia}Q_{ia}.
$$
For an operator family $B$, put $C_B=\sum_{a,b}B_{ab}B_{ba}$ and let $C_K(B)$ be the sum over equal signs. For real tuples use $u\cdot v=\sum_a u_av_a$, $\mathrm{nsq}(u)=u\cdot u$, and, in zero-based indices, $\rho_a=(n-1)/2-a$. The coordinate $\rho_{C,a}$ is half the number of same-sign indices after $a$ minus half the number before it. The tuple $\rho_N$ counts opposite signs in the same way. Put $r=\rho_{\rm Hol}$ with entries $q/2$ on $P$ and $-p/2$ on $Q$. Define
$$
\mathrm{lowK}=\lambda+\rho_N-\rho_C,\qquad
\gamma=\mathrm{gaW}=\lambda-\rho_C+r,\qquad
\mathrm{casVal}(\lambda)=\mathrm{nsq}(\lambda)-\mathrm{nsq}(\rho).
$$
The predicate $\mathrm{IsKHWVec}(\epsilon,B,\nu,v)$ means $B_{aa}v=\nu_av$ for every $a$ and $B_{ab}v=0$ for every same-sign $a<b$. The subspace $\mathrm{lineSub}(\epsilon,E,\lambda,W)$ of $X$ is the intersection of this highest-weight subspace for $(A,\gamma)$, the range $\mathrm{tensFock}(W)=\operatorname{im}(\iota_W\otimes1)$ for the inclusion $\iota_W:W\hookrightarrow M$, and $\mathrm{physicalSubspace}(\epsilon)=\bigcap_{(i,a)\notin P\times Q}\ker Q_{ia}$.

Write $b_s$ for the ordered wedge on a subset $s$ of the $n^2$ modes, with order transported from $\operatorname{Fin}(n^2)$, and $x_s(v)=(1\otimes b_s^\vee)v$ for its coefficient in $M$. The archive's `tform` is $t(v,v')=\sum_s\langle x_s(v),x_s(v')\rangle_M$, conjugate linear in the first argument. Real scalars on complex spaces act through their complex images.

**Lemma (physical highest-weight tensors in the Dirac kernel).** For every $n,\epsilon,M$ above, every real tuple $\lambda$ on $I$, and every family $E$ of complex-linear endomorphisms of $M$, assume the following.

1. $\mathrm{IsGlRep}(E)$ holds, meaning $[E_{ab},E_{cd}]=\delta_{bc}E_{ad}-\delta_{da}E_{cb}$ for all $a,b,c,d\in I$.
2. $\mathrm{IsInfUnitary}(\epsilon,E)$ holds, meaning $\langle E_{ab}u,v\rangle_M=\operatorname{adjSign}(\epsilon,a,b)\langle u,E_{ba}v\rangle_M$ for all $a,b\in I$ and $u,v\in M$. The sign is $1$ for equal signs and $-1$ otherwise.
3. The complex subspace $W\le M$ satisfies $\mathrm{IsKIrrHW}(\epsilon,E,\mathrm{lowK},W)$. It is finite dimensional and stable under every same-sign $E_{ab}$. Every subspace of $W$ stable under all these operators is $0$ or $W$. There is a nonzero $w\in W$ satisfying $\mathrm{IsKHWVec}(\epsilon,E,\mathrm{lowK},w)$.
4. For every $v\in W$, $C_Ev=\mathrm{casVal}(\lambda)v$, with the same $\lambda$ used in $\mathrm{lowK}$ and $\mathrm{gaW}$.

Then for every $z\in\mathrm{lineSub}(\epsilon,E,\lambda,W)$ one has $Dz=0$ in $X$. This is `TRGap.line_ker`. [Lean, read]

**Proof.** On pure tensors $L_{ab}L_{ba}$ applies $E_{ab}E_{ba}$ to the first factor and keeps the second. Summing and extending by linearity gives $C_L=C_E\otimes1$ (`ssh_casimir_eT`). Choose $y\in W\otimes F$ with $(\iota_W\otimes1)y=z$. Put $c=\mathrm{casVal}(\lambda)$. The scalar premise says $C_E\circ\iota_W=c\iota_W$, as maps out of $W$. Thus
$$
C_L z=(C_E\otimes1)(\iota_W\otimes1)y
=((C_E\circ\iota_W)\otimes1)y=c(\iota_W\otimes1)y=cz.
$$
Composition and scaling commute with the tensor map by the pure-tensor rule. This argument uses the whole scalar premise on $W$ because $y$ may have several independent first-factor coefficients.

The operators $L$ inherit the matrix-unit law. Lifted creations anticommute with one another, as do lifted contractions, and $Q_\alpha P_\beta+P_\beta Q_\alpha=\delta_{\alpha\beta}I$ for mode pairs $\alpha,\beta$. These are the canonical anticommutation relations, from exterior antisymmetry and the contraction rule $c^-_\alpha(b_\beta\wedge f)=\delta_{\alpha\beta}f-b_\beta\wedge c^-_\alpha f$. Operators on different factors commute. These are the three inputs to `two_D_sq`.

Put $U=\sum_{i\in P,\,a\in Q}L_{ia}L_{ai}$ and $B=\sum_{\epsilon_a=\epsilon_b}L_{ab}S_{ba}$. Within either mixed block the $L$'s commute, since the two Kronecker terms of their bracket vanish. Anticommutation then gives $D_+^2=D_-^2=0$. In the sum of the two mixed products the summand before the overall minus sign is
$$
[L_{ai},L_{jb}]P_{ia}Q_{jb}+\delta_{ij}\delta_{ab}L_{jb}L_{ai}.
$$
The bracket $\delta_{ij}L_{ab}-\delta_{ab}L_{ji}$ gives $B$ after taking the minus sign and summing. The contraction delta gives $-U$, so $D^2=B-U$. Reversing the mixed products $L_{ai}L_{ia}$ gives the correction $p\sum_{a\in Q}L_{aa}-q\sum_{i\in P}L_{ii}$, hence $C_L=C_K(L)+2U-2\sum_a r_a L_{aa}$. Expanding $C_K(A)$ gives $C_K(L)+2B+C_K(S)$. In $C_K(S)$, moving a contraction past a creation gives $p$ copies of the occupation sum from the positive block and $q$ from the negative block. The quartic sums have terms $P_{ix}P_{jy}Q_{jx}Q_{iy}$ and $P_{ix}P_{jy}Q_{iy}Q_{jx}$ over $i,j\in P$ and $x,y\in Q$. They cancel by anticommutation. Thus $C_K(S)=(p+q)\sum_{i\in P,\,a\in Q}P_{ia}Q_{ia}=2\sum_a r_a S_{aa}$. Substituting gives
$$
2D^2=-C_L+C_K(A)-2\sum_a r_a A_{aa}.
$$

To evaluate on a highest vector, use $[A_{ab},A_{ba}]=A_{aa}-A_{bb}$ for equal signs. The left-family bracket gives the $L$ part. For the $S$ part, anticommuting gives $[P_\alpha Q_\beta,P_\eta Q_\theta]=\delta_{\beta\eta}P_\alpha Q_\theta-\delta_{\theta\alpha}P_\eta Q_\beta$. For a positive pair $a,b$, summing gives the occupation at $a$ minus the occupation at $b$. For a negative pair, contraction and insertion interchange $a,b$ in the defining formula, giving the occupation at $b$ minus that at $a$, which is again $S_{aa}-S_{bb}$. The diagonal terms of $C_K(A)z$ give $\sum_a\gamma_a^2 z$. For same-sign $a<b$ the term $A_{ba}A_{ab}z$ vanishes, and commuting the other product gives $A_{ab}A_{ba}z=(\gamma_a-\gamma_b)z$. These differences sum to $2\rho_C\cdot\gamma$. The resulting coefficient in $2D^2z$ is
$$
\mathrm{nsq}(\gamma+\rho_C)-\mathrm{nsq}(\rho_C)-2r\cdot\gamma-c.
$$
Each block's $\rho_C$ entries sum to zero by pair cancellation, so $\rho_C\cdot r=0$. Listing $P$ then $Q$, in their original internal order, lists $\rho_C+r$ in the order of $\rho$. At zero-based block position $k$, its entry is $(p-1)/2-k+q/2$ on $P$ and $(q-1)/2-k-p/2$ on $Q$. These equal the corresponding $\rho$ entries at positions $k$ and $p+k$. Consequently $\mathrm{nsq}(\rho)=\mathrm{nsq}(\rho_C)+\mathrm{nsq}(r)$. With $\gamma=\delta+r$, expansion gives the coefficient of `two_D_sq_khw`:
$$
2D^2z=\big(\mathrm{nsq}(\delta+\rho_C)-\mathrm{nsq}(\rho)-c\big)z.
$$
In `line_ker`, $\delta=\lambda-\rho_C$. The two compact shifts cancel pointwise and $c$ is exactly $\mathrm{nsq}(\lambda)-\mathrm{nsq}(\rho)$. The real difference and its complex image are zero. Invertibility of $2$ gives $D(Dz)=0$.

On the tensor form the signed adjoint law for $L$ holds coefficient by coefficient. Inserting a mode at position $k$ yields the same sign $(-1)^{k-1}$ as deleting it at that position, so creation and contraction are adjoint in the wedge basis. Expanding the coefficient sums gives $t(P_{ia}v,v')=t(v,Q_{ia}v')$. Moving $L_{ai}$ across the form contributes $-L_{ia}$ because $i,a$ have opposite signs. The right-factor operator $Q_{ia}$ commutes with $L_{ia}$, so moving both factors and summing gives $t(D_+v,v')=t(v,D_-v')$. Hermitian symmetry gives the reverse relation, and adding yields $t(Dv,v')=t(v,Dv')$ (`tform_D`).

The real part of $t(v,v)$ is $\sum_s\|x_s(v)\|^2$. If it vanishes then every coefficient is zero and the basis expansion $v=\sum_s x_s(v)\otimes b_s$ gives $v=0$. This is `tform_self_re_pos`. It follows that $t(Dz,Dz)=t(z,D(Dz))=0$ implies $Dz=0$. The entire proof takes place on the algebraic tensor domain. [Lean, read]

**Failure tests.** Let $N=\begin{pmatrix}0&1\\0&0\end{pmatrix}$ on $\mathbb C^2$. For the ordinary positive form one has $N^2e_2=0$ and $Ne_2=e_1$. The two symmetry pairings $\langle Ne_2,e_1\rangle$ and $\langle e_2,Ne_1\rangle$ are $1,0$. With $G=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and the Hermitian form $t_G(x,y)=\overline{x}^{\,t}Gy$, both $GN$ and $N^\dagger G$ are $\operatorname{diag}(0,1)$. Thus symmetry holds for $t_G$, while $e_1$ is nonzero and isotropic. These two examples isolate symmetry and positivity in the final inference. In the rank-two representation one can also test the scalar premise: use $W'=\mathbb C u_1$, $\lambda'=(5/2,-5/2)$ and $z'=u_1\otimes b_{21}$. The seed and tensor weights are $(3,-3)$ and $(2,-2)$. The compact and physical equations still hold, but the actual Casimir is $18-4-10=4$ and the required value is $12$. Directly $Dz'=4u_0\otimes1$. [Expository]

**Scope and consumers.** The proof takes the highest-weight and tensor-range components of line membership. The original interface retains physical membership and compact irreducibility. Zero tensors are included. If a sign block is empty, both Dirac sums are empty, including in rank zero. The nonzero witness is supplied separately by `line_exists` under $\mathrm{StrictAnti}(\lambda)$, the bracket and compact irreducibility. The existence proof is in §9.4.23. The degree range comes separately from `line_deg` in [§9.4.24](#9424-the-exterior-degree-of-the-physical-fock-highest-weight-line) (`TraceGap/SignedActionTensor.lean:70–118`). The Dirac inclusion uses `lineSub` and the Casimir condition. The degree range serves the parity calculation in the later supertrace.

In `GeneratedSubStable.lean:50–83` the ambient $M$ is a derived domain $D_0\le H$ of a unitary representation on a complete $H$. The derived action supplies the bracket and infinitesimal unitarity. The calls `line_exists hanti hE hV`, `line_ker hE hU hV hc hzL` and `line_deg hE hU hV hzL` use the same $V,\lambda$ and witness. The Dirac equation, $V\le\mathrm{genSub}(E,V)$ and physical membership give
$$
z\in KK=\ker D\cap\mathrm{tensFock}(\mathrm{genSub}(E,V))\cap\mathrm{physicalSubspace}(\epsilon).
$$
Compact stability puts the lowering span of $z$ in $KK$. The reverse inclusion in `ker_D_eq_kLowSpan` uses `lowestKType_casimir_cone`, `casimir_scalar_on_generated`, `khw_lowK_mem`, `highestWeight_uniqueness` and finite-layer exhaustion via `genSub_eq_iSup_layer`. The producer also takes group stability of $V$, integrality of $\lambda_a-(n-1)/2$, $\mathrm{StrictAnti}(\lambda)$, $\mathrm{GapAtLeast}(\epsilon,\lambda,h)$, $\mathrm{thrStar}(\epsilon)<h$ and both sign blocks nonempty. At line 191 the archive returns equality with the lowering span and its compact irreducibility. [Lean] The reverse inclusion and full kernel classification remain [Open] in this reading.

In `SupTrace.lean:75–87,195–215` the domain is the smooth one, and `arb_datum` and `casOnSmooth_of_isDS` supply $V$ and its scalar. The equality puts $KK$ in the finite trace layer $Y_0$ and transports parity from the degree field to all of $KK$. The call to `str_YY` takes the layer inclusion, parity equation and scalar on the generated module. `WKTensFockGenSub.lean:119` takes kernel equality and irreducibility. [Lean]

A uniform lower bound for $D^2$ on the orthogonal complement of the kernel would need control of all remaining compact weights and a uniform bound on their positive square scalars. The related `dirac_sharp` uses `Gap3` and `kernel_lemma` to exclude specified nonempty noncompact shifts by a negative square scalar. The estimate `casimir_gap_at_noncompact_weight` bounds the compact Casimir of the generated first factor under its own weight-gap premises. For a Dirac bound one still needs control of the diagonal tensor Casimir with the $r$ correction and an estimate or decomposition covering the complement. A Hilbert-space spectral statement also needs a closed realization and domain control. These are [Open] boundaries of this reading.

**Classical context.** Proposition 3.1 of Parthasarathy's 1972 article computes the square on equivariant twisted spinors over $G/K$ as a negative ambient Casimir plus a highest-weight scalar. The signed exterior model and its normalization here come from A2. [Paper] [Parthasarathy 1972, pp. 13–14](https://www.math.utah.edu/~ptrapa/math-library/parthasarathy-dirac-operator.pdf#page=14)

The reading is pinned to A2 SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Under `lean/src/ReciprocityTheory/ReductiveGroups/DiscreteSeries/` see `TraceGap/SignedActionTensor.lean:20–28,120–153`, `TensorRepresentations/CARUnit.lean:179–274`, `TensorRepresentations/CsqDdPt.lean:10–208` and `DiscreteSeriesExistence/SchSharpA.lean:13–138,200–204`. [A2](../sources/SOURCES.md#a2) · [Reading record](../sources/SOURCES.md#chapter-9-prv-extremal-component-and-dirac-kernel)

**How the degree proofs use these results.** [§9.4.26](#9426-recovering-the-formal-degree-constant-from-a-translation-ray) applies `thmFD` in `fdc_cd` with the recurrence supplied by `fdc_step` and with the lowest-type coefficient data supplied by `anyF`. The recurrence calls `fdeg_ratio_V` on the compact-dual Haar. The coefficient construction uses `equiv_sigLam_of_isDS`, and the choice of degree uses `isDS_props_of_gap`. Both go through `casOnDatum_of_isDS` and `casimir_eq_casVal_of_no`. The latter calls `lowFock_exists` at the original parameter, consuming the §9.4.23 tensor-range membership, nonvanishing and highest-weight equations to establish its own scalar Casimir. Its physical membership field is discarded. [Lean] (`FormalDegree/FdCons.lean:39–52`, `FormalDegree/FdConsA.lean:94–110,128–141`, `DiscreteSeriesExistence/RangeDatumEmbedding.lean:95–104`, `EquivSigLamOfIsDS.lean:32–54,65–83`, `CFPrime.lean:81–89`.)

In [§9.4.28](#9428-how-the-tensor-sandwich-determines-a-one-step-formal-degree-ratio), `fdeg_ratio_V` obtains the model ratio through `swC_main` and `cc_gk`. Inside `cc_gk` the two model scalars come from `datumV_casimir` on the smooth right-regular datum. The tensor occurrence starts with compact Pieri in [§9.4.21](#9421-compact-pieri-branching-and-the-tensor-step). The embedding, partial traces and Schur equality give the model ratio and eigenspace description. The two calls to `equiv_sigLam_of_isDS` in `swC_main` consume the §9.4.23 witness indirectly through the scalar route above, when transporting the numerical ratio to the caller's representations. The §9.4.25 inclusion `line_ker` is consumed by `ker_D_eq_kLowSpan` in the separate `supTrace` route. The cited degree-limit and tensor-ratio handoffs take neither that kernel equality nor the `line_ker` equation as an input. [Lean] (`TensorRepresentations/Sandwich.lean:17–26`, `SandwichA.lean:157–186`, `CcARatioZero.lean:108–141`, `OccBLowKShiftF.lean:72–89`, `DiscreteSeriesExistence/EqZeroOfDatumEmbeddingEqZero.lean:158–185`, `TraceGap/GeneratedSubStable.lean:79–81`, `SupTrace.lean:75–87,195–215`.)

**Review and scope.** The local proof reading is author-level R3. Same-source initial review R083 upheld the signed square, weight cancellation and kernel inclusion on the algebraic domain. Different-source review of this section is pending. [Source ledger](../sources/SOURCES.md#chapter-9-prv-extremal-component-and-dirac-kernel)

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

**The family and its consumers.** The function `fdcD` chooses an `IsDS` degree on $\mu_{\rm CD}$ at the parameter, with a zero fallback when no witness exists. `fdc_ds_exists` and `fdcGood_unique` supply existence and choice independence on the original gap domain. `fdc_step` chooses both representations and applies `fdeg_ratio_V` on the same Haar, then uses uniqueness at the target. The tensor argument in `Sandwich` supplies this ratio by the two-sided comparison in [§9.4.28](#9428-how-the-tensor-sandwich-determines-a-one-step-formal-degree-ratio). The [conditional ratio in §9.4.7](#947-formal-degree-ratios-under-a-shift-of-the-parameter) derived from `HCFdeg` takes the numerical formula as input. Its unused producer and `up_G` are distinct from the calls traced here. The unit-bound application in `linkS_all` takes its ratio from `AllHyp.s47`. This is the boundary of the previous ratio audit.

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

In §9.4.26 the translation-ray limit fixed the discrete-series formal degree $d(\lambda) = V(\lambda)/F_n$ on the explicit polar measure $d\mu_{\rm CD} = c_{p,q} J(z)\,dz\,dk$, and then passed that value to the global period and flag-measure consumers through `muCD_eq_cd_vol`. Abstract Haar uniqueness on $U(\varepsilon) \cong U(P,Q)$ cannot supply that step on its own: left invariance relates two Haar measures on a noncompact group only up to an unknown positive constant, and scaling the measure by $a > 0$ divides every Schur formal degree by $a$. Worse, the two measures are normalized on different compact groups and in different coordinate charts. The polar measure $\mu_{\rm Polar}$ uses probability Haar $dk$ on $K_\varepsilon \cong U(p) \times U(q)$ as the angular factor and integrates over flat noncompact coordinates $z \in \mathbb C^{pq}$, whereas the global Siegel and CM volume ties package a compact-dual family `CDHaar` that gives probability one to the *ambient* compact unitary group $U(P+Q)$ and transports normalization to $U(P,Q)$ by matching local exponential densities at the identity against the complexified Frobenius volume on $\mathfrak u(P,Q)$.

To prove that the prefactor $c_{p,q} = F_n / (\pi^{pq} F_p F_q)$ pays the exact ratio between these two normalizations, the archive computes three coordinate quantities from scratch and cancels them at the identity: first, the complexification Jacobian $\kappa_n = 2^{n(n-1)/2}$ comparing lower-triangular Lie coordinates with the intrinsic $\Omega$-Lebesgue measure on $\mathfrak u(P,Q)$; second, the Hurwitz–Macdonald volume $\mathrm{volU}(N) = 2^N \pi^{N(N+1)/2} / F_N$ of $U(N)$ via the complex QR Jacobian and matrix Gaussian integral; and third, the identity polar-to-exponential derivative showing that $J(z)\,dz\,dk$ has coordinate density $(\mathrm{volU}(p)\,\mathrm{volU}(q))^{-1}$. Multiplying by $c_{p,q} = \mathrm{volU}(p)\,\mathrm{volU}(q)/\mathrm{volU}(n)$ turns the product-block density into $\mathrm{volU}(n)^{-1}$, and dividing both sides by the same $\kappa_n$ matches the compact-dual $\Omega$-density across every legal sign-splitting chart.

**First worked example: $(P,Q)=(1,1)$ across ordered and swapped charts.** Take $n=2$ and $(P,Q)=(1,1)$, so $\dim_{\mathbb R}\mathfrak u(1,1) = 4$, $F_1 = F_2 = 1$, and $m = pq = 1$. In the ordered signature $\varepsilon = (+,-)$ on $\{0,1\}$, the sole strict-lower pair $(1,0)$ has opposite signs, so $|\mathcal C| = 0$, $|\mathcal N| = 1$, $\dim_{\mathbb R}\mathfrak k = 2$, and $\dim_{\mathbb R}\mathfrak p = 2$. Let us check the volumes, chart factor, and densities term by term.

On $\operatorname{Mat}_N(\mathbb C)$ the Gaussian integral $\int e^{-\operatorname{tr}(Z^\dagger Z)}\,dZ$ equals $\pi^{N^2}$. Under the QR decomposition $Z = k R$ with $k \in U(N)$ of probability Haar mass one and $R$ upper-triangular with positive real diagonal $t_0, \ldots, t_{N-1} > 0$, the Lebesgue Jacobian is a positive constant times $\prod_{j=0}^{N-1} t_j^{2(N-j)-1}$. For $N = 1$, $\int_0^\infty t_0 e^{-t_0^2}\,dt_0 = 1/2$ divides $\pi^1$ to give $\mathrm{volU}(1) = 2\pi$. For $N = 2$, writing $R = \begin{pmatrix} t_0 & u \\ 0 & t_1 \end{pmatrix}$ with $u \in \mathbb C$, the triangular Gaussian integral is
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

Left or right multiplication by $g \in \mathrm{GL}_N(\mathbb C)$ on $\operatorname{Mat}_N(\mathbb C)$ has complex determinant $(\det g)^N$ and real determinant $|\det g|^{2N}$, making $\mathrm{gmMeas}(N) = |\det Z|^{-2N}\,dZ$ bi-invariant (`LeftMulMapEqTransposeConj.lean:43–154`). On `TriCo N`, right multiplication by $R_0 = \mathrm{upMat}(t_0) = U_0 \operatorname{diag}(d_0,\ldots,d_{N-1})$ factors into unipotent right multiplication `rmulL U_0`, whose difference from the identity is nilpotent so $\det_{\mathbb R}(\mathrm{rmulL}\,U_0) = 1$, followed by `scaleL d`, which scales column $j$'s real diagonal by $d_j$ and its $j$ strict-upper complex entries by $d_j$ (real factor $d_j^2$ each), giving $\det_{\mathbb R}(\mathrm{scaleL}\,d) = \prod_{j=0}^{N-1} d_j^{2j+1}$ (`TriHaarA.lean:95–183`). Thus $\mathrm{triMeas}(N) = (\prod_{j=0}^{N-1} t_{1,j}^{-(2j+1)})\,dt$ is right-invariant on `triPos N` (`TriHaar.lean:52–109`). Pulling $\mathrm{gmMeas}(N)$ back under `qrMap` and applying Haar uniqueness first on compact $U(N)$ and then on the opposite triangular group `TG N` identifies the pullback as $\mu_N \times (C\,\mathrm{triMeas}(N))$ for a constant $C \ge 0$ (`TriUniq.lean:113–256`, `QRHaarA.lean:181–312`). Restoring $|\det(k\,\mathrm{upMat}\,t)|^{2N} = \prod_{j=0}^{N-1} t_{1,j}^{2N}$ yields the QR density $C\prod_{j=0}^{N-1} t_{1,j}^{2(N-j)-1}$.

Evaluating this QR integral at $f(Z) = e^{-\operatorname{tr}(Z^\dagger Z)}$ gives $\pi^{N^2}$ on the left and, by unitary invariance $\operatorname{tr}((kR)^\dagger(kR)) = \sum_j t_{1,j}^2 + \sum_{a<b} |t_{2,ab}|^2$,
$$
C \cdot 1 \cdot \pi^{N(N-1)/2} \prod_{j=0}^{N-1} \int_0^\infty r^{2(N-1-j)+1} e^{-r^2}\,dr
= C\,\pi^{N(N-1)/2} \prod_{m=0}^{N-1} \frac{m!}{2}
= C\,\frac{\pi^{N(N-1)/2} F_N}{2^N}
$$
on the right, forcing $C = 2^N \pi^{N(N+1)/2} / F_N = \mathrm{volU}(N)$ (`GaussA.lean:60–116`, `GaussB.lean:33–115`, `LintegralGaussTri.lean:35–86`). Near $(0,0) \in \mathrm{UCo}(N) \times \mathrm{TriCo}(N)$, the map $\mathrm{chartWR}(x,t) = \exp(\mathrm{skMat}\,x)(I_N + \mathrm{upMat}\,t)$ has strict derivative $\mathrm{lamE}(x,t) = \mathrm{skMat}\,x + \mathrm{upMat}\,t$ (`ChartWRB.lean:39–72`). Because $(\mathrm{skMat}\,x + \mathrm{upMat}\,t)_{ab} = t_{2,ab} - \overline{x_{2,ba}}$ for $a < b$, `lamE` is the composition of a unipotent shear in the upper entries with a coordinate permutation, hence preserves Lebesgue measure ($|\det_{\mathbb R}(\mathrm{lamE})| = 1$, `ChartWRA.lean:109–184`, `ChartWR.lean:15–89`). Comparing `chartWR(B_r × ball(0,ρ))` with `qrMap(exp(skMat B_r) × ball(I,ρ))` where the QR weight tends to $1$, and canceling $0 < \mathrm{volume}(\mathrm{ball}(0,\rho)) < \infty$, yields $\mu_N(\exp(\mathrm{skMat}\,B_r))/\mathrm{volume}(B_r) \to \mathrm{volU}(N)^{-1}$ (`VolUDensity.lean:16–137`). Dividing by $\kappa_N$ from Lemma 1 gives `OmegaDensity (cd.cd N 0) (cOmega N)`, and `cd.trick P Q` with uniqueness in Lemma 1 transfers $c_\Omega(P+Q)$ to `cd.cd P Q` (`BridgeA.lean:64–336`, `Bridge.lean:28–37`).

**Proof of Lemma 3.** Using the local matrix logarithm inverse to $\exp$ near $I_n$, the translated map $y \mapsto \log(\exp(-x)\exp(x+y))$ has derivative $\mathrm{id}$ at $(x,y)=(0,0)$ in the $y$ variable, and that derivative varies continuously near $(0,0)$. The resulting uniform local error estimate implies that the pullback of left-invariant $\mu_{\rm Polar}(\varepsilon)$ to $\mathrm{GCo}(\varepsilon)$ satisfies $(1-\delta)$-quasi-translation invariance near $0$ (`HaarExpB.lean:68–321`). Besicovitch differentiation on the finite-dimensional real vector space $\mathrm{GCo}(\varepsilon)$ then produces a positive finite exponential density $d > 0$ (`HaarExpA.lean:84–244`, `HaarExp.lean:19–91`). Next, the polar-to-exponential transition $\mathrm{Lm}(w,z) = \mathrm{cLin}(\varepsilon)(\log(\exp(\mathrm{kMat}\,w)\exp P(z)))$ satisfies $\mathrm{Lm}(0,0) = 0$ and has strict Fréchet derivative $\mathrm{id}_{\mathrm{GCo}(\varepsilon)}$ at $(0,0)$ by the chain rule on $d(\exp)_0 = \mathrm{id}$, $d(\log)_I = \mathrm{id}$, and matrix multiplication at $(I_n, I_n)$ (`HaarPolB.lean:85–147`). Shrinking polar balls are therefore sandwiched between $(1\mp\delta)$-rescaled exponential balls, giving $\mu_{\rm Polar}(\varepsilon)$ the same density $d$ on polar sets (`HaarPol.lean:14–94`).

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

Author-level local R3 covers `OmegaDensityUnique`, the entire `FormalDegree/HaarVolumes/` directory, `VolUFactProdMulLe`, `DataCD`, `HaarDensityNeZero`, `SignSplitEquivInl`, and the four direct consumer bridges listed above. [Polar Haar invariance (§9.4.6)](#946-polar-haar-measure-and-the-discrete-series-integrability-bound) and the translation-ray calibration (§9.4.26) are consumed at their previously recorded scope, while universal `LowestKTypeMultiplicity.HCFdeg`, `AllHyp.s47`, full `GoodS` construction, and `Main` call-graph reachability remain unchanged. Community Lean kernel replay, same-source initial review, different-source mathematical audit, and peer review of the RH argument are accounted separately. [Source and verification record](../sources/SOURCES.md#chapter-9-compact-dual-coordinate-density-and-haar-normalization)

---

### 9.4.28 How the tensor sandwich determines a one-step formal-degree ratio

A translation ray needs a recurrence before its limiting calculation can determine a constant. The step in [§9.4.26](#9426-recovering-the-formal-degree-constant-from-a-translation-ray) compares two discrete-series representations on one Haar measure. Its source is a tensor projection. Tensoring with the defining representation gives an upper bound for the forward degree ratio. Tensoring back with the dual gives an upper bound for the reciprocal, so both bounds are attained. The compact-dual density of [§9.4.27](#9427-paying-the-shared-compact-dual-haar-normalization-from-coordinate-densities) is a separate input to the calibration. [Lean, read]

**Two examples.** Use zero-based indices and keep the sign vector fixed. On $U(1,1)$ take $\varepsilon=(+,-)$, $\mu=(101/2,1/2)$, $s=0$, and $h=50$. The coordinates minus $1/2$ are integers. The source gap is $50$ and the two shifted gaps are $51$ and $49$, both at least $h-1$. All three parameters strictly decrease. Here the threshold plus one is $33+8\sqrt2<45$ since $\sqrt2<3/2$. The lowest compact weights are $(51,0)$, $(52,0)$ and $(50,0)$, respectively, since $\rho_C=0$ and $\rho_N=(1/2,-1/2)$. The defining step has $\operatorname{ratioV}(\mu,0)=51/50$ and the return has ratio $50/51$. The dual step from the same source has ratio $49/50$ and its defining return has $\operatorname{ratioV}=50/49$. Both return applications can use $h=49$. By §9.4.26 the degrees on $\mu_{\mathrm{CD}}$ are $50,51,49$, so on the single measure $\nu=2\mu_{\mathrm{CD}}$ they are $25,51/2,49/2$. The two products of forward and return ratios are one. [Expository]

On $U(2,1)$ choose the interleaved signature $\varepsilon=(+,-,+)$, $\mu=(140,65,0)$, $s=1$, and $h=65$. The lattice offset is $1$, and the ordered gaps $(01,02,12)$ are $(75,140,65)$, $(74,140,66)$ and $(76,140,64)$ for the source, defining step and dual step. The first and last gaps are noncompact. The threshold plus one is $49+8\sqrt2<61$, so $h-1=64$ also works as the source height for each return. All parameters strictly decrease. Both half-sums are $(1/2,0,-1/2)$, so the three lowest compact weights are the parameters themselves. For the defining step the two factors using slot $1$ are $(-74)/(-75)$ and $66/65$. For the dual step they are $(-76)/(-75)$ and $64/65$. Thus the defining and dual ratios are $4884/4875=1628/1625$ and $4864/4875$. At the defining target the dual return has factors $(-75)/(-74)$ and $65/66$, giving $4875/4884$. At the dual target the defining return has factors $(-75)/(-76)$ and $65/64$, giving $\operatorname{ratioV}=4875/4864$. The compact root $02$ contributes $140$ at each endpoint. The inherited compact-dual degree formula gives $140\cdot4875/2=341250$, $140\cdot4884/2=341880$, and $140\cdot4864/2=340480$. On $\nu=2\mu_{\mathrm{CD}}$ the degrees are $170625,170940,170240$, with the same four ratios. In both examples the gapped model supplies give the original $\operatorname{IsDS}$ witnesses at all three parameters. The selected compact highest-weight vectors can be taken to be unit vectors. The numerical degrees here use the previously calibrated formula. [Expository]

**Definitions and the unit-step theorem.** Write $G=\mathrm{UJ}(\varepsilon)$ for the archive's group preserving $J_\varepsilon=\operatorname{diag}(\pm1)$, and $\mu_G=\texttt{Formalism.REAL.muG}\ \varepsilon$ for its fixed Haar measure. Let $p,q$ count the signs and $q_0=\min(p,q)$. The condition $\operatorname{GapAtLeast}(\varepsilon,\mu,h)$ requires $h\le|\mu_i-\mu_j|$ for every pair of opposite signs. A Harish–Chandra parameter is strictly decreasing with $\mu_i-(n-1)/2\in\mathbb Z$ at every index. Put
$$
\begin{aligned}
T_\varepsilon&=\max\{npq+1,\ 16nq_0+8\sqrt{2q_0}\},\\
\mu'&=\operatorname{shiftF}(b,\mu,s)=\mu+\delta_b e_s,\qquad
\delta_{\rm false}=1,\quad\delta_{\rm true}=-1,\\
R_b(\mu,s)&=\operatorname{ratioF}(b,\mu,s)=
\prod_{i\ne s}\frac{\mu_s+\delta_b-\mu_i}{\mu_s-\mu_i}.
\end{aligned}
$$
Here $T_\varepsilon$ is `thrStar`. The branches of $R_b$ are `ratioV` and `ratioVd`, respectively. The tensor actions are on the defining module and its algebraic dual. Both actions keep the same group, sign vector and coordinate index. [Lean, read] (`IsInfUnitary.lean:88–96`, `PsiExistsStatement.lean:44–47`, `Transported.lean:9–11`, `HidaSetting.lean:15–31`, `Residue.lean:11–15`.)

**Lemma (one unit shift on a common Haar measure).** Fix any $n$, $\varepsilon$, $\mu$, real $h$, $s\in\operatorname{Fin}n$ and Boolean $b$. Assume $p,q\ge1$, $\operatorname{IsHCParam}(\mu)$, $\operatorname{GapAtLeast}(\varepsilon,\mu,h)$, $T_\varepsilon+1<h$ and $\operatorname{StrictAnti}(\mu')$. Let $\sigma,\sigma'$ act on complex inner product spaces and satisfy the archive's $\operatorname{IsDS}(\varepsilon,\mu,\sigma)$ and $\operatorname{IsDS}(\varepsilon,\mu',\sigma')$. For one Haar measure $\nu$ on $G$, if $\operatorname{IsFdeg}(\nu,\sigma,d)$ then $\operatorname{IsFdeg}(\nu,\sigma',d R_b(\mu,s))$. The $\operatorname{IsDS}$ predicates include completeness, nontriviality, continuous unitary irreducibility, square-integrable coefficients on $\mu_G$, and a lowest compact type of the specified weight and minimal shifted norm. The $\operatorname{IsFdeg}$ predicate includes positivity and the integrable four-vector Schur identity. In the defining direction the lemma is `fdeg_ratio_V`. [Lean, read] (`SandwichA.lean:141–186`, `Sandwich.lean:17–26`, `RelevantZeroGramTerms.lean:30–76`.)

**Proof, from shift to model.** The new difference between any two coordinates changes by $0$ or $\pm1$. The reverse triangle inequality therefore gives the original opposite-sign gap test with $h-1$ at the target. The two thresholds used for the models are $T_\varepsilon<h$ and $T_\varepsilon<h-1$. The shifted coordinate still lies in the required lattice, and the separately assumed strict decrease completes $\operatorname{IsHCParam}(\mu')$. In particular the two lists of coordinates are injective. The gap condition ranges only over opposite signs and cannot by itself certify the behavior of adjacent coordinates of the same sign. [Lean, read] (`SandwichA.lean:96–160`.)

For each endpoint $\lambda$, `HW.kType_exists` gives a compact type $T$ of weight $\operatorname{lowK}(\varepsilon,\lambda)$ with unit vector $v_0=T.w$. In `swA_model`, `S7.exists_mu` gives the auxiliary integer tuple $m$ for this endpoint and the kernel is $\Psi=\texttt{PsiM}\,T\,m$. The $npq+1$ bound gives `StdGap`, which consists of strict ordering and a gap witness strictly above $npq+1$. The other threshold implies the ordinary $L^2$ condition at $8nq_0$ and the weighted estimate at $8nq_0+8\sqrt{2q_0}$. The named equivariance, identity, smoothness, Casimir and ordinary $L^2$ supplies give `IsPsiFor`. The exponential formula gives positivity on $\exp(\mathfrak p_\varepsilon)$, `weighted_datum` gives $L^2(\mu_G)$ for every generated matrix coefficient multiplied by $\sqrt{\texttt{hs}(g)}$, and `hasGelfandChar_sigLam` gives the Gelfand character on that same generated space. Here `hs` is the squared Frobenius norm. Write $D$ for the smooth right-regular domain, $E$ for its derived action and $M,M'$ for the two algebraic spaces `genSub` from the lowest-type data `datumV`. Their closures carry the two `sigLam` models. The unit seed vectors are nonzero. The model nontriviality supplied by `isDS_sigLam` also provides nonzero test vectors in both closures for `fdegOf`. [Lean, read] (`SandwichA.lean:24–56,150–169`; deeper kernel, estimates and model existence enter by the named calls.)

**Proof, the tensor projection and its trace.** On $M^n=\texttt{tensSub}(M)$ write $A=\texttt{eeF}(b,E)$ and $z_s=\delta_b\mu_s+(1-n)/2$. The nonzero occurrence used in `occ_exists` starts with the compact Pieri map into the defining or dual tensor. The compact weight shifts by the same $\delta_b e_s$ because the two root half-sums depend only on $\varepsilon$. Positivity gives a strictly positive trace of the compressed kernel pairing. If all pairings with the fixed nonzero seed of the target vanished, compact equivariance would spread this vanishing to the whole target compact type, contradicting that trace. The resulting nonzero $L^2$ pairing gives a nonzero map to $M'$ by projecting the tensor coefficient onto the target model. The algebraic adjoint construction gives an injective $(\mathfrak g,K)$-map $\iota:M'\to M^n$ on the indicated generated spaces. On its image the tensor Casimir is the target Casimir. The tensor identity $C_{\rm tensor}=C_{\rm source}+n+2A$ and the shift identity $\operatorname{casVal}(\mu')-\operatorname{casVal}(\mu)=n+2z_s$ put the image in the $z_s$ eigenspace. [Lean, read] (`CoefEmbed.lean:49–68`, `OccBLowKShiftF.lean:72–89`, `OccCExistsPs.lean:66–end`, `OccDAdj.lean:145–155`, `OccDTensKStable.lean:51–76`.)

The weighted tensor unitarization supplies a positive form for the spectral decomposition. On a finite-dimensional invariant subspace containing the tensor of the lowest type, symmetry gives a polynomial annihilator with distinct real roots. Commutation with the tensor derived action propagates that polynomial identity to all of $M^n$. Interpolation then gives an idempotent $P$ for $z_s$, fixing that eigenspace and annihilating the other eigenspaces. If $z_s$ is absent the interpolating projection is zero. For the trace calculation there is also the signed form
$$
 B(f,f')=\sum_i J_{\varepsilon,ii}\langle f_i,f'_i\rangle.
$$
The operator $A$ is symmetric for $B$. Distinct real eigenspaces are $B$-orthogonal by $(a-a') B(f,f')=0$ on vectors of eigenvalues $a,a'$. Hence $P$ is $B$-symmetric and $P\iota=\iota$. [Lean, read] (`Decomp.lean:14–76`, `DecompA.lean:91–120,138–212`, `TraceFormula.lean:223–288`.)

For a tensor endomorphism $Q$, $\operatorname{ptr}Q$ is the sum of its diagonal slot maps. Commutation and the scalar endomorphism lemma make $\operatorname{ptr}P_a=c_a I$ on $M$ for each spectral projection. For each integer $k\ge0$, compare $\operatorname{ptr}A^k$ by the spectral decomposition and by the Gelfand character. The former gives $\sum_a c_a a^k$, and the latter gives $\sum_i r_i z_i^k$ where
$$
r_i=\prod_{j\ne i}\frac{z_i-z_j+1}{z_i-z_j}.
$$
The character side uses the coefficient of $X^{k+1}$ in $\prod_i(1+X/(1-z_iX))-1$. Its expansion into $\sum_i r_i X/(1-z_iX)$ follows by repeatedly using $g_j-g_i=(z_j-z_i)g_jg_i$ for $g_i=X/(1-z_iX)$. A nonzero vector in $M$ lets us equate the scalar coefficients. Evaluating the polynomial which is one at $z_s$ and zero at every other point in the union of the two finite sets isolates the mass there. The injectivity of the $z_i$ gives $\operatorname{ptr}P=R_b(\mu,s)I$. For the dual branch, $z_i-z_j=-(\mu_i-\mu_j)$ accounts for the minus sign in the numerator. [Lean, read] (`PtrScalar.lean:158–166`, `Residue.lean:17–117`, `Resolvent.lean:59–97`, `PoleMatchA.lean:72–156`, `MomentMatch.lean:9–46`, `PoleMatch.lean:13–39`.)

**Proof, the Schur bound and its equality case.** Let $d_1,d_2>0$ be the model degrees on $\mu_G$. Fix a nonzero $y$ in the source lowest type inside $M$, distinct in role from the test vectors used for `fdegOf`. The map $\Phi_y=\texttt{tfPh}$ assigns to a tensor its vector of coefficients against the single-slot vectors $e_i\otimes J_{\varepsilon,ii}y$ in the tensor action. It takes values in $L^2(G,\mu_G)^n$ with the coordinatewise right regular action $\rho$. Write $J$ for the sign operator on that Hilbert space. Pointwise preservation of the signed form by the defining or dual group matrix, followed by source Schur orthogonality, gives
$$
 \langle \Phi_y(f),J\Phi_y(f')\rangle
 = B(f,f')\frac{\|y\|^2}{d_1}.
$$
Taking $f$ to be the coordinatewise sign change of $f'$ shows that $\Phi_y(f')=0$ forces the sum of the squared norms of all slots of $f'$ to be zero. Thus $\Phi_y$ is injective on $M^n$. Weighted integrability ensures that the coefficients used here are genuine $L^2$ classes. [Lean, read] (`TraceFormulaC.lean:94–127`, `TraceFormulaD.lean:30–72`, `TraceFormulaF.lean:96–125`, `TraceFormulaI.lean:11–53`.)

Let $H_P$ be the closed span of $\Phi_y(PM^n)$ and let $H'$ be the closure of $\Phi_y(\iota M')$. The first is $\rho$-invariant by the coefficient intertwining on the smooth domain. Specifically the projected tensor of the lowest type is finite dimensional, is stable under the compact derived operators, and has one Casimir scalar $\operatorname{casVal}(\mu)+n+2z_s$. Its generated space is the image of $\Phi_y P$, so the archive's stable-closure lemma applies. The image of the target lowest type under $\Phi_y\iota$ is nonzero, has the same compact type and Casimir as the target, and generates the image of $M'$. The model equivalence and Schur transport give degree $d_2$ on $H'$. It is contained in $H_P$ since $P\iota=\iota$. [Lean, read] (`TraceFormulaG.lean:71–191`, `TraceFormulaM.lean:12–88`, `TraceFormula.lean:168–209`.)

Set $N=\|y\|^2$, $\kappa=d_1/N$, $u_i=\Phi_y(P(e_i\otimes y))$, and $W_i=\kappa\,\operatorname{proj}_{H_P}Ju_i$. The coefficient representation and trace identity are
$$
 v_i(g)=\langle W_i,\rho(g)v\rangle\quad\text{a.e. for }v\in H_P,
 \qquad
 \operatorname{ptr}P=\frac{\sum_i\|W_i\|^2}{d_1}I.
$$
For the first identity, $J\Phi_y(\eta-P\eta)$ is orthogonal to $H_P$ by the signed Schur formula and $B$-symmetry of the idempotent. Taking $\eta=e_i\otimes y$ in the formula, using right translation on $\Phi_y(Pf)$, replacing the test $\eta$ by $P\eta$ and cancelling $N/d_1$ gives the coordinate identity on generators. It extends linearly, then to the closure via an $L^2$-convergent sequence with an almost-everywhere convergent subsequence in each coordinate. For the second identity, write $\operatorname{ptr}P=rI$. Pairing its diagonal slots against $y$ and using $P^2=P$ and signed symmetry gives $rN=\sum_i J_{\varepsilon,ii}\langle u_i,W_i\rangle$. Inversion invariance of $\mu_G$, the coordinate identity, unitarity and $J\rho=\rho J$ transpose the two slot indices with conjugation:
$$
 \langle (u_i)_j,(W_i)_j\rangle
 =\overline{\langle (u_j)_i,(W_j)_i\rangle}.
$$
Indeed after $g\mapsto g^{-1}$ both coefficient factors transpose by moving $\rho(g)$ to the other argument. For the factors involving $u_i$, move the orthogonal projection and $J$ as well, using invariance of $H_P$. Summing with the signs gives $\sum_i\overline{\langle Ju_i,W_i\rangle}=\sum_i\|W_i\|^2/\kappa$. Cancelling $N$ gives the stated trace identity. This step converts the signed trace calculation to a sum of ordinary squared Hilbert norms. [Lean, read] (`TraceFormulaH.lean:11–284`, `TraceFormulaF.lean:20–66`, `TraceFormulaB.lean:9–30`.)

Project $W_i$ orthogonally onto $H'$, writing $W_i'= \operatorname{proj}_{H'} W_i$. For a nonzero $v\in H'$, invariance lets $W_i'$ replace $W_i$ in the coordinate identity. Integrating its squared modulus gives $\|v_i\|^2=\|W_i'\|^2\|v\|^2/d_2$. Sum over $i$ and cancel $\|v\|^2$ to obtain $\sum_i\|W_i'\|^2=d_2$. Pythagoras then gives the exact bound with its nonnegative remainder
$$
 R_b(\mu,s)=\frac{d_2}{d_1}+
 \frac{\sum_i\|W_i-W_i'\|^2}{d_1}.
$$
If equality holds, each $W_i$ belongs to $H'$. For $v\in H_P$, the residual $v-\operatorname{proj}_{H'}v$ has every coordinate zero almost everywhere by the same coefficient representation and invariance of $H'$. This gives $H_P=H'$. To recover equality on the algebraic domain, put any $f\in M^n$ in a finite-dimensional $K$-stable subspace of $M^n$. Its image under $\Phi_y P$ is finite-dimensional and $K$-stable in $H'$. The target $K$-finite recovery lemma `data_kfin_le` puts that image in the generated space of the target datum. Write $\Phi_y(Pf)=\Phi_y(\iota x)$ there with $x\in M'$, and use injectivity to obtain $Pf=\iota x$. In particular a $z_s$ eigenvector, which $P$ fixes, already belongs to the image on the generated domain. [Lean, read] (`TraceFormulaJ.lean:9–85`, `TraceFormula.lean:129–221`, `TraceFormulaM.lean:90–148`.)

**Proof, returning in the dual direction.** Run the same construction starting at $\mu'$ with Boolean $\neg b$ and index $s$. It uses the primed weighted coefficient and Gelfand data, the two original model thresholds in reversed order, and the opposite tensor. It recovers $\mu$ because the increments have opposite signs. The second bound is $d_1/d_2\le R_{\neg b}(\mu',s)$. For every $i\ne s$, the forward numerator is the backward denominator and the forward denominator is the backward numerator. Both are nonzero, hence $R_b(\mu,s)R_{\neg b}(\mu',s)=1$. Since $d_1,d_2$ are positive, the two bounds give
$$
 R_b(\mu,s)\le\frac{d_2}{d_1}\le R_b(\mu,s).
$$
The result fixes the ratio and triggers the equality case just proved. The proof of `cc_gk` returns both the algebraic eigenspace description and the ratio. [Lean, read] (`CcARatioZero.lean:26–67,82–141`, `Residue.lean:219–235`.)

**Proof, transport to the caller's Haar measure.** The two gapped model equivalences give equivariant complex linear isometries from the models to $\sigma,\sigma'$ respectively. On the identical $g\in G$ they preserve each four-vector matrix coefficient and inner product, so Schur's full identity pulls back on the source and pushes forward on the target. Haar uniqueness gives $\nu=c\mu_G$ with $c>0$ on the fixed $G$. A change of measure multiplies each coefficient integral by $c$, giving model degrees $d_1/c$ and $d_2/c$. For a nonzero test vector $w$ the diagonal integral is $\|w\|^4/d$, so the pulled-back input degree $d$ equals $d_1/c$. The same $c$ therefore gives $dR_b=(d_1/c)(d_2/d_1)=d_2/c$. Pushing forward proves the four-vector target identity. [Lean, read] (`SandwichA.lean:58–94,167–186`, `FdegTransfer.lean:14–23,40–58`.)

**Remarks.** At $h=T_\varepsilon+1$ the bound on the target supplied by the shift is only $h-1=T_\varepsilon$. The invocation of `swA_model` there needs a strict inequality. A separate larger gap witness can rescue a particular pair. With the large-gap threshold omitted entirely, take $(5/2,1/2)$ on $(+,-)$ with $h=2$, and add at slot $1$. The target $(5/2,3/2)$ is still regular on the same lattice, but its gap $1$ cannot supply even the target `StdGap` witness above $3$. With the strict ordering of the target omitted, take $\varepsilon=(+,+,-)$, $\mu=(70,69,0)$, $h=69$ and add at slot $1$. The mixed gap remains at least $68$, but the target is singular, the forward factor at $0$ is zero and the reverse denominator there is zero. These diagnose failures of the indicated proof steps. At $\nu=0$ any nonzero test vector has zero diagonal integral, contradicting the positive-degree Schur identity, so this deletion also destroys the input degree witness. If two different positive measures are used instead, the true ratio acquires the factor $c_{\mathrm{source}}/c_{\mathrm{target}}$. For instance the rank-two step from $\mu_{\mathrm{CD}}$ to $2\mu_{\mathrm{CD}}$ gives $51/100$ instead of $51/50$. [Expository]

The actual degree consumer `fdc_step` calls `fdeg_ratio_V` with $\nu=\mu_{\mathrm{CD}}$ and additionally requires gap at least $h$ at both endpoints for its existence and choice-independence steps. Other direct consumers of `cc_gk` use its algebraic result. `cns_term` uses surjectivity onto the eigenspace, `cns_ofSum_core` uses the embedding, and `regular_term_bound` uses the embedding and the full eigenspace identification in `form_cc`. [Lean, read] (`FormalDegree/FdConsA.lean:128–141`, `ConsumerA.lean:139–153`, `ConsumerB.lean:127–140`, `InfinitesimalDecay/SquareIntegrableGeneratedVectors.lean:125–136`.)

Gould's characteristic-matrix calculation already gives the two algebraic trace products. In his notation the matrices are $(E_{ij})$ and $(-E_{ji})$, so they correspond to the archive's dual and defining operators after a sign change in each case. His roots $\alpha_i=\lambda_i+n-i$ in one-based indexing are the Harish–Chandra coordinates plus a common shift when $\lambda$ here denotes his highest weight. That common shift cancels in each factor of the trace products on p. 408. [Paper] [Gould, §§2–3, pp. 403–408](https://doi.org/10.1017/S1446181100001784)

Harish-Chandra's discrete-series degree formula already gives the numerical ratio as the quotient of all positive-root products with the same Haar normalization. Atiyah–Schmid's Theorem (8.1) gives that formula for the finite-center semisimple group with compact Cartan and a regular shifted-lattice parameter. On $SU(p,q)$ subtract the coordinate mean to represent restriction of the parameter. The integral character part and half-root sum both restrict to the compact torus there. The root values are still $\mu_i-\mu_j$. The pushforward under $U(1)	imes SU(p,q)	o U(p,q)$ of probability Haar on the circle times a fixed Haar on the semisimple group gives one Haar measure for both representations. The scalar central character cancels in coefficient products, and the restriction is irreducible because the product map is onto. This keeps the degree ratio on passing to $U(p,q)$. Their §8 also gives a finite-dimensional and dual translation precedent in the form of a character comparison using an extremal finite-dimensional weight, with the specific scaling $\lambda\mapsto m\lambda$ in (8.10). Zuckerman's appendix gives the dominant integral translation functors and their composition. The numerical recurrence is thus a classical specialization. The archive's signed partial-trace and Schur equality argument explains how its own local consumer obtains it. [Paper] [Harish-Chandra, §37 and Theorem 16](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6013-11511_2006_Article_BF02392813.pdf) · [Atiyah–Schmid, pp. 41–47](https://www.math.utah.edu/~ptrapa/math-library/schmid/atiyah-schmid.pdf#page=41) · [Zuckerman, pp. 493–495](https://www.math.stonybrook.edu/~aknapp/pdf-files/annals1982.pdf) · [Source ledger](../sources/SOURCES.md#chapter-9-unit-shift-tensor-sandwich)

The seed integrability used by both tensor directions is proved in [§9.4.29](#9429-polar-bounds-for-the-weighted-psim-kernel). [Open] Model existence and equivalence, the separate Casimir and Gelfand supplies, and the domain and stability suppliers enter through the named calls. The [conditional ratio from `HCFdeg`](#947-formal-degree-ratios-under-a-shift-of-the-parameter) has its own audit and consumer boundary. Separate open checks concern the full `GoodS` supply, universal `HCFdeg`, `AllHyp.s47` and declaration-level reachability from `Main`. [Community] Public archive replay reports remain independent of the local source reading. [Community verification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)

### 9.4.29 Polar bounds for the weighted PsiM kernel

The tensor comparison in [§9.4.28](#9428-how-the-tensor-sandwich-determines-a-one-step-formal-degree-ratio) uses genuine $L^2$ classes in both directions. A matrix in the defining or dual tensor factor can grow in the noncompact directions. Its entries are controlled by the Frobenius norm. The analytic input therefore bounds the seed after multiplication by that norm and accounts for the growth of Haar volume. [§9.4.28](#9428-how-the-tensor-sandwich-determines-a-one-step-formal-degree-ratio)

**Two examples.** Use the original parameters of §9.4.28. Let $t$ be the Euclidean norm of the complex off-diagonal block in the noncompact logarithm, and put $u=\cosh t$. On $U(1,1)$ take $\varepsilon=(+,-)$, $\lambda=(101/2,1/2)$ and $h=50$. The compact and noncompact half-sums are $0$ and $(1/2,-1/2)$. The lowest compact type is the character of weight $(51,0)$ and the shifted integer tuple is $\mu=(51,0)$. The logarithm has eigenvalues $t,-t$ and the leading minors of its exponential are $u,1$. Compact conjugation leaves the minors fixed, and the projection in the one-dimensional type is the identity. The kernel norm is $u^{-51}$ and the squared Frobenius norm of the group matrix is $4u^2-2$. The actual Haar density is $\sinh(2t)/(2t)$ times the flat radial element $2\pi t\,dt$ and the measure scale $a_\nu>0$. Substituting $u=\cosh t$ gives $2\pi a_\nu u\,du$ on $[1,\infty)$. On this one Haar measure the $L^1$ integral, squared $L^2$ norm, and weighted integral at $s=2$ are
$$
\frac{2\pi a_\nu}{49},\qquad
\frac{2\pi a_\nu}{100},\qquad
2\pi a_\nu\left(\frac4{98}-\frac2{100}\right).
$$
These are integrals of $u^{-50}$, $u^{-101}$ and $4u^{-99}-2u^{-101}$ times $2\pi a_\nu$. The archive tests hold since $50>32$ and $50>16+8\sqrt2$. [Expository]

On $U(2,1)$ choose $\varepsilon=(+,-,+)$, $\lambda=(140,65,0)$ and $h=65$. The mixed gaps are $75$ and $65$. Both root half-sums are $(1/2,0,-1/2)$, so the lowest compact weight is $(140,65,0)$ and $\mu=(141,65,-1)$. The compact type is $\operatorname{Sym}^{140}(\mathbb C^2)$ on the positive block and the weight-$65$ character on the negative block. In the original order the noncompact logarithm is
$$
X=\begin{pmatrix}0&b_0&0\\ \overline{b_0}&0&\overline{b_2}\\0&b_2&0\end{pmatrix}.
$$
For $t^2=|b_0|^2+|b_2|^2>0$, the eigenvalues are $t,0,-t$ and $X^3=t^2 X$. The exponential is $I+(\sinh t/t)X+((u-1)/t^2)X^2$. Put $x=|b_0|^2/t^2$. The first minor is $A=1+(u-1)x$. The second is $uA-(u^2-1)x=1+(u-1)(1-x)=D$. The full determinant is $1$. The scalar in the compact average is $A^{-76}D^{-66}$. Since $AD=u+(u-1)^2x(1-x)\ge u$ and $A\ge1$, the kernel norm is at most $u^{-66}$ after normalized positive averaging, uniformly in the angle. At $t=0$ the norm is $1$. [Expository]

For an exact radial expression, take $b=(t,0)$, since compact conjugation acts transitively on the $b$ of fixed length and preserves the kernel norm. The average is diagonal in the normalized monomials of bidegree $(140-j,j)$, by invariance under the diagonal phases. The squared component of the rotated highest unit vector in that monomial is $\binom{140}{j}x^{140-j}(1-x)^j$. Here $x$ is uniform on $[0,1]$: a uniform complex unit vector is a normalized pair of independent complex Gaussians, and the ratio of the first squared norm to their sum is uniform by changing variables in the product of two exponential densities. Thus the norm is the maximum over $0\le j\le140$ of the positive diagonal entries
$$
141\binom{140}{j}\int_0^1 \frac{x^{140-j}(1-x)^j}{(1+(u-1)x)^{76}(1+(u-1)(1-x))^{66}}\,dx .
$$
The factor $141$ is the dimension of the type, and integrating the same numerator against $dx$ with the denominator set to $1$ gives $1$ after this normalization. [Expository]

The three spectral differences give $J=\sinh(2t)/(2t)\cdot(\sinh t/t)^2$. Multiplying by the flat radial element $2\pi^2t^3dt$ gives the Haar pushforward $2\pi^2 a_\nu u(u^2-1)\,du$. Here the original squared Frobenius norm is $4u^2-1$. Using the uniform bound $u^{-66}$, the three original integrals at $s=2$ are bounded respectively by
$$
2\pi^2 a_\nu\left(\frac1{62}-\frac1{64}\right),\qquad
2\pi^2 a_\nu\left(\frac1{128}-\frac1{130}\right),\qquad
2\pi^2 a_\nu\left(\frac4{126}-\frac5{128}+\frac1{130}\right).
$$
For example, the last integrand after the constant is bounded by $(4u^5-5u^3+u)u^{-132}$. These formulas include the origin by continuity. The tests $65>48$ and $65>24+8\sqrt2$ hold. In each group $a_\nu$ is fixed throughout, with probability compact measure in the polar formula and the compact average. [Expository]

**Definitions.** Index from zero. Fix $n$, signs $\varepsilon$, $G=U(J_\varepsilon)$, its compact subgroup $K$, and a Haar measure $\nu$ on $G$. Write $p,q$ for the sign counts, $q_0=\min(p,q)$, and $\rho_i=(n-1)/2-i$. Fix a strictly decreasing $\lambda$ with $\lambda_i-(n-1)/2\in\mathbb Z$ (`IsHCParam`), the integer tuple $\mu$ with $\mu_i=\lambda_i+\rho_i$ (`IsMu`), and a compact type $T$ of highest weight $\operatorname{lowK}(\varepsilon,\lambda)=\lambda+\rho_N-\rho_C$ with unit highest vector $w$. The half-sums $\rho_N,\rho_C$ use opposite-sign and same-sign positive roots, respectively. Fix a real $h$ with $|\lambda_i-\lambda_j|\ge h$ on all opposite signs (`GapAtLeast`), and assume $q_0\ge1$. Put $f(g)=\operatorname{PsiM}(T,\mu)(g)$, with operator norm on $T.V$, and set $\operatorname{hs}(A)=\sum_{i,j}|A_{ij}|^2$. [Lean, read] [Source ledger](../sources/SOURCES.md#chapter-9-weighted-psim-integrability)

**Lemma (polar integrability).** For the fixed data above,
$$
\begin{aligned}
h>16nq_0 &\ \Longrightarrow\ f\in L^1(\nu),\\
h>8nq_0 &\ \Longrightarrow\ f\in L^2(\nu),\\
s\ge0,\quad h>8nq_0+4s\sqrt{2q_0}
&\ \Longrightarrow\ \int_G\|f(g)\|^2\operatorname{hs}(g)^{s/2}\,d\nu(g)<\infty .
\end{aligned}
$$
The last integral is the squared $L^2$ norm of $\operatorname{hs}^{s/4}f$. The three implications use the same $h$, kernel and Haar, and hold for every choice of that data. [Lean, read] (`CasimirCoefficients/Integr.lean:22–133`.)

**Proof.** Let $r=\sqrt{\operatorname{hs}(X)}$ and $c=\sqrt{2q_0}$. The noncompact space $\mathfrak p$ consists of Hermitian matrices with zero same-sign blocks. In sign-block order $X=X(B)=\left(\begin{smallmatrix}0&B\\B^\dagger&0\end{smallmatrix}\right)$ for $B\in\mathbb C^{p\times q}$. The original order is retained when forming minors. With $y_i$ the real eigenvalues of $X(B)$, the actual density in the chart $(k,B)\mapsto k e^{X(B)}$ is
$$
J(X)=\prod_{i<j}S(y_i-y_j),\qquad S(v)=\frac{\sinh v}{v}\ (v\ne0),\quad S(0)=1.
$$
The [polar Haar construction](#946-polar-haar-measure-and-the-discrete-series-integrability-bound) uses $J(X)$, probability compact Haar $dk$ and entrywise Lebesgue $dB$. The lower-entry coordinates `PCoord` and $B$ differ by a permutation and conjugations with absolute real determinant one. The polar Haar theorem and Haar uniqueness give the exact integration rule $d\nu=a_\nu\,dk\,J(X(B))\,dB$ in the chart. `haar_polar_le` uses measurable extension from the closed matrix realization of $G$, Tonelli and additive Haar comparison to implement this change of variables with an upper bound on $J$. The polar Haar density is inherited from the prior polar-coordinate proof. In the two examples the scale may be fixed to the very measure $\nu=2\mu_{\mathrm{CD}}$ used in §9.4.28. The factor of §9.4.27 then gives $a_\nu=2/\pi$ on $U(1,1)$ and $a_\nu=4/\pi^2$ on $U(2,1)$. In this normalization the front factors in the two radial integrals above are $4$ and $8$. [Lean, read] (`PmatIsHermitian.lean:19–43,80–92`, `IntMuCD.lean:122–131`, `PolarHaar.lean:16–38`, `HaarPolar.lean:42–190`.)

As $S(v)=\int_0^1\cosh(av)\,da\le e^{|v|}$, $\log J(X)\le(n-1)\sum_i|y_i|$. The off-diagonal blocks each have rank at most $q_0$, so $X$ has at most $2q_0$ nonzero eigenvalues. Since $\sum_i y_i^2=r^2$, Cauchy–Schwarz gives $\sum_i|y_i|\le cr$. `jac_le_exp` gives $J(X)\le e^{(n-1)cr}$ and `haar_polar_le` uses $e^{ncr}$. Repeated eigenvalues and $X=0$ are included by the value $S(0)=1$. [Lean, read] (`FormalDegree/JacobianLeExp.lean:39–109,111–297`, `JacBound.lean:14–20`.)

For the seed estimate let $D_m=\det((e^X)_{[0,m)})$ for $1\le m\le n$. These minors are positive and $D_n=1$ since $X$ has zero trace. The scalar of `psM` is $\prod_{m=1}^n D_m^{-(\mu_{m-1}-\mu_m)}$ with $\mu_n=0$. For $r>0$ put $\tau=\min(1,1/(cr))$. Diagonalize $X=U\operatorname{diag}(y)U^\dagger$. Cauchy–Binet writes $D_m=\mathbb E e^{Z_m}$ where $Z_m=\sum_{j\in I}y_j$ with probabilities $|\det U_{[0,m),I}|^2$ for $|I|=m$. The mean is $\operatorname{tr}X_{[0,m)}=0$. Write $P=U^\dagger P_m U$ for the conjugate of the first-$m$ coordinate projection. In the generating determinant $\det(U_{[0,m),:}\operatorname{diag}(1+z_i)U_{[0,m),:}^\dagger)$ the coefficients of $z_i$ and $z_i z_j$ are $P_{ii}$ and $P_{ii}P_{jj}-|P_{ij}|^2$. This follows by expanding the determinant of the identity plus the weighted sum of column rank-one operators. They are the one- and two-index inclusion probabilities. The variance is therefore $\operatorname{tr}(P\operatorname{diag}(y)^2)-\operatorname{tr}((P\operatorname{diag}(y))^2)$, which in the original basis is
$$
V_m=\sum_{b<m\le a}|X_{ab}|^2 .
$$
Also $|Z_m|\le cr$. For $|z|\le1$, the exponential series through degree four has absolute remainder at most $|z|^5/100$, by bounding the factorial series tail by a geometric series of ratio $1/6$. The quadratic and cubic terms sum to at least $z^2/3$, and the fourth term dominates the remainder. Hence $\mathbb E e^{\tau Z_m}\ge1+\tau^2 V_m/3$. For $a=\tau^2V_m/3\le1/3$, integration of $(1+x)^{-1}$ gives $\log(1+a)\ge a/(1+a)\ge3a/4$. Convexity of the power $1/\tau$ gives $\mathbb E e^{Z_m}\ge(\mathbb E e^{\tau Z_m})^{1/\tau}$ and hence $\log D_m\ge\tau V_m/4$. [Lean, read] (`DecMoments.lean:122–149`, `DecALogLower.lean:63–92`, `DecLog.lean:16–97`.)

For $m<n$ the exponent differences $\mu_{m-1}-\mu_m$ are nonnegative. In the weighted sum of the $V_m$, each entry with $b<a$ appears from cut $b+1$ through cut $a$, receiving coefficient $\mu_b-\mu_a=(\lambda_b-\lambda_a)+(a-b)$. For a nonzero entry this coefficient is at least $h$ by the opposite-sign condition. The lower-triangular squared mass is $r^2/2$. The last cut vanishes and $\log D_n=0$, including when $\mu_{n-1}<0$. Exponentiation gives $\Phi_M(\mu,e^X)\le e^{-(h/8)\min(r^2,r/c)}$. All minors are $1$ at the origin. The kernel on $k e^X$ is $T(k)$ times the average on $e^X$. This average integrates the nonnegative scalars at $\ell^{-1}e^X\ell$ against conjugates of the rank-one projection onto $w$, with probability Haar and the factor $\dim T$. Conjugation preserves $r$ and $\mathfrak p$. The normalized average of the projections is the identity by compact Schur and trace, so positivity gives operator domination by the same scalar bound times the identity. Left multiplication by $T(k)$ preserves the operator norm. This proves `psiM_dec`. [Lean, read] (`DecSum.lean:91–127`, `PhiDecayCore.lean:24–109,131–202`, `DecPos.lean:128–182`, `ToMKMulInv.lean:38–43`.)

Completing the square gives $\min(r^2,r/c)\ge r/c-1/(4c^2)$ on the whole half-line. Each threshold implies $h\ge0$. With $A_h=e^{h/(32c^2)}$ we get $\|f(k e^X)\|\le A_h e^{-hr/(8c)}$. Left unitarity gives $\operatorname{hs}(k e^X)=\sum_i e^{2y_i}\le n e^{2r}$. Thus the weight costs at most $n^{s/2}e^{sr}$ for $s\ge0$. Multiplying by the Haar bound, the three densities are at most $M e^{-\delta r}$ with the following constants. [Lean, read] (`IntegrA.lean:146–162`, `Integr.lean:29–133`, `IntegrableOfDecayVG.lean:278–302`.)

| Integrand | $M$ | $\delta$ |
|---|---|---|
| $\|f\|$ | $A_h$ | $(h-16nq_0)/(8c)$ |
| $\|f\|^2$ | $A_h^2$ | $(h-8nq_0)/(4c)$ |
| $\|f\|^2\operatorname{hs}^{s/2}$ | $A_h^2 n^{s/2}$ | $(h-8nq_0-4sc)/(4c)$ |

Let $d=2pq$. For $t=\|B\|_F$ one has $r=\sqrt2 t$. The compact factor has mass one. In each row the required inequality gives $\delta>0$, and the norm integral on the original group is bounded by
$$
a_\nu M\,\frac{2\pi^{pq}}{(pq-1)!}\,\frac{(d-1)!}{(\sqrt2\,\delta)^d}.
$$
The sphere area follows by computing the Euclidean Gaussian integral both as a product of planar Gaussians and radially. Integration by parts gives $\int_0^\infty t^{d-1}e^{-\sqrt2\delta t}dt=(d-1)!/(\sqrt2\delta)^d$. In `IntegrA` the finiteness proof uses the entrywise supremum norm $\|B\|\le r$. For $N=d+1$ and $\eta=\min(1,\delta/(N+1))$, the exponential is bounded by $\eta^{-N}(1+\|B\|)^{-N}$ since $\eta(1+t)\le e^{\delta t/(N+1)}$ for $t\ge0$. The pinned Mathlib finite-integral theorem applies with $N>d$. The explicit sphere-area bound uses the Euclidean radius with the exact normalization above. [Lean, read] (`IntegrA.lean:35–144`.) [Expository] (explicit integral bound.)

In Lean the local smooth extension supplies continuity after composition with `toM`. In the polar formula one can also see continuity directly: $P=(g^\dagger g)^{1/2}$ and $k=gP^{-1}$ depend continuously on $g$. The minors of $\ell^{-1}P\ell$ stay positive, and the integrand in the compact average is jointly continuous in $P$ and $\ell$. On a compact neighborhood of any positive $P$ this gives uniform continuity over $\ell\in K$, so the integral is continuous in operator norm. Its finite-dimensional target makes this strongly measurable, including almost-everywhere strong measurability for each $\nu$. The squared norm and the nonnegative real power of the continuous function `hs` give a continuous weighted integrand, including the constant power at $s=0$. Together with the finite norm integrals this proves Bochner $L^1$, the square-norm criterion for `MemLp` at $2$, and integrability with the original weight. [Lean, read] (`LholClmEventually.lean:57–75`, `Integr.lean:35–37,67–104`.) [Pinned supplies](../sources/SOURCES.md#chapter-9-weighted-psim-integrability)

**Remarks on the endpoints.** In the first example, keep $h=50$ and choose $s_0=34/(4\sqrt2)$. Then $\delta=0$ in the third row, and the product of the three coarse bounds is constant as a function of $B$ and has infinite flat-volume integral. The tighter density estimate $e^{(n-1)cr}$ would still leave margin $c$ here. The true rank-one density at arbitrary $s\ge0$ is $2\pi a_\nu u^{-101}(4u^2-2)^{s/2}$. The inequalities $2u^2\le4u^2-2\le4u^2$ give convergence exactly for $s<100$. Thus at $s_0<100$ the comparison fails and the actual integral remains finite. Deleting the weighted height condition allows $s=100$, for which the same kernel has logarithmically divergent weighted integral. Deleting `IsMu` allows $\mu=(0,0)$ at the same $T,\lambda,h,\nu$. Then $\Phi_M=1$, so the normalized compact average is the identity and the norm is identically one. All three integrals diverge even at $s=2$. [Expository]

For a second boundary check keep the original $U(2,1)$ data. The exact diagonal expression above has norm comparable to $u^{-67}$ for $u\ge2$. For the upper bound, on $x\le1/2$ one has $D\ge u/2$ and $\int_0^{1/2} A^{-76}\,dx\le 1/(75(u-1))$. On $x\ge1/2$ use $A\ge u/2$ and $\int_{1/2}^1 D^{-66}\,dx\le1/(65(u-1))$. The binomial factors are bounded over the finite set of indices. For the lower bound use $j=140$ on $0\le x\le1/u$. There $A\le2$, $D\le u$ and $(1-x)^{140}\ge2^{-140}$. The exact weighted density on $u\ge2$ is consequently comparable to $u^{s-131}du$. At $s=(65-24)/(4\sqrt2)$ the archive's coarse product bound has zero remaining decay, while the actual integral converges. At $s=130$ the actual integral diverges logarithmically. [Expository]

**The tensor consumer.** `swA_model` chooses $\mu=\lambda+\rho$ and fills the ordinary $L^2$ field of `IsPsiFor` with the second branch. Its hypothesis $h>\operatorname{thrStar}(\varepsilon)$ implies $h>8nq_0+8c$, so it supplies `weighted_datum` by the third branch at $s=2$ for every Haar. `wd_psi_memLp` applies this at `Formalism.REAL.muG` through `integrable_muG_of_haar`. The group matrices `S7.toM g` and `umat g` agree here. The squared norm of $\sqrt{\operatorname{hs}}\,\|\Psi_M\|$ is exactly $\operatorname{hs}\,\|\Psi_M\|^2$. The lowest-type identity `formulaF` and the operator norm bound control coefficients on two lowest-type vectors. `wd_key` applies the named `r0bG` at exponent $1/2$ for $\log(\operatorname{hs})$ on the finite-dimensional seed coefficient space and its derived words. Inversion preserves `muG` and $\operatorname{hs}$, so conjugation after inversion exchanges the slots and permits the second generated-space extension. The output is weighted $L^2$ for every pair of algebraically generated vectors. Each defining matrix entry is bounded by $\sqrt{\operatorname{hs}}$. The dual has the same bound by $g^{-1}=J_\varepsilon g^\dagger J_\varepsilon$. `cc_gk` takes these estimates from `hW` and `hW'` in the two directions on `muG`, and `swC_main` transports the resulting degree comparison to the caller's one Haar $\nu$ by the comparison of §9.4.28. [Lean, read] (`WeightedA.lean:65–95`, `WeightedB.lean:47–167`, `Weighted.lean:16–35`, `SandwichA.lean:24–56,150–186`, `CcARatioZero.lean:82–141`.)

**Sources and scope.** Knapp's polar homeomorphism applies to $U(J_\varepsilon)$ because the group is defined by real polynomial equations and is stable under adjoints. The classical Cartan density applies on the connected semisimple finite-center group $SU(p,q)$ with maximal compact subgroup $S(U(p)\times U(q))$. In our examples the positive restricted root $2t$ has multiplicity one, and on $U(2,1)$ the root $t$ has multiplicity two. Multiplying the two displayed $J$ by the respective flat radial factors $t$ and $t^3$ gives the corresponding Cartan densities up to Haar scale. The central circle restores $U(p,q)$ by pushing forward probability Haar on the circle times Haar on $SU(p,q)$. Harish-Chandra's square-integrable coefficient theorem concerns an already realized irreducible unitary representation. Atiyah–Schmid's discrete series theorem takes a finite-center semisimple group with compact Cartan and a regular parameter in the translated character lattice. These supply the classical context for the density and ordinary square-integrability. The displayed sufficient constants come from the archive's explicit kernel, minor bound and choice of Haar majorant. [Paper] [Knapp, Proposition 1.143](https://www.math.stonybrook.edu/~aknapp/download/Beyond2-clickable.pdf) · [Anker–Papageorgiou–Zhang, §2.1, (2.3)](https://arxiv.org/abs/2112.01323) · [Harish-Chandra, §37 and Theorem 16](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6013-11511_2006_Article_BF02392813.pdf) · [Atiyah–Schmid, Theorem (8.1)](https://www.math.utah.edu/~ptrapa/math-library/schmid/atiyah-schmid.pdf)

[Open] The local smooth formula supplies measurability. The separate Casimir eigenvalue identity is used by the coefficient handoff, with the prior Casimir reading at its conditional scope. The weighted derivative theorem `r0bG` and the local differentiability suppliers `casL_psM` and `psiM_local` enter through their stated interfaces. Stable closure and compact-finite recovery enter at their inherited interfaces. Declaration-level reachability from `Main` and independent review retain separate status. [Community] Archive replay is tracked in the public verification record. [Source ledger](../sources/SOURCES.md#chapter-9-weighted-psim-integrability) · [Community verification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)

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
