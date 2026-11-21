# Chapter 8. Divisibility at inert primes

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs
> verified line by line in `WeilJacquetShalikaLaw.lean`, `DataDIVDefs.lean`, `DataParams₂.lean`,
> `DataExtra.lean`, `DefsInst.lean`, `DataG.lean`, `JointServices.lean`, `GServT.lean`, and
> `DIVRecBridgeSel.lean` (`R3`); `[Lean]` for upstream formal-group and row-bound theorems whose
> statement headers were inspected while their deep proof cones remain unread (`R2`); `[Paper]` for
> citations to Alpöge's `remark.pdf` and Masullo's draft; `[Community]` for public community guides;
> `[Expository]` for classical background and worked examples; `[Open]` for unread deep proof
> obligations.

In Chapter 6 we proved Stepanov's hyperelliptic curve bound over $\mathbb F_q$ by forcing an
auxiliary polynomial $\Phi(x)$ to vanish to high order $M$ at every $\mathbb F_q$-rational point,
detecting that vanishing with Hasse–Schmidt divided-power operators $D^{(k)}$, and reading off a
global inequality from $\sum_P \operatorname{ord}_P(\Phi) \le \deg(\Phi)$ `[Stepanov1969]`,
`[Bombieri1973]`, `[HasseSchmidt1937]`. In Chapter 7 we built the archive's candidate replacement
for "differentiating $m$ times": a chain of $m \asymp \sqrt{x}$ iterated Weil–Howe theta lifts
between definite unitary groups over the CM host extension $E/F$, together with the eleven-clause
chain package `SizeData₂` (`src/Formalism/SizeWindowBrackets/SChain.lean:17`) [Lean, read].

Now we must answer the first fundamental question of the arithmetic engine: **where does high-order
prime divisibility actually come from over the integers, and why does it single out the odd prime
powers $p, p^3, p^5, \dots$ of primes $p$ inert in the imaginary quadratic core
$K = \mathbb Q(\sqrt{-d})$?** That phenomenon is governed in the archive by node **P8**, centred on
`WeilJacquetShalikaLaw.Conclusion1`
(`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97`) [Lean, read].

---

## 8.1 Motivation: why supersingular CM points produce odd-power $p$-adic divisibility

Over a function field $\mathbb F_q(t)$, the Frobenius endomorphism $u \mapsto u^q$ is an honest ring
homomorphism, and Hasse–Schmidt derivations satisfy $D^{(k)}(u^q) = 0$ for every $1 \le k < q$. Over
$\mathbb Z$, there is no global Frobenius endomorphism and no derivation of $\mathbb Z$. Yet as
Alpöge's note records at the very start of its timeline ("10/19/26: $D^p \equiv 0$ on a CM curve
with $p$ inert in $K$, giving $p^{a/p + a/p^3 + \dots - O(\log a)}$-divisibility of
$D^a \vartheta(0)/\Omega^a$", `remark.pdf` p. 3, item 2) [Paper; remark p. 3], classical arithmetic
geometry already possesses an exact **local** substitute whenever a CM elliptic curve or abelian
variety is reduced modulo a prime **inert** in its CM field `[Katz1976]` [Expository]!

Let us see the mechanism in three transparent steps [Expository]:

1. **Ordinary (split) versus supersingular (inert) reduction.** Let $K = \mathbb Q(\sqrt{-d})$ be an
   imaginary quadratic field, and let $\mathcal E$ be an elliptic curve with complex multiplication
   by $\mathcal O_K$ defined over a number field $E \supset K$, equipped with a Néron differential
   $\omega$ and invariant derivation $D = \omega^{-1}\,d$. Take an unramified odd rational prime $p$
   and a prime $\mathfrak p_w$ of $E$ above $p$:
   - If $p$ **splits** in $K$ ($p\mathcal O_K = \mathfrak q \overline{\mathfrak q}$), then
     $\mathcal E \bmod \mathfrak p_w$ is **ordinary**: its formal group $\widehat{\mathcal E}$ over
     $\mathcal O_{E_w}$ has height $1$, becoming isomorphic over $\widehat{\mathbb Z}_p^{\mathrm{ur}}$
     to the multiplicative formal group $\widehat{\mathbb G}_m$ (`[Katz1976]`). On $\widehat{\mathbb G}_m$,
     the invariant derivation is $(1 + T)\frac{d}{dT}$, whose $a$-th iterate on rational functions of
     $T$ has unit $p$-adic coefficients (just as $\bigl((1+T)\frac{d}{dT}\bigr)^a T\big\rvert_{T=0} = 1$
     for all $a \ge 1$!). Thus **split primes contribute zero $p$-adic divisibility gain**.
   - If $p$ is **inert** in $K$ ($p\mathcal O_K$ remains prime, residue field $\mathbb F_{p^2}$),
     then $\mathcal E \bmod \mathfrak p_w$ is **supersingular**: its formal group
     $\widehat{\mathcal E}$ has **height $2$**! More specifically, in a Lubin–Tate formal coordinate
     $T$ for the uniformizer $\pi = p$ of $K_p$ (with residue cardinality $q_K = p^2$), the formal
     group logarithm takes the shape
     $$\log_{\widehat{\mathcal E}}(T) = \sum_{e \ge 0} \frac{c_e}{p^e}\,T^{p^{2e}} \qquad (c_e \in \mathcal O_{E_w}^\times,\ c_0 = 1).$$
2. **Why height $2$ produces exponents $\lfloor a / p \rfloor + \lfloor a / p^3 \rfloor + \lfloor a / p^5 \rfloor + \dots$!**
   Differentiating $\log_{\widehat{\mathcal E}}(T) = z$ gives the invariant differential
   $$\omega(T) = \Bigl(\sum_{e \ge 0} c_e\,p^e\,T^{p^{2e} - 1}\Bigr)\,dT \equiv dT \pmod p!$$
   Pause to appreciate that congruence: modulo $p$, $\omega(T) \equiv dT$ has **no higher terms at
   all**, so $D = \frac{1}{\omega(T)}\frac{d}{dT} \equiv \frac{d}{dT} \pmod p$, whose $p$-th iterate
   satisfies
   $$D^p(T^n) \equiv n(n-1)\cdots(n-p+1)\,T^{n-p} \equiv 0 \pmod p$$
   on **every** integral power series in $\mathcal O_{E_w}\llbracket T \rrbracket$ (`remark.pdf`
   p. 3, item 2) [Paper; remark p. 3]! Even better, compute the $p$-adic Newton polygon of the
   inverse power series $T(z) = \exp_{\widehat{\mathcal E}}(z) = \sum_{a \ge 1} d_a\,z^a = \sum_{a \ge 1} \frac{b_a}{a!}\,z^a$,
   where $b_a = (D^a T)(0)$: because $p$ is unramified in $K_p$ of inertia degree $2$, $p$ itself is
   a uniformizer of $\mathcal O_{K_p}$ with residue cardinality $q_K = p^2$, so the Lubin–Tate
   logarithm $\log_{\widehat{\mathcal E}}(T) = \sum_{e \ge 0} \frac{c_e}{p^e}\,T^{p^{2e}}$ has
   Newton-polygon vertices at $(p^{2e}, -e)$. Inverting $\log_{\widehat{\mathcal E}}(T) = z$ gives
   $v_p(d_a) \ge -\frac{a - 1}{p^2 - 1}$ for every $a \ge 1$. Since $b_a = a!\,d_a$, Legendre's
   formula $v_p(a!) = \sum_{r \ge 1} \lfloor a / p^r \rfloor = \frac{a - s_p(a)}{p - 1} = \frac{a}{p - 1} - O(\log_p a)$
   immediately yields
   $$v_p\bigl((D^a T)(0)\bigr) = v_p(a!) + v_p(d_a)
   \ge \Bigl(\frac{1}{p - 1} - \frac{1}{p^2 - 1}\Bigr) a - O(\log_p a)
   = \frac{p}{p^2 - 1}\,a - O(\log_p a)!$$
   Now expand the rational number $\frac{p}{p^2 - 1}$ into a geometric series in $p^{-2}$:
   $$\frac{p}{p^2 - 1} = \frac{1/p}{1 - 1/p^2} = \frac{1}{p} + \frac{1}{p^3} + \frac{1}{p^5} + \frac{1}{p^7} + \cdots!$$
   Look at that identity (`gam p = p / (p^2 - 1)` at
   `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:51`) [Lean]:
   **subtracting the height-$2$ formal-group denominator slope $\frac{1}{p^2 - 1}$ from Legendre's
   factorial slope $\frac{1}{p - 1}$ cancels every even prime power $\frac{1}{p^2} + \frac{1}{p^4} + \dots$
   and leaves the exact sum of odd prime powers $\frac{1}{p} + \frac{1}{p^3} + \frac{1}{p^5} + \dots$!**
3. **Why adding level/weight cutoffs turns $\sum_{e \ge 0} a / p^{2e+1}$ into `ASK`!** In the actual
   theta-lift chain, one does not differentiate a single theta function to order $a$; instead, at each
   step $j \in \{1, \dots, m\}$ of the chain, the local Siegel–Weil / Kudla–Rallis theta kernel has a
   prescribed archimedean weight parameter $\alpha_s$ (`aT`) and a level/place threshold `cap` (`wPart`).
   At each odd prime power $p^{2e+1}$, the local kernel contributes valuation gain
   $\max(\alpha_s / p^{2e+1} - \mathrm{cap}, 0)$ (`gA` at `FormalGroupSystem.lean:66`, matching
   `vonMangoldtClassSum` at `src/Formalism/LocalRingCardinality/DataParams₂.lean:240`) [Lean, read].
   Multiplying by $\log p$ and summing over primes $p$ inert in $E/\Phi$ reproduces **term for term**
   the Riesz-weighted inert prime sum `ASK` of Chapter 5 (Definition 5.1(3))!

---

## 8.2 Worked examples

Before entering the Lean declarations, let us verify both halves of this phenomenon by hand: first on
Gauss's lemniscate curve over $\mathbb Z[i]$, and then on a finite $3$-adic column-divisibility model
matching `WeilJacquetShalikaLaw.lean` [Expository].

### 8.2.1 Hand calculation on the lemniscate sine: split $p = 5$ versus inert $p = 3, 7$

Consider the elliptic curve $\mathcal E : y^2 = 1 - x^4$ (birational to $Y^2 = X^3 - X$), which has
complex multiplication by the Gaussian integers $\mathbb Z[i]$ via $[i](x, y) = (ix, y)$. Its
invariant differential is $\omega = \frac{dx}{y}$, and its local parameter at the origin $(0, 1)$ is
the classical **lemniscate sine** $x = \operatorname{sl}(z)$ satisfying
$$\bigl(\operatorname{sl}'(z)\bigr)^2 = 1 - \operatorname{sl}(z)^4, \qquad \operatorname{sl}(0) = 0, \qquad \operatorname{sl}'(0) = 1,$$
where $D = \frac{d}{dz}$ is the invariant derivation $\omega^{-1}\,d$. Differentiating once gives
$\operatorname{sl}''(z) = -2\,\operatorname{sl}(z)^3$, so $\operatorname{sl}(z) = \sum_{m \ge 0} \frac{b_{4m+1}}{(4m+1)!}\,z^{4m+1}$
with $b_a = (D^a \operatorname{sl})(0) \in \mathbb Z$ determined by the recursion
$$\frac{b_{k+2}}{(k+2)!} = -\frac{2}{(k+1)(k+2)}\sum_{i + j + \ell = k} \frac{b_i}{i!}\,\frac{b_j}{j!}\,\frac{b_\ell}{\ell!}.$$

Compute the first four nonzero derivatives by hand:

- $a = 1$: $b_1 = 1$.
- $a = 5$ ($k = 3$, unique triple $(1, 1, 1)$):
  $\frac{b_5}{5!} = -\frac{2}{4 \cdot 5} \cdot 1 = -\frac{1}{10}$, so
  $$b_5 = -\frac{120}{10} = -12 = -2^2 \cdot \mathbf{3}^1.$$
- $a = 9$ ($k = 7$, three permutations of $(5, 1, 1)$):
  $\frac{b_9}{9!} = -\frac{2}{8 \cdot 9} \cdot 3 \cdot \Bigl(-\frac{1}{10}\Bigr) = \frac{1}{120}$, so
  $$b_9 = \frac{362{,}880}{120} = 3{,}024 = 2^4 \cdot \mathbf{3}^3 \cdot \mathbf{7}^1.$$
- $a = 13$ ($k = 11$, permutations of $(9, 1, 1)$ and $(5, 5, 1)$):
  $\frac{b_{13}}{13!} = -\frac{2}{12 \cdot 13}\Bigl(3 \cdot \frac{1}{120} + 3 \cdot \frac{1}{100}\Bigr) = -\frac{11}{15{,}600}$, so
  $$b_{13} = -4{,}390{,}848 = -2^8 \cdot \mathbf{3}^4 \cdot \mathbf{7}^1 \cdot \mathbf{11}^2.$$

Extending two steps further gives the following table of $p$-adic valuations $v_p(b_a)$:

| Order $a$ | $b_a = (D^a \operatorname{sl})(0)$ | Split $p = 5$ ($5 = (2+i)(2-i)$) | Inert $p = 3$ ($\lfloor a/3 \rfloor + \lfloor a/27 \rfloor$) | Inert $p = 7$ ($\lfloor a/7 \rfloor$) | Inert $p = 11$ ($\lfloor a/11 \rfloor$) |
|---|---|---|---|---|---|
| $1$ | $1$ | $v_5 = 0$ | $v_3 = 0$ ($0$) | $v_7 = 0$ ($0$) | $v_{11} = 0$ ($0$) |
| $5$ | $-12$ | $v_5 = 0$ | $v_3 = 1$ ($1$) | $v_7 = 0$ ($0$) | $v_{11} = 0$ ($0$) |
| $9$ | $3{,}024$ | $v_5 = 0$ | $v_3 = 3$ ($3$) | $v_7 = 1$ ($1$) | $v_{11} = 0$ ($0$) |
| $13$ | $-4{,}390{,}848$ | $v_5 = 0$ | $v_3 = 4$ ($4$) | $v_7 = 1$ ($1$) | $v_{11} = 2$ ($1$) |
| $17$ | $21{,}224{,}560{,}896$ | $v_5 = 0$ | $v_3 = 6$ ($5$) | $v_7 = 2$ ($2$) | $v_{11} = 1$ ($1$) |
| $21$ | $-257{,}991{,}277{,}243{,}392$ | $v_5 = 0$ | $v_3 = 7$ ($7$) | $v_7 = 3$ ($3$) | $v_{11} = 1$ ($1$) |

Every feature of Section 8.1 is visible at a glance:

- At the **split** prime $p = 5 \equiv 1 \pmod 4$, **not a single derivative $b_a$ in the table is
  divisible by $5$** ($v_5(b_a) = 0$ throughout, because $b_a \bmod 5$ is governed by Hurwitz's
  nonvanishing Gauss-sum eigenvalue $a_5 = -2 \not\equiv 0 \pmod 5$).
- At the **inert** primes $p = 3, 7, 11 \equiv 3 \pmod 4$, $v_p(b_a)$ grows linearly with slope
  $\frac{p}{p^2 - 1} = \frac{1}{p} + \frac{1}{p^3} + \dots$, bounded below at every step in the table
  by $\sum_{e \ge 0} \lfloor a / p^{2e+1} \rfloor$!

### 8.2.2 Toy two-step column divisibility and the odd-power ramp

Now let us see how `WeilJacquetShalikaLaw.lean` packages local $p$-adic divisibility across a chain
of $m$ steps [Expository]. Take $L_0 = \mathbb Z[i]$ at the unramified inert prime $p = 3$
(ramification index $e_w = 1$, uniformizer $\varpi_w = 3$, valuation $v_w = v_3$), and let
$\Lambda_w = \mathbb Z_3[i]^2$ be a rank-$2$ integral lattice. In `WeilJacquetShalikaLaw.lean:19`,
an element $y \in E_w^2$ satisfies `VGe D w s y` (for real $s \in \mathbb R$) if $y = a \cdot z$ for
some $a \in \mathcal O_E$ and $z \in \Lambda_w$ with either $a = 0$ or $e_w s \le v_w(a)$ — over our
unramified place $e_w = 1$, simply $3^{\lceil s \rceil} \mid y$ inside $\Lambda_w$!

Suppose we have a $2$-step chain ($m = 2$) of $\mathcal O_E$-linear kernel operators
$K_1, K_2 : \Lambda_w \to \Lambda_w$ whose matrix columns on $\Lambda_w$ are divisible by $3^{g_1}$
and $3^{g_2}$ up to small error slacks $\varepsilon_1, \varepsilon_2$:

- Suppose $K_1(z) = 3^4\,A_1(z)$ (`gainS = 4`, `ES = 0`) and $K_2(z) = 3^3\,A_2(z)$ (`gainS = 3`,
  `ES = 0`) with $A_1(\Lambda_w) \subseteq \Lambda_w$ and $A_2(\Lambda_w) \subseteq \Lambda_w$.
- Start with $y_0 \in \Lambda_w$ (`VGe w 0 y_0`). Applying $K_1$ gives $y_1 = 3^4 A_1(y_0)$
  (`VGe w 4 y_1`), and applying $K_2$ gives $y_2 = K_2(y_1) = 3^4 K_2(A_1(y_0)) = 3^{4+3} A_2(A_1(y_0))$
  (`VGe w 7 y_2`). That additive accumulation of valuations across steps is `val_step` and
  `period_ge` (`WeilJacquetShalikaLaw.lean:401, 419`)!

And what numerical gain does the archive assign to an inert prime $p = 3$ at top scale $a_T = 100$
and place weight $w_{\mathrm{Part}} = 2$ (`vonMangoldtClassSum`, `DataParams₂.lean:240`)? Sum
$\max(a_T / 3^{2e+1} - w_{\mathrm{Part}}, 0)$ over $e = 0, 1, 2, \dots$:

- $e = 0$ ($3^1 = 3$): $\max\bigl(\frac{100}{3} - 2,\ 0\bigr) = \frac{94}{3}$;
- $e = 1$ ($3^3 = 27$): $\max\bigl(\frac{100}{27} - 2,\ 0\bigr) = \frac{46}{27}$;
- $e \ge 2$ ($3^5 = 243$): $\frac{100}{243} - 2 < 0$, so every term with $e \ge 2$ is **identically $0$**!

Thus the finite odd-power sum terminates automatically at $3^{2e+1} \le a_T / w_{\mathrm{Part}} = 50$,
producing total logarithmic gain $\log 3 \cdot \bigl(\frac{94}{3} + \frac{46}{27}\bigr) = \frac{892}{27}\log 3$.
Compare that formula with Chapter 5's `askP` (`FirstPrimeNeSecondPrime.lean:75`): **they are the
exact same function**!

---

## 8.3 Definitions

We now present the exact Lean definitions of node **P8** and its surrounding local-to-global
interfaces.

### 8.3.1 Ramification scaling, fractional ideals `Iu`, and column divisibility (`VGe`, `ColGe`)

Let $E$ be the CM host number field with ring of integers $L_0 = \mathcal O_E$. At each maximal ideal
$w \in \mathrm{HeightOneSpectrum}(\mathcal O_E)$ lying over a rational prime $p = w.\mathrm{natPrime}$,
let $e_w = \mathrm{ramIdx}(w) \ge 1$ denote the ramification index of $w$ over $p$, and let
$v_w : \mathcal O_E \setminus \{0\} \to \mathbb N$ denote the normalized $\mathfrak p_w$-adic
valuation (`vAdd w a`).

**Definition 8.1 (Unramified-scaled valuation thresholds and fractional ideals, `src/Formalism/LocalRingCardinality/DataDIVDefs.lean:15,17,31,48` and `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:19,24,28,33,37`).**

1. **Ramification scaling and fractional ideal (`ur` and `Iu`, `DataDIVDefs.lean:15, 17`).** For a
   place $w$ of $\mathcal O_E$ and $s \in \mathbb R$, set [Lean, read]
   $$\mathrm{ur}(w, s) := e_w \cdot s.$$
   Given a finitely supported place-gain function $g : w \mapsto \mathrm{sg}(u, w) \ge 0$ supported
   on a finite set $\mathrm{supp}$, define the fractional ideal (`Iu`, `:17`)
   $$I_u := \prod_{w \in \mathrm{supp}} \mathfrak p_w^{-\lfloor e_w\,\mathrm{sg}(u, w) \rfloor}$$
   as a fractional ideal of $E$ (`FractionalIdeal L₀⁰ E`). Notice the sign of the exponent: saying
   that a quotient or dual twist lies in $I_u$, or equivalently that an element $y$ lies in
   $I_u^{-1} \Lambda = \prod_w \mathfrak p_w^{\lceil e_w\,\mathrm{sg}(u, w) \rceil}\Lambda$, encodes
   divisibility by $\mathfrak p_w^{\lfloor e_w\,\mathrm{sg}(u,w) \rfloor}$ at every $w \in \mathrm{supp}$!
2. **Scalar-lattice divisibility (`VGe`, `WeilJacquetShalikaLaw.lean:19`).** Given an $\mathcal O_E$-lattice
   $\Lambda_w \subseteq V$ in an $E$-module $V$ and $s \in \mathbb R$, an element $y \in V$ satisfies
   `VGe D w Λ_w s y` if there exist $a \in \mathcal O_E$ and $z \in \Lambda_w$ such that [Lean, read]
   $$y = a \cdot z \qquad\text{and}\qquad \bigl(a = 0 \ \lor\ e_w \cdot s \le v_w(a)\bigr).$$
3. **Untwisted and character-twisted column divisibility (`ColGe0`, `ColGeTw`, `ColGe`, `WeilJacquetShalikaLaw.lean:24, 28, 33`).**
   For an $\mathcal O_E$-linear map $T : V_1 \to V_2$ between spaces equipped with local lattices
   $\Lambda_{1,w}, \Lambda_{2,w}$ (or character-projected components $P_\chi$ over a cyclotomic ring
   extension $\mathcal O_E[\zeta_n]$ when a twisting character $\chi$ is active), `ColGe D w j u s`
   (`:33`) asserts that every column of the $j$-th chain step at unit index $u$ maps $\Lambda_{j-1,w}$
   into elements satisfying `VGe` at order $s$ (`ColGe0` at `:24` when untwisted, `ColGeTw` at `:28`
   when twisted by $\chi$ with root-of-unity conductor dividing $n$) [Lean, read].
4. **Exceptional primes (`Exc`, `WeilJacquetShalikaLaw.lean:37`).** A rational prime $p$ is
   **exceptional** (`Exc D p`) if $p$ divides $\mathrm{condN} \cdot g_0 \cdot g_1$, where
   $\mathrm{condN}$ is the host field conductor and $g_0, g_1$ are the auxiliary finite-field
   Green primes of Chapter 7 (`LabelDatum`) [Lean, read]. Every prime $p$ with `¬ Exc D p` is
   unramified in $E$ ($e_w = 1$) and coprime to the auxiliary level!

### 8.3.2 Stepwise gains, `Ties9`, and `WeilJacquetShalikaLaw.Conclusion1`

Next we read lines 49–101 of `WeilJacquetShalikaLaw.lean` verbatim (`R3`). Pay close attention to the
logical type of `Conclusion1`: **it is a `def ... : Prop` (a conditional implication), not an
unconditional standalone theorem** [Lean, read]!

**Definition 8.2 (Accumulated gain `totS`, compatibility `Ties9`, and `Conclusion1`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:49,57,60,67,73,76,79,92,97`).**
Let `D` be a chain datum of length $m$ (`lifts = Icc 1 m`):

1. **Stepwise gain and total $m$-step order (`gainS` and `totS`, `:49, 76`).** At a prime $p$ and
   lift step $j \in \{1, \dots, m\}$, `gainS D p j` (`:49`) denotes the real local valuation gain
   assigned to $(p, j)$, accompanied by an auxiliary Frobenius/level adjustment $F(j, w)$, an
   off-level slack `ES(u, j, w)`, and a base-vector valuation `vDG(u, w)` weighted by the sparsity
   switch $\mathrm{sp} \in \{0, 1\}$. Their $m$-step total at $(u, w)$ is [Lean, read]
   $$\mathrm{totS}(D, u, w) := \sum_{j = 1}^m \bigl(\mathrm{gainS}(D, w.\mathrm{natPrime}, j) + F(j, w) - \mathrm{ES}(u, j, w)\bigr)
   + \mathrm{sp} \cdot v_{\mathrm{DG}}(u, w).$$
   Two structural clauses accompany `gainS`: `GainZero D` (`:57`) requires $\mathrm{gainS}(D, p, j) = 0$
   whenever $p$ is split or outside the active prime set, and `InNP D` (`:60`) bounds the active
   non-Archimedean primes inside the finite truncation set `NprimeDef` (`DataDIVDefs.lean:22`).
2. **Compatibility bundle (`Ties9`, `:92`).** `Ties9 D : Prop` conjoins `GainZero D`, `InNP D`,
   local twist compatibility `TwLoc D` (`:79`), lattice-inclusion compatibility across steps, and
   positivity of the ramification indices [Lean, read].
3. **The target divisibility implication (`WeilJacquetShalikaLaw.Conclusion1`, `:97`).**
   `Conclusion1 D : Prop` is the proposition [Lean, read]:
   $$\mathrm{Conclusion1}(D) :\iff
   \Bigl(\mathrm{Ties9}(D) \ \land\ \forall u,\ \forall w,\ \forall j \in \{1, \dots, m\},\ \text{stepwise local service holds at }(u, w, j)\Bigr)$$
   $$\implies \forall u,\ \forall w,\ \mathrm{VGe}\bigl(D, w, \Lambda_{m, w}, \mathrm{totS}(D, u, w), y_m(u)\bigr).$$
   In plain English: *whenever the structural ties `Ties9 D` and the stepwise kernel-divisibility
   hypotheses hold at each individual lift $j = 1, \dots, m$, the composite $m$-step output column
   $y_m(u)$ at every place $w$ is divisible in $\Lambda_{m, w}$ to order $\mathrm{totS}(D, u, w)$!*

### 8.3.3 Local service (`Serv`, `ServF`), divided-power polynomials (`DataG`), and `vonMangoldtClassSum`

How are the stepwise hypotheses of `Conclusion1` supplied and connected to `ASK`? Three definitions
form the bridge:

**Definition 8.3 (Kernel service, Weyl divided powers, and the odd-power ramp, `WeilJacquetShalikaLaw.lean:113,241,245,252`, `DataG.lean:11,163`, `FormalGroupSystem.lean:51,66`, and `DataParams₂.lean:208,240`).**

1. **Local kernel valuation and Kudla family service (`IntegralKernelValuation`, `Serv`, `KudlaFamilyStatement`, `ServF`, `WeilJacquetShalikaLaw.lean:113, 241, 245, 252`).**
   `IntegralKernelValuation` (`:113`) states that at a good inert prime $p$ (`¬ Exc D p`), expanding
   the $j$-th local theta-kernel pairing in divided-power / formal-group coordinates produces elements
   divisible by $p^{\lceil \mathrm{gainS}(p, j) + F(j, w) - \mathrm{ES}(u, j, w) \rceil}$ whenever a
   "served orbit" exists (`Serv D u w j`, `:241`); when no served orbit occurs, the lattice is
   stabilized without loss (`stable_lattice_of_no_served_orbit`, `:486`). `KudlaFamilyStatement`
   (`:245`) and `ServF` (`:252`) package this local service across all units $u$ and chain steps $j$
   [Lean, read].
2. **Weyl / divided-power polynomial data and formal-group gain (`DataG` and `FormalGroupSystem.gA`, `src/Formalism/SharpRestriction/GrowthBounds/DataG.lean:11,33,106,163` and `…/FormalGroupSystem.lean:51,57,66`).**
   `DataG.lean` sets up the polynomial differential/divided-power modules (`deltaL` at `:11`, `Places`
   at `:33`, `Level` at `:106`, `GAtP` at `:163`) [Lean, read], while `FormalGroupSystem.lean` defines
   the supersingular slope $\mathrm{gam}(p) := \frac{p}{p^2 - 1}$ (`:51`) and the odd-power sum (`gA`,
   `:66`) [Lean]
   $$\mathrm{gA}(p, \alpha_s, \mathrm{cap}) := \sum_{e = 0}^{E_{\max}} \max\Bigl(\frac{\alpha_s}{p^{2e+1}} - \mathrm{cap},\ 0\Bigr).$$
3. **Connecting `gainD` to `vonMangoldtClassSum` (`src/Formalism/LocalRingCardinality/DataParams₂.lean:205,208,212,240`).**
   On the chain side (`SizeData₂`), `gainD` (`:208`) records the per-lift gain summed into
   `sg(u, w)` (`:212`), and `vonMangoldtClassSum` (`:240`) evaluates the odd-$i$ prime-power ramp
   [Lean, read]:
   $$\mathrm{vonMangoldtClassSum}(p, N, a_T, t, w_{\mathrm{Part}})
   := \sum_{\substack{1 \le i \le N \\ i\text{ odd}}} \max\Bigl(\frac{a_T(t)}{p^i} - w_{\mathrm{Part}}(i),\ 0\Bigr).$$
   Lemma `gainD_le_gainS` (`WeilJacquetShalikaLaw.lean:552`) proves that the arithmetic chain gain
   `gainD` is bounded above by the analytic formal-group gain `gainS` [Lean, read]!

---

## 8.4 Lemmas and proofs

We now give complete, hand-checkable proofs of the `R3`-verified deduction chain inside
`WeilJacquetShalikaLaw.lean` — showing how stepwise column divisibility telescopes across $m$ lifts
(`val_step`, `period_ge`) and how `off_level_bound` and `off_level_bound_family` prove `Conclusion1`
from `Serv` / `ServF` — followed by the bridge to `LinkDIVt` in `DIVRecBridgeSel.lean`.

### 8.4.1 Monotonicity and $m$-step valuation telescoping (`val_step`, `period_ge`)

**Lemma 8.1 (Monotonicity and additive composition of `VGe` across $m$ steps).** *Let $w$ be a
height-one prime of $\mathcal O_E$ with ramification index $e_w \ge 1$.*

1. **Monotonicity (`VGe_mono` and `ColGe_mono`, `WeilJacquetShalikaLaw.lean:325, 332`).** *If
   $s_1 \le s_2$ and `VGe D w Λ s₂ y` holds, then `VGe D w Λ s₁ y` holds; the same monotonicity holds
   for `ColGe`.* [Lean, read]
2. **Single-step composition (`vAdd_mul'` and `val_step`, `WeilJacquetShalikaLaw.lean:395, 401`).**
   *Let $T : V_1 \to V_2$ be an $\mathcal O_E$-linear map whose restriction to $\Lambda_{1,w}$
   satisfies $\forall z \in \Lambda_{1,w},\ \mathrm{VGe}(D, w, \Lambda_{2,w}, s_2, T(z))$. If
   $y \in V_1$ satisfies $\mathrm{VGe}(D, w, \Lambda_{1,w}, s_1, y)$, then*
   $$\mathrm{VGe}\bigl(D, w, \Lambda_{2,w}, s_1 + s_2, T(y)\bigr).$$
   [Lean, read]
3. **$m$-step induction (`period_ge`, `WeilJacquetShalikaLaw.lean:419`).** *Let $T_1, \dots, T_m$ be
   $m$ composable $\mathcal O_E$-linear maps with lattices $\Lambda_{0,w}, \Lambda_{1,w}, \dots, \Lambda_{m,w}$.
   If $y_0 \in V_0$ satisfies $\mathrm{VGe}(D, w, \Lambda_{0,w}, s_0, y_0)$ and each $T_j$
   ($1 \le j \le m$) maps $\Lambda_{j-1,w}$ into $\mathrm{VGe}(D, w, \Lambda_{j,w}, g_j, \cdot)$,
   then $y_m := (T_m \circ \cdots \circ T_1)(y_0)$ satisfies*
   $$\mathrm{VGe}\Bigl(D, w, \Lambda_{m,w},\ s_0 + \sum_{j=1}^m g_j,\ y_m\Bigr).$$
   [Lean, read]

*Proof.*

1. Suppose $y = a \cdot z$ with $a \in \mathcal O_E$, $z \in \Lambda$, and either $a = 0$ or
   $e_w s_2 \le v_w(a)$. Since $e_w \ge 0$ and $s_1 \le s_2$, we have $e_w s_1 \le e_w s_2$; hence
   either $a = 0$ or $e_w s_1 \le e_w s_2 \le v_w(a)$, giving `VGe D w Λ s₁ y` (`:325–331`).
2. Write $y = a_1 \cdot z_1$ with $a_1 \in \mathcal O_E$, $z_1 \in \Lambda_{1,w}$, and
   $(a_1 = 0 \lor e_w s_1 \le v_w(a_1))$. Applying the hypothesis on $T$ to $z_1 \in \Lambda_{1,w}$
   gives $T(z_1) = a_2 \cdot z_2$ with $a_2 \in \mathcal O_E$, $z_2 \in \Lambda_{2,w}$, and
   $(a_2 = 0 \lor e_w s_2 \le v_w(a_2))$. By $\mathcal O_E$-linearity of $T$,
   $$T(y) = T(a_1 \cdot z_1) = a_1 \cdot T(z_1) = (a_1 a_2) \cdot z_2.$$
   Clearly $a_1 a_2 \in \mathcal O_E$ and $z_2 \in \Lambda_{2,w}$. If $a_1 = 0$ or $a_2 = 0$, then
   $a_1 a_2 = 0$ and we are done. Otherwise $a_1 \neq 0$ and $a_2 \neq 0$; because $\mathfrak p_w$
   is a prime ideal in the Dedekind domain $\mathcal O_E$, the normalized valuation $v_w$ is
   additive on nonzero products (`vAdd_mul'`, `:395`):
   $$v_w(a_1 a_2) = v_w(a_1) + v_w(a_2) \ge e_w s_1 + e_w s_2 = e_w (s_1 + s_2).$$
   Thus `VGe D w Λ_{2,w} (s₁ + s₂) (T y)` holds (`val_step`, `:401–417`).
3. Apply induction on $k \in \{0, 1, \dots, m\}$ (`period_ge`, `:419–460`): the base case $k = 0$ is
   $\mathrm{VGe}(D, w, \Lambda_{0,w}, s_0, y_0)$, and the inductive step from $k - 1$ to $k$ applies
   part (2) with $s_1 = s_0 + \sum_{j=1}^{k-1} g_j$ and $s_2 = g_j$. $\square$

### 8.4.2 Discharging `Conclusion1` from local service (`off_level_bound` and `off_level_bound_family`)

Why is Lemma 8.1 not quite the whole proof of `Conclusion1`? Because in the chain datum `D`, there are
**three distinct kinds of places $w$**, and each behaves differently:

- **Unserved / split / out-of-range places:** where `gainS = 0` and no Kudla–Rallis orbit is served,
  one must verify that the step operator still preserves the integral lattice up to `-ES(u, j, w)`
  (`stable_lattice_of_no_served_orbit`, `:486`) so no uncontrolled denominators appear!
- **Ramified / exceptional places (`Exc D p` or `LocLe`):** handled by `nuIn_mem_Sram_of_locLe`
  (`:463`), keeping ramified-place losses inside the finite bad set `Sram`.
- **Good inert places (`¬ Exc D p` with a served orbit):** where `IntegralKernelValuation` supplies
  the positive gain `gainS(D, p, j) + F(j, w) - ES(u, j, w)` (`kernel_valuation_served`, `:348`).

The theorem `off_level_bound` (`WeilJacquetShalikaLaw.lean:504`) unifies all three cases and proves
`Conclusion1 D` unconditionally inside Lean (`R3`)!

**Theorem 8.2 (Proof of `WeilJacquetShalikaLaw.Conclusion1` from local kernel valuation: `off_level_bound` and `off_level_bound_family`).**

1. **Single-datum divisibility (`off_level_bound`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:504`).**
   *If `IntegralKernelValuation D` holds on served orbits and no-orbit steps stabilize the local
   lattice within `-ES`, then `Conclusion1 D` holds: under `Ties9 D` and stepwise service, every
   composite output column $y_m(u)$ satisfies*
   $$\mathrm{VGe}\bigl(D, w, \Lambda_{m,w},\ \mathrm{totS}(D, u, w),\ y_m(u)\bigr).$$
   [Lean, read]
2. **Gain comparison and family lift (`gainD_le_gainS` and `off_level_bound_family`, `WeilJacquetShalikaLaw.lean:552, 614`).**
   *Whenever the step parameters satisfy the sandwich bounds `SandwichE` / `EpDef`
   (`src/Formalism/SharpRestriction/GrowthBounds/DefsInst.lean:11,18`), the discrete chain gain
   satisfies $\mathrm{gainD}(p, j) \le \mathrm{gainS}(D, p, j)$ (`gainD_le_gainS`, `:552`), and
   `ServF` across a family implies the family-wide `DIV` divisibility clause at fractional ideal
   $I_u$ (`off_level_bound_family`, `:614`).* [Lean, read]

*Proof.*

1. Fix a unit index $u$ and a height-one prime $w$ of $\mathcal O_E$ lying over $p = w.\mathrm{natPrime}$.
   First check the base vector $y_0(u)$ at $j = 0$: if $\mathrm{sp} = 0$, then $\mathrm{sp}\cdot v_{\mathrm{DG}}(u, w) = 0$
   and $y_0(u) \in \Lambda_{0,w}$ gives $\mathrm{VGe}(D, w, \Lambda_{0,w}, 0, y_0(u))$ (with $a = 1$);
   if $\mathrm{sp} = 1$, `Ties9 D` supplies $\mathrm{VGe}(D, w, \Lambda_{0,w}, v_{\mathrm{DG}}(u, w), y_0(u))$.
   In both cases,
   $$\mathrm{VGe}\bigl(D, w, \Lambda_{0,w},\ \mathrm{sp}\cdot v_{\mathrm{DG}}(u, w),\ y_0(u)\bigr).$$
   Next, for each step $j \in \{1, \dots, m\}$, set
   $g_j := \mathrm{gainS}(D, p, j) + F(j, w) - \mathrm{ES}(u, j, w)$ and inspect the dichotomy on
   whether $(u, w, j)$ lies in a served orbit (`WeilJacquetShalikaLaw.lean:486–550`):
   - **Case A (served orbit):** `kernel_valuation_served` (`:348`) and `serv_of` (`:376`) invoke
     `IntegralKernelValuation` to conclude `ColGe D w j u g_j`.
   - **Case B (no served orbit):** By `GainZero D` (part of `Ties9 D`), $\mathrm{gainS}(D, p, j) + F(j, w) \le 0$
     outside served orbits, while `stable_lattice_of_no_served_orbit` (`:486`) gives
     `ColGe D w j u (-ES(u, j, w))`. Since $g_j \le -\mathrm{ES}(u, j, w)$, monotonicity
     `ColGe_mono` (Lemma 8.1(1)) yields `ColGe D w j u g_j` here as well!
   Now apply the $m$-step induction `period_ge` (Lemma 8.1(3)) with $s_0 = \mathrm{sp}\cdot v_{\mathrm{DG}}(u, w)$
   and step gains $g_1, \dots, g_m$: the composite column $y_m(u)$ satisfies `VGe` at order
   $$s_0 + \sum_{j=1}^m g_j = \mathrm{totS}(D, u, w),$$
   which is literally `Conclusion1 D`!
2. For `gainD_le_gainS` (`:552–604`), each odd-power summand $\max(a_T / p^{2e+1} - w_{\mathrm{Part}}, 0)$
   of `gainD` (`DataParams₂.lean:208, 240`) is compared term-by-term with the formal-group summand of
   `gainS` using $\alpha_s \ge a_T$ and $\mathrm{cap} \le w_{\mathrm{Part}}$ from `SandwichE`
   (`DefsInst.lean:11`). By Lemma 8.1(1) (`VGe_mono`), replacing `gainS` by the smaller quantity
   `gainD` preserves `VGe` at every $w \in \mathrm{supp}$; multiplying by $e_w = \mathrm{ramIdx}(w)$
   (`ur w`, Definition 8.1(1)) and taking integer floors shows that every column pairing lands in
   $\prod_{w \in \mathrm{supp}} \mathfrak p_w^{\lfloor e_w\,\mathrm{sg}(u, w) \rfloor}$, matching the
   fractional ideal $I_u^{-1}$ (`DataDIVDefs.lean:17`) across the whole family (`isCs_drop`, `:606`,
   and `off_level_bound_family`, `:614`). $\square$

### 8.4.3 Bridging `ServF` to the global divisibility input `LinkDIVt`

Finally, three short bridge files connect `off_level_bound_family` to the global chain assembly of
Chapter 7 (`TieGlobal.lean`) and Chapter 9 (`GlobalTheoremInputs.lean`):

**Proposition 8.3 (From local kernel rows and joint services to `LinkDIVt`).**

1. **Joint two-level lattice services (`JointAt` and `SecondLevelHypothesisFamily`, `src/Formalism/LocalToGlobal/GroupLattices/JointServices.lean:95,125,163`).**
   *Combines the inert-prime divisibility columns `ColBr` (`:13`) with the $2$-adic level congruence
   control `NPc` (`:72`, producing the `SZ.T4` term $\frac{k}{n^2}x^{2\varepsilon}$ of Chapter 5!)
   into a single local-lattice package across all places of $\mathcal O_E$.* [Lean, read]
2. **Closing `ServF` and `LinkDIVt` (`closed_servF_of_servT_of_dGamSize`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/GServT.lean:31`, and `closed_linkDIVt_of_closed_bridge_kernel`, `…/ThirdPlaceSeries/DIVRecBridgeSel.lean:197`).**
   *Given `DivisionKernelData` (`DIVRecBridgeSel.lean:32`) and uniform constant bounds
   `DivisionKernelConstantBounds` (`:166`) produced from the theta-lift rows `pkg_of_rowsK_alt` (`:113`),
   `closed_servF_of_servT_of_dGamSize` discharges `ServF`, and `linkDIVt_of_bridge_kernel` (`:193`) /
   `closed_linkDIVt_of_closed_bridge_kernel` (`:197`) combines `off_level_bound_family` with
   `SecondLevelHypothesisFamily` to inhabit the global divisibility link `LinkDIVt`
   (`GlobalTheoremInputs.lean:94`).* [Lean, read]

*(Statement-level boundary `[Lean]` / `[Open]`.)* Where is `DivisionKernelData` /
`IntegralKernelValuation` itself proved? Its proof passes through
`FormalGroupSystem.Conclusion1` and `Conclusion2`
(`src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:633, 650`),
`trueColumns_row_sharp_bounds`
(`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrueColumnsRowSharpBoundsStatement.lean:8`), and
`sum_over_primes_service` inside the `4,464`-module import cone of `DIVRecBridgeSel.lean`. We
inspected those theorem headers (`R2` / `[Lean]`), verifying that they contain no `sorry` or custom
axioms, while the internal formal-group and $p$-adic Whittaker/Siegel–Weil kernel calculations inside
that `4,464`-module cone have not yet been read line by line by us (`[Open]`).

---

## 8.5 Remarks, formalization notes, and Masullo's counterpart

### 8.5.1 Why `Conclusion1` is a `Prop` — and why reading `WeilJacquetShalikaLaw.lean` resolves its role

In early community summaries (including `notes/proof-map.md` prior to this chapter and LUMI's
`docs/02-proof-map.md`, which cited line 101, the closing line of `def Conclusion1` whose header sits
at line 97) [Community], `WeilJacquetShalikaLaw.Conclusion1` was sometimes referred to as if it were
itself the deep theorem proving $p$-adic theta-kernel vanishing. Reading all 633 lines of
`WeilJacquetShalikaLaw.lean` (`R3`, import cone **309** modules) clarifies the architecture
completely [Lean, read]:

- `Conclusion1` (`:97`) is the **clean inductive specification** stating that *stepwise* kernel
  divisibility implies *$m$-step* divisibility at order `totS`;
- `off_level_bound` (`:504`) and `off_level_bound_family` (`:614`) **prove** that implication in full
  inside `WeilJacquetShalikaLaw.lean` by elementary Dedekind-domain valuation algebra (`val_step`,
  `period_ge`, `VGe_mono`);
- the **genuine arithmetic-geometric depth** (Lubin–Tate / formal-group height-$2$ divided-power
  estimates on supersingular unitary/CM reductions at inert primes, descending from `[Katz1976]` and
  local Kudla–Rallis theory `[KudlaRallis1994]`) lives one layer further upstream, in supplying
  `IntegralKernelValuation` / `DivisionKernelData` (`FormalGroupSystem.lean` and the `4,464`-module
  cone of `DIVRecBridgeSel.lean`) [Lean].

### 8.5.2 Why even powers of $p$ cancel and why ramified primes are harmless

Two small structural points save readers hours of puzzlement [Expository]:

1. **Why only odd powers $p^{2e+1}$ appear in `ASK` (`FirstPrimeNeSecondPrime.lean:76`) and
   `FormalGroupSystem.gA` (`:66`).** On the analytic Fourier side (Chapter 5, Theorem 5.1), an
   inert prime $p$ has Frobenius element $\mathrm{frob}(p) \in \Phi^c$ (first bit $1$ in
   $\mathbb Z/2\mathbb Z$), so $i \cdot \mathrm{frob}(p)$ lands in $\Phi^c$ **if and only if $i$ is
   odd**; even powers $p^{2e}$ have $2e \cdot \mathrm{frob}(p) \in \Phi$ and cancel out of `De`! On
   the $p$-adic formal-group side (Section 8.1), $\frac{1}{p - 1} - \frac{1}{p^2 - 1} = \frac{p}{p^2 - 1} = \sum_{e \ge 0} p^{-(2e+1)}$
   produces the **exact same odd-power series**! That miraculous agreement between finite abelian
   Fourier parity on $\operatorname{Gal}(E/\mathbb Q)$ and height-$2$ Lubin–Tate Newton polygons is
   the heartbeat of the entire proof.
2. **Why `Exc D p` (`p ∣ condN * g₀ * g₁`) causes zero trouble.** Primes dividing $2$, $q$, or
   $\psi.N$ were arranged in Chapter 4 (Lemma 4.1(2)) to **split** in $K = \mathbb Q(\sqrt{-d})$, so
   they contribute $0$ to `ASK` anyway; the single ramified prime $d \asymp \exp(Y^{\varepsilon/5}(\log Y)^2)$
   can exceed the prime truncation $N$ or be absorbed into `Sram` (`nuIn_mem_Sram_of_locLe`, `:463`),
   and the fixed auxiliary Green primes $g_0, g_1$ contribute at most $O(1)$ bounded error.

### 8.5.3 Masullo's counterpart

Masullo's draft *The Music of the Primes* has **no counterpart** to inert-prime $p$-adic divisibility,
supersingular CM reductions, Lubin–Tate formal groups, or `Conclusion1` [Expository]:

- In **Chapter 2 ("Adelic $\theta$-functions", pp. 57, 74–78)** [Paper; Masullo pp. 57, 74–78], local
  places $v \nmid \infty$ enter only through standard Bruhat–Schwartz indicator functions
  $\mathbf{1}_{\mathcal O_{F_v}}$ in Tate's $\mathrm{GL}_1$ local zeta integrals `[Tate1967]`, with no
  distinction between split and inert primes in an auxiliary CM extension and no $p$-adic valuation
  cascades.
- In **Chapter 14, Section 14.2 ("Function fields", pp. 534–536)** [Paper; Masullo pp. 534–536],
  Masullo discusses $\mathbb F_q(X)$ only to explain why his archimedean shell/trace method breaks
  down when all places are non-Archimedean — the exact opposite of Stepanov's method, which is native
  to $\mathbb F_q(X)$ and which the Lean archive transports to $\mathbb Z$ via $p$-adic divisibility
  at inert primes!

---

## 8.6 Lean counterpart for this chapter

| Declaration | File:line | Mathematical content / role in Sections 8.3–8.4 | Tag |
|---|---|---|---|
| `VGe`, `ColGe0`, `ColGeTw`, `ColGe`, `Exc`, `gainS`, `g0S`, `GainZero`, `InNP`, `vDG`, `lowS`, `totS`, `TwLoc`, `Ties9`, `Conclusion1` | `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:19,24,28,33,37,49,54,57,60,67,73,76,79,92,97` | Definitions 8.1–8.2: local lattice valuation `VGe`, column divisibility `ColGe`, exceptional primes `Exc`, accumulated $m$-step gain `totS`, structural bundle `Ties9`, and `Conclusion1`. | [Lean, read] |
| `IntegralKernelValuation`, `admitted`, `Stmt`, `Serv`, `KudlaFamilyStatement`, `ServF`, `PairInt` | `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:113,224,234,241,245,252,383` | Definition 8.3(1): local kernel valuation predicate on served Kudla orbits and family service `ServF`. | [Lean, read] |
| `VGe_mono`, `ColGe_mono`, `kernel_valuation_served`, `serv_of`, `vAdd_mul'`, `val_step`, `period_ge`, `nuIn_mem_Sram_of_locLe`, `stable_lattice_of_no_served_orbit`, `off_level_bound`, `gainD_le_gainS`, `isCs_drop`, `off_level_bound_family` | `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:325,332,348,376,395,401,419,463,486,504,552,606,614` | Lemma 8.1 and Theorem 8.2: monotonicity, $m$-step valuation telescoping, lattice stability off served orbits, proof of `Conclusion1`, comparison `gainD ≤ gainS`, and family `DIV` bound. | [Lean, read] |
| `MramL`, `ur`, `Iu`, `NprimeDef`, `LocLe`, `NuDef`, `hExpl` | `src/Formalism/LocalRingCardinality/DataDIVDefs.lean:12,15,17,22,31,48,89` | Definition 8.1(1): ramification-scaled threshold `ur w s = ramIdx w * s`, fractional ideal $I_u = \prod_w \mathfrak p_w^{-\lfloor e_w \mathrm{sg}(u,w)\rfloor}$, and prime truncation `NprimeDef`. | [Lean, read] |
| `Scale`, `lpFeasible`, `lpF`, `SizeData₂`, `sz`, `lifts`, `gainD`, `sg`, `Fo`, `Ga`, `MAIN`, `vonMangoldtClassSum` | `src/Formalism/LocalRingCardinality/DataParams₂.lean:9,51,58,76,205,208,212,215,218,220,232,240` | Definition 8.3(3): chain step gains `gainD`, total place gain `sg`, and odd-power prime ramp `vonMangoldtClassSum` matching Chapter 5's `ASK`. | [Lean, read] |
| `Extra` | `src/Formalism/LocalRingCardinality/DataExtra.lean:40` | Auxiliary slack record accompanying `DataParams₂`. | [Lean, read] |
| `SandwichE`, `EpDef`, `kapISet`, `KapIDef` | `src/Formalism/SharpRestriction/GrowthBounds/DefsInst.lean:11,18,38,54` | Theorem 8.2(2): parameter sandwich inequalities ensuring `gainD ≤ gainS`. | [Lean, read] |
| `deltaL`, `Places`, `Level`, `GAtP` | `src/Formalism/SharpRestriction/GrowthBounds/DataG.lean:11,33,106,163` | Definition 8.3(2): Weyl / divided-power polynomial data at prime $p$. | [Lean, read] |
| `ColBr`, `NPc`, `JointAt`, `SecondLevelHypothesisAt`, `SecondLevelHypothesisFamily` | `src/Formalism/LocalToGlobal/GroupLattices/JointServices.lean:13,72,95,125,163` | Proposition 8.3(1): merges inert-prime column divisibility with $2$-adic level congruence control `NPc`. | [Lean, read] |
| `SelectionServed`, `closed_servF_of_servT_of_dGamSize` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/GServT.lean:13,31` | Proposition 8.3(2): discharges `ServF` from served orbit selection and gamma-factor bounds. | [Lean, read] |
| `DivisionKernelData`, `pkg_of_rowsK_alt`, `DivisionKernelConstantBounds`, `linkDIVt_of_bridge_kernel`, `closed_linkDIVt_of_closed_bridge_kernel` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:32,113,166,193,197` | Proposition 8.3(2): assembles `LinkDIVt` from `off_level_bound_family` and `SecondLevelHypothesisFamily` (import cone 4,464). | [Lean, read] |
| `gam`, `gB`, `gA`, `Conclusion1`, `Conclusion2`; `trueColumns_row_sharp_bounds` | `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:51,57,66,633,650`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrueColumnsRowSharpBoundsStatement.lean:8` | Definition 8.3(2) (`R2`): supersingular height-$2$ slope $\frac{p}{p^2-1} = \sum_{e \ge 0} p^{-(2e+1)}$, odd-power gain `gA`, and upstream kernel-valuation theorems (internal proof bodies unread `[Open]`). | [Lean] |

**Summary of the chapter.** At primes $p$ inert in the imaginary quadratic core $K = \mathbb Q(\sqrt{-d})$,
supersingular height-$2$ formal groups have $D^p \equiv 0 \pmod p$ and Newton-polygon slope
$\frac{1}{p^2 - 1}$, whose difference from Legendre's factorial slope $\frac{1}{p - 1}$ equals
$\frac{p}{p^2 - 1} = \frac{1}{p} + \frac{1}{p^3} + \frac{1}{p^5} + \dots$ `[Katz1976]`, generating
the odd-power Riesz ramp `vonMangoldtClassSum` / `ASK` while split primes contribute zero [Expository].
In `WeilJacquetShalikaLaw.lean`, `Conclusion1` (`:97`) formulates how stepwise kernel valuation gains
accumulate to $m$-step column divisibility `totS`, and `off_level_bound` (`:504`) plus
`off_level_bound_family` (`:614`) prove this implication in full via `val_step` and `period_ge`,
feeding `LinkDIVt` (`DIVRecBridgeSel.lean:197`) [Lean, read]. In Chapter 9 we see how Bost's
Arakelov slope inequality converts this local $\mathfrak p_w$-adic divisibility into a global
numerical inequality!
