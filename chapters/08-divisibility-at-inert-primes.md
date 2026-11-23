# Chapter 8. Divisibility at inert primes

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs
> verified line by line in `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`, `DataDIVDefs.lean`, `DataParams₂.lean`,
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
Alpöge's note records at the very start of its timeline (*"10/9/26: $D^p \equiv 0$ on a CM curve
for $p$ inert in $K$, $D$ the invariant derivation, and $D^a \Omega \cdot \vartheta(0)$ is divisible by
$p^{a/p + a/p^3 + \dots - O(\log a)}$."*, `remark.pdf` p. 3, item 2) [Paper; remark p. 3], classical arithmetic
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
   $\max(\alpha_s / p^{2e+1} - \mathrm{cap}, 0)$ (`gA` at `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:66`, matching
   `vonMangoldtClassSum` at `src/Formalism/LocalRingCardinality/DataParams₂.lean:240`) [Lean, read].
   Multiplying by $\log p$ and summing over primes $p$ inert in $E/\Phi$ reproduces **term for term**
   the Riesz-weighted inert prime sum `ASK` of Chapter 5 (Definition 5.1(3))!

---

## 8.2 Worked examples

Before entering the Lean declarations, let us verify both halves of this phenomenon by hand: first on
Gauss's lemniscate curve over $\mathbb Z[i]$, and then on a finite $3$-adic column-divisibility model
matching `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean` [Expository].

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

Now let us see how `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean` packages local $p$-adic divisibility across a chain
of $m$ steps and pairs the resulting $m$-step column against an automorphic period functional
[Expository]. Take the coefficient number field $L = \mathbb Q(i)$ (`D.what₂.LL`) with ring of
integers $\mathcal O_L = \mathbb Z[i]$ at the unramified inert prime $p = 3$ (ramification index
$e_w = 1$, uniformizer $\varpi_w = 3$, additive valuation $v_w = v_3 : L^\times \to \mathbb Z$), and
let $\Lambda = \mathbb Z[i]^2 \subset L^2$ with $\mathcal O_{(w)}$-localization
$\Lambda_w = \mathbb Z_{(3)}[i]^2$ (`locW`). In `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:19–22`, an element
$y \in L^2$ satisfies `VGe D w Λ y s` (note the parameter order `(y, s)` for $s \in \mathbb R$) if
$y = a \cdot z$ for some field scalar $a \in L$ and localized lattice vector $z \in \Lambda_w$ with
either $a = 0$ or $e_w s \le v_w(a)$. Allowing $a \in L$ (rather than restricting $a$ to $\mathcal O_L$)
lets the same predicate express both **positive divisibility** ($s > 0$, e.g. $3^{\lceil s \rceil} \mid y$
in $\Lambda_w$) and **controlled denominator bounds** ($s < 0$, such as $s = -v_{\mathrm{DG}}$ in
`IntegralKernelValuation` at `:113`).

Suppose a $2$-step chain ($m = 2$) of kernel operators $K_0, K_1 : L^2 \to L^2$ has served-orbit
gains $g_1 = 4$ and $g_2 = 3$ with zero error slack, plus a base denominator scale $v_{\mathrm{DG}} = 1$:

- Upstream formal-group / Kudla–Rallis analysis (packaged as the input implication `Conclusion1` at
  `:97` with sparsity switch $\mathrm{sp} = 1$) combines the two steps into a single bound on the
  **composite $m$-step column** $C_{\mathrm{col}}(x) = (K_1 \circ K_0)(x)$: for admissible inputs $x$,
  its output $y = C_{\mathrm{col}}(x)$ satisfies `VGe D w Λ y (4 + 3 + 1)` (`ColGe` at `:33`, with
  order $\mathrm{totS} = 4 + 3 + 1 = 8$, i.e. $y = 3^8 z$ with $z \in \Lambda_w$).
- Next, pairing $z \in \Lambda_w$ against a test form $F$ via the period map produces a scalar
  $y_0 \in L$ that can lose at most $3^{-v_{\mathrm{DG}}} = 3^{-1}$ (`PairInt`, `:383–393`:
  $-1 \le v_3(y_0)$). Multiplying $a = 3^8$ by $y_0$ via `val_step` (`:401`) and `period_ge`
  (`:419–437`) cancels the $-v_{\mathrm{DG}}$ pairing denominator against the $+v_{\mathrm{DG}}$ in
  $\mathrm{totS}$, yielding period value $a y_0 \in L$ of valuation $v_3(a y_0) \ge 8 - 1 = 7 = g_1 + g_2$!

And what numerical gain does the archive assign to an inert prime $p = 3$ at top scale $a_T = 100$
and place weight $w_{\mathrm{Part}} = 2$ (`vonMangoldtClassSum`, `src/Formalism/LocalRingCardinality/DataParams₂.lean:240`)? Sum
$\max(a_T / 3^{2e+1} - w_{\mathrm{Part}}, 0)$ over $e = 0, 1, 2, \dots$:

- $e = 0$ ($3^1 = 3$): $\max\bigl(\frac{100}{3} - 2,\ 0\bigr) = \frac{94}{3}$;
- $e = 1$ ($3^3 = 27$): $\max\bigl(\frac{100}{27} - 2,\ 0\bigr) = \frac{46}{27}$;
- $e \ge 2$ ($3^5 = 243$): $\frac{100}{243} - 2 < 0$, so every term with $e \ge 2$ is **identically $0$**!

Thus the finite odd-power sum terminates automatically at $3^{2e+1} \le a_T / w_{\mathrm{Part}} = 50$,
producing total logarithmic gain $\log 3 \cdot \bigl(\frac{94}{3} + \frac{46}{27}\bigr) = \frac{892}{27}\log 3$.
Compare that formula with Chapter 5's `askP` (`src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:75`): **they are the
exact same function**!

---

## 8.3 Definitions

We now present the exact Lean definitions of node **P8** and its surrounding local-to-global
interfaces.

### 8.3.1 Ramification scaling, fractional ideals `Iu`, and column divisibility (`VGe`, `ColGe`)

Let $L = D.\mathrm{what}_2.\mathrm{LL}$ be the coefficient number field attached to the chain datum
$D$ (over the CM host $D.\mathrm{host}.E$), with ring of integers $\mathcal O_L$. At each finite place
$w \in D.\mathrm{what}_2.\mathrm{places}.\mathrm{Pl}$ (identified via `D.plEq w` with a height-one
prime $\mathfrak p_w \in \mathrm{HeightOneSpectrum}(\mathcal O_L)$ of residue characteristic
$p = \mathrm{resChar}(w)$), let $e_w = \mathrm{ramIdx}(w) \ge 1$ denote the ramification index of $w$
over $p$, and let $v_w : L^\times \to \mathbb Z$ denote the normalized additive $\mathfrak p_w$-adic
valuation (`vAdd (D.plEq w) a`).

**Definition 8.1 (Unramified-scaled valuation thresholds and fractional ideals, `src/Formalism/LocalRingCardinality/DataDIVDefs.lean:15,17,22,31,48` and `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:19,24,28,33,37`).**

1. **Ramification scaling, fractional ideal `Iu`, and lattice span `NprimeDef` (`ur`, `Iu`, `NprimeDef`, `src/Formalism/LocalRingCardinality/DataDIVDefs.lean:15, 17, 22`).**
   For a place $w$ and $s \in \mathbb R$, set [Lean, read]
   $$\mathrm{ur}(D, w, s) := e_w \cdot s.$$
   Given a finitely supported place-gain function $g : w \mapsto \mathrm{sg}(u, w) \ge 0$ supported
   on a finite set $\mathrm{supp}$, define the fractional ideal (`Iu`, `:17`)
   $$I_u := \prod_{w \in \mathrm{supp}} \mathfrak p_w^{-\lfloor e_w\,\mathrm{sg}(u, w) \rfloor}$$
   as a fractional ideal of $L$ (`FractionalIdeal (𝓞 L)⁰ L`), and let `NprimeDef` (`:22`) denote the
   module-span identity `(D.div.Nu u).L = Submodule.span (𝓞 L) ↑(Iu u supp sg • NuLat u)` identifying
   the rescaled source lattice `(D.div.Nu u).L` with the fractional-ideal twist $I_u \cdot \mathrm{NuLat}(u)$.
   Saying that a period pairing maps $\mathrm{NuLat}(u)$ into elements of valuation $\ge \lfloor e_w\,\mathrm{sg}(u,w) \rfloor$
   means precisely that multiplying by $I_u$ preserves $\mathcal O_L$-integrality at every $w \in \mathrm{supp}$!
2. **Scalar-lattice divisibility (`VGe`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:19`).** Given an $\mathcal O_L$-submodule
   $\Lambda \subseteq V$ of an $L$-vector space $V$, a place $w$ with localization
   $\mathrm{locW}_w(\Lambda) \subseteq V$, an element $y \in V$, and $s \in \mathbb R$, the predicate
   `VGe D w Λ y s` holds if there exist a field scalar $a \in L$ and $z \in \mathrm{locW}_w(\Lambda)$
   such that [Lean, read]
   $$y = a \cdot z \qquad\text{and}\qquad \bigl(a = 0 \ \lor\ e_w \cdot s \le v_w(a)\bigr).$$
   Because $a$ ranges over the field $L$ (not merely $\mathcal O_L$), `VGe D w Λ y s` uniformly
   handles both positive divisibility ($s \ge 0$) and bounded $\mathfrak p_w$-adic denominators ($s < 0$).
3. **Untwisted and tuple-twisted $m$-step composite column divisibility (`ColGe0`, `ColGeTw`, `ColGe`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:24, 28, 33`).**
   Notice that `ColGe T u μ w x s` carries **no step index $j$**: it constrains the **entire $m$-step
   composite column** from step $0$ (`lat 0`) to step $m = D.R.m$ (`lat D.R.m`) at word $u$ and
   twisting tuple $\mu \in D.\mathrm{what}_2.\mathrm{Tup}$! Specifically, for $x \in ((D.\mathrm{fm}\,u).\mathrm{lat}\,0).V$:
   - when $\mu = \mu_0$ is the untwisted reference tuple, `ColGe0 D u w x s` (`:24`) asserts that the
     composite column `(D.mem u).C.col` sends the embedded vector $x$ to an element $y$ on `lat D.R.m`
     satisfying `VGe D w ((D.fm u).lat D.R.m).L y s`;
   - when $\mu \neq \mu_0$, `ColGeTw T u μ w x s` (`:28`) asserts the same `VGe` bound at order $s$
     for the twisted $m$-step composite column `(D.chTw u μ).col` in `((T.fm u μ).lat D.R.m).L`;
   - `ColGe T u μ w x s` (`:33`) conjoins `(μ = μ₀ → ColGe0 D u w x s)` and
     `(μ ≠ μ₀ → ColGeTw T u μ w x s)` [Lean, read].
4. **Exceptional primes (`Exc`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:37`).** A rational prime $p$ is
   **exceptional** (`Exc D p`) if $p$ divides $\mathrm{condN} \cdot g_0 \cdot g_1$, where
   $\mathrm{condN}$ is the host field conductor and $g_0, g_1$ are the auxiliary finite-field
   Green primes of Chapter 7 (`LabelDatum`) [Lean, read].

### 8.3.2 Stepwise gains, `InNP`, `Ties9`, and `WeilJacquetShalikaLaw.Conclusion1`

Next we read lines 49–102 of `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean` verbatim (`R3`). Pay close attention to the
logical type and role of `Conclusion1`: **it is a `def ... : Prop` stating the $m$-step composite
column implication, and inside `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean` it enters `off_level_bound` as an explicit
hypothesis supplied from upstream** [Lean, read]!

**Definition 8.2 (Accumulated gain `totS`, input predicate `InNP`, compatibility `Ties9`, and `Conclusion1`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:49,57,60,67,73,76,79,92,97`).**
Let `D` be a chain datum of length $m = D.R.m$ (`lifts = Icc 1 m`) with `L : SizeData₂ D`:

1. **Stepwise gain, total $m$-step order, and initial-vector predicate (`gainS`, `totS`, `InNP`, `:49, 60, 76`).**
   At residue characteristic $p = \mathrm{resChar}(w)$ and lift step $j \in \{1, \dots, m\}$,
   `gainS X K p j` (`:49`) denotes the real local valuation gain assigned to $(p, j)$ (vanishing under
   `GainZero D L p`, `:57`), accompanied by the adjustment `L.F j w`, the error slack `ES L Xe K ce u j w`,
   and the base-denominator valuation `vDG D u w = v_p(DGam)` (`:67`) weighted by $\mathrm{sp} \in \mathbb R$.
   Their $m$-step total at $(u, w)$ is [Lean, read]
   $$\mathrm{totS}(X, K, X_e, c_e, \mathrm{sp}, u, w) := \sum_{j = 1}^m \bigl(\mathrm{gainS}(X, K, \mathrm{resChar}(w), j) + L.F(j, w) - \mathrm{ES}(u, j, w)\bigr)
   + \mathrm{sp} \cdot v_{\mathrm{DG}}(D, u, w).$$
   Meanwhile, `InNP X Y K c u w x` (`:60–63`) is a **vector predicate on initial step-$0$ inputs
   $x \in ((D.\mathrm{fm}\,u).\mathrm{lat}\,0).V$**: it holds if either there is a good orbit index
   `hg : GIdx ...` such that `c.cmp u w hg x ∈ NP X Y K u w hg`, or no orbit is active at $w$
   (`VV ... = ∅`) and $x$ lies in the ramified/integral span `LT.Sram D u w` [Lean, read].
2. **Compatibility bundle (`Ties9`, `:92–95`).** `Ties9 D L X Y c : Prop` is a three-field structure
   conjoining `tied : ∃ hT : GatTies D, LatTied hT X Y` (tying the formal-group/polynomial data $X$ to
   the lattice filtration data $Y$), `vram : c.VramDef Y`, and `fdef : L.FDef` [Lean, read].
3. **The composite column divisibility proposition (`WeilJacquetShalikaLaw.Conclusion1`, `:97–101`).**
   `Conclusion1 D L X Y K c Dx T lev Xe ce sp : Prop` is the conditional implication [Lean, read]:
   $$\mathrm{Ties9}(D, L, X, Y, c) \longrightarrow \mathrm{ErrDefs}(D, L, X_e, \mathrm{lev}, K, c_e) \longrightarrow$$
   $$\forall u,\ w \ (\mathrm{resChar}(w) \neq T_u,\ g_0,\ g_1),\ \forall \mu \in \mathrm{Used}(D) \ (\mathrm{resChar}(w) \notin Q_p(\mu)),$$
   $$\forall x,\ \mathrm{InNP}(X, Y, K, c, u, w, x) \longrightarrow \mathrm{ColGe}\bigl(T, u, \mu, w, x, \mathrm{totS}(X, K, X_e, c_e, \mathrm{sp}, u, w)\bigr).$$
   Notice that `Conclusion1` has **no per-step $j$ quantifier in its antecedent**: it directly asserts
   that under `Ties9` and `ErrDefs`, every initial vector $x$ satisfying `InNP` at $(u, w)$ is mapped
   by the $m$-step composite column to order `totS` (`ColGe`).

### 8.3.3 Single-step non-loss (`IntegralKernelValuation`), served growth (`Serv`, `ServF`), and `vonMangoldtClassSum`

How do single-step theta kernels feed `Conclusion1` upstream of `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`, and how
does `gainS` connect to `ASK`?

**Definition 8.3 (Kernel valuation, Kudla family service, Weyl divided powers, and the odd-power ramp, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:113,137,146,234,241,245,252`, `src/Formalism/SharpRestriction/GrowthBounds/DataG.lean:11,163`, `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:51,66`, and `src/Formalism/LocalRingCardinality/DataParams₂.lean:208,240`).**

1. **Single-step denominator control versus served-orbit growth (`IntegralKernelValuation`, `LatticeGrowthAtPlace`, `Stmt`, `Serv`, `ServF`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:113, 137, 146, 234, 241, 245, 252`).**
   In `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`, single-step denominator control and positive inert-prime growth
   are cleanly separated [Lean, read]:
   - `IntegralKernelValuation D Dx T sp` (`:113–121`) states only the **single-step non-loss bound**
     away from $\{d, g_0, g_1, T_u\}$: for each step $i < m$ and each integral vector $x \in (\mathrm{lat}\,i).L$,
     the $i$-th kernel operator $K_i$ produces $y$ on $\mathrm{lat}(i + 1)$ satisfying
     `VGe D w (lat (i + 1)).L y (-((if i = 0 then 1 - sp else 1) * vDG D u w))` (and similarly for
     twisted `chTw u μ` away from $Q_p(\mu)$).
   - Positive inert-prime valuation gains enter through `TupleLatticeValuation` (`:137`) and
     `LatticeGrowthAtPlace` (`:146`, verified under `IntegralKernelValuation` on served orbits by
     `kernel_valuation_served` at `:348`). Above them, `Stmt` (`:234`), `Serv` (`:241`),
     `KudlaFamilyStatement` (`:245`), and `ServF` (`:252`) bundle `Conclusion1` (at $\mathrm{sp} = 1$)
     together with `ColumnValuationAwayFromTypePrimes` (`:108`, used when no served orbit occurs in
     `stable_lattice_of_no_served_orbit`, `:486`) across the family!
2. **Weyl / divided-power polynomial data and formal-group gain (`DataG` and `FormalGroupSystem.gA`, `src/Formalism/SharpRestriction/GrowthBounds/DataG.lean:11,33,106,163` and `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:51,57,66`).**
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
   Lemma `gainD_le_gainS` (`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:552`) proves that the arithmetic chain gain
   `gainD` is bounded above by the analytic formal-group gain `gainS` [Lean, read]!

---

## 8.4 Lemmas and proofs

We now give complete, hand-checkable proofs of the `R3`-verified deduction chain inside
`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean` — showing how `val_step` (`:401`) and `period_ge` (`:419–437`) pair a
composite column bound `ColGe` against period functionals (`PairInt`), and how `off_level_bound`
(`:504`) and `off_level_bound_family` (`:614`) deduce period valuation lower bounds at order
`L.sg u w` **assuming `(h : Conclusion1 ... 1)` as an explicit input hypothesis** — followed by the
upstream bridge supplying `Conclusion1` and `LinkDIVt` in `DIVRecBridgeSel.lean`.

### 8.4.1 Monotonicity, denominator cancellation `val_step`, and period pairing `period_ge`

**Lemma 8.1 (Monotonicity, scalar denominator cancellation, and period pairing).** *Let $w$ be a
place of $L = D.\mathrm{what}_2.\mathrm{LL}$ with ramification index $e_w \ge 1$ and additive
valuation $v_w : L^\times \to \mathbb Z$.*

1. **Monotonicity (`VGe_mono` and `ColGe_mono`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:325, 332`).** *If
   $s_1 \le s_2$ and `VGe D w Λ y s₂` holds, then `VGe D w Λ y s₁` holds; the same monotonicity holds
   for `ColGe T u μ w x s`.* [Lean, read]
2. **Field-product valuation with denominator offset (`vAdd_mul'` and `val_step`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:395, 401`).**
   *Let $a, y_0 \in L$ and $s, v \in \mathbb R$. If $(a = 0 \lor \mathrm{ur}(D, w, s) \le v_w(a))$ and
   $(y_0 = 0 \lor -\mathrm{ur}(D, w, v) \le v_w(y_0))$, then*
   $$a y_0 = 0 \ \lor\ \mathrm{ur}(D, w, s - v) \le v_w(a y_0).$$
   [Lean, read]
3. **Pairing a composite column against a period functional (`period_ge`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:419–437`).**
   *Assume period-pairing integrality `PairInt D Dx T` (`:383–393`) and `DGamDef D`, so pairing any
   localized step-$m$ lattice vector $z \in \mathrm{locW}_w((\mathrm{lat}\,m).L)$ with an admissible
   form $F \in \widetilde M(\mu) \cap V_0(\mu)$ yields a scalar $y_0 \in L$ with
   $y_0 = 0 \lor -\mathrm{ur}(D, w, v_{\mathrm{DG}}(D, u, w)) \le v_w(y_0)$. If $\varphi \in (D.\mathrm{div}.\mathrm{Nu}\,u).V$
   satisfies the composite column bound `ColGe T u μ w (D.nuIn u φ) s` (away from $T_u$ and
   $Q_p(\mu)$), then `D.what₂.perCol u μ (D.jN u φ) F` equals the image of some $y \in L$ satisfying*
   $$y = 0 \ \lor\ \mathrm{ur}\bigl(D, w, s - v_{\mathrm{DG}}(D, u, w)\bigr) \le v_w(y).$$
   [Lean, read]

*Proof.*

1. Suppose $y = a \cdot z$ with $a \in L$, $z \in \mathrm{locW}_w(\Lambda)$, and either $a = 0$ or
   $e_w s_2 \le v_w(a)$. Since $e_w \ge 0$ and $s_1 \le s_2$, we have $e_w s_1 \le e_w s_2$; hence
   either $a = 0$ or $e_w s_1 \le e_w s_2 \le v_w(a)$, giving `VGe D w Λ y s₁` (`:325–331`), and
   unfolding `ColGe` gives `ColGe_mono` (`:332–336`).
2. If $a = 0$ or $y_0 = 0$, then $a y_0 = 0$ (`zero_mul` / `mul_zero`, `:404–411`). Otherwise
   $a \neq 0$ and $y_0 \neq 0$; by additivity of $v_w$ on $L^\times$ (`vAdd_mul'`, `:395–399`),
   $$v_w(a y_0) = v_w(a) + v_w(y_0) \ge e_w s + (-e_w v) = e_w(s - v) = \mathrm{ur}(D, w, s - v),$$
   proving `val_step` (`:401–417`).
3. Notice that `period_ge` (`:419–437`) performs **no induction on $m$** — the $m$-step composition is
   already inside `ColGe`! Splitting by cases on $\mu = \mu_0$ versus $\mu \neq \mu_0$ (`:426`),
   unpacking `ColGe T u μ w (D.nuIn u φ) s` produces $y_{\mathrm{col}} = a \cdot z$ on `lat D.R.m`
   with $a \in L$, $z \in \mathrm{locW}_w((\mathrm{lat}\,m).L)$, and
   $(a = 0 \lor \mathrm{ur}(D, w, s) \le v_w(a))$. Applying `PairInt` (`:429, 434`) to $z$ and $F$
   produces $y_0 \in L$ representing the period pairing of $z$ with $F$ and satisfying
   $(y_0 = 0 \lor -\mathrm{ur}(D, w, v_{\mathrm{DG}}) \le v_w(y_0))$. By $L$-linearity of the period
   pairing (`perCol_base_eq_PtilCol` / `perCol_tie`, `:431, 436`), the period value of $\varphi$ is
   represented by the field product $y := a y_0 \in L$, and part (2) (`val_step`) immediately gives
   $y = 0 \lor \mathrm{ur}(D, w, s - v_{\mathrm{DG}}) \le v_w(y)$. $\square$

### 8.4.2 Deducing period bounds from `Conclusion1` (`off_level_bound` and `off_level_bound_family`)

Now look closely at lines 504–630 of `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean` (`R3`). **`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
does not prove `Conclusion1` itself!** Instead, both `off_level_bound` (`:504`) and
`off_level_bound_family` (`:614`) take `(h : Conclusion1 ... 1)` (at sparsity weight $\mathrm{sp} = 1$)
**as an explicit input hypothesis**, verify the antecedent `InNP` on $\varphi \in \mathrm{NuLat}(u)$
across empty and non-empty orbit sets `VV`, cancel the $+1 \cdot v_{\mathrm{DG}}$ in `totS` against
the $-v_{\mathrm{DG}}$ from `period_ge`, and replace `gainS` by `gainD` to obtain the period valuation
bound at order `L.sg u w` [Lean, read]!

**Theorem 8.2 (From input `Conclusion1` to period valuation bounds at `sg`: `off_level_bound`, `gainD_le_gainS`, and `off_level_bound_family`).**

1. **Single-datum period valuation bound (`off_level_bound`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:504`).**
   *Assume `PairInt D Dx T`, `ErrDefs`, `Ties9 D L X Y c`, `NuServedDef`, local integrality
   `LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)` away from $T_u$, orbit indexing `hGI` when
   `VV ≠ ∅`, stepwise dominance `L.gainD j w ≤ gainS X K (resChar w) j`, and the input hypothesis
   `(h : Conclusion1 D L X Y K c Dx T lev Xe ce 1)`. Then for every $u$, every place $w$ with
   $\mathrm{resChar}(w) \notin \{T_u, g_0, g_1\}$, every $\varphi \in L.\mathrm{NuLat}(u)$, and every
   admissible test form $F$ at $\mu_w = D.\mathrm{what}_2.\mathrm{muAt}(w)$, there exists $y \in L$
   representing `perCol u μ_w (D.jN u φ) F` such that*
   $$y = 0 \ \lor\ \mathrm{ur}\bigl(D, w, L.\mathrm{sg}(u, w)\bigr) \le v_w(y).$$
   [Lean, read]
2. **Gain comparison and family lift (`gainD_le_gainS`, `isCs_drop`, and `off_level_bound_family`, `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:552, 606, 614`).**
   *Whenever `(hF : ∀ w, ParametersFill X K w)` holds and `IsCs` primes lie in `L.drop` (`isCs_drop`,
   `:606`), the chain gain satisfies $L.\mathrm{gainD}(j, w) \le \mathrm{gainS}(X, K, \mathrm{resChar}(w), j)$
   (`gainD_le_gainS`, `:552–575`). Consequently, along a family `Fm : FamP eps`, `PairInt` and the
   explicit hypothesis `(h : Conclusion1 (Fm.D x i) ... 1)` imply the period valuation bound
   $\mathrm{ur}(w, \mathrm{sg}(u, w)) \le v_w(y)$ across every family member (`off_level_bound_family`,
   `:614–630`).* [Lean, read]

*Proof.*

1. Fix $u$, $w$ ($\mathrm{resChar}(w) \notin \{T_u, g_0, g_1\}$), and $\varphi \in L.\mathrm{NuLat}(u)$
   (`:518`). First check `hIn : InNP X Y K c u w (D.nuIn u φ)` by splitting on whether the active
   orbit set `VV` at $\mathrm{resChar}(w)$ is empty (`:520–524`):
   - **If `VV = ∅`:** `nuIn_mem_Sram_of_locLe` (`:463`) uses `LocLe (D.plEq w) 0 (L.NuLat u) (MramL D u)`
     to show `D.nuIn u φ ∈ LT.Sram D u w`, establishing the right disjunct of `InNP`!
   - **If `VV ≠ ∅`:** `hGI` supplies a good index `hg : GIdx ...`, and `NuServedDef` (`hS`) places
     `c.cmp u w hg (D.nuIn u φ)` inside `NP X Y K u w hg`, establishing the left disjunct of `InNP`!
   Now evaluate the input hypothesis `h : Conclusion1 ... 1` at $\mu_w = D.\mathrm{what}_2.\mathrm{muAt}(w)$
   (`used_muAt`, `:39`) and $x = D.\mathrm{nuIn}\,u\,\varphi$ (`:525`): this yields
   `ColGe T u μ_w w (D.nuIn u φ) (totS ... 1 u w)`. Feeding that `ColGe` bound into Lemma 8.1(3)
   (`period_ge`, `:526`) produces $y \in L$ representing `perCol` with valuation bounded below by
   $\mathrm{ur}\bigl(D, w, \mathrm{totS}(1, u, w) - v_{\mathrm{DG}}(D, u, w)\bigr)$. Look at the
   $\mathrm{sp} = 1$ term inside `totS` (`:531–536`):
   $$\mathrm{totS}(1, u, w) - v_{\mathrm{DG}}(D, u, w)
   = \sum_{j=1}^m \bigl(\mathrm{gainS}(p, j) + L.F(j, w) - L.E(u, j, w)\bigr)
   \ge \sum_{j=1}^m \bigl(L.\mathrm{gainD}(j, w) + L.F(j, w) - L.E(u, j, w)\bigr)
   = L.\mathrm{sg}(u, w)!$$
   Multiplying by $e_w \ge 0$ (`ur`) completes `off_level_bound`!
2. For `gainD_le_gainS` (`:552–575`), if $w \in L.\mathrm{drop}$, $w \notin L.\mathrm{supp}$, or
   $\mathrm{resChar}(w)$ is not inert/signal, `L.gainD j w = 0 ≤ gainS` by nonnegativity
   `served_gain_nonneg` (`:545`); on active inert places, `(hF w)` (`ParametersFill`) gives the exact
   equality `L.gain j w = gainP X K (aL L) (bL L) p j` (`:564`), exceptional primes have `L.gain j w = 0`
   (`:567`), and `IsCs` primes are excluded via `isCs_drop` (`:575, 606`). (Meanwhile, in `src/Formalism/SharpRestriction/GrowthBounds/DefsInst.lean:11`,
   `GAtP.SandwichE` records the upstream module-inclusion sandwich $p^e M_{\mathrm{na}} \le M \le M_{\mathrm{na}}$
   used when instantiating the divided-power package `DataG`.) Substituting `local_compatibility_family`
   (`:588`), `gIdx_of_served` (`:577`), and `gainD_le_gainS` into part (1) yields
   `off_level_bound_family` (`:614–630`). $\square$

### 8.4.3 Supplying `Conclusion1` and bridging `ServF` to `LinkDIVt`

Finally, three short bridge files supply `Conclusion1` (via `Serv` / `ServF`) and connect
`off_level_bound_family` to the global chain assembly of Chapter 7 (`TieGlobal.lean`) and Chapter 9
(`GlobalTheoremInputs.lean`):

**Proposition 8.3 (From local kernel rows and joint services to `ServF` and `LinkDIVt`).**

1. **Joint local lattice services (`NPc`, `JointAt`, and `SecondLevelHypothesisFamily`, `src/Formalism/LocalToGlobal/GroupLattices/JointServices.lean:13,72,95,125,163`).**
   *At each finite place $w$ away from $\{T_u, g_0, g_1\}$ (`OffTG`, `:76`), `NPc` (`:72–74`) defines
   the $\mathcal O_L$-submodule of `lat 0` spanned by `{x | InNP X Y K c u w x}`, and `JointAt` (`:95`)
   plus `SecondLevelHypothesisFamily` (`:163`) merge these `InNP`-spanned submodules with the branched
   column bounds `ColBr` (`:13`) across all places of $\mathcal O_L$.* [Lean, read]
2. **Discharging `ServF` (including `Conclusion1`) and `LinkDIVt` (`closed_servF_of_servT_of_dGamSize`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/GServT.lean:31`, and `closed_linkDIVt_of_closed_bridge_kernel`, `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:197`).**
   *Given `DivisionKernelData` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:32`) and uniform constant bounds
   `DivisionKernelConstantBounds` (`:166`) produced from the theta-lift rows `pkg_of_rowsK_alt` (`:113`),
   `closed_servF_of_servT_of_dGamSize` discharges `ServF` (whose `Serv` payload carries `Conclusion1 ... 1`),
   and `linkDIVt_of_bridge_kernel` (`:193`) / `closed_linkDIVt_of_closed_bridge_kernel` (`:197`) feeds
   that `Conclusion1` witness into `off_level_bound_family` alongside `SecondLevelHypothesisFamily` to
   inhabit the global divisibility link `LinkDIVt` (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:94`).* [Lean, read]

### 8.4.4 Finite jets of the local formal-group kernel

**Motivation [Expository].** A theta kernel is represented by a power series, while a
polynomial test reads finitely many of its coefficients. Two different estimates are needed.
The total degree tells us how many powers of a series can enter a test. A valuation estimate
then tells us which denominators those powers can bring into the answer.

**Example [Expository].** Take $p=5$, choose $\pi^{24}=5$, and put $c=\pi^6$.
In the two-position case of `hhS`, one can take $u_0=1$, $u_1=0$ and one pair of indices
$(a,b)$. The two `sSer` factors start with $x,y$ respectively and their next terms have
degree $25$. Thus the resulting $h=\mathrm{hhS}(u)$ agrees with $x^5y$ through degree $12$.
With integral multiplier $1$, the kernel factor $\exp(-ch/5)$ through degree $12$ is
$1-\frac{\pi^6}{5}x^5y+\frac{\pi^{12}}{2\cdot 5^2}x^{10}y^2$.
The $x^5y$ coefficient has normalized valuation $-3/4$, even though the first
nonconstant term has degree $6$. The monomial test $P=X_0^5 X_1$ in `applyD`
reads this coefficient with multiplier $5!\,1!$, giving $-24\pi^6$ of valuation $1/4$.
This example uses the exponential factor alone. [Lean] for the underlying definitions.
`src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:197,200,205,256`.

**Definition [Lean, read].** For a multi-index $n$, write $[Z^n]F$ for its coefficient
and $|n|$ for its total degree. Let $R' \subseteq K'$ be the chosen coefficient subring
of the extension field. A series is coefficientwise integral if each
coefficient belongs to $R'$ (`IntR`). The predicate `InClass` for $F,h$ requires
one sequence of integral series $g_i$ such that for every $n$,
$[Z^n]F=\sum_{i=0}^{|n|}p^{-i}[Z^n](h^i g_i)$.
In `SConcl`, $F$ is the kernel after scalar extension and the linear substitution
`ThZ`, which uses the Frobenius basis and scales the coordinates by $\pi$.
The proposition asks for integral $u$ such that `InClass` holds for every
zero-constant-term $h=\mathrm{hhS}(u)+pG$ with integral $G$. This is the
single-kernel property quantified in `FormalGroupSystem.Conclusion1`.
`src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:123,181,190,194,210,216,633`.

**Lemma (Integral coefficients after extracting explicit denominators) [Lean, read].**
Let $p$ be prime and let $K'$ extend the fraction field of the Witt vectors of $\overline{\mathbb F}_p$,
let $\pi^{p^2-1}=p$, and let $R'$ contain the image of the Witt vectors and $\pi$.
Set $c=\pi^{p+1}$. Suppose $H,h$ have zero constant term,
$h=H+pG$, and $G,V$ are coefficientwise integral in $R'$.
Then $\exp(-cH/p)V$ has the `InClass` expansion relative to $h$.
The exponential is formal and the lemma has no analytic convergence hypothesis.
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/NatCastInvMemRp.lean:52`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/InClassOfExp.lean:143`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelExpansionOfRestrictions.lean:94,116`.

**Proof [Lean, read].**

1. Write $i!=p^v m$ with $v=v_p(i!)$ and $p\nmid m$. Legendre's factorial formula gives
   $(p-1)v\le i$. The image of $m$ is a unit in the Witt ring because its residue
   is nonzero. Since $c^{p-1}=p$, we have $c^i/i!=c^{i-(p-1)v}/m$ in
   the subring generated by the Witt vectors and $\pi$. The same holds with $-c$.
   `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/NatCastInvMemRp.lean:28,40,52`.
2. The relation $h=H+pG$ forces $G(0)=0$. Through degree $N$, the formal exponential
   of any zero-constant-term argument is the sum of its powers through $N$ with
   factorial denominators. In multiplying two such sums only pairs of powers
   with indices $k+l\le N$ can contribute. The binomial formula identifies the
   resulting triangular sum with the exponential of the sum of the arguments.
   Applying this at every $N$ yields
   $\exp(-cH/p)=\exp(-ch/p)\exp(cG)$.
   `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/InClassOfExp.lean:59,67`,
   `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelExpansionOfRestrictions.lean:94`.
3. By step 1, each finite coefficient sum for $\exp(cG)$ belongs to $R'$.
   Set $V'=\exp(cG)V$ and $g_i=((-c)^i/i!)V'$. Products remain integral by
   the finite coefficient convolution. In degree $|n|$, replace the first exponential
   by its powers through $|n|$. Multiplication by $V'$ preserves the discarded
   terms' vanishing through that degree. Pull out $p^{-i}$ and obtain the
   required coefficient identity with the same $g_i$ for every $n$.
   `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/InClassOfExp.lean:16,104,129,143`.

**Conditional passage to the kernel [Lean, read].** For $p\ge5$, with even Frobenius
index count $n'\ge2$, `SConcl_of` starts from `ExtensionLocalCondition`, which writes the
kernel as an exponential of a phase times a residual factor $U$. It uses the supplied
Dwork lemma and `RestSExp` to put the exponential after `ThZ` in the form
$\exp(-cH/p)V$ with $H=\mathrm{hhS}(u)$ and $V$ integral. It uses the supplied
`RestSInt` to make the transformed $U$ integral. Multiplicativity of the substitution
lets us absorb that factor into $V$, and the lemma supplies `SConcl`.
`kernel_expansion_of_restrictions` applies this at each place and step, taking the
local conditions and Dwork input from `admitted`. [Open] for our reading of the
deeper restriction inputs and their geometric construction.
`src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:162,546,548,771`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelExpansionOfRestrictions.lean:12,22,70,116,136`.

**Where this estimate stops.** If $h$ vanishes below degree $d\ge1$, then only
$i\le\lfloor |n|/d\rfloor$ can enter the coefficient sum. This follows by adding total
degrees in the coefficient convolution. For a valuation ring with $v_p(p)=1$, that
alone allows a loss up to $\lfloor |n|/d\rfloor$ from the explicit $p^{-i}$.
The zero-constant-term hypothesis matters: at arguments $1$ and $x$, the linear
coefficient of $\mathrm{expK}(1+x)$ is $2$ by the two terms of the definition,
while that of $\mathrm{expK}(1)\mathrm{expK}(x)$ is $1$. A denominator bound for one jet leaves the passage from
`applyD` to the full lattice inequalities to be justified. [Expository]
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/InClassOfExp.lean:52,67`,
`src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:256,613`.

**Dependency diagram.** Dotted arrows mark where the textbook reading stops.
The packet groups the single-kernel result with other estimates. The unit-bound bridge extracts
`VolumeRatio₂` and `LowTermBound` from it. The twisted part of the true-column row
theorem has $\mathrm{resChar}(w)=T_u$. The column bound in
`WeilJacquetShalikaLaw.Conclusion1` has $\mathrm{resChar}(w)\ne T_u$.
The true-column theorem also returns an own-chain `Conclusion5Sharp`.
[Lean] for the downstream theorems, [Open] for a complete reading of the
jet-to-lattice estimates and both routes' remaining geometric inputs.
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PrvAndKernelCommutationUpToUnitsOfRests.lean:80,94,97,107`,
`src/Formalism/SharpRestriction/GrowthBounds/JointsTw.lean:243,264`,
`src/Formalism/SharpRestriction/SmoothDesignExistence/SumOverPrimesHypotheses.lean:187,202,219`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrueColumnsRowSharpBounds.lean:17,36`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrueColumnsRowSharpBoundsStatement.lean:8`,
`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97`.

```text
piFact + finite exponential truncation
  -> inClass_of_exp -> SConcl_of (restriction inputs)
  -> FormalGroupSystem.Conclusion1 (one kernel)
  -> Conclusion₂ packet, alongside the separate lattice estimates
       ⋯> unit and length bounds -> ServF (off-level column bound)

realized point-kernel laws ⋯> true-column sharp bound
  -> own-chain sharp bound and twisted column bound at the level prime
```

---

## 8.5 Remarks, formalization notes, and Masullo's counterpart

### 8.5.1 Why `Conclusion1` is an input `Prop` to `off_level_bound` — and what `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean` actually proves

In early community summaries (including LUMI's `docs/02-proof-map.md`, which cited line 101, the
closing line of `def Conclusion1` whose header sits at line 97) [Community],
`WeilJacquetShalikaLaw.Conclusion1` was sometimes referred to as if `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`
itself proved $p$-adic theta-kernel divisibility. Reading all 633 lines of
`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean` (`R3`, leaf-inclusive import cone **321** modules) clarifies the exact
division of labor [Lean, read]:

- `Conclusion1` (`:97–101`) is a **`def ... : Prop`** specifying the $m$-step composite column bound
  `InNP ... → ColGe ... (totS ...)` under `Ties9` and `ErrDefs`;
- `off_level_bound` (`:504`) and `off_level_bound_family` (`:614`) **take `(h : Conclusion1 ... 1)` as
  an explicit input hypothesis**, check `InNP` on `NuLat`, pair the composite column against test
  forms via `val_step` (`:401`) and `period_ge` (`:419–437`) so the $\pm v_{\mathrm{DG}}$ denominator
  offsets cancel, and apply `gainD_le_gainS` (`:552`) to deduce period divisibility at order `L.sg u w`;
- Section 8.4.4 proves a conditional single-kernel expansion. The service proof
  also uses lattice estimates from the formal-group packet to obtain the off-level
  composite bound. The two declarations named `Conclusion1` have different conclusions.
  [Lean] `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:633,775`,
  `src/Formalism/SharpRestriction/SmoothDesignExistence/SumOverPrimesHypotheses.lean:187,202,219`.

### 8.5.2 Why even powers of $p$ cancel and why ramified primes are harmless

Two small structural points save readers hours of puzzlement [Expository]:

1. **Why only odd powers $p^{2e+1}$ appear in `ASK` (`src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:76`) and
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
| `VGe`, `ColGe0`, `ColGeTw`, `ColGe`, `Exc`, `gainS`, `g0S`, `GainZero`, `InNP`, `vDG`, `lowS`, `totS`, `TwLoc`, `Ties9`, `Conclusion1` | `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:19,24,28,33,37,49,54,57,60,67,73,76,79,92,97` | Definitions 8.1–8.2: field-scalar localized valuation `VGe D w Λ y s`, $m$-step composite column divisibility `ColGe`, exceptional primes `Exc`, initial-vector predicate `InNP`, three-field `Ties9`, and `Conclusion1` (import cone 321). | [Lean, read] |
| `IntegralKernelValuation`, `TupleLatticeValuation`, `LatticeGrowthAtPlace`, `admitted`, `Stmt`, `Serv`, `KudlaFamilyStatement`, `ServF`, `PairInt` | `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:113,137,146,224,234,241,245,252,383` | Definition 8.3(1): single-step denominator bound `IntegralKernelValuation`, served-orbit growth `LatticeGrowthAtPlace`, period integrality `PairInt`, and family service `ServF`. | [Lean, read] |
| `VGe_mono`, `ColGe_mono`, `kernel_valuation_served`, `serv_of`, `vAdd_mul'`, `val_step`, `period_ge`, `nuIn_mem_Sram_of_locLe`, `stable_lattice_of_no_served_orbit`, `off_level_bound`, `gainD_le_gainS`, `isCs_drop`, `off_level_bound_family` | `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:325,332,348,376,395,401,419,463,486,504,552,606,614` | Lemma 8.1 and Theorem 8.2: monotonicity, denominator cancellation `val_step`, period pairing `period_ge` (`:419–437`), comparison `gainD ≤ gainS` from `ParametersFill`, and deduction of `sg` period bounds from input `Conclusion1`. | [Lean, read] |
| `MramL`, `ur`, `Iu`, `NprimeDef`, `LocLe`, `NuDef`, `hExpl` | `src/Formalism/LocalRingCardinality/DataDIVDefs.lean:12,15,17,22,31,48,89` | Definition 8.1(1): ramification-scaled threshold `ur D w s = ramIdx w * s`, fractional ideal $I_u = \prod_w \mathfrak p_w^{-\lfloor e_w \mathrm{sg}(u,w)\rfloor}$, and fractional-ideal span equality `NprimeDef`. | [Lean, read] |
| `Scale`, `lpFeasible`, `lpF`, `SizeData₂`, `sz`, `lifts`, `gainD`, `sg`, `Fo`, `Ga`, `MAIN`, `vonMangoldtClassSum` | `src/Formalism/LocalRingCardinality/DataParams₂.lean:9,51,58,76,205,208,212,215,218,220,232,240` | Definition 8.3(3): chain step gains `gainD`, total place gain `sg`, and odd-power prime ramp `vonMangoldtClassSum` matching Chapter 5's `ASK`. | [Lean, read] |
| `Extra` | `src/Formalism/LocalRingCardinality/DataExtra.lean:40` | Auxiliary slack record accompanying `DataParams₂`. | [Lean, read] |
| `SandwichE`, `EpDef`, `kapISet`, `KapIDef` | `src/Formalism/SharpRestriction/GrowthBounds/DefsInst.lean:11,18,38,54` | Upstream module-inclusion sandwich $p^e M_{\mathrm{na}} \le M \le M_{\mathrm{na}}$ and parameter definitions instantiating `DataG`. | [Lean, read] |
| `deltaL`, `Places`, `Level`, `GAtP` | `src/Formalism/SharpRestriction/GrowthBounds/DataG.lean:11,33,106,163` | Definition 8.3(2): Weyl / divided-power polynomial data at prime $p$. | [Lean, read] |
| `ColBr`, `NPc`, `JointAt`, `SecondLevelHypothesisAt`, `SecondLevelHypothesisFamily` | `src/Formalism/LocalToGlobal/GroupLattices/JointServices.lean:13,72,95,125,163` | Proposition 8.3(1): spans `InNP`-admissible vectors into the local $\mathcal O_L$-submodule `NPc` away from $T_u, g_0, g_1$ (`OffTG`) and merges it with `ColBr`. | [Lean, read] |
| `SelectionServed`, `closed_servF_of_servT_of_dGamSize` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/GServT.lean:13,31` | Proposition 8.3(2): discharges `ServF` (supplying `Conclusion1`) from served orbit selection and gamma-factor bounds. | [Lean, read] |
| `DivisionKernelData`, `pkg_of_rowsK_alt`, `DivisionKernelConstantBounds`, `linkDIVt_of_bridge_kernel`, `closed_linkDIVt_of_closed_bridge_kernel` | `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:32,113,166,193,197` | Proposition 8.3(2): supplies `Conclusion1` to `off_level_bound_family` alongside `SecondLevelHypothesisFamily` to prove `LinkDIVt` (import cone 4,699). | [Lean, read] |
| `gam`, `gB`, `gA`, `Conclusion1`, `Conclusion2`; `trueColumns_row_sharp_bounds` | `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:51,57,66,633,649`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrueColumnsRowSharpBoundsStatement.lean:8` | Definition 8.3(2) (`R2`): supersingular height-$2$ slope $\frac{p}{p^2-1} = \sum_{e \ge 0} p^{-(2e+1)}$, odd-power gain `gA`, and statement interfaces. Section 8.4.4 reads the conditional kernel expansion, with deeper estimates `[Open]`. | [Lean] |

**Summary of the chapter.** At primes $p$ inert in the imaginary quadratic core $K = \mathbb Q(\sqrt{-d})$,
supersingular height-$2$ formal groups have $D^p \equiv 0 \pmod p$ and Newton-polygon slope
$\frac{1}{p^2 - 1}$, whose difference from Legendre's factorial slope $\frac{1}{p - 1}$ equals
$\frac{p}{p^2 - 1} = \frac{1}{p} + \frac{1}{p^3} + \frac{1}{p^5} + \dots$ `[Katz1976]`, generating
the odd-power Riesz ramp `vonMangoldtClassSum` / `ASK` while split primes contribute zero [Expository].
In `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`, `Conclusion1` (`:97`) states the $m$-step composite column bound
`InNP ... → ColGe ... (totS ...)` (supplied upstream via `FormalGroupSystem.lean` and
`DIVRecBridgeSel.lean`), and `off_level_bound` (`:504`) plus `off_level_bound_family` (`:614`) combine
that `Conclusion1` input with `PairInt`, `val_step`, `period_ge`, and `gainD_le_gainS` to deduce period
divisibility at order `L.sg u w`, feeding `LinkDIVt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:197`) [Lean, read]. In
Chapter 9 we see how Bost's Arakelov slope inequality converts this local $\mathfrak p_w$-adic
divisibility into a global numerical inequality!
