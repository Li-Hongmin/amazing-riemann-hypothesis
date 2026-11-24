# Chapter 8. Divisibility at inert primes

> **Status tags used in this chapter:** `[Lean, read]` for definitions and `sorry`-free proofs
> verified line by line in `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`, `DataDIVDefs.lean`, `DataParams₂.lean`,
> `DataExtra.lean`, `DefsInst.lean`, `DataG.lean`, `JointServices.lean`, `GServT.lean`, and
> `DIVRecBridgeSel.lean` (`R3`); `[Lean]` for upstream formal-group and row-bound theorems whose
> statement headers were inspected while their deep proof cones remain unread (`R2`); Sections
> 8.4.4–8.4.5 add `[Lean, read]` for the formal-group producers in `MultisetValuation/` and the
> reader in `JointsTw.lean`, while their Gauss-bound and `admitted` inputs stay `[Lean]`/`[Open]`; Section 8.4.14 reads the producers `restSIntA` and `ea_restSExpV_of` of `ea_RestSU` (`AtPiEqRescale.lean`, `EaRestSExpVOf.lean`, `InParamMap.lean`, `IntRPsubst.lean`) and their assembly at the three place bounds (local `R3`, awaiting independent review); Section 8.4.16 reads the biadditive supply `restBeta` (`BiadditiveSecondVariable.lean`, `BiadditiveFirstVariable.lean`, `IntegralExpParamOfEquivZero.lean`, `PositivityConditionHolds.lean`) behind the Frobenius-fixed $c$ and the $Y$-factor of `ea_reduce`, with `lawExists` and the Teichmüller root kept named, and Section 8.4.17 reads the conditional classification assembly `BetaIsG_of` (`NormLiftLeOne.lean`, `PartialCoboundaryLinear.lean`, `ConstantCoeffFirstTwoOfThree.lean`, `TopsChoicePartA.lean`, `ScalingSwapLemmas.lean`) through `StepII_of`, `StepH_of`, `StepIII`, and `StepIV_of`, keeping `DworkMv`, `DivDeriv`, `DeIntegral`, `LawSymm`, `LemmaTwo`, `StepZero`, `StepI`, and `SimeqRules` named (local `R3`, awaiting independent review); `[Paper]` for
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
and $|n|$ for its total degree. For a subring $R'$ of a field $K'$, a series is
coefficientwise integral if each coefficient belongs to $R'$ (`IntR`).
The predicate `InClass` for $F,h$ requires
one sequence of integral series $g_i$ such that for every $n$,
$[Z^n]F=\sum_{i=0}^{|n|}p^{-i}[Z^n](h^i g_i)$.
In `SConcl`, $F$ is the kernel after scalar extension and the linear substitution
`ThZ`, which uses the Frobenius basis and scales the coordinates by $\pi$.
`SConcl B K1 R1 Th` quantifies over every extension. Let $K'$ be any field over
$K_0$ and $K_1$ forming a scalar tower, let $R'\subseteq K'$ be any subring, and let
$\pi\in K'$ be any element with $\pi^{p^2-1}=p$. Assume $\mathrm{Rp}(K',\pi)\subseteq R'$
and that $R_1$ maps into $R'$. Then there must be $u$ with entries in $R'$ such that
`InClass` holds, relative to $R'$, for every zero-constant-term $h=\mathrm{hhS}(u)+pG$
with $G$ integral in $R'$. So $u$ may depend on $(K',R',\pi)$ but not on $h$. This is
the single-kernel property quantified in `FormalGroupSystem.Conclusion1`.
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
kernel as an exponential of a phase times a residual factor $U$. It takes three
arguments: the Dwork lemma `DworkLemma p` and the restriction statements `RestSExp p`
and `RestSInt p`. `RestSExp` puts the exponential after `ThZ` in the form
$\exp(-cH/p)V$ with $H=\mathrm{hhS}(u)$ and $V$ integral. `RestSInt` makes the
transformed $U$ integral. Multiplicativity of the substitution lets us absorb that
factor into $V$, and the lemma supplies `SConcl`.
`kernel_expansion_of_restrictions` applies this at each place and step. It takes the
Dwork lemma (`adm1`) and the local conditions (`adm2`) from `admitted`. The two
restriction statements are not hypotheses. They are theorems of the archive:
`restSExp_of` derives `RestSExp` from the statements `RestBeta` and `RestGc`, which the
archive proves as `restBeta` and `restGc`, and `restSInt` proves `RestSInt`.
`theta_kernel_expansion` passes these proofs through `baseChange_preserves_unitary_of`
to `kernel_expansion_of_restrictions` [Lean]. [Open] for our reading of the proof of
`restGc` and of the geometric construction behind `admitted`; `restSInt` and its
place-wise form `restSIntA` are read in Section 8.4.14, and `restBeta` with its `BetaIsG_of` assembly in Sections 8.4.16–8.4.17.
`src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:162,546,548,771`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelExpansionOfRestrictions.lean:12,22,70,116,136`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DworkExponentialRestrictions.lean:95,137`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/InParamMap.lean:124`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CommonEigenvectorThird.lean:21,32`.

**Where this estimate stops.** If $h$ vanishes below degree $d\ge1$, then only
$i\le\lfloor |n|/d\rfloor$ can enter the coefficient sum. This follows by adding total
degrees in the coefficient convolution. For a valuation ring with $v_p(p)=1$, that
alone allows a loss up to $\lfloor |n|/d\rfloor$ from the explicit $p^{-i}$.
The zero-constant-term hypothesis matters. Since `expK` truncates its $k$-sum at
$k\le|n|$, the arguments $1$ and $x$ do not show this: $\mathrm{expK}(1+x)$ and
$\mathrm{expK}(1)\mathrm{expK}(x)$ are the same series $\sum_d x^d/d!$. The arguments
$1$ and $x^2$ do. The $x^2$ coefficient of $\mathrm{expK}(1+x^2)$ is $1+2/2!=2$, from
$k=1,2$. But $\mathrm{expK}(1)=1$, and the $x^2$ coefficient of $\mathrm{expK}(x^2)$ is
$1$. So `expK_add` fails without the hypothesis; we checked this in exact rational
arithmetic. A denominator bound for one jet leaves the passage from `applyD` to the
full lattice inequalities to be justified. Section 8.4.5 follows that passage. [Expository]
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/InClassOfExp.lean:52,67`,
`src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:256,613`.

**Dependency diagram.** Dotted arrows mark where the textbook reading stops.
`Conclusion₂` packs eleven estimates. The packet has three read sites in the pinned
archive: `SumOverPrimesHypotheses.lean:202` through `JointsTw.lean:269–270`, `:219`
through `WeilJacquetShalikaLaw.lean:374`, and `PlaneCountTheoremWithConstants.lean:1649–1650`.
They project only `VolumeRatio₂` and `LowTermBound`. Both fields are produced from
`inClass_of_exp` through `ea_restSU_of` (Section 8.4.5). The single-kernel result
`FormalGroupSystem.Conclusion1` is packed as the field `R.S1` but is never read.
The twisted part of the true-column row theorem has $\mathrm{resChar}(w)=T_u$. The
column bound in `WeilJacquetShalikaLaw.Conclusion1` has $\mathrm{resChar}(w)\ne T_u$.
The true-column theorem also returns an own-chain `Conclusion5Sharp`.
[Lean, read] for the packing and the three projections, [Lean] for the downstream
theorems, and [Open] for the proofs listed in the remarks of Section 8.4.5 and for both
routes' remaining geometric inputs.
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PrvAndKernelCommutationUpToUnitsOfRests.lean:80,94,97,107`,
`src/Formalism/SharpRestriction/GrowthBounds/JointsTw.lean:243,264,269`,
`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:371,374`,
`src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean:1641,1649`,
`src/Formalism/SharpRestriction/SmoothDesignExistence/SumOverPrimesHypotheses.lean:187,202,219`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrueColumnsRowSharpBounds.lean:17,36`,
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrueColumnsRowSharpBoundsStatement.lean:8`,
`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97`.

```text
piFact + finite exponential truncation
  -> inClass_of_exp
       -> SConcl_of -> FormalGroupSystem.Conclusion1 (one kernel)
            -> packed as R.S1 in Conclusion₂; never read
       -> ea_restSU_of (one place, exponential factor)
            -> ea_lowN + Gauss bounds ⋯>
                 -> first_theorem_place_bound -> VolumeRatio₂ ............ read
                 -> second_lemma_place_bound, hecke_place_bound
                      -> EntCondition -> LowTermBound ...................... read
                           (with FormB from adm7 ⋯>, Conclusion4 ⋯>)
  read sites -> unit and length bounds -> ServF (off-level column bound)

realized point-kernel laws ⋯> true-column sharp bound
  -> own-chain sharp bound and twisted column bound at the level prime
```

### 8.4.5 From the single-kernel expansion to the low-term lattice bound `LowTermBound`

**Motivation [Expository].** Section 8.4.4 ends with a coefficient formula for one
exponential factor. The places that read the formal-group packet need lattice
statements instead. At a place $w$ of the coefficient field, the chain of Chapter 7
gives $O$-lattices $\mathrm{Int}_0,\dots,\mathrm{Int}_m$ joined by kernel maps $K_j$.
The bridge in `JointsTw.lean` must know which power of a uniformizer $\varpi$ divides
the $m$-step image of a product of the operators $y_v$. Two passages are needed.
First, a coefficient bound for one exponential factor must become a bound on the
finitely many numbers that a column test reads. This bound must hold for every
integral residual factor, and the archive calls it `LowAt`. Second, these numbers must
be multiplied over places and composed over the $m$ steps. That composition is
`LowTermBound`. The low term is the gain allowed at every place. A served place may
instead receive the larger gain $G_n-\mathrm{PR}_n$.

**Definitions [Lean, read].** Fix a prime $p$, a system $X$ with pending data $Y$
(`Sys`, `Pend`), a place $v$ of $X$ and a step $j<m$.

1. *Rescaling and column tests.* `atPi ϖ f` multiplies the coefficient of $Z^n$ by
   $\varpi^{|n|}$. For a polynomial $P$ with polynomial coefficients, `applyD P f` sums
   $\bigl(\prod_x n_x!\bigr)[Z^n]f$ times the $n$-th coefficient of $P$ over the support
   of $P$. The factorials are the Hasse–Schmidt normalisation of Chapter 6. The column
   tests $\mathrm{PIv}(j,I,v)$ are products of column determinants, and the tests
   $\mathrm{PIvS}$ carry extra factors $p^{\mathrm{colExp}}$.
   `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:253,256,405,417,421`,
   `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AuxUOfFirstTheoremPlaceBound.lean:14`.
2. *Integer encoding of a real bound.* Let $O_c$ be the valuation subring of the
   coefficient field $K_c$. `geC x g` means that $x^bp^{-a}\in O_c$ for all $a\in\mathbb Z$
   and all $b\in\mathbb N$ with $b>0$ and $a\le gb$. In a rank-one valuation ring with
   $v(p)=1$, this says $v(x)\ge g$. Real levels are thus tested by integer pairs.
   `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:522`.
3. *Low bound of one exponential factor.* Let $\mathrm{PhAt}_{j,v}$ be the phase of place
   $v$ at step $j$. `LowAt j v g` says that `geC` holds at level $g$ for every coefficient
   of $\mathrm{applyD}(\mathrm{PIv}(j,I,v))$ applied to
   $\mathrm{ThZA}\bigl(\exp(-\mathrm{PhAt}_{j,v})\,U\bigr)$. This must hold for every column
   choice $I$ and every $U$ with integral $\mathrm{inParamK}(U)$. `VolumeRatio₂` is
   `LowAt j v (g0v v (j+1))` for all $v$ and $j<m$, where $\mathrm{g0v}$ is the odd-power
   gain $\mathrm{gA}$ of Definition 8.3(2). The packet hypothesis `adm11` is the same
   statement at level $0$.
   `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:325,506,529,627,658`.
4. *Lattice valuation.* The system carries a uniformizer $\varpi$ of $O$ with $p$
   associated to $\varpi^{e_O}$. It also carries integers $d_G(j)$ that bound the $p$-adic
   valuation of the stabiliser orders at step $j$. Put
   $\mathrm{vsc}(g)=\varpi^{\lceil ge_O\rceil}$, and let `vGe j F g` mean
   $F\in\mathrm{vsc}(g)\,\mathrm{Int}_j$. `Iprod S VV` is the $O$-span of the vectors
   $\prod_{v\in BB}y_v^{m}F_0$ with $BB\subseteq VV$ and
   $F_0\in\varpi^{\sum_{v\in VV\setminus BB}\lceil S_ve_O\rceil}\mathrm{Int}_0$.
   `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:270,272,274,309,311,361`.
5. *The low-term lattice bound.* `LowTermBound D X Y` quantifies over all functions
   $G_n,G_{0n},\mathrm{PR}_n$, all slacks $S$ and all finite sets $VV$ of places. It has
   four hypotheses. First, $G_n(v,j)\le\mathrm{gv}(v,j)$ on $VV$, where $\mathrm{gv}$ is the
   served gain $\mathrm{gB}$. Second, `LowAt j v (G0n v (j+1))` holds for all $v$ and
   $j<m$. Third, $\Pr(v,j)\le\mathrm{PR}_n(v,j)$ on $VV$; here $\Pr$ is the real number
   `X.Conclusion₂ v j`, not the packet of the same name. Fourth,
   $\sum_{j=1}^m\max(G_n-\mathrm{PR}_n-G_{0n},0)\le S_v$ on $VV$. The conclusion is
   `vGe m (chainK m F) T` for every $F$ in `Iprod S VV`, where
   $T=\sum_{j=1}^{m}\bigl(\sum_{v\in VV}\max(G_n(v,j)-\mathrm{PR}_n(v,j),G_{0n}(v,j))+\sum_{v\notin VV}G_{0n}(v,j)\bigr)-\sum_{j=0}^{m-1}d_G(j)$.
   `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:323,327,708`.
6. *Whole-kernel bounds.* `EntB j i0 g` is `geC` at level $g$ for every coefficient of
   $\mathrm{applyD}(\mathrm{PI}(j,I,i_0))$ applied to the whole kernel
   $\mathrm{ThZA}(\mathrm{ThA})$. `PlaceB j v i g` holds in three cases: $i=0$ and
   `LowAt j v g`; $i=0$ and $g\le\mathrm{gv}-\mathrm{alEven}$; or $1\le i\le r$ and
   $g\le\mathrm{gv}$. `EntCondition` says that, for rational $g_P$, `PlaceB` at every
   place implies `EntB` at level $\sum_vg_P(v)$. `FormB` makes `EntB` a one-step
   lattice bound. Let $i_0\le r$ vanish off a duplicate-free list of places. If
   `EntB j i0 g` holds and $G\in\mathrm{Int}_j$, then the operators $T_{v,i_0(v)}$
   applied to $K_jG$ give a vector of valuation at least $g-d_G(j)$.
   `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PlaceB.lean:14,22,27`,
   `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/RamifiedLatticeOfChainEstimates.lean:15`.

**Example [Expository].** We continue the $p=5$ jet of Section 8.4.4, where $h=x^5y$
agrees with $\mathrm{hhS}(1,0)=x^5y-x^5y^{25}-5x^{29}y+\cdots$ through degree $12$.

- *Which series is tested.* `LowAt` tests the unscaled factor $F=\exp(-h/5)$. Through
  degree $12$ it equals $1-\frac15x^5y+\frac1{50}x^{10}y^2$. The class expansion is a
  statement about $\mathrm{atPi}(\pi,F)$ with $\pi^{24}=5$. That series multiplies the
  degree-$6$ coefficient by $\pi^6$ and the degree-$12$ coefficient by $\pi^{12}$. It is
  the series $\exp(-\pi^6h/5)$ of Section 8.4.4. So $c=\pi^{p+1}$ comes from rescaling the
  leading monomial $x^py$, which has degree $p+1$.
- *Valuations.* The two coefficients of $F$ have $v_5=-1$ and $-2$. After rescaling
  they have $-3/4$ and $-3/2$. In the class identity only $i=|n|/6$ contributes, because
  $h$ vanishes below degree $6$.
- *Column tests.* The tests $X_0^5X_1$ and $X_0^{10}X_1^2$ have multipliers
  $5!\,1!=120$ and $10!\,2!=7257600$, of valuations $1$ and $2$. On $F$ they read $-24$
  and $145152$, both of valuation $0$. On the rescaled series they read $-24\pi^6$ and
  $145152\pi^{12}$, of valuations $1/4$ and $1/2$. The difference is $|n|/(p^2-1)$.
- *Integer encoding.* `geC` at level $1/4$ holds for $x=-24\pi^6$, because $b/4-a\ge0$
  whenever $a\le b/4$. At level $25/96$ it fails at $(a,b)=(7,27)$, because $27/4-7<0$.
- *Lattice exponent.* With $e_O=24$ we get $\mathrm{vsc}(1/4)=\varpi^6$. Take two steps
  at one place with $G_{0n}=1/4$ at each step and $VV=\emptyset$. For $d_G=(0,0)$ the
  bound is $T=1/2$, that is, $\varpi^{12}$. For $d_G=(0,1)$ it is $T=-1/2$, that is,
  $\varpi^{-12}$, so the stabiliser term turns the gain into an allowed denominator.
  For $e_O=1$ the level $T=1/2$ gives $\varpi^1$, since only the total is rounded.

We checked these numbers in exact rational arithmetic. In this toy the unscaled tests
have valuation $0$, which is the level-$0$ statement `adm11` for these two tests.
The positive levels $\mathrm{g0v}$ come from the column determinants $\mathrm{PIv}$.
They are estimated by the Gauss bounds used in Theorem 8.6.

**Lemma 8.4 (one place: from the Dwork form to the class expansion, `ea_restSU_of`)
[Lean, read].** *Assume `ea_RestSExpV X`, the Dwork lemma and `BeProp` for $Y.\mathrm{be}$.
Fix $v$, $j$ and a series $U$ with integral $\mathrm{inParamK}(U)$. Let $K'$ be a field
over $K_c$, let $R'\subseteq K'$ be a subring, and let $\pi\in K'$ satisfy
$\pi^{p^2-1}=p$. Assume $\mathrm{Rp}(K',\pi)\subseteq R'$ and that $O_c$ maps into $R'$.
Then there is $u$ with entries in $R'$ such that
$\mathrm{atPi}\bigl(\pi,\mathrm{ThZA}(\exp(-\mathrm{PhAt}_{j,v})U)\bigr)$ has the class
expansion relative to $\mathrm{hhA}(u)$. In the production proof, `ea_restSU` supplies
the first hypothesis through `ea_restSExpV_of`.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpV.lean:15,28`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EntryAOneParity.lean:101,106`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/FirstTheoremPlaceBound.lean:17`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AllPlacesOfRestrictions.lean:23,33`.

*Proof.*

1. The hypothesis at $K_1=K_c$ gives $u$ with entries in $\mathrm{Rp}$ and an integral
   $V$ with $\mathrm{atPi}(\mathrm{ThZA}(\exp(-\mathrm{PhAt}_{j,v})))=
   \mathrm{expK}\bigl(-(\pi^{p+1}/p)\,\mathrm{hhA}(u)\bigr)V$. This works because
   `PhAt` is by definition the sum of the `sub2` terms in the hypothesis
   (`EaRestSExpV.lean:30–33`; `FormalGroupSystem.lean:506–508`).
2. Substitution and rescaling are multiplicative, so the series is
   $\mathrm{expK}(\cdots)\,V\,W$ with $W=\mathrm{atPi}(\mathrm{ThZA}(U))$ (`EaRestSExpV.lean:35`;
   `AllPlacesOfRestrictions.lean:33`; `KernelExpansionOfRestrictions.lean:82`).
3. `restSIntA` makes $W$ integral in $R'$, and `IntR_mul` makes $VW$ integral. Moreover
   $p\ne0$ in $K'$ (`EaRestSExpV.lean:36–41`; `AtPiEqRescale.lean:64`).
4. Apply `inClass_of_exp` with $c=\pi^{p+1}$, $pp=p$ and $h=\mathrm{hhA}(u)$. `piFact`
   gives $c^k/k!\in R'$, and `hhA_const` gives $h(0)=0$ (`EaRestSExpV.lean:42`;
   `AllPlacesOfRestrictions.lean:23`). $\square$

**Lemma 8.5 (from the class expansion to `LowAt`, `ea_lowN`) [Lean, read].** *Assume
`admitted`, `ea_RestSU X Y` and `ea_RestNorm Y`. The last condition provides an
ultrametric field $K'$ over $K_c$ with $\pi^{p^2-1}=p$ and $\lVert p\rVert=p^{-1}$,
whose unit ball pulls back to $O_c$. Let $P_I$ be test polynomials and let
$g\in\mathbb R$. Suppose the following bound (hK) holds for every such field, every
$u$ in its unit ball and every $F$ such that $\mathrm{atPi}(\pi,F)$ has the class
expansion relative to $\mathrm{hhA}(u)$: $\lVert[n]\,\mathrm{applyD}(P_I)F\rVert\le p^{-g}$
for all $I$ and $n$. Then every coefficient of $\mathrm{applyD}(P_I)$ applied to
$\mathrm{ThZA}(\exp(-\mathrm{PhAt}_{j,v})U)$ satisfies `geC` at level $g$, for every
integral $U$.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaGeCOfNorm.lean:37,51,91`.

*Proof.*

1. Take the normed extension. Its unit ball contains $\mathrm{Rp}(K',\pi)$, because the
   Witt vectors map into $O_c$ and $\lVert\pi\rVert^{p^2-1}=p^{-1}\le1$ (`:71–89`). Apply
   Lemma 8.4 with $R'$ the ball. The Dwork lemma and `BeProp` come from `admitted`
   (`:103–105`).
2. (hK) quantifies over all $F$ in the class, so it applies to our kernel factor
   (`:106`). The kernel enters only through Lemma 8.4.
3. `applyD` commutes with field maps, since factorials and integer coefficients map to
   themselves (`ea_applyD_map`, `EntryAOneParity.lean:88–99`; `EaGeCOfNorm.lean:107`).
4. If $a\le gb$, then $\lVert x^bp^{-a}\rVert\le p^{-gb}p^{a}\le1$, so $x^bp^{-a}$ lies
   in the ball and hence in $O_c$. Here $p^{-a}$ is an integer power, $p^{-gb}$ is a real
   power, and the comparison is made in $\mathbb R$ (`ea_geC_of_norm`,
   `EaGeCOfNorm.lean:53–69,108`). $\square$

**Theorem 8.6 (the three place bounds) [Lean, read].** *Assume `admitted`. For every
place $v$ and step $j<m$:*

1. *`first_theorem_place_bound` gives `LowAt j v (g0v v (j+1))`, which is
   `VolumeRatio₂` by `auxU_of_firstTheoremPlaceBound`;*
2. *`second_lemma_place_bound` gives `LowAt j v (gv v (j+1) - alEven v)`;*
3. *`hecke_place_bound` gives, for $1\le i\le r$, the same statement at level
   $\mathrm{gv}(v,j+1)$ for the tests $\mathrm{PIvS}$ with index $i$ (`LowAtI`).*

*The proof uses inputs whose statements we read but whose proofs we did not read
[Lean]: `restGc`, `nm_restNorm_of_place`, `eb_brJet`,
`ea_brClass`, `ea_brNum`, `ea_brScale`, and the Gauss bounds `kernel_a_one_generic`,
`kernel_a_two_generic` and `kernel_b_generic`; the biadditive supply `restBeta` and its `BetaIsG_of` classification assembly are read in Sections 8.4.16–8.4.17; the producers `ea_restSExpV_of` and `restSIntA`
of `ea_RestSU` are read in Section 8.4.14.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/FirstTheoremPlaceBound.lean:17,20,24,28`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AuxUOfFirstTheoremPlaceBound.lean:32,50,53,56,64`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaGeCOfNorm.lean:156,163,169,177,198,211,224`,
`src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGaussK.lean:213,216,219`.

*Proof.* Each part applies Lemma 8.5 to one family of tests
(`EaGeCOfNorm.lean:200–201,213–214,226–227`). The bound (hK) is proved in three moves.

1. *Jet.* `ea_BrJet` says that a coefficient of $\mathrm{applyD}(\mathrm{PIv})F$ is $0$ or
   equals a coefficient of the frame jet of the restriction of $F$ to the variables of
   place $v$. The first case is trivial (`:204–206`).
2. *Numbers.* `ea_BrNum` identifies $\mathrm{g0v}(v,j+1)$, $\mathrm{gv}(v,j+1)$ and
   $\mathrm{alEven}(v)$ with the excess gain, the gain and the even-position sum on the
   frame side (`:177–192`). The proof rewrites the target level by these identities
   (`:207,220`).
3. *Gauss bound.* `ea_BrClass` moves the class expansion of $\mathrm{atPi}(\pi,F)$ to the
   frame side, relative to $\mathrm{hhS}$ (`:169–175`). `kernel_a_one_generic` then gives
   part 1, and `kernel_a_two_generic` gives part 2 (`:208,221`). For part 3, `ea_BrScale`
   first factors out the power of $p$ carried by $\mathrm{PIvS}$, and
   `kernel_b_generic` with $1\le i$ finishes (`:230–239`). $\square$

**Corollary (`EntCondition`, `restEnt_of`) [Lean, read].** *Assume `admitted`. If
`PlaceB j v (i0 v) (gP v)` holds at every place, with $g_P$ rational, then `EntB j i0`
holds at level $\sum_vg_P(v)$.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/RestEntOf.lean:20,62`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AuxUOfFirstTheoremPlaceBound.lean:58,66`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelProductForm.lean:111,118`.

*Proof.*

1. `kernel_product_form` writes the whole kernel as
   $\mathrm{ThA}=\bigl(\prod_v\exp(-\mathrm{PhAt}_{j,v})\bigr)U_1$ with $U_1$ integral. It
   uses `adm2b` and `expK_add`. `expK_add` needs the zero constant terms of the phases,
   given by `en_PhAt_const`. The counterexample of Section 8.4.4 shows that this
   hypothesis cannot be dropped (`RestEntOf.lean:15–58`).
2. `restPlaces_of` adds the per-place bounds over this product
   (`KernelProductForm.lean:118–124`). Its summation lemma `en_places_add` is [Lean].
3. `restEnt_of_rest` checks each place (`AuxUOfFirstTheoremPlaceBound.lean:66–73`). If
   $i_0(v)=0$ and `LowAt` holds, it uses `lowAtI_zero`. If $i_0(v)=0$ and
   $g_P(v)\le\mathrm{gv}-\mathrm{alEven}$, it uses Theorem 8.6(2) with monotonicity. If
   $1\le i_0(v)\le r$, it uses Theorem 8.6(3) with monotonicity. $\square$

**Theorem 8.7 (`LowTermBound`) [Lean, read].** *Every `admitted` system satisfies
`LowTermBound`. The proof has three inputs. `FormB` comes from `formB`, whose proof
takes `adm7`, `ArchimedeanSignatureMatching` and `adm3b` out of `admitted`.
`EntCondition` comes from the Corollary. The Hecke relations of `Conclusion4` come from
`theorem_of_alternate_form` [Lean].*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PrvAndKernelCommutationUpToUnitsOfRests.lean:89`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/LiftBoundOfIntegrality.lean:103`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/YEPEComm.lean:131`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AofUpdate.lean:172`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelSumOfClassData.lean:206,211,255`,
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/SmulUpdate.lean:99`.

*Proof.* The production proof `p5D` splits on $e_O$
(`PrvAndKernelCommutationUpToUnitsOfRests.lean:89–93`).

1. *Case $e_O=0$.* A place forces $e_O>0$ (`eO_pos`,
   `TheoremOfAlternateForm.lean:618`), so there are no places. Then
   $\mathrm{vsc}(g)=1$ for every $g$, and each `vGe` statement is plain integrality.
   `Iprod` reduces to $\mathrm{Int}_0$, and induction on the step with `Conclusion0`
   keeps the chain image integral (`PrvAndKernelCommutationUpToUnitsOfRests.lean:45–68`).
2. *Generators.* For $e_O>0$, `lift_bound_of_integrality` proceeds by induction on the
   span `Iprod S VV`. A generator is $\prod_{v\in BB}y_v^mF_0$, taken along a
   duplicate-free list $L$ of the places of $BB$. Here $F_0=\varpi^{\sigma}F_1$ with
   $\sigma=\sum_{v\in VV\setminus BB}\lceil S_ve_O\rceil$ and $F_1\in\mathrm{Int}_0$
   (`LiftBoundOfIntegrality.lean:112–114`). The Boolean $Q_j(v)$ records whether
   $G_{0n}(v,j+1)\le G_n(v,j+1)-\mathrm{PR}_n(v,j+1)$ (`:115`).
3. *Chain induction.* `main_ind` shows, for $m'\le m$, that
   $\mathrm{chainK}_{m'}\bigl((\prod_{v\in L}y_v)^{m'}F_1\bigr)$ has valuation at least
   $\sum_{j<m'}b_j$. Here $B_j=\{v\in L:Q_j(v)\}$, the value $\gamma_j(v)$ is
   $G_n(v,j+1)$ on $B_j$ and $G_{0n}(v,j+1)$ elsewhere, and
   $b_j=\sum_v\gamma_j(v)-d_G(j)-\mathrm{PrS}(j+1,B_j)$ (`YEPEComm.lean:127–143`).
   - At step $m'$ the list splits into $B=B_{m'}$ and its complement $C$. The $y_v$
     commute, and the $C$-part stays integral by `adm8` (`:153–164`).
   - On $B$, the relation of `Conclusion4` trades $y_v$ for the operator $Z_v$ at the
     cost $p^{\mathrm{PrZ}}$. This is `ZL_chain` (`:110–123,166–170`).
   - The previous step gives $\mathrm{vsc}(\sum_{j<m'}b_j)\,G'$ with
     $G'\in\mathrm{Int}_{m'}$ (`:171–174`).
   - `ZL_bound` bounds one step. `Zop_gen` expands $Z_v$ into the operators $T_{v,i}$,
     whose coefficients $\mathrm{cl}$ have valuation at least $0$, and at least
     $\mathrm{alEven}$ for $i=0$. For each generator the shifted levels $g_Q$ satisfy
     `PlaceB`, and `form_of_place` gives the step bound $\sum_vg_P(v)-d_G(j)$
     (`AofUpdate.lean:91–217`).
   - The valuations of the scalars $p^{-\mathrm{PrS}}$ and $\mathrm{vsc}$ add
     (`YEPEComm.lean:176–185`).
4. *Real arithmetic.* `basic₂` is a pure inequality in $\mathbb R$. It gives
   $T\le\sum_{v\in VV\setminus BB}S_v+\sum_{j<m}b_j$
   (`LiftBoundOfIntegrality.lean:24–87,122–135`). The index shift
   $\sum_{j=1}^mf(j)=\sum_{j<m}f(j+1)$ is `sum_Icc_shift` (`:12–15`). The integer
   $\mathrm{PrZ}$ equals the real $\Pr$ after casting. This holds because the number
   $n'$ of Frobenius positions is even, so $n'/2$ is exact in $\mathbb N$ (`PrZ_cast`,
   `:91–101`).
5. *Ceilings and witness.* With $g=\sum_{j<m}b_j$ the proof gets
   $\lceil Te_O\rceil\le\lceil ge_O\rceil+\sum_v\lceil S_ve_O\rceil$ (`:143–152`). It
   takes $n\in\mathbb N$ to be the difference. The witness $\varpi^nI$ then places the
   generator in $\mathrm{vsc}(T)\,\mathrm{Int}_m$ (`:153–162`). The span induction
   handles zero, sums and $O$-multiples (`:163–174`). $\square$

*Rational levels.* `EntCondition` is stated for rational $g_P$, while `form_of_place`
uses real levels. `ent_strict` picks rationals $q_v$ with
$g_P(v)-\varepsilon<q_v<g_P(v)$, where $\varepsilon=(\sum g_P-g')/(\#\mathrm{Pl}+1)$.
This gives `EntB` at every $g'<\sum g_P$. `formB_lim` removes the strict inequality.
The lattice is read only through $\lceil(g-d_G)e_O\rceil$, and a small $\delta$ with the
same ceiling exists.
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/RamifiedLatticeOfChainEstimates.lean:46,65,90`.

**Proposition 8.8 (the reader, `unit_bound_of_local_system`) [Lean, read].**
*`unit_bound_of_sum_over_primes` turns `Stmt D` and the local data into
`unitBoundAtTwistedPlaces`. From the packet of an admitted system it takes the sixth
field `VolumeRatio₂` and the eleventh field `LowTermBound`. From `admitted` it takes the
thirteenth field `adm11`. It passes all three to `unit_bound_of_local_system`, which
applies `UAt_of` at each place. `UAt_of` instantiates `LowTermBound` and compares
exponents.*
`src/Formalism/SharpRestriction/GrowthBounds/JointsTw.lean:9,23,216,243`,
`src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:718`,
`src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:161,172`.

*Proof.*

1. The proof sets $h_P$ to `hS.1 _ _ Y5 hA` and projects `hP.2.2.2.2.2.1` and
   `hP.2.2.2.2.2.2.2.2.2.2`, the sixth and eleventh conjuncts of `Conclusion₂`. It also
   projects `hA.2.2.2.2.2.2.2.2.2.2.2.2`, the thirteenth conjunct of `admitted`
   (`JointsTw.lean:265–270`). It never projects the second field,
   `FormalGroupSystem.Conclusion1`.
2. `UAt_of` unpacks `SysUAt` (`:34`). It sets $BB$ to the image of the chosen
   representatives and builds $G_n$, $\mathrm{PR}_n$, $G_{0n}$ and $S$ from the place
   data (`:39–48`).
   - The conditions `c1` and `c3` compare $G_n$ with $\mathrm{gB}$ and $\Pr$ with
     $\mathrm{PR}_n$. They use the small-residue comparison `hNum` when
     $1\le\log_p(2a)$ and the definitions otherwise (`:82–89,106–113`).
   - The condition `c2` is `LowAt` at level $G_{0n}$. At representatives it uses
     `lowAt_max`, which combines `VolumeRatio₂` with `adm11`. Elsewhere it uses the
     hypothesis `hFn` (`:90–105`).
   - `yProd` lies in `Iprod S BB` through the duplicate-free list of images, with
     $F_0=F$ at exponent $0$ (`:114–126`).
3. `LowTermBound` is applied at `:127`. Its bound is read as membership in
   $\varpi^{\lceil(\cdot)e_O\rceil}\mathrm{Int}_m$ (`:128–133`). The comparison `hTB` sums
   the place inequalities `hj` and adds `low` (`:135–209`). Finally `eO_eq_vUnit`
   identifies $e_O$ with the unit valuation `vUnit`, and `scale_pow_mono` lowers the
   integer exponent (`:210–214`; `Joints.lean:1608–1627`). $\square$

**Remarks [Open].**

1. *Hypothesis inputs.* `adm7` is the passage in `FormB` from column tests to lattice
   membership. Given `geC` bounds for every coefficient of
   $\mathrm{applyD}(\mathrm{PI}(j,I,i_0))f$, it supplies a frame $\varphi$ that puts the
   kernel image in `inLatC` (`FormalGroupSystem.lean:613–622`). It enters `entry_mem`
   when `admitted` is destructured (`KernelSumOfClassData.lean:211,231`), together with
   `ArchimedeanSignatureMatching`, the expansion of $K_j$ as a kernel sum. Both are
   fields of `admitted`. At the read site `SumOverPrimesHypotheses.lean:202`, the system
   and its `admitted` arrive in `hSys` from the field `twU` of the structure
   `SumOverPrimesHypotheses` (`:116–136,201`). So the jet-to-lattice step that Section
   8.4.4 left open is an assumption at this level. Where `SumOverPrimesHypotheses` is
   proved lies outside this chapter.
2. *Proofs not read.* The Gauss bounds reduce to `gauss_a_one_generic` and its
   companions (`EGaussK.lean:186–220`). We have also not read the proofs of
   `theorem_of_alternate_form`, `restGc`, `eb_brJet`, `ea_brClass`, `ea_brNum`
   and `ea_brScale`; Section 8.4.14 reads `ea_restSExpV_of` and `restSIntA`, and Sections 8.4.16–8.4.17 read `restBeta` and `BetaIsG_of`. LUMI's guide reports a full reading of `ea_A1U` and `ea_BrNum`
   and outlines `kernel_a_one_generic` and `main_ind`
   ([docs/04](https://github.com/aapolipponen/rh-lean-check-lumi/blob/main/docs/04-chain-and-one-half.md))
   [Community].
3. *An unused interface.* `EntryAOneParity.lean` also derives the place bounds from
   the hypotheses `SeriesGaussValuationFirst`, `SeriesGaussValuationSecond` and
   `ea_RestKerB`, through `ea_low` and `ea_three` (`EntryAOneParity.lean:122–160`;
   `EaRestSExpV.lean:44–47`). A search of the pinned archive finds no caller of
   `ea_three`. The production proof uses `ea_lowN` with the Gauss bounds instead, so
   these hypotheses are not inputs of the main path.
4. *Two uniformizers.* The kernel side uses $\pi\in K'$ with $\pi^{p^2-1}=p$, supplied
   by the normed extension of `nm_restNorm_of_place`. The lattice side uses the
   uniformizer $\varpi$ of $O$, with $p$ associated to $\varpi^{e_O}$. Levels are
   measured in units of $v_p$ on both sides. They become exponents of $\varpi$ only
   through $\lceil ge_O\rceil$.
   `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/NmRestNormOfPlace.lean:21`,
   `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:270,309`.

### 8.4.14 Producing `ea_RestSU`: logarithmic-coordinate integrality (`restSIntA`) and the exponential-factor reduction (`ea_restSExpV_of`)

**Motivation [Expository].** Every one of the three place bounds of Theorem 8.6 carries the hypothesis `hS : ea_RestSU X Y`, and Lemma 8.5 (`ea_lowN`) is where it is consumed: `hS` is what turns the kernel factor $\mathrm{ThZA}(\exp(-\mathrm{PhAt}_{j,v})\,U)$, after rescaling by $\pi$, into a series with the class expansion $\sum_i p^{-i}\,\mathrm{hhA}(u)^i g_i$ on which the Gauss bounds act. In the production file this hypothesis is supplied by a single line (`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/FirstTheoremPlaceBound.lean:17–18`):

```text
theorem ea_restSU (hG : RestGc p) : ea_RestSU X Y :=
  ea_restSU_of X Y (ea_restSExpV_of X (restBeta p) (th_restGcV_of X hG))
```

and the only caller of the three place bounds, `rests` (`PrvAndKernelCommutationUpToUnitsOfRests.lean:97–102`), passes `hG := restGc p`. Lemma 8.4 read the outer link `ea_restSU_of` and listed its two inner inputs, `ea_restSExpV_of` and `restSIntA`, among the declarations "whose statements we read but whose proofs we did not read". This subsection reads both proofs in full, together with their supply (`genInt`, `inParam_map`, `exists_mu`, `lamF_mem`, `log_at`, `atPi_map_ThZA`, `ea_reduce`), and keeps three deeper inputs named: the theorem `restBeta` (the "beta" exponential is $W$-integral after the logarithmic change of variables), the theorem `restGc` with its place-wise transport `th_restGcV_of` (the Gauss-type exponential $\exp(-G)$ in logarithmic $\pi$-coordinates equals $\exp(-(\pi^{p+1}/p)\,\mathrm{hhA}(u))$ times an integral factor), and the geometric construction behind `admitted`.

The mathematics that the two proofs share is a single change of variables. The formal group of this chapter has logarithm $\ell(T)=\sum_{j\ge0}p^{-j}T^{p^{2j}}$, a series with denominators that grow like $p^{(n-1)/(p^2-1)}$ in degree $n$; this is the height-two slope $\frac{1}{p^2-1}$ of Section 8.1 seen on the coefficients of the inverse series $e=\ell^{-1}$. The archive's residual factor $U$ is integral *in logarithmic coordinates*: the hypothesis of `ea_RestSU` is `IntR Y.Oc (inParamK p Y.Kc U)`, i.e. $U(\ell(X_1),\ell(X_2),\dots)$ has coefficients in $O_c$, not $U$ itself. The quantity that the Gauss bounds need is $U(\pi L_1,\pi L_2,\dots)$ for the linear forms $L_i=\mathrm{coordZA}_i$ and the root $\pi^{p^2-1}=p$. The bridge is the identity
$$\ell\bigl(\pi\,\mu(L)\bigr)=\pi L,\qquad \mu:=\lambda^{-1},\quad \lambda(T):=\pi^{-1}\ell(\pi T),$$
where $\lambda$ has coefficients in $R_p=W[\pi]$ and leading term $T$, so that $\mu$ exists and is $R_p$-integral. Hence $U(\pi L)=\bigl(U\circ\ell\bigr)(\pi\mu(L))$ is a substitution of integral zero-constant-term series into an integral series, and is integral. The same identity, applied to the exponential $\exp(-\Phi)$ of the phase, moves it into logarithmic coordinates where `RestBeta` and `RestGc` describe it. "Exponential growth" (the denominators of $e$), "normalization" (the root $\pi$ with $\pi^{p^2-1}=p$, whose powers cancel exactly those denominators), and "integrality" (closure of $R'$-integral series under substitution) are therefore not three separate mechanisms but one: the rescaling by $\pi$ is the logarithm's own normalization.

**Exact declaration check [Lean, read].** We quote the five statements that carry the argument; the notation is that of Sections 8.4.4–8.4.5.

- `ea_RestSU X Y` (`EntryAOneParity.lean:106–113`). Under `DworkLemma p` and `BeProp p Y.be`: for every place $v$, step $j$, series $U\in K_c[[X_{EA_j\sqcup EA_j}]]$ with `IntR Y.Oc (inParamK p Y.Kc U)`, every field $K'$ with compatible algebra maps from `K0 p` and $K_c$, every subring $R'\subseteq K'$ and $\pi\in K'$ with $\pi^{p^2-1}=p$, `Rp p K' vp ≤ R'` and $O_c\to R'$, there is $u:\mathrm{Fin}(n'_v)\to R'$ with `ea_InClassA X R' j (X.hhA K' j v u) (atPi vp (map (ThZA Y.Kc j (map (expS p (-Y.PhAt j v)) * U))))`.
- `RestSIntA X` (`KernelExpansionOfRestrictions.lean:41–46`). For all $j$, fields $K_1$, subrings $R_1\subseteq K_1$, series $U$ with `IntR R1 (inParamK p K1 U)`, fields $K'$ over $K_1$ and `K0 p`, subrings $R'$, roots $\pi$, with `Rp p K' vp ≤ R'` and $R_1\to R'$: `IntR R' (atPi vp (map (algebraMap K1 K') (X.ThZA K1 j U)))`.
- `ea_RestSExpV X` (`EaRestSExpV.lean:15–26`). Under `DworkLemma p`, for every `be` with `BeProp p be`, every $j$, $v$, every tower $K_0\to K_1\to K'$ and root $\pi\in K'$: there are $u$ with entries in `Rp p K' vp` and an `Rp`-integral $V$ with
  $$\mathrm{atPi}\bigl(\pi,\ \mathrm{ThZA}(\exp(-\textstyle\sum_e \mathrm{be}(X_{\mathrm{inl}(v,e)},X_{\mathrm{inr}(v,e)})))\bigr)=\mathrm{expK}\bigl(-(\pi^{p+1}/p)\,\mathrm{hhA}(u)\bigr)\,V .$$
  There is no $U$, no $R'$ and no $O_c$ in this statement: it concerns the exponential factor alone, over the fixed ring `Rp`.
- `RestBeta p` (`DworkExponentialRestrictions.lean:15–17`). If $5\le p$ and `DworkLemma p`, then for every `be` with `BeProp p be` there is $c\in W$ with $\sigma^2(c)=c$ and `E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))`.
- `ea_RestGcV X` (`EaRestSExpVOf.lean:249–258`). For every $c\in W$ with $\sigma^2(c)=c$, every $j$, $v$, field $K'$ over `K0 p`, root $\pi$, and every $\mu$ with $\mu(0)=0$ and `subst μ (lamF p vp) = X`: there are $u$ with entries in `Rp` and `Rp`-integral $V$ with
  $$\bigl(\exp(-\mathrm{ea\_GtV}_{j,v}(c,\sigma c))\bigr)\bigl(\pi\mu(\mathrm{coordZA})\bigr)=\mathrm{expK}\bigl(-(\pi^{p+1}/p)\,\mathrm{hhA}(u)\bigr)\,V,$$
  where `ea_GtV X j v c c' = ∑ e, ren ![inl ⟨v,e⟩, inr ⟨v,e⟩] (Gser p c c')` (`:245–247`) and the substitution is `tOf vp μ (X.coordZA K' j)`.

Three facts follow from the declarations alone. (a) `ea_RestSExpV` is quantified over *all* roots $\pi$ and *all* towers, so the choice of normed field made later in Lemma 8.5 is free; and `ea_RestGcV` is quantified over *all* right inverses $\mu$ of $\lambda$, so the specific $\mu$ produced by `exists_mu` (with coefficients in `Rp`) may be fed to it. (b) The number $5\le p$ enters the production of `ea_RestSU` exactly once, as the first argument of `RestBeta`, and is discharged by `(X.std v).five_le` (`EaRestSExpVOf.lean:262`; `FormalGroupSystem.lean:92`). (c) The phase `Y.PhAt j v` is *definitionally* the sum $\sum_e\mathrm{be}(X_{\mathrm{inl}(v,e)},X_{\mathrm{inr}(v,e)})$ (`FormalGroupSystem.lean:506–508`), so the general `Simeq` hypothesis of the reduction lemma is satisfied by reflexivity (`ea_Simeq_refl`, `EaRestSExpVOf.lean:227`): the production path never uses a phase that is merely *equivalent* to the standard one.

**Worked examples [Expository].** We compute the two mechanisms in the smallest cases: the integrality transfer of `restSIntA` in one variable for $p=5$, and the boundary of the exponential bound `piFact` that fixes the exponent $p+1$ in $\pi^{p+1}/p$.

1. **One-variable `restSIntA` for $p=5$ (minimal nondegenerate case).** Here $\ell(T)=\mathrm{lgF}=T+\tfrac15T^{25}+\tfrac1{25}T^{625}+\cdots$ (`OddLogRelation.lean:13–14`; `logF`, `FormalGroupSystem.lean:126–127`). Let $\pi$ satisfy $\pi^{24}=5$, so $v_p(\pi)=\tfrac1{24}$, and let $R_p=W[\pi]$.

   - *The rescaled logarithm.* $\lambda(T)=\pi^{-1}\ell(\pi T)=\sum_n\pi^{n-1}\ell_nT^n=T+\tfrac{\pi^{24}}{5}T^{25}+\tfrac{\pi^{624}}{25}T^{625}+\cdots=T+T^{25}+5^{24}T^{625}+\cdots$, since $\pi^{624}=(\pi^{24})^{26}=5^{26}$. In general the coefficient at $n=p^{2j}$ is $\pi^{(p^2-1)(1+p^2+\cdots+p^{2j-2})}p^{-j}=p^{(1+p^2+\cdots+p^{2j-2})-j}$, a nonnegative power of $p$ (`lamF_mem`). The leading coefficient is $1$ and the constant term is $0$.
   - *Its inverse.* Write $\mu=T+aT^{25}+bT^{49}+cT^{73}+\cdots$ and solve $\lambda(\mu(T))=\mu+\mu^{25}+\cdots=T$ degree by degree: $\mu^{25}=T^{25}+25aT^{49}+\bigl(25b+\binom{25}{2}a^2\bigr)T^{73}+\cdots$, so $a=-1$, $b=25$, $c=-(25\cdot25+300)=-925$:
     $$\mu(T)=T-T^{25}+25T^{49}-925T^{73}+\cdots\in\mathbb Z[[T]]\subseteq R_p[[T]].$$
   - *The formal-group exponential and its denominators.* Solving $\ell(e(Y))=Y$ with $e=Y+c_{25}Y^{25}+c_{49}Y^{49}+c_{73}Y^{73}+\cdots$: $e^{25}=Y^{25}+25c_{25}Y^{49}+\bigl(25c_{49}+300c_{25}^2\bigr)Y^{73}+\cdots$, and $e+\tfrac15e^{25}=Y$ gives $c_{25}=-\tfrac15$, $c_{49}=1$, $c_{73}=-\tfrac{25+12}{5}=-\tfrac{37}{5}$. So $e$ is **not** integral, and its denominators recur: $v_5(c_{25})=-1$, $v_5(c_{73})=-1$, while $v_5(c_{49})=0$.
   - *The identity $e(\pi Y)=\pi\mu(Y)$.* Coefficientwise: $c_{25}\pi^{25}=-\pi^{25}/5=-\pi$; $c_{49}\pi^{49}=\pi^{49}=25\pi$; $c_{73}\pi^{73}=-37\pi^{73}/5=-37\pi^{49}=-925\pi$. These are exactly $\pi\cdot(-1)$, $\pi\cdot25$, $\pi\cdot(-925)$, the coefficients of $\pi\mu$. The denominators of $e$ are absorbed by $\pi^n$ because $v_p(c_n)\ge-\tfrac{n-1}{p^2-1}$, which is precisely what $e(\pi Y)=\pi\mu(Y)$ with $\mu$ integral asserts.
   - *The transfer.* Take the one-variable residual factor $U(Y)=1+e(Y)$ over $K_1=K_0(\pi)$ with $R_1=R_p$. Then $\mathrm{inParamK}(U)=1+e(\ell(Y))=1+Y$, so the hypothesis `IntR R1 (inParamK U)` holds, while $U$ itself is *not* integral ($c_{25}=-\tfrac15$). With the linear form $L=Y$ (a `coordZA` with a single Witt coefficient $1$), the conclusion of `restSIntA` is the integrality of $U(\pi Y)=1+e(\pi Y)=1+\pi Y-\pi Y^{25}+25\pi Y^{49}-925\pi Y^{73}+\cdots$, which holds with all coefficients in $\pi R_p$. Without the rescaling the statement would be false, and without the logarithmic form of the hypothesis there would be nothing to transfer: the three ingredients (growth of $e$, the root $\pi$, closure of integral series under substitution) are each used.

2. **The exponent $p+1$ is the boundary of `piFact` (boundary-degenerate case).** The exponential factor produced by `ea_RestSExpV` is $\mathrm{expK}(-(\pi^{p+1}/p)\,h)$, and Lemma 8.4 applied `inClass_of_exp` with $c=\pi^{p+1}$, which needs $c^k/k!\in R_p$ for all $k$ (`piFact`, `NatCastInvMemRp.lean:52–70`, read in Section 8.4.4). Write $v=v_p$ with $v(\pi)=\tfrac1{p^2-1}$ and let $s_p(k)$ be the digit sum. Legendre's formula $(p-1)v(k!)=k-s_p(k)$ gives
   $$v\Bigl(\frac{(\pi^e)^k}{k!}\Bigr)=\frac{ek}{p^2-1}-\frac{k-s_p(k)}{p-1}.$$
   For $e=p+1$ this is $\tfrac{s_p(k)}{p-1}\ge\tfrac1{p-1}>0$ for $k\ge1$, with equality exactly at $k=p^m$: e.g. $k=p$ gives $c^p/p!=\pi^{p(p+1)}/(p\,(p-1)!)=\pi^{p+1}/(p-1)!$, an element of $R_p$ of valuation $\tfrac1{p-1}$ and not a unit. This is the archive's computation: `piFact` writes $k=(p-1)v(k!)+r$, uses $(\pi^{p+1})^{(p-1)v}=p^v$ (from $\pi^{(p+1)(p-1)}=p$, `:61–67`) and cancels $p^v$ against $k!=p^vm$, leaving $\pi^{(p+1)r}/m$ with $m$ a unit of $W$ (`natCast_inv_mem_Rp`, `:40–43`). For any smaller exponent $e\le p$ the bound fails: at $k=p^m$ the valuation is $\tfrac{ep^m}{p^2-1}-\tfrac{p^m-1}{p-1}$, which is $\ge0$ for all $m$ iff $e\ge p+1$; concretely for $p=5$, $e=5$, $k=25$: $\tfrac{125}{24}-6=-\tfrac{19}{24}<0$. So $v(\pi^{p+1})=\tfrac1{p-1}$ is the valuation of Dwork's constant $\pi_D$, $\pi_D^{p-1}=-p$ `[Dwork1960]`; by `piFact` the series $\exp(\pi^{p+1}x)$ has $R_p$-integral coefficients, while the explicit $1/p$ in $\pi^{p+1}/p$ is the loss that `inClass_of_exp` isolates as $p^{-i}$.

**Definitions [Lean, read].** All series are formal; `MvPowerSeries.subst` requires zero (nilpotent) constant terms (`MvPowerSeries.HasSubst`), and every substitution below is justified by a `constantCoeff = 0` lemma.

1. *Logarithm and logarithmic coordinates.* `logF p : PowerSeries (K0 p)` has coefficient $p^{-j}$ at $n=p^{2j}$ and $0$ otherwise (`FormalGroupSystem.lean:126–127`); its image in any $K'$ is `lgF K' p` (`map_logF`, `IntRPsubst.lean:155–160`; `OddLogRelation.lean:13`). `inParam p f := subst (fun i => subst (X i) (logF p)) f` and `inParamK p K1 f` with `lgF K1 p` (`FormalGroupSystem.lean:129–134`): substitute $\ell(X_i)$ for each variable. It is a ring homomorphism in $f$ (`th_inParam_sub`, `th_inParam_neg`, `th_inParam_sum`, `SubstitutionOfVariables.lean:139–155`), preserves zero constant terms (`th_inParam_const`, `:134`), commutes with renaming (`th_inParam_ren`, `:172`) and with field maps (`inParam_map`, `InParamMap.lean:99–120`; `th_inParamK_map`, `SubstitutionOfVariables.lean:51`).
2. *The ring `Rp` and the rescaling.* `Rp p K' vp` is the subring of $K'$ generated by the image of $W$ and $\pi$ (`FormalGroupSystem.lean:194–195`); `IntR R f` means every coefficient of $f$ lies in $R$ (`:123–124`). `atPi vp f` multiplies the coefficient of degree $n$ by $\pi^{|n|}$ (`:253–254`), and equals `MvPowerSeries.rescale (fun _ => vp) f` (`atPi_eq_rescale`, `AtPiEqRescale.lean:12–19`), i.e. the substitution $X_i\mapsto\pi X_i$.
3. *The rescaled logarithm and the substitution `tOf`.* `lamF p vp := mk fun n => vp ^ (n - 1) * coeff n (lgF K' p)` (`CyclicPowerClassOfExpEquiv.lean:35–36`), i.e. $\lambda(T)=\pi^{-1}\ell(\pi T)$ for $n\ge1$. For $\mu\in K'[[T]]$ and $L:\sigma\to K'[[X_\tau]]$, `tOf vp μ L i := subst (L i) (C vp * μ)` (`SubstitutionOfVariables.lean:17–19`), i.e. $i\mapsto\pi\mu(L_i)$.
4. *Integral exponentials.* `expK f` is the degree-truncated exponential $\sum_{k\le|n|}f^k/k!$ coefficientwise (`InClassOfExp.lean:52`), equal to `expS` over `K0 p` by definition (`FormalGroupSystem.lean:136–137`). `E0 p f` says $f(0)=0$ and $\exp(f)=1+h$ with $h$ a $W$-integral series with $h(0)=0$ (`IntegralExpRename.lean:61–63`). `Simeq p f g` says $(f-g)(0)=0$ and `E0`-type integrality of $\exp(\mathrm{inParam}(f-g))$ (`FormalGroupSystem.lean:139–142`). `ren φ f` renames variables along $\varphi$ (`IntegralExpRename.lean:88–89`); `sub2 p be x y = subst ![x, y] be` (`FormalGroupSystem.lean:144–145`).
5. *The series `Gser` and `hhA`.* `Gser p c c' = C c * Aser - C c' * Aser'` with `Aser`, `Aser'` the two-variable series supported on exponents $((p^2)^i,\,p(p^2)^j)$, $i\le j$, with coefficients $p^{-(i+j+1)}$ (`OddLogRelation.lean:20–29`); its constant term is $0$ (`th_Gser_const`, `DworkExponentialRestrictions.lean:44–51`). `X.hhA K' j v u = ∑ s, C (u s) * ∑ a b, (sSA s a b)^p * sSA (s+1) a b` with `sSA` the alternating series $\sum_l(-1)^lX_{(v,s-2l,a,b)}^{p^{2l}}$ (`FormalGroupSystem.lean:424–432`); its constant term is $0$ (`hhA_const`, `AllPlacesOfRestrictions.lean:23–26`). We read these as statements; their internal structure is used only through the two constant-term lemmas.

**Lemma 8.14a (the rescaled logarithm is `Rp`-integral and invertible: `lamF_mem`, `exists_mu`, `log_at`) [Lean, read].** *Let $K'$ be a field over `K0 p` and $\pi\in K'$ with $\pi^{p^2-1}=p$.*

1. *Every coefficient of `lamF p vp` lies in `Rp p K' vp`* (`IntRPsubst.lean:97–122`).
2. *There is $\mu\in K'[[T]]$ with $\mu(0)=0$, all coefficients in `Rp`, and `subst μ (lamF p vp) = X`* (`:124–153`).
3. *For such $\mu$ and any $L$ with $L(0)=0$: `subst (subst L (C vp * μ)) (lgF K' p) = C vp * L`, i.e. $\ell(\pi\mu(L))=\pi L$* (`InParamMap.lean:29–56`).

*Proof.*

1. The coefficient at $n$ is $\pi^{n-1}\sum_{j\le n}[n=p^{2j}]p^{-j}$. Fix $j$ with $n=(p^2)^j$. From $(p^2-1)j+1\le(p^2)^j$ (`mul_add_one_le_succ_pow`, `:90–95`, an induction on $j$), write $n-1=(p^2-1)j+m$. Then $\pi^{n-1}p^{-j}=\pi^{(p^2-1)j}\pi^mp^{-j}=p^j\pi^mp^{-j}=\pi^m\in R_p$ (`:109–120`; the case $\pi^{(p^2-1)j}=0$ is handled separately and gives $0$).
2. Let $l_0\in R_p[[T]]$ be `lamF` with coefficients coerced into `Rp` by (1) (`:127–131`). Its constant term is $0$ (`constantCoeff_lamF`, `LogarithmEquivalence.lean:201`) and its linear coefficient is $1$ (`coeff_one_lamF`, `:205`, using $2\le p$), a unit. Mathlib's `PowerSeries.substInvOfIsUnit l0 hu` is a right inverse: `subst (l0.substInvOfIsUnit hu) l0 = X` (`PowerSeries.subst_substInvOfIsUnit_right`), with zero constant term (`constantCoeff_substInvOfIsUnit`). Map everything along the inclusion $R_p\hookrightarrow K'$ (`ps_map_subst`, `LogarithmEquivalence.lean:172`) and set $\mu$ to be the image (`:146–153`). Integrality of $\mu$ is by construction: it was built over the ring $R_p$.
3. Coefficientwise, `rescale vp (lgF) = vp • lamF` (`hres`, `:40–48`): the $n$-th coefficient of $\ell(\pi T)$ is $\pi^n\ell_n=\pi\cdot\pi^{n-1}\ell_n$. Hence $\ell(\pi\mu)=\pi\lambda(\mu)=\pi T$ (`hsub`, `:49–54`, using `PowerSeries.subst_comp_subst_apply` and `rescale_eq_subst`), and substituting $L$ for $T$ (`:55–56`) gives $\ell(\pi\mu(L))=\pi L$. $\square$

**Lemma 8.14b (integrality transfers through logarithmic coordinates: `genInt`, `inParam_map`) [Lean, read].** *Let $R'\subseteq K'$ be a subring with `Rp p K' vp ≤ R'`.*

1. *(`genInt`, `InParamMap.lean:58–97`) If `IntR R' (inParamK p K' U)` and $L_i$ are $R'$-integral with $L_i(0)=0$, then `IntR R' (subst (fun i => C vp * L i) U)`, i.e. $U(\pi L)$ is $R'$-integral.*
2. *(`inParam_map`, `:99–120`) If `IntR R1 (inParamK p K1 U)` and $R_1\to R'$ under $K_1\to K'$, then `IntR R' (inParamK p K' (map (algebraMap K1 K') U))`.*

*Proof.*

1. Take $\mu$ from Lemma 8.14a(2) and set $M_i:=\pi\mu(L_i)$ (`:64`). Each $M_i$ has zero constant term (`cc_subst_lemma`, `:21–27,66`) and is $R'$-integral: the series $\pi\mu$ has coefficients $\pi\mu_n\in R_p\subseteq R'$ (`:67–74`), and substituting an integral zero-constant-term series into an integral series is integral (`IntR_subst`, `IntRPsubst.lean:53–71`: each coefficient of the substitution is a finite sum of products of coefficients, `MvPowerSeries.coeff_subst`). The key identity (`:80–95`) is
   $$U(\pi L)=\bigl(\mathrm{inParamK}\,U\bigr)(M),$$
   because $\mathrm{inParamK}\,U=U(\ell(X_i))$ and $\ell(M_i)=\pi L_i$ by Lemma 8.14a(3); formally, `subst_comp_subst_apply` composes the two substitutions and `log_at` identifies the inner one. Then `IntR_subst` applied to the integral series $\mathrm{inParamK}\,U$ and the integral $M$ gives the claim (`:96–97`).
2. `inParamK` commutes with `map (algebraMap K1 K')` (`:107–116`): `map_subst` moves the field map inside the substitution, and the coefficients $p^{-j}$ of `lgF` are fixed by any field map (`PowerSeries.coeff_map`, `IsScalarTower.algebraMap_apply`). So each coefficient of `inParamK p K' (map U)` is the image of a coefficient of `inParamK p K1 U`, which lies in $R_1$ and maps into $R'$ (`:117–120`). $\square$

**Theorem 8.14c (`restSIntA`) [Lean, read].** *`RestSIntA X` holds for every `X : Sys p`.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AtPiEqRescale.lean:64–71`.

*Proof.* Fix $j$, $K_1$, $R_1$, $U$ with `IntR R1 (inParamK p K1 U)`, and $K'$, $R'$, $\pi$ with `Rp ≤ R'`, $R_1\to R'$ (`:65`).

1. *Rescaling a substitution of linear forms* (`atPi_map_ThZA`, `:49–62`). `ThZA K1 j U = subst (coordZA K1 j) U` (`FormalGroupSystem.lean:392–394`). The field map passes inside the substitution (`MvPowerSeries.map_subst`) and `map_coordZA` (`:42–47`) identifies `map (coordZA K1 j x)` with `coordZA K' j x`, since the coefficients are images of Witt vectors and the tower is compatible. Then `atPi vp = rescale (fun _ => vp) = subst (vp • X)` (`atPi_eq_rescale`; `MvPowerSeries.rescale_eq_subst`), and composing substitutions (`subst_comp_subst_apply` with `HasSubst.smul_X`) gives `subst (fun x => atPi vp (coordZA K' j x)) (map U)`. Finally `atPi_coordZA` (`:38–40`, from `atPi_sum_C_mul_X_eq_C_mul`, `:23–36`): since each `coordZA K' j x` is a sum of monomials of total degree $1$, `atPi vp` multiplies it by $\pi$, i.e. `atPi vp (coordZA x) = C vp * coordZA x`. So
   $$\mathrm{atPi}\bigl(\pi,\ \mathrm{map}(\mathrm{ThZA}\,U)\bigr)=\bigl(\mathrm{map}\,U\bigr)\bigl(\pi\,\mathrm{coordZA}_{K'}\bigr).$$
2. Apply Lemma 8.14b(1) to $U':=\mathrm{map}\,U$ and $L:=\mathrm{coordZA}_{K'}$ (`:67–68`). Its hypothesis `IntR R' (inParamK p K' U')` is Lemma 8.14b(2). The linear forms have zero constant term (`coordZA_const`, `AllPlacesOfRestrictions.lean:28–31`) and are $R'$-integral (`:69–71`): each is a finite sum of `C (Witt image) * X`, and the Witt images lie in `Rp ≤ R'` (`W_mem_Rp`, `NatCastInvMemRp.lean:22–23`; `IntR_sum`, `IntR_mul`, `IntR_C`, `IntR_X`). $\square$

**Lemma 8.14d (integral exponentials: inversion, reflexivity) [Lean, read].**

1. *(`exists_expK_neg_eq_map_of_expK_eq_one_add`, `EaRestSExpVOf.lean:86–100`) If $z(0)=0$ and $\exp(z)=1+h$ with $h$ $W$-integral, $h(0)=0$, then $\exp(-z)$ is the image of a $W$-integral series.*
2. *(`ea_Simeq_refl`, `:227–239`) `Simeq p f f` for every $f$.*

*Proof.* (1) $1+h$ is a unit of $W[[X]]$ with inverse `invOfUnit (1 + h) 1` (`MvPowerSeries.mul_invOfUnit`, since the constant term is $1$). As $z(0)=0$, `expK_add` gives $\exp(-z)\exp(z)=\exp(0)=1$ (`th_expK_zero`), so $\exp(-z)=\exp(-z)\cdot(1+h)\cdot(1+h)^{-1}=(1+h)^{-1}$ (`:92–100`); `CharZero K0` is supplied by `charZero_K' p (K0 p)` (`NatCastInvMemRp.lean:74–84`). (2) $f-f=0$, `inParam p 0 = 0` (`th_inParam_sub`), and `expS p 0 = 1` because only the $k=0$ term of the truncated exponential survives (`:232–239`); take $h=0$. $\square$

**Lemma 8.14e (the exponential-factor reduction: `ea_reduce`) [Lean, read].** *Let $\sigma$ be finite, $A$ a finite index type with maps $a,b:A\to\sigma$, `be` with $\mathrm{be}(0)=0$, $c,c'\in K_0$ with $G:=\mathrm{Gser}(c,c')$, $G(0)=0$, and assume `E0 p (inParam p be - G)` (this is what `RestBeta` provides). Let $\Phi\in K_0[[X_\sigma]]$ with `Simeq p Φ (∑ x, sub2 p be (X (a x)) (X (b x)))`. Let $K'$, $\pi$, and $\mu$ be as in Lemma 8.14a(2), and let $L:\sigma\to K'[[X_\tau]]$ be `Rp`-integral with $L_i(0)=0$. Then there is an `Rp`-integral $V'$ with*
$$\bigl(\exp(-\Phi)\bigr)(\pi L)=\Bigl(\exp\bigl(-\textstyle\sum_{x\in A}\mathrm{ren}_{[a_x,b_x]}G\bigr)\Bigr)\bigl(\pi\mu(L)\bigr)\cdot V'.$$
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpVOf.lean:102–225`.

*Proof.* Write $S:=\sum_x\mathrm{be}(X_{a_x},X_{b_x})=\sum_x\mathrm{ren}_{[a_x,b_x]}\mathrm{be}$ (`hsubren`, `:137–139`), $G_s:=\sum_x\mathrm{ren}_{[a_x,b_x]}G$, $E:=\mathrm{inParam}\,\Phi-\mathrm{inParam}\,S$, and $Y:=\sum_x\mathrm{ren}_{[a_x,b_x]}(\mathrm{inParam}\,\mathrm{be}-G)$ (`:173–176`). All of $S$, $\Phi$, $G_s$, $E$, $Y$ have zero constant term (`:140–146,160–166`, from `th_inParam_const`, `th_ren_const`-type lemmas `hren0`).

1. *Decomposition in logarithmic coordinates* (`hdecomp`, `:156–159`). Since `inParam` is additive and commutes with renaming (`th_inParam_sum`, `th_inParam_ren`), $\mathrm{inParam}\,S=\sum_x\mathrm{ren}_{[a_x,b_x]}(\mathrm{inParam}\,\mathrm{be})=Y+G_s$ (`hInS`, `hY`, `:147–155`). Hence
   $$\mathrm{inParam}(-\Phi)=-G_s-(E+Y).$$
2. *Two integral exponentials* (`hWE`, `hWY`, `:177–210`). The `Simeq` hypothesis says $\exp(\mathrm{inParam}(\Phi-S))=\exp(E)=1+h$ with $h$ $W$-integral, so by Lemma 8.14d(1) $\exp(-E)$ is $W$-integral. For $Y$, the exponential of a finite sum of zero-constant-term series is the product of exponentials (`expK_add`, induction on the finset, `:182–190`); each factor $\exp(-\mathrm{ren}_{[a_x,b_x]}(\mathrm{inParam}\,\mathrm{be}-G))$ is the renaming of $\exp(-(\mathrm{inParam}\,\mathrm{be}-G))$ (`th_subst_expK`, `:209`), which is $W$-integral by `E0` and Lemma 8.14d(1); renaming and products preserve $W$-integrality (`:192–210`). Let $w_E,w_Y\in W[[X_\sigma]]$ be the two witnesses.
3. *The substitution.* The series $\pi\mu(L_i)$ (= `tOf vp μ L i`) have zero constant term (`hT0`, `:124–125`) and are `Rp`-integral (`hTint`, `:127–130`, by `IntR_psubst` since $\pi\mu_n\in R_p$). Define
   $$V':=\bigl(\mathrm{map}(w_E\,w_Y)\bigr)\bigl(\pi\mu(L)\bigr),$$
   `Rp`-integral by `IntR_subst` and `W_mem_Rp` (`:213–218`).
4. *The identity.* By the logarithmic change of variables (`subst_C_mul_map_eq_subst_tOf_map_inParam`, `:40–84`, the multivariable form of Lemma 8.14b(1)'s key step: $f(\pi L)=(\mathrm{inParam}f)(\pi\mu(L))$, using `subst_C_mul_lgF_eq_C_mul_X_of_inverse`, `:18–38`, which is Lemma 8.14a(3) for $L=X$),
   $$\bigl(\exp(-\Phi)\bigr)(\pi L)=\bigl(\mathrm{inParam}\,\exp(-\Phi)\bigr)(\pi\mu(L))=\bigl(\exp(\mathrm{inParam}(-\Phi))\bigr)(\pi\mu(L)),$$
   the last step because `inParam` is a substitution with zero-constant-term entries and commutes with `expK` (`hinExp`, `:167–170`; `th_subst_expK`). By step 1 and `expK_add` twice (`:222–224`), $\exp(\mathrm{inParam}(-\Phi))=\exp(-G_s)\exp(-E)\exp(-Y)=\exp(-G_s)\cdot\mathrm{map}(w_Ew_Y)$. Substituting $\pi\mu(L)$ is multiplicative (`MvPowerSeries.subst_mul`) and commutes with `map` and `expK` (`th_map_expK`, `:225`), which gives the displayed formula with $V'$ from step 3. $\square$

**Theorem 8.14f (`ea_restSExpV_of`) [Lean, read].** *If `RestBeta p` and `ea_RestGcV X`, then `ea_RestSExpV X`.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpVOf.lean:260–272`.

*Proof.* Fix `hD`, `be`, `hbe`, $j$, $v$, the tower $K_0\to K_1\to K'$ and $\pi$ (`:261`).

1. `RestBeta` at $5\le p$ (`(X.std v).five_le`) gives $c\in W$ with $\sigma^2c=c$ and `E0 p (inParam p be - Gser p (wK c) (wK (σ c)))` (`:262`).
2. `exists_mu` gives $\mu$ with $\mu(0)=0$, `Rp`-coefficients, and $\lambda(\mu)=T$ (`:263`).
3. `ea_RestGcV` at $c$, $j$, $v$, $K'$, $\pi$, $\mu$ gives $u$ with entries in `Rp` and an `Rp`-integral $V$ with $\bigl(\exp(-\mathrm{ea\_GtV}_{j,v}(c,\sigma c))\bigr)(\pi\mu(\mathrm{coordZA}))=\mathrm{expK}(-(\pi^{p+1}/p)\,\mathrm{hhA}(u))\,V$ (`:264`).
4. Lemma 8.14e with $A$ the index set `Eidx (n' v) (NN m t j) (NN m t (j+1))`, $a_e=\mathrm{inl}\langle v,e\rangle$, $b_e=\mathrm{inr}\langle v,e\rangle$, $\Phi=S$ itself (reflexivity, Lemma 8.14d(2)), the constant family of `E0` witnesses from step 1, and $L=\mathrm{coordZA}_{K'}$ (zero constant terms by `coordZA_const`; `Rp`-integral by `th_coordZA_int`, `DworkExponentialRestrictions.lean:78–89`) gives $V'$ (`:265–268`).
5. Return $u$, $V\cdot V'$ (`IntR_mul`). The goal is `atPi vp (map (ThZA K1 j (map (expS (-S))))) = expK(...) * (V * V')`. By `atPi_map_ThZA` and `map_map_tower` (`KernelExpansionOfRestrictions.lean:75–80`) the left side is $(\exp(-S))(\pi\,\mathrm{coordZA}_{K'})$; Lemma 8.14e rewrites it as $(\exp(-G_s))(\pi\mu(\mathrm{coordZA}))\cdot V'$; unfolding `ea_GtV` shows $G_s$ is exactly `ea_GtV X j v (wK c) (wK (σ c))`, so step 3 rewrites the first factor and `mul_assoc` finishes (`:269–272`). $\square$

**Corollary 8.14g (assembly of `ea_RestSU` at the three place bounds) [Lean, read].** *Assume `RestGc p`. Then `ea_RestSU X Y` for every `Y : Pend X`, and the hypothesis `hS` at each of the three call sites `FirstTheoremPlaceBound.lean:22,26,30` is the same term `ea_restSU X Y hG`. In the archive, `hG` is the theorem `restGc p` (`CommonEigenvectorThird.lean:21`), passed at `rests` (`PrvAndKernelCommutationUpToUnitsOfRests.lean:100–102`).*

*Proof.* `th_restGcV_of X hG : ea_RestGcV X` (`ThRestGcVOf.lean:27–57`): it instantiates `RestGc` at the place data of $v$, namely $n'=X.G.P.n'\,v$, $r_0=\mathrm{NN}(m,t,j)$, $r_1=\mathrm{NN}(m,t,j+1)$, the basis `X.om v`, with `five_le`, `two_le`, `even` from `X.std v` (`:29–31`), and transports the resulting identity from the variables `Zidx` of one place to `X.ZA j` by the injective renaming $z\mapsto\langle v,z\rangle$ (`:32–57`; `th_GtV_eq`, `:16–25`, identifies `ea_GtV` with the renamed `Gt`). We read the statement and the instantiation (`:27–33`); the renaming lemmas `th_ren_*`, `th_hhA_eq`, `th_coordZA_eq` (`ExpansionAllPlacesOfPlace.lean`) are cited `[Lean]`. Then `restBeta p : RestBeta p` (`BiadditiveSecondVariable.lean:137`, `[Lean]`), Theorem 8.14f and Lemma 8.4 give `ea_RestSU X Y`. The three call sites pass the identical term, so the $u$ chosen inside `ea_lowN` for the three levels `g0v`, `gv - alEven`, `gv` comes from one and the same supply, though `ea_lowN` makes its own existential choices of $R'$, $\pi$, $u$ at each use. $\square$

**Remarks [Expository].**

1. *Where the three mechanisms act in the consumer.* In Lemma 8.5 the ring $R'$ is the unit ball of the normed extension of Section 8.4.13, which contains `Rp` because $\lVert\pi\rVert=p^{-1/(p^2-1)}\le1$ and the Witt images lie in $O_c$ (`ea_Rp_le_ball`). Theorem 8.14c puts $W=\mathrm{atPi}(\pi,\mathrm{ThZA}\,U)$ in the ball (integrality); Theorem 8.14f writes the exponential factor as $\mathrm{expK}(-(\pi^{p+1}/p)h)V$ with $V$ in the ball (normalization by $\pi$); and `inClass_of_exp` with `piFact` converts $\mathrm{expK}(-(\pi^{p+1}/p)h)\,VW$ into $\sum_ip^{-i}h^ig_i$ with $g_i=((-\pi^{p+1})^i/i!)\,VW$ in the ball (exponential growth, bounded by Legendre). The Gauss bounds then estimate each $h^ig_i$ and pay $p^{-i}$ for the $i$-th term; the level $g$ is what survives.
2. *The logarithm is the normalization.* The only place where $\pi^{p^2-1}=p$ is used in this subsection is Lemma 8.14a(1): it makes $\lambda=\pi^{-1}\ell(\pi T)$ integral. Everything else is bookkeeping of substitutions. Equivalently, the rescaling $X\mapsto\pi X$ is the change of variables that makes the formal-group logarithm integral with unit linear term, and `exists_mu` is the resulting formal inverse function theorem over $R_p$. This is the formal-group counterpart of Section 8.1's Newton-polygon computation, and the archive never needs the formal group law itself: `logF` is defined directly as a series, and the functional equation $\ell(T)=T+\tfrac1p\ell(T^{p^2})$, of the type studied in `[Hazewinkel1978]`, is visible in its coefficients but is not invoked.
3. *Why the hypothesis is on `inParamK U`.* `ExtensionLocalCondition` (`FormalGroupSystem.lean:162–170`) and `admitted` phrase the integrality of the residual factor after the logarithmic change of variables. Example 1 shows this is the natural normalization: the factor $1+e(Y)$ is integral in logarithmic coordinates but not in geometric ones, and only the former integrality survives the rescaling. Had `admitted` asked for `IntR Y.Oc U`, Theorem 8.14c would be immediate (integral series, integral linear forms) but the geometric input would be stronger than what the theta-kernel construction provides.
4. *Generality not used in production.* `ea_reduce` allows a phase $\Phi$ merely `Simeq`-equivalent to the standard sum $S$; `ea_restSExpV_of` applies it with $\Phi=S$ (so $E=0$, $w_E=1$). The multi-place variants `RestSExpA`/`restSExpA_of` (`DworkExponentialRestrictions.lean:118–135`, with a product over all places) and the non-`A` variants `RestSExp`/`RestSInt`/`restSInt` (`KernelExpansionOfRestrictions.lean:12–27`; `InParamMap.lean:124–143`) are proved by the same lemmas and feed `Conclusion1` and `ExpansionsMultiply`, which Section 8.4.5's dependency diagram showed are packed but not read at the three read sites. The one-place-at-a-time form `ea_RestSExpV` is the one on the main path.
5. *What remains named.* The Frobenius-fixed element $c$ and the $W$-integrality of $\exp(-(\mathrm{inParam}\,\mathrm{be}-G))$ are `restBeta`, a 137-line-deep statement about the second variable of the biadditive series `be`; the identity $\exp(-G)(\pi\mu(\mathrm{coordZ}))=\exp(-(\pi^{p+1}/p)\mathrm{hhS}(u))V$ is `restGc`, which is where the specific series `Gser`, the dual bases `OmBasis` and the Frobenius-twisted monomials `sSer`/`sSA` interact. Neither is read here. In particular we have **not** verified that $\pi^{p+1}/p$ is the correct constant; we have verified that, given `restGc`, the constant is transported unchanged to `ea_RestSU` and that it is the unique exponent for which `piFact` holds (Example 2). The biadditive supply `restBeta` and its conditional `BetaIsG_of` assembly are read in [§8.4.16](#8416-the-biadditive-supply-restbeta-from-beprop-to-the-frobenius-fixed-class-of-gser) and [§8.4.17](#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar).

**Reading boundary and sources.** This subsection adds R3 `[Lean, read]` for the complete files `EaRestSExpV.lean:1–49`, `EaRestSExpVOf.lean:1–274`, `AtPiEqRescale.lean:1–73`, `InParamMap.lean:1–145`, `IntRPsubst.lean:1–164`, `SubstitutionOfVariables.lean:1–259` (with `th_reduce`, `:199–256`, read as the single-place prototype of `ea_reduce`), `NatCastInvMemRp.lean:1–86`, and `IntegralExpRename.lean:1–127`; for `RestBeta`, `RestGc`, `th_Gser_const`, `th_be_const`, `th_coordZA_int` (`DworkExponentialRestrictions.lean:13–89`); for `RestSInt`, `RestSExpA`, `RestSIntA`, `map_map_tower`, `atPi_mul` (`KernelExpansionOfRestrictions.lean:22–92`); for `hhA_const`, `coordZA_const`, `ThZA_mul` (`AllPlacesOfRestrictions.lean:14–35`); for the statement and instantiation of `th_restGcV_of` (`ThRestGcVOf.lean:16–33`); and for `lamF`, `lgF`, `Gser`, `logF`, `inParam`, `inParamK`, `expS`, `Simeq`, `sub2`, `BeProp`, `Rp`, `atPi`, `coordZA`, `ThZA`, `sSA`, `hhA`, `PhAt` as definitions (`FormalGroupSystem.lean:123–147,194,253,384–394,424–432,506–508`; `OddLogRelation.lean:13–29`; `CyclicPowerClassOfExpEquiv.lean:35–36`). The Mathlib declarations `PowerSeries.substInvOfIsUnit`, `PowerSeries.subst_substInvOfIsUnit_right`, `PowerSeries.constantCoeff_substInvOfIsUnit`, `MvPowerSeries.rescale`, `MvPowerSeries.rescale_eq_subst`, `MvPowerSeries.subst_comp_subst_apply`, `MvPowerSeries.map_subst`, `MvPowerSeries.subst_mul`, `MvPowerSeries.hasSubst_of_constantCoeff_zero`, `MvPowerSeries.invOfUnit`, `MvPowerSeries.mul_invOfUnit`, `sub_one_mul_padicValNat_factorial`, and `WittVector.isUnit_of_coeff_zero_ne_zero` are cited `[Lean]` at the pinned commit, with statements checked against the current Mathlib documentation on 2026-11-25 (where the Legendre lemma now appears as `Nat.Prime.sub_one_mul_multiplicity_factorial`). Named inputs unchanged: `restBeta` (`BiadditiveSecondVariable.lean:137`), `restGc` (`CommonEigenvectorThird.lean:21`), the renaming lemmas of `ExpansionAllPlacesOfPlace.lean`, the Gauss bounds, `ea_brScale`, `ea_brNum`, `eb_brJet`, `ea_brClass`, `nm_restNorm_of_place` (Section 8.4.13), and the geometric construction behind `admitted`. The mathematics and formal proofs are those of Levent Alpöge with Claude, archive A2, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`; the two worked examples and the three-mechanism reading are ours.

| Role | Declaration | Source |
|---|---|---|
| Assembly and call sites | `ea_restSU`; `first_theorem_place_bound`, `second_lemma_place_bound`, `hecke_place_bound`; `rests` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/FirstTheoremPlaceBound.lean:17–30`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PrvAndKernelCommutationUpToUnitsOfRests.lean:97–102` |
| Consumer interface | `ea_RestSU`, `ea_InClassA`, `ea_restSU_of` (Lemma 8.4), `ea_three` (unused) | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EntryAOneParity.lean:101,106`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpV.lean:15,28,44` |
| Exponential factor (top) | `ea_GtV`, `ea_RestGcV`, `ea_restSExpV_of`, `ea_Simeq_refl`, `ea_reduce`, `subst_C_mul_lgF_eq_C_mul_X_of_inverse`, `subst_C_mul_map_eq_subst_tOf_map_inParam`, `exists_expK_neg_eq_map_of_expK_eq_one_add` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpVOf.lean:245,249,260,227,102,18,40,86` |
| Integral factor (top) | `restSIntA`, `atPi_map_ThZA`, `map_coordZA`, `atPi_coordZA`, `atPi_eq_rescale` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AtPiEqRescale.lean:64,49,42,38,12` |
| Logarithmic coordinates | `lgF_const`, `log_at`, `genInt`, `inParam_map`, `restSInt`; `tOf`, `th_inParamK_map`, `th_tOf_const`, `th_subst_log`, `th_inParam_const`, `th_inParam_sub`, `th_inParam_neg`, `th_inParam_sum`, `th_inParam_ren`, `Gt`, `th_reduce` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/InParamMap.lean:17,29,58,99,124`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/SubstitutionOfVariables.lean:17,51,69,76,134,139,145,151,172,196,199` |
| Rescaled logarithm and integrality | `IntR_add`, `IntR_zero`, `IntR_sum`, `IntR_X`, `IntR_subst`, `IntR_of_ps`, `IntR_psubst`, `lamF_mem`, `exists_mu`, `map_logF` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/IntRPsubst.lean:15,20,25,31,53,73,80,97,124,155` |
| Dwork constant and units | `pK'_ne`, `W_mem_Rp`, `vp_mem_Rp`, `natCast_unit`, `natCast_inv_mem_Rp`, `piFact`, `charZero_K'` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/NatCastInvMemRp.lean:16,22,25,28,40,52,74` |
| Integral exponentials | `th_expK_zero`, `th_subst_expK`, `th_map_expK`, `E0`, `integralExp_zero`, `integralExp_add`, `integralExp_sum`, `ren`, `integralExp_rename` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/IntegralExpRename.lean:15,30,48,61,65,69,76,88,91` |
| Statements of the named inputs | `wK`, `RestBeta`, `RestGc`, `RestGcA`, `th_Gser_const`, `th_be_const`, `th_coordZA_int`, `restSExpA_of`; `th_GtV_eq`, `th_restGcV_of`; `restBeta`; `restGc` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DworkExponentialRestrictions.lean:13,15,19,29,44,53,78,118`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/ThRestGcVOf.lean:16,27`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:137`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CommonEigenvectorThird.lean:21` |
| Definitions read | `IntR`, `logF`, `inParam`, `inParamK`, `expS`, `Simeq`, `sub2`, `BeProp`, `Rp`, `DworkLemma`, `atPi`, `Std.five_le`, `coordZA`, `ThZA`, `sSA`, `hhA`, `Pend.PhAt`; `RestSInt`, `RestSExpA`, `RestSIntA`, `map_map_tower`, `atPi_mul`; `sSA_const`, `hhA_const`, `coordZA_const`, `ThZA_mul`; `lgF`, `Aser`, `Aser'`, `Gser`; `lamF`; `constantCoeff_lamF`, `coeff_one_lamF`, `ps_map_subst` | `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:123,126,129,132,136,139,144,147,194,225,253,92,384,392,424,429,506`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelExpansionOfRestrictions.lean:22,29,41,75,82`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AllPlacesOfRestrictions.lean:14,23,28,33`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/OddLogRelation.lean:13,20,24,28`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/CyclicPowerClassOfExpEquiv.lean:35`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean:172,201,205` |
| Mathlib cited `[Lean]` | `PowerSeries.substInvOfIsUnit`, `PowerSeries.subst_substInvOfIsUnit_right`, `PowerSeries.constantCoeff_substInvOfIsUnit`, `PowerSeries.rescale_eq_subst`, `PowerSeries.subst_comp_subst_apply`, `MvPowerSeries.rescale`, `MvPowerSeries.coeff_rescale`, `MvPowerSeries.rescale_eq_subst`, `MvPowerSeries.subst_comp_subst_apply`, `MvPowerSeries.map_subst`, `MvPowerSeries.subst_mul`, `MvPowerSeries.HasSubst.smul_X`, `MvPowerSeries.hasSubst_of_constantCoeff_zero`, `MvPowerSeries.invOfUnit`, `MvPowerSeries.mul_invOfUnit`, `sub_one_mul_padicValNat_factorial`, `WittVector.isUnit_of_coeff_zero_ne_zero` | Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`: `Mathlib/RingTheory/PowerSeries/Substitution.lean`, `Mathlib/RingTheory/MvPowerSeries/Substitution.lean`, `Mathlib/RingTheory/MvPowerSeries/Inverse.lean`, `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`, `Mathlib/RingTheory/WittVector/DiscreteValuationRing.lean` |
| Named inputs retained `[Lean]` / `[Open]` | `restBeta`, `restGc` and the proof body of `th_restGcV_of` (renaming lemmas `th_ren_*`, `th_hhA_eq`, `th_coordZA_eq`, `th_IntR_ren`, `ExpansionAllPlacesOfPlace.lean`); `kernel_a_one_generic`, `kernel_a_two_generic`, `kernel_b_generic`, `ea_brScale`, `ea_brNum`, `eb_brJet`, `ea_brClass`; `admitted` | as in Sections 8.4.5.1–8.4.13 |

---

### 8.4.16 The biadditive supply `restBeta`: from `BeProp` to the Frobenius-fixed class of `Gser`

**Motivation [Expository].** Theorem 8.14f (`ea_restSExpV_of`) opens with a single call, `hB (X.std v).five_le hD be hbe` (`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpVOf.lean:262`), and takes two things from it: an element $c\in W$ with $\sigma^2(c)=c$, which it hands to the `RestGc` transport `th_restGcV_of` at `:264`, and the integral-exponential statement `E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))`, which it hands to the reduction lemma `ea_reduce` at `:267` as the constant family `fun _ => hβ`. Sections 8.4.14 and 8.4.15 kept the theorem behind this call, `restBeta` (`BiadditiveSecondVariable.lean:137`), as a named input. This subsection reads its 155-line file in full, together with the two files it rests on in the `MultisetValuation/` directory (`BiadditiveFirstVariable.lean`, `IntegralExpParamOfEquivZero.lean`), and stops, by name, at the deep theorem it invokes: `Top.betaIsG` (`FinalS.lean:61–62`), the archive's classification of "series biadditive up to an integral exponential" as the class of $c\,\mathrm{Aser}-\sigma(c)\,\mathrm{Aser}'$.

Three ideas organise the file. First, there are two notions of equivalence in play. The system-level `Simeq p f g` (`FormalGroupSystem.lean:139–142`) asks that $\exp$ of the difference be $W$-integral *after* the logarithmic change of variables $X_i\mapsto\ell(X_i)$; the `G7.Simeq f g` of the theta-logarithm layer (`CyclicPowerClassOfExpEquiv.lean:22–23`) asks that $\exp(f-g)$ itself be integral. The map `inParam` carries the first to the second (Lemma 8.16a). Second, in logarithmic coordinates "additivity in a variable" is additivity along a formal group law $F$ with $\ell(F(x,y))=\ell(x)+\ell(y)$, because $\ell(F(X_1,X_2))=\ell(X_1)+\ell(X_2)$ is exactly what `inParam` does to $X_1+X_2$ (Lemma 8.16b). The law $F$ never appears in the statement of `RestBeta`; it is an auxiliary chosen inside the proof. Third, the Frobenius $\sigma$ of $W=W(\overline{\mathbb F}_p)$ enters through the conjugation symmetry `BeProp.conj`, through the Teichmüller lifts of the $(p^2-1)$-th roots of unity, and through the two congruences $\lVert p\rVert=p^{-1}$, $\lVert\sigma(a)-a^p\rVert\le p^{-1}$ that make $K_0=\mathrm{Frac}\,W$ an admissible field for `betaIsG`. The hypothesis $5\le p$ of `RestBeta` is consumed exactly once, as $2<p$.

**Exact declaration check [Lean, read].** We quote the statements that carry the argument; $K_0$ is `K0 p = FractionRing (WW p)`, $W$ is `WW p = WittVector p (AlgebraicClosure (ZMod p))`, $\sigma_W$ is `sigW p = WittVector.frobenius`, $\sigma_K$ is `sigK p`, and `wK p c` is the image of $c\in W$ in $K_0$ (`FormalGroupSystem.lean:109–118`; `DworkExponentialRestrictions.lean:13`).

- `RestBeta p` (`DworkExponentialRestrictions.lean:15–17`): $5\le p\ \to$ `DworkLemma p` $\to$ for every `be : MvPowerSeries (Fin 2) (K0 p)` with `BeProp p be`, there is $c\in W$ with $\sigma_W^2(c)=c$ and `E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))`.
- `theorem restBeta (p : ℕ) [Fact p.Prime] : RestBeta p` (`BiadditiveSecondVariable.lean:137–153`). The theorem has no hypothesis beyond primality: $5\le p$ and `DworkLemma p` are antecedents *inside* the proposition.
- `BeProp p be` (`FormalGroupSystem.lean:147–158`), four fields: `ab` (every nonzero coefficient has exponent $\ge1$ in both variables); `add1` (`Simeq p` of $\mathrm{be}(X_0+X_1,X_2)-\mathrm{be}(X_0,X_2)-\mathrm{be}(X_1,X_2)$ with $0$); `add2` (the same for $\mathrm{be}(X_0,X_1+X_2)-\mathrm{be}(X_0,X_1)-\mathrm{be}(X_0,X_2)$); `conj` (for every $\alpha\in W$ with $\sigma_W^2\alpha=\alpha$, `Simeq p` of $\mathrm{be}(\alpha X_0,X_1)$ with $\mathrm{be}(X_0,\sigma_W(\alpha)X_1)$).
- `E0 p f` (`IntegralExpRename.lean:61–63`): $f(0)=0$ and `expK f = 1 + map h` for some $h\in W[[X]]$ with $h(0)=0$. `Simeq p f g` (`FormalGroupSystem.lean:139–142`): $(f-g)(0)=0$ and `expS p (inParam p (f - g)) = 1 + map h` with the same kind of $h$. `G7.Simeq f g` (`CyclicPowerClassOfExpEquiv.lean:22–23`): $(f-g)(0)=0$ and `Integral (mvExp (f - g))`, where `Integral` means every coefficient has norm $\le1$ (`GaussJetBounds/Statement.lean:25–26`) and `mvExp f = PowerSeries.subst f (PowerSeries.exp K)` (`:28–29`).
- `IsLawOfLog p F` (`IsLawOfLog.lean:40–41`): $F(0)=0$, $F$ integral, and `cob F (lgF K p) = 0`, i.e. $\ell(F)=\ell(X_0)+\ell(X_1)$ with $\ell=$ `lgF` $=\sum_jp^{-j}T^{p^{2j}}$ (`OddLogRelation.lean:13–14`; equal to `logF p` over $K_0$ by `sx_logF_eq`). `swap2 H = H(X_1,X_0)`, `in3 f = f(X_0,X_1)` viewed in three variables, `d1 F H = H(F(X_0,X_1),X_2)-H(X_0,X_2)-H(X_1,X_2)`, `DivAB H` (coefficients with a zero exponent vanish) (`:24–36`).
- `BetaHyp p F be'` (`:89–96`): `DivAB be'`, `G7.Simeq (d1 F be') 0`, `G7.Simeq (d1 F (swap2 be')) 0`, and for every $\zeta\in K$ with $\zeta^{p^2-1}=1$, `G7.Simeq` of $\mathrm{be}'(\zeta X_0,X_1)$ with $\mathrm{be}'(X_0,\zeta^pX_1)$.
- `UnrOK K p σ` (`:13–15`): $p$ prime, $2<p$, $\lVert p\rVert=p^{-1}$, every nonzero norm is an integer power of $p$, and $\lVert\sigma(a)-a^p\rVert\le p^{-1}$ whenever $\lVert a\rVert\le1$.
- `BetaIsG` (`:98–103`): for every complete ultrametric normed field $K$ of characteristic zero with `UnrOK K p σ` and a primitive $(p^2-1)$-th root of unity, every $F$ with `IsLawOfLog p F` and every `be'` with `BetaHyp p F be'`, there is $c\in K$ with $\lVert c\rVert\le1$, $\sigma(\sigma(c))=c$ and `G7.Simeq be' (Gser p c (σ c))`. `Gser p c c' = C c * Aser - C c' * Aser'` with $\mathrm{Aser}=\sum_{i\le j}p^{-(i+j+1)}X_0^{p^{2i}}X_1^{p^{2j+1}}$ and $\mathrm{Aser}'$ the same with the variables exchanged (`OddLogRelation.lean:20–29`).

Four facts follow from the declarations and the first two lines of the proof. (a) `RestBeta` is about the *second* argument of `Gser` being $\sigma(c)$: this is not a convention; the low-degree truncation of Example 2 exhibits its mod-$p$ shadow as a necessary condition, and [§8.4.17](#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar) derives the exact relation across all degrees. (b) The proof begins `intro h5 _ be hbe` (`:138`): the `DworkLemma p` hypothesis is discarded, and `h5 : 5 ≤ p` is used once, at `:143`, as `sx_unrOK (by omega)`, whose hypothesis is `2 < p`. Nothing in this file distinguishes $p=3$ from $p\ge5$. (c) `be` lives in geometric coordinates and `Gser` in logarithmic ones; the conclusion compares `inParam p be` with `Gser`, never `be` itself. (d) Everything is over the fixed field $K_0=\mathrm{Frac}\,W(\overline{\mathbb F}_p)$; the general $K$ of `BetaIsG` is specialised, and the output $c\in K_0$ with $\lVert c\rVert\le1$ is pulled back to $W$ by the unit-ball description `sx_norm_le_one_iff`.

**Worked examples [Expository].** The support of `be` is, by `ab`, contained in the quadrant $\{(n_0,n_1):n_0,n_1\ge1\}$; we call the smallest box containing the support its rectangle. We compute the two defects of `BeProp`, and the two biadditivity defects of `BetaHyp`, for the smallest legal rectangle and for the asymmetric two-corner block of $[1,p]\times[1,p]$ that is the leading part of `Gser`.

1. **The minimal rectangle $\{(1,1)\}$: the remainder vanishes, and `conj` forces $c=0$.** Let $\mathrm{be}=cX_0X_1$ with $c\in W$.
   - *`ab`, `add1`, `add2`.* The exponent condition holds. Both additivity defects vanish identically: $c(X_0+X_1)X_2-cX_0X_2-cX_1X_2=0$ and likewise in the second variable. So `Simeq p 0 0` is needed, and it holds with $h=0$: `inParam p 0 = 0` and `expS p 0 = 1` (Lemma 8.14d(2)). This is the case in which the biadditive remainder *actually vanishes*.
   - *`conj`.* For $\zeta\in K_0$ with $\zeta^{p^2-1}=1$ the two sides are $c\zeta X_0X_1$ and $c\zeta^pX_0X_1$, with difference $aX_0X_1$, $a:=c(\zeta-\zeta^p)$. In logarithmic coordinates this is $a\,\ell(X_0)\ell(X_1)$, whose monomials are $X_0^{p^{2i}}X_1^{p^{2j}}$ with coefficients $a\,p^{-(i+j)}$. The coefficient of $(X_0X_1)^p$ in $\exp(a\,\ell(X_0)\ell(X_1))$ is $a^p/p!$: a product of $m\le p$ monomials of this shape has bidegree $(p,p)$ only if every factor is $X_0X_1$ (each other factor has an exponent $\ge p^2>p$), and then $m=p$. For $p=5$ and $a=1$ this is $1/120$ (checked by exact rational arithmetic, `example-check.log`). So `conj` needs $v_p(a)\ge1/p$, i.e. $a\in pW$. Then the coefficient of $X_0^{p^{2k+1}}X_1^p$ is $(a/p^k)^p/p!$: the $X_1$-exponent $p$ forces $p$ factors all with $X_1$-exponent $1$, and $\sum_{r=1}^pp^{2i_r}=p^{2k+1}$ forces every $i_r=k$ (reduce mod $p^2$ and induct). Its valuation is $p(v_p(a)-k)-1$, nonnegative only if $v_p(a)\ge k+1$. Letting $k$ grow, $a=0$. For $p=5$, $a=5$, $k=1$: the coefficient of $X_0^{125}X_1^5$ is $1/120$ again, of valuation $-1$ (`example-check.log`).
   - *Consequence.* Take $\zeta$ a primitive $(p^2-1)$-th root of unity, which exists in $K_0$ (Lemma 8.16e). Then $\zeta^p\neq\zeta$, since $p\not\equiv1\pmod{p^2-1}$ (for $p=5$: $5\not\equiv1\pmod{24}$). Hence $c=0$: the minimal rectangle carries no nonzero `BeProp` series, and `RestBeta` holds for it with $c=0$, $\mathrm{Gser}(0,0)=0$ and `E0 p 0`. In the language of the deep layer, $c\,\ell(X_0)\ell(X_1)$ is exactly the "$\beta\,\ell(X_0)\ell(X_1)$" direction that `LemmaTwo` (`IsLawOfLog.lean:81–87`) isolates in every biadditive series, and `conj` is the hypothesis that kills it.
   - *Boundary when `conj` is deleted.* $\mathrm{be}=X_0X_1$ satisfies `ab`, `add1`, `add2`. The conclusion of `RestBeta` fails for it: for every $c\in W$, the coefficient of $(X_0X_1)^p$ in $\exp(\ell(X_0)\ell(X_1)-\mathrm{Gser}(c,\sigma c))$ is $1/p!$, because a `Gser` monomial has one exponent $\ge p$ and the other $\ge1$, so a product containing one has bidegree $(p,p)$ only if it is a single `Gser` monomial of bidegree $(p,p)$, and there is none. So no Frobenius-fixed $c$ exists, and the theorem is sharp with respect to its fourth hypothesis.

2. **The asymmetric two-corner block of $[1,p]^2$: the leading linear-$X_2$ term is integral and nonzero, and truncated `add2` forces $c'\equiv\sigma(c)\pmod p$ as a necessary condition.** Work in logarithmic coordinates with
   $$H:=\frac{c}{p}X_0X_1^p-\frac{c'}{p}X_0^pX_1,\qquad c,c'\in W,$$
   the two lowest monomials of $\mathrm{Gser}(c,c')$ (positions $(1,p)$ and $(p,1)$, coefficients $\pm1/p$). Write $Q(X_0,X_1):=\bigl((X_0+X_1)^p-X_0^p-X_1^p\bigr)/p$, a polynomial with coefficients $\binom pk/p$, all $p$-adic units; for $p=5$, $Q=X_0^4X_1+2X_0^3X_1^2+2X_0^2X_1^3+X_0X_1^4$. Write $N:=(X_0+X_1)^{p^2}-X_0^{p^2}-X_1^{p^2}$.
   - *The group law to first order.* From $\ell(F)=\ell(X_0)+\ell(X_1)$ and $\ell(T)=T+T^{p^2}/p+\cdots$: $F=X_0+X_1-N/p+(\text{terms of degree}\ge2p^2-1)$. The correction $N/p$ is integral since $p\mid\binom{p^2}k$ for $0<k<p^2$.
   - *The conjugation symmetry holds exactly.* $H(\zeta X_0,X_1)-H(X_0,\zeta^pX_1)=\frac cp(\zeta-\zeta^{p^2})X_0X_1^p-\frac{c'}p(\zeta^p-\zeta^p)X_0^pX_1=0$ because $\zeta^{p^2}=\zeta$ (for $p=5$: $25\equiv1\pmod{24}$). This is why `Gser` is supported on exponents $p^{2i}$ in one variable and $p^{2j+1}$ in the other.
   - *The second-variable remainder, term by term.* `swap2 H` $=-\frac{c'}pX_0X_1^p+\frac cpX_0^pX_1$, and
     $$\Psi:=\mathrm{d1}\,F\,(\mathrm{swap2}\,H)=\frac cp\bigl(F^p-X_0^p-X_1^p\bigr)X_2-\frac{c'}p\bigl(F-X_0-X_1\bigr)X_2^p=c\,Q(X_0,X_1)\,X_2+\frac{c'}{p^2}N(X_0,X_1)\,X_2^p+\cdots,$$
     where the dots are of $(X_0,X_1)$-degree $\ge p^2+p-1$ in the $X_2$-block and $\ge2p^2-1$ in the $X_2^p$-block. The remainder does not vanish, nor is the full series $\Psi$ integral: its lowest homogeneous piece $c\,Q(X_0,X_1)\,X_2$ (of $(X_0,X_1)$-degree $p$) is integral with unit coefficients, whereas the $X_2$-block acquires valuation $v_p(c)-1$ at $(X_0,X_1)$-bidegree $(p^2(p-1),p^2)$ from $F^p$, and the $X_2^p$-block already has coefficients $c'\binom{p^2}k/p^2$ of valuation $v_p(c')-1$ when $p\mid k$ (for $p=5$: $\binom{25}5/25=10626/5$).
   - *Dwork's test on the low-degree truncation of the $X_2^p$-block.* The archive's `DworkMv` (`CyclicPowerClassOfExpEquiv.lean:13–20`, statement read; `Top.dworkMv` named) says $\exp\Psi$ is integral iff every coefficient of $D:=\Psi^\sigma(X^p)-p\Psi(X)$ has norm $\le p^{-1}$, where $\Psi^\sigma(X^p)$ applies $\sigma$ to coefficients and $X_i\mapsto X_i^p$. Because $\ell$ has rational coefficients, any endomorphism $\sigma$ fixes $F$ (`LawSymm`), so the *complete* $X_2^p$-coefficient of $D$ for the two-corner polynomial $H$ is
     $$[D]_{X_2^p}=\frac{\sigma(c)}{p}\bigl(F(X_0^p,X_1^p)^p-X_0^{p^2}-X_1^{p^2}\bigr)+c'\bigl(F(X_0,X_1)-X_0-X_1\bigr).$$
     Truncate $(X_0,X_1)$ to total degree $\le p^2$ (written $\mathrm{trunc}_{\le p^2}$): there $F(X_0^p,X_1^p)^p$ reduces to $(X_0^p+X_1^p)^p=X_0^{p^2}+X_1^{p^2}+p\,Q(X_0^p,X_1^p)$ and $F(X_0,X_1)-X_0-X_1$ reduces to $-N(X_0,X_1)/p$. Since $(X_0+X_1)^{p^2}=(X_0^p+X_1^p+pQ)^p\equiv(X_0^p+X_1^p)^p\pmod{p^2}$, we have $N/p\equiv Q(X_0^p,X_1^p)\pmod p$ (for $p=5$: $\binom{25}{5k}/5\equiv1,2,2,1\pmod5$ for $k=1,2,3,4$ and $\binom{25}k/5\equiv0$ for $5\nmid k$, `example-check.log`). Hence
     $$\mathrm{trunc}_{\le p^2}[D]_{X_2^p}\equiv\bigl(\sigma(c)-c'\bigr)\,Q(X_0^p,X_1^p)\pmod p.$$
     This truncated degree-$p^2$ slice passes iff $c'\equiv\sigma(c)\pmod p$, which is therefore a *necessary* condition for `add2` (and likewise $c\equiv\sigma(c')\pmod p$ for `add1`, together $c\equiv\sigma^2(c)\pmod p$), **not** a sufficient condition for the full $X_2^p$-block of $H$. Indeed, take $c=c'=1$, which satisfies the congruence: $F$ is integral and its $X_0^{p(p-1)}X_1^p$ coefficient $b=-\binom{p^2}p/p$ is a $p$-adic unit ($-10626\equiv-1\pmod5$ at $p=5$). By Frobenius modulo $p$, $[F(X_0,X_1)^p]$ at $(p^2(p-1),p^2)$ is congruent to $b^p\not\equiv0\pmod p$, so $[F(X_0^p,X_1^p)^p/p]$ at $(X_0,X_1)$-bidegree $(p^3(p-1),p^3)$ has valuation $-1$, which the integral series $F(X_0,X_1)-X_0-X_1$ cannot cancel. Even the full $X_2^p$-block of the two-corner truncation fails to be integral.
   - *Boundaries and higher `Gser` terms.* If $c'\not\equiv\sigma(c)\pmod p$, for instance $c'=c$ with $c$ the Teichmüller lift of an element of $\mathbb F_{p^2}\setminus\mathbb F_p$, the coefficient of $X_0^{(p-1)p}X_1^pX_2^p$ (for $p=5$: $X_0^{20}X_1^5X_2^5$) in $D$ is a unit, so $\exp\Psi$ already fails integrality at total degree $p^2+p$. Conversely, even when $c'=\sigma(c)$ and $\sigma^2(c)=c$ ($c\in W^\times$), the two-corner polynomial $H$ fails both at $(X_0,X_1)$-degree $p^4$ inside the $X_2^p$-block (as just shown) and on the $X_2^{p^2}$-block, which receives $-\frac{\sigma(c')}p(F(X_0^p,X_1^p)-X_0^p-X_1^p)X_2^{p^2}=\frac{\sigma(c')}{p^2}N(X_0^p,X_1^p)X_2^{p^2}+\cdots$ of valuation $-1$ when $p\mid k$. In the full series `Gser` (`OddLogRelation.lean:20–29`), $(i,j)=(0,1)$ supplies the monomials $(1,p^3)$ and $(p^3,1)$ with coefficients $+c/p^2$ and $-c'/p^2$ (whose $j\ge1$ continuation completes $X^p/p$ into $g_0(X)$ and cancels the higher-degree poles of the $X_2^1$- and $X_2^p$-blocks), while $(i,j)=(1,1)$ supplies $(p^2,p^3)$ and $(p^3,p^2)$ with coefficients $+c/p^3$ and $-c'/p^3$ ($i+j+1=3$, not $2$), whose $j\ge1$ continuation cancels the $X_2^{p^2}$-block. Both all-orders cancellations are proved in [§8.4.17](#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar) through `StepII_of` and `StepH_of`. Nothing in either example changes between $p=3$ and $p=5$; the only prime excluded by this file is $p=2$, through `UnrOK`.

**Definitions [Lean, read].**

1. *The model.* `kb p = AlgebraicClosure (ZMod p)`, `WW p`, `K0 p`, `sigW p`, `sigK p` (`FormalGroupSystem.lean:109–118`); `wK p c = algebraMap (WW p) (K0 p) c` (`DworkExponentialRestrictions.lean:13`). The norm on $K_0$ is the one of `WModel` (`WModel.nf`, a local instance in each file); the facts used are: $\lVert x\rVert\le1$ iff $x$ is the image of some $w\in W$ (`sx_norm_le_one_iff`, `PositivityConditionHolds.lean:21–23`, from `WModel.abv_le_one_iff`); $\lVert p\rVert=p^{-1}$ (`sx_norm_p`, `:32–34`, from `WModel.abv_p`); the norm is ultrametric (`sx_ultra`, `:36–38`); `(sigK p).toRingHom = WModel.sig p` (`sx_sigK_eq`, `:40–43`, by `IsLocalization.ringHom_ext`); $\lVert\sigma_K(a)-a^p\rVert\le p^{-1}$ for $\lVert a\rVert\le1$ (`sx_sig_frob`, `:45–48`, from `WModel.abv_sig`); $K_0$ is complete (`WModel.complete`, `WModel.lean:159`); $\sigma_K$ restricted to $W$ is $\sigma_W$ (`WModel.sig_coe`, `:129–131`). We read the five `PositivityConditionHolds` proofs; the `WModel` statements they rest on are cited `[Lean]`.
2. *Integrality and exponentials over $K_0$.* `Integral f` iff `IntS p f` (every coefficient is the image of a Witt vector; `sx_integral_iff`, `PositivityConditionHolds.lean:50–58`). `expS p f = mvExp f` when $f(0)=0$ (`sx_expS_eq`, `:60–`); both are the coefficientwise truncated exponential $\sum_{k\le|n|}f^k/k!$, so `E0 p f` says exactly $f(0)=0$ and $\exp f\in1+W[[X]]$. `expK` is `expS` over a general field (`InClassOfExp.lean:52`, Section 8.4.14).
3. *Logarithmic coordinates.* `inParam p f = f(ℓ(X_i))` (`FormalGroupSystem.lean:129–130`); its ring-homomorphism and constant-term properties are those of Section 8.4.14, Definitions 1; in addition `sx_inParam_X : inParam p (X i) = sx_lX p i` (`IntegralExpParamOfEquivZero.lean:41–43`) with `sx_lX p i = subst (X i) (logF p)`, and `sx_inParam_subst` (`:65–76`): if $a'_i$ satisfies $\ell(a'_i)=\mathrm{inParam}(a_i)$ for all $i$ (all with zero constant term), then $\mathrm{inParam}(f(a))=(\mathrm{inParam}f)(a')$, by composing the two substitutions in both orders (`MvPowerSeries.subst_comp_subst_apply`) and comparing the inner series variable by variable.
4. *Renaming.* `ren φ f = subst (fun k => X (φ k)) f` (`IntegralExpRename.lean:88–89`); `E0` is stable under renaming (`integralExp_rename`, `:91–107`: the exponential commutes with the substitution because the entries have zero constant term, `th_subst_expK`, and the $W$-witness is renamed by `MvPowerSeries.map_subst`). `th_ren_sub` and `th_ren_hasSubst` (`SubstitutionOfVariables.lean:157–163`) say renaming is subtractive and is a legal substitution.
5. *The operators of `BetaHyp`.* `in3`, `d1`, `swap2`, `DivAB`, `cob` as quoted above (`IsLawOfLog.lean:21–36`). The three substitution lemmas of the file (`sx_pair_hasSubst`, `sx_subst_pair`, `sx_subst_swap`, `BiadditiveSecondVariable.lean:15–35`) say: a pair $[u,v]$ with zero constant terms is a legal substitution; $(H(u,v))(b)=H(u(b),v(b))$ for a legal substitution $b$ (composition, then `fin_cases` on the two entries); and $(\mathrm{swap2}\,H)(u,v)=H(v,u)$ (compose with the pair $[X_1,X_0]$ and simplify `subst_X`).

**Lemma 8.16a (translating between the two equivalences) [Lean, read].** *For finite $\sigma$ and $f,g\in K_0[[X_\sigma]]$:*

1. *(`sx_simeq_of`, `IntegralExpParamOfEquivZero.lean:78–85`) `Simeq p f g` implies `G7.Simeq (inParam p f) (inParam p g)`.*
2. *(`integralExp_of_equiv`, `:87–104`) `G7.Simeq f g` implies `E0 p (f - g)`.*
3. *(`equiv_zero_of_integralExp`, `:106–111`) `E0 p f` implies `G7.Simeq f 0`.*
4. *(`integralExp_param_of_equiv_zero`, `:113–118`) `Simeq p f 0` implies `E0 p (inParam p f)`.*

*Proof.* (1) From `Simeq p f g`: $(f-g)(0)=0$, so $\mathrm{inParam}(f-g)$ has zero constant term (`th_inParam_const`), and `inParam` is subtractive (`th_inParam_sub`), giving the constant-term half. For the integrality half, `expS p (inParam (f-g)) = 1 + map w` is given; rewrite `expS` as `mvExp` (`sx_expS_eq`) and `Integral` as `IntS` (`sx_integral_iff`); the witness is $1+w\in W[[X]]$. (2) From `Integral (mvExp (f-g))` obtain, by `sx_integral_iff`, a $w\in W[[X]]$ with $\exp(f-g)=\mathrm{map}\,w$. The constant coefficient of $\exp(f-g)$ is $1$ (`constantCoeff_mvExp`, `LocalComponentGL.lean:267`, cited `[Lean]`), so the image of $w(0)$ is $1$ and, by injectivity of $W\to K_0$ (`IsFractionRing.injective`), $w(0)=1$. Take $h:=w-1$ (`:91–104`). (3) `E0 p f` gives $h$; the witness for `Integral (mvExp f)` is $1+h$ (`:110–111`). (4) is (2) after (1), using $\mathrm{inParam}\,0=0$ (`:115–118`). $\square$

**Lemma 8.16b (logarithmic coordinates turn addition into the group law) [Lean, read].** *Let $F$ satisfy `IsLawOfLog p F` over $K_0$, and let $u,v$ be series with zero constant term.*

1. *(`sx_log_law`, `BiadditiveFirstVariable.lean:59–74`) $\ell(F(u,v))=\ell(u)+\ell(v)$.*
2. *(`sx_law_const`, `:76–81`) $F(u,v)$ has zero constant term.*
3. *(`param_substitution_pair`, `:83–101`) If $\ell(x')=\mathrm{inParam}(x)$ and $\ell(y')=\mathrm{inParam}(y)$, all four with zero constant term, then $\mathrm{inParam}(\mathrm{be}(x,y))=(\mathrm{inParam}\,\mathrm{be})(x',y')$.*
4. *(`sx_eX`, `:103–106`) $\ell(X_i)=\mathrm{inParam}(X_i)$.*
5. *(`sx_divAB`, `:30–49`) If `BeProp p be` then `DivAB (inParam p be)`.*

*Proof.* (1) `cob F (lgF) = 0` unfolds to $\ell(F)=\ell(X_0)+\ell(X_1)$ as series in two variables (`linear_combination h0`, `:65–68`). Substitute $[u,v]$: on the left, substitution commutes with the one-variable substitution of $\ell$ because $F$ has zero constant term (`sx_subst_ps`, `IntegralExpParamOfEquivZero.lean:60–63`, a special case of `subst_comp_subst_apply`); on the right, `subst_add` and `subst_X` (`:69–74`). (2) is `MvPowerSeries.constantCoeff_subst_eq_zero` with $F(0)=0$. (3) is `sx_inParam_subst` (Definitions 3) for the two-element family $[x,y]$, $[x',y']$, with the three hypotheses checked by `fin_cases` (`:88–101`). (4) is the definition `sx_inParam_X`. (5) From `ab`, $X_i\mid\mathrm{be}$ (`MvPowerSeries.X_dvd_iff`: a coefficient with $n_i=0$ is zero, `:34–43`); `inParam` is multiplicative (`sx_inParam_mul`), $\mathrm{inParam}(X_i)=\ell(X_i)$, and $X_i\mid\ell(X_i)$ because $\ell(0)=0$ (`sx_X_dvd_lX`, `:22–28`). So $X_i\mid\mathrm{inParam}\,\mathrm{be}$ for $i=0,1$, which is `DivAB` (`:47–49`). $\square$

**Lemma 8.16c (biadditivity in the first variable: `biadditive_first_variable`) [Lean, read].** *If `IsLawOfLog p F` and `BeProp p be`, then `G7.Simeq (d1 F (inParam p be)) 0`.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveFirstVariable.lean:111–137`.

*Proof.* Write $H:=\mathrm{inParam}\,\mathrm{be}$. The key identity (`:128–133`) is
$$\mathrm{d1}\,F\,H=\mathrm{inParam}\bigl(\mathrm{be}(X_0+X_1,X_2)-\mathrm{be}(X_0,X_2)-\mathrm{be}(X_1,X_2)\bigr).$$
Indeed `inParam` is subtractive, and Lemma 8.16b(3) applies to the three terms with $(x',y')=(\mathrm{in3}\,F,X_2)$, $(X_0,X_2)$, $(X_1,X_2)$: the only nontrivial side condition is $\ell(\mathrm{in3}\,F)=\mathrm{inParam}(X_0+X_1)$, which is Lemma 8.16b(1) with $u=X_0$, $v=X_1$ (in three variables) followed by additivity of `inParam` and Lemma 8.16b(4) (`ex`, `:119–121`). The right side is `E0` by `add1` and Lemma 8.16a(4), hence `G7.Simeq` to $0$ by Lemma 8.16a(3) (`:134–137`). $\square$

**Theorem 8.16d (biadditivity in the second variable: `biadditive_second_variable`) [Lean, read].** *If `IsLawOfLog p F` and `BeProp p be`, then `G7.Simeq (d1 F (swap2 (inParam p be))) 0`.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:37–59`.

*Proof.* Write $H:=\mathrm{inParam}\,\mathrm{be}$, in two variables. The target is
$$\mathrm{d1}\,F\,(\mathrm{swap2}\,H)=(\mathrm{swap2}\,H)(F(X_0,X_1),X_2)-(\mathrm{swap2}\,H)(X_0,X_2)-(\mathrm{swap2}\,H)(X_1,X_2)=H(X_2,F(X_0,X_1))-H(X_2,X_0)-H(X_2,X_1),$$
where the second equality is `sx_subst_swap` three times (`:57–58`, with the constant-term hypotheses from Lemma 8.16b(2) and `sx_cX`). The hypothesis `add2` concerns $\mathrm{be}(X_0,X_1+X_2)-\mathrm{be}(X_0,X_1)-\mathrm{be}(X_0,X_2)$, in which the spectator variable is $X_0$ and the sum sits in positions $1,2$; `d1` places the spectator in position $2$ and the group law in positions $0,1$. The proof therefore has three steps.

1. *Into logarithmic coordinates* (`:39–46`). By `add2` and Lemma 8.16a(4), `E0 p (inParam p (add2-defect))`. Rewrite the defect with `th_inParam_sub` twice and Lemma 8.16b(3) three times: for the pair $(X_0,X_1+X_2)$ take $(x',y')=(X_0,F(X_1,X_2))$, using $\ell(F(X_1,X_2))=\ell(X_1)+\ell(X_2)=\mathrm{inParam}(X_1+X_2)$ (Lemma 8.16b(1), `sx_inParam_add`, `sx_eX`, `:43`); for $(X_0,X_1)$ and $(X_0,X_2)$ take the pairs themselves. The result is
   $$h_1:\ \texttt{E0 p}\bigl(H(X_0,F(X_1,X_2))-H(X_0,X_1)-H(X_0,X_2)\bigr).$$
   Here `F(X_1,X_2)` is `subst ![X 1, X 2] F`, with zero constant term by Lemma 8.16b(2) (`sx_law_const`, `:42`).
2. *Renaming* (`:47–54`). Apply `integralExp_rename` with $\varphi=[2,0,1]:\mathrm{Fin}\,3\to\mathrm{Fin}\,3$, i.e. $X_0\mapsto X_2$, $X_1\mapsto X_0$, $X_2\mapsto X_1$. `E0` is preserved. To see what the renamed series is, distribute `ren` over the two subtractions (`th_ren_sub`), unfold `ren` to a substitution, push it inside each $H(\cdot,\cdot)$ by `sx_subst_pair` (the family $k\mapsto X_{\varphi k}$ is a legal substitution, `th_ren_hasSubst`), and evaluate `subst_X` on the variables. The inner `F(X_1,X_2)` becomes `F(X_0,X_1)` by the same `sx_subst_pair`. The result is
   $$h_2:\ \texttt{E0 p}\bigl(H(X_2,F(X_0,X_1))-H(X_2,X_0)-H(X_2,X_1)\bigr).$$
3. *Conclusion* (`:55–59`). By Lemma 8.16a(3) it suffices to show `E0` of `d1 F (swap2 H)`. Unfold `d1` and `in3`, rewrite the three `swap2` substitutions by `sx_subst_swap`, and the goal is literally $h_2$. $\square$

The formal group law enters only through $\ell(F(u,v))=\ell(u)+\ell(v)$ and $F(0)=0$; no coefficient of $F$ is ever computed, and $F$ is not part of the statement. The renaming is forced by the asymmetric conventions of `add2` and `d1`, and is the only place where `integralExp_rename` (read in Section 8.4.14) is used on the main path to `RestBeta`.

**Lemma 8.16e (Teichmüller lifts of the roots of unity: `sx_root`) [Lean, read].** *If $\zeta\in K_0$ and $\zeta^{p^2-1}=1$, there is $w\in W$ with `wK p w = ζ`, $\sigma_W^2(w)=w$ and `wK p (sigW p w) = ζ ^ p`.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:61–93`.

*Proof.* $p^2-1>0$ since $4\le p^2$ (`:63–66`). The residue field $\overline{\mathbb F}_p$ has a primitive $(p^2-1)$-th root of unity $\xi$ (`HasEnoughRootsOfUnity.exists_primitiveRoot`, `:68`; the instance for an algebraically closed field of characteristic prime to $p^2-1$ uses `neZero_cast`, `WittTeichmullerRoot.lean:12`). The Teichmüller map $x\mapsto[x]$, `WittVector.teichmuller p`, is injective because the zeroth coefficient of $[x]$ is $x$ (`teichmuller_coeff_zero`, `:69–72`), and $W\to K_0$ is injective (`IsFractionRing.injective`), so the image of $[\xi]$ in $K_0$ is a primitive $(p^2-1)$-th root of unity (`IsPrimitiveRoot.map_of_injective` twice, `:73–74`). Hence $\zeta=(\text{image of }[\xi])^k$ for some $k$ (`IsPrimitiveRoot.eq_pow_of_pow_eq_one`, `:76`). Set $w:=[\xi^k]=[\xi]^k$ (`:82`). Frobenius acts on Teichmüller lifts by $\sigma_W[x]=[x^p]=[x]^p$ (`WittVector.frobenius_eq_map_frobenius`, `map_teichmuller`, `frobenius_def`, `:77–80`). Then `wK p w = ζ` (`:83–85`); $\sigma_W^2(w)=w^{p^2}=w\cdot w^{p^2-1}=w$ since $(\xi^k)^{p^2-1}=1$ (`:81,86–90`); and `wK p (sigW p w) = ζ ^ p` (`:91–93`). $\square$

**Lemma 8.16f (the conjugation symmetry in logarithmic coordinates: `sx_conj`) [Lean, read].** *If `BeProp p be` and $\zeta\in K_0$ with $\zeta^{p^2-1}=1$, then `G7.Simeq` of $H(\zeta X_0,X_1)$ with $H(X_0,\zeta^pX_1)$, where $H=\mathrm{inParam}\,\mathrm{be}$.*
`:100–128`.

*Proof.* Take $w$ from Lemma 8.16e. `conj` at $\alpha=w$ (legal because $\sigma_W^2w=w$) gives `Simeq p` of $\mathrm{be}(\mathrm{wK}\,w\cdot X_0,X_1)$ with $\mathrm{be}(X_0,\mathrm{wK}(\sigma_Ww)\cdot X_1)$, i.e. of $\mathrm{be}(\zeta X_0,X_1)$ with $\mathrm{be}(X_0,\zeta^pX_1)$ (`h0`, `h1`, `:118–122`). Lemma 8.16a(1) turns this into `G7.Simeq` of the two `inParam` images (`:123`). Finally Lemma 8.16b(3) with $(x',y')=(\zeta X_0,X_1)$ and $(X_0,\zeta^pX_1)$: the side conditions $\ell(\zeta X_0)=\mathrm{inParam}(\zeta X_0)$ and $\ell(\zeta^pX_1)=\mathrm{inParam}(\zeta^pX_1)$ reduce, by `sx_inParam_C_mul` and `sx_inParam_X`, to $\ell(\zeta T)=\zeta\,\ell(T)$ for $\zeta^{p^2-1}=1$, which is `lgF_subst_C_mul` (`CoeffSubstLgFOfDegreeOne.lean:172`, cited `[Lean]`; it holds because every exponent of $\ell$ is a power of $p^2$ and $\zeta^{p^{2j}}=\zeta$), applied to $\zeta$ and to $\zeta^p$, which is again a $(p^2-1)$-th root of unity (`hζp`, `:106`). $\square$

**Proposition 8.16g (`sx_betaHyp`) [Lean, read].** *If `IsLawOfLog p F` and `BeProp p be`, then `BetaHyp p F (inParam p be)`* (`:130–132`). *Proof.* The four conjuncts are Lemma 8.16b(5), Lemma 8.16c, Theorem 8.16d and Lemma 8.16f. $\square$

**Lemma 8.16h (`sx_unrOK`) [Lean, read].** *If $2<p$, then `UnrOK (K0 p) p (sigK p).toRingHom`* (`:134–135`). *Proof.* The five conjuncts are `hp.out`, the hypothesis $2<p$, `sx_norm_p`, `WModel.abv_value` (every nonzero norm is an integer power of $p$; cited `[Lean]`) and `sx_sig_frob`. $\square$ This is the only place in the file where the size of $p$ matters.

**Theorem 8.16i (`restBeta`) [Lean, read].** *`RestBeta p` holds for every prime $p$.*
`src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:137–153`.

*Proof.* Introduce $5\le p$, discard `DworkLemma p`, and fix `be` with `hbe : BeProp p be` (`:138`).

1. *The field.* $K_0$ is ultrametric (`sx_ultra`) and complete (`WModel.complete`), registered as instances (`:139–140`).
2. *A law of the logarithm.* `Top.lawExists` (`FinalS.lean:43`, named: `formal_law_exists`, `CoeffSubstLgFOfDegreeOne.lean:306`) applied to $K_0$, $p$, `hp.out`, `sx_norm_p` gives $F$ with `IsLawOfLog p F` (`:141`).
3. *A primitive root.* `witt_teichmuller_root` (`WittTeichmullerRoot.lean:32`, named) at $d=2$ gives $\zeta_0\in W$ primitive of order $p^2-1$; its image in $K_0$ is primitive by `IsPrimitiveRoot.map_of_injective` (`:142,144`).
4. *The classification.* `Top.betaIsG` (`FinalS.lean:61–62`, named) at $K_0$, $\sigma_K$, `sx_unrOK (by omega)` (this is where $5\le p$ is used, as $2<p$), $\zeta_0$, $F$, $\mathrm{inParam}\,\mathrm{be}$ and Proposition 8.16g gives $c\in K_0$ with $\lVert c\rVert\le1$, $\sigma_K(\sigma_K(c))=c$ and `G7.Simeq (inParam p be) (Gser p c (σ_K c))` (`:143–144`).
5. *Back to $W$.* By `sx_norm_le_one_iff`, $c=\mathrm{wK}\,w$ for some $w\in W$ (`:145`). The identity `hs`: $\sigma_K(\mathrm{wK}\,x)=\mathrm{wK}(\sigma_Wx)$ (`:146–149`, from `sx_sigK_eq` and `WModel.sig_coe`) rewrites $\sigma_K(c)$ as $\mathrm{wK}(\sigma_Ww)$ and $\sigma_K(\sigma_K(c))$ as $\mathrm{wK}(\sigma_W^2w)$ (`:150–151`); injectivity of `wK` gives $\sigma_W^2(w)=w$ (`:152`).
6. *The exponential.* Lemma 8.16a(2) turns the `G7.Simeq` of step 4, now reading `G7.Simeq (inParam p be) (Gser p (wK p w) (wK p (sigW p w)))`, into `E0 p (inParam p be - Gser p (wK p w) (wK p (sigW p w)))` (`:153`). $\square$

**Corollary 8.16j (how `restBeta` is consumed: the $E/Y$ decomposition and the three place bounds) [Lean, read].** *In Theorem 8.14f the two outputs of `restBeta` go to two different consumers, and the three place bounds receive the same term.*

*Proof.* In `ea_restSExpV_of` (`EaRestSExpVOf.lean:260–272`), line `:262` destructures `hB (X.std v).five_le hD be hbe` as `⟨c, hc, hβ⟩`, with `hc : (sigW p)^[2] c = c` and `hβ : E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))`. The element $c$ and `hc` are the first two arguments of `hG : ea_RestGcV X` at `:264`, whose statement (`:249–258`) quantifies over `c : WW p` with `(sigW p)^[2] c = c`: the Frobenius-fixedness is what `RestGc` needs to form `Gt`/`ea_GtV` with the pair $(c,\sigma c)$ and to run the trace-dual contraction of Section 8.4.15. The witness `hβ` is passed to `ea_reduce` at `:267` as the family `fun _ => hβ` over the index set `Eidx`, i.e. one and the same `E0` for every $e$. Inside Lemma 8.14e this family produces $Y=\sum_e\mathrm{ren}_{[a_e,b_e]}(\mathrm{inParam}\,\mathrm{be}-\mathrm{Gser}(c,\sigma c))$ and the $W$-integral $w_Y$ with $\exp(-Y)=\mathrm{map}\,w_Y$: each factor $\exp(-\mathrm{ren}(\mathrm{inParam}\,\mathrm{be}-\mathrm{Gser}))$ is the renaming of $\exp(-(\mathrm{inParam}\,\mathrm{be}-\mathrm{Gser}))$, which is $W$-integral by `hβ` and Lemma 8.14d(1). Since the phase is the standard sum ($\Phi=S$, `ea_Simeq_refl`), $E=0$ and $w_E=1$, so the correction factor of Theorem 8.14f is $V'=\mathrm{map}(w_Y)(\pi\mu(\mathrm{coordZA}))$: *`RestBeta` is exactly the $W$-integrality of the $Y$-factor, and nothing else in the production of `ea_RestSU` uses `be` beyond `BeProp`.* Finally `ea_restSU X Y hG = ea_restSU_of X Y (ea_restSExpV_of X (restBeta p) (th_restGcV_of X hG))` (`FirstTheoremPlaceBound.lean:17–18`) is passed verbatim as the `hS` argument of `ea_A1U`, `ea_A2U`, `ea_BU` in `first_theorem_place_bound`, `second_lemma_place_bound`, `hecke_place_bound` (`:20–30`), so the three levels `g0v`, `gv - alEven`, `gv` of Lemma 8.5 draw on one application of `restBeta`, whose existential $c$ depends on `be` alone (the place $v$ enters the call only through the proof `(X.std v).five_le` of $5\le p$). $\square$

**Remarks [Expository].**

1. *Where $5\le p$ is used, and where it is not.* `RestBeta` carries $5\le p$ as an antecedent, and `ea_restSExpV_of` discharges it from `Std.five_le` (`FormalGroupSystem.lean:92`). Inside `restBeta` the hypothesis is used once, at `:143`, as `by omega : 2 < p`, to satisfy the second conjunct of `UnrOK`; the file would prove the same statement under $2<p$. Because `RestBeta p` carries $5\le p$ as an antecedent, `theorem restBeta` makes no substantive classification claim at $p=2$ or $p=3$; within `BiadditiveSecondVariable.lean`, excluding $p=2$ enters purely as the interface requirement $2<p$ of `UnrOK` (`IsLawOfLog.lean:14`), whereas `DworkMv` (`CyclicPowerClassOfExpEquiv.lean:13–20`) assumes only `p.Prime`. The genuine uses of $p\ge5$ on the main path are elsewhere (`RestGc`, `Std.five_le` in the frame data). Likewise `DworkLemma p` is an antecedent of `RestBeta` that this proof does not use; it is carried because `ea_RestSExpV` and `ea_RestSU` are phrased under it.
2. *Two coordinate systems, one equivalence.* `BeProp` is stated in geometric coordinates with the equivalence `Simeq p`, whose definition already contains `inParam`; `BetaHyp` and `BetaIsG` are stated in logarithmic coordinates with `G7.Simeq`. Lemma 8.16a(1) is the bridge, and Lemma 8.16b(3) is the reason the bridge is compatible with substitutions: a substitution $x\mapsto x'$ in geometric coordinates corresponds to $\ell(x')=\mathrm{inParam}(x)$. For $x=X_1+X_2$ this reads $\ell(x')=\ell(X_1)+\ell(X_2)$, which is solved by $x'=F(X_1,X_2)$. The formal group law is thus the geometric-coordinate shadow of addition in logarithmic coordinates, and `lawExists` is only needed to have a name for it.
3. *Why the second argument is $\sigma(c)$.* Example 2 shows on the degree-$p^2$ truncation of the $X_2^p$-block that `add2` for a series with leading corners $(c/p)X_0X_1^p-(c'/p)X_0^pX_1$ forces $c'\equiv\sigma(c)\pmod p$ as a necessary condition, and `add1` forces $c\equiv\sigma(c')\pmod p$. The exact statement, $c'=\sigma(c)$ and $\sigma^2(c)=c$ with $\lVert c\rVert\le1$, is what `betaIsG` returns. The archive's `FrobExprG` (`OddLogRelation.lean:51–56`) is the identity behind this: `frobVar p (Gser p c' c) - C p * Gser p c c'` is $p$ times an explicit series, so Frobenius on the variables exchanges the roles of $c$ and $c'$ up to $p$ times $c'g_0(X_0)\ell(X_1)-c\ell(X_0)g_0(X_1)$. Its proof (`frobenius_expression_g`, `TopsChoicePartA.lean:362–370`) and the assembly `BetaIsG_of` are read in [§8.4.17](#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar).
4. *What `restBeta` does and does not decide.* It does not choose $c$; `betaIsG` does, and only up to the equivalence. It does not say that $c\neq0$. Example 1 shows that for the minimal rectangle $c=0$, and that `BeProp` is then only satisfied by $\mathrm{be}=0$. The series `be` on the main path is `Y.be` of the pending data (`Pend`), supplied by the geometric construction behind `admitted` together with `BeProp p Y.be` (`ExtensionLocalCondition`, `FormalGroupSystem.lean:162–170`); which $c$ it produces is not visible from this file.
5. *What remains named.* `Top.betaIsG := BetaIsG_of zeroCondition stepI stepII stepH stepIII stepIV swapRules simeqRules` (`FinalS.lean:61–62`; `BetaIsG_of`, `NormLiftLeOne.lean:32`), together with its steps and the Dwork criterion `dworkMv`; `Top.lawExists` (`formal_law_exists`); `witt_teichmuller_root`; the `WModel` norm facts `abv_p`, `abv_value`, `abv_sig`, `abv_le_one_iff`, `sig_coe`, `complete`; `lgF_subst_C_mul`; `constantCoeff_mvExp`. Of these, `BetaIsG_of`, `StepII_of`, `StepH_of`, `StepIII`, `StepIV_of`, `FrobExprG`, and `SwapRules` are read in [§8.4.17](#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar), while the remaining declarations stay `[Lean]` with their statements read. The deep Witt-vector supply of Section 8.4.15 (`sx_dual`, `sx_mu_alt_int`, `sx_frob_sum`, `frobenius_congruence_witt`) is not touched by this subsection and keeps its status.

**Reading boundary and sources.** This subsection adds R3 `[Lean, read]` for the complete files `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:1–155` (`sx_pair_hasSubst`, `sx_subst_pair`, `sx_subst_swap`, `biadditive_second_variable`, `sx_root`, `sx_j`, `sx_rho` (unused definitions), `sx_conj`, `sx_betaHyp`, `sx_unrOK`, `restBeta`), `BiadditiveFirstVariable.lean:1–139` (`sx_lX_const`, `sx_X_dvd_lX`, `sx_divAB`, `sx_two`, `sx_log_law`, `sx_law_const`, `param_substitution_pair`, `sx_eX`, `sx_cX`, `biadditive_first_variable`), `IntegralExpParamOfEquivZero.lean:1–120` (`sx_logF_eq`, `sx_logF_const`, `sx_lX`, `sx_inParam_X`, `sx_inParam_add`, `sx_inParam_mul`, `sx_inParam_C_mul`, `sx_subst_ps`, `sx_inParam_subst`, `sx_simeq_of`, `integralExp_of_equiv`, `equiv_zero_of_integralExp`, `integralExp_param_of_equiv_zero`) and `PositivityConditionHolds.lean:17–58` (`sx_charZero`, `sx_norm_le_one_iff`, `sx_norm_le_inv_iff`, `sx_norm_p`, `sx_ultra`, `sx_sigK_eq`, `sx_sig_frob`, `sx_integral_iff`); it rereads `IntegralExpRename.lean:61–107` and `EaRestSExpVOf.lean:245–272` and `FirstTheoremPlaceBound.lean:14–32` from Section 8.4.14; and it reads as statements `RestBeta`, `RestGc` (`DworkExponentialRestrictions.lean:15–27`), `BeProp`, `Simeq`, `sub2`, `inParam`, `logF`, `IntS`, `IntR`, `expS`, `Std.five_le` (`FormalGroupSystem.lean:92,109–158`), `UnrOK`, `cob`, `swap2`, `in3`, `d1`, `DivAB`, `IsLawOfLog`, `LawExists`, `LemmaTwo`, `BetaHyp`, `BetaIsG` (`IsLawOfLog.lean:13–103`), `DworkMv`, `G7.Simeq`, `SimeqRules` (`CyclicPowerClassOfExpEquiv.lean:13–33`), `lgF`, `g0F`, `Aser`, `Aser'`, `Gser`, `frobVar`, `FrobExprG` (`OddLogRelation.lean:13–56`), `Integral`, `mvExp` (`GaussJetBounds/Statement.lean:25–29`), `WittTeichRoot` (`FormalGroupWitt/Statement.lean:172–174`), `DworkLemma` (`ArtinHasse/Statement.lean:46–49`), the `Top` wrappers `lawExists`, `betaIsG`, `dworkMv` (`FinalS.lean:33,43,61–62`), and the `WModel` statements listed in Remark 5 (`WModel.lean:42,51,97,129,142,159`). The Mathlib declarations `HasEnoughRootsOfUnity.exists_primitiveRoot`, `WittVector.teichmuller`, `WittVector.teichmuller_coeff_zero`, `WittVector.map_teichmuller`, `WittVector.frobenius_eq_map_frobenius`, `IsPrimitiveRoot.eq_pow_of_pow_eq_one`, `IsPrimitiveRoot.map_of_injective`, `IsFractionRing.injective`, `IsLocalization.ringHom_ext`, `MvPowerSeries.subst_comp_subst_apply`, `MvPowerSeries.hasSubst_of_constantCoeff_zero`, `MvPowerSeries.subst_X`, `MvPowerSeries.X_dvd_iff` and `PowerSeries.exp` are cited `[Lean]` at the pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`, with statements and file locations checked against the pinned source on 2026-11-25 (`PowerSeries.exp` lives in `RingTheory/PowerSeries/Exp.lean` at that commit). Classical background: the exponential integrality criterion is Dwork's `[Dwork1960]`, the Teichmüller representatives and Witt vectors of a perfect residue field are `[SerreLocalFields]`, Chapter II. Named inputs unchanged beyond Remark 5: `restGc` and its supply (Section 8.4.15), the Gauss bounds, `ea_brScale`, `ea_brNum`, `eb_brJet`, `ea_brClass`, `nm_restNorm_of_place`, and the geometric construction behind `admitted`. The mathematics and formal proofs are those of Levent Alpöge with Claude, archive A2, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`; the two worked examples, the reading of where $5\le p$ enters, and the consumer map are ours. Source reading and the book build are not Lean kernel verification.

| Role | Declaration | Source |
|---|---|---|
| Target and consumer | `RestBeta`; `restBeta`; `ea_restSExpV_of` (`:262,264,267`); `ea_restSU`, three place bounds | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DworkExponentialRestrictions.lean:15`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:137`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpVOf.lean:260`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/FirstTheoremPlaceBound.lean:17,20,24,28` |
| Second variable (new proof body) | `sx_pair_hasSubst`, `sx_subst_pair`, `sx_subst_swap`, `biadditive_second_variable`, `sx_root`, `sx_conj`, `sx_betaHyp`, `sx_unrOK` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:15,19,29,37,61,100,130,134` |
| First variable and coordinate change (new proof body) | `sx_X_dvd_lX`, `sx_divAB`, `sx_log_law`, `sx_law_const`, `param_substitution_pair`, `sx_eX`, `sx_cX`, `biadditive_first_variable` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveFirstVariable.lean:22,30,59,76,83,103,108,111` |
| Two equivalences (new proof body) | `sx_logF_eq`, `sx_lX`, `sx_inParam_X`, `sx_inParam_add`, `sx_inParam_mul`, `sx_inParam_C_mul`, `sx_subst_ps`, `sx_inParam_subst`, `sx_simeq_of`, `integralExp_of_equiv`, `equiv_zero_of_integralExp`, `integralExp_param_of_equiv_zero` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/IntegralExpParamOfEquivZero.lean:17,25,41,45,50,55,60,65,78,87,106,113` |
| Norm model over $K_0$ (new proof body; `WModel` statements cited) | `sx_norm_le_one_iff`, `sx_norm_p`, `sx_ultra`, `sx_sigK_eq`, `sx_sig_frob`, `sx_integral_iff`, `sx_expS_eq`; `abv_p`, `abv_le_one_iff`, `abv_value`, `sig_coe`, `abv_sig`, `complete` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PositivityConditionHolds.lean:21,32,36,40,45,50,60`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean:42,51,97,129,142,159` |
| Inherited from §8.4.14 | `E0`, `ren`, `integralExp_rename`; `th_inParam_const`, `th_inParam_sub`, `th_ren_hasSubst`, `th_ren_sub`; `ea_reduce`, `ea_Simeq_refl`, `ea_RestGcV` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/IntegralExpRename.lean:61,88,91`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/SubstitutionOfVariables.lean:134,139,157,161`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpVOf.lean:102,227,249` |
| Definitions and statements read | `kb`, `WW`, `K0`, `sigW`, `sigK`, `IntS`, `IntR`, `logF`, `inParam`, `expS`, `Simeq`, `sub2`, `BeProp`, `Std.five_le`; `wK`; `UnrOK`, `cob`, `swap2`, `in3`, `d1`, `DivAB`, `IsLawOfLog`, `LawExists`, `LemmaTwo`, `BetaHyp`, `BetaIsG`; `DworkMv`, `Simeq`, `SimeqRules`; `lgF`, `g0F`, `Aser`, `Aser'`, `Gser`, `frobVar`, `FrobExprG`; `Integral`, `mvExp`; `WittTeichRoot`; `DworkLemma` | `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:92,109–158`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DworkExponentialRestrictions.lean:13`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/IsLawOfLog.lean:13,21,24,27,30,35,40,43,81,89,98`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/CyclicPowerClassOfExpEquiv.lean:13,22,25`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/OddLogRelation.lean:13,16,20,24,28,34,51`; `src/Formalism/GaussJetBounds/Statement.lean:25,28`; `src/Formalism/FormalGroupWitt/Statement.lean:172`; `src/Formalism/ArtinHasse/Statement.lean:46` |
| Named deep inputs `[Lean]` | `Top.lawExists`, `Top.betaIsG`, `Top.dworkMv`; `BetaIsG_of`; `formal_law_exists`; `lgF_subst_C_mul`; `witt_teichmuller_root`, `neZero_cast`; `constantCoeff_mvExp` | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FinalS.lean:43,61,33`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean:32`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/CoeffSubstLgFOfDegreeOne.lean:306,172`; `src/Formalism/FormalGroupWitt/FormalGroupWittProofs/WittTeichmullerRoot.lean:32,12`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean:267` |
| Mathlib cited `[Lean]` | `HasEnoughRootsOfUnity.exists_primitiveRoot`; `WittVector.teichmuller`, `teichmuller_coeff_zero`, `map_teichmuller`; `WittVector.frobenius_eq_map_frobenius`; `IsPrimitiveRoot.eq_pow_of_pow_eq_one`, `IsPrimitiveRoot.map_of_injective`; `IsFractionRing.injective`; `IsLocalization.ringHom_ext`; `MvPowerSeries.subst_comp_subst_apply`, `hasSubst_of_constantCoeff_zero`, `subst_X`, `X_dvd_iff`; `PowerSeries.exp` | Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`: `Mathlib/RingTheory/RootsOfUnity/EnoughRootsOfUnity.lean`, `Mathlib/RingTheory/WittVector/Teichmuller.lean`, `Mathlib/RingTheory/WittVector/Frobenius.lean`, `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean`, `Mathlib/RingTheory/Localization/FractionRing.lean`, `Mathlib/RingTheory/Localization/Defs.lean`, `Mathlib/RingTheory/MvPowerSeries/Substitution.lean`, `Mathlib/RingTheory/MvPowerSeries/Basic.lean`, `Mathlib/RingTheory/PowerSeries/Exp.lean` |
| Named inputs retained `[Lean]` / `[Open]` | the steps behind `betaIsG` (`StepII_of`, `StepH_of`, `StepIII`, `StepIV_of`, `swap_rules` read in [§8.4.17](#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar); `zeroCondition`, `stepI`, `simeqRules`, `dworkMv`, `divDeriv`, `deIntegral`, `lawSymm`, `lemmaTwo` kept `[Lean]`); `restGc` and the Witt supply of §8.4.15; `kernel_a_one_generic`, `kernel_a_two_generic`, `kernel_b_generic`, `ea_brScale`, `ea_brNum`, `eb_brJet`, `ea_brClass`; `admitted` | as in Sections 8.4.5.1–8.4.15 |

---

### 8.4.17 Assembling `BetaIsG`: partial-coboundary remainders, the two-variable support test, and the Frobenius-fixed scalar

**Motivation [Expository].** Theorem 8.16i (`restBeta`, `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:137–153`) translated `BeProp p be` from geometric coordinates into `BetaHyp p F (inParam p be)` in logarithmic coordinates over $K_0=\mathrm{Frac}\,W(\overline{\mathbb F}_p)$ (via the coordinate bridge `inParam` of [§8.4.16](#8416-the-biadditive-supply-restbeta-from-beprop-to-the-frobenius-fixed-class-of-gser), cited here without re-proving) and handed the resulting logarithmic series to a single classification theorem, `Top.betaIsG` (`src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FinalS.lean:61–62`), assembled by `BetaIsG_of` (`src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean:32–56`). This subsection opens `BetaIsG_of` and expands in full its load-bearing remainder and assembly chain: `StepII_of` (`PartialCoboundaryLinear.lean:225–415`), `StepH_of` (`ConstantCoeffFirstTwoOfThree.lean:277–301`), `c_add_sigma_c_eq_zero : StepIII` (`:338–388`), `StepIV_of` (`:389–418`), the Frobenius identities `OddLogRelation`, `IdentityB`, `FrobExprG` (`TopsChoicePartA.lean:250–370`), and `swap_rules : SwapRules` (`ScalingSwapLemmas.lean:276–313`), while retaining the deeper analytic/formal-group suppliers `DworkMv`, `DivDeriv`, `DeIntegral`, `LawSymm`, `LemmaTwo` (and upstream `StepZero`, `StepI`, `SimeqRules`) as explicit conditional hypotheses.

Why is classifying a two-variable series $be$ that is biadditive *up to an integral exponential* (`G7.Simeq (d1 F be) 0` and `G7.Simeq (d1 F (swap2 be)) 0`) harder than classifying an honestly biadditive series? If $\mathrm{d1}\,F\,H=0$ and $\mathrm{d1}\,F\,(\mathrm{swap2}\,H)=0$, then $H$ is a scalar multiple $\beta\,\ell(X_0)\ell(X_1)$. Under `G7.Simeq`, however, $\exp(\mathrm{d1}\,F\,G)$ is merely integral; by Dwork's multivariable criterion (`DworkMv`), this means that the Frobenius-difference operator $\mathcal D_{p,\sigma}(\Psi):=\mathrm{frobVar}_p(\Psi^\sigma)-p\Psi$ applied to $\Psi=\mathrm{d1}\,F\,G$ has coefficients of norm at most $p^{-1}$. Dividing by $p$ introduces the normalized Dwork series $\mathrm{DeS}_{p,\sigma}(G):=p^{-1}\bigl(\mathrm{frobVar}_p(G^\sigma)-pG\bigr)$. The central obstacle is that $\mathrm{d1}\,F$ and $\mathrm{DeS}_{p,\sigma}$ *do not commute*: in the first slot of $G^\sigma$, $\mathrm{d1}\,F\,(\mathrm{frobVar}_p\,G^\sigma)$ substitutes $F(X_0,X_1)^p$, whereas $\mathrm{frobVar}_p\bigl((\mathrm{d1}\,F\,G)^\sigma\bigr)$ substitutes $F(X_0^p,X_1^p)=F(X_0,X_1)^p+p\,r$, and although the Frobenius congruence remainder $r$ is integral (`frob_congr`), $G^\sigma$ itself has unbounded $p$-adic denominators, so shifting an argument by $p\,r$ need not change $G^\sigma$ by an integral series.

Three mechanisms in the archive resolve this obstacle and assemble the Frobenius-fixed scalar:

1. *Derivative compensation and partial-coboundary remainder (`StepII_of`, `PartialCoboundaryLinear.lean:225`).* Once `StepZero` projects $be$ onto a series $G$ supported on the congruence locus `SuppOK` ($n_0,n_1\ge1$ and $n_0\equiv p n_1\pmod{p^2-1}$) and `StepI` isolates a bounded scalar $c$ for which $\partial_0 G-c\,\ell'(X_0)g_0(X_1)$ is integral (`DerivIs p G c`), subtracting $\sigma(c)\,\ell(X_0)g_0(X_1)$ from $G^\sigma$ produces an auxiliary series $\Phi$ whose $\partial_0\Phi$ *is* integral. The divided-derivative lemma (`DivDeriv`) then bounds $\Phi(F(X_0^p,X_1^p),X_2^p)-\Phi(F^p,X_2^p)$ by $p^{-1}$, while the subtracted product turns, through $g_0(T)=p^{-1}\ell(T^p)$ and $g_0(T^p)=\ell(T)-T$, into $\sigma(c)\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$ plus an integral linear-$X_2$ error controlled by `DeIntegral`.
2. *Constant-coefficient three-variable embedding and the two-variable support test (`StepH_of`, `ConstantCoeffFirstTwoOfThree.lean:277`).* Because $F(0)=0$ forces $(\mathrm{in3}\,F)(0)=0$ (`constantCoeff_first_two_of_three`), the three-variable partial coboundary $\mathrm{d1}\,F$ is well-defined and linear, sends $g_0(X_0)\ell(X_1)$ to $\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$, and annihilates $\ell(X_0)\ell(X_1)$. Subtracting *both* compensation products defines $\mathrm{Hser}_{p,\sigma}(G,\sigma c,\sigma c'):=\mathrm{DeS}_{p,\sigma}(G)-\sigma(c)\,g_0(X_0)\ell(X_1)-\sigma(c')\,\ell(X_0)g_0(X_1)$, whose partial coboundaries in both variables are integral (`StepII_of` on $G$ and on $\mathrm{swap2}\,G$). The two-variable coboundary classification (`LemmaTwo`) then writes $\mathrm{Hser}=\beta\,\ell(X_0)\ell(X_1)+R$ with $R$ integral, and `coeff_lg_lg_eq_zero` shows that $\ell(X_0)\ell(X_1)$ vanishes identically on the congruence locus $n_0\equiv p n_1\pmod{p^2-1}$ where $\mathrm{Hser}$ is supported, forcing $\mathrm{Hser}$ itself to be integral.
3. *Coupling the two scalars to $\sigma^2(c)=c$ and returning to `restBeta` (`StepIII`, `StepIV_of`, `BetaIsG_of`).* Along the infinite ray of bidegrees $(1,p^{2i+1})$ ($i\ge0$), `DerivIs p G c` bounds $G_{(1,p^{2i+1})}-c p^{-(i+1)}$ by $1$, while integrality of $\mathrm{Hser}_{p,\sigma}(G,\sigma c,\sigma c')$ bounds $-G_{(1,p^{2i+1})}-\sigma(c')p^{-(i+1)}$ by $1$ because $\mathrm{frobVar}_p(G^\sigma)$ vanishes at $n_0=1$. Adding the two bounds forces $\lVert(c+\sigma(c'))p^{-(i+1)}\rVert\le1$ for all $i\ge0$, hence $c+\sigma(c')=0$; applying the same argument to $\mathrm{swap2}\,G$ gives $c'+\sigma(c)=0$. Together these yield $\sigma^2(c)=c$ and $c'=-\sigma(c)$, identify $p\,\mathrm{Hser}_{p,\sigma}(G,\sigma c,-c)$ with $\mathcal D_{p,\sigma}\bigl(G-\mathrm{Gser}(p,c,\sigma c)\bigr)$ via `FrobExprG`, and hand $(c,\sigma^2 c=c,\mathrm{Simeq}\,be\,\mathrm{Gser}(p,c,\sigma c))$ back to `restBeta`.

**Worked examples [Expository].** As [§8.4.16](#8416-the-biadditive-supply-restbeta-from-beprop-to-the-frobenius-fixed-class-of-gser) Example 2 showed after revision, truncating `Gser` to a finite polynomial cannot certify the integrality of an infinite exponential series: high powers of $F$ create new $p^{-1}$ poles at degree $p^4$. Both calculations below therefore establish infinite-series statements algebraically across *all* bidegrees (using the exact identities of Lemma 8.17a and Theorem 8.17b together with `DivDeriv`, `DeIntegral`, and `DworkMv`), and then inspect individual bidegrees at $p=5$ only to display concrete rational cancellations.

1. **A nonzero Frobenius-twisted legal parameter ($c\in W(\mathbb F_{p^2})^\times$, $\sigma(c)\neq c$): all-orders verification and genuine cancellation on $X_2^p$ and $X_2^{p^2}$.** Let $p$ be an odd prime, work over $K_0=\mathrm{Frac}\,W(\overline{\mathbb F}_p)$ with Frobenius $\sigma=\sigma_K$, and fix a law $F$ with `IsLawOfLog p F`. For a concrete nonzero parameter that is genuinely twisted by $\sigma$, take $p=5$, choose $\bar\alpha\in\mathbb F_{25}\setminus\mathbb F_5$ with $\bar\alpha^2=2$ ($2$ is a quadratic nonresidue mod $5$), and let $c:=[\bar\alpha]\in W^\times$ be its Teichmüller lift. Because the Teichmüller map is multiplicative and $\sigma([\bar x])=[\bar x^p]$, we have $\lVert c\rVert=1$,
   $$\sigma(c)=[\bar\alpha^5]=[(\bar\alpha^2)^2\bar\alpha]=[4\bar\alpha]=[-1]\,[\bar\alpha]=-c\neq c,\qquad\sigma^2(c)=\sigma(-c)=-\sigma(c)=c.$$
   More generally, let $c,d\in W$ and consider the full two-variable series $B(c,d):=\mathrm{Gser}(p,c,d)=c\,\mathrm{Aser}-d\,\mathrm{Aser}'$.
   - *All-orders proof of `BetaHyp p F (B(c,σ c))` when $\sigma^2(c)=c$ (no finite truncation).* First, every monomial of $\mathrm{Aser}$ has bidegree $(p^{2i},p^{2j+1})$ ($0\le i\le j$), satisfying $p^{2i}\equiv1\equiv p^2\equiv p\cdot p^{2j+1}\pmod{p^2-1}$, and every monomial of $\mathrm{Aser}'$ has bidegree $(p^{2j+1},p^{2i})$, satisfying $p^{2j+1}\equiv p\equiv p\cdot p^{2i}\pmod{p^2-1}$. Thus `SuppOK p B(c,d)` and hence `DivAB B(c,d)` hold identically, and for every $\zeta\in K_0$ with $\zeta^{p^2-1}=1$ we have $\zeta^{n_0}=(\zeta^p)^{n_1}$ on the entire support, so $B(c,d)(\zeta X_0,X_1)-B(c,d)(X_0,\zeta^p X_1)=0$ identically (`Simeq` holds by reflexivity). Next set $G_2:=\mathrm{swap2}\,B(c,\sigma c)=c\,\mathrm{Aser}'-\sigma(c)\,\mathrm{Aser}=\mathrm{Gser}(p,-\sigma c,-c)$ and $\Psi:=\mathrm{d1}\,F\,G_2$. Since $\sigma^2(c)=c$, we have $G_2^\sigma=\mathrm{Gser}(p,-c,-\sigma c)$, and `FrobExprG` (Lemma 8.17a(2)) gives the exact all-orders identity
     $$\mathrm{DeS}_{p,\sigma}(G_2)=-c\,g_0(X_0)\ell(X_1)+\sigma(c)\,\ell(X_0)g_0(X_1),$$
     so $\mathrm{d1}\,F\,(\mathrm{DeS}_{p,\sigma}\,G_2)=-c\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$ because $\mathrm{cob}_F(\ell)=0$. Substituting this into the exact ring identity `key` of Theorem 8.17b (Step 5 below, applied to $G_2$ with scalar $c_2=-\sigma(c)$, so $\sigma(c_2)=-c$) cancels $\mathrm{d1}\,F\,(\mathrm{DeS}_{p,\sigma}\,G_2)-\sigma(c_2)\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$ identically and leaves, across *all* three-variable monomials at once,
     $$\mathcal D_{p,\sigma}(\Psi)=\Psi^\sigma(X^p)-p\Psi(X)=-p c\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,X_2+\Bigl(\Phi_2\bigl(F(X_0^p,X_1^p),X_2^p\bigr)-\Phi_2\bigl(F(X_0,X_1)^p,X_2^p\bigr)\Bigr),$$
     where $\Phi_2:=G_2^\sigma+c\,\ell(X_0)g_0(X_1)$. Using $\ell(X_0)g_0(X_1)=\sum_{i,j\ge0}p^{-(i+j+1)}X_0^{p^{2i}}X_1^{p^{2j+1}}$ to subtract the $i\le j$ triangle $\mathrm{Aser}$, only the strict lower triangle $i>j$ survives:
     $$\Phi_2(X_0,X_1)=c\sum_{i>j\ge0}p^{-(i+j+1)}X_0^{p^{2i}}X_1^{p^{2j+1}}+\sigma(c)\sum_{0\le i\le j}p^{-(i+j+1)}X_0^{p^{2j+1}}X_1^{p^{2i}}.$$
     Differentiating term by term with respect to $X_0$ multiplies the two coefficients by $p^{2i}$ and $p^{2j+1}$, giving
     $$\partial_0\Phi_2(X_0,X_1)=c\sum_{i>j\ge0}p^{i-j-1}X_0^{p^{2i}-1}X_1^{p^{2j+1}}+\sigma(c)\sum_{0\le i\le j}p^{j-i}X_0^{p^{2j+1}-1}X_1^{p^{2i}}.$$
     Because $i>j\implies i-j-1\ge0$ and $i\le j\implies j-i\ge0$, *every* coefficient of $\partial_0\Phi_2$ has norm $\le1$! Writing $F(X_0^p,X_1^p)=F(X_0,X_1)^p+p\,r$ with $r$ integral (Lemma 8.17a(4), using $F^\sigma=F$ from `LawSymm`), `DivDeriv` bounds every coefficient of the $\Phi_2$-difference by $p^{-1}$, while `DeIntegral` bounds $-p c\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,X_2$ by $p^{-1}$. Hence `DworkMv` proves `Integral (mvExp Ψ)`, i.e. `Simeq (d1 F (swap2 B(c,σ c))) 0` across all degrees, and applying the same argument to $(-d,-c)=(-\sigma c,-c)$ proves `Simeq (d1 F B(c,σ c)) 0`.
   - *Exact all-orders cancellation on the $X_2^p$-block.* Keep $c,d\in W$ general in $G_2=\mathrm{swap2}\,B(c,d)=c\,\mathrm{Aser}'-d\,\mathrm{Aser}$ to see how both relations $d=\sigma(c)$ and $c=\sigma(d)$ emerge. The $X_1^1$- and $X_1^p$-slices of $G_2$ are $[G_2]_{X_1^1}=c\sum_{j\ge0}p^{-(j+1)}X_0^{p^{2j+1}}=c\,g_0(X_0)$ ($i=0$, all $j\ge0$) and $[G_2]_{X_1^p}=-\frac dp X_0$ ($i=j=0$). Therefore $[\Psi]_{X_2^1}=c\,\mathrm{cob}_F(g_0)(X_0,X_1)$ and $[\Psi]_{X_2^p}=-\frac dp\bigl(F(X_0,X_1)-X_0-X_1\bigr)$, so the complete $X_2^p$-coefficient of $\mathcal D_{p,\sigma}(\Psi)$ is
     $$\bigl[\mathcal D_{p,\sigma}(\Psi)\bigr]_{X_2^p}=\sigma(c)\,\mathrm{cob}_F(g_0)(X_0^p,X_1^p)+d\bigl(F(X_0,X_1)-X_0-X_1\bigr).$$
     By Lemma 8.17a(1) ($g_0(T^p)=\ell(T)-T$) and $\mathrm{cob}_F(\ell)=0$, we have $g_0(F^p)-g_0(X_0^p)-g_0(X_1^p)=-(F-X_0-X_1)$, hence across *all* $(X_0,X_1)$-bidegrees simultaneously:
     $$\bigl[\mathcal D_{p,\sigma}(\Psi)\bigr]_{X_2^p}=\bigl(d-\sigma(c)\bigr)\bigl(F(X_0,X_1)-X_0-X_1\bigr)+\sigma(c)\Bigl(g_0\bigl(F(X_0^p,X_1^p)\bigr)-g_0\bigl(F(X_0,X_1)^p\bigr)\Bigr).$$
     Since $g_0'(T)=\sum_{j\ge0}p^j T^{p^{2j+1}-1}$ has integral coefficients, `DivDeriv` bounds the second term by $p^{-1}$ in every bidegree; when $d=\sigma(c)$ (so $d=-c$ for $c=[\bar\alpha]$ at $p=5$), the first term vanishes identically! We also see explicitly what cured the degree-$p^4$ pole of [§8.4.16](#8416-the-biadditive-supply-restbeta-from-beprop-to-the-frobenius-fixed-class-of-gser) Example 2: at $p=5$ and $(X_0,X_1)$-bidegree $(500,125)$, the $j=0$ corner $\frac{\sigma(c)}5 F(X_0^5,X_1^5)^5$ has coefficient $\frac{\sigma(c)}5(-456{,}399{,}286{,}548{,}026{,}668{,}640{,}494{,}178{,}126)$ of $5$-adic valuation $-1$, and the $j=1$ term $\frac{c}{25}X_0^{125}X_1$ ($i=0,j=1$ of $c\,\mathrm{Aser}'$) supplies $+\frac{\sigma(c)}{25}\binom{125}{25}$ in $\Psi^\sigma(X^5)$, summing in $\sigma(c)\,\mathrm{cob}_F(g_0)(X_0^5,X_1^5)$ to the exact integer $-91{,}274{,}655{,}115{,}943{,}794{,}520{,}400{,}599{,}125\,\sigma(c)$ of valuation $v_5=3\ge0$ (`example-check.log`), before $+d\,[F]_{500,125}$ brings the total valuation above $1$.
   - *Exact all-orders cancellation on the $X_2^{p^2}$-block.* In $G_2=c\,\mathrm{Aser}'-d\,\mathrm{Aser}$, the $X_1^{p^2}$-slice comes from $i=1$, $j\ge1$ of $c\,\mathrm{Aser}'$:
     $$[G_2]_{X_1^{p^2}}=c\sum_{j\ge1}p^{-(j+2)}X_0^{p^{2j+1}}=\frac cp\Bigl(g_0(X_0)-\frac1p X_0^p\Bigr),$$
     whose leading monomial ($i=j=1$) is $+\frac{c}{p^3}X_0^{p^3}X_1^{p^2}$ (denominator $p^3$, not $p^2$). Pairing the Frobenius image of $[\Psi]_{X_2^p}$ against $-p\,[\Psi]_{X_2^{p^2}}$ gives
     $$\bigl[\mathcal D_{p,\sigma}(\Psi)\bigr]_{X_2^{p^2}}=-\frac{\sigma(d)}p\bigl(F(X_0^p,X_1^p)-X_0^p-X_1^p\bigr)-c\,\mathrm{cob}_F(g_0)(X_0,X_1)+\frac cp\bigl(F(X_0,X_1)^p-X_0^p-X_1^p\bigr).$$
     Now apply the `StepII_of` coboundary identity (`hδ`, Step 4 of Theorem 8.17b below): writing $\ell(T)=T+p\,h_1(T)$ with $h_1(T):=\sum_{i\ge1}p^{-(i+1)}T^{p^{2i}}$, we have
     $$\mathrm{cob}_F(g_0)(X_0,X_1)=\frac1p\Bigl(\ell\bigl(F(X_0,X_1)^p\bigr)-\ell\bigl(F(X_0^p,X_1^p)\bigr)\Bigr)=\frac1p\bigl(F(X_0,X_1)^p-F(X_0^p,X_1^p)\bigr)-\Bigl(h_1\bigl(F(X_0^p,X_1^p)\bigr)-h_1\bigl(F(X_0,X_1)^p\bigr)\Bigr).$$
     Substituting this into $[\mathcal D_{p,\sigma}(\Psi)]_{X_2^{p^2}}$ cancels $\frac cp F(X_0,X_1)^p$ identically and yields, across *all* $(X_0,X_1)$-bidegrees:
     $$\bigl[\mathcal D_{p,\sigma}(\Psi)\bigr]_{X_2^{p^2}}=\frac{c-\sigma(d)}p\bigl(F(X_0^p,X_1^p)-X_0^p-X_1^p\bigr)+c\Bigl(h_1\bigl(F(X_0^p,X_1^p)\bigr)-h_1\bigl(F(X_0,X_1)^p\bigr)\Bigr).$$
     Because $h_1'(T)=\sum_{i\ge1}p^{i-1}T^{p^{2i}-1}\in\mathbb Z[[T]]$ has integral coefficients, `DivDeriv` bounds the second term by $p^{-1}$ everywhere! For the legal twisted choice $d=\sigma(c)$ with $\sigma^2(c)=c$ (at $p=5$, $c=[\bar\alpha]$: $d=-c$ and $\sigma(d)=\sigma(-c)=c$), the numerator $c-\sigma(d)=c-\sigma^2(c)$ vanishes identically, so the entire infinite $X_2^{p^2}$-block has norm $\le p^{-1}$. At $p=5$ and $X_0^{100}X_1^{25}X_2^{25}$, for instance, $-\frac{\sigma(d)}5(F(X_0^5,X_1^5)-X_0^5-X_1^5)$ contributes $+\frac{10626}5\sigma(d)$ ($v_5=-1$) and the $(i,j)=(1,1)$ monomial $+\frac{c}{125}X_0^{125}X_1^{25}$ contributes $-\frac{\binom{125}{25}}{25}c=-\frac{26{,}010{,}968{,}307{,}696{,}038{,}491{,}182{,}501}5 c$ ($v_5=-1$); at $\sigma(d)=c$ their sum is $-5{,}202{,}193{,}661{,}539{,}207{,}698{,}234{,}375\,c$, an integer of $5$-adic valuation $v_5=6\ge1$ (`example-check.log`). Conversely, if $c=[\bar\gamma]$ with $\bar\gamma\in\mathbb F_{p^3}\setminus\mathbb F_p$ and $d=\sigma(c)$, then the *entire* infinite $X_2^p$-block still passes ($d-\sigma(c)=0$), whereas $\lVert c-\sigma^2(c)\rVert=1$ gives $[\mathcal D_{p,\sigma}(\Psi)]_{X_2^{p^2}}$ norm $p>1$ (valuation $-1$) at $X_0^{p^2(p-1)}X_1^{p^2}X_2^{p^2}$, showing directly why $X_2^{p^2}$ enforces $\sigma^2(c)=c$. Finally, running `BetaIsG_of` on $B(c,\sigma c)$ recovers `StepI` scalars $c$ on $B$ and $c'=-\sigma(c)$ on $\mathrm{swap2}\,B$ ($=+c$ for $c=[\bar\alpha]$ at $p=5$), `StepIII` relations $c+\sigma(c')=0$ and $c'+\sigma(c)=0$, and $\mathrm{Hser}_{p,\sigma}(B,\sigma c,-c)=0$.

2. **Deleting one classification antecedent (dropping second-variable biadditivity `Simeq (d1 F (swap2 be)) 0`): disjoint supports on $X_2^p$ and $X_2^{p^2}$ and non-existence of $c$.** Fix $c_0\in W^\times$ ($\lVert c_0\rVert=1$) and set
   $$be_{\mathrm{one}}:=\frac{c_0}p\,\ell(X_0)\,X_1^p=\sum_{i\ge0}\frac{c_0}{p^{i+1}}X_0^{p^{2i}}X_1^p.$$
   - *Every other antecedent of `BetaIsG` holds across all degrees.* Each nonzero coefficient sits at $(n_0,n_1)=(p^{2i},p)$ with $n_0,n_1\ge1$ and $n_0\equiv1\equiv p^2=p n_1\pmod{p^2-1}$, so `SuppOK p be_one` and `DivAB be_one` hold. For $\zeta\in K_0$ with $\zeta^{p^2-1}=1$, $\ell(\zeta X_0)=\zeta\,\ell(X_0)$ and $(\zeta^p X_1)^p=\zeta^{p^2}X_1^p=\zeta X_1^p$, so $be_{\mathrm{one}}(\zeta X_0,X_1)=be_{\mathrm{one}}(X_0,\zeta^p X_1)$ identically (`conj` holds). And by Lemma 8.17c(1) (`partial_coboundary_product`),
     $$\mathrm{d1}\,F\,be_{\mathrm{one}}=\frac{c_0}p\,\mathrm{in3}\bigl(\mathrm{cob}_F(\ell)\bigr)\,X_2^p=0$$
     identically because $\mathrm{cob}_F(\ell)=0$, so $\exp(\mathrm{d1}\,F\,be_{\mathrm{one}})=1$ is integral (`Simeq (d1 F be_one) 0` holds without truncation). Only the third conjunct `Simeq (d1 F (swap2 be_one)) 0` of `BetaHyp` has been deleted.
   - *Zero cancellation on $X_2^p$ and $X_2^{p^2}$ in the deleted variable, and where `StepH` breaks.* Here $\mathrm{swap2}\,be_{\mathrm{one}}=\frac{c_0}p X_0^p\,\ell(X_1)$, so
     $$\Psi_{\mathrm{one}}:=\mathrm{d1}\,F\,(\mathrm{swap2}\,be_{\mathrm{one}})=\frac{c_0}p\bigl(F(X_0,X_1)^p-X_0^p-X_1^p\bigr)\,\ell(X_2)=\sum_{i\ge0}\frac{c_0}{p^{i+1}}\bigl(F^p-X_0^p-X_1^p\bigr)\,X_2^{p^{2i}}.$$
     In $\mathcal D_{p,\sigma}(\Psi_{\mathrm{one}})=\Psi_{\mathrm{one}}^\sigma(X^p)-p\Psi_{\mathrm{one}}(X)$, the first term $\Psi_{\mathrm{one}}^\sigma(X^p)$ is supported exclusively on odd powers $X_2^{p^{2i+1}}$ while $-p\Psi_{\mathrm{one}}(X)$ is supported exclusively on even powers $X_2^{p^{2i}}$. Their supports are *disjoint*, so neither $X_2^p$ nor $X_2^{p^2}$ receives a cancelling partner:
     - at $X_2^p$ ($i=0$ of $\Psi_{\mathrm{one}}^\sigma(X^p)$), $[\mathcal D_{p,\sigma}(\Psi_{\mathrm{one}})]_{X_2^p}=\frac{\sigma(c_0)}p\bigl(F(X_0^p,X_1^p)^p-X_0^{p^2}-X_1^{p^2}\bigr)$ has coefficient $\sigma(c_0)$ of norm $1>p^{-1}$ at $X_0^{p(p-1)}X_1^p$ (since $\binom p1/p=1$) and norm $p>1$ (valuation $-1$) at $X_0^{p^3(p-1)}X_1^{p^3}$;
     - at $X_2^{p^2}$ ($i=1$ of $-p\Psi_{\mathrm{one}}(X)$), $[\mathcal D_{p,\sigma}(\Psi_{\mathrm{one}})]_{X_2^{p^2}}=-\frac{c_0}p\bigl(F(X_0,X_1)^p-X_0^p-X_1^p\bigr)$ has coefficient $-c_0$ of norm $1>p^{-1}$ at $X_0^{p-1}X_1$ and norm $p>1$ (valuation $-1$) at $X_0^{p^2(p-1)}X_1^{p^2}$.
     Inside the classification chain, $\mathrm{DeS}_{p,\sigma}(be_{\mathrm{one}})=\sigma(c_0)\,g_0(X_0)X_1^{p^2}-\frac{c_0}p\ell(X_0)X_1^p$, so for any bounded $\gamma,\gamma'\in K_0$ with $\lVert\gamma'\rVert\le1$, $\mathrm{Hser}_{p,\sigma}(be_{\mathrm{one}},\gamma,\gamma')$ has coefficient $-\frac{c_0+\gamma'}p$ at $(1,p)$ and $-\frac{\gamma'}{p^2}$ at $(1,p^3)$: bounding the first by $1$ forces $\lVert c_0+\gamma'\rVert\le p^{-1}$, hence $\lVert\gamma'\rVert=\lVert c_0\rVert=1$, which gives the $(1,p^3)$-coefficient norm $p^2>1$, so `StepH` fails.
   - *Failure of the conclusion of `BetaIsG` for every $c$ (proved without truncation or `DworkMv`).* Suppose $c\in K_0$ satisfies $\lVert c\rVert\le1$, $\sigma^2(c)=c$, and `Integral (mvExp Δ)` for $\Delta:=be_{\mathrm{one}}-\mathrm{Gser}(p,c,\sigma c)$. Every nonzero monomial of $\Delta$ has $X_1$-exponent at least $1$, so in $\exp(\Delta)=\sum_{k\ge0}\Delta^k/k!$ any monomial with $X_1$-exponent $1$ receives a nonzero contribution only from $k=1$. At every bidegree $(p^{2j+1},1)$ ($j\ge0$), $be_{\mathrm{one}}$ has coefficient $0$ (its $X_1$-exponent is $p>1$), so $\mathrm{coeff}_{(p^{2j+1},1)}(\exp\Delta)=\mathrm{coeff}_{(p^{2j+1},1)}(-\mathrm{Gser}(p,c,\sigma c))=\sigma(c)\,p^{-(j+1)}$. Integrality at all $j\ge0$ gives $\lVert\sigma(c)\,p^{-(j+1)}\rVert\le1$ for every $j\ge0$, hence $\sigma(c)=0$ (`eq_zero_of_div`, Proposition 8.17e(1)) and therefore $c=\sigma^2(c)=0$. Substituting $c=0$ leaves $\Delta=be_{\mathrm{one}}$, and since every monomial of $be_{\mathrm{one}}$ has total degree $\ge p+1$, the $(1,p)$-coefficient of $\exp(be_{\mathrm{one}})$ comes solely from $k=1$ and equals $c_0/p$, of norm $p>1$. Thus no $c$ exists, and `BetaIsG` is sharp with respect to second-variable biadditivity (and, by applying $\mathrm{swap2}$, with respect to first-variable biadditivity as well).

**Definitions and exact declaration check [Lean, read].** Throughout this subsection $K$ is a field (or ultrametric normed field of characteristic zero) in namespace `Formalism.InvariantFactorPaths.G7`. Note the conjugation convention: $\sigma:K\to K$ is a ring endomorphism satisfying the Frobenius-lift congruence $\lVert\sigma(a)-a^p\rVert\le p^{-1}$ on the closed unit ball (`UnrOK`), instantiated in `restBeta` at $K_0=\mathrm{Frac}\,W(\overline{\mathbb F}_p)$ by the arithmetic Witt Frobenius $\sigma_K$ ($\sigma_W([x])=[x^p]$); on the $\sigma^2$-fixed quadratic subextension, $\sigma$ is the nontrivial Galois involution playing the local $p$-adic role of quadratic conjugation, never archimedean complex conjugation.

1. *Auxiliary series and operators (`OddLogRelation.lean:13–36`; `FirstDeriv.lean:17–36`; `LocalComponentGL.lean:22`).*
   - `at1 x f = PowerSeries.subst (X x) f` embeds a one-variable power series $f\in K[[T]]$ in variable $X_x$; `frobVar p f = MvPowerSeries.subst (fun i => X i ^ p) f` substitutes $X_i\mapsto X_i^p$ without twisting coefficients.
   - `lgF K p` is $\ell(T)=\sum_{j\ge0}p^{-j}T^{p^{2j}}$ and `g0F K p` is $g_0(T)=\sum_{j\ge0}p^{-(j+1)}T^{p^{2j+1}}$; `Aser K p` is $\sum_{0\le i\le j}p^{-(i+j+1)}X_0^{p^{2i}}X_1^{p^{2j+1}}$, `Aser' K p` swaps the two exponents, and `Gser p c c' = C c * Aser K p - C c' * Aser' K p`.
   - `SuppOK p G`: for every $n\in\mathbb N^2$ with $\mathrm{coeff}_n(G)\neq0$, $1\le n_0$, $1\le n_1$, and $n_0\equiv p n_1\pmod{p^2-1}$.
   - `fLin G`: the one-variable series $\sum_{j\ge0}\mathrm{coeff}_{(1,j)}(G)\,T^j$.
   - `DeS p σ G = C p⁻¹ * (frobVar p (map σ G) - C p * G)` and
     $$\mathrm{Hser}_{p,\sigma}(G,\gamma,\gamma')=\mathrm{DeS}_{p,\sigma}(G)-\gamma\,g_0(X_0)\ell(X_1)-\gamma'\,\ell(X_0)g_0(X_1)$$
     (`Hser p σ G γ γ'`, `:28–31`, written with `at1 0` and `at1 1`).
   - `DerivIs p G c`: `Integral (pderiv 0 G - C c * (at1 0 (derivative (lgF K p)) * at1 1 (g0F K p)))`, i.e. $\partial_0 G-c\,\ell'(X_0)g_0(X_1)$ has all coefficients of norm $\le1$. `Bd c f` means $\forall n,\ \lVert\mathrm{coeff}_n(f)\rVert\le c$ (`Integral f` is `Bd 1 f`).
2. *Named upstream hypotheses retained at `[Lean]` (`CyclicPowerClassOfExpEquiv.lean:13–33`; `IsLawOfLog.lean:50–87`; `FirstDeriv.lean:39–86`).*
   - `DworkMv`: for finite $\iota$, $p$ prime, $\lVert p\rVert=p^{-1}$, $\lVert\sigma(a)-a^p\rVert\le p^{-1}$ on $\lVert a\rVert\le1$, and $\Psi\in K[[X_\iota]]$ with $\Psi(0)=0$, `Integral (mvExp Ψ)` holds iff `Bd p⁻¹ (frobVar p (map σ Ψ) - C p * Ψ)`.
   - `DivDeriv`: for finite $\iota$, $p$ prime, $\lVert p\rVert=p^{-1}$, slot $x\in\iota$, $\Phi\in K[[X_\iota]]$ with `Integral (pderiv x Φ)`, zero-constant-term integral series $\varphi_i,Y\in K[[X_\kappa]]$, updating $\varphi_x$ to $\varphi_x+p Y$ satisfies `Bd p⁻¹ (subst (update φ x (φ x + C p * Y)) Φ - subst φ Φ)`.
   - `DeIntegral`: under the same norm and Frobenius-lift hypotheses on $(K,p,\sigma)$, `IsLawOfLog p F` implies `Integral (cob F (g0F K p))`.
   - `LawSymm`: for $p$ prime, $\lVert p\rVert=p^{-1}$, and `IsLawOfLog p F`, (i) `map σ F = F` for *every* ring endomorphism $\sigma:K\to K$, (ii) $F(\zeta X_0,\zeta X_1)=\zeta F(X_0,X_1)$ for $\zeta^{p^2-1}=1$, (iii) linear coefficients of $F$ equal $1$, and (iv) $F(X_0,0)=X_0$.
   - `LemmaTwo` (built from `LemmaOne`): over a complete ultrametric field $K$ of characteristic zero with `UnrOK K p σ` and `IsLawOfLog p F`, if `DivAB H`, `Integral (d1 F H)`, and `Integral (d1 F (swap2 H))`, then $H=\beta\,\ell(X_0)\ell(X_1)+R$ for some $\beta\in K$ and integral $R$.
   - `StepZero`, `StepI`, `SimeqRules`: `StepZero` averages $be$ over $(X_0,X_1)\mapsto(\zeta^k X_0,\zeta^{-pk}X_1)$ ($0\le k<p^2-1$) to produce $G$ with `SuppOK p G`, `Simeq G be`, `Simeq (d1 F G) 0`, and `Simeq (d1 F (swap2 G)) 0`; `StepI` extracts $c\in K$ with $\lVert c\rVert\le1$ and `DerivIs p G c` from `SuppOK p G` and the two `Simeq` conditions; `SimeqRules` states reflexivity, symmetry, transitivity, additivity, and integral substitution invariance of `G7.Simeq`.
3. *Load-bearing propositions proved here (`[Lean, read]`).* `OddLogRelation`, `IdentityB`, `FrobExprG` (`OddLogRelation.lean:37–56`), `SwapRules` (`FirstDeriv.lean:114–120`), `StepII` (`:88–95`), `StepH` (`:97–106`), `StepIII` (`:108–112`), `StepIV` (`:121–125`), and `BetaIsG` (`IsLawOfLog.lean:98–103`), wired in `Top.betaIsG := BetaIsG_of zeroCondition stepI stepII stepH stepIII stepIV swapRules simeqRules` (`FinalS.lean:61–62`). Three interface facts stand out in the source: (a) `[CompleteSpace K]` is absent from `StepII`, `StepIII`, and `StepIV`, entering `BetaIsG_of` solely through `StepI` and `StepH` (where `LemmaOne`/`LemmaTwo` take limits in $K$); (b) `StepH_of` accepts `(_hL : LawSymm)` at `ConstantCoeffFirstTwoOfThree.lean:277` and never uses it, and `StepII_of` similarly discards `DivAB G` at `PartialCoboundaryLinear.lean:226` while `StepIII` discards $\lVert c\rVert\le1,\lVert c'\rVert\le1$ at `ConstantCoeffFirstTwoOfThree.lean:339`; (c) every proof body expanded in this subsection weakens $2<p$ from `UnrOK` immediately to $2\le p$ or `p.Prime`.

**Lemma 8.17a (Frobenius identities of `lgF`, `g0F`, `Gser`, `swap2`, and integral series) [Lean, read].**

1. *(`g_zero_relation_holds : OddLogRelation`, `TopsChoicePartA.lean:250–306`; substituted forms `subst_g_zero_eq_log`, `subst_pow_g_zero`, `PartialCoboundaryLinear.lean:106–125`) For $2\le p$ and $(p:K)\neq0$, $g_0(T)=p^{-1}\ell(T^p)$ and $g_0(T^p)=\ell(T)-T$; hence for every $a\in K[[X_\iota]]$ with $a(0)=0$, $g_0(a)=p^{-1}\ell(a^p)$ and $g_0(a^p)=\ell(a)-a$.*
2. *(`identity_b : IdentityB` and `frobenius_expression_g : FrobExprG`, `TopsChoicePartA.lean:307–370`) For $2\le p$, $(p:K)\neq0$, and $c,c'\in K$,*
   $$\begin{aligned}
   \mathrm{frobVar}_p(\mathrm{Aser})&=p\bigl(g_0(X_0)\ell(X_1)-\mathrm{Aser}'\bigr), &
   \mathrm{frobVar}_p(\mathrm{Aser}')&=p\bigl(\ell(X_0)g_0(X_1)-\mathrm{Aser}\bigr),\\
   \mathrm{frobVar}_p\bigl(\mathrm{Gser}(p,c',c)\bigr)-p\,\mathrm{Gser}(p,c,c')&=p\bigl(c'\,g_0(X_0)\ell(X_1)-c\,\ell(X_0)g_0(X_1)\bigr).
   \end{aligned}$$
3. *(`swap_rules : SwapRules`, `ScalingSwapLemmas.lean:276–313`) For $2\le p$, $\mathrm{swap2}$ is an involution, preserves `SuppOK p`, `DivAB`, and `Integral`, commutes with $\mathrm{DeS}_{p,\sigma}$, and satisfies $\mathrm{Hser}_{p,\sigma}(\mathrm{swap2}\,G,\gamma',\gamma)=\mathrm{swap2}\bigl(\mathrm{Hser}_{p,\sigma}(G,\gamma,\gamma')\bigr)$.*
4. *(`frob_congr`, `LocalComponentGL.lean:186–260`, conditional on the binomial identity `add_pow_prime_eq` and `Low` degree-truncation lemmas `[Lean]`) For finite $\iota$, $p$ prime, $\lVert p\rVert=p^{-1}$, $\lVert\sigma(a)-a^p\rVert\le p^{-1}$ on $\lVert a\rVert\le1$, and any integral $f\in K[[X_\iota]]$, `Bd p⁻¹ (f ^ p - frobVar p (map σ f))`.*

*Proof.* (1) Rewrite $T\mapsto T^p$ as `PowerSeries.expand p` (`:253`). At $n=p(p^2)^j$, $\mathrm{coeff}_n(g_0)=p^{-(j+1)}=p^{-1}\mathrm{coeff}_{(p^2)^j}(\ell)$ by uniqueness of exponents (`powq_inj`, `ppowq_inj`, `:109–169,257–260`), and off that set both sides vanish (`:261–273`). For the second identity (`:274–305`), at $n=(p^2)^0=1$ we have $p\nmid 1$, so $\mathrm{coeff}_1(g_0(T^p))=0=1-1=\mathrm{coeff}_1(\ell-T)$; at $n=(p^2)^{k+1}=p\cdot p(p^2)^k$, $\mathrm{coeff}_n(g_0(T^p))=\mathrm{coeff}_{p(p^2)^k}(g_0)=p^{-(k+1)}=\mathrm{coeff}_n(\ell-T)$; elsewhere both vanish. Substituting $a$ (`subst_comp_subst_apply` with `HasSubst.X_pow`, `PartialCoboundaryLinear.lean:110–124`) gives the multivariable forms.

(2) Fix $x\neq y$ in $\mathrm{Fin}\,2$ (`frobVar_AA_eq`, `TopsChoicePartA.lean:307–354`). A bidegree $n$ can appear on either side of $\mathrm{frobVar}_p(\mathrm{AA}_{x,y})=p\bigl(g_0(X_x)\ell(X_y)-\mathrm{AA}_{y,x}\bigr)$ only when $(n_x,n_y)=\bigl(p(p^2)^a,(p^2)^b\bigr)$ (`:313,340–353`). At such $n$, $\mathrm{coeff}_n(g_0(X_x)\ell(X_y))=p^{-(a+1)}p^{-b}=p^{-(a+b+1)}$ (`coeff_product_single_variables`, `:60–89,315`). If $b\le a$ (`:316–328`), then $\mathrm{frobVar}_p(\mathrm{AA}_{x,y})$ vanishes at $n$ (its $n_y$-exponents have the shape $(p^2)^{j+1}$ with $a\le j$, forcing $b=j+1>a$), while $\mathrm{coeff}_n(\mathrm{AA}_{y,x})=p^{-(b+a+1)}$ cancels $g_0(X_x)\ell(X_y)$ to $0$. If $b>a$ (`:329–339`), write $b=b'+1$ with $a\le b'$; then $\mathrm{AA}_{y,x}$ vanishes at $n$, while $\mathrm{coeff}_n(\mathrm{frobVar}_p\,\mathrm{AA}_{x,y})=p^{-(a+b'+1)}=p\cdot p^{-(a+b+1)}$. Taking $(x,y)=(0,1)$ and $(1,0)$ gives `IdentityB` (`:355–360`), and expanding $\mathrm{Gser}(p,c',c)=c'\,\mathrm{Aser}-c\,\mathrm{Aser}'$ by linearity of `expand p` gives `FrobExprG` (`:362–370`).

(3) Viewing $\mathrm{swap2}$ as `MvPowerSeries.rename (Equiv.swap 0 1)` (`ScalingSwapLemmas.lean:28–48`) gives $\mathrm{coeff}_n(\mathrm{swap2}\,G)=\mathrm{coeff}_{(n_1,n_0)}(G)$, from which involution, `DivAB`, and `Integral` are immediate (`:280–286,301–308`). For `SuppOK` (`:287–300`), if $n_1\equiv p n_0\pmod{p^2-1}$, then using $p^2=1+(p^2-1)\equiv1\pmod{p^2-1}$ gives $n_0\equiv p^2 n_0=p(p n_0)\equiv p n_1\pmod{p^2-1}$. Finally, $\mathrm{swap2}$ commutes with `map σ` and `frobVar p` (`:59–85`), hence with $\mathrm{DeS}_{p,\sigma}$, and swaps $g_0(X_0)\ell(X_1)$ with $\ell(X_0)g_0(X_1)$ (`swap_two_single_mul`, `:75–80`), giving $\mathrm{Hser}_{p,\sigma}(\mathrm{swap2}\,G,\gamma',\gamma)=\mathrm{swap2}(\mathrm{Hser}_{p,\sigma}(G,\gamma,\gamma'))$ (`:309–312`).

(4) Write `PhiH hp σ f := frobVar p (map σ f)` (`LocalComponentGL.lean:159–166`), a ring homomorphism. For a single integral monomial $c X^a$ ($\lVert c\rVert\le1$), $(c X^a)^p-\mathrm{PhiH}(c X^a)=(c^p-\sigma(c))X^{p a}$ has `Bd p⁻¹` by the Frobenius-lift hypothesis (`frob_monomial`, `:186–199`). If $x,y$ are integral and satisfy the bound, $(x+y)^p-\mathrm{PhiH}(x+y)=(x^p-\mathrm{PhiH}\,x)+(y^p-\mathrm{PhiH}\,y)+p\,x y\sum_{0<k<p}(\binom pk/p)x^{k-1}y^{p-k-1}$ also has `Bd p⁻¹` by the ultrametric maximum inequality and $\lVert p\rVert=p^{-1}$ (`frob_add`, `:201–215`), so finite sums of integral monomials satisfy `Bd p⁻¹` (`frob_finset`, `:217–238`). For an arbitrary integral series $f$ and multi-index $n$, truncate $f$ to total degree $<\deg(n)+1$ (`truncD (n.degree + 1) f`, `:86–102`): both $f^p-(\mathrm{truncD}\,f)^p$ (divisible by $f-\mathrm{truncD}\,f$) and $\mathrm{PhiH}(f-\mathrm{truncD}\,f)$ vanish at $n$, reducing $\mathrm{coeff}_n(f^p-\mathrm{PhiH}\,f)$ to the finite polynomial $\mathrm{truncD}\,f$ (`:239–260`). $\square$

**Theorem 8.17b (from partial-derivative remainder to partial-coboundary remainder: `StepII_of`) [Lean, read].** *Assume `DworkMv`, `DivDeriv`, `DeIntegral`, and `LawSymm`. Let $K$ be an ultrametric normed field of characteristic zero with `UnrOK K p σ`, let $F\in K[[X_0,X_1]]$ satisfy `IsLawOfLog p F`, let $G\in K[[X_0,X_1]]$ satisfy `DivAB G` and `G7.Simeq (d1 F G) 0`, and let $c\in K$ satisfy $\lVert c\rVert\le1$ and `DerivIs p G c`. Then*
$$\mathrm{Integral}\Bigl(\mathrm{d1}\,F\,\bigl(\mathrm{DeS}_{p,\sigma}(G)\bigr)-\sigma(c)\,\mathrm{in3}\bigl(\mathrm{cob}_F(g_0)\bigr)\,\ell(X_2)\Bigr).$$
`src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/PartialCoboundaryLinear.lean:225–415`.

*Proof.* Unpack `UnrOK` (`:227`) to get $p$ prime, $\lVert p\rVert=p^{-1}$, and $\lVert\sigma(a)-a^p\rVert\le p^{-1}$ for $\lVert a\rVert\le1$ (the `DivAB G` hypothesis is introduced as `_` at `:226` and not used). Since $\lVert p\rVert=p^{-1}>0$, $(p:K)\neq0$ and $\lVert p^{-1}\rVert=p$, so multiplying any series satisfying `Bd p⁻¹` by $p^{-1}$ produces an integral series (`hscale`, `:234–245`).

1. *Frobenius invariance of $F$ and the integral perturbation $r$* (`:228–294`). By `LawSymm`, $\mathrm{map}\,\sigma\,F=F$ (`hσF`, `:228`), and by `DeIntegral`, $\mathrm{cob}_F(g_0)$ is integral (`hδi`, `:229`). Set $A:=\mathrm{in3}\,F=F(X_0,X_1)\in K[[X_0,X_1,X_2]]$. Because $X_0,X_1$ are integral with zero constant term and $F(0)=0$, $F$ integral (`IsLawOfLog`), $A$ has zero constant term (`hA0`, `:266–267`), is integral (`hAi`, `:268`, via `LogarithmEquivalence.integral_subst'`, `LogarithmEquivalence.lean:55–68`), and satisfies $\mathrm{map}\,\sigma\,A=A$ (`hσA`, `:270–272`), while $\mathrm{in3}(\mathrm{cob}_F(g_0))$ is also integral (`hδ3i`, `:269`). Define
   $$r:=p^{-1}\bigl(\mathrm{frobVar}_p(A)-A^p\bigr)\in K[[X_0,X_1,X_2]],\qquad\text{so }\mathrm{frobVar}_p(A)=A^p+p\,r$$
   (`hr`, `hFr`, `:279–286`). Applying Lemma 8.17a(4) (`frob_congr`) to $A$ and rewriting $\mathrm{PhiH}\,A=\mathrm{frobVar}_p(\mathrm{map}\,\sigma\,A)=\mathrm{frobVar}_p(A)$ gives `Bd p⁻¹ (frobVar p A - A^p)`, so $r$ is integral by `hscale` (`hri`, `:287–291`) and $r(0)=0$ (`hr0`, `:292–293`).
2. *Comparing the two three-variable Frobenius expressions* (`:295–330`). Write $G_s:=\mathrm{map}\,\sigma\,G$ (`:303`). Composing the three legal substitutions $[A,X_2],[X_0,X_2],[X_1,X_2]$ of `d1 F` with `frobVar p` in both orders (`pair_frobVar`, `:86–95`, and `map_pair` with `frobVar_pair` and $\mathrm{map}\,\sigma\,A=A$, `:76–85,96–104`) yields (`hd1P`, `hd1s`, `:304–323`):
   $$\begin{aligned}
   \mathrm{d1}\,F\,(\mathrm{frobVar}_p\,G_s)&=G_s(A^p,X_2^p)-G_s(X_0^p,X_2^p)-G_s(X_1^p,X_2^p),\\
   \mathrm{frobVar}_p\bigl(\mathrm{map}\,\sigma\,(\mathrm{d1}\,F\,G)\bigr)&=G_s(\mathrm{frobVar}_p\,A,X_2^p)-G_s(X_0^p,X_2^p)-G_s(X_1^p,X_2^p).
   \end{aligned}$$
   The second and third terms match identically! Meanwhile, applying the forward direction of `DworkMv` to `Simeq (d1 F G) 0` gives `hE2 : Bd p⁻¹ (frobVar p (map σ (d1 F G)) - C p * d1 F G)` (`:325–330`).
3. *Compensating $\partial_0 G_s$ and applying `DivDeriv`* (`:331–369`). Define
   $$\Phi:=G_s-\sigma(c)\,\ell(X_0)g_0(X_1)\in K[[X_0,X_1]]$$
   (`:331–332`). Since $\sigma$ fixes the rational coefficients of $\ell$ and $g_0$ (`map_lgF`, `map_g0F`, `:126–132`) and commutes with `at1`, `derivative`, and `pderiv` (`:134–150`), and since $\partial_0\bigl(\sigma(c)\,\ell(X_0)g_0(X_1)\bigr)=\sigma(c)\,\ell'(X_0)g_0(X_1)$ by the Leibniz rule and one-variable chain rule (`pderiv_prod`, `:151–176`, invoking `Formalism.G.LogCR.pderiv_psubst`, `ChainRule.lean:115–120`), we have
   $$\partial_0\Phi=\mathrm{map}\,\sigma\,\bigl(\partial_0 G-c\,\ell'(X_0)g_0(X_1)\bigr)$$
   (`:334–339`). Because $\lVert\sigma(a)\rVert\le\max(\lVert\sigma(a)-a^p\rVert,\lVert a^p\rVert)\le1$ whenever $\lVert a\rVert\le1$ (`norm_sigma_le`, `:206–212`), `DerivIs p G c` implies `Integral (pderiv 0 Φ)` (`hΦi`, `:333–342`). Now apply `DivDeriv` in variable $0\in\mathrm{Fin}\,2$ to $\Phi$ at base substitution $\varphi=[A^p,X_2^p]$ (zero constant terms and integral by Step 1) and perturbation $Y=r$: since updating slot $0$ of $[A^p,X_2^p]$ by $+p\,r$ produces $[\mathrm{frobVar}_p\,A,X_2^p]$ (`hupd`, `:353–361`), we obtain
   $$h_{E_1}:\ \mathrm{Bd}\bigl(p^{-1},\ \Phi(\mathrm{frobVar}_p\,A,X_2^p)-\Phi(A^p,X_2^p)\bigr)$$
   (`:343–361`). Moreover, for any legal pair $[u,v]$, $\Phi(u,v)=G_s(u,v)-\sigma(c)\,\ell(u)g_0(v)$ (`hSΦ`, `:362–369`).
4. *Rewriting $\mathrm{in3}(\mathrm{cob}_F(g_0))$ and $g_0(X_2^p)$* (`:371–397`). From $\mathrm{cob}_F(\ell)=0$, applying $\mathrm{in3}$ gives $\ell(A)=\ell(X_0)+\ell(X_1)$ (`hlogA`, `:371–380`). By Lemma 8.17a(1) ($g_0(u)=p^{-1}\ell(u^p)$), $g_0(X_i)=p^{-1}\mathrm{frobVar}_p(\ell(X_i))$ (`hat`, `:381–384`), so
   $$\begin{aligned}
   \mathrm{in3}\bigl(\mathrm{cob}_F(g_0)\bigr)&=g_0(A)-g_0(X_0)-g_0(X_1)=p^{-1}\Bigl(\ell(A^p)-\mathrm{frobVar}_p\bigl(\ell(X_0)+\ell(X_1)\bigr)\Bigr)\\
   &=p^{-1}\bigl(\ell(A^p)-\ell(\mathrm{frobVar}_p\,A)\bigr)
   \end{aligned}$$
   (`hδ`, `:385–395`). And by the second identity of Lemma 8.17a(1) at $a=X_2$, $g_0(X_2^p)=\ell(X_2)-X_2$ (`hgb`, `:396–397`).
5. *The master identity `key` and norm bound* (`:399–414`). Since $F(0)=0$, $\mathrm{d1}\,F$ is linear (`partial_coboundary_linear`, `:178–199`), giving $\mathrm{d1}\,F\,(\mathrm{DeS}_{p,\sigma}\,G)=p^{-1}\bigl(\mathrm{d1}\,F\,(\mathrm{frobVar}_p\,G_s)-p\,\mathrm{d1}\,F\,G\bigr)$. Using Step 2 to replace $\mathrm{d1}\,F\,(\mathrm{frobVar}_p\,G_s)$ by $\mathrm{frobVar}_p(\mathrm{map}\,\sigma\,(\mathrm{d1}\,F\,G))-\bigl(G_s(\mathrm{frobVar}_p\,A,X_2^p)-G_s(A^p,X_2^p)\bigr)$, rewriting both $G_s(\cdot,X_2^p)$ terms through $\Phi(\cdot,X_2^p)+\sigma(c)\,\ell(\cdot)g_0(X_2^p)$, and substituting $g_0(X_2^p)=\ell(X_2)-X_2$ and $p^{-1}(\ell(A^p)-\ell(\mathrm{frobVar}_p\,A))=\mathrm{in3}(\mathrm{cob}_F(g_0))$ from Step 4 cancels $-\sigma(c)\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$ identically and yields (`key`, `:399–411`):
   $$\begin{aligned}
   &\mathrm{d1}\,F\,\bigl(\mathrm{DeS}_{p,\sigma}(G)\bigr)-\sigma(c)\,\mathrm{in3}\bigl(\mathrm{cob}_F(g_0)\bigr)\,\ell(X_2)\\
   &\quad=p^{-1}\Bigl[\bigl(\mathrm{frobVar}_p(\mathrm{map}\,\sigma\,(\mathrm{d1}\,F\,G))-p\,\mathrm{d1}\,F\,G\bigr)-\bigl(\Phi(\mathrm{frobVar}_p\,A,X_2^p)-\Phi(A^p,X_2^p)\bigr)\Bigr]\\
   &\qquad-\sigma(c)\,\mathrm{in3}\bigl(\mathrm{cob}_F(g_0)\bigr)\,X_2.
   \end{aligned}$$
   Inside the bracket, `bd_sub hE2 hE1` has `Bd p⁻¹`, so multiplying by $p^{-1}$ is integral (`hscale`); on the right, $\lVert\sigma(c)\rVert\le1$ (`norm_sigma_le`), $\mathrm{in3}(\mathrm{cob}_F(g_0))$ is integral (`hδ3i`), and $X_2$ is integral (`integral_X`), so their product is integral and the difference is integral (`:412–414`). $\square$

**Lemma 8.17c (constant-coefficient three-variable embedding, coboundary of `Hser`, and congruence disjointness: `CoboundarySeries`) [Lean, read].** *Let $K$ be a field and $F\in K[[X_0,X_1]]$ with $F(0)=0$.*

1. *(`constantCoeff_first_two_of_three`, `partial_coboundary_product`, `partial_coboundary_h_series`, `ConstantCoeffFirstTwoOfThree.lean:24–110`) $(\mathrm{in3}\,F)(0)=0$; hence $[(\mathrm{in3}\,F),X_2]$ is a legal substitution, $\mathrm{d1}\,F$ is $K$-linear, $\mathrm{d1}\,F\,(f(X_0)g(X_1))=\mathrm{in3}(\mathrm{cob}_F(f))\,g(X_2)$ for all $f,g\in K[[T]]$, and whenever $\mathrm{cob}_F(\ell)=0$,*
   $$\mathrm{d1}\,F\,\bigl(\mathrm{Hser}_{p,\sigma}(G,\gamma,\gamma')\bigr)=\mathrm{d1}\,F\,\bigl(\mathrm{DeS}_{p,\sigma}(G)\bigr)-\gamma\,\mathrm{in3}\bigl(\mathrm{cob}_F(g_0)\bigr)\,\ell(X_2).$$
2. *(`suppOK_Hser`, `:121–197`) If $2\le p$ and `SuppOK p G`, then `SuppOK p (Hser p σ G γ γ')` for all $\gamma,\gamma'\in K$.*
3. *(`coeff_lg_lg_eq_zero`, `:198–214`) If $2\le p$ and $n\in\mathbb N^2$ satisfies $n_0\equiv p n_1\pmod{p^2-1}$, then $\mathrm{coeff}_n\bigl(\ell(X_0)\ell(X_1)\bigr)=0$.*

*Proof.* (1) Expanding `constantCoeff_subst` for $\mathrm{in3}\,F=F(X_0,X_1)$ over $d\in\mathbb N^2$ (`:27–40`), the $d=0$ summand is $F(0)=0$, and any $d\neq0$ has $d_s\neq0$ for some $s\in\{0,1\}$, where $(\mathrm{constantCoeff}\,X_s)^{d_s}=0^{d_s}=0$. Thus `has_subst_coboundary_first` (`:41–42`) makes $[(\mathrm{in3}\,F),X_2]$ legal, giving subtraction and scalar linearity of $\mathrm{d1}\,F$ (`:46–60`). On a pure tensor $f(X_0)g(X_1)$ (`:88–97`), each of the three substitutions of $\mathrm{d1}\,F$ factors $g(X_2)$ out on the right and leaves $f(\mathrm{in3}\,F)-f(X_0)-f(X_1)=\mathrm{in3}(\mathrm{cob}_F(f))$ (`include_three_coboundary`, `:71–86`). Applying this to $\mathrm{Hser}_{p,\sigma}(G,\gamma,\gamma')$ (`:103–110`) turns $-\gamma\,g_0(X_0)\ell(X_1)$ into $-\gamma\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$ and $-\gamma'\,\ell(X_0)g_0(X_1)$ into $-\gamma'\,\mathrm{in3}(\mathrm{cob}_F(\ell))\,g_0(X_2)=0$.

(2) `SuppOK p` is closed under subtraction and scalar multiplication (`:121–136`), and under `frobVar p (map σ ·)` (`:138–146`: a nonzero coefficient at $n$ forces $n=p m$ with $\mathrm{coeff}_m(G)\neq0$, so $1\le m_k\implies 1\le p m_k$ and $m_0\equiv p m_1\implies p m_0\equiv p(p m_1)\pmod{p^2-1}$). Using $(p^2)^x\equiv1\pmod{p^2-1}$ (`powq_modEq_one`, `:117–120`), any nonzero coefficient of $g_0(X_0)\ell(X_1)$ sits at $(p(p^2)^j,(p^2)^i)$, where $p(p^2)^j\equiv p\equiv p(p^2)^i\pmod{p^2-1}$ (`support_ok_g_zero_log`, `:164–176`), and any nonzero coefficient of $\ell(X_0)g_0(X_1)$ sits at $((p^2)^i,p(p^2)^j)$, where $(p^2)^i\equiv1\equiv(p^2)^{j+1}=p\cdot p(p^2)^j\pmod{p^2-1}$ (`support_ok_log_g_zero`, `:177–191`). Combining these gives `suppOK_Hser` (`:192–197`).

(3) By `coeff_product_single_variables`, $\mathrm{coeff}_n(\ell(X_0)\ell(X_1))=\mathrm{coeff}_{n_0}(\ell)\,\mathrm{coeff}_{n_1}(\ell)$ (`:201`). If this were nonzero, then $n_0=(p^2)^i$ and $n_1=(p^2)^j$ for some $i,j\in\mathbb N$ (`:156–162,203–204`), so $n_0\equiv p n_1\pmod{p^2-1}$ would give $1\equiv p\pmod{p^2-1}$ (`:206–207`). For $2\le p$, $p^2\ge2p$ implies $1<p<p^2-1$ (`:208–211`), so reducing both sides modulo $p^2-1$ gives the contradiction $1=p$ (`:212–213`). $\square$

**Theorem 8.17d (integrality of the compensated Dwork series: `StepH_of`) [Lean, read].** *Assume `LemmaTwo`. Let $K$ be a complete ultrametric normed field of characteristic zero with `UnrOK K p σ`, let $F$ satisfy `IsLawOfLog p F`, let $G\in K[[X_0,X_1]]$ satisfy `SuppOK p G`, and let $\gamma,\gamma'\in K$. If both $\mathrm{d1}\,F\,(\mathrm{DeS}_{p,\sigma}\,G)-\gamma\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$ and $\mathrm{d1}\,F\,(\mathrm{DeS}_{p,\sigma}(\mathrm{swap2}\,G))-\gamma'\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$ are integral, then `Integral (Hser p σ G γ γ')`.*
`src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean:277–301`.

*Proof.* From $2<p$ in `UnrOK`, $2\le p$ (`:279`; the `LawSymm` parameter `_hL` of `StepH_of` is unused, and `SwapRules` is proved unconditionally in Lemma 8.17a(3)). Set $H:=\mathrm{Hser}_{p,\sigma}(G,\gamma,\gamma')$. By Lemma 8.17c(2), `SuppOK p H` holds (`:281`), which implies `DivAB H` (`:282–286`, since $n_0\ge1$ and $n_1\ge1$ whenever $\mathrm{coeff}_n(H)\neq0$). By Lemma 8.17c(1), $\mathrm{d1}\,F\,H=\mathrm{d1}\,F\,(\mathrm{DeS}_{p,\sigma}\,G)-\gamma\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$, which is integral by the first hypothesis (`hd1`, `:287–289`). By Lemma 8.17a(3), $\mathrm{swap2}\,H=\mathrm{Hser}_{p,\sigma}(\mathrm{swap2}\,G,\gamma',\gamma)$, so Lemma 8.17c(1) applied to $(\mathrm{swap2}\,G,\gamma',\gamma)$ identifies $\mathrm{d1}\,F\,(\mathrm{swap2}\,H)$ with $\mathrm{d1}\,F\,(\mathrm{DeS}_{p,\sigma}(\mathrm{swap2}\,G))-\gamma'\,\mathrm{in3}(\mathrm{cob}_F(g_0))\,\ell(X_2)$, which is integral by the second hypothesis (`hd2`, `:290–292`). Therefore `LemmaTwo` applies to $H$ (`:293`) and yields $\beta\in K$ and an integral series $R\in K[[X_0,X_1]]$ with
$$H=\beta\,\ell(X_0)\ell(X_1)+R.$$
Fix $n\in\mathbb N^2$ (`:294`). If $\mathrm{coeff}_n(H)=0$, then $\lVert\mathrm{coeff}_n(H)\rVert=0\le1$ (`:295–297`). Otherwise `SuppOK p H` gives $n_0\equiv p n_1\pmod{p^2-1}$, so Lemma 8.17c(3) gives $\mathrm{coeff}_n(\ell(X_0)\ell(X_1))=0$; hence $\mathrm{coeff}_n(H)=\beta\cdot0+\mathrm{coeff}_n(R)=\mathrm{coeff}_n(R)$, which has norm $\le1$ because $R$ is integral (`:298–301`). $\square$

**Proposition 8.17e (locking $c+\sigma(c')=0$ and closing `G7.Simeq`: `c_add_sigma_c_eq_zero` and `StepIV_of`) [Lean, read].** *Let $K$ be an ultrametric normed field of characteristic zero with `UnrOK K p σ`.*

1. *(`c_add_sigma_c_eq_zero : StepIII`, `ConstantCoeffFirstTwoOfThree.lean:338–388`) If $G\in K[[X_0,X_1]]$ and $c,c'\in K$ ($\lVert c\rVert\le1,\lVert c'\rVert\le1$) satisfy `DerivIs p G c` and `Integral (Hser p σ G (σ c) (σ c'))`, then $c+\sigma(c')=0$.*
2. *(`StepIV_of`, `:389–418`, assuming `DworkMv`) Assume `DworkMv`. If `DivAB G`, $\sigma(\sigma(c))=c$, and `Integral (Hser p σ G (σ c) (-c))`, then `G7.Simeq G (Gser p c (σ c))`.*

*Proof.* (1) First note `eq_zero_of_div` (`:223–237`): if $x\in K$ satisfies $\lVert x\cdot(p^{i+1})^{-1}\rVert\le1$ for all $i\in\mathbb N$, then $\lVert x\rVert\le(p^{-1})^{i+1}$ for all $i\in\mathbb N$ because $\lVert p\rVert=p^{-1}$, forcing $x=0$ since $0\le p^{-1}<1$ (`exists_pow_lt_of_lt_one`). Fix $i\in\mathbb N$, and set $m:=p(p^2)^i$ and $n:=(1,m)\in\mathbb N^2$ (`:352–355`). Direct inspection of the defining sums gives $\mathrm{coeff}_1(\ell)=1$, $\mathrm{coeff}_1(g_0)=0$, and $\mathrm{coeff}_m(g_0)=(p^{i+1})^{-1}$ (`:302–336,349–354`).
- At bidegree $(0,m)$, $\partial_0 G$ has coefficient $1\cdot\mathrm{coeff}_{(1,m)}(G)=\mathrm{coeff}_n(G)$ and $\ell'(X_0)g_0(X_1)$ has coefficient $\mathrm{coeff}_0(\ell')\,\mathrm{coeff}_m(g_0)=1\cdot(p^{i+1})^{-1}$, so `DerivIs p G c` gives (`hcoefD`, `hA`, `:357–365,377–379`)
  $$\bigl\lVert\mathrm{coeff}_n(G)-c\,(p^{i+1})^{-1}\bigr\rVert\le1.$$
- At bidegree $n=(1,m)$, since $2\le p$ implies $p\nmid 1$, $\mathrm{coeff}_n\bigl(\mathrm{frobVar}_p(\mathrm{map}\,\sigma\,G)\bigr)=0$ (`coeff_frobVar_of_not_dvd`, `:344–346,370–371`), so $\mathrm{DeS}_{p,\sigma}(G)$ has coefficient $p^{-1}(0-p\,\mathrm{coeff}_n(G))=-\mathrm{coeff}_n(G)$. Meanwhile $\mathrm{coeff}_n\bigl(g_0(X_0)\ell(X_1)\bigr)=\mathrm{coeff}_1(g_0)\,\mathrm{coeff}_m(\ell)=0$ and $\mathrm{coeff}_n\bigl(\ell(X_0)g_0(X_1)\bigr)=\mathrm{coeff}_1(\ell)\,\mathrm{coeff}_m(g_0)=(p^{i+1})^{-1}$, so integrality of $\mathrm{Hser}_{p,\sigma}(G,\sigma c,\sigma c')$ gives (`hcoefH`, `hB`, `:366–376,380–382`)
  $$\bigl\lVert-\mathrm{coeff}_n(G)-\sigma(c')\,(p^{i+1})^{-1}\bigr\rVert\le1.$$
Since $(c+\sigma(c'))(p^{i+1})^{-1}=-\bigl[(\mathrm{coeff}_n(G)-c(p^{i+1})^{-1})+(-\mathrm{coeff}_n(G)-\sigma(c')(p^{i+1})^{-1})\bigr]$ (`key`, `:383–385`), the ultrametric inequality (`norm_add_le_one`, `:221`) gives $\lVert(c+\sigma(c'))(p^{i+1})^{-1}\rVert\le1$ for all $i\in\mathbb N$, hence $c+\sigma(c')=0$ (`:351,386–387`).

(2) Both $G$ (by `DivAB G` at $n=0$) and $\mathrm{Gser}(p,c,\sigma c)$ (`constantCoeff_Gser`, `:259–270`) have zero constant coefficient, giving the constant-term half of `G7.Simeq` (`hcc`, `:395–397`). Because $\sigma$ fixes the rational coefficients of $\mathrm{Aser}$ and $\mathrm{Aser}'$ (`map_Gser`, `:244–258`) and $\sigma(\sigma(c))=c$, we have $\mathrm{map}\,\sigma\,\bigl(\mathrm{Gser}(p,c,\sigma c)\bigr)=\mathrm{Gser}(p,\sigma c,c)$ (`hmapG`, `:403`). Subtracting Lemma 8.17a(2) (`FrobExprG` at $(c,\sigma c)$) from $\mathrm{frobVar}_p(\mathrm{map}\,\sigma\,G)-pG=p\,\mathrm{DeS}_{p,\sigma}(G)$ (`hDeS`, `:405–408`) yields (`key`, `:409–414`):
$$\mathrm{frobVar}_p\Bigl(\mathrm{map}\,\sigma\,\bigl(G-\mathrm{Gser}(p,c,\sigma c)\bigr)\Bigr)-p\bigl(G-\mathrm{Gser}(p,c,\sigma c)\bigr)=p\,\mathrm{Hser}_{p,\sigma}(G,\sigma c,-c).$$
Since $\mathrm{Hser}_{p,\sigma}(G,\sigma c,-c)$ is integral and $\lVert p\rVert=p^{-1}$, every coefficient on the right has norm $\le p^{-1}\cdot1=p^{-1}$ (`:415–417`), so the reverse direction of `DworkMv` gives `Integral (mvExp (G - Gser p c (σ c)))` (`:398–400`). $\square$

**Theorem 8.17f (conditional classification `BetaIsG_of` and consumer return to `restBeta`) [Lean, read].** *Assume the named interfaces `StepZero`, `StepI`, `LemmaTwo`, `DworkMv`, `DivDeriv`, `DeIntegral`, `LawSymm`, and `SimeqRules`. Then `BetaIsG` holds: for every complete ultrametric normed field $K$ of characteristic zero, prime $p$, and ring endomorphism $\sigma:K\to K$ satisfying `UnrOK K p σ`, if $K$ has a primitive $(p^2-1)$-th root of unity, `IsLawOfLog p F`, and `BetaHyp p F be`, there exists $c\in K$ with*
$$\lVert c\rVert\le1,\qquad\sigma(\sigma(c))=c,\qquad\text{and}\qquad\texttt{G7.Simeq}\;\;be\;\;\bigl(\mathrm{Gser}(p,c,\sigma c)\bigr).$$
*In the archive, `Top.betaIsG` (`FinalS.lean:61–62`) instantiates `BetaIsG_of` (`NormLiftLeOne.lean:32–56`) with the theorems above and supplies Theorem 8.16i (`restBeta`, `BiadditiveSecondVariable.lean:143–153`) at $K=K_0=\mathrm{Frac}\,W(\overline{\mathbb F}_p)$.*

*Proof.* Fix $(K,p,\sigma,F,be)$ satisfying the hypotheses (`NormLiftLeOne.lean:34`), and record $2\le p$ from `UnrOK` (`:36`) and the six conjuncts of Lemma 8.17a(3) (`SwapRules`, `:37`).

1. *Support projection* (`:35,40`). `StepZero` produces $G\in K[[X_0,X_1]]$ with `SuppOK p G`, `Simeq G be` (`hGbe`), `Simeq (d1 F G) 0` (`hG1`), and `Simeq (d1 F (swap2 G)) 0` (`hG2`). From `SuppOK p G`, $n_0,n_1\ge1$ on the support gives `DivAB G` (`divAB_of_suppOK`, `:13–18,40`), and `SwapRules` gives `SuppOK p (swap2 G)`, `DivAB (swap2 G)`, and $\mathrm{swap2}(\mathrm{swap2}\,G)=G$.
2. *First-derivative scalars in both orientations* (`:38–39`). `StepI` applied to $G$ yields $c\in K$ with $\lVert c\rVert\le1$ (`hc`) and `DerivIs p G c` (`hcG`). Applying `StepI` to $\mathrm{swap2}\,G$ — whose first- and second-variable `Simeq` hypotheses are `hG2` and `hG1` after rewriting $\mathrm{swap2}(\mathrm{swap2}\,G)=G$ — yields $c'\in K$ with $\lVert c'\rVert\le1$ (`hc'`) and `DerivIs p (swap2 G) c'` (`hcG'`).
3. *Partial-coboundary remainders* (`:41–42`). Theorem 8.17b (`StepII_of`) applied to $(G,c)$ gives `hI1 : Integral (d1 F (DeS p σ G) - C (σ c) * (in3 (cob F g0F) * at1 2 lgF))`, and applied to $(\mathrm{swap2}\,G,c')$ gives `hI2 : Integral (d1 F (DeS p σ (swap2 G)) - C (σ c') * (in3 (cob F g0F) * at1 2 lgF))`.
4. *Integrality of `Hser` in both orientations* (`:43,45–47`). Theorem 8.17d (`StepH_of`) at $\gamma=\sigma(c),\gamma'=\sigma(c')$ combines `hI1` and `hI2` into `hHs : Integral (Hser p σ G (σ c) (σ c'))` (`:43`). By Lemma 8.17a(3), $\mathrm{Hser}_{p,\sigma}(\mathrm{swap2}\,G,\sigma c',\sigma c)=\mathrm{swap2}\bigl(\mathrm{Hser}_{p,\sigma}(G,\sigma c,\sigma c')\bigr)$ (`:46`), and `swap2` preserves `Integral` (`:47`), giving `hHs' : Integral (Hser p σ (swap2 G) (σ c') (σ c))`.
5. *Assembling the Frobenius-fixed scalar $\sigma(\sigma(c))=c$* (`:44,48–53`). Proposition 8.17e(1) (`c_add_sigma_c_eq_zero`) applied to $(G,c,c',\mathrm{hcG},\mathrm{hHs})$ gives $e_1:c+\sigma(c')=0$ (`:44`), and applied to $(\mathrm{swap2}\,G,c',c,\mathrm{hcG'},\mathrm{hHs'})$ gives $e_2:c'+\sigma(c)=0$ (`:48`). From $e_1$, $\sigma(c')=-c$ (`hA`, `:49`); from $e_2$, $c'=-\sigma(c)$, so applying the ring homomorphism $\sigma$ gives $\sigma(c')=-\sigma(\sigma(c))$ (`hB`, `:50–51`). Subtracting `hA` from `hB` yields $\sigma(\sigma(c))=c$ (`hσσ`, `:52`), and rewriting $\sigma(c')=-c$ in `hHs` gives `Integral (Hser p σ G (σ c) (-c))` (`:53`).
6. *Closing `G7.Simeq` and returning to `restBeta`* (`:54–56`; `BiadditiveSecondVariable.lean:143–153`). Proposition 8.17e(2) (`StepIV_of`) turns `hσσ` and `hHs` into `hSimG : Simeq G (Gser p c (σ c))` (`:54`). Symmetry of `Simeq` (`SimeqRules`) turns `Simeq G be` into `Simeq be G`, and transitivity with `hSimG` gives `Simeq be (Gser p c (σ c))` (`:55–56`). In Theorem 8.16i (`restBeta`), `Top.betaIsG` is invoked at $K_0=\mathrm{Frac}\,W(\overline{\mathbb F}_p)$, $\sigma=\sigma_K$, and $be'=\mathrm{inParam}_p\,be$ (`:143–144`); $\lVert c\rVert\le1$ pulls $c$ back to $w\in W$ with $\sigma_W^2(w)=w$ (`:145–152`), `integralExp_of_equiv` converts `G7.Simeq` into `E0 p (inParam p be - Gser p (wK w) (wK (σ_W w)))` (`:153`), and `ea_restSExpV_of` (`EaRestSExpVOf.lean:262–267`, §8.4.14 and Corollary 8.16j) hands $(w,\sigma_W^2 w=w)$ to `th_restGcV_of` (§8.4.15, whose $\pi^{p+1}/p$ normalization is cited without re-auditing here) and the `E0` witness to the $Y$-factor of `ea_reduce`. $\square$

**Remarks [Expository].**

1. *Why the sign flips between $c'$ in `BetaIsG_of` and the second argument of `Gser`.* In `BetaIsG_of`, $c'$ is the `StepI` scalar of $\mathrm{swap2}\,G$, which measures the singular part of $\partial_0(\mathrm{swap2}\,G)$ along $\ell'(X_0)g_0(X_1)$. Since $\mathrm{swap2}\,\mathrm{Gser}(p,c,d)=c\,\mathrm{Aser}'-d\,\mathrm{Aser}=(-d)\,\mathrm{Aser}-(-c)\,\mathrm{Aser}'$, the first-variable scalar of $\mathrm{swap2}\,\mathrm{Gser}(p,c,d)$ is $-d$. Thus $c'+\sigma(c)=0$ says $-d+\sigma(c)=0$, i.e. $d=+\sigma(c)$, while $-\sigma(c')\,\ell(X_0)g_0(X_1)$ inside $\mathrm{Hser}_{p,\sigma}(G,\sigma c,\sigma c')$ becomes $+c\,\ell(X_0)g_0(X_1)$, matching the $-p c\,\ell(X_0)g_0(X_1)$ term on the right-hand side of `FrobExprG` (`StepIV_of`, `:410–414`).
2. *Where `[CompleteSpace K]`, $2<p$, and the discrete value group are used — and where they are not.* None of `StepII_of`, `StepH_of`, `c_add_sigma_c_eq_zero`, or `StepIV_of` projects the discrete-valuation clause $\forall a\neq0,\ \exists k\in\mathbb Z,\ \lVert a\rVert=p^k$ of `UnrOK`, and each of them relaxes $2<p$ immediately to $2\le p$ or `p.Prime`. Likewise `[CompleteSpace K]` is absent from the type signatures of `StepII`, `StepIII`, and `StepIV`; it enters `BetaIsG_of` only at `StepI` and `StepH`, because `LemmaOne` and `LemmaTwo` construct their integral remainders $R$ by convergent $p$-adic approximation in $K$ (whereas `LemmaOne_of` in `NotDvdChoosePowMul.lean:531` also discards $2<p$ and discrete valuation, passing $\sigma$ only to `DeIntegral`; see [§8.4.19](#8419-classifying-slice-coboundaries-and-the-lemmaone-supply)). Alongside `BetaIsG_of`, `NormLiftLeOne.lean:58–72` also proves `ThmSFull_of` (using `norm_lift_le_one`, `:20–30`), which feeds `Top.thmSFull` (`FinalS.lean:63`); on the main path to `Conclusion₂`, Chapter 8 routes instead through `restBeta` and `ea_restSExpV_of` (§§8.4.14–8.4.16).
3. *Classical context for `DworkMv` and the formal-group coboundaries.* In Serre's February 1960 Bourbaki exposition of Dwork's rationality proof (`[Serre1960]`, §3, Lemma, p. 419), integrality of a two-variable formal series $F(t,Y)\in\mathbb Q[[t,Y]]$ from $F(t^p,Y^p)/F(t,Y)^p\in1+p\mathbb Z_p[[t,Y]]$ is cited directly to Dwork's local norm-residue paper (`[Dwork1958]`, Lemma 1), with Serre noting the equivalent proof via the Artin–Hasse exponential (`[Dieudonne1957]` treats the Witt-vector Frobenius-lift criterion; `[Dwork1962]`, §4(a), pp. 55–57 constructs one-variable splitting functions from the Artin–Hasse series). The archive's named `DworkMv` (`CyclicPowerClassOfExpEquiv.lean:13–20`) is the additive-exponent, multivariable ultrametric version $\mathrm{Integral}(\exp\Psi)\iff\mathrm{Bd}(p^{-1},\mathrm{frobVar}_p(\mathrm{map}\,\sigma\,\Psi)-p\Psi)$. On the formal-group side, the integrality of $\mathrm{cob}_F(g_0)$ (`DeIntegral`) and the coboundary classifications `LemmaOne` and `LemmaTwo` belong to the functional-equation circle of Honda and Hazewinkel (`[Honda1970]`, `[Hazewinkel1978]`) specialized to the height-two logarithm $\ell(T)=\sum_{j\ge0}p^{-j}T^{p^{2j}}$.
4. *What remains named in this subsection.* [§8.4.18](#8418-projection-and-first-derivatives-for-betaisg) reads the production proofs for StepZero and StepI. Within `Top.betaIsG`, we retain as `[Lean]` inputs: `DworkMv` (`Top.dworkMv := dwork_multivariable`), `DivDeriv` (`Top.divDeriv := divided_derivative`), `DeIntegral` (`Top.deIntegral := DeIntegral_of divDeriv lawSymm`), `LawSymm` (`Top.lawSymm := formal_law_symmetric`), `LemmaOne` and `LemmaTwo` (`Top.lemmaOne`, `Top.lemmaTwo`), `StepZero` (`Top.zeroCondition := StepZero_of lamModule simeqRules lawSymm`), `StepI` (`Top.stepI := StepI_of lemmaOne firstDeriv cobLin`), `LamModule` (`Top.lamModule`), `DerivA` (`Top.derivA := derivative_a`; proved directly by exponent arithmetic in Example 1 for expository use, while `IntegralPderivLgF.lean` remains `[Lean]`), `SimeqRules` (`Top.simeqRules := equivalence_rules`), and the polynomial/degree helpers `add_pow_prime_eq`, `sub_dvd_pow_sub_pow`, `Low` (`TopsChoicePartB.lean`, `SolveVAux`) used in Lemma 8.17a(4). Upstream of `restBeta` and elsewhere in Chapter 8, `Top.lawExists`, `witt_teichmuller_root`, the `WModel` norm proofs, the Witt suppliers of §8.4.15, the Gauss bounds, `ea_brScale`, `ea_brNum`, `eb_brJet`, `ea_brClass`, `nm_restNorm_of_place`, and `admitted` retain their status from §§8.4.5–8.4.16.

**Reading boundary and sources.** This subsection adds local R3 `[Lean, read]` for the complete files `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean:1–73` (`divAB_of_suppOK`, `norm_lift_le_one`, `BetaIsG_of`, `ThmSFull_of`), `PartialCoboundaryLinear.lean:1–416` (`FrobeniusSubstitution` lemmas and `StepII_of`), and `ConstantCoeffFirstTwoOfThree.lean:1–419` (`CoboundarySeries` lemmas, `StepH_of`, `c_add_sigma_c_eq_zero`, `StepIV_of`), together with `FinalS.lean:43–63`, `TopsChoicePartA.lean:14–89,109–370` (`frobVar` and product-coefficient helpers, `g_zero_relation_holds`, `frobVar_AA_eq`, `identity_b`, `frobenius_expression_g`), `ScalingSwapLemmas.lean:22–85,276–313` (`swap_rules` and two-variable swap lemmas), `LocalComponentGL.lean:18–118,155–261` (`Bd` rules, `truncD`, `PhiH`, `frob_congr`), `LogarithmEquivalence.lean:18–68` (`ballRing`, `integral_iff_lift`, `integral_subst'`), and `src/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean:1–122` (`pderiv_psubst`); it inherits the coordinate bridge and consumer wiring of `BiadditiveSecondVariable.lean:137–153` (§8.4.16) and `EaRestSExpVOf.lean:260–272` (§8.4.14), and reads as statements `IsLawOfLog.lean:13–104`, `FirstDeriv.lean:13–132`, `OddLogRelation.lean:13–57`, and `CyclicPowerClassOfExpEquiv.lean:13–34`. Pinned Mathlib declarations (`0df444a360eaa60ab8c11dca51a86af692955474`, raw source checked on 2026-11-25): `MvPowerSeries.pderiv`, `coeff_pderiv`, `pderiv_X_self`, `pderiv_X_of_ne` (`RingTheory/MvPowerSeries/Derivative.lean`, author Justus Springer); `MvPowerSeries.expand`, `expand_C`, `expand_subst`, `coeff_expand_smul`, `constantCoeff_expand`, `coeff_expand_of_not_dvd` (`RingTheory/MvPowerSeries/Expand.lean`, author Wenrong Zou); `PowerSeries.derivative`, `coeff_derivative` (`RingTheory/PowerSeries/Derivative.lean`, authors Richard M. Hill and Ralf Stephan); `MvPowerSeries.coe_substAlgHom`, `subst_smul`, `constantCoeff_subst`, `constantCoeff_subst_eq_zero` (`RingTheory/MvPowerSeries/Substitution.lean`, authors Antoine Chambert-Loir and María Inés de Frutos Fernández); `IsUltrametricDist.norm_add_le_max` (`Analysis/Normed/Group/Ultra.lean`, authors Yakov Pechersky and David Loeffler). Classical references: `[Serre1960]` (§3, p. 419, read in primary Numdam scan), `[Dwork1962]` (§4(a), pp. 55–57, read in primary Numdam scan), `[Dwork1958]`, `[Dieudonne1957]`, `[Honda1970]`, `[Hazewinkel1978]`. All formal proofs belong to Levent Alpöge with Claude in archive A2 (`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`); the exposition and the two all-orders worked calculations are ours. Source reading and the book build are not Lean kernel verification.

| Role | Declaration | Source |
|---|---|---|
| Classification assembly and consumer | `Top.betaIsG`, `BetaIsG_of`, `divAB_of_suppOK`, `norm_lift_le_one`, `ThmSFull_of`; consumer `restBeta` (`:143–153`), `ea_restSExpV_of` (`:262–267`) | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FinalS.lean:61`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean:32,13,20,58`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:137`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpVOf.lean:260` |
| Partial-coboundary remainder (`StepII`, new proof body) | `StepII_of`; `frobVar_pair`, `pair_frobVar`, `map_pair`, `subst_g_zero_eq_log`, `subst_pow_g_zero`, `map_lgF`, `map_g0F`, `pderiv_prod`, `partial_coboundary_linear`, `norm_sigma_le`, `integral_X` | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/PartialCoboundaryLinear.lean:225,76,86,96,106,115,126,130,167,178,206,214` |
| Two-variable test, scalar coupling, and `StepIV` (new proof body) | `constantCoeff_first_two_of_three`, `partial_coboundary_product`, `partial_coboundary_h_series`, `suppOK_Hser`, `coeff_lg_lg_eq_zero`, `eq_zero_of_div`, `map_Gser`, `constantCoeff_Gser`, `StepH_of`, `c_add_sigma_c_eq_zero`, `StepIV_of` | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean:24,88,103,192,198,223,244,259,277,338,389` |
| Algebraic Frobenius, swap, and congruence helpers (new proof body) | `frobVar_eq_expand`, `coeff_frobVar_of_not_dvd`, `coeff_frobVar_ne_zero`, `coeff_product_single_variables`, `g_zero_relation_holds`, `frobVar_AA_eq`, `identity_b`, `frobenius_expression_g`; `swap_rules`; `Bd`, `frob_congr`; `integral_subst'`; `pderiv_psubst` | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean:14,23,28,60,250,307,355,362`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean:276`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean:22,239`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean:55`; `src/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean:115` |
| Definitions and `Prop` interfaces read | `SuppOK`, `fLin`, `DeS`, `Hser`, `DerivIs`, `StepII`, `StepH`, `StepIII`, `SwapRules`, `StepIV`; `OddLogRelation`, `IdentityB`, `FrobExprG`; `BetaIsG` | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FirstDeriv.lean:17,21,24,28,33,88,97,108,114,121`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/OddLogRelation.lean:37,44,51`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/IsLawOfLog.lean:98` |
| Named hypotheses retained `[Lean]` | `DworkMv`, `SimeqRules`; `DivDeriv`, `DeIntegral`, `DerivA`, `LemmaOne`, `LemmaTwo`; `LawSymm`, `LamModule`, `StepZero`, `FirstDeriv`, `CobLin`, `StepI`; `Top.dworkMv`, `Top.divDeriv`, `Top.deIntegral`, `Top.lawSymm`, `Top.lemmaTwo`, `Top.zeroCondition`, `Top.stepI`, `Top.simeqRules` | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/CyclicPowerClassOfExpEquiv.lean:13,25`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/IsLawOfLog.lean:50,61,66,73,81`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FirstDeriv.lean:39,51,58,66,74,81`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FinalS.lean:33–59` |
| Mathlib cited `[Lean]` | `MvPowerSeries.pderiv`, `coeff_pderiv`, `pderiv_X_self`, `pderiv_X_of_ne`; `MvPowerSeries.expand`, `expand_C`, `expand_subst`, `coeff_expand_smul`, `constantCoeff_expand`, `coeff_expand_of_not_dvd`; `PowerSeries.derivative`, `coeff_derivative`; `MvPowerSeries.coe_substAlgHom`, `subst_smul`, `constantCoeff_subst`, `constantCoeff_subst_eq_zero`; `IsUltrametricDist.norm_add_le_max` | Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`: `Mathlib/RingTheory/MvPowerSeries/Derivative.lean`, `Mathlib/RingTheory/MvPowerSeries/Expand.lean`, `Mathlib/RingTheory/PowerSeries/Derivative.lean`, `Mathlib/RingTheory/MvPowerSeries/Substitution.lean`, `Mathlib/Analysis/Normed/Group/Ultra.lean` |
| Upstream / sibling inputs unchanged `[Lean]` / `[Open]` | `Top.lawExists`, `witt_teichmuller_root`, `WModel` norm proofs (§8.4.16); `restGc` Witt supply (§8.4.15); `kernel_a_one_generic`, `kernel_a_two_generic`, `kernel_b_generic`, `ea_brScale`, `ea_brNum`, `eb_brJet`, `ea_brClass`, `nm_restNorm_of_place`; `admitted` | as in Sections 8.4.5.1–8.4.16 |


### 8.4.18 Projection and first derivatives for BetaIsG

**Motivation [Expository].** The first two inputs to *BetaIsG_of* select a representative and isolate the singular parts of its two first derivatives. Projection preserves the two additivity defects up to integral exponential. Differentiation on two different coordinate faces turns those hypotheses into ordinary coefficient integrality, which is the input needed in §8.4.17.

**Worked examples [Expository].** Work at $p=5$ over $K_0$ with coefficient ring $W$. Write $\ell$ for the logarithm, $g=g_0$ for its odd partner and $\lambda$ for the compositional inverse of $\ell$. For each scalar $s$ below, take
$$
B_s(x,y)=\sum_{0\le i\le j}
\frac{s x^{25^i}y^{5\cdot25^j}-\sigma(s)x^{5\cdot25^j}y^{25^i}}{5^{i+j+1}},
\qquad \mathrm{be}_s(x,y)=B_s(\lambda(x),\lambda(y)).
$$
Fix a law $F$ as in §8.4.16 and write $d_1$ for its partial additivity defect, defined below. The original coordinate change sends $\mathrm{be}_s$ to $B_s$ exactly. Both triangles have positive exponents, with residues $(1,5)$ and $(5,1)$ modulo $24$, so the projection fixes every coefficient. In positive bidegrees of total degree at most six, congruence gives exactly $(1,5)$ and $(5,1)$: for $b=1,2,3,4,5$ the least positive representative of $5b$ modulo $24$ is respectively $5,10,15,20,1$.

1. **The lowest nonzero block.** For $s=1$ the leading pair is $(xy^5-x^5y)/5$ in both coordinate systems since $\lambda(T)=T+O(T^{25})$. The slice $[x]B_1$ is $g(y)$, with coefficients $1/5$ and $1/25$ at $5$ and $125$. The swapped series is $-B_1$ and its slice is $-g$. The two slice coboundaries are $\delta$ and $-\delta$, where $\delta=\mathrm{cob}_F(g)$ is integral by *DeIntegral*. In particular $[x^4y]\delta=\binom51/5=1$ from the linear part of $F$. After subtracting $\ell'(x)g(y)$ from $\partial_x B_1$, the omitted $i>j$ triangle has coefficients $-5^{i-j-1}$ and the switched $i\le j$ triangle has coefficients $-5^{j-i}$ at their respective differentiated bidegrees. Both exponents are nonnegative. The swapped remainder is the negative. Thus the two derivative scalars are $1,-1$.
2. **A Frobenius twist.** For $s=[\bar a]$ with $\bar a^2=2$ in $\mathbb F_{25}$, $\bar a^5=4\bar a=-\bar a$, so $\sigma(s)=-s$ and $\sigma^2(s)=s$. The leading pair is $s(xy^5+x^5y)/5$ and the swap fixes the series. Both slices are $s g$ with coefficients $s/5$ and $s/25$ at $5$ and $125$. Both coboundaries are $s\delta$, with $[x^4y]s\delta=s$. Subtracting $s\ell'(x)g(y)$ leaves coefficients $-s5^{i-j-1}$ and $s5^{j-i}$ on the respective differentiated triangles. Both derivative scalars are $s$, and $s+\sigma(s)=0$.

For **each** geometric input the four original *BeProp* fields are checked as follows.

- **ab.** Every summand contains both variables, and $\lambda$ has zero constant coefficient.
- **add1 and add2.** In logarithmic variables the defects are $d_1 C$ for $C=B_u$ with $u=s$ and $u=-\sigma(s)$, respectively, up to the cyclic variable permutation for *add2* in Theorem 8.16d. In the two examples these pairs are $(1,-1)$ and $(s,s)$. The all-orders estimate in §8.4.17, Example 1, applies in both orientations since $u\in W$ and $\sigma^2(u)=u$. To record the inputs explicitly, for $\Psi=d_1 C$ the cited identity gives its Dwork difference as
  $$
  5\sigma(u)\delta(x,y)z+\Phi(P,z^5)-\Phi(Q,z^5),
  \qquad \Phi=C^\sigma-\sigma(u)\ell(x)g(y),
  $$
  with $P=F(x^5,y^5)$ and $Q=F(x,y)^5$. Here $P-Q$ is zero-constant and lies in $5W[[x,y]]$. The two triangles of $\partial_x\Phi$ have factors $5^{i-j-1}$ for $i>j$ and $5^{j-i}$ for $i\le j$. The inherited estimate using *DivDeriv* and *DeIntegral* puts the entire difference in $5W[[x,y,z]]$. By *DworkMv* the two exponentials are integral. The geometric defects have zero constant coefficient, and their substituted exponentials minus $1$ give the two Witt witnesses.
- **conj.** The quantifier is over all $\sigma^2$-fixed Witt scalars. Put $U_a(T)=\lambda(a\ell(T))$. If $t$ is a nonzero Teichmüller digit in $W(\mathbb F_{25})$, then $t^{24}=1$ and $U_t=tT$ by the support of $\ell$. Also $U_0=0$. Since $U_{a+b}=F(U_a,U_b)$, finite sums of digits have integral $U_a$. For general $a$ fixed by $\sigma^2$, its Witt digits are in $\mathbb F_{25}$ and $a=\lim_m\sum_{r<m}5^r[t_r]$. For each degree the coefficient of $U_a$ is polynomial in $a$, so the limit remains integral. For any digit $t$, support gives $B_s(tx,y)=B_s(x,t^5y)$ (also for $t=0$). The equivalence
  $$
  B_s(U_a(x),y)\sim B_s(x,U_{\sigma(a)}(y))
  $$
  is closed under addition of scalars: expand both sides for $a+b$ using the two additivity defects and substitute the integral zero-constant $U_a,U_b$ or $U_{\sigma(a)},U_{\sigma(b)}$ into the appropriate defect. Use the equivalence for the two summands and add. Iteration gives the equivalence for each finite digit sum, with $5^r[t_r]$ represented by repeated addition. Each coefficient of the exponential of the difference is a continuous function of $a,\sigma(a)$ by the finite composition formula. The integral bound passes to the limit. This is exactly the geometric *conj* field after $\mathrm{inParam}$; the difference has zero constant coefficient and the exponential minus $1$ is the Witt witness.

In each case the classification returns the scalar $s$ with $\sigma^2(s)=s$ and $\mathrm{inParam}(\mathrm{be}_s)=\mathrm{Gser}(5,s,\sigma s)$. At $5\le p$, the full exponential correction required by the archive is $1$, so the zero series is the witness in the $1+W[[x,y]]$ convention of *RestBeta*.

**Definitions.** Over a characteristic-zero ultrametric normed field $K$, let $\mathcal O=\{a:\lVert a\rVert\le1\}$. Write $H\sim J$ for *G7.Simeq*, meaning $H-J$ has zero constant coefficient and $\exp(H-J)$ has coefficients in $\mathcal O$. Put $N=p^2-1$, $\ell(T)=\sum_{i\ge0}T^{p^{2i}}/p^i$, $g(T)=\sum_{j\ge0}T^{p^{2j+1}}/p^{j+1}$, $G^\tau(x,y)=G(y,x)$ and $f_G(y)=[x]G(x,y)$. Write
$$
d_1G(x,y,z)=G(F(x,y),z)-G(x,z)-G(y,z),
\qquad \mathrm{cob}_F f(x,y)=f(F(x,y))-f(x)-f(y).
$$
*DivAB* requires the coefficients on either axis to vanish. *SuppOK* additionally requires $a\equiv pb\pmod N$ at every nonzero coefficient of $x^ay^b$. *DerivIs* at $c$ means that $\partial_xG-c\ell'(x)g(y)$ is integral.

In *UnrOK*, $p>2$ is prime, $\lVert p\rVert=p^{-1}$, nonzero norms are integer powers of $p$, and the ring endomorphism $\sigma$ satisfies $\lVert\sigma(a)-a^p\rVert\le p^{-1}$ on $\mathcal O$. *IsLawOfLog* specifies an integral $F$ with $F(0,0)=0$ and $\ell(F(x,y))=\ell(x)+\ell(y)$. *BetaHyp* consists of *DivAB*, both defects equivalent to zero, and $B(ux,y)\sim B(x,u^py)$ for all $u^N=1$.

**Lemma 8.18a (StepZero_of) [Lean, read].** Assume *UnrOK* for $K,p,\sigma$, a primitive $N$th root $\zeta\in K$, *IsLawOfLog* for $F$, and the named *LawSymm*, *SimeqRules* and *LamModule*. If $B$ satisfies *BetaHyp*, then there is $G$ with *SuppOK*, $G\sim B$, $d_1G\sim0$ and $d_1(G^\tau)\sim0$. The named *DworkMv* supplies *LamModule*.

*Proof.* Zero constant coefficient of $F$ survives the inclusion into three variables. All three evaluations defining $d_1$ are thus substitution homomorphisms and their difference is $K$-linear. For $u^N=1$, *LawSymm* gives $F(ux,uy)=uF(x,y)$. Comparing the three substituted pairs gives
$$
d_1(H(ux,vy))(x,y,z)=(d_1H)(ux,uy,vz).
$$
Swapping after scaling exchanges $u,v$. For roots of unity the scaling entries are integral because the norm of each root is one, and their constant coefficients vanish.

Finite sums preserve $\sim0$ by *SimeqRules*. The division in this average is permitted by *LamModule_of*. Indeed $p\nmid N$, $\lVert N^{-1}\rVert=1$ and $\sigma(N^{-1})=N^{-1}$. The Dwork difference for $H/N$ is the difference for $H$ divided by $N$, preserving the bound in *DworkMv* and the zero constant coefficient. Take
$$
G(x,y)=N^{-1}\sum_{k=0}^{N-1} B(\zeta^kx,\zeta^{-pk}y).
$$
At $(a,b)$ the multiplier is $N^{-1}\sum_{k=0}^{N-1}(\zeta^{a-pb})^k$. It is $1$ on the congruence class and zero otherwise by the geometric sum. *DivAB* supplies vanishing on the axes. The rotation conjunct of *BetaHyp* at $\zeta^k$, followed by the integral substitution $y\mapsto\zeta^{-pk}y$, makes each summand equivalent to $B$. Average their differences to obtain $G\sim B$. By linearity and covariance the first coboundary is the average of $d_1B$ evaluated at $(\zeta^kx,\zeta^ky,\zeta^{-pk}z)$. The coboundary of the swap is the average of $d_1(B^\tau)$ evaluated at $(\zeta^{-pk}x,\zeta^{-pk}y,\zeta^kz)$. The two original defect hypotheses pass through these integral substitutions and through the average. $\square$

**Lemma 8.18b (FirstDeriv_of and CobLin_of) [Lean, read].** Let $p$ be prime with $\lVert p\rVert=p^{-1}$, and assume *IsLawOfLog*, *LawSymm* and *DivAB* for $G$. If $d_1G\sim0$, then $\partial_xG-\ell'(x)f_G(y)$ is integral. If $d_1(G^\tau)\sim0$, then $\mathrm{cob}_F f_G$ is integral.

*Proof.* The chain rule used here follows from the polynomial product rule. In the source, continuity of the shifted coefficient formula for the derivative and of substitution extends the identity by polynomial density. For zero-constant entries, this extension can be read coefficientwise since each target degree uses only a finite truncation. The auxiliary lemma *integral_lin* starts with $D\sim0$ and an integral zero-constant substitution $b$ with $D(b)=0$. Differentiate to get $\partial_e\exp D=(\exp D)\partial_eD$. On substitution by $b$, the exponential factor is $1$, hence $(\partial_eD)(b)=(\partial_e\exp D)(b)$. Derivatives preserve integrality since their coefficient multipliers are natural integers. Integral zero-constant substitution preserves integrality by the finite coefficient formula.

For $D=d_1G$, take $b=(x,0,z)$. *LawSymm* gives $F(x,0)=x$, and $G(0,z)=0$ by *DivAB*, so $D(b)=0$. Differentiate before restricting:
$$
(\partial_y D)(x,0,z)=(\partial_xG)(x,z)\phi(x)-f_G(z),\qquad
\phi(x)=(\partial_yF)(x,0).
$$
Differentiating the logarithm identity of the law in $y$ and setting $y=0$ gives $\ell'(x)\phi(x)=\ell'(0)=1$. The derivative $\ell'(T)=\sum_{i\ge0}p^i T^{p^{2i}-1}$ is integral. Multiplying the restricted derivative by $\ell'(x)$ proves the first claim.

For $D=d_1(G^\tau)$ take $b=(x,y,0)$. Its terms $G(z,F(x,y)),G(z,x),G(z,y)$ vanish there by *DivAB*. Differentiation in $z$ followed by restriction gives $f_G(F(x,y))-f_G(x)-f_G(y)$, which is integral by the same lemma. All composed pairs have zero constant entries, including the embedded law. The formal proof of *CobLin_of* leaves its *LawSymm* parameter unused. $\square$

**Theorem 8.18c (StepI_of and its two uses in BetaIsG_of) [Lean, read].** Under the assumptions of Lemma 8.18a, also assume completeness of $K$, the named *LemmaOne*, and *SwapRules* of Lemma 8.17a. The projected $G$ admits $c,c'\in\mathcal O$ with *DerivIs* for $(G,c)$ and $(G^\tau,c')$. With the remaining hypotheses of Theorem 8.17f, these same witnesses give $c'=-\sigma(c)$, $\sigma^2(c)=c$ and $B\sim\mathrm{Gser}(p,c,\sigma c)$.

*Proof.* More generally take any $G$ with *SuppOK* and both defects equivalent to zero. *SuppOK* implies *DivAB*. In particular $f_G(0)=0$, and Lemma 8.18b gives the integrality of $\mathrm{cob}_F f_G$. The named *LemmaOne* now writes $f_G=cg+\beta\ell+R$ with $\lVert c\rVert\le1$ and $R$ integral. This call uses completeness. The support of $f_G$ satisfies $1\equiv pj\pmod N$, or $j\equiv p\pmod N$ since $p^2\equiv1$. All exponents of $g$ lie in that class, whereas all exponents of $\ell$ are $1$ modulo $N$. On the class the coefficients of $f_G-cg$ are those of $R$, and off the class the coefficients of $f_G-cg$ are zero. Thus $f_G-cg$ is integral. The identity
$$
\partial_xG-c\ell'(x)g(y)
=\bigl(\partial_xG-\ell'(x)f_G(y)\bigr)+\ell'(x)(f_G(y)-cg(y))
$$
proves *DerivIs*. This is *StepI_of*.

The swap preserves *SuppOK* by $p^2\equiv1\pmod N$ and exchanges the defects since its square is the identity. Apply *StepI_of* again to obtain $c'$. The pair just constructed is passed into the already established *StepII*, *StepH*, *StepIII* and *StepIV* in Theorem 8.17f. Its conclusion for $G$, together with $G\sim B$ and symmetry and transitivity, gives the asserted conclusion for $B$. $\square$

**Remarks.**

1. **Deleting the second direction.** At $p=5$ take $B=\ell(x)y^5/5$ at the *BetaHyp* interface. It has *DivAB*, *SuppOK* and exact rotation symmetry because $25^i\equiv5\cdot5\pmod{24}$. The first defect vanishes. The projection is $B$ but $f_B=y^5/5$. If *DerivIs* held at $c$, its $x^0y^{5\cdot25^j}$ coefficients for every $j\ge1$ would force $c=0$, and its $x^0y^5$ coefficient would then be $1/5$. The failure is already at *StepI*. In the omitted defect $\mathrm{cob}_F(T^5/5)(x,y)\ell(z)$, the first factor has coefficient $1$ at $x^4y$. Hence its Dwork difference at $x^{20}y^5z^5$ has coefficient $1$, as the unexpanded defect has only $z$-exponents $25^i$. *DworkMv* rules out the omitted equivalence. The classification fails directly: in $\exp(B-\mathrm{Gser}(5,c,\sigma c))$ the coefficient of $x^{5\cdot25^j}y$ is $\sigma(c)/5^{j+1}$ since every term in the exponent contains $y$. Integrality for all $j$ forces $c=0$; then the coefficient of $xy^5$ is $1/5$ since every term contains $x$.
2. **Reading boundary.** The new local proof reading covers *LamModule_of*, *StepZero_of*, *FirstDeriv_of*, *CobLin_of* and *StepI_of*. *DworkMv*, *SimeqRules*, *LawSymm*, *LemmaOne* (whose producer `LemmaOne_of` is read in [§8.4.19](#8419-classifying-slice-coboundaries-and-the-lemmaone-supply)), *DivDeriv*, *DeIntegral* and *LemmaTwo* are named inputs. The two examples use §8.4.17's all-degree estimate. See the A2 reading table for the declarations and proof ranges. [A2 source and reading record](../sources/SOURCES.md#chapter-8-8418--projection-and-first-derivatives-for-betaisg)
3. **Classical context.** Serre uses a two-variable Frobenius quotient in §3, p. 419, citing Dwork's 1958 Lemma 1 and noting the Artin–Hasse alternative. Dwork's 1962 paper §4(a), pp. 55–57, uses that exponential to construct splitting functions. The projection and derivative proofs here follow the pinned A2 archive of Levent Alpöge with Claude. The exposition and worked inputs are the book's contribution. [Serre1960](https://www.numdam.org/item/SB_1958-1960__5__415_0/) [Dwork1962](https://www.numdam.org/item/PMIHES_1962__12__5_0/)


### 8.4.19 Classifying slice coboundaries and the LemmaOne supply

**Motivation [Expository].** In [§8.4.18](#8418-projection-and-first-derivatives-for-betaisg), unit-root projection (`StepZero_of`, Lemma 8.18a, cited here without re-proving) replaced an arbitrary `BetaHyp` input $B$ by a series $G$ supported on the congruence locus $n_0\equiv p n_1\pmod{p^2-1}$ (`SuppOK p G`), and zero-face differentiation (`FirstDeriv_of` and `CobLin_of`, Lemma 8.18b, likewise cited without re-proving) extracted from the two exponential-integrality defects $d_1 G\sim 0$ and $d_1(G^\tau)\sim 0$ two ordinary coefficient bounds on the linear slice $f_G(T):=\sum_{j\ge 0}[X_0^1 X_1^j]G\cdot T^j$:
$$\mathrm{Integral}\bigl(\partial_0 G-\ell'(X_0)f_G(X_1)\bigr)\qquad\text{and}\qquad\mathrm{Integral}\bigl(\mathrm{cob}_F(f_G)\bigr).$$
To convert the first bound into `DerivIs p G c` ($\partial_0 G-c\,\ell'(X_0)g_0(X_1)$ integral with $\lVert c\rVert\le 1$), Theorem 8.18c (`StepI_of`) invoked a single named classification theorem on one-variable formal power series, `Top.lemmaOne : LemmaOne := LemmaOne_of deIntegral lawSymm` (`src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FinalS.lean:48` — the `UniformThetaSubstitution` assembly file, distinct from the unrelated `FinalS.lean` wrappers in `CompanionTheory/AutomorphicTheory/CompactTopologicalForms/FinalS.lean` and `DenseThresholdCases/FinalS.lean` and from the `HermitianCurvatureProofs` Fourier-decay files). This subsection opens `LemmaOne_of` and reads in full its 540-line proof body in `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean:1–540` together with its ultrametric integer-norm suppliers, while keeping `DeIntegral`, `LawSymm`, `LemmaTwo`, `DworkMv`, and `DivDeriv` as named `[Lean]` hypotheses.

Why must any zero-constant series $f\in K[[T]]$ whose formal-group coboundary $\mathrm{cob}_F(f)(X_0,X_1)=f(F(X_0,X_1))-f(X_0)-f(X_1)$ has integral coefficients decompose as
$$f=\alpha\,g_0+\beta\,\ell+R\qquad\bigl(\lVert\alpha\rVert\le 1,\ R\text{ integral}\bigr),$$
where $\ell(T)=\sum_{j\ge 0}p^{-j}T^{p^{2j}}$ and $g_0(T)=\sum_{j\ge 0}p^{-(j+1)}T^{p^{2j+1}}$, and why do the scalar bound $\lVert\alpha\rVert\le 1$, the *absence* of any norm bound on $\beta$, completeness of $K$, and $f(0)=0$ enter in the exact places they do? Because $F(X_0,X_1)=X_0+X_1+O(\deg 2)$ is integral, once all coefficients $h_d$ of a remainder $h$ below degree $n\ge 2$ are integral, the top-degree contribution of $h_n T^n$ to $[X_0^i X_1^{n-i}]\mathrm{cob}_F(h)$ ($0<i<n$) is $\binom{n}{i}h_n$ modulo integral lower-degree terms. By Lazard's classical binomial dichotomy (`[Lazard1955]`, §II–III, pp. 256–262), two cases occur:

1. *Non-prime-power degrees ($n\neq p^k$): automatic integrality (`low_up`).* Writing $n=p^k m$ with $p\nmid m$ and $m\ge 2$, Lucas's congruence gives $p\nmid\binom{p^k m}{p^k}$, so $\bigl\lVert\binom{n}{p^k}\bigr\rVert=1$ and $\lVert h_n\rVert\le 1$ immediately. No denominator can ever first appear strictly between consecutive powers of $p$.
2. *Prime-power degrees ($n=p^{k+1}$): alternating $g_0$/$\ell$ cancellation (`correct`, `good_succ`, `exists_limit`).* At $n=p^{k+1}$ every interior binomial coefficient is divisible by $p$, while $v_p\bigl(\binom{p^{k+1}}{p^k}\bigr)=1$ gives $\lVert p\,h_{p^{k+1}}\rVert\le 1$ (at worst a single factor of $p^{-1}$). At odd prime powers $p^{2j+1}$ ($k=2j$), $g_0$ has coefficient $p^{-(j+1)}$, so subtracting $(\mu_j p^j)g_0$ with $\mu_j:=p\,h_{p^{2j+1}}$ ($\lVert\mu_j\rVert\le 1$) kills $T^{p^{2j+1}}$ while preserving `Integral (cob F ·)` via `DeIntegral` because $\lVert a_j\rVert\le 1$; at even prime powers $p^{2j+2}$ ($k=2j+1$), $\ell$ has coefficient $p^{-(j+1)}$, so subtracting $(\nu_j p^j)\ell$ with $\nu_j:=p\,h'_{p^{2j+2}}$ ($\lVert\nu_j\rVert\le 1$) kills $T^{p^{2j+2}}$ while preserving `Integral (cob F ·)` unconditionally because $\mathrm{cob}_F(\ell)=0$. Each subtraction alters higher prime-power coefficients, so $(a_j,b_j)$ must be driven to $j\to\infty$; completeness of $K$ turns $\lVert a_{j+1}-a_j\rVert,\lVert b_{j+1}-b_j\rVert\le p^{-j}$ into limits $(\alpha,\beta)$ with $\lVert\alpha\rVert\le 1$ (whereas $b_0=[T^1]f$ starts unrestricted, leaving $\beta$ unbounded), and in `StepI_of` congruence support modulo $p^2-1$ deletes $\beta\,\ell$ without ever needing a bound on $\beta$.

**Worked examples [Expository].** Fix $p=5$ ($N=p^2-1=24$), work over $K_0=\mathrm{Frac}\,W(\overline{\mathbb F}_5)$ with Frobenius $\sigma=\sigma_K$ (or $\mathbb Q_5$ in Example 3(a)), and fix $F$ satisfying `IsLawOfLog 5 F`. Both calculations below run the actual two-step recurrence $(a_j,b_j)$ of `LemOne.exists_limit` (`NotDvdChoosePowMul.lean:403–524`) across *all* stages $j\ge 0$ without finite truncation.

1. **A nonzero Frobenius-twisted scalar at $p=5$: non-terminating odd-power approximation and return to `StepI_of`.** Choose $\bar\alpha\in\mathbb F_{25}\setminus\mathbb F_5$ with $\bar\alpha^2=2$ and set $s:=[\bar\alpha]\in W(\mathbb F_{25})^\times$, so $\lVert s\rVert=1$, $\sigma(s)=[\bar\alpha^5]=[4\bar\alpha]=-s\neq s$, and $\sigma^2(s)=s$. Consider the two-variable series
   $$G_{\mathrm{tw}}(X_0,X_1):=\mathrm{Gser}(5,s,-s)+H_{\mathrm{int}}(X_0,X_1),\qquad H_{\mathrm{int}}(X_0,X_1):=5s\sum_{m=0}^\infty X_0 X_1^{5^{2m+1}}.$$
   - *All-orders check of the `StepI` hypotheses.* Every monomial of $H_{\mathrm{int}}$ has bidegree $(1,5^{2m+1})$ with $1\ge 1$, $5^{2m+1}\ge 1$, and $1\equiv 25^{m+1}=5\cdot 5^{2m+1}\pmod{24}$; combined with $\mathrm{Gser}(5,s,-s)$ ([§8.4.17](#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar), Example 1), `SuppOK 5 G_tw` holds identically. Because $F\in W[[X_0,X_1]]$ has $F(0,0)=0$ and $H_{\mathrm{int}}\in 5W[[X_0,X_1]]$ has $H_{\mathrm{int}}(0,0)=0$, both $d_1 F\,H_{\mathrm{int}}$ and $d_1 F\,(H_{\mathrm{int}}^\tau)$ lie in $5W[[X_0,X_1,X_2]]$ with zero constant term; for every $k\ge 1$, $v_5(5^k/k!)=k-v_5(k!)>k-k/4>0$ (equivalently by `ExpIntegral` or `DworkMv`), so $\exp(d_1 F\,H_{\mathrm{int}})$ and $\exp(d_1 F\,(H_{\mathrm{int}}^\tau))$ are $W$-integral across all bidegrees, and `SimeqRules` adds them to $d_1 F\,\mathrm{Gser}(5,s,-s)\sim 0$ and $d_1 F\,(\mathrm{Gser}(5,s,-s)^\tau)\sim 0$ to establish $d_1 F\,G_{\mathrm{tw}}\sim 0$ and $d_1 F\,(G_{\mathrm{tw}}^\tau)\sim 0$.
   - *Closed-form run of `LemOne` across all $j\ge 0$.* The slice $f_{\mathrm{tw}}(T):=[X_0^1]G_{\mathrm{tw}}=s\,g_0(T)+5s\sum_{m=0}^\infty T^{5^{2m+1}}$ satisfies $f_{\mathrm{tw}}(0)=0$, and Lemma 8.18b (`CobLin_of`) supplies `Integral (cob F f_tw)` (directly, $\mathrm{cob}_F(f_{\mathrm{tw}})=s\,\mathrm{cob}_F(g_0)+5s\sum_{m\ge 0}(F^{5^{2m+1}}-X_0^{5^{2m+1}}-X_1^{5^{2m+1}})$ is integral by `DeIntegral` and `Integral F`). At $j=0$, `good_zero` sets $(a_0,b_0)=(0,[T^1]f_{\mathrm{tw}})=(0,0)$. At $j=0\to 1$, $[T^5]\mathrm{rem}_5(f_{\mathrm{tw}},0,0)=s\bigl(\frac15+5\bigr)=\frac{26}{5}s$, so `good_succ` forms
     $$\mu_0=5\cdot\frac{26}{5}s=26s=(1+5^2)s\quad(\lVert\mu_0\rVert=1),\qquad a_1=26s,\qquad \nu_0=0,\qquad b_1=0.$$
     Notice why the process does not terminate at $j=1$: stage $0$ absorbs the integral $5s T^5$ piece into $a_1$, overshooting $s$ by $+25s$ and creating new denominators $-25s\cdot 5^{-(m+1)}$ in $r_1(T)$ for $m\ge 2$ (starting with $+\frac{24}{5}s\,T^{3125}$ at $m=2$). By induction on $j\ge 1$, the `good_succ` state is
     $$a_j=\bigl(1+5^{j+1}\bigr)s,\qquad b_j=0,\qquad r_j(T):=\mathrm{rem}_5(f_{\mathrm{tw}},a_j,0)=\sum_{m=0}^\infty s\bigl(5-5^{j-m}\bigr)T^{5^{2m+1}}.$$
     Indeed, for $m<j$ ($d=5^{2m+1}<5^{2j+1}$), $j-m\ge 1$ puts $s(5-5^{j-m})\in 5W$ of norm $\le 5^{-1}\le 1$ (`Good` holds); at $m=j$ ($d=5^{2j+1}$), $[T^{5^{2j+1}}]r_j=s(5-5^0)=4s$ (while $m=j+1$ still carries the non-integral pole $\frac{24}{5}s$), giving $\mu_j=5\cdot(4s)=20s$ ($\lVert\mu_j\rVert=5^{-1}\le 1$), $a_{j+1}=\bigl(1+5^{j+1}\bigr)s+20s\cdot 5^j=\bigl(1+5^{j+2}\bigr)s$ with $\lVert a_{j+1}-a_j\rVert=5^{-(j+1)}\le 5^{-j}$, and $\nu_j=0$, $b_{j+1}=0$ since $r_j^{(1)}$ vanishes on all even powers $T^{5^{2m}}$. Passing to the $5$-adic limit in $K_0$ gives $\alpha=\lim_{j\to\infty}(1+5^{j+1})s=s\in W(\mathbb F_{25})^\times$ ($\sigma(\alpha)=-\alpha\neq\alpha$), $\beta=0$, and the integral remainder $R_{\mathrm{tw}}(T)=5s\sum_{m=0}^\infty T^{5^{2m+1}}\in 5W[[T]]$.
   - *Return to `StepI_of` and `BetaIsG_of`.* `StepI_of` (`ConstantCoeffLawFirstTwoOfThree.lean:426–474`) multiplies $f_{\mathrm{tw}}(X_1)-s\,g_0(X_1)=R_{\mathrm{tw}}(X_1)$ by the integral series $\ell'(X_0)$ and adds it to the integral series $\partial_0 G_{\mathrm{tw}}-\ell'(X_0)f_{\mathrm{tw}}(X_1)=\bigl(\partial_0\mathrm{Gser}(5,s,-s)-s\ell'(X_0)g_0(X_1)\bigr)+\bigl(1-\ell'(X_0)\bigr)R_{\mathrm{tw}}(X_1)$ (supplied by `FirstDeriv_of`); cancelling $-\ell'(X_0)R_{\mathrm{tw}}(X_1)$ leaves $\bigl(\partial_0\mathrm{Gser}(5,s,-s)-s\ell'(X_0)g_0(X_1)\bigr)+R_{\mathrm{tw}}(X_1)\in W[[X_0,X_1]]$, certifying `DerivIs 5 G_tw s`. On the swapped series $G_{\mathrm{tw}}^\tau=\mathrm{Gser}(5,s,-s)+5s\sum_{m\ge 0}X_0^{5^{2m+1}}X_1$, every summand $X_0^{5^{2m+1}}X_1$ has $X_0$-degree $5^{2m+1}\ge 5>1$, so $[X_0^1](G_{\mathrm{tw}}^\tau)=s\,g_0(T)$ (`StepI_of` yields $c'=s=-\sigma(s)$), and `BetaIsG_of` locks $s+\sigma(s)=0$ and $G_{\mathrm{tw}}\sim\mathrm{Gser}(5,s,\sigma s)$.

2. **Coexisting integral remainder $R$ and unbounded $\beta\,\ell$ across all orders ($p=5$).** Consider the one-variable series
   $$f_{\mathrm{mix}}(T):=g_0(T)+\frac{1}{5}\,\ell(T)+R_0(T),\qquad R_0(T):=T^2+T^6+\sum_{m=1}^\infty T^{5^{2m}}\in\mathbb Z[[T]].$$
   - *All-orders check of $f_{\mathrm{mix}}(0)=0$ and `Integral (cob F f_mix)`, plus degree-$25$ cancellation.* Clearly $f_{\mathrm{mix}}(0)=0$. Since $F(0,0)=0$ and $\mathrm{cob}_F(\ell)=0$, linearity of $\mathrm{cob}_F$ (`cob_comb`, `:362–373`) gives
     $$\mathrm{cob}_F(f_{\mathrm{mix}})=\mathrm{cob}_F(g_0)+\frac{1}{5}\underbrace{\mathrm{cob}_F(\ell)}_{=\,0}+\mathrm{cob}_F(R_0)=\mathrm{cob}_F(g_0)+\bigl(F^2-X_0^2-X_1^2\bigr)+\bigl(F^6-X_0^6-X_1^6\bigr)+\sum_{m=1}^\infty\bigl(F^{5^{2m}}-X_0^{5^{2m}}-X_1^{5^{2m}}\bigr).$$
     Here $\mathrm{cob}_F(g_0)$ is integral by `DeIntegral`, and because $F$ is integral with $F(0,0)=0$, each summand $F^d-X_0^d-X_1^d$ is integral of order $\ge d$, so the infinite sum converges coefficientwise to an integral series (`coeff_subst`). It is instructive to watch why $\frac15\ell(T)$ — which has coefficient $\frac1{25}$ at $T^{25}$ and norm $\lVert\frac15\rVert=5>1$ at $T^1$ — creates no $5$-adic pole in $\mathrm{cob}_F(f_{\mathrm{mix}})$: from $\ell(T)=T+\frac15 T^{25}+O(T^{625})$ and $\ell(F)=\ell(X_0)+\ell(X_1)$, the law expands as $F(X_0,X_1)=X_0+X_1-\frac15\bigl((X_0+X_1)^{25}-X_0^{25}-X_1^{25}\bigr)+O(\deg 49)$. At bidegree $(5,20)$, $[X_0^5 X_1^{20}]F=-\frac15\binom{25}{5}=-\frac{53130}{5}=-10626\in\mathbb Z$, so in $\mathrm{cob}_F(\frac15\ell)$ the $d=1$ term $\frac15\cdot(-10626)=-\frac{10626}{5}$ cancels the $d=25$ term $\frac1{25}\binom{25}{5}=+\frac{10626}{5}$ to $0$, leaving $[X_0^5 X_1^{20}]\mathrm{cob}_F(f_{\mathrm{mix}})=[X_0^5 X_1^{20}]\mathrm{cob}_F(g_0)+\binom{25}{5}\in W$.
   - *Binomial witnesses and closed-form run of `LemOne` across all $j\ge 0$.* At $j=0$, `good_zero` sets $a_0=0$ and $b_0=[T^1]f_{\mathrm{mix}}=\frac15$ (so $\lVert b_0\rVert=5>1$, permitted because `Good` bounds only $\lVert a_j\rVert\le 1$), leaving $r_0(T)=g_0(T)+R_0(T)$ with $[T^0]r_0=[T^1]r_0=0$. Between prime powers, `exists_not_dvd_choose` tests non-prime-power degrees via unit binomial coefficients: at $d=2=5^0\cdot 2$ ($i=1$, $\binom{2}{1}=2$, $\lVert 2\rVert=1$) we read $[X_0 X_1]\mathrm{cob}_F(r_0)=2[T^2]r_0=2$; after subtracting $a_1 g_0$ with $\mu_0=5\cdot[T^5]r_0=1$ ($a_1=1$), `low_up` on $5<d<25$ tests $d=6=5^0\cdot 6$ ($i=1$, $\binom{6}{1}=6\equiv 1\pmod 5$) and $d=10=5^1\cdot 2$ ($i=5$, where Lucas's congruence gives $\binom{10}{5}=252\equiv\binom{2}{1}=2\not\equiv 0\pmod 5$, $\lVert 252\rVert=1$). At the even prime power $d=25=5^2$, $r_0^{(1)}(T)=R_0(T)$ has $[T^{25}]r_0^{(1)}=1$, so `good_succ` computes $\nu_0=5\cdot 1=5$ ($\lVert\nu_0\rVert=5^{-1}\le 1$) and $b_1=\frac15+5=\frac{26}{5}$, absorbing $T^{25}$ into $\ell$ at the cost of shifting every higher $T^{5^{2m}}$ ($m\ge 1$) by $-5\cdot 5^{-m}$. By induction on $j\ge 1$,
     $$a_j=1,\qquad b_j=\frac{1}{5}+5^j,\qquad r_j(T)=\mathrm{rem}_5(f_{\mathrm{mix}},a_j,b_j)=-5^j T+T^2+T^6+\sum_{m=1}^\infty\bigl(1-5^{j-m}\bigr)T^{5^{2m}}.$$
     Indeed, $r_j$ vanishes on all odd prime powers $T^{5^{2m+1}}$ (so $\mu_j=0$ and $a_{j+1}=1$), satisfies $\lVert 1-5^{j-m}\rVert\le 1$ for $1\le m\le j$ (`Good` holds up to $5^{2j+1}$), and at $m=j+1$ ($d=5^{2j+2}$) has $[T^{5^{2j+2}}]r_j=1-5^{-1}=\frac45$, yielding $\nu_j=5\cdot\frac45=4$ ($\lVert\nu_j\rVert=1$) and $b_{j+1}=\bigl(\frac15+5^j\bigr)+4\cdot 5^j=\frac15+5^{j+1}$ with $\lVert b_{j+1}-b_j\rVert=5^{-j}$. In the $5$-adic limit, $5^j\to 0$ gives
     $$\alpha=1\quad(\lVert\alpha\rVert=1),\qquad \beta=\lim_{j\to\infty}\Bigl(\frac{1}{5}+5^j\Bigr)=\frac{1}{5}\quad(\lVert\beta\rVert=5>1),\qquad R(T)=R_0(T)\in\mathbb Z[[T]],$$
     exhibiting an all-orders decomposition in which $\alpha g_0$, a non-integral $\beta\,\ell$, and a full integral remainder $R$ with both non-prime-power ($T^2,T^6$) and prime-power ($T^{5^{2m}}$) terms all coexist.

3. **Deleting an antecedent: actual failure without `[CompleteSpace K]` in `LemmaOne` and without `SuppOK` in `StepI_of`.**
   - *(a) Dropping completeness `[CompleteSpace K]` in `LemmaOne` ($p=5$, $K=(\mathbb Q,\lVert\cdot\rVert_5)$, $\sigma=\mathrm{id}_{\mathbb Q}$).* Equip $K=\mathbb Q$ with the $5$-adic absolute value $\lVert\cdot\rVert_5$ ($\lVert 5\rVert_5=5^{-1}$). Every conjunct of `UnrOK ℚ 5 id` holds unconditionally: $5>2$ is prime, $\lVert 5\rVert_5=5^{-1}$, $\lVert q\rVert_5\in 5^{\mathbb Z}$ for $q\in\mathbb Q^\times$, and for $a\in\mathbb Q$ with $\lVert a\rVert_5\le 1$ ($a\in\mathbb Z_{(5)}$), Fermat's little theorem gives $a^5\equiv a\pmod{5\mathbb Z_{(5)}}$, i.e. $\lVert\mathrm{id}(a)-a^5\rVert_5\le 5^{-1}$. Since $\ell(T)=T+\sum_{j\ge 1}5^{-j}T^{25^j}\in\mathbb Q[[T]]$ has formal compositional inverse $\lambda(T)\in\mathbb Q[[T]]$, the rational series $F(X_0,X_1):=\lambda(\ell(X_0)+\ell(X_1))\in\mathbb Q[[X_0,X_1]]$ satisfies $F(0,0)=0$ and $\mathrm{cob}_F(\ell)=0$; under the isometric embedding $(\mathbb Q,\lVert\cdot\rVert_5)\hookrightarrow\mathbb Q_5$, the uniqueness clause of the named `LawExists` (`IsLawOfLog.lean:47–49`) identifies $F$ with the integral law over $\mathbb Q_5$, so `IsLawOfLog 5 F` holds over $(\mathbb Q,\lVert\cdot\rVert_5)$ as well. Now let $w\in\mathbb Z_5\setminus\mathbb Q$ be the $5$-adic square root of $-1$ congruent to $2\pmod 5$ ($w^2=-1$, so $w\notin\mathbb Q$; its rational Hensel partial sums $s_0=2,s_1=7,s_2=57,s_3=182,\dots\in\mathbb Z$ satisfy $s_j^2\equiv -1\pmod{5^{j+1}}$ and $\lVert s_j-w\rVert_5\le 5^{-(j+1)}$), and define
     $$f_{\mathbb Q}(T):=\sum_{j=0}^\infty\frac{s_j}{5^{j+1}}T^{5^{2j+1}}\in\mathbb Q[[T]].$$
     Then $f_{\mathbb Q}(0)=0$, and over $\mathbb Q_5$ we have $f_{\mathbb Q}-w\,g_0=\sum_{j\ge 0}\frac{s_j-w}{5^{j+1}}T^{5^{2j+1}}=:R_w\in\mathbb Z_5[[T]]$ with $R_w(0)=0$. Hence in $\mathbb Q_5[[X_0,X_1]]$ (and therefore in $(\mathbb Q,\lVert\cdot\rVert_5)$ by isometry), $\mathrm{cob}_F(f_{\mathbb Q})=w\,\mathrm{cob}_F(g_0)+\mathrm{cob}_F(R_w)$ is $5$-adically integral by the named `DeIntegral` over $\mathbb Q_5$ and `Integral F`. Yet **no** $(\alpha,\beta,R)\in\mathbb Q\times\mathbb Q\times\mathbb Q[[T]]$ with $\forall n,\ \lVert[T^n]R\rVert_5\le 1$ satisfies $f_{\mathbb Q}=\alpha g_0+\beta\ell+R$: reading $[T^{5^{2j+1}}]$ (where $\ell$ vanishes) yields $\lVert(s_j-\alpha)/5^{j+1}\rVert_5\le 1$, so $\lVert\alpha-s_j\rVert_5\le 5^{-(j+1)}$ and $\lVert\alpha-w\rVert_5\le\max(\lVert\alpha-s_j\rVert_5,\lVert s_j-w\rVert_5)\le 5^{-(j+1)}$ for all $j\ge 0$, forcing $\alpha=w\notin\mathbb Q$.
   - *(b) Dropping `SuppOK p G` in `StepI_of` ($G_{\mathrm{bad}}(X_0,X_1):=\ell(X_0)\ell(X_1)$, unconditional).* At $p=5$ over any complete $(K,\sigma)$ with `UnrOK K 5 σ` and `IsLawOfLog 5 F`, $G_{\mathrm{bad}}=\ell(X_0)\ell(X_1)$ satisfies `DivAB G_bad`, $G_{\mathrm{bad}}^\tau=G_{\mathrm{bad}}$, and $d_1 F\,G_{\mathrm{bad}}=\mathrm{in3}(\mathrm{cob}_F(\ell))\,\ell(X_2)=0$ identically, so both $d_1 F\,G_{\mathrm{bad}}\sim 0$ and $d_1 F\,(G_{\mathrm{bad}}^\tau)\sim 0$ hold without calling `DworkMv`; only `SuppOK 5 G_bad` fails (at $(1,1)$, $1\not\equiv 5\pmod{24}$). Its slice $f_{G_{\mathrm{bad}}}(T)=\ell(T)$ satisfies `LemmaOne` with $(\alpha,\beta,R)=(0,1,0)$, leaving $\beta=1\neq 0$ unkilled, and for *every* $c\in K$ the series $\partial_0 G_{\mathrm{bad}}-c\,\ell'(X_0)g_0(X_1)=\ell'(X_0)\bigl(\ell(X_1)-c\,g_0(X_1)\bigr)$ has $(0,5^{2j})$-coefficient $5^{-j}$ of norm $5^j\to\infty$ ($j\ge 1$), so `DerivIs 5 G_bad c` fails.

**Definitions and exact declaration check [Lean, read].** Work in namespace `Formalism.InvariantFactorPaths.G7`. Recall from `IsLawOfLog.lean:13–42` and `OddLogRelation.lean:13–33` that $\ell=\mathtt{lgF}\;K\;p$, $g_0=\mathtt{g0F}\;K\;p$, $\mathrm{cob}_F(f)=f(F(X_0,X_1))-f(X_0)-f(X_1)$, `IsLawOfLog p F` means $F(0,0)=0$, `Integral F`, and $\mathrm{cob}_F(\ell)=0$, and `UnrOK K p σ` packages `p.Prime`, $2<p$, $\lVert(p:K)\rVert=p^{-1}$, discrete $p^{\mathbb Z}$ norms on $K^\times$, and $\lVert\sigma(a)-a^p\rVert\le p^{-1}$ on $\lVert a\rVert\le 1$.

1. *The classification interface `LemmaOne` (`IsLawOfLog.lean:73–80`) and wrapper `Top.lemmaOne` (`FinalS.lean:48`).* `LemmaOne` states that for every complete ultrametric characteristic-zero normed field $K$, $(p,\sigma)$ with `UnrOK K p σ`, $F$ with `IsLawOfLog p F`, and $f\in K[[T]]$ with $f(0)=0$ (`PowerSeries.constantCoeff f = 0`) and `Integral (cob F f)`, there exist $\alpha,\beta\in K$ and $R\in K[[T]]$ such that
   $$\lVert\alpha\rVert\le 1,\qquad\forall n\in\mathbb N,\ \bigl\lVert[T^n]R\bigr\rVert\le 1,\qquad\text{and}\qquad f=\alpha\,g_0+\beta\,\ell+R.$$
   In `FinalS.lean:48`, `Top.lemmaOne : LemmaOne := LemmaOne_of deIntegral lawSymm` supplies this interface to `Top.stepI := StepI_of lemmaOne firstDeriv cobLin` (`:54`) and `Top.lemmaTwo := LemmaTwo_of lemmaOne lawSymm` (`:49`, retained at `[Lean]`).
2. *Remainder series and two-step inductive invariant (`NotDvdChoosePowMul.lean:380–402`).* For $f\in K[[T]]$ and $a,b\in K$, `LemOne` defines
   $$\mathrm{rem}_p(f,a,b):=f-a\,g_0-b\,\ell\in K[[T]],$$
   and for $j\in\mathbb N$, `LemOne.Good p f j a b` holds iff $\lVert a\rVert\le 1$ and $\bigl\lVert[T^d]\mathrm{rem}_p(f,a,b)\bigr\rVert\le 1$ for all $d<p^{2j+1}$. Note that in `LemmaOne_of` (`:529–539`), `obtain ⟨hp, -, hnp, -, hσ⟩ := hU` discards *both* $2<p$ and the discrete-valuation clause of `UnrOK`, passes $(\sigma,h_\sigma)$ solely to `hDe : DeIntegral` to obtain `hde : Integral (cob F (g0F K p))` (`:532`), projects only the linear-term clause `hF1 : ∀ n, n.degree = 1 → coeff n F = 1` from `hL : LawSymm` (`:533`), and runs `LemOne.exists_limit` for any prime $p$.

**Lemma 8.19a (Lazard's binomial dichotomy, ultrametric integer norms, and top-degree coefficients of $F^n$) [Lean, read].**

1. *(`LemOne.not_dvd_choose_pow_mul`, `exists_not_dvd_choose`, `padicValNat_choose_pow`, `NotDvdChoosePowMul.lean:16–57`) Let $p$ be prime. If $p\nmid m$, then $p\nmid\binom{p^k m}{p^k}$ for every $k\in\mathbb N$; consequently, if $n\ge 2$ satisfies $\forall k,\ n\neq p^k$, there exists $i$ with $0<i<n$ and $p\nmid\binom{n}{i}$. At prime powers, $v_p\bigl(\binom{p^{k+1}}{p^k}\bigr)=1$ for every $k\in\mathbb N$.*
2. *(`norm_natCast_eq_one_of_not_dvd`, `NormNatCastEqOneOfNotDvd.lean:7–28` and `NormNatCastEqPowPadicValNat.lean:17–20`; `norm_natCast_eq_pow_padicValNat`, `:21–29`) Over an ultrametric normed field $K$, if $p$ is prime and $\lVert(p:K)\rVert<1$, then $p\nmid m$ implies $\lVert(m:K)\rVert=1$, and $n\neq 0$ implies $\lVert(n:K)\rVert=\lVert(p:K)\rVert^{v_p(n)}$.*
3. *(`LemOne.integral_mul`, `integral_pow`, `order_sub_lin`, `order_pow_sub_lin`, `coeff_lin_pow`, `coeff_pow_top`, `NotDvdChoosePowMul.lean:62–184`) Over an ultrametric normed field $K$, `Integral` is closed under multiplication and natural powers. Over any field $K$, if $F\in K[[X_0,X_1]]$ satisfies $F(0,0)=0$ and $[X^d]F=1$ whenever $\deg(d)=1$, then $\mathrm{ord}\bigl(F-(X_0+X_1)\bigr)\ge 2$, $\mathrm{ord}\bigl(F^n-(X_0+X_1)^n\bigr)\ge n+1$ for all $n\in\mathbb N$, and $[X_0^i X_1^{n-i}](F^n)=\binom{n}{i}$ for $0\le i\le n$.*

*Proof.* (1) Induct on $k$ (`:19–36`). For $k=0$, $\binom{m}{1}=m$ is not divisible by $p$. For $k+1$, Lucas's theorem (`Choose.choose_modEq_choose_mod_mul_choose_div_nat`) gives $\binom{p^{k+1}m}{p^{k+1}}\equiv\binom{0}{0}\binom{p^k m}{p^k}=\binom{p^k m}{p^k}\pmod p$ since $p\mid p^{k+1}m$ and $p\mid p^{k+1}$, carrying non-divisibility from $k$ to $k+1$. If $n\ge 2$ is not a power of $p$ (`:37–46`), factor $n=p^k m$ with $p\nmid m$ (`Nat.exists_eq_pow_mul_and_not_dvd`); then $m\neq 0$ (else $p\mid 0$) and $m\neq 1$ (else $n=p^k$), so $m\ge 2$, giving $0<p^k<p^k m=n$ and $p\nmid\binom{n}{p^k}$. For $n=p^{k+1}$ (`:47–57`), `Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity` at $p^k\le p^{k+1}$ gives $v_p\binom{p^{k+1}}{p^k}+v_p(p^k)=k+1$, and $v_p(p^k)=k$ (`padicValNat.prime_pow`) leaves $v_p\binom{p^{k+1}}{p^k}=1$.

(2) By the ultrametric triangle inequality, $\lVert(m:K)\rVert\le 1$ (`norm_natCast_le_one`, `NormNatCastEqOneOfNotDvd.lean:10`). If $\lVert(m:K)\rVert<1$, coprimality of $p$ and $m$ (`:13–14`) supplies $a,b\in\mathbb Z$ with $ap+bm=1$; casting into $K$ and using $\lVert(c:K)\rVert\le 1$ for $c\in\mathbb Z$ (`:18–24`) gives $1=\lVert ap+bm\rVert\le\max(\lVert a\rVert\lVert p\rVert,\lVert b\rVert\lVert m\rVert)<1$, a contradiction (`:25–27`). For $n\neq 0$ (`NormNatCastEqPowPadicValNat.lean:21–29`), factoring $n=p^{v_p(n)}m$ with $p\nmid m$ (`ordProj_mul_ordCompl_eq_self`, `not_dvd_ordCompl`) and taking norms yields $\lVert(n:K)\rVert=\lVert(p:K)\rVert^{v_p(n)}\cdot 1$.

(3) In $[X^n](f g)=\sum_{u+v=n}f_u g_v$, ultrametric subadditivity and $\lVert f_u\rVert\lVert g_v\rVert\le 1$ give `integral_mul` (`:62–70`), and induction on $d$ gives `integral_pow` (`:71–80`). Next, $F-(X_0+X_1)$ vanishes at $d=0$ by $F(0,0)=0$ and at $d=(1,0),(0,1)$ because $[X^d]F=1=[X^d](X_0+X_1)$, so `nat_le_order` gives $\mathrm{ord}(F-L)\ge 2$ for $L:=X_0+X_1$ (`:87–126`). Inducting on $n$ via $F^{n+1}-L^{n+1}=F(F^n-L^n)+(F-L)L^n$ (`:133–136`), $\mathrm{ord}(F)\ge 1$ and $\mathrm{ord}(F^n-L^n)\ge n+1$ bound the first product below by $n+2$, while $\mathrm{ord}(F-L)\ge 2$ and $\mathrm{ord}(L^n)\ge n$ bound the second below by $n+2$, so `min_order_le_add` gives $\mathrm{ord}(F^{n+1}-L^{n+1})\ge n+2$ (`:138–149`). Since $(i,n-i)$ has total degree $n<n+1$, $[X_0^i X_1^{n-i}](F^n-L^n)=0$ (`coeff_of_lt_order`, `:178–183`), and the binomial expansion of $L^n$ isolates $\binom{n}{i}$ (`:154–173`). $\square$

**Lemma 8.19b (Coboundary bootstrap `low_up` and model-series cancellation `correct`) [Lean, read].** *Let $K$ be a characteristic-zero ultrametric normed field, $p$ a prime with $\lVert(p:K)\rVert=p^{-1}$, and $F\in K[[X_0,X_1]]$ an integral zero-constant series with $[X^d]F=1$ for $\deg(d)=1$.*

1. *(`norm_coeff_mul_choose`, `norm_coeff_of_not_pow`, `norm_coeff_of_pow`, `low_up`, `NotDvdChoosePowMul.lean:195–296`) Let $h\in K[[T]]$ satisfy `Integral (cob F h)`. If $\lVert h_d\rVert\le 1$ for all $d<n$, then $\bigl\lVert h_n\binom{n}{i}\bigr\rVert\le 1$ for every $0<i<n$. Consequently:*
   - *if $n\ge 2$ is not a power of $p$ and $\lVert h_d\rVert\le 1$ for all $d<n$, then $\lVert h_n\rVert\le 1$; hence $\forall d\le p^k,\ \lVert h_d\rVert\le 1$ implies $\forall d<p^{k+1},\ \lVert h_d\rVert\le 1$ (`low_up`);*
   - *if $\lVert h_d\rVert\le 1$ for all $d<p^{k+1}$, then $\bigl\lVert p\,h_{p^{k+1}}\bigr\rVert\le 1$ (`norm_coeff_of_pow`).*
2. *(`correct`, `g_zero_low_coeff_norm`, `lg_low`, `cob_comb`, `:297–373`) Suppose $h,\psi,h'\in K[[T]]$ satisfy `Integral (cob F h)`, $\lVert h_d\rVert\le 1$ for $d<p^{k+1}$, $\lVert p^j\psi_d\rVert\le 1$ for $d<p^{k+1}$, $\psi_{p^{k+1}}=p^{-(j+1)}$, $h'=h-(p\,h_{p^{k+1}}p^j)\psi$, and `Integral (cob F h')`. Then $\lVert p\,h_{p^{k+1}}\rVert\le 1$ and $\lVert h'_d\rVert\le 1$ for all $d<p^{k+2}$. Moreover, $\psi=g_0$ satisfies the template hypotheses at $(k,j)=(2j,j)$ ($p^{k+1}=p^{2j+1}$), $\psi=\ell$ satisfies them at $(k,j)=(2j+1,j)$ ($p^{k+1}=p^{2j+2}$), and $\mathrm{cob}_F(f-a g_0-b\ell)=\mathrm{cob}_F(f)-a\,\mathrm{cob}_F(g_0)-b\,\mathrm{cob}_F(\ell)$.*

*Proof.* (1) Fix $0<i<n$ and put $e:=(i,n-i)\in\mathbb N^2$ of degree $n$ (`:202–206`). Because $e_0=i>0$ and $e_1=n-i>0$, the single-variable embeddings $h(X_0)$ and $h(X_1)$ vanish at $e$ (`coeff_single_variable_series`, `TopsChoicePartA.lean:43–59`; `NotDvdChoosePowMul.lean:207–218`). Since $F(0,0)=0$, $\mathrm{ord}(F^d)\ge d$, so $[X^e](F^d)=0$ whenever $d>n$, truncating `PowerSeries.coeff_subst` to $0\le d\le n$ (`:219–231`). Splitting off $d=n$ via $[X^e](F^n)=\binom{n}{i}$ (Lemma 8.19a(3), `:232–236`) gives
$$[X^e]\mathrm{cob}_F(h)=\sum_{d=0}^{n-1}h_d\,[X^e](F^d)+h_n\binom{n}{i}.$$
By `integral_pow` and $\lVert h_d\rVert\le 1$ ($d<n$), the sum over $d<n$ has norm $\le 1$ (`:237–240`); subtracting it from $[X^e]\mathrm{cob}_F(h)$ (norm $\le 1$) gives $\bigl\lVert h_n\binom{n}{i}\bigr\rVert\le 1$ (`norm_sub_le_max`, `:191–194,241–246`). When $n\ge 2$ is not a power of $p$, Lemma 8.19a(1)–(2) supplies $0<i<n$ with $\bigl\lVert\binom{n}{i}\bigr\rVert=1$, giving $\lVert h_n\rVert\le 1$ (`:258–262`); strong induction on $d<p^{k+1}$ then gives `low_up` because no $p^m$ can satisfy $p^k<p^m<p^{k+1}$ (`:283–296`). At $n=p^{k+1}$, taking $i=p^k<p^{k+1}$ gives $\bigl\lVert\binom{p^{k+1}}{p^k}\bigr\rVert=\lVert p\rVert^1=\lVert p\rVert$ by Lemma 8.19a(1)–(2), whence $\lVert p\,h_{p^{k+1}}\rVert\le 1$ (`:271–274`).

(2) Set $\mu:=p\,h_{p^{k+1}}$, so $\lVert\mu\rVert\le 1$ by (1) (`:309`). To prove $\lVert h'_d\rVert\le 1$ for $d<p^{k+2}$, `low_up` applied to $h'$ at $k+1$ reduces the goal to $d\le p^{k+1}$ (`:314`). For $d<p^{k+1}$, $h'_d=h_d-\mu\,(p^j\psi_d)$ has norm $\le\max(\lVert h_d\rVert,\lVert\mu\rVert\lVert p^j\psi_d\rVert)\le 1$ (`:316–319`). For $d=p^{k+1}$, $\psi_{p^{k+1}}=p^{-(j+1)}$ and $(p:K)\neq 0$ give $h'_{p^{k+1}}=h_{p^{k+1}}-p\,h_{p^{k+1}}p^j p^{-(j+1)}=0$, of norm $0\le 1$ (`:320–326`). Next, any nonzero coefficient of $g_0$ below $p^{2j+1}$ sits at $d=p^{2i+1}$ with $2i+1<2j+1$ (`coeff_g0F_ne_zero`, `coeff_g0F_of`, `TopsChoicePartA.lean:163–180`), so $i+1\le j$ and $p^j(g_0)_d=p^{j-i-1}$ has norm $\le 1$ (`g_zero_low_coeff_norm`, `:328–344`); likewise any nonzero coefficient of $\ell$ below $p^{2j+2}$ sits at $d=p^{2i}$ with $2i<2j+2$ (`coeff_lgF_ne_zero`, `coeff_lgF_pow`, `TopsChoicePartA.lean:145–162`), so $i\le j$ and $p^j\ell_d=p^{j-i}$ has norm $\le 1$ (`lg_low`, `:345–361`). Finally, $F(0,0)=0$ makes substitution by $F$, $X_0$, and $X_1$ $K$-linear (`PowerSeries.subst_sub`, `subst_mul`, `subst_C`), giving `cob_comb` (`:362–373`). $\square$

**Theorem 8.19c (Alternating approximation `LemmaOne_of` and congruence elimination of $\beta\,\ell$ in `StepI_of`) [Lean, read].** *Assume the named interfaces `DeIntegral` and `LawSymm`. Then `LemmaOne` holds (`NotDvdChoosePowMul.lean:529–539`; wrapped as `Top.lemmaOne` at `FinalS.lean:48`): for every complete ultrametric characteristic-zero normed field $K$, $(p,\sigma)$ satisfying `UnrOK K p σ`, $F\in K[[X_0,X_1]]$ satisfying `IsLawOfLog p F`, and $f\in K[[T]]$ satisfying $f(0)=0$ and `Integral (cob F f)`, there exist $\alpha,\beta\in K$ and $R\in K[[T]]$ with $\lVert\alpha\rVert\le 1$, $\forall n,\ \lVert[T^n]R\rVert\le 1$, and $f=\alpha\,g_0+\beta\,\ell+R$. Combined with `FirstDeriv_of` and `CobLin_of` (Lemma 8.18b), `StepI_of` (`ConstantCoeffLawFirstTwoOfThree.lean:411–474`; wrapped as `Top.stepI` at `FinalS.lean:54`) eliminates $\beta\,\ell$ on `SuppOK p G` by congruence modulo $p^2-1$ and returns $\alpha$ with $\lVert\alpha\rVert\le 1$ and `DerivIs p G α`.*

*Proof.* Unpack `hU : UnrOK K p σ` (`NotDvdChoosePowMul.lean:531`) to retain $p$ prime (`hp`), $\lVert(p:K)\rVert=p^{-1}$ (`hnp`), and $\lVert\sigma(a)-a^p\rVert\le p^{-1}$ on $\lVert a\rVert\le 1$ (`hσ`), obtain `hde : Integral (cob F (g0F K p))` from `DeIntegral` (`:532`) and `hF1` from `LawSymm` (`:533`), and unpack `IsLawOfLog p F` into $F(0,0)=0$ (`hF0`), `Integral F` (`hFi`), and $\mathrm{cob}_F(\ell)=0$ (`hFl`, `:534`). Note first `cob_rem_integral` (`:389–399`): for *any* $a,b\in K$ with $\lVert a\rVert\le 1$ (and *no* condition on $b$), Lemma 8.19b(2) (`cob_comb`) and $\mathrm{cob}_F(\ell)=0$ give $\mathrm{cob}_F(\mathrm{rem}_p(f,a,b))=\mathrm{cob}_F(f)-a\,\mathrm{cob}_F(g_0)$, which is integral because `hcob` and `hde` are integral and $\lVert a\rVert\le 1$.

1. *Base step $j=0$ (`good_zero`, `:403–427`).* Set $a_0:=0$ ($\lVert a_0\rVert=0\le 1$) and $b_0:=[T^1]f$. By `cob_rem_integral`, $\mathrm{cob}_F(\mathrm{rem}_p(f,0,b_0))$ is integral. At $d=0$, $\ell_0=0$ (`coeff_lgF_ne_zero` since $(p^2)^i\ge 1$) and $f_0=0$ (`hf0`), so $[T^0]\mathrm{rem}_p(f,0,b_0)=0$; at $d=1$, $\ell_1=1$ (`coeff_lgF_pow` at $0$), so $[T^1]\mathrm{rem}_p(f,0,b_0)=f_1-f_1\cdot 1=0$ (`:415–426`). Applying `low_up` at $k=0$ extends integrality from $d\le p^0=1$ to all $d<p^1$, proving `Good p f 0 0 ([T^1]f)`.
2. *Two-substep inductive step $j\to j+1$ (`good_succ`, `:428–485`).* Assume `Good p f j a b`, so $\lVert a\rVert\le 1$ and $r:=\mathrm{rem}_p(f,a,b)$ satisfies $\lVert r_d\rVert\le 1$ for all $d<p^{2j+1}$.
   - *Odd-power substep ($p^{2j+1}$ via $g_0$, `:440–461`).* Define $\mu:=p\,[T^{p^{2j+1}}]r$ and $a':=a+\mu\,p^j$. Applying `norm_coeff_of_pow` (Lemma 8.19b(1) at $k=2j$, using `cob_rem_integral` at $(a,b)$) gives $\lVert\mu\rVert\le 1$ (`:442–444`). Since $\lVert p^j\rVert=p^{-j}\le 1$, ultrametric subadditivity gives $\lVert a'\rVert\le\max(\lVert a\rVert,\lVert\mu\rVert\lVert p^j\rVert)\le 1$ (`:445–448`), so `cob_rem_integral` also makes $\mathrm{cob}_F(\mathrm{rem}_p(f,a',b))$ integral! Rewriting $r^{(1)}:=\mathrm{rem}_p(f,a',b)=r-(\mu\,p^j)g_0$ (`:449–455`) and noting $[T^{p^{2j+1}}]g_0=p^{-(j+1)}$ (`:456–459`), `correct` at $(2j,j)$ with `g_zero_low_coeff_norm` upgrades integrality of $r^{(1)}$ to all $d<p^{2j+2}$ (`:460–461`), while $\lVert a'-a\rVert=\lVert\mu\rVert p^{-j}\le p^{-j}$ (`:481–482`).
   - *Even-power substep ($p^{2j+2}$ via $\ell$, `:463–484`).* Define $\nu:=p\,[T^{p^{2j+2}}]r^{(1)}$ and $b':=b+\nu\,p^j$. Rewriting $\mathrm{rem}_p(f,a',b')=r^{(1)}-(\nu\,p^j)\ell$ (`:465–472`), noting $[T^{p^{2j+2}}]\ell=p^{-(j+1)}$ (`:473–476`), and using `cob_rem_integral` at $(a',b')$ (which still needs only $\lVert a'\rVert\le 1$!), `correct` at $(2j+1,j)$ with `lg_low` yields both $\lVert\nu\rVert\le 1$ and $\lVert[T^d]\mathrm{rem}_p(f,a',b')\rVert\le 1$ for all $d<p^{2j+3}=p^{2(j+1)+1}$ (`:477–480`), i.e. `Good p f (j+1) a' b'`, together with $\lVert b'-b\rVert=\lVert\nu\rVert p^{-j}\le p^{-j}$ (`:483–484`).
3. *Geometric Cauchy convergence in complete $K$ (`exists_limit`, `LemmaOne_of`, `:486–539`).* Selecting step functions $(fa,fb)$ from `good_succ` (`choose!`, `:494`) and iterating from $s_0=(0,[T^1]f)$ defines $s_j=(a_j,b_j)$ satisfying `Good p f j a_j b_j`, $\lVert a_{j+1}-a_j\rVert\le(p^{-1})^j$, and $\lVert b_{j+1}-b_j\rVert\le(p^{-1})^j$ for all $j\in\mathbb N$ (`:495–512`). Because $p^{-1}<1$ and `[CompleteSpace K]` holds, `cauchySeq_of_le_geometric` and `cauchySeq_tendsto_of_complete` produce limits $a_j\to\alpha\in K$ and $b_j\to\beta\in K$ (`:504–514`). Closedness of $[0,1]$ under limits (`le_of_tendsto`) gives $\lVert\alpha\rVert\le 1$ from $\lVert a_j\rVert\le 1$ (`:515`). For each fixed $n\in\mathbb N$, $2j+1<p^{2j+1}$ (`Nat.lt_pow_self`) implies $n<p^{2j+1}$ for all $j\ge n$ (`:521–523`), so $\lVert[T^n]\mathrm{rem}_p(f,a_j,b_j)\rVert\le 1$ holds for all $j\ge n$; since $[T^n]\mathrm{rem}_p(f,a_j,b_j)=f_n-a_j(g_0)_n-b_j\ell_n$ converges to $[T^n]\mathrm{rem}_p(f,\alpha,\beta)$, `le_of_tendsto` gives $\lVert[T^n]R\rVert\le 1$ for $R:=\mathrm{rem}_p(f,\alpha,\beta)$, and $f=\alpha\,g_0+\beta\,\ell+R$ (`:517–523,536–539`).
4. *Eliminating $\beta\,\ell$ by congruence support in `StepI_of` (`ConstantCoeffLawFirstTwoOfThree.lean:393–474`).* Given $G\in K[[X_0,X_1]]$ with `SuppOK p G`, $d_1 F\,G\sim 0$, and $d_1 F\,(G^\tau)\sim 0$, `SuppOK p G` gives `DivAB G` (`:416–420`), hence $f(0)=G_{(1,0)}=0$ for $f:=\mathrm{fLin}\,G$ (`:423–425`), while `FirstDeriv` and `CobLin` (Lemma 8.18b) supply `hFD : Integral (∂_0 G - ℓ'(X_0) f(X_1))` and `hCL : Integral (cob F f)` (`:421–422`). Applying `LemmaOne` to $f$ yields $(\alpha,\beta,R)$ with $\lVert\alpha\rVert\le 1$, $R$ integral, and $f=\alpha\,g_0+\beta\,\ell+R$ (`:426`). Fix $j\in\mathbb N$ (`:428`) and test $j\equiv p\pmod{p^2-1}$:
   - If $j\equiv p\pmod{p^2-1}$ (`:429–440`), then $[T^j]\ell=0$: any nonzero coefficient of $\ell$ sits at $j=(p^2)^i\equiv 1\pmod{p^2-1}$ (`powq_modEq_one`, `:396–397`), whereas $1\not\equiv p\pmod{p^2-1}$ for $p\ge 2$ because $0<p-1<p^2-1$ prevents $(p^2-1)\mid(p-1)$ (`not_one_modEq`, `:399–406`). Thus $[T^j](f-\alpha g_0)=[T^j]R$, of norm $\le 1$.
   - If $j\not\equiv p\pmod{p^2-1}$ (`:441–460`), then $[T^j]f=0$ (for $[T^j]f=G_{(1,j)}\neq 0$ implies $1\equiv p j\pmod{p^2-1}$ by `SuppOK p G`, and multiplying by $p$ with $p^2\equiv 1\pmod{p^2-1}$ gives $p\equiv p^2 j\equiv j\pmod{p^2-1}$, `:449–453`) and $[T^j]g_0=0$ (since $p(p^2)^i\equiv p\pmod{p^2-1}$, `:454–458`), so $[T^j](f-\alpha g_0)=0$ of norm $0\le 1$.
   Hence `key : Integral (f - C α * g_0)` holds (`:427`). Writing $\partial_0 G-\alpha\ell'(X_0)g_0(X_1)=\bigl(\partial_0 G-\ell'(X_0)f(X_1)\bigr)+\ell'(X_0)\bigl(f(X_1)-\alpha g_0(X_1)\bigr)$ coefficientwise (`coeff_product_single_variables`, `:463–470`) and bounding $\ell'(X_0)$ by `norm_coeff_dlgF` (`:472–474`) gives `DerivIs p G α` with $\lVert\alpha\rVert\le 1$. $\square$

**Remarks [Expository].**

1. *Why `LemmaOne` leaves $\beta$ unbounded, and why `StepI_of` never has to prove $\beta=0$.* In `Good p f j a b`, $\lVert a_j\rVert\le 1$ is maintained inductively because subtracting $a_j g_0$ changes $\mathrm{cob}_F$ by $-a_j\mathrm{cob}_F(g_0)$, which stays integral via `DeIntegral` only when $\lVert a_j\rVert\le 1$. By contrast, $\mathrm{cob}_F(\ell)=0$ identically, so `cob_rem_integral` accepts *any* $b_j\in K$, and at $j=0$ `good_zero` must set $b_0=[T^1]f$ to clear the linear term — which has norm $>1$ whenever $[T^1]f$ is non-integral, as in Worked Example 2 ($b_0=\beta=\frac15$, $\lVert\beta\rVert=5$). On a `SuppOK` slice $f=\mathrm{fLin}\,G$, one *could* deduce $\beta=0$ post hoc by evaluating $0=[T^{p^{2i}}]f=\beta p^{-i}+[T^{p^{2i}}]R$ for all $i\ge 0$ (`eq_zero_of_div` of §8.4.17), because $p^{2i}\equiv 1\not\equiv p\pmod{p^2-1}$; `StepI_of` avoids even that limit argument by observing directly that $f-\alpha g_0$ equals $R$ on $j\equiv p\pmod{p^2-1}$ and $0-0=0$ off that residue class.
2. *Role of $f(0)=0$, unused `UnrOK` clauses, and connection to `LemmaTwo`.* At degree $0$, $g_0(0)=\ell(0)=0$ forces $[T^0]R=f(0)$. In fact, $[X^0]\mathrm{cob}_F(f)=f(F(0,0))-2f(0)=-f(0)$ already forces $\lVert f(0)\rVert\le 1$ whenever `Integral (cob F f)` holds; `LemmaOne` nevertheless takes $f(0)=0$ explicitly so `good_zero` (`:420`) can rewrite $[T^0]\mathrm{rem}_p(f,0,f_1)=0$ directly, and `StepI_of` supplies $f_G(0)=G_{(1,0)}=0$ from `DivAB G`. As noted in the declaration check above, `NotDvdChoosePowMul.lean:531` discards both $2<p$ and the discrete-valuation hypothesis of `UnrOK` (working for every prime $p$, including $p=2$), and uses $(\sigma,h_\sigma)$ only once to invoke `DeIntegral`. Downstream in `FinalS.lean:49`, `LemmaTwo_of lemmaOne lawSymm` (`LemmaTwoOf.lean`, retained at `[Lean]`) applies `LemmaOne` slice-by-slice to construct the two-variable classification consumed by `StepH_of` in §8.4.17.
3. *Classical context.* The binomial gcd dichotomy underlying Lemma 8.19a(1) — that $\gcd_{0<i<n}\binom{n}{i}$ equals $p$ if $n=p^r$ ($r\ge 1$) and $1$ otherwise, with explicit non-prime-power witness $i=p^k$ for $n=p^k m$ ($p\nmid m$) and prime-power reduction $(X_0+X_1)^{p^{k+1}}\equiv(X_0^{p^k}+X_1^{p^k})^p\pmod{p^2}$ — was introduced into formal-group cohomology by Lazard (`[Lazard1955]`, §II, Proposition 3 / Lemme 4, pp. 257–259, and §III, Démonstration du lemme 3, pp. 261–262) to classify symmetric $2$-cocycles and one-variable coordinate perturbations modulo degree $n+1$; its $p$-typical logarithm / functional-equation specialization appears in `[Honda1970]` and `[Hazewinkel1978]` (§2 and §6).
4. *Reading boundary and sources.* This subsection adds local R3 `[Lean, read]` for `FinalS.lean:48` (`Top.lemmaOne`) and the complete file `NotDvdChoosePowMul.lean:1–540` (`LemOne.*` and `LemmaOne_of`), together with the ultrametric integer-cast norm proofs `NormNatCastEqOneOfNotDvd.lean:1–29` (`norm_natCast_eq_one_of_not_dvd`) and `NormNatCastEqPowPadicValNat.lean:13–30` (`norm_natCast_eq_pow_padicValNat`), while inheriting `TopsChoicePartA.lean:43–59,109–180` (§8.4.17) and `ScalingSwapLemmas.lean:314–447`, `ConstantCoeffLawFirstTwoOfThree.lean:190–474` (`StepZero_of`, `FirstDeriv_of`, `CobLin_of`, `StepI_of`, §8.4.18). Retained as named `[Lean]` inputs: `DeIntegral` (`FinalS.lean:46`), `LawSymm` (`:44`), `LawExists` (`:43`, used only in Example 3(a)), `DivDeriv` (`:45`), `LemmaTwo` (`:49`), `DworkMv` (`:33`), and `SimeqRules` (`:34`). Pinned Mathlib declarations (`0df444a360eaa60ab8c11dca51a86af692955474`, verified against raw source on 2026-11-25): `Choose.choose_modEq_choose_mod_mul_choose_div_nat` (`Data/Nat/Choose/Lucas.lean:69`, author Gareth Ma); `Nat.Prime.emultiplicity_choose_prime_pow_add_emultiplicity` (`Data/Nat/Multiplicity.lean:229`, author Chris Hughes); `padicValNat.prime_pow` (`NumberTheory/Padics/PadicVal/Basic.lean:401`, authors Robert Y. Lewis and Matthew Robert Ballard); `MvPowerSeries.nat_le_order`, `min_order_le_add`, `le_order_mul` (`RingTheory/MvPowerSeries/Order.lean:425,460,471`, authors Antoine Chambert-Loir and María Inés de Frutos-Fernández); `PowerSeries.coeff_subst` (`RingTheory/PowerSeries/Substitution.lean:236`, same authors); `cauchySeq_of_le_geometric` (`Analysis/SpecificLimits/Basic.lean:528`, authors Sébastien Gouëzel, Johannes Hölzl, Yury Kudryashov, and Patrick Massot); `cauchySeq_tendsto_of_complete` (`Topology/UniformSpace/Cauchy.lean:433`, authors Johannes Hölzl and Mario Carneiro). Classical primary source read in Numdam scan: `[Lazard1955]` (pp. 256–262). All formal proofs in archive A2 (`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`) belong to Levent Alpöge with Claude; the textbook exposition, all-orders worked calculations, and antecedent-deletion counterexamples are ours. Source reading and the book build do not constitute Lean kernel verification. [A2 source and reading record](../sources/SOURCES.md#chapter-8-8419--classifying-slice-coboundaries-and-the-lemmaone-supply)

| Role | Declaration | Source |
|---|---|---|
| Newly read at local R3 `[Lean, read]` | `Top.lemmaOne`; `LemmaOne_of`, `LemOne.not_dvd_choose_pow_mul`, `exists_not_dvd_choose`, `padicValNat_choose_pow`, `integral_mul`, `integral_pow`, `order_sub_lin`, `order_pow_sub_lin`, `coeff_lin_pow`, `coeff_pow_top`, `norm_coeff_mul_choose`, `norm_coeff_of_not_pow`, `norm_coeff_of_pow`, `low_up`, `correct`, `g_zero_low_coeff_norm`, `lg_low`, `cob_comb`, `rem`, `cob_rem_integral`, `Good`, `good_zero`, `good_succ`, `exists_limit`; `norm_natCast_eq_one_of_not_dvd`, `norm_natCast_eq_pow_padicValNat` | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FinalS.lean:48`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean:16–539`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormNatCastEqOneOfNotDvd.lean:7–28`; `src/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean:17–29` |
| Inherited `[Lean, read]` (cited, not re-proved) | `coeff_single_variable_series`, `coeff_lgF_pow`, `coeff_lgF_ne_zero`, `coeff_g0F_of`, `coeff_g0F_ne_zero` (§8.4.17); `StepZero_of`, `FirstDeriv_of`, `CobLin_of`, `sq_modEq_one`, `powq_modEq_one`, `not_one_modEq`, `StepI_of` (§8.4.18); `BetaIsG_of` (§8.4.17) | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean:43–59,109–180`; `ScalingSwapLemmas.lean:340–447`; `ConstantCoeffLawFirstTwoOfThree.lean:190–474`; `NormLiftLeOne.lean:32–56` |
| Unread / named inputs retained `[Lean]` | `DeIntegral` (`Top.deIntegral`), `LawSymm` (`Top.lawSymm`), `LawExists` (`Top.lawExists`), `DivDeriv` (`Top.divDeriv`), `LemmaTwo` (`Top.lemmaTwo`), `DworkMv` (`Top.dworkMv`), `SimeqRules` (`Top.simeqRules`) | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/IsLawOfLog.lean:43–65,81–87`; `FirstDeriv.lean:39–49`; `CyclicPowerClassOfExpEquiv.lean:13–34`; `FinalS.lean:33–34,43–46,49` |

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
- Sections 8.4.4–8.4.5 read the formal-group side. The two declarations named
  `Conclusion1` have different conclusions. The single-kernel
  `FormalGroupSystem.Conclusion1` is packed into `Conclusion₂` as the field `R.S1`, but
  none of the three read sites projects it. They use only `VolumeRatio₂` and
  `LowTermBound`, which reach the service proof through `unitBoundAtTwistedPlaces` and
  `SmallInertPrimeSmallOrderLengthBound`. Both fields come from the same exponential
  estimate `inClass_of_exp` through `ea_restSU_of`, not through `Conclusion1`.
  [Lean, read] `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:633,775`,
  `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PrvAndKernelCommutationUpToUnitsOfRests.lean:94,97`,
  `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:172,185`,
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
| `gam`, `gB`, `gA`, `Conclusion1`, `Conclusion2`; `trueColumns_row_sharp_bounds` | `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:51,57,66,633,649`; `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TrueColumnsRowSharpBoundsStatement.lean:8` | Definition 8.3(2) (`R2`): supersingular height-$2$ slope $\frac{p}{p^2-1} = \sum_{e \ge 0} p^{-(2e+1)}$, odd-power gain `gA`, and statement interfaces. Sections 8.4.4–8.4.5 read the kernel expansion and the production of `VolumeRatio₂` and `LowTermBound`; the Gauss bounds and the `admitted` inputs stay `[Open]`. | [Lean] |
| `atPi`, `applyD`, `Sys.vsc`, `Sys.vGe`, `Sys.Iprod`, `Pend.geC`, `Pend.LowAt`, `adm7`, `adm11`, `VolumeRatio₂`, `LowTermBound`, `lowAt_max`, `admitted`, `Conclusion₂`, `Stmt` | `src/Formalism/SharpRestriction/GrowthBounds/FormalGroupSystem.lean:253,256,309,311,361,522,529,613,627,658,708,718,771,775,779` | Section 8.4.5 definitions: rescaling, column tests, lattice valuation, integer encoding of a real bound, low bound of one exponential factor, the packet and its hypotheses. | [Lean, read] |
| `ea_restSU_of`, `ea_InClassA`, `ea_RestSU`, `ea_applyD_map`, `ea_geC_of_norm`, `ea_Rp_le_ball`, `ea_lowN`, `ea_A1U`, `ea_A2U`, `ea_BU`, `first_theorem_place_bound`, `second_lemma_place_bound`, `hecke_place_bound`, `restEnt_of_rest`, `kernel_product_form`, `restEnt_of`, `restPlaces_of` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpV.lean:28`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EntryAOneParity.lean:88,101,106`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaGeCOfNorm.lean:53,71,91,198,211,224`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/FirstTheoremPlaceBound.lean:20,24,28`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AuxUOfFirstTheoremPlaceBound.lean:66`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/RestEntOf.lean:20,62`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelProductForm.lean:118` | Lemmas 8.4–8.5, Theorem 8.6 and its corollary: one-place class expansion, transfer to `LowAt`, the three place bounds and `EntCondition`. | [Lean, read] |
| `low_term_bound_of_eO_eq_zero_of_aux0`, `prv_and_kernel_commutation_up_to_units_of_rests`, `rests`, `stmt_proved`, `basic₂`, `PrZ_cast`, `lift_bound_of_integrality`, `ZL_chain`, `bbJ`, `main_ind`, `Zop_gen`, `ZL_mem`, `ZL_bound`, `ent_strict`, `formB_lim`, `form_of_place` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PrvAndKernelCommutationUpToUnitsOfRests.lean:45,80,97,107`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/LiftBoundOfIntegrality.lean:24,91,103`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/YEPEComm.lean:110,127,131`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AofUpdate.lean:91,152,172`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/RamifiedLatticeOfChainEstimates.lean:46,65,90` | Theorem 8.7: production proof of `LowTermBound` in both cases of $e_O$, the chain induction, the one-step bound, and the rational and ceiling bookkeeping. | [Lean, read] |
| `SysUAt`, `UAt_of`, `unit_bound_of_local_system`, `unit_bound_of_sum_over_primes`, `UAt`, `unitBoundAtTwistedPlaces`, `eO_eq_vUnit`, `scale_pow_mono` | `src/Formalism/SharpRestriction/GrowthBounds/JointsTw.lean:9,23,216,243`; `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:161,172`; `src/Formalism/SharpRestriction/GrowthBounds/Joints.lean:1608,1618` | Proposition 8.8: the reader of `VolumeRatio₂`, `adm11` and `LowTermBound`. | [Lean, read] |
| `ea_restSExpV_of`, `ea_RestSExpV`, `ea_RestGcV`, `ea_GtV`, `ea_reduce`, `ea_Simeq_refl`; `restSIntA`, `atPi_map_ThZA`, `atPi_eq_rescale`; `genInt`, `inParam_map`, `log_at`, `restSInt`; `lamF_mem`, `exists_mu`, `IntR_subst`, `IntR_psubst`; `tOf`, `th_reduce`; `E0`, `ren`, `th_subst_expK`, `th_map_expK`; `RestSIntA`, `RestSExpA`; `RestBeta`, `RestGc`, `th_coordZA_int`; `ea_restSU` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpVOf.lean:260,245,249,102,227`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaRestSExpV.lean:15`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/AtPiEqRescale.lean:64,49,12`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/InParamMap.lean:58,99,29,124`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/IntRPsubst.lean:97,124,53,80`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/SubstitutionOfVariables.lean:17,199`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/IntegralExpRename.lean:61,88,30,48`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelExpansionOfRestrictions.lean:41,29`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DworkExponentialRestrictions.lean:15,19,78`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/FirstTheoremPlaceBound.lean:17` | Section 8.4.14: the rescaled logarithm $\lambda=\pi^{-1}\ell(\pi T)$ and its `Rp`-integral inverse $\mu$, the identity $\ell(\pi\mu(L))=\pi L$ transferring integrality from `inParamK U` to $U(\pi\,\mathrm{coordZA})$ (`restSIntA`), the exponential-factor reduction $\exp(-\Phi)(\pi L)=\exp(-G_s)(\pi\mu(L))\,V'$ with $W$-integral `RestBeta`/`Simeq` factors (`ea_reduce`), and the assembly `ea_restSU` from `restBeta`, `th_restGcV_of`, `ea_restSExpV_of`, `ea_restSU_of` at the three place bounds. | [Lean, read] |
| `restBeta`, `biadditive_second_variable`, `biadditive_first_variable`, `sx_conj`, `sx_root`, `sx_betaHyp`, `sx_unrOK`, `param_substitution_pair`, `sx_divAB`, `sx_simeq_of`, `integralExp_of_equiv`, `equiv_zero_of_integralExp`, `integralExp_param_of_equiv_zero`; `sx_norm_le_one_iff`, `sx_sig_frob` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveSecondVariable.lean:137,37,100,61,130,134`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/BiadditiveFirstVariable.lean:111,83,30`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/IntegralExpParamOfEquivZero.lean:78,87,106,113`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/PositivityConditionHolds.lean:21,45` | [§8.4.16](#8416-the-biadditive-supply-restbeta-from-beprop-to-the-frobenius-fixed-class-of-gser): `BeProp` in geometric coordinates becomes `BetaHyp` in logarithmic coordinates (biadditivity along the law $F$ with $\ell(F(x,y))=\ell(x)+\ell(y)$, Teichmüller lifts of the $(p^2-1)$-th roots of unity for `conj`), `betaIsG` returns the Frobenius-fixed $c$, and the unit ball of $K_0$ is the image of $W$; $5\le p$ is used once as $2<p$. `lawExists`, `witt_teichmuller_root` kept named (`BetaIsG_of` read in [§8.4.17](#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar)). | [Lean, read] |
| `Top.betaIsG`, `BetaIsG_of`, `divAB_of_suppOK`, `norm_lift_le_one`, `ThmSFull_of`; `StepII_of`, `partial_coboundary_linear`, `subst_g_zero_eq_log`, `subst_pow_g_zero`, `pderiv_prod`, `norm_sigma_le`; `constantCoeff_first_two_of_three`, `partial_coboundary_product`, `partial_coboundary_h_series`, `suppOK_Hser`, `coeff_lg_lg_eq_zero`, `eq_zero_of_div`, `StepH_of`, `c_add_sigma_c_eq_zero`, `StepIV_of`; `g_zero_relation_holds`, `identity_b`, `frobenius_expression_g`; `swap_rules`; `frob_congr`, `pderiv_psubst` | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FinalS.lean:61`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormLiftLeOne.lean:32,13,20,58`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/PartialCoboundaryLinear.lean:225,178,106,115,167,206`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean:24,88,103,192,198,223,277,338,389`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean:250,355,362`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean:276`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LocalComponentGL.lean:239`; `src/Formalism/FormalGroupLog/FormalGroupLogProofs/ChainRule.lean:115` | [§8.4.17](#8417-assembling-betaisg-partial-coboundary-remainders-the-two-variable-support-test-and-the-frobenius-fixed-scalar): derivative compensation turns `DerivIs` and `Simeq (d1 F G) 0` into the integral partial-coboundary remainder of `DeS` (`StepII_of`); three-variable zero-constant embedding, coboundary linearity, `LemmaTwo`, and disjointness of `SuppOK` from $\ell(X_0)\ell(X_1)$ make `Hser` integral (`StepH_of`); comparing $(1,p^{2i+1})$ coefficients gives $c+\sigma(c')=0$ and $c'+\sigma(c)=0$, hence $\sigma^2(c)=c$, and `FrobExprG` with `DworkMv` returns `Simeq be (Gser p c (σ c))` to `restBeta`. `DworkMv`, `DivDeriv`, `DeIntegral`, `LawSymm`, `LemmaTwo`, `StepZero`, `StepI`, `SimeqRules` kept named. | [Lean, read] |
| StepZero_of, LamModule_of, FirstDeriv_of, CobLin_of, StepI_of | src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean:314–447 and ConstantCoeffLawFirstTwoOfThree.lean:178–474 | [§8.4.18](#8418-projection-and-first-derivatives-for-betaisg): congruence projection, integral derivatives on two coordinate faces and the bounded scalars passed to BetaIsG_of. | [Lean, read] |
| `Top.lemmaOne`, `LemmaOne_of`; `not_dvd_choose_pow_mul`, `exists_not_dvd_choose`, `padicValNat_choose_pow`, `coeff_pow_top`, `norm_coeff_mul_choose`, `low_up`, `correct`, `g_zero_low_coeff_norm`, `lg_low`, `cob_rem_integral`, `good_zero`, `good_succ`, `exists_limit`; `norm_natCast_eq_one_of_not_dvd`, `norm_natCast_eq_pow_padicValNat` | `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FinalS.lean:48`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NotDvdChoosePowMul.lean:16–539`; `src/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormNatCastEqOneOfNotDvd.lean:7–28`; `src/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean:17–29` | [§8.4.19](#8419-classifying-slice-coboundaries-and-the-lemmaone-supply): Lazard binomial dichotomy, two-step $g_0$/$\ell$ Cauchy approximation for one-variable slice coboundaries $f=\alpha g_0+\beta\ell+R$ ($\lVert\alpha\rVert\le 1$), and congruence elimination of $\beta\,\ell$ in `StepI_of` (`DeIntegral`, `LawSymm`, `LemmaTwo`, `DworkMv` kept named). | [Lean, read] |
| `restGc`, `th_restGcV_of` (proof body), `nm_restNorm_of_place`, `eb_brJet`, `ea_brClass`, `ea_brNum`, `ea_brScale`, `kernel_a_one_generic`, `kernel_a_two_generic`, `kernel_b_generic`, `formB`, `entry_mem`, `theorem_of_alternate_form` | `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CommonEigenvectorThird.lean:21`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/ThRestGcVOf.lean:27`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/NmRestNormOfPlace.lean:21`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EbBrJet.lean:41`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaDegreeMapDomain.lean:162`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/GainOfCapacityLoss.lean:252`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/EaApplyDScale.lean:98`; `src/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EGaussK.lean:213,216,219`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/SmulUpdate.lean:99`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/KernelSumOfClassData.lean:206`; `src/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/TheoremOfAlternateForm.lean:561` | Inputs of Theorems 8.6–8.7 whose proofs we have not read; `entry_mem` takes `adm7` and `ArchimedeanSignatureMatching` from `admitted`. | [Lean] |

**Summary of the chapter.** At primes $p$ inert in the imaginary quadratic core $K = \mathbb Q(\sqrt{-d})$,
supersingular height-$2$ formal groups have $D^p \equiv 0 \pmod p$ and Newton-polygon slope
$\frac{1}{p^2 - 1}$, whose difference from Legendre's factorial slope $\frac{1}{p - 1}$ equals
$\frac{p}{p^2 - 1} = \frac{1}{p} + \frac{1}{p^3} + \frac{1}{p^5} + \dots$ `[Katz1976]`, generating
the odd-power Riesz ramp `vonMangoldtClassSum` / `ASK` while split primes contribute zero [Expository].
In `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean`, `Conclusion1` (`:97`) states the $m$-step composite column bound
`InNP ... → ColGe ... (totS ...)` (supplied upstream via `FormalGroupSystem.lean` and
`DIVRecBridgeSel.lean`), and `off_level_bound` (`:504`) plus `off_level_bound_family` (`:614`) combine
that `Conclusion1` input with `PairInt`, `val_step`, `period_ge`, and `gainD_le_gainS` to deduce period
divisibility at order `L.sg u w`, feeding `LinkDIVt` (`src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/DIVRecBridgeSel.lean:197`) [Lean, read].
On the formal-group side, one exponential estimate (`inClass_of_exp`) yields, through
`ea_restSU_of`, the place bound `VolumeRatio₂` and the chain bound `LowTermBound`. These are the only
packet fields read downstream, and the passage from column tests to lattices is the `admitted` field
`adm7` (Sections 8.4.4–8.4.5). Section 8.4.14 reads the producers `restSIntA` and `ea_restSExpV_of` that supply `ea_RestSU` by one change of variables, the formal-group logarithm rescaled by $\pi$, which makes the residual factor integral and the exponential factor Dwork-normalized, and Section 8.4.16 reads the biadditive supply `restBeta`, whose two outputs, the Frobenius-fixed $c$ and the $W$-integral exponential of $\mathrm{inParam}\,\mathrm{be}-\mathrm{Gser}(c,\sigma c)$, feed `th_restGcV_of` and the $Y$-factor of `ea_reduce`, while Section 8.4.17 reads the conditional classification assembly `BetaIsG_of` (`StepII_of`, `StepH_of`, `StepIII`, `StepIV_of`, `FrobExprG`, `SwapRules`) that produces $c$, proves $\sigma^2(c)=c$, and closes `G7.Simeq` from the named `DworkMv`, `DivDeriv`, `DeIntegral`, `LawSymm`, and `LemmaTwo` supplies, with `StepZero_of`/`StepI_of` and the one-variable coboundary producer `LemmaOne_of` opened in [§8.4.18](#8418-projection-and-first-derivatives-for-betaisg)–[§8.4.19](#8419-classifying-slice-coboundaries-and-the-lemmaone-supply). In
Chapter 9 we see how Bost's Arakelov slope inequality converts this local $\mathfrak p_w$-adic
divisibility into a global numerical inequality!
