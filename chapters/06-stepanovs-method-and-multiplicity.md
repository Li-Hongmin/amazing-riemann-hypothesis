# Chapter 6. Stepanov's method and multiplicity over the integers

Part I closed at Corollary 5.6 (`level_gm_le_on_family_scales`,
`src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean:28`) [Lean, read]:
every target theorem of `src/Main.lean` follows from classical harmonic analysis once, at each
window scale $x$, we can inhabit the chain-existence predicate `CoreAtH`
(`src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean:29`) [Lean, read] and the
Tate–Shafarevich window bound `VWin` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49`) [Lean, read].
Part II (Chapters 6–11) opens `CoreAtH` and `VWin`.

Before plunging into definite unitary groups, Weil representations, and Arakelov lattices, we have
to understand the **organizing idea** of the entire arithmetic engine. In his four-page announcement,
Alpöge explains where the architecture came from in three sentences [Paper; remark p. 1]:

> "In Stepanov's argument resolving Riemann over function fields one uses a divisor involving
> multiplicity. This argument is a descendant of Stepanov's, but multiplicity is hard to find over
> the integers, corresponding to something like differentiating whole numbers. ... The line: for the
> von Mangoldt sum of length $X$, Claude's suggested length of chain of theta lifts, in view of each
> mimicking multiplicity, was $\sqrt{X}$."

This chapter does two jobs:

1. **The classical function-field model (`[Expository]`, following `[Stepanov1969]`, `[Bombieri1973]`,
   `[Schmidt1976]`, `[HasseSchmidt1937]`):** We prove the Hasse–Weil square-root bound
   $\lvert \#C(\mathbb F_q) - (q + 1) \rvert \le 2g\sqrt{q}$ for hyperelliptic and smooth projective
   curves over finite fields from scratch by the **Stepanov–Bombieri auxiliary-polynomial method**,
   using zero intersection theory on surfaces and zero $\ell$-adic cohomology. Along the way we see
   precisely *why* multiplicity $m = 1$ gives only the trivial bound $O(q)$, *how* Hasse–Schmidt
   divided-power derivations $D^{(k)}$ interact with the Frobenius $q$-th power so that $m$ vanishing
   orders cost degree proportional to $m^2$ rather than $m q$, *why* optimizing $q/m + g m$ selects
   $m \asymp \sqrt{q}$, and *how* curve point counting converts directly into square-root bounds for
   multiplicative and additive character sums `[Weil1948]`, `[IwaniecKowalski2004]`.
2. **The formal P7 bridge to $\mathbb Z$ (`[Lean, read]` on node `P7`):** We inspect the actual Lean
   files of node `P7` — `MeanBoundSecondForm.lean`, `WeightedMeanData.lean`,
   `QuotientSlopeBoundsWith.lean`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`, `src/Formalism/SizeWindowBrackets/SChain.lean`, `DataParams₂.lean`,
   `EvenCeil.lean`, and `TieGlobal.lean` — and prove in full human prose the archive's unconditional
   algebraic deduction `each_unit_bound_statement` (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`) [Lean, read]. Doing
   so reveals an exact structural isomorphism between Stepanov's zero-versus-pole inequality over
   $\mathbb F_q(x)$ and the archive's 11-clause package `SizeData₂` (`src/Formalism/SizeWindowBrackets/SChain.lean:17`) [Lean, read],
   while keeping a strict line between the elementary algebra genuinely proved in `P7` (`[Lean, read]`)
   and the deep arithmetic hypotheses packaged as `structure` fields (`[Lean]` / `[Open]`).

---

The host geometry supplies the pure signatures used by `gram0Def` and the finite adelic sign change. [Pure host signatures (§6.4.16)](#6416-producing-pure-signatures-from-the-host-spaces) · [Finite adelic norm minus one (§6.4.17)](#6417-producing-the-finite-adelic-element-of-norm-minus-one)

The local coefficient step for the prismatic datum uses the normalized Frobenius matrix of a quasi-logarithm basis. [Adapted Frobenius matrices (§6.4.21)](#6421-why-the-frobenius-matrix-in-an-adapted-basis-is-a-unit) · [First torsion group (§6.4.22)](#6422-reading-the-second-block-on-the-first-torsion-group)

## 6.1 Motivation

### 6.1.1 Why multiplicity beats the trivial bound without algebraic geometry

Let $C$ be a smooth projective geometrically connected curve of genus $g \ge 1$ over the finite
field $\mathbb F_q$, with $N_1 := \#C(\mathbb F_q)$ rational points. For an elliptic curve ($g = 1$)
given in affine Weierstrass form
$$E : y^2 = f(x) = x^3 + a x + b, \qquad 4a^3 + 27b^2 \neq 0 \text{ in } \mathbb F_q \quad (\operatorname{char}\mathbb F_q \neq 2, 3),$$
each $x_0 \in \mathbb F_q$ yields $1 + \chi_2(f(x_0)) \in \{0, 1, 2\}$ affine points $(x_0, y_0) \in E(\mathbb F_q)$,
where $\chi_2 : \mathbb F_q^\times \to \{\pm 1\}$ (extended by $\chi_2(0) = 0$) is the quadratic
character. Including the point at infinity $P_\infty$,
$$N_1 = \#E(\mathbb F_q) = 1 + \sum_{x_0 \in \mathbb F_q} \bigl(1 + \chi_2(f(x_0))\bigr)
= q + 1 + \sum_{x_0 \in \mathbb F_q} \chi_2(f(x_0))$$
[Expository]. The trivial bound $\lvert \chi_2(f(x_0)) \rvert \le 1$ gives only $1 \le N_1 \le 2q + 1$,
missing the square-root Hasse–Weil bound $\lvert N_1 - (q + 1) \rvert \le 2\sqrt{q}$ `[Hasse1936]`,
`[Weil1948]` by a full power $q^{1/2}$.

How could pure polynomial algebra ever see $\sqrt{q}$? Try first the naive polynomial method at
**multiplicity $m = 1$** [Expository]. Over a prime field $\mathbb F_p$ ($p \ge 5$), Euler's
criterion says that for $x_0 \in \mathbb F_p$,
$$f(x_0) \text{ is a nonzero square in } \mathbb F_p \iff f(x_0)^{(p-1)/2} \equiv 1 \pmod p.$$
The single polynomial $P_{\mathrm{naive}}(x) := f(x)^{(p-1)/2} - 1 \in \mathbb F_p[x]$ is nonzero of
degree $\frac{3(p-1)}{2}$ and vanishes at every $x_0 \in \mathbb F_p$ where $f(x_0) \in (\mathbb F_p^\times)^2$.
Each such $x_0$ contributes **two** points $(x_0, \pm y_0)$ to $E(\mathbb F_p)$ and at least **one**
root to $P_{\mathrm{naive}}$, so the number $N_+$ of such $x_0$ satisfies $N_+ \le \frac{3(p-1)}{2}$ —
worse than the trivial bound $N_+ \le p$!

Now watch what changes if we can manufacture a nonzero polynomial $H(x) \in \mathbb F_p[x]$ (or a
rational function $\Phi \in \mathbb F_q(C)$) that vanishes at every rational point not to order $1$,
but to **multiplicity $m \ge 1$** [Expository]:

1. **Zero-count lower bound from multiplicity:** If $\Phi \neq 0$ vanishes to order $\ge m$ at each
   of $N$ distinct points, then the total number of zeros of $\Phi$ (counted with multiplicity) is at
   least $m \cdot N$. Since a rational function on a projective curve has as many zeros as poles,
   $$m \cdot N \le \deg(\Phi)_\infty \implies N \le \frac{\deg(\Phi)_\infty}{m}.$$
   Notice the division by $m$! Any pole cost that was independent of $m$ (say of size $\approx q$)
   immediately shrinks from $q$ to **$q / m$**!
2. **Why differentiating $x^q$ is "free":** Why doesn't forcing $m$ derivatives to vanish at every
   point of $\mathbb F_q$ blow up $\deg(\Phi)_\infty$ to $m \cdot q$, cancelling the division by $m$?
   Because on $\mathbb F_q$, **every element satisfies $x_0^q = x_0$, while in the polynomial ring
   $\mathbb F_q[x]$ the $q$-th power $x^q$ has vanishing derivatives up to order $q - 1$**! More
   precisely, for the Hasse–Schmidt divided-power operators $D^{(k)}$ (`[HasseSchmidt1937]`, Section 6.3),
   $$D^{(k)}\bigl(u(x)^q\bigr) = 0 \qquad \text{for every } 1 \le k < q.$$
   Consequently, if we build $\Phi$ as a linear combination of low-degree basis functions multiplied
   by $q$-th powers,
   $$\Phi = \sum_{i = 1}^{M} s_i\,u_i^q,$$
   then applying $D^{(0)}, D^{(1)}, \dots, D^{(m-1)}$ ($m \le q$) **never differentiates the high-degree
   factor $u_i^q$**! Each derivative $D^{(k)}\Phi = \sum_i (D^{(k)} s_i) u_i^q$ lands in a space
   whose pole order grows only with the tiny "coefficient" functions $s_i$, not with $m \cdot q$!
3. **Linear-algebra dimension vs. degree (`[Stepanov1969]`, `[Bombieri1973]`):** Choosing $M$ large
   enough that the number of free coefficients in $(s_1, \dots, s_M)$ strictly exceeds the number of
   linear constraints imposed by $D^{(0)}\Phi = \dots = D^{(m-1)}\Phi \equiv 0$ on Frobenius points
   forces the pole degree $\deg(\Phi)_\infty$ to look like
   $$\deg(\Phi)_\infty \approx q \cdot (\text{small shift}) + c_g\,m^2 + m q / (\dots),$$
   so dividing by $m$ produces a bound with the signature two-term shape
   $$\frac{q}{m} + c_g\,m.$$
   Minimizing $\frac{q}{m} + c_g m$ over $m$ forces **$m \asymp \sqrt{q}$**, yielding an upper bound
   of order $q + O_g(\sqrt{q})$ — and pairing the upper bound over extensions $\mathbb F_{q^n}$ (or
   on quadratic twists) sharpens the constant to the exact Hasse–Weil bound $2g\sqrt{q}$!

### 6.1.2 Why "multiplicity over $\mathbb Z$" needs a new mechanism

Look back at Equation (5.2.2) in Chapter 5 (`proposition_size_bound`,
`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507`) [Lean, read]:
the normalized prime-sum bound in `core_gm` had the *exact same* algebraic shape,
$$\Lambda.\mathrm{Gm}(x) \lesssim \frac{x}{m} + m\,x^{O(\varepsilon)} \qquad\text{optimized at}\qquad m \asymp x^{1/2}!$$
Why couldn't Riemann, Landau, or Stepanov simply write down an auxiliary polynomial over $\mathbb Z$
with multiplicity $m \approx \sqrt{x}$? Three fundamental obstructions separate $\mathrm{Spec}\,\mathbb Z$
from a curve $C / \mathbb F_q$ [Expository]:

1. **No global constant field and no Frobenius endomorphism on $\mathbb Z$:** Over $\mathbb F_q(x)$,
   $\mathbb F_q$ is a subfield of constants ($D^{(1)} c = 0$ for all $c \in \mathbb F_q$) and
   $u \mapsto u^q$ is a ring endomorphism fixing $\mathbb F_q$ pointwise while annihilating
   $D^{(1)}, \dots, D^{(q-1)}$. Over $\mathbb Z$, any integer $n$ satisfies $(d/dn)(n) = 1$: there is
   no non-identity ring endomorphism of $\mathbb Z$, and reducing modulo $p$ changes the base ring
   at every prime $p$!
2. **Product formula vs. Riemann–Roch:** Over $\mathbb Z$ (or a number field $E$), the analogue of
   "$\#\text{zeros} = \#\text{poles}$" is the **Arakelov product formula** $\sum_v \log\lvert \alpha \rvert_v = 0$
   for $\alpha \in E^\times$, upgraded on higher-rank Hermitian vector bundles over $\mathrm{Spec}\,\mathcal O_E$
   to **Bost's slope inequality** (`Data.SlopeIneq`, `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:151` [Lean, read],
   instantiating the abstract `Prop` `Formalism.HN.SlopeIneq` at
   `src/Formalism/HarderNarasimhan/Statement.lean:91` whose full proof at
   `src/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean:507` is read in Chapter 9
   [Lean, read]): if a nonzero $\mathcal O_E$-linear
   evaluation map between Hermitian lattices is highly divisible by prime ideals $\mathfrak p \mid p$
   at finite places while having bounded archimedean operator norm at infinite places, then the sum
   of its $\mathfrak p$-adic valuation orders is bounded above by the archimedean height plus slope
   spread!
3. **Replacing $D^{(0)}, \dots, D^{(m-1)}$ by an $m$-step chain of theta lifts:** If high $p$-adic
   valuation $\operatorname{ord}_{\mathfrak p}(\det \text{ or period}) \ge m \cdot (\text{signal})$
   at primes $p$ inert in $K = \mathbb Q(\sqrt{-d})$ replaces $m$-fold vanishing $D^{(k)}\Phi(P) = 0$,
   how do we create $m$ independent layers of $p$-adic divisibility without squaring the archimedean
   height? According to Alpöge's note (`remark.pdf` p. 1, p. 3 item 2, and p. 4 items 8–10, 13–14)
   [Paper; remark pp. 1, 3–4], the archive replaces $m$ derivatives on one curve by **$m$ iterated theta lifts
   $U(X_0) \to U(X_1) \to \dots \to U(X_m)$ between totally definite unitary groups** over the CM
   host $E/F$ (Chapter 7), where each step twists by a carefully spaced Hecke character $\mu_j$ so
   that at primes $p$ inert in $K = \mathbb Q(\sqrt{-d})$, local supersingular/theta-kernel vanishing
   contributes one fresh unit of Riesz prime-sum divisibility (`SDiv = ∑ t, m * (...)`,
   `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:129` [Lean, read]) while the congruence/Selmer cost per step stays linear
   in $m$ rather than quadratic!

---

## 6.2 Worked examples

Before proving the general theorems, we carry out two explicit calculations you can check with pen
and paper: first, an explicit multiplicity-$2$ Stepanov polynomial over $\mathbb F_5$ and $\mathbb F_7$
whose derivative vanishes at every rational $x$-coordinate; second, the $m$-optimization on a
hyperelliptic curve compared side-by-side with `evenCeil` and `mAt` in `EvenCeil.lean`.

### 6.2.1 Hand-computed Stepanov polynomial on $y^2 = x^3 + x + 1$ over $\mathbb F_5$ and $y^2 = x^3 + 2$ over $\mathbb F_7$

Let $p \ge 5$ be an odd prime, put $s := \frac{p - 1}{2}$ (note $s \equiv -2^{-1} \pmod p$), and let
$f(x) \in \mathbb F_p[x]$ be a monic squarefree cubic defining the elliptic curve $E : y^2 = f(x)$
over $\mathbb F_p$ [Expository].

At $m = 1$, $f(x)^s - 1$ had degree $3s = \frac{3(p-1)}{2}$ and gave nothing nontrivial. Let us ask
for **multiplicity $m = 2$** on the $x$-line, using a linear combination of $1$, $f(x)^s$, and the
Frobenius binomial $(x^p - x)$:
$$H_0(x) := P_0(x) + Q_0(x)\,f(x)^s \in \mathbb F_p[x].$$
Watch how differentiating $f(x)^s$ in $\mathbb F_p[x]$ stays inside $\mathbb F_p[x] + \mathbb F_p[x] f(x)^s$
once we multiply by $f(x)$! Since $s = \frac{p-1}{2}$,
$$f(x)\,\frac{d}{dx}\bigl(f(x)^s\bigr) = s\,f'(x)\,f(x)^s.$$
Therefore $f(x)\,H_0'(x) = P_1(x) + Q_1(x)\,f(x)^s$ with
$$P_1(x) = f(x) P_0'(x), \qquad Q_1(x) = f(x) Q_0'(x) + s\,f'(x) Q_0(x).$$
At any $x_0 \in \mathbb F_p$ where $f(x_0)$ is a **nonzero square** in $\mathbb F_p$, we have
$x_0^p - x_0 = 0$ and $f(x_0)^s = 1$, so $H_0(x_0) = P_0(x_0) + Q_0(x_0)$ and
$f(x_0) H_0'(x_0) = P_1(x_0) + Q_1(x_0)$. To make **both** vanish modulo $(x^p - x)$:

- Set $P_0(x) := -Q_0(x) + C(x)(x^p - x)$, so $P_0(x) + Q_0(x) = C(x)(x^p - x) \equiv 0 \pmod{x^p - x}$
  automatically!
- Differentiate $P_0(x)$ in characteristic $p$, where $(x^p - x)' = p x^{p-1} - 1 = -1$:
  $$P_0'(x) = -Q_0'(x) + C'(x)(x^p - x) - C(x) \equiv -Q_0'(x) - C(x) \pmod{x^p - x}!$$
- Substitute into $P_1 + Q_1$ modulo $(x^p - x)$: the $Q_0'$ terms cancel identically, leaving
  $$P_1(x) + Q_1(x) \equiv f(x)\bigl(-Q_0'(x) - C(x)\bigr) + f(x) Q_0'(x) + s\,f'(x) Q_0(x)
  = s\,f'(x) Q_0(x) - f(x) C(x) \pmod{x^p - x}!$$

Look at $s f'(x) Q_0(x) - f(x) C(x) = 0$: we can solve it **explicitly with zero linear algebra** by
choosing $Q_0(x) := f(x)$ and $C(x) := s\,f'(x)$! That gives the explicit closed-form Stepanov
polynomial
$$H_0(x) = f(x)\bigl(f(x)^{(p-1)/2} - 1\bigr) + \frac{p - 1}{2}\,f'(x)\,(x^p - x) \in \mathbb F_p[x]$$
together with its exact derivative (using $1 + \frac{p-1}{2} = \frac{p+1}{2}$ in $\mathbb F_p$)
$$H_0'(x) = \frac{p + 1}{2}\,f'(x)\bigl(f(x)^{(p-1)/2} - 1\bigr) + \frac{p - 1}{2}\,f''(x)\,(x^p - x)$$
[Expository]! Check three facts immediately:

1. **Guaranteed non-vanishing:** Since $f$ is monic of degree $3$, $\deg\bigl(f^{(p+1)/2}\bigr) = \frac{3(p+1)}{2}$,
   whereas $\deg\bigl(f'(x)(x^p - x)\bigr) = p + 2$. For every prime $p \ge 5$,
   $\frac{3(p+1)}{2} - (p + 2) = \frac{p - 1}{2} \ge 2 > 0$, so the two top degrees cannot cancel:
   $H_0(x)$ is **monic of exact degree $\frac{3(p+1)}{2}$**!
2. **Multiplicity at every affine point of $E(\mathbb F_p)$:** For each $x_0 \in \mathbb F_p$:
   - if $f(x_0) \in (\mathbb F_p^\times)^2$ (giving $2$ affine points $(x_0, \pm y_0) \in E(\mathbb F_p)$),
     then $x_0^p - x_0 = 0$ and $f(x_0)^{(p-1)/2} - 1 = 0$, so $H_0(x_0) = H_0'(x_0) = 0$ and
     $\operatorname{ord}_{x_0}(H_0) \ge 2$;
   - if $f(x_0) = 0$ (giving $1$ affine $2$-torsion point $(x_0, 0) \in E(\mathbb F_p)$), then
     $H_0(x_0) = 0 \cdot (-1) + 0 = 0$, so $\operatorname{ord}_{x_0}(H_0) \ge 1$.
   Summing over all $x_0 \in \mathbb F_p$ already proves, in four lines of Freshman algebra,
   $$\#E_{\mathrm{aff}}(\mathbb F_p) \le \sum_{x_0 \in \mathbb F_p} \operatorname{ord}_{x_0}(H_0)
   \le \deg H_0 = \frac{3(p + 1)}{2}, \qquad\text{so}\qquad \#E(\mathbb F_p) \le \frac{3}{2}p + \frac{5}{2} < 2p + 1!$$
3. **Explicit numerical check at $p = 5$ and $p = 7$:**
   - Take **$p = 5$ ($s = 2$) and $E : y^2 = f(x) = x^3 + x + 1$**. Evaluating $f(x) \bmod 5$ gives
     $f(0) = 1$, $f(1) = 3$ (non-square mod $5$), $f(2) = 11 \equiv 1$, $f(3) = 31 \equiv 1$, and
     $f(4) = 69 \equiv 4$, so $E(\mathbb F_5)$ has $8$ affine points plus $P_\infty$, i.e.
     $\#E(\mathbb F_5) = 9 = 5 + 1 + 3$ (saturating $\lvert 9 - 6 \rvert = 3 \le \lfloor 2\sqrt{5}\rfloor = 4$).
     Expanding $H_0(x) = (x^3 + x + 1)^3 - (x^3 + x + 1) + 2(3x^2 + 1)(x^5 - x)$ in $\mathbb F_5[x]$ gives
     $$H_0(x) = x^9 + 4x^7 + 3x^6 + x^4 + 2x^3 + 3x^2 = x^2(x - 2)^3(x - 3)^2(x - 4)^2 \in \mathbb F_5[x]!$$
     Notice how $H_0$ has degree $9$, vanishes to order $2, 3, 2, 2$ at $x_0 = 0, 2, 3, 4$ (and is
     nonzero, $H_0(1) = 4$, at the lone non-residue point $x_0 = 1$), and gives
     $\#E_{\mathrm{aff}}(\mathbb F_5) \le 2\lfloor 9/2 \rfloor = 8$, **hitting the exact point count
     $\#E(\mathbb F_5) = 9$ on the nose**!
   - Take **$p = 7$ ($s = 3$) and $E' : y^2 = f(x) = x^3 + 2$**. In $\mathbb F_7[x]$,
     $(x^3 + 2)^4 = x^{12} + 8x^9 + 24x^6 + 32x^3 + 16 \equiv x^{12} + x^9 + 3x^6 + 4x^3 + 2 \pmod 7$,
     while $3(3x^2)(x^7 - x) \equiv 2x^9 - 2x^3 \pmod 7$, so
     $$H_0(x) = (x^{12} + x^9 + 3x^6 + 3x^3) + (2x^9 - 2x^3)
     = x^{12} + 3x^9 + 3x^6 + x^3 = x^3(x^3 + 1)^3 = x^3(x - 3)^3(x - 5)^3(x - 6)^3 \in \mathbb F_7[x]!$$
     Without solving a single equation by brute force, the Stepanov combination factors cleanly into
     cubes at the exact four $x$-coordinates $\{0, 3, 5, 6\} \subset \mathbb F_7$ where $x^3 + 2 \in \{1, 2, 4\}$
     is a square!

### 6.2.2 Scaling the multiplicity $m$ on hyperelliptic curves vs. `evenCeil` in `EvenCeil.lean`

Why did $m = 2$ reduce the trivial coefficient $2p$ down to $\frac{3}{2}p$, and how does larger $m$
push the coefficient of $p$ all the way down to $1$ with a $O(\sqrt{p})$ remainder?

Suppose $y^2 = f(x)$ has odd degree $d = 2g + 1$ over $\mathbb F_q$ ($q$ odd; in Section 6.4 we allow
arbitrary $q = p^r$ using Hasse–Schmidt derivations $D^{(k)}$ so $m$ is *not* stopped by small
characteristic $p$!). When we build an auxiliary function $\Phi = \sum_{j=0}^1 \sum_{\ell=0}^{L-1} a_{j,\ell}(x) y^j x^{\ell q}$
with $\deg a_{j,\ell} \le K$ that vanishes to even multiplicity $m$ at every rational point
$P \in C(\mathbb F_q)$ [Expository]:

1. **Free parameters:** $2 L (K + 1)$ coefficients in $\mathbb F_q$.
2. **Linear constraints:** $m$ vanishing conditions ($k = 0, \dots, m - 1$), each reducing modulo
   $y^q = f(x)^{(q-1)/2} y$ and $x^q = x$ to a polynomial of degree at most
   $K + \frac{d(q-1)}{2} + (L - 1) + (m - 1)(d - 1)$ (or, in Bombieri's Riemann–Roch setup over
   $\mathbb F_{q^2}$ `[Bombieri1973]`, a section in $\mathcal L\bigl((m K' + q L')P_\infty\bigr)$).
   Requiring $\#\text{parameters} > \#\text{constraints}$ roughly sets $2 L \approx m\bigl(1 + \frac{d}{2K/q}\bigr)$,
   and dividing the pole order at $P_\infty$ by $m$ yields an upper bound of the form
   $$N_1 \le q + \frac{q}{L} + c_{d}\,L\,m \qquad\text{with } L \asymp m \asymp \sqrt{q},$$
   balancing $\frac{q}{m} + c_d m$ at **$m \asymp \sqrt{q}$**!

Now open `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:11–25`
(read in full, `[Lean, read]`) and compare the archive's parameter schedule at scale $s = (x, \varepsilon)$:

```lean
def evenCeil (y : ℝ) : ℕ := 2 * ⌈y / 2⌉₊
def eAt : ℕ := Nat.clog 2 ⌈s.x ^ (2 + 8 * s.eps)⌉₊
def nAt : ℕ := 2 ^ eAt s
def mAt : ℕ := evenCeil (Real.sqrt (s.x * s.delta1))
def kAt : ℕ := evenCeil (s.x ^ (9 / 2 + 10 * s.eps))
```

Look at concrete numbers when $x = 10^4$ and $\varepsilon = 1/64 < 1/52$ (`Scale.delta1 = x^{-ε/8}`,
`src/Formalism/LocalRingCardinality/DataParams₂.lean:45` [Lean, read]):

- $\delta_1 = (10^4)^{-1/512} \approx 0.9822$, so $\sqrt{x\,\delta_1} \approx 99.10$, and
  `mAt = 2 * ⌈99.10 / 2⌉₊ = 100` — an **even** chain length $m = 100 = x^{1/2}$ (`Ranks.m_even`,
  `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:51` [Lean, read]), playing the exact role of even vanishing multiplicity $m$!
- $x^{2 + 8\varepsilon} = (10^4)^{2 + 1/8} = 10^{8.5} \approx 3.16 \times 10^8$, so `eAt = 29` and
  `nAt = 2^29 = 536,870,912` — the size of the real $2$-cyclotomic host layer $\varphi.\mathrm{ord}$,
  which Alpöge compares (`remark.pdf` p. 4, item 11: *"Iwasawa tower via analogy to pigeonhole on
  $\mathbb F_{q^n}/\mathbb F_q$"* [Paper; remark p. 4]) to passing to a controlled field tower to
  create linear-algebra room!
- `kAt` $= 2\lceil (10^4)^{9/2 + 10/64}/2 \rceil = 4{,}216{,}965{,}034{,}285{,}822{,}486 \approx 4.22 \times 10^{18}$
  (`10^{18.625}`) — the auxiliary Hermitian rank parameter (`Ranks.k_even`, `:50`) chosen large enough
  that the word-ratio error $x m / k$ (`SZ.T2`) is negligible while $k / n^2 \approx 14.63 \le x^{1/2 - \varepsilon} \approx 86.60$
  (`SZ.T4`) stays well below the square-root barrier!

---

## 6.3 Definitions

We begin with the exact algebraic definitions of Hasse–Schmidt derivations and curve function fields
needed for Stepanov–Bombieri, followed by the formal definitions of node `P7` in the Lean archive.

### 6.3.1 Hasse–Schmidt higher derivations and curve function fields

Why do we need Hasse–Schmidt derivations rather than repeated ordinary differentiation $(d/dx)^k$?
Because over any field $K$ of prime characteristic $p > 0$, $(d/dx)^p(x^n) = n(n-1)\cdots(n-p+1)x^{n-p} = 0$
for **every** $n \ge 0$, so $(d/dx)^p \equiv 0$ identically! Thus ordinary derivatives cannot detect
vanishing multiplicity $m > p$ — which kills the $\sqrt{q}$ optimization whenever $q = p^r$ ($r \ge 3$)
has $\sqrt{q} = p^{r/2} > p$! Hasse and F. K. Schmidt `[HasseSchmidt1937]` solved this permanently by
dividing out $k!$ *before* reducing modulo $p$.

**Definition 6.1 (Hasse–Schmidt higher derivations on polynomials and function fields).** Let $K$ be
any field (in particular $K = \mathbb F_q$ or $\overline{\mathbb F}_q$) `[HasseSchmidt1937]`,
`[Schmidt1976]` [Expository]:

1. **On the polynomial ring $K[x]$:** Introduce a formal power-series indeterminate $T$ and consider
   the $K$-algebra homomorphism $\Delta_T : K[x] \to K[x][[T]]$ sending $x \mapsto x + T$. Define
   $K$-linear operators $D^{(k)} : K[x] \to K[x]$ ($k \ge 0$) as the Taylor coefficients of $\Delta_T$:
   $$F(x + T) = \sum_{k = 0}^{\infty} \bigl(D^{(k)} F\bigr)(x)\,T^k \qquad\text{in } K[x][[T]].$$
   Explicitly, on monomials $x^n$ ($n \ge 0$),
   $$D^{(k)}(x^n) = \binom{n}{k}\,x^{n - k} \quad (0 \le k \le n), \qquad D^{(k)}(x^n) = 0 \quad (k > n),$$
   where $\binom{n}{k} \in \mathbb Z$ is projected into $K$ (so $D^{(0)} = \mathrm{id}$, $D^{(1)} = d/dx$,
   and for $k! \neq 0$ in $K$, $D^{(k)} = \frac{1}{k!}(d/dx)^k$, whereas in characteristic $p > 0$
   $D^{(p)}(x^p) = \binom{p}{p} x^0 = 1 \neq 0$!).
2. **Unique extension to rational and separable algebraic functions:** Because $\Delta_T(F) = F(x) + \sum_{k \ge 1} (D^{(k)}F) T^k$
   has invertible constant term $F(x) \in K(x)^\times$ whenever $F \neq 0$, $\Delta_T$ extends
   uniquely to a field homomorphism $\Delta_T : K(x) \to K(x)((T))$, and by Hensel's lemma in the
   complete discrete valuation ring $L[[T]]$ to **any finite separable extension $L / K(x)$** (given
   an étale local parameter $t$ at a smooth point $P \in C(\overline{K})$ with completion
   $\widehat{\mathcal O}_{C,P} \cong \overline{K}[[t]]$, setting $f(t + T) = \sum_{k \ge 0} (D_t^{(k)} f)(t)\,T^k$
   defines $D_t^{(k)}$ on the whole function field $\overline{K}(C)$!).
3. **Riemann–Roch pole spaces $\mathcal L(r P_\infty)$:** Let $C / \mathbb F_q$ be a smooth projective
   geometrically connected curve of genus $g \ge 0$ with a fixed rational point $P_\infty \in C(\mathbb F_q)$.
   For each integer $r \ge 0$, write
   $$\mathcal L(r P_\infty) := \{0\} \cup \bigl\{u \in \mathbb F_q(C)^\times : \operatorname{div}(u) + r P_\infty \ge 0\bigr\}$$
   for the finite-dimensional $\mathbb F_q$-vector space of functions regular on $C \setminus \{P_\infty\}$
   with a pole of order at most $r$ at $P_\infty$. By the Riemann–Roch inequality (whose elementary
   lower bound $\dim_{\mathbb F_q}\mathcal L(r P_\infty) \ge r + 1 - g$ and equality for $r > 2g - 2$
   on plane/hyperelliptic curves require only counting monomials!), for a hyperelliptic curve
   $y^2 = f(x)$ of odd degree $d = 2g + 1$ with unique point $P_\infty$ at infinity,
   $\operatorname{ord}_{P_\infty}(x) = -2$, $\operatorname{ord}_{P_\infty}(y) = -d = -(2g+1)$, and
   $$\mathcal L(r P_\infty) = \operatorname{Span}_{\mathbb F_q}\bigl\{x^a y^b : a \ge 0,\ b \in \{0, 1\},\ 2a + (2g+1)b \le r\bigr\}$$
   has exact dimension $r + 1 - g$ for every $r \ge 2g$ `[Schmidt1976]`!

### 6.3.2 Formal P7 chain data (`Data`, `SizeData₂`, `evenCeil`, and `ChainTied`)

Now compare Definition 6.1 with how the Lean archive packages "multiplicity $m$ over $\mathbb Z$" in
node `P7`. Note carefully a naming detail in the archive that can confuse first-time readers: the
identifier `SizeData₂` appears in **two** namespaces [Lean, read]:

- `Formalism.BasicNotions.SizeData₂ (D : D7)` (`src/Formalism/LocalRingCardinality/DataParams₂.lean:76–182`)
  is a concrete **data `structure`** attached to a global unitary-chain datum `D : D7`, storing the
  scale `sc : Scale`, integer top/bottom cutoffs `aT, bT`, finite place support `supp`, per-lift
  inert-prime divisibility gains `gain j w`, Fourier/period terms `F j w`, congruence error exponents
  `E u j w`, and Harish-Chandra window bounds `win_thick`, `win_top`, `win_thin` (through `lenMN` at `:182`),
  while `namespace SizeData₂` (`:184–245`) defines the derived totals `Fo` (`:218`), `Ga` (`:220`),
  `Ee` (`:222`), `MAIN` (`:232`), and the `D`-level $Ш^1$ sum `VV l` (`:238`, depending on `D` and `l`
  without taking a `SizeData₂ D` term);
- `Formalism.LFunctionChainParameters.LChain.SizeData₂ (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : Prop`
  (`src/Formalism/SizeWindowBrackets/SChain.lean:17`) is the **11-clause `Prop` conjunction** on the
  abstract numerical record `Data U0 W Top m f` (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:37`),
  bridged to `D7` by `TieGlobal`, `TieLocal`, `TieArith`, and `ChainTied`
  (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:50,63,84,97`)!

**Definition 6.2 (Abstract Arakelov–Stepanov record `Data` and the 11-clause proposition `SizeData₂`, `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:37`, `src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:19–35`, `src/Formalism/SizeWindowBrackets/SChain.lean:17`).**
Fix a finite index set $U_0$ (shift cosets in $H = \varphi.A$), nonempty finite word sets $W(u_0)$
($u_0 \in U_0$), a finite set `Top` of cardinality $n_T = \lvert TT \rvert$, chain length $m \in \mathbb N$,
and CM-type place count $f = 2\lvert H \rvert$. A record `Dd : Data U0 W Top m f` packages scalar
scales $(x, \varepsilon, a, b, b', k, L, L_a, B_0, N_c, \gamma, L'/L, v, \mathrm{lg}, \log\Gamma)$,
top thresholds $a_t$ ($t \in \mathrm{Top}$), place weights $w_{u_0, j, \rho} > 0$, word lattice
ranks $d(u_0, u) > 0$, level primes $T(u_0, u) > 0$, Hermitian minimum/maximum slopes
$(\mu_N, \mu_{\max, N}, \mu_M, \mu_{\max, M})$, word heights $h(u_0, u)$, per-lift congruence
losses $\mathrm{Ee}_J(u_0, u, j)$, dual target slopes $(\mu_{CC}, \mu_{\min, CC})$, total gains
$\mathrm{Ga}(u_0)$, Fourier shifts $\mathrm{Fo}(u_0)$, inert-prime sums $\mathrm{ASK}(u_0)$,
in-out losses $\mathrm{IO}(u_0)$, and near-orthogonality defect parameters $(\mathrm{HH}, \delta, \eta, e)$
[Lean, read].

Given nonnegative constants `C : Consts` (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:15`) and $X'' \in \mathbb R$,
`SizeData₂ Dd C Xpp` (`src/Formalism/SizeWindowBrackets/SChain.lean:17–19`) is the conjunction of **eleven clauses** [Lean, read]:

1. `Dd.HidaSetting C` (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:111`): positivity/ordering of scales, weights
   $w_{u_0,j,\rho} > 0$, lattice ranks $d(u_0, u) > 0$, $\mu_N \le \mu_{\max, N}$, $\bar\delta < 1$,
   and $0 \le \bar e \le 1/4$.
2. `Dd.DIV C` (`:118`, **the global divisibility inequality**): for every $(u_0, u)$,
   $$\mu_{CC}(u_0) + h(u_0, u) - \mathrm{Fo}(u_0)
   \le \sum_{t \in \mathrm{Top}} \Bigl[m\bigl(\mathrm{ph}(a_t) - a_t \log\Omega\bigr) - a_t \log T(u_0, u)\Bigr]
   + c_{\mathrm{Div}} n_T a L_a + c_{\mathrm{Div}} m (B_0 + N_c) x^{e_{\mathrm{Div}}\varepsilon},$$
   where $\mathrm{ph}(y) = y\log y - y$ and $\log\Omega = \gamma + \log(\pi / v) - \mathrm{LpL}$.
3. `EComp5 Dd C` (`src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:24`, **congruence-loss concentration**):
   $\bigl\lvert \mathrm{Ee}(u_0, u) - m\,\mathrm{sum}_A\cdot\mathrm{lg} \bigr\rvert \le c_E m B_0$,
   where $\mathrm{Ee}(u_0, u) = \sum_{j=0}^{m-1} \mathrm{Ee}_J(u_0, u, j)$ and $\mathrm{sum}_A = \sum_t a_t$.
4. `Dd.HComp C` (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:126`, **word-to-word height variation**): for all $u, u' \in W(u_0)$,
   $\bigl\lvert (h(u) + \mathrm{sum}_A\log T(u)) - (h(u') + \mathrm{sum}_A\log T(u')) \bigr\rvert \le c_H(n_T a L_a + m B_0)$.
5. `Count5 Dd C` (`src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:27`, **level-prime size bracket**):
   $\log T(u_0, u)$ is bounded below by
   $\sum_{j=0}^{m-1} \frac{1}{f}\sum_{\rho=1}^f \log\bigl(w_{u_0,j,\rho} v / \pi\bigr) + m\,\mathrm{lg} - c_{\mathrm{Count}}(L_a + m^2 L_a / k)$,
   bounded above by $c_{\mathrm{Count}} m L$, and varies across $u, u' \in W(u_0)$ by at most $c_{\mathrm{Count}}\log k$.
6. `Dd.Slopes C` (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:139`, **source lattice archimedean slopes**):
   $-c_{\mathrm{Slope}} n_T a L_a (1 + m/k) \le \mu_M(u_0, u)$ and $\mu_{\max, M}(u_0, u) \le c_{\mathrm{Slope}} n_T a L_a$.
7. `QuotientSlopeBoundsWith Dd C Xpp` (`src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:19`, **quotient slope transfer across $m$ lifts**):
   $$\mu_M + \mathrm{Ga} + \mathrm{Fo} - \mathrm{Ee} - \mathrm{Lo}_5 \le \mu_N,
   \qquad
   \mu_{\max, N} \le \mu_{\max, M} + \mathrm{Ga} + \mathrm{Fo} - \mathrm{Ee} + c_{\mathrm{Sl1}} m B_0.$$
8. `LossBounds Dd C` (`:34`, **inert-prime vs. gain comparison**):
   $\mathrm{ASK}(u_0) - \mathrm{Ga}(u_0) \le \mathrm{Lo}_P$ and $\mathrm{IO}(u_0) \le \mathrm{Lo}_P$,
   where $\mathrm{Lo}_P = c_{\mathrm{Loss}} n_T m b\,x^{e_{\mathrm{Loss}}\varepsilon}$.
9. `Dd.SlopeIneq` (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:151`, **Bost / Harder–Narasimhan near-orthogonal slope inequality**):
   for the rank-weighted mean slope $s(u_0) := \frac{\sum_u d(u)(\mu_N(u) - h(u))}{\sum_u d(u)}$ and
   slope spread $u_F(u_0) := \max_u(\mu_{\max, N}(u) - h(u)) - s(u_0) \ge 0$,
   $$s(u_0) - \log\lvert W(u_0) \rvert
   - (1 - \delta)^{-1}\Bigl(4 u_F \log\Bigl(1 + \frac{\mathrm{HH}}{u_F}\Bigr) + (\eta + 4\sqrt{e})\,\mathrm{HH}\Bigr)
   \le \mu_{CC}(u_0).$$
10. `Dd.HHBound C` (`:158`): $s(u_0) - \mu_{\min, CC}(u_0) \le \mathrm{HH}(u_0)$ and $0 < \mathrm{HH}(u_0) \le x^{c_{\mathrm{HH}}} b$.
11. `Dd.FParams` (`:161`): $0 \le \delta(u_0) \le \bar\delta$, $0 \le \eta(u_0) \le \bar\eta$, and $0 \le e(u_0) \le \bar e$.

---

## 6.4 Lemmas and proofs

We now give complete, self-contained proofs of (A) the classical Stepanov–Bombieri curve bound and
its exponential-sum corollaries over finite fields, and (B) the archive's algebraic P7 deduction
`each_unit_bound_statement` from `SizeData₂`.

### 6.4.1 Hasse–Schmidt derivations and the multiplicity criterion

**Lemma 6.1 (Algebraic laws and multiplicity criterion for Hasse–Schmidt derivations).** *Let $K$ be
any field (of characteristic $0$ or $p > 0$), and let $(D^{(k)})_{k \ge 0}$ be the Hasse–Schmidt
derivations on $K[x]$ (or with respect to an étale local parameter $t$ in $\overline{K}[[t]]$ at a
smooth point $P$ of a curve $C / K$)* `[HasseSchmidt1937]`, `[Schmidt1976]` [Expository]:

1. *(Product / Leibniz rule)* *For all $F, G$ and $k \ge 0$,
   $D^{(k)}(FG) = \sum_{i + j = k} D^{(i)}F \cdot D^{(j)}G$.*
2. *(Composition / iteration rule)* *For all $i, j \ge 0$,
   $D^{(i)} \circ D^{(j)} = \binom{i + j}{i}\,D^{(i + j)}$.*
3. *($q$-th power annihilation in characteristic $p$)* *Suppose $\operatorname{char} K = p > 0$ and
   $q = p^r$ ($r \ge 1$). Then for every $U$ and every $k \ge 0$,*
   $$D^{(k)}(U^q) = \begin{cases} \bigl(D^{(k/q)} U\bigr)^q & \text{if } q \mid k,\\ 0 & \text{if } q \nmid k.\end{cases}$$
   *In particular, for every $F, U$ and every $0 \le k < q$, $D^{(k)}(F \cdot U^q) = (D^{(k)} F)\cdot U^q$.*
4. *(Exact vanishing-multiplicity criterion)* *Let $P \in C(\overline{K})$ be a smooth point with
   local uniformizer $t$ ($\operatorname{ord}_P(t) = 1$). For any $f \in \overline{K}(C)$ regular at
   $P$ and any integer $m \ge 1$,*
   $$\operatorname{ord}_P(f) \ge m \iff \bigl(D_t^{(k)} f\bigr)(P) = 0 \quad \text{for all } 0 \le k < m.$$

*Proof.*
(1) Since $\Delta_T(FG) = \Delta_T(F)\,\Delta_T(G)$ in $R[[T]]$ ($R = K[x]$ or $\overline{K}[[t]]$),
equating coefficients of $T^k$ in $\bigl(\sum_{i \ge 0} D^{(i)}F\,T^i\bigr)\bigl(\sum_{j \ge 0} D^{(j)}G\,T^j\bigr)$
immediately gives $\sum_{i+j=k} D^{(i)}F \cdot D^{(j)}G$.

(2) Introduce two commuting formal variables $S, T$. Expanding $F(x + S + T)$ first in $T$ and then
in $S$ gives $\sum_{j \ge 0} \sum_{i \ge 0} D^{(i)}(D^{(j)} F)\,S^i T^j$; expanding directly in
$(S + T)^n = \sum_{i+j=n} \binom{i+j}{i} S^i T^j$ gives $\sum_{i, j \ge 0} \binom{i+j}{i} D^{(i+j)}F\,S^i T^j$.
Comparing coefficients of $S^i T^j$ yields $D^{(i)} \circ D^{(j)} = \binom{i+j}{i} D^{(i+j)}$.

(3) In characteristic $p$, the Frobenius map $z \mapsto z^q$ ($q = p^r$) is a ring homomorphism on
$R[[T]]$ sending $T \mapsto T^q$. Hence
$$\sum_{k = 0}^{\infty} D^{(k)}(U^q)\,T^k = \Delta_T(U^q) = \bigl(\Delta_T(U)\bigr)^q
= \Bigl(\sum_{\ell = 0}^{\infty} (D^{(\ell)} U)\,T^\ell\Bigr)^q
= \sum_{\ell = 0}^{\infty} (D^{(\ell)} U)^q\,T^{\ell q}.$$
Matching powers of $T$ gives $D^{(k)}(U^q) = 0$ whenever $q \nmid k$ and $(D^{(k/q)}U)^q$ when $q \mid k$.
For $0 \le k < q$, only $j = 0$ in (1) has $q \mid j$, so $D^{(k)}(F U^q) = (D^{(k)}F)\,D^{(0)}(U^q) = (D^{(k)}F) U^q$.

(4) In the completion $\widehat{\mathcal O}_{C,P} \cong \overline{K}[[t]]$, write $f = \sum_{n = 0}^{\infty} c_n t^n$
($c_n \in \overline{K}$). Then $\operatorname{ord}_P(f) \ge m \iff c_0 = c_1 = \dots = c_{m-1} = 0$.
On the other hand, applying $\Delta_T(t^n) = (t + T)^n = \sum_{k=0}^n \binom{n}{k} t^{n-k} T^k$ and
evaluating at $t = 0$ (which corresponds to $P$) kills every term with $n > k$, leaving
$\bigl(D_t^{(k)} f\bigr)(P) = \binom{k}{k} c_k = c_k$ for all $k \ge 0$! Hence
$\operatorname{ord}_P(f) \ge m \iff (D_t^{(k)} f)(P) = 0$ for all $0 \le k < m$. $\square$

### 6.4.2 Linear independence of Frobenius powers and the Stepanov–Bombieri theorem

We now prove Bombieri's clean general version `[Bombieri1973]` of Stepanov's theorem `[Stepanov1969]`
for any smooth projective geometrically connected curve $C / \mathbb F_q$ of genus $g$ (assuming only
the Riemann–Roch inequality $\dim_{\mathbb F_q} \mathcal L(r P_\infty) \ge r + 1 - g$ and the degree
inequality $\#\text{zeros} \le \#\text{poles}$ for rational functions on $C$, both of which are
completely elementary on plane/hyperelliptic models `[Schmidt1976]`).

**Lemma 6.2 (Linear independence over Frobenius $q$-th powers).** *Let $C / \mathbb F_q$ be a smooth
projective geometrically connected curve with a rational point $P_\infty \in C(\mathbb F_q)$, and let
$u_1, \dots, u_B \in \mathcal L(\ell P_\infty)$ be $\mathbb F_q$-linearly independent functions. If
$s_1, \dots, s_B \in \mathcal L(r P_\infty)$ with **$r < q$**, then*
$$\sum_{b = 1}^{B} s_b\,u_b^q = 0 \text{ in } \mathbb F_q(C) \iff s_1 = s_2 = \dots = s_B = 0.$$
*(Classical: `[Bombieri1973]`, Lemma 1, p. 236.)* [Expository]

*Proof.* Suppose $s_1, \dots, s_B \in \mathcal L(r P_\infty)$ are not all zero. Because
$\operatorname{ord}_{P_\infty}$ is a discrete valuation on $\mathbb F_q(C)$ and $u_1, \dots, u_B$
are $\mathbb F_q$-linearly independent, Gaussian elimination over $\mathbb F_q$ produces a new basis
$u_1', \dots, u_B'$ of $\operatorname{Span}_{\mathbb F_q}(u_1, \dots, u_B)$ whose pole orders
$d_b := -\operatorname{ord}_{P_\infty}(u_b')$ satisfy $d_1 < d_2 < \dots < d_B$ in $\mathbb Z$; writing
$\sum_{b=1}^B s_b u_b^q = \sum_{b=1}^B s_b' (u_b')^q$ via the invertible $\mathbb F_q$-change-of-basis
matrix (using $(c u)^q = c u^q$ for $c \in \mathbb F_q$) leaves $s_b' \in \mathcal L(r P_\infty)$ not
all zero.

Now examine $\operatorname{ord}_{P_\infty}(s_b')$ for each $b$ with $s_b' \neq 0$: since $s_b'$ has
no poles outside $P_\infty$ and pole order at most $r$ at $P_\infty$, we have $\operatorname{ord}_{P_\infty}(s_b') \ge -r$;
on the other hand, if $\operatorname{ord}_{P_\infty}(s_b') > 0$, then $s_b'$ would be regular everywhere
on the projective curve $C$ and vanish at $P_\infty$, forcing $s_b' = 0$. Thus
$$-r \le \operatorname{ord}_{P_\infty}(s_b') \le 0, \qquad\text{so}\qquad
\operatorname{ord}_{P_\infty}\bigl(s_b' (u_b')^q\bigr) = \operatorname{ord}_{P_\infty}(s_b') - q d_b \in [-r - q d_b,\ -q d_b].$$
Because $d_1 < d_2 < \dots < d_B$ are integers and **$r < q$**, for every $b < b'$ we have
$-q d_{b'} \le -q(d_b + 1) = -q d_b - q < -q d_b - r$, so the intervals $[-r - q d_b, -q d_b]$ are
**pairwise disjoint**! By the strict ultrametric triangle inequality for $\operatorname{ord}_{P_\infty}$,
a nonempty sum of nonzero terms with pairwise distinct valuations at $P_\infty$ cannot vanish. $\square$

**Theorem 6.3 (The Stepanov–Bombieri theorem: Hasse–Weil bound for curves over finite fields).** *Let
$C / \mathbb F_q$ be a smooth projective geometrically connected curve of genus $g \ge 0$. Then*
$$\bigl\lvert \#C(\mathbb F_q) - (q + 1) \bigr\rvert \le 2g\sqrt{q}.$$
*(Classical: `[Hasse1936]` for $g = 1$, `[Weil1948]` for all $g$, elementary auxiliary-polynomial proof
by `[Stepanov1969]`, `[Bombieri1973]`, `[Schmidt1976]`.)* [Expository]

*Proof.* For $g = 0$, every smooth projective geometrically connected genus-$0$ curve over $\mathbb F_q$
is isomorphic to $\mathbb P^1_{\mathbb F_q}$ with $\#C(\mathbb F_q) = q + 1$; assume $g \ge 1$. We
prove the bound in three clean steps following `[Bombieri1973]` and `[Schmidt1976]`.

**Step 1: Stepanov upper bound $\#C(\mathbb F_Q) \le Q + C_0 Q^{1/2}$ over any large extension $\mathbb F_Q = \mathbb F_{q^n}$.**
Fix a base extension $\mathbb F_{q_1}$ over which $C$ has at least one rational point $P_\infty \in C(\mathbb F_{q_1})$,
and pick a separating variable $t \in \mathcal L((2g + 1)P_\infty) \setminus \mathbb F_{q_1}(C)^p$:
such a $t$ exists because $\dim_{\mathbb F_{q_1}}\mathcal L((2g+1)P_\infty) = g + 2$ whereas the subspace
of $p$-th powers lies inside $\bigl(\mathcal L(\lfloor (2g+1)/p \rfloor P_\infty)\bigr)^p$ of dimension at
most $\lfloor (2g+1)/2 \rfloor + 1 = g + 1 < g + 2$. Let $S_{\mathrm{ram}} \subset C(\overline{\mathbb F}_q) \setminus \{P_\infty\}$
be the finite locus where $dt$ vanishes or fails to be an étale uniformizer; since $\deg(\operatorname{div}(dt)) = 2g - 2$
and $-\operatorname{ord}_{P_\infty}(dt) \le 2g + 2$, we have $\lvert S_{\mathrm{ram}} \rvert \le 4g$
independently of any further field extension! Moreover, in the finite separable extension
$\mathbb F_{q_1}(C) / \mathbb F_{q_1}(t)$, differentiating the minimal polynomial of a primitive
generator $Y \in \mathcal L(c_1 P_\infty)$ inductively with respect to $\Delta_T$ produces a fixed
nonzero clearing element $R_1 \in \mathcal L(c_1 P_\infty) \setminus \{0\}$ (explicitly $R_1 = f(x)$
with $c_1 = 2(2g+1)$ and $c_C = 4g$ on any hyperelliptic model $y^2 = f(x)$ with $t = x$) and a
constant $c_C \ge 1$ depending **only on $(C, P_\infty, t)$** such that for every extension $\mathbb F_Q \supseteq \mathbb F_{q_1}$,
every $r \ge 0$, every $s \in \mathcal L_{\mathbb F_Q}(r P_\infty)$, and every $k \ge 0$,
$$R_1^k\,D_t^{(k)} s \in \mathcal L_{\mathbb F_Q}\bigl((r + c_C k) P_\infty\bigr).$$

Now let $\mathbb F_Q = \mathbb F_{q^n} \supseteq \mathbb F_{q_1}$ be a large extension, fix positive
integers $m, r, \ell$ satisfying **$m < Q$** and **$r < Q$**, let $u_1, \dots, u_B$ be an
$\mathbb F_Q$-basis of $\mathcal L_{\mathbb F_Q}(\ell P_\infty)$ ($B \ge \ell + 1 - g$ by Riemann–Roch),
and consider the Frobenius-power Ansatz
$$\Phi = \sum_{b = 1}^{B} s_b\,u_b^Q \in \mathcal L_{\mathbb F_Q}\bigl((r + Q\ell) P_\infty\bigr),
\qquad s_1, \dots, s_B \in \mathcal L_{\mathbb F_Q}(r P_\infty).$$
By Lemma 6.1(3) (since $0 \le k < m < Q$), $D_t^{(k)}\Phi = \sum_{b=1}^B (D_t^{(k)} s_b)\,u_b^Q$.
Evaluate at any rational point $P \in C(\mathbb F_Q) \setminus (\{P_\infty\} \cup S_{\mathrm{ram}})$:
because $u_b$ is regular at $P$ and defined over $\mathbb F_Q$, we have $u_b(P) \in \mathbb F_Q$,
whence **$u_b(P)^Q = u_b(P)$**! Thus at every such $P$,
$$(D_t^{(k)}\Phi)(P) = \sum_{b = 1}^{B} \bigl(D_t^{(k)} s_b\bigr)(P)\,u_b(P) = \Theta_k(P),
\qquad\text{where}\qquad
\Theta_k := \sum_{b = 1}^{B} \bigl(D_t^{(k)} s_b\bigr)\,u_b \in \mathbb F_Q(C).$$
Notice what happened to the pole order: whereas $\Phi$ has pole order $\le r + Q\ell$ at $P_\infty$,
each cleared constraint function $R_1^k \Theta_k$ has **no factor of $Q$** in its pole bound:
$$R_1^k\,\Theta_k \in \mathcal L_{\mathbb F_Q}\bigl((r + c_C k + \ell) P_\infty\bigr)
\subseteq \mathcal L_{\mathbb F_Q}\bigl((r + c_C m + \ell) P_\infty\bigr) \qquad (0 \le k < m)!$$
Consider the $\mathbb F_Q$-linear map $\mathcal T : \mathcal L_{\mathbb F_Q}(r P_\infty)^B \to \mathcal L_{\mathbb F_Q}\bigl((r + c_C m + \ell)P_\infty\bigr)^m$
sending $(s_1, \dots, s_B) \mapsto (R_1^0 \Theta_0, R_1^1 \Theta_1, \dots, R_1^{m-1}\Theta_{m-1})$:
- $\dim_{\mathbb F_Q}(\text{domain}) = B \cdot \dim_{\mathbb F_Q}\mathcal L(r P_\infty) \ge (\ell + 1 - g)(r + 1 - g)$;
- $\dim_{\mathbb F_Q}(\text{codomain}) \le m\,(r + c_C m + \ell + 1)$ (since $\dim_{\mathbb F_Q}\mathcal L(D P_\infty) \le D + 1$
  for every $D \ge 0$ by jet evaluation at $P_\infty$).

Set **$\ell := m + 2g - 1$** (so $\ell + 1 - g = m + g$). Then $\dim(\text{domain}) > \dim(\text{codomain})$
holds whenever $(m + g)(r + 1 - g - m) > m(r + c_C m + g)$, which rearranges to
$$g\,r > (c_C + 1)m^2 + (3g - 1)m + g(g - 1).$$
Choose
$$m := \Bigl\lfloor \frac{1}{2}\sqrt{\frac{g}{c_C + 2}}\,Q^{1/2} \Bigr\rfloor,
\qquad
r := \Bigl\lfloor \frac{c_C + 1}{g}\,m^2 + 3m + g \Bigr\rfloor + 1.$$
For all sufficiently large $Q$, we have $1 \le m < Q$ and $r \le \frac{c_C + 1}{4(c_C + 2)} Q + O_C(Q^{1/2}) < Q$.
Hence $\ker\mathcal T \neq \{0\}$: there exists $(s_1, \dots, s_B) \neq 0$ with $\Theta_0 = \dots = \Theta_{m-1} = 0$
identically in $\mathbb F_Q(C)$. Because $r < Q$, Lemma 6.2 guarantees **$\Phi \neq 0$**! At every point
$P \in C(\mathbb F_Q) \setminus (\{P_\infty\} \cup S_{\mathrm{ram}})$ where $R_1(P) \neq 0$ (all but at
most $c_1$ points), $(D_t^{(k)}\Phi)(P) = \Theta_k(P) = 0$ for all $0 \le k < m$, so Lemma 6.1(4) gives
$\operatorname{ord}_P(\Phi) \ge m$. Comparing total zeros with $\deg(\Phi)_\infty \le r + Q\ell$ yields
$$m\bigl(\#C(\mathbb F_Q) - 1 - 4g - c_1\bigr) \le r + Q(m + 2g - 1),$$
and dividing by $m \asymp Q^{1/2}$ balances $\frac{(2g-1)Q}{m}$ against $\frac{r}{m} \asymp m$ to prove
$$\#C(\mathbb F_Q) \le Q + \frac{(2g - 1)Q}{m} + \frac{r}{m} + 1 + 4g + c_1 \le Q + C_0\,Q^{1/2}$$
for every sufficiently large $n \ge n_0$, with a constant $C_0$ depending only on $(C, P_\infty, t)$!

**Step 2: From an upper bound $\#C(\mathbb F_{q^n}) \le q^n + C_0 q^{n/2}$ to the two-sided bound
$\lvert \#C(\mathbb F_{q^n}) - (q^n + 1) \rvert \le C_1 q^{n/2}$.**
How does a *one-sided* upper bound on points imply a *lower* bound too (`[Stepanov1969]`,
`[Bombieri1973]`, p. 239; `[Schmidt1976]`)? Let $t : C \to \mathbb P^1$ be our finite separable
morphism of degree $d_t := [\mathbb F_q(C) : \mathbb F_q(t)] \le 2g + 1$, and let $\widetilde{C} / \mathbb F_{q'}$
be the smooth projective curve corresponding to the Galois closure $M$ of $\mathbb F_{\bar q}(C) / \mathbb F_{\bar q}(t)$
(defined over some finite extension $\mathbb F_{q'} = \mathbb F_{q^{n_1}}$, with Galois group
$G = \operatorname{Gal}(M / \mathbb F_{q'}(t))$ and subgroup $H = \operatorname{Gal}(M / \mathbb F_{q'}(C))$
of index $[G : H] = d_t$). Above any point $x_0 \in \mathbb P^1(\mathbb F_{q^n})$ ($n_1 \mid n$) unramified
in $\widetilde{C} \to \mathbb P^1$ (all but $O_C(1)$ points of $\mathbb P^1$), Frobenius at $x_0$ defines
a conjugacy class $\mathrm{Frob}_{x_0} \subset G$:
- the number of $\mathbb F_{q^n}$-rational points of $C$ above $x_0$ equals the number of fixed cosets
  $\#\{g H \in G/H : \sigma g H = g H\}$ ($\sigma \in \mathrm{Frob}_{x_0}$);
- summing over the twists $\widetilde{C}^{(\tau)}$ of $\widetilde{C}$ by elements $\tau \in G$ (as in
  Bombieri `[Bombieri1973]`, p. 239, where $\tau$-twisted Frobenius fixes $y \in \widetilde{C}(\overline{\mathbb F}_q)$
  iff $y^{q^n} = \tau(y)$, so every $x_0 \in \mathbb P^1(\mathbb F_{q^n})$ unramified in $\widetilde{C}$
  lifts to **exactly $\lvert G \rvert$ points in total** across the $\lvert G \rvert$ twisted curves
  $\{\widetilde{C}^{(\tau)}\}_{\tau \in G}$: $\sum_{\tau \in G} \#\widetilde{C}^{(\tau)}(\mathbb F_{q^n}) = \lvert G \rvert(q^n + 1) + O_C(1)$!).
Applying Step 1's upper bound $\#\widetilde{C}^{(\tau)}(\mathbb F_{q^n}) \le q^n + C_\tau q^{n/2}$ to the
$\lvert G \rvert - 1$ twists $\tau' \neq \tau$ immediately forces the **matching lower bound** on the
remaining twist:
$$\#\widetilde{C}^{(\tau)}(\mathbb F_{q^n})
= \lvert G \rvert(q^n + 1) + O_C(1) - \sum_{\tau' \neq \tau} \#\widetilde{C}^{(\tau')}(\mathbb F_{q^n})
\ge q^n + 1 - \Bigl(\sum_{\tau' \neq \tau} C_{\tau'}\Bigr) q^{n/2} - O_C(1)!$$
And since each point of $C(\mathbb F_{q^n})$ outside ramification lifts to $\lvert H \rvert$ points
spread across the twists $\widetilde{C}^{(h)}$ ($h \in H$), summing over $h \in H$ gives the **two-sided
square-root estimate**
$$\bigl\lvert \#C(\mathbb F_{q^n}) - (q^n + 1) \bigr\rvert \le C_1\,q^{n/2} \qquad \text{for all } n_1 \mid n \text{ sufficiently large!}$$
(Note how effortlessly this goes on a hyperelliptic curve $y^2 = f(x)$: for any nonsquare $c \in \mathbb F_{q^n}^\times$,
every $x_0 \in \mathbb F_{q^n}$ with $f(x_0) \neq 0$ gives $2$ points either on $C : y^2 = f(x)$ or on
its quadratic twist $C_c : c y^2 = f(x)$, so $\#C(\mathbb F_{q^n}) + \#C_c(\mathbb F_{q^n}) = 2(q^n + 1)$
identically! An upper bound $q^n + C_0 q^{n/2}$ on $C_c$ IS the lower bound $q^n + 2 - C_0 q^{n/2}$ on $C$!)

**Step 3: Tensor-power amplification from $O_C(q^{n/2})$ to the exact constant $2g\sqrt{q}$.**
By Riemann–Roch (elementary divisor class finiteness on $C / \mathbb F_q$, `[Schmidt1976]`, Ch. IV),
the zeta function
$$Z(C/\mathbb F_q, T) := \exp\Biggl(\sum_{n = 1}^{\infty} \#C(\mathbb F_{q^n})\,\frac{T^n}{n}\Biggr)
= \frac{P_1(T)}{(1 - T)(1 - qT)}$$
is a rational function whose numerator $P_1(T) = \prod_{j = 1}^{2g} (1 - \alpha_j T) \in \mathbb Z[T]$
has degree $2g$, meaning $\#C(\mathbb F_{q^n}) = q^n + 1 - \sum_{j=1}^{2g} \alpha_j^n$ for all $n \ge 1$!
Also, by Serre/Riemann–Roch duality $\deg(K_C) = 2g - 2$, $Z(C, 1/(qT)) = q^{1-g} T^{2-2g} Z(C, T)$,
so the multiset of inverse roots $\{\alpha_1, \dots, \alpha_{2g}\}$ is closed under $\alpha_j \mapsto q / \alpha_j$.
Now confront $\sum_{j=1}^{2g} \alpha_j^n$ with Step 2's bound $\lvert \sum_{j=1}^{2g} \alpha_j^n \rvert \le C_1 q^{n/2}$
along all large multiples $n = k n_1$ ($k = 1, 2, \dots$): the radius of convergence of the rational
function
$$\sum_{k = 1}^{\infty} \Biggl(\sum_{j = 1}^{2g} (\alpha_j^{n_1})^k\Biggr) U^k
= \sum_{j = 1}^{2g} \frac{\alpha_j^{n_1} U}{1 - \alpha_j^{n_1} U}$$
is at least $q^{-n_1/2}$ because its coefficients are bounded by $C_1 (q^{n_1/2})^k$! Since nonzero
equal roots $\alpha_j^{n_1}$ merge with positive integer multiplicities (never cancelling!), no pole
$U = \alpha_j^{-n_1}$ can lie inside the open disk $\lvert U \rvert < q^{-n_1/2}$! Hence
$\lvert \alpha_j \rvert^{n_1} \le q^{n_1/2}$, i.e. $\lvert \alpha_j \rvert \le \sqrt{q}$, for every $j$!
Applying symmetry $\alpha_j \mapsto q/\alpha_j$ gives $\lvert q / \alpha_j \rvert \le \sqrt{q}$, so
**$\lvert \alpha_j \rvert = \sqrt{q}$ for every $1 \le j \le 2g$** — and at $n = 1$,
$$\bigl\lvert \#C(\mathbb F_q) - (q + 1) \bigr\rvert = \Bigl\lvert \sum_{j = 1}^{2g} \alpha_j \Bigr\rvert
\le \sum_{j = 1}^{2g} \lvert \alpha_j \rvert = 2g\sqrt{q}. \quad \square$$

### 6.4.3 Bridge to multiplicative and additive character sums over finite fields

In analytic number theory (`[IwaniecKowalski2004]`, Ch. 11), the immediate payoff of Theorem 6.3 is
square-root cancellation for complete character and exponential sums along curves.

**Corollary 6.4 (Weil bounds for quadratic character sums and Artin–Schreier exponential sums).**
*Let $\mathbb F_q$ be a finite field of characteristic $p$* `[Weil1948]`, `[Schmidt1976]`,
`[IwaniecKowalski2004]` [Expository]:

1. *(Multiplicative character sums)* *Suppose $p \neq 2$, let $\chi_2 : \mathbb F_q \to \{-1, 0, +1\}$
   be the quadratic character, and let $f(x) \in \mathbb F_q[x]$ be a monic squarefree polynomial of
   degree $d \ge 1$ (or more generally not a constant times a square in $\overline{\mathbb F}_q[x]$,
   with $d_0$ distinct roots in $\overline{\mathbb F}_q$). Then*
   $$\Bigl\lvert \sum_{x \in \mathbb F_q} \chi_2(f(x)) \Bigr\rvert \le (d_0 - 1)\sqrt{q} \le (\deg f - 1)\sqrt{q}.$$
2. *(Additive exponential sums)* *Let $\psi : \mathbb F_q \to \mathbb C^\times$ be a nontrivial additive
   character ($\psi(a) = e^{2\pi i \operatorname{Tr}_{\mathbb F_q/\mathbb F_p}(a)/p}$), and let
   $f(x) \in \mathbb F_q[x]$ have degree $d \ge 1$ with **$p \nmid d$**. Then*
   $$\Bigl\lvert \sum_{x \in \mathbb F_q} \psi(f(x)) \Bigr\rvert \le (d - 1)\sqrt{q}.$$

*Proof.*
(1) Write $f(x) = c\,g(x)^2 h(x)$ in $\mathbb F_q[x]$ with $c \in \mathbb F_q^\times$ and $h$ monic
squarefree of degree $d_1 := \deg h \ge 1$ (since $f$ is not a constant times a square in
$\overline{\mathbb F}_q[x]$). Because every root of $h$ in $\overline{\mathbb F}_q$ is a root of $f$
and any root of $g$ in $\mathbb F_q$ with $h(x) \neq 0$ is an additional distinct root of $f$, the set
$Z_1 := \{x \in \mathbb F_q : g(x) = 0,\ h(x) \neq 0\}$ has cardinality $m_1 := \lvert Z_1 \rvert \le d_0 - d_1$.
For $x \in \mathbb F_q \setminus Z_1$ we have $\chi_2(f(x)) = \chi_2(c)\,\chi_2(h(x))$ (both sides
vanish when $h(x) = 0$), whereas on $Z_1$ we have $\chi_2(f(x)) = 0$ and $\lvert \chi_2(c)\chi_2(h(x)) \rvert = 1$,
so $\lvert \sum_{x \in \mathbb F_q} \chi_2(f(x)) \rvert \le \lvert \sum_{x \in \mathbb F_q} \chi_2(h(x)) \rvert + m_1$.
Now let $C_h$ be the smooth projective model of $y^2 = c\,h(x)$: it has genus $g_h = \lfloor (d_1 - 1)/2 \rfloor$
and $1$ point at infinity when $d_1$ is odd ($2g_h = d_1 - 1$, $\delta_\infty = 0$) or
$1 + \chi_2(c) \in \{0, 2\}$ rational points at infinity when $d_1 \ge 2$ is even ($2g_h = d_1 - 2$,
$\lvert \delta_\infty \rvert = 1$). In both parities,
$\#C_h(\mathbb F_q) = q + 1 + \chi_2(c)\sum_{x \in \mathbb F_q} \chi_2(h(x)) + \delta_\infty$, so
Theorem 6.3 gives $\lvert \sum_{x \in \mathbb F_q} \chi_2(h(x)) \rvert \le 2g_h\sqrt{q} + \lvert \delta_\infty \rvert \le (d_1 - 1)\sqrt{q}$
(using $1 \le \sqrt{q}$ when $d_1$ is even). Adding $m_1 \le d_0 - d_1 \le (d_0 - d_1)\sqrt{q}$ yields
$$\Bigl\lvert \sum_{x \in \mathbb F_q} \chi_2(f(x)) \Bigr\rvert
\le (d_1 - 1)\sqrt{q} + (d_0 - d_1) \le (d_0 - 1)\sqrt{q} \le (\deg f - 1)\sqrt{q}.$$

(2) Consider the Artin–Schreier curve $C / \mathbb F_q$ with affine model $y^p - y = f(x)$ (`[Schmidt1976]`,
Ch. II, §2). Because $p \nmid d = \deg f$, $C$ is geometrically irreducible with a single totally
ramified point $P_\infty$ at infinity and Hurwitz genus $g = \frac{(p - 1)(d - 1)}{2}$! For each
$x_0 \in \mathbb F_q$ and each nontrivial character $\psi_a(z) := \psi(a z)$ ($a \in \mathbb F_p^\times$)
of $\mathbb F_p$, Hilbert's Theorem 90 on $\mathbb F_q / \mathbb F_p$ says $y^p - y = f(x_0)$ has $p$
solutions $y_0 \in \mathbb F_q$ if $\operatorname{Tr}_{\mathbb F_q/\mathbb F_p}(f(x_0)) = 0$ and $0$
solutions otherwise, so orthogonality on $\mathbb F_p$ gives
$$\#C(\mathbb F_q) = 1 + \sum_{x_0 \in \mathbb F_q} \sum_{a \in \mathbb F_p} \psi\bigl(a f(x_0)\bigr)
= q + 1 + \sum_{a \in \mathbb F_p^\times} S(a f), \qquad S(a f) := \sum_{x \in \mathbb F_q} \psi(a f(x)).$$
Replacing $\mathbb F_q$ by $\mathbb F_{q^n}$, the Dedekind/Artin factorization of $Z(C/\mathbb F_q, T)$
under the cyclic group $\mathbb F_p$ splits its $2g = (p-1)(d-1)$ Frobenius inverse roots into $p - 1$
Artin $L$-polynomials $L(T, \psi_a)$ ($a \in \mathbb F_p^\times$) of degree $d - 1$ each! By Theorem 6.3,
every inverse root of $Z(C/\mathbb F_q, T)$ — and hence every inverse root of $L(T, \psi_1)$ — has
modulus $\sqrt{q}$, yielding $\lvert S(f) \rvert \le (d - 1)\sqrt{q}$. $\square$

### 6.4.4 The Lean archive's algebraic Arakelov–Stepanov deduction (`each_unit_bound_statement`)

Now turn directly to node `P7` of the Lean archive and watch the **exact same logical skeleton** run
in characteristic zero! In Chapter 5 (Theorem 5.5, Step 1, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean:37`), `core_gm` unpacked a
single theorem from `P7` — `each_unit_bound_statement`
(`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`) [Lean, read]. We
have read `MeanBoundSecondForm.lean`, `WeightedMeanData.lean`, `QuotientSlopeBoundsWith.lean`, and
`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean` line by line (`R3`). Every step in these four files is genuine, `sorry`-free
real algebra and convexity (`[Lean, read]`).

First we isolate the two elementary analytic/algebraic lemmas inside `WeightedMeanData.lean` (`:81, 170`):

**Lemma 6.5 (Concave logarithm linearization `phi_bound` and cancellation identity `key_identity`).**
*Let `D : Data U0 W Top m f` and `C : Consts`* [Lean, read]:

1. *(`phi_bound`, `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:81`)* *For any reals $u \ge 0$, $H > 0$, $b > 0$, $X > 0$, and
   $U$ satisfying $H \le X b$ and $u \le U$,*
   $$u\,\log\Bigl(1 + \frac{H}{u}\Bigr) \le \log(1 + X)\cdot (U + b)$$
   *(with $0 \cdot \log(1 + H/0) := 0$ at $u = 0$).*
2. *(`key_identity5`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:105`, via `Data.key_identity`, `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:170`)*
   *Suppose $D.v > 0$, $f > 0$, and $D.w(u_0, j, \rho) > 0$ for all $(j, \rho)$. Put
   $\mathrm{Lam}_5(u_0) := \sum_{j=0}^{m-1} \frac{1}{f}\sum_{\rho=1}^f \log\bigl(D.w(u_0,j,\rho) D.v / \pi\bigr) + m\cdot D.\mathrm{lg} - C.c_{\mathrm{Count}}(D.L_a + m^2 D.L_a / D.k)$. Then*
   $$D.\mathrm{SDiv} - D.\mathrm{sum}_A\cdot \mathrm{Lam}_5(u_0) + m\cdot D.\mathrm{sum}_A\cdot D.\mathrm{lg}
   = D.\mathrm{Main}(u_0) + D.\mathrm{sum}_A\cdot C.c_{\mathrm{Count}}\Bigl(D.L_a + \frac{m^2 D.L_a}{D.k}\Bigr).$$

*Proof.*
(1) If $u = 0$, the left-hand side is $0 \le \log(1 + X)(U + b)$ since $X > 0$ and $U + b \ge u + b > 0$.
Suppose $u > 0$. Applying $\log y \le y - 1$ (`Real.log_le_sub_one_of_pos`, `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:99`)
to $y := \frac{1 + H/u}{1 + X} > 0$ gives
$$\log\Bigl(1 + \frac{H}{u}\Bigr) \le \log(1 + X) + \frac{1 + H/u}{1 + X} - 1.$$
Multiply by $u > 0$:
$$u\log\Bigl(1 + \frac{H}{u}\Bigr) \le u\log(1 + X) + \frac{H}{1 + X} - u\Bigl(1 - \frac{1}{1 + X}\Bigr)
\le U\log(1 + X) + \frac{X b}{1 + X}$$
since $u \le U$, $\log(1 + X) > 0$, $1 - (1 + X)^{-1} > 0$, and $H \le X b$. Finally, applying
$\log z \le z - 1$ to $z = (1 + X)^{-1}$ gives $-\log(1 + X) \le (1 + X)^{-1} - 1$, i.e.
$\frac{X}{1 + X} = 1 - \frac{1}{1 + X} \le \log(1 + X)$ (`hb0`, `:91`). Multiplying by $b > 0$ gives
$\frac{X b}{1 + X} \le b\log(1 + X)$, completing (1)!

(2) Expand $\log(w v / \pi) = \log w + \log v - \log\pi$ across all $m$ lifts and $f$ places:
$$\sum_{j=0}^{m-1} \frac{1}{f}\sum_{\rho=1}^f \log\Bigl(\frac{w_{u_0,j,\rho} v}{\pi}\Bigr)
= \sum_{j=0}^{m-1} \frac{1}{f}\sum_{\rho=1}^f \log w_{u_0,j,\rho} + m\,(\log v - \log\pi).$$
On the other hand, by definition of $\mathrm{SDiv}$ (`src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:129`), $\mathrm{ph}(a_t) = a_t\log a_t - a_t$
(`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:9`), and $\log\Omega = \gamma + \log(\pi / v) - \mathrm{LpL}$ (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:88`),
$$\mathrm{SDiv} = m \sum_t a_t\bigl(\log a_t - 1 - \gamma + \mathrm{LpL}\bigr) - m\,(\log\pi - \log v)\,\mathrm{sum}_A.$$
When we compute $\mathrm{SDiv} - \mathrm{sum}_A\cdot\mathrm{Lam}_5(u_0) + m\cdot\mathrm{sum}_A\cdot\mathrm{lg}$,
**both** archimedean covolume/period constants $m\,(\log v - \log\pi)\,\mathrm{sum}_A$ and
$m\cdot\mathrm{sum}_A\cdot\mathrm{lg}$ cancel identically (`linear_combination`, `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:216`), leaving
$D.\mathrm{Main}(u_0) + \mathrm{sum}_A\cdot C.c_{\mathrm{Count}}(D.L_a + m^2 D.L_a / D.k)$! $\square$

**Theorem 6.6 (Pointwise Arakelov–Stepanov chain bound: `each_unit_bound_statement`).** *Let
`D : Data U0 W Top m f`, `C : Consts`, and $X'' \in \mathbb R$ satisfy the 11-clause conjunction
`SizeData₂ D C Xpp` (`src/Formalism/SizeWindowBrackets/SChain.lean:17`). Then for every coset shift $u_0 \in U_0$,*
$$D.\mathrm{ASK}(u_0) \le D.\mathrm{Main}(u_0) + \mathrm{ErrX5at}(D, C, X'', u_0),$$
*where $\mathrm{ErrX5at}(D, C, X'', u_0)$ (`src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:45`) is bounded under
`ErrWindows` and `LargeX` by $D.x^{\mathrm{CErr}(C) D.\varepsilon}\,\mathrm{ErrText}(D)$ (`errX5at_le`,
`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean:613`), and together with `BNBounds`
yields the window bound in terms of $D.x^{\mathrm{CErr}(C) D.\varepsilon}\,\mathcal E_{\mathrm{win}}$
(`top_each_bound_sized`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean:674`, feeding Chapter 5's `ch_top`).*
*(Lean: `each_unit_bound_statement`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`.)* [Lean, read]

*Proof.* Fix $u_0 \in U_0$. Watch how the proof in `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:50–197` mirrors Stepanov's
argument step for step:

1. **Slope lower bound from $m$-lift divisibility (`s_lower5`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:50–66` — the
   analogue of $\deg(\text{zeros}) \ge m N$):** For each word $u \in W(u_0)$, combine the lower
   quotient-slope inequality of Clause 7 (`QuotientSlopeBoundsWith`:
   $\mu_N(u) \ge \mu_M(u) + \mathrm{Ga}(u_0) + \mathrm{Fo}(u_0) - \mathrm{Ee}(u) - \mathrm{Lo}_5(u)$)
   with the global divisibility inequality of Clause 2 (`DIV`:
   $-h(u) \ge \mu_{CC}(u_0) - \mathrm{Fo}(u_0) - \mathrm{SDiv} + \mathrm{sum}_A\log T(u) - \mathrm{EDiv}$):
   the Fourier shift $\mathrm{Fo}(u_0)$ cancels out, giving
   $$\mu_N(u) - h(u) \ge \mathrm{Ga}(u_0) + \mu_{CC}(u_0) + \mu_M(u) + \mathrm{sum}_A\log T(u) - \mathrm{Ee}(u) - \mathrm{SDiv} - \mathrm{EDiv} - \mathrm{Lo}_5(u).$$
   Bound $\mu_M(u) \ge -c_{\mathrm{Slope}} n_T a L_a (1 + m/k)$ (Clause 6), $\log T(u) \ge \mathrm{Lam}_5(u_0)$
   (Clause 5, multiplied by $\mathrm{sum}_A \ge 0$), and $-\mathrm{Ee}(u) \ge -m(\mathrm{sum}_A\cdot\mathrm{lg} + c_E B_0)$
   (Clause 3, `exponent_le_upper`, `:32`). Taking the $d(u_0, u)$-weighted average over $u \in W(u_0)$
   (`sub_wmean_le`, `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:40`) yields
   $$D.s(u_0) \ge \mathrm{Ga}(u_0) + \mu_{CC}(u_0) - K_{5,\mathrm{v5}}(u_0) - \mathrm{wmean}_{d}(\mathrm{Lo}_5).$$
2. **Bounding the slope spread across words (`u_function_le_mean`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:81–103`):**
   For any pair of words $u, u' \in W(u_0)$, comparing the upper quotient-slope bound on $\mu_{\max, N}(u) - h(u)$
   with the lower bound on $\mu_N(u') - h(u')$ cancels $\mathrm{Ga}(u_0) + \mathrm{Fo}(u_0)$, while
   Clauses 3, 4, and 5 bound the variation of $(-\mathrm{Ee}(u) - h(u))$ across $u, u'$ by $D.\mathrm{Vvar}(C)$
   (`Vvar_bound5`, `:68`). Taking the supremum over $u$ and weighted mean over $u'$ bounds the slope
   spread:
   $$0 \le D.u_F(u_0) \le D.K_3(C) + \mathrm{wmean}_d(\mathrm{Lo}_5).$$
3. **Confronting the slope lower bound with Bost's slope inequality (`Ga_bound5`, `:113–160` — the
   analogue of $\deg(\text{zeros}) \le \deg(\text{poles})$):** Clause 9 (`SlopeIneq`) says
   $$D.s(u_0) - \mu_{CC}(u_0) \le \log\lvert W(u_0) \rvert
   + (1 - \delta)^{-1}\Bigl(4 u_F \log\Bigl(1 + \frac{\mathrm{HH}}{u_F}\Bigr) + (\eta + 4\sqrt{e})\,\mathrm{HH}\Bigr).$$
   Notice how **$\mu_{CC}(u_0)$ cancels identically** between Step 1 and Step 3! Applying Lemma 6.5(1)
   (`phi_bound`) with $H = \mathrm{HH}(u_0) \le x^{c_{\mathrm{HH}}} b$ (Clause 10) and
   $U = K_3 + \mathrm{wmean}_d(\mathrm{Lo}_5)$ (Step 2), bounding $\delta \le \bar\delta < 1$,
   $\eta \le \bar\eta$, $e \le \bar e$ (Clause 11), and substituting Lemma 6.5(2) (`key_identity5`)
   turns $\mathrm{SDiv} - \mathrm{sum}_A\cdot\mathrm{Lam}_5 + m\,\mathrm{sum}_A\cdot\mathrm{lg}$ into
   $D.\mathrm{Main}(u_0)$ plus error $K_{0,\mathrm{v5}}$!
4. **Replacing $\mathrm{Ga}(u_0)$ by $\mathrm{ASK}(u_0)$ (`each_unit_bound_statement`, `:175–198`):**
   Clause 5 (`\log T \le c_{\mathrm{Count}} m L`) bounds $\mathrm{wmean}_d(\mathrm{Lo}_5) \le c_{\mathrm{Sl1}}\,\mathrm{IO}(u_0) + K_{7,\mathrm{v5}}$
   (`weighted_mean_lower_bound_le`, `:162`), and Clause 8 (`LossBounds`) bounds both
   $\mathrm{IO}(u_0) \le \mathrm{Lo}_P$ and $\mathrm{ASK}(u_0) - \mathrm{Ga}(u_0) \le \mathrm{Lo}_P$.
   Adding $\mathrm{ASK}(u_0) - \mathrm{Ga}(u_0) \le \mathrm{Lo}_P$ to Step 3 gives
   $D.\mathrm{ASK}(u_0) \le D.\mathrm{Main}(u_0) + \mathrm{ErrX5at}(D, C, X'', u_0)$. $\square$

### 6.4.5 From lattice slopes to the weighted mean: the main-path instance of Clause 7

Theorem 6.6, Step 1 used Clause 7 (`QuotientSlopeBoundsWith`) with $\mu_N(u)$, $\mu_M(u)$ and the
weights $d(u_0, u)$ as abstract real fields of `Data`. This subsection follows one direct
dependency that the chapter has not yet opened. On the path to `riemannHypothesis` these three
fields are slopes and ranks of hermitian $\mathcal O_K$-lattices. Clause 7 for them is produced by
`Mod.model_slopes_five` and consumed by `s_lower5`, and the weighted mean inside `Data.s` is the
rank-weighted frame average `sFrame`. We read the producer, the identification `Mod.s_eq` and the
consumer line by line. We do not return to the Stepanov–Bombieri warm-up (§6.2, §6.4.2) or to the
assembly of `SizeData₂` and `ChainTied` (§6.3.2, Theorem 6.6). All line numbers refer to the fixed
archive `lean.tar.gz` (sha256 `9631b4f0…49c7fc`, toolchain `leanprover/lean4:v4.33.1`).
Reachability statements use the main-theorem export recorded in `sources/SOURCES.md` (compressed
sha256 `d5fad832…89fb`).

**Motivation.** Stepanov counts vanishing at each point and then sums over points. Here each word
$u \in W(u_0)$ carries a lattice $N_u$. Clause 7 bounds the slope of $N_u$ from below one word at a
time, and `sub_wmean_le` averages these bounds. Two questions decide what the averaged bound
means:

- *Which average?* The weights are the ranks of the $N_u$ over $K$. A rank-weighted mean of slopes
  is the slope of an orthogonal direct sum (Lemma 6.9(3)), so `Data.s` is a slope in its own right.
- *Which slope?* The field `muN` is `HLat.mu`. This is a normalized slope of an
  $\mathcal O_K$-lattice, computed on its $\mathbb Z$-realization. Reading a slope bound correctly
  requires keeping three things apart: torsion in a quotient, saturation of a sublattice, and the
  base ring ($\mathcal O_K$ or $\mathbb Z$) over which sublattices are allowed.

The file `MeanBoundSecondForm.lean` supplies the vocabulary used below (`Data`, `wmean`, `Data.s`,
`HidaSetting`, `DIV`, `Slopes`). The averaged propositions named after that file, the term
`Data.MeanBoundSecondForm` (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:187–190`) and the
term `MeanBoundWith` (`src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:67–70`), are not
in the export, so they are not on the main path. The consumption traced here is the pointwise one
(Remark 6.12).

**Example 6.8 (one rank-two lattice read three ways)** [Expository]. Let $K = \mathbb Q(\sqrt{-5})$.
Then $[K:\mathbb Q] = 2$, $K$ has one complex place, and $\lvert d_K \rvert = 20$. Realize the ideal
$\mathfrak a = 2\mathbb Z + (1+\sqrt{-5})\mathbb Z$ in $\mathbb C = \mathbb R^2$ by real and imaginary
parts, with the standard inner product. This follows the pattern of `realize`
(`src/Formalism/HermitianLattices/StatementMaj.lean:78–81`). With this choice the archive's
normalized slope of $\mathcal O_K$ (Definition 6.7(1)) is $0$. Then $e_1 = 2 \mapsto (2, 0)$ and
$e_2 = 1 + \sqrt{-5} \mapsto (1, \sqrt 5)$. The Gram
matrix is $G = \begin{pmatrix} 4 & 2 \\ 2 & 6 \end{pmatrix}$, so $\mathrm{covol}(\mathfrak a)^2 = 20$.
Multiplication by $\sqrt{-5}$ has matrix $A = \begin{pmatrix} -1 & -3 \\ 2 & 1 \end{pmatrix}$ in the
basis $(e_1, e_2)$, with $A^2 = -5$ and $A^{\mathsf T} G A = 5G$. Hence $L = \mathfrak a$ is a rank-two
integral lattice and also an $\mathcal O_K$-module of rank one.

(a) *Index and torsion.* Take $N = \mathbb Z \cdot 2e_1$, with $\lVert 2e_1 \rVert^2 = 16$. Its
saturation is $N^{\mathrm{sat}} = L \cap \mathbb R N = \mathbb Z e_1$, and
$[N^{\mathrm{sat}} : N] = 2$. Hence $L/N \cong \mathbb Z/2 \oplus \mathbb Z$, and the torsion subgroup
$N^{\mathrm{sat}}/N$ has order $2$.

(b) *The archive's quotient.* `F.quot L N` is the image of $L$ under orthogonal projection onto
$(\mathbb R N)^{\perp}$ (`src/Formalism/LatticeSlopes/Statement.lean:35–36`) [Lean, read]. Here
$\pi(e_1) = 0$ and $\pi(e_2) = e_2 - \tfrac12 e_1 = (0, \sqrt 5)$, so
$\mathrm{covol}(\pi L)^2 = 6 - 2^2/4 = 5$. The projection depends only on
$\mathbb R N = \mathbb R N^{\mathrm{sat}}$. So `F.quot L N` equals `F.quot L N^sat` and does not see
the torsion.

(c) *Covolumes, degrees, slopes over $\mathbb Z$.* With $\deg = -\log \mathrm{covol}$ and
$\mathrm{slope} = \deg / \mathrm{rk}$ (`src/Formalism/LatticeSlopes/Statement.lean:15–25`):

| lattice | rank | $\mathrm{covol}^2$ | $\deg$ | slope |
|---|---|---|---|---|
| $L = \mathfrak a$ | 2 | 20 | $-\tfrac12 \log 20$ | $-\tfrac14 \log 20$ |
| $N^{\mathrm{sat}} = \mathbb Z e_1$ | 1 | 4 | $-\log 2$ | $-\log 2$ |
| $N = \mathbb Z \cdot 2e_1$ | 1 | 16 | $-2\log 2$ | $-2\log 2$ |
| $\pi L$ (`F.quot`) | 1 | 5 | $-\tfrac12 \log 5$ | $-\tfrac12 \log 5$ |

For the saturated sublattice, $20 = 4 \cdot 5$, that is
$\deg L = \deg N^{\mathrm{sat}} + \deg \pi L$. For $N$ itself,
$\deg N + \deg \pi L = -\tfrac12 \log 80 = \deg L - \log 2$. The defect is exactly
$\log \# (L/N)_{\mathrm{tors}}$.

(d) *Harder–Narasimhan over $\mathbb Z$.* The norm form is
$4x^2 + 4xy + 6y^2 = (2x + y)^2 + 5y^2$. Its minimum on $L \setminus 0$ is $4$, attained only at
$\pm e_1$. A rank-two sublattice has slope at most $\mathrm{slope}(L)$ (Lemma 6.9(1)), so the
largest slope of a $\mathbb Z$-sublattice is $-\log 2$. This exceeds
$\mathrm{slope}(L) = -\tfrac14 \log 20$ because $2^4 = 16 < 20$. So $L$ is
unstable as a $\mathbb Z$-lattice. Its filtration is $0 \subset \mathbb Z e_1 \subset L$, with
quotient slope $-\tfrac12 \log 5$.

(e) *Base ring $\mathcal O_K$.* The line $\mathbb Z e_1$ is not an $\mathcal O_K$-submodule, since
$\sqrt{-5}\, e_1 = -e_1 + 2e_2$. Every nonzero $\mathcal O_K$-submodule of the rank-one module $L$
has finite index, so its slope is at most $\mathrm{slope}(L)$. Over $\mathcal O_K$, therefore, $L$ is
semistable. In the archive's normalization (Definition 6.7(1)),
$\mathrm{mu}(\mathfrak a) = 2\cdot(-\tfrac14 \log 20) - \log 2 + \tfrac12 \log 20 = -\log 2$,
and `muMax` of $\mathfrak a$, a supremum over $\mathcal O_K$-submodules, is also $-\log 2$.
Taking the supremum over $\mathbb Z$-sublattices instead would give
$2\cdot(-\log 2) - \log 2 + \tfrac12 \log 20 = \tfrac12 \log \tfrac{5}{16}$, an overshoot of
$\tfrac12 \log \tfrac54$. As a cross-check against Bost's normalization, the Arakelov degree is
$\widehat{\deg}\, \mathfrak a = \log \#(\mathfrak a / 2\mathcal O_K) - 2\log 2 = -\log 2$, so
$\hat\mu(\mathfrak a) = -\tfrac12 \log 2$ [Bost1996, App. A.2, pp. 146–147]. In this example
$\mathrm{mu} = 2\hat\mu$.

(f) *Index and weighted mean.* The square $\mathfrak a^2 = 2\mathcal O_K$, with basis
$e_1, -e_1 + 2e_2$, is an $\mathcal O_K$-submodule of index $2$ in $\mathfrak a$, with
$\mathrm{covol}^2 = 80$ and $\mathrm{mu}(2\mathcal O_K) = -2\log 2$. The drop is
$\log 2 = 2 \log 2 / ([K:\mathbb Q] \cdot 1)$. This equals `sizeOfVal` at the prime $\mathfrak a$ of
norm $2$ with exponent $1$, that is $2 \cdot \tfrac{\log 2}{2} \cdot 1$
(`src/Formalism/LocalRingCardinality/DataArith.lean:39–46`). The orthogonal sum
$\mathfrak a \oplus 2\mathcal O_K$ has $\mathbb Z$-rank $4$ and $\mathrm{covol}^2 = 1600$. Its
normalized slope is $-\tfrac32 \log 2$, the rank-weighted mean of $-\log 2$ and $-2\log 2$. With
heights $h = (0, \log 2)$, the frame average of Definition 6.7(2) is
$\tfrac12\bigl((-\log 2 - 0) + (-2\log 2 - \log 2)\bigr) = -2\log 2$.

Every number in (a)–(f) is checked exactly by `verify_lattice_example.py` (6044 integer and rational
assertions). Real logarithms are handled as exact vectors of rational exponents over primes. The
example illustrates the definitions. It is not evidence for any general statement.

**Definition 6.7 (the objects behind the fields of `Data` on the main path)** [Lean, read].

1. *Hermitian $\mathcal O_K$-lattices.* `HLat K` (`src/Formalism/LocalRingCardinality/DataArith.lean:61–72`)
   is a $K$-space $V$ with basis $b$, matrices $X_v$ at the infinite places, and an
   $\mathcal O_K$-submodule $L$. Its `rank` is $\mathrm{rk}_K L$ (`:82`, via
   `src/Formalism/HarderNarasimhan/StatementPl.lean:27`). Its `mu` and `muMax` (`:84, 86`) are
   `muDef` and `muMaxDef` (`StatementPl.lean:64–68`):
   $$\mathrm{mu}(L) = 2\,\mathrm{slope}_{\mathbb Z}\bigl(\rho(L)\bigr) - \log 2 + \frac{\log \lvert d_K \rvert}{[K:\mathbb Q]},$$
   where $\rho$ = `realize b X`. The maximal slope `HN.muMax` is a supremum over nonzero
   **$\mathcal O_K$-submodules** $N \le L$ (`src/Formalism/HarderNarasimhan/Statement.lean:29–30`).
   The minimal slope `HN.muMin` is an infimum, over $N \ne L$ with `IsSat`, of the slope of
   `F.quot` (`:32–34`). Here `IsSat` means $N \le L$ together with $\mathbb Z$-saturation of the
   realized lattices (`:26–27`, `src/Formalism/LatticeSlopes/Statement.lean:32–33`).
2. *Frame averages.* For words $u$ with lattices $N_u$ and heights $h_u$:
   `dU Nu u` is the rank of $N_u$, `Rsum` $= \sum_u$ `dU`, and
   $$\mathrm{sFrame}(N, h) = \frac{\sum_u \mathrm{rk}(N_u)\,\bigl(\mathrm{mu}(N_u) - h_u\bigr)}{\sum_u \mathrm{rk}(N_u)}$$
   (`DataArith.lean:127–132`). `DivData` (`:139–159`) bundles a target `RR`, the family `Nu`, maps
   `Bk u` into the dual of `RR`, and the heights `h`.
3. *The per-member bound.* `SlopesN_at L C` (`src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:181–183`)
   asserts, for every word $u$,
   $$\mathrm{muMax}(N_u) \le \mathrm{muMax}(M_u) + \mathrm{Ga} + \mathrm{Fo} - \mathrm{Ee}(u) + C m B_0,
   \qquad \mathrm{mu}(M_u) + \mathrm{Ga} + \mathrm{Fo} - \mathrm{Ee}(u) - \mathrm{LoU}(u) \le \mathrm{mu}(N_u),$$
   with $N_u$ = `D.div.Nu u`, $M_u$ = `(D.fm u).lat 0`, and `LoU` as in `:177–179`.
4. *The model record.* `Mod.data` (`QuadraticLogDerivCongr.lean:464–504`) fills `Data` from a
   family member. In particular: `d u0 u` is the rank of $N_u$ (`:483`); `muN` and `muMaxN` are
   `mu` and `muMax` of $N_u$ (`:485–486`); `h` is `div.h` (`:487`); `muM` and `muMaxM` are those of
   $M_u$ (`:488–489`); `muCC` is `div.RR.muDual` (`:491`); `IO` is `IOsum` (`:497`).

**Lemma 6.9 (three classical lattice facts)** [Expository]. Let $L$ be a lattice in a euclidean
space and $N \le L$ a sublattice.

1. *(Index.)* If $L' \le L$ has the same rank $r$, then $\mathrm{covol}(L') = [L:L']\,\mathrm{covol}(L)$,
   so $\mathrm{slope}(L') = \mathrm{slope}(L) - \log[L:L']/r$.
2. *(Quotients and torsion.)* Let $\pi$ be the orthogonal projection onto $(\mathbb R N)^{\perp}$.
   Then $\deg L = \deg N^{\mathrm{sat}} + \deg \pi L$. In general
   $\deg L = \deg N + \deg \pi L + \log \# (L/N)_{\mathrm{tors}}$.
3. *(Direct sums.)* For an orthogonal sum, $\deg(L_1 \oplus L_2) = \deg L_1 + \deg L_2$. Hence the
   slope of the sum is the rank-weighted mean of the slopes.

*Proof.* (1) A basis of $L'$ is a basis of $L$ multiplied by an integer matrix of determinant
$\pm[L:L']$, and Gram determinants change by its square. (2) $N^{\mathrm{sat}}$ is a direct summand
of $L$. Choose a basis $f_1, \dots, f_s, g_1, \dots, g_t$ of $L$ whose first $s$ vectors span
$N^{\mathrm{sat}}$. The Gram matrix of $f_1, \dots, f_s, \pi g_1, \dots, \pi g_t$ is block diagonal,
and replacing each $\pi g_j$ by $g_j$ adds a real combination of the $f_i$. This is a unipotent
change of the real basis, so the Gram determinant does not change. This gives the first identity. For the second, $L/N^{\mathrm{sat}}$ is torsion-free, so
$(L/N)_{\mathrm{tors}} = N^{\mathrm{sat}}/N$, and (1) gives
$\deg N = \deg N^{\mathrm{sat}} - \log [N^{\mathrm{sat}} : N]$. (3) The Gram matrix of a union of
bases is block diagonal. $\square$

The saturated case of (2) is the archive input `DegQuot`
(`src/Formalism/LatticeSlopes/Statement.lean:83–86`). It is supplied as `degQuot`
(`src/Formalism/LatticeSlopes/ExistsSaturatedSlopeEqMuMax.lean:26`), whose proof we have not read,
and used through `deg_eq_deg_add_deg_quot` (`:45–47`) [Lean]. The torsion-free quotients of the
canonical filtration appear in [Bost1996, Prop. A.1, p. 148]. Example 6.8(c) shows that the
hypothesis `IsSaturated` cannot be dropped.

**Proposition 6.10 (`s_lower5`, with its full hypotheses).** *Let `D : Data U0 W Top m f`,
`C : Consts` and $X'' \in \mathbb R$, with every $W(u_0)$ finite and nonempty. Assume*
`D.HidaSetting C` *(`MeanBoundSecondForm.lean:111–116`)*, `D.DIV C` *(`:118–121`)*, `EComp5 D C`
*(`src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:24–25`)*, `Count5 D C` *(`:27–32`)*,
`D.Slopes C` *(`MeanBoundSecondForm.lean:139–141`)* *and* `QuotientSlopeBoundsWith D C Xpp`
*(`QuotientSlopeBoundsWith.lean:19–22`). Then for every $u_0$,*
$$\mathrm{Ga}(u_0) + \mu_{CC}(u_0) - K_{5,\mathrm{v5}}(u_0) - \mathrm{wmean}_{d(u_0)}\bigl(\mathrm{Lo}_5(u_0, \cdot)\bigr) \le D.s(u_0),$$
*with $K_{5,\mathrm{v5}} = c_{\mathrm{Slope}} n_T a L_a (1 + m/k) + m(\mathrm{sum}_A\,\mathrm{lg} + c_E B_0) + \mathrm{SDiv} - \mathrm{sum}_A\,\mathrm{Lam}_5(u_0) + \mathrm{EDiv}$*
(`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:21–23`).
*(Lean: `s_lower5`, `LevelOfCongruence.lean:50–66`.)* [Lean, read]

*Proof (the archive's proof, line by line).* Line `:53` records $\mathrm{sum}_A \ge 0$
(`sumA_nonneg`, `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:152–154`, from the
eighth conjunct $a_t \ge 0$ of `HidaSetting`). Line `:54` extracts the tenth conjunct
$d(u_0, u) > 0$ (`MeanBoundSecondForm.lean:114`). Line `:55` unfolds `Data.s` to
$\mathrm{wmean}_{d(u_0)}(\mu_N - h)$ (`:92`). Line `:56` applies `sub_wmean_le`
(`WeightedMeanData.lean:40–46`): if $c - Y_u \le X_u$ for every $u$ and all $d_u > 0$, then
$c - \mathrm{wmean}_d Y \le \mathrm{wmean}_d X$. This follows from `wmean_mono`, `wmean_add` and
`wmean_const` (`:16–32`), because $\mathrm{wmean}_d X + \mathrm{wmean}_d Y - c$ is the
$d$-weighted mean of $X_u + Y_u - c \ge 0$. It remains to prove, for each word $u$,
$$\bigl(\mathrm{Ga} + \mu_{CC} - K_{5,\mathrm{v5}}\bigr) - \mathrm{Lo}_5(u) \le \mu_N(u) - h(u). \tag{G}$$
Lines `:57–63` collect five inequalities at $(u_0, u)$:

| name | source | inequality |
|---|---|---|
| $h_1$ | `(hSN u0 u).2`, Clause 7 | $\mu_M + \mathrm{Ga} + \mathrm{Fo} - \mathrm{Ee} - \mathrm{Lo}_5 \le \mu_N$ |
| $h_2$ | `hDIV u0 u`, rewritten | $\mu_{CC} + h - \mathrm{Fo} \le \mathrm{SDiv} - \mathrm{sum}_A \log T + \mathrm{EDiv}$ |
| $h_4$ | $\mathrm{sum}_A \ge 0$ times `(hCount u0 u).1` | $\mathrm{sum}_A\,\mathrm{Lam}_5 \le \mathrm{sum}_A \log T$ |
| $h_5$ | `exponent_le_upper` (`:32–35`) | $\mathrm{Ee} \le m(\mathrm{sum}_A\,\mathrm{lg} + c_E B_0)$ |
| $h_6$ | `(hSl u0 u).1`, Clause 6 | $-c_{\mathrm{Slope}} n_T a L_a (1 + m/k) \le \mu_M$ |

The rewrite of $h_2$ at `:59` splits the sum in `DIV` (`Finset.sum_sub_distrib`). It identifies
$\sum_t m(\mathrm{ph}(a_t) - a_t \log\Omega)$ with `SDiv` (`WeightedMeanData.lean:129`) and
$\sum_t a_t \log T$ with $\mathrm{sum}_A \log T$ (`sum_aT_mul`, `:156–157`). The constant terms of
`DIV` are `EDiv` (`:131–132`). Here $h_3$ is $\mathrm{Lam}_5(u_0) \le \log T(u_0, u)$, which is the
first conjunct of `Count5` because `Lam5` (`LevelOfCongruence.lean:17–19`) is that conjunct's
left-hand side. After `unfold K5v5 Data.SDiv Data.EDiv` (`:64`), `linarith` closes (G).

A certificate is $h_1 + h_2 + h_4 + h_5 + h_6$, each with multiplier $1$. Adding the five
inequalities, the terms $\mu_M$, $\mathrm{Fo}$, $\mathrm{Ee}$ and $\mathrm{sum}_A \log T$ cancel, and
what is left is (G). Each of the five is needed. For each $i$ there is a rational point, in the
atoms as `linarith` sees them, where the other four hold with equality and both $h_i$ and (G) fail.
Both facts are checked by `verify_s_lower5_certificate.py` (668 exact assertions). $\square$

**Proposition 6.11 (production and identification on the main path).** *Let `M : Mod Fm x` with
`hx : Fm.x1 < x`, and suppose `∀ u0, SlopesN_at (Fm.L x (M.pt u0)) C.cSl1`. Then:*

1. *`QuotientSlopeBoundsWith (M.data N CH etaB eB ηv ev) C X''` holds, with
   $X'' = $ `(Fm.L x M.i0).sc.X'' (Fm.D x M.i0).R.n` (`model_slopes_five`,
   `QuadraticLogDerivCongr.lean:677–685`)*;
2. *`(M.data …).s u0 = sFrame (div.Nu) (div.h)` at the member `M.pt u0` (`s_eq`, `:687–691`)*;
3. *consequently, Proposition 6.10 applied to `M.data` reads*
   $$\mathrm{sFrame}(N, h) \ge \mathrm{Ga}(u_0) + \mathrm{mu}^{\vee}(\mathrm{RR}) - K_{5,\mathrm{v5}}(u_0) - \mathrm{wmean}_{\mathrm{rk}(N_\cdot)}\bigl(\mathrm{Lo}_5(u_0, \cdot)\bigr),$$
   *where $\mathrm{mu}^{\vee}(\mathrm{RR})$ is `div.RR.muDual`, the slope of the dual lattice
   (`src/Formalism/LocalRingCardinality/DataArith.lean:98`).*

[Lean, read]

*Proof.* (1) After `intro u0 u` and splitting the hypothesis at `M.pt u0` (`:680–681`), the proof
unfolds `LoU` (`:682`) and rewrites with transport lemmas only: `Ee_eq` (`:671–675`), `s_m` (`:530`),
`point_base_constants_eq` (`:538`), `s_card` (`:546–547`), `s_sc` (`:526`), `s_k` (`:532–533`) and
`s_n` (`:534`). These move the member's own $\mathrm{Ee}$, $m$, $B_0$, $\# T$, scale, $k$ and $n$ to
those of the base index `M.i0` used by `M.data`. Then `exact ⟨h1, h2⟩` (`:685`). No lattice theory
happens in this step. Note that `IOsum` becomes the field `IO` (`:497`), and the term
`C * L.sc.X'' D.R.n + 1` of `LoU` becomes $c_{\mathrm{Sl1}} X'' + 1$ in `Lo5`. (2) Unfolding
`Data.s`, `wmean`, `sFrame`, `Rsum` and `dU`, the two sides differ only by the cast
$\sum_u (\mathrm{rk}\,N_u : \mathbb R) = (\sum_u \mathrm{rk}\,N_u : \mathbb N)$, which `Nat.cast_sum`
removes before `rfl` (`:689–691`). (3) Substitute Definition 6.7(4) into Proposition 6.10. $\square$

On the main path the hypothesis of Proposition 6.11 comes from `SlopesNF Fm`
(`QuadraticLogDerivCongr.lean:254`), a hypothesis of `linkCore`
(`src/Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean:38–42`). It is destructured
at `:47` and turned into clause `L7` by `model_slopes_five` at `:198–200`. `SlopesNF` is in turn
produced by `slopesNF_of` and `slopesN_at_of`
(`src/Formalism/SharpRestriction/GlobalSchurBounds/TopDensityNGeSixteen.lean:1529–1546`) from
`Places_at` (`:1516–1525`). There the place-by-place hypotheses `HypLow`, `HypLow2` and `HypHigh`
carry the actual comparison of $\mathrm{mu}(N_u)$ with $\mathrm{mu}(M_u)$; we have not read them
[Lean]. On the consumer side, `s_lower5` is called by `Ga_bound5` (`LevelOfCongruence.lean:121`),
which is called by `each_unit_bound_statement` (`:187`), which `Deduction.ch_top` applies to the
seventh component of `SizeData₂` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean:53–54`).

**Remark 6.12 (what is and is not consumed).** Three points.

- *The pointwise form carries the main path.* `PointwiseBoundVariant`
  (`QuotientSlopeBoundsWith.lean:72–75`) is in the export, together with
  `QuotientSlopeBoundsWith`, `s_lower5`, `sub_wmean_le`, `Data.s`, `sFrame`, `Mod.data`,
  `model_slopes_five` and `s_eq`. Outside the export are the following: `Data.MeanBoundSecondForm`;
  its slope clause `Data.SlopesN` (`MeanBoundSecondForm.lean:143–146`, which uses the older error
  term `Lo`, `:101–103`, rather than `Lo5`); `MeanBoundWith` and `MeanBoundOfLossBounds`
  (`QuotientSlopeBoundsWith.lean:67–80`); and their provers `weighted_mean_bound_statement` and
  `uniform_bound_statement` (`LevelOfCongruence.lean:199–242`). So `MeanBoundSecondForm.lean`
  enters the main path through its definitions, not through its namesake proposition. The cone
  status of `SlopesN`, `QuotientSlopeBoundsWith`, `MeanBoundOfLossBounds` and
  `PointwiseBoundVariant`, and the reading of $s$ as a rank-weighted average, were already published
  by JoseClaudioSJr [Community; `leanprover-community/riemann-hypothesis` issue #5]. M. Jaswal's
  exposition describes Clause 7 as a comparison of slopes "shifted by the gains" [Community;
  Jaswal2026, §3]. Our export check reproduces the cone status independently.
- *Why torsion and saturation must be kept apart.* Clause 7 compares full slopes, so no quotient is
  formed inside `s_lower5`. In the mean bound, quotient slopes enter through `muMinCC`. In
  `Mod.data` this field is `div.RR.muMinDual` (`QuadraticLogDerivCongr.lean:492`), a `muMinDef`,
  that is an infimum of `F.quot` slopes over saturated sublattices (Definition 6.7(1)). It appears
  in Clauses 9 and 10 (`SlopeIneq`, `HHBound`). `F.quot` is torsion-free (Example 6.8(b)), and both
  `HN.muMin` and `DegQuot` require saturation. Without saturation the degree bookkeeping is off by
  $\log \#(L/N)_{\mathrm{tors}}$ (Example 6.8(c)).
- *Why the base ring matters.* The extremal slopes `muMax` and `muMin` range over
  $\mathcal O_K$-submodules, while the weights $d$ are $K$-ranks. Restricting scalars to $\mathbb Z$
  admits more sublattices and can raise $\mu_{\max}$ (Example 6.8(d)–(e)). Extension of scalars is
  different: Bost's canonical filtration and normalized slopes are invariant under
  $f^{\ast}$ for a finite extension $L/K$ [Bost1996, App. A.2 and Prop. A.2, pp. 147–149]. Inside
  `sFrame` all $N_u$ live over the same $K$ (`DivData K Words`), so the factor $[K:\mathbb Q]$ in the
  normalization is common to every term. The weighted mean is therefore the normalized slope of the
  orthogonal sum (Lemma 6.9(3), Example 6.8(f)), with each $h_u$ absorbed by rescaling the metric of
  $N_u$; compare the input `Twist`, `StatementPl.lean:133–146` [Lean].

**Scope and open items.** Proposition 6.10 is the archive's lemma, with its hypotheses copied
verbatim. Proposition 6.11 adds only transport and an unfolding. The relation $\mathrm{mu} = 2\hat\mu$
is checked in Example 6.8 only; a general comparison would need the archive inputs `SizeMu` and
`PlLat` (`StatementPl.lean:75–106`). These are supplied by `sizeMu` and `plLat`
(`src/Formalism/HarderNarasimhan/ShiftInvariance.lean:49–50`), whose proofs we have not read, and
they are used in `bridge_hn_mu_holds` (`src/Formalism/LocalRingCardinality/RankBoundMonotoneInDimension.lean:975–991`)
[Lean]. Three questions remain [Open] here: whether `Ga`, `Fo` and `Ee` are literally sums of
`sizeOfVal` terms; how `HypLow` and `HypHigh` produce Clause 7; and how $N_u$ is built from $M_u$.
The clause is named after quotients, but as stated it only compares slopes.

---

### 6.4.6 From local lengths to Clause 7: the weight partition

The two inequalities of Clause 7 have different sources. The ordinary slope records the total
length lost by passing to a sublattice, divided by its rank. A bound for the maximal slope instead
uses local containment in a scalar ideal multiple. The same rounded shifts enter both estimates.
The finite-sum argument splits the places above the level prime from the rest, where a different
length estimate is available. This is the split used by the calls at
`TopDensityNGeSixteen.lean:1516–1539`.

**Example 6.13 (two places) [Expository].** Take $W=\{t,v\}$, $W_T=\{t\}$ and one lift. Use
$d_M=4$, $d_u=3$, $\delta=1/4$, $f=1$, $T=8$ and $b=1$. The rows are the local inputs for
Proposition 6.14.

| Place | $\ell$ | $g$ | $F$ | $E$ | $\tau$ | $i$ | $n$ | $s'$ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| $t$ | $1$ | $3/2$ | $1$ | $1/4$ | $0$ | $0$ | $2$ | $2$ |
| $v$ | $1/2$ | $2$ | $1$ | $1/4$ | $1$ | $1$ | $8$ | $5/2$ |

The second row saturates $n_v\le 4(\tau_v+i_v)=8$. The gain, $F$ and $E$ sums are $4$, $3$ and
$3/4$. The weighted shift therefore equals $25/4$, while its rounded version equals $11/2$.
The first row contributes $4/3$ to the normalized length sum. The second contributes
$(8-3)/3=5/3$, for a total of $3$. Set
$P=L_T=4/3$, $R=R_X=3/4$, $Q=1/2$, $m_0=0$ and $m_*=-c$, where $c=\log(7)/6$.
The ordinary slope identity gives $m_N=5/2-c$. The global checks are
$\delta=2f/T=1/4\le 1/2$, $A=1=b^2$, $I=1=2Q$ and $4fb^2/T+c=1/2+c<1$ since $\log 7<3$.
Here $s'$ lies $1/4$ below $s$ in each row. Taking $h_M=h_*=1$ and $h_N=13/2$ makes the two
maximal-slope input inequalities equalities. The conclusions give $m_N\ge 7/6$ and
$h_N\le 29/4$. The two rows are abstract real data for the finite-sum proposition.

**Definition (local sums).** Let $W,J$ be finite sets of places and lifts, respectively,
with a distinguished finite set $W_T$. Let $\ell,\tau,i,n,s'$ be real functions of the place, and
$g,F,E$ real functions of lift and place. With `sgw`, `Sg`, `Ta`, `IO` and `BeSum`
as in `src/Formalism/SizeWindowBrackets/ClaimGaFree.lean:11–40`, write
$$
\begin{aligned}
s_w &= \sum_{j\in J}(g_{jw}+F_{jw}-E_{jw}),&
S(z)&=\sum_{w\in W}2\ell_w(z_w-\tau_w),\\
G &= 2\sum_{w\in W}\ell_w\Bigl(\sum_{j\in J}g_{jw}-\tau_w\Bigr),&
F_0&=2\sum_{j\in J}\sum_{w\in W}\ell_w F_{jw},\\
E_0 &= 2\sum_{j\in J}\sum_{w\in W}\ell_w E_{jw},&
A&=2\sum_{w\in W}\ell_w\tau_w,\\
I&=\sum_{w\in W}2\ell_w i_w,&
B&=\sum_{w\in W}2\ell_w\frac{n_w-d_u\tau_w}{d_u}.
\end{aligned}
$$
Here $G,F_0,E_0$ stand for `Ga`, `Fo`, `Ee`. The identity $S(s)=G+F_0-E_0$
follows by interchanging the two finite sums for $F,E$ and distributing the place weights.
This is `weightedSlopeExcess_decomposition` in
`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedSlopeExcessDecomposition.lean:9–18`.

**Proposition 6.14 (ordinary and maximal slope bounds) [Lean, read].**
Take real parameters $d_M,d_u,\delta,f,T,b,P,R,Q,L_T,R_X$ and the six slopes below. Denote the ordinary slope inputs
`muM`, `muMu`, `muN` by $m_0,m_*,m_N$, and the maximal slope inputs by $h_M,h_*,h_N$.
The hypotheses are exactly the following three bundles in `ClaimGaFree.lean:65–102`.

- **`HypLow`.** $\ell_w\ge0$ on $W$, $d_M>0$, $0\le\delta<1$,
  $d_u=(1-\delta)d_M$, $W_T\subseteq W$, $\tau_w=0$ on $W_T$, $i_w\ge0$ on $W$,
  and $n_w\le d_M(\tau_w+i_w)$ on $W\setminus W_T$. In addition,
  $$
  \sum_{w\in W_T}2\ell_w n_w/d_u\le P,\qquad
  \sum_{w\in W}2\ell_w(s_w-s'_w)\le R,\qquad
  m_N=m_*+S(s')-B .
  $$
- **`HypLow2`.** With $c=f\log(T-1)/(T-2)$, assume
  $$
  m_*=m_0-c,\qquad \delta\le 2f/T\le 1/2,\qquad
  \tau_w\ge0\ (w\in W),\qquad A\le b^2,\qquad
  4fb^2/T+c\le1,\qquad I=2Q,\qquad P\le L_T,\qquad R\le R_X.
  $$
  Here $Q$ is the parameter named `IOp`.
- **`HypHigh`.** $\ell_w\ge0$ and $s'_w\le s_w$ on $W$,
  $h_N\le h_*+S(s')$, and $h_*\le h_M$.

Under `HypLow` and `HypLow2` the ordinary slope satisfies
$$
m_N\ge m_0+G+F_0-E_0-(4Q+L_T+R_X+1).
$$
Independently, under `HypHigh` the maximal slope satisfies
$h_N\le h_M+G+F_0-E_0$.

*Proof.* The source is `WeightedSlopeExcessDecomposition.lean:81–204`.

1. **Split the length sum** (`:87–121`). The rank equation makes $d_u>0$. On $W_T$,
   $\tau=0$ leaves exactly the sum bounded by $P$. On its complement, for each $w$ the
   difference between the proposed upper bound and the summand of $B$ is
   $$
   \frac{2\ell_w i_w}{1-\delta}
   +\frac{\delta}{1-\delta}\,2\ell_w\tau_w
   -2\ell_w\frac{n_w-d_u\tau_w}{d_u}
   =\frac{2\ell_w[d_M(\tau_w+i_w)-n_w]}{d_u}\ge0 .
   $$
   This uses the rank equation and the local length bound.
2. **Restore the full place sums** (`:95–105,122–143`). The $i$-sum over the complement
   is bounded by $I$ because $\ell_w i_w\ge0$. The $\tau$-sum over the complement already
   equals $A$ because the omitted terms vanish. Thus
   $B\le P+I/(1-\delta)+\delta A/(1-\delta)$.
   The inequality for $R$ gives $S(s')\ge S(s)-R$. Substitution into the ordinary
   slope identity gives
   $$
   m_N\ge m_*+G+F_0-E_0-R-P-\frac{I}{1-\delta}
         -\frac{\delta}{1-\delta}A .
   $$
3. **Simplify the losses** (`:145–189`). The wrapper reads $I=2Q$ from `HypLow2`
   and factors the $2$ out of the sum. Nonnegative $\ell,i,\tau$ imply $Q,A\ge0$.
   Since $1-\delta\ge 1/2$, we have $I/(1-\delta)\le 4Q$ and
   $\delta/(1-\delta)\le 2\delta$. Hence
   $\delta A/(1-\delta)\le 2\delta A\le (4f/T)A\le 4fb^2/T$.
   The last multiplier is nonnegative by $0\le\delta\le2f/T$.
   Combining this cost with $c$ uses the single budget $4fb^2/T+c\le1$.
   Replace $P,R$ by $L_T,R_X$ to obtain the stated lower bound.
4. **Compare maximal slopes** (`:191–204`). Multiply $s'_w-\tau_w\le s_w-\tau_w$
   by $2\ell_w\ge0$ and sum. Then $h_N\le h_*+S(s')\le h_M+S(s)$, and the same
   sum identity gives the upper bound. $\square$

**The lattices and the local inputs.** Fix a member $D$ with its size record $L$ and a word $u$.
Here $K=D.\mathrm{what}_2.\mathrm{LL}$ and $M_u$ is `(D.fm u).lat 0`. The final Hermitian
lattice $N_u$ is `D.div.Nu u`. Write $N_u^0$ for the submodule `L.NuLat u` before the
fractional-ideal shift. The relevant relations are the following.

- `D.nuIn u` is a norm-preserving injection from the ambient $K$-space of $N_u$ to that of
  $M_u$, with image `(D.fm u).ramSub`. The reference module $M_u^{\rm ram}$ is the preimage of the module of $M_u$ under
  this injection. `LocalQuadraticParts.MuH D u` uses that preimage with the ambient space,
  basis and metric of $N_u$. Its slopes are $m_*$ and $h_*$, while those of $M_u$ are $m_0$
  and $h_M$. See `src/Formalism/LocalRingCardinality/RhoDetPrimeEqMuTildeMulChiPow.lean:291–298`,
  `DataDIVDefs.lean:12–13` in the same directory and
  `src/Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean:445,621–630`.
- `NuDef` away from $T$ and the containment clause of `adm26` at $T$ give
  $N_u^0\subseteq M_u^{\rm ram}$ via `nu_le_mram`. The local-to-global step considers
  the ideal of scalars sending a vector into the reference module. A proper such ideal
  would lie in a maximal ideal, contradicting containment at that place.
  Under `NuCommens` a nonzero scalar sends all of $M_u^{\rm ram}$ into $N_u^0$.
  Both span the ambient space of $N_u$ and have rank $d_u$. The quotient in the length
  calculation is the localization of $M_u^{\rm ram}/N_u^0$. In `NuDef` its finite
  length at $w$ is $e_w\,L.\mathrm{lenMN}(u,w)$, where $e_w$ is `ramIdx w`.
  See `DataDIVDefs.lean:31–54`,
  `src/Formalism/SharpRestriction/GlobalSchurBounds/LinkPk.lean:23–35,65–71,104–105,121–130`,
  `TopDensityNGeSixteen.lean:1579–1599` and
  `src/Formalism/LocalToGlobal/GlobalTheory/PlacesP.lean:110–127`.
- `NprimeDef` identifies the module of $N_u$ with $I_uN_u^0$, where
  $I_u=\prod_{w\in W}\mathfrak p_w^{-\lfloor e_ws_w\rfloor}$ and
  $\mathfrak p_w$ is the prime ideal at `D.plEq w` (`DataDIVDefs.lean:15–24`).
  Thus the source uses a pullback, a commensurable sublattice and a fractional-ideal
  multiple. The rank deficit compares the original rank parameter `D.duS u` with
  the rank $d_u$ of $N_u$. Here `duS` is the complex dimension of `(D.mem u).A.Mu0` (`RhoDetPrimeEqMuTildeMulChiPow.lean:345–346`). The relative-index computation takes place between the
  two rank-$d_u$ lattices in the ambient space of $N_u$.

**The three size sums.** With $\bar w=D.\mathrm{plEq}(w)$,
$\ell_w=e_w\,\mathrm{lw}(K,\bar w)$ and
$\mathrm{lw}(K,\bar w)=\log\mathrm N\mathfrak p_w/[K:\mathbb Q]$.
By definition, for every real $y$,
$\mathrm{sz}(w,y)=\mathrm{sizeOfVal}(\bar w,e_w y)=2\ell_w y$.
The record identifies $e_w$ with the ramification index at $\bar w$ (`ram_eq`).
The three equalities `Ga_eq`, `Fo_eq` and `Ee_eq'` distribute the factor $2$ and give
$$
\begin{aligned}
L.\mathrm{Ga}
 &=\sum_{w\in W}\mathrm{sizeOfVal}\Bigl(\bar w,
         e_w\Bigl[\sum_{j\in J}L.\mathrm{gainD}(j,w)-L.\tau(w)\Bigr]\Bigr),\\
L.\mathrm{Fo}
 &=\sum_{j\in J}\sum_{w\in W}\mathrm{sizeOfVal}(\bar w,e_w L.F(j,w)),\\
L.\mathrm{Ee}(u)
 &=\sum_{j\in J}\sum_{w\in W}\mathrm{sizeOfVal}(\bar w,e_w L.E(u,j,w)).
\end{aligned}
$$
Here $W=L.\mathrm{supp}$ and $J=\{1,\ldots,D.R.m\}$. Gains use `gainD`, which zeroes the
gain at dropped residue characteristics. Only the $E$ sum depends explicitly on $u$.
These identities use the real-valued size function on the given inputs. The actual integer
ideal exponent occurs at the separate rounding step in $I_u$.
See `DataArith.lean:39–46`, `DataParams₂.lean:203–222`,
`RhoDetPrimeEqMuTildeMulChiPow.lean:134–138` and `TopDensityNGeSixteen.lean:1482–1512`.

**How the archive fills the hypotheses.** In `PlacesP.lean:297–435`, `places_at_of`
takes `NprimeDef`, `NuDef`, `NuCommens`, positive rank, `adm26` with constant $C_{26}$,
and `NprimeMuR` with constant $C_\mu$. Both constants are bounded by $C$. Its remaining
inputs are the local containment and length bound away from $T$, natural-valued $\tau$,
nonnegative $i$, zero $\tau$ above $T$, vanishing local length or `lenMN` off support,
the budget $A\le b^2$, and the three numerical bounds $T>2$, $2f/T\le1/2$ and
$4fb^2/T+c\le1$. Here $T=(D.\mathrm{mem}\,u).A.T$, $f=D.R.f$, $b=L.\mathrm{sc}.b$,
$W_T$ is the subset of $W$ with residue characteristic $T$, and $Q=\mathrm{IOsum}(L)$.
The local functions are $g=L.\mathrm{gainD}$, $F=L.F$, $E=L.E(u,\cdot,\cdot)$,
$\tau=L.\tau$, $i=L.\mathrm{io}$ and $n=L.\mathrm{lenMN}(u,\cdot)$.
Away from $T$, containment is in the local ideal power with exponent
$\lfloor e_w\tau_w\rfloor$ (natural floor in Lean). Off support the containment
uses exponent zero. See `QuadraticLogDerivCongr.lean:163` for `IOsum`.
The proof assembles the witnesses as follows.

1. **Rank and truncation** (`:313–333,359–370,405–420`). With $d_M=D.\mathrm{duS}(u)$,
   `adm26` gives $d_u/d_M=(1-1/(T-1))^f$. Positivity of $d_u$ forces $d_M>0$.
   `deficit_bounds` (`WeightedSlopeExcessDecomposition.lean:35–62`) uses
   $0<1-1/(T-1)<1$ and Bernoulli's inequality, giving
   $0\le\delta=1-d_u/d_M<1$ and $\delta\le f/(T-1)\le 2f/T$.
   The proof takes $P=L_T$ equal to the exact truncated sum above $T$.
   The last clause of `adm26` supplies its bound
   $L_T\le C\,\#D.\mathrm{host}.\mathrm{TT}\,m(a/k+b')\log T$.
2. **Ordinary slope** (`:129–169,334,371–380`). The conditional theorem `mu_index_sum`
   first gets a finite relative index for the same-rank inclusion. It factors that
   index into prime norms to local length powers, takes logarithms and divides the
   normalized log cost by rank (`:61–102`). In `mu_eq` the off-support input and
   `NuDef` restrict the sum to $W$, and the latter converts length to $e_w n_w$.
   The fractional-ideal shift `J.mu_diff` adds
   $\sum_w 2\,\mathrm{lw}(K,\bar w)\lfloor e_ws_w\rfloor$.
   It applies the fractional-ideal slope formula to $I_u$, then expands the norm
   of $I_u$ as a product of powers of prime norms
   (`src/Formalism/SharpRestriction/AdmissibleParameterJoins/SumLogPrimeFactorsLe.lean:352–397`).
   Set $s'_w=\lfloor e_ws_w\rfloor/e_w$. Then the resulting slope identity is
   $m_N=m_*+S(s')-B$ because the $\tau$ terms cancel.
3. **Maximal slope** (`:171–237,335–351,393–404`). Set $k_w$ equal to the natural floor
   of $e_w\tau_w$, which is exactly $e_w\tau_w$ by the natural-valued input. At $T$ it
   is zero. To glue the local containment bounds, at each place multiply by a
   scalar in the product of the other prime powers and outside that place's prime.
   A prime containing that product would contain one of its factors, forcing equality
   with one of the other maximal ideals. The local membership criterion then gives an
   inclusion of $N_u^0$ in
   $(\prod_w\mathfrak p_w^{k_w})M_u^{\rm ram}$. After multiplying by $I_u$, monotonicity
   of maximal slope and the fractional-ideal norm bound yield $h_N\le h_*+S(s')$.
   The other comparison $h_*\le h_M$ is a clause of `adm26`. Integer floor gives
   $s'_w\le s_w$.
4. **Remaining losses** (`:381–392,421–435`). Take $R=R_X$ equal to
   $\sum_w2\ell_w(s_w-s'_w)$. Rewriting it as the negative of the difference
   between the rounded and unrounded weighted shifts allows the absolute bound
   in `NprimeMuR` (`src/Formalism/SharpRestriction/GlobalTheoremInputs.lean:69–70`) to give $R_X\le C\,L.\mathrm{sc}.X''(D.R.n)$.
   The input `adm26` also gives $m_*=m_0-c$, and unfolding `IOsum` gives $I=2Q$.

**Remark (connection to Proposition 6.11).** In `slopesN_at_of`, `Places_at L C`
supplies the three bundles and both bounds on $L_T,R_X$. The two calls in Proposition
6.14 are followed by the three size-sum rewrites. The upper bound is weakened by
$C m B_0\ge0$ via `loss_bound_nonneg`. For the lower bound, $C\ge4$ and $Q\ge0$
give $4Q\le CQ$, so $4Q+L_T+R_X+1\le\mathrm{LoU}(L,C,u)$.
This proves `SlopesN_at` (`TopDensityNGeSixteen.lean:1529–1539`).
The family wrapper `slopesNF_of` applies it at every member beyond the threshold
(`:1541–1546`). On the main path, the family inputs enter through `placesF_min'`
(`src/Formalism/LocalToGlobal/GlobalTheory/PlacesMin.lean:23–116`). It takes a common
threshold and passes the level-prime summary, ranks, commensurability, and the
`LinkG` and `LinkMu` estimates to `places_at_of` at lines 101–105.
The rank and slope suppliers for this application are traced in §6.4.7.
The call is explicit in `src/Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean:505,510`.
Proposition 6.11(1) transports this input into Clause 7. The conditional use of
Proposition 6.10 is precisely item (3).

For comparison, Bost's canonical filtration uses torsion-free quotients with
quotient Hermitian metrics [Paper; Bost1996, Appendix A.3, pp. 147–148].
Here the local length of the finite-index quotient measures a slope loss.
Issue #5 identifies the pointwise consumer and Jaswal describes the comparison
as a shift by the gains [Community; G2 and Jaswal2026, §4, printed p. 21].

The finite-sum and assembly proofs above are [Lean, read]. The underlying level-prime
facts `adm26`, `LinkG` for the local containment and length estimates, `LinkMu` for
the rounding bound, and the index and Hermitian fractional-ideal theorems used in
`PlacesP` are named inputs [Lean]. Their deeper arithmetic proofs and the upstream
construction of the lattice data are outside this reading [Open].

---

### 6.4.7 The rank and slope at the level prime

**Motivation.** In the pointwise slope comparison the reference lattice is the ramified part of the level-zero lattice, transported to the division space. Its rank determines the denominator of the local length loss. Its average slope determines the starting point for adding gains. Both quantities come from the same level-prime operation: take the kernel of each coordinate sum over the residue-field units. Each sum eliminates one coordinate in its own direction. The remaining integral directions have a different Gram determinant, even when the original unit action is isometric.

**Example 6.15 (two blocks).** Take $T=7$, two level places with residue field $\mathbb F_7$, and the product of their unit groups. Each factor has six elements. In one factor the five vectors $e_a-e_1$, indexed by $a\ne1$, have Gram matrix $I_5+J_5$, where every entry of $J_5$ is one. Its eigenvalues are $6,1,1,1,1$. In two factors, their tensor products give $25$ directions from the original $36$. The tensor Gram determinant is $6^{10}$, since each factor contributes its determinant to the fifth power. Take the coefficient field $\mathbb Q(i)$ with the standard Hermitian metric, and take a slice with the standard lattice $\mathbb Z[i]^r$. The two blocks below use $r=1$ and $r=2$. The reference slope before imposing the sums is zero in both examples. The determinant column is the ramified Gram determinant at the one complex place.

| Slice rank $r$ | Level-zero rank | Ramified rank | Gram determinant | Ramified slope |
|---:|---:|---:|---:|---:|
| 1 | 36 | 25 | $6^{10}$ | $-10\log(6)/25$ |
| 2 | 72 | 50 | $6^{20}$ | $-20\log(6)/50$ |

The deficit is $11/36$ in each block. A weighted length numerator $A$ in the division formula would be divided by $25$ or by $50$, respectively. The average slope shift stays equal to $-(2/5)\log 6$ because the determinant exponent and the rank double together. These are examples of the finite Hermitian calculation.

**Definitions and hypotheses.** Fix a prime $T>2$, a finite index set $I$ with $f$ elements, and a group $G_i$ of order $T-1$ for each $i\in I$. In the archive $G_i=\mathbb F_i^\times$ with $\lvert\mathbb F_i\rvert=T$. Write $G=\prod_iG_i$, and use $a_i$ for the element with entry $a$ at $i$ and identities elsewhere. For a function $F$ on $G$ set $S_i F(h)=\sum_{a\in G_i} F(a_i h)$. Put $U=\bigcap_i\ker S_i$. The archive uses the unaveraged sums. Inversion of the summation variable leaves the sum unchanged.

Let $K$ be a totally complex number field and let $W$ be a finite-dimensional $K$-space of positive dimension $r$. Give $W$ a Hermitian metric at each complex place and a finitely generated $\mathcal O_K$-lattice $P$ spanning $W$. The induced model has an injective $K$-linear map from $W^G$ into the level-zero ambient space. On this image the metric is the orthogonal sum of the metrics on $W$. The level-zero lattice $M_0$ is exactly the image of $P^G$, and its rational ramified subspace is the image of $U$. Let $M_{\mathrm{ram}}=M_0\cap U$ under this identification. The slope convention is $\mu(M)=-\log\operatorname{ht}(M)/(n_\infty\operatorname{rk}_K M)$, where $n_\infty$ is the number of complex places and the height uses Hermitian Gram determinants and the finite-index correction. This is the convention of the archive's $\mu$, with the complex Gram determinant itself in the height calculation. Bost gives the classical definition of normalized Hermitian slope and the canonical polygon in Appendix A.2–A.3, pp. 146–148. [Bost1996](https://www.numdam.org/item/SB_1994-1995__37__115_0/)

**Lemma 6.16 (rank and average slope of the ramified block).** Under these hypotheses, write $d_0=\operatorname{rk}_K M_0$ and $d=\operatorname{rk}_K M_{\mathrm{ram}}$. Then
$d=d_0(1-1/(T-1))^f$
and
$\mu(M_{\mathrm{ram}})=\mu(M_0)-f\log(T-1)/(T-2)$.
The rank identity also holds for a finite free $G$-set $X$ in place of $G$, with $d_0=\dim_{\mathbb C}\mathbb C^X$ and $d$ the dimension of the joint kernel on $\mathbb C^X$. Here free means that a group element fixing any point is the identity.

**Proof.** Write $s=T-1$ and $m=s-1$. For each $i$ and $a\ne1$ let $b_a=e_a-e_1$. The products $b_{\alpha}=\bigotimes_i b_{\alpha_i}$, indexed by tuples $\alpha$ with every entry different from the identity, lie in the joint kernel because each $b_a$ sums to zero. Their values on such tuples form the identity matrix. A function in the kernel is determined by those values: whenever a coordinate equals $1$, express that value as the negative sum of values obtained by replacing the coordinate by a nonidentity element, and induct on the number of identity coordinates. Thus $F=\sum_\alpha b_\alpha F(\alpha)$. The same reconstruction holds for functions valued in $P$, since its coefficients are integers. It identifies $M_{\mathrm{ram}}$ with $P^{m^f}$ through this particular integral map. The ambient rank is $rs^f$, and the ramified rank is $rm^f$. On a free finite $G$-set, a choice of representative gives a bijection from $G$ to each orbit, and the argument applies on every orbit with scalar coefficients. This gives the same rank fraction. If $f=0$, the empty product is one and the joint kernel is the entire ambient space.

For the metric, $\langle b_a,b_b\rangle=\mathbf 1_{a=b}+1$. The Gram matrix in each factor has determinant $s$. The full Gram matrix $Q$ is their tensor product and for $f\ge1$ has determinant $s^{f m^{f-1}}$. For $f=0$ it is the identity of size one. To see precisely how its determinant enters the slope, take a $K$-basis of $W$ from $P$ with $\mathcal O_K$-span $E$ of finite index $J$ in $P$. For a product of $b$ copies of $P$ injected with Gram factor $Q_b$, the basis formed from $b$ copies of this basis has index $J^b$. At each complex place, its Gram matrix is $Q_b\otimes H_v$ where $H_v$ is the basis Gram matrix of $W$. Its determinant is $(\det Q_b)^r(\det H_v)^b$. Consequently the height is $\operatorname{ht}(P)^b(\det Q_b)^{r n_\infty}$, since the finite-index correction is also raised to the $b$-th power. Dividing its negative logarithm by $br n_\infty$ gives $\mu(P)-\log(\det Q_b)/b$. Apply this first with $b=s^f$ and $Q_b$ the identity, then with $b=m^f$ and $Q_b=Q$. The loss is $f\log(s)/m$. The positivity assumptions ensure positive ranks, positive Gram determinants and a nonzero denominator. $\square$

**How level zero supplies the hypotheses.** For a word $u$, set $T=(D.mem\,u).A.T$ and $f=D.R.f$. On the rank side the input is the finite equivariant model `FreeT`. Its equivalence $\Theta$ identifies the zero-level complex forms with scalar functions on $X$. Equivariance carries each local diamond operator to translation in one coordinate, so summing the operators carries its kernel to the zero-sum kernel. This identifies $D.duS\,u$ with $\lvert X\rvert$ and $(D.mem\,u).A.du$ with the joint-kernel dimension. The archive first proves the integer identity $d(T-1)^f=d_0(T-2)^f$, then divides in $\mathbb Q$ using $T-1\ne0$.

For the metric side the archive constructs the slice from forms supported on representatives of the free diamond orbits of classes. Restrict a rational form to the classes belonging to one translated support, then translate back. Summing these translates recovers the original form. The supports partition the classes, so the decomposition is unique. The integral membership test is pointwise on classes and local bases, and the diamonds and their inverses preserve the lattice. Hence membership in the full lattice is equivalent to membership in the slice lattice in every coordinate. Disjoint class supports are orthogonal at every infinite place. Each diamond acts isometrically, so the inner product on a translated copy is the slice inner product. Finally the coordinate norm sums correspond to the sums $S_i$ by reindexing the translates. This yields the induced model in Lemma 6.16. The archive proves that the level-zero lattice is nonzero using a nonzero polynomial value supported on a class and the full rational span of the lattice. Projection onto the identity summand sends the full lattice into the slice lattice and is the identity on the slice. The slice therefore spans over $K$. It is finitely generated by the Noetherian property of the ring of integers and nonzero because a zero slice would give a zero full lattice. With $T>2$ and $r>0$ the ramified lattice is also nonzero.

The tied level-zero forms supply the split diamond action and the stabilizer condition `admS` (`StabZero`). The finite-character hypothesis `ChiFin0` gives a common positive exponent annihilating the level-zero character and requires its values to lie in the embedded coefficient field. In particular every conjugate of such a value has modulus one. The isometry proof uses the corresponding equality of diagonal norms and polarization. The archive's `HidaSetting` asks for $2fN(m)+1<T$, $4a_{\max}<T$, $2(w_{j,\tau,a}-w_{j,\tau,b}+N(j))<T$ for all $j\le m$, $\tau,a,b$ and nonnegative $b_{\rm Top}$ at the top places. With $N(m)\ge1$ this ensures $T>2f+1$, as well as $T>2$ in the archive's ranks. The finite group proof concerns an average Hermitian slope. Any deeper assertion about the construction of a Hida ordinary summand, for example via a unit-root projector for a $U$-operator, remains an upstream question [Open]. `HidaSetting`, the tied arithmetic data and the deeper suppliers of their geometric identities are named inputs [Lean].

**The call in PlacesP.** `transposed_slope_of_form_tie` takes the actual family pair `Nonempty FreeT` and `SlopeLine` delivered by `slope_free_branch_family` and invokes `division_side_conditions_at_sizeData`. This supplies the rational rank equation, the average slope equation and the maximal-slope inequality. The maximal inequality uses the sublattice inclusion with the restricted metric (with equality in the zero-dimensional branch). `RamifiedRankLines` casts the rank identity to $\mathbb R$ and transports both slopes using `ram_slopes`, an isometry along `nuIn` carrying `MramL` to the level-zero ramified lattice. In `division_rank_slopes_of_lines` these become the first three fields of `adm26`. Its last two fields use separate local length inputs. In the positive-rank branch of the length estimate, Bernoulli's inequality applied with $1/(T-1)$ and $T>2f+1$ gives $d/d_0\ge1/2$. This permits replacing $d_0$ by $2d$ when normalizing the length bound.

The family call `LvlWire.slope_lemma_division_side` passes `J.lemma_five_one_of_theorem_two Fm hTu hE` as the `LevelTFamily` argument of `placesF_min'`. Here `hE` is the `LvlF` obtained from the tied forms, and the level summary uses $C_{26}=4\cdot9$. At the selected scale and index `placesF_min'` passes `h26 x e3 i` to `places_at_of`. In that body `nuFull_of` uses the commensurability witness and the nonzero fractional ideal to give a full division lattice. `NuFull.rank` then identifies its rank with $d$. The separate positive-rank input `hrank` and `c1` force $d_0>0$. The argument `hform` to `deficit_bounds` is now the actual identity $d=d_0(1-1/(T-1))^f$. The deficit witness is $1-d/d_0$, and the average length terms use $d$ in their denominator. The second field `c2` supplies the reference average slope shift, while `c3` supplies the maximal-slope comparison. This is the application within the previously traced pointwise comparison.

**Proof references.** All paths below lie in the fixed `lean.tar.gz`, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The detailed source map records the arithmetic suppliers, consumed projections and reading boundaries.

- [Lean, read] Finite rank and rational cast: `src/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean:10–210` and `src/Formalism/SharpRestriction/GlobalSchurBounds/FiniteModelOfAdmissibleTransports.lean:751–857`.
- [Lean, read] Integral fibre kernel and determinant normalization: `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/SlopeRamifiedInducedPrimeField.lean:18–107,149–259,299–355` and `src/Formalism/LocalToGlobal/Columns/SliceIntegralDeltaNeBot.lean:127–303,421–556,681–710`.
- [Lean] Arithmetic model and its finite-character assembly: `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/SlopeRamifiedInducedPrimeField.lean:547–850`, `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/SlopeLineRamifiedFormula.lean:24–69` and `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/SlopeFormulaOfCharacterFinite.lean:12–20`.
- [Lean, read] Consumption of the rank and slopes: `src/Formalism/SharpRestriction/GlobalSchurBounds/LinkMin.lean:463–608,638–650`, `src/Formalism/LocalRingCardinality/Lemmas.lean:59–67,101–113`, `src/Formalism/LocalToGlobal/Divisibility/DivisibilityRemainder/NoColumnCase/LvlWire.lean:17–43`, `src/Formalism/LocalToGlobal/GlobalTheory/PlacesMin.lean:97–105` and `src/Formalism/LocalToGlobal/GlobalTheory/PlacesP.lean:309–420`.

---

### 6.4.8 From residue-field units to the level-zero forms

A congruence condition at the level prime starts with reduction of a lattice. To impose a condition on an automorphic form, one also needs to know which operator on forms corresponds to a unit in the residue field. At level zero this correspondence comes from the diamond actions on classes and on their value spaces. The class action identifies which blocks can be moved to one another. The value action tells us what to transport. Together they turn a zero-sum function into a form with the required local vanishing.

**Examples [Expository].** Take one residue coordinate and one scalar value on one free orbit. At $T=5$, in $\mathbb Z[i]$ take $\pi=2+i$. It has norm $5$. Reduction at $(\pi)$ sends $i$ to $-2$ in $\mathbb F_5$, so $\pi$ reduces to zero and $\bar\pi$ to $4$. In unit order $1,2,3,4$, the function $(1,-1,0,0)$ sums to zero. The fibre sum at $2$, for example, reads the entries at $2,4,1,3$ and gives zero. At $T=7$ use $\mathbb Z[\omega]$, where $\omega^2+\omega+1=0$, and take $\pi=3+\omega$. Its norm is $9-3+1=7$. Reduction sends $\omega$ to $4$, and $\bar\pi=2-\omega$ reduces to $5$. In unit order $1,2,3,4,5,6$, take $(1,0,-1,0,0,0)$. The fibre sum at $3$ reads the entries at $3,6,2,5,1,4$ and again gives zero. In the scalar orbit model with pullback by multiplication, these are the actual form values in the chosen trivialization. With nontrivial value transport, the same lists specify values of the *translated* forms at the orbit representative. These examples isolate the quotient and orbit constructions. The host congruence, valuation, chart and size hypotheses below are additional arithmetic inputs.

**Definition (the two level-zero records).** Fix a member $u$ of the family and write $T=T(u)$. The archive calls the CM field $E$ and its real field $F$. The index $v$ runs over the selected primes $P$ of $E$ dividing the integral element $\pi$ with $\pi\bar\pi=T$. Write $k_v=\mathcal O_E/P$. The record `AtTTied` identifies $v$ with the prime $P\cap\mathcal O_F$ above $T$, supplies reduction to $k_v$, and ties the two sides to valuations in the coefficient field. It includes the original host congruence on $\pi$ and its membership in the specified subfield. The flag `seenP` chooses whether $\pi$ or $\bar\pi$ has positive valuation under the specified embeddings. This is information at coefficient-field places.

The record `Forms0` keeps this prime data, a class and level description, an evaluation and value-space description, and a common auxiliary-prime localization with its level condition. For the lattice $L_c$ of a class $c$, let $L_c^\vee$ be its Hermitian dual and $K_{v,c}=L_c+P L_c^\vee$. The reduction maps in `lv0` are surjective, semilinear via reduction, and have kernels $P L_c^\vee$ and $P K_{v,c}$, respectively. The distinguished functional on the first quotient has preimage of zero equal to $K_{v,c}$. If $z$ maps to a vector of functional value $1$, the image of $Tz$ in the second quotient is the distinguished vector. The additive comparison `fMe0` identifies the chart functional with the prescribed residue functional after transporting into chart coordinates. The up and down comparisons describe the chart moves, their local lattice equalities and their action on values with the inverse level-character factor. The norm and `bw0` fields retain the prescribed metric and weight comparison. Here level zero is the index $i=0$ of the chain. The residue prime $T$ still occurs in the level-zero data. See `src/Formalism/LocalToGlobal/HermitianForms/PrkSmul.lean:25–93,134–166` and `src/Formalism/LocalToGlobal/GroupLattices/DownNaturalLevelZero.lean:12–30`.

**Lemma (conditional construction of the level-zero ramified forms) [Lean, read].** Fix a word of a standard column record $D=I.\mathrm{rec7}(l,Z)$ with its supplied laws and pins. Use the chart, value, lattice and level comparisons for $I$, and assume the level-zero stabilizer condition `admS`. In the finite action step, write $C$ for the class set, $M$ for the complex space `Mu0`, $G=\prod_v k_v^\times$, and $V=\mathbb C^d$ for the common coordinate space supplied by the level-zero evaluation theorem. The supplied comparison is a linear isomorphism $\Phi:M\to V^C$. The class action is free, the operators give a representation $\rho$ of $G$, and $\Phi(\rho(g)\phi)(c)=0$ implies $\Phi(\phi)(gc)=0$. The action of a single unit $a$ in coordinate $v$ agrees with the prescribed $\rho_T(v,a)$.

Choose representatives $c_q$ of the class orbits. For every complex function $b$ on $G\times(C/G)\times\{1,\ldots,d\}$ with zero sum in each unit coordinate separately, there is a unique $\phi\in M$ with
$$
\Phi(\rho(g)\phi)(c_q)_j=b(g,q,j).
$$
It belongs to the archive's `Mram`, and every form in `Mram` is obtained this way. The prime and chart hypotheses used to obtain the action are those of the standard comparison producer, with the split-prime and stabilizer comparisons specified below.

**Proof.** First construct the prime record. The map `underT` contracts a prime dividing $\pi$ to $\mathcal O_F$. The norm identity puts $T$ in the contraction. Two selected primes above the same real prime are equal or conjugate by the split-prime comparison. The conjugate case would put $\bar\pi$ in a selected prime, contrary to `conj_piT_notMem`. Conversely, take a prime above a real prime containing $T$ by integral lying-over. It is nonzero since it contains the nonzero integer $T$. Primality and $T=\pi\bar\pi$ put either $\pi$ or $\bar\pi$ in it. In the second case take the conjugate prime, which has the same contraction. This proves bijectivity.

Use the quotient maps for `res`. They are surjective, kill $\pi$, and send its conjugate to a nonzero element by the preceding exclusion. Extension followed by reduction kills an integer of $F$ exactly when it belongs to the contraction. At a coefficient-field prime $w$ of residual characteristic $T$, first put $T$ in its prime ideal. The supplied `tauAt_mem_iff` then matches ideal membership at the selected real prime with membership of the transported integer at $w$. Positive valuation is equivalent to this membership. For `seenP`, when the flag is true the required membership is the defining `seenC` condition. When false, use primality at $w$ and the norm identity under each embedding. The equality of the embedded copies of $\pi$ in the prime law makes membership for one embedding imply membership for all. Thus in the false case every embedded conjugate belongs to $w$. Identify the integral conjugate with the host conjugate by compatibility of the embeddings. The stated norm, subfield and congruence conditions are inherited from $X$. This is the complete assembly in `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnderTBijective.lean:11–98`. The field and prime laws, including `tauAt_mem_iff`, enter as supplied comparisons [Lean].

The standard form comparison chooses the common auxiliary-prime data and finite charts. At the two endpoints the chart type has a unique element. Use its default element as representative, and use uniqueness to rewrite the chart of each class to this representative. The geometric comparison at the base endpoint then has a single chart for all classes. The producer takes $A(u)=\mathrm{atTTied}(I,l,Z,u)$, uses the chosen projections and their identity witnesses, and views the compatible quotient maps as `LvTied` by copying their maps and laws. The chart representative gives `cls0`. The chart evaluation, determinant, inner-product and dilation comparisons give `val0`. The common auxiliary-prime data and the endpoint chart supply `glev0`. Specializing the local functional and up/down comparisons to the unique chart supplies `fv0` and the natural transport fields. The metric and weight comparisons supply the final two fields. For the determinant comparison the producer takes the change-of-basis matrix to be the identity, using the standard-coordinate Gram and lattice identities. There is no transport across chart types at this endpoint because the representative equals every chart label.

The reduction supplier `exists_level_projections` identifies the coordinate dual with the decorated shifted lattice and identifies the kernel of reduction with the selected prime ideal. Consequently the sum defining $K_{v,c}$ agrees with the decorated kernel lattice. It uses the two localization equalities, one for the shifted lattice and one for this kernel lattice, to take their reduction maps. The projection laws supply surjectivity, scalar compatibility and the two kernels. On the first reduction the chart functional agrees with the decorated functional, so the decorated zero criterion supplies the required kernel of the composite. On a lift with functional value $1$, `reductionModPrime_levelPrime_smul_eq` identifies the image of $Tz$ with the decorated distinguished vector. Finally the maps agree on local representatives by `proj_mk`, giving the identity witnesses used in the standard comparison. See `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ReductionModPrimeLevelPrimeSmulEq.lean:197–231`.

In the source the preceding specialization occurs inside the construction of `FormsTiedSym`, before packaging the family as `ColsTiedSym`. The actual `FormsTiedSym.to0` projection then copies `atT`, the auxiliary localization and `glev0`, and evaluates every indexed field at $0$ using the proof $0\le m$ and, where required, the left endpoint witness. This proves each field of `Forms0`; the transport compares the data of the same word and the same chart. The chart and value suppliers `exists_charts`, `charts_funKilled`, `val_tied`, `dilTied`, `fvTieG`, `upNatTie`, `dnNatTieG_cols`, `ipV_norm_tie` and `bw_tie` enter through their specified comparison properties [Lean]. See `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsStandardFormComparisonSymmetricLevelMember.lean:52–108,127–140,160–178,224–243`, `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MemFiCComp.lean:82–111`, and `src/Formalism/LocalToGlobal/GroupLattices/Joint0.lean:13–30`.

Now pass from the record to coordinates. The split comparison and the diamond-existence theorem supply single-coordinate diamond elements. Each $k_v$ has $T$ elements, so its prime-field identification transports $k_v^\times$ to $(\mathbb Z/T\mathbb Z)^\times$. Products of the individual diamonds give the commuting action used by the coordinate map. To check freeness, represent a group element fixing $c$ by a multi-diamond. Each component of its residue multiplier is nonzero. The stabilizer comparison forces every component to equal $1$. The diamond transport gives the zero-implication of the lemma, and the single-coordinate comparison identifies the operator with $\rho_T(v,a)$. These are the inputs used in `free_rank_model_of_diamonds`. See `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/GroupActionMulSingleEqDilation.lean:195–247,253–304`.

Define $E(\phi)(g,q,j)=\Phi(\rho(g)\phi)(c_q)_j$. If $E(\phi)=0$, all the value blocks of $\rho(g)\phi$ vanish at the representatives. The zero-implication makes $\Phi(\phi)$ vanish at every $gc_q$, hence $\phi=0$. The map $(g,q)\mapsto gc_q$ is bijective: surjectivity follows from the choice of representatives, and equality first forces the same orbit and then the same group element by freeness. Therefore domain and codomain of $E$ have the same finite dimension and $E$ is surjective. Since $G$ is abelian and $\rho$ is multiplicative, $E(\rho(a)\phi)(g,q,j)=E(\phi)(ag,q,j)$. Applying this to a single-coordinate unit and summing proves that $E$ takes the unaveraged operator `Nm v` to the fibre sum. By definition, $\mathrm{Mram}=M\cap\bigcap_v\ker(\mathrm{Nm}_v)$ in the ambient value space. Thus the unique inverse image of $b$ is the claimed form, and conversely any form in that subspace gives such a $b$. This reproduces the coordinate-map proof and the single-coordinate transport, without requiring the numerical rank or slope formula. See `src/Formalism/LocalToGlobal/GlobalTheory/GL6/CoordMapInjective.lean:23–99`, `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/SlopeLineRamifiedFormula.lean:18–45`, and `src/Formalism/LocalRingCardinality/DataKernels.lean:146–152`.

**Remark (what “ordinary” means here).** The local condition actually proved is the vanishing of each diamond sum. Over $\mathbb C$, dividing that sum by $T-1$ gives the projector onto the invariants of that residue-unit coordinate. Its kernel is the sum of the nontrivial character spaces in that coordinate. The common kernel requires nontrivial character in every coordinate. The coefficient-place flag used in the prime record has the separate job of selecting the positive-valuation side of the split prime.

For this application, `HidaSetting` is precisely the size and weight hypothesis $2fN(m)+1<T$, $4a_{\max}<T$, the alcove inequalities $2(w_{j,\tau,a}-w_{j,\tau,b}+N(j))<T$ for all indicated weights at $j\le m$, and nonnegative $b_{\mathrm{Top}}$ at the top embeddings. The proof of the free coordinate model takes the forms and stabilizer data independently of this setting. See `src/Formalism/SharpRestriction/GlobalSchurBounds/ProductFirstZerothParts.lean:131–141`. The slope wrapper additionally takes `HidaSetting` and `ChiFin0`. The latter supplies a common positive exponent for the level character and membership of its values in the embedded coefficient field. In classical Hida terminology an ordinary part is the part selected by the unit eigenvalues of the relevant normalized $p$-adic Hecke operator. The definition of `adm26` uses the ramified lattice, the Hermitian slope comparisons and the local length bounds. An identification of these finite diamond conditions with a Hida ordinary summand requires further arithmetic input [Open]. For the invertible summand and its projector see Hida, *$p$-adic ordinary Hecke algebras for $\mathrm{GL}(2)$*, p. 1298. [Original article](https://www.numdam.org/item/AIF_1994__44_5_1289_0.pdf)

**Remark (the argument passed to the division proof).** At a point of the family the real-place second-layer hypothesis supplies $C$ and the finite-character proof for $S=C.\mathrm{forms}(u)$. The family bridge pairs them with the stabilizer hypothesis. `freeTT_holds` passes $S.\mathrm{to0}$ to `freeT_0`. `slopeLineT_holds` passes the same projection together with the pointwise `HidaSetting` and `chiFin0_to0S S hC` to `slopeLine_0`. The other branch of `level_lines_of_form_tie` supplies the length comparison. The resulting `hE : J.LvlF Fm` is the argument of `J.lemma_five_one_of_theorem_two Fm hTu hE`. Its pointwise specialization is the `h26 x e3 i` passed to `places_at_of` by `placesF_min'`. Thus it is the conditions proved *using* the forms that reach `adm26`; the record itself serves upstream. See `src/Formalism/SharpRestriction/GlobalSchurBounds/LinkTied.lean:31–67`, `src/Formalism/LocalToGlobal/Divisibility/DivisibilityRemainder/NoColumnCase/LvlWire.lean:15–43`, `src/Formalism/SharpRestriction/GlobalSchurBounds/LinkMin.lean:584–622`, and `src/Formalism/LocalToGlobal/GlobalTheory/PlacesMin.lean:101–105`.

Lean citations in this subsection refer to the pinned [Alpöge archive](../sources/SOURCES.md#a2-alpöge-lean-archive-leantargz-14-parts), joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

### 6.4.9 Why the split diamonds act freely

The inverse in §6.4.8 needs two facts about the same projected form $F=(C.\mathrm{forms}(u)).\mathrm{to0}$. First, prescribed value blocks extend from class representatives to adelic forms. The obstruction is a rational stabilizer that could impose an extra relation on a block. Second, changing a residue-unit coordinate moves the class freely. The second assertion requires a separate argument: a diamond can fix a double coset through a rational element even when the rational stabilizer of the original representative is trivial.

**Two local calculations [Expository].** In each example the two components of the integral split algebra are interchanged by conjugation. Let $Q$ be the first component reduced modulo $T$. The functional on the standard localized dual lattice in rank one is $f(x_+,x_-)=x_+\bmod T$. The examples verify the split local hypotheses at $T$. Global host and auxiliary congruences are additional inputs.

- At $T=5$, take $E=\mathbb Q(i)$ and $\pi=2+i$. The selected root is $i=3\bmod5$, so $\pi=0$ and $\bar\pi=4$ in the selected residue field. For $\alpha=2i$ one gets $\alpha^2=-4$ and $\alpha=1\bmod5$. The lift $r=11\bmod25$ has $r^2=21=-4\bmod25$, and $2r$ is a unit. In the two evaluations $\alpha\mapsto r,-r$, the expression $e=(1+\alpha/r)/2$ has components $(1,0)$. For $k=2$, the local scalar is $(1/2,2)$, or $(13,2)\bmod25$. Its norm is one and $2f(\delta x)=2\cdot3 f(x)=f(x)$ in $\mathbb F_5$. The fourth power has first coordinate $13^4=11\bmod25$, which is $1\bmod5$. It therefore fixes $f$. A diamond with multiplier $2$ itself cannot fix $f$, since $f(1,0)=1$.
- At $T=7$, use $\omega^2+\omega+1=0$ and $\pi=3+\omega$ in $\mathbb Q(\omega)$. The selected evaluation $\omega=4\bmod7$ gives $\pi=0$ and $\bar\pi=5$. Here $\alpha=1+2\omega$ has square $-3$ and residue $2$. The lift $r=37\bmod49$ satisfies $r^2=46=-3\bmod49$, and $2r$ is again a unit. The same formula gives $(1,0)$ in the evaluations at $r,-r$. For $k=3$, the scalar $(1/3,3)$ reduces to $(33,3)\bmod49$. In the quotient $3f(\delta x)=3\cdot5 f(x)=f(x)$, while $33^6=8\bmod49$ gives the identity on $Q$. The multiplier $3$ itself acts nontrivially on $f$.

**Level and stabilizer.** Write $H$ for the finite adelic unitary group, $\Gamma$ for the rational unitary group embedded in it, $U$ for the projected level subgroup, and $[y]$ for the double coset of $y$. The class space is the double quotient by $\Gamma$ on the left and $U$ on the right. The class chart gives representatives $y_c$ indexed bijectively by $c$. Its map $\mathrm{stabI}_c$ identifies the abstract stabilizer with the rational matrices in $y_c U y_c^{-1}$. At a selected place over $T$, the level condition consists of preserving the base and dual lattices, being unitary, and fixing the linear map $f_v$ from the localized dual lattice to its quotient $Q_v$ of order $T$. In particular $f_v$ is nonzero and $TQ_v=0$. At the two auxiliary type primes $g_0,g_1$, the level is described in local frames with split projections. In degree zero the rank fits in the first block, so the entire matrix reduces to an upper unitriangular matrix.

**Lemma 1 (extension from a class chart) [Lean, read].** Under the class and value chart hypotheses of $F$, the rational stabilizers vanish, and each family of allowed value blocks extends uniquely to a covariant adelic form.

*Proof.* In a type-prime frame, a matrix stabilizing the base lattice maps each integral basis vector to another integral vector. Apply the same argument to the inverse. This gives an invertible matrix over the valuation ring. The first-block conditions of $\mathrm{glev0}$ give the unitriangular reduction just described. These are the integrality and Iwahori steps of the level-zero stabilizer producer.

An integral invertible local matrix with unitriangular reduction in residue characteristic $p$ has no nonidentity torsion of order prime to $p$. Indeed its reduction lies in a finite $p$-group, so an element of order dividing an integer coprime to $p$ reduces to the identity. If $M=I+B$ and the least entry valuation of $B$ is $s>0$, the term $nB$ in $(I+B)^n-I$ has least entry valuation $s$ for $p\nmid n$, while all higher terms have valuations at least $2s$. Thus $(I+B)^n=I$ implies $B=0$. Conjugating back and using the injective composite on rational matrices transfers this criterion to rational elements.

The finiteness input is $\mathrm{finite\_stabAt\_of\_local}$ [Lean], for the totally definite nondegenerate Hermitian form and the finite spanning lattice in $F$ with its local stabilizers. For a rational element $\gamma$ in $y_c U y_c^{-1}$, all its powers are in that finite stabilizer, so $\gamma^N=1$ for some $N>0$. Write $N=g_0^a m$ with $g_0\nmid m$. Apply the local criterion at $g_0$ to $\gamma^{g_0^a}$ to obtain $\gamma^{g_0^a}=1$, and at $g_1$ to $\gamma$ to obtain $\gamma=1$. By the range and injectivity of $\mathrm{stabI}_c$, this also proves the abstract condition $\mathrm{admS}$.

Every $x\in H$ can now be written uniquely as $x=\gamma y_c\kappa$ with $\gamma\in\Gamma$ and $\kappa\in U$. Existence is surjectivity of the class chart. For uniqueness two expressions first give the same $c$, and then $\gamma_2^{-1}\gamma_1=y_c\kappa_2\kappa_1^{-1}y_c^{-1}$ is in the trivial intersection. Cancellation gives equality of the two level factors as well. Write $z$ for an archimedean frame and $\chi$ for the level character. For prescribed allowed blocks $b_c$, put $\mathcal F(\gamma y_c\kappa,z)=\chi(\kappa)b_c(\gamma^{-1}z)$.
The value space is stable under rational frame translation, the input to this step from the polynomial value chart. The formula is covariant: replacing $x$ by $\eta x\lambda$ and $z$ by $\eta z$ replaces $\gamma$ by $\eta\gamma$ and $\kappa$ by $\kappa\lambda$, so the value is multiplied by $\chi(\lambda)$. At $y_c$ the two factors are identities and the value is $b_c$. Conversely this same covariance forces the displayed formula at every point. If one replaces the chart representative by $y'_c=\gamma_0 y_c\kappa_0$, the new datum is $b'_c(z)=\chi(\kappa_0)b_c(\gamma_0^{-1}z)$. Substituting the factors $\gamma\gamma_0^{-1}$ and $\kappa_0^{-1}\kappa$ in the formula gives the original form. The extension and restriction are linear inverses, including with the change of frame labels prescribed by the chart. This is the block evaluation used in §6.4.8. $\square$

**Lemma 2 (split diamond comparison) [Lean, read].** Suppose the $\mathrm{AtTTied}$ prime record, the level and value charts of $F$, and the type-prime conditions above are supplied. For every tuple of residue units $a=(a_v)_v$, the chart dilation is induced by an adelic diamond $\delta$. Right translation by $\delta$ descends to classes. A class fixed by this translation forces every $a_v=1$.

*Proof.* Fix a selected place $v$. Put $\alpha=\pi-\bar\pi$, so $\bar\alpha=-\alpha$ and $A=\alpha^2$ belongs to the real field and is integral. Reduction at the selected prime sends $\pi$ to zero and $\bar\pi$ to a unit. Restriction of reduction to the real integers has kernel $v$ and image the entire prime field: the additive image contains $1$ in a group of prime order. Lift the nonzero residue of $\alpha$ to a real integer $b$. Then $b^2\equiv A\bmod v$ and $2b$ is a unit since $T$ is odd. The complete valuation ring lifts the simple root $b$ of $X^2-A$ to a unit $r$ with $r^2=A$. Consequently $e=(1+\alpha/r)/2$ is in the integral local tensor algebra, $e^2=e$, and $\bar e=1-e$. The simple-root version of Hensel's lemma applies to the actual real completed ring. [Stacks Project, §59.32](https://stacks.math.columbia.edu/tag/03QD)

On the additive group of $Q_v$ an idempotent has either zero image or full image, since the group has prime order. In the latter case it is the identity by idempotence. Exchange $e$ with $1-e$ in the zero case. Lift $a_v$ to an integer $k_v$ prime to $T$, so $k_v$ and its inverse are integral at $v$. The scalar $\mu_v=k_v^{-1}e+k_v(1-e)$ has inverse $\bar\mu_v$, by $e(1-e)=0$. Its scalar matrix is unitary and preserves both lattices because it and its inverse are integral. On $Q_v$ it acts by $k_v^{-1}$, so $k_v f_v(\mu_v x)=f_v(x)$. Extend the scalar matrix by the identity at all other places. The adelic extension is unitary by the local identities and has the stipulated support. The product of these extensions over the distinct selected places gives $\delta$ with local equations $f_v(\delta x)=a_v^{-1}f_v(x)$. The chart's dilation comparison identifies $[y_c\delta]$ with the chart dilation of $c$. This argument also works with any diamond witnesses satisfying the same local equations and support. Composition multiplies the residue multipliers, with reversal of the order for successive right translations written as left actions on classes. The residue group is abelian.

Conjugating an element $\kappa\in U$ by $\delta$ preserves the lattice conditions. At a selected place one has $f_v\delta^{-1}=a_v f_v$, so $f_v(\delta^{-1}\kappa\delta x)=a_v f_v(\kappa\delta x)=f_v(x)$. The other places see the identity. Applying the same functional calculation to $\delta^{-1}$ with multiplier $a_v^{-1}$ gives the converse inclusion. In the scalar construction, centrality at each place also gives this conclusion. In particular if $y'=\eta y\kappa$, then $y'\delta=\eta(y\delta)(\delta^{-1}\kappa\delta)$. Hence the action is independent of the representative of each double coset. Two witnesses for the same multipliers differ by a level element: their quotient preserves the two lattices and the functional at every selected place, and is the identity elsewhere. More generally, for a diamond, membership in $U$ is equivalent to $a_v=1$ at all selected places. The forward direction evaluates $a_v f_v(\delta x)=f_v(x)$ at an $x$ with $f_v(x)\ne0$ using that $U$ fixes $f_v$. The reverse direction follows from the local characterization of $U$.

Assume now $[y_c\delta]=[y_c]$. Write the quotient equality as $y_c=\gamma y_c\delta\kappa$ for $\gamma\in\Gamma$ and $\kappa\in U$. Put $z=\delta\kappa=y_c^{-1}\gamma^{-1}y_c$. Fermat's theorem gives $a_v^{T-1}=1$ for all $v$, so $\delta^{T-1}\in U$. For every $j\ge0$, $z^j=\delta^j\kappa_j$ with $\kappa_j\in U$: start at $\kappa_0=1$ and take $\kappa_{j+1}=(\delta^{-1}\kappa_j\delta)\kappa$. Thus $z^{T-1}\in U$ and $\gamma^{T-1}=1$ by Lemma 1.

The prime-record congruence makes $T$ distinct from each type prime $g_i$. Indeed, $\pi\equiv1$ modulo an integer divisible by $g_i$, so $\pi\bar\pi\equiv1$ modulo $g_i$ in the integer ring. If $T=g_i$, the norm equality would give $1\equiv0$. Bézout then excludes any selected place over $T$ from the places over $g_i$. At either type prime the local component of $z^j$ is therefore that of $\kappa^j$ and lies in the local level. Whenever $(\gamma^{-j})^n=1$ with $n$ prime to $g_i$, the corresponding projection of $z^j$ is trivial by the local criterion of Lemma 1, and rational injectivity gives $\gamma^{-j}=1$. Apply the two-prime factorization argument to $N=T-1$ as in Lemma 1. It follows that $\gamma=1$, hence $\delta=\kappa^{-1}\in U$. The multiplier comparison gives $a_v=1$ for every $v$, as required. $\square$

**Changing the orbit representative.** Let $G=\prod_v\mathbb F_T^\times$, and use the coordinate convention of §6.4.8, $B_q(g)=\Phi(\rho(g)\varphi)(c_q)$ for an orbit $q$ and a representative $c_q$. The actual single-place transport is an invertible linear change on the allowed value block, by the $\mathrm{rhoT\_dil}$ comparison; their compositions give the same statement for a tuple. Concretely, write $\Phi(\rho(h)\varphi)(c)=L_{h,c}\Phi(\varphi)(hc)$. The block map is invertible: the transport fixes the zero condition in each direction by applying the comparison for $h^{-1}$ and using the representation law. Since arbitrary allowed blocks occur by Lemma 1, the maps for $h$ and $h^{-1}$ are inverse at the respective points. If $c'_q=hc_q$, the new coordinates satisfy $B'_q(g)=L_{h,c_q}^{-1}B_q(hg)$. Freeness makes $h$ unique. The shift permutes each one-coordinate summation fibre onto another such fibre and the fixed invertible block map carries zero to zero. Thus the joint zero-sum condition is unchanged, and applying the inverse construction in the new coordinates gives the same $\varphi$. Holding the numerical coordinates fixed while changing representatives would in general change the form. This is a change of coordinates on the finite-orbit model already proved in §6.4.8.

**Symmetric projection and comparison in both directions [Lean, read].** The producer packages $C.\mathrm{forms}(u)$ as the symmetric record. In $\mathrm{FormsTiedSym.to0}$ the class and value charts, residue record and auxiliary frames in the two lemmas are exactly its fields at the left endpoint, with the equality $0=0$ supplying the endpoint alternative. Restriction and extension in Lemma 1 then go in both directions on the projected value space. The inverse on forms uses $F$ and retains the same representative and value labels. The round trip concerns the endpoint value data with the symmetric witness held fixed.

There is also a record-level comparison in the production chain. With the supplied symmetric witness $C$, the group-compatible forms satisfy $g.\mathrm{forms}(u)=(C.\mathrm{forms}(u)).\mathrm{to0}$. In the actual true-column construction, `exists_trueVolume_stage_of_any_column_choice` passes the projected family and `C.joint0` to `exists_isLocalFamily`. On reconstruction, `isRecG_of_isLocalFamily` uses the projected family after the local group update as its internal `T'` and returns the group form equality by reflexivity. The caller composes this equality with the reversed `forms0Re_setGat` and `columnFormsAlongLaterStages_stageZero_eq` identities, then uses function extensionality to obtain the symmetric projection equality for the new stage. Each identity reduces to the same endpoint fields under the indicated record update. In the other direction, `hServTwoSidesJoint0` substitutes the Hermitian and form equalities, uses the full-column compatibility on the base level, and reads `C.joint0 u`. The assembly $\mathrm{tiedDataS\_assemble}$ keeps the equality while storing both $g$ and $C$. Under the divisor replacement $\mathrm{setDiv}$ in $\mathrm{colTTr}$, applying $\mathrm{forms0S}$ to the equality gives the transported equality of level-zero forms. Indeed projecting the transported symmetric record and transporting the old projection reduce field by field to the same record, which is the reflexivity proof $\mathrm{colsRe\_to0S}$. Composing with this equality in reverse gives the required $\mathrm{forms\_eq}$ for the new column. At the endpoint $\mathrm{ColsTiedSym.joint0}$ reads $C.\mathrm{car0}(u)$ directly. These are the precise senses in which the symmetric and level-zero descriptions can be used interchangeably.

**Where the proof is consumed.** In $\mathrm{freeT\_tied}(F)$ the pointwise call to $\mathrm{admissible\_stabilisers\_of\_compatible\_forms}(F)$ supplies Lemma 1, and $\mathrm{splitAtT\_of\_tied}(F.\mathrm{atT})$ supplies the idempotent for Lemma 2. The resulting split comparison feeds $\mathrm{free\_rank\_model\_of\_diamonds}$ and hence $\mathrm{freeT\_0}(F)$. The parallel slope call uses the same $F$, adds $\mathrm{HidaSetting}$ and the transported $\mathrm{ChiFin0}$, and additionally draws on the metric and isometry supplies of §6.4.8.

The family route also supplies its own stabilizer evidence. From the scale threshold for the real-place layer and the one from $\mathrm{stabF}$, $\mathrm{family\_conditions\_of\_layer\_two}$ takes their maximum and packages $(C.\mathrm{forms}(u),h_C(u))$ with the appropriate family stabilizer witness at $(x,i,u)$. This family witness is obtained via $\mathrm{stabiliser\_family\_of\_column\_lemma}$ with the column conclusions and level-at-type-primes supply. It is distinct from the proof of pointwise admissibility reconstructed in Lemma 1. In $\mathrm{lvlF\_of\_ties}$ the freedom and slope branches use the same symmetric $\mathrm{to0}$, and the length branch adds its own supplied comparison. The two entries $(h_E(x,e_2,i)).1$ and $(h_E(x,e_2,i)).2$ reach $\mathrm{division\_rank\_slopes\_of\_lines}$ through $\mathrm{lemma\_five\_one\_of\_theorem\_two}(F_m,h_{Tu},h_E)$. This last family is the $h_{26}$ argument of $\mathrm{placesF\_min'}$, evaluated there as $h_{26}(x,e_3,i)$. The proof uses the conditions derived from the projected form at that word and scale.

**Reading boundary.** The chapter uses the pinned joined archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The main pointwise proofs are `src/Formalism/LocalToGlobal/GlobalTheory/GL6/ValuationClassTranslateMem.lean:28–125`, `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/AdmissibleStabilisersOfCompatibleForms.lean:19–195`, `src/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/GenCoprime.lean:63–124`, `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/PSplitT.lean:276–330`, `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/LocalDiamondOfSplitIdempotent.lean:14–198`, and `src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/EqOneOfCoprimeTorsionTwoPrimes.lean:571–620,630–637,670–698`. The symmetric projection and divisor comparison are `src/Formalism/LocalToGlobal/GroupLattices/Joint0.lean:13–30` and `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ColsReTo0S.lean:21–30,63–90`.

The deeper [Lean] inputs include `finite_stabAt_of_local`, `complex_span_block_action_stable`, `formsTiedSym_std`'s underlying chart constructions, and the recursive comparisons `Test.comparison_statements` and `groupCompatibilityOfRecursion`. On the family side, the inputs include `UnusedSlot33.field_lemmas_except_seven`, `GenusMassVolumes.levels_pro_g`, the deeper proof of `flipTwoThree.stabiliser_family_of_definite`, and the metric, isometry and length inputs `metric_disjoint_support_orthogonal`, `diamond_isometry_at_infinity` and `second_branch_all_members`. The Hida ordinary identification remains [Open]. Hida's ordinary and nearly ordinary projectors arise from the invertible summand of a specified Hecke operator with topologically nilpotent complementary action. The finite diamond comparison above concerns the actions of residue units. [Hida, 1994, p. 1298](https://www.numdam.org/articles/10.5802/aif.1434/)

### 6.4.10 Local torsion and the finite rational stabilizer

A rational element fixing a level-zero class has an adelic conjugate in the level subgroup. Its local components therefore preserve lattices, and its images in the two type-prime frames reduce to upper unitriangular matrices. The lattice conditions and archimedean definiteness give finite order. The two reduction tests then force that order to be one. At a single place a stronger torsion statement is available when all entries are sufficiently close to the identity.

**Two calculations [Expository].** At the odd prime $5$, take $K=\mathbb Q_5$, $B=\begin{pmatrix}5&5\\0&0\end{pmatrix}$, and $A=1+B$. Its determinant is the unit $6$. It is the identity modulo $5$ and differs from it modulo $25$. Since $B^2=5B$, we have $A^5-1=((6^5-1)/5)B=1555B$. From $1555=5\cdot311$, the upper left entry has valuation two. Here $e=1$ and the depth one satisfies $1>1/(5-1)$. This completion occurs as a split factor in the CM model $\mathbb Q(i)/\mathbb Q$: the simple root $i=2\bmod 5$ lifts, and conjugation interchanges the two factors. In the standard Hermitian lattice the pair $(A,(A^{-1})^{\mathsf T})$ is integral and unitary. Thus the first projection in the standard frame is a legal local unitriangular model.

At equality, take $K=\mathbb Q_3(\zeta)$ with $\zeta^2+\zeta+1=0$ and set $\pi=\zeta-1$. Its equation $\pi^2+3\pi+3=0$ is Eisenstein at $3$, so $\pi$ is a uniformizer and $v(3)=2$. The scalar $\zeta=1+\pi$ has exact order $3$ and depth one, with $(3-1)\cdot1=2$. In $(1+\pi)^3-1$, both $3\pi$ and $\pi^3$ have valuation three, while $3\pi^2$ has valuation four. Multiplying $\pi^2=-3(1+\pi)$ by $\pi$ shows that the three terms sum to zero. These calculations concern local fields and frames. The global proof below supplies the finite stabilizer at the given adelic point.

**Definitions.** Let $K/\mathbb Q_p$ be finite, with ring of integers $R$, uniformizer $\pi$, and valuation $v(\pi)=1$. The residue characteristic is $p$, the absolute ramification index is $e=v(p)$, and the principal group of depth $r\ge1$ is $P_r=1+\pi^r M_n(R)$, the kernel of reduction modulo $\pi^r$. Let $I^+$ be the preimage in $\mathrm{GL}_n(R)$ of the upper unitriangular group over $R/\pi R$. Embedded in $\mathrm{GL}_n(K)$ this is the archive's iwU. The rational type prime $g$ below a finite place of the base field gives $p=g$ in that completion. The place determines $e$, which can vary among places above $g$. Congruence modulo $p^b$ corresponds to principal depth $eb$.

**Lemma 1 (local torsion).** The finite-order elements of $I^+$ have $p$-power order [Lean, read]. The principal group $P_r$ is torsion-free if $(p-1)r>e$. The depth assertion is the matrix counterpart of the classical bound for scalar principal units. [Rong Zhou, notes by Leonard Tomczak, *Local Fields*, §6.3, Proposition 6.14, pp. 28–29](https://math.berkeley.edu/~ltomczak/notes/Mich2022/LF_Notes.pdf)

*Proof.* Suppose $A\in I^+$ satisfies $A^N=1$ with $p\nmid N$. Its reduction is $1+X$ for a strictly upper triangular $X$ satisfying $X^n=0$. Choose $s$ with $p^s\ge n$. In characteristic $p$ we have $(1+X)^{p^s}=1+X^{p^s}=1$, so $C=A^{p^s}$ belongs to $P_1$. If $C=1+Y\in P_j$ for $j\ge1$, then $Y^2=0$ modulo $\pi^{j+1}$ and $C^N=1$ gives $NY=0$ there. As $N$ is a unit, $C\in P_{j+1}$. Separation of the filtration gives $C=1$. Bézout applied to $p^s$ and $N$ then gives $A=1$. If the order of $A$ is $p^a m$ with $p\nmid m$, the same argument applied to $A^{p^a}$ gives $m=1$.

In $P_r$ it now suffices to exclude elements of order $p$: a nontrivial element of $p$-power order has a power of order $p$. Write $C=1+Y\ne1$ and put $t=\min_{i,j}v(Y_{ij})\ge r$, with zero entries given valuation infinity. In $C^p-1$ the term $pY$ has least entry valuation $e+t$. For $2\le j<p$, all entries of $\binom pjY^j$ have valuations at least $e+jt>e+t$. Those of $Y^p$ have valuations at least $pt>e+t$, since $(p-1)t\ge(p-1)r>e$. At an entry of least valuation of $Y$, the term $pY$ therefore survives and $C^p\ne1$. This proves the strict depth bound. $\square$

The sufficient integer depth is $\lfloor e/(p-1)\rfloor+1$. The equality example shows why a uniform statement requires a strict inequality. A unitriangular reduction can have a nonzero strictly upper triangular part, so even at an unramified odd prime, principal depth one requires an additional membership test. For example over $\mathbb Q_3$ the matrix $\begin{pmatrix}0&-1\\1&-1\end{pmatrix}$ has order three by its quadratic equation. In the ordered integral basis $(1,-1),(1,0)$ its reduction is $\begin{pmatrix}1&-1\\0&1\end{pmatrix}$. Thus in that frame it belongs to $I^+$ and has nonidentity reduction.

**Lemma 2 (finiteness from local lattices) [Lean, read].** Let $E/F$ be the CM extension, $J$ a nondegenerate Hermitian form on $E^n$ definite at every real place, and $\Lambda\subset E^n$ a finitely generated spanning $\mathcal O_E$-lattice. Set $\mathcal A=E\otimes_F\mathbb A_{F,f}$. At each finite place $v$ let $S_v$ be the subring of $E\otimes_F F_v$ generated by the images of $\mathcal O_E$ and $\mathcal O_v$, and let $\Lambda_v$ be the $S_v$-span of $\Lambda$. Suppose the projection of a subgroup $U\le\mathrm{GL}_n(\mathcal A)$ at each $v$ preserves $\Lambda_v$. For every finite adelic unitary point $x$, the rational unitary matrices $\gamma$ with $x^{-1}\gamma x\in U$ form a finite group. In expressions in $\mathcal A$, rational matrices are embedded diagonally.

*Proof.* Write $S$ for the subring of $\mathcal A$ generated by $\mathcal O_E$ and the integral finite adeles of $F$. Let $L\subset\mathcal A^n$ consist of vectors whose projection at each $v$ lies in $\Lambda_v$. Projection commutes with multiplication, so $U$ preserves $L$. Choose positive integers $a,b$ with $a\mathcal O_E^n\subset\Lambda\subset b^{-1}\mathcal O_E^n$. For the lower bound, clear denominators in expressions of the coordinate vectors as $E$-linear combinations from $\Lambda$. For the upper bound, clear the coordinates of finitely many generators. Extension gives $aS_v^n\subset\Lambda_v\subset b^{-1}S_v^n$.

Choose an $F$-basis $b_i$ consisting of algebraic integers and write $b_i^\vee$ for its trace dual. The trace of an element of $S_v$ lies in $\mathcal O_v$ because $S_v$ is the $\mathcal O_v$-span of the image of $\mathcal O_E$ and traces of algebraic integers are integral. Therefore if $z\in\mathcal A$ projects to $S_v$ everywhere, the scalar-extended trace of $b_i z$ is an integral finite adele for each $i$. The trace expansion is $z=\sum_i b_i^\vee\otimes \operatorname{Tr}_{E/F}(b_i z)$. A single positive integer $d$ clears the denominators of all $b_i^\vee$, so $dz\in S$. Applied coordinatewise, this gives $aS^n\subset L\subset (bd)^{-1}S^n$.

Now intersect $xL$ with the diagonal $E^n$ to obtain $\Lambda_x$. Choose an integer $D>0$ clearing all entries of $x$ and $x^{-1}$ into $S$. Such a $D$ exists by expanding in the integral basis over $F$ and clearing the finitely many denominators of the finite adelic coefficients. The two bounds for $L$ give $aD\mathcal O_E^n\subset\Lambda_x$ and $bdD\Lambda_x\subset S^n\cap E^n$. Rational elements of $S$ have integral trace pairings with the $b_i$ at every finite place, hence in $\mathcal O_F$. Thus $bdD\Lambda_x$ lies in the $n$-fold direct sum of $\sum_i\mathcal O_F b_i^\vee$, a finitely generated $\mathbb Z$-module. This exhibits $\Lambda_x$ as a finitely generated spanning $\mathcal O_E$-lattice.

Each stabilizer element preserves $\Lambda_x$ because its conjugate by $x^{-1}$ and the inverse of that conjugate preserve $L$. For each complex embedding of $E$, change the sign of the embedded form if needed to make it positive definite. The images $\gamma(aD e_j)$ have prescribed norms equal to those of $aD e_j$ and are bounded at every archimedean embedding. They belong to the discrete fractional lattice just constructed, so there are finitely many possible images of each basis vector. These images determine $\gamma$. The archive counts bounded integral multiples of entries of $J\gamma$, using Hermitian Cauchy–Schwarz for the archimedean bounds. [Brian Conrad, *A lattice in the adele ring*, p. 1](https://math.stanford.edu/~conrad/154Page/handouts/adelelattice.pdf) $\square$

**Proposition (the degree-zero rational stabilizer) [Lean, read].** In Lemma 2 suppose $g_0\ne g_1$ are rational primes and for each $i$ a place $v_i$ above $g_i$, a unital ring map $\rho_i:E\otimes_F F_{v_i}\to F_{v_i}$, and a frame $h_i$ are supplied. Suppose the image of $U$ under local projection, $\rho_i$ and conjugation by $h_i^{-1}$ lies in $I^+$ for each $i$. Then the rational stabilizer of Lemma 2 is trivial.

*Proof.* The composite $E\to E\otimes_F F_{v_i}\to F_{v_i}$ is an injective field map. Projecting a stabilizer element and applying the two conjugations preserves any equation $\gamma^N=1$. If $g_i\nmid N$, Lemma 1 kills the resulting matrix. Undo the conjugations and use injectivity entrywise to recover $\gamma=1$. For an arbitrary stabilizer element, Lemma 2 gives an exponent $N>0$ by repetition of powers. Write $N=g_0^a m$ with $g_0\nmid m$. The first test applied to $\gamma^{g_0^a}$ with exponent $m$ gives $\gamma^{g_0^a}=1$. The second test applied to $\gamma$ with exponent $g_0^a$ gives $\gamma=1$. A one-place variant would require both principal membership above the bound and the finite-order input. $\square$

**Remark (actual arguments).** For the projected form $T_f$ of type `Forms0` at $(D,u)$, `adms_core` sets $S=(T_f.\mathrm{cls}(0,\ldots)).\mathrm{lev}$ and passes to `gen_triv` its lattice `S.Lb` with `Lb_fin` and `Lb_span`, and its subgroup S.U. The local preservation hypothesis is obtained from `S.U_eq` followed by S.Uloc_lev. The two primes are `D.host.g` with `g_prime` and `g_ne`, the places are chosen above them, and the projections and frames are `Tf.gl.phi` and Tf.glev0.fr. The proof of `adms_iwU` uses the lattice basis for integrality of the matrix and its inverse and the first-block rank inequality for unitriangular reduction. These are the exact frame hypotheses used by `gen_coprime`, which invokes `iwU_coprime` on the projected conjugate. In `gen_triv` the finite type comes from `finite_stabAt_of_local` at the same point $x$. In that declaration `latLoc` supplies $L$, and the nonzero scalars passed to `adelstab_core` are the lower denominator m₁ and the upper clearing factor d times m₂. See ``src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/AdmissibleStabilisersOfCompatibleForms.lean:113–127,141–168`` and ``src/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/GenCoprime.lean:15–55,63–124``.

For a class $c$, `adms_triv` takes $x=(T_f.\mathrm{cls}(0,\ldots)).y(c)$ and rewrites membership in $xUx^{-1}$ into the hypothesis of adms_core. The range and injectivity of `stabI` transfer the identity to the original abstract stabilizer in `admissible_stabilisers_of_compatible_forms`, giving the pointwise `admS` consumed in §6.4.9. See ``src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/AdmissibleStabilisersOfCompatibleForms.lean:172–195``. The pointwise wrappers `freeT_tied` and `slopeLine_tied` pass precisely this proof to `freeT_of_tied` and `slopeLine_of_tied`, respectively. The family calls discussed in §6.4.9 instead supply their stabilizer argument through the family hypothesis. See ``src/Formalism/LocalToGlobal/GlobalTheory/GL6/DiagonalSlopes/SlopeLineRamifiedFormula.lean:44–57,67–69``. The family-level `stabF` remains a supplied [Lean] input. Identification with Hida's ordinary projector remains [Open].

The source is the pinned [Alpöge archive](../sources/SOURCES.md#a2-alpöge-lean-archive-leantargz-14-parts), joined SHA-256 9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc. The declaration ranges are in the subsection's source map.

### 6.4.11 Level-zero stabilizers in a family

A column valuation needs one symmetric column record covering every word, together with trivial stabilizers. For a local slope calculation, one word at a time suffices. The family proof supplies the first stabilizer assertion using the levels of the actual scale family. When an individual record is updated, the columns and recursive comparison must also remain tied. That compatibility comes from carrying the chosen data and their equations through the update.

**Two calculations [Expository].** Use the same rational vector space $\mathbb Q^2$ in two stages $Z_0,Z_1$. Over each stage consider divisor lattices $2\mathbb Ze_1+\mathbb Ze_2$ and $6\mathbb Ze_1+\mathbb Ze_2$, with heights $1$ and $2$. They differ since $2e_1$ belongs only to the first. Let two words have projected columns $v_1=(1,2)$ and $v_2=(3,-1)$. Take the comparison $A(a,b)=(a+b,b)$.

1. Transport the column record at every update by retaining its projected components. Both paths around each projection square give $((1,2),(3,-1))$. On the comparison side, comparing and then transporting gives $((3,2),(2,-1))$. Transporting and then comparing gives $((1+2,2),(3-1,-1))$, the same pair. These computations apply in both stages at both divisors.
2. Suppose each word allows either sign of its column. Retain the positive choices at three corners but choose $-v_1,v_2$ at $(Z_1,6\mathbb Ze_1+\mathbb Ze_2)$. Every corner has allowed columns and an invertible comparison. Along the transported path from the first divisor at $Z_1$ the first column is $(1,2)$ and its comparison is $(3,2)$. Projecting the independently chosen record at the second divisor gives $(-1,-2)$ and comparison $(-3,-2)$. The differences $(2,4)$ and $(6,4)$ show exactly which equations fail. This models pointwise existence without compatibility.

#### The family stabilizer supply

**Definition.** Write $D_{xi}=\mathrm{Fm.D}(x,i)$, $L_{xi}=\mathrm{Fm.L}(x,i)$, and $\Gamma_{u,c}$ for the abstract level-zero stabilizer of the class $c$ at word $u$ of $D_{xi}$. The consumed assertion `flipTwoThree.admF3` is
$\exists b\ \forall x\ge b,\ x_1<x\ \Longrightarrow\ \forall i\in I_x\ \forall u\ \forall c\in C_u(0),\ \mathrm{Subsingleton}(\Gamma_{u,c})$.
The fixed-word assertion `admS` retains the quantifier over $c$. The group identity belongs to each stabilizer, so being a subsingleton gives triviality.

**Lemma (the supply used by the family consumer) [Lean, read].** From the archive's definite grade-zero Gram data, its pro-$g$ levels and definite finite-order input, `stabF` gives `admF3` with $b=3$.

**Proof.** `stabF` takes the uniform constant $C_5$ from `field_lemmas_except_seven` before introducing $x,i$. At the member and its scale, it inserts `division_rational_lattice` as the omitted seventh slot of `UnusedSlot33.ConclusionOnFamily Fm 100 C₅`. Only that slot is used here. At $x\ge3$ and $x_1<x$, the level is the actual $(\mathrm{Fm.ex}(x,h,i)).\mathrm{lev}$. Its level subgroups are pro-$g_j$ at the relevant places above each auxiliary prime $g_j$, by `levels_pro_g` and the supplied split Iwahori charts. The Gram matrix is definite by the grade-zero signature supply. Using the scale equality $L_{xi}.\mathrm{sc}.x=x$, `gBig_fam` applies `gBig_of`. In that proof, $b_{\mathrm{sc}}\ge2$, $f\le k$, $k\ge3$ and $(kb_{\mathrm{sc}})^8\le g_0$ imply $2fk+1<4k^2\le(kb_{\mathrm{sc}})^2\le(kb_{\mathrm{sc}})^8\le g_0$. This gives `GBig` with index $0$ and the strict bound $2fk<g_0-1$.

Fix $u,c$. Let $J$ be the grade-zero Hermitian matrix over $E$, $U$ the compact open unitary level and $y$ the adelic representative of $c$. The involution agrees with host conjugation by injectivity of the distinguished complex embedding, applied to their equal conjugate images. Choose a finite place $v$ above the prime $g=g_0$ by lying over. An element of the rational intersection is the diagonal image of a rational unitary $\gamma$, and also equals $y a y^{-1}$ for $a\in U$. By the definite finite-order supply, $\gamma$ has finite order $n$. Localizing the two expressions gives the diagonal image of $\gamma$ in $E\otimes_F F_v$ and the conjugate of the local image of $a$. Diagonal base change is injective, and localization is a homomorphism. Thus the local image of $a$ has exact order $n$.

That image lies in the compact pro-$g$ level. Choose an open normal subgroup inside the complement of the finite set of nonidentity powers of the local element. Its cyclic subgroup injects into the quotient, which has order a power of $g$. Consequently $n=g^m$ for some $m$. Apply `hostStab` to the rational cyclic subgroup generated by $\gamma$, whose elements all have order dividing $g^m$. In its proof, if an element has order $g^s$ for $s>0$, raising to $g^{s-1}$ gives a nonidentity matrix of order $g$. The supplied host dimension inequality would give $g-1\le4\,\mathrm{ord}\, k=2fk$, contrary to the bound above. This proves the rational intersection equality with the trivial subgroup. For the topology underlying the open normal subgroup argument, see the compact totally disconnected characterization of profinite spaces. [Stacks Project, §5.22](https://stacks.math.columbia.edu/tag/08ZW)

By `stabI_range` the rational image of each abstract stabilizer element has its diagonal image in this intersection. For two such elements their diagonal images are equal to $1$. Injectivity of diagonal base change equates the rational matrices, and `stabI_inj` equates the original elements. This proves `adm3` at $(x,i)$ and gives `admS` by evaluation at $u$. The cutoff $3$ was fixed before $x,i,u,c$. The two-prime proof of §6.4.10 is used through the pointwise wrappers described below. $\square$

#### Compatibility on the fixed base and columns

**Definition.** Fix a column choice $w$, including its base $B$ and column record. Write $D_Z=w.D(Z)$ for $Z=(W,V,S,N,G)$ over those data. For symmetric columns $C$, put $F_C(u)=(C.\mathrm{forms}(u)).\mathrm{to0}$ and $L_0=C.\mathrm{herm}.\mathrm{base}.\mathrm{lev0}$. We use the projection and the `Joint0` readback of §6.4.9. A local family for $(D_Z,L_0,F_C,g)$ carries identifications $I$, away-level characters $\psi$, and embeddings $i_K,\lambda$ indexed by word $u$, coefficient place $w'$ and prime-index witness $h_g$. There is one rational basis matrix $A$ (called `B` in the Lean comparison) with the standard basis property. For every such triple and host place $v$ over the residue prime, and every proof of that condition, the local frame of $I$ equals the first split projection of the base change of $A$. For every triple and coefficient $z$, $i_K(\mathrm{embRec}(z))=\mathrm{lamV}(\lambda)(\mathrm{embLL}(z))$. Place positivity is required for the same embeddings. Each $\psi$ satisfies `PsiTied` for $L_0,F_C$, and the Galois-at-place family has the equality $g=\mathrm{gatOf}(D_Z,L_0,I,\psi,\mathrm{sc})$. The dimension witness $h_d$ compares each $g(u,w',h_g).d$ to the dimension of the fixed level-zero space.

The recursive comparison `IsRecG` gives a source $D_0$ and witnesses $L_c,I,\psi,h_d,H_0,h_L,T,A,h_{As},h_A,i_K,\lambda,h_K,h_{\rm pos},CH$. It requires $h_L(u):H_0.\mathrm{lev0}(u)=L_c(u)$ and a dependent tuple equality
$(D,G_t,c,H,F)=(\mathrm{recC},\mathrm{gatTiesC},\mathrm{latCmpC},H_0,T)$.
The right side uses the same source and witnesses, scale $\mathrm{sc}$ and recursion parameter $1$. The comparison $\mathrm{latCmpC}$ uses $CH$ completed with `pos_C`. Here $c$ denotes the comparison data. The output of `isRecG_of_isLocalFamily` includes a further ideal test. For every $u,w',h_g$, every local component $v$, every subindex $s$ at $v$ and every $z\in\mathcal O_F$, membership of $z$ in the prime ideal read from the Hermitian witness is equivalent to positive valuation at $w'$ of $\tau_{\rm LL}$ applied to the image of $z$ in $E$, with embedding index $G_t.\mathrm{gat\_pos}(u,w',h_g,v,s)$.

**Theorem (conditional family compatibility) [Lean, read].** Given the archive's standard-column, local comparison, volume and omega supplies for a fixed column choice, the construction chooses one updated Galois stage before quantifying over all admissible $(W,V,S,N)$, with a tied recursive column package at each such later stage. Given a tied package, any typed divisor update transports its recursive comparison and its Hermitian and whole-word form equalities. Projection commutes with this update. For a scale family with `RealPlaceSecondLayerConditions`, the stabilizer lemma and these column inputs supply the three conclusions of `family_conditions_of_layer_two` at the cutoffs below.

**Proof.** Take one base $Z_0$, its standard columns $C$ and the standard column and level witnesses. From the standard Hermitian data, companion, `Joint0` and rational level-zero character supply, `exists_isLocalFamily` takes `placeId`, `awayChar`, `stdBasis`, `embK` and `embAlg` for the displayed local witnesses. The frame and $g$ equations are reflexive for these choices. The character compatibility comes from the existence proof for the selected character. Insert the resulting $g,h_d$ into the true-volume Galois stage of $Z_0$ before letting $W,V,S,N$ vary. At any target stage $Z'$ carry the same $C$ by `colsRe`. Its projection satisfies $F_{\mathrm{colsRe}(Z',C)}(u)=\mathrm{forms0Re}(Z',F_C(u))$ by reflexivity. The local family proof at its transported type uses the original proof with the same $g$ and level. Function extensionality on the projection equality rewrites its forms argument. The true-volume supply gives the volume tie and the omega supply uses the same $\delta$.

In the Galois update $D'=\mathrm{setGat}(D,g,h_d)$, the recursive construction uses $H_0$ with level $L_0$ and $T(u)=\mathrm{forms0Set}(D,g,h_d,F_C(u))$. The comparison theorem supplies $CH$, the positivity tests and the group comparison. This gives a group package $G$ with $G.\mathrm{herm}.\mathrm{lev0}(u)=L_0(u)$ and $G.\mathrm{forms}(u)=T(u)$ by reflexivity, along with the ideal test. For each word, append the inverse of `forms0Re_setGat` to the latter equality, then the inverse of `columnFormsAlongLaterStages_stageZero_eq`. Function extensionality gives the equality with the full projected word family of the updated columns. Function extensionality also collects the level equalities. At the common level choose the symmetric group witness heterogeneously equal to $G.\mathrm{herm}.g$. The full Hermitian lift supplies a column equality and a heterogeneous equality to that chosen witness. Apply the level projection to the column equality and compose with the inverse of the level equality for $G$. Compose the heterogeneous equalities, substitute the identified levels, and obtain $G.\mathrm{herm}=\mathrm{Full}.\mathrm{to0}$. The same equalities let the ideal test be read on the full witness. Substituting the recursive tuple equality also gives both numerical equations in `gatNum_of_isRecG`. The existential packages at the later stages use transported seed data, with the initial choice of $g$ outside the later-stage quantifier.

For a divisor update $(N_{\rm new},h_{\rm new})$, let $C'$ be the updated columns. Expanding `colsRe` applies `formsRe` at each word. Projection reads `atT`, the grade-zero class and value data, and the grade-zero level data. On the other path `forms0S` copies exactly these entries, with `atTTS` on the level-prime component. The remaining fields reduce to the same terms. Hence $F_{C'}(u)=\mathrm{forms0S}(F_C(u))$ by `colsRe_to0S`. If $e_F$ is the old equality $G.\mathrm{forms}=F_C$, apply the wordwise operation $\mathrm{forms0S}$ to $e_F$. This equates the forms of the transported group with $u\mapsto\mathrm{forms0S}(F_C(u))$. Compose with function extensionality on the inverse component equality. The result equates the transported group's forms with $F_{C'}$ for every word. This proves the divisor projection square for the tied package. On the Hermitian side compose `fullS_cols` with `hermRe` applied to the old column equality, and compose `herm0S` applied to the old group-to-projection equality with the inverse of $(\mathrm{fullS}(X)).\mathrm{to0}=\mathrm{herm0S}(X.\mathrm{to0})$. These are the full-column, Hermitian and form equalities in `colTTr`.

For the recursive comparison square, substitute the old dependent tuple equality. Update its source by `setDiv` and carry $H_0,T$ by `herm0S` and `forms0S`. The level and local inputs $L_c,I,\psi,h_d,A,i_K,\lambda$ are reused in their updated types. Their level, basis, frame, embedding and positivity proofs are retained. The primitive comparison hypothesis keeps existence, evaluation injectivity, point existence, point universality, character and lattice membership. The completed comparison copies existence, uniqueness, positivity, character, linearity and lattice membership. With these same witnesses, `latCmpC_setDiv` identifies comparison followed by `cmpTr` with comparison of the transported inputs by reflexivity. Replacing the comparison component gives `sigma_setDiv`, the equality of the dependent tuples. Compose it with reflexivity for the rest of the updated recursive record. This constructs the new `IsRecG` equality, so `columnLocalDataTransportDivision` attaches the updated recursive proof to `colTTr` and keeps the omega witness. In the surrounding `witMv_of_positionMv` the kernel equality is transported by applying the tuple operation to the old equality, and the error equality by rewriting with the old error equality and then reflexivity.

In these updates the fixed base and columns identify the class and stabilizer types and their indexing words. In particular, the divisor update changes the lattice and height in the divisor record and recalculates its height bound. The class type and its stabilizer come from the separate word membership record. For any two members of the updated stabilizer, the old subsingleton proof applies in that same type. The recursive equations use the actual fixed levels and comparisons in addition to the common host. Equality of fields alone supplies no identification of those data. For a second divisor update apply the same square with the first updated package as input.

Finally take the scale family. The hypothesis has order $\exists a\ \forall x\ge a\ \forall i\in I_x$, real compatibility and $\exists C_{xi}\ \forall u,\ \mathrm{ChiFin0}(C_{xi}.\mathrm{forms}(u))$. A supplied tied-record selection $s$ with threshold $s_0$ and character threshold $a_\chi$ yields this hypothesis at $a=\max(\max(a_\chi,s_0),x_1+1)$, by reading real data and columns from the same selected record before applying the character proof at each word. The volume family follows at $a$ by `volTie_of_realTied` with the strict scale guard. For `tCVTies` take $\max(\max(a,b),x_1+1)$. This ensures $x_1<x$ and both cutoff inequalities, so pair the inhabitation by $C_{xi}$ with `adm3`. For `FamU ConcreteFormsLevelZero` take $\max(a,b)$ and retain the strict guard. Under the requested setting at $u$, return the chart type and class map, $C_{xi}.\mathrm{forms}(u)$ and its character witness, and `admS` by evaluating `adm3` at $u$. This construction uses no operation on the setting proof. The threshold is uniform over $x,i$, while a column witness is taken at $(x,i)$ and serves every word there. The common base and host in the transport are those of the chosen column record. $\square$

#### The actual level-prime input in `adm26`

**[Lean, read]** `LvlWire.lvlF_of_ties` takes the third conjunct of `family_conditions_of_layer_two`. `level_lines_of_form_tie` uses `slope_free_branch_family` with `freeTT_holds`, `slopeLineT_holds` and `LemB.second_branch_all_members`. The first two wrappers discard the supplied stabilizer conjunct. They project the symmetric witness and call the pointwise free action and slope results, with the character projection on the slope side. The first two branch outputs give the transposed slope conditions. The third is combined with integral base-point data and the ramified Hecke level-zero result for the no-kernel length bound. With the eventual setting from `TuSize`, `lvlF_of` evaluates both implications at every word to produce $h_E:\mathrm{J.LvlF}$.

In `lemma_five_one_of_theorem_two` the cutoff is the maximum of the numerical-weight, `TuSize`, $h_E$ and eventual $4\le x^{2/5}$ thresholds and the cutoffs $4$ and $x_1+1$. The equality of scales allows the chain-length estimate to give $4\le m$. The first two proof arguments to `division_rank_slopes_of_lines` after $D,L,9$ are $(h_E(x,e_2,i)).1$ and $(h_E(x,e_2,i)).2$, the all-word rank-line and length inputs. The remaining arguments supply the member's $\nu$ definition, `lat.atT`, local span, lengths at the level prime, fifth-level weights, the all-word setting and $0\le9$. The result gives the ramified rank identity, the mean-slope identity and maximum-slope bound, localized inclusion in $M_{\rm ram}$, and the normalized sum of lengths at places of residue characteristic $T_u$. It supplies `LocalQuadraticParts.LevelTFamily` with constant $4\cdot9$. In the division remainder bound, the caller passes the actual $h_E$ from the real place tie to `hh_of_lvl`. Its slope branch passes the level-prime family to `Places.placesF_min'`, which unpacks $(C_{26},x_{26},h_{26})$, obtains $e_3:x_{26}\le x$ and actually passes $h_{26}(x,e_3,i)$ to `places_at_of` between the rank and mean-slope proofs.

**Scope.** The host lattice, metric, pro-$g$ charts, standard-column existence and arithmetic comparison theorem supply the inputs used here. The pointwise finite stabilizers, two-prime torsion elimination, split diamond and projection round trip are as in §§6.4.8–6.4.10. The finite diamond kernel's identification with a Hida ordinary part remains [Open]. Hida's projector uses invertibility on one summand and topological nilpotence on the other, with the nearly ordinary and ordinary operators distinguished on the same page. [Hida 1994, p. 1298](https://www.numdam.org/item/AIF_1994__44_5_1289_0.pdf)

**Archive references.** See `src/Formalism/SharpRestriction/GlobalSchurBounds/LinkTied.lean:24–29,51–67`, `JointsL.lean:1098–1113,1144–1146,1169–1172` and `JointsF.lean:125–132` in the same directory, and `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConcreteSplitPrimeAutomorphicDataDivisionLattice.lean:17–79` and `ColsReTo0S.lean:21–90` in its directory. Archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. [Alpöge's archive index](https://alpo.ge/)

### 6.4.12 Rational finite order on a fixed host

A level condition at one auxiliary prime can force a finite-order element to have prime-power order. For this to give a family stabilizer statement, we need to know that the rational matrix itself has finite order and that the prime in any nontrivial prime-power order is bounded by data available before choosing a word or a class. The finite adèles give the first assertion together with definiteness at infinity. The degree of a cyclotomic field gives the second.

**Example (dimension two) [Expository].** Put $A=\left(\begin{smallmatrix}0&-1\\1&-1\end{smallmatrix}\right)$ over $\mathbb Q$. Its square is $\left(\begin{smallmatrix}-1&1\\-1&0\end{smallmatrix}\right)$ and $A^2+A+I=0$, so multiplying by $A-I$ gives $A^3=I$. Since $A\ne I$, its order is $3$. Expanding $\det(TI-A)=T(T+1)+1$ gives $T^2+T+1$. The roots are the two primitive cube roots, giving $3-1=2$, the full available dimension. The matrix also preserves the rational positive form $Q(a,b)=a^2-ab+b^2$: substituting $(-b,a-b)$ gives $b^2+b(a-b)+(a-b)^2=a^2-ab+b^2$. In matrix language this is the Gram matrix with diagonal entries $2$ and off-diagonal entries $-1$, since it represents $2Q$. The matrix and its inverse are integral at every finite prime.

**Example (growing dimension) [Expository].** For each prime $p$, take $W_p=\{(x_0,\ldots,x_{p-1})\in\mathbb Q^p:\sum_j x_j=0\}$ and the cycle $P e_j=e_{j+1\bmod p}$. The basis $v_j=e_j-e_{p-1}$ for $0\le j<p-1$ shows that $\dim W_p=p-1$. For $0\le j<p-2$, $Pv_j=v_{j+1}-v_0$, and $Pv_{p-2}=-v_0$. These formulas preserve the integral span and $P^p=I$. For $p>2$ the first formula moves $v_0$. For $p=2$ the last formula sends it to $-v_0$. Thus the restriction has order $p$. Its characteristic polynomial is computed by splitting off the constant line, on which $P$ is the identity. On $\mathbb Q^p$ the vector $e_0$ is cyclic with basis $e_0,Pe_0,\ldots,P^{p-1}e_0$, so the minimal and characteristic polynomials both equal $T^p-1$. On $W_p$ the quotient is $1+T+\cdots+T^{p-1}$. The sum of squares restricts to a positive preserved form and the integral lattice is preserved in both directions. Even over the single field $\mathbb Q$, letting the rank vary permits arbitrarily large prime orders.

**Definition.** Fix a totally real field $F$, a number field $E/F$, a rank $k$ and the archive's Hermitian and definite data $(\sigma,J)$. Here $\sigma$ is an $F$-algebra endomorphism of $E$, and definiteness in `PI.IsDef` gives one strict sign on nonzero rational vectors at each real embedding of $F$. Write $A_f$ for the finite adèles of $F$. A rational stabilizing matrix is a $\gamma\in\operatorname{GL}_k(E)$ satisfying $\sigma(\gamma)^{\mathsf T}J\gamma=J$ whose diagonal image in $\operatorname{GL}_k(E\otimes_F A_f)$ lies in $yUy^{-1}$ for the compact unitary level $U$ and a unitary class representative $y$. Put $d=[E:\mathbb Q]k$. This is the rational dimension of the underlying $E$-space.

**Lemma (the definite adelic supply) [Lean, read].** Each such $\gamma$ has finite order.

**Proof.** The case $k=0$ is the trivial group. For $k>0$ the definiteness input to `PI.finOrdAd_of` gives, for every embedding $\phi:E\hookrightarrow\mathbb C$, $\phi\sigma=\overline{\phi}$ and positive definiteness of one of $\pm\phi(J)$. The host's production of the definite Gram data is the input used in §6.4.11.

To obtain these complex assertions, restrict $\phi$ to the real embedding of $F$. For $s\ne0$, take the ratio of the form on $se_i$ to its value on $e_i$. Both values have the same strict sign, so $\phi(\sigma s)\phi(s)$ is positive real. For $z=\phi(s)$ and $w=\phi(\sigma s)$, apply this test to $s+q$ for rational $q$ with $z+q\ne0$. If $z$ is nonreal, subtract the imaginary-part equations at $q=0,1$ to get $\operatorname{Im}w=-\operatorname{Im}z$, then use the equation at $0$ to get equal real parts. If $z$ is real, a single $q$ with $z+q\ne0$ gives $w$ real. If $w\ne z$, a rational $q$ between $-w$ and $-z$ would make $(w+q)(z+q)$ negative. Thus $w=\overline z$ in all cases.

It follows that $\phi(J)$ is Hermitian. Choose the sign given by definiteness on $E^k$. If $\phi(E)$ contains a nonreal $z$, the vectors with entries in $\mathbb Q+\mathbb Q z$ are dense in $\mathbb C^k$, so the signed form is nonnegative everywhere by continuity. If $\phi(E)$ is real, extend from $\mathbb Q^k$ to $\mathbb R^k$ by continuity. For a real symmetric matrix the value on $a+ib$ is the sum of its values on $a$ and $b$, giving the same nonnegativity over $\mathbb C$. The determinant of $J$ is nonzero because any nonzero vector in its kernel over $E$ would have form value zero. Its image under $\phi$ is still nonzero, so the signed semidefinite Hermitian matrix is positive definite.

Write the diagonal image of $\gamma$ as $yuy^{-1}$ with $u\in U$. For each $n\ge0$ its $n$th power is $yu^ny^{-1}$. Each entry of $yay^{-1}$ depends continuously on $a$, since it is a finite sum of fixed left and right scalar multiples of entries of $a$. The union of these $k^2$ images of $U$ is compact in $E\otimes_F A_f$ and contains the scalar base changes of all entries of every $\gamma^n$.

The compact denominator argument works first over $F$. The subgroup $\prod_v\mathcal O_v$ is open in the restricted product $A_f$. Each finite adèle has only finitely many nonintegral coordinates. At each such place a positive power of the underlying rational prime clears its denominator, so a positive integer clears all finitely many. The inverse images of the integral subgroup under these integer multiplications give an open cover of the compact set. Take a finite subcover and multiply its integers; the product still clears every denominator because integer multiplication preserves local integrality. For an element of $F$, integrality at every finite place is membership in $\mathcal O_F$. For the tensor product, choose an $F$-basis $(b_i)$ of $E$. The coordinate projections extended to $A_f$ are continuous in the module topology. Apply the preceding bound to each compact coordinate image and take the product $N_0$ of the bounds. Choose $D_0>0$ with $D_0 b_i\in\mathcal O_E$ for all $i$. For a diagonal element $z=\sum_i z_i b_i$ in the compact set, $N_0D_0z=\sum_i (N_0z_i)(D_0b_i)$ lies in $\mathcal O_E$. Thus one $N>0$ works for all the entries of all powers.

Now $\mathbb Z[\gamma]$, spanned as a $\mathbb Z$-module by the powers, lies in $N^{-1}M_k(\mathcal O_E)$, a finite free $\mathbb Z$-module. It is itself finite free. Multiplication by $\gamma$ on it has an integral matrix. Cayley–Hamilton for that operator, applied to $1$, gives a monic $P\in\mathbb Z[T]$ with $P(\gamma)=0$. Over an algebraic closure an eigenvector for $\lambda$ then gives $P(\lambda)=0$. Every eigenvalue is integral, and the coefficients of $\chi_\gamma$ are signed elementary symmetric functions of the eigenvalues counted with multiplicity. Hence they belong to $\mathcal O_E$. This is the power-bounded integrality step of the archive.

For each $\phi$, put $G=\phi(\gamma)$ and take the positive form $H=\pm\phi(J)$. The equation becomes $\overline G^{\mathsf T}HG=H$. For $Gv=\lambda v$ with $v\ne0$, this gives $|\lambda|^2 H(v,v)=H(v,v)$, so $|\lambda|=1$. Every conjugate over $\mathbb Q$ of each eigenvalue is a root of some $\phi(\chi_\gamma)$: extend the embedding of the eigenvalue field to a field containing both the eigenvalue and $E$, then restrict to $E$. Equivalently the archive uses the field formed by adjoining a root of the relevant irreducible factor over $E$. The root is an algebraic integer by transitivity of integrality for the monic polynomial with integral coefficients. Kronecker's argument now applies. If $\alpha$ is such an integer of degree $r$, each $\alpha^j$ for $j\ge1$ has degree at most $r$, and all its conjugates have modulus one. The coefficients of its monic integer minimal polynomial are bounded in absolute value by the corresponding binomial coefficients of its degree. There are finitely many such polynomials and finitely many roots in their union. Two positive powers of $\alpha$ coincide, and $\alpha\ne0$ gives a positive power equal to $1$.

Choose one embedding $\phi$ and a positive common multiple $m$ of the orders of the distinct eigenvalues of $G$ (the archive takes their product). The characteristic polynomial of $G$ divides $(T^m-1)^k$, because each of its linear factors divides $T^m-1$ and there are $k$ factors with multiplicity. Cayley–Hamilton gives $(G^m-I)^k=0$. To see the role of definiteness, write $W=G^m$. If $u=(W-I)v$ and $(W-I)u=0$, then preservation of $H$ gives $H(u,Wv)=H(Wu,Wv)=H(u,v)$, so $H(u,u)=0$ and $u=0$. Apply this implication to $(W-I)^{k-2}v$ when $k\ge2$ to lower the vanishing exponent by one, and repeat to obtain $W=I$. For $k=1$ this already follows from the exponent-one relation. Injectivity of $\phi$ on entries gives $\gamma^m=I$. $\square$

**Lemma (the prime-order dimension bound) [Lean, read].** If $g$ is prime, $M\in M_k(E)$, $M^g=I$ and $M\ne I$, then $g-1\le [E:\mathbb Q]k$.

**Proof.** Let $q$ be the monic minimal polynomial of $M$ over $E$. It divides $\chi_M$ by Cayley–Hamilton, so $\deg q\le k$. It also divides $T^g-1=(T-1)\Phi_g(T)$ by the power equation. If $q$ divided $T-1$, evaluating at $M$ would give $M=I$. There must therefore be an irreducible factor $f$ of $q$ dividing $\Phi_g$. If there were none, coprimality with $\Phi_g$ would give $q\mid T-1$. In $K=E[T]/(f)$ the residue class $\zeta$ of $T$ has order $g$, since it is a root of $\Phi_g$ and $\Phi_g(1)=g\ne0$. The power basis gives $[K:E]=\deg f\le k$. Over $\mathbb Q$, $\Phi_g$ has degree $g-1$ and is irreducible. Indeed $\Phi_g(T+1)=\sum_{j=1}^{g}\binom gj T^{j-1}$ is monic, every other coefficient is divisible by $g$, and its constant coefficient is $g$. Eisenstein and translation give irreducibility. Thus the two towers inside $K$ give
$g-1=[\mathbb Q(\zeta):\mathbb Q]\le[K:\mathbb Q]=[E:\mathbb Q]\deg f\le [E:\mathbb Q]k$.
The factor over $E$ can have smaller degree than $\Phi_g$. The factor $[E:\mathbb Q]$ accounts for this. $\square$ [Conrad, §5, Theorem 5.3](https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf)

**Theorem (uniform order control and the family stabilizer) [Lean, read].** With the definite data above, every rational stabilizing element has finite order. Any prime $g$ dividing its order satisfies $g-1\le d$. In particular, under the archive's actual level hypotheses, a pro-$g$ component above a prime with $g-1>d$ gives a trivial rational intersection and a trivial abstract level-zero stabilizer. The family construction supplies the numerical threshold $3$ with the guard $x_1<x$.

**Proof.** If $n$ is the order and $g\mid n$, then $M=\gamma^{n/g}$ has order exactly $g$. Indeed $M^g=I$, and $M=I$ would contradict the minimality of $n$. The preceding lemma supplies the bound. For the archive host $d=4\,\mathrm{ord}\,k=2fk$. The actual intersection argument applies this reasoning to the cyclic subgroup through `hostStab`.

To apply the bound the exact order must survive passage to the local level. Localize the identity between the diagonal image of $\gamma$ and $yuy^{-1}$ at $v\mid g$. The composite on rational entries is $E\to E\otimes_F F_v$, which is injective by extension of scalars over a field. Entrywise base change on invertible matrices is therefore injective and preserves exact order: equality of a power to the identity after base change implies the same equality before base change. Localization commutes with conjugation, which also preserves exact order. Consequently the image of $u$ in the local pro-$g$ subgroup has exact order $n$. The finite cyclic subgroup injects into a finite $g$-group quotient by the open normal subgroup argument of §6.4.11. Thus $n=g^s$. If $s>0$, $\gamma^{g^{s-1}}$ contradicts $g-1>d$, so the rational intersection is trivial.

There are now two injections in the abstract readback. The range condition for `stabI` places the adelic images of the rational matrices of any two abstract stabilizer elements in the intersection just proved trivial. The first injection, `InclInj`, equates the rational matrices from equality of their diagonal adelic images. The second, `stabI_inj`, equates the abstract stabilizer elements. The earlier local injection serves a different step, namely transferring the exact order. This argument uses injectivity only on the rational matrices at the local step.

For the actual family, `LinkTied.stabF` first selects the family constant from `field_lemmas_except_seven` and fills slot seven with `division_rational_lattice`. The supplied size inequalities of §6.4.11 give $2fk+1<4k^2\le(kb_{\rm sc})^8\le g_0$ at $x\ge3$ with $x_1<x$, so $g_0-1>d$. The cutoff $3$ precedes the member index, word and class, as required by `admF3`. Across the scale family the individual values of $d$ can vary: the size inequalities supply the same cutoff for beating the member's bound with its own prime. For later stages over the fixed base and columns of §6.4.11, it is the same host and rank, with the typed identification of the stabilizers already established there. A divisor update requires no new cutoff. The later column and level-prime consumers and their guard remain as traced in §6.4.11. $\square$

**Remark.** The archive needs the prime-order test for a pro-$g$ level. An elementary consequence for the full finite order at a fixed $d\ge1$ follows by viewing $\gamma$ on the underlying $d$-dimensional $\mathbb Q$-space. For each maximal prime power $p^a$ dividing $n$, the power $\gamma^{n/p^a}$ has order $p^a$. It is diagonalizable over $\mathbb C$ since its minimal polynomial divides the square-free polynomial $T^{p^a}-1$. The least common multiple of the eigenvalue orders is $p^a$, so at least one eigenvalue is primitive of order $p^a$. Its rational minimal polynomial $\Phi_{p^a}$ divides the characteristic polynomial of that rational operator. Its degree is $p^{a-1}(p-1)$, by the prime-power cyclotomic formula and Eisenstein after translation. Therefore $p\le d+1$ and $p^{a-1}(p-1)\le d$. The product of all prime powers satisfying the latter inequality is a finite common multiple for all possible orders. This explains the full uniform bound as a textbook consequence of the same degree argument. [Conrad, §5, Theorem 5.3](https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf)

**Reading boundary.** The two-prime detorsion, pointwise finiteness, split diamond and family comparison are quoted from §§6.4.8–6.4.11. Host Gram and metric production, the construction of the split pro-$g$ charts and the arithmetic comparison remain named inputs. The ordinary-projector identification remains [Open]. The proof-body reading is specified by the archive references below.

**Archive references.** The pinned SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The direct proofs are `src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/FinOrdAd.lean:9–10`, `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdicFiniteOrder/Assembly.lean:10–78` and `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Orbits.lean:24–91`. The consumption is in `src/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/LemmaOneSevenOfFiniteOrder.lean:168–226`, `src/Formalism/SharpRestriction/GlobalSchurBounds/Joints.lean:707–750` and `src/Formalism/SharpRestriction/GlobalSchurBounds/LinkTied.lean:24–29,51–67`. [Alpöge's archive index](https://alpo.ge/)


### 6.4.13 Split local groups and the pro-$g$ transport

The family stabilizer proof of §6.4.11 and the finite-order argument of §6.4.12 both use one local hypothesis: at a place $v$ of the host field $F$ above an auxiliary prime $g$, the local level subgroup $U_v$ of the unitary group is a pro-$g$ group. That is, $U_v$ is compact and every open normal subgroup has index a power of $g$. This is what turns a finite-order rational element into one of $g$-power order, which the host dimension bound then kills. In the archive this hypothesis is the field `ProG` of a level record, and it is proved rather than assumed. The proof has three parts. An explicit Iwahori-type subgroup of $\mathrm{GL}_k(F_v)$ is pro-$g$. A ring isomorphism $s:E\otimes_F F_v\cong F_v\times F_v$ identifies the local unitary group with a copy of $\mathrm{GL}_k(F_v)$, and the identification transports the pro-$g$ property provided $s$ and its inverse are continuous. The continuity is itself a theorem: every ring endomorphism of a nonarchimedean local field of characteristic zero is a homeomorphism onto its image, and in fact an automorphism. This subsection reads these three proofs and the single theorem `colProG` that assembles them, and then returns the conclusion to the stabilizer consumer. The finite-order supply, the Kronecker step and the host dimension bound keep the readings of §6.4.12. The level record itself, in particular the existence of the split isomorphisms `splitG` and of the frames `frG`, remains a named input, as does the Hida ordinary identification.

**Example (a pro-$3$ subgroup of $\mathrm{GL}_2(\mathbb Q_3)$) [Expository].** Take $g=3$, $k=2$ and the completed ring $\mathbb Z_3$ with maximal ideal $3\mathbb Z_3$. Let $S$ be the group of matrices in $\mathrm{GL}_2(\mathbb Z_3)$ whose lower-left entry lies in $3\mathbb Z_3$ and whose diagonal entries lie in $1+3\mathbb Z_3$. Modulo $3$ these are exactly the upper unitriangular matrices, so $S$ is the preimage of the unipotent upper triangular group of $\mathrm{GL}_2(\mathbb F_3)$. Consider $a=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)\in S$. By induction $a^{n}=\left(\begin{smallmatrix}1&n\\0&1\end{smallmatrix}\right)$, so $a^{3^m}-1$ has its only nonzero entry equal to $3^m$. The $3^m$-th powers converge to the identity in the $3$-adic topology, and $a^{3^m}\equiv1$ modulo $3^{m}$ exactly, never modulo $3^{m+1}$. For a matrix in the full principal congruence subgroup, take $A=1+3X$ with $X=\left(\begin{smallmatrix}1&2\\2&1\end{smallmatrix}\right)$, so $A=\left(\begin{smallmatrix}4&6\\6&4\end{smallmatrix}\right)$. Exact computation gives $A^{3}\equiv\left(\begin{smallmatrix}10&18\\18&10\end{smallmatrix}\right)$ modulo $27$ and $A^{9}\equiv\left(\begin{smallmatrix}28&54\\54&28\end{smallmatrix}\right)$ modulo $81$. In both cases $A^{3^m}-1$ is divisible by exactly $3^{m+1}$, which is the congruence $A^{g^m}\equiv1\pmod{\mathfrak m^{m+1}}$ proved below for every element congruent to $1$ modulo $\mathfrak m$. For a finite quotient, reduce $S$ modulo $9$. The image consists of the matrices over $\mathbb Z/9$ with lower-left entry in $\lbrace0,3,6\rbrace$ and diagonal entries in $\lbrace1,4,7\rbrace$, with the upper-right entry free. There are $3\cdot3\cdot3\cdot9=243=3^5$ of them. Each has determinant congruent to $1$ modulo $3$, hence is invertible modulo $9$, and the set is closed under multiplication since products preserve the two congruence conditions. So the open normal subgroup $S\cap(1+9M_2(\mathbb Z_3))$ has index $3^5$ in $S$, a power of $3$. The matrix $a$ has order exactly $9$ in this quotient. The full group $1+3M_2(\mathbb Z_3)$ has $3^4=81$ classes modulo $9$, so $S$ is strictly larger than the first principal congruence subgroup and still pro-$3$. These integers were checked by exact computation.

**Example (what fails without the hypotheses) [Expository].** Keep $g=3$. The matrix $d=\mathrm{diag}(-1,1)$ is not in $S$, since its first diagonal entry is $-1\equiv2$ modulo $3$. Its $3^m$-th powers are all equal to $d$ itself, because $(-1)^{3^m}=-1$, so they do not converge to $1$. The compact group generated by $d$ and $1+3M_2(\mathbb Z_3)$ has the open normal subgroup $1+3M_2(\mathbb Z_3)$ of index $2$, which is not a power of $3$. In one dimension, $\mathbb Z_3^\times=\lbrace\pm1\rbrace\times(1+3\mathbb Z_3)$ and the open subgroup $1+3\mathbb Z_3$ has index $2$. The condition that every element has $g$-power iterates tending to $1$ is therefore not a formality. It is exactly what the diagonal congruence $a_{ii}\equiv1\pmod{\mathfrak m}$ in the definition of $S$ secures, and the sublemma below reduces it to the nilpotence of the strictly upper triangular part modulo $\mathfrak m$ together with $g\in\mathfrak m$. For the transport lemma, the continuity hypotheses are also necessary. Let $G_1$ be the group $1+3\mathbb Z_3$ with the discrete topology and $G_2$ the same group with its $3$-adic topology. The identity map $\theta:G_1\to G_2$ is a continuous isomorphism, since every map out of a discrete space is continuous, and $G_2$ is pro-$3$. Its inverse $\psi$ is not continuous. The conclusion fails for $G_1$: an infinite discrete group is not compact. The transport lemma therefore needs the inverse map to be continuous, and the archive supplies that continuity through the homeomorphism theorem for local endomorphisms.

**Definition (pro-$g$ subgroups).** Let $G$ be a topological group, $g$ a natural number and $H\le G$ a subgroup. `IsProGrp g H` asserts that $H$ is compact as a subset of $G$ and that for every subgroup $N$ of $H$ that is open in $H$ and normal in $H$ there is $m$ with $[H:N]=g^m$. The archive's `IsProG` in `CMFieldLemmas.lean` is the same condition, used in §6.4.11 for the rational intersection.

**Definition (the Iwahori-type level).** For a number field $F$, a finite place $v$ and $k\ge0$, write $\mathcal O_v$ for the completed valuation ring, $\mathfrak m$ for its maximal ideal and $K_v$ for the completion. The set `upperUni` consists of the elements of $\mathrm{GL}_k$ of a ring whose entries below the diagonal vanish and whose diagonal entries equal $1$. The subgroup `iwU F k v` of $\mathrm{GL}_k(K_v)$ is the image under the inclusion $\mathcal O_v\to K_v$ of the preimage, under reduction modulo $\mathfrak m$, of the subgroup of $\mathrm{GL}_k(\mathcal O_v/\mathfrak m)$ generated by `upperUni`. By `closure_upperUni` that generated subgroup equals `upperUni` itself, so membership is the entry condition $a_{ij}\in\mathfrak m$ for $j<i$ and $a_{ii}-1\in\mathfrak m$ used in the example. The predicate `IwProG` states that `iwU F k v` is pro-$g$ whenever $g$ is a prime number with $g\in v$.

**Definition (the split unitary identification).** Let $E/F$ be an extension of number fields, $\sigma$ an $F$-algebra endomorphism of $E$ and $J\in M_k(E)$ with $\sigma(J)^{\mathsf T}=J$ and $\det J$ a unit. For an $F$-algebra $R$, `UPts σ J R` is the unitary group of $J$ over $E\otimes_F R$, the group of $x\in\mathrm{GL}_k(E\otimes_F R)$ with $\sigma_R(x)^{\mathsf T}Jx=J$, where $\sigma_R=\sigma\otimes\mathrm{id}$. Over the split ring $R\times R$ with the coordinate swap $\mathrm{sw}$ in the role of $\sigma$ and the matrix $\mathrm{split}(J_1)_{ij}=(J_{1,ij},J_{1,ji})$, the unitary group `UJ sw (splitJ J₁)` consists of pairs $(X,Y)$ of matrices with $Y^{\mathsf T}J_1X=J_1$. Its first projection to $\mathrm{GL}_k(R)$ is a group isomorphism, with inverse $u\mapsto(u,(J_1u^{-1}J_1^{-1})^{\mathsf T})$. The topology on $E\otimes_F K_v$ is the module topology `tensTopL` for the right $K_v$-module structure.

**Definition (the local homeomorphism assertion).** `LocalEndHomeo` states that for every number field $F$, finite place $v$ and ring homomorphism $\tau:K_v\to K_v$, the map $\tau$ is continuous and there is a continuous ring homomorphism $\tau'$ with $\tau\circ\tau'=\mathrm{id}$. The version `PI.LocalEndHomeo` in the period-integral layer and the version `ProGW.LocalEndHomeo` in the $\mathrm{GL}_5$ layer have the same statement, and `local_endomorphism_continuous` passes one to the other.

**Lemma (local endomorphisms are homeomorphisms) [Lean, read].** `LocalEndHomeo` holds. More precisely, every ring homomorphism $\tau:K_v\to K_v$ preserves the valuation, is a uniform embedding, and is surjective, and its inverse is again valuation preserving and continuous.

**Proof.** The proof is `localEndHomeo_of_three`, which combines five named steps. Each is proved in the archive and read here.

Hensel roots (`henselRoot`). Let $\ell$ be a natural number with $|\ell|_v=1$ and $u\in K_v$ with $|u-1|_v<1$. Then $u$ has an $\ell$-th root in $K_v$. The proof picks a uniformizer $\varpi$ of $\mathcal O_v$, shows that $\mathcal O_v$ is adically complete for $(\varpi)$ using the geometric Cauchy criterion in the complete normed field, and applies Mathlib's Henselian property to $X^\ell-u$ with approximate root $1$: the value at $1$ is $1-u\in(\varpi)$ and the derivative $\ell$ is a unit modulo $(\varpi)$ because $|\ell|_v=1$. Note $u\in\mathcal O_v$ since $|u|_v\le\max(|u-1|_v,1)$.

Integrality (`intOfHensel`). Let $N$ be the absolute norm of $v$. It lies in the prime $v$, so $|N|_v=\exp(-m)$ for some integer $m>0$ in the archive's multiplicative notation for $\mathbb Z^{\mathrm{m}0}$-valued valuations, and every prime $\ell>N$ has $|\ell|_v=1$ because $\ell$ and $N$ are coprime and $v$ is a prime ideal. Fix a prime $\ell>N+m$ and let $|x|_v\le1$. Then $u=1+Nx^\ell$ satisfies $|u-1|_v\le\exp(-m)<1$, so $u=z^\ell$ for some $z$. Apply $\tau$, which fixes natural numbers: $\tau(z)^\ell=1+N\tau(x)^\ell$. Suppose $|\tau(x)|_v=\exp(a)$ with $a>0$. Then $|N\tau(x)^\ell|_v=\exp(\ell a-m)>1=|1|_v$, so the strict triangle inequality gives $|\tau(z)|_v^\ell=\exp(\ell a-m)$. Writing $|\tau(z)|_v=\exp(c)$ gives $\ell c=\ell a-m$, so $\ell\mid m$, contradicting $0<m<\ell$. Hence $|\tau(x)|_v\le1$.

Valuation preservation (`valOfInt`). If $|y|_v=1$ then $|\tau(y)|_v\le1$ and $|\tau(y)^{-1}|_v=|\tau(y^{-1})|_v\le1$, so $|\tau(y)|_v=1$. For $x\ne0$ with $|x|_v=\exp(a)$ and $|\tau(x)|_v=\exp(b)$, the element $y=x^mN^{a}$ has $|y|_v=\exp(ma-ma)=1$, where a negative $a$ uses the inverse of $N$. Since $\tau(N)=N$, applying $\tau$ gives $\exp(mb-ma)=1$, so $m(b-a)=0$ and $b=a$.

Continuity (`valContinuous`). The uniformity of a valued field has the basis of entourages $\lbrace(p,q):|p-q|_v<\gamma\rbrace$. Since $|\tau(p)-\tau(q)|_v=|\tau(p-q)|_v=|p-q|_v$, the preimage of each basic entourage is itself, so $\tau$ is a uniform embedding (`isUniformInducing_of_val`) and in particular uniformly continuous.

Surjectivity (`valSurjective`). The range of a uniform embedding of a complete space is complete, hence closed. The range contains the image of $F$: for $a\in F$, the roots in $K_v$ of the minimal polynomial of $a$ over $\mathbb Q$ form a finite set, $\tau$ maps that set into itself because $\tau$ fixes $\mathbb Q$, and an injective self-map of a finite set is surjective, so $a$ is in the range. The image of $F$ is dense in $K_v$, so the closed range is everything.

Assembly (`localEndHomeo_of`). From the first three steps $\tau$ preserves the valuation. From the last two it is a continuous bijection. Let $\tau'$ be its inverse ring homomorphism. For any $x$, $|\tau(\tau'x)|_v=|\tau'x|_v$, so $|\tau'x|_v=|x|_v$, and the continuity step applies to $\tau'$. $\square$

Conrad's exposition of this result for finite extensions of $\mathbb Q_p$ runs the same way. His Step 1 uses Hensel's lemma to make elements of $1+\mathfrak m$ into $n$-th powers for infinitely many $n$, Step 5 derives the isometry, and continuity follows. Surjectivity there comes from $\mathbb Q_p$-linearity and finite dimension, whereas the archive uses the dense image of $F$ and the closed range. The archive also avoids Teichmüller representatives by choosing one large prime $\ell$ relative to the explicit integer $N$. [Conrad, Theorem 6.1 and Corollary 6.3, pp. 5–6](https://kconrad.math.uconn.edu/blurbs/gradnumthy/autRandQp.pdf)

**Lemma (a compact group with $g$-power convergence is pro-$g$) [Lean, read].** Let $H$ be a compact subgroup of a topological group $G$ and $g$ a prime. Suppose that for every $x\in H$ the sequence $x^{g^m}$ tends to $1$. Then $H$ is pro-$g$. The image of such an $H$ under a continuous homomorphism into another topological group is again pro-$g$.

**Proof.** This is `isProGrp_of_pow`. Compactness is assumed. Let $N$ be an open normal subgroup of $H$. Since $H$ is compact and $N$ is open, the quotient $H/N$ is finite. For a class $xN$, the open set $N$ is a neighborhood of $1$ in $H$, so $x^{g^m}\in N$ for some $m$, and $(xN)^{g^m}=1$. Every element of the finite group $H/N$ has $g$-power order, so $H/N$ is a $g$-group and $[H:N]=|H/N|$ is a power of $g$. For the image statement (`isProGrp_map`), the image of a compact set under a continuous map is compact, and for $y=f(x)$ the sequence $y^{g^m}=f(x^{g^m})$ tends to $f(1)=1$ by continuity. $\square$

The topological background is the characterization of profinite spaces as compact, Hausdorff and totally disconnected spaces. The quotient argument above does not need that characterization; it uses only that open subgroups of compact groups have finite index. [Stacks Project, Lemma 5.22.2](https://stacks.math.columbia.edu/tag/08ZW)

**Lemma (convergence from ideal powers) [Lean, read].** Let $R$ be a compact Hausdorff Noetherian topological ring and $I$ an ideal with $\bigcap_n I^n=0$. Every neighborhood of $0$ contains some $I^n$. If $x_m-c\in I^{m+1}$ for all $m$ then $x_m\to c$.

**Proof.** This is `pow_subset_nhds` and `tendsto_of_mem_pow`. Each ideal $J$ is finitely generated, so it is the image of the compact space $R^{s}$ under the continuous map $(c_i)\mapsto\sum c_i j_i$, hence closed. Let $V$ be a neighborhood of $0$ and $W\subseteq V$ open with $0\in W$. The complement $W^{\mathsf c}$ is closed in the compact space $R$, hence compact. The closed sets $W^{\mathsf c}\cap I^n$ are directed downward, since $I^{\max(a,b)}\subseteq I^a\cap I^b$, and their intersection is $W^{\mathsf c}\cap\bigcap_nI^n=W^{\mathsf c}\cap\lbrace0\rbrace=\varnothing$ because $0\in W$. A directed family of closed subsets of a compact set with empty intersection has an empty member, so $I^n\subseteq W\subseteq V$ for some $n$. The second claim follows: given a neighborhood $U$ of $0$ pick $n$ with $I^n\subseteq U$; then for $m\ge n$ we have $x_m-c\in I^{m+1}\subseteq I^n\subseteq U$. $\square$

**Sublemma (the congruence $A^{g^m}\equiv1\pmod{I^{m+1}}$) [Lean, read].** Let $R$ be a commutative ring, $I$ an ideal, $g$ a natural number with $g\in I$, and $A\in M_k(R)$ with $A\equiv1$ entrywise modulo $I$. Then $A^{g^m}\equiv1$ modulo $I^{m+1}$ for all $m$.

**Proof.** This is `congPow`, by induction on $m$; the case $m=0$ is the hypothesis. Put $B=A^{g^m}$, so $B-1$ has entries in $I^{m+1}$. The geometric sum identity gives
$B^{g}-1=\Big(\sum_{t<g}B^t\Big)(B-1)=\Big(\sum_{t<g}(B^t-1)\Big)(B-1)+g\,(B-1).$
Each $B^t-1=(\sum_{r<t}B^r)(B-1)$ has entries in $I^{m+1}$, so the first product has entries in $I^{m+1}I^{m+1}\subseteq I^{m+2}$. The second term has entries in $gI^{m+1}\subseteq I\cdot I^{m+1}=I^{m+2}$. Since $A^{g^{m+1}}=B^g$, the induction closes. $\square$

**Sublemma (killing the unipotent part) [Lean, read].** Let $g$ be prime with $g\in I$, and let $A\in M_k(R)$ have $A_{ij}\in I$ for $j<i$ and $A_{ii}-1\in I$. If $k\le g^s$ then $A^{g^s}\equiv1$ modulo $I$.

**Proof.** This is `unip_pow`. Reduce modulo $I$ and write the image as $1+N$ with $N$ strictly upper triangular over $R/I$. By induction $(N^m)_{ij}=0$ whenever $j<i+m$, so $N^k=0$, and then $N^m=0$ for all $m\ge k$. Expand $(1+N)^{g^s}=\sum_m\binom{g^s}{m}N^m$. For $0<m<g^s$ the binomial coefficient is divisible by the prime $g$, hence zero in $R/I$. For $m=g^s\ge k$ the power $N^m$ vanishes. Only the term $m=0$ survives. $\square$

For odd $p$, the congruence sublemma is the matrix form of the classical computation $(1+pX)^p\equiv1+p^2X$ modulo $p^3$ that shows $1+pM_d(\mathbb Z_p)$ is a pro-$p$ group; Klopsch's lectures record that $G_1=1+p\,\mathrm{Mat}_d(\mathbb Z_p)$ is the kernel of reduction, is pro-$p$, and is uniform for odd $p$. The archive's $S$ is larger than $G_1$, which is why the unipotent sublemma is needed first. [Klopsch, Section 8 and Proposition 8.1, p. 32](https://www.math.uni-duesseldorf.de/~klopsch/mathematics/Manuskripte/analytic_groups.pdf)

**Theorem (the Iwahori-type level is pro-$g$) [Lean, read].** `IwProG` holds: for a prime $g\in v$, the subgroup `iwU F k v` of $\mathrm{GL}_k(K_v)$ is pro-$g$.

**Proof.** This is `iwProG`. First, $\mathcal O_v$ is compact (`compactOv`). It is a complete discrete valuation ring, closed in $K_v$, and its residue field is finite by the supplied `glint_finite_residueField`; Mathlib's characterization of compact valuation rings gives compactness. Hence $M_k(\mathcal O_v)$ is compact as a finite product. By `natCast_mem_max` the image of $g$ lies in $\mathfrak m$: otherwise $g$ would be a unit in $\mathcal O_v$, while $|g|_v<1$ because $g\in v$. By Krull's intersection theorem for local rings, $\bigcap_n\mathfrak m^n=0$.

Let $S\le\mathrm{GL}_k(\mathcal O_v)$ be the preimage of the closure of `upperUni` under reduction. Using `closure_upperUni`, $a\in S$ if and only if $a_{ij}\in\mathfrak m$ for $j<i$ and $a_{ii}-1\in\mathfrak m$. Each entry map $a\mapsto a_{ij}$ is continuous on $\mathrm{GL}_k(\mathcal O_v)$, and $\mathfrak m$ is closed, being finitely generated in the compact Hausdorff ring. So $S$ is a finite intersection of closed sets, hence closed, hence compact since $\mathrm{GL}_k(\mathcal O_v)$ embeds in the compact $M_k(\mathcal O_v)\times M_k(\mathcal O_v)$ via $A\mapsto(A,A^{-1})$, whose image is closed by the equations $AB=BA=1$.

For $a\in S$, choose $s$ with $k\le g^s$. The unipotent sublemma gives $B=a^{g^s}\equiv1$ modulo $\mathfrak m$, and the congruence sublemma gives $B^{g^m}\equiv1$ modulo $\mathfrak m^{m+1}$. The inverse satisfies $B^{-g^m}-1=-B^{-g^m}(B^{g^m}-1)$, whose entries are $\mathcal O_v$-combinations of entries of $B^{g^m}-1$, hence also lie in $\mathfrak m^{m+1}$. The convergence lemma, applied entrywise, shows that both $B^{g^m}$ and its inverse tend to $1$ in $M_k(\mathcal O_v)$. The topology on units is the embedding $u\mapsto(u,u^{-1})$, so $B^{g^m}\to1$ in $\mathrm{GL}_k(\mathcal O_v)$ (`units_tendsto_one`). Since $a^{g^{m+s}}=B^{g^m}$, the shifted sequence converges and so does $a^{g^m}$. The compact-group lemma shows that $S$ is pro-$g$. Finally `iwU F k v` is the image of $S$ under the continuous homomorphism $\mathrm{GL}_k(\mathcal O_v)\to\mathrm{GL}_k(K_v)$ induced by the inclusion, so the image statement finishes the proof. $\square$

**Lemma (continuity of the split isomorphism from the homeomorphism theorem) [Lean, read].** Assume `LocalEndHomeo`. Let $s:E\otimes_FK_v\cong K_v\times K_v$ be a ring isomorphism such that $s\circ\sigma_{K_v}=\mathrm{sw}\circ s$. Then $s$ and $s^{-1}$ are continuous for the module topology on $E\otimes_FK_v$.

**Proof.** This is `split_cont_of_homeo`. Define $\tau:K_v\to K_v$ as the first coordinate of $s(1\otimes a)$. Since $\sigma_{K_v}$ fixes $1\otimes a$, the swap hypothesis gives $s(1\otimes a)=\mathrm{sw}(s(1\otimes a))$, so both coordinates agree and $s(1\otimes a)=(\tau a,\tau a)$. The homeomorphism theorem gives $\tau$ continuous with a continuous right inverse $\tau'$. A ring homomorphism out of a module-topology algebra is continuous as soon as its restriction to the scalars is continuous, so $s$ is continuous because $a\mapsto(\tau a,\tau a)$ is. For $s^{-1}$, compute $s^{-1}(c,c)=1\otimes\tau'(c)$: indeed $s(1\otimes\tau'c)=(\tau\tau'c,\tau\tau'c)=(c,c)$. Hence $s^{-1}$ is $\tau'$-semilinear, $s^{-1}(c\cdot p)=\tau'(c)\cdot s^{-1}(p)$, and a semilinear map into a module topology with continuous scalar twist is continuous. $\square$

Without the homeomorphism theorem the archive has a second route, `split_cont`, which assumes that $s(1\otimes a)=(a,a)$. That makes $s$ a $K_v$-linear isomorphism of finite free modules, continuous in both directions for the module topology. The actual level record only carries the swap compatibility `splitG_sig`, not this $K_v$-linearity, so the main-path theorem `levels_pro_g` uses the homeomorphism route. The alternative predicate `SplitGAlg` and `levels_pro_g_of_split_algebra` package the other route and are not on the path to `stabF`.

For the actual matrix group $S$, the kernels of reduction modulo $\mathfrak m^n$ form a neighborhood basis at the identity and have trivial intersection. If the residue field has size $q=g^f$, the first quotient is upper unitriangular of order $q^{k(k-1)/2}$. Each subsequent layer has order $q^{k^2}$, since $1+\varpi^n X$ at layer $n$ is determined by $X$ modulo $\mathfrak m$. Reduction onto these finite images and compactness identify $S$ with their inverse limit.

**Lemma (transport of the pro-$g$ property) [Lean, read].** Let $\theta:G_1\to G_2$ be a continuous homomorphism of topological groups and $\psi:G_2\to G_1$ a continuous map. Let $U\le G_1$ and $P\le G_2$ satisfy $\theta(U)\subseteq P$, $\psi(P)\subseteq U$ with $\theta\psi=\mathrm{id}$ on $P$, and $\psi\theta=\mathrm{id}$ on $U$. If $P$ is pro-$g$ then $U$ is pro-$g$.

**Proof.** This is `isProGrp_transfer`. The restrictions give a group isomorphism $e:U\to P$ with inverse induced by $\psi$, and $e^{-1}$ is continuous. Compactness: $U=\psi(P)$, since $x=\psi(\theta x)$ for $x\in U$, and this is the continuous image of a compact set. Index: for $N$ open normal in $U$, the preimage $e^{-1\,*}N$ under the continuous surjective homomorphism $e^{-1}:P\to U$ is open and normal in $P$ and has the same index, which is a power of $g$. $\square$

**Theorem (transport from $\mathrm{GL}_k(K_v)$ to the local unitary group) [Lean, read].** Let $E/F$, $\sigma$, $J$ be as above with $J$ $\sigma$-Hermitian and $\det J$ a unit. Let $s:E\otimes_FK_v\cong K_v\times K_v$ be a ring isomorphism with $s\circ\sigma_{K_v}=\mathrm{sw}\circ s$, continuous in both directions. Let $h\in\mathrm{GL}_k(K_v)$, $P\le\mathrm{GL}_k(K_v)$, and $U\le$ `UPts σ J K_v` such that for all $x$ in the unitary group, $x\in U$ if and only if $h^{-1}\,\pi_1(s(x))\,h\in P$, where $\pi_1(s(x))$ is the entrywise first coordinate of $s$ applied to $x$. If $P$ is pro-$g$ then $U$ is pro-$g$.

**Proof.** This is `proGTransfer_of_cont`. Let $J_1\in M_k(K_v)$ be the first coordinate of $s(1\otimes J)$ entrywise. The Hermitian condition $J_{ij}=\sigma(J_{ji})$ and the swap compatibility give that the second coordinate of $s(1\otimes J_{ij})$ equals the first coordinate of $s(1\otimes J_{ji})$, so $s(1\otimes J)=\mathrm{split}(J_1)$. The determinant of $J_1$ is the image of $\det J$ under a ring homomorphism, hence a unit. Put $\varphi=\pi_1\circ s$, $\theta(x)=h^{-1}\varphi(x)h$, and
$\psi(a)=s^{-1}\big(\mathrm{lift}_{J_1}(hah^{-1})\big),\qquad \mathrm{lift}_{J_1}(u)=\big(u,(J_1u^{-1}J_1^{-1})^{\mathsf T}\big),$
with $s^{-1}$ applied entrywise. The lift lies in the split unitary group `UJ sw (splitJ J₁)`: with $Y=(J_1u^{-1}J_1^{-1})^{\mathsf T}$ one has $Y^{\mathsf T}J_1u=J_1u^{-1}J_1^{-1}J_1u=J_1$. Transporting along $s^{-1}$ turns the split unitary group for $\mathrm{split}(J_1)$ into the unitary group of $J$ over $E\otimes_FK_v$, because $s^{-1}\circ\mathrm{sw}=\sigma_{K_v}\circ s^{-1}$ (`transport_symm_comp`, `transport_bc_mem`) and $s^{-1}(\mathrm{split}(J_1))=1\otimes J$. So $\psi(a)$ is unitary. Its $\theta$-image is $h^{-1}\pi_1(\mathrm{lift}_{J_1}(hah^{-1}))h=h^{-1}(hah^{-1})h=a$, since the first coordinate of the lift is its argument. Conversely, for unitary $x$, both $\psi(\theta x)$ and $x$ are unitary and have the same $\varphi$-image, so their images under $s$ lie in the split unitary group with the same first coordinate. In the split unitary group the second coordinate is determined by the first: from $Y^{\mathsf T}J_1X=J_1$ one gets $Y^{\mathsf T}=J_1X^{-1}J_1^{-1}$ (`split_injective`). Hence $\psi(\theta x)=x$.

Continuity: $\theta$ is conjugation by a fixed element composed with the entrywise map $\varphi$, and $\varphi$ is continuous because $s$ is. The map $\psi$ is the composite of conjugation by $h$, the lift $u\mapsto(u,(J_1u^{-1}J_1^{-1})^{\mathsf T})$, which is continuous because inversion is continuous on units and the remaining operations are fixed matrix multiplications and transposition (`continuous_splitLift`), and the entrywise $s^{-1}$, which is continuous by hypothesis. The membership equivalence says exactly that $\theta(U)\subseteq P$ and that $\psi(p)\in U$ for $p\in P$, using $\theta(\psi p)=p$. The transport lemma applies. $\square$

**Theorem (the level record is pro-$g$) [Lean, read].** Assume `LocalEndHomeo`. Let $L$ be a level record `ColLevel` for ranks $R$, fields $E/F$, Hermitian data `sp` and two primes $g_0,g_1$. Then $L$ satisfies `ProG`: for $i\in\lbrace0,1\rbrace$ and every finite place $v$ with $g_i\in v$, the local subgroup $L.\mathrm{Uloc}(v)\le\mathrm{GL}_k(E\otimes_FK_v)$ is pro-$g_i$.

**Proof.** This is `colProG`, and the whole proof is the application of the preceding results to the fields of $L$. The record supplies, for each $i$ and $v\mid g_i$, a ring isomorphism $L.\mathrm{splitG}(i,v):E\otimes_FK_v\cong K_v\times K_v$ with the swap compatibility `splitG_sig` for the involution `sp.cm.sig`, a frame $L.\mathrm{frG}(i,v)\in\mathrm{GL}_k(K_v)$, the inclusion `Uloc_le` of the local subgroup in the unitary group of `sp.gram0`, and the chart equation `Uloc_g`: for unitary $x$, $x\in L.\mathrm{Uloc}(v)$ if and only if $\mathrm{frG}^{-1}\,\pi_1(\mathrm{splitG}(x))\,\mathrm{frG}\in$ `iwU F k v`. The Gram matrix `sp.gram0` is Hermitian by `baseGram_isHermitian`, and its determinant is a unit by the supplied `isUnit_det_gram0`. The continuity lemma gives continuity of $\mathrm{splitG}(i,v)$ and its inverse from `LocalEndHomeo`. The Iwahori theorem gives that `iwU F k v` is pro-$g_i$ since $g_i$ is prime and $g_i\in v$. The transport theorem with $P=$ `iwU F k v`, $h=\mathrm{frG}(i,v)$, $U=L.\mathrm{Uloc}(v)$ concludes. $\square$

**Corollary (the actual main-path supply) [Lean, read].** `levels_pro_g` proves `Link4p`: for every data record $D$ and level family `Lv`, `StandardLattice.Conclusion4p D Lv` holds, that is, `(Lv u).ProG` for every word $u$.

**Proof.** `local_endomorphism_continuous` restates `local_endomorphism_homeomorph` for the $\mathrm{GL}_5$-layer predicate, `levels_pro_g_of_continuity` applies `colProG` to `Lv u` with the primality `D.host.g_prime`, and `levels_pro_g` composes the two. $\square$

**Returning to the stabilizer input.** In §6.4.11 the family theorem `stabF` passes `(fun _ _ _ => GenusMassVolumes.levels_pro_g _ _)` as the pro-$g$ argument `hP` of `stabiliser_family_of_column_lemma`. Following that argument down, `stabiliser_family_of_definite` evaluates `hP x hx1 i` to `Conclusion4p (Fm.D x i) (Fm.ex x hx1 i).lev`, and `stabiliser_condition_of_level` passes `hP u : (Lv u).ProG` to `stabZero_of_level`. There, `column_lemma_of_definite_form` chooses a place $v$ above $g_i$ by lying over and feeds `(Lv u).Uloc v` together with `hP i v hv : IsProGrp (g i) ((Lv u).Uloc v)` into `division_rows_rational_lattice` as the local group $U_w$ with the hypothesis $\mathrm{IsProG}\,g\,U_w$. This is the compact pro-$g$ level in which the open normal subgroup argument of §6.4.11 forces the exact order of the localized stabilizer element to be a power of $g$, after which the host dimension bound of §6.4.12 and the two injections `InclInj` and `stabI_inj` give the trivial abstract stabilizer. The chart equation `Uloc_g` is therefore the precise point where the explicit group $S$ of the first example enters the proof: the local level is the conjugate, by the frame, of the Iwahori-type group, read back through the split isomorphism.

**Remark (which hypotheses do what).** The primality of $g$ is used twice: in the binomial divisibility $g\mid\binom{g^s}{m}$ for the unipotent sublemma and in the conclusion that a finite group all of whose elements have $g$-power order has $g$-power order. The membership $g\in v$ is used only to put $g$ into $\mathfrak m$. The compactness of $\mathcal O_v$ is where finiteness of the residue field enters, through the named input `glint_finite_residueField`. The Hermitian condition and the unit determinant of the Gram matrix are used only to show that the split form is $\mathrm{split}(J_1)$ with $J_1$ invertible, which makes the first projection of the split unitary group injective. The $K_v$-linearity of the split isomorphism is not needed; the swap compatibility and the homeomorphism theorem replace it.

**Remark (limits of the reading).** The level record is a structure. This subsection proves the pro-$g$ property of its local subgroups from its fields and from the four theorems named above, and does not prove that level records exist. The existence of `splitG`, `frG` and the groups `Uloc` with the chart equation is part of the family data `Fm.ex` of §6.4.11, which remains a named input here. The finite residue field, the unit determinant of the Gram matrix, Mathlib's Henselian property and Krull intersection theorem, and the compactness criterion for valuation rings are used as library inputs. The finite-order and host dimension bounds are quoted from §6.4.12 and not re-audited. The Hida ordinary identification remains [Open].

**Archive references.** The pinned SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The consumer and the three transport proofs are in `src/Formalism/LocalToGlobal/GlobalTheory/GL5/LevelsProGOfSplitAlgebra.lean`: `isProGrp_of_pow`, `isProGrp_map` (:20–50), `pow_subset_nhds`, `tendsto_of_mem_pow` (:56–99), `congPow` (:120–143), `units_tendsto_one` (:145–151), `compactOv`, `iwProG` (:157–253), `isProGrp_transfer` (:259–290), `splitLift`, `splitLift_mem`, `splitLift_fst`, `continuous_splitLift` (:295–345), `proGTransfer_of_cont` (:349–436), `split_cont` (:438–456), `LocalEndHomeo`, `split_cont_of_homeo`, `colProG`, `levels_pro_g_of_continuity` (:466–524). The homeomorphism theorem is `src/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/LocalEnd.lean:7–8` with proof bodies in `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalEndomorphisms/` (`HenselRoot.lean:21–48,50–87`, `IntVal.lean:12–71,74–119`, `IsUniformInducingOfVal.lean:8–25`, `AlgebraMapMemRange.lean:12–51`, `LocalEndHomeoOf.lean:9–22`, `Assembly.lean:8–10`), with the predicates in `ValSurjective.lean:8–35`. The unipotent sublemma is `src/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean:32–82`, with `natCast_mem_max` at `:152–175`. The definitions are in `src/Formalism/LocalRingCardinality/DataLevel.lean:17–39,94–191,193–195`, `src/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/ProGTransfer.lean:11–26` and `src/Formalism/SatakeDualWeyl/Statement.lean:13–49,73–78,88–96,118–120`. The wiring is `src/Formalism/LocalToGlobal/GlobalTheory/GL5/LocalEndomorphismContinuous.lean:6–8`, `src/Formalism/SharpRestriction/GlobalSchurBounds/LinkTied.lean:24–29`, `JointsF.lean:125–132` and `Joints.lean:707–750` in that directory. [Alpöge's archive index](https://alpo.ge/)

### 6.4.14 Definiteness of the host Gram matrix at real embeddings

**Motivation.** The rational unitary intersection in §6.4.11 uses the definiteness hypothesis of §6.4.12. The host record gives signatures for complex matrices, while the intersection lemma asks for inequalities on elements of the fixed real subfield. The bridge is the diagonal value of the Hermitian form on a rational vector, meaning a vector defined over the host field $E$. That value descends to $F$, where it can be evaluated at a real embedding.

**Worked examples [Expository].** Take $E=\mathbb Q(i)$ and $F=\mathbb Q$. For $z=(u,v)^{\mathsf T}$ write $z^\dagger$ for its conjugate transpose. Write $u=a+bi$ and $v=c+di$.

1. For $J_+=\begin{pmatrix}1&i\\-i&2\end{pmatrix}$, direct multiplication gives
   $z^\dagger J_+z=\bar u u+i\bar u v-i\bar v u+2\bar v v=|u+iv|^2+|v|^2=(a-d)^2+(b+c)^2+c^2+d^2$.
   The value is rational. Equality to zero forces $c=d=0$ and then $a=b=0$. The coordinate map $(u,v)\mapsto(u+iv,v)$ has inverse $(s,t)\mapsto(s-it,t)$, exhibiting signature $(2,0)$. At $(1+i,2-i)$ the value is $2^2+3^2+2^2+(-1)^2=18$.
2. For $J_-=\begin{pmatrix}-2&1+i\\1-i&-2\end{pmatrix}$,
   $z^\dagger J_-z=-2\bar u u+(1+i)\bar u v+(1-i)\bar v u-2\bar v v=-2|u-(1+i)v/2|^2-|v|^2$.
   The first squared modulus is $(a-(c-d)/2)^2+(b-(c+d)/2)^2$. Thus the value is rational, and it is strictly negative unless $v=0$ and $u=0$. The invertible coordinate map $(u,v)\mapsto(\sqrt{2}(u-(1+i)v/2),v)$ exhibits signature $(0,2)$. At $(1+i,2-i)$ the value is $-2((-1/2)^2+(1/2)^2)-5=-6$.
3. The mixed matrix $\mathrm{diag}(1,-1)$ gives $1$ at $(1,0)$, $-1$ at $(0,1)$ and $0$ at the nonzero vector $(1,1)$. Hermitian symmetry and invertibility alone allow all three values at a single real embedding.

The other embedding of $\mathbb Q(i)$ conjugates both the matrix and the vector, leaving the rational value fixed in each calculation.

**Definitions.** Let $E/F$ be a field extension with an involutive $F$-algebra automorphism $\sigma$. Write $\iota:F\hookrightarrow E$ for the structure map. For a finite coordinate set $I$, Hermitian symmetry means $\sigma(J_{ji})=J_{ij}$. Put $H_J(x,y)=\sum_{i,j\in I}\sigma(x_i)J_{ij}y_j$. The archive's `IsDef` requires that for each $\rho:F\hookrightarrow\mathbb R$ there be a sign $\epsilon_\rho\in\{1,-1\}$ such that every nonzero $x\in E^I$ has a witness $a\in F$ with $\iota(a)=H_J(x,x)$ and $\epsilon_\rho\rho(a)>0$. The witness is unique by injectivity of $\iota$. The sign is chosen before the vector.

For a complex matrix $M$ on $I$, `HasSignature` of type $(p,q)$ supplies a bijection $e:I\to B$, with $B$ the disjoint union of $p$ positive and $q$ negative indices, and an invertible matrix $P$ on $B$ with $P^\dagger M_e P=\mathrm{diag}(I_p,-I_q)$. Here $(M_e)_{ab}=M_{e^{-1}(a),e^{-1}(b)}$.

**Lemma (signature, strict signs and relabeling) [Lean, read].** For $z\ne0$, the real part of $z^\dagger Mz$ is strictly positive at signature $(p,0)$ and strictly negative at signature $(0,q)$. Any relabeling $M_f$ along a bijection $f:I\to I'$ has the same signature.

**Proof.** Transport $z$ to $z'=z\circ e^{-1}$ and put $y=P^{-1}z'$. The inverse transport is $z=(Py)\circ e$, so $y\ne0$. Indexing the two sums in the matrix product by $B$ gives
$z^\dagger Mz=(Py)^\dagger M_e(Py)=y^\dagger\mathrm{diag}(I_p,-I_q)y=\sum_{a\in B_+}|y_a|^2-\sum_{b\in B_-}|y_b|^2$,
where $B_+$ and $B_-$ are the positive and negative index sets. Each sum is real. A block containing a nonzero coordinate has strictly positive sum. For $(p,0)$ the negative block is empty, so the nonzero coordinate lies in the positive block. For $(0,q)$ the positive block is empty and the nonzero coordinate lies in the negative block. For relabeling, use $e\circ f^{-1}:I'\to B$ with the same $P$. Relabeling $M_f$ by this bijection gives $M_e$ entrywise, since $f^{-1}\circ f\circ e^{-1}=e^{-1}$. Equalities of the numerical parameters in `sig_reindex` simply substitute $p$ and $q$ in this witness. $\square$

**Theorem (descent of definiteness and the host supply) [Lean, read].** Let $E/F$ be algebraic and let $\sigma$ be an involutive $F$-algebra automorphism with fixed field $\iota(F)$. Assume $\tau(\sigma b)=\overline{\tau(b)}$ for every complex embedding $\tau:E\hookrightarrow\mathbb C$ and $b\in E$. Let $J$ be $\sigma$-Hermitian of size $k$. If for every $\tau$ the matrix $\tau(J)$ has signature $(k,0)$ or $(0,k)$, then $J$ satisfies `IsDef`. For every archive datum $D$ of type `D7`, the hypotheses hold for its base Gram matrix with $k=D.R.k$ and $\sigma=D.\mathrm{sp}.\mathrm{cm}.\mathrm{sig}$, giving `Gram0Def`.

**Proof.** Fix $\rho:F\hookrightarrow\mathbb R$ and compose it with the inclusion into $\mathbb C$. Order embeddings of intermediate fields into $\mathbb C$ extending this map by restriction. The union along a chain defines an embedding on the union field. A maximal embedding exists by Zorn's lemma. If its domain $L$ omits $b\in E$, transport the minimal polynomial $m_b$ of $b$ over $L$ to the image field. It is irreducible there and has a root in $\mathbb C$. Evaluating at that root induces a unital map from the field $L[T]/(m_b)$ and hence an embedding of $L(b)$. This contradicts maximality. In the quadratic host case a single adjunction suffices. Lean uses the algebraically closed lift with the $F$-algebra structure on $\mathbb C$ given by $\rho$. Denote the extension by $\tau$. [Milne, *Fields and Galois Theory*, Theorem 6.6, p. 90](https://www.jmilne.org/math/CourseNotes/FT.pdf)

For any $x\in E^k$, involutivity and Hermitian symmetry give
$\sigma(H_J(x,x))=\sum_{i,j}x_iJ_{ji}\sigma(x_j)=\sum_{i,j}\sigma(x_i)J_{ij}x_j=H_J(x,x)$.
The middle step interchanges indices and commutes factors. Thus the fixed-field hypothesis supplies $\iota(a)=H_J(x,x)$. With $z_i=\tau(x_i)$ the ring map laws and conjugation compatibility give
$z^\dagger\tau(J)z=\tau(H_J(x,x))=\tau(\iota(a))=\rho(a)$
in $\mathbb C$. If $x\ne0$, a nonzero coordinate of $x$ has nonzero image by injectivity of $\tau$.

Apply the signature hypothesis to the fixed $\tau$. In the $(k,0)$ branch the lemma gives $\rho(a)>0$ for every nonzero $x$. In the $(0,k)$ branch it gives $\rho(a)<0$ for every nonzero $x$. Taking real parts in the displayed identity gives the required inequalities in $F$ under $\rho$. For $k=0$ the only vector is zero and both universal sign branches hold vacuously. The common signature $(0,0)$ has the empty bijection and the identity on the zero space as witnesses. The general descent theorem includes this endpoint. The actual host ranks satisfy $2\le R.m$ and $R.m+3\le R.k$.

For the host specialization, take the fields of `D.host` and the star installed by `D.host.cmStar`. The record `D.sp` uses that star. Its `cm.deg2` supplies finite dimensionality and hence algebraicity. The map `cm.sig` acts by star and fixes the image of $F$ by `cm.fixed`. The same field supplies descent for every fixed element. Involutivity is `star_star` and compatibility with every $\tau$ is the conjugation clause `cm.cmUnram.2.1`.

Set $X_0=D.\mathrm{sp}.X(0)$ and $r=\mathrm{rank}(X_0)$. Evaluating `X_rank` at $0\le D.R.m$ gives `rank0`, because $R.N(0)=R.k+0(R.t+1)=k$. The map `finCongr rank0` gives the bijection $f:\mathrm{Fin}(r)\to\mathrm{Fin}(k)$. The matrix `gram0` is the frame Gram of $X_0$ relabeled by $f$. Its Hermitian proof `baseGram_isHermitian` evaluates the symmetry of $X_0$ on the two frame vectors indexed by the inverse relabeling. Mapping entries by $\tau$ commutes with relabeling since both entries at $(a,b)$ are $\tau((X_0.\mathrm{gram})_{f^{-1}(a),f^{-1}(b)})$.

For each $\tau$, `D.sp.X_sig` at grade $0$ and embedding $\tau$ gives a signature witness at the pair $X_0.\mathrm{sig}(\tau)$. `D.sp.X_def` at grade $0$ with the proof of $0\le D.R.m$, evaluated at $\tau$, gives $(r,0)$ or $(0,r)$ for that pair. Substitute the pair into the witness and use the relabeling lemma with $r=k$ in the corresponding slot. This proves the signature hypothesis for $\tau(J)$ and completes `gram0Def`. $\square$

**Remark (the sign belongs to the real place).** Any two complex extensions of the same $\rho$ give the same value $\rho(a)$. In positive dimension a nonzero vector therefore forces the same branch for both extensions. Across real places either sign may occur. On $\mathbb Q(\sqrt{2},i)/\mathbb Q(\sqrt{2})$, the rank-one Gram $[\sqrt{2}]$ gives $a=\sqrt{2}\,x\sigma(x)$. Under either real embedding the norm factor of a nonzero $x$ becomes $|\tau(x)|^2>0$, while the first factor has opposite signs at the two embeddings.

**Remark (use in the family).** At each member $D=\mathrm{Fm.D}(x,i)$, the family wrappers supply `gram0Def` at that member. The column wrapper `column_lemma_family_holds` passes it to `column_lemma_family_of_definite`, which uses the seventh lemma of `ConclusionOnFamily` and the actual level to give the pointwise intersection assertion `adm17`. The pointwise call passes the same $J$, its Hermitian proof and `IsDef` separately to `division_rows_rational_lattice`. The wrapper `stabiliser_family_of_column_lemma` supplies `Gram0Def` to `stabiliser_family_of_definite` alongside the pro-$g$ levels and the eventual `GBig` input at cutoff $3$. The latter gives `admF3` by evaluating `stabiliser_condition_of_level` at the family member. The main family call `stabF` invokes this wrapper with `levels_pro_g`. The pointwise theorem uses `adm17` via `stabZero_of_level`. The finite-order and prime-order arguments are in §6.4.12, and the local pro-$g$ transport is in §6.4.13.

**Remark (source boundaries).** The proof-body reading is pinned to A2, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. It covers the signature, descent, host Gram and wiring proofs identified in the source register. The signature geometry enters by the fields `X_sig` and `X_def` [Lean]. Standard-column existence, the host metric and the level charts retain their named supplies. The ordinary projection identification remains [Open]. [Source register](../sources/SOURCES.md#host-gram-definiteness)

### 6.4.15 Extending a real embedding to the host field: the algebraically closed lift

**Motivation.** The descent theorem of §6.4.14 begins by fixing a real embedding $\rho:F\hookrightarrow\mathbb R$ and choosing a complex embedding $\tau:E\hookrightarrow\mathbb C$ of the host field that restricts to $\rho$. In the archive this is the two-line theorem `exists_ext` (`JointsL.lean:489–492`), whose whole content is a call to Mathlib's `IsAlgClosed.lift`. §6.4.14 recorded the library implementation as unread. This subsection reads it at the pinned Mathlib commit `0df444a` and explains three things the consumer silently relies on: where the hypotheses of the lift come from in `gram0Def`, why the lifted map is injective, and why it restricts to $\rho$ on $F$. Nothing here reproves the Gram definiteness; the signature transport and the sign branches are cited from §6.4.14 and not reread.

**Worked examples [Expository].**

1. *Two conjugate choices.* Let $F=\mathbb Q(\sqrt2)$ with the real embedding $\rho(\sqrt2)=\sqrt2$, and let $E=F(i)=\mathbb Q(\sqrt2,i)$. Since $F\subset\mathbb R$, the polynomial $X^2+1$ has no root in $F$, so it is the minimal polynomial of $i$ over $F$. Transport it by $\rho$ to $\mathbb R[X]\subset\mathbb C[X]$: it is still $X^2+1$, with the two roots $\pm i$. Each root gives one extension of $\rho$,
   $\tau_{\pm}(u+vi)=\rho(u)\pm\rho(v)\,i\qquad(u,v\in F).$
   Both maps are ring homomorphisms, since $\rho$ is one and $(\pm i)^2=-1$; both restrict to $\rho$ on $F$ because $v=0$ there; and they differ, since $\tau_+(i)=i\ne-i=\tau_-(i)$. Any extension $\tau$ of $\rho$ satisfies $\tau(i)^2=\tau(i^2)=-1$, so $\tau(i)\in\{i,-i\}$ and $\tau$ is one of $\tau_\pm$. Existence holds, uniqueness fails, and the failure is exactly the set of roots of the transported minimal polynomial. For the Gram link of §6.4.14 take $J=[\sqrt2]$, $\sigma$ the complex conjugation of $E$ (so $\sigma(i)=-i$, $\sigma$ fixes $F$), and $x=u+vi$ with $u=1+2\sqrt2$, $v=-1+3\sqrt2$. Then $x\sigma(x)=u^2+v^2=(9+4\sqrt2)+(19-6\sqrt2)=28-2\sqrt2$, so the Hermitian value is
   $a=\sqrt2\,x\sigma(x)=28\sqrt2-4\in F.$
   Under $\rho$ it is $28\sqrt2-4\approx35.6>0$, and this is the real number $\overline{\tau_\pm(x)}\,\sqrt2\,\tau_\pm(x)=\sqrt2\,|\tau_\pm(x)|^2$ for either choice of sign. Under the other real embedding $\rho'(\sqrt2)=-\sqrt2$ the same $a$ becomes $-28\sqrt2-4<0$. The sign depends on $\rho$ and not on which of the two lifts of $\rho$ is used. Both $\tau_\pm$ satisfy $\tau_\pm(\sigma(y))=\overline{\tau_\pm(y)}$ for all $y\in E$; this is a property of the chosen $\sigma$ and is checked by hand on $y=i$, not supplied by the lift.

2. *Three complex embeddings, one real.* Let $F=\mathbb Q$ with $\rho$ the inclusion, and $E=\mathbb Q(\sqrt[3]2)$. The polynomial $X^3-2$ is irreducible over $\mathbb Q$ by Eisenstein's criterion at $2$, so it is the minimal polynomial of $\sqrt[3]2$ and $[E:\mathbb Q]=3$. In $\mathbb C$ it has the three roots $r_k=\omega^k\sqrt[3]2$ for $k=0,1,2$, where $\omega=(-1+\sqrt{-3})/2$. Each root gives one extension
   $\tau_k(a+b\sqrt[3]2+c\sqrt[3]4)=a+br_k+cr_k^2\qquad(a,b,c\in\mathbb Q),$
   and these are all of them, since a ring homomorphism is the identity on $\mathbb Q$ and is determined on $E$ by the image of the generator. Only $\tau_0$ has real image; $\tau_1$ and $\tau_2$ send $\sqrt[3]2$ to non-real numbers of modulus $\sqrt[3]2$. Here the real inclusion has one real extension and two nonreal extensions. For $\mathbb Q(i)/\mathbb Q$ the rational inclusion has no real extension because $X^2+1$ has no real root. The archive asks for $\tau:E\hookrightarrow\mathbb C$, never for $E\hookrightarrow\mathbb R$. The restriction identity $\tau_k|_{\mathbb Q}=\rho$ is automatic here because every ring homomorphism out of $\mathbb Q$ is the inclusion.

A pure Python script in the run directory checks the arithmetic of both examples numerically (34 assertions); it is a sanity check of the examples, not a certificate for the theorem below.

**Definitions.** Let $F$ and $E$ be fields with a ring homomorphism $\iota:F\to E$, written as an $F$-algebra structure on $E$. An element $b\in E$ is *algebraic* over $F$ if it is a root of a nonzero polynomial in $F[X]$, equivalently *integral*, that is a root of a monic polynomial; for fields the two notions agree. The extension $E/F$ is algebraic (`Algebra.IsAlgebraic F E`) if every element is. A field $K$ is *algebraically closed* (`IsAlgClosed K`, `Basic.lean:62–63`) if every polynomial over $K$ splits into linear factors; Mathlib derives from this that every polynomial of nonzero degree has a root (`exists_root`, `:78–79`) and that the image of any polynomial under a ring homomorphism into $K$ splits (`splits_domain`, `:66–68`).

Given a second $F$-algebra $K$, a *lift* (`IntermediateField.Lifts F E K`, `Extension.lean:35–39`) is a pair $(L,\varphi)$ of an intermediate field $F\subseteq L\subseteq E$ and an $F$-algebra homomorphism $\varphi:L\to K$. Lifts are partially ordered by $(L_1,\varphi_1)\le(L_2,\varphi_2)$ if $L_1\subseteq L_2$ and $\varphi_2$ restricts to $\varphi_1$ on $L_1$ (`:45–56`). The least lift is $(F,\mathrm{algebraMap})$ (`:58–63`).

A real embedding $\rho:F\hookrightarrow\mathbb R$ makes $\mathbb C$ an $F$-algebra through the composite $F\to\mathbb R\to\mathbb C$. In Lean this is `(Complex.ofRealHom.comp ι').toAlgebra` (`JointsL.lean:491`), and the structure map of the resulting algebra is literally this composite (`RingHom.algebraMap_toAlgebra`, `Defs.lean:205–207`, proved by `rfl`).

**Theorem (extension of a real embedding to an algebraic extension) [Lean, read].** Let $E/F$ be an algebraic extension of fields and $\rho:F\hookrightarrow\mathbb R$ a ring homomorphism. There is a ring homomorphism $\tau:E\to\mathbb C$ with $\tau(\iota(a))=\rho(a)$ for every $a\in F$. Every such $\tau$ is injective. If $E=F(\beta)$ is generated by one element with minimal polynomial $m_\beta$, the extensions of $\rho$ correspond bijectively to the roots of $\rho(m_\beta)$ in $\mathbb C$, so there are exactly $\deg m_\beta$ of them when $m_\beta$ is separable.

**Proof.** We follow the pinned Mathlib proof, which is the Zorn's lemma argument of Milne's Theorem 6.6 with the single-root step made explicit, and we indicate the Lean name of each step. Regard $\mathbb C$ as an $F$-algebra through $\rho$ as in the definitions; then an $F$-algebra homomorphism $\tau:E\to\mathbb C$ is a ring homomorphism with $\tau(\iota(a))=\mathrm{algebraMap}(a)=\rho(a)$, which is the statement `AlgHom.commutes` (`Hom.lean:203`). So it suffices to produce an $F$-algebra homomorphism.

*Step 1, one root at a time (`exists_lift_of_splits'`, `Extension.lean:208–221`).* Let $(L,\varphi)$ be a lift and let $s\in E$ be integral over $L$ with minimal polynomial $m\in L[X]$. Suppose the transported polynomial $\varphi(m)\in\mathbb C[X]$ splits. It has positive degree (`minpoly.degree_pos`), so it has a root $y\in\mathbb C$; Lean picks one with `rootOfSplits` (`Splits.lean:286–292`), which is `Classical.choose` applied to the existence statement `Splits.exists_eval_eq_zero` (`:274–283`). Make $\mathbb C$ an $L$-algebra through $\varphi$. The field $L(s)$ has the power basis $1,s,\dots,s^{d-1}$ with $d=\deg m$, and `PowerBasis.lift` (`PowerBasis.lean:287–293`) defines the $L$-linear map sending $s^j\mapsto y^j$; it is multiplicative and unital because $y$ satisfies the same monic relation $m$ as $s$ (the `constr_pow` lemmas), and it sends $s$ to $y$ (`lift_gen`, `:296–298`). Mathlib packages this as the bijection `algHomAdjoinIntegralEquiv` between $L$-algebra homomorphisms $L(s)\to\mathbb C$ and roots of $m$ in $\mathbb C$ (`Adjoin/Basic.lean:600–609`, via `liftEquiv'`, `PowerBasis.lean:326–331`). The resulting $\psi:L(s)\to\mathbb C$ is $L$-linear for the structure given by $\varphi$, which means $\psi(z)=\varphi(z)$ for $z\in L$ (`AlgHom.commutes` again); reassembling $(\varphi,\psi)$ into one $F$-algebra homomorphism on $L(s)$ is `algHomEquivSigma`. Hence $(L(s),\psi)$ is a lift above $(L,\varphi)$ containing $s$. When $s$ is integral over $F$ and its minimal polynomial over $F$ splits after transport by $\mathrm{algebraMap}:F\to\mathbb C$, the minimal polynomial over $L$ divides it and also splits after transport by $\varphi$ (`exists_lift_of_splits`, `:225–228`, using `minpoly_splits_tower_top'`); this is the form used below. Over $\mathbb C$ the splitting hypothesis is free: `IsAlgClosed.splits_domain`.

*Step 2, chains have upper bounds (`union`, `le_union`, `exists_upper_bound`, `Extension.lean:111–138`).* Let $c$ be a chain of lifts. The carriers form a directed family of intermediate fields, and their supremum $L'=\bigcup_{(L,\varphi)\in c}L$ is again an intermediate field because any two elements lie in a common member of the chain. Define $\varphi'$ on $L'$ by $\varphi'(z)=\varphi(z)$ for any member $(L,\varphi)$ with $z\in L$. This is well defined because for two members one restricts to the other. Lean builds $\varphi'$ with `Subalgebra.iSupLift`, whose compatibility obligation is discharged by the chain comparability `hc.total` (`:115–121`). The pair $(L',\varphi')$ is an upper bound of $c$ (`le_union`, `:124–130`). This is Milne's upper bound $(M',\varphi')$.

*Step 3, a maximal lift reaches everything (`exists_algHom_adjoin_of_splits`, `Extension.lean:297–303`).* Start from the least lift $(F,\mathrm{algebraMap})$. By Step 2 and Zorn's lemma in the form `zorn_le_nonempty_Ici₀`, there is a maximal lift $(L,\varphi)$ above it, and $\varphi$ restricts to the structure map on $F$ (`hfφ.2`). Let $s\in E$. Since $E/F$ is algebraic, $s$ is integral over $F$ (`Algebra.IsIntegral.isIntegral`, from `Algebra.IsAlgebraic`), and its minimal polynomial splits over $\mathbb C$. Step 1 gives a lift $(L_1,\psi)\ge(L,\varphi)$ with $s\in L_1$. Maximality gives $(L_1,\psi)\le(L,\varphi)$, hence $s\in L$. So $L=E$. Lean phrases this as $\mathrm{adjoin}\,F\,S\le L$ for the generating set $S$ and composes $\varphi$ with the inclusion; with $S$ the whole of $E$ (`adjoin_univ`, used by `nonempty_algHom_of_adjoin_splits`, `:316–317`, and `liftAux`, `Basic.lean:324–328`) the inclusion is the identity up to the canonical isomorphism $\top\cong E$. This is Milne's contradiction with maximality of $(M,\varphi)$ when $M\ne E$; the Lean proof reaches the same conclusion positively, as containment of every element.

*Step 4, the public name.* `IsAlgClosed.lift` (`Basic.lean:349–357`) is stated for an algebraic extension of domains $R\to S$ and an algebraically closed $R$-algebra $M$. For fields $R=F$, $S=E$ it routes through the fraction fields, which are copies of $F$ and $E$: it equips $\mathbb C$ and $\mathrm{FractionRing}\,E$ with $\mathrm{FractionRing}\,F$-algebra structures by `FractionRing.liftAlgebra` (`FractionRing.lean:752–760`), applies `liftAux` to the fraction fields, restricts scalars back to $F$ and composes with the canonical map $E\to\mathrm{FractionRing}\,E$. The algebraicity of the fraction fields is `FractionRing.isAlgebraic` (`Basic.lean:336–345`). The output is an element of $E\to_{\mathrm{alg}[F]}\mathbb C$ chosen by `Classical.choice`; nothing in the statement singles out one root, which is exactly the non-uniqueness of the examples.

*Injectivity.* Let $\tau:E\to\mathbb C$ be any ring homomorphism. Its kernel is a two-sided ideal of the field $E$. A field is a simple ring (`DivisionRing.isSimpleRing`), so the kernel is $0$ or all of $E$; the latter would force $\tau(1)=0$, contradicting $1\ne0$ in $\mathbb C$. Hence $\tau$ is injective. This is `RingHom.injective` (`SimpleRing/Basic.lean:67–70`), the lemma Mathlib also uses in `AlgEquiv.ofInjectiveField`. In `isDef_of_sig` injectivity enters once, as `hne`: a nonzero vector in $E^k$ has a nonzero coordinate, whose image under $\tau$ is nonzero.

*Restriction.* By construction $\tau$ is an $F$-algebra homomorphism for the structure induced by $\rho$, so `AlgHom.commutes` gives $\tau(\iota(a))=\mathrm{algebraMap}_{F\to\mathbb C}(a)$, and the right side unfolds by `rfl` to $(\rho(a):\mathbb C)$. This is the second component of `exists_ext` (`JointsL.lean:492`).

*Counting for a simple extension.* If $E=F(\beta)$, Step 1 applied to $(F,\mathrm{algebraMap})$ and $s=\beta$ shows that extensions of $\rho$ to $E$ are in bijection with roots of $\rho(m_\beta)$ in $\mathbb C$ (`algHomAdjoinIntegralEquiv`). The general statement that the images $\{\tau(x)\}$ of a fixed $x$ under all $F$-algebra homomorphisms $E\to\mathbb C$ are exactly the roots of its minimal polynomial is `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly_of_splits` (`Extension.lean:364–373`). For $X^2+1$ and $X^3-2$ this gives the two and three embeddings of the examples. $\square$

**Corollary (the premises in `gram0Def`) [Lean, read].** For an archive datum $D$ of type `D7`, with $F=D.\mathrm{host}.F$ and $E=D.\mathrm{host}.E$, the hypotheses of the theorem hold and `exists_ext` applies to every real embedding of $F$.

**Proof.** The field structures and the $F$-algebra structure on $E$ are fields of the host record. Algebraicity is not a stored field; it is derived in two steps at `JointsL.lean:544–545`. First, the CM datum stores the degree, `D.sp.cm.deg2 : finrank F E = 2` (`DataSpaces.lean:18`). The lemma `Module.finite_of_finrank_pos` (`Dimension/Free.lean:272–274`) turns a positive finite rank into the finiteness instance; its proof is the contrapositive of the convention that the finrank of a module that is not finitely generated is $0$, which is why a positive rank, and not merely a rank, is needed. Second, the instance `Algebra.IsAlgebraic.of_finite` (`Algebraic/Integral.lean:108–109`) gives algebraicity from finiteness: every element of a finite-dimensional algebra is integral (`IsIntegral.of_finite`, `IntegralClosure/Algebra/Basic.lean:64–66`, via the characteristic polynomial of multiplication), and integral elements are algebraic. This instance is what `isDef_of_sig` and then `exists_ext` pick up when `gram0Def` calls them. The remaining input of the lift is `IsAlgClosed ℂ`, Mathlib's fundamental theorem of algebra (`Complex.isAlgClosed`), cited as [Lean] without a proof-body reading. $\square$

**Remark (what the lift does not provide).** The descent theorem of §6.4.14 also assumes $\tau(\sigma b)=\overline{\tau(b)}$ for every complex embedding $\tau$. This is not a consequence of the lift. It is the second clause of the CM hypothesis `IsCMUnram` (`StatementMass.lean:44–48`), a universally quantified statement over all $\tau:E\to\mathbb C$ that the host record carries as an input, and `gram0Def` passes it through as `D.sp.cm.cmUnram.2.1` (`JointsL.lean:551–552`). The quantification over all $\tau$ is what makes the clause usable with the lift's arbitrary choice. The hypothesis is genuinely about $\sigma$: on $E=\mathbb Q(\sqrt2,i)$ the involution $\sigma'$ fixing $i$ and sending $\sqrt2\mapsto-\sqrt2$ is an automorphism of order two with fixed field $\mathbb Q(i)$, and for $\tau=\tau_+$ one has $\tau_+(\sigma'(\sqrt2))=-\sqrt2\ne\sqrt2=\overline{\tau_+(\sqrt2)}$. The same lift serves both involutions; only the CM one is compatible with conjugation.

**Remark (the two extensions give one sign).** Example 1 illustrates the general fact used in §6.4.14: the Hermitian value $H_J(x,x)$ lies in $\iota(F)$, so its image under any extension of $\rho$ is $\rho(a)$ and does not depend on the extension. For a quadratic CM host the two extensions of a given $\rho$ are $\tau$ and $\overline{\tau}$, and both compute the same real number. The archive never needs to compare them; it applies the signature hypothesis `hsig` at the one $\tau$ returned by `exists_ext`.

**Remark (source boundaries).** Lean readings are pinned to A2, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, and to Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, the manifest pin of the archive. Proof bodies read: `exists_ext`; the Zorn, chain-union and single-root steps `exists_algHom_adjoin_of_splits`, `union`, `le_union`, `exists_lift_of_splits'`, `exists_lift_of_splits`, `nonempty_algHom_of_adjoin_splits`, `liftAux`; `rootOfSplits` and `Splits.exists_eval_eq_zero`; `PowerBasis.lift`, `lift_gen`, `liftEquiv'`; `algHomAdjoinIntegralEquiv`; `RingHom.injective`; `Module.finite_of_finrank_pos`; `Algebra.IsAlgebraic.of_finite` and `IsIntegral.of_finite`; and the field case of `lift`. Statements read without proof bodies: `FractionRing.liftAlgebra` and `isScalarTower_liftAlgebra`, `FractionRing.isAlgebraic`, `minpoly_splits_tower_top'`, `algHomEquivSigma`, `Subalgebra.iSupLift`, `zorn_le_nonempty_Ici₀`, `Complex.isAlgClosed`. These are source-level readings of the pinned text; they are not a kernel check, and the inference of the algebraicity instance in `gram0Def` is read from the source, not replayed. The Lean proofs are by Thomas Browning, Junyan Xu and Kenny Lau and the Mathlib community; the archive wrapper is by Alpöge with Claude. The published argument is [Milne, *Fields and Galois Theory*, Theorem 6.6, p. 90](https://www.jmilne.org/math/CourseNotes/FT.pdf) and Stacks [Tag 09GU](https://stacks.math.columbia.edu/tag/09GU); Mathlib's chain formulation cites I. M. Isaacs, *Roots of polynomials in algebraic extensions of fields*, Amer. Math. Monthly 87 (1980), 543–544. [Source register](../sources/SOURCES.md#host-gram-definiteness)

### 6.4.16 Producing pure signatures from the host spaces

**Motivation.** In `gram0Def` the host space and its frame have already been chosen. Its stored signature must both be witnessed by the Gram matrix and be pure at each embedding. The constructor `hostSpacesOfNorm` produces these two certificates from the standard positive Hermitian form with an integral coordinate lattice. Its inclusion into the appropriate $Y_j$ is an isometry onto positive coordinate directions. The choice of this geometry comes before the extension of any real embedding. [Source register](../sources/SOURCES.md#production-of-pure-host-signatures)

#### Worked examples

For both examples let $F=\mathbb Q(a)$ with $a=\sqrt3$, $E=F(i)$ and $\sigma(u+iv)=u-iv$ for $u,v\in  F$. The two real embeddings are $\rho_s(a)=s\sqrt3$ for $s\in \{1,-1\}$. Over each, the embeddings $\tau_{s,d}(u+iv)=\rho_s(u)+di\rho_s(v)$ for $d\in \{1,-1\}$ exhaust the extensions, since the image of $i$ must square to $-1$. This checks total reality of $F$, total complexity of $E$, degree two, the fixed field $F$, and $\tau_{s,d}\sigma=\tau_{s,-d}=\overline{\tau_{s,d}}$. For the finite-prime clause in `CMData.cmUnram`, take $\theta=(a+i)/2$ and $t=\sigma(\theta)$. Their sum is $a$, their product is $1$, so both are integral by the monic equation $X^2-aX+1=0$ and transitivity of integrality. Their difference $i$ is a unit, hence outside every maximal ideal of $\mathcal O_E$. Conjugation preserves integrality by transporting a monic integer equation.

1. **Opposite signs at the two real places [Expository].** Start with $E^2$, coordinate frame $(e_1,e_2)$, and $h(x,y)=a(\sigma(x_1)y_1+\sigma(x_2)y_2)$. The form is Hermitian since $\sigma(a)=a$. Testing the coordinates gives nondegeneracy, and the dimension and recorded rank are both two. Take the lattice with $\mathcal O_E$-basis $b_1=(e_1+(1+i)e_2)/a$, $b_2=e_2$. The basis spans over $E$ since its coordinate determinant is $1/a$. Its Gram has entries $h(b_1,b_1)=3/a=a$, $h(b_1,b_2)=1-i$, $h(b_2,b_1)=1+i$, $h(b_2,b_2)=a$. The determinant is $3-2=1$, so the integral Gram has integral inverse and this finitely generated spanning lattice is its own Hermitian dual. The space frame remains $(e_1,e_2)$, where the Gram is $aI_2$. At each $\tau_{s,d}$, scale both coordinates by $1/\sqrt{\sqrt3}$ and relabel into the all-positive block for $s=1$ or the all-negative block for $s=-1$. This produces the two witnesses for each real place and checks `SigOK` and `IsDefinite` for this space. For the base rank $k=8$ of the next example take four orthogonal copies of this plane and its lattice. The four integral blocks still have determinant one. The rank relabeling preserves $J=aI_8$, with witnesses $(8,0)$ and $(0,8)$ at the two real places. For $x=(1+i,2,0,0,0,0,0,0)$ its descended value is $6a$, giving $6\sqrt3$ and $-6\sqrt3$. The full sign check follows from $\rho_s(h(x,x))=s\sqrt3\sum_\ell|\tau_{s,d}(x_\ell)|^2$ for every nonzero $x$. Thus the matrix meets the signature premise and the real-place sign conclusion of the base-Gram step. Both family proof inputs would use $aI_8$ and the same sign branch at each $\rho_s$ if these base data came from a family member. For the rank schedule in Example 2 the prescribed $Y_0$ has only one negative direction. At $\rho_{-1}$ an eight-dimensional negative space cannot embed isometrically into it. This example tests the base-signature interface only. A full `Spaces` record additionally requires the rank schedule and the $Y$-side comparisons.

2. **A positive-rank instance of the diagonal constructor [Expository].** Keep these fields and take the actual archive rank record `Examples₂.R0`, with $k=8$, $m=2$ and $t=15$ (here $t$ is the rank increment parameter). For the prime $T=5$ choose $p_z=2+i$. The norm is $(2-i)(2+i)=5$. The relative order $\mathcal O_F[\theta]$ has discriminant $(\theta-\sigma(\theta))^2=-1$. Its integral trace matrix on $(1,\theta)$ has determinant $-1$, so its trace dual is the order itself. Every integral element of $E$ lies in that trace dual, since its products with elements of the order have integral trace. Hence $(1,\theta)$ is an integral basis with unit discriminant. At each finite place the quadratic algebra is split or unramified by the discriminant criterion. [Milne, *Algebraic Number Theory*, Theorem 3.35](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

    In the split case the conjugation swaps factors and $(-1,1)$ has norm $-1$. In the field case the unit norm is surjective. In Milne's proof one lifts a residue norm preimage, then corrects modulo successive powers of the uniformizer using the surjective residue trace and takes the convergent product. Unit solutions at every place give an element of the finite adelic tensor algebra, with norm $-1$. This checks the remaining input of `spacesOfRanks` independently for this example. [Milne, *Class Field Theory*, III, Proposition 1.2 and its proof, p. 98](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

   | Grade $j$ | $N(j)=8+16j$ | $Y_j$ rank | $X_j$ signature at every $\tau_{s,d}$ | $Y_j$ signature at every $\tau_{s,d}$ |
   |---|---:|---:|---|---|
   | $0$ | $8$ | $9$ | $(8,0)$ | $(8,1)$ |
   | $1$ | $24$ | $24$ | $(24,0)$ | $(24,0)$ |
   | $2$ | $40$ | $39$ | $(40,0)$ | $(39,0)$ |

   The $X_j$ form is the sum of coordinate pairings in every grade, including grades above $m$. Coordinate tests give nondegeneracy, the coordinate frame gives the rank, and $\mathcal O_E^{N(j)}$ is self-dual because its Gram is the identity. `X_sig` uses the identity congruence and the positive-block index map at every embedding. The left equality witnesses `X_def` for $j\le 2$, and the rank column checks `X_rank`. At grade zero the first eight coordinates embed isometrically into $Y_0$ and $(2+i)e_9$ is orthogonal to them with norm $-5$. At grade one the isometry is the identity. At grade two $X'$ is the first $39$ coordinates and the remaining unit vector has norm one and is orthogonal to $X'$. The isometry $X'\to Y_2$ is the identity on the $39$ coordinates. There are zero hyperbolic pairs because $r_S=2/2-1=0$. The comparison spaces $W_1,W_2$ have rank $9$ with signatures $(8,1),(9,0)$. The finite adelic comparison from $Y_0$ to $W_1$ is the identity, and the comparison to $W_2$ multiplies the last coordinate by the norm-$-1$ element. The $V$ spaces have rank $24$ with their positive coordinate frames.

   The rank relabeling at grade zero gives $J=I_8$. For $x=(1+i,2,0,0,0,0,0,0)$ the descended value is $2+4=6$ at both real places and for either conjugate lift. For every nonzero $x$ the sum of coordinate squared moduli is strictly positive. In a family record using these spaces, both calls in the table below use $I_8$ and the positive-branch proof for that member. The calculation constructs the space data from the stated fields and prime. A full `Host R`, `D7` or `FamP` includes further arithmetic and comparison data. In particular the synthetic rank record's $R.f$ is $8$, whereas this illustrative field has degree two. The space constructor itself has no equation between those two quantities.

#### Definitions and conditional existence theorem

An `HSpace E` stores a finite-dimensional $E$-space, a nondegenerate Hermitian form (conjugate-linear first), a rank and its dimension equality, a frame indexed by that rank, a signature function on complex embeddings, and a spanning finitely generated unimodular $\mathcal O_E$-lattice. For a frame Gram $G$ of rank $r$, a signature witness at $\tau$ for $(p,q)$ consists of an index bijection to $\mathrm{Fin}(p)\sqcup\mathrm{Fin}(q)$ and an invertible complex congruence matrix $P$ taking the relabeled $\tau(G)$ to $\operatorname{diag}(I_p,-I_q)$ by conjugate transpose on the left. In particular $p+q=r$. The rank count, complex congruence and choice of sign are distinct pieces of information. [A2, `DataSpaces.lean:29–69` and `SatakeDualWeyl/Statement.lean:483–486`](../sources/SOURCES.md#production-of-pure-host-signatures)

For a supplied `Spaces R F E`, the exact order of quantifiers is

- `X_sig` for every natural grade $j$ and every complex embedding $\tau$, with a signature witness for the stored pair.
- `X_rank` for each $j\le  m$, with rank $N(j)=k+j(t+1)$.
- `X_def` for each $j\le  m$ and each $\tau$, with stored pair $(N(j),0)$ or $(0,N(j))$ by the preceding rank equality. The disjunction is inside the embedding quantifier.
- `cmUnram.2.1` for every $\tau$ and every $b\in  E$, with $\tau(\sigma b)=\overline{\tau(b)}$. The extension used by a consumer may be chosen after $\rho$ is fixed.

**Theorem (conditional space construction and signature supply) [Lean, read].** Fix a rank record $R$ and a quadratic CM datum $E/F$ as in `CMData`. Assume conjugation preserves $\mathcal O_E$, a rational prime $T$ and $p_z\in  E$ with $\sigma(p_z)p_z=T$ are given, and in $E\otimes_F\mathbb A_{F,f}$ there is an element $y$ of norm $\sigma(y)y=-1$, with $\sigma$ acting on the $E$ factor. Then the diagonal construction `spacesOfRanks` gives a `Spaces R F E` with every $X_j$ equal to the positive standard Hermitian space of dimension $N(j)$ with its coordinate lattice. For every $j$ and every $\tau:E\hookrightarrow\mathbb C$, its Gram image has witnessed signature $(N(j),0)$. In particular the three $X$ conditions above hold. For a supplied `Host R` and level norm element, `hostSpacesOfNorm` invokes this construction, obtaining the CM datum and the [finite adelic norm witness](#6417-producing-the-finite-adelic-element-of-norm-minus-one) from the host.

For any $D:\mathrm{D7}$ carrying these spaces, the grade-zero conclusion `Gram0Def D` holds on the matrix $J=D.\mathrm{sp}.\mathrm{gram0}$, called the base Gram. More generally for a supplied $D$ with the three $X$ fields, for every real embedding $\rho:F\hookrightarrow\mathbb R$ there is a sign $\epsilon_\rho\in \{1,-1\}$ such that for every nonzero $x\in  E^k$ there is $b\in  F$ with $h_J(x,x)=\iota(b)$ and $\epsilon_\rho\rho(b)>0$. The sign is positive for the diagonal construction and can vary with $\rho$ for the general signature interface. For $k>0$ the sign at a real place is unique. The signature and the conclusion use the same base frame and form. [A2, `BaseFormAnisotropicOrthogonalSingle.lean:325–386`, `RankRecordRowDimensionZero.lean:137–142`, `JointsL.lean:542–565`](../sources/SOURCES.md#production-of-pure-host-signatures)

#### Proof

**Produce the space and its integral lattice.** Choose each coordinate space and form before choosing any embedding. In the proof term `stdSpace`, a Boolean function selects the diagonal entries $d_i=\pm1$. The form is $h(x,y)=\sum_i\sigma(x_i)d_i y_i$. Each $d_i$ is fixed by conjugation. Swapping the arguments and conjugating verifies symmetry. Testing against a coordinate vector on either side isolates a coordinate times a unit and proves nondegeneracy. The frame vectors generate a finite lattice and span over $E$. For any vector in the Hermitian dual, testing against each frame vector gives integral coordinates because conjugation preserves integrality and $d_i$ is a unit. The reverse inclusion follows by summing integral products. In Lean `stdLat_unimod` uses `hermDual` with diagonal determinant a product of signs, whose inverse is the same product. [A2, `SpanPowerMembership/Spaces.lean:18–148`](../sources/SOURCES.md#production-of-pure-host-signatures)

**Place $X$ inside the host geometry.** Set all $d_i=1$ for each $X_j$. For $Y_j$ use the last $q_j=\lfloor(m-j)/2\rfloor$ coordinates as negative, with natural subtraction. The rank inequality in `rk_XY` puts the $N(j)$ coordinates within the positive block for $j<m$. In `extLE_isom`, split the pairing sum into the original coordinates and the appended ones. The latter are zero by the zero extension. The first sum is unchanged by agreement of the diagonal signs. In $X_m$, $X'$ has codimension one, so the complementary last coordinate has norm one. At $j=m$ there is no negative tail in $Y_m$, whose rank is that of $X'$. At grade zero, put $p_z$ in the first negative coordinate. This gives norm $-T$ and orthogonality to the positive initial block. Pair each remaining negative vector $f$ with a disjoint positive vector $e$ outside $X_0$. The vectors $e+f$ and $(e-f)/2$ have self-pairings zero and mutual pairing one. Disjoint supports give the required cross-pairings and orthogonality to the image of $X_0$ and to the norm-$-T$ vector. This is the geometric calculation in `hyperbolic_basis_dual_pairing` and its neighboring lemmas. The resulting $Y_0$ has $k+r_S$ positive and $1+r_S$ negative coordinates, where $r_S=m/2-1$. [A2, `BaseFormAnisotropicOrthogonalSingle.lean:69–108,167–195,207–323,333–367`](../sources/SOURCES.md#production-of-pure-host-signatures)

For $1\le  j\le  m$ take $W_j$ of rank $k+m-1$ with $m-j$ negative coordinates. The local comparison is the explicit diagonal congruence `dSpace_congr`. On a matching coordinate use multiplier $1$. Where a sign must change use $y$, with inverse $-\sigma(y)$ from the norm equation. The conjugate diagonal entries then multiply the source diagonal coefficient by $-1$ exactly where required. The $V$ spaces have the positive standard frame of rank $R.nV$. These choices fill out the space record, including its finite adelic comparison. In the host wrapper `cmData H` packages total reality, quadraticity, the fixed field and compatible conjugation using the host. The wrapper installs the host star and rewrites the supplied $p_z H.\mathrm{conj}(p_z)=T$ as the norm equation above. It calls [`exists_adelic_neg_one`](#6417-producing-the-finite-adelic-element-of-norm-minus-one) before passing the finite adelic witness to the constructor. [A2, `BaseFormAnisotropicOrthogonalSingle.lean:117–164,368–386`, `ExampleLayerExistsGenerators.lean:126–145`, `RankRecordRowDimensionZero.lean:137–142`](../sources/SOURCES.md#production-of-pure-host-signatures)

**Produce the signature witness.** The calculation of the frame Gram in `stdSpace_gram_apply` leaves only the matching coordinate term. In `posSpace_sigOK`, introduce an arbitrary $\tau$ and map the entries. A ring homomorphism preserves $0$ and $1$, so the image is the identity. In `stdform_sig_one`, enumerate the coordinates as the positive block with an empty negative block and take $P=I$. The diagonal and off-diagonal entries are then those of $I$. For the signed-tail spaces the same argument identifies the two blocks with the positive prefix and negative tail, again with $P=I$. Hence the chosen signature function on $X_j$ is certified for all $\tau$ and $j$. The left branch of `X_def` and the equality `X_rank` are by definition. The proof also works with an empty index set in the positive-space lemma. The actual $R$ has $k\ge  m+3$ and $m\ge 2$. [A2, `Spaces.lean:144–164`, `Stdform.lean:229–233`, `BaseFormAnisotropicOrthogonalSingle.lean:25–67,325–332`](../sources/SOURCES.md#production-of-pure-host-signatures)

**Use the fixed base Gram.** The order in the proof term is to construct the spaces from the supplied host and norm data, use grade $0$ and the stored frame, and relabel via $N(0)=k$. When `gram0Def` discharges the signature premise it takes an arbitrary $\tau$, obtains the witness `X_sig 0 τ`, selects the branch from `X_def 0` at that $\tau$, and relabels the corresponding occupied block. The inherited deduction of §§6.4.14–15 then fixes any $\rho$, chooses an extension $\tau$, selects the sign once for the entire place, and applies the fixed-field and sign conclusions to each nonzero $x$. At a fixed $\rho$, the descended $b$ is independent of the extension. Evaluating it on any one nonzero vector shows that two conjugate lifts force the same branch when $k>0$. This proves the quantified conclusion. [A2, `DataLevel.lean:48–52,77–80`, `JointsL.lean:542–565`](../sources/SOURCES.md#production-of-pure-host-signatures)

| Call on a family member $D=\mathrm{Fm.D}(x,i)$ | Base-form input | Consumer |
|---|---|---|
| `column_lemma_family_holds` | `gram0Def D` on `D.sp.gram0` | `column_lemma_family_of_definite`, using the column hypotheses to obtain `adm17` |
| `stabiliser_family_of_column_lemma` | `gram0Def D` on that same `D.sp.gram0` | `stabiliser_family_of_definite`, with the pro-$g$ levels and eventual `GBig`, to obtain `admF3` |

Both wrappers pass the proof pointwise. There is no change of Gram or choice of a new space in either wrapper. $\square$ [A2, `JointsF.lean:16–18`, `JointsL.lean:571–573,1169–1172`](../sources/SOURCES.md#production-of-pure-host-signatures)

**Remarks on scope.** The archive also has a diagonal geometric variant `spL`. Its record update replaces the second vector in each hyperbolic pair by the corresponding trace-one construction and changes the related pairing proofs. It inherits the $X$ fields directly from `spacesOfRanks`. For a general $D$ the family wrappers take its `Spaces` as supplied and use the two signature fields without requiring this diagonal presentation. The construction theorem begins with a rank record, CM host data and the indicated norms. In particular, availability of the level norm element for an arbitrary prime and the other arithmetic hypotheses for a full family are separate inputs. The ordinary projection identification remains [Open]. The source register gives the proof-body boundary and the fixed archive hash. [Source register](../sources/SOURCES.md#production-of-pure-host-signatures)

### 6.4.17 Producing the finite adelic element of norm minus one

**Motivation.** §6.4.16 showed that the diagonal constructor `spacesOfRanks` builds the host spaces once it is given, besides the CM datum and the level norm element, one more input: an element $y$ of $E\otimes_F\mathbb A_{F,f}$ with $(\sigma\otimes\mathrm{id})(y)\,y=-1$. The constructor spends $y$ only in the finite adelic comparison `dSpace_congr`, where scaling a coordinate by $y$ changes the sign of its diagonal entry. The host wrapper `hostSpacesOfNorm` obtains $y$ from `exists_adelic_neg_one`, which [§6.4.16](#6416-producing-pure-signatures-from-the-host-spaces) uses as an input. At first sight the input looks impossible. If $x\in E^\times$ and $\tau$ extends a real embedding $\rho$ of $F$, the CM clause $\tau\circ\sigma=\overline{\tau}$ gives $\rho(\sigma(x)x)=\overline{\tau(x)}\,\tau(x)=|\tau(x)|^2>0$, so $-1$ is never of the form $\sigma(x)x$. The finite adeles have no real component, so there is no contradiction, but the statement is genuinely about the finite places, and it fails for some CM extensions (Example C below). This subsection reads the archive's proof. It does not invoke local class field theory. A host field contains square roots of $-q$ and $-d$ for two distinct primes $q\equiv d\equiv3\pmod4$, so it carries two integral binary norm forms, of discriminants $-d$ and $-q$. At every finite place at least one of them is unimodular, and a unimodular binary form over the valuation ring of a local field represents every unit, in particular $-1$. The proof chooses such local solutions, checks that they are integral at almost all places, and assembles them into one element of the tensor product. [Source register](../sources/SOURCES.md#finite-adelic-norm-minus-one)

#### Worked examples

In this subsection $q$ and $d$ always denote the two host primes, not the signature index of §6.4.14 or the sign $d$ of §6.4.16. For the examples take $q=571$ and $d=599$, the primes of the archive's example host `H0` (`ExampleLayerExistsGenerators.lean:172–174,207–217`). They satisfy every clause of `HostHyp`: both are prime, $571\equiv3\pmod8$, $599\equiv7\pmod{16}$, and $(-599/571)=1$, as Example A shows by exhibiting the square root. Let $E_0=\mathbb Q(\omega_q,\omega_d)$ with $\omega_q^2=-571$ and $\omega_d^2=-599$, and let $\sigma$ be complex conjugation, which negates both roots. Its fixed field is $F_0=\mathbb Q(\omega_q\omega_d)$, and $(\omega_q\omega_d)^2=571\cdot599=342029$. So $E_0/F_0$ is a CM extension with the three properties (U1)–(U3) that the proof uses, listed in the definitions below. $E_0$ has degree $4$ and is not itself a host record: a host field is Galois over $\mathbb Q$ with group isomorphic to the record's `GG`, of order $4\cdot2^e$ with $e\ge2$ (`ConjEMemHostFIff.lean:18,26–27`, `FrobeniusOrbits/Statement.lean:24–29`). The archive's `H0` has the same $q$ and $d$, and its fields `sqq` and `sqd` satisfy the same two equations (`exampleSqrt_sq`, `:276–280`, records $\omega_d^2=-599$), so it contains a copy of $E_0$.

Put $N_d=(d+1)/4=150$, $N_q=(q+1)/4=143$, $\vartheta=(1+\omega_d)/2$, $\vartheta_q=(1+\omega_q)/2$, $\beta=\omega_q/\omega_d$ and $\alpha=(1-\beta)/2$. Since $\sigma(\vartheta)=1-\vartheta$ and $\vartheta(1-\vartheta)=N_d$, the norm of $s+\vartheta t$, for $s,t$ in any commutative $F_0$-algebra, is $Q_d(s,t)=s^2+st+150t^2$. Likewise the norm of $s+\vartheta_qt$ is $Q_q(s,t)=s^2+st+143t^2$. Both $571$ and $599$ divide the discriminant $342029\equiv1\pmod4$ of $F_0$, so each has a single place of $F_0$ above it, $v_{571}$ and $v_{599}$, with residue fields $\mathbb F_{571}$ and $\mathbb F_{599}$.

**Example A (a split place, $v_{571}$) [Expository].** Here $599\notin v_{571}$, so the proof uses $Q_d$, whose discriminant $1-4\cdot150=-599$ is a unit at $v_{571}$. Its residue polynomial $X^2+X+150$ has the root $31$ in $\mathbb F_{571}$, because $31^2+31+150=1142=2\cdot571$. The derivative $2\cdot31+1=63$ is a unit, so Hensel's lemma lifts $31$ to a root $r\in\mathbb Z_{571}\subset\mathcal O_{v_{571}}$ of $X^2+X+150$, and $v_{571}$ splits in $E_0$. Put $\delta=1+2r$. Then $\delta^2=1+4(r^2+r)=-599$ and $\delta\equiv63\pmod{571}$, which shows $(-599/571)=1$. One Newton step can be done by hand. From $63^2+599=4568=8\cdot571$, the lift $\delta\equiv63+571k$ needs $8+126k\equiv0\pmod{571}$, and $k=9$ works because $8+126\cdot9=1142=2\cdot571$. So $\delta\equiv5202\pmod{571^2}$. The archive's split formula, with target $-1$, takes $t=(-1-1)/\delta$ and $s=1+rt$, that is, $s=1/\delta$ and $t=-2/\delta$. Then $Q_d(s,t)=(1-2+600)/\delta^2=599/(-599)=-1$. Modulo $571$ one has $63^{-1}\equiv426$, since $63\cdot426=26838=47\cdot571+1$, so $(s,t)\equiv(426,290)\pmod{571}$. Both coordinates lie in $\mathcal O_{v_{571}}$, as the theorem requires at a place not dividing $d$. The local component of $y$ is $s+\vartheta t=(1-2\vartheta)/\delta=-\omega_d/\delta$. Under $E_0\otimes_{F_0}F_{0,v_{571}}\cong F_{0,v_{571}}\times F_{0,v_{571}}$, $\omega_d\mapsto(\delta,-\delta)$, this element becomes $(-1,1)$. The map $\sigma\otimes\mathrm{id}$ swaps the two factors, so $(\sigma\otimes\mathrm{id})(y_v)\,y_v=(1,-1)(-1,1)=-1$. This is the split-place element $(-1,1)$ that §6.4.16, Example 2, used by hand; here the archive's formula produces it.

**Example B (a non-split permitted place, $v_{599}$) [Expository].** Here $599\in v_{599}$, so $Q_d$ is not unimodular and the proof switches to $Q_q$, whose discriminant $-571$ is a unit at $v_{599}$. The residue polynomial $X^2+X+143$ has discriminant $-571$. By quadratic reciprocity for $7\equiv599\equiv3\pmod4$, $(-571/599)=(28/599)=(7/599)=-(599/7)=-(4/7)=-1$. So the polynomial has no root in $\mathbb F_{599}$, the place $v_{599}$ is inert in $E_0$, and the proof takes the no-root branch. That branch first solves $a^2+ab+143b^2\equiv-1\pmod{599}$ in the residue field. One solution is $(a,b)=(34,2)$, since $34^2+34\cdot2+143\cdot4=1796=3\cdot599-1$. In the archive's odd-characteristic route this pair corresponds to $x=2a+b=70$ and $y=b=2$, with $x^2+571y^2=7184=12\cdot599-4$. The partial derivative $2a+b=70$ is a unit, so the proof keeps $t=2$ and lifts $s$ from $34$ as a root of $f(X)=X^2+2X+573$. Indeed $f(34)=1797=3\cdot599$ and $f'(34)=70$. Since $-572=4\cdot(-143)$, the roots of $f$ are $-1\pm2\lambda$ with $\lambda^2=-143$. The square root exists in $\mathbb Z_{599}$ with $\lambda\equiv317\pmod{599}$, because $317^2=100489=167\cdot599+456$ and $456\equiv-143$, and the root congruent to $34$ is $-1+2\lambda$, since $2\cdot317-1=633\equiv34$. A Newton step uses $317^2+143=168\cdot599$, $2\cdot317\equiv35\pmod{599}$ and $168+35\cdot115=4193=7\cdot599$, so $\lambda\equiv69202\pmod{599^2}$. Thus $(s,t)=(2\lambda-1,2)$ and $Q_q(s,t)=4\lambda^2+571=-1$. The proof then converts to the coordinates of $Q_d$ by $(s_v,t_v)=(s+\alpha t,\beta t)=(2\lambda-\beta,2\beta)$, and $Q_d(s_v,t_v)=4\lambda^2+599\beta^2=4\lambda^2+571=-1$. Here $\beta=\omega_q\omega_d/\omega_d^2=-\varpi/599$ with $\varpi=\omega_q\omega_d$. Since $599$ ramifies in $F_0$, $\varpi$ is a uniformizer of $F_{0,v_{599}}$ and $599$ has valuation $2$, so $\beta$ has valuation $-1$. Hence $s_v$ and $t_v$ are not integral at $v_{599}$, and the theorem asserts integrality only at places not dividing $d$. The local component of $y$ is still integral: $s_v+\vartheta t_v=2\lambda+\beta\omega_d=2\lambda+\omega_q$, a unit of norm $4\lambda^2+571=-1$.

The numbers $r$, $\delta$ and $\lambda$ are $p$-adic integers and $\alpha,\beta$ lie in $F_0$. So the same pairs solve the local equations at every place above $571$ or $599$ of any field satisfying (U1)–(U3) with these primes, for instance the real subfield of `H0`, which contains $\beta$. Which branch the archive's proof takes at such a place depends on the residue field there.

**Example C (outside the hypotheses: $\mathbb Q(\omega_d)/\mathbb Q$) [Expository].** Let $F=\mathbb Q$ and $E=\mathbb Q(\omega_d)$ with $\omega_d^2=-599$, a CM extension with the root $\omega_d$ but no second root $\omega_q$ for a prime $q\ne599$, so (U2) fails. At every prime $p\ne599$, including $p=2$ because $-599$ is odd, $Q_d$ is unimodular and Lemma 2 below gives a local solution. At $p=599$ there is none. Suppose $s^2+st+150t^2=-1$ with $s,t\in\mathbb Q_{599}$, and put $u=2s+t$, so that $u^2+599t^2=-4$. If $u=0$, the left side has odd valuation and $-4$ has valuation $0$, which is impossible. If $t\ne0$ and $u\ne0$, the valuations $2v(u)$ and $1+2v(t)$ have different parity, so the valuation $0$ of the sum is the smaller one, forcing $v(u)=0$ and $v(t)\ge0$. If $t=0$, then $v(u)=0$ directly. In every case $u$ is a unit with $u^2\equiv-4\pmod{599}$, so $-1\equiv(u/2)^2$ would be a square in $\mathbb F_{599}$, which is false because $599\equiv3\pmod4$. Hence $\mathbb Q(\omega_d)/\mathbb Q$ has no finite adelic element of norm $-1$. In Hilbert-symbol terms $(-1,-599)_{599}=(-1/599)=-1$ ([Serre, *A Course in Arithmetic*, III, Proposition 1, p. 19 and Theorem 1, p. 20](https://doi.org/10.1007/978-1-4684-9884-4)). The obstruction sits exactly where the proof below switches from $Q_d$ to $Q_q$; without $\omega_q$ there is no second form.

A pure-Python script in the run directory checks the integer arithmetic of the three examples (residues, Newton steps, Legendre symbols and the displayed products). It is a check of the examples, not a certificate for the theorem.

#### Definitions

**Places and completions.** Let $F$ be a number field with ring of integers $\mathcal O_F$. A finite place $v$ is a nonzero prime ideal $\mathfrak p_v$ of $\mathcal O_F$, an element of Mathlib's `HeightOneSpectrum (𝓞 F)`. Write $F_v$ for the completion (`v.adicCompletion F`), $\mathcal O_v$ for its valuation ring (`v.adicCompletionIntegers F`), $\mathfrak m_v$ for the maximal ideal and $k_v$ for the residue field. For an integer $n$ write $v\mid n$ when $n\in\mathfrak p_v$.

**Finite adeles.** The finite adele ring is
$\mathbb A_{F,f}=\{(x_v)_v\in\prod_vF_v : x_v\in\mathcal O_v\text{ for all but finitely many }v\}$
with componentwise operations. In Mathlib it is `FiniteAdeleRing (𝓞 F) F`, the restricted product of the $F_v$ with respect to the $\mathcal O_v$ along the cofinite filter, and two elements are equal when all their components are (`RestrictedProduct.ext`). Only finite places occur. [Mathlib, `FiniteAdeleRing.lean:86–95`, `RestrictedProduct/Basic.lean:79,112–114`](../sources/SOURCES.md#finite-adelic-norm-minus-one)

**The base change of $\sigma$.** For an $F$-algebra $E$ and an $F$-algebra homomorphism $\sigma:E\to E$, the archive's `sigR σ` is $\sigma\otimes\mathrm{id}$ on $E\otimes_F\mathbb A_{F,f}$. It fixes every $1\otimes a$ and sends $x\otimes1$ to $\sigma(x)\otimes1$. The norm equation of §6.4.16 is $(\sigma\otimes\mathrm{id})(y)\,y=-1$. [A2, `SatakeDualWeyl/Statement.lean:88–89`](../sources/SOURCES.md#finite-adelic-norm-minus-one)

**The host data used.** A host record `H : Host R` contains a CM number field $E$ with the involution $c=$ `H.conj` and the subfield $F=$ `maximalRealSubfield E`. It contains two primes $q=$ `H.q` and $d=$ `H.d` with `HostHyp q d`: $q$ and $d$ are prime, $q\equiv3\pmod8$, $d\equiv7\pmod{16}$ and $(-d/q)=1$. It contains elements $\omega_q=$ `H.sqq` and $\omega_d=$ `H.sqd` with $\omega_q^2=-q$ and $\omega_d^2=-d$. An automorphism $g$ of $E$ multiplies $\omega_q$ and $\omega_d$ by the two signs in the first component of its image in the record's group (`gal_sqq`, `gal_sqd`), and $c$ is the automorphism with image $((-1,-1),1)$ (`Frame.cc`), so $c(\omega_q)=-\omega_q$ and $c(\omega_d)=-\omega_d$ (`adel_conj_aE`, `adel_conj_bE`). [A2, `ConjEMemHostFIff.lean:13–31,58,64`, `DataHost.lean:39–44`, `FrobeniusOrbits/Statement.lean:13–14,35`, `ZsmulGeneratorEqZeroOfProjection.lean:102`](../sources/SOURCES.md#finite-adelic-norm-minus-one)

**The three facts the proof uses.**

- (U1) $q$ and $d$ are distinct primes with $q\equiv3\pmod8$ and $d\equiv7\pmod{16}$. This is part of `HostHyp`, and only $4\mid q+1$, $4\mid d+1$, $q\ne d$, the resulting coprimality and $d\ne0$ are used.
- (U2) $\omega_q^2=-q$, $\omega_d^2=-d$, $c(\omega_q)=-\omega_q$ and $c(\omega_d)=-\omega_d$.
- (U3) Every $c$-fixed element of $E$ lies in $F$.

**The two forms.** Put $N_d=(d+1)/4$ and $N_q=(q+1)/4$ (`adelNd`, `adelNq`), $\vartheta=(1+\omega_d)/2$ (`adelTheta`), $\beta=\omega_q/\omega_d$ (`adelBeta`) and $\alpha=(1-\beta)/2$ (`adelAlpha`). For elements $T,N$ of a commutative ring $B$ define $Q_{T,N}(s,t)=s^2+Tst+Nt^2$ for $s,t\in B$, with discriminant $T^2-4N$, and write $Q_d=Q_{1,N_d}$ and $Q_q=Q_{1,N_q}$. Their discriminants are $1-4N_d=-d$ and $1-4N_q=-q$. Call $Q_{T,N}$ unimodular over a local ring when its discriminant is a unit there.

#### Lemmas

**Lemma 1 (the algebra in $E$) [Lean, read].** Assume (U1)–(U3). Then $4N_d=d+1$, $4N_q=q+1$, $c(\vartheta)=1-\vartheta$, $\vartheta(1-\vartheta)=N_d$, $\beta\in F$, $2\alpha+\beta=1$ and $\alpha^2+\alpha\beta+N_d\beta^2=N_q$. Consequently, in every commutative $F$-algebra, $Q_d(s+\alpha t,\beta t)=Q_q(s,t)$, and $(s+\alpha t)+\vartheta\beta t=s+\vartheta_qt$.

*Proof.* The congruences $q\equiv3\pmod8$ and $d\equiv7\pmod{16}$ give $4\mid q+1$ and $4\mid d+1$ (`adelNq_spec`, `adelNd_spec`). Next, $c(\vartheta)=(1-\omega_d)/2=1-\vartheta$ and $\vartheta(1-\vartheta)=(1-\omega_d^2)/4=(1+d)/4$. The quotient $\beta$ is $c$-fixed because $c(\omega_q)/c(\omega_d)=(-\omega_q)/(-\omega_d)$, so $\beta\in F$. For a host, the fixed-field step is `adel_mem_F`: if $c(x)=x$ then every complex embedding $\psi$ satisfies $\overline{\psi(x)}=\psi(c(x))=\psi(x)$ by `conjE_apply`, which is the defining condition of the maximal real subfield. The linear relation is the definition of $\alpha$. For the quadratic one, $\alpha^2+\alpha\beta+N_d\beta^2=\tfrac14+\beta^2(N_d-\tfrac14)=\tfrac14+\tfrac{d}{4}\beta^2=\tfrac{1+q}{4}$, because $\beta^2d=q$. Expanding $Q_d(s+\alpha t,\beta t)=s^2+(2\alpha+\beta)st+(\alpha^2+\alpha\beta+N_d\beta^2)t^2$ gives the first consequence. The second follows from $\alpha+\beta\vartheta=\tfrac12+\tfrac12\beta\omega_d=\tfrac12(1+\omega_q)$. $\square$ [A2, `Adelic.lean:289–324,342–396`](../sources/SOURCES.md#finite-adelic-norm-minus-one)

**Lemma 2 (a unimodular binary form represents every unit) [Lean, read].** Let $S$ be a Henselian local ring with maximal ideal $\mathfrak m$ and finite residue field $k$. Let $T,N\in S$ with $T^2-4N\in S^\times$ and let $u\in S^\times$. Then $s^2+Tst+Nt^2=u$ for some $s,t\in S$.

*Proof.* Write bars for residues and $D=T^2-4N$. *Case 1: $X^2+\bar TX+\bar N$ has a root in $k$.* Lift it to $r_0\in S$ and put $g=X^2+TX+N$. Then $g(r_0)\in\mathfrak m$, and $(2r_0+T)^2=D+4g(r_0)$ has unit residue, so $g'(r_0)=2r_0+T$ is a unit. Hensel's lemma gives a root $r$ of $g$. Since $(T+2r)^2=D$, $T+2r$ is a unit. Put $t=(u-1)/(T+2r)$ and $s=1+rt$. Then
$s^2+Tst+Nt^2=1+(T+2r)t+(r^2+Tr+N)t^2=u.$

*Case 2: no residue root.* Then $\bar N\ne0$, since otherwise $0$ is a root, so $N$ is a unit. The residue form represents $\bar u$. In characteristic $2$ every element of the finite field $k$ is a square, and $(\sqrt{\bar u},0)$ works. In odd characteristic the two quadratic polynomials $X^2$ and $-\bar DX^2-4\bar u$ have values whose sum vanishes somewhere, by counting: each takes $(|k|+1)/2$ values. This gives $x^2-\bar Dy^2=4\bar u$, and $(a,b)=((x-\bar Ty)/2,y)$ satisfies $a^2+\bar Tab+\bar Nb^2=\bar u$. Lift $(a,b)$ to $(s_0,t_0)$. The two partial derivatives $2s_0+Tt_0$ and $Ts_0+2Nt_0$ cannot both lie in $\mathfrak m$. Otherwise the residue identities $\bar D\bar t_0=\bar T(2\bar s_0+\bar T\bar t_0)-2(\bar T\bar s_0+2\bar N\bar t_0)$ and $\bar D\bar s_0=\bar T(\bar T\bar s_0+2\bar N\bar t_0)-2\bar N(2\bar s_0+\bar T\bar t_0)$ force $\bar s_0=\bar t_0=0$ and $\bar u=0$. If $2s_0+Tt_0$ is a unit, keep $t=t_0$ and apply Hensel's lemma to the monic $X^2+Tt_0X+(Nt_0^2-u)$ at $s_0$. Otherwise keep $s=s_0$, apply it to $X^2+TN^{-1}s_0X+N^{-1}(s_0^2-u)$ at $t_0$, whose derivative there is $N^{-1}(Ts_0+2Nt_0)$, and multiply the resulting identity by $N$. $\square$ [A2, `UnimodUnramUnique.lean:14–138`; Mathlib, `Henselian.lean:108–111`, `Finite/Basic.lean:81–98,764`](../sources/SOURCES.md#finite-adelic-norm-minus-one)

The classical counterparts are Hensel's lemma for simple zeros and the fact that a binary quadratic form over a finite field of odd characteristic represents every nonzero element ([Serre, *A Course in Arithmetic*, II, Theorem 1 and Corollary 1, pp. 14–15; IV, Proposition 4, p. 34](https://doi.org/10.1007/978-1-4684-9884-4)). The bracketed proof of Serre's Proposition 4 is the same counting as Mathlib's `exists_root_sum_quadratic`. Lemma 2 is the degree-two case of the surjectivity of the unit norm in unramified extensions ([Milne, *Class Field Theory*, III, Proposition 1.2, p. 98](https://www.jmilne.org/math/CourseNotes/CFT.pdf)), but the archive does not use Milne's filtration argument. It needs only the explicit form and one application of Hensel's lemma.

**Lemma 3 (the local rings) [Lean, read].** For every finite place $v$ of $F$, $\mathcal O_v$ is complete for its $\mathfrak m_v$-adic topology and is therefore a Henselian local ring. Its residue field is finite, and an element of $\mathcal O_F$ outside $\mathfrak p_v$ is a unit of $\mathcal O_v$. Hence if $T,N\in\mathbb Z$ and $v\nmid T^2-4N$, then $Q_{T,N}$ represents $-1$ over $\mathcal O_v$ (`adicInt_exists_norm`).

*Proof.* The archive proves completeness directly. An element of every $\mathfrak m_v^n$ has valuation at least $n$ for every $n$, in additive notation, so it is $0$. A sequence that is Cauchy for the $\mathfrak m_v$-adic filtration is Cauchy in $F_v$. Its limit lies in the closed subring $\mathcal O_v$ and stays in each closed ball around the terms. Mathlib's `IsAdicComplete.henselianRing` turns completeness into the Henselian property by Newton iteration. The map $\mathcal O_F\to k_v$ is onto, because $F$ is dense in $F_v$ and a $v$-integral element of $F$ is approximated by elements of $\mathcal O_F$. It kills $\mathfrak p_v$, and $\mathcal O_F/\mathfrak p_v$ is finite, so $k_v$ is finite. An element $r\in\mathcal O_F\setminus\mathfrak p_v$ has multiplicative valuation $1$, so it is a unit. The last sentence is Lemma 2 with $u=-1$. $\square$ [A2, `Adelic.lean:18–278`; Mathlib, `AdicValuation.lean:396,561–562,883`, `Henselian.lean:170`](../sources/SOURCES.md#finite-adelic-norm-minus-one)

**Lemma 4 (a local solution at every finite place) [Lean, read].** In the setting of Lemma 1, for every finite place $v$ of $F$ there are $s_v,t_v\in F_v$ with $Q_d(s_v,t_v)=-1$, and $s_v,t_v\in\mathcal O_v$ if $v\nmid d$.

*Proof.* No place divides both $q$ and $d$: they are distinct primes, since $q\equiv3$ and $d\equiv7\pmod8$, so $1=aq+bd$ for some integers $a,b$, and $1\notin\mathfrak p_v$ (`adel_not_both`). If $v\nmid d$, Lemma 3 applies to $Q_d$, whose discriminant is $-d$, and gives integral $s_v,t_v$. If $v\mid d$, then $v\nmid q$, and Lemma 3 applies to $Q_q$ instead. It gives integral $s,t$ with $Q_q(s,t)=-1$. Put $s_v=s+\alpha t$ and $t_v=\beta t$, with $\alpha,\beta\in F\subset F_v$. By Lemma 1, $Q_d(s_v,t_v)=Q_q(s,t)=-1$. Nothing is claimed about integrality here, and Example B shows that it can fail. $\square$ [A2, `Adelic.lean:407–475`](../sources/SOURCES.md#finite-adelic-norm-minus-one)

**Lemma 5 (almost all choices are integral) [Lean, read].** Choose $(s_v,t_v)$ as in Lemma 4 for every $v$. Then $\mathbf s=(s_v)_v$ and $\mathbf t=(t_v)_v$ lie in $\mathbb A_{F,f}$, and $\mathbf s^2+\mathbf s\mathbf t+N_d\mathbf t^2=-1$ there.

*Proof.* The set of places with $v\mid d$ is the set of prime factors of the nonzero ideal $d\mathcal O_F$, which is finite (`Ideal.finite_factors`). Off this set both coordinates are integral by Lemma 4. So the set of places where $s_v\notin\mathcal O_v$ is contained in a finite set, which is the cofinite condition defining the restricted product. The same holds for $t_v$. The identity holds in every component, and the image of the integer $N_d$ in $\mathbb A_{F,f}$ is $N_d$ in every component. Equality of all components is equality in $\mathbb A_{F,f}$. $\square$ [A2, `Adelic.lean:486–525`; Mathlib, `Factorization.lean:84–85`](../sources/SOURCES.md#finite-adelic-norm-minus-one)

The archive makes the choice with `Classical.choose` (`adelSv`, `adelTv`), so no particular solution is singled out. The examples above exhibit one admissible choice at two places.

**Lemma 6 (assembly in a commutative ring) [Lean, read].** Let $B$ be a commutative ring with a ring endomorphism $\tau$, and let $s,t,u\in B$ and $N\in\mathbb Z$ satisfy $\tau(s)=s$, $\tau(t)=t$, $\tau(u)=1-u$, $u(1-u)=N$ and $s^2+st+Nt^2=-1$. Then $\tau(s+ut)(s+ut)=-1$.

*Proof.* $\tau(s+ut)(s+ut)=(s+(1-u)t)(s+ut)=s^2+st+u(1-u)t^2=s^2+st+Nt^2=-1$. $\square$ [A2, `Adelic.lean:527–537`](../sources/SOURCES.md#finite-adelic-norm-minus-one)

#### The theorem

**Theorem 6.4.17 (finite adelic element of norm $-1$ for a host) [Lean, read].** Let `H : Host R` be a host record with $E$, $F$, $c$, $q$, $d$, $\omega_q$, $\omega_d$ as above, and let $\sigma:E\to E$ be an $F$-algebra homomorphism with $\sigma(x)=c(x)$ for all $x\in E$. Then there are $\mathbf s,\mathbf t\in\mathbb A_{F,f}$ with

1. $\mathbf s^2+\mathbf s\mathbf t+N_d\mathbf t^2=-1$, and $s_v,t_v\in\mathcal O_v$ at every finite place $v\nmid d$;
2. $y=1\otimes\mathbf s+\vartheta\otimes\mathbf t\in E\otimes_F\mathbb A_{F,f}$ satisfies $(\sigma\otimes\mathrm{id})(y)\,y=-1$.

In particular $y$ is a unit of $E\otimes_F\mathbb A_{F,f}$ with inverse $-(\sigma\otimes\mathrm{id})(y)$. The archive supplies the witnesses in part 1 through `adelS`, `adelT`, `adel_key` and the integrality clause of `adelSTv_spec`. The declaration `exists_adelic_neg_one` asserts the existence of an element satisfying the norm equation in part 2. [A2, `Adelic.lean:501–505,517–518,539–571`](../sources/SOURCES.md#finite-adelic-norm-minus-one) [Expository] The same proof gives the statement for any number field $E$ with a subfield $F$ and an $F$-algebra endomorphism $\sigma$ satisfying (U1)–(U3) with $c=\sigma$. That generalization is ours, not a Lean statement. The worked examples use it.

*Proof.* For a host, (U1) is `hyp`, (U2) is `sqq_sq`, `sqd_sq`, `adel_conj_aE` and `adel_conj_bE`, and (U3) is `adel_mem_F`. Lemmas 4 and 5 give $\mathbf s,\mathbf t$ with part 1. For part 2 let $B=E\otimes_F\mathbb A_{F,f}$ and $\tau=\sigma\otimes\mathrm{id}$, which is a ring endomorphism of $B$. Put $s=1\otimes\mathbf s$, $t=1\otimes\mathbf t$ and $u=\vartheta\otimes1$. The map $a\mapsto1\otimes a$ is a ring homomorphism, so part 1 gives $s^2+st+N_dt^2=-1$ in $B$, and $\tau$ fixes $s$ and $t$. The map $x\mapsto x\otimes1$ is a ring homomorphism, so Lemma 1 gives $u(1-u)=N_d\otimes1=N_d$. Finally $\tau(u)=\sigma(\vartheta)\otimes1=c(\vartheta)\otimes1=(1-\vartheta)\otimes1=1-u$, by the hypothesis on $\sigma$ and Lemma 1. Lemma 6 gives $\tau(s+ut)(s+ut)=-1$, and $s+ut=1\otimes\mathbf s+\vartheta\otimes\mathbf t=y$. Multiplying $\tau(y)y=-1$ by $-1$ shows that $-\tau(y)$ is an inverse of $y$. $\square$

The proof never decomposes $E\otimes_F\mathbb A_{F,f}$ into local factors. All local information sits in the coefficients $\mathbf s,\mathbf t$. The single global element $\vartheta$ carries the action of $\sigma$, and its norm form has integer coefficients, so it makes sense in every component at once. The same $\sigma$ acts at every place, through the identity $\sigma(\vartheta)=1-\vartheta$ in $E$.

#### The same input in `spacesOfRanks`

`hostSpacesOfNorm` calls `exists_adelic_neg_one H (cmData H).sig (fun x => star_eq_conj H x)`. Here `(cmData H).sig` is the host's star, the CM complex conjugation of Mathlib, packaged as an $F$-algebra homomorphism. `star_eq_conj` identifies it with `H.conj` pointwise by testing against the injective embedding `H.φ₀`. The output type is literally the hypothesis `hy` of `spacesOfRanks` with `cm = cmData H`, the same $\sigma$ and the same ring $E\otimes_F\mathbb A_{F,f}$. Theorem 6.4.17 therefore discharges the finite adelic hypothesis of the theorem in §6.4.16 for every host, with no further input. For a host the CM datum is `cmData H`, built from the record, and the level prime $T$ with an element $p_z$ satisfying $p_z\,c(p_z)=T$ remain the separate inputs of `hostSpacesOfNorm`.

| Step | Declaration | What happens to $y$ |
|---|---|---|
| Production | `exists_adelic_neg_one`, `Adelic.lean:539–571` | $y=1\otimes\mathbf s+\vartheta\otimes\mathbf t$ with $(\sigma\otimes\mathrm{id})(y)\,y=-1$ |
| Host call | `hostSpacesOfNorm`, `RankRecordRowDimensionZero.lean:137–142` | passed with $\sigma=$ `(cmData H).sig` |
| Hypothesis | `spacesOfRanks` variable `hy`, `BaseFormAnisotropicOrthogonalSingle.lean:204–205` | same type, unchanged |
| Consumer | `dSpace_congr`, `:128–164`, called in `baseSpace_isometric_graded`, `:376` | diagonal multiplier $y$ on sign-changing coordinates, inverse $-(\sigma\otimes\mathrm{id})(y)$ |

In `dSpace_congr` a coordinate whose sign must change is multiplied by $y$, and $(\sigma\otimes\mathrm{id})(y)\cdot(\pm1)\cdot y=\mp1$. So over $E\otimes_F\mathbb A_{F,f}$ the one-dimensional forms $\langle1\rangle$ and $\langle-1\rangle$ are isometric. Over $E$ they are not, because their signs differ at every real place. §6.4.16 reads this step, and it is inherited here.

#### Remarks

**Remark (why positivity at the real places is no counterexample) [Expository].** The computation in the motivation shows that $-1\ne\sigma(x)x$ for $x\in E^\times$. For the same reason $-1$ is not a norm from $E\otimes_F\mathbb R\cong\mathbb C$ at any real place, where $\sigma\otimes\mathrm{id}$ is complex conjugation and $\sigma(z)z=|z|^2$. The theorem is consistent with both facts because $\mathbb A_{F,f}$ omits the real places. The real places still constrain the finite ones. By Hilbert's reciprocity law the quadratic Hilbert symbols satisfy $\prod_v(-1,-d)_v=1$ over all places of $F$ ([Neukirch, *Algebraic Number Theory*, VI, Theorem 8.1, p. 414](https://doi.org/10.1007/978-3-662-03983-0)). For a host $E=F(\omega_d)$, because $[E:F]=2$ and $\omega_d\notin F$, so $(-1,-d)_v=1$ exactly when $-1$ is a norm from $E\otimes_FF_v$ (Neukirch, V, Proposition 3.2(iii), p. 334). At each of the $[F:\mathbb Q]$ real places of the totally real $F$ both entries are negative and the symbol is $-1$ (Serre, III, Theorem 1, p. 20). So the number of finite places where $-1$ is not a local norm is congruent to $[F:\mathbb Q]$ modulo $2$. The theorem makes this number $0$, so $[F:\mathbb Q]$ must be even. It is: $\beta^2=q/d$ with $q\ne d$ primes, so $F$ contains the real quadratic field $\mathbb Q(\beta)$. For $F=\mathbb Q$ the number is odd, and Example C finds the single failing place, $599$. In Examples A and B the two real places of $F_0$ give $(-1)^2=1$, and no finite place fails.

**Remark (no general surjectivity is claimed) [Expository].** The theorem is not the statement that local norms of a CM extension are onto, and that statement is false at ramified places: in Example C, $-1$ is a unit of $\mathbb Z_{599}$ and not a norm. The correct general statement is Milne's: the unit norm is surjective for finite unramified extensions of local fields. Lemma 2 proves only its degree-two case for an explicit unimodular form. A host extension $E/F$ is unramified at every finite place, because at each place one of the orders $\mathcal O_v[\vartheta]$ and $\mathcal O_v[\vartheta_q]$ has unit discriminant. The archive's proof never states this; the record carries unramifiedness as the separate field `unramEF`, which this proof does not use. It uses the two forms directly. The example $\mathbb Q(\sqrt3,i)/\mathbb Q(\sqrt3)$ of §6.4.16 is also unramified at every finite place, so Milne's theorem supplies its finite adelic input. It is not of the two-root form: its quadratic subfields are $\mathbb Q(i)$, $\mathbb Q(\sqrt3)$ and $\mathbb Q(\sqrt{-3})$, so it contains $\sqrt{-p}$ for only one prime, $p=3$, while (U2) needs two. Theorem 6.4.17 does not apply to it.

**Remark (hypotheses not used) [Expository].** The Jacobi clause $(-d/q)=1$ of `HostHyp`, the record's `q_ne_three`, its degree and Galois data, and the field `unramEF` play no role in this proof. Neither does the CM clause beyond (U3). The congruences mod $8$ and $16$ are used only through $4\mid q+1$, $4\mid d+1$ and $q\ne d$. For instance $q=3$ and $d=7$ violate the Jacobi clause, since $(-7/3)=-1$, and `q_ne_three`, yet $\mathbb Q(\sqrt{-3},\sqrt{-7})$ over $\mathbb Q(\sqrt{21})$ satisfies (U1)–(U3), and the proof applies verbatim. Where the archive needs those other clauses lies outside this subsection.

**Remark (comparison with Chapter 11) [Expository].** §§11.4.3.5–11.4.3.6 read a different producer in the same archive, `normIntegerUnits_surjective` for arbitrary unramified local extensions and the restricted-product description `mem_range_ideleNorm_iff` of idelic norms. Here the archive uses neither. It fixes one global basis $1,\vartheta$, solves one explicit equation per place and glues coefficients, not norms. [§11.4.3.5](11-the-window-bound-vwin.md#11435-norms-of-local-units-in-unramified-extensions) · [§11.4.3.6](11-the-window-bound-vwin.md#11436-the-idelic-norm-as-a-restricted-product-from-local-norms-to-one-idele)

**Remark (source boundaries).** Readings are pinned to A2, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`, and to Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Proof bodies read for the first time here: all of `Adelic.lean` (lines 18–571), comprising the local completeness, Henselian, residue-field and unit lemmas, `adicInt_exists_norm`, the host identities, `adel_not_both`, `adel_local`, `adel_finite_d`, the choices `adelSv`/`adelTv`, `adelS`/`adelT`, `adel_key`, `adel_hom_key`, `adel_alg` and `exists_adelic_neg_one`; the quadratic section of `UnimodUnramUnique.lean` (lines 10–140); `star_eq_conj` and `emb_star` (`ExampleLayerExistsGenerators.lean:40–53`); and Mathlib's counting proof of `exists_root_sum_quadratic`. Mathlib statements read without proof bodies: `HenselianLocalRing`, `IsAdicComplete.henselianRing`, `FiniteAdeleRing`, `RestrictedProduct` with its one-line `ext`, `Ideal.finite_factors`, `maximalRealSubfield` with `mem_maximalRealSubfield_iff`, `IsCMField.complexEmbedding_complexConj`, `valuation_exists_uniformizer`, `exists_valuation_sub_lt_of_integer`, `denseRange_algebraMap`, `valuedAdicCompletion_eq_valuation'` and `isSquare_of_char_two`. Named but not read: the finiteness of $\mathcal O_F/\mathfrak p_v$ (`Ideal.finiteQuotientOfFreeOfNeBot` or an instance, tried inside `first`) and the tensor-product maps `Algebra.TensorProduct.map`, `includeLeftRingHom` and `includeRight`. The host fields `hyp`, `sqq_sq`, `sqd_sq`, `gal_sqq`, `gal_sqd`, `der.conj_iff` and `Frame.cc` enter as record inputs, read by statement. The construction of the example host `H0` (`D7.hostAx`, `layerExists`) is covered in [§19.3.11](19-published-layer-case-studies-ii.md#19311-the-layer-host-of-the-second-constructor). `hostSpacesOfNorm`, `spacesOfRanks` and `dSpace_congr` are inherited from §6.4.16, with the call and the type of `hy` rechecked here. Several archive proofs try alternative tactic scripts with `first`. Reading the source does not decide which alternative elaborates, and none of this is a Lean kernel check. The ordinary projection identification remains [Open]. [Source register](../sources/SOURCES.md#finite-adelic-norm-minus-one)

### 6.4.21 Why the Frobenius matrix in an adapted basis is a unit

A quasi-logarithm has a Frobenius operation on both coefficients and variables. The archive writes its columns in an adapted basis as $UD$, with $D=\operatorname{diag}(pI_d,I_k)$. The factor $p$ records extra divisibility of the first $d$ columns. To form the dual Frobenius, the archive needs an inverse to $U$ over the original ring, before inverting $p$. It detects each coordinate of a hypothetical residue-field kernel vector, then lifts a determinant unit through the frame. This is a local step in the chapter's $p$-adic divisibility machinery. Its hypotheses are independent of the Gauss seminorm construction for crystalline periods. [Source register](../sources/SOURCES.md#adapted-frobenius-matrix-unit)

#### Two hand calculations [Expository]

Both calculations use the ordered basis $(e_L,e_R)$ of a split free module of rank two. The semilinear map has columns $UD$ for $D=\operatorname{diag}(2,1)$ and the endomorphism $\sigma$ specified in each example. In both examples $s$ is the extension of $\sigma$ to $Q$ that fixes $1/2$. They model the coefficient-ring calculation. The adapted basis in the theorem below is a basis of quasi-logarithms modulo integral series.

**A nonzero kernel correction.** Take $B=\mathbb Z_2[t]/(t^2-2t)$, $O=\mathbb Z_2$, $\theta(t)=0$, and $Q=B[1/2]$. Let $\sigma$ fix $\mathbb Z_2$ and send $t$ to zero. In the basis $1,t$, $B$ is complete and separated for $(2)$. Its kernel under $\theta$ is $\mathbb Z_2t$, and $(at)^2=2a^2t$. Modulo $2$, $\sigma(a+bt)=a\equiv(a+bt)^2$. Take
$$
U=\begin{pmatrix}1+t&2\\1&5\end{pmatrix},
\qquad UD=\begin{pmatrix}2+2t&2\\2&5\end{pmatrix},
\qquad M=\begin{pmatrix}1&0\\1&1\end{pmatrix}\quad\text{over }\mathbb F_2.
$$
For $w=(1+t,3)^{\mathsf T}$ we have $\sigma(w)=(1,3)^{\mathsf T}$ and $U\sigma(w)=(7+t,16)^{\mathsf T}$. The squared residues of $w$ are $(1,1)^{\mathsf T}$, with image $(1,0)^{\mathsf T}$ under $M$. The target residues $(1,1)$ lift through $O$ as $(1,1)$ with the same square roots, and $w$ is one choice of subsequent lift modulo $J$. The row $(1,0)$ applied to $M$ detects the first input coordinate. On a right-supported input, $M(0,b)^{\mathsf T}=(0,b)^{\mathsf T}$.

We have $\det U=3+5t$ and can lift the inverse of its $\theta$-image by $b'=1/3$. The error $x=(3+5t)/3-1$ is $5t/3$ and $x^2=2(25t/9)$. Thus $(1+x)(1-x)=1-50t/9$ is a unit by the $2$-adic geometric series. Direct multiplication gives $(3+5t)^{-1}=1/3-(5/39)t$. The matrix inverse is this scalar times $\begin{pmatrix}5&-2\\-1&1+t\end{pmatrix}$. The determinant of $UD$ has image $6$ in $O$, hence $UD$ is a nonunit.

**A nontrivial residue Frobenius.** Take $O=B=\mathbb Z_2[\alpha]$ with $\alpha^2+\alpha+1=0$, $\theta=\operatorname{id}$ and $Q=B[1/2]$. The ring is complete in the basis $1,\alpha$. Its reduction is the field $\mathbb F_4$ because the defining polynomial has no root modulo $2$. Elements with nonzero residue are units by lifting a residue inverse and summing a geometric series. Every nonzero element is $2^m$ times such a unit, by taking the smaller valuation of its two coefficients. Products of nonzero elements are therefore nonzero, and $B$ is a discrete valuation ring. The automorphism $\sigma(\alpha)=\alpha^2=-1-\alpha$ fixes $\mathbb Z_2$ and reduces to squaring. Take
$$
U=\begin{pmatrix}\alpha&2\\1&1\end{pmatrix},
\qquad UD=\begin{pmatrix}2\alpha&2\\2&1\end{pmatrix},
\qquad M=\begin{pmatrix}\bar\alpha&0\\1&1\end{pmatrix}\quad\text{over }\mathbb F_4.
$$
For $z=(\bar\alpha,1)^{\mathsf T}$ choose the root lift $w=(\alpha^2,1)^{\mathsf T}$. Since $\alpha^3=1$, squaring its residue gives $z$, and $\sigma(w)=(\alpha,1)^{\mathsf T}$. Then $U\sigma(w)=(\alpha^2+2,\alpha+1)^{\mathsf T}$, with residue $Mz=(\bar\alpha^2,\bar\alpha+1)^{\mathsf T}$. The row $(\bar\alpha^{-1},0)$ applied to $M$ reads off the left input coordinate. On a right-supported input the second row of $M$ reads off the right coordinate. The determinant $\alpha-2$ reduces to $\bar\alpha$. Here $\theta$ is the identity, so the frame lift of the determinant inverse has zero error. Since $(\alpha-2)(\alpha^2-2)=7$, the matrix inverse is $(\alpha^2-2)/7$ times $\begin{pmatrix}1&-2\\-1&\alpha\end{pmatrix}$.

Both examples are scalar frames with injective coefficient embedding in $Q$, denominators powers of $2$, odd integers invertible and $O$ torsion-free. The second has zero frame kernel. Both residue fields are perfect. An instance with the full BFrame record and an algebraically closed ambient field is given below.

#### Frame, adaptation and the matrix hypothesis

Fix a prime $p$, an algebraically closed field $C$ of characteristic zero with a multiplicative valuation $v:C\to\mathbb R_{\ge0}$, and a commutative ring $O$ with an $O$-algebra structure on $C$ that identifies $O$ with the valuation integers. The map $O\to C$ is injective with image the elements of value at most one. Assume $O$ is a domain, $p$ is a nonunit in $O$, and $O$ is separated and complete for $(p)$. Fix a pretilt element $\varepsilon$ with a primitive system of $p$-power roots of unity and any BFrame $F$ for it. Write $B=F.B$, $Q=F.Q$, $\iota:B\hookrightarrow Q$, $\theta=F.\theta$, $\sigma=F.\sigma$ and $s=F.s$. The full record includes $a:A_{\inf}\to B$ with $\theta a$ the Fontaine map and $\sigma a=a\varphi$ for Witt Frobenius $\varphi$. It includes $\tau\in B$ with $p\tau=a(\mu(\varepsilon))$ and $\tau^2=0$, where $\mu(\varepsilon)$ denotes the cyclotomic Witt element. Every $b\in B$ has the form $a(x)+\tau a(y)$. The remaining clauses are $\tau a(y)=0$ exactly when $\mu(\varepsilon)\mid y$, and $\tau\mid a(x)$ exactly when $\mu(\varepsilon)\mid x$.

The scalar frame gives a surjective $\theta$, an injective $\iota$, denominators in $Q$ cleared by powers of $p$, invertibility of $p$ in $Q$ and of integers prime to $p$ in $B$, and $p$-torsion freeness of $O$. It requires $B$ separated and complete for $(p)$ and
$$
x\in\ker\theta\ \Longrightarrow\ \exists y\in\ker\theta,\quad x^p=py.
$$
This last law follows in a divided-power ideal from $x^p=p!\gamma_p(x)$. Also $s\iota=\iota\sigma$ and $\sigma(b)-b^p\in pB$ for all $b\in B$.

For any $p$-divisible group $G$ over $O$, fix a QLog chart $c$ of dimension $d$ and a lift $\mu'$ of its law $\mu=c.\mu$. The condition IsLift gives zero constants, the right unit law, symmetry and a formal group law after reduction. Require also $\theta(\mu'_i)=\mu_i$ coefficientwise. For an ideal $N$ of $B$ write $f\in[N]$ if all coefficients are in $\iota(N)$. Put $\operatorname{lin}_i f=[X_i]f$ and $\delta_{\mu'} f=f(\mu'(X,Y))-f(X)-f(Y)$, extending coefficients to $Q$ as needed. A quasi-logarithm for $N$ has zero constant term, linear coefficients in $\iota(N)$, and $\delta_{\mu'} f\in[N]$.

For any $k\ge0$, let $I=L\sqcup R$ with $L=\operatorname{Fin}(d)$ and $R=\operatorname{Fin}(k)$ tagged disjointly. Fix $e_l\in Q[[X_1,\ldots,X_d]]$ for $l\in I$. The condition IsBasis requires that each $e_l$ is a quasi-logarithm for $B$ and every such $f$ admits a unique $b\in B^I$ with $f-\sum_l\iota(b_l)e_l\in[B]$. The condition IsAdapted requires $\delta_{\mu'}e_i\in[\ker\theta]$ and $\operatorname{lin}_j e_i=\delta_{ji}$ for each $i\in L$ and each variable $j$. Define $\Phi f$ by applying $s$ to the coefficients and substituting $X_j^p$ for $X_j$. For a matrix $U$ over $B$ on $I$, put
$$
E_m=\Phi e_m-\sum_l\iota((UD)_{lm})e_l,\qquad D=\operatorname{diag}(pI_d,I_k).
$$

**Theorem (adapted Frobenius matrix).** For every choice of the data above, if $E_m\in[B]$ for all $m\in I$ and $E_m\in[pB]$ for all $m\in L$, then $U$ is invertible over $B$. The proof produces the first block from coefficients and the second from a cotangent test. Lemma 4 identifies the archive results used for that test. [Lean, read] [Source register](../sources/SOURCES.md#adapted-frobenius-matrix-unit)

#### Lemma 1. Reflection of units along the frame

Suppose $\theta(b)$ is a unit. Surjectivity lifts its inverse to $b'\in B$, so $x=bb'-1$ belongs to the kernel. The frame gives $x^p=py$ with $y$ in the kernel. For any $a\in pB$, the sums $\sum_{i=0}^{n-1}a^i$ give compatible residues at increasing precision. Completeness gives a limit, and separatedness makes its product with $1-a$ equal to $1$, since the finite products equal $1-a^n$. Applying this to every multiple of $a$ proves $pB\subseteq\operatorname{Jac}(B)$. In particular $1-(-x)^p=1-(-1)^ppy$ is a unit. Now
$$
(1+x)\sum_{i=0}^{p-1}(-x)^i=1-(-x)^p.
$$
The product on the left is a unit in a commutative ring, so its first factor $bb'$ is a unit, as is $b$. The lifting uses the divisibility $x^p=py$. The extra conclusion $\theta(y)=0$ is part of the frame.

#### Lemma 2. Lifting root coordinates

The units of the valuation ring are the elements of value one, since both an element and its reciprocal must have value at most one. The elements of value strictly less than one form an ideal by the valuation laws, so they form the unique maximal ideal. Write $\mathfrak m$ for that ideal, $\kappa=O/\mathfrak m$ for the residue field, $\rho:B\to\kappa$ for the composite with $\theta$, and $J=\ker\rho$. Since $p$ is a nonunit in $O$, $pB\subseteq J$. For $a\in O$ choose a root $z$ of $T^p-a$ in $C$. Then $v(z)^p=v(a)\le1$, hence $v(z)\le1$ since $p>0$. Thus $z$ comes from $r\in O$ and injectivity gives $r^p=a$. The argument includes $a=0$. Given $x\in\kappa$, lift it to $a\in O$, choose such $r$ and lift $r$ along $\theta$ to $w\in B$. This gives $\rho(w)^p=x$. For all $b\in B$,
$$
\rho(\sigma(b))=\rho(b)^p
$$
because the error is in $pB$. Therefore $\sigma$ preserves $J$ and $\sigma(b)\in J$ implies $b\in J$, since a field has no nonzero nilpotents. This identity is in the residue field of $O$.

#### Lemma 3. Detecting the first block by coefficients of $X_i^p$

**Weighted coefficient integrality.** For a quasi-logarithm $f$ for $N$, differentiate the composite $f(\mu'(X,Y))$ with respect to $Y_i$ and set $Y=0$. Put $A_{ji}=\partial_{Y_i}\mu'_j(X,0)$. The resulting row has entries
$$
g_i=\sum_j(\partial_j f)\,\iota(A_{ji})
    =\partial_{Y_i}(\delta_{\mu'} f)(X,0)+\operatorname{lin}_i f.
$$
The first identity uses $\mu'(X,0)=X$ and the formal chain rule, which follows by differentiating monomials and comparing coefficients. The coefficient of $X^\alpha$ in the derivative of the coboundary is exactly its coefficient at $X^\alpha Y_i$. Thus $g_i\in[N]$. Symmetry gives $\mu'(0,Y)=Y$, so $A(0)=I_d$. The series $\sum_{n\ge0}(I_d-A)^n$ defines its inverse over $B$, coefficientwise, since the $n$th power contributes only in degrees at least $n$. Multiplication by this inverse preserves coefficient membership in $\iota(N)$, since each coefficient uses finite sums of products by $\iota(B)$. Therefore every coefficient of $\partial_j f$ belongs to $\iota(N)$. Reading the coefficient at $\alpha-\mathbf e_j$ when $\alpha_j>0$ proves $\alpha_j[X^\alpha]f\in\iota(N)$, and for $\alpha_j=0$ the assertion is zero. The archive solves the same row equation by a unit determinant and the constant-coefficient criterion for formal series.

**The coordinate rows.** Write $M=\rho(U)$ entrywise. For $i\in L$ choose $c_l\in B$ with $\iota(c_l)=p[X_i^p]e_l$ by weighted coefficient integrality. The coefficient of $X_i^p$ in $\Phi e_m$ is $s(\operatorname{lin}_i e_m)$. If $m\in L$ this equals $\delta_{im}$ and the column of $UD$ is $p$ times that of $U$. The stronger error condition and injectivity of $\iota$ yield
$$
\delta_{im}-\sum_lU_{lm}c_l\in pB.
$$
If $m\in R$, the linear coefficient is integral and $s$ preserves the embedded $B$ because $s\iota=\iota\sigma$. As the error lies in $[B]$, so does the indicated coefficient of the combination. Multiplying by $p$ and using injectivity gives $\sum_lU_{lm}c_l\in pB$. Consequently $(\rho(c_l))_l M$ is the $i$th coordinate row. If $U\sigma(w)\in J^I$, multiply its zero residue by this row to obtain $\rho(w_i)^p=0$, hence $w_i\in J$. This proves the first-block supplier. Both column congruences hold modulo $pB$ before passage to the residue field.

#### Lemma 4. Detecting the second block by the dual Lie coordinates

Take $b\in B^R$, write $\widetilde b=(0,b)$, and assume $W=U\sigma(\widetilde b)$ has all coordinates in $J$. Write $\delta'=\delta_{\mu'}$ and $\delta=\delta_\mu$. The integer frame and `frame_fraction_map` extend $\theta$ to $\Theta:Q\to C$. Indeed the frame identifies $Q$ with $B[1/p]$, and $\theta$ followed by $O\hookrightarrow C$ sends $p$ to a unit. The identity map of $O$ also gives a scalar frame with $C=O[1/p]$. To see denominator clearing here, use $v(p)<1$ and multiply a given element of $C$ by a sufficiently large $p$-power. Integers prime to $p$ are units in $O$ by Bézout and locality, and the identity kernel is zero. Hence the required frame clauses follow from the hypotheses on $O$ and $C$.

Coefficient transport makes each $e_l^C=\Theta(e_l)$ a quasi-logarithm for $\mu$ and gives $\delta e_i^C=0$ on $L$ by adaptation. The geometric supply `quasiLogarithm_secondBlock_tangent_basis_dual_lie` gives an $O$-basis $(\lambda_j)_{j\in R}$ of $\operatorname{Lie}(G^\vee)$ with $c.\operatorname{IsLie}(e_j^C,\lambda_j)$. The chart's `IsLie` tests an integral representative of $p^n e_j^C-e_j^C\circ[p^n]$ at every level $n$. Its value on a dual point with prescribed differential gives the pairing with $\lambda_j$ modulo $p^n$.

Set $f=\sum_{j\in R}\iota(b_j)e_j$. Semilinearity gives
$$
\Phi f-\sum_l\iota(W_l)e_l=\sum_{j\in R}\iota(\sigma(b_j))E_j\in[B].
$$
Here the right block of $D$ is the identity. There is a series $T$ over $B$ whose image is the left-hand side, and a series $F_1$ over $B$ whose image is $\delta'f$, by coefficientwise integrality. The archive gives $\delta'\Phi f-\Phi\delta'f\in[pB]$ by comparing the two substitutions with entries $(\mu'_i)^p$ and $\Phi\mu'_i$ in $s(f)$. The pure $X$ and pure $Y$ terms commute with $\Phi$ and cancel. The two substitution tuples have zero constants and agree modulo $pB$ by the coefficient Frobenius relation and characteristic-$p$ powering. The Lean proof applies `GlobalTheory.KatzCongr.subst_sub_in` with ideal $pB$. In this special case one can see the denominator control directly. For any formal series $a,h$ over $B$ and positive integer $n$, expand
$$
(a+ph)^n-a^n=n\sum_{j=1}^{n}\binom{n-1}{j-1}\frac{p^j}{j}a^{n-j}h^j.
$$
The fraction $p^j/j$ denotes an element of $pB$. Indeed write $j=p^r m$ with $m$ prime to $p$ and use $r<j$ and the unit $m$. Applying this identity to one variable at a time in a monomial difference produces a factor of its exponent in that variable, times a series over $pB$. The weighted coefficient of $s(f)$ times that exponent is integral by Lemma 3 and $s\iota=\iota\sigma$. Thus each monomial contribution to the substitution difference lies in $[pB]$. Both substitution tuples have zero constants, so each coefficient involves only finitely many monomials.

Take $t=\theta(T)$. To see the exact congruence, lift the integral series $\delta'e_l$ to series $g_l$ over $B$. Then, after bringing all integral terms back to $B$ using $\iota$,
$$
\delta_{\mu'}T=\sigma(F_1)(Z^p)+H-\sum_l W_l g_l
\qquad\text{with all coefficients of }H\text{ in }pB.
$$
Here $Z=(X,Y)$ and $\sigma(F_1)$ means coefficientwise action. Reduction along $\rho$ kills $H$ and the terms with $W_l$. Thus the coefficient of $\delta t$ at $p\beta$ is $\theta([Z^\beta]F_1)^p$ modulo $\mathfrak m$, and the remaining coefficients have zero residue. The linear coefficients of $t$ also have zero residue. Indeed $\Phi f$ has no linear terms, each $e_l$ has integral linear coefficients, and $W_l\in J$.

Write bars for reduction from $O$ to $\kappa$, and consider $\overline t$ over the reduced law $\overline\mu$. Every derivative of the reduced coboundary is zero since its support consists of exponents divisible coordinatewise by $p$. Differentiating in $Y$, setting $Y=0$ and using the vanishing linear coefficients of $\overline t$ gives the row equation $d\overline t\,A=0$ with $A(0)=I_d$, as in Lemma 3. Hence all partial derivatives of $\overline t$ vanish. Any coefficient whose exponent has a coordinate that is not divisible by $p$ occurs multiplied by a nonzero scalar in one of these partial derivatives and is zero. Therefore $\overline t$ itself has support in the exponents $p\beta$.

For every such exponent choose an integral $p$th root of the corresponding coefficient of $t$ by Lemma 2 and use it as the coefficient of an integral series $u$ at $\beta$. Then $\overline t=\overline u^p$. This equality follows by applying the finite characteristic-$p$ sum rule to the finitely many monomials relevant to each coefficient. Since composition with the zero-constant reduced law commutes with powering, $\delta_{\overline\mu}\overline t=(\delta_{\overline\mu}\overline u)^p$. Compare coefficients at $p\beta$ with the congruence for $\delta t$ and use injectivity of Frobenius in $\kappa$. This gives $\theta(F_1)-\delta u$ coefficientwise in $\mathfrak m$.

Applying $\Theta$ to $\iota(F_1)=\delta'f$ identifies the image of $\theta(F_1)$ in $C$ with the coboundary of $\sum_j\theta(b_j)e_j^C$. The second geometric supply `tangent_coords_nonunit_alt` takes this coefficientwise difference with the integral coboundary $\delta u$, the quasi-logarithms $e_l^C$, the left logarithms and the right Lie basis. It concludes $\theta(b_j)\in\mathfrak m$ for every $j\in R$. This proves the second-block implication given the two named geometric results. [Source register](../sources/SOURCES.md#adapted-frobenius-matrix-unit)

#### Proof of the theorem

If $\theta(\det U)$ is a nonunit, entrywise reduction commutes with determinant and gives $\det M=0$. A singular square matrix over $\kappa$ has a nonzero kernel vector $x$. Indeed, injectivity would imply bijectivity by finite-dimensional rank-nullity, and an inverse would give nonzero determinant. In size zero the determinant is $1$ by the empty-product convention.

Choose $w_l$ as in Lemma 2 with $\rho(w_l)^p=x_l$ for every $l\in I$. Then $\rho(U\sigma(w))=Mx=0$, since $\rho(\sigma(w_l))=x_l$. Lemma 3 forces all left coordinates of $w$ into $J$. Write $w=w_L+w_R$ by extending both blocks by zero. As $\sigma(J)\subseteq J$, all coordinates of $U\sigma(w_L)$ belong to $J$. Subtract this vector from $U\sigma(w)$ to obtain $U\sigma(w_R)\in J^I$. Lemma 4 forces all right coordinates of $w$ into $J$. Thus $x_l=\rho(w_l)^p=0$ for all $l$, contradicting the choice of $x$. This proves that $\theta(\det U)$ is a unit. Lemma 1 lifts it to a unit determinant, and $(\det U)^{-1}\operatorname{adj}(U)$ is a two-sided inverse.

#### Remarks and the original consumer

**A witness on the original objects.** Take $C=\mathbb C_p$ with its extended $p$-adic absolute value and $O$ its valuation integers. The ideals $p^nO$ are the closed balls of radii $|p|^n$, since division by $p^n$ gives the reverse inclusion. Hence $O$ is separated and complete for $(p)$. Start at $1$, choose a primitive $p$th root of unity, and recursively take a $p$th root of the last chosen root. For $n\ge1$, a root of a primitive root of order $p^n$ has order $p^{n+1}$, by the order formula for $p$th powers. All chosen roots are units of $O$. Their reductions modulo $p$ form $\varepsilon$ in the pretilt, and untilting the shifted sequence at index $n$ gives the original root there, since its exact lifts satisfy $\zeta_{n+r}^{p^r}=\zeta_n$ for every $r$. The archive's `exists_bFrame` provides the frame over this $O$.

For the height-zero group take $G.A(n)=O$ with the unit Hopf algebra and identity restrictions. The counit is the identity, so its augmentation ideal is zero. Its levels have rank $1=p^{n\cdot0}$ and the torsion ideals and restriction kernels are zero. Take $d=k=0$. The evaluations are the constant-coefficient identifications $O[[\varnothing]]\cong O$ and $O[[\varnothing]]\cong O\otimes_O O$. All variable and law conditions are vacuous. In the filtration condition for evaluation one can take degree cutoff $1$, and in the chart's kernel condition any level works since evaluation is injective. A series in zero variables with zero constant coefficient is zero. Thus the empty family is the adapted basis with unique coordinates and the empty matrix satisfies the column conditions and has determinant $1$. This witnesses the theorem's domain, including its zero-size boundary. The two rank-two calculations above exercise both blocks in coefficient frames. [Source register](../sources/SOURCES.md#adapted-frobenius-matrix-unit)

**The general matrix lemma modulo $p$.** In a separated $p$-adically complete commutative ring, a square matrix invertible modulo $pB$ is invertible over $B$. Lift an inverse to the reduced determinant and invert the resulting product in $1+pB$ by a geometric series. The converse is reduction. In the adapted argument the two smallness proofs supply invertibility over $B/J$. The quotient $B/pB$ can have nonzero nilpotents, as witnessed by $\bar t$ in the first example. The frame kernel law makes each element of $\ker\theta$ nilpotent modulo $pB$, and completeness puts $pB$ in the Jacobson radical. Lemma 1 gives the final lift and shows that $J$ is the ideal of nonunits of $B$. Hence $B$ is local with maximal ideal $J$, and $B/pB$ is local with maximal ideal $J/pB$. Over these rings, invertibility of $U$ over $B$, $B/pB$ and $\kappa$ is therefore equivalent. The general lifting lemma alone supplies no test for invertibility over either quotient.

**Deleting completeness in Lemma 1.** Take the subring $B$ of $\mathbb Q_p[T]$ generated over $\mathbb Z_p$ by $g_n=T^n/n!$ for all $n\ge1$, with $\theta$ the constant term to $\mathbb Z_p$ and $Q=B[1/p]=\mathbb Q_p[T]$. Products of generators are integer multiples of the generator of the summed degree by the multinomial formula, so kernel elements are finite $\mathbb Z_p$-linear combinations of positive-degree generators. In $g_n^p$, the coefficient of $g_{pn}$ is divisible by $p$ because $v_p((pn)!)-p v_p(n!)=s_p(n)\ge1$, where $s_p(n)$ is the sum of base-$p$ digits. The factorial identity follows by counting multiples of each power of $p$. Mixed multinomial terms of the $p$th power of any such combination have coefficients divisible by $p$, since all individual exponents are less than $p$. Thus $x^p/p\in\ker\theta$ for every kernel element. The remaining frame conditions, apart from completeness, follow from the specified embedding, localization, and target. In particular, separation follows degree by degree from $\bigcap_m p^m(1/n!)\mathbb Z_p=0$. But $1+T$ maps to $1$ and is a nonunit already in $\mathbb Q_p[T]$. The partial sums of $\sum_{n\ge0}(-T)^n$ are Cauchy since $T^n=n!g_n$ and $v_p(n!)$ tends to infinity. A limit in $B$ would invert $1+T$, proving the failure of completeness.

**Deleting the kernel law in Lemma 1.** Take $B=\mathbb Z_p\times\mathbb Z_p$, $\theta$ the first projection, and $Q=\mathbb Q_p\times\mathbb Q_p$. Every other scalar frame condition holds, including completeness and separation. The kernel element $(0,1)$ is idempotent and lies outside $pB$. The element $(1,0)$ has unit image and is a nonunit in $B$.

**Where the inverse is used.** In *HasPeriodIntegral.lean*, *GlobalTheory.QLog.WindowMat.window_matrices* starts with $G$ and $G^\vee$ connected. It chooses a chart, an adapted basis over the valuation integers and its lift, then $U$ with exactly the two column conditions of the theorem. It invokes *GlobalTheory.T.frobenius_matrix_isUnit_adapted_basis* on that same matrix. The result *hUu* goes into the window record and is passed to *isNil_dual_frobenius_alt* for $(U^{\mathsf T})^{-1}\operatorname{diag}(I_d,pI_k)$. The forward matrix is $UD$. The period equations preserve this order of factors, for example $\sigma(Y)=DU^{\mathsf T}Y$. The later *prismaticDieudonneHodge* proof passes *window_matrices* to *hasDatum_biconn_of*. That consumer forwards the same $U$ and its unit proof to *window_lift_to_fontaineAinf_matrices*, whose first step lifts a unit matrix modulo $\tau$ to $A_{\inf}$. Chart, law lift, adapted basis, normalized-column existence and the nilpotence arguments are separate inputs here.

**Classical context and reading status.** Fontaine constructs the universal completed divided-power thickening. The Jacobson radical criterion and the determinant criterion give the scalar and matrix lifting steps in this setting. Zink's normal decomposition has an invertible normalized Frobenius matrix by the display generation axiom. Scholze and Weinstein define the quasi-logarithm map and its projection to the logarithm of a lift. Here the coordinate test is proved for the archive's series and chart, and the two named geometric results supply the bridge to the dual Lie algebra. Local R3 [Lean, read] covers the unit argument, the first block, the second block through the named inputs in Lemma 4 and the indicated consumer calls. The archive is due to Levent Alpöge with Claude. This subsection records an author-level reading and uses expository examples. The static import path from Main reaches the module. Declaration-level dependence of the exported theorem, local kernel replay and peer review are separate verification questions. [Source and attribution register](../sources/SOURCES.md#adapted-frobenius-matrix-unit)

### 6.4.22 Reading the second block on the first torsion group

The second-block argument in §6.4.21 compares a linear combination of quasi-logarithms with the coboundary of a single integral series. The coboundary has two blocks of variables, whereas the chart evaluates series in one block on $G[p]$. Repeated addition converts the coboundary into the required series. On $G[p]$, multiplication by $p$ factors through the identity section, and a normalized Cartier dual functional kills the resulting constant.

For example, a height-two formal group at $p=2$ gives a quasi-logarithm whose first defect reduces to $x^2$ in $(O/2O)[x]/(x^4)$. Extracting the coefficient of $x^2$ gives $1$. The differential of this coefficient functional generates the dual cotangent module modulo $2$, so the value detects a Lie vector with unit coordinate. We will compute this example and a product example after the proof.

#### The chart, the defect, and the fixed basis

Let $p$ be prime, $C$ an algebraically closed field of characteristic zero with an $\mathbb R_{\ge 0}$-valued multiplicative valuation $v$, and $O$ its valuation integers. Assume $O$ is a domain, is $p$-adically complete and separated, and has $p$ as a nonunit. Write $\mathfrak m$ for its maximal ideal. Let $G$ be a $p$-divisible group over $O$, with level algebras $A_n$ representing $G[p^n]$, and let $c$ be its given $d$-variable chart with formal law $\mu$. Its maps $\operatorname{ev}_n$ and $\operatorname{ev}_{2,n}$ evaluate one and two blocks in $A_n$ and $A_n\otimes_O A_n$. They send sufficiently high degree tails into any prescribed $p^a$ multiple. They send the variables to the chart coordinates and identify the law with the coproduct on those coordinates. The full chart also requires the coordinates to be compatible under restriction, have augmentation zero and have powers divisible by $p$. Each one-block evaluation is surjective. For any $m,N$, some level has the property that every series in the evaluation kernel has all coefficients of total degree less than $N$ divisible by $p^m$.

Independently of the choice of $E$, the original window fixes the primitive root system and the corresponding $B$-frame $\mathcal F$ over $O$. For the local theorem take any commutative $O$-algebra $E$ satisfying the archive's $\operatorname{IsFrame}(p,E,\operatorname{id}_O)$. Its coefficient map $\iota:O\to E$ is injective, $p$ is invertible in $E$, and every element of $E$ becomes integral after multiplication by a power of $p$. The frame also requires prime-to-$p$ natural numbers to be units in $O$, $p$-torsion freeness and $p$-adic completeness of $O$, and surjectivity and the divided-power condition for the map $\operatorname{id}_O$. The latter two conditions hold for the identity map. In the consumer the original $B$-frame $\mathcal F$ stays in place and $E=C$ via the frame comparison $\Theta:\mathcal F.Q\to C$. Let $L=\operatorname{Fin}(d)$ and $R=\operatorname{Fin}(k)$. A quasi-logarithm here has zero constant, integral linear coefficients, and coefficientwise integral coboundary
$$
\delta g(X,Y)=g(\mu(X,Y))-g(X)-g(Y),
$$
with the law mapped to $E$ when appropriate. These are the conditions of $\operatorname{QL}(\mu,\top,g)$. Define $D_n g=p^n g-g\circ[p^n]_\mu$, where $[a]_\mu$ denotes the $a$-fold formal sum of $X$.

Write $M=\omega(G^\vee)$ for the inverse limit of the augmentation cotangent modules of the Cartier dual levels. Thus $\operatorname{Lie}(G^\vee)=\operatorname{Hom}_O(M,O)$. At level $n$, an element $\phi$ of the dual Hopf algebra is an $O$-linear functional on $A_n$. Its differential $d_1\phi$ is the class of $\phi-\phi(1)\epsilon_n$ in the dual augmentation ideal modulo its square, where $\epsilon_n$ is the counit of $A_n$. The map $d_1$ is surjective onto the level cotangent module. Write $w_n$ for the projection of $w\in M$. The relation $c.\operatorname{IsLie}(g,\lambda)$ requires integral coefficients for $D_n g$ at every $n$ and, for every $n,w,\phi$ and integral series $r$ with $d_1\phi=w_n$ and $\iota(r)=D_n g$, requires
$$
\lambda(w)-\phi(\operatorname{ev}_n r)\in p^n O.
$$
Here $\iota$ on series acts coefficient by coefficient. Every integral representative is covered, and injectivity makes it unique. [Source register](../sources/SOURCES.md#tangent-coordinate-nonunits)

#### An integral coboundary comparison forces nonunit coordinates

**Lemma [Lean, read].** Fix a family $(e_i)_{i\in L\sqcup R}$ of quasi-logarithms and a given $O$-basis $(\lambda_j)_{j\in R}$ of $\operatorname{Lie}(G^\vee)$. Assume that each original left logarithm has $\delta e_i=0$ and that $c.\operatorname{IsLie}(e_j,\lambda_j)$ holds for each right index. For every $b:R\to O$ and every $s\in O[[X]]$, set $f=\sum_{j\in R}\iota(b_j)e_j$, the combination with zero left support. Suppose every coefficient of $\delta f-\iota(\delta s)$ is the image of an element of $\mathfrak m$. Then every $b_j$ is in $\mathfrak m$. This is `TangentIndep.tangent_coords_nonunit` and its forwarding theorem `T.tangent_coords_nonunit_alt`. [Source register](../sources/SOURCES.md#tangent-coordinate-nonunits)

**Proof.** For $k=0$ the conclusion is empty. Defects are linear in the series. At each level, sum the integral representatives of the right defects with coefficients $b_j$. Evaluating this sum and summing the congruences for the same $n,w,\phi$ gives the Lie relation for $\lambda=\sum_j b_j\lambda_j$. Injectivity gives the relation for every representative of the summed defect. This is the finite-sum application of `LieLin.main`. The sum also satisfies the quasi-logarithm conditions by linearity of constant and linear coefficients and of the coboundary. The left logarithms retain their zero coboundaries and have coefficient zero in this computation.

Choose one series $T\in O[[X,Y]]$ with coefficients in $\mathfrak m$ satisfying $\delta f=\iota(\delta s+T)$. For a series $g$ over either ring, telescoping the identity for $\delta g$ along $[a]_\mu X$ gives
$$
g([p]_\mu X)=g(0)+p g(X)+\sum_{a=0}^{p-1}\delta g([a]_\mu X,X).
$$
The constant of $\delta g$ is $-g(0)$, hence $f(0)=\iota(s(0)-T(0,0))$. Substitution by zero-constant tuples commutes with coefficient maps and uses finitely many monomials in each coefficient. Applying the identity first to $f$ and then to $s$ gives a representative of $D_1 f$ over $O$,
$$
r=T(0,0)+p s-s\circ[p]_\mu-\sum_{a=0}^{p-1}T([a]_\mu X,X).
$$
In the archive, `s'` is first formed as the negative of the constant $s(0)-T(0,0)$ and the telescoping sum of $\delta s+T$. The second telescoping identity cancels the two occurrences of $s(0)$ in this expression. The constant of the residual series stays visible in $r$.

Evaluation after $[a]_\mu$ agrees with pullback by multiplication by $a$ on $G[p]$. For the variables, use induction on $a$, starting with the augmentation. In the induction step, compare evaluation after substituting $([a]_\mu X,X)$ with two-block evaluation followed by multiplication-by-$a$ on the first tensor factor and multiplication in $A_1$. They agree on the variables by the induction hypothesis and hence on polynomials. Truncate a series to agree with both evaluations modulo $p^m$ for each $m$. The degree cutoff survives the zero-constant substitution, and the finite projective algebra $A_1$ is separated. The coproduct identity now gives the induction step. Applying the same truncation to one-block series gives the asserted equality of evaluations. In particular $\operatorname{ev}_1(s\circ[p]_\mu)=s(0)\,1$, by the torsion condition and the augmentation of the chart coordinates.

Fix $w\in M$. Lift $w_1$ to a Cartier dual functional $\phi_0$ and set $\phi=\phi_0-\phi_0(1)\epsilon_1$. The differential stays $w_1$ and $\phi(1)=0$. Each $T([a]_\mu X,X)$ has all coefficients in $\mathfrak m$. Truncate such a series to match its evaluation modulo $pA_1$. The polynomial evaluates into $\mathfrak m A_1$ by $O$-linearity, and the error lies in $pA_1\subseteq\mathfrak m A_1$. This finite truncation works for a nondiscrete valuation. In the formula for $r$, $\phi$ kills both constants and sends $ps$ after evaluation into $pO$. Thus $\phi(\operatorname{ev}_1 r)\in\mathfrak m$, so the $n=1$ Lie congruence gives $\lambda(w)\in\mathfrak m$.

The archive's `PDiv.omega_finite_projective` applies to $G^\vee$ under the given valuation and completeness hypotheses. It uses injectivity on cotangents along multiplication by $p$ to get a $p$-torsion-free inverse limit, and lifts generators of the level-one quotient by adic completeness. Total divisibility in $O$ gives torsion freeness, hence flatness. Over the local ring $O$, $M$ is finite free. In any basis $(w_a)_a$ with dual basis $(w_a^\vee)_a$, the expansion $\lambda=\sum_a\lambda(w_a)w_a^\vee$ belongs to $\mathfrak m\,\operatorname{Hom}_O(M,O)$. Taking coordinates in the original $(\lambda_j)_j$ gives $b_j\in\mathfrak m$ for every $j$. Nonunits in a local ring form precisely its maximal ideal. [Source register](../sources/SOURCES.md#tangent-coordinate-nonunits)

#### First calculation. A nonzero tangent in dimension one [Expository]

Use $p=2$, $C=\mathbb C_2$ and $O=\mathcal O_{\mathbb C_2}$. The ideals $2^nO$ are the closed balls of radii $2^{-n}$, so $O$ is $2$-adically complete and separated. Start with $\zeta_0=1$ and $\zeta_1=-1$, and successively choose $\zeta_{n+1}^2=\zeta_n$. Each $\zeta_n$ has exact order $2^n$. Their reductions modulo $2$ give the pretilt element, whose $n$-th shifted sequence untilts to $\zeta_n$ since $\zeta_{n+r}^{2^r}=\zeta_n$. Use the archive's $B$-frame $\mathcal F$ from `exists_bFrame`. The scalar frame is $E=C$ over $O$ via $\operatorname{id}_O$. Powers of $2$ clear denominators by the valuation bound, odd integers are units, $O$ is $2$-torsion free, and the identity is surjective with zero kernel.

Over $\mathbb Z_2$ take the height-two formal law with normalized logarithm
$$
\ell(x)=\sum_{r\ge0}\frac{x^{4^r}}{2^r},
\qquad
\mu(x,y)=\ell^{-1}(\ell(x)+\ell(y)).
$$
Hazewinkel's functional equation lemma applies with base $\mathbb Z_2$, fraction field $\mathbb Q_2$, ideal $(2)$, $q=4$, coefficient endomorphism the identity, first coefficient $1/2$ and later coefficients zero. The linear term is $x$, the coefficients in $\mathbb Z_2$ equal their fourth powers modulo $2$, and $\ell(x)-\ell(x^4)/2=x$. The lemma gives integral $\mu$ and $P=[2]_\mu\equiv x^4\bmod 2$, using $\ell(P(x))-\ell(x^4)=2x$ in the comparison (2.8). Here $P$ is integral by substitution into the integral group law. [Hazewinkel, pp. 74–75](https://www.numdam.org/article/AST_1979__63__73_0.pdf#page=2)

Put $P_n=P^{\circ n}$ with $P_0(x)=x$. The algebras $\mathbb Z_2[[x]]/(P_n)$ are free on $1,x,\ldots,x^{4^n-1}$. To divide, reduce modulo $2$, divide by $x^{4^n}$, lift quotient and remainder, and repeat on the error divided by $2$. The $2$-adically convergent sums give division, and reduction at every step gives uniqueness. The same argument for $P(x)-z$ over $\mathbb Z_2[[z]]$ uses the ideal $(2,z)$ and its successive powers. On each graded piece the reduction of the divisor is $x^4$. Divide each coefficient in that graded piece by $x^4$, then lift the resulting quotient and the remainder of degree below four. Iteration gives convergent sums since $\mathbb Z_2[[z]][[x]]$ is $(2,z)$-adically complete coefficientwise with a uniform bound at each stage. Reduction and division at each graded piece also show uniqueness. Substituting $z=P(x)$ identifies the quotient by $P(x)-z$ with $\mathbb Z_2[[x]]$, using the $(2,z,x)$-adic formal series topology. Thus $[2]_\mu$ is finite free of degree $4$. Tate's construction for divisible formal Lie groups applies over $\mathbb Z_2$. Base change the resulting finite free algebras to $O$ to get $A_n$. The restriction $A_{n+1}\to A_n$ imposes $[2^n]=0$, as required by the archive's torsion ideal, and the rank is $4^n$. More explicitly, the torsion ideal on level $n+1$ is generated by the images of the augmentation ideal under multiplication by $2^n$. Here the augmentation ideal is generated by $x$, so the torsion ideal is $(P_n(x))$. These equations and the finite bases persist under base change.

Since $x^{4^n}\in2A_n$, evaluation at $x$ and at the two tensor images converges and satisfies the chart's tail bounds. It is surjective onto $A_n$ by the basis. For the kernel bound, the linear term $2x$ and absence of a constant in $P$ give $P_n\in x(2,x)^n$ by induction. For any $m,N$, take $n\ge m+N$. The polynomial truncation algebra $(O/2^m O)[x]/(x^N)$ receives a map from $A_n$ sending $x$ to $x$, since $P_n$ vanishes there. This reads all coefficients below $N$ modulo $2^m$. The counit and coproduct are those given by $0$ and $\mu$ on the torsion quotients. [Tate, §§1.2, 2.1–2.3, pp. 159, 161–163 and 166](https://math.bu.edu/people/jsweinst/AWS/Files/TatePDivisibleGroups.pdf) [Source register](../sources/SOURCES.md#tangent-coordinate-nonunits)

Keep the left logarithm $\ell$ and set $h(x)=\ell(x^2)/2$ on the right. Its constant and linear coefficients are zero, and
$$
\delta h(x,y)=\frac{\ell(\mu(x,y)^2)-\ell(\mu(x^2,y^2))}{2}.
$$
The two arguments agree modulo $2$ by squaring in characteristic two. If $U\equiv V\bmod 2^a$ with $a\ge1$, then $U+V$ is divisible by $2$ and $U^2-V^2$ by $2^{a+1}$. Thus $U^{4^r}-V^{4^r}$ is divisible by $2^{2r+1}$ for the displayed arguments. Division by $2^{r+1}$ leaves integral coefficients in each summand, and every coefficient sees finitely many summands. This proves the quasi-logarithm condition.

We check $c.\operatorname{IsLie}$ at all levels. Telescoping with $2^n$ in place of $p$ gives an integral representative $r_n$ of $D_n h$ because $h(0)=0$ and $\delta h$ is integral. Put $a_n=\operatorname{ev}_n r_n$. Since $P_n$ is a group endomorphism, $\delta r_n=2^n\delta h-(\delta h)\circ(P_n,P_n)$ over $O$. After evaluation on two tensor factors the second term vanishes, since $P_n=0$ there and $\delta h(0,0)=0$. Thus $a_n$ is primitive modulo $2^n$, meaning that its comultiplication equals $a_n\otimes1+1\otimes a_n$ modulo $2^n$, and has augmentation zero. The map $\phi\mapsto\phi(a_n)\bmod 2^n$ kills products of two dual augmentation elements by the convolution formula, and kills scalars by augmentation zero. It defines a linear map from the level cotangent module to $O/2^nO$. The identity
$$
r_{n+1}=r_n\circ P+2^n r_1
$$
gives $a_{n+1}\equiv G.\operatorname{mulP}(n)(a_n)\bmod 2^n A_{n+1}$. Here $G.\operatorname{mulP}(n):A_n\to A_{n+1}$ is pullback by multiplication by $2$ from $G[2^{n+1}]$ to $G[2^n]$, so it sends $x$ to $P(x)$ by `mulP_res`. The restriction on the Cartier dual algebras sends $\phi_{n+1}$ to $\phi_{n+1}\circ G.\operatorname{mulP}(n)$. Its map on cotangent modules sends $d_{n+1}\phi_{n+1}$ to the differential of that restriction. Hence the residues obtained from a compatible $w=(w_n)_n$ agree under reduction. Completeness produces one $O$-linear functional $\lambda_h$ with those residues. At level zero the algebra is $O$, the defect is zero and the congruence modulo $2^0$ is automatic. This proves the congruence for every $n,w,\phi$, and coefficient injectivity gives it for every integral representative. [Source register](../sources/SOURCES.md#tangent-coordinate-nonunits)

At level one, the functional equation of $\ell$ gives
$$
r_1=x^2+\frac{\ell(x^8)-\ell(P(x)^2)}{2}.
$$
Since $P(x)\equiv x^4\bmod 2$, its square agrees with $x^8$ modulo $4$. Iterating the squaring estimate shows the logarithm difference, divided by $2$, is in $2O[[x]]$. Therefore $a_1\equiv x^2\bmod 2A_1$.

Set $\bar O=O/2O$. In $\bar O[x]/(x^4)$ the tensor-square coproduct is
$$
\Delta x=x+y+x^2y^2,\quad
\Delta x^2=x^2+y^2,\quad
\Delta x^3=x^3+x^2y+xy^2+y^3 .
$$
Indeed the degrees of $\ell$, its compositional inverse, and the two-variable law are $1\bmod 3$. Only degrees $1$ and $4$ survive in this tensor square. The degree-four part of $\mu$ is $(x^4+y^4-(x+y)^4)/2$, whose surviving coefficient is $-3\equiv1\bmod2$. Squaring and cubing give the other two formulas. If $u_i$ is dual to $x^i$, convolution gives $u_2^2=u_1$, $u_2u_1=u_3$ and $u_1^2=0$. So the dual algebra modulo $2$ is $\bar O[u_2]/(u_2^4)$, with cotangent generator $d_1u_2$. Reduction commutes with the augmentation quotient because constants split off by the counit and products of augmentation elements reduce to the corresponding products. The archive identification $M/2M\simeq\omega(G^\vee[2])$ and finite freeness show that $M$ is free of rank one and any lift $w$ of this generator is a basis. In particular take $w$ projecting to the differential of the integral coefficient functional extracting $x^2$. The level-one pairing gives $\lambda_h(w)\equiv1\bmod2$. Thus $\lambda_h$ is a basis of the dual Lie module.

Take the fixed basis $(\lambda_h)$, $b=2$, and $s=2(1+x)$. Then $f=2h$ and the comparison coboundary has coefficients in $2O$. Its residual $T=2\delta h-\delta s$ has constant $T(0,0)=2$, since $f(0)=0$ and $s(0)=2$. The normalized coefficient functional gives $0\bmod2$ on $D_1 f$ evaluated at level one, and the Lie pairing is $2\lambda_h(w)\ne0$. This example has one integral comparison series and a nonzero Lie vector of nonunit coordinate.

#### Second calculation. Two coordinates in a product [Expository]

Use the same $O,\mathcal F,E$ and take the product of two copies of this group with the two original factor charts. Its torsion algebras are tensor products. The product algebra has basis $x_1^i x_2^j$ for $0\le i,j<4^n$, so evaluation is onto. In one or two blocks there are at most four coordinates, each with its $4^n$-th power in $2$ times the target. In a monomial of total degree at least $4m4^n$, some coordinate exponent is at least $m4^n$, giving the required tail bound modulo $2^m$. For $n\ge m+N$, both relations $P_n(x_i)$ vanish in $(O/2^mO)[x_1,x_2]/(x_1,x_2)^N$. Mapping the product algebra there reads the coefficients of degree below $N$ modulo $2^m$. Restriction, augmentation and the coproduct are componentwise. Pull back the left logarithms $\ell(x_1),\ell(x_2)$ and put $h_i=h(x_i)$. The all-level calculation applies to each factor: the defects evaluate as $a_n\otimes1$ and $1\otimes a_n$. Pairing with a tensor product of dual functionals gives the first factor pairing times the second augmentation, or the second pairing times the first augmentation. The dual cotangent modules split as direct sums, since the cross products of augmentation elements vanish in the quotient by the square. The same pairing therefore descends for every functional on the tensor product by linearity, since finite freeness makes the tensor products of dual basis vectors a basis of the functional module. This gives the two Lie functionals $\lambda_i$ and a factor basis $w_j$ with $\lambda_i(w_j)\equiv\delta_{ij}\bmod2$. In particular the two $\lambda_i$ form a basis.

Use right series $(h_1+h_2,h_2)$ and the fixed basis $(\lambda_1+\lambda_2,\lambda_2)$. Choose $\pi\in O$ with $\pi^2=2$. For $b=(\pi,2)$ and $s=2(1+x_1+x_2)$ the combination is $f=\pi h_1+(\pi+2)h_2$. Its comparison coboundary has coefficients in $\mathfrak m$ by integrality of both $\delta h_i$. The first defect evaluated on the first torsion algebra modulo $2$ is
$$
\pi x_1^2+(\pi+2)x_2^2 .
$$
The respective coefficient extractions give $\pi$ and $\pi+2\bmod 2O$. These reduce to zero in the residue field, and $\pi\notin2O$ since $|\pi|_2=2^{-1/2}$. In the fixed Lie basis the coordinate formula takes the first factor coordinate and subtracts it from the second. Applied to $(\pi,\pi+2)$ it gives $(\pi,2)$. The test therefore detects the maximal ideal even when the displayed vector has a coordinate outside $2O$.

#### Deleting the pairing or the integrality hypothesis [Expository]

In the first chart keep $O,\mathcal F,E,\ell$ and the basis $(\lambda_h)$. Remove the right Lie pairing and retain integral right defects at every level. Choose the right series $x$, take $b=1$, and choose $s=x$. The comparison is exactly zero, and every defect is integral since $x$ and $[2^n]_\mu$ are integral. At level one the defect evaluates to $2x$. The normalized functional extracting $x^2$ gives zero, whereas $\lambda_h(w)\equiv1\bmod2$ for the lift $w$ of its differential. The conclusion for $b$ fails with precisely the pairing clause removed.

Now retain the right series $h$ and its full Lie relation, but allow the single comparison series to belong to $C[[x]]$, forming both coboundaries over $C$. Take $b=1$ and $s=h$. The difference is zero again, and the coefficient of $x^2$ in $s$ is $1/2$, which fails the primitive's integrality. These controls use the same actual torsion tower, chart, left logarithm, frame, and basis.

#### The original consumer and the scope of the proof

In `SmallModMaximalOfFrobeniusImageSmall.lean:17–44`, `SmallSecond.small_second` retains the original $B$-frame $\mathcal F$ and comparison $\Theta:\mathcal F.Q\to C$. It uses the basis `lb` returned with `hlb` by `quasiLogarithm_secondBlock_tangent_basis_dual_lie`. The call passes the family $\Theta(e_i)$, `hQL`, `hlb`, `hlog`, the coordinates $\theta(b_j)$, and the single series $u$ supplied by `exists_integral_coboundaryOne_congr_frobenius`. The proof assigns the theorem's $s$ to that exact $u$ and may take the residual $T$ to be $\theta(F_1)-\delta u$, coefficient by coefficient. The equality `key` makes the coboundary of that right combination the image of $\theta(F_1)$. The coefficient condition `hu` supplies the nonunit witnesses after subtracting $\delta u$. The lemma gives the required conclusion for that same coordinate $\theta(b_j)$.

[Paper] Hazewinkel supplies the formal law, and Tate supplies the torsion tower and Cartier duality. Scholze and Weinstein's quasi-logarithm on the universal cover and its projection to the logarithm of a lift give the broader context. The finite-level production proof and the exact series and frame hypotheses here come from Alpöge with Claude. The worked pairings specialize classical Cartier duality and the functional equation lemma. [Scholze–Weinstein, §3.2, pp. 25–26](https://arxiv.org/pdf/1211.6357#page=25)

The local reading has author-level R3 status. In particular `LieLin.main` supplies its first conjunct here. The proof reads one pairing at level one after using the all-level relation to form the linear combination. The height-two and product calculations verify both clauses directly. Kernel replay, declaration-level reachability from Main, independent audit and peer review are separate verification records. The dual Lie basis existence for the original lifted family, the dimension–height identity, and the two nilpotence suppliers stay at the named boundaries of §6.4.21. The Gauss family and Frobenius matrix assembly are cited there. [Source and attribution register](../sources/SOURCES.md#tangent-coordinate-nonunits)

## 6.5 Remarks and formalization notes

### 6.5.1 The dictionary: Stepanov over $\mathbb F_q(x)$ versus the theta-lift chain over $\mathbb Z$

Having proved both Theorem 6.3 and Theorem 6.6 in full, we can lay the function-field prototype and
the Lean archive's number-field engine side by side [Expository]:

| Feature | Stepanov–Bombieri over $\mathbb F_q(C)$ (Theorem 6.3) | Lean archive over $\mathbb Z$ / CM host $E$ (Theorem 6.6, P7–P12) |
|---|---|---|
| **Scale parameter** | Field size $Q$ | Prime-sum cutoff $x \in [Z, Z^{3/2}]$ (`Scale.x`, `src/Formalism/LocalRingCardinality/DataParams₂.lean:10`) [Lean, read] |
| **Target sum** | Point count $\#C(\mathbb F_Q)$ or character sum $\sum_{x \in \mathbb F_Q} \chi(f(x))$ | Inert-prime Riesz sum `ASK` $\longleftrightarrow$ character sum `Level.Gm x` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean:200`) [Lean, read] |
| **Multiplicity parameter $m$** | Vanishing order $m \asymp \sqrt{Q}$ at rational points | Chain length `mAt = evenCeil (sqrt (x * delta1))` $\asymp \sqrt{x}$ (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:21`) [Lean, read] |
| **Operators creating $m$ layers** | Hasse–Schmidt derivations $D_t^{(0)}, \dots, D_t^{(m-1)}$ (`[HasseSchmidt1937]`) | $m$ iterated theta lifts $U(X_0) \to U(X_1) \to \dots \to U(X_m)$ (`remark.pdf` p. 4, item 8 [Paper]; Chapter 7) |
| **Linear-algebra ambient** | Extensions $\mathbb F_{q^n}$ and Riemann–Roch space $\mathcal L((r + Q\ell)P_\infty)$ | Real $2$-cyclotomic tower $n = 2^{e} \asymp x^{2+8\varepsilon}$ (`eAt`, `nAt`) and word set $W(u_0)$ (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:15,17,86`) [Lean, read] |
| **Local vanishing / divisibility** | $\operatorname{ord}_P(\Phi) \ge m$ at each $P \in C(\mathbb F_Q) \setminus \{P_\infty\}$ | Inert-prime $p$-adic divisibility `DIV` / `Conclusion1` (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:118` [Lean, read]; `src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean:97` [Lean], Chapter 8) |
| **Global conservation law** | $\sum_P \operatorname{ord}_P(\Phi) = 0$ ($\#\text{zeros} \le \deg(\Phi)_\infty$) | Bost's Hermitian slope inequality `SlopeIneq` + `s_lower5` (`src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:151`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:50`) [Lean, read] |
| **Main-term extraction** | Leading pole term $Q\ell / m = Q + O(\sqrt{Q})$ | Exact cancellation `key_identity5`: $\mathrm{SDiv} - \mathrm{sum}_A\cdot\mathrm{Lam}_5 + m\,\mathrm{sum}_A\cdot\mathrm{lg} = \mathrm{Main}(u_0) + \dots$ (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:105`) [Lean, read] |
| **Per-step "differentiation cost"** | Pole shift $c_C m$ from $R_1^k D_t^{(k)} s_b$ ($m^2/m = m$) | Non-compounding congruence/Selmer budget $m(B_0 + N_c)$ (`BNBounds`, `src/Formalism/SizeWindowBrackets/SChain.lean:33` [Lean, read]; bounded via $Ш^1$ in Chapters 10–11) |
| **One-sided $\implies$ zeros on $\Re s = 1/2$** | Twisting + rationality of $Z(C, T)$ (Steps 2–3 of Theorem 6.3) | Positive cyclic weights $(4,3)/(3o+1)$ + Landau window criterion `formB` (Chapters 3 and 5) [Lean, read] |

### 6.5.2 Honest audit of formalization scope in node P7: `structure` packaging vs. proved algebra

It is essential not to overstate what node `P7` proves on its own [Expository]:

1. **Stepanov's function-field theorem itself is *not* in the Lean archive:** Searching all 175,187
   files confirms that the archive never formalizes curves over $\mathbb F_q$ or Theorem 6.3; Stepanov's
   method is the *informal conceptual blueprint* explained by Alpöge (`remark.pdf` pp. 1, 3–4) [Paper;
   remark pp. 1, 3–4], whereas the Lean code starts directly at the number-field data structures `D7`
   and `Data U0 W Top m f`.
2. **What is genuinely proved without `sorry` in the P7 files we read (`R3` / `[Lean, read]`):**
   - the real-analytic concavity inequality `phi_bound` (`src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:81`) and exact main-term
     cancellation `key_identity` / `key_identity5` (`src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:170`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:105`);
   - the entire deduction `s_lower5` $\to$ `u_function_le_mean` $\to$ `Ga_bound5` $\to$ `each_unit_bound_statement`
     and `uniform_bound_statement` (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:50–242`), proving unconditionally that
     *any* `Data` record satisfying the 11 inequalities of `SizeData₂` obeys `ASK u0 ≤ Main u0 + ErrX5at`;
   - the explicit integer/rational parameter constructors `evenCeil`, `eAt`, `mAt`, `kAt`, `tAt`,
     `ranksOf`, and the rational Harish-Chandra interlacing verification `HCIn.hc` (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:11–161`),
     whose order inequalities (`u_gt_v`, `v_gt_u`, `u_last_gt`, `gap_be`, `gap_eb`) are discharged
     purely by `omega` and `linarith`;
   - the shift-covering lemmas `wt_self`, `coverS_of_cover`, `FamCore.coverS_carry` (`src/Formalism/SharpRestriction/FamCore.lean:27,47,187`)
     and the bundle projection `ChainTied.core_of` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:116`).
3. **What is packaged as `structure` fields or `Prop` hypotheses (and proved only in the deep Part II–III
   engine):** Inside `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean` and `src/Formalism/SizeWindowBrackets/SChain.lean`, `DIV`, `QuotientSlopeBoundsWith`,
   `SlopeIneq`, `LossBounds`, and `BNBounds` are **hypotheses** (conjuncts of the `Prop` `SizeData₂`),
   and `src/Formalism/SizeWindowBrackets/SChain.lean` even contains toy `Unit`-word model propositions such as `DataCompletion` (`:126`),
   `SizesModelAt` (`:153`), and `SizesTextAt` (`:207`) used for sanity-checking the parameter inequalities
   in isolation [Lean, read]! On the actual `src/Main.lean` proof path, `ChainTied` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97`)
   is inhabited not by a toy `Unit` model, but by the genuine automorphic chain family built in
   nodes `P17` and `P8`–`P12` (`topDesWin`, `src/Development/AutomorphicArithmetic/CharacterBoxes/DesWin.lean:11`), which we begin opening in Chapter 7.

### 6.5.3 Masullo's counterpart

Masullo's draft *The Music of the Primes* never uses Stepanov's auxiliary-polynomial method, Hasse–Schmidt
derivations, or an Arakelov chain of length $\sqrt{x}$ [Expository]. Nevertheless, **Chapter 14
("Complements", pp. 523–536)** touches two themes whose contrast with Chapter 6 is illuminating
[Paper; Masullo pp. 524–536]:

1. **Two unrelated meanings of "multiplicity" (§14.1, pp. 524–533, and §7.1, pp. 312–331):** Whenever
   Masullo writes "Multiplicity Bound" (e.g. Proposition 14.1.2.3 on p. 531, bounding $N(\rho) \le [F : \mathbb Q]$
   for non-central zeros $\rho \neq 1/2$ of a Hecke $L$-function $L(s, \chi)$, contrasted in
   Proposition 14.1.2.5 on pp. 531–532 with CM Mordell curves $Y^2 = X^3 + d$ over $F = \mathbb Q(\sqrt{-3})$
   whose central zero at $s = 1/2$ can have multiplicity $\ge 6 > [F : \mathbb Q] = 2$ conditional on
   $\operatorname{rk} E_d(F) \le \operatorname{ord}_{s=1} L(E_F/F, s)$), he means the **analytic
   vanishing order $\operatorname{ord}_{s=\rho} L(s, \chi)$ of an $L$-function at a zero** (or polar
   multiplicity of partial Euler products in §7.1) [Paper; Masullo pp. 312, 528–533]. In Alpöge's
   Stepanov strategy, "multiplicity $m \approx \sqrt{x}$" means the **divisibility / vanishing order of
   an auxiliary arithmetic object at prime ideals**, and implies nothing by itself about whether the
   critical-line zeros of $L(s, \chi)$ are simple!
2. **Why Masullo's Hardy–Sobolev trace formula fails over global function fields (§14.2, "The case of
   global function fields of positive characteristic", pp. 534–536):** At the very start of §14.2
   (p. 534), Masullo asks whether his Theorem 13.3.1.1 adapts to $F = \mathbb F_q(X)$ to give a new
   proof of the Riemann hypothesis for curves over $\mathbb F_q$, and answers bluntly: *"The short
   answer is 'no' to both parts of the question"* [Paper; Masullo p. 534]. His explanation on
   pp. 534–535 pinpoints two obstructions [Paper; Masullo pp. 534–536]:
   - Every closed point $x \in \lvert X \rvert$ has residue cardinality $\lvert k(x) \rvert = q^{\deg(x)}$,
     so **infinitely many Euler factors $(1 - q^{-\deg(x) s})^{-1}$ share the exact same vertical
     poles $s \in \frac{2\pi i}{\log q}\mathbb Z$** (unlike $\mathrm{Spec}\,\mathcal O_F$, where only
     finitely many prime ideals lie above each rational prime $p$!). Cancelling that infinite pole
     superposition in his $W^{s,2}(C_F)$ framework would force the Mellin transform of the test
     function to vanish to *infinite* order at a point, killing every nonzero holomorphic test function
     (p. 534); passing instead to a non-normable locally convex topology recovers only Weil's classical
     explicit formula with no zero-location constraint (p. 535, citing R. Meyer).
   - Moreover, **maximal curves over $\mathbb F_{q^2}$** (such as Hermitian curves, p. 535) have
     Frobenius characteristic polynomial $P_1(X) = (X + q)^{2g}$, where the eigenvalue multiplicity
     $2g$ strictly exceeds the gonality $\le g + 1$ (written "$g + 1$" on p. 535; e.g. gonality
     $q \le g + 1$ on the Hermitian curve $y^q + y = x^{q+1}$ of genus $g = q(q-1)/2$) when $g \ge 2$, violating
     the function-field analogue of his $[F : \mathbb Q]$ multiplicity bound (and over $\mathbb F_{p^2}(t)$,
     a supersingular elliptic double cover already gives a quadratic $L(s, \chi_f)$ with a double zero,
     p. 536) [Paper; Masullo pp. 535–536].

Notice the complete reversal of direction: Stepanov's method is **native to $\mathbb F_q(X)$**, and
Alpöge's 175,187-file archive is an effort to build a substitute for Frobenius/Hasse–Schmidt
multiplicity over $\mathbb Z$; Masullo's trace-formula method is designed around the prime-by-prime
incommensurability of $\log p$ over **number fields**, and breaks down over $\mathbb F_q(X)$ because
all closed-point norms are powers of a single $q$!

---

## 6.6 Lean counterpart for this chapter

Every Lean file listed below was read in full by us (`R3` / `[Lean, read]`), except that the last two
rows (Section 6.4.5) list single declarations read line by line in files not read in full. Upstream
constructions that *inhabit* `FamP` and `ChainTied` belong to Chapters 7–12 (`P17`, `P8`–`P12`).

| Declaration | File:line | Mathematical content / role in Sections 6.3–6.4 | Tag |
|---|---|---|---|
| `Scale`, `Scale.L`, `b`, `a`, `X'`, `b'`, `w''`, `X''`, `delta1`, `Formalism.BasicNotions.SizeData₂`, `SizeData₂.AdmT`, `lifts`, `Fo`, `Ga`, `Ee`, `MAIN`, `VV` | `src/Formalism/LocalRingCardinality/DataParams₂.lean:9,27,29,31,33,35,37,39,45,76,186,208,218,220,222,232,238` | Concrete scale record (`L = x^ε`, `b = exp(x^ε)`, `delta1 = x^{-ε/8}`), concrete `D7`-attached `SizeData₂` structure (`:76–182`), and derived definitions `Fo`, `Ga`, `Ee`, `MAIN`, `VV` in `namespace SizeData₂`. | [Lean, read] |
| `GlobalTheory.Mem.Num.evenCeil`, `eAt`, `nAt`, `fAt`, `mAt`, `kAt`, `rAt`, `tAt`, `NAt`, `RanksOK`, `ranksOf`, `HCIn`, `HCIn.OK`, `HCIn.hc` | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:11,15,17,19,21,23,25,33,35,41,45,92,100,109` | Section 6.2.2 & 6.5.2: even ceiling `2 * ⌈y / 2⌉₊`, chain length `mAt` $\approx \sqrt{x\delta_1}$, $2$-power tower `nAt = 2^(eAt)`, rank admissibility `RanksOK`, and verified rational Harish-Chandra parameters `HCIn.hc`. | [Lean, read] |
| `ph`, `wmean`, `umean`, `Consts`, `Data`, `Data.s`, `uF`, `Main`, `HidaSetting`, `DIV`, `HComp`, `Slopes`, `SlopeIneq`, `HHBound`, `FParams` | `src/Formalism/RankGapBounds/MeanBoundSecondForm.lean:9,11,13,15,37,92,94,107,111,118,126,139,151,158,161` | Definition 6.2: abstract numerical chain record `Data U0 W Top m f`, weighted mean slope `s`, slope spread `uF`, global divisibility clause `DIV`, and Bost slope inequality clause `SlopeIneq`. | [Lean, read] |
| `wmean_le_const`, `sub_wmean_le`, `phi_bound`, `Data.SDiv`, `EDiv`, `K3`, `Data.key_identity` | `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:34,40,81,129,131,138,170` | Lemma 6.5: weighted-mean inequalities, logarithmic concavity bound $u\log(1+H/u) \le \log(1+X)(U+b)$, and exact cancellation of $\log(\pi/v)$ and $\mathrm{lg}$ into `Main`. | [Lean, read] |
| `Lo5`, `QuotientSlopeBoundsWith`, `EComp5`, `Count5`, `LossBounds`, `MLo5`, `UBar5`, `ErrX5at`, `PointwiseBoundVariant` | `src/Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:15,19,24,27,34,37,41,45,72` | Definition 6.2: remaining clauses of `SizeData₂` (`QuotientSlopeBoundsWith`, `EComp5`, `Count5`, `LossBounds`) and pointwise error bracket `ErrX5at`. | [Lean, read] |
| `s_lower5`, `Vvar_bound5`, `u_function_le_mean`, `key_identity5`, `Ga_bound5`, `weighted_mean_lower_bound_le`, `each_unit_bound_statement`, `uniform_bound_statement` | `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:50,68,81,105,113,162,175,237` | Theorem 6.6: complete formal deduction of `ASK u0 ≤ Main u0 + ErrX5at` from the 11 clauses of `SizeData₂`. | [Lean, read] |
| `Formalism.LFunctionChainParameters.LChain.SizeData₂`, `Ident`, `BNBounds`, `CostWindows`, `RestSize`, `ChainCore` | `src/Formalism/SizeWindowBrackets/SChain.lean:17,26,33,50,53,60` | Definition 6.2: 11-clause `SizeData₂` conjunction, non-compounding budgets $B_0, N_c$ (`BNBounds`), scale windows, and `ChainCore`. | [Lean, read] |
| `wt_self`, `coverS_of_cover`, `FamCore`, `FamCore.Windows`, `FamCore.coverS_carry` | `src/Formalism/SharpRestriction/FamCore.lean:27,47,71,155,187` | Core family structure across scales $x \in \mathrm{Win}$ and shift-covering transfer across $u_0 < n$. | [Lean, read] |
| `NoGain`, `FamP`, `DFamP` | `src/Formalism/SharpRestriction/ParConsts.lean:24,31,99` | Enriched chain-family structure `FamP eps` extending `FamCore eps` with lattice ties, dropped-prime criteria, and pinned constants. | [Lean, read] |
| `TiePts`, `TieGlobal`, `TieLocal`, `TieArith`, `ChainTied`, `ChainTied.core_of` | `src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:39,50,63,84,97,116` | Bridges a family `Fm : FamP eps` (`D7` + `BasicNotions.SizeData₂`) to `Data` + `LChain.SizeData₂` (`ChainCore` / `CoreAtH`). | [Lean, read] |
| `Mod.data`, `Mod.Ee_eq`, `Mod.model_slopes_five`, `Mod.s_eq`, `SlopesN_at`, `LoU`, `SlopesNF` | `src/Formalism/SharpRestriction/GlobalSchurBounds/QuadraticLogDerivCongr.lean:464,671,677,687,181,177,254` | Section 6.4.5 (Proposition 6.11): the main-path `Data` record, with ranks as weights and `HLat.mu` as slopes; Clause 7 transported from `SlopesN_at`; `Data.s = sFrame`. | [Lean, read] |
| `HLat`, `HLat.rank`, `HLat.mu`, `dU`, `Rsum`, `sFrame`, `DivData`, `sizeOfVal` | `src/Formalism/LocalRingCardinality/DataArith.lean:61,82,84,127,129,131,139,46` | Section 6.4.5 (Definition 6.7): hermitian $\mathcal O_K$-lattices, the archive-normalized slope, and the rank-weighted frame average. | [Lean, read] |

**Summary of the chapter.** Over a finite field $\mathbb F_q$, Stepanov's and Bombieri's auxiliary
polynomial $\Phi = \sum_{b=1}^B s_b u_b^Q$ combines Hasse–Schmidt divided-power derivations $D_t^{(k)}$
(Lemma 6.1, which treat $Q$-th powers as constants for $k < Q$) with distinct-valuation linear
independence (Lemma 6.2, valid for $r < Q$) to force vanishing of multiplicity $m$ at rational points,
dividing the leading pole cost by $m$ and balancing $Q/m + m$ at $m \asymp \sqrt{Q}$ to prove the
Hasse–Weil bound $\lvert \#C(\mathbb F_q) - (q + 1) \rvert \le 2g\sqrt{q}$ (Theorem 6.3) and Weil's
character-sum bounds (Corollary 6.4) `[Stepanov1969]`, `[Bombieri1973]`, `[Schmidt1976]` [Expository].
Over $\mathbb Z$, node `P7` of the Lean archive mirrors this zero-versus-pole comparison in genuine
`sorry`-free algebra (`each_unit_bound_statement`, Theorem 6.6) [Lean, read]: given the 11-clause
package `SizeData₂` at even chain length `mAt` $\approx \sqrt{x\delta_1}$ (`src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:21`),
$m$-step inert-prime divisibility (`DIV`) bounds the weighted mean slope $s(u_0)$ from below while
Bost's slope inequality (`SlopeIneq`) bounds $s(u_0)$ from above, cancelling $\mu_{CC}(u_0)$ and
$\log(\pi/v)$ (`key_identity5`) to bound `ASK` by `Main + ErrX5at`. On the main path the weights in
$s(u_0)$ are lattice ranks, $s(u_0)$ is the frame average `sFrame`, and Clause 7 is transported from
`SlopesN_at` by `model_slopes_five` (Section 6.4.5). How the archive actually builds
$m$ commuting "derivatives" over a CM field out of **iterated theta lifts** is the subject of Chapter 7.
