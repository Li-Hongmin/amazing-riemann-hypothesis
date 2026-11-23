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

---

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

Every Lean file listed below was read in full by us (`R3` / `[Lean, read]`). Upstream constructions
that *inhabit* `FamP` and `ChainTied` belong to Chapters 7–12 (`P17`, `P8`–`P12`).

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
$\log(\pi/v)$ (`key_identity5`) to bound `ASK` by `Main + ErrX5at`. How the archive actually builds
$m$ commuting "derivatives" over a CM field out of **iterated theta lifts** is the subject of Chapter 7.
