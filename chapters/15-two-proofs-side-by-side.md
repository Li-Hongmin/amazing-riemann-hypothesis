# Chapter 15. Two proofs side by side

> **Status tags used in this chapter:** `[Lean, read]` for declarations and `sorry`-free proofs in
> Alpöge's archive verified line by line across Chapters 1–13 (`R3`); `[Lean]` for statement-level
> archive declarations whose deep proof cones remain unread (`R2`); `[Paper; remark p. …]` and
> `[Paper; Masullo p. …]` for the two primary announcements/manuscripts; `[Community]` for public
> verification and formalization records; `[Expository]` for our structural synthesis and the running
> $\chi_{-4}$ comparison; `[Open]` for unread proof cones and unresolved manuscript gaps.

Never before in the history of mathematics have two serious, full-length attempts at the Riemann
Hypothesis arrived on the very same day in forms so diametrically opposite.

On 20 November 2026:

- **Levent Alpöge (working with Claude)** posted a four-page informal timeline (`remark.pdf`) [Paper;
  remark pp. 1–4] together with a **239 MB, 175,187-file, 17.37-million-line Lean 4 archive** whose
  top file `src/Main.lean` (`:4, 6, 8, 10, 12`) [Lean, read] compiles cleanly and passes multiple
  independently written proof kernels (`leanchecker`, `nanoda`, `con-leche --compare`, `con-ron --compare`,
  `lean4lean`) `[Community]`, proving Mathlib's `RiemannHypothesis` and the Generalized Riemann
  Hypothesis for all Dirichlet $L$-functions over $\mathbb Q$ — with **zero pages of human-readable
  proof prose** released alongside it, and more than 140,000 used modules still unread by human
  specialists `[Open]`.
- **Alessandro Maria Masullo** released a **940-page human-written manuscript**, *The Music of the
  Primes* [Paper; Masullo p. 1], written with classical definitions, motivations, and footnotes over
  nearly twelve years without AI [Paper; Masullo p. 6] `[Community]`, targeting the Generalized
  Riemann Hypothesis for **all unitary Hecke $L$-functions of all number fields $F$** — with Chapter 13
  (`pp. 521–522`) still an unwritten placeholder, Section 12.3 (`p. 514`) omitted, and a public
  functional-analytic gap in Chapter 10 (`pp. 444, 451, 463`) that remains unrepaired on positive-width
  strips $I = [-\alpha, \alpha]$ `[Open]`.

Even more remarkably, the contrast is **not** merely one of presentation (machine code versus human
prose): **their mathematical engines share almost zero common theorems beyond Euler products,
functional equations, and the link between prime powers and nontrivial zeros!** Placing the two routes
side by side — first on a single concrete Dirichlet character $\chi_{-4} \bmod 4$, and then across five
sharp structural dimensions — illuminates both what makes the Riemann Hypothesis so resistant to purely
local/analytic manipulations and what each architecture supplies where the other is silent.

---

## 15.1 Motivation: why comparing two disjoint architectures clarifies the barrier to RH

Step back and ask what every attempted proof of the Riemann Hypothesis has to overcome (`[Bombieri2000]`,
`[IwaniecKowalski2004]`) [Expository]:

1. **Analytic continuation hides the Euler product.** On $\Re s > 1$, $L(s, \chi) = \prod_p (1 - \chi(p) p^{-s})^{-1}$
   cannot vanish because a convergent Euler product of nonzero factors is nonzero. Inside the critical
   strip $0 < \Re s < 1$, the Euler product diverges, and zeros arise from subtle destructive
   interference among primes.
2. **Functional equations enforce symmetry about $\Re s = \frac{1}{2}$, not concentration on $\Re s = \frac{1}{2}$.**
   Tate's thesis `[Tate1967]` and Poisson summation pair every hypothetical off-line zero $\rho = \beta + i\gamma$
   ($\beta > \frac{1}{2}$) with its reflection $1 - \overline{\rho} = (1 - \beta) + i\gamma$
   ($1 - \beta < \frac{1}{2}$). Any linear identity built solely from Poisson summation and Mellin
   inversion (such as Weil's explicit formula `[Weil1952]`) is automatically satisfied by such a
   symmetric off-line pair $(\rho, 1 - \overline{\rho})$!

How do our two routes try to break that off-line symmetry?

- **Alpöge–Claude's arithmetic Stepanov route (Parts I–III, nodes `P0`–`P18`):** Never sums over all
  zeros at once and never uses a two-sided explicit formula! Instead, it uses **Landau/Pólya real
  Laplace positivity** (`P5`, Chapter 3) to reduce zero-freeness right of $\frac{1}{2}$ to a
  **one-sided upper bound** $G_m(x) \le x^{1/2 + O(\varepsilon)}$ on Riesz-weighted prime sums over
  sparse scale windows $[Y, Y^{1+\delta}]$, and then builds an **algebraic-geometric global height
  machine** (`P7`–`P12`, Chapters 6–11): $m \asymp \sqrt{x}$ iterated unitary theta lifts accumulate
  odd-power $p$-adic divisibility at inert primes (`P8`), Bost's Arakelov slope inequality (`P9`) and
  Hilbert–Schmidt near-orthogonality (`P10`) convert that divisibility into a global bound on `ASK`,
  and Galois cohomology + Iwasawa/$U(3)$ modularity (`P11`–`P12`) cap the Hecke congruence denominators
  at $\exp(x^\varepsilon/2)$!
- **Masullo's topological trace-formula route (Chapter 14):** Stays entirely on $\mathrm{GL}_1(\mathbb A_F) / F^\times = C_F$
  and tries to **break symmetry topologically** (`§1.4.8`, [Paper; Masullo p. 31]): by completing the
  divisor quotient $\mathcal H_F$ inside the strip-weighted Hardy–Sobolev space $W_{[-\alpha, \alpha]}^{s,2}(C_F)$,
  zeros with $\lvert \Re \rho - \frac{1}{2}\rvert > \alpha$ are excluded from the continuous dual
  spectrum (`Ch. 10`), while the geometric prime-shell decomposition (`Chs. 11–12`) is claimed to
  evaluate to the **same $\alpha$-independent distribution** for every $\alpha > 0$ (`Theorem 12.5.1.1`,
  p. 519)!

---

## 15.2 Running worked example: following $\chi_{-4} \bmod 4$ step by step through both routes

To see every gear of both machines mesh on a single concrete $L$-function, fix the unique primitive
non-principal Dirichlet character modulo $N = 4$:
$$\chi_{-4}(n) := \begin{cases} +1 & \text{if } n \equiv 1 \pmod 4, \\ -1 & \text{if } n \equiv 3 \pmod 4, \\ 0 & \text{if } 2 \mid n,\end{cases}
\qquad
L(s, \chi_{-4}) = 1 - \frac{1}{3^s} + \frac{1}{5^s} - \frac{1}{7^s} + \frac{1}{9^s} - \frac{1}{11^s} + \cdots$$
(the Dirichlet beta function $\beta(s)$, whose Dedekind product $\zeta(s)\,L(s, \chi_{-4}) = \zeta_{\mathbb Q(i)}(s)$
is the Dedekind zeta function of the Gaussian field $\mathbb Q(i)$!) [Expository].

### 15.2.1 Route A: $\chi_{-4}$ inside the Alpöge–Claude Lean archive (`P0` $\to$ `P18`)

Trace $\psi := \chi_{-4}$ (`N = 4`, `ψ.IsPrimitive`) from `src/Main.lean` down to `VWin`:

1. **Target statement and functional-equation reduction (`P0`–`P1` & `P3`, Chapters 1–2):**
   At `src/Main.lean:8` and `:12` (`LFunction_ne_zero_of_half_lt_re` and `LFunction_eq_zero_re_of_isPrimitive`,
   defined in `src/Statements.lean:6, 14`) [Lean, read], the archive instantiates $N = 4$ and
   $\chi = \chi_{-4}$. Since $\chi_{-4}$ is odd ($\chi_{-4}(-1) = -1$), its completed $L$-function is
   $\Lambda(s, \chi_{-4}) = (4/\pi)^{(s+1)/2}\,\Gamma\bigl(\frac{s+1}{2}\bigr)\,L(s, \chi_{-4})$,
   satisfying $\Lambda(s, \chi_{-4}) = \Lambda(1 - s, \chi_{-4})$. In `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:42, 59`
   (`prim_reflect`, `Claim.strip`) [Lean, read], nonvanishing of $\Gamma\bigl(\frac{s+1}{2}\bigr)$ on
   $0 < \Re s < 1$ reduces all critical-strip zeros of $L(s, \chi_{-4})$ to `EveryCharacter`
   ($L(s, \chi) \neq 0$ for $\Re s > \frac{1}{2}$).
2. **Cyclic level $\Lambda_{\mathrm{cyc}}(\chi_{-4})$ and Riesz prime sum (`P4`–`P5`, Chapter 3):**
   Because $\chi_{-4}$ has multiplicative order $2$ in $(\widehat{\mathbb Z/4\mathbb Z})^\times$, its
   cyclic level (`Level.cyc`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:121`) [Lean, read] consists of
   just **two** characters modulo $4$: the imprimitive principal character $\chi_{0, 4} = \chi_{-4}^0$
   ($\mathbf{1}_{\text{odd}}$) and $\chi_{-4} = \chi_{-4}^1$! Look at their individual and combined
   Riesz-weighted prime sums $G_\chi(x) = \sum_{n \le x} \Lambda(n)\,\chi(n)\,\bigl(\frac{x}{n} - 1\bigr)$
   (plus the smooth subtraction of the $s = 1$ pole for $\chi_{0, 4}$ in `An.gChi`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:23`)
   [Lean, read]: before pole subtraction, the raw prime sums take the exact numerical values:

   | Scale $x$ | $\sum_{n \le x, \text{ odd}} \Lambda(n)(x/n - 1)$ | $G_{\chi_{-4}}^{\mathrm{raw}}(x) = \sum_{n \le x} \Lambda(n)\chi_{-4}(n)(x/n - 1)$ | Sum over $\{1, \chi_{-4}\}$ ($\equiv 1 \bmod 4$ odd powers!) |
   |---|---|---|---|
   | $10$ | $5.128896$ | $-1.665884$ | $3.463012 = 2\bigl(\frac{10}{5}-1\bigr)\log 5 + 2\bigl(\frac{10}{9}-1\bigr)\log 3$ |
   | $20$ | $20.008355$ | $-3.904020$ | $16.104335$ |
   | $50$ | $88.511301$ | $-11.589000$ | $76.922301$ |
   | $100$ | $240.444346$ | $-24.513189$ | $215.931157$ |

   Look at column 4 at $x = 10$: summing over the cyclic group $\{1, \chi_{-4}\}$ **annihilates the
   primes $3, 7 \equiv 3 \pmod 4$ with negative $\chi_{-4}(n) = -1$** and leaves a **nonnegative** sum
   supported on odd $n \equiv 1 \pmod 4$ ($n = 5$ and $n = 3^2 = 9$)! After subtracting the $s = 1$
   main term $x$, Landau's monotonicity theorem on windows (`Deduction.landau_window`,
   `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean:83`) [Lean, read] says: *if for every small $\varepsilon > 0$ there exist
   arbitrarily large windows $[Y, Y^{1+\delta}]$ on which $\Lambda.\mathrm{Gm}(x) \le x^{1/2 + C\varepsilon}$,
   then neither $\zeta(s)$ nor $L(s, \chi_{-4})$ has a zero on $\Re s > \frac{1}{2} + C\varepsilon$!*
3. **Auxiliary prime pair $(q, d)$ and CM host field $E$ (`P13`, Chapter 4):**
   Fix a tiny $\varepsilon \in (0, \frac{1}{52})$ (`src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:26`) and a large scale $Y$.
   The two-stage sieve `QH.pairEx` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/pairEx.lean:112`) [Lean, read] selects primes
   $q \equiv 3 \pmod 8$ ($\log q \asymp Y^{\varepsilon/5}$) and $d \equiv 7 \pmod{16}$
   ($\log d \asymp Y^{\varepsilon/5}(\log Y)^2$) such that $2$ (the sole prime factor of $N = 4$) and
   $q$ split appropriately while parasitic quadratic twists have $O(x^{1/2})$ prime-sum bounds and
   zero-free boxes of width $\frac{1}{400}$. For $x \in [Y, Y^{1+\delta}]$, let $2^e \asymp x^{2+8\varepsilon}$
   (`eAt`, `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:15`); then the host field $E \subset \mathbb Q(\zeta_{2^e \cdot 4 q d})$
   (`IsChiField`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:19`) [Lean, read] is an **abelian CM field** (complex conjugation
   excluded from its fixing subgroup because $q \equiv 3 \pmod 8$!) containing the character $\chi_{-4}$
   alongside the Jacobi symbols mod $q, d$ and the $2^e$-cyclotomic tower!
4. **The $m \asymp \sqrt{x}$ theta-lift chain, inert divisibility, Bost slope, and `VWin` (`P6`–`P12`, Chapters 5–11):**
   Set $m := 2\lceil\sqrt{x\delta_1}/2\rceil \asymp \sqrt{x}$ (`mAt`, `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/EvenCeil.lean:21`) [Lean, read].
   Across $m$ definite unitary theta lifts (`HypsAlt`, `P17`), primes $p$ inert in the imaginary
   quadratic core $\mathbb Q(\sqrt{-d})$ produce odd-power $p$-adic divisibility
   $\sum_{i\text{ odd}} \max(a_T/p^i - w_{\mathrm{Part}}, 0)$ (`vonMangoldtClassSum`, `P8`); finite
   abelian Fourier inversion (`gmA_eq`, Chapter 5) projects that `ASK - MAIN` difference onto the
   $\chi_{-4}$-coset; Bost's slope inequality (`SlopeIneq`, `P9`) and stretched-exponential Gram decay
   $\exp(-x^{\varepsilon/8})$ (`LinkS`, `P10`) turn divisibility into a global upper bound; GMA Fitting
   ideals (`CutCoreUnit.main`, `P11`) reduce Hecke congruence denominators to
   $\sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)$ (`R.t \le \lfloor x^{400}\rfloor`); and `VWin`
   (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`, `P12`) bounds that $\log \ell$-weighted $Ш^1$ sum by $\exp(x^\varepsilon/2)$
   using Sinnott/Ferrero–Washington on $E^-$ and $U(3)$ congruences on $E^+$, closing
   $G_m(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}$ (`core_gm`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12`) [Lean, read]!

### 15.2.2 Route B: $\chi_{-4}$ inside Masullo's trace-formula draft (`Chs. 2–13`)

Now feed the **exact same character $\chi_{-4}$** into Masullo's *The Music of the Primes*:

1. **Idelic realization on $C_{\mathbb Q} \cong \mathbb R_{>0} \times \widehat{\mathbb Z}^\times$ (`Chs. 2–3`, pp. 57–154):**
   Take $F = \mathbb Q$ ($[F : \mathbb Q] = 1$) and view $\chi_{-4}$ as the unitary character of
   $C_{\mathbb Q}^1 = \widehat{\mathbb Z}^\times$ pulled back from
   $\widehat{\mathbb Z}^\times \twoheadrightarrow \mathbb Z_2^\times / (1 + 4\mathbb Z_2) \cong \{\pm 1\}$,
   ramified only at the two-element set of places $S = \{\infty, 2\}$ (`\mathrm{Pic}(\mathbb Z[1/2]) = 1`).
   As we computed by hand in Section 14.2.1, $f_{\chi_{-4}}(x_\infty, x_f) = x_\infty e^{-\pi x_\infty^2}(\mathbf{1}_{1+4\mathbb Z_2} - \mathbf{1}_{3+4\mathbb Z_2})\prod_{p \ge 3}\mathbf{1}_{\mathbb Z_p}$
   already lies in $\mathcal S_0(\mathbb A_{\mathbb Q})$ (`p. 91`), and $\lvert \cdot \rvert_{\mathbb Q}^{1/2}\Phi_{\mathbb Q}(f_{\chi_{-4}})$
   has Mellin transform $\pi^{-(s+3/2)/2}\Gamma\bigl(\frac{s+3/2}{2}\bigr)L(s + \frac{1}{2}, \chi_{-4})$,
   with $\delta(\chi_{-4}) = 0$ (no pole at $s = \pm \frac{1}{2}$!).
2. **Local transition operators and Polar Multiplicities (`Chs. 5–7`, pp. 221–380):**
   At every odd prime $p \ge 3$, $\chi_{-4}$ is unramified with local Frobenius sign $\chi_{-4}(p) = (-1)^{(p-1)/2}$,
   so Weil's principal value operator $(PV_p f_p)(x_p) = f_p(x_p) - f_p(p^{-1} x_p)$ (`p. 240`) strips
   $(1 - (-1)^{(p-1)/2} p^{-s-1/2})^{-1}$. Because $[F : \mathbb Q] = 1$, no two distinct odd primes
   $p \neq q$ share a pole of $(1 - \chi_{-4}(p)p^{-z})^{-1}$ (`Theorem 7.1.3.2`, p. 324), so Masullo's
   Sobolev threshold is simply **$s \ge 2[\mathbb Q : \mathbb Q] = 2$**!
3. **Strip Hardy–Sobolev completion $W_{[-\alpha, \alpha]}^{2, 2}\mathcal H_{\mathbb Q}(\chi_{-4})$ (`Chs. 9–10`, pp. 395–474; `Ch. 9` pp. 395–432, `Ch. 10` pp. 433–474):**
   For $\alpha \in (0, \frac{1}{2})$, completing the $\chi_{-4}$-quotient in weight
   $\max\{t^{-2\alpha}, t^{2\alpha}\}(1 + (\log t)^2)^{s/2}$ (at $s = 2$, exponent $s/2 = 1$) restricts dual eigenmodes $t^{\rho - 1/2}$ to
   zeros of $L(\rho, \chi_{-4})$ in $\frac{1}{2} - \alpha \le \Re \rho \le \frac{1}{2} + \alpha$ (`p. 446`).
4. **Geometric trace (`Chs. 11–12`, pp. 475–520) — and the double stall (`pp. 451, 463, 514, 521–522`):**
   For a smooth test function $\varphi \in C_c^\infty(\mathbb R_{>0})$ vanishing at the identity coset ($\varphi(1) = 0$, i.e. pointwise $\varphi(C_F^1) = 0$, `pp. 28, 514, 519`),
   `Theorem 12.5.1.1` (`p. 519`) asserts that the trace on $W_{[-\alpha, \alpha]}^{2, 2}\mathcal H_{\mathbb Q}(\chi_{-4})$
   equals the $\alpha$-independent explicit-formula sum over odd prime powers
   $-\sum_{p \ge 3} (\log p) \sum_{k \neq 0} (-1)^{(p-1)\lvert k\rvert/2} p^{-\lvert k \rvert/2}\varphi(p^k)$
   plus the $\{\infty, 2\}$ local Weil integrals (`§12.4`, p. 518). **Here the argument stalls at the
   exact points analyzed in Chapter 14:** close vertical pairs of critical-line zeros of $L(s, \chi_{-4})$
   refute the uniform biorthogonal bound invoked at `(10.3.1.18)` (`p. 451`) and `(10.4.2.24)` (`p. 463`),
   `§12.3` (`p. 514`) is unwritten, and `Theorem 13.3.1.2` (`p. 522`) is blank `[Open]`!

Notice how vividly $\chi_{-4}$ contrasts the two philosophies: **Alpöge's archive surrounds $\chi_{-4}$
with an enormous auxiliary tower** $\mathbb Q(\zeta_{2^e \cdot 4 q d})$, higher-rank unitary groups
$U(X_j)$, and $U(3)$ Galois cohomology just to bound a finite prime sum on $[Y, Y^{1+\delta}]$, whereas
**Masullo stays directly on $\mathbb R_{>0} \times \mathbb Z_2^\times / (1 + 4\mathbb Z_2)$** — and hits
the full infinite-dimensional analytic resistance of strip-holomorphic quotient spaces head-on!

### 15.2.3 Top-to-bottom dependency spines compared on one screen

To anchor every `file:line` and page reference before we dissect the five structural axes, compare the
exact top-to-bottom deduction chain of `src/Main.lean` (`P0` $\to$ `P18`) [Lean, read] against the intended
deduction chain of Masullo's manuscript (`Ch. 13` $\Leftarrow$ `Chs. 2–12`) [Paper]:

1. **Alpöge–Claude's verified Lean call spine (`src/Main.lean` $\to$ four foundational pillars):**
   - `src/Main.lean:4, 6, 8, 10, 12` (`riemannHypothesis`, `LFunction_ne_zero_of_half_lt_re`, etc.)
     calls `allChi`, `rhOfAll`, `critAll`, `claimAll` in `src/Supplements/Kernels/MainTheorems.lean:7, 9, 11, 15`
     (`P0`–`P1`) [Lean, read];
   - `allChi` invokes `UpperTheory.FinalTheorems.everyCharacter` in
     `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean:10` (`:7`
     `everyCharacter_of_row`), which assembles four global pillars (`P2`) [Lean, read]:
     - **Pillar A (`Row0b`, `P14`):** CM automorphic Galois representations via
       `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`;
     - **Pillar B (`RecTExists`, `P15`):** partial local Langlands laws via
       `src/Development/AutomorphicArithmetic/Foundations/LocalLanglands/LocalCentralUnits/RecTExists.lean:20`;
     - **Pillar C (`VWin`, `P12`):** the $\exp(x^\varepsilon/2)$ cyclotomic $\mathrm{Ш}^1$ window bound
       via `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`;
     - **Pillar D (`OpenLiteratureStatements` + `HypsAlt` + `Green`, `P16`–`P18`):** discharged in
       `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean:810`
       $\to$ `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean:69` (regularized Siegel–Weil
       first/second term matching descending from `[Weil1965]` and `[KudlaRallis1994]`) $\to$
       `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12, 16` (`zero_free_all_of_green_v_win`) [Lean, read];
   - inside `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/TopPlug.lean:12`, `TopG` feeds `src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean:26`
     (`P4`), which combines `formB` (`P5`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean:83`),
     `supplyChi` (`P13`, `src/Development/AutomorphicArithmetic/CharacterBoxes/SupplyChi.lean:8`), and
     `core_gm` (`P6`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12`) to let
     $\varepsilon \downarrow 0$ and close `EveryCharacter`!
2. **Masullo's intended manuscript spine (`Ch. 13` $\Leftarrow$ `Chs. 2–12`):**
   - Unwritten `Theorem 13.3.1.2` (`p. 522`, `[Open]`) is intended to follow via one-sided test
     approximations $\varphi_z(t) = t^{-z}\mathbf{1}_{t > 1}$ (`§1.4.2–1.4.5`, `pp. 28–30`; formalized
     conditionally by Loeffler `[Community]`) from `Theorem 12.5.1.1` (`pp. 519–520`) [Paper];
   - `Theorem 12.5.1.1` equates the **spectral trace** on $W_{[-\alpha, \alpha]}^{s,2}\mathcal H_F$
     (`Ch. 10`, stalled at `Terminology 10.2.1.2(2)` on `p. 444`, `(10.3.1.18)` on `p. 451`, and
     `(10.4.2.24)` on `p. 463` `[Open]`) with the **geometric shell + $S$-local trace** (`Chs. 11–12`,
     resting on `Theorem 11.3.2.1` `p. 495`, omitted `§12.3` `p. 514`, and `(12.4.1.17)` `p. 518` `[Open]`),
     built atop Hardy–Sobolev strip completions (`Ch. 9`), Polar Multiplicities (`Thm. 7.1.3.2` `p. 324`),
     Structure Theorems I–V (`Chs. 5–6`, where the printed proof of `Thm. 5.2.1.1` `p. 230` is flagged
     in `mccorvie/riemann-masullo` `[Community]`), and Tate's $\mathrm{GL}_1$ thesis (`Chs. 2–3`)!

---

## 15.3 Exact definitions of the five structural comparison axes

To make our side-by-side comparison completely systematic, we organize every difference between the two
routes along **five structural axes** [Expository]:

**Definition 15.1 (The five structural axes comparing Alpöge–Claude and Masullo).**

1. **Axis I — Theorem scope and statement surface:** Which class of $L$-functions is covered, how the
   target propositions are stated (`src/Statements.lean:3, 6, 10, 14` and Mathlib's `RiemannHypothesis`
   [Lean, read] versus Masullo `p. 6` and `pp. 521–522` [Paper; Masullo pp. 6, 521–522]), and where
   abelian versus non-abelian Dedekind zeta functions sit.
2. **Axis II — The analytic zeros $\leftrightarrow$ primes bridge:** How locations of zeros are
   connected to prime powers: **one-sided** Riesz-weighted prime sums + real Laplace pole monotonicity
   on sparse windows (`Deduction.landau_window`, `P5` [Lean, read]) versus a **two-sided** distributional
   convolution trace on $C_F$ for test functions vanishing on the norm-$1$ fiber $\varphi(C_F^1) = 0$ (`Theorem 12.5.1.1`,
   [Paper; Masullo p. 519]).
3. **Axis III — Exact origin of the critical exponent $\frac{1}{2}$:** How the number $\frac{1}{2}$
   emerges algebraically/analytically: discrete AM–GM balancing of $x/m + m\,x^{O(\varepsilon)}$ at
   chain length $m \asymp \sqrt{x}$ (`core_gm` / `proposition_size_bound`, `P6`–`P7` [Lean, read])
   versus continuous diagonal Haar-measure matching $\lvert x \rvert_{F, S}^{2a - 1} = 1 \iff a = \frac{1}{2}$
   (`§1.2.3` p. 16 & `§12.4.1` p. 518) coupled with asserted $\alpha$-independence of strip completions
   (`Theorem 12.5.1.1`, p. 519).
4. **Axis IV — Mathematical engine and the opposite roles of $\mathbb F_q(X)$:** Non-Archimedean
   arithmetic geometry + automorphic congruences + Galois cohomology (`P7`–`P18`, modeled directly on
   Stepanov's $\mathbb F_q(X)$ proof `[Stepanov1969]`, `[Bombieri1973]`) versus locally convex nuclear
   functional analysis on $\mathrm{GL}_1(\mathbb A_F)/F^\times$ (`Chs. 4–12`, which **provably breaks
   down** over $\mathbb F_q(X)$ in `§14.2`, [Paper; Masullo pp. 534–536]!).
5. **Axis V — Epistemic and verification asymmetry:** Machine-checked formal proof terms with zero
   `sorry`s across 175,187 modules (`[Lean]` / `[Community]`) whose deep mathematical proof bodies
   remain largely unread by humans (`[Open]`) versus a 940-page human-readable draft with transparent
   motivations (`[Paper]`) whose central analytic step (`Ch. 10`) and final deduction (`Ch. 13`) remain
   incomplete (`[Open]`).

---

## 15.4 Structural propositions across the five axes

Let us analyze each of the five axes in turn, proving the exact structural relationships that govern
them.

### 15.4.1 Axis I: Scope hierarchy — Dirichlet $L$-functions versus all unitary Hecke characters

**Proposition 15.1 (Strict inclusion of $L$-function scopes).** *Consider the following four nested
classes of global $L$-functions:*
$$\bigl\{\zeta(s)\bigr\}
\;\subsetneq\; \bigl\{\text{Dirichlet }L(s, \chi)\text{ over }\mathbb Q\bigr\}
\;\subsetneq\; \bigl\{\text{unitary Hecke }L(s, \chi)\text{ over all number fields }F\bigr\}
\;\subsetneq\; \bigl\{\text{autom. }\mathrm{GL}_n(\mathbb A_{\mathbb Q})\ L\text{-functions}\bigr\}.$$

1. *Alpöge's `src/Main.lean` (`:4, 6, 8, 10, 12`) [Lean, read] proves GRH for the **second** class
   (`EveryCharacter`: all Dirichlet $L(s, \chi)$ over $\mathbb Q$, hence by Kronecker–Weber also
   Dedekind $\zeta_K(s)$ for every **abelian** number field $K / \mathbb Q$), and states **no** theorem
   for Hecke characters of number fields $[F : \mathbb Q] > 1$ or Dedekind $\zeta_K(s)$ of **non-abelian**
   extensions $K / \mathbb Q$ (Alpöge remarks on `remark.pdf` p. 1 that he expects the method to give
   ERH "with more time" [Paper; remark p. 1], `[Open]`).*
2. *Masullo's manuscript targets the **third** class: all unitary Hecke characters $\chi$ of all number
   fields $F$ [Paper; Masullo p. 6], which includes $\zeta_K(s)$ for **every** finite extension
   $K / \mathbb Q$ (abelian or non-abelian, taking $F = K$ and $\chi = \mathbf{1}$!) as well as CM
   elliptic-curve $L$-functions via Deuring's theorem (`§14.1.2`, [Paper; Masullo pp. 531–532]).* [Expository]

*Proof.* Over $F = \mathbb Q$, finite-order unitary characters of $C_{\mathbb Q} \cong \mathbb R_{>0} \times \widehat{\mathbb Z}^\times$
trivial on $\mathbb R_{>0}$ correspond bijectively to primitive Dirichlet characters $\chi$, while
characters $t \mapsto t^{i\tau}$ on $\mathbb R_{>0}$ merely shift $L(s, \chi)$ vertically to
$L(s + i\tau, \chi)$, so unitary Hecke GRH over $F = \mathbb Q$ is equivalent to Dirichlet GRH.
Conversely, for any number field $K / \mathbb Q$ with $[K : \mathbb Q] > 1$:
- If $K / \mathbb Q$ is **abelian**, the Kronecker–Weber theorem embeds $K \subseteq \mathbb Q(\zeta_N)$
  for its conductor $N \ge 1$, and class field theory factors $\zeta_K(s) = \prod_{\chi \in X(K)} L(s, \chi^\ast)$
  into primitive Dirichlet $L$-functions over $\mathbb Q$, so `EveryCharacter` implies RH for $\zeta_K(s)$.
- If $K / \mathbb Q$ is **non-abelian** (for example $K = \mathbb Q(\sqrt[3]{2})$, analyzed in full in
  Section 16.2.1) or if $\chi$ is an infinite-order Grossencharacter of an imaginary quadratic field
  such as $\mathbb Q(i)$ (`[Hecke1920]`, e.g. $\chi((a + bi)) = \bigl(\frac{a + bi}{\lvert a + bi \rvert}\bigr)^{4k}$
  for $k \ge 1$), $L(s, \chi)$ is an Euler product of degree $2$ over $\mathbb Q$ (a weight-$(4k+1)$
  cuspidal CM modular form) that **cannot** be factored into degree-$1$ Dirichlet $L$-functions over
  $\mathbb Q$! Thus the third class strictly contains the second. $\square$

*(Remark on internal versus external scope.)* Notice a fascinating irony inside Alpöge's archive:
although `src/Main.lean` only **outputs** GRH for $\mathrm{GL}_1 / \mathbb Q$ (`DirichletCharacter.LFunction`),
its **internal proof** constructs automorphic representations and Galois representations (`Row0b`, `P14`)
for high-rank $\mathrm{GL}_a$ and definite unitary groups $U(X_j)$ over CM number fields $E$ of degree
$[E : \mathbb Q] \asymp x^{2+8\varepsilon}$! Conversely, Masullo **outputs** (in intention) GRH for all
number fields $F$, while **internally** never leaving $\mathrm{GL}_1(\mathbb A_F)$!

### 15.4.2 Axis II: One-sided Landau windows versus two-sided explicit traces

Look at how the two routes translate between primes and zeros:

1. **Alpöge–Claude (`P5`, Chapter 3 `[Lean, read]`):** Forms a nonnegative linear combination
   $G_m(x) = \sum_{\chi \in \Lambda} c_\chi G_\chi(x)$ whose coefficients $c_n$ in
   $\sum_{n \le x} c_n \Lambda(n)(x/n - 1)$ are **nonnegative** (or bounded below after subtracting the
   $s = 1$ pole). Why is nonnegativity a superpower? Because by **Landau's theorem (`[Landau1905]`,
   `[Polya1930]`, formalized as `Deduction.landau_window`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean:83`)**, if the real
   Laplace integral $\int_0^\infty (C e^{\theta u} - g(u)) e^{-su}\,du$ has a nonnegative integrand on
   long windows $[\log Y, (1+\delta)\log Y]$ while its analytic continuation is regular on real
   $(\theta, \sigma_0)$ with a singularity at $\sigma_0 + i\gamma_0$, Taylor expansion around a real
   abscissa $\sigma_1 > \sigma_0$ produces a contradiction **from an upper bound alone** — **without
   ever needing a lower bound on $G_m(x)$, without summing over high-ordinate zeros $\lvert \gamma \rvert \to \infty$,
   and even if bad Siegel zeros destroy uniform bounds on intermediate scales outside the windows $[Y, Y^{1+\delta}]$!**
2. **Masullo (`Chs. 10–12` & `App. B.4`, [Paper; Masullo pp. 441–520, 606–625]):** Uses a **two-sided
   linear trace identity** on $C_F$ for arbitrary smooth test functions $\varphi \in D(C_F)$ with
   $\varphi(C_F^1) = 0$. Because there is no sign/monotonicity restriction (`§1.4.6`, p. 30 explicitly
   avoids Weil positivity!), **every** zero in the strip $\frac{1}{2} + I$ must be accounted for on the
   spectral side simultaneously across all heights $t \in (-\infty, \infty)$ — which is **precisely why
   Masullo crashes into the infinite-height spectral nuclearity problem of Chapter 10 (`p. 451`)**,
   whereas Alpöge's compactly supported Riesz kernel $(x/n - 1)_+$ decays like $\lvert \rho \rvert^{-2}$
   and never needs biorthogonal dual functionals at zeros!

### 15.4.3 Axis III: Two completely different mechanisms for the critical exponent $\frac{1}{2}$

Why $\frac{1}{2}$, and not $\frac{2}{3}$ or $\frac{3}{4}$? Compare the two mechanisms side by side
[Expository]:

- **In Alpöge–Claude (`P6`–`P7` & `P10`–`P11`, Chapters 5–10 `[Lean, read]`):** Fix a window scale $x$
  and a chain of **$m$ iterated theta lifts** ($m \in \mathbb N$). In `proposition_size_bound`
  (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507`) [Lean, read], dividing the global Arakelov slope inequality by
  the number of lifts $m$ produces four error brackets `SZ.T1`–`SZ.T4`:
  - the **base archimedean / initial height cost** is $O(x)$ *in total*, which after dividing by $m$
    lifts becomes **$\frac{x}{m}\,x^{O(\varepsilon)}$** (`SZ.T1`–`SZ.T2`);
  - the **per-lift congruence / rank-growth cost** accumulates across the $m$ lifts, contributing
    **$m\,x^{O(\varepsilon)}$** (`SZ.T3` — *only after* Chapter 10's Selmer-killing twists and Chapter
    11's `VWin` prevent quadratic compounding $m^2$, which as Alpöge notes on `remark.pdf` p. 4 item 14
    would otherwise stop at $\min_m (x/m + m^2) \asymp x^{2/3}$ at $m \asymp x^{1/3}$!).
  Minimizing the sum of those two competing terms over $m \ge 1$ by AM–GM:
  $$\min_{m \ge 1} \Bigl(\frac{x}{m} + m\Bigr) \;=\; 2\,\sqrt{\frac{x}{m} \cdot m} \;=\; 2\,x^{1/2}
  \qquad\text{at}\qquad m \asymp x^{1/2}!$$
  Here **$\frac{1}{2}$ is literally the AM–GM exponent balancing $\frac{x}{m}$ against $m$** (exactly as
  in Stepanov's polynomial degree $\deg \Phi \approx r q + \frac{1}{2} M^2$ divided by vanishing order
  $M \approx \sqrt{q}$ in Chapter 6!).
- **In Masullo (`§1.2.1–1.2.3` pp. 13–16, `§12.4.1` p. 518, `§12.5` p. 519 `[Paper]`):** There is no
  discrete parameter $m$ and no AM–GM optimization! Instead, $\frac{1}{2}$ enters in **two** coupled
  steps:
  1. *Symmetry center:* Embedding $\Phi_F(\mathcal S_0(\mathbb A_F))$ with $\lvert \cdot \rvert_F^a$
     converts the normalized multiplicative Haar measure
     $d\mu_S(x) = c_S\,\lvert x \rvert_{F, S}^{-1} d\nu_S(x)$ on the diagonal $x = y$ into
     $c_S\,\lvert x \rvert_{F, S}^{2a - 1} d\nu_S(x)$, which matches additive Fourier measure
     $d\nu_S(x)$ up to a positive constant (namely $c_S$, for $S \ne \emptyset$) **if and only if
     $2a - 1 = 0 \iff a = \frac{1}{2}$** (`p. 16, p. 518`). (Note: this alone only identifies
     $\Re s = \frac{1}{2}$ as the **functional-equation symmetry axis**, which is classical!
     Subsections 15.4.3.1 and 15.4.3.2 below prove it as Theorems 15.3 and 15.6, with the local and
     real-linear determinant normalizations of $\lvert\cdot\rvert_{F,S}$, the domain $K_S^\times$ of
     $\mu_S$, the constant $c_S$ of (12.4.1.17), the `withDensity` $L^2$ half-density transport, and
     four worked hand calculations.)
  2. *Concentration on that axis:* Zeros are forced onto $\Re s = \frac{1}{2}$ **only if** the trace on
     $W_{[-\alpha, \alpha]}^{s,2}\mathcal H_F$ is independent of $\alpha > 0$ (`Theorem 12.5.1.1`, p. 519)
     — the exact step currently blocked by the `[Open]` issues of Chapter 14!

#### 15.4.3.1 Half-densities: the modulus, the multiplicative Haar measure and the diagonal weight

> **Reading boundary.** This subsection explains only existing measure theory. The Lean
> correspondence below is `[Lean, read]` at the archive's Mathlib pin
> `0df444a360eaa60ab8c11dca51a86af692955474` (archive bundle SHA-256
> `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`); none of these Mathlib
> declarations is consumed by `src/Main.lean`, so the tag records our reading of the library,
> not a kernel check of Masullo's draft. The quotations from Masullo are `[Paper; Masullo
> pp. 16, 518–519]` (PDF SHA-256 `e039d3f6…97bf5`). The $\mathbb Q_5$ normalization is a
> hand calculation `[Expository]`: the pinned Mathlib has no Haar measure instance on
> $\mathbb Q_p$ (its `NumberTheory/Padics/Measure/` files define abstract measures
> $C(X,R)\to E$, not Haar measure).

**Motivation.** Item 1 of the Masullo column above compresses a sentence from the
introduction of *The Music of the Primes* (§1.2.3 (1), p. 16): the product
$\lvert x\rvert_{F,S}^{a}\lvert y\rvert_{F,S}^{a}$ produced by the kernel $k_{S,\varphi}(x,y)$
"turns, along the diagonal, into $\lvert x\rvert_{F,S}^{2a}$. If $a=1/2$ exactly, then this is
$\lvert x\rvert_{F,S}$, which will multiply the multiplicative Tamagawa measure $\mu_S$ on
$\mathrm{GL}_1(\mathbb A_{F,S})$ to give the additive measure $\nu_S$, up to a positive
multiplicative constant." The same identity is used on p. 518, where (12.4.1.17) records
$\mu_S = c_S\,\lvert\cdot\rvert_{F,S}^{-1}\nu_S$ with
$c_S=\prod_{v\in S_f} N(\mathfrak p_v)/(N(\mathfrak p_v)-1)$, and (12.4.1.23) performs the
change of variables $w=xu$, $d\nu_S(x)\otimes d\nu_S(u)=\lvert x\rvert_{F,S}^{-1}d\nu_S(x)\otimes d\nu_S(w)$
[Paper; Masullo pp. 16, 518]. Three questions are left implicit there and are answered here:
*what exactly is $\lvert\cdot\rvert_{F,S}$* (a modulus, with a specific normalization at each
place), *where the measures live* (the multiplicative measure is a measure on $K^\times$, not
on $K$), and *in what sense $a=1/2$ is forced* (an identity of measures that holds for one
exponent only, once the modulus is non-constant).

**Example (the real half-line).** On $\mathbb R_{>0}$ the additive measure is $dx$ and the
multiplicative Haar measure is $dx/x$. Take the window $g=\mathbf 1_{[1,4]}$ and the dilation
$x\mapsto 2x$, which sends $[1,4]$ to $[2,8]$. Additive masses: $\nu([1,4])=3$, $\nu([2,8])=6$;
the ratio is $2$. Multiplicative masses: $\mu([1,4])=\log 4=\mu([2,8])$; the ratio is $1$. Now
weight the multiplicative measure by $x^{2a}$, which is what the diagonal of a kernel
$x^{a}y^{a}k(x,y)$ does. Then $x^{2a}\,dx/x = x^{2a-1}dx$ and, for $a\ne 0$ (with both integrals equal
to $\log 4$ at $a=0$),
$$\int_1^4 x^{2a-1}\,dx=\frac{4^{2a}-1}{2a},\qquad \int_2^8 x^{2a-1}\,dx=2^{2a}\,\frac{4^{2a}-1}{2a},$$
so the weighted measure scales under $x\mapsto 2x$ by $2^{2a}$. The additive measure scales by
$2^{1}$. The two agree for exactly one $a$, namely $2a=1$. (Numerically: at $a=1/4$ the two
masses are $2.000$ and $2.828$, ratio $\sqrt 2$; at $a=1/2$ they are $3$ and $6$, ratio $2$; at
$a=1$ they are $7.5$ and $30$, ratio $4$.) The point of the subsection is that this is the whole
content of "$a=1/2$ is forced": a one-parameter family of measures $x^{2a-1}dx$ contains the
dilation-covariant additive measure for one value of the parameter.

**Definition 15.2 (modulus, additive and multiplicative Haar measure).** Let $K$ be a field with
a locally compact, non-discrete Hausdorff topology making it a topological field (so
$K=\mathbb R$, $\mathbb C$, or a non-archimedean local field such as $\mathbb Q_p$). Fix an
additive Haar measure $\nu$ on $K$.

1. For $t\in K^\times$ the map $x\mapsto tx$ is a topological group automorphism of $(K,+)$, so
   the pushed-forward measure is again a Haar measure and is a positive multiple of $\nu$. The
   **modulus** $\Delta_K(t)\in\mathbb R_{>0}$ is the number with
   $$\nu(tS)=\Delta_K(t)\,\nu(S)\quad\text{for every Borel set } S\subseteq K .$$
   It does not depend on $\nu$ and $\Delta_K:K^\times\to\mathbb R_{>0}$ is a group homomorphism.
   In Mathlib this is `MeasureTheory.distribHaarChar K t` for the action of $K^\times$ on $(K,+)$
   by multiplication; the defining property is `distribHaarChar_mul`
   ([`DistribChar.lean:83–86`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean#L83-L86)),
   the independence of $\nu$ is the construction at
   [`DistribChar.lean:43–55`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean#L43-L55)
   through `addHaarScalarFactor_smul_congr'`, and multiplicativity is the `map_mul'` field there.
   Masullo's $\lvert\cdot\rvert_v$ at a place $v$ is $\Delta_{F_v}$, and $\lvert x\rvert_{F,S}=\prod_{v\in S}\Delta_{F_v}(x_v)$
   on $\mathrm{GL}_1(\mathbb A_{F,S})=\prod_{v\in S}F_v^\times$ [Paper; Masullo p. 518].
2. The **multiplicative Haar measure** attached to $\nu$ is the measure on the open set
   $K^\times=K\setminus\{0\}$ with density $\Delta_K^{-1}$ against $\nu$:
   $$\mu(S)=\int_S \Delta_K(x)^{-1}\,d\nu(x)\qquad (S\subseteq K^\times \text{ Borel}).$$
   Masullo's $\mu_S$ is $c_S\prod_{v\in S}\mu_v$ for the constant $c_S$ of (12.4.1.17) fixed by
   the normalizations in Lemma 15.3a(3) below.
3. The **half-density map** is $U:g\mapsto \Delta_K^{1/2}g$, from functions on $K$ to functions on
   $K^\times$ (restriction to $K^\times$ understood). Masullo's space
   $\lvert\cdot\rvert_F^{1/2}H_{0,\mathrm{cont}}(F^\times,\mathcal S_0(\mathbb A_F))$ in the divisor
   exact sequence of §1.2.1 (p. 13) is the image of such a map.

**Lemma 15.3a (values of the modulus).**

1. $K=\mathbb R$, $\nu=$ Lebesgue measure: $\Delta_{\mathbb R}(t)=\lvert t\rvert$.
2. $K=\mathbb C$, $\nu=$ Lebesgue measure on $\mathbb R^2$: $\Delta_{\mathbb C}(z)=\lvert z\rvert^2$
   (the square of the ordinary absolute value; this is the normalization that makes
   $\Delta_{\mathbb C}$ restrict to $\Delta_{\mathbb R}$ on $\mathbb R\subset\mathbb C$ *only up to the square*,
   which is why Tate's thesis writes $\lvert z\rvert_{\mathbb C}=z\bar z$).
3. $K$ non-archimedean with valuation ring $\mathcal O$, maximal ideal $\mathfrak p=(\pi)$, residue
   field of size $q$, and $\nu(\mathcal O)=1$: $\Delta_K(t)=q^{-v(t)}$ where $t\in\pi^{v(t)}\mathcal O^\times$.
   Moreover $\nu(\mathcal O^\times)=1-q^{-1}$, so the multiplicative measure $\mu=\Delta_K^{-1}\nu$ gives
   $\mu(\mathcal O^\times)=1-q^{-1}$, and the measure with $\mu'(\mathcal O^\times)=1$ is
   $\mu'=\frac{q}{q-1}\,\Delta_K^{-1}\nu$. The factor $\frac{q}{q-1}=\frac{N(\mathfrak p)}{N(\mathfrak p)-1}$
   is Masullo's local factor of $c_S$ in (12.4.1.17) [Paper; Masullo p. 518].

*Proof.* (1) Both sides are determined on intervals, since two locally finite Borel measures on
$\mathbb R$ that agree on all rational open intervals agree (`Real.measure_ext_Ioo_rat`). For
$t>0$ the preimage of $(p,q)$ under $x\mapsto tx$ is $(p/t,q/t)$ of length $(q-p)/t$; for $t<0$
it is $(q/t,p/t)$, again of length $(q-p)/\lvert t\rvert$. Hence the pushforward of $\nu$ under
$x\mapsto tx$ is $\lvert t\rvert^{-1}\nu$, i.e. $\nu(tS)=\lvert t\rvert\,\nu(S)$. This is exactly
the proof of `Real.smul_map_volume_mul_left` and `Real.map_volume_mul_left`
([`Lebesgue/Basic.lean:312–328`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L312-L328)):
the two sign cases are `preimage_const_mul_Ioo_of_neg` and `preimage_const_mul_Ioo₀`, and the
length computation is `Real.volume_Ioo`. Then `Real.volume_preimage_mul_left` (`:331–336`) restates
it for sets.

(2) Multiplication by $z=re^{i\theta}$ on $\mathbb C=\mathbb R^2$ is the real-linear map with
matrix $r\begin{pmatrix}\cos\theta&-\sin\theta\\ \sin\theta&\cos\theta\end{pmatrix}$, of
determinant $r^2=\lvert z\rvert^2$. For a Haar measure on a finite-dimensional real vector space
$E$ the image of a set under a linear map $f$ has measure $\lvert\det f\rvert$ times the original
(`addHaar_image_linearMap`, [`EqHaar.lean:297–306`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean#L297-L306)),
and for real scalars this specializes to `addHaar_smul`:
$\mu(r\cdot S)=\lvert r^{\dim E}\rvert\,\mu(S)$ ([`EqHaar.lean:362–375`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean#L362-L375),
proved by writing $r\cdot$ as the linear map $r\cdot\mathrm{id}$ with determinant $r^{\dim E}$ via
`LinearMap.det_smul`, and treating $r=0$ separately through `measure_singleton`). With
$\dim_{\mathbb R}\mathbb C=2$ this gives $\Delta_{\mathbb C}(r)=r^2$ for real $r$; the full production
proof of `map_linearMap_addHaar_eq_smul_addHaar`, `addHaar_image_linearMap`, and
$\det_{\mathbb R}(w\mapsto zw)=\lvert z\rvert^2$ for arbitrary $z\in\mathbb C$ is given in Lemmas
15.5a–15.5c of §15.4.3.2 below.

(3) $\mathcal O$ is the disjoint union of the $q$ cosets $r+\pi\mathcal O$, which are translates
of $\pi\mathcal O$; translation invariance gives $\nu(\pi\mathcal O)=q^{-1}\nu(\mathcal O)=q^{-1}$,
and inductively $\nu(\pi^k\mathcal O)=q^{-k}$. Since $\pi\mathcal O=\pi\cdot\mathcal O$ this says
$\Delta_K(\pi)=q^{-1}$; a unit $u$ satisfies $u\mathcal O=\mathcal O$, so $\Delta_K(u)=1$;
multiplicativity gives $\Delta_K(\pi^k u)=q^{-k}$. Then
$\nu(\mathcal O^\times)=\nu(\mathcal O)-\nu(\pi\mathcal O)=1-q^{-1}$, and on $\mathcal O^\times$ the
density $\Delta_K^{-1}$ is identically $1$, so $\mu(\mathcal O^\times)=1-q^{-1}$. $\square$

**Lemma 15.3b (zero removal and the domain of $\mu$).** With $K,\nu$ as in Definition 15.2:

1. $\nu(\{0\})=0$; hence $L^2(K,\nu)=L^2(K^\times,\nu|_{K^\times})$ and restriction to $K^\times$
   loses nothing.
2. $\mu=\Delta_K^{-1}\nu$ is a Radon measure on $K^\times$ but has infinite mass on every
   neighbourhood of $0$ in $K$. So $\mu$ is a Radon measure on the locally compact group $K^\times$,
   and does not extend to a locally finite Borel measure on $K$.

*Proof.* (1) Suppose $\nu(\{0\})>0$. By translation invariance every singleton has the same
positive measure. A compact neighbourhood $C$ of $0$ exists by local compactness and is infinite
because $0$ is not isolated ($K$ is non-discrete); so $\nu(C)=\infty$, contradicting finiteness of
Haar measure on compact sets. This is verbatim the Lean proof of
`IsHaarMeasure.nullSingletonClass` ([`Group/Measure.lean:935–944`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Group/Measure.lean#L935-L944)),
whose hypothesis `(𝓝[≠] 1).NeBot` is precisely non-discreteness; for $\mathbb R$ it is also
`Real.volume_singleton` (`Lebesgue/Basic.lean:123`). A direct check in $\mathbb Q_5$ is given in
Example 2 below.

(2) For the fields of Lemma 15.3a let $C=\{x\in K:\Delta_K(x)\le1\}$, the closed unit ball, a
compact neighbourhood of $0$ with $0<\nu(C)<\infty$, and pick $t\in K^\times$ with $\Delta_K(t)<1$
($t=1/2$ for $\mathbb R,\mathbb C$; $t=\pi$ in the non-archimedean case). Then $tC=\{\Delta_K\le\Delta_K(t)\}\subseteq C$,
the shells $C_k=t^kC\setminus t^{k+1}C=\{\Delta_K(t)^{k+1}<\Delta_K\le\Delta_K(t)^k\}$ ($k\ge0$) are
pairwise disjoint with union $C\setminus\{0\}$, and $C_k=t^kC_0$. By (1) and the defining property
of the modulus, $\nu(C_0)=\nu(C)-\nu(tC)=(1-\Delta_K(t))\nu(C)>0$, hence $\mu(C_0)>0$; by the
invariance of $\mu$ under $x\mapsto tx$ (Lemma 15.3c below, whose proof does not use this lemma)
$\mu(C_k)=\mu(C_0)$ for every $k$, so $\mu(C\setminus\{0\})=\sum_{k\ge0}\mu(C_k)=\infty$. Every
neighbourhood of $0$ contains some $t^kC$, which has the same infinite $\mu$-mass by invariance. $\square$

**Lemma 15.3c ($\Delta_K^{-1}\nu$ is a Haar measure on $K^\times$, invariant under inversion).**
For every $t\in K^\times$ and every Borel $S\subseteq K^\times$, $\mu(tS)=\mu(S)$. Moreover
$\mu(S^{-1})=\mu(S)$. In particular the identity $\mu_S=c_S\lvert\cdot\rvert^{-1}_{F,S}\nu_S$ of
Masullo's (12.4.1.17) determines $\mu_S$ up to the constant $c_S$, and the inversion invariance
invoked in (12.4.1.16) holds for it [Paper; Masullo p. 518].

*Proof.* By the defining property of $\Delta_K$ and the density formula
(`lintegral_withDensity_eq_lintegral_mul`,
[`WithDensity.lean:398–409`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/WithDensity.lean#L398-L409)),
for a non-negative Borel $f$ on $K^\times$,
$$\int f(tx)\,\Delta_K(x)^{-1}\,d\nu(x)
=\Delta_K(t)\int f(tx)\,\Delta_K(tx)^{-1}\,d\nu(x)
=\Delta_K(t)\,\Delta_K(t)^{-1}\int f(y)\,\Delta_K(y)^{-1}\,d\nu(y),$$
where the first equality is multiplicativity $\Delta_K(tx)=\Delta_K(t)\Delta_K(x)$ and the
second is the substitution $y=tx$, i.e. $\int h(tx)\,d\nu(x)=\Delta_K(t)^{-1}\int h\,d\nu$, which
is the integrated form of $\nu(tS)=\Delta_K(t)\nu(S)$. Taking $f=\mathbf 1_{tS}$ gives
$\mu(tS)=\mu(S)$. For $K=\mathbb R_{>0}$ the substitution step is literally
`integral_comp_mul_left_Ioi`: $\int_{(a,\infty)}g(bx)\,dx=b^{-1}\int_{(ba,\infty)}g$
([`IntegralEqImproper.lean:1187–1195`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L1187-L1195),
proved by rewriting both sides as integrals of indicators and applying
`Measure.integral_comp_mul_left`, the integrated form of `Real.map_volume_mul_left`), and
the twisted form $\int f(bt)\,t^{s}\,dt/t=b^{-s}\int f(t)\,t^{s}\,dt/t$ is `mellin_comp_mul_left`
([`MellinTransform.lean:133–149`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/MellinTransform.lean#L133-L149)),
whose proof pulls $b^{1-s}$ out of $(bt)^{s-1}$ and then calls `integral_comp_mul_left_Ioi`; at
$s=0$ it is the invariance of $dt/t$.

Inversion invariance: $K^\times$ is an abelian locally compact group and $\mu$ is a Haar measure
on it, so its image under $x\mapsto x^{-1}$ is $c\mu$ for some $c>0$ by uniqueness of Haar
measure; applying inversion twice gives $c^2\mu=\mu$, hence $c=1$. This is the Lean proof of
`IsHaarMeasure.isInvInvariant_of_regular`
([`Haar/Unique.lean:978–1000`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Unique.lean#L978-L1000)),
where $c$ is `haarScalarFactor μ.inv μ` and $c^2=1^2$ is extracted on a positive compact.
Regularity of $\mu$ on $K^\times$ holds because $\nu$ is regular and $\Delta_K^{-1}$ is continuous
and positive on $K^\times$. $\square$

**Lemma 15.3d (the half-density map is an $L^2$ isometry; the general exponent).** For $a\in\mathbb R$
let $U_a g=\Delta_K^{a}g$ on $K^\times$. Then for every Borel $g$ on $K$
$$\int_{K^\times}\lvert U_a g\rvert^2\,\Delta_K^{\,1-2a}\,d\mu=\int_K\lvert g\rvert^2\,d\nu .$$
Hence $U_a$ is an isometric isomorphism $L^2(K,\nu)\to L^2(K^\times,\Delta_K^{1-2a}\mu)$, and it
is an isometry into $L^2(K^\times,\mu)$ itself exactly when the weight $\Delta_K^{1-2a}$ equals $1$
$\nu$-a.e. on $K^\times$, i.e. (Theorem 15.3(2)) exactly when $a=1/2$. For $a=1/2$ the map
$U=U_{1/2}:L^2(K,\nu)\to L^2(K^\times,\mu)$ is unitary, with inverse $f\mapsto\Delta_K^{-1/2}f$
extended by $0$ at the $\nu$-null point $0$.

*Proof.* $\lvert U_ag\rvert^2\Delta_K^{1-2a}\,d\mu=\Delta_K^{2a}\lvert g\rvert^2\Delta_K^{1-2a}\Delta_K^{-1}\,d\nu=\lvert g\rvert^2\,d\nu$
on $K^\times$, by the density formula, and $\{0\}$ is $\nu$-null by Lemma 15.3b(1). Because
$0<\Delta_K<\infty$ on $K^\times$, $\nu|_{K^\times}$ and $\Delta_K^{1-2a}\mu=\Delta_K^{-2a}\nu|_{K^\times}$
have the same null sets, so $U_a$ descends to almost-everywhere classes and is surjective with inverse
$f\mapsto\Delta_K^{-a}f$ (extended by $0$ at $0$). (Caution: $U_a$ is a **density-multiplication**
isometry, *not* an instance of Mathlib's `Lp.isometry_compMeasurePreserving`
([`LpSpace/Basic.lean:581–583`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L581-L583)):
the latter requires `MeasurePreserving` and acts only by precomposition $h\mapsto h\circ\phi$, whereas
for $\phi=\mathrm{id}_{K^\times}$ the pushforward $(\mathrm{id}_{K^\times})_\ast\nu=\nu$ differs from
$\Delta_K^{1-2a}\mu=\Delta_K^{-2a}\nu$ whenever $a\ne 0$—for example on $[1,4]\subset\mathbb R_{>0}$ at
$a=1/2$, $\nu([1,4])=3\ne\log 4=\mu([1,4])$. Lemma 15.5d and Theorem 15.6 in §15.4.3.2 build the
`withDensity` $L^2$ isometric isomorphism directly and incorporate the product normalization
$c_S^{-1/2}$.) $\square$

**Theorem 15.3 (the diagonal weight and the uniqueness of $a=1/2$).** Let $K,\nu,\Delta_K,\mu$ be
as in Definition 15.2, and assume

- **(H1)** $\Delta_K$ is continuous on $K^\times$ and not identically $1$ (true for
  $\mathbb R,\mathbb C$ and every non-archimedean local field by Lemma 15.3a: $\Delta(1/2)=1/2$,
  $\Delta(1/2)=1/4$, $\Delta(\pi)=q^{-1}$);
- **(H2)** $\nu$ has full support on $K$ (every non-empty open set has positive measure; true for
  Haar measures).

Let $k(x,y)$ be a Borel function on $K^\times\times K^\times$ whose diagonal restriction
$x\mapsto k(x,x)$ is Borel (as in Masullo's smoothing along the diagonal, which we take as
given), and for $a\in\mathbb R$ set $k_a(x,y)=\Delta_K(x)^a\Delta_K(y)^a k(x,y)$. Then:

1. *(Diagonal identity, all $a$.)* For every $a$,
   $$\int_{K^\times}k_a(x,x)\,d\mu(x)=\int_{K^\times}k(x,x)\,\Delta_K(x)^{2a-1}\,d\nu(x),$$
   whenever either side converges absolutely.
2. *(Uniqueness.)* There is a constant $c>0$ with $\Delta_K^{2a}\mu=c\,\nu$ as measures on
   $K^\times$ if and only if $a=1/2$; and then $c=1$. Equivalently, the weight $\Delta_K^{2a-1}$ in
   (1) is a constant if and only if $a=1/2$.
3. *(Product form and the two occurrences of $c_S$.)* Let $S$ be a finite set of places of $F$,
   $K_S=\prod_{v\in S}F_v$ (each factor satisfying **(H1)**–**(H2)**), $\Delta_S=\prod_{v\in S}\Delta_{F_v}$,
   $\nu_S=\bigotimes_{v\in S}\nu_v$, and $\mu_S=c_S\bigotimes_{v\in S}\mu_v$ on
   $K_S^\times=\prod_{v\in S}F_v^\times$, where $c_S=\prod_{v\in S_f}N(\mathfrak p_v)/(N(\mathfrak p_v)-1)>0$
   (with $c_\emptyset=1$). Then:
   - *(i)* For every finite $S$ and every $a\in\mathbb R$, $k_a(x,y)=\Delta_S(x)^a\Delta_S(y)^a k(x,y)$
     satisfies
     $$\int_{K_S^\times}k_a(x,x)\,d\mu_S(x)=c_S\int_{K_S^\times}k(x,x)\,\Delta_S(x)^{2a-1}\,d\nu_S(x)$$
     whenever either side converges absolutely.
   - *(ii)* Assuming **$S\ne\emptyset$** (so $\Delta_S$ is non-constant on $K_S^\times$), there is a
     constant $c>0$ with $\Delta_S^{2a}\mu_S=c\,\nu_S$ on $K_S^\times$ if and only if $a=1/2$, and
     then $c=c_S$. (For the empty product $S=\emptyset$, $K_\emptyset^\times=\{1\}$ has
     $\Delta_\emptyset\equiv 1$ and $c_\emptyset=1$, so $\Delta_\emptyset^{2a}\mu_\emptyset=\nu_\emptyset$
     holds for *every* $a\in\mathbb R$ and uniqueness fails.)
   Clauses *(i)* and *(ii)* are the exact form of Masullo's (12.4.1.17)–(12.4.1.23) and of the p. 16
   sentence [Paper; Masullo pp. 16, 518].

*Proof.* (1) By Definition 15.2(2) and the density formula,
$k_a(x,x)\,d\mu(x)=\Delta_K(x)^{2a}k(x,x)\Delta_K(x)^{-1}d\nu(x)$.

(2) If $a=1/2$ then $\Delta_K^{2a}\mu=\Delta_K\cdot\Delta_K^{-1}\nu=\nu$ on $K^\times$, so $c=1$.
Conversely suppose $\Delta_K^{2a}\mu=c\nu$, i.e. $\Delta_K^{2a-1}\nu=c\nu$ on $K^\times$. Then
$\Delta_K^{2a-1}=c$ $\nu$-almost everywhere on $K^\times$: if, say, $\nu(\{\Delta_K^{2a-1}>c\})>0$, then for some
$\varepsilon>0$ the set $A_\varepsilon=\{\Delta_K^{2a-1}\ge c+\varepsilon\}\cap C$ has positive finite
$\nu$-measure for a suitable compact $C$ ($\nu$ is inner regular and the sets increase to
$\{\Delta_K^{2a-1}>c\}$ as $\varepsilon\downarrow0$), and then
$(\Delta_K^{2a-1}\nu)(A_\varepsilon)\ge(c+\varepsilon)\nu(A_\varepsilon)>c\,\nu(A_\varepsilon)$, contradicting
$\Delta_K^{2a-1}\nu=c\nu$; the set $\{\Delta_K^{2a-1}<c\}$ is handled symmetrically.
A continuous function that equals $c$ almost everywhere for a
measure of full support equals $c$ everywhere: the set $\{\Delta_K^{2a-1}\ne c\}$ is open and
null, hence empty by (H2). Evaluating at $x=1$ gives $c=1$. Now pick $t$ with
$\Delta_K(t)\ne1$ by (H1); from $\Delta_K(t)^{2a-1}=1$ and $\Delta_K(t)>0$, $\Delta_K(t)\neq 1$,
we get $2a-1=0$.

(3) On $K_S^\times$, the product of the local densities $\Delta_{F_v}^{-1}$ is $\Delta_S^{-1}$, so
$\mu_S=c_S\bigotimes_{v\in S}\mu_v=c_S\,\Delta_S^{-1}\nu_S|_{K_S^\times}$; multiplying by
$\Delta_S(x)^{2a}k(x,x)$ gives $k_a(x,x)\,d\mu_S(x)=c_S\,k(x,x)\Delta_S(x)^{2a-1}\,d\nu_S(x)$, proving
*(i)*. For *(ii)*, $\Delta_S^{2a}\mu_S=c_S\Delta_S^{2a-1}\nu_S$ on $K_S^\times$: at $a=1/2$ this is
$c_S\nu_S$, while if $c_S\Delta_S^{2a-1}\nu_S=c\nu_S$ on $K_S^\times$ with $S\ne\emptyset$, continuity
of $\Delta_S$ and full support of $\nu_S$ force $c_S\Delta_S(x)^{2a-1}=c$ for all $x\in K_S^\times$;
evaluating at $x=(1)_{v\in S}$ gives $c=c_S$, and picking $v_0\in S$ and $t=(t_v)_{v\in S}$ with
$\Delta_{F_{v_0}}(t_{v_0})\ne 1$ and $t_v=1$ for $v\ne v_0$ gives $\Delta_S(t)^{2a-1}=1$ with
$\Delta_S(t)\ne 1$, hence $2a-1=0$. $\square$

**Proposition 15.4 (why the exponent is the symmetry centre: unitarity of dilations).**
For $a\in\mathbb R$ and $t\in K^\times$ define $T^{(a)}_t g(x)=\Delta_K(t)^{a}g(tx)$ on functions
on $K$.

1. $T^{(a)}_t$ is an isometry of $L^2(K,\nu)$ for every $t$ if and only if $a=1/2$ (under (H1)).
2. Let $\psi$ be a non-trivial continuous unitary character of $(K,+)$ and
   $\widehat g(\xi)=\int_K g(x)\psi(x\xi)\,d\nu(x)$ the Fourier transform. Then
   $\widehat{T^{(a)}_t g}=T^{(1-a)}_{t^{-1}}\widehat g$ for $g\in L^1(K,\nu)$. So the Fourier
   transform conjugates the $a$-dilation family to the $(1-a)$-dilation family, and $a=1/2$ is the
   unique fixed point of $a\mapsto1-a$. `[Expository]`

*Proof.* (1) $\int\lvert T^{(a)}_tg\rvert^2d\nu=\Delta_K(t)^{2a}\int\lvert g(tx)\rvert^2d\nu(x)=\Delta_K(t)^{2a-1}\int\lvert g\rvert^2d\nu$
by the substitution $y=tx$. This equals $\int\lvert g\rvert^2d\nu$ for all $t$ and all $g\ne0$
iff $\Delta_K(t)^{2a-1}=1$ for all $t$, iff $2a-1=0$ by (H1). (2)
$\widehat{T^{(a)}_tg}(\xi)=\Delta_K(t)^{a}\int g(tx)\psi(x\xi)\,d\nu(x)=\Delta_K(t)^{a-1}\int g(y)\psi(y\,t^{-1}\xi)\,d\nu(y)=\Delta_K(t^{-1})^{1-a}\,\widehat g(t^{-1}\xi)$,
again by $y=tx$ and $\Delta_K(t)^{-1}=\Delta_K(t^{-1})$. $\square$

**Example 1 (the real half-line, completed).** With $g=\mathbf 1_{[1,4]}$: $\lVert g\rVert^2_{L^2(dx)}=3$,
and $U g=x^{1/2}\mathbf 1_{[1,4]}$ has $\lVert Ug\rVert^2_{L^2(dx/x)}=\int_1^4 x\,dx/x=3$, confirming
Lemma 15.3d; with $a=1$ instead, $\int_1^4x^2\,dx/x=15/2\ne3$. Dilation: $T^{(1/2)}_2g=\sqrt2\,\mathbf 1_{[1/2,2]}$
has $L^2(dx)$-norm squared $2\cdot\tfrac32=3$, while $T^{(1)}_2g=2\,\mathbf 1_{[1/2,2]}$ has
$4\cdot\tfrac32=6$. Mellin: with $s=2$, $\int_0^\infty\mathbf 1_{[1,4]}(t)\,t^{2}\,dt/t=15/2$ and
$\int_0^\infty\mathbf 1_{[1,4]}(2t)\,t^2\,dt/t=\int_{1/2}^{2}t\,dt=15/8=2^{-2}\cdot15/2$, which is
`mellin_comp_mul_left` at $a=2$, $s=2$. Together with the opening computation (ratios $2^{2a}$
against $2$), every clause of Theorem 15.3 and Proposition 15.4 has been checked on this window.

**Example 2 (the unit shells of $\mathbb Q_5$).** Take $K=\mathbb Q_5$, $\nu(\mathbb Z_5)=1$,
$\pi=5$, $q=5$. Local compactness is the `ProperSpace ℚ_[p]` instance in namespace `Padic`
([`Padics/ProperSpace.lean:64–69`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/ProperSpace.lean#L64-L69),
from compactness of $\mathbb Z_5$); the measure itself is a hand normalization `[Expository]`.
The shells $U_k=5^k\mathbb Z_5^\times=\{x:\lvert x\rvert_5=5^{-k}\}$, $k\in\mathbb Z$, partition
$\mathbb Q_5^\times$.

- *Additive masses.* $\nu(5^k\mathbb Z_5)=5^{-k}$ by Lemma 15.3a(3), so
  $\nu(U_k)=5^{-k}-5^{-k-1}=\tfrac45\cdot5^{-k}$: the values are $4/5,\,4/25,\,4/125,\dots$
- *Zero removal, checked directly.* $\sum_{k\ge0}\nu(U_k)=\tfrac45\sum_{k\ge0}5^{-k}=\tfrac45\cdot\tfrac54=1=\nu(\mathbb Z_5)$,
  so $\nu(\{0\})=\nu(\mathbb Z_5)-\nu(\mathbb Z_5\setminus\{0\})=0$, as Lemma 15.3b(1) predicts.
- *Modulus.* $\Delta(2)=1$ since $2\mathbb Z_5=\mathbb Z_5$; $\Delta(1/5)=5$ since
  $\nu(5^{-1}\mathbb Z_5)=5$; in general $\Delta(x)=5^{-k}$ on $U_k$.
- *Multiplicative masses.* $\mu(U_k)=\int_{U_k}\Delta^{-1}d\nu=5^{k}\cdot\tfrac45\cdot5^{-k}=\tfrac45$
  for every $k$, so $\mu$ is invariant under $x\mapsto5x$ (which maps $U_k$ to $U_{k+1}$) and under
  $x\mapsto x^{-1}$ (which maps $U_k$ to $U_{-k}$), as Lemma 15.3c says. The normalization
  $\mu'(\mathbb Z_5^\times)=1$ needs the factor $c_5=5/4=N(\mathfrak p)/(N(\mathfrak p)-1)$ of
  (12.4.1.17); then $\mu'(U_k)=1$ for all $k$.
- *Diagonal weight.* $\int_{U_k}\Delta^{2a}\,d\mu'=5^{-2ak}$. Compare with $\nu(U_k)=\tfrac45 5^{-k}$:
  the ratio $\nu(U_k)\big/\!\int_{U_k}\Delta^{2a}d\mu'=\tfrac45\,5^{(2a-1)k}$ is independent of $k$
  if and only if $2a=1$, in which case it is $4/5=1/c_5$ for every shell. At $a=1/4$ the ratios
  for $k=0,1,2,3$ are $0.8,\,0.358,\,0.16,\,0.072$; at $a=1$ they are $0.8,\,4,\,20,\,100$. This is
  Theorem 15.3(2) read shell by shell, and the constant $c$ of (2) for Masullo's normalized
  $\mu_S$ is exactly his $c_S$.
- *A bonus identity.* $\int_{\mathbb Z_5\setminus\{0\}}\Delta(x)^{s}\,d\mu'(x)=\sum_{k\ge0}5^{-ks}=(1-5^{-s})^{-1}$
  for $\Re s>0$: the local Euler factor appears as the Mellin transform of
  $\mathbf 1_{\mathbb Z_5}$ against $\mu'$, which is the non-archimedean analogue of the real
  Mellin check in Example 1 and the $\mathrm{GL}_1$ content of Masullo's Ch. 3 (Tate's thesis)
  [Paper; Masullo pp. 117–154].

**Remark 1 (what this does and does not show).** Theorem 15.3 and Proposition 15.4 are local
statements about one field at a time (or a finite product), and they hold for *every* test
kernel and every exponent $a$; the exponent $1/2$ is singled out as the only one for which a
translation-invariant, degree-one dilation-covariant measure (the additive measure $\nu$, or a
unitary dilation action on $L^2(\nu)$) appears. This is
the same mechanism that places the symmetry axis of Tate's local functional equation at
$\Re s=1/2$: Proposition 15.4(2) is the Fourier side of that equation. In particular the
subsection proves **nothing about zeros**. It does not supply the $\alpha$-independence of the
spectral trace on $W^{s,2}_{[-\alpha,\alpha]}\mathcal H_F$ asserted in Theorem 12.5.1.1 (p. 519),
whose proof passes through the Chapter 10 completion and the biorthogonal bound at (10.3.1.18)
(p. 451) that Chapter 14 records as `[Open]`; nor does it bear on the omitted §12.3 (p. 514). A
reader who checks every line of §12.4.1 (pp. 515–519) with the lemmas above will have verified
that the geometric side is correctly normalized at $a=1/2$, and nothing more. Masullo says as
much on p. 16 ("Connes' expectation on the $S$-adelic Fourier transform playing this role …
is therefore correct") and on p. 519 ("This is also where the necessity of the choice $a=1/2$ is
explained") [Paper; Masullo pp. 16, 519]: the necessity is for the *geometric computation to
close*, which is a different statement from the location of zeros.

**Remark 2 (the two mechanisms compared, with content).** Chapter 5 (`core_gm`,
`proposition_size_bound`) produces $1/2$ as an *extremal* exponent: the bracket
$x/m+m\,x^{O(\varepsilon)}$ is minimized at $m\asymp\sqrt x$, and the exponent would move to
$2/3$ if the per-lift cost compounded to $m^2$ (remark.pdf p. 4, item 14 [Paper]). The value
$1/2$ there is an output of the arithmetic engine, sensitive to the error profile, and it is a
*bound*: $G_m(x)\le x^{1/2+O(\varepsilon)}$. Here $1/2$ is a *fixed point*: it is the unique
solution of $2a-1=0$ (Theorem 15.3(2)), equivalently of $a=1-a$ (Proposition 15.4(2)), and it is
insensitive to everything except the non-constancy of the modulus. The two can be put in one
sentence: the Alpöge–Claude route proves that the primes do not fluctuate beyond the
square-root scale, while the half-density normalization only records that the square-root scale
is the self-dual one. Both routes then need a second, global input to turn the symmetry axis into
the zero locus: the Landau-window criterion plus the chain bound in Chapters 3–11, or the
asserted $\alpha$-independence of Theorem 12.5.1.1.

**Remark 3 (normalizations in the draft).** Masullo's (12.4.1.17) presupposes
$\nu_v(\mathcal O_v)=1$ and $\mu_v(\mathcal O_v^\times)=1$ at finite places and $c_v=1$ at
archimedean places, which is how Lemma 15.3a(3) reproduces $c_S$; the statement of Theorem
12.5.1.1 (p. 519) instead divides each finite-place term by $\mu_v(\mathcal O_{F_v}^\times)$ and is
therefore normalization-free [Paper; Masullo pp. 518–519]. We have not checked the archimedean
constants in (12.4.1.25)–(12.4.1.26) and do not use them.

**Source map for this subsection.** Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`.

| File and lines at the pin | Declaration | Role here | Reading |
|---|---|---|---|
| `Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean:43–55, 57–58, 83–86, 92–95` | `distribHaarChar`, `distribHaarChar_pos`, `distribHaarChar_mul`, `distribHaarChar_eq_of_measure_smul_eq_mul` | Definition 15.2(1): the modulus as the Haar scalar factor of the pulled-back measure; homomorphism property | R3 (whole file read) |
| `Mathlib/MeasureTheory/Measure/Haar/Unique.lean:277, 1063–1073` | `haarScalarFactor`, `addHaarScalarFactor_smul_congr'` | supplies independence of $\nu$ in Definition 15.2(1) | statement level |
| `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean:96, 123, 312–336` | `Real.volume_Ioo`, `Real.volume_singleton`, `Real.smul_map_volume_mul_left`, `Real.map_volume_mul_left`, `Real.volume_preimage_mul_left` | Lemma 15.3a(1), Lemma 15.3b(1) for $\mathbb R$ | R3 |
| `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:297–306, 336–375` | `addHaar_image_linearMap`, `map_addHaar_smul`, `addHaar_preimage_smul`, `addHaar_smul` | Lemma 15.3a(2), real-scalar case (`:297–306` and general $z\in\mathbb C$ read at R3 in §15.4.3.2) | R3 (`:336–375` here; `:297–306` in §15.4.3.2) |
| `Mathlib/LinearAlgebra/Determinant.lean:256` | `LinearMap.det_smul` | $\det(r\cdot\mathrm{id})=r^{\dim}$ inside `map_addHaar_smul` | statement level |
| `Mathlib/MeasureTheory/Group/Measure.lean:935–944` | `IsHaarMeasure.nullSingletonClass` | Lemma 15.3b(1) | R3 |
| `Mathlib/MeasureTheory/Measure/WithDensity.lean:398–409` | `lintegral_withDensity_eq_lintegral_mul` | the density formula in Lemmas 15.3c–d and Theorem 15.3(1) | R3 |
| `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1187–1195` | `integral_comp_mul_left_Ioi` | Lemma 15.3c substitution on $\mathbb R_{>0}$ | R3 |
| `Mathlib/Analysis/MellinTransform.lean:91, 133–149` | `mellin`, `mellin_comp_mul_left` | Example 1 Mellin check; twisted invariance of $dt/t$ | R3 |
| `Mathlib/MeasureTheory/Measure/Haar/Unique.lean:978–1000` | `IsHaarMeasure.isInvInvariant_of_regular` | Lemma 15.3c inversion invariance | R3 |
| `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:561–583` | `Lp.compMeasurePreserving`, `Lp.isometry_compMeasurePreserving` | precomposition isometry under `MeasurePreserving`; contrasted with density multiplication in Lemma 15.3d and §15.4.3.2 | statement level (R3 in §15.4.3.2) |
| `Mathlib/MeasureTheory/Measure/Haar/MulEquivHaarChar.lean:40–68` | `mulEquivHaarChar`, `mulEquivHaarChar_smul_map` | the multiplicative-group analogue of the modulus; not used in the proofs, read for orientation | R3 |
| `Mathlib/NumberTheory/Padics/ProperSpace.lean:64–69` | `ProperSpace ℚ_[p]` instance (namespace `Padic`) | local compactness of $\mathbb Q_5$ in Example 2 | R3 |
| `Mathlib/MeasureTheory/Measure/Haar/Basic.lean:584` | `MeasureTheory.Measure.haar` | existence of $\nu$ on any locally compact group | statement level |

**Retained inputs (not read in §15.4.3.1; linear-Haar and density-$L^2$ items opened in §15.4.3.2).**
The uniqueness theorem for Haar measure behind `haarScalarFactor` and
`isAddLeftInvariant_eq_smul_of_regular` (`Haar/Unique.lean`); the Fourier transform on a general
local field (Proposition 15.4(2) is classical `[Expository]`, and for $\mathbb R$ Mathlib's
`Real.fourierIntegral` is not cited here); a Haar measure on $\mathbb Q_p$ as a Mathlib instance
(absent at the pin); and Masullo's smoothing of kernels along the diagonal (Hardy–Littlewood and
Lebesgue differentiation, pp. 15, 517), which we assume as the hypothesis "the diagonal
restriction is Borel" in Theorem 15.3. The real-linear determinant formulas
`map_linearMap_addHaar_eq_smul_addHaar` and `addHaar_image_linearMap`, the real determinant of
complex multiplication, and the `withDensity` $L^2$ isometric isomorphism are proved in §15.4.3.2
immediately below.

#### 15.4.3.2 From real-linear Haar determinants to density-weighted $L^2$ transport

> **Reading boundary.** This subsection explains only existing measure theory and linear algebra.
> All `[Lean, read]` citations refer to the archive's Mathlib pin
> `0df444a360eaa60ab8c11dca51a86af692955474` (archive bundle SHA-256
> `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`); reading these library
> proofs (and building this book) is not a Lean kernel verification of any RH claim. Single-field
> results already established in §15.4.3.1—$\Delta_{\mathbb R}(t)=\lvert t\rvert$, the
> non-archimedean shell values $\Delta_K(\pi^k u)=q^{-k}$ and $\nu(\mathcal O^\times)=1-q^{-1}$,
> zero removal $\nu(\{0\})=0$, multiplicative and inversion invariance of $\mu=\Delta_K^{-1}\nu$,
> and the one-field dilation/Fourier Proposition 15.4—are inherited without repeating their proofs.
> Masullo's diagonal smoothing of kernels (pp. 15, 517), the omitted §12.3 (p. 514), the Chapter 10
> biorthogonal bound (p. 451), the asserted $\alpha$-independence of the strip trace in Theorem
> 12.5.1.1 (p. 519), and the unwritten Chapter 13 (pp. 521–522) remain named `[Paper]`/`[Open]`
> inputs (PDF SHA-256 `e039d3f6…97bf5`).

**Motivation.** Subsection 15.4.3.1 left three concrete production steps behind interfaces or
one-line assertions, and an independent audit of §15.4.3.1 showed why each of the three matters
quantitatively:

1. *Why a non-real complex multiplier scales planar area by $\lvert z\rvert^2$:* Lemma 15.3a(2)
   read only the real-scalar lemma `addHaar_smul` in Lean, leaving the general linear determinant
   theorem `map_linearMap_addHaar_eq_smul_addHaar` and its image companion
   `addHaar_image_linearMap` unread. Opening those proofs shows how Mathlib reduces an arbitrary
   real-linear endomorphism $f:E\to E$ to elementary shears (`TransvectionStruct`, preserving
   slice integrals by Fubini) and diagonal stretches on $\mathbb R^n$, plus geometric-series
   translates for singular maps (`addHaar_submodule`), and how evaluating left multiplication by
   $z=u+iv$ in the real basis $\{1,i\}$ (`Complex.basisOneI`) produces $\det_{\mathbb R}(w\mapsto zw)=u^2+v^2=\lvert z\rvert^2$
   (`[Tao2011]`, Exercise 1.2.21; `[Weil1967]`, Ch. I, §2).
2. *Why half-density transport is a `withDensity` multiplication unitary and not a
   `MeasurePreserving` composition:* In Mathlib, `Lp.compMeasurePreserving` acts exclusively by
   precomposition $h\mapsto h\circ\phi$ under a measure-preserving map $\phi_\ast\mu_1=\mu_2$. For
   the identity map on $K^\times$, $(\mathrm{id}_{K^\times})_\ast\nu=\nu\ne\Delta_K^{-2a}\nu=\Delta_K^{1-2a}\mu$
   whenever $a\ne 0$. The genuine $L^2$ half-density isomorphism is a **pointwise multiplication
   operator** $M_{w^{1/2}}:u\mapsto w^{1/2}u$ built from the `withDensity` integral calculus
   (`WithDensity.lean`, patterned on the $L^1$ isometry `L1.withDensitySMulLI`), while
   `compMeasurePreserving` enters on the multiplicative group $(K^\times,\mu)$ through the
   genuine Haar-preserving translation $x\mapsto tx$, whose conjugation by $M_{\Delta_K^{1/2}}$
   recovers the unitary dilation $T_t^{(1/2)}$ on $L^2(K,\nu)$.
3. *How the finite-product constant $c_S=\prod_{v\in S_f}N(\mathfrak p_v)/(N(\mathfrak p_v)-1)$
   behaves simultaneously in half-density $L^2$ norms and in diagonal kernel integrals:* In a
   normalized half-density map $U_{S,a}(g)=c_S^{-1/2}\Delta_S^a g$, the two factors of $c_S^{-1/2}$
   cancel the $c_S$ inside $\mu_S=c_S\Delta_S^{-1}\nu_S$, making $U_{S,1/2}:L^2(K_S,\nu_S)\to L^2(K_S^\times,\mu_S)$
   strictly unitary; in Masullo's unscaled kernel $k_a(x,y)=\Delta_S(x)^a\Delta_S(y)^a k(x,y)$
   ((12.4.1.16)–(12.4.1.23), p. 518), no $c_S^{-1/2}$ is inserted into the test functions, so
   $c_S$ remains explicit on the right-hand side of **both** clauses of Theorem 15.3(3), and
   uniqueness of $a=1/2$ requires $S\ne\emptyset$.

**Example 1 (non-real complex dilation $z=1+2i$ on $\mathbb C$: shear-diagonal factorization,
annular masses, and $L^2$ transport).** Let $K=\mathbb C$ with planar Lebesgue measure
$\nu_{\mathbb C}=dx\,dy$ under `Complex.basisOneI` $=(1,i)$, multiplicative Haar measure
$d\mu_{\mathbb C}(w)=\lvert w\rvert^{-2}dx\,dy$ on $\mathbb C^\times$, and non-real multiplier
$z=1+2i$.

- *Real matrix and two-sided transvection pivot.* Because $(1+2i)\cdot 1=1+2i$ and
  $(1+2i)\cdot i=-2+i$, left multiplication $\ell_z(x+iy)=(1+2i)(x+iy)=(x-2y)+i(2x+y)$ has matrix
  $$M=\begin{pmatrix}1&-2\\2&1\end{pmatrix},\qquad \det_{\mathbb R} M = 1\cdot 1 - (-2)\cdot 2 = 5 = \lvert 1+2i\rvert^2.$$
  Following `Transvection.lean`'s two-sided elimination on the bottom-right pivot $M_{22}=1\ne 0$,
  left multiplication by the column shear $T_{\mathrm{col}}=\begin{pmatrix}1&2\\0&1\end{pmatrix}$
  clears the top-right entry, and right multiplication by the row shear
  $T_{\mathrm{row}}=\begin{pmatrix}1&0\\-2&1\end{pmatrix}$ clears the bottom-left entry:
  $$T_{\mathrm{col}} M T_{\mathrm{row}}=\begin{pmatrix}5&0\\0&1\end{pmatrix}=:D
  \quad\Longleftrightarrow\quad
  M = T_{\mathrm{col}}^{-1} D T_{\mathrm{row}}^{-1}
  = \begin{pmatrix}1&-2\\0&1\end{pmatrix}\begin{pmatrix}5&0\\0&1\end{pmatrix}\begin{pmatrix}1&0\\2&1\end{pmatrix}.$$
  Track the unit square $Q=[0,1]^2$ (`piIcc01 (Fin 2)`, area $1$) through the three factors:
  1. $T_{\mathrm{row}}^{-1}(x,y)=(x,2x+y)$ shears each vertical slice $\{x\}\times[0,1]$ to
     $\{x\}\times[2x,2x+1]$ of 1D length $1$, so Fubini gives $\nu_{\mathbb C}(T_{\mathrm{row}}^{-1}Q)=\int_0^1 1\,dx=1$;
  2. $D(u,v)=(5u,v)$ stretches the first coordinate by $5$, giving area $5\cdot 1=5$;
  3. $T_{\mathrm{col}}^{-1}(r,s)=(r-2s,s)$ shears each horizontal slice by $-2s$, preserving its
     1D length and landing on the parallelogram $M(Q)$ with vertices $(0,0)$, $(1,2)$, $(-1,3)$,
     $(-2,1)$, of area $\lvert 1\cdot 1 - (-2)\cdot 2\rvert = 5 = \Delta_{\mathbb C}(1+2i)\,\nu_{\mathbb C}(Q)$.
- *Annulus check refuting `MeasurePreserving` for $\mathrm{id}_{\mathbb C^\times}$.* Take the
  annulus $A=\{w\in\mathbb C:1\le\lvert w\rvert\le 2\}$ and $g=\mathbf 1_A$. In polar coordinates
  $dx\,dy=r\,dr\,d\theta$:
  $$\nu_{\mathbb C}(A)=\int_0^{2\pi}\!\!\int_1^2 r\,dr\,d\theta = 3\pi,\qquad
    \mu_{\mathbb C}(A)=\int_0^{2\pi}\!\!\int_1^2 r^{-2}\cdot r\,dr\,d\theta = 2\pi\log 2.$$
  Since $3\pi\ne 2\pi\log 2$, $(\mathrm{id}_{\mathbb C^\times})_\ast\nu_{\mathbb C}(A)\ne\mu_{\mathbb C}(A)$:
  the identity map is **not** measure-preserving between $\nu_{\mathbb C}$ and $\mu_{\mathbb C}$!
  Under $w\mapsto zw$ ($z=1+2i$, $\lvert z\rvert=\sqrt 5$), the image annulus is
  $zA=\{\sqrt 5\le\lvert w\rvert\le 2\sqrt 5\}$, with
  $$\nu_{\mathbb C}(zA)=\pi\bigl((2\sqrt 5)^2-(\sqrt 5)^2\bigr)=15\pi=5\,\nu_{\mathbb C}(A),\qquad
    \mu_{\mathbb C}(zA)=2\pi\log\frac{2\sqrt 5}{\sqrt 5}=2\pi\log 2=\mu_{\mathbb C}(A).$$
  Thus $\ell_z$ scales $\nu_{\mathbb C}$ by $\lvert\det_{\mathbb R} M\rvert=5$ while preserving
  $\mu_{\mathbb C}$.
- *Weighted $L^2$ norm and non-real dilation.* For any $a\in\mathbb R$, $U_a g(w)=\lvert w\rvert^{2a}\mathbf 1_A(w)$
  satisfies
  $$\int_{\mathbb C^\times}\lvert U_a g(w)\rvert^2\,\Delta_{\mathbb C}(w)^{1-2a}\,d\mu_{\mathbb C}(w)
    =\int_A \lvert w\rvert^{4a}\lvert w\rvert^{2-4a}\lvert w\rvert^{-2}\,dx\,dy
    =\nu_{\mathbb C}(A)=3\pi=\lVert g\rVert^2_{L^2(\nu_{\mathbb C})}.$$
  Against unweighted $\mu_{\mathbb C}$, however, $\int_A\lvert U_1 g\rvert^2\,d\mu_{\mathbb C}=2\pi\int_1^2 r^3\,dr=\frac{15}{2}\pi\ne 3\pi$,
  while $\int_A\lvert U_{1/2}g\rvert^2\,d\mu_{\mathbb C}=2\pi\int_1^2 r\,dr=3\pi$. Likewise, the
  non-real dilation $(T_z^{(a)}g)(w)=\Delta_{\mathbb C}(z)^a g(zw)=5^a\mathbf 1_{z^{-1}A}(w)$ has
  $z^{-1}A=\{1/\sqrt 5\le\lvert w\rvert\le 2/\sqrt 5\}$ of area $\frac{3\pi}{5}$, so
  $$\lVert T_{1+2i}^{(a)}g\rVert^2_{L^2(\nu_{\mathbb C})}
    = 5^{2a}\cdot\frac{3\pi}{5} = 3\pi\cdot 5^{2a-1},$$
  which equals $\lVert g\rVert^2_{L^2(\nu_{\mathbb C})}=3\pi$ if and only if $a=1/2$ (and jumps to
  $15\pi$ at $a=1$).

**Example 2 (the $S=\{5\}$ unit shell $\mathbb Z_5^\times$ and shells $U_k$, with the audit
counterexample repaired).** Let $F=\mathbb Q$ and $S=\{5\}$, so $K_{\{5\}}=\mathbb Q_5$,
$\nu_{\{5\}}(\mathbb Z_5)=1$, $c_{\{5\}}=\frac{5}{5-1}=\frac{5}{4}$, and
$U_k=5^k\mathbb Z_5^\times=\{x\in\mathbb Q_5^\times:\Delta_{\{5\}}(x)=5^{-k}\}$ ($k\in\mathbb Z$).
From §15.4.3.1 Example 2 we inherit $\nu_{\{5\}}(U_k)=\frac{4}{5}\cdot 5^{-k}$, unnormalized
$\mu_5(U_k)=\frac{4}{5}$, and Masullo-normalized $\mu_{\{5\}}(U_k)=c_{\{5\}}\mu_5(U_k)=\frac{5}{4}\cdot\frac{4}{5}=1$.

- *Audit counterexample on the unit shell $U_0=\mathbb Z_5^\times$, before and after repair.* Take
  the factorized indicator kernel $k(x,y)=\mathbf 1_{U_0}(x)\mathbf 1_{U_0}(y)$. Since
  $\Delta_{\{5\}}(x)=1$ for every $x\in U_0$, $k_a(x,x)=\mathbf 1_{U_0}(x)$ for **every**
  $a\in\mathbb R$ (in particular at $a=1/2$). Evaluating both sides of the diagonal formula gives:
  $$\text{LHS}=\int_{\mathbb Q_5^\times} k_a(x,x)\,d\mu_{\{5\}}(x)=\mu_{\{5\}}(U_0)=1,$$
  $$\text{unrepaired RHS (omitting }c_S\text{)}=\int_{U_0}\Delta_{\{5\}}(x)^{2a-1}\,d\nu_{\{5\}}(x)=\nu_{\{5\}}(U_0)=\frac{4}{5}\ne 1,$$
  $$\text{repaired RHS (Theorem 15.3(3)(i))}=c_{\{5\}}\int_{U_0}\Delta_{\{5\}}(x)^{2a-1}\,d\nu_{\{5\}}(x)=\frac{5}{4}\cdot\frac{4}{5}=1=\text{LHS}.$$
  Notice two things simultaneously on $U_0$: omitting $c_{\{5\}}=\frac{5}{4}$ makes the identity
  false even at $a=1/2$ ($1\ne\frac{4}{5}$), **and** restricting attention to the unit shell $U_0$
  alone cannot detect $a=1/2$, because $\Delta_{\{5\}}|_{U_0}\equiv 1$ makes $\text{LHS}=\text{repaired RHS}=1$
  for *every* $a\in\mathbb R$! To see $a=1/2$ singled out, compare across shells $U_k$
  ($k=-1,0,1,2$):

  | Shell $U_k=5^k\mathbb Z_5^\times$ | $\Delta_{\{5\}}|_{U_k}$ | $\nu_{\{5\}}(U_k)$ | $\mu_{\{5\}}(U_k)$ | $a$ | LHS $\int_{U_k}\Delta^{2a}\,d\mu_{\{5\}}$ | Omitted-$c_S$ $\int_{U_k}\Delta^{2a-1}\,d\nu_{\{5\}}$ | Repaired RHS $c_{\{5\}}\int_{U_k}\Delta^{2a-1}\,d\nu_{\{5\}}$ |
  |---|---:|---:|---:|---:|---:|---:|---:|
  | $U_{-1}=5^{-1}\mathbb Z_5^\times$ | $5$ | $4$ | $1$ | $0$ | $1$ | $4/5$ | $1$ |
  | $U_{-1}=5^{-1}\mathbb Z_5^\times$ | $5$ | $4$ | $1$ | $1/2$ | $5$ | $4$ | $5$ |
  | $U_{-1}=5^{-1}\mathbb Z_5^\times$ | $5$ | $4$ | $1$ | $1$ | $25$ | $20$ | $25$ |
  | $U_0=\mathbb Z_5^\times$ | $1$ | $4/5$ | $1$ | $0,\,1/2,\,1$ | $1$ | $4/5$ | $1$ |
  | $U_1=5\mathbb Z_5^\times$ | $1/5$ | $4/25$ | $1$ | $0$ | $1$ | $4/5$ | $1$ |
  | $U_1=5\mathbb Z_5^\times$ | $1/5$ | $4/25$ | $1$ | $1/2$ | $1/5$ | $4/25$ | $1/5$ |
  | $U_1=5\mathbb Z_5^\times$ | $1/5$ | $4/25$ | $1$ | $1$ | $1/25$ | $4/125$ | $1/25$ |
  | $U_2=25\mathbb Z_5^\times$ | $1/25$ | $4/125$ | $1$ | $1/2$ | $1/25$ | $4/125$ | $1/25$ |
  | $U_2=25\mathbb Z_5^\times$ | $1/25$ | $4/125$ | $1$ | $1$ | $1/625$ | $4/3125$ | $1/625$ |

  In every row, repaired RHS $=$ LHS, and LHS $/ \nu_{\{5\}}(U_k)=\frac{5}{4}\cdot 5^{(1-2a)k}$ is
  independent of $k$ if and only if $a=1/2$, where its constant value is $c_{\{5\}}=\frac{5}{4}$.
- *Normalized half-density $L^2$ check on $U_0$.* Take $g=\mathbf 1_{U_0}\in L^2(\mathbb Q_5,\nu_{\{5\}})$,
  so $\lVert g\rVert^2_{L^2(\nu_{\{5\}})}=\frac{4}{5}$. With the normalized multiplier
  $c_{\{5\}}^{-1/2}=\frac{2}{\sqrt 5}$, the half-density $U_{\{5\},1/2}(g)=\frac{2}{\sqrt 5}\Delta_{\{5\}}^{1/2}\mathbf 1_{U_0}$
  has
  $$\lVert U_{\{5\},1/2}(g)\rVert^2_{L^2(\mu_{\{5\}})}=\Bigl(\frac{2}{\sqrt 5}\Bigr)^2\mu_{\{5\}}(U_0)=\frac{4}{5}\cdot 1=\frac{4}{5}=\lVert g\rVert^2_{L^2(\nu_{\{5\}})},$$
  whereas the unscaled map $g\mapsto\Delta_{\{5\}}^{1/2}g$ gives $\int_{U_0}1\,d\mu_{\{5\}}=1\ne\frac{4}{5}$.
- *Mixed two-place check $S=\{\infty_{\mathbb C},5\}$ and empty-product check $S=\emptyset$.* For
  $S=\{\infty_{\mathbb C},5\}$ ($c_S=1\cdot\frac{5}{4}=\frac{5}{4}$) on $A\times U_1\subset\mathbb C^\times\times\mathbb Q_5^\times$
  at $a=1/2$, $\text{LHS}=\bigl(\int_A\lvert w\rvert^2\,d\mu_{\mathbb C}\bigr)\bigl(\int_{U_1}\Delta_5\,d\mu_{\{5\}}\bigr)=3\pi\cdot\frac{1}{5}=\frac{3}{5}\pi$,
  and repaired $\text{RHS}=\frac{5}{4}\cdot 3\pi\cdot\frac{4}{25}=\frac{3}{5}\pi$ (while omitting
  $c_S$ gives $\frac{12}{25}\pi\ne\frac{3}{5}\pi$). For $S=\emptyset$, $K_\emptyset^\times=\{1\}$,
  $c_\emptyset=1$, and $\Delta_\emptyset(1)^{2a}=1$ for all $a\in\mathbb R$, confirming that
  $S\ne\emptyset$ is indispensable for uniqueness.

**Definition 15.5 (elementary transvections, density-multiplication versus precomposition operators,
and normalized $S$-half-densities).**

1. *(Transvections.)* Let $\iota$ be a finite index set with decidable equality and $R$ a
   commutative ring. A **transvection datum** (`Matrix.TransvectionStruct ι R`,
   [`Transvection.lean:145–166`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Transvection.lean#L145-L166))
   is a quadruple $t=(i,j,h_{ij},c)$ with $i,j\in\iota$, $i\ne j$, and $c\in R$; its matrix is the
   elementary shear $t.\mathrm{toMatrix}=I+c\,E_{ij}$ (`1 + single i j c`), of determinant $1$
   (`TransvectionStruct.det`, `:168–170`) and explicit inverse $(i,j,h_{ij},-c)$ (`:181–197`).
2. *(Two distinct classes of $L^2$ operators.)* Let $(X,\mathcal M,\rho_1)$ and $(Y,\mathcal N,\rho_2)$
   be measure spaces:
   - Given a measurable map $\phi:X\to Y$ that is **measure-preserving** ($\phi_\ast\rho_1=\rho_2$
     and $\phi$ measurable, `MeasureTheory.MeasurePreserving`), the **precomposition operator**
     $C_\phi:L^2(Y,\rho_2)\to L^2(X,\rho_1)$ sends $[v]_{\rho_2}\mapsto [v\circ\phi]_{\rho_1}$
     (`Lp.compMeasurePreserving` / `Lp.compMeasurePreservingₗᵢ`,
     [`LpSpace/Basic.lean:561–583, 632–636`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/LpSpace/Basic.lean#L561-L583)).
   - Given a measurable weight $w:X\to(0,\infty)$ on the **same** underlying space $X$, let
     $\rho_w:=\rho_1.\mathrm{withDensity}(w)$ be the measure $\rho_w(B)=\int_B w\,d\rho_1$. The
     **density-multiplication operator** $M_{w^{1/2}}:L^2(X,\rho_w)\to L^2(X,\rho_1)$ sends
     $[u]_{\rho_w}\mapsto [w^{1/2}u]_{\rho_1}$, with candidate inverse
     $M_{w^{-1/2}}:[v]_{\rho_1}\mapsto [w^{-1/2}v]_{\rho_w}$.
3. *(Normalized $S$-adelic $a$-density map.)* In the product setting of Theorem 15.3(3) with
   $\mu_S=c_S\bigotimes_{v\in S}\mu_v=\nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{-1})$
   and $c_S=\prod_{v\in S_f}N(\mathfrak p_v)/(N(\mathfrak p_v)-1)>0$, define for each $a\in\mathbb R$
   the weighted multiplicative measure $\mu_{S,a}:=\mu_S.\mathrm{withDensity}(\Delta_S^{1-2a})$ on
   $K_S^\times$ and the **normalized $a$-density map**
   $$U_{S,a}(g)(x):=c_S^{-1/2}\,\Delta_S(x)^a\,g(x)\qquad (x\in K_S^\times),$$
   setting $U_S:=U_{S,1/2}$. When $S=\{v\}$ consists of one archimedean place, $c_S=1$ and
   $U_{S,a}$ reduces to $U_a$ of Lemma 15.3d; when $S_f\ne\emptyset$, $c_S>1$ and $U_{S,a}$ differs
   from the unscaled factor $\Delta_S(x)^a$ inside $k_a(x,y)=\Delta_S(x)^a\Delta_S(y)^a k(x,y)$ by
   $c_S^{-1/2}$.

**Lemma 15.5a (Haar nullity of proper subspaces and elementary-matrix scaling on $\mathbb R^\iota$)
`[Lean, read]`.**

1. *(Proper subspaces are Haar-null.)* Let $E$ be a finite-dimensional real normed vector space
   equipped with its Borel $\sigma$-algebra and an additive Haar measure $\mu$. Every proper
   $\mathbb R$-linear subspace $W\subsetneq E$ satisfies $\mu(W)=0$ (`Measure.addHaar_submodule`,
   [`EqHaar.lean:172–197`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean#L172-L197)).
2. *(Diagonal matrices on $\mathbb R^\iota$.)* Let $\iota$ be a finite type with decidable equality
   and $\mathrm{vol}$ the product Lebesgue measure on $\iota\to\mathbb R$. For $D:\iota\to\mathbb R$
   with $\det(\operatorname{diag}(D))=\prod_{i\in\iota}D_i\ne 0$,
   $\lvert\det(\operatorname{diag}(D))\rvert\cdot(\operatorname{diag}(D))_\ast\mathrm{vol}=\mathrm{vol}$
   (`Real.smul_map_diagonal_volume_pi`,
   [`Lebesgue/Basic.lean:364–386`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L364-L386)).
3. *(Transvections preserve $\mathrm{vol}$.)* For every transvection datum $t=(i,j,h_{ij},c)$ on
   $\iota$, multiplication by $t.\mathrm{toMatrix}$ is `MeasurePreserving` on
   $(\iota\to\mathbb R,\mathrm{vol})$ (`Real.volume_preserving_transvectionStruct`,
   [`Lebesgue/Basic.lean:389–408`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L389-L408)).
4. *(Invertible linear maps on $\mathbb R^\iota$.)* Every $M\in\mathrm{GL}_\iota(\mathbb R)$
   factors as $M=L_1\cdot\operatorname{diag}(D)\cdot L_2$ where $L_1,L_2$ are products of
   transvection matrices (`Matrix.exists_list_transvec_mul_diagonal_mul_list_transvec`,
   [`Transvection.lean:676–687`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Transvection.lean#L676-L687));
   consequently, for every $\mathbb R$-linear $f:(\iota\to\mathbb R)\to(\iota\to\mathbb R)$ with
   $\det f\ne 0$, $f_\ast\mathrm{vol}=\lvert(\det f)^{-1}\rvert\,\mathrm{vol}$
   (`Real.map_matrix_volume_pi_eq_smul_volume_pi` and `Real.map_linearMap_volume_pi_eq_smul_volume_pi`,
   [`Lebesgue/Basic.lean:411–444`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L411-L444)).

*Proof.* (1) Mathlib first proves `addHaar_eq_zero_of_disjoint_translates_aux`
([`EqHaar.lean:137–150`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean#L137-L150)):
if $s\subseteq E$ is Borel measurable and bounded, and $(u_n)_{n\in\mathbb N}$ is a bounded sequence
in $E$ whose translates $\{u_n\}+s$ are pairwise disjoint, then assuming $\mu(s)\ne 0$ gives
$$\infty=\sum_{n=0}^\infty\mu(s)=\sum_{n=0}^\infty\mu(\{u_n\}+s)=\mu\Bigl(\bigcup_{n=0}^\infty(\{u_n\}+s)\Bigr)=\mu(\operatorname{range}(u)+s)<\infty$$
by translation invariance (`measure_preimage_add`), countable additivity (`measure_iUnion`), and
finiteness of Haar measure on the bounded sumset $\operatorname{range}(u)+s$ (`(hu.add sb).measure_lt_top`),
a contradiction (`lt_irrefl ∞`). Exhausting an arbitrary Borel set $s=\bigcup_{N\in\mathbb N}(s\cap\overline B(0,N))$
by closed balls (`iUnion_inter_closedBall_nat`) removes boundedness of $s$
(`addHaar_eq_zero_of_disjoint_translates`, `:154–169`). Now let $W\subsetneq E$ be a proper
$\mathbb R$-subspace (`addHaar_submodule`, `:172–197`): pick $x\in E\setminus W$ and $c:=\frac{1}{2}\in(0,1)$,
and set $u_n:=c^n x$. Because $c^n x\to 0$, $\operatorname{range}(u)$ is bounded (`isBounded_range_of_tendsto`);
because $E$ is finite-dimensional, $W$ is closed (`Submodule.closed_of_finiteDimensional`) and hence
Borel measurable; and if $m\ne n$ with $y\in(c^m x+W)\cap(c^n x+W)$, subtracting gives
$(c^n-c^m)x\in W$, whence $x=(c^n-c^m)^{-1}(c^n-c^m)x\in W$ since $t\mapsto c^t$ is strictly
decreasing (`pow_right_strictAnti₀`), contradicting $x\notin W$. Thus $\mu(W)=0$.

(2) By `Measure.pi_eq` ([`Lebesgue/Basic.lean:369–385`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L369-L385)),
two $\sigma$-finite product measures on $\iota\to\mathbb R$ agree once they agree on measurable
rectangles $R=\prod_{i\in\iota}s_i$. Since $\operatorname{diag}(D)^{-1}(R)=\prod_{i\in\iota}(D_i\cdot)^{-1}(s_i)$
and $\det(\operatorname{diag}(D))=\prod_{i\in\iota}D_i$, factoring $\lvert\prod_i D_i\rvert=\prod_i\lvert D_i\rvert$
and applying Lemma 15.3a(1) (`Real.volume_preimage_mul_left`, $\lvert D_i\rvert\operatorname{vol}((D_i\cdot)^{-1}s_i)=\operatorname{vol}(s_i)$)
in each coordinate gives $\lvert\det(\operatorname{diag}(D))\rvert\,\mathrm{vol}(\operatorname{diag}(D)^{-1}R)=\prod_i\operatorname{vol}(s_i)=\mathrm{vol}(R)$.

(3) For $t=(i,j,h_{ij},c)$, `Real.volume_preserving_transvectionStruct`
([`Lebesgue/Basic.lean:389–408`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L389-L408))
checks $\mathrm{vol}((t.\mathrm{toMatrix})^{-1}R)=\mathrm{vol}(R)$ on rectangles $R=\prod_k s_k$ by
rewriting both sides as Lebesgue integrals of indicators (`lintegral_indicator_one`) and integrating
first along the single coordinate $\{i\}$ via the Fubini marginal lemma
`lintegral_eq_of_lmarginal_eq {t.i}` and `lmarginal_singleton`. Because $j\ne i$, the $j$-th
coordinate $x_j$ is constant along each $\{i\}$-fibre, so $(t.\mathrm{toMatrix}\cdot x)_i=x_i+c x_j$
acts on the $i$-th coordinate by a pure translation $+c x_j$, which preserves the one-dimensional
Lebesgue integral by `lintegral_add_right_eq_self`.

(4) In [`Transvection.lean:337–687`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Transvection.lean#L337-L687),
induction on $\lvert\iota\rvert$ splits a non-empty index type as $\mathrm{Fin}\,r\oplus\mathrm{Unit}$.
If some entry in the last row or column is nonzero, a transvection moves a nonzero pivot into the
corner $(\mathrm{inr}\,\star,\mathrm{inr}\,\star)$; then `listTransvecCol M` (`:337–341`) and
`listTransvecRow M` (`:343–346`) clear the remaining $r$ entries of the last column and last row,
reducing $M$ to `IsTwoBlockDiagonal` (`:524–558`), and if the entire last column vanishes the matrix
already block-triangularizes and clears similarly. Inducting on the top-left $r\times r$ block yields
$M=L_1\cdot\operatorname{diag}(D)\cdot L_2$ (`exists_list_transvec_mul_diagonal_mul_list_transvec`,
`:676–687`), packaged as the induction principle `Matrix.diagonal_transvection_induction_of_det_ne_zero`
(`:731–743`). In `Real.map_matrix_volume_pi_eq_smul_volume_pi` (`Lebesgue/Basic.lean:411–430`),
the predicate $P(M):\iff (x\mapsto Mx)_\ast\mathrm{vol}=\lvert(\det M)^{-1}\rvert\,\mathrm{vol}$
holds for $\operatorname{diag}(D)$ by (2), holds for every transvection by (3) (since $\det t=1$),
and is closed under matrix products by functoriality of `Measure.map_map` and multiplicativity of
$\det$; reindexing $\iota\simeq\mathrm{Fin}\,n$ and representing $f$ by `LinearMap.toMatrix` gives
`Real.map_linearMap_volume_pi_eq_smul_volume_pi` (`:433–444`). $\square$

**Lemma 15.5b (production proof of `map_linearMap_addHaar_eq_smul_addHaar` and
`addHaar_image_linearMap`) `[Lean, read]`.** Let $E$ be a finite-dimensional real normed space
equipped with its Borel $\sigma$-algebra and an additive Haar measure $\mu$, and let
$f:E\to E$ be an $\mathbb R$-linear map.

1. *(Pushforward and preimages for $\det f\ne 0$.)* If $\det f\ne 0$, then
   $$f_\ast\mu=\lvert(\det f)^{-1}\rvert\,\mu
   \qquad\text{and}\qquad
   \mu(f^{-1}(B))=\lvert(\det f)^{-1}\rvert\,\mu(B)\quad\text{for every subset } B\subseteq E$$
   (`Measure.map_linearMap_addHaar_eq_smul_addHaar`,
   [`EqHaar.lean:231–256`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean#L231-L256);
   `Measure.addHaar_preimage_linearMap`,
   [`EqHaar.lean:261–268`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean#L261-L268)).
2. *(Images for all linear maps, invertible or singular.)* For **every** $\mathbb R$-linear map
   $f:E\to E$ and **every** subset $B\subseteq E$ (without assuming $B$ Borel measurable),
   $$\mu(f(B))=\lvert\det f\rvert\,\mu(B)$$
   (`Measure.addHaar_image_linearMap`,
   [`EqHaar.lean:297–306`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean#L297-L306),
   with the convention $0\cdot\infty=0$ in $\mathbb R_{\ge 0\infty}$).

*Proof.* (1) First suppose $E=(\iota\to\mathbb R)$ for a finite type $\iota$, with an arbitrary
additive Haar measure $\mu$ (`map_linearMap_addHaar_pi_eq_smul_addHaar`, `EqHaar.lean:218–226`). By
Haar uniqueness normalized on the unit cube $[0,1]^\iota$ (`addHaarMeasure_unique μ (piIcc01 ι)`
and `addHaarMeasure_eq_volume_pi`, `:117–121`), $\mu=\mu([0,1]^\iota)\,\mathrm{vol}$. Pushing forward
along $f$ commutes with scalar multiplication (`Measure.map_smul`), so Lemma 15.5a(4) yields
$f_\ast\mu=\mu([0,1]^\iota)\,\lvert(\det f)^{-1}\rvert\,\mathrm{vol}=\lvert(\det f)^{-1}\rvert\,\mu$.

For a general finite-dimensional $E$ (`EqHaar.lean:231–256`), set $n:=\operatorname{finrank}_{\mathbb R}E$
and choose an $\mathbb R$-linear isomorphism $e:E\xrightarrow{\sim}(\mathrm{Fin}\,n\to\mathbb R)$
(`LinearEquiv.ofFinrankEq`). Define $g:=e\circ f\circ e^{-1}$ on $\mathrm{Fin}\,n\to\mathbb R$. By
similarity invariance of the determinant (`LinearMap.det_conj`,
[`Determinant.lean:306–321`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Determinant.lean#L306-L321)),
$\det g=\det f\ne 0$. Every linear map between finite-dimensional real normed spaces is continuous
(`LinearMap.continuous_of_finiteDimensional`), so $e$, $e^{-1}$, and $g$ are continuous (hence
Borel measurable), and $e$ is a topological additive-group isomorphism pushing $\mu$ to an additive
Haar measure $e_\ast\mu$ on $\mathrm{Fin}\,n\to\mathbb R$ (`AddEquiv.isAddHaarMeasure_map`). Applying
the $\mathrm{Fin}\,n\to\mathbb R$ case to $(g,e_\ast\mu)$ and pushing back along $e^{-1}$ via
$f=e^{-1}\circ g\circ e$ and `Measure.map_map` gives
$$f_\ast\mu=(e^{-1})_\ast\bigl(g_\ast(e_\ast\mu)\bigr)
=(e^{-1})_\ast\bigl(\lvert(\det g)^{-1}\rvert\,e_\ast\mu\bigr)
=\lvert(\det f)^{-1}\rvert\,(e^{-1}\circ e)_\ast\mu=\lvert(\det f)^{-1}\rvert\,\mu.$$
Next, because $\det f\ne 0$, `f.equivOfDetNeZero hf` (`Determinant.lean:569–575`) upgrades $f$ to a
linear equivalence, hence a homeomorphism and a `MeasurableEquiv`. For a `MeasurableEquiv`,
`MeasurableEquiv.map_apply` identifies $(f_\ast\mu)(B)=\mu(f^{-1}(B))$ for **every** set
$B\subseteq E$ (outer-measure invariance under measurable bijections with measurable inverse,
needing no measurability of $B$!), yielding `addHaar_preimage_linearMap` (`:261–268`).

(2) Following `EqHaar.lean:297–306`, split on whether $\det f\ne 0$ or $\det f=0$:
- If $\det f\ne 0$, let $\widetilde f:E\xrightarrow{\sim} E$ be the continuous linear equivalence
  `(f.equivOfDetNeZero hf).toContinuousLinearEquiv`. Then $\widetilde f(B)=(\widetilde f^{-1})^{-1}(B)$
  (`ContinuousLinearEquiv.image_eq_preimage_symm`), and applying (1) to $\widetilde f^{-1}$ together
  with $\det(\widetilde f^{-1})=(\det f)^{-1}$ (`LinearEquiv.det_coe_symm`, `Determinant.lean:508–510`)
  gives $\mu(f(B))=\mu((\widetilde f^{-1})^{-1}(B))=\lvert(\det(\widetilde f^{-1}))^{-1}\rvert\,\mu(B)=\lvert\det f\rvert\,\mu(B)$.
- If $\det f=0$, then $f$ is not surjective—its image $\operatorname{range}(f)$ is a **proper**
  $\mathbb R$-linear subspace of $E$ (`LinearMap.range_lt_top_of_det_eq_zero`,
  [`Determinant.lean:369–375`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Determinant.lean#L369-L375)).
  Since $f(B)\subseteq\operatorname{range}(f)\subsetneq E$, monotonicity of outer measure and Lemma
  15.5a(1) give $\mu(f(B))\le\mu(\operatorname{range}(f))=0=\lvert 0\rvert\,\mu(B)$. $\square$

**Lemma 15.5c (real determinant of complex multiplication and $\Delta_{\mathbb C}(z)=\lvert z\rvert^2$).**
Identify $\mathbb C$ as a two-dimensional $\mathbb R$-vector space via the ordered basis
`Complex.basisOneI` $=(1,i)$ (`finrank ℝ ℂ = 2`,
[`Complex/Module.lean:144–165`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Complex/Module.lean#L144-L165),
[`Complex/FiniteDimensional.lean:31–32`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean#L31-L32)),
carrying planar Lebesgue measure $\nu_{\mathbb C}$ (`Complex.volume_preserving_equiv_pi`,
[`Lebesgue/Complex.lean:53–62`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean#L53-L62)).
For every $z=u+iv\in\mathbb C$ ($u=\Re z$, $v=\Im z$), left multiplication $\ell_z(w)=zw$
(`Algebra.lmul ℝ ℂ z`) has real matrix and determinant
$$\operatorname{Mat}_{\{1,i\}}(\ell_z)=\begin{pmatrix}u&-v\\v&u\end{pmatrix},\qquad
  \det_{\mathbb R}(\ell_z)=\operatorname{Nm}_{\mathbb C/\mathbb R}(z)=u^2+v^2=\lvert z\rvert^2\ge 0.$$
Consequently, $\nu_{\mathbb C}(zB)=\lvert z\rvert^2\,\nu_{\mathbb C}(B)$ for every $z\in\mathbb C$
and every subset $B\subseteq\mathbb C$, and $\Delta_{\mathbb C}(z)=\lvert z\rvert^2$ for every
$z\in\mathbb C^\times$. (`[Lean, read]` for the basis, volume, algebra-norm, and Haar-image lemmas;
`[Expository]` for the two-line $2\times 2$ matrix evaluation, which is not packaged as a separate
`Algebra.norm_complex_apply` lemma at the pin—compare `Complex.det_conjAe = -1` at
[`Complex/Determinant.lean:26–28`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Complex/Determinant.lean#L26-L28).)

*Proof.* By `Complex.coe_basisOneI` and `Complex.coe_basisOneI_repr`
(`Complex/Module.lean:156–163`), `basisOneI` has basis vectors $e_0=1$, $e_1=i$ and coordinate map
$w\mapsto(\Re w,\Im w)$. Evaluating $\ell_z$ on $(1,i)$ gives $\ell_z(1)=u\cdot 1+v\cdot i$ and
$\ell_z(i)=zi=-v\cdot 1+u\cdot i$, which are the two columns of $\begin{pmatrix}u&-v\\v&u\end{pmatrix}$.
By `Algebra.norm_apply` and `Algebra.norm_eq_matrix_det`
([`RingTheory/Norm/Defs.lean:61–64, 82–84`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Norm/Defs.lean#L61-L84)),
$\det_{\mathbb R}(\ell_z)=\operatorname{Algebra.norm}\,\mathbb R\,z=\det\operatorname{Mat}_{\{1,i\}}(\ell_z)=u^2+v^2$.
In Mathlib's complex norm file, $u^2+v^2=\operatorname{Complex.normSq}z=\lVert z\rVert^2$
(`Complex.normSq_apply`, [`Data/Complex/Basic.lean:517–518`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Complex/Basic.lean#L517-L518);
`Complex.normSq_eq_norm_sq`, [`Analysis/Complex/Norm.lean:147–150`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/Norm.lean#L147-L150)).
Since $\nu_{\mathbb C}$ is an additive Haar measure on $\mathbb C$ (transported from
$\mathrm{Fin}\,2\to\mathbb R$ via `OrthonormalBasis.volume_parallelepiped` in
[`Haar/InnerProductSpace.lean:82–96`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean#L82-L96)
and `Complex.volume_preserving_equiv_pi`), Lemma 15.5b(2) applied to $f=\ell_z$ yields
$\nu_{\mathbb C}(zB)=\lvert\det_{\mathbb R}(\ell_z)\rvert\,\nu_{\mathbb C}(B)=\lvert z\rvert^2\nu_{\mathbb C}(B)$
for all $z\in\mathbb C$ and all $B\subseteq\mathbb C$. Comparing with Definition 15.2(1) on a set of
positive finite measure (such as $[0,1]^2$ in Example 1) gives $\Delta_{\mathbb C}(z)=\lvert z\rvert^2$
for all $z\in\mathbb C^\times$. $\square$

**Lemma 15.5d (density-weighted $L^2$ isometric isomorphism versus `MeasurePreserving`
precomposition).** Let $(X,\mathcal M,\rho)$ be a measure space and $w:X\to(0,\infty)$ a measurable
weight, with weighted measure $\rho_w:=\rho.\mathrm{withDensity}(w)$ (via `ENNReal.ofReal ∘ w`).

1. *(Genuine `withDensity` $L^2$ unitary.)* Pointwise multiplication $M_{w^{1/2}}([u]_{\rho_w}):=[w^{1/2}u]_\rho$
   is a well-defined $\mathbb C$-linear isometric isomorphism of Hilbert spaces
   $$M_{w^{1/2}} : L^2(X,\rho_w) \xrightarrow{\;\sim\;} L^2(X,\rho), \qquad
     M_{w^{1/2}}^{-1}([v]_\rho) = [w^{-1/2}v]_{\rho_w},$$
   preserving norms and inner products: $\langle M_{w^{1/2}}u_1,M_{w^{1/2}}u_2\rangle_{L^2(\rho)}=\langle u_1,u_2\rangle_{L^2(\rho_w)}$.
2. *(Strict separation from `compMeasurePreserving`.)* Mathlib's `Lp.compMeasurePreserving ϕ hϕ`
   (`LpSpace/Basic.lean:561–583`) acts on equivalence classes by $[v]_{\rho_2}\mapsto [v\circ\phi]_{\rho_1}$
   (`AEEqFun.compMeasurePreserving`, [`AEEqFun.lean:280–297`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/AEEqFun.lean#L280-L297))
   under the hypothesis $\phi_\ast\rho_1=\rho_2$. For $\phi=\mathrm{id}_X$, $(\mathrm{id}_X)_\ast\rho=\rho$,
   so `MeasurePreserving id ρ ρ_w` holds on a $\sigma$-finite space $(X,\rho)$ if and only if $w=1$
   $\rho$-almost everywhere; whenever $w$ is not $\rho$-a.e. equal to $1$, no precomposition
   operator $C_{\mathrm{id}}$ exists between $L^2(X,\rho)$ and $L^2(X,\rho_w)$, and when $w=1$
   $\rho$-a.e., $C_{\mathrm{id}}=M_1$ is the trivial identity (`compMeasurePreserving_id`, `:589–595`).
3. *(How the two operators compose to produce unitary dilations.)* For $(K,\nu,\Delta_K,\mu)$ as in
   Definition 15.2 and $t\in K^\times$, left multiplication $\tau_t(x):=tx$ satisfies
   $(\tau_t)_\ast\mu=\mu$ on $K^\times$ (Lemma 15.3c), so `Lp.compMeasurePreservingₗᵢ` supplies a
   unitary precomposition operator $C_{\tau_t}:L^2(K^\times,\mu)\xrightarrow{\sim} L^2(K^\times,\mu)$,
   $(C_{\tau_t}f)(x)=f(tx)$. Writing $\mu=\nu|_{K^\times}.\mathrm{withDensity}(\Delta_K^{-1})$ and
   setting $U_{1/2}:=M_{\Delta_K^{-1/2}}^{-1}:L^2(K,\nu)\xrightarrow{\sim} L^2(K^\times,\mu)$
   ($g\mapsto\Delta_K^{1/2}g|_{K^\times}$, using $\nu(\{0\})=0$), conjugating $C_{\tau_t}$ by the
   density unitary $U_{1/2}$ yields Proposition 15.4's unitary dilation on $L^2(K,\nu)$:
   $$U_{1/2}^{-1}\circ C_{\tau_t}\circ U_{1/2} = T_t^{(1/2)},\qquad
     \bigl(T_t^{(1/2)}g\bigr)(x)=\Delta_K(t)^{1/2}g(tx).$$
   (`[Lean, read]` for the `WithDensity`, `LebesgueNormedSpace`, `L1.withDensitySMulLI`, and
   `compMeasurePreserving` lemmas below; `[Expository]` for the $p=2$ square-root assembly.)

*Proof.* (1) Patterned on Mathlib's $L^1$ linear isometry `L1.withDensitySMulLI`
([`L1Space/Integrable.lean:864–914`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L864-L914),
which multiplies by $f$ rather than $w^{1/2}$ because $p=1$), we verify four things from the pinned
`WithDensity` supply:
- *Same almost-everywhere equality:* Because $0<w(x)<\infty$ everywhere, the $\mathbb R_{\ge 0\infty}$-density
  $d(x):=\mathrm{ofReal}(w(x))$ satisfies $d(x)\ne 0$ for all $x$. By `withDensity_ae_eq`
  ([`WithDensity.lean:589–596`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/WithDensity.lean#L589-L596),
  derived from `ae_withDensity_iff'` at `:291–300`), $u_1=^{\mathrm{a.e.}}_{\rho_w} u_2 \iff u_1=^{\mathrm{a.e.}}_\rho u_2$.
  Since $w(x)^{1/2}>0$ everywhere, $u_1=u_2$ $\rho$-a.e. iff $w^{1/2}u_1=w^{1/2}u_2$ $\rho$-a.e., so
  $M_{w^{1/2}}$ and $M_{w^{-1/2}}$ are well-defined and mutually inverse on a.e.-equivalence classes,
  and $\mathbb C$-linearity holds pointwise hence a.e.
- *Strong measurability:* Since $w^{1/2}:X\to\mathbb R_{\ge 0}$ is measurable and nowhere zero,
  applying `aemeasurable_withDensity_iff`
  ([`LebesgueNormedSpace.lean:22–49`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/LebesgueNormedSpace.lean#L22-L49))
  and the separability of $\mathbb C$ shows that $u$ is `AEStronglyMeasurable` for $\rho_w$ (which
  equals $u$ `AEStronglyMeasurable` for $\rho$ since $\rho_w$ and $\rho$ share null sets) if and
  only if $w^{1/2}u$ is `AEStronglyMeasurable` for $\rho$ (multiplying by the measurable scalar
  $w^{1/2}$ or $w^{-1/2}$).
- *$L^2$ seminorm identity:* In Mathlib, $\lVert [u]_{\rho_w}\rVert_{L^2(\rho_w)}=\bigl(\int_X \lVert u(x)\rVert_{\mathrm{e}}^2\,d\rho_w(x)\bigr)^{1/2}$
  at $p=2\notin\{0,\infty\}$. Because $d=\mathrm{ofReal}\circ w$ is measurable and $x\mapsto\lVert u(x)\rVert_{\mathrm{e}}^2$
  is $\rho$-a.e. measurable, `lintegral_withDensity_eq_lintegral_mul₀'`
  ([`WithDensity.lean:419–449`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/WithDensity.lean#L419-L449);
  cf. `[Tao2011]`, Exercise 1.2.1, cited in `WithDensity.lean:389`) gives
  $$\int_X \lVert u(x)\rVert_{\mathrm{e}}^2\,d\rho_w(x)
    = \int_X \mathrm{ofReal}(w(x))\,\lVert u(x)\rVert_{\mathrm{e}}^2\,d\rho(x)
    = \int_X \bigl\lVert w(x)^{1/2}u(x)\bigr\rVert_{\mathrm{e}}^2\,d\rho(x).$$
  Taking square roots shows $u\in\mathcal L^2(\rho_w)\iff w^{1/2}u\in\mathcal L^2(\rho)$ and
  $\lVert M_{w^{1/2}}[u]_{\rho_w}\rVert_{L^2(\rho)}=\lVert [u]_{\rho_w}\rVert_{L^2(\rho_w)}$.
- *Inverse measure symmetry and inner product:* By `withDensity_inv_same₀`
  ([`WithDensity.lean:559–567`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/WithDensity.lean#L559-L567)),
  $\rho_w.\mathrm{withDensity}(w^{-1})=\rho$, so $M_{w^{-1/2}}$ is literally the same construction
  for $(\rho_w,w^{-1})$. Polarization (or applying `lintegral`/Bochner change of density directly to
  $w^{1/2}u_1\cdot\overline{w^{1/2}u_2}=w\,u_1\overline{u_2}$) gives inner-product preservation.

(2) By definition of `MeasurePreserving`, $(\mathrm{id}_X)_\ast\rho=\rho_w$ means $\rho(B)=\int_B w\,d\rho$
for every $B\in\mathcal M$. On any $\sigma$-finite space $(X,\rho)$, testing on $\{w\ge 1+\varepsilon\}\cap X_n$
and $\{w\le 1-\varepsilon\}\cap X_n$ along an exhausting sequence $\rho(X_n)<\infty$ forces $w=1$
$\rho$-a.e.; conversely, if $w=1$ $\rho$-a.e., then $\rho_w=\rho$ and `compMeasurePreserving_id`
gives the identity operator.

(3) By Lemma 15.3c, $\tau_t:K^\times\to K^\times$ is a homeomorphism with $(\tau_t)_\ast\mu=\mu$,
so `Lp.compMeasurePreservingₗᵢ` applies at $p=2$. For $g\in L^2(K,\nu)$, $(U_{1/2}g)(x)=\Delta_K(x)^{1/2}g(x)$
on $K^\times$, hence $(C_{\tau_t}U_{1/2}g)(x)=\Delta_K(tx)^{1/2}g(tx)=\Delta_K(t)^{1/2}\Delta_K(x)^{1/2}g(tx)$
by multiplicativity of $\Delta_K$ (`distribHaarChar_mul`), and applying $U_{1/2}^{-1}=M_{\Delta_K^{-1/2}}$
cancels $\Delta_K(x)^{1/2}$ on $K^\times$ (which is $\nu$-conull in $K$ by Lemma 15.3b(1)), leaving
$\Delta_K(t)^{1/2}g(tx)=(T_t^{(1/2)}g)(x)$. $\square$

**Theorem 15.6 (unified archimedean determinant, finite-product $c_S$ normalization, and
half-density transport).** Let $F$ be a number field and $S=S_{\mathbb R}\sqcup S_{\mathbb C}\sqcup S_f$
a finite set of places of $F$. Fix local additive Haar measures $\nu_v$ ($dx$ for $v\in S_{\mathbb R}$,
planar $dx\,dy$ under `Complex.basisOneI` for $v\in S_{\mathbb C}$, and $\nu_v(\mathcal O_v)=1$ for
$v\in S_f$), local moduli $\Delta_v=\Delta_{F_v}$, unnormalized multiplicative Haar measures
$\mu_v=\nu_v|_{F_v^\times}.\mathrm{withDensity}(\Delta_v^{-1})$, and on $K_S:=\prod_{v\in S}F_v$ and
$K_S^\times:=\prod_{v\in S}F_v^\times$ set
$$\nu_S:=\bigotimes_{v\in S}\nu_v,\qquad
  \Delta_S(x):=\prod_{v\in S}\Delta_v(x_v),\qquad
  c_S:=\prod_{v\in S_f}\frac{N(\mathfrak p_v)}{N(\mathfrak p_v)-1},\qquad
  \mu_S:=c_S\bigotimes_{v\in S}\mu_v$$
(with the empty-product conventions $K_\emptyset=K_\emptyset^\times=\{1\}$, $\Delta_\emptyset\equiv 1$,
$c_\emptyset=1$, and $\nu_\emptyset=\mu_\emptyset$ the unit point mass). Then:

1. *(Explicit determinant and valuation formula for $\Delta_S$, and zero-hyperplane removal.)* For
   every $x=(x_v)_{v\in S}\in K_S^\times$,
   $$\Delta_S(x)
     = \prod_{v\in S_{\mathbb R}}\bigl\lvert\det_{\mathbb R}(\ell_{x_v})\bigr\rvert
       \cdot \prod_{v\in S_{\mathbb C}}\bigl\lvert\det_{\mathbb R}(\ell_{x_v})\bigr\rvert
       \cdot \prod_{v\in S_f} N(\mathfrak p_v)^{-\operatorname{ord}_v(x_v)}
     = \prod_{v\in S_{\mathbb R}}\lvert x_v\rvert
       \cdot \prod_{v\in S_{\mathbb C}}\bigl((\Re x_v)^2+(\Im x_v)^2\bigr)
       \cdot \prod_{v\in S_f} N(\mathfrak p_v)^{-\operatorname{ord}_v(x_v)}.$$
   Moreover $\nu_S(K_S\setminus K_S^\times)=0$, so restriction gives $L^2(K_S,\nu_S)\cong L^2(K_S^\times,\nu_S|_{K_S^\times})$,
   and $\mu_S=\nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{-1})$ is a Haar measure on
   $K_S^\times$ invariant under multiplication and inversion, normalized on the maximal compact
   unit subgroup $\prod_{v\in S_f}\mathcal O_v^\times$ when $S=S_f$.
2. *(Unified measure identity transporting both normalized half-densities and unscaled diagonal
   kernels.)* For every $a\in\mathbb R$, the density-weighted measures on $K_S^\times$ satisfy
   $$\mu_{S,a}:=\mu_S.\mathrm{withDensity}(\Delta_S^{1-2a})
     = \nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{-2a}),\qquad
     \mu_S.\mathrm{withDensity}(\Delta_S^{2a})
     = \nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{2a-1}).$$
   From this single change of density flow both downstream formulas:
   - *(Normalized $a$-density $L^2$ unitary.)* The multiplication operator
     $U_{S,a}(g)=c_S^{-1/2}\Delta_S^a g|_{K_S^\times}$ is a unitary isomorphism
     $L^2(K_S,\nu_S)\xrightarrow{\sim} L^2(K_S^\times,\mu_{S,a})$, satisfying for all
     $g,h\in L^2(K_S,\nu_S)$
     $$\int_{K_S^\times} U_{S,a}(g)(x)\,\overline{U_{S,a}(h)(x)}\,\Delta_S(x)^{1-2a}\,d\mu_S(x)
       = \int_{K_S} g(x)\,\overline{h(x)}\,d\nu_S(x);$$
     at $a=1/2$, $U_S=U_{S,1/2}:L^2(K_S,\nu_S)\xrightarrow{\sim} L^2(K_S^\times,\mu_S)$ is unitary
     into unweighted $L^2(K_S^\times,\mu_S)$, and conjugating the `MeasurePreserving` translation
     $C_{\tau_t}$ on $L^2(K_S^\times,\mu_S)$ by $U_S$ yields the unitary dilation
     $(T_t^{(1/2)}g)(x)=\Delta_S(t)^{1/2}g(tx)$ on $L^2(K_S,\nu_S)$ for all $t\in K_S^\times$.
   - *(Unscaled diagonal kernel integral — Masullo (12.4.1.17)–(12.4.1.23).)* For every Borel
     kernel $k$ on $K_S^\times\times K_S^\times$ with Borel diagonal $x\mapsto k(x,x)$ and
     $k_a(x,y):=\Delta_S(x)^a\Delta_S(y)^a k(x,y)$,
     $$\int_{K_S^\times} k_a(x,x)\,d\mu_S(x)
       = c_S\int_{K_S^\times} k(x,x)\,\Delta_S(x)^{2a-1}\,d\nu_S(x)$$
     whenever either side converges absolutely. In particular, for a rank-one kernel
     $k(x,y)=g(x)\overline{h(y)}$ with $g,h\in L^2(K_S,\nu_S)$ at $a=1/2$,
     $$\int_{K_S^\times} k_{1/2}(x,x)\,d\mu_S(x)
       = c_S\,\langle U_S g, U_S h\rangle_{L^2(\mu_S)}
       = c_S\,\langle g, h\rangle_{L^2(\nu_S)},$$
     reconciling the exact cancellation of $c_S$ in $U_S$ with its explicit presence in (12.4.1.17)
     and (12.4.1.23) [Paper; Masullo p. 518].
3. *(Non-empty $S$ criterion for uniqueness of $a=1/2$.)* If $S\ne\emptyset$, the following four
   conditions on $a\in\mathbb R$ are equivalent:
   *(i)* $\mu_S.\mathrm{withDensity}(\Delta_S^{2a})=c\,\nu_S|_{K_S^\times}$ for some $c>0$ (and then
   necessarily $c=c_S$);
   *(ii)* $U_{S,a}:L^2(K_S,\nu_S)\to L^2(K_S^\times,\mu_S)$ is an isometry (or scalar multiple of
   one);
   *(iii)* $T_t^{(a)}:g(x)\mapsto\Delta_S(t)^a g(tx)$ is unitary on $L^2(K_S,\nu_S)$ for every
   $t\in K_S^\times$;
   *(iv)* $a=1/2$.
   If $S=\emptyset$, then *(i)*–*(iii)* hold with $c=c_\emptyset=1$ for **every** $a\in\mathbb R$.

*Proof.* (1) The archimedean determinant values are Lemma 15.3a(1) (for $v\in S_{\mathbb R}$, where
$\ell_{x_v}$ is the $1\times 1$ matrix $(x_v)$) and Lemma 15.5c (for $v\in S_{\mathbb C}$); the
non-archimedean value $\Delta_v(x_v)=N(\mathfrak p_v)^{-\operatorname{ord}_v(x_v)}$ and unit mass
$\mu_v(\mathcal O_v^\times)=1-N(\mathfrak p_v)^{-1}$ are inherited from Lemma 15.3a(3). The
complement $K_S\setminus K_S^\times=\bigcup_{v\in S}\{x\in K_S:x_v=0\}$ is a finite union of
coordinate hyperplanes; for each $v\in S$, $\nu_v(\{0\})=0$ by Lemma 15.3b(1) and the remaining
factors are $\sigma$-finite, so Fubini/Tonelli gives $\nu_S(\{x:x_v=0\})=0$ and hence
$\nu_S(K_S\setminus K_S^\times)=0$. Product density multiplication and Lemma 15.3c in each coordinate
give $\mu_S=\nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{-1})$ and its multiplication and
inversion invariance; when $S=S_f$, $\mu_S\bigl(\prod_{v\in S_f}\mathcal O_v^\times\bigr)=c_S\prod_{v\in S_f}(1-N(\mathfrak p_v)^{-1})=1$.

(2) Since $c_S\Delta_S^{-1}$, $\Delta_S^{1-2a}$, and $\Delta_S^{2a}$ are continuous positive functions
on $K_S^\times$, `withDensity_mul₀` (`WithDensity.lean:538–544`) composes densities by pointwise
multiplication:
$$\mu_S.\mathrm{withDensity}(\Delta_S^{1-2a})
  = \nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{-1}\cdot\Delta_S^{1-2a})
  = \nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{-2a}),$$
and similarly $\mu_S.\mathrm{withDensity}(\Delta_S^{2a})=\nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{2a-1})$.
Applying Lemma 15.5d(1) on $X=K_S^\times$ with $\rho=\nu_S|_{K_S^\times}$ and strictly positive
measurable weight $w(x)=c_S\Delta_S(x)^{-2a}$ (so $w(x)^{-1/2}=c_S^{-1/2}\Delta_S(x)^a$) shows that
$M_{w^{-1/2}}:[g]_\rho\mapsto [c_S^{-1/2}\Delta_S^a g]_{\rho_w}$ is unitary from
$L^2(K_S^\times,\nu_S|_{K_S^\times})\cong L^2(K_S,\nu_S)$ onto $L^2(K_S^\times,\mu_{S,a})$. At
$a=1/2$, $\Delta_S^{1-2a}\equiv 1$ so $\mu_{S,1/2}=\mu_S$, and the conjugation formula
$U_S^{-1}\circ C_{\tau_t}\circ U_S=T_t^{(1/2)}$ follows exactly as in Lemma 15.5d(3) because
$c_S^{-1/2}$ and $c_S^{1/2}$ cancel:
$$(U_S^{-1}C_{\tau_t}U_S g)(x)=c_S^{1/2}\Delta_S(x)^{-1/2}\bigl(c_S^{-1/2}\Delta_S(tx)^{1/2}g(tx)\bigr)=\Delta_S(t)^{1/2}g(tx).$$
Integrating $k(x,x)$ against $\mu_S.\mathrm{withDensity}(\Delta_S^{2a})=\nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{2a-1})$
via `lintegral_withDensity_eq_lintegral_mul` (for $\lvert k(x,x)\rvert$ and then by linearity for real
and imaginary parts) gives the diagonal kernel formula; for $k(x,y)=g(x)\overline{h(y)}$ at $a=1/2$,
$k_{1/2}(x,x)=\Delta_S(x)g(x)\overline{h(x)}=c_S\,U_S(g)(x)\overline{U_S(h)(x)}$.

(3) Assume $S\ne\emptyset$. The equivalence *(i)* $\iff$ *(iv)* (with $c=c_S$) is Theorem
15.3(3)(ii). Clearly *(iv)* $\implies$ *(ii)* and *(iii)* by part (2). If *(ii)* holds—say
$\lVert U_{S,a}g\rVert^2_{L^2(\mu_S)}=\kappa\lVert g\rVert^2_{L^2(\nu_S)}$ for some $\kappa>0$ and all
$g\in L^2(K_S,\nu_S)$—testing on $g=\mathbf 1_B$ for all relatively compact Borel $B\subseteq K_S^\times$
gives $\int_B\Delta_S^{2a}\,d\mu_S=\kappa c_S\,\nu_S(B)$, hence *(i)* with $c=\kappa c_S$, forcing
$a=1/2$ and $\kappa=1$. If *(iii)* holds, substituting $y=tx$ gives
$\lVert T_t^{(a)}g\rVert^2_{L^2(\nu_S)}=\Delta_S(t)^{2a-1}\lVert g\rVert^2_{L^2(\nu_S)}$ for a nonzero
$g\in L^2(K_S,\nu_S)$, so $\Delta_S(t)^{2a-1}=1$ for all $t\in K_S^\times$; choosing $v_0\in S$ and
$t$ non-unit at $v_0$ as in Theorem 15.3(3) forces $a=1/2$. Finally, when $S=\emptyset$, $K_\emptyset^\times=\{1\}$
has $\Delta_\emptyset(1)=1$ and $c_\emptyset=1$, making *(i)*–*(iii)* trivial identities $1=1$ for
every $a\in\mathbb R$. $\square$

**Remark 1 (operator dichotomy: why `withDensity` and `compMeasurePreserving` live on orthogonal
legs of the diagram).** Lemma 15.5d(3) and Theorem 15.6(2) resolve the confusion flagged in the
audit of Lemma 15.3d by separating the horizontal group action from the vertical change of measure:
$$\begin{array}{ccc}
L^2(K_S,\nu_S) & \xrightarrow{\quad T_t^{(1/2)}\;:\;g(x)\mapsto\Delta_S(t)^{1/2}g(tx)\quad} & L^2(K_S,\nu_S) \\[6pt]
\Big\downarrow{\scriptstyle U_S = M_{(c_S\Delta_S^{-1})^{-1/2}}} & & \Big\downarrow{\scriptstyle U_S = M_{(c_S\Delta_S^{-1})^{-1/2}}} \\[6pt]
L^2(K_S^\times,\mu_S) & \xrightarrow[\quad C_{\tau_t}\;=\;\mathrm{compMeasurePreserving}(\tau_t)\quad]{} & L^2(K_S^\times,\mu_S)
\end{array}$$
The bottom horizontal arrow $C_{\tau_t}$ is a pure precomposition (`Lp.compMeasurePreserving`),
unitary with **no** Jacobian factor because $\tau_t$ preserves $\mu_S$. The vertical arrows $U_S$ do
**not** move points of $K_S^\times$ at all—they change the measure from $\nu_S$ to
$\mu_S=c_S\Delta_S^{-1}\nu_S$ via `withDensity` multiplication $g\mapsto c_S^{-1/2}\Delta_S^{1/2}g$.
The top horizontal arrow $T_t^{(1/2)}$ acquires its half-Jacobian $\Delta_S(t)^{1/2}$ precisely by
going down via $U_S$, precomposing via $C_{\tau_t}$, and coming back up via $U_S^{-1}$
(`[Bourbaki2004]`, Ch. VII, §1; `[Weil1967]`, Ch. I, §2).

**Remark 2 (why Masullo's (12.4.1.17) carries $c_S$ while Theorem 12.5.1.1 divides it out).** In
Masullo's §12.4.1 (p. 518), the kernel $k_{S,\varphi}(x,y)$ is formed directly from unnormalized
local Schwartz/Bruhat test functions twisted by $\lvert x\rvert_{F,S}^a\lvert y\rvert_{F,S}^a$,
without inserting $c_S^{-1/2}$ into each variable; hence at $a=1/2$ the diagonal integral retains an
overall factor of $c_S$ in (12.4.1.17) and (12.4.1.23) (verified at $c_{\{5\}}=5/4$ in Example 2),
which is subsequently cancelled in Theorem 12.5.1.1 (p. 519) when the finite-place orbital terms are
divided by $\mu_v(\mathcal O_{F_v}^\times)$ `[Paper; Masullo pp. 518–519]`. As in §15.4.3.1 Remark 1,
closing this finite-$S$ measure identity proves **nothing** toward Masullo's global claims: diagonal
kernel smoothing (`pp. 15, 517`), the omitted §12.3 (`p. 514`), the Chapter 10 positive-width strip
nuclearity gap (`p. 451`), $\alpha$-independence of the strip trace in Theorem 12.5.1.1 (`p. 519`),
and the unwritten Chapter 13 (`pp. 521–522`) remain untouched `[Open]`.

**Remark 3 (summary of §15.4.3.1 audit repairs).** Relative to the initial text of §15.4.3.1, five
fixes are now in place across §§15.4.3.1–15.4.3.2: *(a)* $c_S$ is restored to the right-hand side of
the product diagonal integral Theorem 15.3(3)(i) as well as $c=c_S$ in Theorem 15.3(3)(ii) (repaired
on $U_0=\mathbb Z_5^\times$ in Example 2); *(b)* the hypothesis $S\ne\emptyset$ is added to Theorem
15.3(3)(ii) and Theorem 15.6(3), with the $S=\emptyset$ degeneracy explicitly exhibited; *(c)* the
erroneous `MeasurePreserving`-identity explanation in Lemma 15.3d is replaced by Lemma 15.5d's
`withDensity` $L^2$ construction and refuted on $[1,4]\subset\mathbb R_{>0}$ and on the complex
annulus $A\subset\mathbb C^\times$; *(d)* the line range of `addHaar_image_linearMap` at the pin is
corrected from `:310–319` to `:297–306` and its full R3 production proof (with
`map_linearMap_addHaar_eq_smul_addHaar` and $\det_{\mathbb R}(\ell_z)=\lvert z\rvert^2$) is supplied
in Lemmas 15.5a–15.5c; and *(e)* $a\ne 0$ (versus $\log 4$ at $a=0$) in §15.4.3.1's opening
integral, "locally finite Borel measure on $K$" in Lemma 15.3b(2), and "dilation-covariant" in
§15.4.3.1 Remark 1 are stated precisely.

**Source map for this subsection.** Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`.

| File and lines at the pin | Declaration | Role here | Reading |
|---|---|---|---|
| `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:117–121, 137–197, 218–306` | `addHaarMeasure_eq_volume_pi`, `addHaar_eq_zero_of_disjoint_translates_aux`, `addHaar_eq_zero_of_disjoint_translates`, `addHaar_submodule`, `map_linearMap_addHaar_pi_eq_smul_addHaar`, `map_linearMap_addHaar_eq_smul_addHaar`, `addHaar_preimage_linearMap`, `addHaar_preimage_continuousLinearEquiv`, `addHaar_image_linearMap` | Lemmas 15.5a(1) and 15.5b(1)–(2): proper subspaces are Haar-null; pushforward, preimage, and image Haar scaling by $\lvert\det f\rvert^{\pm 1}$ | R3 |
| `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean:364–444` | `Real.smul_map_diagonal_volume_pi`, `Real.volume_preserving_transvectionStruct`, `Real.map_matrix_volume_pi_eq_smul_volume_pi`, `Real.map_linearMap_volume_pi_eq_smul_volume_pi` | Lemma 15.5a(2)–(4): diagonal stretches, Fubini slice invariance of transvections, and matrix/linear scaling on $\iota\to\mathbb R$ | R3 |
| `Mathlib/LinearAlgebra/Matrix/Transvection.lean:145–215, 337–465, 502–558, 676–743` | `TransvectionStruct`, `TransvectionStruct.det`, `listTransvecCol`, `listTransvecRow`, `isTwoBlockDiagonal_listTransvecCol_mul_mul_listTransvecRow`, `exists_list_transvec_mul_diagonal_mul_list_transvec`, `diagonal_transvection_induction_of_det_ne_zero` | Definition 15.5(1), Example 1 pivot factorization, and Lemma 15.5a(4) Gauss-transvection induction | R3 |
| `Mathlib/LinearAlgebra/Determinant.lean:306–321, 369–375, 508–510, 569–575` | `LinearMap.det_conj`, `LinearMap.range_lt_top_of_det_eq_zero`, `LinearEquiv.det_coe_symm`, `LinearMap.equivOfDetNeZero` | Lemma 15.5b: similarity invariance, proper range when $\det f=0$, inverse determinant, and upgrade to equivalence when $\det f\ne 0$ | R3 |
| `Mathlib/LinearAlgebra/Complex/Module.lean:144–165` · `Complex/FiniteDimensional.lean:31–32` · `Complex/Determinant.lean:26–28` | `Complex.basisOneI`, `coe_basisOneI_repr`, `coe_basisOneI`, `finrank_real_complex`, `Complex.det_conjAe` | Example 1 and Lemma 15.5c: ordered $\mathbb R$-basis $(1,i)$ of $\mathbb C$, $\dim_{\mathbb R}\mathbb C=2$, and $2\times 2$ determinant template | R3 |
| `Mathlib/RingTheory/Norm/Defs.lean:61–64, 82–84` · `Data/Complex/Basic.lean:509–518` · `Analysis/Complex/Norm.lean:29–32, 147–150` | `Algebra.norm`, `Algebra.norm_apply`, `Algebra.norm_eq_matrix_det`, `Complex.normSq`, `Complex.normSq_eq_norm_sq` | Lemma 15.5c: $\det_{\mathbb R}(\ell_z)=\operatorname{Nm}_{\mathbb C/\mathbb R}(z)$ and $u^2+v^2=\operatorname{normSq}(z)=\lvert z\rvert^2$ | R3 |
| `Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean:53–62` · `Haar/InnerProductSpace.lean:82–96` | `Complex.volume_preserving_equiv_pi`, `Complex.volume_preserving_equiv_real_prod`, `OrthonormalBasis.volume_parallelepiped` | Lemma 15.5c: identification of planar Lebesgue measure $\nu_{\mathbb C}$ on $\mathbb C$ with product volume | R3 |
| `Mathlib/MeasureTheory/Measure/WithDensity.lean:245–300, 322–355, 398–449, 538–572, 589–596` | `ae_withDensity_iff'`, `lintegral_withDensity_eq_lintegral_mul₀'`, `withDensity_mul₀`, `withDensity_inv_same₀`, `withDensity_ae_eq` | Lemma 15.5d(1) and Theorem 15.6(2): null-set equivalence, Lebesgue density multiplication, density composition, and inverse weight | R3 |
| `Mathlib/MeasureTheory/Integral/LebesgueNormedSpace.lean:22–49` · `Function/L1Space/Integrable.lean:864–914` | `aemeasurable_withDensity_iff`, `L1.withDensitySMulLI`, `L1.withDensitySMulLI_apply` | Lemma 15.5d(1): strong measurability under positive density and Mathlib's $L^1$ multiplication-isometry prototype | R3 |
| `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:547–636` · `Function/AEEqFun.lean:280–318` | `AEEqFun.compMeasurePreserving`, `Lp.compMeasurePreserving`, `Lp.isometry_compMeasurePreserving`, `Lp.compMeasurePreserving_id`, `Lp.compMeasurePreservingₗᵢ` | Definition 15.5(2) and Lemma 15.5d(2)–(3): precomposition operator under `MeasurePreserving` and its conjugation by $U_{1/2}$ | R3 |
| Inherited from §15.4.3.1 | `distribHaarChar`, `Real.map_volume_mul_left`, `IsHaarMeasure.nullSingletonClass`, `IsHaarMeasure.isInvInvariant_of_regular`, `ProperSpace ℚ_[p]`, Lemmas 15.3a(1),(3), 15.3b, 15.3c, Proposition 15.4 | Single-field $\mathbb R$ and non-archimedean modulus/shells, zero removal, multiplicative and inversion invariance, 1-field Fourier scaling | Inherited (audited in §15.4.3.1) |
| Retained named inputs (unread / `[Open]`) | `addHaarMeasure_unique` (`Haar/Unique.lean`), `Measure.pi_eq` / `lintegral_eq_of_lmarginal_eq` (`Constructions/Pi.lean`, `Integral/Lebesgue/Marginal.lean`), Haar instance on $\mathbb Q_p$ (absent at pin), Masullo diagonal smoothing (`pp. 15, 517`) & Ch. 10/12/13 strip-trace steps (`pp. 451, 514, 519, 521–522`) | Measure-uniqueness and Fubini-marginal foundations `[Lean]`; $\mathbb Q_5$ measure normalization `[Expository]`; Masullo global trace steps `[Paper]` / `[Open]` | Statement / named boundary |

### 15.4.4 Axis IV: Arithmetic geometry versus nuclear functional analysis — and the opposite fate of $\mathbb F_q(X)$

Perhaps the single deepest conceptual contrast in the entire book is how the **global function-field
analogy $\mathbb F_q(X)$** behaves in the two routes (`Chapter 6` versus `Section 14.5.1`) [Expository]:

**Proposition 15.2 (Opposite behavior of the function-field case $\mathbb F_q(X)$).**

1. **In Alpöge–Claude (`remark.pdf` p. 1, p. 3 items 1–5 [Paper]; Chapters 6–8):** *$\mathbb F_q(X)$ is
   the **guiding model where everything works transparently**! Over $\mathbb F_q(X)$, Frobenius
   $u \mapsto u^q$ and Hasse–Schmidt derivations $D^{(k)}$ (`[HasseSchmidt1937]`, `[Stepanov1969]`,
   `[Bombieri1973]`) exist globally, giving high-order vanishing at $\mathbb F_q$-points in five pages
   (Theorem 6.2). All 17.37 million lines of the Lean archive exist to **simulate that function-field
   proof over $\mathbb Z$**, replacing $D^{(k)}$ by iterated unitary theta lifts (`P7`), Frobenius
   vanishing by height-$2$ supersingular formal groups $D^p \equiv 0 \pmod p$ at inert primes (`P8`),
   and $\sum \operatorname{ord}_P \le \deg$ by Bost's Arakelov slope inequality (`P9`)!*
2. **In Masullo (`§1.7.1` pp. 33–37 and `§14.2` pp. 534–536 [Paper]):** *$\mathbb F_q(X)$ is the case
   where **Masullo's method provably fails**! Because $\mathbb F_q(X)$ has **no archimedean places**
   ($C_F / C_F^1 \cong \mathbb Z$ is discrete rather than $\mathbb R_{>0}$, destroying smooth Lebesgue
   differentiation along $\log\lvert g \rvert_F$) and **all non-Archimedean norms $\lvert k(x) \rvert = q^{\deg x}$
   are powers of $q$** (destroying the $\mathbb Q$-linear independence of $\{\log p\}_{p\text{ prime}}$
   used in `Theorem 7.1.3.2`, p. 324!), infinitely many local Euler factors collide at the same poles
   modulo $\frac{2\pi i}{\log q}$, invalidating both `Theorem 7.1.3.2` and the orbital nuclearity bound
   `Theorem 11.2.2.1`!* [Paper; Masullo pp. 33–37, 534–536]

Think about what Proposition 15.2 means mathematically: **Alpöge succeeds where $\mathbb Q$ looks most
like $\mathbb F_q(X)$ (local $p$-adic Frobenius congruence $D^p \equiv 0 \pmod p$ at supersingular
primes), whereas Masullo builds on the one structural feature that $\mathbb Q$ possesses and
$\mathbb F_q(X)$ lacks — the continuum $\mathbb R_{>0}$ and the $\mathbb Q$-linear independence of
$\log 2, \log 3, \log 5, \dots$!**

### 15.4.5 Axis V: The verification mirror image

Finally, look at the epistemic mirror image between the two works as of `2026-11-22`:

- **Alpöge–Claude:** Every logical step from the three standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`) to Mathlib's `RiemannHypothesis` has been checked at the level of primitive dependent
  type theory by Lean's kernel, `lean4lean`, `nanoda`, `con-leche --compare`, and `con-ron --compare`,
  and reproduced byte-for-byte in a no-network bubblewrap sandbox (`61,570,595,788` bytes, sha256
  `5ea74b91…244e`) `[Community]`. Yet **why** the deep internal modules of `VwinOfRow` (`157,603`
  modules), `EveryCharacterOfLiteratureOfVWin` (`151,285` modules), and `RowSrc` (`66,167` modules) work
  — and which classical theorems inside `GlobalTheory.Published.*` were proved only in specialized cases
  — is only now being excavated by human readers (including Chapters 1–13 of this book!).
- **Masullo:** Every definition, heuristic motivation, and classical inspiration (`[Tate1967]`,
  `[Deninger1993]`, `[Connes1999]`, `[Meyer2005]`) is laid out in 940 pages of human prose so clearly
  that readers could pinpoint the exact line on **p. 444** and **p. 451** where the spectral nuclearity
  proof fails within three hours of publication `[Community]`! Yet until the positive-width strip gap in
  Chapter 10, the omitted Section 12.3, and the unwritten Chapter 13 are either repaired or shown
  irrecoverable, **the manuscript does not contain a complete proof of RH or GRH** `[Open]`.

---

## 15.5 Master comparison tables and cross-fertilization

### 15.5.1 Five-axis structural comparison matrix

| Structural axis | Alpöge–Claude Lean archive (`P0`–`P18`) | Masullo *The Music of the Primes* (`Chs. 1–14`) |
|---|---|---|
| **I. Target scope** | $\zeta(s)$ and all Dirichlet $L(s, \chi)$ over $\mathbb Q$ (`src/Main.lean:4–12`) + abelian $\zeta_K(s)$ via Kronecker–Weber; non-abelian ERH **not** covered (`[Lean, read]`). | Intended: all unitary Hecke $L(s, \chi)$ over **all** number fields $F$ (`p. 6`), including all Dedekind $\zeta_K(s)$; Ch. 13 (`pp. 521–522`) unwritten (`[Paper]`, `[Open]`). |
| **II. Zeros $\leftrightarrow$ primes bridge** | **One-sided** Riesz prime sum $G_m(x) \le x^{1/2+O(\varepsilon)}$ on sparse windows $[Y, Y^{1+\delta}]$ + Landau/Pólya real Laplace monotonicity (`P5`, `landau_window`); **no** sum over high zeros! | **Two-sided** convolution trace on $C_F$ for $\varphi \in D(C_F)$ with $\varphi(C_F^1) = 0$ (`Thm. 12.5.1.1`, `p. 519`); avoids Weil positivity (`§1.4.6`, `p. 30`) and requires summing over all strip zeros. |
| **III. Origin of exponent $\frac{1}{2}$** | Discrete **AM–GM balance** $\min_m (x/m + m\,x^{O(\varepsilon)}) \asymp x^{1/2+O(\varepsilon)}$ at chain length $m \asymp \sqrt{x}$ (`core_gm` / `proposition_size_bound`, `P6`–`P7`). | Continuous diagonal Haar-measure matching $c_S\lvert x \rvert_{F,S}^{2a-1} = c_S \iff a = \frac{1}{2}$ for $S\ne\emptyset$ (`p. 16, p. 518`; proved as Theorems 15.3 and 15.6 in §§15.4.3.1–15.4.3.2) + asserted **$\alpha$-independence** of strip trace on $W_{[-\alpha,\alpha]}^{s,2}\mathcal H_F$ (`p. 519`, `[Open]`). |
| **IV. Core engine & $\mathbb F_q(X)$** | **Arithmetic-geometric / automorphic:** definite $U(n)$ theta chains (`P17`), supersingular $p$-adic divisibility (`P8`), Bost slopes (`P9`), Rallis/Gram decay (`P10`), GMA congruences & Iwasawa/$U(3)$ $\mathrm{Ш}^1$ (`P11`–`P12`), $\mathrm{GL}_a$ Galois reps (`P14`–`P16`). **Inspired directly by $\mathbb F_q(X)$!** | **Topological / functional-analytic on $\mathrm{GL}_1$:** periodic Schauder bases (`Chs. 4, 7`), Weil $PV_v$ operators (`Ch. 5`), nuclear locally convex duals (`App. C`), Hardy–Sobolev strip spaces (`Ch. 9`), divisorial shells (`Ch. 11`). **Provably fails over $\mathbb F_q(X)$ (`§14.2`, `pp. 534–536`)!** |
| **V. Verification state (`2026-11-22`)** | **175,187 `.lean` files, 0 `sorry`s, 3 standard axioms**; accepted by `leanchecker`, `nanoda`, `con-leche --compare`, `con-ron --compare`, `lean4lean`; sandboxed rebuild export byte-identical (`[Community]`). Deep ~146k-module proof bodies largely unread by humans (`[Open]`). | **940-page human draft**; Wave 1 (`Chs. 2–4, 9`) mostly formalized in `mccorvie/riemann-masullo`, Wave 2 (`Thm. 5.2.1.1`, `§B.4`) flagged issues `[Community]`; **Ch. 10 `p. 451`/`p. 463` strip nuclearity gap, omitted `§12.3` (`p. 514`), and unwritten Ch. 13 (`pp. 521–522`) remain `[Open]`.** |

### 15.5.2 Block-by-block dictionary between `P0`–`P18` and Masullo's chapters

| Lean node (`notes/proof-map.md`) | Role in Alpöge–Claude archive | Nearest counterpart in Masullo's *The Music of the Primes* |
|---|---|---|
| `P0` Target statements (`src/Main.lean`, `src/Statements.lean`) | Mathlib `RiemannHypothesis` + 4 Dirichlet GRH theorems `[Lean, read]` | Placeholder `§13.3` (`pp. 521–522`), aiming at all unitary Hecke $L(s, \chi)$ `[Paper]` / `[Open]` |
| `P1`, `P3` Functional equations & Euler factors | Reduces 5 theorems to `EveryCharacter` on $\Re s > \frac{1}{2}$ `[Lean, read]` | `Ch. 3` (`pp. 117–154`, Tate's thesis) and intended `§13.1` — **shared classical foundation** |
| `P4`, `P5` Landau-window zero-free engine | One-sided prime-sum bound on $[Y, Y^{1+\delta}]$ $\implies$ zero-free (`landau_window`) `[Lean, read]` | `App. B.4` (`pp. 606–625`, idelic explicit formulas) and `§1.4.2–1.4.5` (`pp. 28–30`) — **same role, opposite mechanism** |
| `P13` Auxiliary prime pairs $(q, d)$ & host $E$ | Zero-density + mean-square + Siegel sieve supplying CM host fields `[Lean, read]` / `[Lean]` | `App. B.1` (convexity, `pp. 588–591`) & `App. B.6` (zero-free regions, `pp. 636–643`) as classical analytic background only |
| `P6`, `P7` `core_gm` & `SizeData₂` ($m \asymp \sqrt{x}$) | Finite Fourier projection + 4-term chain bracket balancing $x/m + m$ `[Lean, read]` | **None** ($\frac{1}{2}$ enters via $\lvert \cdot \rvert_F^{1/2}$ in `§1.2.1` `p. 13` & `§12.4.1` `p. 518`) |
| `P8`–`P10` Inert divisibility, Bost slopes, `LinkS`/`LinkG` | Supersingular formal groups + Arakelov lattice slopes + Rallis/Gram decay `[Lean, read]` / `[Lean]` | **None** (Masullo has no CM reductions, Arakelov lattices, or unitary periods) |
| `P11`–`P12` GMA congruences & `VWin` on $\mathrm{Ш}^1$ | Bounds Hecke congruence loss via Sinnott/Ferrero–Washington + $U(3)$ patching `[Lean, read]` / `[Lean]` | **None** (Masullo uses no $\ell$-adic Galois cohomology or Iwasawa theory) |
| `P14`–`P17` $\mathrm{GL}_a$ Galois reps, local Langlands, Green, `HypsAlt` | Automorphic/Galois foundations for high-rank unitary theta chains `[Lean, read]` / `[Lean]` | `Ch. 3` is the $\mathrm{GL}_1$ local Tate base case; `Ch. 2` "adelic $\theta$-functions" (`p. 77`) are $\mathrm{GL}_1$ orbit sums, **not** oscillator kernels |
| `P18` Literature layer (`OpenLiteratureStatements`) | 257 named classical theorems stated as `Prop`s and proved in Lean `[Lean, read]` / `[Open]` | `Apps. A–E` (`pp. 537–932`) cite classical monographs and prove bespoke locally convex / analytic lemmas |
| *(No Lean counterpart)* | *(Not used in Alpöge's archive)* | `Chs. 4–12` (`pp. 155–520`): periodic Schauder bases, Hardy–Sobolev strip spaces $W_I^{s,2}(C_F)$, spectral & shell trace formulas `[Paper]` / `[Open]` |

### 15.5.3 What each project teaches the other

Studying both works side by side leaves two lasting lessons for working mathematicians and formalizers
[Expository]:

1. **Why Alpöge's avoidance of global spectral expansions was decisive:** By working with a **compactly
   supported** Riesz weight $(x/n - 1)_+$ on **finite windows** $[Y, Y^{1+\delta}]$ and extracting
   zero-freeness via Landau's real-axis pole monotonicity (`P5`), Alpöge's proof never has to invert or
   biorthogonalize operators at close vertical pairs of critical-line zeros! Where Masullo's Chapter 10
   is blocked by $\Delta\gamma \to 0$ on $\Re s = \frac{1}{2}$, Alpöge's analytic endgame (`P3`–`P5`)
   fits into fewer than 150 small Lean modules that any graduate student can check by hand (Chapters 2–3).
2. **Why Masullo's prose discipline and `mccorvie/riemann-masullo`'s wave model matter for Alpöge's archive:**
   Conversely, Masullo's explicit statement of every intermediate topological structure theorem (`Chs. 2–9`)
   allowed human readers and Lean formalizers (`mccorvie/riemann-masullo`) to isolate both true reusable
   foundations (Wave 1's ~3,950 proved theorems on adeles, Haar measures, and Hardy–Sobolev spaces) and
   exact broken steps (`Terminology 10.2.1.2(2)` on p. 444, `Theorem 5.2.1.1` on p. 230) within 48 hours.
   Applying that same wave-by-wave human digestion and clean interface extraction to Alpöge's 175,187
   Lean files is the central task now facing the mathematical community — and the subject of **Chapters 16 and 18**!

**Summary of the chapter.** Tracing $\chi_{-4} \bmod 4$ through both routes and comparing them across
five structural axes shows that Alpöge–Claude and Masullo share only Euler products, Tate/Dirichlet
functional equations, and the classical duality between prime powers and zeros. Alpöge proves GRH for
Dirichlet $L$-functions over $\mathbb Q$ (`src/Main.lean:4–12`) [Lean, read] by combining a one-sided
Landau-window prime-sum criterion (`P5`) with an $\mathbb F_q(X)$-inspired arithmetic-geometric engine
of $m \asymp \sqrt{x}$ unitary theta lifts, supersingular $p$-adic divisibility, Bost Arakelov slopes,
and Iwasawa/$U(3)$ bounds on $\mathrm{Ш}^1$ (`P6`–`P17`) — kernel-checked across 175,187 modules
`[Community]` while largely unread in its deep layers `[Open]`. Masullo aims at all unitary Hecke
$L$-functions over all number fields (`p. 6`) via two-sided convolution traces on strip-weighted
Hardy–Sobolev quotients $W_I^{s,2}\mathcal H_F$ over $C_F$ (`Chs. 9–12`, failing over $\mathbb F_q(X)$
in `§14.2` pp. 534–536) — transparent to human readers `[Paper]` but stalled at the Chapter 10
biorthogonal-bound gap (`pp. 444, 451, 463`), omitted `§12.3` (`p. 514`), and unwritten Chapter 13
(`pp. 521–522`) `[Open]`.
