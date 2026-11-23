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
     converts multiplicative Haar measure $d\mu_S(x) = \lvert x \rvert_{F, S}^{-1} d\nu_S(x)$ on the
     diagonal $x = y$ into $\lvert x \rvert_{F, S}^{2a - 1} d\nu_S(x)$, which matches additive Fourier
     measure $d\nu_S(x)$ **if and only if $2a - 1 = 0 \iff a = \frac{1}{2}$** (`p. 16, p. 518`). (Note:
     this alone only identifies $\Re s = \frac{1}{2}$ as the **functional-equation symmetry axis**,
     which is classical!)
  2. *Concentration on that axis:* Zeros are forced onto $\Re s = \frac{1}{2}$ **only if** the trace on
     $W_{[-\alpha, \alpha]}^{s,2}\mathcal H_F$ is independent of $\alpha > 0$ (`Theorem 12.5.1.1`, p. 519)
     — the exact step currently blocked by the `[Open]` issues of Chapter 14!

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
| **III. Origin of exponent $\frac{1}{2}$** | Discrete **AM–GM balance** $\min_m (x/m + m\,x^{O(\varepsilon)}) \asymp x^{1/2+O(\varepsilon)}$ at chain length $m \asymp \sqrt{x}$ (`core_gm` / `proposition_size_bound`, `P6`–`P7`). | Continuous diagonal Haar-measure matching $\lvert x \rvert_{F,S}^{2a-1} = 1 \iff a = \frac{1}{2}$ (`p. 16, p. 518`) + asserted **$\alpha$-independence** of strip trace on $W_{[-\alpha,\alpha]}^{s,2}\mathcal H_F$ (`p. 519`, `[Open]`). |
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
