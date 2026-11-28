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
     four worked hand calculations. Subsection 15.4.3.3 reads the uniqueness of Haar measure used
     by both and identifies $c_S$ as a ratio of two Haar measures, Theorem 15.8 and Corollary 15.9.)
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
   the pushed-forward measure is again a Haar measure and is a positive multiple of $\nu$ (Theorem
   15.8(3),(6) in §15.4.3.3). The
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
measure (Theorem 15.8(3) in §15.4.3.3); applying inversion twice gives $c^2\mu=\mu$, hence $c=1$. This is the Lean proof of
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

The local measure and its normalization are proved in [§15.4.3.11 Haar measure on p-adic balls and shells](#154311-haar-measure-on-p-adic-balls-and-shells), over the Cauchy-completed field and discrete valuation constructed in [§15.4.3.12 Completing the rationals at a prime](#154312-completing-the-rationals-at-a-prime).

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
| `Mathlib/MeasureTheory/Measure/Haar/Unique.lean:277, 1063–1073` | `haarScalarFactor`, `addHaarScalarFactor_smul_congr'` | supplies independence of $\nu$ in Definition 15.2(1) | statement level (R3 in §15.4.3.3) |
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
`isAddLeftInvariant_eq_smul_of_regular` (`Haar/Unique.lean`; read in §15.4.3.3); the Fourier transform on a general
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
and `addHaarMeasure_eq_volume_pi`, `:117–121`; Lemma 15.7f(2)–(3) in §15.4.3.3), $\mu=\mu([0,1]^\iota)\,\mathrm{vol}$. Pushing forward
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
   $\rho$-almost everywhere. Whenever $w$ is not $\rho$-a.e. equal to $1$, the identity does not
   satisfy the `MeasurePreserving` hypothesis, so this isometric precomposition interface does not
   apply to it. The precomposition $C_{\mathrm{id}}:[v]_\rho\mapsto[v]_{\rho_w}$ can still be a
   bounded operator, but it is not an isometry: for $X=[0,1]$, $\rho=dx$ and $w=4$, it is a bounded
   invertible operator $L^2(\rho)\to L^2(4\rho)$ of norm $2$ whose inverse has norm $1/2$. When $w=1$
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
gives the identity operator. In the example, $\lVert[v]_{4\rho}\rVert^2_{L^2(4\rho)}=4\lVert[v]_\rho\rVert^2_{L^2(\rho)}$,
which gives the two norms $2$ and $1/2$.

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
     $k(x,y)=g(x)\overline{h(y)}$ with $g,h\in L^2(K_S,\nu_S)$ at $a=1/2$, and with the inner
     product conjugate-linear in the first variable as in Mathlib (Corollary 15.9(5) in §15.4.3.3),
     $$\int_{K_S^\times} k_{1/2}(x,x)\,d\mu_S(x)
       = c_S\,\langle U_S h, U_S g\rangle_{L^2(\mu_S)}
       = c_S\,\langle h, g\rangle_{L^2(\nu_S)},$$
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
That this normalization determines $\mu_S$ among the Haar measures on $K_S^\times$, and that $c_S$ is
the ratio of two such measures, is Theorem 15.8(5) and Corollary 15.9(6) in §15.4.3.3.

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
$k_{1/2}(x,x)=\Delta_S(x)g(x)\overline{h(x)}=c_S\,\overline{U_S(h)(x)}\,U_S(g)(x)$, whose
$\mu_S$-integral is $c_S\langle U_Sh,U_Sg\rangle_{L^2(\mu_S)}$ because Mathlib's $L^2$ inner product
is $\langle u,v\rangle=\int\overline u\,v$ (`L2.inner_def`, `RCLike.inner_apply`).

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
| Retained named inputs (unread / `[Open]`) | `Measure.pi_eq` / `lintegral_eq_of_lmarginal_eq` (`Constructions/Pi.lean`, `Integral/Marginal.lean`), Haar instance on $\mathbb Q_p$ (absent at pin), Masullo diagonal smoothing (`pp. 15, 517`) & Ch. 10/12/13 strip-trace steps (`pp. 451, 514, 519, 521–522`); `addHaarMeasure_unique` is in `Haar/Basic.lean:670–676`, not `Haar/Unique.lean`, and is read in §15.4.3.3 | Measure-uniqueness and Fubini-marginal foundations [read in §15.4.3.5](#15435-finite-place-products-from-rectangles-and-marginals); $\mathbb Q_5$ measure normalization `[Expository]`; Masullo global trace steps `[Paper]` / `[Open]` | Statement / named boundary |

#### 15.4.3.3 Uniqueness of Haar measure: proportionality, normalization and the constant in the half-density transport

> **Reading boundary.** This subsection explains existing measure theory and does no new RH
> research. `[Lean, read]` refers to proof bodies read at the archive's Mathlib pin
> `0df444a360eaa60ab8c11dca51a86af692955474` (archive bundle SHA-256
> `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`). Reading library proofs and
> building this book is not a Lean kernel verification. Unlike the declarations of §15.4.3.1, the
> uniqueness theorems read here are also called by archive files, for instance
> `isMulLeftInvariant_eq_smul` at
> `src/Formalism/HermitianCurvature/HermitianCurvatureProofs/HaarUniquenessConjugation.lean:154` and
> `addHaarMeasure_unique` at
> `src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FundamentalDomainPiBasis.lean:44–45`.
> Those call sites are not followed, and nothing below says whether they lie on the import path of
> `src/Main.lean`. Inherited without re-proof: §15.4.3.1 (values of the modulus, zero removal,
> invariance of $\Delta_K^{-1}\nu$, Theorem 15.3) and §15.4.3.2 (Lemmas 15.5a–d, Theorem 15.6).
> Kept at statement level and named where used: the construction of Haar measure from Haar
> content, Urysohn's lemma, Halmos's theorem that a Haar measure is completion regular, Fubini for
> compactly supported continuous functions, Tonelli and the box criterion for product measures,
> and the regularity and $\sigma$-finiteness instances listed in the source map. Masullo's diagonal
> smoothing (pp. 15, 517) and the strip-trace and nuclearity steps (pp. 451, 514, 519, 521–522)
> remain `[Paper]`/`[Open]`.

**Motivation.** Subsections 15.4.3.1–15.4.3.2 use the uniqueness of Haar measure five times
without reading its proof:

1. Definition 15.2(1) says that the pushforward of $\nu$ under $x\mapsto tx$ "is a positive
   multiple of $\nu$" and that the multiple "does not depend on $\nu$". In Mathlib the identity
   $\nu(tS)=\Delta_K(t)\,\nu(S)$ is `distribHaarChar_mul` (`DistribChar.lean:83–86`), which
   rewrites with `isAddLeftInvariant_eq_smul_of_regular` (`Haar/Unique.lean:905–914`). The
   independence of $\nu$ is `addHaarScalarFactor_smul_congr'` (`Haar/Unique.lean:1069–1072`),
   called at `DistribChar.lean:63–66`.
2. Lemma 15.3c obtains inversion invariance from `isInvInvariant_of_regular`
   (`Haar/Unique.lean:978–999`), which calls `isMulLeftInvariant_eq_smul_of_regular` for the
   reflected measure.
3. The first step of Lemma 15.5b(1), `map_linearMap_addHaar_pi_eq_smul_addHaar`
   (`EqHaar.lean:218–226`), writes an arbitrary additive Haar measure on $\iota\to\mathbb R$ as
   $\mu([0,1]^\iota)\cdot\mathrm{vol}$ by `addHaarMeasure_unique`. This is the additive form of
   `haarMeasure_unique` in `Haar/Basic.lean:670–676`, not a declaration of `Haar/Unique.lean` as
   the source map of §15.4.3.2 said, and it is proved by a different method.
4. The normalization of product Lebesgue measure, `addHaarMeasure_eq_volume_pi`
   (`EqHaar.lean:117–121`), is the same `addHaarMeasure_unique` applied to `volume` on
   $\iota\to\mathbb R$.
5. Theorem 15.6(1) calls $\mu_S=c_S\Delta_S^{-1}\nu_S$ "normalized on $\prod_{v\in S_f}\mathcal O_v^\times$",
   and Masullo's (12.4.1.17) presents $c_S$ as the constant relating two normalizations
   [Paper; Masullo p. 518]. That one normalization fixes a Haar measure, and that the ratio of two
   Haar measures is a single number, is uniqueness on the locally compact group $K_S^\times$.

The pinned library proves uniqueness twice, by different methods and under different
hypotheses, and §15.4.3 uses both. Route T (test functions; `Haar/Unique.lean`, Sébastien
Gouëzel, 2023) needs local compactness to compare integrals, and regularity of both measures to
compare measures. Items 1–2 use it. Route P (products; `Group/Prod.lean` and `Haar/Basic.lean`,
Floris van Doorn, 2020–2021, after Halmos 1950, §§59–60) needs $\sigma$-finiteness and a measurable
multiplication $G\times G\to G$, which second countability supplies. Items 3–4 use it. This
subsection reads both routes (Lemmas 15.7a–f), states the theorem with the hypotheses each
consumer uses (Theorem 15.8), shows by examples what each hypothesis does (Example 3), and
returns the result to the half-density transport of Theorem 15.6 (Corollary 15.9), where Masullo's
$c_S$ appears as one such ratio.

**Example 1 (real-linear coordinates on $\mathbb R^2=\mathbb C$: one constant, three
measurements).** Let $\nu_{\mathbb C}$ be planar Lebesgue measure on $\mathbb C$ in the basis
$(1,i)$, as in §15.4.3.2, and let $Q=\{x+iy:0\le x,y\le 1\}$, so $\nu_{\mathbb C}(Q)=1$. Put
$b_1=1+2i$ and $b_2=-2+i$, the images of $1$ and $i$ under $\ell_{1+2i}$, and give $w\in\mathbb C$
the real-linear coordinates $(s,t)$ defined by $w=sb_1+tb_2=(1+2i)(s+it)$. Mathlib's coordinate
measure for this basis is `b.addHaar`, the Haar measure normalized on the parallelogram
$P_b=\{sb_1+tb_2:0\le s,t\le1\}$ (`Haar/OfBasis.lean:50–51, 253–256`); call it $\nu_b$. Theorem
15.8 below predicts $\nu_b=c\,\nu_{\mathbb C}$ for one number $c$. Three independent measurements
give it.

- *(a) The normalizing compact.* $\nu_b(P_b)=1$ (`Basis.addHaar_self`, `Haar/OfBasis.lean:278–279`).
  The vertices of $P_b$ are $0$, $1+2i$, $-1+3i$, $-2+i$, and the shoelace formula gives
  $\nu_{\mathbb C}(P_b)=\tfrac12\lvert 0+5+5+0\rvert=5$. Hence $c=1/5$.
- *(b) A second positive compact.* The image of $ds\,dt$ under $L_b(s,t)=sb_1+tb_2$ is
  $\sigma$-finite, translation-invariant and gives $P_b=L_b([0,1]^2)$ mass $1$, so it equals
  $\nu_b$ by `Basis.addHaar_eq_iff` (`Haar/OfBasis.lean:267–271`), an instance of Theorem
  15.8(4)–(5). Thus $\nu_b(Q)$ is the area of $L_b^{-1}(Q)$ in the $(s,t)$-plane. Since
  $L_b^{-1}(x,y)=\bigl(\tfrac{x+2y}{5},\tfrac{-2x+y}{5}\bigr)$, the square $Q$ goes to the square
  with vertices $(0,0)$, $(\tfrac15,-\tfrac25)$, $(\tfrac35,-\tfrac15)$, $(\tfrac25,\tfrac15)$, of
  side $1/\sqrt5$. So $\nu_b(Q)=1/5$ and again $c=1/5$.
- *(c) A positive test function.* Let $g(w)=(1-\lvert w\rvert^2)_+$: continuous, supported in
  the closed unit disc, $g\ge0$, $g(0)=1$. Then
  $\int g\,d\nu_{\mathbb C}=2\pi\int_0^1(1-r^2)\,r\,dr=\frac{\pi}{2}$. Since
  $\lvert L_b(s,t)\rvert^2=\lvert1+2i\rvert^2(s^2+t^2)=5(s^2+t^2)$,
  $$\int g\,d\nu_b=\iint\bigl(1-5(s^2+t^2)\bigr)_+\,ds\,dt=2\pi\int_0^{1/\sqrt5}(1-5\rho^2)\,\rho\,d\rho=\frac{\pi}{10},$$
  and the quotient $\int g\,d\nu_b\big/\int g\,d\nu_{\mathbb C}=\frac15$ is the formula for $c$ in
  Lemma 15.7b.
- *(d) The constant depends on the normalization, the modulus does not.* Because
  $\ell_{1+2i}(Q)=P_b$, the modulus of $w\mapsto(1+2i)w$ computed with $\nu_{\mathbb C}$ is
  $\nu_{\mathbb C}(P_b)/\nu_{\mathbb C}(Q)=5$, and computed with $\nu_b$ it is
  $\nu_b(P_b)/\nu_b(Q)=1\big/\tfrac15=5$. This is Theorem 15.8(6) on one example: $c=1/5$
  changes with the normalization, $\Delta_{\mathbb C}(1+2i)=5$ does not.
- *(e) Transport and the order of the inner product.* Here $\nu_b=\lambda\,\nu_{\mathbb C}$ with
  $\lambda=1/5$, and $\mu_b:=\Delta_{\mathbb C}^{-1}\nu_b=\kappa\,\mu_{\mathbb C}$ with $\kappa=1/5$,
  so the constant of Corollary 15.9 is $c'=\kappa\cdot1/\lambda=1$ and $U_b\colon g\mapsto\lvert w\rvert g$
  is unitary from $L^2(\mathbb C,\nu_b)$ onto $L^2(\mathbb C^\times,\mu_b)$. On the annulus
  $A=\{1\le\lvert w\rvert\le2\}$, $\nu_{\mathbb C}(A)=3\pi$ and $\nu_b(A)=\frac{3\pi}{5}$. With
  Mathlib's convention $\langle u,v\rangle=\int\overline u\,v$ (conjugate-linear in the first
  variable) and $g=i\mathbf 1_A$, $h=\mathbf 1_A$:
  $\langle h,g\rangle_{L^2(\nu_b)}=i\,\nu_b(A)=\frac{3\pi i}{5}$, while
  $\langle g,h\rangle_{L^2(\nu_b)}=-\frac{3\pi i}{5}$, and
  $\langle U_bh,U_bg\rangle_{L^2(\mu_b)}=i\int_A\lvert w\rvert^2\,d\mu_b=i\,\nu_b(A)=\frac{3\pi i}{5}$.
  The rescaling $R_\lambda g=\lambda^{-1/2}g=\sqrt5\,g$ is unitary from $L^2(\nu_{\mathbb C})$ onto
  $L^2(\nu_b)$: $\lVert R_\lambda\mathbf 1_A\rVert^2_{L^2(\nu_b)}=5\cdot\frac{3\pi}{5}=3\pi=\lVert\mathbf 1_A\rVert^2_{L^2(\nu_{\mathbb C})}$.

**Example 2 (the complex coordinate on $\mathbb C$ and $\mathbb C^\times$).**

- *(a) Additive.* In the coordinate $w=x+iy$,
  $dw\wedge d\overline w=(dx+i\,dy)\wedge(dx-i\,dy)=-2i\,dx\wedge dy$, so the coordinate measure
  $\nu_w:=\lvert dw\wedge d\overline w\rvert$ is $2\,dx\,dy$, i.e. $\nu_w=\lambda\,\nu_{\mathbb C}$
  with $\lambda=2$. The three measurements of Example 1 agree: $\nu_w(Q)/\nu_{\mathbb C}(Q)=2$,
  $\nu_w(D)/\nu_{\mathbb C}(D)=2\pi/\pi=2$ for the closed unit disc $D$, and
  $\int g\,d\nu_w\big/\int g\,d\nu_{\mathbb C}=\pi\big/\frac{\pi}{2}=2$.
- *(b) Multiplicative, normalized on a positive compact of $\mathbb C^\times$.* The annulus $A$ is
  compact with non-empty interior in $\mathbb C^\times$. Let $\mu_A$ be the Haar measure on
  $\mathbb C^\times$ with $\mu_A(A)=1$ (`haarMeasure A`). The measure
  $\Delta_{\mathbb C}^{-1}\nu_w=2\,dx\,dy/\lvert w\rvert^2=2\,dr\,d\theta/r$ is a Haar measure on
  $\mathbb C^\times$ (Lemma 15.3c), with
  $(\Delta_{\mathbb C}^{-1}\nu_w)(A)=2\cdot2\pi\int_1^2\frac{dr}{r}=4\pi\log 2$. Theorem 15.8(5)
  gives $\mu_A=c'\,\Delta_{\mathbb C}^{-1}\nu_w$ with $c'=\frac{1}{4\pi\log 2}$. In the notation of
  Corollary 15.9, $\kappa=\mu_A(A)/\mu_{\mathbb C}(A)=\frac{1}{2\pi\log 2}$ and $c'=\kappa\cdot1/\lambda$.
- *(c) The same constant from a test function on $\mathbb C^\times$.* Let
  $\varphi(w)=(1-\lvert\log\lvert w\rvert\rvert)_+$: continuous, supported in the compact set
  $\{e^{-1}\le\lvert w\rvert\le e\}\subset\mathbb C^\times$, $\varphi\ge0$, $\varphi(1)=1$. With
  $u=\log r$, $\int\varphi\,d\mu_{\mathbb C}=2\pi\int(1-\lvert u\rvert)_+\,du=2\pi$ and
  $\int\varphi\,d(\Delta_{\mathbb C}^{-1}\nu_w)=4\pi$. The test-function quotient is $2$, the same
  as the quotient $4\pi\log 2/(2\pi\log 2)$ on $A$. For $\mu_A$ the theorem then predicts
  $\int\varphi\,d\mu_A=c'\cdot4\pi=\frac{1}{\log 2}$, and the quotient
  $\int\varphi\,d\mu_A\big/\int\varphi\,d\mu_{\mathbb C}=\frac{1}{2\pi\log 2}$ is $\kappa$ again.
- *(d) A pushforward with no determinant.* The squaring map $q(w)=w^2$ is a continuous,
  surjective, proper homomorphism of $\mathbb C^\times$, so $q_\ast\mu_{\mathbb C}$ is again a Haar
  measure (`isHaarMeasure_map`, `Group/Measure.lean:817–827`), and Theorem 15.8 makes
  $q_\ast\mu_{\mathbb C}=c\,\mu_{\mathbb C}$. On $E_1=\{1\le\lvert z\rvert\le4\}$:
  $q^{-1}(E_1)=A$, so $q_\ast\mu_{\mathbb C}(E_1)=2\pi\log 2$ against
  $\mu_{\mathbb C}(E_1)=2\pi\log4$. On $E_2=\{1\le\lvert z\rvert\le2,\ 0\le\arg z\le\pi\}$:
  $q^{-1}(E_2)=\{1\le\lvert w\rvert\le\sqrt2,\ \arg w\in[0,\frac{\pi}{2}]\cup[\pi,\frac{3\pi}{2}]\}$ has
  $\mu_{\mathbb C}$-mass $\frac{\pi}{2}\log 2$ against $\mu_{\mathbb C}(E_2)=\pi\log 2$. Both quotients
  are $c=\frac12$. This is the multiplicative counterpart of the pushforward comparison in
  `map_linearMap_addHaar_pi_eq_smul_addHaar`: $\mathbb C^\times$ is not a vector space, there is no
  determinant, and only uniqueness says that the quotient is the same on every set.
- *(e) Transport, constants and the order of the inner product.* By Corollary 15.9(4) the map
  $U_A\colon g\mapsto c'^{-1/2}\Delta_{\mathbb C}^{1/2}g=(4\pi\log 2)^{1/2}\lvert w\rvert g$ is unitary
  from $L^2(\mathbb C,\nu_w)$ onto $L^2(\mathbb C^\times,\mu_A)$. With $g=i\mathbf 1_A$ and
  $h=\mathbf 1_A$: $\nu_w(A)=6\pi$, $\langle h,g\rangle_{L^2(\nu_w)}=6\pi i$,
  $\langle g,h\rangle_{L^2(\nu_w)}=-6\pi i$, and
  $\langle U_Ah,U_Ag\rangle_{L^2(\mu_A)}=4\pi\log 2\cdot i\int_A\lvert w\rvert^2\,d\mu_A=6\pi i$.
  For the rank-one kernel $k(x,y)=g(x)\overline{h(y)}$ one has
  $k_{1/2}(x,x)=\Delta_{\mathbb C}(x)\,g(x)\overline{h(x)}=i\lvert x\rvert^2\mathbf 1_A(x)$ and
  $$\int_{\mathbb C^\times}k_{1/2}(x,x)\,d\mu_A(x)=i\,c'\,\nu_w(A)=\frac{3i}{2\log 2}=c'\langle U_Ah,U_Ag\rangle_{L^2(\mu_A)}=c'\langle h,g\rangle_{L^2(\nu_w)},$$
  whereas the reversed order $c'\langle g,h\rangle$ would give $-\frac{3i}{2\log 2}$. The factor in
  front is $c'$, not the $c_S=1$ of Theorem 15.6 at a complex place, because $\nu_w$ and $\mu_A$
  are not the normalizations of Theorem 15.6.

**Definition 15.7 (Haar measures, positive compacts, positive test functions, regularity, scalar
factor).** Let $G$ be a topological group with its Borel $\sigma$-algebra. To keep the letters
$\mu,\nu$ of §§15.4.3.1–15.4.3.2 free, the measures compared here are called $m$ and $m'$
(Mathlib's `μ` and `μ'`).

1. $m$ is *left-invariant* if $m(gE)=m(E)$ for all $g\in G$ and Borel $E$; right-invariance is
   defined with $Eg$. A *Haar measure* in Mathlib's sense (`IsHaarMeasure`,
   `Group/Measure.lean:779–781`; additive `IsAddHaarMeasure`, `:766–768`) is a left-invariant
   measure that is finite on compact sets (`IsFiniteMeasureOnCompacts`) and positive on non-empty
   open sets (`IsOpenPosMeasure`). Regularity is not part of the definition (docstring,
   `:758–765`).
2. A *positive compact* is a compact $K_0\subseteq G$ with non-empty interior
   (`PositiveCompacts G`). A group with a positive compact is locally compact
   (`PositiveCompacts.locallyCompactSpace_of_group`, used at `Haar/Basic.lean:543`), and every Haar
   measure has $0<m(K_0)<\infty$. The measure `haarMeasure K₀` (`Haar/Basic.lean:521–522`) is a
   Haar measure (`:574–579`) with mass $1$ on $K_0$ (`:542–548`); it is regular (`:552–557`) and,
   if $G$ is second countable, $\sigma$-finite (`:565–567`). Its construction from Haar content
   (`Haar/Basic.lean:88–507`) is not read here.
3. A *positive test function* at $x_0$ is a continuous compactly supported $g\colon G\to\mathbb R$
   with $g\ge0$ and $g(x_0)\ne0$. On a locally compact group one exists at every point
   (`exists_continuous_nonneg_pos`, `UrysohnsLemma.lean:540–548`: Urysohn's lemma on a compact
   neighbourhood).
4. $m$ is *outer regular* if $m(E)=\inf\{m(U):U\supseteq E\text{ open}\}$ for Borel $E$, and
   *regular* if moreover it is finite on compact sets and $m(U)=\sup\{m(K):K\subseteq U\text{ compact}\}$
   for open $U$ (`Measure/Regular.lean:304–318`). It is *inner regular* if
   $m(E)=\sup\{m(K):K\subseteq E\text{ compact}\}$ for all Borel $E$ (`:327–330`), and *inner
   regular on finite-measure sets* if this holds when $m(E)<\infty$ (`InnerRegularCompactLTTop`,
   `:332–337`). A regular measure is inner regular on finite-measure sets (`:1122–1123`), and
   every locally finite measure on a $\sigma$-compact pseudometrizable space is regular
   (`:1183–1187`). The last instance covers $\mathbb R^n$, $\mathbb C$, $\mathbb C^\times$,
   $\mathbb Q_p$, $\mathbb Q_p^\times$, $K_S$ and $K_S^\times$.
   Compact finiteness gives local finiteness on these locally compact groups.
   Chapter 3 proves the compact-exhaustion supply for this instance and for all-Borel
   inner regularity. [From compact exhaustions to Radon inner regularity](03-landau-window-criterion.md#from-compact-exhaustions-to-radon-inner-regularity)
5. For $m$ a Haar measure and $m'$ left-invariant and finite on compact sets, the *scalar factor*
   $c(m',m)\in[0,\infty)$ is `haarScalarFactor m' m` (`Haar/Unique.lean:277–281`). On a locally
   compact group it is a number with $\int f\,dm'=c(m',m)\int f\,dm$ for every continuous
   compactly supported $f$ (`:292–300`); such a number exists by Lemma 15.7b. On a group that is
   not locally compact the definition returns $1$; this is harmless, because every continuous
   compactly supported function there is $0$.

**Lemma 15.7a (the Fubini identity with a positive test function) `[Lean, read]`.** Let $m$ and
$\varrho$ be measures on $G$, finite on compact sets, with $m$ left-invariant and $\varrho$
right-invariant and positive on non-empty open sets. Let $f,g$ be continuous with compact support,
$g\ge0$ and $g(x_0)\ne0$. Put $D(x)=\int g(y^{-1}x)\,d\varrho(y)$. Then
$$\int f\,dm=\Bigl(\int f(y)\,D(y)^{-1}\,d\varrho(y)\Bigr)\int g\,dm$$
(`integral_isMulLeftInvariant_isMulRightInvariant_combo`, [`Haar/Unique.lean:129–217`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Unique.lean#L129-L217)).
If $G$ is locally compact, $D$ is continuous and everywhere positive.

*Proof.* If $G$ is not locally compact, then $f=0$
(`HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group`, `Topology/Algebra/Group/Pointwise.lean:419–423`)
and both sides vanish; assume $G$ locally compact. *Continuity of $D$*
(`continuous_integral_apply_inv_mul`, `Haar/Unique.lean:74–100`): on a compact neighbourhood $t$
of a point, the integrand $(x,y)\mapsto g(y^{-1}x)$ vanishes for $y$ outside the compact set
$t\cdot(\operatorname{tsupport}g)^{-1}$, and a parametric integral of a continuous function with
uniformly compact support is continuous. *Positivity* (`:140–148`): for fixed $x$, the function
$y\mapsto g(y^{-1}x)$ is continuous and $\ge0$, and it is non-zero at $y=xx_0^{-1}$ because
$(xx_0^{-1})^{-1}x=x_0$. Its support is a non-empty open set, which has positive
$\varrho$-measure, so $D(x)>0$. This is the only use of $g\ge0$, $g(x_0)\ne0$ and the positivity
of $\varrho$ on open sets. *The computation* (`:149–217`) is a chain of seven equalities. First
$$\int f\,dm=\int f(x)D(x)^{-1}D(x)\,dm(x)=\int\!\!\int f(x)D(x)^{-1}g(y^{-1}x)\,d\varrho(y)\,dm(x).$$
Exchange the integrals: the integrand is continuous with support in $K\times\overline{KL^{-1}}$
for $K=\operatorname{tsupport}f$ and $L=\operatorname{tsupport}g$, and Fubini for continuous
compactly supported functions needs only finiteness of $m$ and $\varrho$ on compact sets, not
$\sigma$-finiteness (`integral_integral_swap_of_hasCompactSupport`, `Integral/Prod.lean:600–606`;
statement level). In the inner $m$-integral substitute $x\mapsto yx$, which preserves $m$; this
gives $\int\!\!\int f(yx)D(yx)^{-1}g(x)\,dm(x)\,d\varrho(y)$. Exchange again (support in
$L\times\overline{KL^{-1}}$). In the inner $\varrho$-integral use right-invariance,
$\int f(yx)D(yx)^{-1}\,d\varrho(y)=\int f(y)D(y)^{-1}\,d\varrho(y)$, a constant, and pull it out
of the $m$-integral. $\square$

**Lemma 15.7b (proportionality of integrals, and the algebra of the scalar factor)
`[Lean, read]`.** Let $G$ be locally compact, $m$ a Haar measure and $m'$ left-invariant and
finite on compact sets.

1. There is $c\ge0$ with $\int f\,dm'=c\int f\,dm$ for every continuous compactly supported $f$,
   and $c=\int g\,dm'\big/\int g\,dm$ for any positive test function $g$ (the denominator is
   positive). Hence $c=c(m',m)$ does not depend on $g$, and $c(m',m)=\int f\,dm'\big/\int f\,dm$
   whenever $\int f\,dm\ne0$
   (`exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`, `Haar/Unique.lean:226–258`;
   `haarScalarFactor_eq_integral_div` and `…_of_continuous_nonneg_pos`, `:302–320`).
2. $c(m,m)=1$ (`:363–375`); $c(m',n)=c(m',m)\,c(m,n)$ for a third Haar measure $n$
   (`haarScalarFactor_eq_mul`, `:377–397`); $c(a\,m',m)=a\,c(m',m)$ for $a\ge0$ (`:322–334`); and
   $c(m',m)>0$ when $m'$ is also a Haar measure (`:417–423`).
3. If $m'$ is also a Haar measure, $c(\phi_\ast m',\phi_\ast m)=c(m',m)$ for every topological group
   automorphism $\phi$ (`haarScalarFactor_map`, `:399–415`). If a group $\Gamma$ acts on a locally
   compact abelian group $A$ by additive automorphisms, each continuous, and
   $(\gamma\cdot n)(E):=n(\gamma E)$, then $c(\gamma\cdot m,\gamma\cdot n)=c(m,n)$ and therefore
   $c(\gamma\cdot m,m)=c(\gamma\cdot n,n)$ for any two additive Haar measures $m,n$ on $A$
   (`addHaarScalarFactor_domSMul`, `addHaarScalarFactor_smul_congr'`, `:1042–1072`).

*Proof.* (1) Let $\varrho=m^{\mathrm{inv}}$ be the image of $m$ under $x\mapsto x^{-1}$. It is
right-invariant, finite on compact sets and positive on open sets, because inversion is a
homeomorphism exchanging left and right translations (`Group/Measure.lean:371–372, 496–503`).
Take $x_0=1$ and a positive test function $g$ at $1$ (`:237–238`). Lemma 15.7a with the same $g$,
applied once to $m$ and once to $m'$, gives $\int f\,dm=B_f\int g\,dm$ and $\int f\,dm'=B_f\int g\,dm'$
with the same $B_f=\int fD^{-1}\,d\varrho$, because $D$ depends only on $g$ and $\varrho$. Since $m$
is positive on the open set $\{g>0\}$, $\int g\,dm>0$; eliminate $B_f$ (`:250–258`). For any other
$f$ with $\int f\,dm\ne0$, in particular any positive test function, divide. (2) Each identity is
a one-line computation with one positive test function $g$. For the chain rule,
$\int g\,dm'=c(m',n)\int g\,dn$ and also $\int g\,dm'=c(m',m)\int g\,dm=c(m',m)\,c(m,n)\int g\,dn$,
with $\int g\,dn>0$. Positivity follows from $1=c(m',m')=c(m',m)\,c(m,m')$. (3) Change variables,
$\int f\,d(\phi_\ast m)=\int f\circ\phi\,dm$, in numerator and denominator (`:405–415`); the action
is the same computation with $f\mapsto f(\gamma\,\cdot)$ (`:1048–1060`). Then
$c(\gamma\cdot m,m)=c(\gamma\cdot m,\gamma\cdot n)\,c(\gamma\cdot n,m)=c(m,n)\,c(\gamma\cdot n,m)=c(\gamma\cdot n,n)$
by the chain rule, the invariance just proved, and the chain rule again (`:1069–1072`). $\square$

**Lemma 15.7c (from integrals to sets with compact closure, without regularity)
`[Lean, read]`.** Let $G$ be locally compact, $m$ a Haar measure, $m'$ left-invariant and finite
on compact sets, and $c=c(m',m)$.

1. $m'(f^{-1}\{1\})=c\,m(f^{-1}\{1\})$ for every continuous compactly supported
   $f\colon G\to\mathbb R$ (`measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport`,
   `Haar/Unique.lean:476–538`).
2. If $m$ is inner regular on finite-measure sets, then $m'(E)=c\,m(E)$ for every Borel $E$ with
   compact closure (`:553–610`).
3. The same holds with no regularity assumption on $m$ or $m'$, and for every set $E$ with
   compact closure, measurable or not (`measure_isMulInvariant_eq_smul_of_isCompact_closure`,
   `:625–668`). In particular $m'=c\,m$ if $G$ is compact (`isMulInvariant_eq_smul_of_compactSpace`,
   `:675–679`).

*Proof.* (1) Choose $u_n\downarrow0$ in $(0,1)$ and let $v_n\colon\mathbb R\to[0,1]$ be the
thickened indicator of $\{1\}$ at scale $u_n$: continuous, equal to $1$ at $1$ and to $0$ outside
$(1-u_n,1+u_n)$. Then $v_n\circ f$ is continuous with compact support ($v_n(0)=0$ since $u_n<1$),
so $\int v_n\circ f\,dm'=c\int v_n\circ f\,dm$ by Lemma 15.7b. As $n\to\infty$, $v_n\circ f$
tends pointwise to $\mathbf 1_{f^{-1}\{1\}}$ with the integrable bound
$\mathbf 1_{\operatorname{tsupport}f}$, and dominated convergence on both sides gives the claim.
Both sides are finite because $f^{-1}\{1\}$ is compact (`:485–538`). (2) Lower bound
(`:553–569`): for $r<c\,m(E)$, Halmos's theorem gives a compact zero set $Z=f^{-1}\{1\}\subseteq E$
with $r<c\,m(Z)$ (`innerRegularWRT_preimage_one_hasCompactSupport_measure_ne_top_of_group`,
`Measure/EverywherePos.lean:280–288`, under exactly the hypotheses on $m$ assumed here; statement
level). Then $r<c\,m(Z)=m'(Z)\le m'(E)$ by (1). Upper bound (`:584–610`): Urysohn's lemma
(`exists_continuous_one_zero_of_isCompact`, `UrysohnsLemma.lean:404–406`; statement level) gives a
continuous compactly supported $f$ equal to $1$ on $\overline E$, so $E\subseteq T:=f^{-1}\{1\}$, a
compact zero set. The lower bound applied to $T\setminus E$ gives $c\,m(T\setminus E)\le m'(T\setminus E)$.
With $m'(T)=c\,m(T)$ from (1) and all four quantities finite, subtraction gives
$m'(E)\le c\,m(E)$. (3) Let $n$ be the regular Haar measure `haar` (`Haar/Basic.lean:584–585`); being
regular, it is inner regular on finite-measure sets. Apply (2) to the pairs $(m',n)$ and $(m,n)$
and use the chain rule $c(m',n)=c(m',m)\,c(m,n)$ (`:625–634`). A non-measurable $E$ is squeezed
between measurable hulls taken inside $\overline E$, once for each measure (`:645–668`). On a
compact group every set has compact closure. $\square$

This is the argument of Colin McQuillan's MathOverflow answer cited in the file header
(`:52–54`, sketch at `:425–461`): integrals of continuous functions determine the measures of
compact zero sets, and Halmos's completion-regularity theorem lets zero sets approximate every set
of finite measure. The question it answered, asked by Gouëzel while formalizing this file, was
whether two left-invariant Borel probability measures on a compact group must coincide; in the
file this is `isHaarMeasure_eq_of_isProbabilityMeasure` (`:695–711`) [McQuillan2024].

**Lemma 15.7d (regular measures: equality of measures) `[Lean, read]`.** Let $G$ be locally
compact and $m$ a Haar measure.

1. If $m$ and the left-invariant measure $m'$ are both regular, or both inner regular and $m'$ is
   finite on compact sets, then $m'=c(m',m)\,m$ (`isMulLeftInvariant_eq_smul_of_regular`,
   `Haar/Unique.lean:905–914`; `isMulLeftInvariant_eq_smul_of_innerRegular`, `:888–896`).
2. If $G$ is moreover second countable, $m'=c(m',m)\,m$ for every left-invariant $m'$ that is
   finite on compact sets (`isMulLeftInvariant_eq_smul`, `:921–924`).

*Proof.* For a Borel $E$ with $m(E),m'(E)<\infty$, inner regularity on finite-measure sets writes
both values as suprema over compact $K\subseteq E$ (`MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`,
`Measure/Regular.lean:881–884`), and $m'(K)=c\,m(K)$ by Lemma 15.7c because a compact set has
compact closure (`:847–879`; a non-measurable $E$ goes through a common measurable hull). In the
inner regular case every Borel set is such a supremum, which gives (1) at once (`:892–896`). In the
regular case, regularity writes $m'(U)$ and $m(U)$ as suprema over compact subsets for open $U$
(`IsOpen.measure_eq_iSup_isCompact`, `Measure/Regular.lean:1112–1114`), so $m'(U)=c\,m(U)$
(`:908–913`); outer regular measures that agree on open sets agree, because
$m(E)=\inf\{m(U):U\supseteq E\text{ open}\}$ (`OuterRegular.ext_isOpen`, `Measure/Regular.lean:481–486`).
(2) A second-countable locally compact group is $\sigma$-compact and pseudometrizable, so every
measure finite on compact sets is regular by the instance of Definition 15.7(4), and (1) applies
(`:924`). $\square$ The [Chapter 3 production proof](03-landau-window-criterion.md#from-compact-exhaustions-to-radon-inner-regularity) gives the open compact supremum and the outer field used here.

**Lemma 15.7e (σ-finite left-invariant measures on a measurable group: Halmos's argument)
`[Lean, read]`.** Let $G$ be a group whose multiplication $G\times G\to G$ and inversion are
measurable, let $m$ and $m'$ be $\sigma$-finite left-invariant measures, and let $s\subseteq G$
satisfy $0<m(s)<\infty$. Then $m'(s)\,m(t)=m(s)\,m'(t)$ for every $t\subseteq G$, and
$$m'=\frac{m'(s)}{m(s)}\,m$$
(`measure_mul_measure_eq`, `measure_eq_div_smul`, [`Group/Prod.lean:312–335`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Group/Prod.lean#L312-L335)).
If $G$ is a second-countable topological group with its Borel $\sigma$-algebra, the measurability
hypotheses hold (`ContinuousMul.measurableMul₂`, `ContinuousInv.measurableInv`,
`Constructions/BorelSpace/Basic.lean:543–544, 605–608`), and for every $\sigma$-finite
left-invariant $m'$ and every positive compact $K_0$, $m'=m'(K_0)\cdot$`haarMeasure K₀`
(`haarMeasure_unique`, [`Haar/Basic.lean:670–676`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L670-L676)).
Finiteness on compact sets is not assumed, and $m'=0$ is allowed.

*Proof.* (i) *Shears.* The map $S(x,y)=(x,xy)$ preserves $m'\times m$: on each fibre
$\{x\}\times G$ it is left translation by $x$, which preserves $m$ (`Group/Prod.lean:78–86`). With
the swap $R(x,y)=(y,x)$, the map $T=S^{-1}RSR$, $T(x,y)=(yx,x^{-1})$, preserves $m'\times m$
(`:130–140`), so by Tonelli, for measurable $F\ge0$,
$\int\!\!\int F(yx,x^{-1})\,dm(y)\,dm'(x)=\int\!\!\int F(x,y)\,dm(y)\,dm'(x)$ (`:182–195`).
(ii) *Halmos §60, Theorem A.* With $F(x,y)=\mathbf 1_s(x)f(y)$ this reads
$m'(s)\int f\,dm=\int m(sx^{-1})\,f(x^{-1})\,dm'(x)$, where $sx^{-1}=\{z:zx\in s\}$
(`measure_mul_lintegral_eq`, `:222–239`). (iii) Replace $f$ by $y\mapsto f(y^{-1})/m(sy^{-1})$,
which needs $0<m(sx^{-1})<\infty$. Positivity holds for every $x$: a right translate of a non-null
set is non-null (`:197–206`). Finiteness holds for $m'$-almost every $x$ (`:256–281`, through the
mutual absolute continuity of non-zero left-invariant measures, `:241–249`). This finiteness is the
step Halmos's proof leaves unjustified (docstring `:283–291`). Van Doorn's 2021 formalization
patched it by assuming $s$ compact and the measure regular, and he left open whether finiteness
holds for every $x$ [vanDoorn2021, §6, p. 18:15]; the pinned file needs only almost every $x$ and
so allows any $s$ with $0<m(s)<\infty$. The result is
$m'(s)\int f(y^{-1})\,m(sy^{-1})^{-1}\,dm(y)=\int f\,dm'$ (`measure_lintegral_div_measure`,
`:292–310`). (iv) Take $f=\mathbf 1_t$ and apply (iii) to the pairs $(m',m)$ and $(m,m)$. The same
integral $J=\int\mathbf 1_t(y^{-1})\,m(sy^{-1})^{-1}\,dm(y)$ gives $m'(s)J=m'(t)$ and $m(s)J=m(t)$,
hence $m'(s)\,m(t)=m(s)\,m'(t)$ (`:312–326`; non-measurable $s,t$ through common measurable hulls).
(v) Divide by $m(s)$ (`:329–335`). For `haarMeasure_unique` take $m=$ `haarMeasure K₀` and
$s=\overline{K_0}$: $m(\overline{K_0})=1$ (`Haar/Basic.lean:559–561`), $\overline{K_0}$ is compact
with non-empty interior, and $m'(\overline{K_0})=m'(K_0)$ (`IsCompact.measure_closure`,
`Constructions/BorelSpace/Basic.lean:288–289`). $\square$

**Lemma 15.7f (finite products, the unit-cube normalization and the pushforward comparison)
`[Lean, read]`.**

1. A finite product of $\sigma$-finite left-invariant measures $m_i$ on groups with measurable
   translations is left-invariant: translation by $v$ pulls the box $\prod_i E_i$ back to the box
   $\prod_i v_i^{-1}E_i$, whose mass is $\prod_i m_i(E_i)$, and $\sigma$-finite product measures
   are determined by boxes (`pi.isMulLeftInvariant`, `Constructions/Pi.lean:572–578`, with `pi_eq`
   and `pi_pi`, `:276–293`). A finite product of Haar measures is a Haar measure
   (`pi.isHaarMeasure`, `:648–650`).
2. *(Unit-cube normalization.)* On $\iota\to\mathbb R$, `volume` is `addHaarMeasure` of $[0,1]^\iota$
   (`addHaarMeasure_eq_volume_pi`, `EqHaar.lean:117–121`): by Lemma 15.7e,
   $\mathrm{vol}=\mathrm{vol}([0,1]^\iota)\cdot$`addHaarMeasure`$([0,1]^\iota)$, and
   $\mathrm{vol}([0,1]^\iota)=\prod_{i\in\iota}\mathrm{vol}([0,1])=1$ (`volume_pi_pi`,
   `Constructions/Pi.lean:664–666`).
3. *(Pushforward comparison.)* For an additive Haar measure $\mu$ on $\iota\to\mathbb R$ and a
   linear $f$ with $\det f\ne0$, (2) and Lemma 15.7e give $\mu=\mu([0,1]^\iota)\,\mathrm{vol}$; the
   pushforward of a multiple is the multiple of the pushforward, and Lemma 15.5a(4) computes
   $f_\ast\mathrm{vol}$, so $f_\ast\mu=\lvert\det f\rvert^{-1}\mu$ (`EqHaar.lean:218–226`).

*Proof.* Items (1)–(3) transcribe the cited proof bodies; the only input from outside this
subsection is Lemma 15.5a(4). $\square$

**Theorem 15.8 (uniqueness of Haar measure, with the hypotheses each consumer uses)
`[Lean, read]`.** Let $G$ be a locally compact topological group with its Borel $\sigma$-algebra,
$m$ a Haar measure on $G$, and $m'$ a left-invariant measure on $G$. Write $c=c(m',m)$.

1. *(Integrals.)* If $m'$ is finite on compact sets, $\int f\,dm'=c\int f\,dm$ for every
   continuous compactly supported $f$, and $c=\int g\,dm'/\int g\,dm$ for every positive test
   function $g$.
2. *(Sets with compact closure.)* If $m'$ is finite on compact sets, $m'(E)=c\,m(E)$ for every
   $E\subseteq G$ with compact closure; if $G$ is compact, $m'=c\,m$.
3. *(Regular measures.)* If $m$ and $m'$ are regular, or both are inner regular and $m'$ is finite
   on compact sets, then $m'=c\,m$.
4. *(σ-finite measures on second-countable groups.)* If $G$ is second countable and $m'$ is
   $\sigma$-finite, then $m'=\frac{m'(s)}{m(s)}\,m$ for every $s$ with $0<m(s)<\infty$; in
   particular $m'=m'(K_0)\cdot$`haarMeasure K₀` for every positive compact $K_0$.
5. *(Normalization.)* Under (3) or (4), the constant equals $m'(K_0)/m(K_0)$ for every positive
   compact $K_0$, and $\int g\,dm'/\int g\,dm$ for every positive test function $g$; it is positive
   when $m'$ is a Haar measure. Two such Haar measures that give one positive compact the same
   mass, or one positive test function the same integral, are equal. In particular `haarMeasure K₀`
   is the only such measure with mass $1$ on $K_0$ (`haarMeasure_eq_iff`, `Haar/Basic.lean:682–685`).
6. *(Moduli.)* Let a group $\Gamma$ act on a locally compact abelian group $A$ by additive
   automorphisms, each continuous. Then $\Delta(\gamma):=c(\gamma\cdot n,n)$ does not depend on the
   additive Haar measure $n$, $\gamma\mapsto\Delta(\gamma)$ is a homomorphism to $\mathbb R_{>0}$, and
   $n(\gamma E)=\Delta(\gamma)\,n(E)$ for every $E\subseteq A$ when $n$ is regular. For a local field
   $K$ and $\Gamma=K^\times$ acting by multiplication this is $\Delta_K$ of Definition 15.2(1)
   (`distribHaarChar`).

*Proof.* (1) is Lemma 15.7b(1), (2) is Lemma 15.7c(3), and (3) is Lemma 15.7d(1). For (4), $m$ is
$\sigma$-finite because a second-countable locally compact group is $\sigma$-compact
(`IsHaarMeasure.sigmaFinite`, `Group/Measure.lean:912–916`), and Lemma 15.7e applies.
(5) Under (3), apply (2) to $K_0$ and (1) to $g$. Under (4), take $s=K_0$, which satisfies
$0<m(K_0)<\infty$ because $K_0$ is compact with non-empty interior. The constant
$m'(K_0)/m(K_0)$ is finite: the measure $\infty\cdot m$ gives infinite mass to every set of
positive $m$-measure, so it is not $\sigma$-finite. Hence $m'$ is a finite multiple of $m$,
finite on compact sets, and (1) applies to $g$. Positivity is Lemma 15.7b(2), and a constant equal
to $1$ on one positive compact or one test function is $1$. (6) Independence of $n$ is Lemma
15.7b(3), as used in `addHaarScalarFactor_smul_eq_distribHaarChar` (`DistribChar.lean:63–66`). The
homomorphism property is the chain rule together with $c(\gamma\cdot m,\gamma\cdot n)=c(m,n)$; it
is the `map_mul'` field of `distribHaarChar` (`DistribChar.lean:43–55`), and $\Delta(\gamma)>0$ is
Lemma 15.7b(2). For regular $n$ the measure $E\mapsto n(\gamma E)$ is regular, as the image of $n$
under a homeomorphism (`Regular.domSMul`, `Measure/Regular.lean:1176–1179`), and left-invariant, so
(3) gives $n(\gamma E)=\Delta(\gamma)\,n(E)$; this is `distribHaarChar_mul` (`DistribChar.lean:83–86`).
$\square$

**Corollary 15.9 (the constant in the half-density transport) `[Expository]` over `[Lean, read]`
inputs.** In the setting of Theorem 15.6, let $\nu'$ be any additive Haar measure on $K_S$ and
$\mu'$ any Haar measure on the multiplicative group $K_S^\times$.

1. $\nu'=\lambda\,\nu_S$ with $\lambda=\nu'(C)/\nu_S(C)>0$ for any positive compact
   $C\subseteq K_S$; for a product $C=\prod_vC_v$ of positive compacts,
   $\nu_S(C)=\prod_v\nu_v(C_v)$.
2. The modulus $\Delta_S$ computed from $\nu'$ is the one computed from $\nu_S$.
3. $\mu'=c'\,\Delta_S^{-1}\nu'|_{K_S^\times}$ with $c'=\mu'(C')\big/\int_{C'}\Delta_S^{-1}\,d\nu'$ for
   any positive compact $C'\subseteq K_S^\times$; equivalently $c'=\kappa\,c_S/\lambda$ with
   $\kappa=\mu'(C')/\mu_S(C')$.
4. $U'_{S,a}(g):=c'^{-1/2}\Delta_S^{a}g|_{K_S^\times}$ is a unitary map from $L^2(K_S,\nu')$ onto
   $L^2(K_S^\times,\mu'_{S,a})$, where $\mu'_{S,a}:=\mu'.\mathrm{withDensity}(\Delta_S^{1-2a})$, and
   $U'_{S,a}\circ R_\lambda=R_\kappa\circ U_{S,a}$ for the rescaling unitaries
   $R_\lambda\colon g\mapsto\lambda^{-1/2}g$ from $L^2(\nu_S)$ onto $L^2(\nu')$ and
   $R_\kappa\colon f\mapsto\kappa^{-1/2}f$ from $L^2(\mu_{S,a})$ onto $L^2(\mu'_{S,a})$. The whole
   dependence of the transport of Theorem 15.6 on the two normalizations is carried by the number
   $c'$.
5. With the inner product conjugate-linear in the first variable, as in Mathlib,
   $\langle U'_{S,1/2}h,U'_{S,1/2}g\rangle_{L^2(\mu')}=\langle h,g\rangle_{L^2(\nu')}$, and the
   rank-one kernel $k(x,y)=g(x)\overline{h(y)}$ satisfies
   $\int_{K_S^\times}k_{1/2}(x,x)\,d\mu'(x)=c'\langle U'_{S,1/2}h,U'_{S,1/2}g\rangle_{L^2(\mu')}=c'\langle h,g\rangle_{L^2(\nu')}$.
6. At a finite place $v$ with residue field of size $q_v$ and $\nu_v(\mathcal O_v)=1$, the Haar
   measure $\mu_v^1$ on $F_v^\times$ with $\mu_v^1(\mathcal O_v^\times)=1$ is $c_v\,\Delta_v^{-1}\nu_v$
   with $c_v=\frac{q_v}{q_v-1}$. With $c_v=1$ at the archimedean places, where Masullo takes
   $\mu_v=\Delta_v^{-1}\nu_v$, the product measure is $\mu_S=c_S\Delta_S^{-1}\nu_S$ with
   $c_S=\prod_{v\in S_f}c_v$, Masullo's (12.4.1.17) [Paper; Masullo p. 518]; for $v=5$,
   $c_5=\frac54$.

*Proof.* (1) $K_S$ is a second-countable locally compact group, so its Haar measures are regular
(Definition 15.7(4)) and Theorem 15.8(3),(5) applies; $\nu_S(C)=\prod_v\nu_v(C_v)$ is the product
formula on boxes. (2) is Theorem 15.8(6) for $K_S^\times$ acting on $K_S$ coordinatewise.
(3) $\Delta_S^{-1}\nu'=\lambda\,\Delta_S^{-1}\nu_S=(\lambda/c_S)\,\mu_S$ is a Haar measure on
$K_S^\times$ (Theorem 15.6(1)), and $\mu'=\kappa\,\mu_S$ by Theorem 15.8(3),(5) on $K_S^\times$, so
$\mu'=\kappa c_S\lambda^{-1}\,\Delta_S^{-1}\nu'$. (4) The proof of Theorem 15.6(2) uses only the
identity $\mu_S=\nu_S|_{K_S^\times}.\mathrm{withDensity}(c_S\Delta_S^{-1})$ and Lemma 15.5d(1). By (3)
the identity $\mu'=\nu'|_{K_S^\times}.\mathrm{withDensity}(c'\Delta_S^{-1})$ holds, and the same
argument gives unitarity. For the square,
$U'_{S,a}R_\lambda g=c'^{-1/2}\lambda^{-1/2}\Delta_S^ag=(\kappa c_S)^{-1/2}\Delta_S^ag=R_\kappa U_{S,a}g$.
(5) Lemma 15.5d(1) preserves inner products. In Mathlib $\langle u,v\rangle_{L^2}=\int\overline{u}\,v$
(`L2.inner_def`, `Function/L2Space.lean:134–138`, with `RCLike.inner_apply`,
`Analysis/InnerProductSpace/Basic.lean:910–912`; the convention is stated at
`Analysis/InnerProductSpace/Defs.lean:53–54`). Pointwise,
$k_{1/2}(x,x)=\Delta_S(x)g(x)\overline{h(x)}=c'\,\overline{U'h(x)}\,U'g(x)$; integrate against
$\mu'$. (6) $\mathcal O_v^\times$ is compact and open in $F_v^\times$, hence a positive compact, and
$(\Delta_v^{-1}\nu_v)(\mathcal O_v^\times)=\nu_v(\mathcal O_v^\times)=1-q_v^{-1}$ by Lemma 15.3a(3), so
Theorem 15.8(5) gives $c_v=1/(1-q_v^{-1})$. The product of the local measures is a Haar measure on
$K_S^\times$ (Lemma 15.7f(1)) and equals $c_S\Delta_S^{-1}\nu_S$ on boxes. $\square$

Corollary 15.9(5) is the Mathlib-convention form of the rank-one identity of Theorem 15.6(2),
which now reads $c_S\langle U_Sh,U_Sg\rangle=c_S\langle h,g\rangle$. Example 2(e) shows that the two
orders differ by complex conjugation as soon as $g$ and $h$ carry different phases.

**Example 3 (deleting a hypothesis).**

- *(a) Positivity of $m$.* The zero measure on $\mathbb R^2$ is left-invariant and finite on
  compact sets, but $\int g\,d0=0$ for every test function, so the quotient of Lemma 15.7b is
  undefined, and $\nu_{\mathbb C}\ne c\cdot0$ for every $c\in[0,\infty]$ ($\nu_{\mathbb C}(Q)=1$,
  while $\infty\cdot0=0$ in $[0,\infty]$). This is why `haarScalarFactor` asks $m$ to be a Haar
  measure, "to exclude for instance the case where `μ = 0`" (`Haar/Unique.lean:265–268`). On
  $\mathbb R^2$ this is the only failure: a left-invariant measure that is finite on compacts and
  vanishes on one open ball vanishes on countably many translates covering $\mathbb R^2$, hence is
  $0$.
- *(b) Positivity of the test function.* $g_-(x,y)=x\,(1-x^2-y^2)_+$ is continuous with compact
  support and $g_-(\tfrac12,0)=\frac{3}{8}\ne0$, but it changes sign. Every Haar measure on
  $\mathbb R^2$ is a multiple of $\nu_{\mathbb C}$, which is invariant under $(x,y)\mapsto(-x,y)$, so
  $\int g_-\,dm=0$ for all of them: the quotient $\int g_-\,d\nu_b\big/\int g_-\,d\nu_{\mathbb C}=0/0$
  fixes nothing. In Lemma 15.7a with $\varrho=\nu_{\mathbb C}$,
  $D(x)=\int g_-(x-y)\,d\nu_{\mathbb C}(y)=0$ for every $x$, and $D^{-1}$ does not exist.
- *(c) Local finiteness.* Counting measure $\#$ on $\mathbb R^2$ is translation-invariant and
  positive on non-empty open sets, but $\#(Q)=\infty$. It is no multiple of $\nu_{\mathbb C}$:
  $\#(\{0\})=1$, while $c\,\nu_{\mathbb C}(\{0\})=0$ for every $c\in[0,\infty]$. Both routes fail at a
  definite step. For a positive test function the Lebesgue integral is
  $\int g\,d\#=\sum_xg(x)=\infty$, since $g>0$ on an uncountable open set; $g$ is not
  $\#$-integrable, Mathlib's Bochner integral assigns it the value $0$, and neither Lemma 15.7a nor
  Lemma 15.7b applies, both requiring finiteness on compact sets. And $\#$ is not $\sigma$-finite (a
  set of finite measure is finite), so Lemma 15.7e does not apply.
- *(d) Normalizing on the wrong set.* The unit circle $S^1\subset\mathbb C^\times$ is compact with
  empty interior: $\mu_{\mathbb C}(S^1)=\int_{S^1}\lvert w\rvert^{-2}\,d\nu_{\mathbb C}=0$, so every Haar
  measure on $\mathbb C^\times$ gives $S^1$ mass $0$ and the normalization "$\mu'(S^1)=1$" has no
  solution. The group $\mathbb C^\times$ itself has interior but is not compact, and every Haar
  measure gives it mass $\infty$ (`measure_univ_of_isMulLeftInvariant`, `Group/Measure.lean:662–663`;
  here directly, $\mathbb C^\times$ contains the disjoint translates $4^{j}A$, $j\in\mathbb Z$). These are
  the hypotheses $m(s)\ne0$ and $m(s)\ne\infty$ of `measure_eq_div_smul`; positive compacts satisfy
  both.
- *(e) Regularity, or second countability.* Let $G=\mathbb R_d\times\mathbb R$, the first factor
  discrete: locally compact, not second countable. With $\lambda_1$ Lebesgue measure and
  $E_x=\{y:(x,y)\in E\}$, the measure $m_\Sigma(E)=\sum_{x\in\mathbb R}\lambda_1(E_x)$ is a Haar measure:
  it is translation-invariant, finite on compact sets (a compact set meets finitely many lines
  $\{x\}\times\mathbb R$) and positive on open sets. It is not $\sigma$-finite. Let $m_{\mathrm{reg}}$ be
  the regular Haar measure `haarMeasure K₀` for $K_0=\{0\}\times[0,1]$. By Theorem 15.8(2) applied to
  $K_0$ the constant is $1$, the two measures agree on every set with compact closure, and by
  `measure_isHaarMeasure_eq_smul_of_isOpen` (`Haar/Unique.lean:828–831`) they agree on every open set.
  On the closed set $E=\mathbb R_d\times\{0\}$, $m_\Sigma(E)=0$. An open $U\supseteq E$ contains
  segments $\{x\}\times(-\varepsilon_x,\varepsilon_x)$ for every $x$; for some $k$ uncountably many
  $\varepsilon_x$ exceed $1/k$, and $N$ of these disjoint segments have $m_{\mathrm{reg}}$-mass $2N/k$.
  So outer regularity gives $m_{\mathrm{reg}}(E)=\infty$, and $m_\Sigma\ne c\,m_{\mathrm{reg}}$ for every
  $c$: equality of measures needs the hypotheses of (3) or (4). The comment at
  `Haar/Basic.lean:587–592` uses the same set to show that Steinhaus' theorem fails for the regular
  Haar measure.

**Remark 1 (two routes, one constant).** The consumers in §15.4.3 and what they use:

| Consumer | Declaration called | Route | Hypotheses used |
|---|---|---|---|
| Definition 15.2(1): $\nu(tS)=\Delta_K(t)\nu(S)$ | `distribHaarChar_mul` → `isAddLeftInvariant_eq_smul_of_regular` | T | locally compact, $\nu$ regular |
| Definition 15.2(1): independence of $\nu$ | `addHaarScalarFactor_smul_congr'` | T, integrals only | locally compact |
| Lemma 15.3c: inversion | `isInvInvariant_of_regular` → `isMulLeftInvariant_eq_smul_of_regular` | T | locally compact, regular, abelian |
| Lemma 15.5b(1): pushforward on $\iota\to\mathbb R$ | `map_linearMap_addHaar_pi_eq_smul_addHaar` → `addHaarMeasure_unique` | P | second countable, $\sigma$-finite |
| Unit-cube normalization of `volume` | `addHaarMeasure_eq_volume_pi` → `addHaarMeasure_unique` | P | second countable, $\sigma$-finite, box formula |
| Theorem 15.6(1) and (12.4.1.17): $c_S$ | Corollary 15.9(3),(6) | T or P | second countable, locally compact |

On every group of this chapter both routes apply, and Theorem 15.8(5) says that they give the same
number. They extend in different directions: route T reaches groups that are not second countable
(Example 3(e) shows that it then needs regularity for sets that are not relatively compact), and
route P reaches measures that are only $\sigma$-finite.

**Remark 2 (what this does not show).** Like §§15.4.3.1–15.4.3.2, this subsection is local measure
theory on one locally compact group at a time and proves nothing about zeros. It makes the constant
in (12.4.1.17) a theorem. It does not touch the diagonal smoothing of kernels (pp. 15, 517), the
omitted §12.3 (p. 514), the Chapter 10 strip bound (p. 451), the asserted $\alpha$-independence in
Theorem 12.5.1.1 (p. 519) or the unwritten Chapter 13 (pp. 521–522), which stay `[Open]`.

**Remark 3 (repairs to §§15.4.3.1–15.4.3.2 made with this subsection).** Following the audit of
§15.4.3.2: Lemma 15.5d(2) now says that the identity fails the `MeasurePreserving` hypothesis of the
isometric precomposition interface, instead of saying that no precomposition operator exists, and
gives a bounded non-isometric example; the rank-one identity of Theorem 15.6(2) is written in
Mathlib's order $c_S\langle U_Sh,U_Sg\rangle=c_S\langle h,g\rangle$. Found while reading for this
subsection: the source map of §15.4.3.2 placed `addHaarMeasure_unique` in `Haar/Unique.lean`; it is
the additive form of `haarMeasure_unique` in `Haar/Basic.lean:670–676`.

**Source map for this subsection.** Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`; all
paths under `Mathlib/`.

| File and lines at the pin | Declarations | Role here | Reading |
|---|---|---|---|
| [`MeasureTheory/Measure/Haar/Unique.lean:74–423`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Unique.lean#L74-L423) | `continuous_integral_apply_inv_mul`, `integral_isMulLeftInvariant_isMulRightInvariant_combo`, `exists_integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`, `haarScalarFactor`, `integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`, `haarScalarFactor_eq_integral_div`, `…_of_continuous_nonneg_pos`, `haarScalarFactor_smul`, `haarScalarFactor_self`, `haarScalarFactor_eq_mul`, `haarScalarFactor_map`, `haarScalarFactor_pos_of_isHaarMeasure` | Definition 15.7(5), Lemmas 15.7a–b | R3 |
| [`MeasureTheory/Measure/Haar/Unique.lean:425–711`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Unique.lean#L425-L711) | `measure_preimage_isMulLeftInvariant_eq_smul_of_hasCompactSupport`, `smul_measure_isMulInvariant_le_of_isCompact_closure`, `measure_isMulInvariant_eq_smul_of_isCompact_closure_of_innerRegularCompactLTTop`, `…_of_measurableSet`, `measure_isMulInvariant_eq_smul_of_isCompact_closure`, `isMulInvariant_eq_smul_of_compactSpace`, `isHaarMeasure_eq_of_isProbabilityMeasure` | Lemma 15.7c | R3 |
| [`MeasureTheory/Measure/Haar/Unique.lean:821–924`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Unique.lean#L821-L924) | `measure_isHaarMeasure_eq_smul_of_isOpen`, `measure_isMulLeftInvariant_eq_smul_of_ne_top`, `isMulLeftInvariant_eq_smul_of_innerRegular`, `isMulLeftInvariant_eq_smul_of_regular`, `isMulLeftInvariant_eq_smul` | Lemma 15.7d, Example 3(e) | R3 (the open-set case `:720–820` statement level) |
| [`MeasureTheory/Measure/Haar/Unique.lean:1042–1072`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Unique.lean#L1042-L1072) | `addHaarScalarFactor_domSMul`, `addHaarScalarFactor_smul_congr`, `addHaarScalarFactor_smul_congr'` | Lemma 15.7b(3), Theorem 15.8(6) | R3 |
| [`MeasureTheory/Group/Prod.lean:78–335`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Group/Prod.lean#L78-L335) | `measurePreserving_prod_mul`, `measurePreserving_mul_prod_inv`, `lintegral_lintegral_mul_inv`, `measure_mul_right_null`, `measure_mul_lintegral_eq`, `absolutelyContinuous_of_isMulLeftInvariant`, `ae_measure_preimage_mul_right_lt_top(_of_ne_zero)`, `measure_lintegral_div_measure`, `measure_mul_measure_eq`, `measure_eq_div_smul` | Lemma 15.7e | R3 |
| [`MeasureTheory/Measure/Haar/Basic.lean:517–585, 644–700`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L644-L700) | `haarMeasure`, `haarMeasure_self`, `regular_haarMeasure`, `haarMeasure_closure_self`, `sigmaFinite_haarMeasure`, `isHaarMeasure_haarMeasure`, `haar`, `haarMeasure_unique`, `haarMeasure_eq_iff`, `regular_of_isMulLeftInvariant` | Definition 15.7(2), Lemma 15.7e | R3 (construction `:88–507` statement level) |
| [`MeasureTheory/Constructions/Pi.lean:276–293, 572–578, 648–650, 664–666`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Constructions/Pi.lean#L572-L578) | `pi_eq`, `pi_pi`, `pi.isMulLeftInvariant`, `pi.isHaarMeasure`, `volume_pi_pi` | Lemma 15.7f(1)–(2) | R3 (`pi_eq` statement level) |
| `MeasureTheory/Measure/Lebesgue/EqHaar.lean:113–121, 218–226` | `addHaarMeasure_eq_volume`, `addHaarMeasure_eq_volume_pi`, `map_linearMap_addHaar_pi_eq_smul_addHaar` | Lemma 15.7f(2)–(3) | inherited R3 (§15.4.3.2); uniqueness step read here |
| `MeasureTheory/Measure/Haar/OfBasis.lean:50–51, 187–200, 253–279` | `parallelepiped`, `Basis.parallelepiped`, `Basis.addHaar`, `Basis.addHaar_eq_iff`, `Basis.addHaar_self` | Example 1 | R3 |
| `MeasureTheory/Measure/Haar/DistribChar.lean:43–86` | `distribHaarChar`, `addHaarScalarFactor_smul_eq_distribHaarChar`, `distribHaarChar_mul` | Theorem 15.8(6) | inherited R3 (§15.4.3.1) |
| `MeasureTheory/Group/Measure.lean:371–372, 496–503, 662–663, 758–781, 791–797, 804–827, 912–916` | inversion instances, `measure_univ_of_isMulLeftInvariant`, `IsAddHaarMeasure`, `IsHaarMeasure`, `IsHaarMeasure.smul`, `isHaarMeasure_of_isCompact_nonempty_interior`, `isHaarMeasure_map`, `IsHaarMeasure.sigmaFinite` | Definition 15.7(1), Lemma 15.7b, Examples 2(d), 3(d) | R3 for the definitions, statement level for the instances |
| `MeasureTheory/Measure/Regular.lean:304–337, 481–486, 881–884, 1112–1123, 1176–1187` | `OuterRegular`, `Regular`, `InnerRegular`, `InnerRegularCompactLTTop`, `OuterRegular.ext_isOpen`, `measure_eq_iSup_isCompact(_of_ne_top)`, `Regular.domSMul`, `Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` | Definition 15.7(4), Lemma 15.7d, Theorem 15.8(6) | definitions and `ext_isOpen` R3; `:1183–1187` local R3 in [Chapter 3](03-landau-window-criterion.md#from-compact-exhaustions-to-radon-inner-regularity); other listed instances retain statement level here |
| `MeasureTheory/Measure/EverywherePos.lean:280–288` · `Topology/UrysohnsLemma.lean:404–406, 540–548` · `MeasureTheory/Integral/Prod.lean:600–606` · `MeasureTheory/Constructions/BorelSpace/Basic.lean:288–289, 543–544, 605–608` · `Topology/Algebra/Group/Pointwise.lean:419–423` | Halmos's completion-regularity theorem, `exists_continuous_one_zero_of_isCompact`, `exists_continuous_nonneg_pos`, `integral_integral_swap_of_hasCompactSupport`, `IsCompact.measure_closure`, `ContinuousInv.measurableInv`, `ContinuousMul.measurableMul₂`, `HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group` | named inputs of Lemmas 15.7a–e | statement level (`exists_continuous_nonneg_pos` R3) |
| `Analysis/InnerProductSpace/Defs.lean:53–54` · `Analysis/InnerProductSpace/Basic.lean:903–915` · `MeasureTheory/Function/L2Space.lean:134–138` | convention, `RCLike.innerProductSpace`, `RCLike.inner_apply`, `L2.inner_def` | Corollary 15.9(5), Examples 1(e), 2(e), Theorem 15.6(2) | R3 |

**Reading levels.**

| Level | What |
|---|---|
| Read here (R3) | The test-function chain of `Haar/Unique.lean` (`:74–711`, `:821–924`, `:1042–1072`); the Halmos chain of `Group/Prod.lean:78–335`; `haarMeasure_unique` and its neighbours in `Haar/Basic.lean`; the product lemmas of `Constructions/Pi.lean`; `Basis.addHaar`; the inner-product convention |
| Inherited | `distribHaarChar` and `isInvInvariant_of_regular` (§15.4.3.1); the determinant and `withDensity` lemmas, Lemmas 15.5a–d and Theorem 15.6 (§15.4.3.2) |
| Statement level, named | The construction of Haar measure from Haar content; Halmos's completion-regularity theorem; the open-set case `measure_isHaarMeasure_eq_smul_of_isEverywherePos`; Urysohn's lemma; Fubini for compactly supported functions; Tonelli and `pi_eq`; the remaining regularity and $\sigma$-finiteness instances (the [compact-exhaustion instance](03-landau-window-criterion.md#from-compact-exhaustions-to-radon-inner-regularity) is read in Chapter 3); measurability of multiplication under second countability; the archive's own call sites of these theorems |
| Literature | Halmos, *Measure Theory* (1950), Ch. XI, §§59–60, as cited by `Group/Prod.lean` [Halmos1950; bibliographic record checked, text not consulted]; F. van Doorn, "Formalized Haar Measure", ITP 2021, §6 [vanDoorn2021]; C. McQuillan's answer to S. Gouëzel's MathOverflow question 456670 [McQuillan2024] |

**Reading order.** [Finite covers and Haar existence](#15434-constructing-haar-measure-from-finite-covers) supply the comparison measure used above. [Finite-place products](#15435-finite-place-products-from-rectangles-and-marginals) recover the density and transport constants of Theorem 15.6. [Carathéodory restriction](#15436-from-outer-measure-to-a-countably-additive-measure) supplies both measure constructions.

#### 15.4.3.4 Constructing Haar measure from finite covers

The comparison in Lemma 15.7c(3) starts by choosing a regular left Haar
measure. Where does that measure come from? A small open neighborhood $U$ of
the identity gives a unit of size: count how many translates cover a compact
set. The unit changes with $U$, so compare every count with the count for
one fixed compact set $K_0$. On a finite discrete group one can use
$U=\{1\}$ and the counts are already cardinalities. On the real line an
interval of positive length needs more and more translates as the unit
shrinks, but the *ratio* of counts stays bounded. The proof constructs one
simultaneous value for all compact sets and then makes open sets measurable.

**Definition 15.10 (covering number and normalized count).**
Let $G$ be a topological group with identity $1$ and let $K$ be compact. Write $N(K,V)$ for the
least size of a finite cover of $K$ by left translates of $V$, when it
exists. The pin writes a translate as the preimage under left
multiplication by $g$, namely $g^{-1}V$. Inverting the finite set of
indices gives the equivalent convention $gV$ used here. For compact
$K$ and $\operatorname{int}V\ne\varnothing$ there is always such a cover.
Indeed, if $v\in\operatorname{int}V$, the translate
$xv^{-1}\operatorname{int}V$ contains $x$. Compactness extracts finitely
many of these open sets, and the well-ordering of the natural numbers
gives a minimum. The code takes the infimum of natural cardinalities
and uses zero also when no cover exists. Every use of a minimum below
has the finite-cover proof just given.

Fix a compact $K_0$ with nonempty interior. For each open neighborhood
$U$ of $1$ set $p_U(K)=N(K,U)/N(K_0,U)$. The denominator is a positive
integer because $K_0$ is nonempty and a cover exists. Its nonempty
interior will also allow translates of $K_0$ to cover *other* compact sets.

**Lemma 15.10a (uniform bounds and small-scale additivity) [Lean, read].**
For each compact $K$, the counts satisfy $0\le p_U(K)\le N(K,K_0)$ and $p_U(K_0)=1$.
They are monotone, left invariant, vanish on the empty set and are
subadditive on unions of two compact sets. If $G$ is Hausdorff and
$K,L$ are disjoint compact sets, then $p_U(K\cup L)=p_U(K)+p_U(L)$
for every sufficiently small $U$.

**Proof.** Replace each translate of $K_0$ in a minimum cover of $K$
by the corresponding translate of a minimum $U$-cover of $K_0$.
This gives $N(K,U)\le N(K,K_0)N(K_0,U)$, including possible duplicate
translates. Inclusion lets a cover of the larger set cover the smaller.
Left multiplication by $g$ sends a cover to a cover of the same size,
and $g^{-1}$ gives the reverse inequality. The empty family covers
the empty set. The union of two minimum families proves subadditivity.

For additivity, the indices of translates $gU$ that meet $K$ lie in
$KU^{-1}$. If $KU^{-1}$ and $LU^{-1}$ are disjoint, separate a minimum
cover of $K\cup L$ into the subfamilies meeting the two sets. Their sizes
are at least $N(K,U)$ and $N(L,U)$, and their sum is at most the size
of the original family. To find an appropriate neighborhood, choose
disjoint opens $O_K,O_L$ around the compact sets. Such separation follows
by separating pairs of points and using compactness twice, first over
$L$ for each point of $K$, then over $K$. For each $x\in K$, continuity
of multiplication at $(x,1)$ gives open neighborhoods $A_x$ of $x$
and $W_x$ of $1$ with $A_xW_x\subseteq O_K$. Finitely many $A_x$
cover $K$. Intersect the associated $W_x$ to get $W_K$ with
$KW_K\subseteq O_K$. Obtain $W_L$ in the same way. For
$U\subseteq(W_K\cap W_L)^{-1}$ the two sets of indices are disjoint.
$\square$

**Lemma 15.10b (a common cluster point) [Lean, read].**
There is a finite-valued function $c$ on the compact sets with the
normalization, monotonicity, invariance and subadditivity above, and
with additivity on disjoint compact sets in a Hausdorff group.

**Proof.** Give the functions on the set of compact subsets the product
topology and put
$P=\prod_{K\text{ compact}}[0,N(K,K_0)]$. Tychonoff's theorem makes
$P$ compact. For each open identity neighborhood $V$, let $F_V$ be
the closure of $\{p_U:1\in U\subseteq V,\ U\text{ open}\}$.
For finitely many $V_i$, the function $p_{\cap_i V_i}$ belongs to $P$
and to every $F_{V_i}$. The empty finite family can use $p_G$. Compactness
gives $c\in P\cap\bigcap_V F_V$.

The evaluation $f\mapsto f(K)$ is continuous. Each equation or weak
inequality of Lemma 15.10a describes a closed subset of the product,
since it concerns a finite linear combination of evaluations. For
normalization, monotonicity, invariance and subadditivity use $F_G$.
For additivity of a particular disjoint pair use $F_V$ for the
neighborhood supplied by Lemma 15.10a. This proves all the relations
for the same $c$. The construction allows arbitrary neighborhood
systems and chooses a point in the intersection of tail closures.
$\square$

**Definition 15.11 (from content to outer measure).**
Call a finite nonnegative function $c$ with these compact-set relations
a content for this construction. Put
$I(O)=\sup\{c(K):K\subseteq O,\ K\text{ compact}\}$ for open $O$ and
$m^\ast(A)=\inf\{I(O): A\subseteq O,\ O\text{ open}\}$ for every subset
$A$. These two operations take values in $[0,\infty]$. The empty compact
set contributes zero to every supremum. For any compact $K$,
$m^\ast(\operatorname{int}K)\le c(K)\le m^\ast(K)$ once the
agreement $m^\ast(O)=I(O)$ on opens is established.

**Lemma 15.11a (open covers and Borel measurability) [Lean, read].**
On a Hausdorff space the preceding content construction yields an
outer measure, agrees with $I$ on opens and makes every Borel set
Carathéodory measurable.

**Proof.** Suppose a compact $K$ is contained in a countable union of
opens $O_i$. Extract a finite subcover. To use subadditivity of $c$,
shrink this subcover *inside* $K$. For each point of $K$ choose an
index of an open set containing it and choose a relative neighborhood
whose closure in $K$ stays in $K\cap O_i$. This uses regularity of
the compact Hausdorff space $K$, which follows by separating the
point from the compact complement. Finitely many such neighborhoods
cover $K$. For each index take the union of the assigned closures,
yielding compact pieces $K_i\subseteq K\cap O_i$ whose union is $K$.
Hence $c(K)\le\sum_i c(K_i)\le\sum_i I(O_i)$. Taking the supremum
proves countable subadditivity of $I$ on opens. The outer measure in
the pin starts with countable covering costs. Those costs reduce to a
single open superset because a countable union of opens is open and
its cost is at most the sum. Directly, if $\sum_i m^\ast(A_i)<\infty$,
choose opens $O_i\supseteq A_i$ with
$I(O_i)<m^\ast(A_i)+\varepsilon 2^{-i-1}$ for $i\ge0$. Their union bounds
$m^\ast(\bigcup_i A_i)$ by the sum plus $\varepsilon$. An infinite
sum gives the inequality immediately. Monotonicity and the empty-set
axiom follow from the defining infimum. For open $O$, monotonicity of
$I$ gives $m^\ast(O)=I(O)$.

To test an open set $B$ for measurability, first split an open test
set $O$. For any compact $L\subseteq O\cap B$, the set $O\setminus L$
is open and contains $O\setminus B$. For every compact
$M\subseteq O\setminus L$, disjoint additivity yields
$c(L)+c(M)=c(L\cup M)\le I(O)$. Take the supremum over $M$ to get
$c(L)+m^\ast(O\setminus B)\le I(O)$. Taking the supremum over $L$ now
gives $m^\ast(O\cap B)+m^\ast(O\setminus B)\le m^\ast(O)$, including
infinite values. For an arbitrary test set $A$, monotonicity bounds
the two split terms by the same terms for every open $O\supseteq A$.
Taking the infimum gives the Carathéodory inequality for $A$. The
reverse inequality is subadditivity. The [Carathéodory sets](#15436-from-outer-measure-to-a-countably-additive-measure) form a
$\sigma$-algebra on which the outer measure is countably additive.
Since it contains the opens, restriction yields a Borel measure $m$.
$\square$

**Theorem 15.12 (existence with specified scale) [Lean, read].**
Let $G$ be a locally compact Hausdorff topological group with the
Borel $\sigma$-algebra. For any compact $K_0$ with nonempty interior,
the preceding construction followed by division by $m(K_0)$ gives a
regular left Haar measure $\mu$ with $\mu(K_0)=1$. Here regular means
outer regular on Borel sets and inner regular by compact sets on opens,
with finite mass on compact sets.

**Proof.** Translation takes compact subsets of an open set bijectively
to compact subsets of its translate and preserves $c$. Thus it
preserves $I$. It also bijects the families of open supersets, so it
preserves $m^\ast$ and its Borel restriction. For any compact $K$,
local compactness gives compact neighborhoods of its points. Finitely
many interiors cover $K$ and the union of the corresponding compact
sets is a compact $F$ with $K\subseteq\operatorname{int}F$. Consequently
$m(K)\le I(\operatorname{int}F)\le c(F)<\infty$. Outer regularity is
the defining infimum. On opens $O$, the inequality $c(K)\le m(K)$
for compact $K\subseteq O$ gives
$I(O)\le\sup_{K\subseteq O}m(K)\le m(O)=I(O)$.

In particular, $1=c(K_0)\le m(K_0)<\infty$. This makes the scalar
$1/m(K_0)$ strictly positive and finite, so it preserves invariance
and regularity. If $O$ is any nonempty open set, choose a finite cover
of $K_0$ by $n$ translates of $O$, as in Definition 15.10. Then
$1=\mu(K_0)\le n\mu(O)$, which forces $\mu(O)>0$. In the other direction,
$\operatorname{int}K_0$ has finite mass by inclusion. Finitely many of
its translates cover each compact set, giving the finite-mass
condition of the Haar interface directly. $\square$

**Where the hypotheses enter.** Local compactness supplies a compact
neighborhood of $1$, hence an admissible $K_0$. Given such a $K_0$,
its interior can be translated to give a compact neighborhood at
every point. Inside any prescribed open neighborhood of $1$, choose
a symmetric open $W$ with $W^2$ contained in that neighborhood and
$W$ contained in the interior of a compact neighborhood. Then
$\overline W\subseteq W^2$ because each translate $xW$ with
$x\in\overline W$ meets $W$. This gives a compact neighborhood basis.
The product compactness of Lemma 15.10b uses only compactness of the
coordinate intervals and the covering bounds. Hausdorffness in this
presentation is used for compact separation, compact-cover shrinking
and closedness of compact sets in the Borel argument. The pin uses a
weaker formulation: the group supplies the $R_1$ separation instance
(distinct point closures admit disjoint neighborhoods), and
`chaar_sup_eq` asks for disjoint compact sets with the second one closed.
`Content.sup_disjoint` uses both closed. In the Carathéodory argument
the pin replaces each compact $L,M$ by its compact closure inside the
corresponding open set before applying disjoint additivity. It evaluates
the measure of a compact set via its closure in
`haarMeasure_self`. For the finiteness argument
`Content.regular` uses weak local compactness, which
`PositiveCompacts.locallyCompactSpace_of_group` supplies through
$K_0$ in this application.

**Worked example 1 (the discrete group $\mathbb Z/6\mathbb Z$).**
Take $K_0=\{0,1,2\}$ in additive notation. The identity neighborhood
$\{0\}$ forces every finer neighborhood to equal $\{0\}$. Each translate
covers one point, so $N(K,\{0\})=|K|$, $N(K_0,\{0\})=3$ and the
corresponding tail closure forces $c(K)=|K|/3$. For example,
$K=\{0,4\}$ is covered by the two singletons and cannot be covered by
one. The opens $O_1=\{0,1\}$ and $O_2=\{1,4\}$ also cover it.
Their costs are $2/3$ each and their union costs $1$, as its three
points give three translates. Since every subset is compact and open,
$I(A)=c(A)$ and the open infimum equals $I(A)$. Thus $m(K_0)=1$ and
$\mu(A)=|A|/3$. The whole group has mass $2$, and probability
normalization instead gives mass $|A|/6$. The factor between the two
scales is $2$.

**Worked example 2 (the additive real line).**
Take $K_0=[0,2]$. To determine the content of $[a,a+\ell]$ for $\ell>0$,
we need estimates valid for every sufficiently small neighborhood $U$.
Fix a positive integer $q$ and let $b=2/q$. If $U\subset(-\eta/2,\eta/2)$,
a translate of $U$ meets at most one of any family of closed blocks
separated by gaps of length $\eta$. For any length $s>0$,
$\lfloor(s+\eta)/(b+\eta)\rfloor$ such blocks fit in $[0,s]$,
and $\lceil s/b\rceil$ adjoining blocks cover it. Thus
$\lfloor(s+\eta)/(b+\eta)\rfloor N([0,b],U)\le N([0,s],U)
\le \lceil s/b\rceil N([0,b],U)$.
For fixed $b$ choose $\eta>0$ small enough that the lower integer
bound is at least $\lfloor s/b\rfloor-1$ for both $s=2$ and $s=\ell>0$.
All $U\subset(-\eta/2,\eta/2)$ satisfy the estimates. Taking $q>1$
gives
$(\lfloor\ell/b\rfloor-1)/q\le p_U([a,a+\ell])
\le\lceil\ell/b\rceil/(q-1)$.
Each such closed bound passes to the cluster point. As $q\to\infty$
the two bounds converge to $\ell/2$. A singleton has content $0$ by
monotonicity inside arbitrarily short intervals.

For a numerical cover, take $U=(-1/4,1/4)$. For any open interval
unit of length $w$, the minimum for a closed interval of length
$\ell$ is $\lfloor\ell/w\rfloor+1$. The union of the covering intervals
has length at most $nw$ and contains an open neighborhood of both
endpoints, so $nw>\ell$. Conversely if $nw>\ell$, divide the closed
interval into $n$ equal pieces and center one open interval of width
$w$ at each midpoint. For $K_0$ the minimum is $5$, and for $K=[1,4]$
it is $7$. Thus this approximation gives $7/5$, with limiting
content $3/2$.
For a bounded open interval $(u,v)$, monotonicity bounds its inner
content by $c([u,v])=(v-u)/2$. Closed intervals
$[u+\varepsilon,v-\varepsilon]$ give the reverse bound as
$\varepsilon\downarrow0$. For $K=[1,4]$, the opens $(0,3)$ and $(2,5)$
both cost $3/2$. Their union $(0,5)$ costs $5/2$, while the single
open neighborhood $(1-\varepsilon,4+\varepsilon)$ costs
$3/2+\varepsilon$. Hence $3/2=c(K)\le m(K)\le3/2+\varepsilon$ for
every $\varepsilon>0$. The same upper cover of $[0,2]$ costs
$1+\varepsilon$, so $m(K_0)=1$ and $\mu(K)=3/2$. Translation and
the same shrinking-cover calculation give half the ordinary length
on every bounded interval. These intervals generate the Borel sets
and cover the line by a countable sequence of finite-mass intervals,
so $\mu$ is Lebesgue measure divided by $2$.

**Failure of a zero-mass normalization [Expository].**
Replace $[0,2]$ in the real-line construction by $\{0\}$. For every
$U=(-w/2,w/2)$, the denominator is $1$, even though the singleton has
empty interior. Now $p_U([0,2])=\lfloor2/w\rfloor+1\to\infty$.
In the putative product bound the index $N([0,2],\{0\})$ is coded as
zero because the cover family is empty. No bounded product argument
results. At the measure level, a translation-invariant measure
assigning mass $1$ to $\{0\}$ gives mass at least $n$ to $[0,2]$ for
every $n$, by taking $n$ distinct points. It cannot be finite on
compacts. Empty interior here breaks the covering comparison and
the intended scale, even with a positive denominator at every step.

**Notes and source map.** The inequalities involving compact content
refer to the unscaled $m$. The pin performs a separate normalization
after passing to a measure. Halmos §58, pp. 252–256, gives the covering ratios and the compact-product argument.
His §53, Theorem C, gives the inequalities of Definition 15.11 and explains
why the construction can change the value on a compact set. Gleason’s
Theorem 4.3, Step 9, pp. 7–8, verifies the compact-to-open comparison on
compact open sets. Van Doorn discusses the general comparison in §5,
pp. 18:12–18:13. [Halmos, scanned reprint](https://59clc.wordpress.com/wp-content/uploads/2012/05/paul_r-_halmos_measure_theory_graduate_texts_inbookfi-org.pdf)
[Gleason 2010](https://math.uchicago.edu/~may/VIGRE/VIGRE2010/REUPapers/Gleason.pdf) · [van Doorn 2021](https://doi.org/10.4230/LIPIcs.ITP.2021.18)

`Measure.haar` at line 584 is an abbreviation which chooses an
arbitrary `PositiveCompacts G` using local compactness and applies
`haarMeasure`. This is the regular comparison measure $n$ in
[§15.4.3.3, Lemma 15.7c](#15433-uniqueness-of-haar-measure-proportionality-normalization-and-the-constant-in-the-half-density-transport).
For a specified $K_0$, use `haarMeasure K₀`. The uniqueness comparison
and the scale transport are supplied by Theorem 15.8 and Corollary 15.9.
The group-specific arguments in [Chapter 9](09-heights-slopes-and-near-orthogonality.md) use this existence supply.

The paths below are relative to `Mathlib/` at
`0df444a360eaa60ab8c11dca51a86af692955474`, pinned by the Lean archive
with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
R3 here records proof-body reading. The mathematical exposition uses
the Hausdorff specialization of the topology interfaces.

| Reading | Source | Role |
|---|---|---|
| Read | `MeasureTheory/Measure/Haar/Basic.lean:88–313` | `index`, `prehaar` and the covering inequalities |
| Read | `MeasureTheory/Measure/Haar/Basic.lean:319–507` | Compact product, closed tail conditions, `chaar`, content and positive outer mass |
| Read | `MeasureTheory/Measure/Content.lean:68–77, 105–108, 116, 118–221, 229–382` | Compact-cover shrinking, open cost, Borel measurability, outer and inner regularity |
| Read | `MeasureTheory/OuterMeasure/Induced.lean:111–119, 155–203, 238–257` | Reduction of countable costs to one open superset and open Carathéodory tests |
| Read | `MeasureTheory/Measure/Haar/Basic.lean:515–585`; `Topology/Algebra/Group/Compact.lean:24–32`; `MeasureTheory/Group/Measure.lean:584–601, 635–655, 799–809` | Normalization, regularity, finite compact mass, positivity and the choice underlying `Measure.haar` |
| Read | `Topology/Algebra/Group/Basic.lean:1260–1277, 1306–1316`, `Topology/Algebra/Group/Pointwise.lean:312–323, 389–395`, `Topology/Sets/Compacts.lean:745–748` | Finite open translates, uniform thickening, group regularity and compact neighborhoods, and availability of a positive compact |
| Inherited | §§15.4.3.1–15.4.3.3 | Modulus, linear change of variables, half-density and uniqueness, including their stated hypotheses |
| Compactness and separation suppliers | [§15.4.3.7](#ch15-tychonoff-haar-content) opens Tychonoff and the common closed-tail witness. [§15.4.3.8](#ch15-preregular-compact-covers) opens `RegularSpace` to `R1Space`, `IsCompact.finite_compact_cover` and the compact separation used here. | The proof above gives the Hausdorff arguments. The linked sections trace the pinned proof bodies and list their named inputs. |
| Retained | Masullo diagonal smoothing and strip-trace claims in §§15.4.3.1–15.4.3.3 | Existing [Paper] and [Open] boundaries |

Source reading and the book build give local checks of this section.
Lean kernel verification has its own evidence record.

#### 15.4.3.5 Finite-place products from rectangles and marginals

Theorem 15.6 uses two measure identities before it can transport a half-density. The local additive moduli must multiply to give the modulus of the coordinatewise dilation, and the product of the local multiplicative measures must equal the additive product weighted by $c_S\Delta_S^{-1}$. Both identities can be tested on rectangles. The missing step is to explain when that test determines a measure on all Borel sets. For the real-coordinate calculation in Lemma 15.5a, there is a second question. Why does equality after integration in the sheared coordinate suffice to compare two full integrals?

**First example.** Over $\mathbb Q$, take the real place and the place above $5$. With $\nu_5(\mathbb Z_5)=1$, the box $[1,2]\times 5\mathbb Z_5^\times$ has additive mass $4/25$. Its multiplicative mass is $\log 2$, since the finite-place factor is a translate of the normalized unit group and the positive real factor has measure $dx/x$. The two computations use the same box. The half-density has to account for the change in both of its sides.

**Definition 15.13 (rectangles and lower marginals).** For a finite index set $I$, let $X=\prod_{i\in I}X_i$ with the product measurable structure, the least one making each evaluation $x\mapsto x_i$ measurable. Write $R(A)=\prod_i A_i$, with every $A_i$ measurable. Cylinders arise by letting unused sides be $X_i$. Write $P=\bigotimes_i m_i$ for the finite product of the measures $m_i$. A lower marginal over $J\subseteq I$ is
$$M_J f(x)=\int f(x[J\leftarrow y])\,dP_J(y),\qquad P_J=\bigotimes_{i\in J}m_i,$$
where $f$ takes values in $[0,\infty]$ and $x[J\leftarrow y]$ substitutes the coordinates in $J$. The result is constant in those coordinates of $x$. The product over an empty index set has one point, the empty tuple. Its mass is one.

**Lemma 15.13a (production and uniqueness on rectangles).** [Lean, read] Assume each $m_i$ is $\sigma$-finite. Then
$$P(R(A))=\prod_i m_i(A_i).$$
The measure $P$ is $\sigma$-finite and every measure with these rectangle values equals $P$. More generally one may use side families $\mathcal C_i$ generating the coordinate measurable structures, closed under nonempty pairwise intersections and each containing a countable cover by sets of finite $m_i$-measure. [Pinned Mathlib, `Constructions/Pi.lean:71–293`][ch15-pi] · [`MeasurableSpace/Pi.lean:66–110`][ch15-pi-generation] · [`Measure/Restrict.lean:461–503`][ch15-pi-uniqueness]

*Proof.* The pinned definition starts with the cost $b(E)=\prod_i m_i(\operatorname{pr}_i E)$, using the outer measures of the factors on arbitrary projections. It takes the largest outer measure dominated by this cost. Equivalently take the infimum of the cost sums of countable covers. Here the cost of the empty set can be taken to be zero, including in the empty-index case. This preserves the same outer measure. A nonempty set lies in the box of its projections, so the equivalent maximality test is domination by the product formula on boxes. For a coordinate cylinder $C=\{x:x_i\in A_i\}$ the $i$-projection splits exactly into its intersections with $A_i$ and its complement. Each other projection of either piece is contained in the original projection. Thus $b(E\cap C)+b(E\setminus C)\le b(E)$ by measurability of $A_i$ and distributivity in $[0,\infty]$. Splitting every member of a countable cover proves the Carathéodory inequality for the outer measure. The reverse is subadditivity. Hence the outer measure [restricts to a measure](#15436-from-outer-measure-to-a-countably-additive-measure) on the product measurable structure. This is the path through `OuterMeasure.pi`, `pi_caratheodory` and `Measure.pi`. [`OuterMeasure/OfFunction.lean:247–279`][ch15-cover-cost] · [`OuterMeasure/Caratheodory.lean:195–224`][ch15-cover-split]

The upper bound on a box follows from its cost, with the empty box handled by the zero measure of the empty set. For the lower bound, enumerate $I$ without repetition. Build a measure by iterating the binary product along this list, starting with the unit mass on the empty tuple, then carry it to $X$ by the measurable coordinate equivalence. At every step the binary rectangle formula applies because the tail product is $\sigma$-finite, hence s-finite (a countable sum of finite measures). Indeed binary products of countable finite-measure exhaustions give a countable finite-measure exhaustion, starting here with a single point. The resulting measure has the asserted value on every measurable box by induction. The pinned helper `pi'_pi` in fact evaluates even boxes with arbitrary sides, using the outer-measure values of the measures. This stronger fact lets `OuterMeasure.le_pi` compare its outer measure with the canonical one on all boxes. Hence the auxiliary product gives the reverse inequality in `pi_pi_aux`. In the classical measurable-box argument, the same comparison on arbitrary boxes follows by enlarging each side to a measurable hull of the same outer measure, applying the measurable box formula there, and using monotonicity. [Binary product and its rectangle formula, `Measure/Prod.lean:169–247`][ch15-binary]

For uniqueness, the rectangles with sides in $\mathcal C_i$ are a $\pi$-system with the empty intersection treated separately. They are measurable because they are finite intersections of cylinders. Conversely, a cylinder from the coordinate generator in position $i$ is a countable union of these boxes. Fix the prescribed side in position $i$ and use the countable cover in every other coordinate. A finite tuple of natural-number indices ranges over a countable set. This gives the two inclusions for `generateFrom_eq_pi`. Taking side covers in all positions also supplies countably many finite-mass boxes $B_n$ covering $X$. With all measurable sides one can choose increasing finite side exhaustions and use their diagonal products. The pinned `FiniteSpanningSetsIn.pi` enumerates tuples even for general side families, using measurable hulls for the finite-mass bound.

If $Q$ agrees on the rectangles, restrict $P$ and $Q$ to a single $B_n$. They have the same finite total and agree on each generating rectangle since its intersection with $B_n$ is another generating rectangle or empty. The measurable sets on which the restrictions agree form a Dynkin system. For complements subtract from the common finite total, and for disjoint countable unions use countable additivity. The $\pi$–$\lambda$ theorem gives equality of restrictions. To recover the measures on all of $X$, split the cover into disjoint pieces $B_n\setminus\bigcup_{k<n} B_k$ and sum. This is the finite cancellation in `ext_of_generateFrom_of_cover` and the subsequent assembly of equal restrictions. Only the reference measure needs an assumed finite spanning family. The competitor inherits the same masses from rectangle agreement. For all measurable sides this is `Measure.pi_eq`. The pinned proof then identifies the list product with the canonical product and obtains `pi_pi`. $\square$

**Lemma 15.13b (block integration and order).** [Lean, read] Let the factors be as in Lemma 15.13a. Reindexing by a bijection transports the product to the product of the relabelled measures. Splitting into two disjoint coordinate blocks identifies their product with the product on the union. If measurable $f,g:X\to[0,\infty]$ have $M_J f=M_J g$ pointwise, their full lower integrals agree. [Pinned Mathlib, `Constructions/Pi.lean:730–739`][ch15-pi-blocks] · [`Constructions/Pi.lean:781–788, 824–835, 893–901`][ch15-pi-glue] · [`Integral/Marginal.lean:78–156, 187–196, 220–239`][ch15-marginal]

*Proof.* Each map and its inverse is measurable because evaluations are measurable. Its rectangle preimages have the same factors in a different order or split into two boxes. The binary rectangle formula and commutative multiplication therefore give the right masses under the map. Lemma 15.13a identifies the resulting measure. In the pin, the glue map for a disjoint union of finite sets uses the sum-type decomposition and then relabels the disjoint sum by the finite union.

For disjoint $J,L$, transport $P_{J\cup L}$ to $P_L\otimes P_J$. Substituting into the two disjoint blocks commutes. Binary Tonelli for the nonnegative measurable integrand therefore gives $M_{J\cup L}f=M_L(M_J f)$. The inner integral is measurable by parametric lower integration, applied to the measurable substitution map. With $L=I\setminus J$, the marginal over the full index set is the constant full integral, since substituting all coordinates no longer uses $x$. The pin rewrites with `lmarginal_univ`, using the index equivalence from the full finite subtype to $I$, and applies `lmarginal_eq_of_subset` with the complementary block. If $X$ itself is empty, both integrals are zero, the other branch of `lintegral_eq_of_lmarginal_eq`. If $J$ is empty, its marginal is $f$ by integration against the unit atom. A singleton marginal is the ordinary lower integral in the updated coordinate, by the measure-preserving equivalence of a singleton-indexed product with its factor. Iterating the block formula gives any order of nonnegative integration, with no requirement that the full integral be finite. $\square$

**Where §15.4.3.2 uses these lemmas.** In `Real.smul_map_diagonal_volume_pi`, the candidate is the rescaled pushforward. Its preimage of a box is the box of coordinate preimages, so the local factors are compared by `volume_pi_pi` and equality of measures is supplied by `pi_eq`. In `Real.volume_preserving_transvectionStruct`, `pi_eq` again reduces measure preservation to a box. The mapped mass becomes the integral of the box indicator composed with the map. The proof compares its singleton marginal along the changed coordinate with that of the original indicator and invokes `lintegral_eq_of_lmarginal_eq` to restore the full integral. These are separate uses of uniqueness and Tonelli. The determinant argument itself is Lemma 15.5a. [Pinned Mathlib, `Measure/Lebesgue/Basic.lean:364–408`][ch15-product-consumers]

**Theorem 15.14 (finite-place modulus and half-density).** Let $S$ be a finite set of places of a number field, $K_S=\prod_{v\in S}F_v$ and $G_S=\prod_{v\in S}F_v^\times$. Use the local additive Haar measures $\nu_v$ from §15.4.3.1, with finite-place integer rings of mass one. Let $\rho_v$ be the restriction of $\nu_v$ to $F_v^\times$, and use the local multiplicative Haar measures $\mu_v=c_v\Delta_v^{-1}\rho_v$, where $c_v=1$ at infinity and $c_v=q_v/(q_v-1)$ at a finite place of residue size $q_v$. Put $\nu_S=\bigotimes_v\nu_v$, $\mu_S=\bigotimes_v\mu_v$, $c_S=\prod_v c_v$ and $\Delta_S(x)=\prod_v\Delta_v(x_v)$. Then:

1. The additive and multiplicative products are Haar measures, and their values on rectangles fix their normalization. The complement of $G_S$ has additive measure zero.
2. For $t\in G_S$ and $D_tx=tx$, the pushforward on $K_S$ is $(D_t)_*\nu_S=\Delta_S(t)^{-1}\nu_S$. Equivalently a Borel set $E$ has $\nu_S(tE)=\Delta_S(t)\nu_S(E)$.
3. On $G_S$, letting $\rho=\nu_S|_{G_S}$, one has
$$d\mu_S=c_S\Delta_S^{-1}\,d\rho.$$
The map $U_Sg=c_S^{-1/2}\Delta_S^{1/2}g|_{G_S}$ is a unitary isomorphism from $L^2(K_S,\nu_S)$ to $L^2(G_S,\mu_S)$. The conjugate of multiplicative precomposition by $D_t$ is $g(x)\mapsto\Delta_S(t)^{1/2}g(tx)$.
4. These statements hold for the empty product. For nonempty $S$, the condition that $g\mapsto\Delta_S(t)^a g(tx)$ be isometric for every $t$ forces $a=1/2$.

*Proof.* Local fields and their multiplicative groups are second-countable locally compact Hausdorff. In these finite products, the Borel and product measurable structures agree. Evaluations are continuous, and every open set is a countable union of basic open rectangles using countable bases in the factors. Each factor has a countable cover by relatively compact open sets, obtained from local compactness and second countability, and Haar finiteness on compact sets makes these covering sets finite in measure. Thus each factor is $\sigma$-finite. The product is $\sigma$-finite by Lemma 15.13a. Compact subsets of the product lie in boxes of their compact projections, which have finite masses, so the product is finite on compact sets. Products of relatively compact neighborhoods give local finiteness at each point. Conversely local finiteness alone on an arbitrary space supplies no countable exhaustion. An uncountable discrete space with counting measure is locally finite and fails $\sigma$-finiteness.

For translations on the additive group and multiplications on the multiplicative group, inverse images of rectangles have the same factor masses. The defining uniqueness applies to the translated measure. Any nonempty open set contains a nonempty open rectangle of positive mass. These facts give Haar invariance, compact finiteness and positivity on opens. The same rectangle argument gives inversion invariance of $\mu_S$ using its local version. For the restriction, the set $x_v=0$ is a box whose $v$-mass is zero, so its product mass is zero even if other factors have infinite mass. The complement of $G_S$ is the union of these finitely many boxes. The restricted measure has on boxes in $G_S$ the values $\prod_v\rho_v(A_v)$, so it is their product by uniqueness.

The given local modulus identity says $\nu_v(t_v^{-1}A_v)=\Delta_v(t_v)^{-1}\nu_v(A_v)$. The inverse image under $D_t$ is exactly the product of these inverse sides. Multiplying the equalities shows that $\Delta_S(t)(D_t)_*\nu_S$ has the same rectangle values as $\nu_S$. Use Lemma 15.13a and divide by the positive finite scalar. Evaluating the pushforward formula on $tE$ gives the image formula.

For the product density, write $w_v=c_v\Delta_v^{-1}$, so $w=\prod_v w_v$. The measure $w\rho$ on a box has mass
$$\int \prod_v (1_{A_v}w_v)(x_v)\,d\rho(x)=\prod_v\int_{A_v} w_v\,d\rho_v=\prod_v\mu_v(A_v).$$
The first equality follows by Lemma 15.13b and successively pulling out the factors independent of the integration variable. In extended nonnegative arithmetic, a zero factor multiplies infinity to zero. If one side integral vanishes, its factor is zero almost everywhere, and the full integral vanishes as well by the zero-mass cylinder calculation. Thus the equality holds for arbitrary Borel sides. The second equality is the single-place density identity. Rectangle uniqueness now gives $w\rho=\mu_S$. In particular the constant in this identity uses one $c_v$ for each finite place. For a purely finite set the product of integer unit groups has multiplicative mass one.

The measures $w\rho$ and $\rho$ have the same null sets since $w$ is strictly positive and finite. The single-measure density integral formula gives the squared norm of $w^{-1/2}g$ as $\int |g|^2\,d\rho$. Multiplication by $w^{1/2}$ is its inverse, with extension from $G_S$ across the additive null set. This is Lemma 15.5d applied to the density just constructed. Taking the ratio of the multipliers at $tx$ and $x$ gives $\Delta_S(t)^{1/2}$, and precomposition on $L^2(\mu_S)$ is unitary by multiplicative invariance. For exponent $a$, the pushforward gives the squared norm ratio $\Delta_S(t)^{2a-1}$ on every nonzero $g$. With $S$ nonempty one can select a coordinate with modulus different from one, such as a uniformizer at a finite place or a dilation by $2$ at infinity, and use identity in the other coordinates. A nonzero $g$ exists by testing a finite positive-mass box. The ratio is one for all $t$ precisely at $a=1/2$. [Masullo, p. 518][ch15-product-masullo] $\square$

**Two computations.**

1. *The real and $5$-adic places of $\mathbb Q$.* For $R=[1,2]\times U_1$, $U_j=5^j\mathbb Z_5^\times$, the additive sides have masses $1$ and $5^{-1}(1-5^{-1})=4/25$. Take $t=(2,5)$. The image $[2,4]\times U_2$ has additive mass $2\cdot4/125=8/125$, which is $(2/5)(4/25)$. The preimage of $R$ is $[1/2,1]\times U_0$ and has mass $(1/2)(4/5)=2/5=(5/2)(4/25)$. The multiplicative measure on each shell is one and the interval integral is $\int_1^2 dx/x=\log 2$. On $R$ the squared multiplier of $U_S$ is $(4/5)(x/5)=4x/25$. For $g=1_R$ its norm after transport is
   $$\|U_Sg\|^2=\frac{4}{25}\int_1^2 x\,\frac{dx}{x}\,\mu_5(U_1)=\frac{4}{25}=\|g\|^2.$$
   The dilation sends $g$ to $(2/5)^{1/2}1_{D_t^{-1}R}$, of squared norm $(2/5)(2/5)=4/25$.

2. *The complex place and the place above $(1+i)$ of $\mathbb Q(i)$.* This prime has residue size two. Put $\varpi=1+i$ in the finite completion, and use $V_j=\varpi^j\mathcal O_v^\times$. Let $A=\{z:1\le |z|\le 2\}$ and $R=A\times V_1$. The side masses are $3\pi$ in planar Lebesgue measure and $2^{-1}-2^{-2}=1/4$, so $\nu_S(R)=3\pi/4$. Take $t=(1+i,\varpi)$. Its two moduli are $2$ and $1/2$. The image has radii $\sqrt 2,2\sqrt 2$ and finite shell $V_2$, so its additive mass is $6\pi/8=3\pi/4$. The preimage has radii $1/\sqrt 2,\sqrt 2$ and shell $V_0$, so its mass is $(3\pi/2)(1/2)=3\pi/4$. With $c_S=2$, the squared multiplier on $R$ is $r^2/4$ at $r=|z|$. The complex multiplicative measure is $dr\,d\theta/r$ in polar coordinates and $\mu_v(V_1)=1$. Consequently
   $$\mu_S(R)=2\pi\log 2,\qquad
   \|U_S1_R\|^2=\frac{2\pi}{4}\int_1^2 r\,dr=\frac{3\pi}{4}.$$
   The dilation for this particular $t$ has multiplier one. It preserves even the additive rectangle mass because the two local moduli cancel. A different dilation, with only the complex coordinate scaled, still tests uniqueness of the exponent.

**Remarks.** For $S=\varnothing$, the full rectangle is the singleton and $\nu_S=\mu_S$ is its unit atom. The empty tuple serves as additive zero and as multiplicative identity in their respective groups. The only coordinate map is the identity, $\Delta_S=c_S=1$, and the norm of a constant value $b$ is $|b|$. Every exponent gives the same isometry. The empty set describes the endpoint of the finite-product theorem.

**Tamagawa normalization [Paper].** The book uses $dx\,dy$ at a complex place and $\nu_v(\mathcal O_v)=1$ at every finite place. Write $\nu_v^{\mathrm{Tam}}=a_v\nu_v$ for Masullo's additive measure. Definition A.3.1.2 (p. 556) gives $a_v=1$ at a real place, $a_v=2$ at a complex place, and $a_v=N(\mathfrak d_{F_v/\mathbb Q_p})^{-1/2}$ at a finite place of residue characteristic $p$, with $\mathfrak d$ the local different. The finite factor is one at an unramified place. Definition A.3.2.2 and Lemma A.3.2.3 (p. 560) give $\mu_v^{\mathrm{Tam}}=a_v\mu_v$. Thus $c_S=\prod_{v\in S_f}q_v/(q_v-1)$ has the same value in the Tamagawa density formula when both measures are taken in Tamagawa scale. The finite unit mass in that scale is $a_v$, which accounts for the denominator $\mu_v^{\mathrm{Tam}}(\mathcal O_v^\times)$ in (12.5.1.2). In the complex example the two factors $2$ and $1/2$ cancel in the product. The Tamagawa side masses of the original rectangle are $6\pi$ and $1/8$. [Masullo, pp. 518, 519, 556 and 560][ch15-product-masullo]

**The choice of $S$ in the trace formula [Paper].** In the proof on p. 520, $S$ is finite and contains all archimedean places, all places ramified over $\mathbb Q$, and all places where the character $\chi$ is ramified. It satisfies $\operatorname{Pic}(\mathcal O_{F,S})=1$. For $K=\operatorname{supp}\phi$ it is large enough that $|K|_F\subset (1/T,T)$ for some $T<N(\mathfrak p_v)$ at every finite $v\notin S$. The test function $\phi$ is invariant under left translation by the image in $C_F$ of $\prod_{v\notin S}\mathcal O_{F_v}^{\times}$. The two rectangle examples satisfy the conditions on places and the class group. The support and invariance conditions are on the test function. [Masullo, p. 520][ch15-product-masullo-520]

The finite spanning family is essential for the general box uniqueness statement. On $X=Y=[0,1]$ use counting measure in the first coordinate and Lebesgue measure $\lambda$ in the second. On Borel sets $E$, set $P(E)=\sum_{x\in[0,1]}\lambda(E_x)$, where the sum is the supremum of finite subsums. This is a measure, since nonnegative sums commute, or equivalently since each summand is the pushforward of $\lambda$ along its vertical inclusion and arbitrary sums of measures are measures. Set $Q=P+d_*\lambda$ with $d(x)=(x,x)$. Both give the same product values on all Borel rectangles $A\times B$. If $A$ is finite or $\lambda(B)=0$, the added term $\lambda(A\cap B)$ is zero. In every remaining case the product is infinite. However the diagonal has $P$-mass zero and $Q$-mass one. The counting factor has no countable finite-mass cover. The theorem above supplies such a cover through the factor measures and rectangle values. It needs no additional $\sigma$-finiteness assumption on the competing measure.

The product argument uses the existing single-place Haar and density formulas. Its hypotheses concern a finite product and a nonnegative marginal or an $L^2$ norm. The passage from a diagonal integral to the strip trace, the nuclearity issue on p. 451, and the $\alpha$-independence claim remain [Open] as in §15.4.3.2. For the classical binary construction and uniqueness, see Tao's Proposition 30 and Exercise 41. [Tao, *245A Notes 6*][ch15-tao-products]

[ch15-cover-cost]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/OuterMeasure/OfFunction.lean#L247-L279
[ch15-cover-split]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean#L195-L224
[ch15-pi]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Constructions/Pi.lean#L71-L293
[ch15-pi-generation]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/MeasurableSpace/Pi.lean#L66-L110
[ch15-pi-uniqueness]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Restrict.lean#L461-L503
[ch15-binary]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Prod.lean#L169-L247
[ch15-pi-blocks]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Constructions/Pi.lean#L730-L739
[ch15-pi-glue]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Constructions/Pi.lean#L781-L901
[ch15-marginal]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Marginal.lean#L78-L239
[ch15-product-consumers]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean#L364-L408
[ch15-product-masullo]: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=518
[ch15-tao-products]: https://terrytao.wordpress.com/2010/10/30/245a-notes-6-outer-measures-pre-measures-and-product-measures/#existiprod
[ch15-product-masullo-520]: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=520

#### 15.4.3.6 From outer measure to a countably additive measure

**Motivation.** In §15.4.3.4, the outer measure prices every subset using open supersets. Two disjoint sets may share the same cheapest cover. The open-set test supplies a way to cut every test set at an open set while preserving its total price. We prove how such cuts give a measure and when its values recover the original data.

**Example (a four-point space).** Partition $X=\{a,b,c,d\}$ into $P=\{a,b\}$, $Q=\{c\}$ and $R=\{d\}$ of weights $2,3,5$. Allow covers by unions of blocks, priced by the sum of their weights. Each cover pays at least once for every block meeting the set being covered. The union of just those blocks attains this lower bound. For the four possible intersections with $P$, in order $\varnothing,\{a\},\{b\},P$, the four price rows, according to whether the remainder is $\varnothing,\{c\},\{d\},\{c,d\}$, are $(0,2,2,2)$, $(3,5,5,5)$, $(5,7,7,7)$ and $(8,10,10,10)$.

Every cut along a union of blocks assigns each block meeting a test set to exactly one side. A cut separating $a$ from $b$ fails on the test set $P$, where $2<2+2$. Thus exactly eight sets are measurable, with masses $0,2,3,5,5,7,8,10$ for $\varnothing,P,Q,R,P\cup Q,P\cup R,Q\cup R,X$. The disjoint sequence $P,Q,R,\varnothing,\ldots$ has finite union masses $0,2,5,10,10,\ldots$ starting at the empty union, with supremum $2+3+5=10$. Deleting measurability from disjoint additivity gives the strict counterexample $m(\{a,b\})=2<4=m(\{a\})+m(\{b\})$. [Expository]

**Definition.** An outer measure $m:\mathcal P(X)\to[0,\infty]$ is monotone, vanishes on the empty set and is countably subadditive. A set $A$ belongs to the Carathéodory class $\mathcal C_m$ if, for **every** $T\subseteq X$, $m(T)=m(T\cap A)+m(T\setminus A)$. Subadditivity gives $m(T)\le m(T\cap A)+m(T\setminus A)$, so the test is the reverse inequality. [Lean, read] [OuterMeasure/Caratheodory.lean:53–70](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean#L53-L70)

**Lemma (finite cuts).** The class contains the empty set and is closed under complements, finite unions and differences. For pairwise disjoint $A_i\in\mathcal C_m$ and $U_N=\bigcup_{i<N}A_i$, every $T\subseteq X$ satisfies $m(T\cap U_N)=\sum_{i<N}m(T\cap A_i)$.

*Proof.* The empty cut has sides $\varnothing$ and $T$, and complementation exchanges the two terms in the test. For $A,B\in\mathcal C_m$, split $T$ at $A$ and split both pieces at $B$. The four masses sum to $m(T)$. Apply the same cuts to $T\cap(A\cup B)$; this gives the same three pieces inside the union and the empty set as fourth piece. The fourth piece of $T$ is $T\setminus(A\cup B)$. Grouping the terms proves the test for the union. De Morgan's law gives intersections, hence differences. For the finite sum start at $U_0=\varnothing$ and split $T\cap U_{N+1}$ at $A_N$. Disjointness gives the pieces $T\cap A_N$ and $T\cap U_N$, so induction proves the identity. [Lean, read] [OuterMeasure/Caratheodory.lean:62–134](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean#L62-L134)

**Theorem (Carathéodory restriction).** For every outer measure on any set, $\mathcal C_m$ is a $\sigma$-algebra. On every $\sigma$-algebra $\mathcal A\subseteq\mathcal C_m$, the assignment $\mu(A)=m(A)$ for $A\in\mathcal A$ defines a measure.

*Proof.* For a disjoint sequence in the lemma put $U=\bigcup_i A_i$. Subadditivity and the finite identity give $m(T\cap U)\le\sum_i m(T\cap A_i)=\sup_N m(T\cap U_N)$. For every $N$, the finite union is measurable and
$m(T\cap U_N)+m(T\setminus U)\le m(T\cap U_N)+m(T\setminus U_N)=m(T)$.
Addition of a fixed extended nonnegative number commutes with the supremum of this nonempty sequence: for a finite addend translate the supremum, and for an infinite addend both sides are infinite. Thus $m(T\cap U)+m(T\setminus U)\le m(T)$. For an arbitrary sequence $B_i$ of measurable sets, the measurable differences $B_i\setminus\bigcup_{j<i}B_j$ are disjoint and have the same union, since every point has a first index. This proves countable union closure.

For pairwise disjoint $A_i\in\mathcal A$, subadditivity gives the upper bound $m(U)\le\sum_i m(A_i)$. For the lower bound, the finite identity at $T=X$ gives $\sum_{i<N}m(A_i)=m(U_N)\le m(U)$ for every $N$. Taking the supremum proves equality and the empty-set axiom completes the proof, including infinite masses. [Lean, read] [OuterMeasure/Caratheodory.lean:126–192](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean#L126-L192)

**Remark (the formal measure).** Mathlib packages the cut class as **caratheodoryDynkin** and uses intersection closure in **DynkinSystem.toMeasurableSpace**. **OuterMeasure.toMeasure** supplies the empty-set value and disjoint-union equality to **Measure.ofMeasurable**. The resulting Lean measure evaluates arbitrary subsets via the underlying outer measure **trim**, whose value on $T$ is the infimum of $m(A)$ over $T\subseteq A\in\mathcal A$. Indeed the union of a countable measurable cover is a measurable superset of cost at most the sum, and each measurable superset is itself an admissible cover. For $T\in\mathcal A$ its own cover and monotonicity give equality. [Lean, read] [Measure/MeasureSpace.lean:773–798](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/MeasureSpace.lean#L773-L798) · [Measure/MeasureSpaceDef.lean:120–140](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean#L120-L140) · [OuterMeasure/Induced.lean:311–356](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/OuterMeasure/Induced.lean#L311-L356)

**Lemma (agreement with cover costs).** Let $\mathcal D$ contain $\varnothing$ and let $p:\mathcal D\to[0,\infty]$ have $p(\varnothing)=0$. For each $T\subseteq X$ let $m(T)$ be the infimum of $\sum_i p(D_i)$ over sequences in $\mathcal D$ covering $T$, with empty infimum $\infty$. Then $m$ is an outer measure. For each $D\in\mathcal D$, $m(D)=p(D)$ exactly when every allowed cover of $D$ costs at least $p(D)$. To recover this equality as a measure value on its domain also require $D\in\mathcal A\subseteq\mathcal C_m$. If every member $D$ of $\mathcal D$ splits at $S\subseteq X$ into two allowed pieces of combined price at most $p(D)$, then $S\in\mathcal C_m$.

*Proof.* The all-empty cover gives zero and a cover of a larger set also covers a smaller one. When $\sum_i m(T_i)<\infty$, cover each $T_i$ within $\varepsilon/2^{i+1}$ of its infimum, enumerate the double sequence as a single cover, and let $\varepsilon$ decrease to zero. This gives subadditivity, whose infinite right side is automatic. A cover by $D$ padded with empty sets gives $m(D)\le p(D)$; the lower bound is precisely the cover condition. For the split test, split each cover member into the two allowed pieces. The two covering sums bound $m(T\cap S)$ and $m(T\setminus S)$ and have total at most the original cover cost. Take the infimum.

In particular a premeasure on a ring, countably additive on disjoint sequences with union in the ring, satisfies both tests. For $D\subseteq\bigcup_i D_i$, the disjoint ring members $(D\cap D_i)\setminus\bigcup_{j<i}D_j$ have union $D$ and prices at most $p(D_i)$ by monotonicity from finite additivity. Cuts by ring members give two ring pieces of unchanged total price. Thus the restriction to the generated $\sigma$-algebra extends the premeasure. Finite additivity alone fails: price finite subsets of $\mathbb N$ at zero and cofinite sets at one. The singleton cover prices $\mathbb N$ at zero although its original price was one. [Lean, read] for the cover and split constructions. [Expository] for the ring deduction. [OuterMeasure/OfFunction.lean:55–119](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/OuterMeasure/OfFunction.lean#L55-L119) · [OuterMeasure/Caratheodory.lean:198–213](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean#L198-L213)

**Example (interval covers on the real line).** Allow bounded half-open intervals $[u,v)$, $u\le v$, of price $v-u$. Cutting at $(-\infty,t)$ for $u<t<v$ gives pieces of lengths $t-u$ and $v-t$. For $t\le u$ or $t\ge v$ one piece is empty. Thus all left open half-lines pass the test. Closed left half-lines are countable intersections of larger open left half-lines, and open intervals are differences of those two types. Every open set is a union of a countable family of rational open intervals. Hence the Borel sets lie in the cut class.

For $a<b$ the one-interval cover gives $m([a,b))\le b-a$. Given any cover $[a,b)\subseteq\bigcup_n[u_n,v_n)$, enlarge each member at each end by $\varepsilon/2^{n+2}$. These open intervals have total excess length $\varepsilon$. For $0<\delta<b-a$, a finite subfamily covers $[a,b-\delta]$ by compactness. Partition that segment at the finitely many covering endpoints in its interior. Assign each successive subinterval to an interval containing its midpoint. Its interior lies in that interval because there is no covering endpoint in the interior of the subinterval. The disjoint lengths assigned to each covering interval sum to at most its length. Hence $b-a-\delta\le\sum_n(v_n-u_n)+\varepsilon$. Let $\delta,\varepsilon$ decrease to zero. This proves equality and the empty case is zero.

For a concrete infinite disjoint family let $I_n=[1-2^{-n},1-2^{-(n+1)})$, $n\ge0$. Its individual masses are $2^{-(n+1)}$. The first $N$ intervals have union $[0,1-2^{-N})$ of mass $1-2^{-N}$, the telescoping sum of their masses. Their full union is $[0,1)$, of mass $1$ by the upper and lower cover bounds above. The singleton $\{1\}$ has mass zero by the covers $[1,1+2^{-N})$, so adjoining it gives $[0,1]$ of mass $1$. [Expository] [Tao, 245A Notes 1, Lemmas 6–7 and Exercise 17](https://terrytao.wordpress.com/2010/09/09/245a-notes-1-lebesgue-measure/)

**Remark (the Haar consumer).** [§15.4.3.8](#ch15-preregular-compact-covers) gives the preregular compact-cover and closed-compact content inputs used before the measure constructor. The open-set test in §15.4.3.4 gives $\operatorname{Borel}(G)\subseteq\mathcal C_m$. **Content.measure** invokes **outerMeasure.toMeasure** with **borel_le_caratheodory**. By the inherited open-cover formula, its values on open sets are $I(O)=\sup_{K\subseteq O}c(K)$ over compact $K$. For a Hausdorff space and compact $K$, $\mu(K)=\inf_{O\supseteq K}I(O)$ over open $O$, and $c(K)\le\mu(K)$. Since $c(K)$ is finite, equality is equivalent to having, for every $\varepsilon>0$, an open superset of price at most $c(K)+\varepsilon$. A sufficient condition is **ContentRegular**, meaning that $c(K)$ is the infimum of $c(K')$ over compact $K'$ with $K\subseteq\operatorname{int}K'$. Choose such $K'$ with $c(K')\le c(K)+\varepsilon$. Then $\mu(K)\le I(\operatorname{int}K')\le c(K')$ by monotonicity of the compact content. The pin also allows an $R_1$ space and uses $\mu(\operatorname{cl}K)=\mu(K)$ for compact $K$ in the lower bound. **haarMeasure** divides by the finite positive value of **haarContent.measure** on $K_0$. It requires no agreement of the original content with the measure on every compact set. The product argument in §15.4.3.5 uses the same restriction after its rectangle test, and its uniqueness is a separate finite-spanning argument. [Lean, read] [Measure/Content.lean:355–360,388–427](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Content.lean#L355-L427) · [Measure/Haar/Basic.lean:517–522](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L517-L522) · [Compact closure mass](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean#L288-L289) · [Halmos, §54, Theorem A](https://59clc.wordpress.com/wp-content/uploads/2012/05/paul_r-_halmos_measure_theory_graduate_texts_inbookfi-org.pdf)

<a id="chapter-15-companion-drafts"></a>

<a id="ch15-tychonoff-haar-content"></a>

#### 15.4.3.7 Tychonoff compactness and a single Haar content

**Motivation.** Each normalized count $p_U$ in [Lemma 15.10a](#15434-constructing-haar-measure-from-finite-covers) assigns a value to **every** compact subset of $G$. Taking a cluster value for each coordinate separately gives no reason for the resulting numbers to satisfy an identity involving several coordinates. The product topology supplies a common test: ask one $p_U$ to meet a tolerance at each of finitely many compact sets, with $U$ inside any prescribed identity neighborhood.

**Example 1 (binary tails).** In $X=\{0,1\}^{\mathbb N}$, with indices starting at zero and discrete factors, let $x^{(n)}_i=1$ for $i<n$ and $0$ otherwise. Write $F_m$ for the closure of $\{x^{(n)}:n\ge m\}$. Then $F_m$ consists precisely of the displayed tail and the all-one point $\mathbf 1$. Every cylinder about $\mathbf 1$ with finite support $S$ contains $x^{(n)}$ for $n\ge m$ and $n>\max S$ if $S$ is nonempty. Any omitted binary string either has a zero followed by a one, which gives a two-coordinate cylinder missing the entire sequence, or is $x^{(k)}$ for $k<m$, in which case its zero in coordinate $k$ excludes the tail. A finite nonempty collection of tails has witness $x^{(\max m)}$. The empty collection has witness $x^{(0)}$. For support $S=\{0,2,5\}$ the projected sequence takes the four values $000,100,110,111$, reaching $111$ at $n=6$. The full intersection of the tails is $\{\mathbf 1\}$, although no term of the sequence equals $\mathbf 1$.

**Definition 15.17 (filters and cylinders).** A proper filter $\mathcal F$ on $X$ contains $X$, is upward closed and is closed under finite intersections, and omits $\varnothing$. A point $x$ is a cluster point if every neighborhood of $x$ meets every member of $\mathcal F$. The filter converges to $x$ if it contains every neighborhood of $x$. An ultrafilter is a maximal proper filter under inclusion of its families of sets. For $q:X\to Y$, the pushed filter $q_*\mathcal F$ contains precisely the sets $B\subseteq Y$ for which $q^{-1}(B)\in\mathcal F$. A basic neighborhood of $x$ in $\prod_{i\in I}X_i$ is a cylinder $\bigcap_{i\in S}\pi_i^{-1}(O_i)$, where $S\subseteq I$ is finite and each $O_i$ is an open neighborhood of $x_i$.

**Lemma 15.17a (extension and convergence) [Lean, read].** Every proper filter extends to an ultrafilter. A proper filter is an ultrafilter exactly when for every $B\subseteq X$ it contains one of $B$ and $X\setminus B$. Pushforward preserves ultrafilters, and every cluster point of an ultrafilter is a limit.

**Proof.** In the partially ordered set of proper extensions, a nonempty chain has its union as an upper bound. Two sets in the union belong together to one chain member, so their intersection belongs to the union, and no member contains the empty set. The starting filter bounds the empty chain. Zorn's lemma gives a maximal extension. If $B$ is absent from a maximal filter, adjoining $B$ must destroy properness. Indeed, the candidate extension consists of supersets of sets $A\cap B$ with $A$ in the original filter, so there is some $A$ for which $A\cap B=\varnothing$. Upward closure gives $X\setminus B$ in the original filter. Conversely, a proper extension that adds a missing set would contain it and its complement. Pushforward preserves all the proper filter axioms by inverse image, and inverse image commutes with complement, so it also preserves the ultrafilter criterion. If a neighborhood of a cluster point were missing from an ultrafilter, its complement would belong to it and would miss that neighborhood. A limit is a cluster point of any proper filter because the intersection of two filter members is nonempty. $\square$

**Lemma 15.17b (compact subsets and filters) [Lean, read].** For a subset $C$ of a topological space $X$, the following are equivalent.

1. Every open cover of $C$ has a finite subcover.
2. Every proper filter on $X$ containing $C$ has a cluster point in $C$.
3. Every ultrafilter on $X$ containing $C$ converges to some point in $C$.

**Proof.** Suppose an open-cover compact $C$ contains no cluster point of a proper filter containing $C$. All open sets disjoint from some filter member then cover $C$. A finite subcover yields finitely many such filter members. Their intersection with $C$ belongs to the filter and misses $C$, a contradiction. Lemma 15.17a gives (3) from (2). Conversely, a limit of an ultrafilter extension of a proper filter containing $C$ clusters in the original filter, since each of its sets remains in the extension. If an open cover of $C$ has no finite subcover, the sets $C$ minus finite unions from the cover form a proper filter base, including $C$ for the empty union. Every point in $C$ has a cover neighborhood disjoint from one of these base sets. This contradicts (2). $\square$

**Theorem 15.18 (product compactness and common tail points) [Lean, read].** Let $I$ be any set and $C_i\subseteq X_i$ compact for every $i\in I$. Then $P=\prod_{i\in I} C_i$ is compact in the product topology inherited from $\prod_{i\in I} X_i$. In any topological space, if $P$ is compact and $(F_j)_{j\in J}$ is a family such that each $P\cap F_j$ is closed in $P$, then the condition $P\cap\bigcap_{j\in E}F_j\ne\varnothing$ for every finite $E\subseteq J$, including $E=\varnothing$, implies $P\cap\bigcap_{j\in J}F_j\ne\varnothing$.

**Proof.** Let $\mathcal U$ be an ultrafilter on the ambient product with $P\in\mathcal U$. For each $i$, the preimage $\pi_i^{-1}(C_i)$ contains $P$, so the ultrafilter $(\pi_i)_*\mathcal U$ contains $C_i$. Lemma 15.17b gives a point $x_i\in C_i$ to which this pushed ultrafilter converges. Choose such points for all $i$. For any basic cylinder about $x=(x_i)_{i\in I}$, each of its finitely many inverse images is in $\mathcal U$, and so is their intersection. Thus $\mathcal U$ converges to $x\in P$. Lemma 15.17b proves compactness. Taking $C_i=X_i$ gives the product theorem for spaces. For the closed-family assertion, if the full intersection in $P$ were empty, the relative opens $P\setminus F_j$ would cover $P$. A finite subcover would contradict the corresponding finite witness. $\square$

**Remarks on emptiness, separation and choice.** The empty product has one element, the empty tuple, and the empty cylinder is the whole space. One empty factor makes the product empty, hence compact, and prevents any proper ultrafilter from containing the product. A compact space may be non-Hausdorff. For example, the principal ultrafilter at either point of a two-point indiscrete space converges to both. Throughout the proof the chosen limit must belong to $C_i$, even when $C_i$ is not closed in $X_i$.

The extension lemma can be taken as the ultrafilter lemma, equivalent over ZF to the Boolean prime ideal theorem. The Zorn proof above uses full choice as a sufficient principle. For Hausdorff factors, disjoint neighborhoods would contradict the properness of an ultrafilter converging to two distinct points. The coordinate limits are therefore unique, and unique specification assembles the tuple without an additional choice principle. In particular the ultrafilter lemma suffices for the product of Haar's real intervals. Once existence is known, selecting one common $c$ for a fixed $K_0$ is an existential instantiation in the mathematical argument. The pinned library uses classical choice for its general product proof and for a noncomputable function assigning a content to each $K_0$.

For arbitrary compact spaces the product theorem itself implies full choice. Given an arbitrary family of nonempty sets $A_i$, add a distinguished point to each and equip the enlarged set with the topology in which the two blocks $A_i$ and the added singleton are clopen and indiscrete internally. Each enlarged factor is compact since at most two opens suffice. The product has the all-distinguished tuple. Require membership in the $A_i$ block one coordinate at a time. These are closed conditions, and any finite subfamily admits a tuple by finite choice, filled with the distinguished points elsewhere. Compactness and the closed-family assertion give a choice function for the original family. Kelley proved the choice implication with the cofinite topology on the enlarged factors. [Choice principles and historical attribution](https://plato.stanford.edu/entries/axiom-choice/)

**Corollary 15.19 (the compactness input to Haar content) [Lean, read].** With $G$, $K_0$ and $p_U$ as in Lemma 15.10a, let $\mathcal K$ be the set of compact subsets of $G$, and $\mathcal N$ the set of open neighborhoods of $1$. There is one $c:\mathcal K\to\mathbb R$ such that, for every $K\in\mathcal K$, $0\le c(K)\le N(K,K_0)$, and for every $V\in\mathcal N$, every finite $S\subseteq\mathcal K$ and every $\varepsilon>0$, there exists $U\in\mathcal N$ with $U\subseteq V$ and $|p_U(K)-c(K)|<\varepsilon$ for every $K\in S$. The same $c$ satisfies all content relations in Lemma 15.10b.

**Proof.** Put $P=\prod_{K\in\mathcal K}[0,N(K,K_0)]$ in $\mathbb R^{\mathcal K}$. Each interval is nonempty and compact, including $[0,0]$ for the empty compact set. Theorem 15.18 gives compactness. For $V\in\mathcal N$ put $T_V=\{p_U:U\in\mathcal N,\ U\subseteq V\}$ and $F_V=\overline{T_V}$ in the ambient product. For every finite $E\subseteq\mathcal N$, put $V_E=\bigcap_{V\in E}V$ with $V_\varnothing=G$. It is an open neighborhood of $1$. Lemma 15.10a places $p_{V_E}$ in $P$, and $V_E\subseteq V$ puts it in $T_V$ for every $V\in E$. Hence the closed-family assertion gives $c\in P\cap\bigcap_V F_V$. Membership in every closure is precisely the stated simultaneous approximation: equal-radius cylinders at finitely many coordinates form a neighborhood basis, since the minimum of finitely many positive radii is positive. The empty support imposes no constraint. Equivalently, $c$ clusters along the filter of tails indexed by neighborhoods ordered by reverse inclusion.

Fix any closed constraint on the values of $f$ which is satisfied by every $p_U$ with $U\subseteq V$. Its closed locus contains $F_V$, so $c$ satisfies it. Each linear combination of finitely many evaluation maps is continuous, and $\{0\}$, $\{1\}$ and $[0,\infty)$ are closed in $\mathbb R$. For each inclusion, each pair, or each translating element, use the appropriate row below. In the disjoint case fix the pair first. Lemma 15.10a provides a neighborhood $V$ for that pair, and $c$ already belongs to $F_V$. This proves $\exists c\,\forall$ constraints from a supply of thresholds of the form $\forall$ constraints $\exists V\,\forall U\subseteq V$. The threshold may depend on the constraint. For finitely many constraints, intersect their thresholds to get a common refinement. The pin chooses a full function before evaluating it at $K$. $\square$

| Actual consumer in `Haar/Basic.lean` | What it receives for that one function |
|---|---|
| `nonempty_iInter_clPrehaar`, `chaar` (325–352) | `isCompact_univ_pi` and `isCompact_Icc` give compactness of $P$. `IsCompact.inter_iInter_nonempty` uses $p_{V_E}$. `Classical.choose` returns a whole function. |
| `chaar_mem_haarProduct`, `chaar_mem_clPrehaar`, `chaar_nonneg` (355–366) | The two projections of the same witness specification give all coordinate bounds and all tail memberships. |
| `chaar_empty`, `chaar_self` (369–386) | $F_G$, with $f(\varnothing)=0$ and $f(K_0)=1$. |
| `chaar_mono`, `chaar_sup_le` (390–412) | $F_G$, with $f(L)-f(K)\ge0$ whenever $K\subseteq L$, and $f(K)+f(L)-f(K\cup L)\ge0$ for each pair. |
| `chaar_sup_eq` (415–446) | $F_V$, with $f(K)+f(L)-f(K\cup L)=0$ for a fixed disjoint pair. The pin assumes a topological group and asks that its second compact set be closed. The threshold is the inverse of an intersection of identity neighborhoods chosen from the two separating thickenings. In the Hausdorff specialization both compacts are closed. |
| `is_left_invariant_chaar` (449–459) | $F_G$, with $f(gK)-f(K)=0$ for every $g\in G$ and compact $K$. |
| `haarContent`, `haarContent_self`, `is_left_invariant_haarContent` (463–493) | The nonnegative real values become a content. Its operations use monotonicity, subadditivity and disjoint additivity. Normalization and invariance pass through the coercion. |

**Example 2 (a finite projection of the Haar box).** Use the additive discrete group $G=\mathbb Z/6\mathbb Z$, $K_0=\{0,1\}$, $A=\{0\}$ and $B=\{3\}$. Project to $(A,B,A\cup B,K_0,G)$. Translates of $K_0$ are adjacent pairs on the six-cycle. The bounds on this projection are $(1,1,2,1,3)$: the opposite vertices need two translates and three adjacent pairs partition the cycle. At $U=\{0,3\}$ the cosets are $\{0,3\},\{1,4\},\{2,5\}$. The cover counts in the five coordinates are $(1,1,1,2,3)$, giving $(1/2,1/2,1/2,1,3/2)$. At $U=\{0\}$ they are $(1,1,2,2,6)$, giving $(1/2,1/2,1,1,3)$. For any finite list of identity neighborhoods the singleton is a refinement. Its tail contains just $p_{\{0\}}$, which is closed in the real product. Therefore every common point has exactly the second vector. The normalization coordinate equals one throughout and the disjoint equality is enforced on the singleton tail. This calculation concerns compact-set values prior to measure extension.

**Failure boundaries.** In $\mathbb R^{\mathbb N}$ with its product topology, the closed sets $F_n=\{x:x_0\ge n\}$ have finite witnesses (take $x_0$ to be the largest chosen index and the other coordinates zero), but no common point. Their complementary cylinders form an open cover without a finite subcover. Even in the compact space $[0,1]$, the nonclosed tails $(0,1/n)$ for $n\ge1$ have finite witnesses and empty intersection, whereas the closed tails share $0$. In a two-point discrete space, the closed singleton constraints $F_0=\{0\}$ and $F_1=\{1\}$ each admit a witness, but no common witness exists. Likewise the pairs $(0,1),(1,0)$ supply zero separately in each coordinate without ever approximating $(0,0)$ in a two-coordinate cylinder of radius $1/2$. Finally, Example 2 disproves the stronger claim that disjoint additivity holds at every scale. Its coarse vector has $p_U(A\cup B)=1/2<1=p_U(A)+p_U(B)$.

**Source note.** In Lean, filter order reverses inclusion of the families of sets. Thus `f ≤ 𝓟 s` says that the filter contains $s$, and `f ≤ 𝓝 x` says it converges to $x$. Mathlib takes the proper-filter condition of Lemma 15.17b as its definition of compactness.  The pinned producer is `Topology/Compactness/Compact.lean:1167–1184`. It pushes one ultrafilter through every evaluation, applies the compactness criterion and assembles the limits via `choose`. `isCompact_univ_pi` is the direct entry used by Haar. The neighborhood calculation is `Topology/Constructions.lean:792–793` with `Order/Filter/Pi.lean:38–51`, the ultrafilter criterion is `Topology/Compactness/Compact.lean:138–151`, and the finite-intersection interface is at lines 267–299. This section explains the pinned source and the compact-product step of van Doorn's §5, pp. 11–12. Interval compactness, deeper lattice infrastructure and group separation are used as inputs. Existing [Paper] and [Open] statuses for Masullo's smoothing, strip trace and parameter independence apply as in the preceding sections. [Pinned Mathlib](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Compactness/Compact.lean#L1167-L1184) · [van Doorn](https://arxiv.org/abs/2102.07636)

**Reading and downstream use.** [Lean, read] covers the pinned filter, compactness and Haar construction bodies listed in the source ledger. The textbook proof and its examples carry same-source preliminary acceptance. The Haar constructor supplies compact-group probability in A2's `SmoothOnGVIff.lean:83–92`, `CompactHaarRightInvariantInst.lean:69–75` and `HaarSK.lean:259–274`. The next section uses this same closed-tail function with the preregular separation hypotheses. [Source ledger](../sources/SOURCES.md#ch15-tychonoff-haar-content-sources) · [§15.4.3.8](#ch15-preregular-compact-covers)

<a id="ch15-preregular-compact-covers"></a>

#### 15.4.3.8 Compact covers and contents in preregular spaces

**Motivation.** A compact set can contain one point from an indistinguishable pair while its closure contains both. Closing the pieces of an open cover can thus enlarge the set being covered. The inner-content inequality needs compact pieces whose union is exactly the original set. The Haar argument needs disjoint open neighborhoods of compact sets. These requirements use closedness at different steps.

**Opening example.** Project $G=(\mathbb Z/5\mathbb Z)\times(\mathbb Z/2\mathbb Z)$ to its first coordinate and give $G$ the inverse-image topology from the discrete quotient. The point $(0,0)$ is compact as a singleton, but its closure is the entire fiber over $0$. The singleton still fits in every open set containing that fiber. The disjoint singletons $(0,0)$ and $(0,1)$ have no disjoint open neighborhoods.

**Definition 15.20.** Write $x\sim y$ if every open set contains either both points or neither point. A set is *saturated* if it is a union of equivalence classes for $\sim$. A space is *preregular*, or $R_1$, if each pair $x\not\sim y$ has disjoint open neighborhoods. Compactness means the finite-subcover property.

**Lemma 15.20a (compact separation and closure) [Lean, read].** In an $R_1$ space $X$, every compact $K$ satisfies
$$
\overline K=\{y\in X:\exists x\in K,\ x\sim y\}.
$$
Its closure is compact and lies in every open set containing $K$. For any compact $K,L$, disjoint open neighborhoods exist exactly when there is no indistinguishable cross-pair $x\in K$, $y\in L$. In particular, $K\cap L=\varnothing$ and closedness of $L$ suffice.

**Proof.** Suppose each $x\in K$ has an open neighborhood $A_x$ disjoint from some open neighborhood $B_x$ of a fixed $y$. A finite subcover of $K$ by the $A_x$ gives their union $A$ and the corresponding finite intersection $B$ of the $B_x$. These are disjoint open neighborhoods of $K$ and $y$. If $y$ is indistinguishable from no point of $K$, the $R_1$ axiom supplies the initial neighborhoods, so $y\notin\overline K$. Conversely, if $y\sim x\in K$, every open neighborhood of $y$ meets $K$ at $x$. This proves the formula. Every open set is saturated, so any open set containing $K$ contains $\overline K$. Given an open cover of $\overline K$, take a finite subcover of $K$. Its open union contains $\overline K$, proving compactness.

If there is no indistinguishable cross-pair, apply the point-against-compact argument to each $y\in L$. This gives an open set $A_y$ containing $K$ and an open neighborhood $B_y$ of $y$ disjoint from $A_y$. Take a finite subcover of $L$ by the $B_y$, union those $B_y$, and intersect the corresponding $A_y$. Empty unions and intersections handle empty sets. Conversely, disjoint open neighborhoods distinguish every cross-pair. Every closed set is saturated, since its complement is open. Thus if $L$ is closed and disjoint from $K$, an indistinguishable cross-pair is impossible. By the closure formula the exact criterion can also be written $\overline K\cap\overline L=\varnothing$. [Pinned separation proof](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Separation/Basic.lean#L964-L1016)

**Lemma 15.20b (binary and finite compact covers) [Lean, read].** Let $K$ be compact in an $R_1$ space. If $U,V$ are open and $K\subseteq U\cup V$, then there are compact $K_U\subseteq K\cap U$ and $K_V\subseteq K\cap V$ with $K=K_U\cup K_V$. More generally, let $I$ be any index set, $T\subseteq I$ finite, and $(U_i)_{i\in I}$ a family of sets open for $i\in T$. If $K\subseteq\bigcup_{i\in T}U_i$, then there are compact sets $K_i\subseteq K\cap U_i$ for every $i\in I$ with $K_i=\varnothing$ for $i\notin T$ and $K=\bigcup_{i\in T}K_i$.

**Proof.** Put $C=\overline K$. It is compact and contained in $U\cup V$ by Lemma 15.20a. The sets $C\setminus U$ and $C\setminus V$ are closed in $X$ and compact as closed subsets of $C$. They are disjoint. Choose disjoint open neighborhoods $A,B$ containing these differences, respectively. Put $K_U=K\setminus A$ and $K_V=K\setminus B$. Each is compact as a relatively closed subset of $K$. Every point of $K$ outside $U$ lies in $A$, and every point outside $V$ lies in $B$. Moreover,
$$
(K\setminus A)\cup(K\setminus B)=K\setminus(A\cap B)=K.
$$
The ambient closedness used for separation belongs to the differences in $C$. The pieces retained in the union are taken inside $K$.

Induct on $T$, allowing the compact set to vary. If $T$ is empty, the covering assumption forces $K=\varnothing$ and all pieces are empty. For $T=\{i\}\cup T'$ with $i\notin T'$, apply the binary assertion with $U_i$ and $\bigcup_{j\in T'}U_j$. This produces $K_i$ and a compact remainder in the second open set. Apply the induction hypothesis to that remainder and $T'$, then overwrite its $i$-coordinate with $K_i$. Compactness and containment hold coordinate by coordinate and the union is $K$. [Pinned binary and finite proof bodies](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Separation/Basic.lean#L1018-L1059)

**Proposition 15.21 (two compact-content contracts) [Lean, read].**

1. A compact content $c$ assigns a finite nonnegative real to every compact subset. Assume monotonicity, binary subadditivity and equality in binary subadditivity for disjoint **closed** compact sets. Then $c(\varnothing)=0$. In an $R_1$ space its open inner content $I(O)=\sup\{c(K):K\subseteq O,\ K\text{ compact}\}$ satisfies
   $$
   I\left(\bigcup_{n\ge 0}O_n\right)\le\sum_{n\ge 0}I(O_n)
   $$
   for every sequence of open sets, and $I(O\cup P)=I(O)+I(P)$ for disjoint open sets $O,P$.
2. Let $G$ be a topological group and $M$ a compact set with nonempty interior. Let $h=\operatorname{chaar}(M)$ be the common closed-tail function of [§15.4.3.7](#ch15-tychonoff-haar-content). For every pair of compact sets $K,L$ with $K\cap L=\varnothing$ and $L$ closed, one has $h(K\cup L)=h(K)+h(L)$. The same equality follows if $K$ is the closed member, and whenever $\overline K\cap\overline L=\varnothing$.

**Proof of (1).** Apply disjoint additivity to two empty sets and cancel the finite value. Induction using binary subadditivity gives the finite-union inequality, including the empty family. For each compact $K\subseteq\bigcup_n O_n$, take a finite subcover indexed by $T$. Lemma 15.20b gives compact pieces $K_n\subseteq O_n$ with union $K$ over $T$. Therefore
$$
c(K)\le\sum_{n\in T}c(K_n)\le\sum_{n\in T}I(O_n)\le\sum_{n\ge 0}I(O_n).
$$
Taking the supremum over $K$ gives the claim. This inequality uses normalization at the empty set and binary subadditivity. For disjoint opens and arbitrary compact $A\subseteq O$, $B\subseteq P$, the closures stay in the respective opens and remain compact. Thus
$$
c(A)+c(B)\le c(\overline A)+c(\overline B)
=c(\overline A\cup\overline B)\le I(O\cup P).
$$
The two compact families contain the empty set, so the supremum over independent choices $A,B$ gives $I(O)+I(P)$, including when either supremum is infinite. Countable subadditivity applied to the two opens and empty opens gives the reverse inequality. The pinned proof of subadditivity takes the finite subcover at lines 170–171, shrinks it at 172–173, identifies the finite supremum of compact pieces at 174–178 and bounds the finite sum at 179–183. [Pinned content consumer](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Content.lean#L159-L185)

**The instance used in (2).** Regularity here means separation of a point from a closed set by disjoint open neighborhoods. If $y\notin\overline{\{x\}}$, separate $y$ from $\overline{\{x\}}$. This separates $x$ and $y$. A distinguishable pair admits an orientation with $y\notin\overline{\{x\}}$. The pinned instance uses this oriented implication with the neighborhood filter of a singleton.

The group instance produces regularity via a closed neighborhood basis. For a neighborhood $S$ of $a$, continuity at $(a,1)$ gives neighborhoods $D$ of $a$ and $E$ of $1$ with $DE\subseteq S$. If $x\in\overline D$, the open neighborhood $x(\operatorname{int} E)^{-1}$ of $x$ meets $D$. Hence $x=de$ for some $d\in D$ and $e\in\operatorname{int} E$. Thus $\overline D\subseteq S$. Taking $S$ to be the complement of a closed set, the interior of $\overline D$ and the complement of $\overline D$ give the required separation. The source writes the product step via the equality $\overline D\,\operatorname{int} E=D\,\operatorname{int} E$.

Consequently the call to compact separation in the group proof of `chaar_sup_eq` receives $R_1$ from group regularity. The theorem `innerContent_iSup_nat` takes $R_1$ directly. When `haarMeasure` calls `Content.measure` through the [Carathéodory restriction of §15.4.3.6](#15436-from-outer-measure-to-a-countably-additive-measure), the group instance also supplies $R_1$ for the outer measure construction through `innerContent_iUnion_nat`. The outer measure exists before the $R_1$ binder. Its agreement with inner content on opens consumes the countable inequality. In the Borel cut calculation the pinned proof closes both compact test sets inside the relevant open regions before invoking the two-closed content axiom. [Regular to preregular](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Separation/Regular.lean#L155-L168) · [Group regularity](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/Group/Pointwise.lean#L309-L323)

**Proof of (2).** Lemma 15.20a gives disjoint open neighborhoods $O_K,O_L$. Apply the common right-thickening result of §15.4.3.4 to each set and intersect the resulting open identity neighborhoods to obtain $V$ with $KV\subseteq O_K$ and $LV\subseteq O_L$. For every open identity neighborhood $U\subseteq V^{-1}$, the sets $KU^{-1},LU^{-1}$ are disjoint. A translating element for a translate of $U$ meeting $K$ therefore cannot translate $U$ to meet $L$. The covering-index equality of §15.4.3.4 gives $p_U(K\cup L)=p_U(K)+p_U(L)$ for the normalized ratios. The continuous real function $f\mapsto f(K)+f(L)-f(K\cup L)$ vanishes on the entire tail and hence on its closure, which contains $h$. The pin uses only closedness of the second member in `chaar_sup_eq`, then fills the two-closed content axiom using the second closedness proof. [Pinned Haar consumer](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L415-L467)

**Worked calculation 1 (non-$T_0$ group and quotient).** Return to the projection $q:G\to\mathbb Z/5\mathbb Z$. Write $F_i=q^{-1}(\{i\})$ and $F_S=q^{-1}(S)$. Open and closed sets are exactly unions of fibers. Addition and inversion are continuous because $q$ is a homomorphism and the inverse images of the quotient's fibers under addition are unions of open fiber rectangles, while inversion permutes fibers. Distinct fibers separate points, and points of one fiber are indistinguishable. Thus the quotient by indistinguishability is the discrete five-cycle. Let
$$
K=\{(0,0),(1,0),(2,0),(2,1),(3,1)\},\qquad
(O_0,O_1,O_2)=(F_{\{0,1\}},F_{\{1,2\}},F_{\{2,3\}}).
$$
The first split uses the differences $F_{\{2,3\}}$, $F_0$ of $\overline K=F_{\{0,1,2,3\}}$ from $O_0$ and $O_1\cup O_2$. They are disjoint and already open. Removing the first from $K$ gives $K'_0=\{(0,0),(1,0)\}$, and removing the second gives the remainder with image $\{1,2,3\}$. The remainder's closure has differences $F_3,F_1$ from $O_1,O_2$, respectively. Removing these from the remainder gives $K'_1=\{(1,0),(2,0),(2,1)\}$ and $K'_2=\{(2,0),(2,1),(3,1)\}$. Each piece has two quotient points and the union is exactly the five points of $K$. No family of ambient closed pieces could have this union, since every union of fibers is saturated and $K$ is missing points from its fibers.

Normalize at $M=F_{\{0,1,2\}}$. The smallest open identity neighborhood is $F_0$ and its translates are precisely the fibers. Thus the index of any subset $D$ at this scale is $|q(D)|$. The tail below $F_0$ has this single scale and its function is closed as a singleton in the real product. Therefore $h(D)=|q(D)|/3$. Compactness of all the opens here and monotonicity give $I(O_i)=2/3$, while the union has inner content $4/3$. The compact bound reads $h(K)=4/3\le 2$.

Let $A=\{(1,0)\}$ and $B=F_2$. Their values and their union's value are $1/3,1/3,2/3$. Only $B$ is closed. Adding $F_0$ gives the disjoint open neighborhoods $F_1,F_2$. At the coarser scale $U=F_{\{0,1\}}$, the denominator index is two because three quotient points cannot fit in a two-point translate, while the translates by $0,1$ suffice. One translate by $1$ covers $A\cup B$, so all three ratios are $1/2$. The additivity is a small-tail statement. For the two disjoint singletons $(1,0)$ and $(1,1)$, each value and the union value are $1/3$. Dropping the last closedness condition while retaining only set disjointness can fail. On the other hand, the singletons $(1,0)$ and $(2,0)$ have disjoint closures and satisfy the same additivity equality as $A,B$.

**Worked calculation 2 (Hausdorff real line).** Work in the additive real line with compact $K=[0,6]$ and opens
$$
O_0=(-1,3),\qquad O_1=(1,5),\qquad O_2=(4,7).
$$
The first differences from $O_0$ and $O_1\cup O_2$ are $[3,6]$ and $[0,1]$. Take disjoint neighborhoods $(5/2,7)$ and $(-1,3/2)$. The pieces are $[0,5/2]$ and $[3/2,6]$. In the remainder the differences from $O_1,O_2$ are $[5,6]$ and $[3/2,4]$. Use $(9/2,7)$ and $(1,17/4)$. The final pieces are $[0,5/2]$, $[3/2,9/2]$ and $[17/4,6]$. They lie in their prescribed opens and cover $K$. Their overlaps have lengths $1$ and $1/4$, with no triple intersection. Usual length on compact sets gives $6\le5/2+3+7/4=29/4$. The open inner values are $4,4,3$ and the union value is $8$. For any bounded open interval the upper bound is its length, and closed subintervals approaching its endpoints give the reverse supremum inequality.

For the covering ratios, normalize at $M=[0,2]$ and take $A=[0,1]$, $B=[3,5]$. A closed interval of length $d$ has index $\lfloor d/(2r)\rfloor+1$ at $U=(-r,r)$. For $d>0$, an open union of $n$ translates covering the closed interval contains a strictly larger closed interval, so $2rn>d$. Conversely, split the interval into $n$ equal closed subintervals of length $d/n<2r$ and center a translate at each midpoint. For a singleton the index is one. At $r=1/4$ the indices for $A,B,M$ are $3,5,5$. No translate can meet both $A$ and $B$ because their gap is $2$. The union index is $8$ and the ratios for $A,B,A\cup B$ are $3/5,1,8/5$. For the full tail, choose $V=(-1/2,1/2)$. Then $A+V=(-1/2,3/2)$ and $B+V=(5/2,11/2)$ are disjoint. For every open identity neighborhood $U\subseteq V$, the inverse-translating sets are contained in those intervals, so the ratio equality holds on the entire tail. In particular the closed-tail function is additive at this pair.

The actual tail coordinates are $1/2,1,3/2$. To see this for arbitrary open scales, write $N_U(d)$ for the index of $[0,d]$. Fix any integer $m\ge2$ and put $\varepsilon=1/m$. Restrict to open identity neighborhoods $U\subseteq(-\varepsilon/3,\varepsilon/3)$. Two translates of $[0,1-\varepsilon]$ at positions $0$ and $1$ sit inside $[0,2]$ with gap $\varepsilon$. Also $m$ translates of $[0,\varepsilon]$ at positions $2j\varepsilon$, $0\le j<m$, sit there with gaps $\varepsilon$. A translate of $U$ cannot meet two intervals from either family. Hence $N_U(2)\ge2N_U(1-\varepsilon)$ and $N_U(2)\ge m N_U(\varepsilon)$. Subdivision gives $N_U(1)\le N_U(1-\varepsilon)+N_U(\varepsilon)$ and $N_U(2)\le2 N_U(1)$. Dividing by $N_U(2)>0$ bounds the first coordinate between $1/2$ and $1/2+1/m$ on the entire restricted tail. These closed bounds pass to $h$ for each $m$. Translation invariance gives $h(B)=h(M)=1$, and the pairwise equality gives $h(A\cup B)=3/2$.

**Closedness in the general content axiom.** On the subspace $X'=F_1\cup F_2$ of the first model define $c(\varnothing)=0$, $c(X')=2$, and $c(D)=1$ for each proper nonempty subset. All subsets are compact. The values are monotone, a union of two nonempty sets costs at most two, and union with the empty set gives equality. The only disjoint nonempty closed pair consists of the two fibers, whose costs add to two. But for $A=\{(1,0)\}$ and $B=F_2$, the proper union costs one while the sum is two. Interchanging the sets shows failure for either deletion from the general axiom. Topologically $X'$ is the product of a discrete two-point space and an indiscrete two-point space, also realized by a topological group. The proof of the open-set equality avoids this failure by computing with closed compact enlargements. The shrinking lemma itself places no ambient closedness requirement on the input compact set or the output pieces.

**Failure without preregularity.** Use the Alexandroff extension of the rationals, a compact space with closed compact subsets recorded by Steven Clontz, Example 2.8. [Published example](https://doi.org/10.4064/cm9556-4-2026)

Let $Y=\mathbb Q$ with its usual topology and $X=Y\cup\{\infty\}$. Keep the opens on $Y$, and use $X\setminus C$ as a neighborhood basis at $\infty$ for compact $C\subseteq Y$. These are compatible because compact sets of $Y$ are closed and finite unions of them are compact. The space is compact because a single cover member containing $\infty$ leaves at most a compact subset of $Y$ to cover. Singletons are closed. Every neighborhood of $0$ contains a rational interval around $0$ that cannot fit in a compact subset of $Y$. Indeed a sequence within the interval tending to an irrational point inside it would force that irrational point into the compact subset's closed image in $\mathbb R$. Hence $0,\infty$ have no disjoint neighborhoods, even though both singletons are closed.

In fact every compact $D\subseteq X$ is closed. If $\infty\notin D$, it is compact in $Y$ and its complement is open at $\infty$ and in $Y$. If $\infty\in D$, then for each compact $C\subseteq Y$, the set $D\cap C$ is compact because $C$ is closed in $X$. Hence $D\cap C$ is closed in $C$. If $D\cap Y$ were nonclosed in $Y$, a sequence in it converging to a point of $Y\setminus D$ together with its limit would be a compact $C$ witnessing a contradiction. Thus $D$ is closed also in this case. Now the two opens $X\setminus\{0\}$ and $X\setminus\{\infty\}$ cover $X$. If subordinate compact pieces covered $X$, their complements would be disjoint open neighborhoods of $0$ and $\infty$. This refutes binary and finite compact shrinking without $R_1$, even for a closed compact set in a compact $T_1$ space.

The same cover can violate the inner-content inequality for a genuine compact content. Let $\mathcal J$ consist of the compact subsets of $X$ contained in a finite union of compact sets each subordinate to one of these two opens. This family is downward closed among compacts and closed under finite union. It contains every compact set missing either $0$ or $\infty$. It excludes $X$, because grouping the members of a finite cover into two compact unions would give the forbidden binary shrinking. Define $c(D)=0$ on $\mathcal J$ and $c(D)=1$ otherwise. This is monotone and subadditive. If two compact sets are disjoint, at most one is outside $\mathcal J$, since any such set contains both $0$ and $\infty$. When both are in $\mathcal J$ their union is there as well, and when one is outside, the union is outside by downward closure. Thus $c$ is additive even on all disjoint compact pairs. The two opens each have inner content zero, but $I(X)=c(X)=1$. This also shows why agreement of an induced outer measure with the original open cost needs more than the outer measure definition.

**Source and scope.** Halmos's *Measure Theory*, §53, Theorem A, uses the compact refinement from §50A in a locally compact Hausdorff setting. Van Doorn's *Formalized Haar Measure*, §5, Lemma 5, gives the compact-content relations and the passage through a closed locus in the product. The preregular formulation, the single closed member and the instance path here come from the pinned Mathlib bodies. The worked models and boundaries are the book's explanations. [Halmos](https://doi.org/10.1007/978-1-4684-9440-2) · [van Doorn](https://arxiv.org/pdf/2102.07636v1)

**Reading.** [Lean, read] covers the pinned compact separation, shrinking and content bodies and the listed group-instance and Haar call sites. The textbook proof and its examples carry same-source preliminary acceptance. [Source ledger](../sources/SOURCES.md#ch15-preregular-compact-covers-sources)

<a id="ch15-concentrating-kernels"></a>

#### 15.4.3.9 Why concentrating kernels recover a point value

**Motivation.** The Gaussian in the [pinned additive inversion proof][ch15-peak-consumer] becomes taller and narrower in the physical variable as the frequency damping is removed. On the physical side a positive kernel of mass one is an average. Continuity at the point controls the values it samples nearby. For an integrable input that may be unbounded elsewhere, we also need to control the kernel uniformly away from that point. The dilation formula in [§15.4.3.2](#15432-from-real-linear-haar-determinants-to-density-weighted-l2-transport) supplies the Jacobian behind the average.

**Example 1 (the normalized Gaussian on the line).** With Lebesgue measure put
$\varphi(u)=\sqrt{\pi}\,e^{-\pi^2u^2}$ and $f(x)=e^{-\pi^2x^2}$.
The Gaussian integral $\int_{\mathbb R}e^{-\pi y^2}\,dy=1$ gives $\int\varphi=1$
by $y=\sqrt{\pi}\,u$. The input is continuous and $\|f\|_1=1/\sqrt{\pi}$.
For a real scale $r>0$, the dilation has Jacobian $r$ and
$\int r\varphi(rx)\,dx=\int\varphi(u)\,du=1$. Positivity is immediate and
$|u|\varphi(u)\to0$ as $|u|\to\infty$. In fact for every $\rho>0$ the
scaled supremum on $|x|\ge\rho$ is $r\sqrt{\pi}\,e^{-\pi^2r^2\rho^2}$, while the tail mass is
$2\sqrt{\pi}\int_{r\rho}^\infty e^{-\pi^2u^2}\,du$.
For $u\ge r\rho$, bound the integrand by $u e^{-\pi^2u^2}/(r\rho)$ and integrate
the derivative of $e^{-\pi^2u^2}$. The mass is at most
$\sqrt{\pi}\,e^{-\pi^2r^2\rho^2}/(\pi^2r\rho)$.

At the origin, multiplying the two Gaussians and using
$y=\sqrt{\pi(r^2+1)}\,x$ gives
$$
 A_rf(0)=r\sqrt{\pi}\int_{\mathbb R}e^{-\pi^2(r^2+1)x^2}\,dx
 =\frac{r}{\sqrt{r^2+1}}.
$$
Since $f(0)=1$, the error is exactly
$$
 \frac{1}{\sqrt{r^2+1}(\sqrt{r^2+1}+r)}\le\frac{1}{2r^2}.
$$
The frequency damping parameter in the pinned inversion lemma is $c=r^2$,
so the last bound is $1/(2c)$ for this input. At $r=2$ the error is
$1-2/\sqrt 5$, strictly between $1/10$ and $1/9$.
[Gaussian integral in §1.2.2.7](01-statement-and-fidelity.md#1227-from-poisson-summation-to-theta-inversion)

**Example 2 (a one-sided rectangle and a vector value).** Take $F=E=\mathbb R^2$,
with the Euclidean norm on $F$, the maximum norm on $E$ and area measure on $F$.
Put $Q=[0,2]\times[-1,0]$ and $\varphi=\tfrac12\mathbf1_Q$.
It has mass $(2\cdot1)/2=1$, is nonnegative and vanishes for $\|u\|>\sqrt5$.
Set $f(x_1,x_2)=(1+x_1,2+x_2)\mathbf1_{[-3,3]^2}(x_1,x_2)$.
This input is continuous at $0$ and integrable, since its norm is bounded by $5$
on a box of area $36$. Its origin value is $(1,2)$.
The weight $r^2\varphi(r(0-x))$ is $r^2/2$ on $[-2/r,0]\times[0,1/r]$,
whose area is $2/r^2$. Thus its mass is one and both off-ball tail bounds are
zero whenever $r>\sqrt5/\rho$ for a fixed radius $\rho>0$.

For $r\ge1$ the sampling rectangle is inside $[-3,3]^2$. Integrating the first
coordinate of the displacement over $[-2/r,0]$ gives $-2/r^2$.
Multiplying by the other width $1/r$ and by $r^2/2$ gives $-1/r$.
Integrating the second coordinate over $[0,1/r]$ gives $1/(2r^2)$.
Multiplying by $2/r$ and by $r^2/2$ gives $1/(2r)$.
Hence $A_rf(0)=(1-1/r,2+1/(2r))$ and the exact maximum-norm error is $1/r$.
At $r=2$ this is the vector $(1/2,9/4)$ with error $1/2$. With $x-0$ in the
kernel instead of $0-x$, the displacement is $(1/r,-1/(2r))$.
The limit is the same and the approximating averages have different values.

**Definition 15.22 (a scaled peak and its average).** Let $F$ be any finite-dimensional
real normed vector space with Borel $\sigma$-algebra and additive Haar measure $\nu$.
Write $d=\dim_{\mathbb R}F$, which may be zero. Let $E$ be any real Banach space,
$f:F\to E$ a specified function and $x_0\in F$. Fix a real profile $\varphi:F\to\mathbb R$.
For real $r>0$ set
$$
 K_r(z)=r^d\varphi(rz),\qquad
 A_rf(x_0)=\int_F K_r(x_0-x)\,f(x)\,d\nu(x).
$$
Products of real weights and vectors denote scalar action, and the integrals of vectors
are Bochner integrals. For the tail hypothesis, the notation
$\|u\|^d\varphi(u)\to0$ at infinity means that for every $\eta>0$ there is $R>0$
such that $|\|u\|^d\varphi(u)|<\eta$ for every $u$ with $\|u\|>R$.
This is the cobounded filter in the source. The real scale tends to $+\infty$,
so only its positive tail enters the formula.

**Lemma 15.22a (dilation and concentration).** Suppose $\varphi\ge0$ at every point,
$\int_F\varphi\,d\nu=1$, and $\|u\|^d\varphi(u)\to0$ at infinity.
Then $\varphi$ is integrable, $K_r$ has unit mass for every $r>0$, and for each
$\rho>0$ both
$$
 M_r(\rho)=\int_{\|z\|\ge\rho}K_r(z)\,d\nu(z),\qquad
 D_r(\rho)=\sup_{\|z\|\ge\rho}K_r(z)
$$
tend to zero, with the supremum of the empty set here defined to be zero.
The supremum is allowed to be infinite before the eventual off-ball bound takes effect.

**Proof.** Unit integral is understood for an integrable profile. In the pinned Lean
statement, where the Bochner integral evaluates to zero on nonintegrable functions,
the equality to one itself gives integrability. The map $z\mapsto rz$ has
absolute determinant $r^d$. On measurable $B$,
$\nu(rB)=r^d\nu(B)$ and the pushforward under the dilation is $r^{-d}\nu$.
This works at every Haar normalization. Change variables to get
$\int_B K_r\,d\nu=\int_{rB}\varphi\,d\nu$. In particular the integral on $F$ is
one. Dilation preserves null sets in both directions, so the scaled profile is
almost everywhere strongly measurable. The tail $M_r(\rho)$ is exactly
$\int_{\|u\|\ge r\rho}\varphi(u)\,d\nu(u)$. For any tolerance choose an integer
$N$ such that the integral outside the closed ball of radius $N$ is below that
tolerance. Such an $N$ exists by monotone convergence of the integrals of the
nonnegative profile on the expanding balls. Every $r$ with $r\rho>N$ then
meets the tolerance, including when a sphere has positive mass.

For the supremum fix $\varepsilon>0$, choose $R$ from the tail hypothesis
with $\eta=\rho^d\varepsilon/2$, and let $r>R/\rho$. If $\|z\|\ge\rho$,
then $\|rz\|\ge r\rho>R$ and
$$
 0\le K_r(z)=\|z\|^{-d}\,\|rz\|^d\varphi(rz)<\varepsilon/2.
$$
Here $\|z\|>0$. Thus $D_r(\rho)\le\varepsilon/2$. The mass bound uses
integrability of the profile. The supremum bound uses its prescribed pointwise
decay. [Haar determinant in §15.4.3.2](#15432-from-real-linear-haar-determinants-to-density-weighted-l2-transport)

**Theorem 15.23 (pointwise recovery) [Lean, read].** For every $F,\nu,E,\varphi,f,x_0$
as above, assume all three profile hypotheses of Lemma 15.22a, that $f$ is
Bochner integrable for $\nu$, and that $f$ is continuous at $x_0$. Then the
integral defining $A_rf(x_0)$ is Bochner integrable for all sufficiently large
$r$, and $A_rf(x_0)\to f(x_0)$ in $E$ as $r\to+\infty$.
The limit is the conclusion of the pinned declaration
`tendsto_integral_comp_smul_smul_of_integrable'`.
[Pinned `Mathlib/MeasureTheory/Integral/PeakFunction.lean:452–469`][ch15-peak-reflected]

**Proof.** In additive Haar measure the affine involution $x\mapsto x_0-x$
preserves measure. Translation is Haar invariant, and the linear part $-1$
has determinant of absolute value one. Thus $h(z)=f(x_0-z)$ is integrable,
with $\|h\|_1=\|f\|_1$, and is continuous at $0$ with $h(0)=f(x_0)$.
The average is $\int_F K_r(z)h(z)\,d\nu(z)$.

Choose $\rho>0$ so that $h$ is bounded on $\|z\|<\rho$, by continuity at
zero. On that ball the integrable kernel times this bound controls the norm
of $K_rh$. On the complement the product is bounded in norm by
$D_r(\rho)\|h(z)\|$, integrable once $D_r(\rho)$ is finite. Almost everywhere
strong measurability of the factors gives the same property for the product.
Also the function $z\mapsto K_r(z)h(0)$
is integrable with norm integral $\|h(0)\|$. Subtract this weighted constant
using unit mass.

Write $\omega_h(\rho)=\sup_{\|z\|<\rho}\|h(z)-h(0)\|$ for the local
oscillation. The norm of the near integral is at most $\omega_h(\rho)$
because of nonnegativity and mass one. On the far region, the part
containing the original $h$ has norm at most
$D_r(\rho)\int_{\|z\|\ge\rho}\|h(z)\|\,d\nu(z)$.
The remaining constant part has norm $\|h(0)\|M_r(\rho)$. In particular
$$
 \|A_rf(x_0)-f(x_0)\|
 \le\omega_h(\rho)+D_r(\rho)\|f\|_1+\|f(x_0)\|M_r(\rho).
$$
Given $\varepsilon>0$, first choose $\rho>0$ so that
$\omega_h(\rho)\le\varepsilon/3$. Keep this radius fixed and take $r$ so
large that $D_r(\rho)<\varepsilon/(3(1+\|f\|_1))$ and
$M_r(\rho)<\varepsilon/(3(1+\|f(x_0)\|))$. The error is then less than
$\varepsilon$. This argument controls a varying integrand by separate
estimates on two regions. The vanishing of $K_r(z)$ at every fixed
nonzero $z$ by itself gives no integral convergence.

**Remark (how the source produces the limit).** The general supplier uses a
finite-measure window so that subtracting the value at the center preserves
$L^1$. Here is the localized argument, including the integrability step. Keep the real Banach target, so the pinned Bochner integral takes values in a complete space.
On a Borel space $X$ with measure $\mu$, let $S,T$ be measurable, with
$T\subseteq S$, $\mu(T)<\infty$, and $T$ a neighborhood of $x_0$ within $S$.
Let $g$ be integrable on $S$ and have limit $a$ within $S$ at $x_0$.
Along any filter of indices let the real weights $p_i$ be eventually
nonnegative on $S$ and almost everywhere strongly measurable there.
Assume $p_i\to0$ uniformly on $S\setminus U$ for every open $U$ containing
$x_0$, and $\int_T p_i\,d\mu\to1$.

Choose $U$ with $S\cap U\subseteq T$ and $\|g-a\|\le1$ on $S\cap U$.
Eventually $\int_T p_i\,d\mu$ is nonzero, which in Lean gives integrability
of $p_i$ on $T$. On $S\cap U$ multiply this integrable weight by the bound
$\|a\|+1$ for $g$. On $S\setminus U$ use the eventual uniform bound $1$
for the weight and integrability of $g$. The two disjoint pieces give
eventual integrability of $p_i g$ on $S$.

When $a=0$, choose $0<\delta<1$ with
$\delta\int_S\|g\|\,d\mu+2\delta<\varepsilon$. Shrink $U$ so that
$\|g\|\le\delta$ on $S\cap U$ and retain $S\cap U\subseteq T$.
Eventually the near integral has norm at most
$\delta\int_T p_i\,d\mu\le2\delta$, using nonnegativity,
and the far integral has norm at most $\delta\int_S\|g\|\,d\mu$.
Their sum tends to zero in the stated $\varepsilon$ sense.
For general $a$ apply this zero-limit case to $g-\mathbf1_Ta$.
The difference has limit zero and is integrable on $S$, since the subtracted
function has norm integral $\mu(T)\|a\|$. Eventually the weighted indicator
is integrable too, with norm integral $\|a\|\int_T p_i\,d\mu$ by nonnegativity.
Linearity and $T\subseteq S$ restore the term $(\int_T p_i\,d\mu)a$, which
tends to $a$. Taking $S=X$ gives the global version. The compact normalized powers of [§15.4.3.10](#154310-how-powers-of-a-unique-peak-concentrate-at-a-point) use the same supplier with the compact set as both the integration set and the window.

In `PeakFunction.lean` the near and far integrability bounds are at lines
56–88, the zero-limit estimate at 94–177, the window subtraction at 184–217
and the global specialization at 222–234. The origin-scaling proof at
394–446 uses the closed unit ball for $T$, a finite-measure neighborhood by
finite-dimensional compactness. The restricted change of variables
makes its mass $\int_{\|u\|\le r}\varphi(u)\,d\nu(u)$, which tends to one.
The source's expanding-ball convergence applies dominated convergence
to the unscaled profile times the indicator of the expanding ball.
Each point is eventually in the ball, and $|\varphi|$ is a fixed integrable majorant. The cobounded decay supplies uniform
smallness outside each neighborhood, as in Lemma 15.22a. Lines 452–469
apply the origin theorem to $z\mapsto f(x_0-z)$ and undo translation and
negation in the integral. The exact-mass error estimate above is a textbook
form of this argument. [Pinned localized supplier][ch15-peak-local]
[Pinned origin scaling][ch15-peak-origin]

**Remark (which hypotheses carry the value).** Remove unit mass in Example 1
by replacing $\varphi$ by $2\varphi$. It remains nonnegative with the same
decay and the original input remains integrable and continuous. The value
of the average is $2r/\sqrt{r^2+1}$, tending to $2$ instead of $f(0)=1$.
For deletion of point continuity keep the unit-mass Gaussian and use
$f=\mathbf1_{[0,1]}$ with $f(0)=1$. The average at $0$ is
$\int_0^r\varphi(u)\,du$ by evenness and scaling. By evenness its limit is
$1/2$, and the difference from $1/2$ is exactly $\int_r^\infty\varphi(u)\,du$.
Changing the single assigned value at $0$ leaves every average identical.

In dimension zero, $F=\{0\}$ and Haar measure has some finite positive mass
$m=\nu(\{0\})$. The unit-mass equation requires $\varphi(0)=1/m$.
The tail condition concerns empty sets away from zero, $r^0=1$,
and every average equals $f(0)$. This includes the zero-dimensional
case in the theorem's quantifiers.

**Remark (the actual Gaussian call and the half-density comparison).**
The existing Mathlib consumer `Real.tendsto_integral_gaussian_smul'` calls
the reflected theorem at `Mathlib/Analysis/Fourier/Inversion.lean:116`.
It uses a finite-dimensional real inner product space $V$ with its canonical
volume and a complex normed target. The Banach-target inversion theorem
uses this call through the real scalar action on its complex Banach target.
The profile in the call is
$$
 \varphi(w)=\pi^{d/2}e^{-\pi^2\|w\|^2},\qquad d=\dim_{\mathbb R}V.
$$
In orthonormal coordinates its mass is
$\pi^{d/2}(1/\sqrt{\pi})^d=1$, including the empty product when $d=0$.
For decay, set $s=\pi^2\|w\|^2$.
Then $\|w\|^d\varphi(w)=\pi^{-d/2}s^{d/2}e^{-s}$ for $w\ne0$.
For an integer $m>d/2$, use $e^s\ge s^m/m!$ for $s>0$.
The consumer checks positivity, mass and decay at lines 117–135 and
passes integrability and point continuity at lines 136–137.
It substitutes $r=\sqrt{c}$ as $c\to+\infty$, giving the kernel
$(\pi c)^{d/2}e^{-\pi^2c\|v-w\|^2}$ at $v$, and reconciles real and complex
scalars on the positive tail at lines 138–156. This is the physical-space
limit used by `MeasureTheory.Integrable.fourierInv_fourier_eq` at lines
165–171 in the [pinned inversion proof][ch15-peak-consumer].
The [Gaussian transform](01-statement-and-fidelity.md#1227-from-poisson-summation-to-theta-inversion)
and the [Fourier convolution identity](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/Convolution.lean#L55-L122)
have their own proofs. [Pinned Gaussian consumer][ch15-peak-consumer]

For constant Haar rescaling $\nu'=\lambda\nu$ with $\lambda>0$, use
$\varphi'=\varphi/\lambda$ for the unit-mass profile, and then
$K'_r\,d\nu'=K_r\,d\nu$. In particular the determinant factor and the
recovered value are independent of this joint change. In the
[half-density comparison](#15431-half-densities-the-modulus-the-multiplicative-haar-measure-and-the-diagonal-weight),
the measure identity on $K_S^\times$ is instead
$\Delta_S\,d\mu_S=c_S\,d\nu_S$. Squaring the normalized half-density
$c_S^{-1/2}\Delta_S^{1/2}$ cancels $c_S$ for the isometry. The unnormalized
diagonal weight retains $c_S$ in both formulas of Theorem 15.3(3).
Corollary 15.9 describes independent rescalings of the two measures.
The Euclidean averaging result applies directly in additive coordinates.
On the positive real norm coordinate it applies to
$h(u)=e^{u/2}g(e^u)$ whenever $h$ is in $L^1(du)$ and is continuous at
$u_0=\log x_0$. The corresponding returned value for $g$ is
$x_0^{-1/2}A_rh(u_0)\to g(x_0)$. This is a textbook consequence of the
coordinate map. Masullo's strip-parameter independence in Theorem 12.5.1.1
remains [Open]. [Paper; Masullo pp. 16, 518–520][ch15-peak-masullo]

**Reading and attribution.** [Lean, read] here denotes local R3 for the
concentrating-kernel proof bodies at Mathlib pin
`0df444a360eaa60ab8c11dca51a86af692955474`, fixed by
`lean/lake-manifest.json:6–13` in the archive whose bundle SHA-256 is
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
The consumer is inherited from the inversion reading. This is a source
reading, with kernel replay and reachability from `src/Main.lean`
unassessed here. The new source reading and textbook proof are author-level. The section's estimates, examples and half-density
calculation are textbook work [Expository]. Stein and Shakarchi give the
normalized Gaussian family and Schwartz convergence on $\mathbb R$
in Chapter 5, Corollary 1.5, Theorem 1.6 and Corollary 1.7 (pp. 139–140).
Their near/far proof on the circle is in Chapter 2 §4, pp. 48–50.
With $\delta=1/(\pi r^2)$ their real Gaussian is exactly the scaled Gaussian
here. Their proof uses boundedness of the Schwartz input to multiply the tail
mass by a constant. The uniform off-ball bound in Theorem 15.23 controls an
$L^1$ input that may be unbounded away from the sampling point. [Stein–Shakarchi, `Fourier Analysis`][ch15-peak-stein]
[Source ledger](../sources/SOURCES.md#ch15-concentrating-kernels-sources) · [Local proof map](../notes/proof-map.md#ch15-concentrating-kernels-proof)

[ch15-peak-local]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/PeakFunction.lean#L54-L234
[ch15-peak-origin]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/PeakFunction.lean#L387-L446
[ch15-peak-reflected]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/PeakFunction.lean#L452-L469
[ch15-peak-consumer]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/Inversion.lean#L109-L171
[ch15-peak-masullo]: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=518
[ch15-peak-stein]: https://tildesites.bowdoin.edu/~tpietrah/hugo/math2805/pdfs/stein_shakarchi.pdf

#### 15.4.3.10 How powers of a unique peak concentrate at a point

**Motivation.** A continuous profile on a compact set can generate narrower averages without a change of coordinates. Raise the profile to the $n$th power and divide by its integral. The division is essential. If the peak height is less than one, the entire unnormalized profile decays. The ratio compares the height away from the peak with a strictly larger height attained throughout a small set of positive measure. This is the mechanism behind the cosine averages already used in [the Euler sine product](02-functional-equations-and-primitive-characters.md#2321-why-gamma-has-no-zeros-in-the-right-half-plane).

**Example 1 (a polynomial peak on an interval).** On $S=[-1,1]$ with Lebesgue measure take $c(x)=1-x^2$. Its unique maximum is at zero. For integers $n\ge0$, let $Z_n=\int_{-1}^1(1-x^2)^n\,dx$ and $J_n=\int_{-1}^1 x^2(1-x^2)^n\,dx$. The derivative of $x(1-x^2)^{n+1}$ is $(1-x^2)^{n+1}-2(n+1)x^2(1-x^2)^n$. Both boundary values vanish. Hence $Z_{n+1}=2(n+1)J_n$. Since $Z_{n+1}=Z_n-J_n$, we get
$$
 Z_n=2\prod_{j=1}^n\frac{2j}{2j+1}
     =\frac{2^{2n+1}(n!)^2}{(2n+1)!},
 \qquad \frac{J_n}{Z_n}=\frac{1}{2n+3}.
$$
The reciprocal of $Z_n$ is the normalizing multiplier. For the vector input $g(x)=(x,x^2)$, oddness makes the first coordinate of the average zero. In the maximum norm the exact error from $g(0)$ is $1/(2n+3)$. For $0<r\le1$, the integral of the normalized kernel over $|x|\ge r$ is at most $1/((2n+3)r^2)$ by integrating $r^2\mathbf 1_{\{|x|\ge r\}}\le x^2$. A second bound is
$$
 \frac{2(1-r)}{r}
 \left(\frac{1-r^2}{1-r^2/4}\right)^n
 \qquad (0<r<1),
$$
since the numerator is at most $2(1-r)(1-r^2)^n$ and the interval $[-r/2,r/2]$ contributes at least $r(1-r^2/4)^n$ to $Z_n$. At $r=1$ the tail has zero mass. The two bounds measure the same concentration at different scales.

**Example 2 (two equal peaks on the circle).** Take $S=\mathbb R/(2\pi\mathbb Z)$ with probability Haar measure $d\theta/(2\pi)$, and put $c(\theta)=\cos^2\theta$. The two maximizing points are $0$ and $\pi$. Write $Z_n=\int_S \cos^{2n}\theta\,d\theta/(2\pi)$. The periodic derivative of $\sin\theta\cos^{2n+1}\theta$ integrates to zero, so
$$
 Z_{n+1}=(2n+1)(Z_n-Z_{n+1}),\qquad
 Z_n=\prod_{j=1}^n\frac{2j-1}{2j}
     =\frac{\binom{2n}{n}}{4^n}.
$$
Here $Z_0=1$. For the normalized probability $\nu_n$, this recurrence gives $\int_S\sin^2\theta\,d\nu_n=1/(2n+2)$. The half turn preserves both $c$ and Haar measure, so it exchanges two semicircles of mass $1/2$ each. Use the arcs $[-\pi/2,\pi/2)$ and $[\pi/2,3\pi/2)$ modulo $2\pi$, assigning each to its center. For $0<r\le\pi/2$, let $T_r$ be the set at circular distance at least $r$ from both centers. On $T_r$ we have $\sin^2\theta\ge\sin^2 r$, so $\nu_n(T_r)\le 1/((2n+2)\sin^2 r)$. For any bounded Borel input $h$ continuous at both centers, write $\omega_h(r)$ for the larger of its two oscillations from the respective center on the open arcs of radius $r$. Subtract the assigned center value on each semicircle. Exact half mass on each, the near-arc bound and the tail estimate give
$$
 \left|\int_S h\,d\nu_n-\frac{h(0)+h(\pi)}2\right|
 \le \omega_h(r)+\frac{2\sup_S|h|}{(2n+2)\sin^2 r}.
$$
First choose $r$ small and then $n$ large. This proves the limit $\tfrac12\delta_0+\tfrac12\delta_\pi$. For $g(\theta)=(\cos\theta,\sin^2\theta)$ the average is exactly $(0,1/(2n+2))$. The first coordinate vanishes by the half turn. The error from the mixed value is $1/(2n+2)$ in the maximum norm, while the distance from $g(0)=(1,0)$ is one for every $n$. The equal split is forced by the symmetry of this profile and measure.

**Definition (normalized powers and support).** Let $X$ be a metrizable space with its Borel $\sigma$-algebra, $\mu$ a locally finite Borel measure, and $S\subseteq X$ compact. Let $E$ be a real Banach space and $x_0\in S$. For a continuous profile $c:S\to[0,\infty)$ set
$$
 Z_n=\int_S c(y)^n\,d\mu(y),\qquad
 K_n(x)=\frac{c(x)^n}{Z_n}\quad(x\in S),\qquad n=0,1,2,\ldots ,
$$
whenever $Z_n>0$. The power at $n=0$ is one even at zeros of $c$. The corresponding measure on $X$ is $\nu_n(B)=\int_{B\cap S} K_n\,d\mu$. Thus the density is extended by zero outside $S$, even at $n=0$. The positivity condition at the center is $\mu(U\cap S)>0$ for every open $U\ni x_0$. This says that $x_0$ belongs to the support of the *restricted measure* $\mu|_S$. Local finiteness gives $\mu(S)<\infty$ by a finite cover by finite-measure neighborhoods. The ambient measure may have infinite total mass. There is no assumption on $c$ off $S$.

**Theorem (concentration and pointwise recovery) [Lean, read].** Suppose $c(x_0)>0$, $c(x)<c(x_0)$ for every $x\in S\setminus\{x_0\}$, and $x_0$ belongs to the support of $\mu|_S$. Then $0<Z_n<\infty$ for every $n$ and the probability measures $\nu_n$ converge weakly to $\delta_{x_0}$, meaning convergence against every bounded continuous real test function on $X$, or equivalently here on $S$. For every specified $g:S\to E$ that is Bochner integrable for $\mu|_S$ and continuous at $x_0$ relative to $S$, the weighted functions are Bochner integrable for every $n$ and
$$
 \int_S K_n(x)g(x)\,d\mu(x)
   = Z_n^{-1}\int_S c(x)^n g(x)\,d\mu(x)
   \longrightarrow g(x_0).
$$
The pinned theorem gives the norm limit on the right. Weak convergence and the explicit estimates follow from its proof. In the source $c$ and $g$ are functions on $X$ tested only on $S$. A function on $S$ can be extended by zero for this purpose. [Pinned power theorem][ch15-maxpeak-core]

**Proof.** The powers are Borel measurable and bounded on $S$, so their integrals are finite. Positivity at $x_0$ and continuity give an open $V$ about $x_0$ with $c\ge c(x_0)/2$ on $V\cap S$. This subset has finite positive measure. Its contribution gives $Z_n\ge (c(x_0)/2)^n\mu(V\cap S)>0$. Consequently $K_n$ is nonnegative, bounded for each fixed $n$, and has integral one. Its product with $g$ is strongly measurable almost everywhere and has integrable norm by boundedness for each $n$. The scalar can therefore be taken outside the Bochner integral.

Fix an open $U\ni x_0$. When $S\setminus U$ is empty the far term vanishes. Otherwise $S\setminus U$ is compact, so $c$ attains its maximum there, say $t$. The strict maximum hypothesis gives $0\le t<c(x_0)$. Choose $t<b<c(x_0)$, and take an open $V\ni x_0$ on which $c>b$ relative to $S$. Put $m=\mu(V\cap S)$, so $0<m<\infty$. Monotonicity of the integral and nonnegativity give
$$
 Z_n\ge m b^n,\qquad
 0\le K_n(x)\le \frac{1}{m}\left(\frac{t}{b}\right)^n
 \quad(x\in S\setminus U).
$$
The ratio is strictly less than one. For $t=0$ the bound is $1/m$ at $n=0$ and zero for $n\ge1$. Integrating the uniform bound gives $\nu_n(S\setminus U)\le\mu(S\setminus U)(t/b)^n/m$.

For any $\varepsilon>0$, continuity at $x_0$ gives $U$ with $\|g(x)-g(x_0)\|\le\varepsilon$ on $U\cap S$. The constant $g(x_0)$ is integrable on $S$ by finite measure. Subtract it from the integrand using mass one and apply the Bochner norm inequality on the two pieces. With $t,b,m$ as above the result is
$$
 \left\|\int_S K_n g\,d\mu-g(x_0)\right\|
 \le\varepsilon+
 \frac{(t/b)^n}{m}
 \left(\int_{S\setminus U}\|g\|\,d\mu+
       \mu(S\setminus U)\|g(x_0)\|\right).
$$
The near term uses the oscillation and the total kernel mass. The far term uses the uniform bound so that $g$ may be unbounded there. Taking $n$ to infinity, then using arbitrary $\varepsilon$, proves recovery. A continuous real test on $S$ is bounded there and hence integrable. Its limit integral equals evaluation against the Dirac mass, proving weak convergence. The ambient and restricted formulations also agree directly for this limit. Fix a compatible metric $d$ and radius $r>0$. The ambient continuous test $x\mapsto\min(1,d(x,x_0)/r)$ is zero at $x_0$ and one off the open radius-$r$ ball. Its integral bounds the tail mass there. If ambient weak convergence holds, that mass tends to zero, which proves convergence for any continuous test on $S$ by its local oscillation and boundedness on $S$. [Pinned denominator, uniform tail and limit][ch15-maxpeak-core]

**Two ways to discharge the support and input conditions.** The second pinned declaration uses a measure positive on all nonempty open subsets of $X$ and $x_0\in\overline{\operatorname{int}S}$. Since compact $S$ is closed, this puts $x_0$ in $S$. Each open $U\ni x_0$ meets $\operatorname{int}S$, so $U\cap\operatorname{int}S$ is nonempty open and gives $\mu(U\cap S)>0$. The most general declaration makes the latter condition directly. For example, it applies with $X=\mathbb R$, $\mu=\delta_0$, $S=\{0\}$ and $c(0)=1$, where the interior of $S$ is empty.

The third declaration uses the same open-set positivity and closure-of-interior condition and assumes $g$ continuous on all of $S$. Then $g$ is bounded and strongly measurable on $S$: cover its compact image by finitely many balls of radius $1/k$ and choose the first center whose ball contains the value. These simple Borel functions converge uniformly to $g$. Finite measure then gives Bochner integrability, and the relative continuity at $x_0$ is immediate. The first two declarations admit an integrable input with jumps away from the peak. For instance $\mathbf1_{[1/2,1]}$ in Example 1 is locally constant at zero. [Pinned corollaries][ch15-maxpeak-versions]

**Connection with the finite-window argument.** In the [finite-window theorem][ch15-maxpeak-window], use $S$ itself as both integration set and window. Its mass under the kernel is exactly one at every index. The preceding estimates give nonnegativity and uniform vanishing off each neighborhood, and measurability follows from continuity of the powers on $S$. This is the call in the pinned proof. The Gaussian and translated kernels used in [Fourier inversion][ch15-maxpeak-gaussian] arise from the scaling branch of the same finite-window argument. The [finite-window result](#ch15-concentrating-kernels) permits a limiting window mass. This accommodates the scaling branch's growing domains in the unscaled variable.

**Where the limit is consumed.** The cosine case in Chapter 2 uses the continuous-input version with $c(x)=\cos x$ on $[0,\pi/2]$ and the complex Banach input $g(x)=\cos(2zx)$. The endpoint $0$ lies in the closure of the interior. The normalized integral tends to $1$ along the even exponents, the factor needed in the sine-product limit. [Pinned Euler sine consumer][ch15-maxpeak-euler]

Two A2 source call sites use this same Mathlib branch. In `lean/src/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean:426–475`, the cube $[-1/2,1/2]^d$ carries the profile $\prod_j |1+e^{2\pi i y_j}|^2$. Its unique maximum is at zero because each factor is at most $4$ and equals $4$ in this cube only at coordinate zero. The integrable input is an indicator of an open neighborhood of zero, locally constant there. Its normalized average tends to one, allowing the proof to pass a finite-sum lower bound to the limit. In `lean/src/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HolomorphicExtensionCompactRep.lean:74–108`, the continuous-input version is used on the compact group subtype with Haar measure and center $1$. On unitary matrices the profile is $1+\operatorname{tr}((g+1)^\dagger(g+1))$ and its drop from the maximum is $\operatorname{tr}((g-1)^\dagger(g-1))$, the sum of squared moduli of the matrix entries of $g-1$. The normalized average of the representation tends to the algebra unit. An index at distance less than one gives an invertible normalized average by the norm criterion for invertibility. Undoing the scalar normalization supplies the right inverse used in the extension proof. These are local consumer links. The FlagMeasures wrapper `TendstoIntegralNormalisedPowPeakStatement.lean:6–7` refers to the separate archive supplier `GlobalTheory.tendsto_integral_normalised_pow_peak`. [A2 archive and verification record](../sources/SOURCES.md#1-the-lean-archive-primary-source)

**Remarks on the hypotheses and the reading.** Full ambient support alone can miss the relative support condition. For $X=\mathbb R$ with Lebesgue measure, take $S=[1,2]\cup\{0\}$, $c(0)=2$, $c=1$ on $[1,2]$, and $g(0)=1$, $g=0$ on $[1,2]$. Both functions are continuous on $S$ and the positive maximum is unique, but the open interval $(-1/2,1/2)$ meets $S$ only at a null point. Every $Z_n$ is one and every average of $g$ is zero. Example 2 shows the distinct effect of deleting uniqueness with relative support intact. Point continuity selects the actual value of the chosen function: in Example 1 assign $g(0)=1$ and $g(x)=0$ elsewhere. Every weighted integral is zero, since the singleton is null.

Sébastien Gouëzel's three declarations are the formal source. [Lean, read] denotes author-level local R3 for those bodies at Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, fixed by A2's `lean/lake-manifest.json:6–13` in archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The estimates and examples are textbook derivations. The local source calls are documented in the proof map. Kernel replay, declaration reachability from `src/Main.lean`, and independent review of this increment are unassessed here. [Source ledger](../sources/SOURCES.md#chapter-15-154310-unique-maximum-powers) · [Proof map](../notes/proof-map.md#chapter-15-unique-maximum-powers)

[ch15-maxpeak-core]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/PeakFunction.lean#L249-L339
[ch15-maxpeak-versions]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/PeakFunction.lean#L350-L379
[ch15-maxpeak-window]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/PeakFunction.lean#L179-L221
[ch15-maxpeak-gaussian]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Fourier/Inversion.lean#L109-L171
[ch15-maxpeak-euler]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean#L251-L292

#### 15.4.3.11 Haar measure on p-adic balls and shells

**Motivation.** The finite-place half-density in [§15.4.3.1](#15431-half-densities-the-modulus-the-multiplicative-haar-measure-and-the-diagonal-weight) uses two measures on the same local coordinate. Multiplication by $p$ shrinks additive volume by $1/p$. On the multiplicative group it moves one valuation shell to the next and preserves its mass. The factor $c_p$ is determined by the additive volume of the unit shell.

For example, $\mathbb Z_2$ splits into $2\mathbb Z_2$ and $1+2\mathbb Z_2$. Each piece has additive mass $1/2$ when $\mathbb Z_2$ has mass one. The second piece is the unit shell. Multiplication by $2$ takes it to $2+4\mathbb Z_2$, of additive mass $1/4$. The inverse absolute value there is $2$, so weighting both shells by $|x|_2^{-1}$ gives each mass $1/2$. A further factor of $2$ makes both masses one.

**Definition.** Fix a prime $p$. Equip $K=\mathbb Q_p$ with the Borel sets of the metric $d(x,y)=|x-y|_p$, where $|p|_p=p^{-1}$. Write
$$
O=\mathbb Z_p=\{x:|x|_p\le 1\},\qquad H_n=p^n O,\qquad
B_n(b)=b+H_n,\qquad U_n=p^n O^\times
$$
for $b\in K$ and $n\in\mathbb Z$. Regard $O$ as a subset of $K$ via the inclusion of $p$-adic integers. Identify $K^\times$ with the open subspace $K\setminus\{0\}$, with its subspace topology and Borel sets. For $a\ne 0$, set $D_a(x)=ax$.

**Lemma (the residue partition).** Each $B_n(b)$ is the closed ball of radius $p^{-n}$ centered at $b$, and it is compact and open. The ball has the disjoint partition
$$
B_n(b)=\bigsqcup_{j=0}^{p-1} B_{n+1}(b+jp^n).
$$
Also $U_n=H_n\setminus H_{n+1}=\{x:|x|_p=p^{-n}\}$.

*Proof.* The pinned `PadicInt.appr` supplies at natural level $k$ an integer $j$, $0\le j<p^k$, with $x-j\in p^k O$, for each $x\in O$. These representatives give finite covers at arbitrarily small radii since $p^{-k}\to0$. The proof of `PadicInt.compactSpace` combines total boundedness with completeness of the closed norm sublevel in the complete field. Its image in $K$ is compact. An ultrametric closed ball of positive radius is open because the open ball of that radius about any of its points lies inside it. The affine map $y\mapsto b+p^ny$ is a homeomorphism. Norm multiplicativity and $|p^n|_p=p^{-n}$ identify its image of $O$ with the indicated closed ball. [Integer compactness][ch15-padic-compact] · [Open integer embedding][ch15-padic-open] · [Powers][ch15-padic-powers] · [Discrete norm values][ch15-padic-values]

Reduction $O\to\mathbb Z/p\mathbb Z$ is onto since it preserves integer casts. Its kernel is $pO$. The pinned proof first approximates a $p$-adic integer by a rational at distance $<1$. The rational is integral and its reduced denominator is prime to $p$. Inverting the denominator modulo $p$ supplies a representative in $0,\ldots,p-1$. The ultrametric inequality transfers the congruence to the original point. Two representatives with the same residue differ by a multiple of $p$, hence agree in this range. The higher digit step divides the error by $p^k$, reduces it modulo $p$ and appends the resulting digit. This supplies the representatives used for compactness. The first reduction fibers are $j+pO$. Transport them by the affine map to obtain the partition for every integer $n$. A unit of $O$ has norm one because both it and its inverse have norm at most one. Conversely the inverse of a norm-one element lies in $O$. Since nonzero norms lie in $p^\mathbb Z$, the gap between $p^{-n}$ and $p^{-(n+1)}$ isolates $U_n$. $\square$ [Residue representatives and kernel][ch15-padic-residue] · [Units][ch15-padic-units]

**Theorem (normalized additive and multiplicative Haar measures).** There is a unique additive Haar measure $\mu$ on $K$ with $\mu(O)=1$. For every $b\in K$, $n\in\mathbb Z$, $a\in K^\times$ and Borel $E\subseteq K$,
$$
\mu(B_n(b))=p^{-n},\qquad
\mu(U_n)=p^{-n}(1-1/p),\qquad
\mu(aE)=|a|_p\,\mu(E),\qquad
(D_a)_*\mu=|a|_p^{-1}\mu .
$$
The origin has mass zero. Put $\rho=\mu|_{K^\times}$. The unique multiplicative Haar measure $\lambda$ on $K^\times$ with $\lambda(O^\times)=1$ is
$$
d\lambda(x)=c_p\,|x|_p^{-1}d\rho(x),\qquad c_p=(1-1/p)^{-1}=\frac{p}{p-1}.
$$
In particular $\lambda(U_n)=1$ for every $n\in\mathbb Z$.

*Proof.* The local topological inputs are the Hausdorff topological field structure, local compactness and second countability. The closed unit ball gives a compact neighborhood of zero, and the pinned `ProperSpace` instance supplies local compactness. The pinned proper-metric instance also supplies second countability, which can be seen directly from the countable dense rational image. The multiplicative group is an open subspace and inherits these three properties. Apply the general `Measure.addHaarMeasure` construction and its Haar, regularity and normalization declarations to the positive compact $O$, whose interior contains $0$. The Haar measure is $\sigma$-finite under these topological inputs. The inherited uniqueness theorem with normalizing set $O$ fixes $\mu$. [Rational density][ch15-padic-dense] · [General Haar construction and normalization][ch15-padic-haar]

By translation invariance all children of $H_n$ have mass $\mu(H_{n+1})$. Finite additivity gives $\mu(H_n)=p\mu(H_{n+1})$. Compactness gives finite masses. Starting at $\mu(H_0)=1$, division by $p$ gives $\mu(H_m)=p^{-m}$ for $m\ge0$. Multiplying by $p$ backwards gives $\mu(H_{-m})=p^m$ for $m\ge0$. Translation gives $B_n(b)$, and subtraction of the two finite concentric masses gives the shell formula. Since $0\le\mu(\{0\})\le p^{-m}$ for every $m\ge0$, the origin is null. The valuation of each nonzero point gives the disjoint decomposition $H_n\setminus\{0\}=\bigsqcup_{k\ge n}U_k$. Its additive mass is still $p^{-n}$.

For $a\ne0$, let $k$ be the unique integer with $|a|_p=p^{-k}$. The element $p^{-k}a$ has norm one, so multiplication by it carries $O$ onto itself. Thus $aO=H_k$. The image-side identity for the distributive Haar character of scalar multiplication reads $\mu(aE)=\Delta(a)\mu(E)$ for our regular Haar measure. Evaluate it on $O$ to get $\Delta(a)=p^{-k}=|a|_p$. The preimage of $E$ under $D_a$ is $a^{-1}E$, so its pushforward uses the reciprocal. [Haar character identity and calibration][ch15-padic-char]

Apply the multiplicative Haar construction of §15.4.3.1 to $\rho$ with modulus $|\cdot|_p$. The inverse modulus is continuous and positive on $K^\times$, and bounded on each compact subset there. The change of variables uses $\mu(a\,dx)=|a|_p\,\mu(dx)$ against $|ax|_p^{-1}=|a|_p^{-1}|x|_p^{-1}$. These factors cancel, giving a multiplicatively invariant density measure, finite on compact sets and positive on nonempty opens. On $U_0$ the density is one and $\rho(U_0)=1-1/p>0$. The extra factor $c_p$ normalizes the unit shell. Haar uniqueness on $K^\times$ applies since $U_0$ is compact open and contains $1$. Every $U_n$ is a multiplicative translate of $U_0$ and has mass one. In particular the punctured ball $H_n\setminus\{0\}$ has infinite multiplicative mass by countable additivity over $k\ge n$. $\square$

**Two calculations in the original fields.**

1. **At $p=2$.** In $\mathbb Q_2$, the ball $2^{-1}O$ splits as $O\sqcup(1/2+O)$, of mass two. Two reductions give $O=\bigsqcup_{j=0}^3(j+4O)$ with each cell of mass $1/4$. The translated ball $B_2(3/2)=3/2+4O$ also has mass $1/4$. The balls at levels $-1,0,2$ have masses $2,1,1/4$ and their next levels have masses $1,1/2,1/8$. Subtracting gives $\mu(U_{-1}),\mu(U_0),\mu(U_2)=1,1/2,1/8$. These shells contain $1/2,1,4$, respectively. Their inverse-norm weights are $1/2,1,4$, so the three weighted masses before normalization are $1/2,1/2,1/2$. Multiplying by $c_2=2$ gives three unit masses. For $a=3/2$, $aU_0=U_{-1}$ and $a^{-1}U_0=U_1$. Their additive masses are $1$ and $1/4$, while $\mu(U_0)=1/2$ and $|a|_2=2$. The punctured ball $2^{-1}O\setminus\{0\}$ has additive mass $\sum_{k=-1}^\infty 2^{-k}/2=2$ and multiplicative mass $\sum_{k=-1}^\infty 1=\infty$. The origin lies in every $2^m O$, whose masses tend to zero. For $g=\mathbf 1_{U_2}$ the squared half-density multiplier $c_2^{-1}|x|_2$ is $1/8$ on $U_2$. Its integral against the unit multiplicative mass recovers $\|g\|_{L^2(\mu)}^2=1/8$.
2. **At $p=5$.** In $\mathbb Q_5$, $5^{-2}O=\bigsqcup_{j=0}^{24}(j/25+O)$ and $5^{-1}O=\bigsqcup_{j=0}^{4}(j/5+O)$. Their masses are $25$ and $5$. The five cosets of $5O$ in $O$ have mass $1/5$ each and the five cosets of $25O$ in $5O$ have mass $1/25$ each. The translated ball $B_1(2/5)=2/5+5O$ has mass $1/5$. The shells at $-2,0,1$ have masses $25-5=20$, $1-1/5=4/5$ and $1/5-1/25=4/25$. They contain $1/25,1,5$, respectively. The inverse-norm weights are $1/25,1,5$, so each weighted mass is $4/5$. Multiplying by $c_5=5/4$ gives one in each case. For $a=3/25$, $aU_0=U_{-2}$ has mass $20=25(4/5)$, and the preimage of $U_0$ is $U_2$, of mass $4/125=(4/5)/25$. The punctured ball $5^{-2}O\setminus\{0\}$ has additive mass $\sum_{k=-2}^\infty (4/5)5^{-k}=25$ and infinite multiplicative mass since all these shells have mass one. The origin has mass zero by the bound $5^{-m}$. For $g=\mathbf 1_{U_1}$ the squared half-density multiplier is $(4/5)(1/5)=4/25$ on $U_1$. Integration against the unit multiplicative mass recovers the same additive squared norm.

**Remarks on the normalization.** If the additive normalization is deleted, $2\mu$ is still a regular additive Haar measure on the same field. Its ball and shell masses double, and its scalar modulus stays $|a|_p$. Using the same $c_p$ with $2\mu$ gives unit-shell mass $2$. Keeping $\mu(O)=1$ and dropping only $c_p$ preserves multiplicative invariance, with unit-shell mass $1-1/p$. The unweighted restriction $\rho$ fails multiplicative invariance: $D_p$ carries $U_0$ to $U_1$, whose positive $\rho$-mass is $1/p$ times that of $U_0$.

In Theorem 15.6 take the additive factor $\nu_p=\mu$ and the unnormalized multiplicative factor $\mu_p=|x|_p^{-1}\rho$ in density notation. Then $c_p\mu_p=\lambda$ is the normalized factor of $\mu_S$, and the local half-density multiplier is $c_p^{-1/2}|x|_p^{1/2}$. The additive nullity of zero identifies $L^2(K,\mu)$ with $L^2(K^\times,\rho)$. The factor $c_p$ enters $c_S$ in the finite-place product formula. Masullo's Example A.3.1.7 uses this additive normalization over $\mathbb Q_p$. His Definition A.3.2.2 and Lemma A.3.2.3 give the density ratio $q_v/(q_v-1)$ at a finite place, hence the factor in (12.4.1.17) for $q_v=p$. For an extension $F_v/\mathbb Q_p$, the two Tamagawa masses on the integer ball and unit group both carry the factor $|\operatorname{disc}(\mathcal O_{F_v}/\mathbb Z_p)|_p^{1/2}$. Over $\mathbb Q_p$ this factor is one. The one-place computation supplies a factor of the measure formula. The trace theorem uses additional restrictions on $S$ and on the test function, specified on p. 520. [Masullo, Appendix A][ch15-padic-masullo] · [The finite-place product constant][ch15-padic-cs]

**Where the archive uses the measures.** The theorem is a textbook specialization. The Mathlib construction takes the `PadicInt` image as a `PositiveCompacts` and uses generic Haar measure with values in the extended nonnegative reals. The A2 archive has the actual local-field declarations under `lean/src/GroundTheory/LocalFields/`, and `Examples.lean:7–38` supplies the valuative local-field instance on `ℚ_[p]`. Valuation compatibility identifies its integer ring with the norm sublevel $O$. The actual ring equivalence and order calculation are `Padic.padicIntRingEquivInteger` and `Padic.ord_p` in `LocalFourierPadic.lean:31–51`. Transporting the quotient through this ring equivalence and the pinned integer residue equivalence gives $\mathbb Z/p\mathbb Z$. Every $a\ne0$ has the form $p^ku$ with $u\in O^\times$. The archive order adds under multiplication and vanishes on $u$, so it takes value $k$ on $a$. This identifies the A2 ball and shell indices with $H_n$ and $U_n$. [A2 pin and file references](../sources/SOURCES.md#chapter-15-p-adic-haar-measure)

| Actual A2 declaration or call | What its proof uses |
| --- | --- |
| `LocalFourierHaar.lean:237–281, 285–323` | `measure_valBall_zero_eq_mul` partitions into measurable translates indexed by residue classes. `measure_valBall_eq_mul_succ` transports the identity by a scalar of order $n$. `measure_valBall` uses successor and predecessor inductions. |
| `LocalFourierHaar.lean:327–340, 347–382, 384–396` | `haarIntegers` calls `addHaarMeasure` at the positive compact integer ball. `distribHaarChar_eq_modulus` evaluates the image formula on this ball. The pushforward and integral identities use the inverse modulus. |
| `LocalFourier.lean:135–186, 188–276, 278–312` | `multHaar` uses `withDensity` and `Measure.comap Units.val`. Invariance cancels two modulus factors. Unit normalization subtracts nested ball masses and applies `multHaarConst`. |
| `LocalZetaShell.lean:66–85, 113–141` | `multHaar_ordShell` pulls each shell back to the unit shell by a uniformizer power. The shell decomposition supplies the corresponding integral sum. |
| `LocalZetaTate.lean:51–77, 82–102` and `LocalZetaIntegral.lean:210–231` | The former uses the additive ball bounds to remove zero, then changes multiplicative to additive integration with the explicit constant. The latter sums the local zeta integral by shells and extracts the constant modulus on each shell. `LocalZetaChar.lean:162–175` explicitly uses shell mass one to integrate the unramified character after transport to the unit shell. |

The half-density call is the textbook formula in §15.4.3.1 and Theorem 15.6. The A2 calls above concern Haar measures and integration. Local R3 [Lean, read] covers the named production bodies and the displayed consumer calls. The full local zeta theorem enters at its interface. The general Haar construction, uniqueness, finite products and density transport are inherited. Whole-archive replay and independent adjudication are separate. Masullo's strip nuclearity and independence of the strip parameter retain their [Open] status.

[ch15-padic-compact]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/ProperSpace.lean#L39-L69
[ch15-padic-open]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicIntegers.lean#L144-L148
[ch15-padic-residue]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/RingHoms.lean#L145-L475
[ch15-padic-powers]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L853-L866
[ch15-padic-units]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicIntegers.lean#L370-L403
[ch15-padic-dense]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L815-L823
[ch15-padic-haar]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/Basic.lean#L515-L585
[ch15-padic-char]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Haar/DistribChar.lean#L80-L95
[ch15-padic-masullo]: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=560
[ch15-padic-cs]: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=518
[ch15-padic-values]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L1049-L1062

#### 15.4.3.12 Completing the rationals at a prime

**Motivation.** The local Haar calculation in [§15.4.3.11](#154311-haar-measure-on-p-adic-balls-and-shells) takes as given a complete topological field $K=\mathbb Q_p$ in which the rationals sit densely and every nonzero norm is an integer power $p^{-k}$. Both properties come from completing $\mathbb Q$ with respect to its $p$-adic absolute value, but the norm extension does *not* imitate the archimedean completion $\mathbb Q\to\mathbb R$. For $\mathbb R$, the absolute values of a rational Cauchy sequence form a rational Cauchy sequence whose limit typically lies only in $\mathbb R$. For $\mathbb Q_p$, the strong triangle inequality forces the rational $p$-adic norms along any Cauchy sequence away from zero to become **strictly constant** on a tail. As a result, the norm on the quotient field is already rational-valued before any cast to $\mathbb R$, and its nonzero values are literally the norms of nonzero rationals — namely $p^{\mathbb Z}$.

**Example (rational approximations before completion).** At $p=3$, the partial sums $1$, $1+3=4$, and $1+3+9=13$ satisfy $1-(-1/2)=3/2$, $4-(-1/2)=9/2$, and $13-(-1/2)=27/2$, so their $3$-adic distances to $-1/2$ are $1/3$, $1/9$, and $1/27$, while every term from $1$ onward already has $3$-adic norm $1$. At $p=5$, $a_1=1$ and $a_2=16$ satisfy $1^2-6=-5$ and $16^2-6=250=2\cdot 5^3$; their $5$-adic distance is $|16-1|_5=|15|_5=1/5$, and continuing mod-$5^n$ lifts produces a $5$-adic Cauchy sequence whose limit squares to $6$ and therefore lies outside $\mathbb Q$.

**Definition (rational $p$-adic valuation, norm and Cauchy quotient).** Fix a rational prime $p$. For a nonzero integer $b$, let $e_p(b)=\max\{j\in\mathbb Z_{\ge 0}:p^j\mid b\}$. For a nonzero rational written as $a/b$ with $a,b\in\mathbb Z\setminus\{0\}$, set
$$
v_p(a/b)=e_p(a)-e_p(b)\in\mathbb Z,\qquad |a/b|_p=p^{-v_p(a/b)}\in\mathbb Q_{>0},
$$
and put $v_p(0)=+\infty$, $|0|_p=0$, and $d_p(r,s)=|r-s|_p$ on $\mathbb Q$. Let $C$ be the set of rational sequences $r=(r_i)_{i\ge 0}$ such that for every real $\varepsilon>0$ (or equivalently every rational $\varepsilon>0$) there exists $N\in\mathbb N$ with $|r_i-r_j|_p<\varepsilon$ whenever $i,j\ge N$. Define $r\sim s$ on $C$ by $\lim_{i\to\infty}|r_i-s_i|_p=0$, and write $K=C/{\sim}$ with class map $r\mapsto [r]$ and constant embedding $\iota(q)=[(q)_{i\ge 0}]$. In pinned Mathlib, `padicValRat p q` is integer-valued on reduced numerator and denominator with totalized value $0$ at $q=0$, while `padicNorm p q` tests $q=0$ explicitly. [Pinned rational valuation][ch15-qpc-ratval] · [Pinned rational norm][ch15-qpc-ratnorm]

**Lemma (the rational $p$-adic absolute value) [Lean, read].** On $\mathbb Q$, $v_p(a/b)$ is independent of the fraction representation. For all $q,s\in\mathbb Q$, $|-q|_p=|q|_p$, $|qs|_p=|q|_p|s|_p$, and
$$
|q+s|_p\le\max(|q|_p,|s|_p),
$$
with equality $|q+s|_p=\max(|q|_p,|s|_p)$ whenever $|q|_p\ne |s|_p$.

*Proof.* For $u,w\in\mathbb Z\setminus\{0\}$, factor $u=p^{e_p(u)}u_0$ and $w=p^{e_p(w)}w_0$ with $p\nmid u_0$ and $p\nmid w_0$. Because $p$ is prime, $p\nmid u_0w_0$, so $e_p(uw)=e_p(u)+e_p(w)$ and $e_p(-u)=e_p(u)$. If $a/b=a'/b'$ with nonzero integers, then $ab'=a'b\ne 0$ gives $e_p(a)+e_p(b')=e_p(a')+e_p(b)$, proving representation independence, $|-q|_p=|q|_p$, and $v_p(qs)=v_p(q)+v_p(s)$ for $q,s\ne 0$; multiplication by $0$ gives $0=0$ on norms. For addition, if $q=0$, $s=0$, or $q+s=0$, then $v_p(q+s)\ge\min(v_p(q),v_p(s))$ holds from $v_p(0)=+\infty$ and $|-q|_p=|q|_p$. When $q,s,q+s$ are all nonzero, put $k=\min(v_p(q),v_p(s))$ and write $p^{-k}q=u_1/w_1$, $p^{-k}s=u_2/w_2$ in lowest terms. Since $v_p(p^{-k}q)\ge 0$ and $v_p(p^{-k}s)\ge 0$, neither $w_1$ nor $w_2$ is divisible by $p$, hence $p\nmid w_1w_2$ by primality. From $p^{-k}(q+s)=(u_1w_2+u_2w_1)/(w_1w_2)$ we obtain $v_p(p^{-k}(q+s))=e_p(u_1w_2+u_2w_1)\ge 0$, so $v_p(q+s)\ge k$. Because $p>1$, reversing the exponent gives $|q+s|_p\le\max(|q|_p,|s|_p)$. If $|q|_p>|s|_p$, applying this inequality to $q=(q+s)+(-s)$ gives $|q|_p\le\max(|q+s|_p,|s|_p)$, which forces $|q|_p\le |q+s|_p\le |q|_p$; the case $|s|_p>|q|_p$ is symmetric. $\square$ [Rational valuation proofs][ch15-qpc-ratval] · [Rational norm and ultrametric equality][ch15-qpc-ratmul] · [Generic unequal-norm lemma][ch15-qpc-nonarch]

**Theorem (the completed field $\mathbb Q_p$, its discrete value group and local-field bridge) [Lean, read].** Let $p$ be prime and $K=C/{\sim}$ be the Cauchy quotient above.

1. $K$ is a field of characteristic zero under termwise addition, negation and multiplication, with $\iota:\mathbb Q\hookrightarrow K$ injective and $[r]^{-1}$ given for $[r]\ne 0$ by inverting any representative on a tail where its entries are nonzero.
2. For every $r\in C$ with $[r]\ne 0$, the sequence $(|r_i|_p)_{i\ge 0}$ is eventually constant with a positive value depending only on $[r]$. Setting $|[r]|_p$ to that eventual rational value (and $|0|_p=0$) defines a multiplicative ultrametric norm on $K$ extending $|\cdot|_p$ on $\mathbb Q$, whose image on $K^\times$ is $\{p^{-k}:k\in\mathbb Z\}$. Writing $|x|_p=p^{-v_p(x)}$ for $x\ne 0$ and $v_p(0)=+\infty$ defines the unique extended discrete valuation on $K$ extending $v_p$ on $\mathbb Q$, satisfying $v_p(xy)=v_p(x)+v_p(y)$ and $v_p(x+y)\ge\min(v_p(x),v_p(y))$.
3. Under $d_p(x,y)=|x-y|_p$, $K$ is a Hausdorff topological field, $\iota(\mathbb Q)$ is isometric and dense in $K$ with $|\,[r]-\iota(r_i)\,|_p\to 0$ for every $r\in C$, and $(K,d_p)$ is complete.
4. $K$ is Mathlib's `Padic p` (`ℚ_[p]`). Under the A2 valuative-topology and nonarchimedean local-field instances on `ℚ_[p]`, its valuation ring is $\{x\in\mathbb Q_p:|x|_p\le 1\}$, $\operatorname{ord}(x)=v_p(x)$ for all $x\in\mathbb Q_p^\times$ (with $\operatorname{ord}(0)=0$), and `GroundTheory.LocalField.normalizedValuation ℚ_[p]` agrees pointwise on all of $\mathbb Q_p$ with `Padic.mulValuation`.

*Proof of stabilization and the discrete value group.* Symmetry and $|r_i-t_i|_p\le\max(|r_i-s_i|_p,|s_i-t_i|_p)$ make $\sim$ an equivalence relation, with zero class $\{r\in C:|r_i|_p\to 0\}$. If $r\in C$ satisfies $r\not\sim 0$, there is a rational $\eta>0$ such that arbitrarily large indices satisfy $|r_j|_p\ge\eta$. Choose a Cauchy threshold $N_0$ with $|r_i-r_m|_p<\eta$ for all $i,m\ge N_0$, and pick one index $N\ge N_0$ with $c:=|r_N|_p\ge\eta>0$. For every $i\ge N$, $|r_i-r_N|_p<\eta\le c=|r_N|_p$, so the unequal-norm clause of the Lemma applied to $r_i=r_N+(r_i-r_N)$ yields $|r_i|_p=|r_N|_p=c$. If $s\sim r$, then $|s_i-r_i|_p<c$ for all large $i$, whence $|s_i|_p=c$ on a common tail. Thus $|[r]|_p:=c$ on $K^\times$ and $|0|_p:=0$ is well defined and rational-valued. Because $c=|r_N|_p$ with $r_N\in\mathbb Q^\times$, every nonzero norm in $K$ already lies in $p^{\mathbb Z}$; conversely, the constants $\iota(p^k)$ ($k\in\mathbb Z$) have norm $p^{-k}$ and exhaust $p^{\mathbb Z}$. Since $p>1$, the exponent $k\in\mathbb Z$ in $|x|_p=p^{-k}$ is unique for $x\ne 0$. (In `PadicSeq.stationary`, Lean obtains the tail lower bound via `CauSeq.abv_pos_of_not_limZero` and combines it with `cauchy₂` and `padicNorm.add_eq_max_of_ne`.) [Stationary tail][ch15-qpc-stationary] · [Representative independence and laws][ch15-qpc-norme] · [Discrete norm image][ch15-qpc-values]

*Proof of the field, norm and topological-field laws.* Closure and congruence of addition and negation follow from the ultrametric bound. Every $r\in C$ is bounded: choosing $N_1$ with $|r_i-r_{N_1}|_p<1$ for $i\ge N_1$ bounds $|r_i|_p$ by $\max(\max_{0\le m\le N_1}|r_m|_p,1)$. If $M\ge 1$ bounds $r,s\in C$, inserting $r_i s_j$ gives
$$
|r_i s_i - r_j s_j|_p \le M\max(|r_i-r_j|_p,|s_i-s_j|_p),
$$
proving $rs\in C$, and the analogous four-sequence estimate proves congruence of multiplication; the commutative ring laws descend termwise, while $|\iota(q)-\iota(s)|_p=|q-s|_p$ gives injectivity of $\iota$ and characteristic zero. For $[r]\ne 0$ with tail norm $c>0$ on $i\ge N$, any sequence $g$ with $g_i=r_i^{-1}$ for $i\ge N$ satisfies
$$
|g_i - g_j|_p = \left|\frac{r_j-r_i}{r_i r_j}\right|_p = c^{-2}|r_i-r_j|_p \qquad (i,j\ge N),
$$
so $g\in C$ and $[g][r]=1$. Representative independence on $K^\times$ follows either from the same $c^{-2}$ estimate on a common tail or, as in `CauSeq.Completion`, from associative cancellation of two-sided inverses in the quotient ring (with Lean's totalized $0^{-1}=0$). [Cauchy ring and inverse bounds][ch15-qpc-causeq] · [Quotient field and totalized inverse][ch15-qpc-quotinv]

No archimedean limit of rational norms is needed to pass the norm axioms to $K$. If $x=0$ or $y=0$, $|xy|_p=0=|x|_p|y|_p$; if $x=[r]\ne 0$ and $y=[s]\ne 0$, then on the intersection of their constant-norm tails $|r_i s_i|_p=|x|_p|y|_p>0$, so $xy\ne 0$ and $|xy|_p=|x|_p|y|_p$. Likewise, $|x+y|_p\le\max(|x|_p,|y|_p)$ is trivial if $x=0$, $y=0$, or $x+y=0$, and when all three are nonzero it holds by evaluating $|r_i+s_i|_p\le\max(|r_i|_p,|s_i|_p)$ at a single index beyond all three stationary thresholds (`PadicSeq.lift_index_left_left`). Unequal norms force $x+y\ne 0$ and give $|x+y|_p=\max(|x|_p,|y|_p)$ at the same index, and reversing exponents yields $v_p(xy)=v_p(x)+v_p(y)$ and $v_p(x+y)\ge\min(v_p(x),v_p(y))$ on $K$. Under $d_p(x,y)=|x-y|_p$, the ultrametric sum, bounded-product, and constant-norm-ball reciprocal estimate ($|y|_p=|x|_p=c$ whenever $|y-x|_p<c$, giving $|y^{-1}-x^{-1}|_p=c^{-2}|y-x|_p$) establish continuity of addition, negation, multiplication, and inversion on $K^\times$. [Quotient norm lift][ch15-qpc-lift] · [Metric and NormedField instances][ch15-qpc-metric]

*Proof of rational density and completeness.* Given $x=[r]\in K$ and $\varepsilon>0$, choose $N$ with $|r_j-r_i|_p<\varepsilon$ for all $i,j\ge N$. Fix $i\ge N$: the difference sequence $j\mapsto r_j-r_i$ either lies in the zero class (giving $|x-\iota(r_i)|_p=0<\varepsilon$) or stabilizes at some index $m\ge N$ (giving $|x-\iota(r_i)|_p=|r_m-r_i|_p<\varepsilon$). Thus $\iota(r_i)\to x$ and $\iota(\mathbb Q)$ is dense in $K$. Now let $(x_i)_{i\ge 0}$ be Cauchy in $(K,d_p)$ and pick $q_i\in\mathbb Q$ with $|x_i-\iota(q_i)|_p<p^{-i}$ for each $i\ge 0$. By isometry of $\iota$ and the ultrametric inequality,
$$
|q_i-q_j|_p \le \max(|q_i-x_i|_p,\,|x_i-x_j|_p,\,|x_j-q_j|_p),
$$
whose right-hand side tends to $0$ as $i,j\to\infty$. Hence $q=(q_i)\in C$ defines $x=[q]\in K$, and since $|\iota(q_i)-x|_p\to 0$ we get $|x_i-x|_p\le\max(|x_i-\iota(q_i)|_p,|\iota(q_i)-x|_p)\to 0$. In `PadicNumbers.lean`, `limSeq` chooses rational approximations within $\frac{1}{i+1}\in\mathbb Q_{>0}$ and uses $\varepsilon/3$ and $\varepsilon/2$ triangle splittings on rational radii before passing to real radii via `exists_rat_btwn`; because the metric uniformity has a countable basis of $1/(n+1)$-entourages, `complete_of_cauchySeq_tendsto` upgrades sequential completeness to the filter-based `CompleteSpace ℚ_[p]` instance. [Representative convergence][ch15-qpc-lift] · [Diagonal Cauchy completion][ch15-qpc-complete] · [CompleteSpace bridge][ch15-qpc-complete-metric] · [Countable-uniformity criterion][ch15-qpc-uniform]

*Proof of the local-field valuation bridge.* By definition `Padic p` is `CauSeq.Completion.Cauchy (padicNorm p)`, with `Padic.valuation x = v_p(x)` for $x\ne 0$ ($0$ at $x=0$) and `Padic.mulValuation x = WithZero.exp (-x.valuation)` for $x\ne 0$ ($0$ at $x=0$). Pinned Mathlib's `Padics/ValuativeRel.lean` equips `ℚ_[p]` with `ValuativeRel.ofValuation Padic.mulValuation`. In A2 `Examples.lean:17–39`, `mulValuation_le_iff_norm_le` checks across zero and nonzero cases (using $1<p$ and `Padic.norm_eq_zpow_neg_valuation`) that `Padic.mulValuation x ≤ Padic.mulValuation y ↔ ‖x‖ ≤ ‖y‖`, supplying `IsValuativeTopology ℚ_[p]` and, with the named `LocallyCompactSpace ℚ_[p]` and `IsNontrivial ℚ_[p]` inputs, `IsNonarchimedeanLocalField ℚ_[p]`. In `LocalFourierPadic.lean:31–51`, this equivalence identifies $\mathcal O[\mathbb Q_p]=\{x\in\mathbb Q_p:|x|_p\le 1\}$ (`padicIntRingEquivInteger` is the identity on underlying elements) and transports the named `PadicInt.irreducible_p` to `ord_p : ord (p : ℚ_[p]) = 1` via `ord_uniformizer`. For any $x\in\mathbb Q_p^\times$, put $k=v_p(x)\in\mathbb Z$ and $u=p^{-k}x$. Both $u$ and $u^{-1}$ have norm $1$, hence lie in $\mathcal O[\mathbb Q_p]$, making $u$ a unit of $\mathcal O[\mathbb Q_p]$ with $x=p^k u$. Applying A2's `ord_mul` and `ord_unit` (`UnitsBasic.lean:151–158`) gives $\operatorname{ord}(x)=\operatorname{ord}(p^k)+0=k$, using induction from $\operatorname{ord}(p)=1$ for $k\ge 0$ and $\operatorname{ord}(p^m)+\operatorname{ord}(p^{-m})=\operatorname{ord}(1)=0$ for $k=-m<0$. At $x=0$, $\operatorname{ord}(0)=-\mathtt{WithZero.log}(0)=0$. Finally `normalizedValuation_eq_exp_ord` gives $\mathtt{normalizedValuation}\ \mathbb Q_p\ x = \operatorname{WithZero.exp}(-k) = \mathtt{Padic.mulValuation}\ x$ for $x\ne 0$, and both vanish at $x=0$. $\square$ [Padic quotient][ch15-qpc-padic] · [Padic valuations][ch15-qpc-val] · [ValuativeRel instance][ch15-qpc-valrel] · [Archive file references](../sources/SOURCES.md#chapter-15-rational-p-adic-completion)

**Two worked calculations in the completed fields.**

1. **A $3$-adic geometric series, its tail reciprocal and a negative-order scaling.** At $p=3$, define $s_n=\sum_{j=0}^{n-1}3^j=(3^n-1)/2$ for $n\ge 0$ (with $s_0=0$). For $m>n\ge 0$, $s_m-s_n=3^n(3^{m-n}-1)/2$ has $3\nmid (3^{m-n}-1)$ and $3\nmid 2$, so $v_3(s_m-s_n)=n$ and $|s_m-s_n|_3=3^{-n}$; hence $(s_n)\in C$. Subtracting $-1/2$ gives $s_n-(-1/2)=3^n/2$, so $[s]=\iota(-1/2)$ with exact error $|s_n-(-1/2)|_3=3^{-n}$ for every $n\ge 0$. Notice that $s_0=0$ has norm $0$, whereas for every $n\ge 1$ the norm stabilizes at $|s_n|_3=1=|-1/2|_3$ ($N=1$). Inverting on the nonzero tail $n\ge 1$ gives $s_n^{-1}-(-2)=2\cdot 3^n/(3^n-1)$, with exact error $|s_n^{-1}-(-2)|_3=3^{-n}$ ($s_1,s_2,s_3,s_4=1,4,13,40$, errors $1/3,1/9,1/27,1/81$). Scaling by $3^{-1}$ gives $w_n=s_n/3=(3^n-1)/6\to -1/6$, an element outside $\mathbb Z_3$ of valuation $v_3(-1/6)=-1$ and stationary norm $c=|w_n|_3=3>1$ for $n\ge 1$; its tail reciprocals $w_n^{-1}=6/(3^n-1)\to -6$ satisfy $|w_n^{-1}-(-6)|_3=c^{-2}|w_n-(-1/6)|_3=3^{-2}\cdot 3^{1-n}=3^{-1-n}$, illustrating the $c^{-2}$ factor when $c\ne 1$.
2. **A $5$-adic non-rational simple root with exact residual error.** At $p=5$, put $f(T)=T^2-6$ and $a_1=1$, so $f(a_1)=-5$ and $f'(a_1)=2$ ($3\cdot 2\equiv 1\pmod 5$). Inductively, given $a_n\in\mathbb Z$ with $a_n\equiv 1\pmod 5$ and $5^n\mid f(a_n)$, write $E_n=f(a_n)/5^n\in\mathbb Z$, choose the unique $t_n\in\{0,1,2,3,4\}$ with $t_n\equiv -3E_n\pmod 5$, and set $a_{n+1}=a_n+t_n 5^n$. Expanding the square gives
   $$
   f(a_{n+1}) = 5^n(E_n + 2a_n t_n + t_n^2 5^n) \equiv 5^n(E_n + 2t_n) \equiv 0 \pmod{5^{n+1}},
   $$
   with $a_{n+1}\equiv 1\pmod 5$. Telescoping shows $5^n\mid (a_m-a_n)$ for all $m\ge n\ge 1$, so $(a_n)_{n\ge 1}\in C$ defines $\alpha=[(a_n)]\in\mathbb Q_5$ with $|\alpha-\iota(a_n)|_5\le 5^{-n}$ and $|\alpha|_5=|a_1|_5=1$. Termwise multiplication gives $\alpha^2-\iota(6)=[(f(a_n))]=0$ since $|f(a_n)|_5\le 5^{-n}\to 0$, so $\alpha^2=6$ and $f'(\alpha)=2\alpha\ne 0$. No rational $q$ can satisfy $\alpha=\iota(q)$: injectivity of $\iota$ on $\iota(q^2)=\alpha^2=\iota(6)$ would force $q^2=6$ in $\mathbb Q$, contradicting $2v_2(q)=v_2(6)=1$. Because both $\alpha$ and $a_n$ lie at distance $\le 1/5$ from $1$, $|\alpha+a_n-2|_5\le 1/5<1=|2|_5$, so $|\alpha+a_n|_5=1$ for every $n\ge 1$. Factoring $a_n^2-6=(a_n-\alpha)(a_n+\alpha)$ therefore gives the exact distance $|\alpha-\iota(a_n)|_5=|f(a_n)|_5$ at every step (and the same factorization $(\beta-\alpha)(\beta+\alpha)=0$ forces uniqueness of $\alpha$ on $|\beta-1|_5<1$):

   | $n$ | $a_n$ | $E_n = (a_n^2-6)/5^n$ | $t_n$ | Exact $\lvert\alpha-\iota(a_n)\rvert_5 = \lvert f(a_n)\rvert_5$ |
   | --- | --- | --- | --- | --- |
   | $1$ | $1$ | $-1$ | $3$ | $1/5$ |
   | $2$ | $16$ | $10$ | $0$ | $1/125$ |
   | $3$ | $16$ | $2$ | $4$ | $1/125$ |
   | $4$ | $516$ | $426$ | $2$ | $1/625$ |
   | $5$ | $1766$ | $998$ | $1$ | $1/3125$ |
   | $6$ | $4891$ | $1531$ | $2$ | $1/15625$ |

   At $n=2$, $5\mid E_2=10$ produces $t_2=0$ and $a_3=a_2=16$, so $a_2$ already achieves error $5^{-3}=1/125$ strictly smaller than the generic Cauchy bound $5^{-2}$.

**Remarks (deleting primality, Lean conventions, consumer wiring and classical attribution).** Deleting the primality hypothesis breaks the construction at the rational base. For composite base $6$ with $e_6(b)=\max\{j\ge 0:6^j\mid b\}$, the unreduced formula assigns $e_6(1)-e_6(2)=0$ and $e_6(3)-e_6(6)=-1$ to $1/2=3/6$. Fixing reduced fractions (as Lean's `padicNorm 6` does) still fails multiplicativity on integers ($e_6(2)=e_6(3)=0$ while $e_6(6)=1$, giving $|2|_6|3|_6=1\ne 1/6=|6|_6$) and even violates the ordinary triangle inequality on rationals: $|1/2|_6=1$ and $|1/3|_6=1$, whereas $|1/2+1/3|_6=|5/6|_6=6 > 1+1=2$. Completing $\mathbb Z$ modulo $6^n$ instead yields $\varprojlim\mathbb Z/6^n\mathbb Z\cong\mathbb Z_2\times\mathbb Z_3$, where Chinese-remainder lifts of $(0,1)$ and $(1,0)\bmod (2^n,3^n)$ multiply to $0\bmod 6^n$ and produce nonzero zero divisors rather than a field.

In Lean, `Padic.valuation` and A2's `ord` are totalized $\mathbb Z$-valued functions returning $0$ at $x=0$, whereas `Padic.addValuation` uses $\top\in\mathtt{WithTop}\ \mathbb Z$ (`v_p(0)=+\infty`) and both `Padic.mulValuation` and A2's `normalizedValuation ℚ_[p]` take values in $\mathbb Z^{\mathrm m 0}$ (`WithZero (Multiplicative ℤ)`), sending $0\mapsto 0$ and $x\ne 0\mapsto\operatorname{WithZero.exp}(-v_p(x))$. In A2, this same `ℚ_[p]` instance feeds: (i) [§15.4.3.11](#154311-haar-measure-on-p-adic-balls-and-shells) (keeping its named `LocallyCompactSpace ℚ_[p]`, Borel, Hausdorff, second-countability and `PadicInt.irreducible_p` inputs, with C1–C5 established by secondary audit), (ii) the standard additive character and conductor calculation in `LocalFourierPadic.lean:57–223`, (iii) explicit local reciprocity over `ℚ_[p]` via `ExplicitQp.ord_eq_of_eq_mul_zpow` (`ExplicitQp.lean:336–348`), and (iv) the canonical continuous embedding `CharZero.padicHom : ℚ_[p] →+* K` into a characteristic-zero nonarchimedean local field of residue characteristic $p$, preserving valuation comparisons via `Padics/WithVal.lean:40–167` (`ExamplesCharZero.lean:113–199`). Integer-sequence limits and $\mathbb Z_p/p^n\mathbb Z_p$ quotients belong to [Chapter 10, §10.4.14](10-congruence-modules-to-sha.md#10414-a-compatible-tate-generator-for-torsion-coefficients) and [§10.4.16](10-congruence-modules-to-sha.md#10416-one-integral-primitive-from-coboundaries-at-every-level), while total boundedness and unit-ball compactness from finite residue fields belong to [Chapter 2, §2.3.5.1](02-functional-equations-and-primitive-characters.md#2351-finite-residue-fields-and-compact-unit-balls). [WithVal uniform bridge][ch15-qpc-withval] · [§15.4.3.13 on the target normalization](#154313-the-canonical-discrete-value-group-of-a-local-field)

The mathematical results are classical. Sutherland's Lecture 8 (Definitions 8.1–8.2, Proposition 8.3, §8.1.1 and Example 8.13) treats Cauchy completions of valued fields, topological-field continuity, rational density, extension of discrete valuations via eventual constancy, and the prime-$p$ specialization $\mathbb Q_p$. Lewis's CPP 2019 paper (§§4.1–4.4 and §5.1) documents this exact Lean quotient construction and explains why `PadicSeq.stationary` yields a $\mathbb Q$-valued norm without first constructing $\mathbb R$. Conrad's *Hensel's Lemma* (Theorem 2.1, Remark 2.4 and Theorem 4.1(1)) covers the integer simple-root lift and the exact residual distance $|\alpha-a_n|_p=|f(a_n)|_p$ when $|f'(a_n)|_p=1$. The prose and worked examples are `[Expository]`; local R3 `[Lean, read]` covers the cited Mathlib and A2 declarations. Local kernel replay, compiled `Main.lean` reachability and independent review of this subsection are tracked separately, and Masullo's positive-width strip nuclearity and $\alpha$-independence remain `[Open]`. [Sutherland, Lecture 8][ch15-qpc-sutherland] · [Lewis, CPP 2019][ch15-qpc-lewis] · [Conrad, Hensel's Lemma][ch15-qpc-conrad] · [Sources and consumers](../sources/SOURCES.md#chapter-15-rational-p-adic-completion)

[ch15-qpc-ratval]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean#L87-L329
[ch15-qpc-ratnorm]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNorm.lean#L45-L132
[ch15-qpc-ratmul]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNorm.lean#L133-L213
[ch15-qpc-nonarch]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Ring/IsNonarchimedean.lean#L78-L116
[ch15-qpc-stationary]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L168-L248
[ch15-qpc-norme]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L361-L523
[ch15-qpc-values]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L848-L883
[ch15-qpc-causeq]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Basic.lean#L49-L558
[ch15-qpc-quotinv]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/CauSeq/Completion.lean#L33-L273
[ch15-qpc-lift]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L599-L666
[ch15-qpc-metric]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L774-L824
[ch15-qpc-complete]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L673-L772
[ch15-qpc-complete-metric]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L994-L1035
[ch15-qpc-uniform]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/UniformSpace/Cauchy.lean#L904-L922
[ch15-qpc-padic]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L528-L594
[ch15-qpc-val]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L1039-L1239
[ch15-qpc-valrel]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/ValuativeRel.lean#L29-L47
[ch15-qpc-withval]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Padics/WithVal.lean#L40-L167
[ch15-qpc-sutherland]: https://math.mit.edu/classes/18.785/2017fa/LectureNotes8.pdf
[ch15-qpc-lewis]: https://doi.org/10.1145/3293880.3294089
[ch15-qpc-conrad]: https://kconrad.math.uconn.edu/blurbs/gradnumthy/hensel.pdf

#### 15.4.3.13 The canonical discrete value group of a local field

**Motivation.** The Cauchy quotient in [§15.4.3.12](#154312-completing-the-rationals-at-a-prime) has $p^{-1}$ as its first nonzero real value below $1$. What plays that role before choosing any real absolute value on a local field? The valuative relation already compares the values of field elements. From the original topology, Mathlib obtains a largest value strictly below $1$ and proves that its powers exhaust the nonzero values. This determines integer coordinates even when a real realization of the values is still unspecified.

**Example.** In $K=\mathbb Q_3$, one step below $1$ is the value of $3$. In $L=\mathbb Q_3(\pi)$ with $\pi^2=3$, one step below $1$ is the value of $\pi$. The original inclusion carries $3$ to an element two steps below $1$ in $L$. There is also a quadratic extension in which $3$ still gives one step, but the residue field has nine elements. These two effects will enter the real modulus in different ways.

**Definition.** Let $K$ have exactly the Lean inputs `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`. The last class supplies local compactness, the valuative topology for the given relation, and nontriviality of the relation. Write $G_0$ for `ValueGroupWithZero K`, $G=G_0^\times$, and $v:K\to G_0$ for `ValuativeRel.valuation K`. In the quotient construction of $G_0$, a class $[a,s]$ with $s\ne 0$ represents $v(a)/v(s)$. Comparison of $[a,s]$ and $[b,t]$ compares $at$ and $bs$ in the valuative relation. The map $a\mapsto[a,1]$ realizes all such classes since $[a,s]=v(a/s)$, and $v(x)=0$ exactly for $x=0$. In particular every element of $G$ comes from $K^\times$. Put $O=\{x:v(x)\le1\}$ and $\mathfrak m=\{x:v(x)<1\}$. An element of $O$ is a unit exactly when its value is $1$, by applying the valuation to it and its reciprocal. The nonunits form $\mathfrak m$, so $O$ is local. The fraction field is $K$, since a nonzero $x$ with $v(x)>1$ has $x^{-1}\in O$. A uniformizer means a generator of $\mathfrak m$ in the resulting DVR, equivalently an irreducible of $O$. [Canonical quotient and valuation][ch15-vg-rel] · [Original topology and ring][ch15-vg-local] · [Source and consumer ledger](../sources/SOURCES.md#chapter-15-canonical-discrete-value-group)

**Lemma (finite intervals in the original value group) [Lean, read].** Every closed interval of $G$ is finite.

*Proof.* The source starts with a compact neighbourhood $C$ of $0$ and a strict valuative ball of radius $r>0$ inside it. Choose $0<\rho<\min(r,1)$ in $G_0$. If $r<1$ one can use $r^2$, and if $r\ge1$ one can use any value strictly between $0$ and $1$, which exists by nontriviality and inversion. Thus the closed ball of radius $\rho$ lies in $C$. A closed ball of positive radius is an open additive subgroup by the ultrametric inequality, hence is closed as well. For any $\gamma>0$, use surjectivity to choose a scalar of value $\gamma/\rho$. Multiplication by it is a homeomorphism onto the ball of radius $\gamma$, so every such closed ball is compact. At $\gamma=0$ the ball is $\{0\}$. In particular $O$ is compact.

For $0<z\le1$, cover $O$ by the ball $v\le z$ and the spheres $v=g$ for $z<g\le1$. A positive-value sphere is open because adding an element of strictly smaller value leaves the value unchanged. This follows by applying the ultrametric inequality to the sum and then to the difference recovering the larger-value summand. Every sphere in the cover is nonempty by surjectivity and disjoint from the other covering sets. A finite subcover therefore sees every value strictly between $z$ and $1$, as well as $1$ when $z<1$. Including $z$ gives a finite $[z,1]$. Multiplication by the inverse of the upper endpoint reduces any nonempty interval to this form. The source obtains the same conclusion by inversion and splitting intervals at $1$. [Compact balls][ch15-vg-local] · [Open-sphere cover][ch15-vg-compact]

**Theorem (canonical coordinates and uniformizers) [Lean, read].** There is exactly one order-preserving multiplicative isomorphism $E:G_0\to \mathtt{WithZero}(\mathtt{Multiplicative} \mathbb Z)$. For every uniformizer $\pi$, $v(\pi)$ is the largest element of $G$ below $1$ and generates $G$. For every $x\in K^\times$ and every uniformizer $\pi$, there is a unique pair $(m,u)\in \mathbb Z\times O^\times$ with $x=\pi^m u$. The integer $m$ is independent of $\pi$.

*Proof.* In additive notation for $G$ with identity $0_G$, put $n(a)=\# [0_G,a)-\#[0_G,-a)$, where an interval with upper endpoint at or below its lower endpoint is empty. For $b\ge a$, one has $n(b)-n(a)=\#[a,b)$. If both endpoints are nonnegative, split $[0_G,b)$ at $a$. If both are nonpositive, split $[0_G,-a)$ at $-b$ and reverse the interval to $(a,b]$, which has the same size as $[a,b)$. If they straddle $0_G$, split $[a,b)$ at $0_G$ and translate $[a,0_G)$ by $-a$. Consequently $n(a+b)-n(a)=n(b)$ for $b\ge0_G$ by translation of $[a,a+b)$. For $b<0_G$, apply the nonnegative case to $a+b$ and $-b$. The function is strictly increasing because $[a,b)$ contains $a$ for $a<b$. Nontriviality gives a positive element, and finiteness below it gives a least positive element $d$. Since $n(d)=1$, the multiples of $d$ map onto every integer. This is the interval-count construction in `LocallyFiniteOrder.orderAddMonoidEquiv`, expressed multiplicatively by `orderMonoidEquiv`.

In multiplicative notation the inverse of the generator above $1$ is the largest element $g_-$ below $1$. The map sends $g_-^m$ to $\operatorname{exp}(-m)$, where $\operatorname{exp}(j)$ is the element labelled by $j$ in `Multiplicative ℤ`. Adjoin the least, absorbing element $0$ on both sides and send it to $0$. This extension preserves product and order, including comparisons with zero. Every order-preserving group isomorphism sends $g_-$ to $\operatorname{exp}(-1)$ because both are the immediate predecessor of $1$. Its values on all powers and on zero are consequently forced.

Now choose $\pi_0\in K^\times$ with $v(\pi_0)=g_-$. If $v(x)<1$, then $v(x)\le g_-$ and $x/\pi_0\in O$. Conversely every multiple of $\pi_0$ by an element of $O$ has value below $1$. Thus $\mathfrak m=(\pi_0)$. For any nonzero ideal of $O$, take an element $x$ whose nonnegative integer depth $m$ is minimal among its nonzero elements, where $v(x)=g_-^m$. Every $y$ in the ideal has $v(y)\le v(x)$, including $y=0$, and $y/x\in O$. The ideal is therefore $(x)$. The zero ideal is principal as well, and $\pi_0$ gives a nonzero nonunit. This proves the DVR assertion directly from the group result. In the actual source the DVR is a parallel instance: the finite intervals give a multiplicatively Archimedean range with a gap, the valuation-integer criterion gives principality, and nontriviality keeps the maximal ideal nonzero.

Two generators of $\mathfrak m$ divide each other in $O$. Cancelling their nonzero product factors shows they differ by a unit, so every uniformizer has value $g_-$. Given $x\ne 0$, let $m$ be the unique integer with $v(x)=g_-^m$. The element $u=\pi^{-m}x$ has value $1$, hence belongs to $O^\times$. In any such factorization the value forces $m$, and cancellation forces $u$ once $\pi$ is fixed. Replacing $\pi$ by $\pi w$ for $w\in O^\times$ replaces $u$ by $w^{-m}u$. In Lean, `valueGroupWithZeroIsoInt` uses the inverse of the range inclusion isomorphism (surjectivity of $v$) and the interval-count isomorphism on that range. A2 also proves the splitting directly from the DVR fraction-field factorization, and its first projection recovers this same $m$. $\square$ [Interval count and extension][ch15-vg-count] · [DVR instance and factorization][ch15-vg-dvr] · [A2 ledger](../sources/SOURCES.md#chapter-15-canonical-discrete-value-group)

**The sign, zero and the real modulus.** A2 defines `normalizedValuation K` by transporting $v$ through $E$. Thus it preserves and reflects the original comparisons, even at $0$. On $x\ne 0$ it gives $\operatorname{exp}(-m)$, while `ord x` is minus the integer label and equals $m$. Here $\operatorname{exp}(0)=1$, and the adjoined $0$ is distinct from every integer-labelled value. A2 totalizes its integer `ord` by $\operatorname{ord}(0)=0$ because `WithZero.log 0 = 0`. Its formula $\operatorname{exp}(-\operatorname{ord}(x))$ and the additive multiplication law for integer `ord` require nonzero inputs. The extended additive valuation instead sends $0$ to $+\infty$. For $x\ne 0$, positive order means a nonunit of $O$, order zero means a unit of $O$, and negative order means $x \notin O$. [Integer labels and zero][ch15-vg-exp] · [A2 valuation and order ledger](../sources/SOURCES.md#chapter-15-canonical-discrete-value-group)

Write $q=\lvert O/\mathfrak m\rvert>1$, finite by the local-field instance. For any real $b>1$, sending $\operatorname{exp}(j)$ to $b^j$ and $0$ to $0$ realizes the value group as $\{0\}\cup b^{\mathbb Z}$ in order-preserving fashion. This realizes the same valuation topology. The choice $b=q$ gives the residue-normalized absolute value $|x|_{\mathrm{res}}=q^{-\operatorname{ord}(x)}$ for $x\ne 0$, and $|0|_{\mathrm{res}}=0$. It equals A2's `modulus`. With additive Haar measure $\mu$ and $a\ne 0$, the direct-set factor in $\mu(aS)$ is $|a|_{\mathrm{res}}$, while $(x\mapsto ax)_*\mu$ has factor $|a|_{\mathrm{res}}^{-1}$. These are the scaling identities used above in [§15.4.3.11](#154311-haar-measure-on-p-adic-balls-and-shells). The integer coordinate comes from the ordered group. The real base $q$ comes from the residue field and calibrates Haar. [A2 modulus and consumers](../sources/SOURCES.md#chapter-15-canonical-discrete-value-group) · [Milne, §7 note 2 and Lemma 8.6][ch15-vg-milne]

**Two quadratic extensions on the original inclusion.** [Expository] Let $K=\mathbb Q_3$ with $|3|_3=1/3$, and use the scalar inclusion $a\mapsto a+0\theta$ into each quadratic field below. Sutherland's finite-extension theorem gives the complete absolute value $|N_{L/K}(x)|_3^{1/2}$ extending $|\cdot|_3$. We denote it by $|x|_{\mathrm{ext}}$. From the computed orders, the residue fields are finite, so the compactness criterion of [§2.3.5.1](02-functional-equations-and-primitive-characters.md#2351-finite-residue-fields-and-compact-unit-balls) supplies local compactness in the same topology. Each relation is nontrivial, witnessed by the displayed uniformizer. [Sutherland, Lecture 10, Theorem 10.4][ch15-vg-suth10]

1. **Totally ramified, $\pi=\sqrt{3}$.** Use the computation in [§2.3.5.1](02-functional-equations-and-primitive-characters.md#2351-finite-residue-fields-and-compact-unit-balls) on this very field. The odd order of $3$ proves irreducibility. Multiplication by $a+b\pi$ on $(1,\pi)$ has columns $(a,b)$ and $(3b,a)$, so its norm is $a^2-3b^2$. The distinct parities of $2v_3(a)$ and $1+2v_3(b)$ on nonzero terms give their minimum as the order of the norm. With $v_3(0)=+\infty$ this formula includes a zero coefficient. Hence $|a+b\pi|_{\mathrm{ext}}=3^{-m/2}$ for $m=\min(2v_3(a),1+2v_3(b))$ when $a+b\pi \ne 0$. The ring is $\mathbb Z_3+\mathbb Z_3\pi$, with maximal ideal $\pi O=3\mathbb Z_3+\mathbb Z_3\pi$. Reduction sends $a+b\pi \mapsto \bar a$ and a member of the ring is a unit exactly when $\bar a\ne 0$. Since $m(\pi)=1$, this is the canonical order. The identity $3=\pi^2$ gives $e=2$ and reduction gives $f=1$. In particular $(\pi,3,1+\pi,\pi^{-1})$ have orders $(1,2,0,-1)$ and canonical values $(\operatorname{exp}(-1),\operatorname{exp}(-2),1,\operatorname{exp}(1))$. Their real values are $(3^{-1/2},1/3,1,3^{1/2})$ for $|\cdot|_{\mathrm{ext}}$ and $(1/3,1/9,1,3)$ for $|\cdot|_{\mathrm{res}}$. For example $(1+\pi)^{-1}=(\pi-1)/2$, and $3=(\pi(1+\pi))^2((\pi-1)/2)^2$ exhibits the same exponent for the alternate uniformizer.
2. **Unramified, $i^2=-1$.** The polynomial $T^2+1$ has no root in $\mathbb F_3$, since the squares are $0,1$. A root over $\mathbb Q_3$ would have order zero and reduce to a root, so $L=K(i)$ is quadratic. Multiplication on $(1,i)$ has columns $(a,b)$ and $(-b,a)$ for $a+bi$, with norm $a^2+b^2$. For $a+bi\ne 0$ put $m=\min(v_3(a),v_3(b))$. Divide both coefficients by $3^m$. At least one is a unit, so the sum of the normalized squares is $1$ or $2$ modulo $3$. Thus $v_3(a^2+b^2)=2m$ and $|a+bi|_{\mathrm{ext}}=3^{-m}$. The integer ring is $\mathbb Z_3+\mathbb Z_3i$, its maximal ideal is $3O$, and reduction sends $a+bi\mapsto \bar a+\bar b\bar i$ in $\mathbb F_3[T]/(T^2+1)$. A pair of integral coefficients gives a unit exactly when at least one is nonzero modulo $3$. Here $\pi=3$, $e=1$, $f=2$ and $q=9$. The elements $(3,i,1+i,3^{-1})$ have orders $(1,0,0,-1)$ and canonical values $(\operatorname{exp}(-1),1,1,\operatorname{exp}(1))$. Their real values are $(1/3,1,1,3)$ for $|\cdot|_{\mathrm{ext}}$ and $(1/9,1,1,9)$ for $|\cdot|_{\mathrm{res}}$. The inverse $(1+i)^{-1}=(1-i)/2$ is integral, and $3=(3(1+i))((1-i)/2)$ checks the alternate uniformizer explicitly.

In both examples the inclusion induces the original residue inclusion $\mathbb F_3\to k_L$ on constants. On $K^\times$ one has $\operatorname{ord}_L(a)=e\,v_3(a)$ and $\operatorname{ord}_L(a)/e=v_3(a)$. In the group with zero the original inclusion sends $\operatorname{exp}(-v_3(a))$ to $\operatorname{exp}(-e v_3(a))$, and $0$ to $0$. The extending real absolute value restricts to $|\cdot|_3$. The residue-normalized one restricts to $3^{-ef v_3(a)}=|a|_3^2$ in each example. Thus the embedding preserves valuation comparisons, and is an isometry for the extending absolute value. To identify the inclusion with the A2 characteristic-zero construction, both maps agree on $\mathbb Q$, and continuity, density and Hausdorffness force the same extension to $\mathbb Q_3$. In general, for a finite extension with its extending valuation, a base uniformizer has the form $\pi_L^e w$ with $w\in O_L^\times$ and base units remain units. This gives the same $e$-fold restriction and $|a|_{L,\mathrm{res}}=|a|_{K,\mathrm{res}}^{ef}$ since $q_L=q_K^f$. [Sutherland, Lecture 10, Theorem 10.4 and Remark 10.7][ch15-vg-suth10] · [Milne, Lemma 8.6][ch15-vg-milne] · [A2 embedding ledger](../sources/SOURCES.md#chapter-15-canonical-discrete-value-group)

**What each hypothesis buys.** [Expository] Consider the field $\bigcup_{n\ge1}\mathbb F_3((t^{1/n!}))$ with the inclusions that send $t^{1/n!}$ to $(t^{1/(n+1)!})^{n+1}$. Least exponent gives an additive valuation with image $\mathbb Q$ on nonzero elements. Its positive exponents have no least element. In the induced valuation topology a compact neighbourhood of zero would contain some closed ball of positive radius. As in the lemma, scaling would make the integer ball compact, but the interval from the value of $t$ to $1$ contains all the distinct values of $t^{1/n!}$. Its open sphere cover forbids compactness. Thus this field retains the nontrivial relation and its topology and loses local compactness. If we give the very same field the discrete topology it becomes locally compact and retains the same nontrivial relation, but the singleton $\{0\}$ is open and contains no positive-radius valuative neighbourhood: powers of $t$ of sufficiently large exponent lie inside each such neighbourhood. This deletes compatibility and leaves the noncyclic value group intact. Finally, on a field with the trivial relation $G=\{1\}$ and $G_0=\{0,1\}$. Its induced topology is discrete because the strict ball of radius $1$ is $\{0\}$. It is locally compact with the compatible topology but lacks nontriviality and has $O=K$, $\mathfrak m=(0)$ and no uniformizer. These examples isolate the three components of the local-field class.

Bruhat proves the underlying local compactness criterion for a nontrivial valuation in an arbitrary totally ordered group. Sutherland establishes the uniformizer decomposition and its intrinsic order on a DVR, followed by the finite-extension comparison. The exact identification with the current Mathlib construction and the two explicit comparisons above are textbook exposition. The source reading covers the cited producers and identified local calls. Lean kernel replay, compiled declaration reachability from `Main`, and independent review of this section remain pending. [Bruhat, Part I, Ch. 1, §7, Theorem 3][ch15-vg-bruhat] · [Sutherland, Lecture 1, pp. 4–5][ch15-vg-suth1]

[ch15-vg-rel]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Valuation/ValuativeRel/Basic.lean#L330
[ch15-vg-local]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LocalField/Basic.lean#L45-L148
[ch15-vg-compact]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Topology/Algebra/Valued/LocallyCompact.lean#L184-L323
[ch15-vg-count]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/Monoid/LocallyFiniteOrder.lean#L72-L198
[ch15-vg-dvr]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/DiscreteValuationRing/Basic.lean#L321-L358
[ch15-vg-exp]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/GroupWithZero/WithZero.lean#L355-L414
[ch15-vg-suth1]: https://math.mit.edu/classes/18.785/2021fa/LectureNotes1.pdf
[ch15-vg-suth10]: https://math.mit.edu/classes/18.785/2021fa/LectureNotes10.pdf
[ch15-vg-milne]: https://www.jmilne.org/math/CourseNotes/ANT.pdf
[ch15-vg-bruhat]: https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr27.pdf

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
| **III. Origin of exponent $\frac{1}{2}$** | Discrete **AM–GM balance** $\min_m (x/m + m\,x^{O(\varepsilon)}) \asymp x^{1/2+O(\varepsilon)}$ at chain length $m \asymp \sqrt{x}$ (`core_gm` / `proposition_size_bound`, `P6`–`P7`). | Continuous diagonal Haar-measure matching $c_S\lvert x \rvert_{F,S}^{2a-1} = c_S \iff a = \frac{1}{2}$ for $S\ne\emptyset$ (`p. 16, p. 518`; proved as Theorems 15.3 and 15.6 in §§15.4.3.1–15.4.3.2, with $c_S$ a ratio of Haar measures by Corollary 15.9 in §15.4.3.3) + asserted **$\alpha$-independence** of strip trace on $W_{[-\alpha,\alpha]}^{s,2}\mathcal H_F$ (`p. 519`, `[Open]`). |
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
