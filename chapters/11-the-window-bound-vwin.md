# Chapter 11. The window bound `VWin`

> **Status tags used in this chapter:** `[Lean, read]` for declarations and `sorry`-free proof
> bodies read line by line in `ExistsPageN.lean`, `IsChiField.lean`, `StmtFields.lean`,
> `LengthEqAddEigen.lean`, `PrimeSetBoundDataOfPrimitiveChar.lean`, `IsCMFieldOfIsChiField.lean`,
> `ConductorBoundsOfIsChiField.lean`, `minusle.lean`, `ErrorTermsLeSqrtExpRpow.lean`,
> `AdmissibleOfPageN.lean`, `PointArith.lean`, `ThmHV.lean`, `CountVs.lean`, `SumOut.lean`,
> `FinalLe.lean`, `JointWinOfCounts.lean`, `PublishedTheorems/FerreroWashington.lean`,
> `FerreroWashingtonIndex/FerreroWashington.lean`, `ExistsIwasawaRankBoundOfFerreroWashington.lean`,
> `LemmaK.lean`, `KatoUse.lean`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/TaylorWilesObstructionBound.lean`,
> `WindowBoundOfLiteratureLevel.lean`, `TopMainZj.lean`, and `VwinOfRow.lean` (`R3`); `[Lean]` for
> statement-level inspections of imported sub-modules in the 157,603-module cone (`R2` / `R1`);
> `[Paper]` for citations to Alpöge's `remark.pdf` and Masullo's draft; `[Community]` for public
> audit and Zulip reports; `[Expository]` for classical Iwasawa, Euler-system, and Taylor–Wiles
> background and worked calculations; `[Open]` for unread deep proof cones and unverified
> statement-fidelity or domain-generality claims inside `AutomorphicVarieties/`.

At the end of Chapter 10 (`divinN_of_hypV`,
`src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:117`, Theorem 10.4)
[Lean, read], the entire Part II arithmetic engine reduced to a single global statement on the
cyclotomic CM host fields $E \subset \mathbb Q(\zeta_N)$: **the window bound `VWin`** (node **P12**,
`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:49`) [Lean, read].

Measured by import weight, **node P12 is the largest block in the entire 175,187-file archive**:
its 5-line top file `VwinOfRow.lean` imports **157,603 project modules** (90.0% of all files in the
archive!). Yet its top-level mathematical architecture is remarkably clean. At scale $x$ inside a
carefully chosen quadratic scale window $[Y, Y^2] \subset [X^{1/J}, X]$, `VWin` bounds the
$\log \ell$-weighted sum over **all** primes $\ell$ and all cyclotomic twists
$1 \le e < \lfloor x^{401} \rfloor$ of the Tate–Shafarevich lengths
$$\sum_{\ell \in S} \log \ell \sum_{1 \le e < \lfloor x^{401} \rfloor}
\operatorname{len}_{\mathbb Z_\ell}\,Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)
\le \sqrt{\exp(x^\varepsilon)} = \exp\bigl(x^\varepsilon / 2\bigr)$$
by splitting the left-hand side (`vvle_of_parts`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:127`) [Lean, read] into
**three pieces**, each controlled by a distinct pillar of modern algebraic number theory:

1. **The $\ell = 2$ tower and finitely many bad odd primes (`ThmBab`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:49`):**
   Bounded by $\exp(x^{4\varepsilon / 5})$ on a pigeonholed window $[Y, Y^2]$ using **Iwasawa theory**
   in the cyclotomic $\mathbb Z_\ell$-tower `[Iwasawa1959]`, `[Iwasawa1973]`, an in-archive proof of
   the **Ferrero–Washington theorem ($\mu = 0$)** `[FerreroWashington1979]` via Sinnott's rational-function
   method `[Sinnott1984]` (`FW.ferreroWashington`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104`), and a Soulé-type
   $K$-theoretic torsion bound `[Soule1979]` (`LemmaK`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GeneratorCountTuples/LemmaK.lean:13`) on the few exceptional twists
   near Iwasawa roots.
2. **The odd-$\ell$ minus eigenspace of complex conjugation (`ShaMinus`, `ThmBcFree`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:64`):**
   Bounded polynomially in $([E : \mathbb Q], \operatorname{cond}(E), t)$ — hence by
   $K \exp(8 x^{\varepsilon/4})$ — via the **cyclotomic Euler system** of Gauss/Jacobi sums and
   Stickelberger elements, mirroring the upper-bound half of the **Mazur–Wiles / Kolyvagin–Rubin**
   theory `[MazurWiles1984]`, `[Rubin2000]`.
3. **The odd-$\ell$ plus ("Vandiver") eigenspace of complex conjugation (`ShaPlus`, `ThmHV`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:79`):**
   Bounded by $(\operatorname{cond}(E)\cdot t)^C + C \exp(x^{4\varepsilon/5})$ by constructing a
   **nonzero rational integer annihilator `NN`** (`PropGK`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:36`) out of Frobenius trace
   differences on $U(3)$ and $\mathrm{GSp}_4$ Galois representations, combining **Kato's $\mathrm{GL}_2$
   Euler system** `[Kato2004]` (`KatoUse`, `:13`) with a **residually reducible ordinary modularity-lifting
   machine** built on **Taylor–Wiles patching** `[TaylorWiles1995]`, `[ClozelHarrisTaylor2008]`,
   `[Thorne2015]` (`PfromAut`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/TaylorWilesObstructionBound.lean:150`).

Once those three bounds are assembled, an elementary exponent comparison (`error_terms_le_sqrt_exp_rpow`,
`src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ErrorTermsLeSqrtExpRpow.lean:6`, read in full) squeezes their sum below $\exp(x^\varepsilon / 2)$
because $\frac{\varepsilon}{4} < \frac{4\varepsilon}{5} < \varepsilon$ — closing Part II!

---

## 11.1 Motivation

### 11.1.1 Why a subexponential bound $\exp(x^\varepsilon / 2)$ suffices to beat prime-window growth

At first glance, a number theorist opening `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:41–49` might be startled by the target
bound $\sqrt{\exp(x^\varepsilon)} = \exp(x^\varepsilon / 2)$ [Expository]. Classical conjectures on
class groups and cyclotomic $K$-groups (such as Kummer–Vandiver or Lichtenbaum–Quillen) predict
far smaller sizes, whereas unconditional analytic bounds (such as Brauer–Siegel on a field $E$ of
degree $[E : \mathbb Q] \asymp x^{2 + 8\varepsilon}$) give $\log \lvert d_E \rvert \asymp x^{2 + O(\varepsilon)}$,
so a naive discriminant bound on class numbers or Selmer groups would be $\exp(x^{2 + O(\varepsilon)})$ —
**exponentially too large**!

Why does $\exp(x^\varepsilon / 2)$ sit in the exact "Goldilocks zone" where it is simultaneously
**small enough** to close the analytic endgame of Chapters 5–10 and **large enough** to absorb all
conductor, Bernoulli, and Iwasawa error terms? Trace the two sides of the inequality [Expository]:

1. **Why $\exp(x^\varepsilon / 2)$ is small enough for Chapters 6, 9, and 10 (`phi_bound` and `divinN_of_hypV`):**
   Look back at how the scale parameter $b := \exp(x^\varepsilon)$ entered the chain of $m \asymp x^{1/2}$
   theta lifts:
   - In Chapter 6 (`phi_bound`, `src/Formalism/RankGapBounds/RankGapProofs/WeightedMeanData.lean:81`) and Chapter 9 (`SlopeIneq`), the concave
     logarithmic penalty $u_F \log(1 + \mathrm{HH}/u_F)$ from Bost's near-orthogonal frame inequality
     was linearized via $u \log(1 + H/u) \le \log(1 + X)(U + b)$ at $\mathrm{HH} \le x^{c_{\mathrm{HH}}} b$
     with $X = x^{c_{\mathrm{HH}}}$, costing only $O(\varepsilon (\log x)\,b) \ll b\,x^\varepsilon$
     because $\log(1 + x^{c_{\mathrm{HH}}})$ grows logarithmically!
   - In Chapter 10 (`vvRecord` and `divinN_of_hypV`, `src/Development/AutomorphicArithmetic/CharacterBoxes/DivinNOfHypV.lean:17,117`) [Lean, read], the
     total congruence denominator loss across the $m$ lifts had the shape $O\bigl(f m b (\log x)^2 + m B\bigr)$,
     where $B$ bounds $\sum_\ell \log \ell \sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)$. Setting
     $B = \sqrt{b} = \exp(x^\varepsilon / 2) \le b = \exp(x^\varepsilon)$ absorbs $m\sqrt{b}$ cleanly
     into the per-step budget $B_0 = f m b x^\varepsilon$, which in Chapter 5's `SZ.T3`
     (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:53`) is divided by the archimedean weight $a \asymp x^{1 + O(\varepsilon)} b$ —
     **cancelling the factor $b = \exp(x^\varepsilon)$ completely** and leaving $m \cdot x^{-1 + O(\varepsilon)} \ll x^{1/2 + O(\varepsilon)}$!
2. **Why $\exp(x^\varepsilon / 2)$ is large enough to swallow both polynomial conductor bounds and $4\varepsilon/5$ Iwasawa bounds:**
   Look at the conductor $\operatorname{cond}(E)$ of our CM host field $E \subset \mathbb Q(\zeta_N)$
   (`conductor_bounds_of_isChiField`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ConductorBoundsOfIsChiField.lean:77`) [Lean, read]:
   $$\operatorname{cond}(E) \le 2^{e(x) + 2} \cdot \psi.N \cdot q \cdot d.$$
   Remember from Chapter 4 (`WinPair`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:27–37`) that $2^{e(x)} \asymp x^{2 + 8\varepsilon}$,
   while the auxiliary primes $(q, d)$ were chosen at the subexponential scale $\log q \le Y^{\varepsilon/5}$
   and $\log d \le Y^{\varepsilon/5}(\log Y)^2$! Consequently, for $x \ge Y$,
   $$\log\bigl(\operatorname{cond}(E) \cdot \lfloor x^{401} \rfloor\bigr)
   \le (403 + 8\varepsilon)\log x + \log(8\,\psi.N) + x^{\varepsilon/4}
   \le 2\,x^{\varepsilon/4}$$
   for all large $x$ (`log_conductor_mul_height_le_of_pageN`,
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/LogConductorMulHeightLeOfPageN.lean:6`,
   invoked at `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean:49` and proved line by line in **Chapter 17**, Theorem 17.4(3)) [Lean, read]!
   Therefore **any bound that is polynomial in $(\operatorname{cond}(E), t)$ — even $(\operatorname{cond}(E)\cdot t)^{10{,}000}$! —
   has size $\exp\bigl(O(x^{\varepsilon/4})\bigr)$**, while the Iwasawa window bounds at $\ell = 2$ and
   $l \in B_\chi(\psi)$ have size $\exp(x^{4\varepsilon/5})$! Because
   $$\frac{\varepsilon}{4} < \frac{4\varepsilon}{5} < \varepsilon,$$
   every $\exp(O(x^{\varepsilon/4}))$ and $\exp(O(x^{4\varepsilon/5}))$ term is crushed beneath
   $\exp(x^\varepsilon / 2)$ as $x \to \infty$!

### 11.1.2 Plus versus minus, Vandiver's shadow, and why three methods are needed

Why can we not bound $Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)$ uniformly for
all primes $\ell$ and all twists $1 \le e < t$ by a single classical theorem [Expository]?

Recall from Poitou–Tate duality (`PTShaAt`, `src/Formalism/GaloisCohomology/Statement.lean:101`) that
for a CM field $E$ with maximal totally real subfield $F = E^+$ and complex conjugation $c \in \operatorname{Gal}(E/F)$,
$Ш^1\bigl(G_{E, S_\ell}, \mathbb Q_\ell / \mathbb Z_\ell(-e)\bigr)$ is Pontryagin dual to the kernel
of localization in $H^1\bigl(G_{E, S_\ell}, \mathbb Z_\ell(e + 1)\bigr)$ / unramified étale cohomology
$H^2(\mathcal O_E[1/\ell], \mathbb Z_\ell(e + 1))$, which for $e \ge 1$ tracks the $\ell$-primary
part of Quillen's even algebraic $K$-group $K_{2e}(\mathcal O_E)$ `[Soule1979]`. When $\ell \neq 2$,
$2 \in \mathbb Z_\ell^\times$ is invertible, so the involution $c$ splits $Ш^1$ into two eigenspaces
(`ShaPlus` with eigenvalue $(-1)^e$ and `ShaMinus` with eigenvalue $(-1)^{e+1}$, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:68–72`):

- **On `ShaMinus` (eigenvalue $(-1)^{e+1}$):** Complex conjugation acts with the parity where the
  equivariant Dirichlet/Hecke $L$-values $L(1 - (e + 1), \psi) = -\frac{B_{e+1, \psi}}{e + 1}$ are
  **generically nonzero**! Just as Herbrand–Ribet `[Ribet1976]` and Mazur–Wiles `[MazurWiles1984]`
  relate the minus part of the ideal class group of $\mathbb Q(\zeta_\ell)$ to generalized Bernoulli
  numbers $B_{1, \chi}$, the cyclotomic Euler system of Gauss/Jacobi sums `[Rubin2000]` bounds the
  $\psi$-component of `ShaMinus` by the $\ell$-adic valuation of $B_{e+1, \psi}$! Since the archimedean
  size $\lvert \mathrm{den}\cdot B_{e+1, \psi} \rvert$ of a single nonzero rational algebraic integer
  bounds $\sum_\ell \log \ell \cdot v_\ell(\dots)$ across **all** odd primes $\ell$ at once by the
  fundamental theorem of arithmetic $\sum_{\ell \mid M} v_\ell(M)\log \ell = \log\lvert M \rvert$,
  `ShaMinus` obeys an **unconditional, window-free polynomial bound** in $([E : \mathbb Q], \operatorname{cond}(E), t)$
  (`ThmBcFree`)!
- **On `ShaPlus` (eigenvalue $(-1)^e$ — the "Vandiver" side):** Complex conjugation acts with the
  opposite parity, where $L(-e, \psi) = 0$ vanishes trivially because of its archimedean $\Gamma$-factor!
  Over $\mathbb Q(\zeta_\ell)$, Kummer–Vandiver conjectures that $\mathrm{Cl}(\mathbb Q(\zeta_\ell)^+)[\ell] = 0$,
  which remains open after 175 years; over general abelian CM fields $E$ of conductor divisible by $q d$,
  `ShaPlus` need **not** vanish at all! As Alpöge writes in `remark.pdf` (p. 4, item 17 and fn. 6)
  [Paper; remark p. 4]:
  > *"11/15/26: for the classes in $H^1(\mathfrak o_E[1/\ell], \mathbb Q_\ell/\mathbb Z_\ell(-e))$
  > that we couldn't kill by twisting, fight for a significant weakening of Vandiver."*
  How do you bound `ShaPlus` across infinitely many primes $\ell$ without $L(-e, \psi) \neq 0$? By
  **reversing Ribet's method on $U(3)$**! A nonzero Selmer/$Ш^1$ class in `ShaPlus` builds a
  non-split $3$-dimensional residually Eisenstein Galois deformation of $\psi \oplus 1 \oplus \psi^{-1}$.
  Using Taylor–Wiles patching (`PfromAut`) and Kato's $\mathrm{GL}_2$ Euler system (`KatoUse` `[Kato2004]`)
  to identify the points of that deformation ring with cohomological automorphic forms $\rho$ on $U(3)$
  of bounded level and weight over an auxiliary imaginary quadratic field $K = \mathbb Q(\sqrt{-p_K})$,
  the Selmer length at every generic prime $\ell$ divides the $\ell$-adic valuation of a **single
  nonzero rational integer `NN`** (`PropGK`) built from Frobenius trace differences
  $\operatorname{tr}\rho(\mathrm{Frob}_p) - \bigl(\Psi(\mathrm{Frob}_p) + 1 + \Psi(\mathrm{Frob}_p)^{-1}\bigr)$
  at one small unramified prime $p$! Once again $\sum_\ell v_\ell(\mathrm{NN})\log \ell \le \log\lvert \mathrm{NN} \rvert$
  bounds **all generic primes $\ell$ simultaneously**!
- **At $\ell = 2$ and the finite set $B_\chi(\psi)$ of small/bad primes (`ThmBab`):** Neither $1/2 \in \mathbb Z_\ell$
  (at $\ell = 2$) nor unramified $U(3)$ congruence theory (at primes dividing $2 \cdot 3 \cdot \psi.N \cdot \operatorname{ord}(\psi) \cdots$)
  applies cleanly. But for a **fixed** prime $\ell$, our host field $E$ climbs the cyclotomic
  $\mathbb Z_\ell$-tower (at $\ell = 2$, $2^{e(x)} \asymp x^{2+8\varepsilon}$ is literally the $e(x)$-th
  layer of the cyclotomic $\mathbb Z_2$-extension!). By **Ferrero–Washington** `[FerreroWashington1979]`
  ($\mu_\ell = 0$), the $\ell$-rank $R$ of the Iwasawa module is **bounded independently of $(q, d)$ and
  of the tower height $e(x)$**! Thus only at most $R$ roots of the Iwasawa characteristic polynomial can
  create resonant twists $e$ with large $Ш^1$, and pigeonholing over $J$ disjoint windows $[Y, Y^2]$
  inside $[X^{1/J}, X]$ avoids any deep $\ell$-adic resonance while bounding shallow resonances via
  `LemmaK`!

---

## 11.2 Worked examples

Let us verify the three core mechanisms of Chapter 11 by explicit hand calculations [Expository].

### 11.2.1 Involution splitting (`length_eq_add_eigen`), why $\ell = 2$ breaks it, and Bernoulli primes $\ell = 37, 691$

1. **Exact eigenspace splitting when $2 \in R^\times$ vs. failure at $\ell = 2$:**
   Suppose $R = \mathbb Z_\ell$ and $N$ is a finite-length $R$-module carrying an $R$-linear involution
   $f : N \to N$ ($f^2 = \mathrm{id}_N$), and fix a sign $s = (-1)^e \in \{\pm 1\}$ ($s^2 = 1$).
   - When **$\ell \neq 2$**, $c := 2^{-1} \in \mathbb Z_\ell^\times$ exists! For every $x \in N$, set
     $$x_+ := \frac{1}{2}\bigl(x + s\,f(x)\bigr), \qquad x_- := \frac{1}{2}\bigl(x - s\,f(x)\bigr).$$
     Then $x_+ + x_- = x$, while $f(x_+) = \frac{1}{2}(f(x) + s x) = s\,x_+$ and
     $f(x_-) = \frac{1}{2}(f(x) - s x) = -s\,x_-$ (since $s^2 = 1$). Moreover, if $a \in N$ satisfies
     $f(a) = s a$ and $f(a) = -s a$, then $2 s a = 0 \implies a = 0$ because $2 s \in \mathbb Z_\ell^\times$!
     Thus $N \cong N^{f = s} \oplus N^{f = -s}$ as $\mathbb Z_\ell$-modules, so their Jordan–Hölder
     lengths add **on the nose**:
     $$\operatorname{len}_{\mathbb Z_\ell}(N)
     = \operatorname{len}_{\mathbb Z_\ell}\bigl(N^{f = (-1)^e}\bigr)
     + \operatorname{len}_{\mathbb Z_\ell}\bigl(N^{f = (-1)^{e+1}}\bigr)$$
     (`length_eq_add_eigen` and `shaLen_eq_add`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:10,88` [Lean, read])!
   - Now test **$\ell = 2$** ($R = \mathbb Z_2$) on the rank-$2$ $\mathbb F_2$-vector space
     $N = \mathbb F_2 \oplus \mathbb F_2$ with coordinate-swap involution $f(u, v) = (v, u)$ and $s = 1$:
     because $-1 = +1$ in $\mathbb F_2$, **both** eigenspaces $N^{f = +1}$ and $N^{f = -1}$ equal the
     diagonal line $\{(0, 0), (1, 1)\}$ of $\mathbb Z_2$-length $1$, yet $N^{f=+1} + N^{f=-1}$ is strictly
     smaller than $N$ (missing $(1, 0)$)! Even worse, on $N' = \mathbb Z/2\mathbb Z$ with $f = \mathrm{id}$
     and $s = 1$, $N' \cap \ker(f - 1) = \mathbb Z/2\mathbb Z$ AND $N' \cap \ker(f + 1) = \mathbb Z/2\mathbb Z$,
     so $\operatorname{len}(N'_{+}) + \operatorname{len}(N'_{-}) = 1 + 1 = 2 \neq 1 = \operatorname{len}(N')$!
     That concrete $2$-torsion collision is why `LengthEqAddEigen.lean` isolates $\ell = 2$ into
     `BoundedHeightTwoPlaceCondition` before splitting odd primes into `ShaPlus` and `ShaMinus`!

2. **How Bernoulli numerators bound a sum over *all* irregular primes $\ell$ at once:**
   Consider the classical cyclotomic prototype over $\mathbb Q$ (and $E = \mathbb Q(i)$, conductor $4$,
   primitive quadratic character $\chi_{-4}$) `[Washington1997]`:
   - At odd twist $e = 11$ ($e + 1 = 12$), the $12$-th Bernoulli number is
     $$B_{12} = -\frac{691}{2730}, \qquad \zeta(-11) = -\frac{B_{12}}{12} = \frac{691}{32{,}760}.$$
     Only the single irregular prime **$\ell = 691$** divides the numerator of $B_{12}/12$, reflecting
     the nontriviality of the $\omega^{-11}$-eigenspace of $\mathrm{Cl}(\mathbb Q(\zeta_{691}))[691]$
     (and of $K_{22}(\mathbb Z)[691]$)! Similarly, at $e = 31$ ($e + 1 = 32$),
     $$B_{32} = -\frac{7{,}709{,}321{,}041{,}217}{510}
     = -\frac{37 \times 683 \times 305{,}065{,}927}{510}$$
     is divisible in its numerator by the three irregular primes $\ell \in \{37, 683, 305{,}065{,}927\}$ —
     and **no other odd prime $\ell > 33$ in the entire universe** can divide its numerator! Summing
     $\log \ell \cdot v_\ell(\mathrm{num}(B_{32}))$ over *all* primes $\ell$ gives simply
     $\log(7{,}709{,}321{,}041{,}217) \approx 29.67$!
   - Likewise, for the odd Dirichlet character $\chi_{-4}$ mod $4$ ($B_{k, \chi_{-4}} = 4^{k-1}\bigl(B_k(1/4) - B_k(3/4)\bigr)$),
     direct evaluation gives $B_{1, \chi_{-4}} = -\frac{1}{2}$, $B_{3, \chi_{-4}} = \frac{3}{2}$,
     $B_{5, \chi_{-4}} = -\frac{25}{2}$ (while $B_{2m, \chi_{-4}} = 0$ for even indices because $\chi_{-4}$
     is odd!). For any character $\psi$ mod $N$ with $\psi(-1) = (-1)^{e+1}$, the functional equation
     of $L(s, \psi)$ bounds $\lvert L(-e, \psi) \rvert = \frac{\lvert B_{e+1, \psi} \rvert}{e + 1}$ by
     $(N(e + 1))^{O(N e)}$ — in fact $\log\lvert \mathrm{den}\cdot B_{e+1, \psi} \rvert \ll (e + 1)\log(N(e + 1))$!
     That single archimedean bound on a nonzero integer is the prototype for **both** the Euler-system
     minus bound `minusBound` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean:69`) and the $U(3)$ trace-difference integer `NN` in
     `PropGK` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:36`)!

### 11.2.2 Toy Iwasawa root-avoidance pigeonhole on $[Y, Y^2]$ and the $\frac{\varepsilon}{4} < \frac{4\varepsilon}{5} < \varepsilon$ squeeze

Why does `VWinAt` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:44–47`) assert that **inside every super-window $[X^{1/J}, X]$ there
exists a quadratic sub-window $[Y, Y^2]$** on which `VAt` holds, rather than holding at *every* scale $x$
at $\ell = 2$? Watch the Iwasawa algebra $\Lambda = \mathbb Z_\ell[[T]]$ in action [Expository]:

1. Suppose a finitely generated torsion $\Lambda$-module $X_\infty$ in the cyclotomic $\mathbb Z_\ell$-tower
   has **$\mu = 0$** (by Ferrero–Washington!) and $\lambda$-invariant $R = 1$: say
   $$X_\infty = \mathbb Z_\ell[[T]] / \bigl(1 + T - \kappa_\ell^{e_\ast}\bigr),$$
   where $\kappa_\ell = 1 + 4 = 5$ for $\ell = 2$ (or $1 + \ell$ for odd $\ell$) is the topological
   generator action of $\Gamma \cong \mathbb Z_\ell$ on $\mathbb Z_\ell(1)$, and $e_\ast \in \mathbb Z_\ell$
   is a single $2$-adic "bad root" (imagine $e_\ast$ has its first $10^6$ binary digits matching some
   integer $e_0$!).
2. Twisting by $\chi_{\mathrm{cyc}}^{-e}$ ($1 \le e < t(x) = \lfloor x^{401} \rfloor$) and descending to
   finite level specializes $1 + T \mapsto \kappa_\ell^e$, producing a cyclic $\mathbb Z_\ell$-quotient
   of length controlled by
   $$v_\ell\bigl(\kappa_\ell^e - \kappa_\ell^{e_\ast}\bigr)
   = v_\ell(\kappa_\ell - 1) + v_\ell(e - e_\ast).$$
   Look closely at $v_\ell(e - e_\ast)$:
   - For **all but at most one** integer $e \in [1, \lfloor x^{401} \rfloor)$, the distance $\lvert e - e'\rvert_\ell$
     between any two *distinct* integers $e \neq e'$ below $x^{401}$ satisfies $\ell^{v_\ell(e - e')} \le \lvert e - e' \rvert < x^{401}$,
     so **$v_\ell(e - e_\ast) \le \frac{401 \log x}{\log \ell}$** — logarithmic in $x$!
   - However, for the **single** integer $e_{\mathrm{bad}} \in [1, \lfloor x^{401} \rfloor)$ closest
     $\ell$-adically to $e_\ast$, $v_\ell(e_{\mathrm{bad}} - e_\ast)$ could a priori be huge at the
     scale $x \approx e_{\mathrm{bad}}^{1/401}$ where $e_{\mathrm{bad}}$ first enters $[1, \lfloor x^{401} \rfloor)$!
   - Now apply `LemmaK` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/GeneratorCountTuples/LemmaK.lean:13`) at that single resonant integer $e_{\mathrm{bad}}$! If
     $e_{\mathrm{bad}}$ is tiny — say $e_{\mathrm{bad}} \le x^{\delta}$ for $\delta = \frac{4\varepsilon}{5 C_K}$ —
     then Soulé's $K$-theory bound $\log \# H^2(\mathbb Z_\ell(e_{\mathrm{bad}} + 1)) \le \exp\bigl((2 e_{\mathrm{bad}} [L_1 : \mathbb Q])^{C_K}\log(2\lvert d_{L_1}\rvert)\bigr)$
     (applied on a fixed base layer $L_1$ of bounded degree independent of $(q, d, x)$!) is **already at
     most $\exp(x^{4\varepsilon / 5})$**!
   - And how many disjoint scale intervals $[Y_0, Y_0^2], [Y_1, Y_1^2], \dots, [Y_{J-1}, Y_{J-1}^2]$
     with $Y_{r+1} = Y_r^{K'}$ can have their *newly entering* twists $e \in [Y_r^{\delta}, Y_r^{802}]$
     hit one of the $R$ roots $e_{\ast, 1}, \dots, e_{\ast, R} \in \mathbb Z_\ell$ to super-logarithmic
     $\ell$-adic precision? **At most $1$ scale interval per root — at most $R$ intervals in total!**
     Because Ferrero–Washington ($\mu = 0$) makes $R$ **uniformly bounded** (depending only on $\psi$
     and $B_\chi(\psi)$, never on $q, d$, or $X$!), choosing $J = B.\mathrm{J} = 2^{R+2}(2 C_K C_t / \varepsilon)^R$
     (`BConst.J`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:20–21` [Lean, read]) guarantees by the
     **pigeonhole principle** at least one clean window $[Y, Y^2] \subset [X^{1/J}, X]$ on which both
     `BaAt` ($\ell = 2$) and `BbAt` ($l \in B_\chi(\psi)$) stay below $\exp(x^{4\varepsilon/5})$!

3. **Numerical check of the final subexponential squeeze (`error_terms_le_sqrt_exp_rpow`):**
   Take $\varepsilon = 1/60 < 1/52$ and compare the three exponents in
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ErrorTermsLeSqrtExpRpow.lean:6–9` [Lean, read]:
   - Minus-part / conductor exponent: $\frac{\varepsilon}{4} = \frac{1}{240} \approx 0.00417$;
   - $\ell = 2$ and bad-prime window exponent: $\frac{4\varepsilon}{5} = \frac{1}{75} \approx 0.01333$;
   - Target `HypV` exponent: $\varepsilon = \frac{1}{60} \approx 0.01667$, where $\sqrt{\exp(x^\varepsilon)} = \exp\bigl(\frac{1}{2} x^{1/60}\bigr)$.
   Because $x^{1/60} = x^{1/75} \cdot x^{1/300}$ (`hc : x ^ eps = b * s` at
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ErrorTermsLeSqrtExpRpow.lean:33`, where $b = x^{4\varepsilon/5}$ and $s = x^{\varepsilon/5}$!), as
   soon as $s = x^{\varepsilon/5} \ge 2(D + \log N + 1)$, multiplying $b$ by $s/2$ dominates $D b + \log N$:
   $$N\,\exp\bigl(D\,x^{4\varepsilon/5}\bigr) \le \exp\Bigl(\frac{1}{2}\,x^\varepsilon\Bigr) = \sqrt{\exp(x^\varepsilon)}!$$

---

## 11.3 Definitions

We now record the exact Lean declarations of node **P12**, separating the small-cone `R3`-verified
statement and assembly files from the deep modularity/Kato/K-theory interface definitions.

### 11.3.1 Host fields, conductor, and the master target `VWin` (`ExistsPageN.lean`, `StmtFields.lean`)

**Definition 11.1 (`VVle`, `IsChiField`, `PageN`, `VAt`, `VWinAt`, `VWin`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12,19,39,41,44,49`, and `condF`, `Bchi`, `minusBound`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean:44,66,69`).** [Lean, read]

1. **Bounded $\log \ell$-weighted $Ш^1$ sum (`VVle`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12–17`):** For a number field $E$,
   a twist cutoff $t \in \mathbb N$, and a real bound $B \in \mathbb R$, `VVle E t B : Prop` asserts that
   for every algebraic closure $\Omega / E$ and every family of prime-level cohomological packages
   `ld : ∀ p [Fact p.Prime], LData E Ω p`,
   - *(finiteness)* for every prime $p$ and every $0 < e < t$, $\mathrm{shaLen}(\mathrm{ld}\,p, e) \neq \top$; and
   - *(uniform partial-sum bound)* for every finite set $S$ of primes,
     $$\sum_{\ell \in S} \log \ell \sum_{1 \le e < t} \bigl(\mathrm{shaLen}(\mathrm{ld}\,\ell, e).\mathrm{toNat} : \mathbb R\bigr) \le B.$$
2. **Cyclotomic CM host characterization (`IsChiField`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:19–25`; generalized to subgroup data `AbF` as `IsCompField`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean:36–42`):**
   Given a primitive Dirichlet character $\psi : \mathrm{PChar}$ of conductor $\psi.N$, a $2$-adic exponent
   $e \in \mathbb N$, and auxiliary primes $q, d \in \mathbb N$, `IsChiField ψ e q d E` asserts that $E$
   embeds via $j : E \hookrightarrow \mathbb Q(\zeta_N)$ ($2^{e+2} \mid N$, $\psi.N \mid N$, $q \mid N$, $d \mid N$)
   as the exact fixed field of all $\tau_a : \zeta_N \mapsto \zeta_N^a$ satisfying
   $$\bigl(a \equiv \pm 1 \pmod{2^{e+2}}\bigr) \ \wedge\ \psi(a) = 1 \ \wedge\ \Bigl(\frac{a}{q}\Bigr) = 1 \ \wedge\ \Bigl(\frac{a}{d}\Bigr) = 1.$$
   Its minimal cyclotomic conductor is `condF E := sInf {N | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)}` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean:44`).
3. **Scale page, pointwise bound, window bound, and `VWin` (`PageN`, `VAt`, `VWinAt`, `VWin`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:39–49`):**
   - `PageN eps x e` (`:39`): $x^{2 + 8\varepsilon} \le 2^e \le 2\,x^{2 + 8\varepsilon}$ (inhabited for all $\varepsilon > 0$ by `exists_pageN`, `:67`);
   - `VAt ψ eps Ct q d e x` (`:41`): for every number field $E$ satisfying `IsChiField ψ e q d E`,
     `VVle E ⌊x ^ Ct⌋₊ (Real.sqrt (Real.exp (x ^ eps)))`;
   - `VWinAt ψ Ct` (`:44`): for every $0 < \varepsilon < 1/52$ and every page function $e : \mathbb R \to \mathbb N$
     satisfying `∀ x ≥ 1, PageN eps x (e x)`, there exist $J \ge 1$ and $X_0$ such that for all $X \ge X_0$
     and all $(q, d)$ satisfying `WinPair eps (X ^ (1 / J)) q d`, there exists $Y$ with
     $X^{1/J} \le Y$ and $Y^2 \le X$ such that `VAt ψ eps Ct q d (e x) x` holds for **all $x \in [Y, Y^2]$**;
   - `VWin : Prop` (`:49`): `∀ ψ : PChar, VWinAt ψ 401`.
4. **Auxiliary bad-prime set and explicit minus-part bound (`Bchi`, `minusBound`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean:57–71`):**
   For $\psi : \mathrm{PChar}$ of multiplicative order $o = \mathrm{ordC}\,\psi$, let $p_K(\psi)$ be the
   least prime $p \equiv 3 \pmod 4$ with $p \ge 7$ and $\gcd(p, \psi.N) = 1$, let $h^{\ast}(\psi) = h(\mathbb Q(\sqrt{-p_K(\psi)}))$,
   and let $p_1(\psi)$ be the least prime $p \equiv 1 \pmod{o_{\mathrm{odd}}}$ coprime to $2\,\psi.N\,p_K(\psi)$. Then
   $$B_\chi(\psi) := \{3\} \cup \bigl\{\text{odd prime factors of } o \cdot \psi.N \cdot p_K(\psi) \cdot h^{\ast}(\psi) \cdot p_1(\psi)\bigr\},$$
   and for real constant $C$ and natural numbers $(o, n, N, t)$,
   $$\mathrm{minusBound}(C, o, n, N, t) := 3 n t^2 \log(t N) + C \sum_{\substack{\ell \mid o \\ \ell \text{ odd prime}}} \ell\,n^2 t^2 \bigl(\log(t \ell N)\bigr)^2.$$

### 11.3.2 Three-way parity decomposition and window propositions (`LengthEqAddEigen.lean`, `PrimeSetBoundDataOfPrimitiveChar.lean`)

**Definition 11.2 (`ShaPlus`, `ShaMinus`, `BoundedHeightTwoPlaceCondition`, `VVminusLe`, `VVplusLe`, `ThmBab`, `ThmBcFree`, `ThmHV`, `JointWin`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:68,71,107,111,113,120` and `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:49,64,75,79,88`).** [Lean, read]

1. **Plus and minus submodules (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:64–76`):** Over a CM field $E$ with complex
   conjugation `cE E : E ≃+* E` acting on $H^1(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e))$ via
   `cAct D e`, define
   $$\mathrm{ShaPlus}(D, e) := \mathrm{Sha}(D, e) \cap \ker\bigl(\mathrm{cAct}(D, e) - (-1)^e\bigr),
   \quad
   \mathrm{ShaMinus}(D, e) := \mathrm{Sha}(D, e) \cap \ker\bigl(\mathrm{cAct}(D, e) - (-1)^{e+1}\bigr),$$
   with $\mathbb Z_\ell$-lengths `plusLen D e` and `minusLen D e`.
2. **The three prime/parity predicates (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:107–125`):**
   - `VVat l E t B` (`:107`): finiteness of $\mathrm{shaLen}(D, e)$ for $0 < e < t$ and unweighted sum
     $\sum_{1 \le e < t} \mathrm{shaLen}(D, e) \le B$ at the single prime $\ell$; at $\ell = 2$ this is
     `BoundedHeightTwoPlaceCondition E t B` (`:111`);
   - `VVminusLe E t B` (`:113`) and `VVplusLe E t B` (`:120`): finiteness at all odd primes $p \neq 2$
     and $\sum_{\ell \in S} \log \ell \sum_{1 \le e < t} \mathrm{minusLen}(\mathrm{ld}\,\ell, e) \le B$
     (respectively `plusLen`) for every finite set $S$ of **odd** primes ($\forall \ell \in S,\ \ell \neq 2$).
3. **The three global component theorems (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:12–94`):**
   - `ThmBab K Ct` (`:49`,given `K : BConst` with $R = R_0(M) + \sum_{\ell \in B'} R_\ell(L_\ell)$ and
     window count $K.J = 2^{R+2}(2 C_K C_t / \varepsilon)^R$, `:18–21`): inside every super-window
     $[X^{1/K.J}, X]$ with $\log(qd) \le X^{\varepsilon / (4 K.J)}$, there exists $Y \in [X^{1/K.J}, X^{1/2}]$
     such that for all $x \in [Y, Y^2]$, **both** `BaAt` (`BoundedHeightTwoPlaceCondition E (t x) (exp(x^{4ε/5}))`)
     and `BbAt` (`VVat l L₁ (t x) (exp(x^{4ε/5}))` on the fixed cyclotomic layer $L_1$ at each bad prime
     $l \in B'$) hold simultaneously;
   - `ThmBcFree` (`:64`, equivalent for $C_t \ge 1$ to `ThmBc Ct` by `thmBc_iff`, `:112`): there exists $C$
     such that for **every** composite CM host field `IsCompField M e q d E` ($e, t \ge 2$, `PrimePair M.m q d`),
     `VVminusLe E t (minusBound C M.deg [E : ℚ] (condF E) t)` holds **without restricting $x$ to a window**;
   - `ThmHV K Ct` (`:79`): on any `IsBWindow` $[Y, Y^2]$ supplied by `ThmBab` (where `BbAt` already
     controls the bad primes $l \in B_\chi(\psi)$!), every $x \in [Y, Y^2]$ satisfies `HVAt`, i.e.,
     `VVplusLe E (t x) ((condF E * t x)^C + C * exp(x^{4ε/5}))`;
   - `JointWin Ct` (`:88`): combines `BaAt` and `HVAt` on a common window $[Y, Y^2]$.

### 11.3.3 Deep P12 ingredients: `FerreroWashington`, `LemmaK`, `KatoUse`, `PropGK`, and `PfromAut`

**Definition 11.3 (Internal P12 theorem interfaces).** [Lean, read]

1. **Rank-form Ferrero–Washington (`UpperTheory.V.Published.FerreroWashington`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:7`):**
   For every prime $\ell$ and every abelian number field $K / \mathbb Q$ containing $\mu_4$ (if $\ell = 2$)
   or $\mu_\ell$ (if $\ell \neq 2$), there exists $r \in \mathbb N$ such that for every $n \in \mathbb N$
   and every $n$-th cyclotomic $\ell$-layer $K' / K$ (`IsCyclotomicExtension {l ^ n} K K'`),
   $$\bigl\lvert \mathrm{Cl}(\mathcal O_{K'}) / \mathrm{Cl}(\mathcal O_{K'})^\ell \bigr\rvert \le \ell^r.$$
2. **Soulé-type $H^2$ torsion bound (`UpperTheory.V.LemmaK`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GeneratorCountTuples/LemmaK.lean:13`):**
   `LemmaK CK : Prop` asserts that for every prime $\ell$, every totally complex number field $L$ containing
   $\mu_4$ ($\ell = 2$) or $\mu_\ell$ ($\ell \neq 2$), and every $e \ge 1$, the global étale cohomology group
   $H^2\bigl(G_{L, S_\ell}, \mathbb Z_\ell(e + 1)\bigr)$ (`H2 (zlTw D (e + 1))`) is finite with
   $$\log\bigl\lvert H^2\bigl(G_{L, S_\ell}, \mathbb Z_\ell(e + 1)\bigr) \bigr\rvert
   \le \mathrm{kBound}(C_K, e, [L : \mathbb Q], \lvert d_L \rvert)
   := \exp\Bigl(\bigl(2 e [L : \mathbb Q]\bigr)^{C_K}\,\log\bigl(2\lvert d_L \rvert\bigr)\Bigr).$$
3. **Kato's Euler-system vanishing and the $U(3)$ trace annihilator (`KatoUse`, `PropGK`, `CorGK`, `OneChar`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:13,36,44,54`):**
   - `KatoUse` (`:13`): for any odd prime $\ell$, integer $e \ge 1$, weight-$(2e + 1)$ classical newform $f$,
     attached $2$-dimensional Galois representation $W : G_{\mathbb Q} \to \mathrm{GL}_2(\overline{\mathbb Q}_\ell)$
     twisted by $\chi_{\mathrm{cyc}}^{-e}$, and finite-order character $\varphi$ satisfying `KillsMu M φ`,
     the Bloch–Kato Selmer group of the twisted representation vanishes (`BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W φ))`);
   - `PropGK` (`:36`): for every number field $K$, there exist $c_5, A \in \mathbb N$ such that for all
     $e \ge 1$, modulus $N \ge 1$, subgroup $H \le (\mathbb Z/N\mathbb Z)^\times$, and prime
     $p \nmid 30 N \lvert d_K \rvert$, there exists a **nonzero integer $\mathrm{NN} \in \mathbb Z \setminus \{0\}$**
     satisfying
     $$\log\lvert \mathrm{NN} \rvert \le c_5\,\varphi\bigl([(\mathbb Z/N\mathbb Z)^\times : H]\bigr)\,(N(e + 1))^A \log p$$
     such that for **every prime $\ell \neq p$** and every coefficient ring $c : \mathrm{Coef}\,\ell$ whose
     $H$-orbit satisfies the generic datum `GD`, all orbit Selmer/plus lengths are finite and satisfy
     $$\sum_{\psi \in \mathrm{orb}(c, H)} V_n(\Omega, c, e, \psi) \le 2\,v_\ell(\mathrm{NN})!$$
     (Compare `OneChar` at `:54–65`, which exhibits the per-character upper bound as
     $2 \sum_{\rho \in X} v_\ell\bigl(\operatorname{tr}\rho(\sigma) - (\Psi(\sigma) + 1 + \Psi(\sigma)^{-1})\bigr)$
     over pairwise non-isomorphic admissible $3$-dimensional representations $\rho : G_K \to \mathrm{GL}_3(\overline{\mathbb Q}_\ell)$!)
4. **Taylor–Wiles patching for universal ordinary determinant rings (`TaylorWilesObstructionBound`, `PfromAut`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/TaylorWilesObstructionBound.lean:88,126,136,150`):**
   Given Galois cohomology duality `CohP` (`:23–31`), a CM field $L$, an ordinary `HidaSetting l L Ω`
   with level `V0`, Taylor–Wiles prime systems `TWPl r T` (`:88–111`, adjoining split primes $w_{N,j}$
   outside $S$ with controlled Frobenius `fr` and tame inertia generator `τ`), and universal ordinary
   determinant (pseudo-deformation) ring `B : UniversalOrdinaryDeterminantRing r` with ideal $J \triangleleft B$:
   `PfromAut` (`:150–154`) asserts that under local class field theory `LocCFT s`, cyclotomic non-triviality
   mod $\ell$, and existence of patched automorphic modules `HasAut B J` (`:147`), the core modularity
   propagation properties `B.P1core J ∧ B.P3core J` hold!

---

## 11.4 Lemmas and proofs

We now prove in full human prose every `R3`-read theorem assembling `VWin` from its three components,
walk through the archive's `R3` top-level proof of `FW.ferreroWashington`, and trace the 157,603-module
modularity wiring `vwin_of_row`.

### 11.4.1 Exact involution splitting and three-part `VVle` assembly (`LengthEqAddEigen.lean`)

**Proposition 11.1 (Module-length eigenspace additivity and `vvle_of_parts`).** [Lean, read]

1. *(`length_eq_add_eigen`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:10–55`)* *Let $R$ be a commutative ring in which
   $2 \in R^\times$ is a unit, $M$ an $R$-module, $N \le M$ a submodule, $f \in \operatorname{End}_R(M)$
   an $R$-linear involution ($f(f(x)) = x$ for all $x \in M$) preserving $N$ ($f(N) \subseteq N$), and
   $s \in R$ an element with $s^2 = 1$. Then*
   $$\operatorname{len}_R(N) = \operatorname{len}_R\bigl(N \cap \ker(f - s)\bigr) + \operatorname{len}_R\bigl(N \cap \ker(f + s)\bigr).$$
2. *(`shaLen_eq_add` and `vvle_of_parts`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:88–103, 127–189`)* *Let $E$ be a CM
   number field and $t \in \mathbb N$. For every odd prime $\ell \neq 2$, every package $D : \mathrm{LData}\,E\,\Omega\,\ell$,
   and every $e \in \mathbb N$, $\mathrm{shaLen}(D, e) = \mathrm{plusLen}(D, e) + \mathrm{minusLen}(D, e)$
   in $\mathbb N_\infty$. Consequently, if `BoundedHeightTwoPlaceCondition E t B₂`, `VVminusLe E t Bm`,
   and `VVplusLe E t Bp` hold, then*
   $$\mathrm{VVle}\bigl(E,\ t,\ B_2 \log 2 + B_m + B_p\bigr) \quad \text{holds!}$$

*Proof.*
(1) Set $c := 2^{-1} \in R^\times$ (`2 * c = 1`, `:13–14`). For any $x \in M$, since $f^2 = \mathrm{id}$
and $s^2 = 1$, we have $f(x + s f(x)) = f(x) + s x = s(x + s f(x))$ (`eP`, `:15`) and
$f(x - s f(x)) = f(x) - s x = (-s)(x - s f(x))$ (`eQ`, `:18`). Because $N$ is $f$-stable, for $x \in N$
the projections $\pi_+(x) := c(x + s f(x))$ and $\pi_-(x) := c(x - s f(x))$ land in
$N_+ := N \cap \ker(f - s)$ and $N_- := N \cap \ker(f + s)$, respectively (`memP`, `memQ`, `:22–27`).
Define $R$-linear maps $\Phi = (\pi_+, \pi_-) : N \to N_+ \times N_-$ and $\Psi : N_+ \times N_- \to N$,
$\Psi(a, b) := a + b$ (`back`, `:38`). Then:
- For any $x \in N$, $\Psi(\Phi(x)) = c(x + s f(x)) + c(x - s f(x)) = 2 c x = x$ (`h₂`, `:51–54`);
- For $(a, b) \in N_+ \times N_-$ ($f(a) = s a$, $f(b) = -s b$),
  $\pi_+(a + b) = c(a + s(s a)) + c(b + s(-s b)) = 2 c a + 0 = a$ since $s^2 = 1$, and symmetrically
  $\pi_-(a + b) = b$ (`h₁`, `:40–50`).
Hence $\Phi$ is an $R$-linear isomorphism $N \simeq_R N_+ \times N_-$, so Mathlib's
`LinearEquiv.length_eq` and `Module.length_prod` give $\operatorname{len}_R(N) = \operatorname{len}_R(N_+) + \operatorname{len}_R(N_-)$ (`:55`).

(2) For any prime $\ell \neq 2$, $2 \notin \ell\mathbb Z_\ell$ is a unit in $\mathbb Z_\ell$ (`h2`, `:89–96`),
`cAct D e` is a $\mathbb Z_\ell$-linear involution (`cAct_cAct`, `:78–83`) preserving `Sha D e`
(`cAct_mem_Sha`, `:85–86`), and $(-1)^e \in \mathbb Z_\ell$ satisfies $((-1)^e)^2 = 1$ with
$-(-1)^e = (-1)^{e+1}$ (`:97–102`). Part (1) therefore gives $\mathrm{shaLen}(D, e) = \mathrm{plusLen}(D, e) + \mathrm{minusLen}(D, e)$.
Now assume `h2 : BoundedHeightTwoPlaceCondition E t B₂`, `hm : VVminusLe E t Bm`, and `hp : VVplusLe E t Bp` (`:127–133`):
- *Finiteness:* At $p = 2$, `h2` gives $\mathrm{shaLen}(\mathrm{ld}\,2, e) \neq \top$; at $p \neq 2$,
  both `plusLen` and `minusLen` are $\neq \top$, so their sum in $\mathbb N_\infty$ is $\neq \top$ (`WithTop.add_ne_top`, `:138–139`).
- *Partial-sum bound:* Partition any finite set $S$ of primes into $S_2 := \{\ell \in S : \ell = 2\}$
  (a subset of $\{2\}$) and $S_{\mathrm{odd}} := \{\ell \in S : \ell \neq 2\}$ (`Finset.sum_filter_add_sum_filter_not`, `:148`).
  Since every summand $g(\ell) \ge 0$, $\sum_{\ell \in S_2} g(\ell) \le g(2) \le B_2 \log 2$ (`hA`, `:150–165`),
  while on $S_{\mathrm{odd}}$ converting finite `ENat.toNat` of `plusLen + minusLen` into real addition
  (`ENat.toNat_add`, `:185`) splits $\sum_{\ell \in S_{\mathrm{odd}}} g(\ell)$ into the `minusLen` sum ($\le B_m$)
  plus the `plusLen` sum ($\le B_p$), giving $B_2 \log 2 + B_m + B_p$ (`:166–189`). $\square$

### 11.4.2 Host CM property, conductor bound, plus-part counts, and the subexponential squeeze (`vwin_of_counts`)

Next we verify the complete `R3` algebraic and analytic glue in `IsCMFieldOfIsChiField.lean`,
`ConductorBoundsOfIsChiField.lean`, `CountVs.lean`, `FinalLe.lean`, `SumOut.lean`, `PointArith.lean`,
`ThmHV.lean`, `minusle.lean`, `ErrorTermsLeSqrtExpRpow.lean`, `AdmissibleOfPageN.lean`, and
`JointWinOfCounts.lean`!

**Proposition 11.2 (From `ThmBab`, `ThmBcFree`, `LemmaK`, and the five plus-part counts to `VWin`: `vwin_of_counts`).** [Lean, read]

1. *(Why `q ≡ 3 (mod 8)` forces $E$ to be CM, and conductor bound)* *Let `IsChiField ψ e q d E` hold
   with $q$ prime and $q \equiv 3 \pmod 4$ (satisfied by `WinPair` since $q \equiv 3 \pmod 8$). Then
   $E$ is an abelian CM field (`isCMField_of_isChiField`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/IsCMFieldOfIsChiField.lean:7`) and its
   cyclotomic conductor satisfies*
   $$1 \le \operatorname{cond}(E) \le 2^{e + 2}\,\psi.N\,q\,d \qquad\text{and}\qquad [E : \mathbb Q] \le \operatorname{cond}(E)$$
   *(`conductor_bounds_of_isChiField`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ConductorBoundsOfIsChiField.lean:77`).*
2. *(Assembling `VVplusLe` from bad-prime layers and generic counts: `thmHV_of_counts`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/JointWinOfCounts.lean:20`)*
   *Assume `PoitouTateDuality` (`[Lean]` / `[Open]`), `LocalFinitenessK`, `LocalTateDualityK`,
   `LemmaK CK`, and the five character-level plus-part count packages `CountI`, `CountII`, `CountIII`,
   `CountV`, and `CountZ`. Then `ThmHV K Ct` holds for every $C_t > 0$.*
3. *(Subexponential squeeze to `VWin`: `vwin_of_joint` and `vwin_of_counts`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean:131`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/JointWinOfCounts.lean:30`)*
   *Combining `ThmBab K 401`, `ThmBcFree`, and `ThmHV K 401` proves `VWin`!*

*Proof.*
(1) Inside $\mathbb Q(\zeta_N)$ ($q \mid N$), the primitive $q$-th root $\zeta_q := \zeta_N^{N/q}$ builds
the quadratic Gauss sum $G$ with $G^2 = -q$ (`exists_gauss` for $q \equiv 3 \pmod 4$,
`src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/IsCMFieldOfIsChiField.lean:19`) on which $\tau_a(\zeta_N) = \zeta_N^a$ acts by the Legendre/Jacobi
symbol $\bigl(\frac{a}{q}\bigr)$. Every $\tau_a$ fixing $j(E)$ satisfies $\bigl(\frac{a}{q}\bigr) = 1$
by `IsChiField` (`:26`), hence fixes $G$, so Galois theory places $G \in j(E)$, producing $x \in E$
with **$x^2 = -q < 0$** (`:42–46`)! No complex embedding $\sigma : E \hookrightarrow \mathbb C$ can be
real (if $\Im\sigma(x) = 0$, then $(\Re\sigma(x))^2 = -q < 0$, impossible!, `:47–59`), so $E$ is
totally complex and abelian over $\mathbb Q$, hence a CM field (`IsCMField.of_isAbelianGalois E`, `:60`).
Similarly (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ConductorBoundsOfIsChiField.lean:86–119`), setting $L := \operatorname{lcm}(2^{e+2}, \psi.N, q, d) \mid N$,
every $\tau_a$ with $a \equiv 1 \pmod L$ satisfies $a \equiv 1 \pmod{2^{e+2}}$, $\psi(a) = 1$,
$\bigl(\frac{a}{q}\bigr) = 1$, and $\bigl(\frac{a}{d}\bigr) = 1$, so $j(E) \subseteq \mathbb Q(\zeta_L)$
(`descend`, `:11–64`), giving $\operatorname{cond}(E) \le L \le 2^{e+2}\,\psi.N\,q\,d$ and
$[E : \mathbb Q] \le \varphi(\operatorname{cond}(E)) \le \operatorname{cond}(E)$ (`finrank_le`, `:66–75`).

(2) Look at how `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/JointWinOfCounts.lean:16–23` splits the odd primes $\ell \neq 2$ in `VVplusLe` into
two regimes (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/PointArith.lean:36–92`):
- **Outside the fixed bad set ($\ell \notin B_\chi(\psi)$, `sumOut` in `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/SumOut.lean:50–231`):** At each
  twist $1 \le e < t$, filter $S$ by `CaseI l e` ($\ell \notin B_\chi$ and $(\ell - 1) \nmid 2e$, `:171`).
  On `CaseI`, `CountI` (derived from `PropGK`!) bounds the **entire sum over $\ell$ at once** by $M^{C_1}$
  where $M := h.N \cdot t$ (`:176`)! On $\neg\mathrm{CaseI}$, $(\ell - 1) \mid 2e$ forces
  $\ell \le 2e + 1 \le 2t$ (`card_small`, `:19, 192`: **at most $2t$ such primes exist!**), and
  `CountZ`, `CountII`, `CountIII` bound each character summand by $(\ell \cdot h.N \cdot e)^K \le M^{3K}$
  (`:73–118`). Summing over $1 \le e < t$ gives $\le t(M^{C_1} + 2 M^{3K+1}) \le M^{C_1 + 3K + 4}$
  (`final_le`, `:31–47, 231`)!
- **Inside the fixed finite bad set ($\ell \in B_\chi(\psi)$, `sumIn` in `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/FinalLe.lean:86–263`):**
  First, `countVs` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/CountVs.lean:86–171`) handles large-$R_1$ bad-prime twists at $e = 1$ by cutting out
  a cyclic extension $L / \mathbb Q$ of bounded degree $[L : \mathbb Q] \le n_0(\psi)$ (`vsField`, `:112`),
  using Poitou–Tate duality (`shaLeV`, `:123`) and `LemmaK` (`klen`, `:124`) to bound the length by
  $(\ell \cdot h.N)^{C_6}$. Then `sumIn` splits the characters $\psi' \in h.X(c, e)$ into at most $h.q = \psi.N$
  odd-order characters `Oset` (`hOcard`, `:175`, bounded across $1 \le e < t$ by $B + M^{C_4}$ via `CountIV`
  from the Iwasawa layer hypothesis `BbAt`!) and the remaining characters (bounded pointwise by
  $(M^2)^{C_m}$ via `CountII`, `CountV`, `CountVs`), combining them via `sum_split` (`:14–54`) and
  `final_le` (`:56–84`) into $\le M^C + C \cdot B$.
- Summing `sumOut` with the $\lvert B_\chi(\psi) \rvert$ bad primes of `sumIn` (`point_arith`,
  `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/PointArith.lean:5–34`) and substituting $B = \exp(x^{4\varepsilon/5})$ and $h.N = \operatorname{cond}(E)$
  (`hostCond`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/ThmHV.lean:39`) yields `HVAt`:
  $$\mathrm{VVplusLe}\Bigl(E,\ t(x),\ \bigl(\operatorname{cond}(E)\cdot t(x)\bigr)^C + C\,\exp\bigl(x^{4\varepsilon/5}\bigr)\Bigr)!$$

(3) Finally, follow `vwinAt_of_joint` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean:41–129`):
- `jointWin_of` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:145–156`) intersects the threshold of `ThmBab`
  and `ThmHV` to obtain a window $[Y, Y^2] \subset [X^{1/J}, X]$ on which both `BaAt`
  ($B_2 = \exp(x^{4\varepsilon/5})$) and `HVAt` ($B_p = u^C + C\exp(x^{4\varepsilon/5})$ with
  $u := \operatorname{cond}(E)\cdot t(x)$) hold for all $x \in [Y, Y^2]$;
- `ThmBcFree` (`thmBc_iff`, `:112`) supplies `VVminusLe E (t x) (minusBound Cb ...)`. Since
  $[E : \mathbb Q] \le \operatorname{cond}(E)$ and $\log u = \log(\operatorname{cond}(E)\cdot \lfloor x^{401} \rfloor) \le 2 x^{\varepsilon/4}$
  (`hxN`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean:120`), `minusBound_le_exp_of_log_le` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/minusle.lean:6–75`) bounds
  $u^4 \le \exp(8 x^{\varepsilon/4})$ and gives $B_m \le K \exp(8 x^{\varepsilon/4})$;
- Proposition 11.1(2) (`vvle_of_parts`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean:123`) combines $B_2, B_m, B_p$ into
  $$\mathrm{VVle}\Bigl(E,\ \lfloor x^{401} \rfloor,\ \exp\bigl(x^{4\varepsilon/5}\bigr)\log 2 + K\exp\bigl(8 x^{\varepsilon/4}\bigr) + \bigl(u^C + C\exp(x^{4\varepsilon/5})\bigr)\Bigr);$$
- and for $x \ge x_T$ (`error_terms_le_sqrt_exp_rpow`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ErrorTermsLeSqrtExpRpow.lean:6–88`), writing
  $a = x^{\varepsilon/4} \le b = x^{4\varepsilon/5}$ and $x^\varepsilon = b \cdot x^{\varepsilon/5}$,
  every term is bounded by $N \exp(D b) \le \exp(x^\varepsilon / 2) = \sqrt{\exp(x^\varepsilon)}$,
  so `VVle.mono` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:51`) concludes `VAt ψ eps 401 q d (e x) x`! $\square$

### 11.4.3 Sinnott's proof of Ferrero–Washington ($\mu = 0$) and Iwasawa $\ell$-rank bounds (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`)

Remarkably, `FerreroWashington` is **not** left in the unreviewed `GlobalTheory.Published` pool: we read
the entire 119-line file `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`
(import cone **809** modules) and the 104-line bridge `ExistsIwasawaRankBoundOfFerreroWashington.lean`
(cone **2,033**) line by line (`R3` / `[Lean, read]` for both files; see §11.4.3.1 for the finite independence supply and its remaining imported inputs)!

**Proposition 11.3 (In-archive deduction of `FerreroWashington` and Iwasawa rank stabilization).**
*For every prime $\ell$ (including $\ell = 2$!) and every abelian number field $K / \mathbb Q$ containing
$\mu_4$ ($\ell = 2$) or $\mu_\ell$ ($\ell \neq 2$), the $\ell$-cotorsion rank of $\mathrm{Cl}(\mathcal O_{K_n})$
is uniformly bounded along the cyclotomic $\mathbb Z_\ell$-tower $K_n = K(\mu_{\ell^n})$:*
$$\exists r \in \mathbb N,\ \forall n \in \mathbb N,\quad \bigl\lvert \mathrm{Cl}(\mathcal O_{K_n}) / \mathrm{Cl}(\mathcal O_{K_n})^\ell \bigr\rvert \le \ell^r,$$
*and for odd $\ell$ this bounds the dual Iwasawa module rank `XRk l 1 (levU l U n) r` uniformly in $n$.*
*(Lean: `UpperTheory.V.FW.cyc` and `UpperTheory.V.FW.ferreroWashington`,
`src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:18,104`;
`exists_iwasawaRank_bound_of_ferreroWashington`,
`src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/RealPlaceConjugation/ExistsIwasawaRankBoundOfFerreroWashington.lean:23`.)* [Lean, read]

*Proof.* Look at the two-step proof in `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`:

1. **Full cyclotomic towers $\mathbb Q(\zeta_{f \ell^n})$ (`FW.cyc`, `:18–102`):** Let $f > 1$ be
   coprime to $\ell$, and set $c := 2 f \ell + 1$ (odd, $> 1$, coprime to $f\ell$, `:25–28`).
   - *Minus part via Stickelberger + Sinnott (`[FerreroWashington1979]`, `[Sinnott1984]`):* The
     output of the independence argument is `memZ` (see §11.4.3.1). It supplies a fixed exponent and
     a cyclotomic generator $\gamma$ such that a power of $[\gamma]-1$ lies in the ideal generated
     by the smoothed Stickelberger half-sum, $1+[-1]$, and $\ell$. Combining this with
     Stickelberger annihilation (`stickH`) and the ambiguous-class estimate (`ambCyc`),
     `core` gives $\lvert \mathrm{difR}(-1)\cap\mathrm{Cl}(L)[\ell]\rvert\le B^N$ (`:47–53`, `:83–89`).
   - *From the $(1-J)$-image to the whole class group (`:54–64` for $\ell = 2$; `:90–102` for $\ell \ge 3$):*
     For odd $\ell$, $L = \mathbb Q(\zeta_{f \ell^n})$ ($n \ge n_0 \ge 2$) contains $\mu_\ell$, and the Kummer
     reflection inequality `reflOdd` together with `pOdd` (`:99–102`) bounds the total $\ell$-rank index
     `[Cl(L) : Cl(L)^l]` by $\ell \cdot (B^N)^2$. For $\ell = 2$ the image of $1-J$ can be smaller than the
     minus subgroup; the unit-sign bound `sgnCyc` on this defect and `pTwo` (`:56–64`) give
     $\bigl(2^{\varphi(f \cdot 2^{\mathrm{ee}\,2}) N} B^N\bigr)^2$. Both bounds are **independent of
     $n \ge n_0$**. Section 11.4.3.2 proves them, together with `core`, `stickH` and `ambCyc`, from their
     named inputs.
2. **Descent from $\mathbb Q(\zeta_{f \ell^m})$ to general abelian $K_n / K$ (`FW.ferreroWashington`, `:104–119`):**
   By Kronecker–Weber (`embed l K`, `:107` `[Lean]`), $K$ embeds into $\mathbb Q(\zeta_{f \ell^{m_0}})$
   with $f > 1$ coprime to $\ell$ and bounded relative degree $D$, embedding each $K_n$ into
   $L = \mathbb Q(\zeta_{f \ell^m})$ ($m \ge n_0$) of relative degree $[L : K_n] \le D \ell^{n_0}$ (`:111`).
   Norm/transfer descent on class groups (`desc`, `:113` `[Lean]`) gives
   $$\bigl[\mathrm{Cl}(K_n) : \mathrm{Cl}(K_n)^\ell\bigr] \le [L : K_n] \cdot \bigl[\mathrm{Cl}(L) : \mathrm{Cl}(L)^\ell\bigr]
   \le D \ell^{n_0} B < \ell^{D \ell^{n_0} B}$$
   (using $k < \ell^k$ for $\ell \ge 2$, `Nat.lt_pow_self`, `:119`), proving `FerreroWashington` with
   $r := D \ell^{n_0} B$! In `src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/RealPlaceConjugation/ExistsIwasawaRankBoundOfFerreroWashington.lean:73–104`, Kummer duality
   between unramified $\mathbb Z/\ell\mathbb Z$-extensions and $\mathrm{Hom}(\mathrm{Cl}(K_n), \mathbb Z/\ell\mathbb Z)$
   (`cardClDual` and `pullOnto`, `:99–103` `[Lean]`) immediately transfers $\le \ell^r$ to the Iwasawa
   cotorsion module `XDual`! $\square$

#### 11.4.3.1 From a finite difference to Stickelberger nonvanishing

**Motivation.** A sum of dilates of a distribution can vanish even when the distribution is nonzero. Here the distribution has a finite-difference equation with a numerator that has a known nonzero coefficient. The archive uses that equation to prove nonvanishing after averaging over roots of unity and twisting by a character. It works with finite group rings and makes the level of detection uniform in the character. The declaration that supplies the class-group proof is the resulting ideal membership in `memZ`. The source map below refers throughout to the joined Lean archive with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. [Lean, read]

**Example.** [Expository] Over $\mathbb F_5$, take $P(X)=a+bX$ and the dilates $P(X)/(1-X^2)$ and $P(Y)/(1-Y^2)$. Think of $X$ and $Y$ as the monomials for the two independent directions in $\mathbb Z^2$. If the sum of these fractions is zero, then
$$
(a+bX)(1-Y^2)+(a+bY)(1-X^2)=0.
$$
Map to the group ring with $X^2=1$ and $Y$ still unrestricted. Only $(a+bX)(1-Y^2)$ survives. Multiplication by $1-Y^2$ is injective since a nonzero Laurent polynomial in $Y$ has a highest term. The coefficients of $1$ and $X$ are independent in the group ring of $\mathbb Z/2\mathbb Z$, so $a=b=0$. This calculation uses the denominator factors in two ways. Clearing them first produces a finite expression, and killing one of them in a quotient then isolates its numerator. The archive uses the same operations with additive $\ell$-adic exponents.

**Definitions.** For an abelian group $A$ written additively, use $[a]$ for its basis element in $k[A]$. Thus $[a][b]=[a+b]$ and $[0]=1$. Fix a nonempty finite index set $I$, units $\eta_i\in\mathbb Z_\ell^\times$, and an integer $N>0$. For $P\colon\mathbb N\to k$, set
$$
B_i=\sum_{0\le s<N}P(s)[s\eta_i],\qquad D_i=1-[N\eta_i],\qquad
E=\sum_{i\in I}B_i\prod_{j\ne i}D_j.
$$
Here $E$ is the archive's `sinE` in $k[\mathbb Z_\ell]$. In the localization inverting the $D_i$, it is the numerator obtained by clearing denominators in $\sum_i B_i/D_i$. At a finite level we use the cross-multiplied expression $E$ directly. The factors $1-[N\eta_i]$ there have finite-order exponents and can be zero divisors. [Lean, read]

**Lemma (finite-level independence).** [Lean, read] Let $\ell$ be prime. Suppose for $i\ne j$ and $a,b\in\mathbb Z$ that $a\eta_i=b\eta_j$ in $\mathbb Z_\ell$ implies $a=0$. There is an integer $d_0\ge 0$ depending only on the $\eta_i$ and $N$ with the following property. For every $d\ge d_0$, every commutative ring $k$, and functions $P\colon\mathbb N\to k$ and $\alpha\colon\mathbb Z/\ell^d\mathbb Z\to k$, assume
$$
\alpha(y)-\alpha(y-N)=\sum_{0\le s<N,\ s\equiv y\bmod\ell^d}P(s),
\qquad
\sum_{i\in I}\alpha(\bar\eta_i^{-1}y)=0
$$
for every $y\in\mathbb Z/\ell^d\mathbb Z$. Then $P(s)=0$ for every $0\le s<N$. The requirement on the directions is pairwise absence of a nonzero rational ratio.

**Proof.** At level $d$, set $A_i=\sum_y\alpha(y)[\bar\eta_i y]$. Use overbars on group-ring elements for reduction of exponents modulo $\ell^d$. Translation by $N$ in the first hypothesis gives $\bar D_i A_i=\bar B_i$ coefficient by coefficient. The second hypothesis says $\sum_i A_i=0$ since multiplication by $\bar\eta_i$ permutes residues. Consequently
$$
\bar E=\sum_i A_i\prod_j\bar D_j=0.
$$
This proves the finite group-ring identity in `sinFin`. The reduction map commutes with the sums and products defining $E$ because it sends $[a]$ to $[\bar a]$. This is `sinMap`.

Expand the products in $E$. Its support is contained in the fixed finite set of exponents
$$
S=\left\{s\eta_i+\sum_{j\in U}N\eta_j:\ i\in I,\ 0\le s<N,\ U\subseteq I\right\}.
$$
This is `sinSupp`. Distinct $\ell$-adic integers differ modulo some power of $\ell$ and then differ modulo every higher power. Take $d_0$ to be the largest distinguishing level for pairs of distinct elements of $S$, with $d_0=0$ if there are no pairs. This is `sep`. For $d\ge d_0$, each coefficient of $E$ on $S$ is therefore the coefficient of $\bar E$ at the corresponding residue. It follows that $E=0$ before reduction.

Choose $i_0\in I$ and project to the additive quotient $A'=\mathbb Z_\ell/\mathbb Z N\eta_{i_0}$, where the denominator denotes the **abstract cyclic subgroup**. In the group ring of this quotient, $D_{i_0}$ maps to zero. The image of $E=0$ is therefore the image of $B_{i_0}$ times the product of the other denominator factors. For each $j\ne i_0$, the image of $N\eta_j$ has infinite order. If $mN\eta_j=bN\eta_{i_0}$ with $m>0$, pairwise independence gives $mN=0$, an impossibility. For an infinite-order element $u$ of an abelian group, multiplication by $1-[u]$ is injective on its group ring over any $k$. Indeed, an element killed by this factor has coefficients invariant under translation by $u$. Any nonzero coefficient would generate infinitely many nonzero coefficients, contrary to finite support. This is `nzd`. Cancel the factors one at a time. The image of $B_{i_0}$ vanishes, and the $N$ exponents $s\eta_{i_0}$ for $0\le s<N$ are distinct in $A'$ because $\eta_{i_0}$ has infinite additive order. Reading their coefficients gives $P(s)=0$. This is `sinLem` and completes the proof of `sinnott`. $\square$

**Arithmetic application.** [Lean, read] Fix $f$ coprime to $\ell$ and an odd integer $c>1$ coprime to $f\ell$. Write $M=f\ell^n$, $G=(\mathbb Z/M\mathbb Z)^\times$, and $e=2$ for $\ell=2$ and $e=1$ otherwise. Put $W=\mu_{\varphi(\ell^e)}(\mathbb Z_\ell)$ and $Q_d=(\mathbb Z/\ell^d\mathbb Z)^\times/\bar W$. For $d\le n$, let $\pi_d:G\to Q_d$ be reduction followed by the quotient. Over a field $k$ of characteristic $\ell$, let $\chi:G\to k^\times$ satisfy $\chi(-1)=-1$. Extend $\chi$ to a function $\Psi$ by zero on nonunits. The smoothing coefficient and half-sum are
$$
g(s)=\left\lfloor\frac{c\,\operatorname{rep}_M(c^{-1}s)}{M}\right\rfloor-\frac{c-1}{2},\qquad
\theta_{\mathrm{half}}=\sum_{s\in G,\ 2\operatorname{rep}_M(s)<M}g(s)[s].
$$
Here $\operatorname{rep}_M$ takes least nonnegative representatives, and $[s]$ in the multiplicative group ring denotes a basis element with $[s][t]=[st]$. The twist of the reduced half-sum is its image under $[s]\mapsto \chi(s)[\pi_d(s)]$.

The archive's `nonvan` asserts that a single $d\ge2$, depending on $\ell,f,c$, makes this twist nonzero for **all** $n\ge d$, all such $k$, and all such $\chi$. To see the application of the lemma, choose representatives $R$ for $W/\{\pm1\}$. For $r,r'\in R$, a relation $ar=br'$ with $a\ne0$ gives $a^{\varphi(\ell^e)}=b^{\varphi(\ell^e)}$ upon raising to the common exponent $\varphi(\ell^e)$, so $a=\pm b$ and $r=\pm r'$. Distinct representatives satisfy the independence hypothesis. Use $N=cf\ell$ and take $d=\max(d_0,2)$ from the lemma with these directions.

Suppose the twist vanishes. Let $\alpha(y)$ be the sum of $g(s)\Psi(s)$ over the fiber of $y$ under $\mathbb Z/M\mathbb Z\to\mathbb Z/\ell^d\mathbb Z$. For unit $y$, the residues $\bar r^{-1}y$ partition the corresponding $\pi_d$-fiber up to sign, using injectivity of reduction on $W$ for $d\ge2$ (`reps`, with `teich` [Lean]). More precisely, their inverse images in $G$ select one member of each orbit $\{s,-s\}$ in the fiber. The lower-half representatives defining $\theta_{\mathrm{half}}$ also select one member of each orbit, since $M>2$. The value $g(s)\Psi(s)$ is the same on both members. Indeed $g(-s)=-g(s)$ by complementary floors: if $x=\operatorname{rep}_M(c^{-1}s)$, then $0<x<M$ and $cx/M$ is nonintegral, so $\lfloor c(M-x)/M\rfloor+\lfloor cx/M\rfloor=c-1$. Also $\Psi(-s)=-\Psi(s)$. This proves that $\sum_{r\in R}\alpha(\bar r^{-1}y)$ is the corresponding twist coefficient. For nonunit $y$ all terms are zero since no unit maps to a nonunit. This is the coefficient comparison in `twCoef`. It applies in characteristic two as well: choosing one per orbit avoids division by two.

For the difference equation, $\Psi$ has period $f\ell$. Units remain units under translation by $f\ell$, and for each unit the ratio between its translate and itself lies in the $\ell$-group $\ker(G\to(\mathbb Z/f\ell\mathbb Z)^\times)$. Every element of $\ell$-power order in $k^\times$ is $1$. Nonunits remain nonunits. This is `charPer`. The shift by $c$ in $g$ comes from changing $\operatorname{rep}_M(c^{-1}s)$ by one. If $x=\operatorname{rep}_M(c^{-1}s)>0$, the floor difference is $\lfloor cx/M\rfloor-\lfloor c(x-1)/M\rfloor$, the number of integers $h$ satisfying $c(x-1)<hM\le cx$. Setting $j=cx-hM$ counts precisely the integers $0\le j<c$ congruent to $s$ modulo $M$. At $x=0$ the same calculation uses the floor at $x-1=-1$. Replacing $-1$ by the actual representative $M-1$ increases that floor by $c$, so the difference has an extra term $-c$ at $s=0$. Thus the one-step difference sums $1-c\,\mathbf 1_{c\mid j}$ over $0\le j<c$ congruent to $s$. Telescoping $f\ell$ steps and multiplying by the periodic $\Psi$ gives the numerator
$$
P(j)=\Psi(j)(1-c\,\mathbf 1_{c\mid j})\quad(0\le j<cf\ell).
$$
Summing over the reduction fibers commutes with translation by $N$, so the difference identity descends to $\alpha$ (`gcShift`, `pushDiff`). The lemma would force $P(1)=0$, whereas $c>1$ and $\Psi(1)=1$ give $P(1)=1$. This proves `nonvan`.

**The interface consumed by Ferrero–Washington.** [Lean, read] For the same $\ell,f,c$, `memZ` supplies $H,d$ with $d\ge 2$ such that for every $n\ge d$ there is $\gamma\in G$ represented by $1+f\ell^e$, with $[G:\langle\gamma\rangle]=\varphi(f\ell^e)$, satisfying
$$
([\gamma]-1)^H\in(\theta_{\mathrm{half}},\ 1+[-1],\ \ell)\subseteq\mathbb Z[G].
$$
The proof takes $d$ from `nonvan`, writes $\varphi(f\ell^e)=\ell^a m$ with $(m,\ell)=1$, and takes $H=\ell^d\ell^a$. The group-splitting input `struct` gives the index of $\langle\gamma\rangle$ stated above, $\gamma^{\ell^n}=1$, and a homomorphism $p:G\to G$ with image in $\langle\gamma\rangle$. It supplies $p(-1)=1$, $(g/p(g))^{\ell^a m}=1$, $\pi_d\circ p=\pi_d$, and $(\pi_d\gamma)^{\ell^d}=1$. To see how the nonvanishing enters the ideal, work over $k=\overline{\mathbb F}_\ell$ and write $p$ for that projection, $q=\ell^a$, and $T=[\gamma]-1$. Let $D$ be the image of $g\mapsto (g/p(g))^q$. Every element of $D$ has order dividing $m$, so $D$ has order prime to $\ell$. In the quotient by $(\theta_{\mathrm{half}},1+[-1])$, consider an eigenvector $v\ne0$ for $D$ with character $\psi$. Define $\chi(g)$ by $\chi(g)^q=\psi((g/p(g))^q)$ using inverse Frobenius. Because $p(-1)=1$ and $[-1]$ acts as the scalar $-1$ in this quotient, $\chi(-1)=-1$. Put $F=\operatorname{tw}(\chi,p)(\theta_{\mathrm{half}}\bmod\ell)$. Taking the $q$-th power of the half-sum and acting on $v$ is the same as acting by $F^q$: on each monomial this is the identity $g^q=(g/p(g))^q p(g)^q$, and Frobenius distributes over sums. Hence $F^qv=0$.

Now $F$ is a polynomial in the nilpotent $T$ since $p(g)\in\langle\gamma\rangle$. The image of $T^{\ell^d}$ under $\pi_d$ is zero, while the image of $F$ is the nonzero twist from `nonvan`. Thus $F$ is not divisible by $T^{\ell^d}$. Factoring its polynomial at zero gives $F=T^u U$ for some $u<\ell^d$ and a unit $U$ (its constant coefficient is nonzero and its remaining terms are nilpotent). In particular $F\mid T^{\ell^d}$ and $T^{q\ell^d}v=0$. The character eigenspaces span the quotient: the usual idempotents $|D|^{-1}\sum_{x\in D}\psi(x)^{-1}[x]$ sum to $1$ by character orthogonality. Therefore $T^{q\ell^d}$ is zero there. This is the deduction in `algK`. The proof of `descZ` descends the resulting expression coefficientwise by choosing an $\mathbb F_\ell$-linear retraction $\overline{\mathbb F}_\ell\to\mathbb F_\ell$ fixing $1$. This retraction commutes with multiplication by the reductions of integral group-ring elements. Lifting coefficients of the multipliers to $\mathbb Z$ leaves an error divisible by $\ell$. In `cyc`, the single call to `memZ` uses $c=2(f\ell)+1$. The resulting membership, together with Stickelberger annihilation, is what the class-group bound consumes. In additive notation, multiply the ideal relation by $1-[J]$, where $J=-1$. The term $1+[J]$ drops out because $J^2=1$, and $\theta_{\mathrm{half}}(1-[J])$ annihilates the class group by `stickH`. It follows that $(1-[\gamma])^H$ sends $(1-J)C$ into $\ell(1-J)C$ for the class group $C$. [Lean] for the group splitting and class-group estimates used at this interface.

**Remark on $\mu$.** [Expository] The finite functions $\alpha$ play the role of distribution coefficients on residue classes, and summing their dilates is the operation behind the $\Gamma$-transform on units. For an integral power series over a discrete valuation ring, having $\mu=0$ means surviving reduction modulo a uniformizer. A compatible system in the completed group ring survives reduction as soon as a finite quotient has a coefficient that survives. In the archive the reduced coefficients are used on the **algebraic** side through `memZ`, which feeds the uniform class-group rank bound in the preceding proposition.

Sinnott's continuous result starts from a measure whose associated power series is a rational function. Its $\Gamma$-transform has the same $\mu$-invariant as the sum of the restriction to units and its image under negation. The sign pairing matters at $\ell=2$ as well. The paper proves rational-function independence by rescaling independent Laurent monomials to shorten a putative relation. The finite proof above isolates a numerator by killing a denominator in an abstract group quotient. [Paper] [Sinnott1984, Theorem 1 and §3, pp. 276–279](https://gdz.sub.uni-goettingen.de/id/PPN356556735_0075?tify=%7B%22pages%22%3A%5B282%5D%7D).

For the usual Iwasawa-module interpretation, assume the cyclotomic class-group control theorem and the torsion $\mathbb Z_\ell[[T]]$ structure theorem in the following form. The finite-layer class groups agree with the coinvariants by $(1+T)^{\ell^j}-1$ up to errors of bounded order, and the inverse-limit module is pseudo-isomorphic to the elementary module, with finite kernel and cokernel. A summand $\mathbb Z_\ell[[T]]/(\ell^b)$ with $b>0$ contributes $\ell^j$ dimensions after taking these coinvariants and reducing modulo $\ell$, since $(1+T)^{\ell^j}-1$ reduces to $T^{\ell^j}$. Finite errors affect the dimensions by a bounded amount: apply the coinvariant-and-reduction functor, quotient by $(\ell,(1+T)^{\ell^j}-1)$, and bound the resulting kernel correction for a finite cokernel by its first Tor, computed with the two-generator Koszul resolution. Its middle term consists of two copies of the finite cokernel. The same bound applies to a control map with bounded finite errors on the finite-layer coinvariants after reduction by $\ell$, using the resolution of $\mathbb Z_\ell/\ell$. Thus the uniform bound excludes every such summand, giving $\mu=0$ under those named structure and control inputs. [Open] for the proof of these inputs and for the construction and identification of the continuous measures. The finite-level theorem above supplies the independence argument used by the archive.

**Source map.** Joined archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Paths are relative to the archive root.

| Archive file and lines | Status |
| --- | --- |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/TwSingle.lean:7–48` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/SinFin.lean:5–64` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/SinMap.lean:5–10` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/SinSupp.lean:5–56` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/SepPair.lean:5–25` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/Nzd.lean:5–36` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/SinLem.lean:7–78` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/Sinnott.lean:10–44` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/EvenTot.lean:24–86` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/CharPer.lean:5–53` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/GcNeg.lean:28–62` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/GcDiff.lean:25` | [Lean] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/GcShift.lean:6–62` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/PushDiff.lean:5–38` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/TwCoef.lean:5–203` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/Nonvan.lean:12–60` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/ToKOf.lean:13–37` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/DescZRetr.lean:5–61` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/Struct.lean:27` | [Lean] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/AlgK.lean:8–84` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/ToZModPowOneEqZeroIff.lean:53` | [Lean] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/HalfSum.lean:5` | [Lean] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/CardRangeInfTorsionLeIndexPow.lean:64` | [Lean] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:29–50` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:79–89` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/PhiDvd.lean:5–89` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FrobEig.lean:5` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/SepChar.lean:5` | [Lean, read] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/StickH.lean:8` | [Lean] |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/AmbCyc.lean:9` | [Lean] |

#### 11.4.3.2 From the Stickelberger membership to a uniform class-group rank bound

**Motivation.** Section 11.4.3.1 ends with a relation in the group ring of $G=(\mathbb Z/f\ell^n\mathbb Z)^\times$. A fixed power $([\gamma]-1)^N$ lies in the ideal generated by the smoothed half-sum $\theta=\theta_{\mathrm{half}}$, by $1+[J]$ with $J=-1$, and by $\ell$, and $N$ does not depend on $n$. This subsection explains how `cyc` turns that relation into a bound on the $\ell$-rank $d_\ell(\mathrm{Cl}(L))=\dim_{\mathbb F_\ell}\mathrm{Cl}(L)/\ell\,\mathrm{Cl}(L)$ of $L=\mathbb Q(\zeta_{f\ell^n})$ that is the same for every large $n$. Three mechanisms are involved. Stickelberger's theorem makes $\theta(1-[J])$ act as zero on the class group, so the relation says that $(1-\gamma)^N$ maps the image $(1-J)\mathrm{Cl}(L)$ into its $\ell$-multiples. A nilpotent endomorphism of a finite abelian group shrinks it at each step by at most the size of its cokernel, so the $\ell$-torsion of that image is bounded by the $N$-th power of the cokernel of $1-\gamma$ modulo $\ell$. That cokernel is an ambiguous quotient for $L$ over the fixed field $F=\mathbb Q(\zeta_{f\ell^e})$ ($e=2$ for $\ell=2$, $e=1$ otherwise), and class field theory bounds it by a number attached to $F$ alone. The group ring supplies the uniformity of $N$: without $\theta$ the exponent would have to be $\ell^{n-e}$ (Remark 4). The rest of `cyc` passes from the $(1-J)$-image to the whole class group, by Kummer reflection when $\ell$ is odd and by signs of units when $\ell=2$. Source references are to the joined archive with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. [Lean, read]

**Example 1 (a cyclic module of order $\ell^2$).** [Expository] Let $\ell$ be odd and $C=\mathbb Z/\ell^2$. Let $G=\langle J\rangle\times\langle\gamma\rangle\cong C_2\times C_\ell$ act by $J=-1$ and $\gamma=1+\ell$; the latter has order $\ell$ because $(1+\ell)^\ell\equiv1\bmod\ell^2$. Take $\theta=0$. Then $\mathbb Z[G]/(1+[J],\ell)\cong\mathbb F_\ell[T]/(T^\ell)$ with $T=[\gamma]-1$, since $(\gamma-1)^\ell=\gamma^\ell-1=0$ in characteristic $\ell$. So $([\gamma]-1)^N\in(\theta,1+[J],\ell)$ holds for $N=\ell$ and for no smaller $N$. On the module, $1-J$ is multiplication by $2$, which is invertible, so $(1-J)C=C$ and
$$
(1-J)C\cap C[\ell]=\ell C,\qquad \lvert(1-J)C\cap C[\ell]\rvert=\ell .
$$
Also $1-\gamma$ is multiplication by $-\ell$, so $(1-\gamma)C=\ell C$, $\ell C+(1-\gamma)C=\ell C$, and the cokernel index is $\ell$. Proposition 4 below gives $\ell\le\ell^{\ell}$. Lemma 3 sees more: $(1-\gamma)(1-J)C=\ell C=\ell(1-J)C$, so its hypothesis already holds with $N=1$. Its auxiliary subgroup is $U=\ell C$, the induced map on $C/U\cong\mathbb Z/\ell$ is zero, and Lemma 2 is the equality $\ell=[C/U:0]$. Lemma 1 for $T=1-\gamma$ reads $\ker(1-\gamma)=\ell C$ and $C/(1-\gamma)C=C/\ell C$, both of order $\ell$: the $\gamma$-invariants and the $\gamma$-coinvariants have the same order, as they always do.

For $\ell=2$ the same construction on $C=\mathbb Z/4$ with $J=-1$ shows how the image of $1-J$ differs from the minus subgroup. Here $(1-J)C=2C=\{0,2\}$, whereas $C^-=\ker(1+J)=C$ since $1+J$ acts as $0$. The odd-$\ell$ splitting $C=C^+\oplus C^-$ fails, because $C^+=\ker(1-J)=\{0,2\}$ meets $C^-$ in $\{0,2\}$. The defect $[C^-:(1-J)C]=2$ is exactly the factor that Lemma 8 has to pay: $[C:2C]=2\le\bigl([C^-:(1-J)C]\cdot\lvert(1-J)C\cap C[2]\rvert\bigr)^2=16$.

**Example 2 ($C_\ell\times C_\ell$ with a unipotent generator).** [Expository] Let $\ell$ be odd, $C=\mathbb F_\ell^2$ with basis $e_1,e_2$, and let the same group $G$ act by $J=-1$ and $\gamma e_1=e_1$, $\gamma e_2=e_1+e_2$, with $\theta=0$ as before; the group ring again allows $N=\ell$. Now $(1-J)C=C=C[\ell]$, so $\lvert(1-J)C\cap C[\ell]\rvert=\ell^2$. The map $\psi=1-\gamma$ sends $e_1\mapsto0$ and $e_2\mapsto-e_1$. Hence $\psi C=\mathbb F_\ell e_1$, $\psi^2=0$, $\ell C=0$, and $[C:\ell C+\psi C]=\ell$. Proposition 4 gives $\ell^2\le\ell^\ell$. Inside Lemma 3 the hypothesis $\psi^N(1-J)C\subseteq\ell(1-J)C=0$ fails for $N=1$ and holds for $N=2$. Here $U=0$, and the filtration $C\supset\psi C\supset0$ has two layers of order $\ell$, each a quotient of $C/\psi C$. Lemma 2 is the equality $\ell^2=[C:\psi C]^2$, and Lemma 1 for $\psi$ reads $\lvert\ker\psi\rvert=\lvert\mathbb F_\ell e_1\rvert=\ell=\lvert C/\psi C\rvert$. The $\ell$-rank of the $(1-J)$-image is $2$ while the ambiguous quotient has rank $1$. This is why the bound has the shape $B^N$ rather than $B$.

Read the same matrices over $\mathbb F_2$. Then $J=-1$ is the identity, so $(1-J)C=0$, while $C^-=\ker(1+J)=\ker 2=C$. The bound on $\lvert(1-J)C\cap C[2]\rvert$ says nothing about $C$, and Lemma 8(i) reads $4=[C:2C]\le\bigl([C^-:0]\cdot1\bigr)^2=16$. The whole $2$-rank lies in the defect $C^-/(1-J)C$, which has to be bounded by a separate argument (Lemma 8(ii)).

**Definitions.** Write finite abelian groups additively. For an endomorphism $\sigma$ of $C$ and an integer $m$, put $mC=\{mx\}$, $C[m]=\{x:mx=0\}$ and $(1-\sigma)C=\{x-\sigma x\}$. For an automorphism $J$ with $J^2=1$, put $C^-=\ker(1+J)$ and $C^+=\ker(1-J)$. Indices are $[C:H]$, and $[C:\ell C]=\ell^{d_\ell(C)}$, where $d_\ell(C)$ is the minimal number of generators of the $\ell$-primary part of $C$. In the archive these are `powR C l`, `torK C l`, `difR σ` and `minK J`; the archive writes the groups multiplicatively (`TwSingle.lean:56–64`). For $M=f\ell^n$ and $L=\mathbb Q(\zeta_M)$, the group $G=(\mathbb Z/M\mathbb Z)^\times$ acts on $\mathrm{Cl}(L)$ through `cycRep`: the basis element $[t]$ acts by $\sigma_t^{-1}$, where $\sigma_t(\zeta)=\zeta^t$ (`clA`, `cycRep_apply`, `CycRepApply.lean:16–24`). So $J=-1$ acts by complex conjugation (`conjEq`), and $\Theta=\sum_u\{u/M\}[u]$ acts as the classical Stickelberger element $\sum_u\{u/M\}\sigma_u^{-1}$. [Lean, read]

**Lemma 1 (kernel and cokernel).** [Lean, read] Let $T$ be an endomorphism of a finite abelian group $V$. Then $\lvert\ker T\rvert=\lvert V/TV\rvert$. In particular $\lvert V[\ell]\rvert=\lvert V/\ell V\rvert=\lvert\mathrm{Hom}(V,\mathbb Z/\ell)\rvert$.

**Proof.** The sequence
$$
0\to\ker T\to V\xrightarrow{\ T\ }V\to V/TV\to0
$$
is exact, and the orders in an exact sequence of finite groups have alternating product $1$. Thus $\lvert\ker T\rvert\,\lvert V\rvert=\lvert V\rvert\,\lvert V/TV\rvert$ (the archive writes this as $\lvert V\rvert=\lvert\ker T\rvert\,\lvert TV\rvert$ twice). Homomorphisms $V\to\mathbb Z/\ell$ factor through the $\mathbb F_\ell$-vector space $V/\ell V$ and form its dual, which has the same order. $\square$

**Lemma 2 (nilpotent length estimate).** [Lean, read] If $T^N=0$, then $\lvert V\rvert\le\lvert V/TV\rvert^N$.

**Proof.** For a subgroup $H\le V$ the restriction $T|_H$ gives $\lvert H\rvert=\lvert\ker T|_H\rvert\,\lvert TH\rvert\le\lvert\ker T\rvert\,\lvert TH\rvert$. With $H=T^kV$ this is $\lvert T^kV\rvert\le\lvert\ker T\rvert\,\lvert T^{k+1}V\rvert$. Induction gives $\lvert V\rvert\le\lvert\ker T\rvert^k\,\lvert T^kV\rvert$, and at $k=N$ the last factor is $1$. Lemma 1 replaces $\lvert\ker T\rvert$ by $\lvert V/TV\rvert$. $\square$

Equivalently, the filtration $V\supseteq TV\supseteq\cdots\supseteq T^NV=0$ has $N$ layers, and $T^k$ maps $V/TV$ onto the $k$-th layer. For a $\mathbb Z_\ell[T]$-module of finite length this is the length estimate $\operatorname{length}V\le N\cdot\operatorname{length}(V/TV)$.

**Lemma 3 (pushing $\ell$-divisibility through a nilpotent quotient).** [Lean, read] Let $\varphi,\psi$ be commuting endomorphisms of a finite abelian group $C$ with $\psi^N\varphi(C)\subseteq\ell\,\varphi(C)$. Then
$$
\lvert\varphi(C)\cap C[\ell]\rvert\le[C:\ell C+\psi C]^N .
$$

**Proof.** Put $U=\{x\in C:\varphi(x)\in\ell\varphi(C)\}$, the preimage of $\ell\varphi(C)$ under $\varphi\colon C\to\varphi(C)$. Since this map is onto, Lemma 1 for the group $\varphi(C)$ gives
$$
[C:U]=[\varphi(C):\ell\varphi(C)]=\lvert\varphi(C)[\ell]\rvert=\lvert\varphi(C)\cap C[\ell]\rvert .
$$
If $\varphi(x)=\ell\varphi(y)$, then $\varphi(\psi x)=\psi\varphi(x)=\ell\varphi(\psi y)$, so $\psi U\subseteq U$ and $\psi$ induces $\bar\psi$ on $V=C/U$. The hypothesis says $\varphi(\psi^Nx)=\psi^N\varphi(x)\in\ell\varphi(C)$, so $\psi^Nx\in U$ for all $x$, that is $\bar\psi^N=0$. Next, $\varphi(\ell x)=\ell\varphi(x)$ shows $\ell C\subseteq U$. The preimage of $\bar\psi V$ in $C$ is $U+\psi C\supseteq\ell C+\psi C$, so $[V:\bar\psi V]$ divides $[C:\ell C+\psi C]$. Lemma 2 for $\bar\psi$ gives $[C:U]=\lvert V\rvert\le[V:\bar\psi V]^N$. $\square$

**Proposition 4 (the group-ring form).** [Lean, read] Let a commutative group $G$ act on a finite abelian group $C$. Let $J,\gamma\in G$ with $J^2=1$ and $\theta\in\mathbb Z[G]$. Assume that $\theta(1-[J])$ acts on $C$ as zero and that $([\gamma]-1)^N\in(\theta,\,1+[J],\,\ell)$. Then
$$
\lvert(1-J)C\cap C[\ell]\rvert\le[C:\ell C+(1-\gamma)C]^N .
$$

**Proof.** Put $a=1-[J]$ and $b=1-[\gamma]$. As $b^N=(-1)^N([\gamma]-1)^N$, there are $u,v,z\in\mathbb Z[G]$ with $b^N=u\theta+v(1+[J])+\ell z$. Since $[J]^2=1$, $a(1+[J])=0$, and multiplying by $a$ gives
$$
ab^N=u\cdot\theta a+\ell\,az .
$$
Let $\varphi=1-J$ and $\psi=1-\gamma$ act on $C$. The term $u\cdot\theta a$ acts as zero by hypothesis, so $\psi^N\varphi(x)=\ell\,\varphi(zx)$ for every $x\in C$. Hence $\psi^N\varphi(C)\subseteq\ell\varphi(C)$, and $\varphi,\psi$ commute because $G$ is commutative. Lemma 3 applies. $\square$

**Remark 4 (where the uniformity comes from).** [Expository] Let $\gamma=1+f\ell^e$ in $G=(\mathbb Z/f\ell^n\mathbb Z)^\times$. It generates the kernel of reduction to $(\mathbb Z/f\ell^e\mathbb Z)^\times$ (`gamGen`). This kernel has order $\varphi(f\ell^n)/\varphi(f\ell^e)=\ell^{n-e}$, and it is a direct factor of $G$ not containing $J$. Hence $\mathbb Z[G]/(1+[J],\ell)\cong R\otimes\mathbb F_\ell[T]/(T^{\ell^{n-e}})$ with $T=[\gamma]-1$ and $R=\mathbb F_\ell[G/\langle\gamma\rangle]/(1+[J])\neq0$. So $([\gamma]-1)^N\in(1+[J],\ell)$ if and only if $N\ge\ell^{n-e}$. With $\theta=0$, Proposition 4 would only give $\lvert(1-J)C\cap C[\ell]\rvert\le B^{\ell^{n-e}}$, a bound that grows with $n$. The membership of §11.4.3.1 adds $\theta_{\mathrm{half}}$ to the ideal and lowers the exponent to $N=\ell^{d+a}$, with $d$ from `nonvan` and $\ell^a$ the $\ell$-part of $\varphi(f\ell^e)$, independent of $n$. The two examples show the opposite situation on a single module: the universal exponent can be larger than the exponent a particular module needs. The proof only needs uniformity, not sharpness.

**Lemma 5 (Stickelberger annihilation in the form used).** Let $M>2$, let $c$ be odd and prime to $M$, put $k=(c-1)/2$ and
$$
g_c(s)=\left\lfloor\frac{c\,\operatorname{rep}_M(c^{-1}s)}{M}\right\rfloor-k\qquad(s\in G).
$$

(i) [Lean, read] $\theta_{\mathrm{half}}(1-[-1])=\sum_{s\in G}g_c(s)[s]$, and every coefficient of $\theta_{\mathrm{half}}(1+[-1])$ is congruent to $g_c(s)$ modulo $2$.

(ii) [Lean, read, assuming Stickelberger's theorem [Lean]] Suppose that whenever $\beta,\gamma'\colon G\to\mathbb Z$ satisfy $M\gamma'(t)=\sum_s\beta(s)\operatorname{rep}_M(st)$ for all $t$, the element $\sum_t\gamma'(t)\sigma_t^{-1}$ annihilates $\mathrm{Cl}(L)$ (`Stick.coef`). Then $\theta_{\mathrm{half}}(1-[-1])$ annihilates $\mathrm{Cl}(L)$.

**Proof.** (i) The coefficient of $[s]$ in $\theta_{\mathrm{half}}[-1]$ is the coefficient of $[-s]$ in $\theta_{\mathrm{half}}$. Exactly one of $s,-s$ has least residue below $M/2$, since $2\operatorname{rep}_M(s)=M$ would give $2s=0$ for a unit, hence $M\le2$. For $s$ in the lower half the coefficient of $[s]$ in $\theta_{\mathrm{half}}(1-[-1])$ is $g_c(s)$. For $s$ in the upper half it is $-g_c(-s)=g_c(s)$, by the symmetry $g_c(-s)=-g_c(s)$ of §11.4.3.1 (`gcNeg`). With $1+[-1]$ the upper-half coefficient is $g_c(-s)\equiv g_c(s)\pmod2$. (ii) Take $\beta=c\,\mathbf 1_{\{c^{-1}\}}-(k+1)\mathbf 1_{\{1\}}-k\,\mathbf 1_{\{-1\}}$. Using $\operatorname{rep}_M(-t)=M-\operatorname{rep}_M(t)$,
$$
\sum_s\beta(s)\operatorname{rep}_M(st)=c\operatorname{rep}_M(c^{-1}t)-\operatorname{rep}_M(t)-kM .
$$
Since $c\cdot c^{-1}t\equiv t\pmod M$, division with remainder reads $c\operatorname{rep}_M(c^{-1}t)=Mq+\operatorname{rep}_M(t)$ with $q=\lfloor c\operatorname{rep}_M(c^{-1}t)/M\rfloor$. So the right side equals $M(q-k)=Mg_c(t)$. The hypothesis gives $\sum_tg_c(t)\sigma_t^{-1}=0$ on $\mathrm{Cl}(L)$. By (i) and the convention $[t]\mapsto\sigma_t^{-1}$, this operator is the action of $\theta_{\mathrm{half}}(1-[-1])$. $\square$

In classical terms [Expository], $\sum_tg_c(t)[t]=\beta^\ast\Theta$ with $\beta^\ast=c[c]-(k+1)-k[-1]$. Since $\Theta(1+[-1])=\sum_u[u]$, this equals $(c[c]-1)\Theta-k\sum_u[u]$. Here $[c]$ acts as $\sigma_c^{-1}$, and the norm element kills $\mathrm{Cl}(L)$ because $N_{L/\mathbb Q}$ of an ideal is principal. So the annihilator used is, up to the unit $\sigma_c^{-1}$ and the norm, the integral Stickelberger element $(c-\sigma_c)\theta$; compare [Washington1997, §6.2]. The archive proves `Stick.coef` from a degree-one prime in each class (`degOne`) and a Jacobi-sum carry identity at that prime (`carryPrime`), followed by `combFloor` and `comb` (`carryAll`). That proof is not read here.

**Proposition 6 (the ambiguous quotient).** Let $F=\mathbb Q(\zeta_{f\ell^e})$, with $f$ prime to $\ell$. Let $B_F$ be the number of continuous homomorphisms $\mathrm{Gal}(\overline F/F)\to\mathbb Z/\ell$ that vanish on the inertia groups of all finite places not above $\ell$. Then $B_F<\infty$. For every $n\ge2$ and every $\gamma\in(\mathbb Z/f\ell^n\mathbb Z)^\times$ with $\gamma\equiv1+f\ell^e$, the class group $C$ of $L=\mathbb Q(\zeta_{f\ell^n})$ satisfies
$$
[C:\ell C+(1-\gamma)C]\le B_F .
$$
[Lean, read for the reduction and the counting; the inputs named in the proof are [Lean]]

**Proof.** *Step 1 (relative Galois group).* Since $e\le2\le n$, $F\subseteq L$, and $L=F(\zeta_{\ell^n})$. The group $\mathrm{Gal}(L/F)$ consists of the $\sigma_t$ with $t\equiv1\bmod f\ell^e$, and these $t$ form the cyclic group generated by $\gamma$ (`relCyc`, `gamGen` [Lean]). So $\tau=\sigma_{\gamma^{-1}}$ generates $\mathrm{Gal}(L/F)$, and by the convention above $\tau$ acts on $C$ as $[\gamma]$.

*Step 2 (invariant characters).* Put $H=\ell C+(1-\tau)C$ and $Q=C/H$. Then $\tau$, hence all of $\mathrm{Gal}(L/F)$, acts trivially on $Q$, and $\ell Q=0$. By Lemma 1, $[C:H]=\lvert\mathrm{Hom}(Q,\mathbb Z/\ell)\rvert$, and composing with $C\to Q$ embeds $\mathrm{Hom}(Q,\mathbb Z/\ell)$ into the $\mathrm{Gal}(L/F)$-invariant characters $C\to\mathbb Z/\ell$.

*Step 3 (class field theory).* Composition with the Artin map identifies the invariant class characters with the group $E$ of continuous homomorphisms $\chi\colon G_L\to\mathbb Z/\ell$ that vanish on all inertia groups and are invariant under conjugation by $G_F$ (`pullEq`, `pullMem` [Lean]; this step uses that $L$ is totally complex).

*Step 4 (extension to $G_F$).* $E$ is finite. Let $N=\bigcap_{\chi\in E}\ker\chi$, an open subgroup of $G_L$ that is normal in $G_F$ by invariance. For $g\in G_F$ and $u\in G_L$, $\chi(gug^{-1}u^{-1})=\chi(gug^{-1})-\chi(u)=0$, so $[G_F,G_L]\subseteq N$. Thus $G_L/N$ is central in $G_F/N$ with cyclic quotient $\mathrm{Gal}(L/F)$, and therefore $G_F/N$ is abelian. A homomorphism $G_L\to\mathbb Z/\ell$ that is trivial on $N$ lies in $E$. It is continuous because $N$ is open, unramified because inertia elements of $G_L$ lie in $N$, and invariant because commutators lie in $N$. Hence $\lvert E\rvert=\lvert\mathrm{Hom}(G_L/N,\mathbb Z/\ell)\rvert$. For finite abelian groups $B\le A$, Lemma 1 gives $\lvert\mathrm{Hom}(B,\mathbb Z/\ell)\rvert=\lvert B[\ell]\rvert\le\lvert A[\ell]\rvert=\lvert\mathrm{Hom}(A,\mathbb Z/\ell)\rvert$. So $\lvert E\rvert\le\lvert\mathrm{Hom}(G_F/N,\mathbb Z/\ell)\rvert$ (`homCyc`). Finally, every homomorphism $G_F\to\mathbb Z/\ell$ trivial on $N$ is continuous and kills the inertia group of every finite place not above $\ell$. Such inertia groups lie in $G_L$ because $L/F$ is unramified outside $\ell$ (`ineCyc` [Lean]), and their elements then lie in $N$. Therefore $\lvert E\rvert\le B_F$ (`ambHom`). Finiteness of $B_F$ is `finChar` [Lean], whose statement requires a primitive $\ell$-th root of unity in $F$. $\square$

By Lemma 1 for $T=1-\tau$, the invariant classes $C^{\tau}$ and the coinvariants $C/(1-\tau)C$ have the same order, which is why this is an ambiguous-class estimate. The archive bounds only the $\ell$-rank of the coinvariants. For comparison, the ambiguous class number formula for a cyclic extension $L/K$ of prime degree $\ell$ counts the ambiguous classes exactly as $h(K)\,\ell^{t-1}/(E_K:E_K\cap N_{L/K}L^\times)$, where $t$ is the number of ramified places, infinite ones included [Paper] [Lemmermeyer2013, Theorem 1]. The archive does not compute a unit index. It bounds only the $\ell$-rank of the coinvariants, for the layers $F(\zeta_{\ell^n})/F$ of every degree, by the number $B_F$ of $\mathbb Z/\ell$-characters of $G_F$ unramified outside $\ell$, a constant that is not made explicit.

**Lemma 7 (odd $\ell$: from the $(1-J)$-image to the $\ell$-rank).** [Lean, read] Let $\ell$ be odd and $J$ an automorphism of a finite abelian group $C$ with $J^2=1$. Then $C^-[\ell]=(1-J)C\cap C[\ell]$. If moreover $[C:\ell C+(1-J)C]\le\ell\,\lvert C^-\cap C[\ell]\rvert$, then
$$
[C:\ell C]\le\ell\cdot\lvert(1-J)C\cap C[\ell]\rvert^2 .
$$

**Proof.** If $Jx=-x$ and $\ell x=0$ with $\ell=2k+1$, then $(1-J)((k+1)x)=(2k+2)x=x$. Conversely $(1-J)C\subseteq C^-$, because $J(1-J)=-(1-J)$ when $J^2=1$. Put $D=(1-J)C$. Then $[C:\ell C]=[\ell C+D:\ell C]\cdot[C:\ell C+D]$. The first factor is $[D:D\cap\ell C]\le[D:\ell D]=\lvert D[\ell]\rvert$ by Lemma 1. The second is at most $\ell\lvert C^-[\ell]\rvert=\ell\lvert D[\ell]\rvert$. $\square$

The hypothesis is the reflection inequality `reflOdd`: for a CM field $K$ containing $\zeta_\ell$ with $\ell$ odd,
$$
[\mathrm{Cl}(K):\ell\,\mathrm{Cl}(K)+(1-J)\mathrm{Cl}(K)]\le\ell\cdot\lvert\mathrm{Cl}(K)^-\cap\mathrm{Cl}(K)[\ell]\rvert .
$$
[Lean, read for the counting; Kummer and class-field inputs [Lean]] Its proof in the archive is a kernel–image count. The left side counts class characters fixed by complex conjugation (Lemma 1). Through the Artin map these are unramified $\mathbb Z/\ell$-characters of $G_K$ fixed by a lift of complex conjugation (`pullEq`, `pullMem`). Each such character has a Kummer radical $\beta$ with $\beta^\ell=a\in K^\times$, where $(a)=\mathfrak a^\ell$. Because $J\zeta_\ell=\zeta_\ell^{-1}$, the fixed characters have $a\cdot J(a)\in K^{\times\ell}$, so the class $[\mathfrak a]$ lies in $\mathrm{Cl}(K)^-[\ell]$; this map $\kappa$ has image in the right-hand group (`reflect`, `reflMap`, `reflTw`, `radXDual`). If $[\mathfrak a]=1$, then $a$ is a unit times an $\ell$-th power, and the minus condition forces $a=t\,b^\ell$ with $t$ a root of unity (`reflect_tors`, using `radClKer` and `unitMinus`). So the kernel of $\kappa$ consists of characters with root-of-unity radicals, and there are at most $\ell$ of them (`reflRoot`). The factor $\ell$ is this root-of-unity error. Compare the reflection theorems of [Washington1997, §10.2].

**Lemma 8 ($\ell=2$).**

(i) [Lean, read] For an automorphism $J$ of a finite abelian group $C$ with $J^2=1$,
$$
[C:2C]\le\bigl([C^-:(1-J)C]\cdot\lvert(1-J)C\cap C[2]\rvert\bigr)^2 .
$$

(ii) [Lean, read] Let $G$ be a finite commutative group, $J\in G$ with $J^2=1\neq J$, $\gamma\in G$ and $\theta\in\mathbb Z[G]$. Let $\mathcal E_J$ be the group of functions $G\to\mathbb F_2$ with $h(Jg)=h(g)$, and let $S$ be a translation-stable subgroup of $\mathrm{Map}(G,\mathbb F_2)$ containing the reductions mod $2$ of the coefficients of $\theta(1+[J])$. If $([\gamma]-1)^N\in(\theta,1+[J],2)$, then $[\mathcal E_J:S\cap\mathcal E_J]\le2^{[G:\langle\gamma\rangle]N}$.

(iii) [Lean, read as an assembly of named inputs] For $L=\mathbb Q(\zeta_{f2^n})$ with $f>1$ odd and $n\ge2$, and the membership of `memZ`, $[\mathrm{Cl}(L)^-:(1-J)\mathrm{Cl}(L)]\le2^{\varphi(4f)N}$ (`sgnCyc`).

**Proof.** (i) Let $T=C[2]$, $D=(1-J)C$ and $K=C^-$; then $D\subseteq K$, and $[C:2C]=\lvert T\rvert$ by Lemma 1. The map $t\mapsto t-Jt$ sends $T$ into $D\cap T$. Its kernel consists of the $t\in T$ with $Jt=t$, and these lie in $K\cap T$ because $Jt+t=2t=0$. The map $K\cap T\to K/D$ has kernel $D\cap T$. Hence $\lvert T\rvert\le\lvert K\cap T\rvert\cdot\lvert D\cap T\rvert\le[K:D]\cdot\lvert D\cap T\rvert^2$, which is at most the square of $[K:D]\cdot\lvert D\cap T\rvert$.

(ii) This is a group-ring module length estimate. Define $\kappa\colon\mathbb Z[G]\to\mathrm{Map}(G,\mathbb F_2)$ by letting $\kappa(x)(g)$ be the coefficient of $[g]$ in $x(1+[J])$ modulo $2$, that is, $x_g+x_{Jg}$. Because $J\neq1$ the orbits $\{g,Jg\}$ have two elements, and prescribing $x$ on one element of each orbit shows that $\kappa$ maps onto $\mathcal E_J$. Since $\kappa([g]x)$ is a translate of $\kappa(x)$, the preimage $I=\kappa^{-1}(S)$ is an ideal. It contains $\theta$ by hypothesis. It contains $1+[J]$ and $2$, since $(1+[J])^2=2(1+[J])$ and $\kappa$ of an even element vanishes. Hence $([\gamma]-1)^N\in I$. Now $\kappa$ induces $\mathbb Z[G]/I\cong\mathcal E_J/(S\cap\mathcal E_J)$, a group killed by $2$. Multiplication by $t=[\gamma]-1$ is an endomorphism of $V=\mathbb Z[G]/I$ with $t^N=0$, so Lemma 2 gives $\lvert V\rvert\le\lvert V/tV\rvert^N$. In $V/tV$ the images of $[\gamma g]$ and $[g]$ agree. So $V/tV$ is generated by $[G:\langle\gamma\rangle]$ elements of order at most $2$, and $\lvert V/tV\rvert\le2^{[G:\langle\gamma\rangle]}$.

(iii) `sgnCyc` applies (ii) with $S$ the span of the sign vectors $t\mapsto\operatorname{sgn}\varphi(\sigma_t u)$ of real units $u$ of $L$ under one complex embedding $\varphi$. The hypothesis on $\theta$ comes from `sgnUnit`, `sgnStab` and Lemma 5(i). It combines this with `hMinus`, which gives $[\mathrm{Cl}(L)^-:(1-J)\mathrm{Cl}(L)]\le[\mathcal E_J:S\cap\mathcal E_J]$ when $L/L^+$ is unramified at all finite places (`unrJ`, which needs $f>1$ odd and $n\ge2$) and $u\mapsto u/\bar u$ maps the units onto the roots of unity (`unitSurj`). The index $[G:\langle\gamma\rangle]=\varphi(4f)$ is part of the output of `memZ`. The proof of `hMinus` sends a minus class $[\mathfrak a]$ to the sign vector of a real generator of $\mathfrak a\cdot J(\mathfrak a)$, modulo the signs of real units, and shows that this map is injective on $\mathrm{Cl}(L)^-/(1-J)\mathrm{Cl}(L)$ (the map is defined at `HMinus.lean:138–146`). The injectivity proof, `realGen`, and the bodies of `sgnUnit`, `sgnStab`, `unrJ` and `unitSurj` are not read here [Lean]. $\square$

**Theorem 9 (uniform rank bound on the cyclotomic layers; `cyc`).** Let $\ell$ be prime, $f>1$ prime to $\ell$, $c=2f\ell+1$, and $L_n=\mathbb Q(\zeta_{f\ell^n})$ with $C_n=\mathrm{Cl}(L_n)$. Assume the named inputs: the membership `memZ` (§11.4.3.1), Stickelberger's theorem `Stick.coef`, the inputs of Proposition 6, the reflection inputs of Lemma 7 when $\ell$ is odd, and the sign inputs of Lemma 8(iii) when $\ell=2$. Then there are $N$, $n_0\ge2$ and $B$, depending only on $\ell$ and $f$, such that for every $n\ge n_0$:
$$
\lvert(1-J)C_n\cap C_n[\ell]\rvert\le B^N,\qquad
[C_n:\ell C_n]\le\begin{cases}\ell\,B^{2N},&\ell\ \text{odd},\\ \bigl(2^{\varphi(4f)N}B^N\bigr)^2,&\ell=2.\end{cases}
$$
In particular $d_\ell(C_n)$ is bounded independently of $n$. [Lean, read for the assembly; inputs as named]

**Proof, with the arguments of `cyc`.** The constant $c$ is odd, greater than $1$ and prime to $f\ell$ (`FerreroWashington.lean:25–28`). `memZ l f c` returns $N$, $n_0\ge2$ and, for each $n\ge n_0$, an element $\gamma$ with $\gamma=1+f\ell^e$, $[G:\langle\gamma\rangle]=\varphi(f\ell^e)$ and $([\gamma]-1)^N\in(\theta_{\mathrm{half}},1+[-1],\ell)$ (`:29`, `:43`, `:79`). `ambCyc l f` returns $B=B_F$ (`:30`). Fix $n\ge n_0$. Then $f\ell^n>2$, so $L_n$ is CM and totally complex (`:36–42`, `:68–78`). The call of `core` is Proposition 4 with group $(\mathbb Z/f\ell^n\mathbb Z)^\times$, module $\mathrm{Cl}(L_n)$, representation `cycRep`, $J=-1$, the given $\gamma$, $\theta=\theta_{\mathrm{half}}$ (`thetaH (f*l^n) c`) and exponent $N$. Its hypotheses are $(-1)^2=1$, the two instances of `cycRep_apply` identifying the actions of $[J]$ and $[\gamma]$ with `clA`, Lemma 5 (`stickH`, with $c$ prime to $f\ell^n$ by `:44–46`, `:80–82`) and the membership (`:47–50`, `:83–86`). Proposition 6 with $n\ge2$ and $\gamma=1+f\ell^e$ bounds the index by $B$ (`:51`, `:87`), which gives the first inequality (`:52–53`, `:88–89`). `conjEq` identifies `clA (-1)` with the action of complex conjugation (`:55`, `:98`). For odd $\ell$, $\zeta^{f\ell^{n-1}}$ is a primitive $\ell$-th root of unity in $L_n$ (`:91–97`). Then `reflOdd` supplies the hypothesis of Lemma 7 (`:99–100`), and `pOdd` gives $[C_n:\ell C_n]\le\ell\,(B^N)^2$ (`:101–102`). For $\ell=2$, $f$ is odd (`:54`). `sgnCyc` gives the defect bound of Lemma 8(iii), rewritten with $[G:\langle\gamma\rangle]=\varphi(4f)$ (`:56–57`). After checking that `clA (-1)` is an involution (`:58–62`), `pTwo` gives Lemma 8(i), and the two bounds combine to $\bigl(2^{\varphi(4f)N}B^N\bigr)^2$ (`:63–64`). $\square$

The hypothesis $f>1$ is used only in the $\ell=2$ branch, by `unrJ` and `unitSurj` through `sgnCyc`. The descent from these cyclotomic fields to an arbitrary abelian $K$ is the second half of Proposition 11.3 (`:104–119`).

**Remarks.** [Expository] *Image of $1-J$ and minus subgroup.* Always $(1-J)C\subseteq C^-$, and $C^-/(1-J)C$ is killed by $2$, since $Jx=-x$ gives $2x=(1-J)x$. With $\langle J\rangle$ acting, $C^-/(1-J)C=\ker(1+J)/(1-J)C$ is the Tate cohomology group $\widehat H^{-1}(\langle J\rangle,C)$, and $C^+/(1+J)C=\widehat H^0(\langle J\rangle,C)$. For odd $\ell$ both vanish on $\ell$-primary parts, so the $(1-J)$-image and the minus subgroup have the same $\ell$-torsion (Lemma 7), and Theorem 9 is a statement about $C^-$. For $\ell=2$ they differ, and Example 2 shows that the difference can carry the whole $2$-rank. The class-group argument (Proposition 4) controls only the image. The defect is controlled through units (Lemma 8), and the same membership enters again, now reduced modulo $2$ in a quotient of the group ring.

*Kernels, cokernels and roots of unity.* Lemma 1 appears for multiplication by $\ell$ (torsion versus cotorsion, in Lemmas 3, 7 and 8), inside Lemma 2, and in the character counts of Proposition 6 and Lemma 7. Applied to $1-\tau$, it identifies the order of the coinvariant quotient with that of the ambiguous classes. The subgroup $U$ of Lemma 3 is the kernel of $C\to\varphi(C)/\ell\varphi(C)$, and the nilpotent map acts on $C/U\cong\varphi(C)/\ell\varphi(C)$. Roots of unity enter at three places. In Proposition 6, $\zeta_\ell\in F$ is used only for the finiteness of $B_F$. In Lemma 7 the kernel of the Kummer map consists of root-of-unity radicals and produces the factor $\ell$. For $\ell=2$, the unit index condition `unitSurj` and the signs of real units replace Kummer theory. The Teichmüller representatives behind $\theta_{\mathrm{half}}$ belong to §11.4.3.1 and are not used again here.

*Comparison with the literature.* The theorem behind this step is Ferrero–Washington [FerreroWashington1979]. Sinnott's proof of $\mu=0$ is in [Washington1997, §16.2]. The archive does not pass through the Iwasawa module here. It bounds $d_\ell$ of each finite layer directly, and the rank form `FerreroWashington` consumes exactly this bound. The Iwasawa-theoretic reading of the same bound, under named control and structure inputs, is the last remark of §11.4.3.1 and is not repeated.

**Reading boundary.** Read in full for this subsection [Lean, read]: `cyc` (`FerreroWashington.lean:18–102`), `core` and `card_range_inf_torsion_le_index_pow`, `nilCard`, `cardTors`, `stickH` and `thetaFull`, `ambCyc`, `amb`, `ambHom` and `homCyc`, `pOdd`, `reflOdd` and the counting body of `reflect`, `pTwo`, `sgnAlg`, `sgnCyc` as an assembly, `conjEq` and the definitions in `CycRepApply.lean` and `TwSingle.lean`. Named inputs not read here [Lean]: `memZ` (read in §11.4.3.1), `Stick.coef` (with `carryAll`, `degOne`, `carryPrime`, `combFloor`, `comb`), `relCyc`, `gamGen`, `ineCyc`, `finChar`, `pullEq`, `pullMem`, `reflMap`, `reflTw`, `radClKer`, `hMinus` beyond the definition of its sign map, `realGen`, `sgnUnit`, `sgnStab`, `unrJ` and `unitSurj`. No Iwasawa control theorem or structure theorem for $\mathbb Z_\ell[[T]]$-modules is used. Section 11.4.3.3 reads the three direct Kummer producers `radXDual`, `unitMinus` and `reflRoot`.

**Source map.** Paths are relative to the archive root, with joined SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The prefix `GL/` stands for `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/`.

| Archive file and lines | Declaration | Status |
| --- | --- | --- |
| `GL/FerreroWashingtonIndex/FerreroWashington.lean:18–102` | `cyc` | [Lean, read] |
| `GL/FerreroWashingtonIndex/CardRangeInfTorsionLeIndexPow.lean:7–62` | `card_range_inf_torsion_le_index_pow` (Lemma 3) | [Lean, read] |
| `GL/FerreroWashingtonIndex/CardRangeInfTorsionLeIndexPow.lean:64–105` | `core` (Proposition 4) | [Lean, read] |
| `GL/FerreroWashingtonIndex/NilCard.lean:5–91` | `nilCard` (Lemma 2) | [Lean, read] |
| `GL/FerreroWashingtonIndex/CardTors.lean:5–60` | `cardTors` (Lemma 1) | [Lean, read] |
| `GL/FerreroWashingtonIndex/TwSingle.lean:42–64` | `gc`, `thetaH`, `powR`, `torK`, `difR`, `minK` | [Lean, read] |
| `GL/FerreroWashingtonIndex/CycRepApply.lean:16–24` | `clA`, `cycRep`, `cycRep_apply` | [Lean, read] |
| `GL/FerreroWashingtonIndex/ConjEq.lean:6–39` | `conjEq` | [Lean, read] |
| `GL/FerreroWashingtonIndex/ThetaFull.lean:6–65` | `thetaFull` (Lemma 5(i)) | [Lean, read] |
| `GL/FerreroWashingtonIndex/StickH.lean:8–44` | `stickH` (Lemma 5(ii)) | [Lean, read] |
| `GL/StickelbergerTheorem/ImportsAlt.lean:9–16` | `Stick.coef` | [Lean] |
| `GL/FerreroWashingtonIndex/AmbCyc.lean:9–75` | `ambCyc` (Proposition 6) | [Lean, read] |
| `GL/FerreroWashingtonIndex/AmbIndex.lean:11–127` | `amb` | [Lean, read] |
| `GL/FerreroWashingtonIndex/AmbHom.lean:10–122` | `ambHom` | [Lean, read] |
| `GL/FerreroWashingtonIndex/HomCyc.lean:6–98` | `homCyc` | [Lean, read] |
| `GL/FerreroWashingtonIndex/RelCyc.lean:28` | `relCyc` | [Lean] |
| `GL/FerreroWashingtonIndex/GamGen.lean:65` | `gamGen` | [Lean] |
| `GL/FerreroWashingtonIndex/IneCyc.lean:52` | `ineCyc` | [Lean] |
| `GL/KummerTheory/FinChar.lean:49` | `finChar` | [Lean] |
| `GL/KummerTheory/PullEq.lean:7` | `pullEq` | [Lean] |
| `GL/KummerTheory/PullMem.lean:10` | `pullMem` | [Lean] |
| `GL/FerreroWashingtonIndex/POddRelIndexLe.lean:5–51` | `pOdd` (Lemma 7) | [Lean, read] |
| `GL/FerreroWashingtonIndex/ReflOdd.lean:11–113` | `reflOdd` | [Lean, read] |
| `GL/KummerTheory/Reflect.lean:11–90` | `reflect` (counting body) | [Lean, read] |
| `GL/FerreroWashingtonIndex/PTwo.lean:5–85` | `pTwo` (Lemma 8(i)) | [Lean, read] |
| `GL/FerreroWashingtonIndex/SgnAlg.lean:6–137` | `sgnAlg` (Lemma 8(ii)) | [Lean, read] |
| `GL/FerreroWashingtonIndex/SgnCyc.lean:13–37` | `sgnCyc` (Lemma 8(iii)) | [Lean, read] |
| `GL/FerreroWashingtonIndex/HMinus.lean:135` | `hMinus` | [Lean] |
| `GL/FerreroWashingtonIndex/SgnUnit.lean:54` | `sgnUnit` | [Lean] |
| `GL/FerreroWashingtonIndex/SgnStab.lean:12` | `sgnStab` | [Lean] |
| `GL/FerreroWashingtonIndex/UnrJPrime.lean:45` | `unrJ` | [Lean] |
| `GL/FerreroWashingtonIndex/UnitSurj.lean:77` | `unitSurj` | [Lean] |
| `GL/FerreroWashingtonIndex/ToKOf.lean:13` | `memZ` (see §11.4.3.1) | [Lean, read] |

#### 11.4.3.3 Kummer reflection and the root-of-unity kernel

The odd-prime branch of §11.4.3.2 has a bound on the image of $1-J$, where $J$ is complex conjugation on the class group of the layer $L=\mathbb Q(\zeta_{f\ell^n})$. To count the remaining classes modulo $\ell$, take characters of the quotient by this image. They are fixed by conjugation. A Kummer character measures how an automorphism moves a root, with values in $\mu_\ell$. Since conjugation inverts those values, a fixed scalar-valued character yields an inverted radical class. The kernel of the resulting map to the negative class group is controlled by the roots of unity. This is the use of reflection in the finite layer.

**Example 1 (a field containing $\mu_3$).** [Expository] Put $K=\mathbb Q(\zeta_3)$ and $\ell=3$. The ring of integers $\mathbb Z[\zeta_3]$ has discriminant $-3$. The imaginary quadratic Minkowski bound $2\sqrt{3}/\pi<2$ makes every ideal class principal. Thus $C=0$, $(1-J)C=C^-=0$, and the dual of $C/(3C+(1-J)C)$ has one element. The unit norm of $x+y\zeta_3$ is $x^2-xy+y^2$. Solving for norm $1$ using $(2x-y)^2+3y^2=4$ gives the six units $\mu_6$. A cube root in $K$ of any of these units would itself be integral with integral inverse. Hence the unit image modulo $K^{\times3}$ has order $3$, represented by $1,\zeta_3,\zeta_3^2$. All three classes are inverted by $J$ and map to the principal ideal class.

Write $\xi=\zeta_9$ with $\xi^3=\zeta_3$. On $E=K(\xi)$ take $u(\xi)=\xi^4$ and let $J$ act by inversion on $\xi$. On the powers of $u$ the pairing is
$$
\langle u^i,[\zeta_3^j]\rangle=\zeta_3^{ij}\qquad (i,j\in\mathbb Z/3\mathbb Z).
$$
The two automorphisms commute, so the scalar characters $u^i\mapsto ij$ are fixed by conjugation. The target $\mu_3$ contributes the sign $-1$, accounting for inversion on the radical side. Evaluation at $u$ gives the full three-element allowance for root-of-unity characters. In the unramified character space only the zero character survives. Indeed $\Phi_9(1+X)=(1+X)^6+(1+X)^3+1$ has constant term $3$, leading coefficient $1$, and all other coefficients divisible by $3$. Eisenstein gives total ramification at $3$ in $E/\mathbb Q$, hence ramification of degree $3$ in $E/K$. In the rank inequality the negative torsion contributes size $1$ and the kernel estimate permits a factor $3$, while the actual index is $1$.

**Example 2 (a field without $\mu_3$).** [Expository] Put $K_0=\mathbb Q(\sqrt{-23})$ and $\omega=(1+\sqrt{-23})/2$. Then $\mathcal O_{K_0}=\mathbb Z[\omega]$ and $\omega^2-\omega+6=0$. The discriminant is $-23$, so $K_0$ is distinct from the quadratic field $\mathbb Q(\zeta_3)$. The Minkowski bound $2\sqrt{23}/\pi<4$ gives representatives of norm $1$, $2$, or $3$. The polynomial reduces to $X(X-1)$ at both $2$ and $3$. Write $\mathfrak p=(2,\omega)$ and $\mathfrak q=(3,\omega)$, with the other primes their conjugates. Since $\operatorname{Nm}(\omega)=6$, one has $(\omega)=\mathfrak p\mathfrak q$. Thus the classes of norm $2$ and $3$ are represented by $\pm[\mathfrak p]$. The norm formula
$$
\operatorname{Nm}(x+y\omega)=(x+y/2)^2+23y^2/4
$$
rules out norm $2$ and shows that the units are $\{\pm1\}$. In particular $\mathfrak p$ is nonprincipal. The element $\omega-2$ has norm $8$, vanishes at $\mathfrak p$, and reduces to $1$ at its conjugate. Hence $(\omega-2)=\mathfrak p^3$ and $C=\mathbb Z/3\mathbb Z$ generated by $[\mathfrak p]$. Complex conjugation sends that generator to its inverse class, because $\mathfrak p J\mathfrak p=(2)$. Consequently $1-J$ multiplies by $2$, $(1-J)C=C^-=C[3]=C$, and $[C:3C]=3$. The full class dual has characters $\lambda_j(k[\mathfrak p])=jk$. Their values under precomposition by $J$ change sign, so the fixed dual of $C/(3C+(1-J)C)$ has only the zero character.

The element $a=\omega-2$ has cube-divisible valuations and gives a nonprincipal class by the ideal-root map. Here $aJ(a)=8=2^3$, exhibiting the negative radical class directly. The unit contribution modulo cubes over $K_0$ has order $1$, since both units are cubes. The scalar Kummer formula in the theorem below requires a primitive cube root in its ground field. Over $K'=K_0(\zeta_3)$ the radical $a$ still fails to be a cube: otherwise taking the norm from the quadratic extension $K'/K_0$ makes $a^2$ a cube, which makes $a$ a cube and contradicts the nonprincipality of $\mathfrak p$. Thus a root $\beta$ of $X^3-a$ gives a cyclic cubic extension of $K'$ with generator $u(\beta)=\zeta_3\beta$. The automorphism fixing $K_0$ and inverting $\zeta_3$ lifts to one fixing $\beta$, and conjugates $u$ to $u^{-1}$. The scalar radical character consequently has sign $-1$ under this automorphism, while the radical $a$ is fixed by it. Complex conjugation on $K'$ inverts $\zeta_3$ and sends $a$ to $8/a$. Its lift $\beta\mapsto 2/\beta$ commutes with $u$, so the scalar radical character has sign $+1$ under this lift. These are the two instances of the cyclotomic twist. This calculation concerns the pairing before imposing inertia conditions. The at-most-$3$ estimate belongs to the root-unit character count over a field containing $\mu_3$. The calculation of $[C:3C]=3$ over $K_0$ uses the explicit class group.

**Definitions.** Write class groups additively, and let $C=\mathrm{Cl}(K)$, $D=(1-J)C$, and $C^-=\ker(1+J)$. Here $K$ is a CM number field containing a chosen primitive $\ell$-th root $\zeta$, with $\ell$ odd. For the equivariant statement let $K/F$ be finite Galois, $\Omega$ an algebraic closure, $G=G_F$, and $U=G_K$ inside $G$. Let $\chi(g)$ be the scalar specified by $g(\zeta)=\zeta^{\chi(g)}$, and let $\psi:G\to\mathbb F_\ell^\times$ be a character. Write $X_\psi^+$ for the space of continuous additive characters $\phi:U\to\mathbb F_\ell$ that vanish on all finite inertia groups and satisfy
$$
\phi(gug^{-1})=\psi(g)\phi(u),\qquad
\phi(\widetilde J u\widetilde J^{-1})=\phi(u),
$$
where $\widetilde J$ lifts complex conjugation on $K$. These are the conditions of $\mathrm{EqEig}$ at splitting parameter $1$ and eigenvalue $1$. At general splitting parameter the definition also kills the decomposition groups at primes dividing that parameter. The consumer here takes $1$, so that condition is empty. Put $C[\ell]_{\chi\psi^{-1}}=\{c\in C[\ell]:gc=(\chi\psi^{-1})(g)c\ \forall g\in G\}$, with $g$ acting through its restriction to $K$.

A radical for $\phi$ is a nonzero $\beta\in\Omega$ with $u(\beta)=\zeta^{\phi(u)}\beta$. Then $a=\beta^\ell\in K^\times$. Define the valuation subgroup and its radical quotient by
$$
V=\{a\in K^\times:v_{\mathfrak p}(a)\in\ell\mathbb Z\ \text{at every finite prime }\mathfrak p\},\qquad R=V/K^{\times\ell}.
$$
The ideal-root map sends $[a]$ to $[\prod_{\mathfrak p}\mathfrak p^{v_{\mathfrak p}(a)/\ell}]$. This is $\mathrm{radCl}$ on the empty-set $\mathrm{SelK}$. All finite valuations are normalized to take integer values.

**Lemma (Kummer pairing and valuation condition).** [Lean, read] For any finite Galois extension $E/K$ with abelian group of exponent dividing $\ell$, put $R_E=(K^\times\cap E^{\times\ell})/K^{\times\ell}$. The pairing $\langle u,[a]\rangle=u(\beta)/\beta$, with $\beta^\ell=a$ in $E$, is perfect under the Hilbert 90 input. An unramified character of $U$ has a radical class in $R$ under the inertia-to-valuation input.

**Proof.** Multiplying $\beta$ by an element of $\mu_\ell$ or scaling it along with the representative $a$ by the corresponding element of $K^\times$ leaves the quotient unchanged. Multiplication of roots gives bilinearity, since $U$ fixes the values in $\mu_\ell$. The equation $u(\beta)/\beta=1$ for every $u$ means $\beta$ is fixed and belongs to $K$. Conversely, to recover a root from a character with values in $\mu_\ell$, apply Hilbert 90 to the cocycle $u\mapsto\zeta^{\phi(u)}$, which is locally constant for $U$ and factors through a finite quotient. It gives $\beta\ne0$ with the stated transformation. Taking $\ell$-th powers shows $\beta^\ell\in K^\times$. In the finite pairing this supplies every character of $\mathrm{Gal}(E/K)$, and the characters of that finite elementary abelian group separate its elements.

For the uniqueness assertion of `radXDual`, let $\beta$ and $\beta'$ give the same $\phi$. For every $u$,
$$
u(\beta'/\beta)=\frac{\zeta^{\phi(u)}\beta'}{\zeta^{\phi(u)}\beta}=\beta'/\beta.
$$
The fixed-field criterion yields $\beta'/\beta\in K^\times$, so $a$ is unique modulo $K^{\times\ell}$. In the production proof the homeomorphism in `toGalDict` transfers local constancy and identifies the inertia condition on $U$ with the one over $K$. Then `radExists` supplies the root and `dvdOfIne` gives $\ell\mid v_{\mathfrak p}(a)$ for each $\mathfrak p$, since inertia fixes $\beta$. In valuation terms the latter step takes the inertia-fixed field inside a finite Galois field containing $\beta$. At the chosen prime its ramification index over $K$ is $1$, so $v_{\mathfrak p}(a)=\ell v(\beta)$ with $v$ integer-valued there. This direction suffices for the proof. At primes over $\ell$ the valuation condition alone allows ramified Kummer extensions, as Example 1 shows. [MilneFT, Theorem 5.30 and Remark 5.32, pp. 75–76](https://www.jmilne.org/math/CourseNotes/FT.pdf).

**Lemma (negative units and the root-character bound).** [Lean, read] Suppose $a$ represents a class of $R$ with trivial ideal-root class and $aJ(a)\in K^{\times\ell}$. Then $a=t b^\ell$ for some $b\in K^\times$ and $t\in\mu(K)$, the group of roots of unity in $K$. Among characters satisfying the $\psi$-condition, those with a root-of-unity radical have cardinality at most $|\mathbb F_\ell^{G,\psi}|$, the size of the invariants of the scalar representation.

**Proof.** The trivial class says the fractional ideal $\prod_{\mathfrak p}\mathfrak p^{v_{\mathfrak p}(a)/\ell}$ is principal, say $(b)$. After division by $b^\ell$, the element is an everywhere finite unit $w$. The production proof of `unitMinus` identifies such a unit with an element of $\mathcal O_K^\times$ by applying the integrality criterion to $w$ and $w^{-1}$. The CM unit identity gives $w/J(w)$ of finite order. Indeed this is an algebraic integer and every complex embedding has modulus one, so Kronecker's theorem applies. The hypothesis gives $wJ(w)\in K^{\times\ell}$, and
$$
w^2=(w/J(w))(wJ(w))\in\mu(K)K^{\times\ell}.
$$
For $\ell=2k+1$, both $w^\ell$ and $(w^2)^k$ belong to that subgroup, hence so does their quotient $w$. This is precisely the oddness step of `unitMinus`. Writing $a=t b^\ell$ then replaces the radical $\beta$ by $\beta/b$, which has finite order and gives the same character.

Here is the common evaluation argument of `reflRoot`. Let $m=|\mu(K)|$. All roots of unity $\beta$ with $\beta^\ell\in K$ lie in the finite cyclic group
$$
T=\{\xi\in\mu_{\ell m}(\Omega):\xi^\ell\in K\}.
$$
Indeed $\beta^\ell$ has order dividing $m$. Choose a generator $\xi$ of $T$. The map $u\mapsto u(\xi)/\xi$ is a homomorphism into $\mu_\ell$ because $\xi^\ell\in K$ and $U$ fixes $\mu_\ell$. Choose $u_0\in U$ whose image generates its image, allowing the identity if that image is trivial. Any root character has a radical $\xi^j$. For each $u$ choose an integer $k_u$ with $u(\xi)/\xi=(u_0(\xi)/\xi)^{k_u}$. Taking the $j$-th power shows
$$
\zeta^{\phi(u)}=\bigl(\zeta^{\phi(u_0)}\bigr)^{k_u}.
$$
Thus a single evaluation at $u_0$ determines the character. Moreover every $g\in G$ and $u_0$ act by powers on the cyclic group generated by the given root of unity $\beta=\xi^j$. Their actions there commute, so $\phi(gu_0g^{-1})=\phi(u_0)$. The $\psi$-condition makes $\phi(u_0)$ an invariant. This proves injectivity into the invariants, including finiteness. With trivial $\psi$ their size is $\ell$. If $\psi$ is nontrivial their size is $1$, since one scalar $\psi(g)-1$ is invertible. The proof counts characters having such a radical and imposes the inertia condition separately.

**Theorem (odd-prime transport of a finite-layer bound).** [Lean, read] Assume radical existence via Hilbert 90 and the inertia-to-valuation implication of the first lemma, and assume the CM unit torsion identity of the second lemma. Then
$$
|X_\psi^+|\le |\mathbb F_\ell^{G,\psi}|\,|C[\ell]_{\chi\psi^{-1}}\cap C^-|.
$$
Assume also that Artin pullback embeds the fixed class characters into the unramified fixed Galois characters. If $|(1-J)C\cap C[\ell]|\le M$, then
$$
[C:\ell C]\le \ell M^2,\qquad
d_\ell(C)\le 1+2\log_\ell M.
$$

**Proof.** For $g\in G$ and any radical $\beta$ of $\phi$,
$$
\frac{u(g\beta)}{g\beta}
=g\!\left(\frac{(g^{-1}ug)(\beta)}{\beta}\right)
=\zeta^{\chi(g)\psi(g)^{-1}\phi(u)}.
$$
Thus $g\beta$ and $\beta^{\chi(g)\psi(g)^{-1}}$ have the same character, where an integer representative is used for the exponent. The fixed quotient argument gives $[g(a)]=[a]^{\chi(g)\psi(g)^{-1}}$ in $R$. For $\widetilde J$ the scalar character is fixed and $\widetilde J$ inverts $\zeta$, so $[J(a)]=[a]^{-1}$. This gives $aJ(a)\in K^{\times\ell}$. The ideal-root map respects multiplication and automorphisms, since they add or permute the normalized valuations. Changing $a$ by a power changes its ideal root by a principal ideal. Its image is $\ell$-torsion because the $\ell$-th power of the ideal root is $(a)$. Therefore the map $\kappa:X_\psi^+\to C$ sending a character to its ideal-root class takes values in $C[\ell]_{\chi\psi^{-1}}\cap C^-$. Its kernel has precisely the characters in $X_\psi^+$ that admit root-of-unity radicals. The forward implication is the negative-unit lemma, and a root of unity gives zero valuations for its $\ell$-th power, proving the converse. Counting kernel times image gives the first estimate. The twist formula is the classical mirror-character rule, expressed here for scalar characters and the explicit conjugation convention of `EqHom`. [Gras1998, §4, Lemma and Definition 4.3, p. 419](https://www.numdam.org/item/JTNB_1998__10_2_399_0.pdf).

For the finite-layer call take $F=K=L$, $\chi=\psi=1$ on $G_L$, and impose the separate $\widetilde J$-condition. Let $Q=C/(\ell C+D)$. Its $\mathbb F_\ell$-dual has size $|Q|$ and consists of class characters fixed by $J$. The Artin pullback inputs `pullEq` and `pullMem` identify their images with unramified scalar characters satisfying the $\widetilde J$-condition and give injectivity. The estimate above therefore gives $|Q|\le\ell |C^-\cap C[\ell]|$. One always has $D\subseteq C^-$ since $(1+J)(1-J)=0$. For $x\in C^-\cap C[\ell]$, set $y=((\ell+1)/2)x$. Then $(1-J)y=(\ell+1)x=x$. This identifies $D\cap C[\ell]=C^-\cap C[\ell]$ at the point where the supplied negative-image estimate is used.

The kernel of $C/\ell C\to Q$ is the image of $D/\ell D$ and has order at most $|D/\ell D|=|D[\ell]|$ by multiplication by $\ell$ on $D$. Hence
$$
[C:\ell C]\le |D[\ell]|\,|Q|\le\ell |D[\ell]|^2\le\ell M^2.
$$
Here the root-unit factor appears only in the fixed-character count $|Q|$. The other factor counts the image of $D$ in $C/\ell C$. In `cyc`, $M=B^N$ by the earlier bound at lines 88–89. Lines 91–97 take a primitive root of order $f\ell^n$ to its $f\ell^{n-1}$-st power to supply $\zeta$. Line 98 identifies the action of $-1$ with $J$. The calls to `reflOdd` and `pOdd` at lines 99 and 101 give the claimed $\ell(B^N)^2$ at line 102. $\square$

**Source map and reading boundary.** All Lean paths here refer to the joined archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. In the table, `GL/` expands to `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/`.

| Source and lines | Role and reading |
|---|---|
| `GL/KummerTheory/Mk0IdMapCongr.lean:56–82,90–113,126–157` | Class characters, valuation subgroup, $\mathrm{radCl}$, Galois dual and scalar conjugation conditions, twisted class group and radical predicate. |
| `GL/KummerTheory/RadXDual.lean:8–55` | [Lean, read] Existence with finite-prime divisibility and uniqueness by taking the fixed ratio. |
| `GL/KummerTheory/UnitMinus.lean:5–37` | [Lean, read] Integrality of the unit and its inverse, CM unit torsion identity and cancellation for odd exponent. |
| `GL/KummerTheory/ReflRoot.lean:5–89,91–133` | [Lean, read] Finite cyclic root group, a common evaluation element and injection into scalar invariants. |
| `GL/KummerTheory/Reflect.lean:29–42,44–90` | Kernel normalization and kernel–image consumer. |
| `GL/FerreroWashingtonIndex/ReflOdd.lean:30–113`, `GL/FerreroWashingtonIndex/POddRelIndexLe.lean:30–51`, `GL/FerreroWashingtonIndex/FerreroWashington.lean:83–102` | Specialization, subgroup index bound and consumption in the odd-prime finite layer. |

The three new R3 readings cover the displayed production bodies with their imported inputs. The proof uses `radExists` via `h90`, `toGalDict`, `exists_isPlaceOver`, `dvdOfIne` and the imported CM unit identity `IsCMField.unitsMulComplexConjInv` as named inputs [Lean]. The archive supplies the ideal-class map, twist and unit criterion in `reflMap`, `reflTw` and `radClKer`. The empty-set and odd-prime deductions above explain the parts needed here. Full proof credit for those imported declarations and for the Artin pullback `pullEq` and `pullMem` stays at [Lean]. The binary sign route retains `hMinus`, `realGen`, `sgnUnit`, `sgnStab`, `unrJ` and `unitSurj` as named inputs. The reading status of the full Ferrero–Washington dependency cone remains as in §11.4.3.

### 11.4.4 Top-level modularity-to-`VWin` wiring (`vwin_of_row`) and honest map of the 157,603-module cone

Finally, we read the three top-level P12 assembly files `VwinOfRow.lean`, `TopMainZj.lean`, and
`WindowBoundOfLiteratureLevel.lean` in full (`R3` / `[Lean, read]` for these three files; `R2` / `R1`
for their deep sub-trees):

**Theorem 11.4 (From CM automorphic Galois representations `Row0b` to `VWin`: `vwin_of_row`).**
*Assume `h : UpperTheory.GalStar.Row0b (fun h rc => UpperTheory.Zero.LLC.IsRecT h rc)` (node `P14` + `P15`,
Chapter 12). Then `UpperTheory.Top.VWin` holds.*
*(Lean: `UpperTheory.One.vwin_of_row`,
`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`;
`automorphic_window_of_inputs`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TopMainZj.lean:71`;
`v_window_of_literal_automorphy_n` and `vwin_of_hypotheses_H_E_alt`,
`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/WindowBoundOfLiteratureLevel.lean:25,33`.)* [Lean, read]

*Proof (top-level wiring in Lean, with reading-level boundaries marked explicitly).*

1. **Packaging `OpenImageCondition` and four literature bundles (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4–5`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TopMainZj.lean:18–74` `[Lean, read]`):**
   `vwin_of_row h` wraps `h` into the 1-field structure `O := OpenImageCondition.mk h`
   (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TemperedProductOfSquareIntegrable.lean:207`) and passes `O`, `baseChangeN` (`[Lean]`), and `h` into
   `automorphic_window_of_inputs`. Inside `TopMainZj.lean`, the archive constructs four hypothesis bundles
   feeding `LiteratureRankNHypothesis`:
   - `local_inputs_from_literature O` (`:18–37`): 18 local $\mathrm{GL}_n$ representation-theory fields
     (Bernstein–Zelevinsky, Moy–Prasad, Langlands multisegments, local converse, Green regular characters);
   - `automorphic_inputs_from_literature O bc gal` (`:38–54`): 15 global automorphic/Galois fields
     (cusp rapid decay, Jacquet–Shalika, base change `bc`, Gelfand–Kazhdan, `gal : RowT`, Clozel purity
     and cohomologicality, global Artin reciprocity, Berger's $p$-adic monodromy);
   - `galois_cohomology_from_literature O` (`:58`): Poitou–Tate and local Tate duality; and
   - `cm_abelian_inputs_from_literature O` (`:59–70`): 11 CM abelian-scheme and $p$-adic L-function
     inputs (Grothendieck–Messing, de Rham/crystalline comparison, Serre–Tate, Shimura's main theorem of
     CM, Siegel–Klingen–Deligne–Ribet, partial zeta and Hecke–Tate functional equations).
2. **Discharging `LemmaK`, Kato's Euler system, and residually reducible modularity (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/WindowBoundOfLiteratureLevel.lean:25–34` `[Lean, read]`):**
   `published_hypotheses_from_patching_alt` (`:31` `[Lean]`) upgrades `LiteratureRankNHypothesis` and
   solvable descent `descWeak` to `hH : HypothesesH'`. Then `vwin_of_hypotheses_H_E_alt` (`:25–29`) extracts:
   - `hK := lemmaK_litN_alt hH.litN` (`LemmaK`, `[Lean]` — proved in the $K$-theory stability subtree `[Open]`);
   - `katoTwoW_of_printsH hH` (`KatoUse` / Kato's $\mathrm{GL}_2$ Euler system `[Kato2004]`, `[Lean]` / `[Open]`);
   - `hE := ends0_alt hH` and `automorphyUnramified_of_litN_of_gdEnd hH.litN hE.1` (`[Lean]` — the
     residually Eisenstein $U(3)$ modularity theorem powered downstream by Hida families, adjoint $\mathrm{GL}_2$
     seeds, and Taylor–Wiles patching `PfromAut` `[TaylorWiles1995]`, `[Thorne2015]`, `[Community]` / `[Open]`),
     producing `CountI` (from `PropGK`) and `CountV`;
   - `sp4In0_alt hH` (`[Lean]` / `[Open]`), producing `CountII` and `CountIII` via $\mathrm{GSp}_4$ congruences;
   - and `of_four_alt` (`:29` `[Lean]`), which supplies `ThmBab` (from `FW.ferreroWashington` + `hK`),
     `ThmBcFree` (from the cyclotomic Euler system), and `CountZ`, and invokes Proposition 11.2
     (`vwin_of_counts`) to conclude `VWin`! $\square$

---

## 11.5 Remarks, formalization notes, and Masullo's counterpart

### 11.5.1 Import-cone anatomy and where human mathematical review is needed most

Our exact transitive import-cone audit separates the fully read (`R3`) algebraic/Iwasawa spine of node
**P12** from its deep unread proof cones (`[Open]`):

| File | Import cone | Reading level & tag | Mathematical content / audit status |
|---|---|---|---|
| `PublishedTheorems/FerreroWashington.lean` | **0** | `R3` (`[Lean, read]`) | Pure Mathlib statement of bounded $\ell$-rank in cyclotomic $\mathbb Z_\ell$-towers (including $\ell = 2$). |
| `LemmaK.lean` | **9** | `R3` (`[Lean, read]`) | Statement of Soulé-type $\log\lvert H^2(\mathbb Z_\ell(e+1)) \rvert$ torsion bound; proof cone in `KTheoryStability/` is `[Open]`. |
| `ExistsPageN.lean`, `LengthEqAddEigen.lean`, `PrimeSetBoundDataOfPrimitiveChar.lean`, `AdmissibleOfPageN.lean` | **19–38** | `R3` (`[Lean, read]`) | Master definitions `VVle`, `VWin`, parity split `vvle_of_parts`, CM/conductor proofs, and subexponential squeeze `vwin_of_joint`. |
| `FerreroWashingtonIndex/FerreroWashington.lean` | **809** | `R3` (`[Lean, read]` top proof; `R3` for the finite independence supply in §11.4.3.1) | Proves `FW.ferreroWashington` via Sinnott's independence lemma, Stickelberger annihilation, and Kummer reflection. |
| `JointWinOfCounts.lean` (with `ThmHV`, `FinalLe`, `SumOut`, `CountVs`) | **1,144** | `R3` (`[Lean, read]` top files; `R2` `[Lean]` character-orbit helpers) | Assembles `CountI`–`CountV`, `CountZ`, `LemmaK`, `ThmBab`, and `ThmBcFree` into `VWin`. |
| `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/TaylorWilesObstructionBound.lean`, `KatoUse.lean` | **1,711–1,713** | `R3` (`[Lean, read]` statements; proof cones `[Open]`) | Interfaces `PfromAut` (Taylor–Wiles patching on universal ordinary determinant rings) and `KatoUse` / `PropGK` ($U(3)$ trace annihilator). |
| `WindowBoundOfLiteratureLevel.lean` $\to$ `TopMainZj.lean` $\to$ `VwinOfRow.lean` | **55,066 $\to$ 157,603** | `R3` (`[Lean, read]` top wiring; deep proof cones `[Open]`) | Wires `Row0b`, `OpenImageCondition`, `LemmaK`, Kato, and residually reducible $U(3)/\mathrm{GSp}_4$ modularity into `VWin`. |

Three community observations (`[Community]`) help orient specialists reading into the 157,603-module cone:

1. **Where the genuine mathematical novelty of P12 sits (`PropGK` and `PfromAut`):** As reported in
   LUMI's `docs/06-window-bound.md` [Community], `FerreroWashington`, the minus-part Euler-system bound,
   `LemmaK`, and Kato's Euler system all follow recognizable classical blueprints (`[FerreroWashington1979]`,
   `[Sinnott1984]`, `[MazurWiles1984]`, `[Soule1979]`, `[Kato2004]`). By contrast, `PropGK` (bounding
   Vandiver-parity `ShaPlus` lengths by an explicit $U(3)$ Frobenius-trace integer `NN`) and the
   residually reducible ordinary modularity-lifting step `PfromAut` (stated for general dimension $n$
   and residual pseudo-representations over CM fields, cf. `[Thorne2015]`) sit at or beyond the published
   literature frontier; human expert verification of `PatchingModules/` and `UnitaryThreeGroups/` is
   therefore one of the highest-value open digestion tasks (`[Open]`, Chapter 16).
2. **Why `KatoTwoW` needs no non-vanishing $L$-value hypothesis (`Zulip #642442900`):** On Lean Zulip,
   Ishaan Dixit (`#642435200`) asked how the archive's `KatoTwoW` could deduce Bloch–Kato Selmer vanishing
   without assuming $L(f \otimes \varphi, \cdot) \neq 0$; David Loeffler (`#642442900`) pointed out that
   in `KatoUse` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:15–17`), twisting a weight-$(2e + 1)$ newform ($e \ge 1$) by $\chi_{\mathrm{cyc}}^{-e}$
   evaluates Kato's Euler system at $s = 2e + 1 - e = e + 1$ in classical normalization (analytic
   $s = 1$, strictly to the right of the critical center $s = 1/2$ and at the edge of Euler-product
   non-vanishing!), where $L$-values of $\mathrm{GL}_2$ cusp forms never vanish `[Kato2004]` [Community]
   (see **Chapter 18**, Lemma 18.2(1), for the line-by-line `R3` verification of `Published.Kato` and `2 * r ≠ k` `[Lean, read]`)!
3. **What happened to Behrend's set (`remark.pdf` p. 4, item 19 vs. `P12` and `HostOfField`):** In `remark.pdf`
   (p. 4, item 19 and fn. 7), Alpöge listed an October step tuning the choice of the Iwasawa tower via
   Behrend sets while noting *"This is the sort of trick that intuitively to me is
   obviously going to be unnecessary"* [Paper; remark p. 4]. Indeed, on the **P12 `VWin`** branch (`LUMI doc 06`
   [Community]), the Iwasawa root-avoidance window uses the elementary pigeonhole count `BConst.J`
   (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:20`), while the 14-file folder `src/Formalism/BehrendSets/`
   is an evolutionary remnant whose misfiled export `Formalism.BehrendSets.FinalE.trivStab`
   (`src/Formalism/BehrendSets/FinalE.lean:12`, Minkowski cyclotomic matrix torsion-freeness) is still
   imported inside `VwinOfRow`'s cone — **whereas Mathlib's genuine Behrend sphere lemma
   `Behrend.exists_large_sphere` (`Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:245`) IS
   load-bearing on the `src/Main.lean` spine** inside host-field thick-frame assembly
   (`src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean:181` $\to$
   `src/Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean:29` $\to$
   `src/Development/AutomorphicArithmetic/CharacterBoxes/HostOfField.lean:8`), which we prove in full
   in **Chapter 17** [Lean, read]!

### 11.5.2 Masullo's counterpart

Masullo's draft *The Music of the Primes* has **no counterpart** to `VWin`, Iwasawa $\mathbb Z_\ell$-towers,
Ferrero–Washington, generalized Bernoulli numbers, Kato's or Kolyvagin–Rubin's Euler systems, $U(3)$
deformation rings, or Taylor–Wiles patching [Expository]. The only conceptual point of contact is
indirect: Alpöge motivated his Iwasawa $\mathbb Z_2$-tower (`remark.pdf` p. 4, item 11 [Paper; remark p. 4])
as a characteristic-zero analogue of passing to constant-field extensions $\mathbb F_{q^n} / \mathbb F_q$
in Stepanov's curve proof (Chapter 6, Step 2–3 of Theorem 6.3), whereas Masullo works directly on the
fixed number field's idele class group $C_F = \mathrm{GL}_1(\mathbb A_F)/F^\times$ without auxiliary
field towers (and explains in §14.2, pp. 534–536, why his Hardy–Sobolev trace formula fails over
$\mathbb F_q(X)$ [Paper; Masullo pp. 534–536]).

---

## 11.6 Lean counterpart for this chapter

| Declaration | File:line | Mathematical content / role in Sections 11.3–11.4 | Tag |
|---|---|---|---|
| `VVle`, `IsChiField`, `WinPair`, `PageN`, `VAt`, `VWinAt`, `VWin`, `VVle.mono`, `exists_pageN` | `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12,19,27,39,41,44,49,51,67`; `src/Development/AutomorphicArithmetic/CharacterBoxes/IsChiField.lean:5` | Definition 11.1: master $\log\ell$-weighted $Ш^1$ predicates, CM host characterization `IsChiField`, scale pages `PageN`, and `VWin` (import cones 19 and 22). | [Lean, read] |
| `AbF`, `IsCompField`, `condF`, `ordC`, `pK`, `hStar`, `pOne`, `Bchi`, `minusBound`, `isCompField_ofChar` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean:11,36,44,57,59,61,63,66,69,91` | Definition 11.1(4): cyclotomic conductor `condF`, finite bad-prime set `Bchi ψ`, and explicit Euler-system polynomial bound `minusBound` (cone 20). | [Lean, read] |
| `length_eq_add_eigen`, `ShaPlus`, `ShaMinus`, `shaLen_eq_add`, `BoundedHeightTwoPlaceCondition`, `VVminusLe`, `VVplusLe`, `vvle_of_parts` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:10,68,71,88,111,113,120,127` | Definition 11.2 & Proposition 11.1: exact involution module-length split when $2 \in R^\times$ and three-way decomposition $B_2 \log 2 + B_m + B_p$ (cone 21). | [Lean, read] |
| `BConst`, `BConst.J`, `ThmBab`, `ThmBcFree`, `ThmHV`, `JointWin`, `thmBc_iff`, `jointWin_of` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean:12,20,49,64,79,88,112,145` | Definition 11.2(3) & Proposition 11.2: pigeonhole count $J = 2^{R+2}(2 C_K C_t / \varepsilon)^R$ and window assembly propositions (cone 23). | [Lean, read] |
| `isCMField_of_isChiField`; `conductor_bounds_of_isChiField`; `minusBound_le_exp_of_log_le`; `error_terms_le_sqrt_exp_rpow`; `admissible_of_pageN`, `vwinAt_of_joint`, `vwin_of_joint` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/IsCMFieldOfIsChiField.lean:7`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ConductorBoundsOfIsChiField.lean:77`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/minusle.lean:6`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ErrorTermsLeSqrtExpRpow.lean:6`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean:24,41,131` | Proposition 11.2(1,3): proves $\sqrt{-q} \in E \implies \mathrm{IsCMField}\,E$, $\operatorname{cond}(E) \le 2^{e+2}\psi.N q d$, and squeezes $B_2\log 2 + B_m + B_p \le \sqrt{\exp(x^\varepsilon)}$ (cones 21–38). | [Lean, read] |
| `countVs`; `sumIn`; `sumOut`; `point`; `thmHV`; `pointHV_of_counts`, `thmHV_of_counts`, `jointWin_of_counts`, `vwin_of_counts` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/CountVs.lean:86`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/FinalLe.lean:86`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/SumOut.lean:50`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/PointArith.lean:36`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/ThmHV.lean:6`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/JointWinOfCounts.lean:16,20,25,30` | Proposition 11.2(2–3): combines `LemmaK`, `CountI`–`CountV`, `CountZ`, `ThmBab`, and `ThmBcFree` into `VWin` (cone 1,144). | [Lean, read] |
| `UpperTheory.V.Published.FerreroWashington`; `UpperTheory.V.FW.cyc`, `ferreroWashington`; `exists_iwasawaRank_bound_of_ferreroWashington` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:7`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:18,104`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/WeakShimuraTheory/RealPlaceConjugation/ExistsIwasawaRankBoundOfFerreroWashington.lean:23` | Definition 11.3(1) & Proposition 11.3: Sinnott-route proof of $\mu = 0$ bounded $\ell$-rank for all primes $\ell$ (including $\ell = 2$) and Iwasawa cotorsion rank stabilization (cones 0, 809, 2,033). | [Lean, read] |
| `core`, `card_range_inf_torsion_le_index_pow`, `nilCard`, `cardTors`, `stickH`, `thetaFull`, `ambCyc`, `amb`, `ambHom`, `homCyc`, `pOdd`, `reflOdd`, `pTwo`, `sgnAlg`, `sgnCyc` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/CardRangeInfTorsionLeIndexPow.lean:7,64`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/NilCard.lean:26`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/CardTors.lean:22`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/StickH.lean:8`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/ThetaFull.lean:43`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/AmbCyc.lean:9`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/AmbIndex.lean:11`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/AmbHom.lean:59`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/HomCyc.lean:58`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/POddRelIndexLe.lean:30`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/ReflOdd.lean:30`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/PTwo.lean:5`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/SgnAlg.lean:64`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/SgnCyc.lean:13` | §11.4.3.2: the membership of `memZ`, Stickelberger annihilation and the ambiguous quotient bound give $\lvert(1-J)\mathrm{Cl}\cap\mathrm{Cl}[\ell]\rvert\le B^N$ on every layer $n\ge n_0$; reflection ($\ell$ odd) or the unit-sign defect ($\ell=2$) gives the rank bound consumed by `cyc`. | [Lean, read] |
| `HasMuQ`, `kBound`, `UpperTheory.V.LemmaK` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GeneratorCountTuples/LemmaK.lean:9,11,13` | Definition 11.3(2): Soulé-type bound $\log\lvert H^2(\mathbb Z_\ell(e+1)) \rvert \le \exp((2e[L:\mathbb Q])^{C_K}\log(2\lvert d_L \rvert))$ (statement `R3`, cone 9; proof in `KTheoryStability/` `[Open]`). | [Lean, read] |
| `KatoUse`, `CohInp`, `Inp`, `PropGK`, `CorGK`, `OneChar` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:13,19,26,36,44,54` | Definition 11.3(3): Kato $\mathrm{GL}_2$ Selmer vanishing and the $U(3)$ Frobenius-trace integer annihilator `NN` bounding generic `ShaPlus` across all $\ell \neq p$ (statement `R3`, cone 1,713; proof cone `[Open]`). | [Lean, read] |
| `TWPl`, `LocCFT`, `ArPl`, `FirstOrderDualArithmeticBound`, `TaylorWilesObstructionBound`, `HasAut`, `PfromAut` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/TaylorWilesObstructionBound.lean:88,115,119,126,136,147,150` | Definition 11.3(4): Taylor–Wiles prime systems and patching theorem `PfromAut` on universal ordinary determinant rings (statement `R3`, cone 1,711; 50k-line `PatchingModules/` proof cone `[Open]`). | [Lean, read] |
| `vwin_of_hypotheses_H_E_alt`, `v_window_of_literal_automorphy_n`; `local_inputs_from_literature`, `automorphic_inputs_from_literature`, `cm_abelian_inputs_from_literature`, `automorphic_window_of_inputs`; `UpperTheory.One.vwin_of_row` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/WindowBoundOfLiteratureLevel.lean:25,33`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/TopMainZj.lean:18,38,59,71`; `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4` | Theorem 11.4: top-level deduction of `VWin` from `Row0b` and `OpenImageCondition` (top files `R3`; 157,603-module internal proof cone `[Lean]` / `[Open]`). | [Lean, read] |

**Summary of the chapter (and of Part II).** For every cyclotomic CM host field $E$ cut out by
`IsChiField ψ (e x) q d E` ($q \equiv 3 \pmod 8$, $d \equiv 7 \pmod{16}$), `LengthEqAddEigen.lean`
(Proposition 11.1) decomposes the $\log \ell$-weighted Tate–Shafarevich sum across $1 \le e < \lfloor x^{401} \rfloor$
into $\ell = 2$, odd-$\ell$ `ShaMinus`, and odd-$\ell$ `ShaPlus` [Lean, read]. The archive bounds
$\ell = 2$ and finitely many bad primes by $\exp(x^{4\varepsilon/5})$ on a pigeonholed window $[Y, Y^2]$
using its Sinnott-route proof of Ferrero–Washington (`FW.ferreroWashington`, Proposition 11.3)
`[FerreroWashington1979]`, `[Sinnott1984]` and Soulé-type $K$-theory bounds (`LemmaK` `[Soule1979]`),
bounds `ShaMinus` polynomially via cyclotomic Euler systems (`ThmBcFree` `[MazurWiles1984]`, `[Rubin2000]`),
and bounds `ShaPlus` via a nonzero integer annihilator `NN` built from $U(3)$ / $\mathrm{GSp}_4$ Frobenius
trace congruences (`PropGK`), Kato's Euler system (`KatoUse` `[Kato2004]`), and Taylor–Wiles patching
(`PfromAut` `[TaylorWiles1995]`, `[Thorne2015]`). Because $\frac{\varepsilon}{4} < \frac{4\varepsilon}{5} < \varepsilon$,
`error_terms_le_sqrt_exp_rpow` and `vwin_of_counts` (Proposition 11.2) squeeze the combined bound below
$\sqrt{\exp(x^\varepsilon)} = \exp(x^\varepsilon / 2)$, discharging `HypV` in Chapter 10 and **completing
Part II**! Only the three foundational packages passed into `MainConclusion.lean` — automorphic Galois
representations `Row0b` and partial local Langlands `RecTExists` (Chapter 12), together with Green's
theorem and the literature layer `OpenLiteratureStatements` (Chapter 13) — remain to be opened in **Part III**.
