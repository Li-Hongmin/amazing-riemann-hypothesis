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

(iii) [Lean, read; the inputs are read in §11.4.3.4] For $L=\mathbb Q(\zeta_{f2^n})$ with $f>1$ odd and $n\ge2$, and the membership of `memZ`, $[\mathrm{Cl}(L)^-:(1-J)\mathrm{Cl}(L)]\le2^{\varphi(4f)N}$ (`sgnCyc`).

**Proof.** (i) Let $T=C[2]$, $D=(1-J)C$ and $K=C^-$; then $D\subseteq K$, and $[C:2C]=\lvert T\rvert$ by Lemma 1. The map $t\mapsto t-Jt$ sends $T$ into $D\cap T$. Its kernel consists of the $t\in T$ with $Jt=t$, and these lie in $K\cap T$ because $Jt+t=2t=0$. The map $K\cap T\to K/D$ has kernel $D\cap T$. Hence $\lvert T\rvert\le\lvert K\cap T\rvert\cdot\lvert D\cap T\rvert\le[K:D]\cdot\lvert D\cap T\rvert^2$, which is at most the square of $[K:D]\cdot\lvert D\cap T\rvert$.

(ii) This is a group-ring module length estimate. Define $\kappa\colon\mathbb Z[G]\to\mathrm{Map}(G,\mathbb F_2)$ by letting $\kappa(x)(g)$ be the coefficient of $[g]$ in $x(1+[J])$ modulo $2$, that is, $x_g+x_{Jg}$. Because $J\neq1$ the orbits $\{g,Jg\}$ have two elements, and prescribing $x$ on one element of each orbit shows that $\kappa$ maps onto $\mathcal E_J$. Since $\kappa([g]x)$ is a translate of $\kappa(x)$, the preimage $I=\kappa^{-1}(S)$ is an ideal. It contains $\theta$ by hypothesis. It contains $1+[J]$ and $2$, since $(1+[J])^2=2(1+[J])$ and $\kappa$ of an even element vanishes. Hence $([\gamma]-1)^N\in I$. Now $\kappa$ induces $\mathbb Z[G]/I\cong\mathcal E_J/(S\cap\mathcal E_J)$, a group killed by $2$. Multiplication by $t=[\gamma]-1$ is an endomorphism of $V=\mathbb Z[G]/I$ with $t^N=0$, so Lemma 2 gives $\lvert V\rvert\le\lvert V/tV\rvert^N$. In $V/tV$ the images of $[\gamma g]$ and $[g]$ agree. So $V/tV$ is generated by $[G:\langle\gamma\rangle]$ elements of order at most $2$, and $\lvert V/tV\rvert\le2^{[G:\langle\gamma\rangle]}$.

(iii) `sgnCyc` applies (ii) with $S$ the span of the sign vectors $t\mapsto\operatorname{sgn}\varphi(\sigma_t u)$ of real units $u$ of $L$ under one complex embedding $\varphi$. The hypothesis on $\theta$ comes from `sgnUnit`, `sgnStab` and Lemma 5(i). It combines this with `hMinus`, which gives $[\mathrm{Cl}(L)^-:(1-J)\mathrm{Cl}(L)]\le[\mathcal E_J:S\cap\mathcal E_J]$ when $L/L^+$ is unramified at all finite places (`unrJ`, which needs $f>1$ odd and $n\ge2$) and $u\mapsto u/\bar u$ maps the units onto the roots of unity (`unitSurj`). The index $[G:\langle\gamma\rangle]=\varphi(4f)$ is part of the output of `memZ`. The proof of `hMinus` sends a minus class $[\mathfrak a]$ to the sign vector of a real generator of $\mathfrak a\cdot J(\mathfrak a)$, modulo the signs of real units, and shows that this map is injective on $\mathrm{Cl}(L)^-/(1-J)\mathrm{Cl}(L)$ (the map is defined at `HMinus.lean:138–146`). The injectivity proof, `realGen`, and the bodies of `sgnUnit`, `sgnStab`, `unrJ` and `unitSurj` are read in §11.4.3.4 (Theorem E and Lemmas D, F and G). $\square$

**Theorem 9 (uniform rank bound on the cyclotomic layers; `cyc`).** Let $\ell$ be prime, $f>1$ prime to $\ell$, $c=2f\ell+1$, and $L_n=\mathbb Q(\zeta_{f\ell^n})$ with $C_n=\mathrm{Cl}(L_n)$. Assume the named inputs: the membership `memZ` (§11.4.3.1), Stickelberger's theorem `Stick.coef`, the inputs of Proposition 6, the reflection inputs of Lemma 7 when $\ell$ is odd, and the sign inputs of Lemma 8(iii) when $\ell=2$ (read in §11.4.3.4 down to the class-field and inertia inputs named there). Then there are $N$, $n_0\ge2$ and $B$, depending only on $\ell$ and $f$, such that for every $n\ge n_0$:
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

**Reading boundary.** Read in full for this subsection [Lean, read]: `cyc` (`FerreroWashington.lean:18–102`), `core` and `card_range_inf_torsion_le_index_pow`, `nilCard`, `cardTors`, `stickH` and `thetaFull`, `ambCyc`, `amb`, `ambHom` and `homCyc`, `pOdd`, `reflOdd` and the counting body of `reflect`, `pTwo`, `sgnAlg`, `sgnCyc` as an assembly, `conjEq` and the definitions in `CycRepApply.lean` and `TwSingle.lean`. Named inputs not read here [Lean]: `memZ` (read in §11.4.3.1), `Stick.coef` (with `carryAll`, `degOne`, `carryPrime`, `combFloor`, `comb`), `relCyc`, `gamGen`, `ineCyc`, `finChar`, `pullEq`, `pullMem`, `reflMap`, `reflTw`, `radClKer`, `hMinus` beyond the definition of its sign map, `realGen`, `sgnUnit`, `sgnStab`, `unrJ` and `unitSurj`. No Iwasawa control theorem or structure theorem for $\mathbb Z_\ell[[T]]$-modules is used. Section 11.4.3.3 reads the three direct Kummer producers `radXDual`, `unitMinus` and `reflRoot`. Section 11.4.3.4 reads the binary sign suppliers `hMinus`, `realGen`, `sgnUnit`, `sgnStab`, `unrJ` and `unitSurj`.

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
| `GL/FerreroWashingtonIndex/HMinus.lean:135–163` | `hMinus` (§11.4.3.4) | [Lean, read] |
| `GL/FerreroWashingtonIndex/SgnUnit.lean:54–111` | `sgnUnit` (§11.4.3.4) | [Lean, read] |
| `GL/FerreroWashingtonIndex/SgnStab.lean:12–51` | `sgnStab` (§11.4.3.4) | [Lean, read] |
| `GL/FerreroWashingtonIndex/UnrJPrime.lean:45–62` | `unrJ` (§11.4.3.4) | [Lean, read] |
| `GL/FerreroWashingtonIndex/UnitSurj.lean:77–95` | `unitSurj` (§11.4.3.4) | [Lean, read] |
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

The three new R3 readings cover the displayed production bodies with their imported inputs. The proof uses `radExists` via `h90`, `toGalDict`, `exists_isPlaceOver`, `dvdOfIne` and the imported CM unit identity `IsCMField.unitsMulComplexConjInv` as named inputs [Lean]. The archive supplies the ideal-class map, twist and unit criterion in `reflMap`, `reflTw` and `radClKer`. The empty-set and odd-prime deductions above explain the parts needed here. Full proof credit for those imported declarations and for the Artin pullback `pullEq` and `pullMem` stays at [Lean]. Section 11.4.3.4 reads the binary sign route `hMinus`, `realGen`, `sgnUnit`, `sgnStab`, `unrJ` and `unitSurj`. The reading status of the full Ferrero–Washington dependency cone remains as in §11.4.3.

#### 11.4.3.4 Signs of real generators and the binary minus defect

**Motivation.** For $\ell=2$ the class-group argument of §11.4.3.2 controls only the image $(1-J)C$ of $1-J$ on $C=\mathrm{Cl}(L)$. Lemma 8(i) also needs the defect $[C^-:(1-J)C]$, where $C^-=\ker(1+J)$. For odd $\ell$ the defect vanishes on $\ell$-primary parts, because $(1-J)/2$ is a projection onto the minus part. The step $(1-J)((k+1)x)=x$ in Lemma 7 is that projection. When $2$ is not invertible there is no such projection, and $C^-/(1-J)C$ is the Tate group $\widehat H^{-1}(\langle J\rangle,C)$, an $\mathbb F_2$-vector space that can carry the whole $2$-rank (Example 2 of §11.4.3.2). The archive measures this defect arithmetically. A minus class is represented by an ideal $\mathfrak a$ with $\mathfrak aJ(\mathfrak a)$ principal. If every root of unity is a quotient $u/J(u)$ of units, this principal ideal has a real generator $\alpha$. The signs of $\alpha$ at the real places of the maximal real subfield, taken modulo the signs of real units, determine the class modulo $(1-J)C$. The kernel statement rests on the Hasse norm theorem: when no finite prime ramifies in the CM extension, a totally positive real generator is a local norm everywhere. This subsection reads `hMinus` and its direct producers `realGen` and `hasse`, the local lemmas behind `hasse`, the real-unit sign supplies `sgnStab` and `sgnUnit`, and the cyclotomic inputs `unitSurj` and `unrJ`. It returns them to `sgnCyc` and to the $\ell=2$ branch of `cyc`. Source references are to the joined archive with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. [Lean, read]

**Example 1 (the Gaussian field: a defect in the units).** [Expository] Let $K=\mathbb Q(i)$, so $K^+=\mathbb Q$ and $J$ is complex conjugation. The Minkowski bound $(4/\pi)\cdot(2/4)\cdot\sqrt4=4/\pi<2$ gives $\mathrm{Cl}(K)=0$. The unit rank is $0$, so the units are the roots of unity $W=\mu_4=\{\pm1,\pm i\}$, and the real units are $\{\pm1\}$. The quotient map $u\mapsto u/J(u)$ sends $\pm1\mapsto1$ and $\pm i\mapsto-1$. Its image is $\mu_2=W^2\neq W$. As a $\langle J\rangle$-module the unit group is $\mathbb Z/4$ with $J=-1$, because $J(i)=i^{-1}$. This is the module of Example 1 of §11.4.3.2 read at $\ell=2$. The image of $1-J$ is $\mu_2$, while $\ker(1+J)=\{u:uJ(u)=1\}$ is all of $\mu_4$, so the unit defect $\mu_4/\mu_2$ has order $2$. The norms of units are $uJ(u)=1$, so the norm image of the units is $\{1\}$. The totally positive units of $\mathbb Q$ are $\{1\}$, and $-1=x^2+y^2$ has no rational solution, so $-1$ is not even the norm of an element.

Both hypotheses of the theorem below fail here. From $2=-i(1+i)^2$ and $1-i=-i(1+i)$, the prime $\mathfrak P=(1+i)$ satisfies $J(\mathfrak P)=\mathfrak P$ and $\mathfrak P^2=(2)$, so $\mathfrak P$ is ramified over $\mathbb Q$. The unit hypothesis fails as computed above. Its effect is visible on $\mathfrak P$ itself. The generators of this $J$-stable principal ideal are $\pm(1+i)$ and $\pm(1-i)$, and none of them is real. The obstruction is the ratio $(1+i)/J(1+i)=i$, a root of unity outside the image $\mu_2$ of $u\mapsto u/J(u)$. For the ideals to which Lemma D below is applied nothing goes wrong. Every ideal is $\mathfrak a=(\beta)$, and $\mathfrak aJ(\mathfrak a)=(\beta J(\beta))$ has the totally positive generator $\lvert\beta\rvert^2$. In the archive normalization $M=4$, $G=(\mathbb Z/4\mathbb Z)^\times=\{1,3\}$ and $J=3$. Fix $\varphi$ with $\varphi(i)=i$. The family $e=(\varphi,\varphi\circ\sigma_3)$ consists of $\varphi$ and its conjugate. The $J$-invariant sign vectors are the two constant vectors, and $\operatorname{sgn}(-1)=(1,1)$ already gives both, so the sign quotient is trivial. The inequality of Theorem E would read $1\le1$. It holds because $C=0$, while its hypotheses fail. The archive applies the sign route only when $f>1$, and $K=\mathbb Q(\zeta_4)$ is the excluded case $f=1$. For comparison, the ambiguous class number formula for $K/\mathbb Q$ has $t=2$ ramified places (the prime $2$ and the real place), $h(\mathbb Q)=1$ and unit norm index $(\{\pm1\}:\{1\})=2$, giving $1\cdot2^{1}/2=1$ ambiguous class [Paper] [Lemmermeyer2013, Theorem 1].

**Example 2 ($\mathbb Q(\zeta_{12})$: a quartic layer with a totally positive fundamental unit).** [Expository] Let $\zeta=\zeta_{12}$, fix $\varphi(\zeta)=e^{\pi i/6}$, and let $K=\mathbb Q(\zeta)$. This is the layer $f=3$, $n=2$ of the family in `cyc`. Here $\zeta^3=i$ and $\zeta+\zeta^{-1}=2\cos(\pi/6)=\sqrt3$, so $K=\mathbb Q(i,\sqrt3)$ and $K^+=\mathbb Q(\sqrt3)$. The discriminant is $12^4/(2^4\cdot3^2)=144$. The Minkowski bound $(4/\pi)^2(4!/4^4)\sqrt{144}=18/\pi^2<2$ gives $\mathrm{Cl}(K)=0$. Similarly $(2/4)\sqrt{12}=\sqrt3<2$ gives $\mathrm{Cl}(K^+)=0$. The roots of unity are $W=\mu_{12}=\langle\zeta\rangle$, with $W^2=\mu_6$.

*Units.* Since $\Phi_{12}(X)=X^4-X^2+1$ and $\Phi_{12}(1)=1$, the element $1-\zeta$ has norm $1$ to $\mathbb Q$ and is a unit. Its conjugation quotient is
$$
\frac{1-\zeta}{J(1-\zeta)}=\frac{1-\zeta}{1-\zeta^{-1}}=-\zeta=\zeta^7,
$$
a generator of $W$. So every root of unity is a quotient $u/J(u)$ of units, and Hasse's unit index is $2$. The relative norm is $(1-\zeta)(1-\zeta^{-1})=2-\sqrt3$. In $\mathbb Z[\sqrt3]$ the equation $x^2-3y^2=-1$ has no solution modulo $3$, and $y=1$ gives the fundamental unit $2+\sqrt3$. So $E^+=\{\pm(2+\sqrt3)^k\}$, and all real units have norm $+1$. Squaring $u=-\zeta J(u)$ for $u=1-\zeta$ gives $(1-\zeta)^2=-\zeta(2-\sqrt3)$. Since $1-\zeta$ is not in $WE^+$ (its quotient $-\zeta$ is not in $\mu_6$), the unit group is $W\times\langle1-\zeta\rangle$. Both $2+\sqrt3$ and $2-\sqrt3$ are positive, so the totally positive real units are $\langle2+\sqrt3\rangle$, a subgroup of index $2$ with $-1$ representing the other coset. The norm image of the units is $\langle N(1-\zeta)\rangle=\langle2-\sqrt3\rangle$, which is the same group, because $N(\zeta)=1$. Every norm from the totally complex $K$ is totally positive. Therefore the real units that are norms of elements are again exactly $\langle2+\sqrt3\rangle$. In the language of Tate groups of units, $W/(1-J)E=0$ and $E^+/N(E)=\{\pm1\}$.

*Ramification.* The relative discriminant of $K/K^+$ has norm $144/12^2=1$, so no finite prime ramifies. In the archive's argument (Lemma G(ii) below), $J=\sigma_{11}$. For $p=2$ the prime-to-$p$ part of $12$ is $3$ and $11\not\equiv1\bmod 3$. For $p=3$ it is $4$ and $11\not\equiv1\bmod4$. The prime above $2$ illustrates the unit hypothesis. One has $(1+\sqrt3)^2=2(2+\sqrt3)$ and $(1+i)^2=2i$, so $\mathfrak P=(1+i)=(1+\sqrt3)$ is the unique prime above $2$ and $J(\mathfrak P)=\mathfrak P$. Unlike Example 1, this $J$-stable ideal has the real generator $1+\sqrt3$. The unit $(1+i)/(1+\sqrt3)$ has conjugation quotient $i=\zeta^3=(-\zeta)^9$. Further, $\mathfrak PJ(\mathfrak P)=(2)$ has the totally positive generator $2=N_{K/K^+}(1+i)$. This is the situation of Proposition C, with $\beta=1+i$.

*Signs.* Index the embeddings by $t\in G=\{1,5,7,11\}$ through $e_t=\varphi\circ\sigma_t$. Since $\sigma_5(\sqrt3)=2\cos(5\pi/6)=-\sqrt3$ and $\sigma_7(\sqrt3)=-\sqrt3$, one finds in the order $(1,5,7,11)$
$$
\operatorname{sgn}(-1)=(1,1,1,1),\qquad \operatorname{sgn}(2+\sqrt3)=(0,0,0,0),\qquad \operatorname{sgn}(\sqrt3)=(0,1,1,0).
$$
The $J$-invariant vectors form $V=\{h:h(1)=h(11),\ h(5)=h(7)\}\cong\mathbb F_2^2$, and the real units give $S=\{0,(1,1,1,1)\}$. Hence $V/S$ has order $2$, generated by the class of $\operatorname{sgn}(\sqrt3)$. Theorem E gives $[C^-:(1-J)C]\le2$, and the true value is $1$. The nontrivial sign class is not in the image of the sign map. If $\mathfrak aJ(\mathfrak a)=(\alpha)$ with $\alpha$ real, then $\mathfrak a=(\beta)$ and $\alpha=\varepsilon\beta J(\beta)$ for a real unit $\varepsilon$, so $\operatorname{sgn}(\alpha)=\operatorname{sgn}(\varepsilon)\in S$. In ideal terms, $(\sqrt3)$ has residue field $\mathbb F_3$, over which $X^2+1$ is irreducible, so $(\sqrt3)$ is inert in $K=K^+(i)$. A relative norm ideal $N_{K/K^+}(\mathfrak a)$ therefore has even valuation at $(\sqrt3)$, and $(\sqrt3)$ is not one. The same holds for $(1+\sqrt3)$, whose generator also has the sign class $(0,1,1,0)$. The ambiguous class number formula for $K/K^+$ has $t=2$, $h(K^+)=1$ and unit norm index $2$, giving one ambiguous class, as it must.

*The sign supply.* With $c=5$ and $k=2$, the unit of Lemma F(ii) is $u_5=\zeta^{-2}(1+\zeta+\zeta^2+\zeta^3+\zeta^4)$, with $e_t(u_5)=\sin(5\pi a/12)/\sin(\pi a/12)$ for $a=1,5,7,11$. These values are $2+\sqrt3$, $2-\sqrt3$, $2-\sqrt3$, $2+\sqrt3$. So $u_5=2+\sqrt3$, and the floors $\lfloor5a/12\rfloor=0,2,2,4$ are even, as Lemma F(ii) predicts. The constant of `cyc` is $c=2\cdot(3\cdot2)+1=13\equiv1\bmod12$. Then $u_{13}=\zeta^{-6}(\zeta^{13}-1)/(\zeta-1)=\zeta^{-6}=-1$, and $\lfloor13a/12\rfloor=a$ is odd, giving the vector $(1,1,1,1)$. The coefficients $g_{13}(t)=t-6$ of Lemma 5 equal $-5,-1,1,5$, all odd, in agreement with Corollary H. At this layer $\gamma=1+3\cdot4\equiv1$, so $[G:\langle\gamma\rangle]=4=\varphi(12)$, and the group-ring bound of Lemma 8(ii) is far weaker than the direct value $[V:S]=2$.

**Definitions.** Let $K$ be a CM field with maximal totally real subfield $K^+$ and complex conjugation $J$ (`cE`, `LengthEqAddEigen.lean:64`). Write $W$ for the roots of unity of $K$, $E=\mathcal O_K^\times$, and $E^+=E\cap K^+$ for the real units. Every complex embedding satisfies $\varphi\circ J=\overline\varphi$, so $\varphi(a)$ is a nonzero real number for $a\in K^{+\times}$. For a finite family $e=(e_i)_{i\in\iota}$ of embeddings and $a\in K^{+\times}$, the sign vector $\operatorname{sgn}_e(a)\in\mathbb F_2^\iota$ has $i$-th entry $1$ if $e_i(a)<0$ and $0$ otherwise (`sgn`, `CycRepApply.lean:34`). Let $S_e$ be the subgroup generated by the sign vectors of real units (`sgnE`, `:36–37`). Write $C=\mathrm{Cl}(K)$ additively, $C^-=\ker(1+J)$ and $(1-J)C$ as in §11.4.3.2 (`minK`, `difR`, `TwSingle.lean:62–64`). A class $x=[\mathfrak a]$ lies in $C^-$ exactly when $\mathfrak aJ(\mathfrak a)$ is principal. The hypotheses are:

- (U) every prime of $\mathcal O_K$ has ramification index $1$ over $K^+$ (`UnrFin`, `CycRepApply.lean:41–42`);
- (Q) every $\xi\in W$ equals $u/J(u)$ for some $u\in E$, that is, Mathlib's `IsCMField.unitsMulComplexConjInv` is surjective.

By Mathlib's `indexRealUnits_mul_eq` (`Mathlib/NumberTheory/NumberField/CMField.lean:362–368` at `0df444a`), (Q) is equivalent to Hasse's unit index $Q_K=[E:WE^+]$ being $2$. For the cyclotomic application let $M=f2^n$, $L=\mathbb Q(\zeta_M)$, $G=(\mathbb Z/M\mathbb Z)^\times$ and $\sigma_t(\zeta)=\zeta^t$. The family is $e_t=\varphi\circ\sigma_t$ (`embT`, `CycRepApply.lean:26`), and $\mathcal E_J$ is the group of $J$-invariant functions $G\to\mathbb F_2$ (`evenF (-1)`, `TwSingle.lean:68–72`), as in Lemma 8(ii).

**Lemma A (ideal-theoretic Hilbert 90).** [Lean, read] Let $\tau$ be an automorphism of a number field $K$ with $\tau^2=1$. If nonzero integral ideals $\mathfrak A,\mathfrak B$ satisfy $\mathfrak A\tau(\mathfrak A)=\mathfrak B\tau(\mathfrak B)$, then $[\mathfrak A]-[\mathfrak B]\in(1-\tau)\mathrm{Cl}(K)$.

**Proof.** Put $H=(1-\tau)\mathrm{Cl}(K)$. For every nonzero ideal $\mathfrak c$, $[\mathfrak c]-[\tau\mathfrak c]\in H$ by definition. Nonzero ideals form a factorial monoid with $(1)$ as its only unit. Induct on the number of prime factors of $\mathfrak A$. If $\mathfrak A=(1)$, then $\mathfrak B\tau(\mathfrak B)=(1)$ forces $\mathfrak B=(1)$. Otherwise $\mathfrak A=\mathfrak p\mathfrak A'$ with $\mathfrak p$ prime, and $\mathfrak p$ divides $\mathfrak B$ or $\tau(\mathfrak B)$. If $\mathfrak B=\mathfrak p\mathfrak B'$, cancelling $\mathfrak p\tau(\mathfrak p)$ gives $\mathfrak A'\tau(\mathfrak A')=\mathfrak B'\tau(\mathfrak B')$, and $[\mathfrak A]-[\mathfrak B]=[\mathfrak A']-[\mathfrak B']$ lies in $H$ by induction. If $\tau(\mathfrak B)=\mathfrak p\mathfrak K$, then $\mathfrak B=\tau(\mathfrak p)\tau(\mathfrak K)$. Cancelling $\mathfrak p\tau(\mathfrak p)$ leaves $\mathfrak A'\tau(\mathfrak A')=\mathfrak K\tau(\mathfrak K)$. Then
$$
[\mathfrak A]-[\mathfrak B]=\bigl([\mathfrak p]-[\tau\mathfrak p]\bigr)+\bigl([\mathfrak A']-[\mathfrak K]\bigr)+\bigl([\mathfrak K]-[\tau\mathfrak K]\bigr)\in H.\qquad\square
$$
No ramification hypothesis enters. In cohomological terms, the ideal group is a permutation $\langle\tau\rangle$-module and has $\widehat H^{-1}=0$.

**Lemma B (local norms).** [Lean, read; the norm of local units at unramified places is read in §11.4.3.5] Let $K$ be CM with (U). Let $\mathfrak A$ be a nonzero integral ideal and $x\in K^{+\times}$ with $\mathfrak AJ(\mathfrak A)=x\mathcal O_K$. Then $x$ is a norm from the completion of $K$ at every finite place $v$ of $K^+$. If $\varphi(x)>0$ for every complex embedding $\varphi$ of $K$, then $x$ is also a local norm at every infinite place.

**Proof.** Let $\mathfrak P=v\mathcal O_K$. It is $J$-stable, since $J$ fixes $K^+$. By Mathlib's `IsDedekindDomain.exists_sup_span_eq`, choose $b\in\mathfrak A$ with $\mathfrak A\mathfrak P+b\mathcal O_K=\mathfrak A$, and write $b\mathcal O_K=\mathfrak A\mathfrak J$. Cancelling $\mathfrak A$ gives $\mathfrak P+\mathfrak J=\mathcal O_K$, and applying $J$ gives $\mathfrak P+J(\mathfrak J)=\mathcal O_K$. Now
$$
bJ(b)\mathcal O_K=\mathfrak AJ(\mathfrak A)\,\mathfrak JJ(\mathfrak J)=x\,\mathfrak JJ(\mathfrak J),
$$
so $bJ(b)=xt$ with $t\mathcal O_K=\mathfrak JJ(\mathfrak J)$. No prime containing $\mathfrak P$ contains $t$ (`ideal_step`). Since $bJ(b)=N_{K/K^+}(b)$ (`norm_cm`), $t=N(b)/x$ lies in $K^+$. At a prime $w$ of $K$ above $v$ it has valuation $0$, hence $v(t)=0$. So $x=N(b)t^{-1}$ is a global norm times a $v$-adic unit. A global norm is a local norm. At a place unramified in $K$ every local unit is a norm (`map_integerUnitsOver_eq_of_ramificationIdx_eq_one`, Proposition C of §11.4.3.5). This is where (U) is used. At an infinite place $u$ of $K^+$ below a place $W$ of $K$, the completion of $K^+$ is $\mathbb R$, and $x$ is positive there because the embedding defining $W$ sends $x$ to a positive real. With $d=[K_W:K^+_u]\in\{1,2\}$ and $r=x^{1/d}>0$ in $K^+_u$, the local norm of $r$ is $r^d=x$. $\square$

**Proposition C (totally positive real generators; `hasse`).** [Lean, read; the Hasse norm theorem is [Lean]] Let $K$ be CM with (U). Let $\alpha\in\mathcal O_K$ be real with $\varphi(\alpha)>0$ for every complex embedding $\varphi$. If a nonzero integral ideal satisfies $\mathfrak AJ(\mathfrak A)=\alpha\mathcal O_K$, then $[\mathfrak A]\in(1-J)C$.

**Proof.** Here $\alpha\ne0$. By Lemma B, $\alpha$ is a local norm at every place of $K^+$. The Hasse norm theorem for the quadratic extension $K/K^+$ (`mem_range_norm_iff_forall_local_of_finrank_eq_two` [Lean]) gives $\beta\in K^\times$ with $\beta J(\beta)=N_{K/K^+}(\beta)=\alpha$. Write $\beta=b/d$ with $b,d\in\mathcal O_K$ nonzero. Then $dJ(d)\alpha=bJ(b)$. The ideals $\mathfrak A_1=d\mathfrak A$ and $\mathfrak B=b\mathcal O_K$ satisfy
$$
\mathfrak A_1J(\mathfrak A_1)=dJ(d)\alpha\,\mathcal O_K=bJ(b)\,\mathcal O_K=\mathfrak BJ(\mathfrak B).
$$
Lemma A gives $[\mathfrak A_1]-[\mathfrak B]\in(1-J)C$. This difference is $[\mathfrak A]$, because $d\mathcal O_K$ and $\mathfrak B$ are principal. $\square$

The archive derives the Hasse norm theorem (`src/GroundTheory/GlobalFields/HasseNorm.lean:17–62`) from the triviality of $\widehat H^{-1}(\mathrm{Gal}(K/K^+),C_K)$ for the idele class group (`natCard_cycTateNegOne_ideleClassGroup`, `src/GroundTheory/GlobalFields/SecondInequality/Cyclic.lean:26`, read in §11.4.3.7) and from the place-by-place description of idelic norms (`mem_range_ideleNorm_iff_forall`, `src/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean:58`, read in §11.4.3.5 and, down to `mem_range_ideleNorm_iff`, in §11.4.3.6). Suppose the diagonal image of $x$ is the norm of an idele $j$. Then the idele class of $j$ has norm $1$, so it is $\sigma(c)/c$ for an idele class $c$. Lifting, $j=(\sigma(c')/c')a$ with $a\in K^\times$, and injectivity of the diagonal gives $x=N(a)$. This is the proof in [MilneCFT, Ch. VIII, Theorem 3.1, p. 234](https://www.jmilne.org/math/CourseNotes/CFT.pdf), which also starts from the vanishing of $\widehat H^{-1}(G,C_L)$. [Paper]

**Lemma D (real generators; `realGen`).** [Lean, read] Let $K$ be CM with (Q). For every $x\in C^-$ there are a nonzero integral ideal $\mathfrak A$ with $[\mathfrak A]=x$ and a nonzero real $\alpha\in\mathcal O_K$ with $\mathfrak AJ(\mathfrak A)=\alpha\mathcal O_K$.

**Proof.** Choose $\mathfrak A$ with $[\mathfrak A]=x$. Since $x+Jx=0$, $\mathfrak AJ(\mathfrak A)=b\mathcal O_K$ with $b\ne0$. The ideal is $J$-stable, so $J(b)\mathcal O_K=b\mathcal O_K$, and $J(b)t=b$ for a unit $t$. Applying $J$ and substituting gives $tJ(t)=1$. Every infinite place $w$ satisfies $w(J(t))=w(t)$, so $w(t)^2=1$ and $w(t)=1$. By Mathlib's torsion criterion for units (Kronecker's theorem), $t$ is a root of unity. By (Q) choose $v\in E$ with $v/J(v)=t^{-1}$. Then $\alpha=bv$ satisfies
$$
J(\alpha)=J(b)J(v)=bt^{-1}J(v)=bv=\alpha,
$$
and $\alpha\mathcal O_K=b\mathcal O_K$. $\square$

**Theorem E (sign detection of the binary minus defect; `hMinus`).** [Lean, read; the Hasse norm theorem as a named input; the norms of unramified local units are read in §11.4.3.5] Let $K$ be CM with (U) and (Q). Let $e=(e_i)_{i\in\iota}$ be a finite family of complex embeddings containing every embedding of $K$. Let $V\subseteq\mathbb F_2^\iota$ be a subgroup containing $\operatorname{sgn}_e(a)$ for every $a\in K^{+\times}$.

(i) Let $x,y\in C^-$ be represented as in Lemma D by $(\mathfrak A,\alpha)$ and $(\mathfrak B,\beta)$. If $\operatorname{sgn}_e(\alpha)+\operatorname{sgn}_e(\beta)\in S_e$, then $y-x\in(1-J)C$.

(ii) Choose such data for one representative of each coset. Then the map from $C^-/(1-J)C$ to $V/(S_e\cap V)$ sending the coset of $x$ to the class of $\operatorname{sgn}_e(\alpha_x)$ is injective. Hence
$$
[C^-:(1-J)C]\le[V:S_e\cap V].
$$
Thus the cokernel of $1-J$ on the kernel of $1+J$, which is the quotient $C^-/(1-J)C$, embeds into the cokernel of the sign map on real units.

**Proof.** Every element of $S_e$ is the sign vector of a single real unit (`hMinus_unit`). Sign vectors of real elements add under multiplication (`hMinus_mul`), and negation is the identity in $\mathbb F_2$, so sums and negatives in the generated subgroup are realized by products of units. Choose $u\in E^+$ with $\operatorname{sgn}_e(u)=\operatorname{sgn}_e(\alpha)+\operatorname{sgn}_e(\beta)$ and put $\gamma=\alpha\beta u$. It is real and nonzero, and
$$
\operatorname{sgn}_e(\gamma)=\operatorname{sgn}_e(\alpha)+\operatorname{sgn}_e(\beta)+\operatorname{sgn}_e(u)=2\operatorname{sgn}_e(u)=0 .
$$
Since $e$ contains every embedding, $\varphi(\gamma)>0$ for all $\varphi$ (`hMinus_pos`). The ideal $\mathfrak D=J(\mathfrak A)\mathfrak B$ satisfies
$$
\mathfrak DJ(\mathfrak D)=J(\mathfrak A)\,\mathfrak B\,\mathfrak A\,J(\mathfrak B)=\bigl(\mathfrak AJ(\mathfrak A)\bigr)\bigl(\mathfrak BJ(\mathfrak B)\bigr)=\alpha\beta\,\mathcal O_K=\gamma\,\mathcal O_K,
$$
using $J^2=1$ on ideals (`idMap_complexConj_involutive`) and that $u$ is a unit. Proposition C gives $[\mathfrak D]\in(1-J)C$. As $x\in C^-$, $[J(\mathfrak A)]=Jx=-x$, so $[\mathfrak D]=y-x$. This proves (i) (`classGroup_inv_mul_mem_difR_of_sign`). For (ii), suppose two cosets have the same image. Then $\operatorname{sgn}_e(\alpha)-\operatorname{sgn}_e(\beta)=\operatorname{sgn}_e(\alpha)+\operatorname{sgn}_e(\beta)$ lies in $S_e$, so by (i) the cosets coincide. An injective map between finite sets gives the inequality of cardinalities. Note that $(1-J)C\subseteq C^-$, so $[C^-:(1-J)C]$ is the relative index of `difR` in `minK`. $\square$

In Lean the statement is `hMinus` (`HMinus.lean:135–163`). Its hypotheses are `UnrFin K`, surjectivity of `IsCMField.unitsMulComplexConjInv K`, surjectivity of `e`, and `sgn e a ∈ V` for every real `a`. Its conclusion is `(difR (clMap (cE K))).relIndex (minK (clMap (cE K))) ≤ (sgnE e).relIndex V`.

**Lemma F (signs of real units in a cyclotomic layer; `sgnStab`, `sgnUnit`).** [Lean, read] Let $M>2$, let $L=\mathbb Q(\zeta_M)$ with its CM structure, let $\varphi$ be an embedding, and let $e_t=\varphi\circ\sigma_t$ for $t\in G$ with $S=S_e$.

(i) The family $e$ contains every embedding of $L$. For $a\in L^{+\times}$, $\operatorname{sgn}_e(a)\in\mathcal E_J$. The subgroup $S$ is stable under the translations $h\mapsto h(g\,\cdot)$ for $g\in G$. It contains the constant vector $1=\operatorname{sgn}_e(-1)$.

(ii) Let $c=2k+1$ be odd and prime to $M$. There is a primitive $M$-th root of unity $\zeta\in L$ with $\varphi(\zeta)=e^{2\pi i/M}$. The element $u_c=\zeta^{-k}(1+\zeta+\cdots+\zeta^{2k})$ is a real unit with
$$
e_t(u_c)=\frac{\sin(\pi ca/M)}{\sin(\pi a/M)},\qquad a=\operatorname{val}(t)\in\{1,\dots,M-1\},
$$
so $\operatorname{sgn}_e(u_c)(t)\equiv\lfloor ca/M\rfloor\pmod2$. In particular the vector $t\mapsto\lfloor c\operatorname{val}(t)/M\rfloor\bmod2$ lies in $S$.

**Proof.** (i) Two embeddings of the Galois extension $L/\mathbb Q$ differ by an automorphism, and every automorphism is some $\sigma_t$. So every embedding is some $e_t$. For real $a$, the identity $e_{gx}(a)=e_x(\sigma_ga)$ (`embT_mul`) with $\sigma_{-1}=J$ (`conjEq`) gives $e_{-x}(a)=e_x(a)$. Hence $\operatorname{sgn}_e(a)\in\mathcal E_J$. For a real unit $u$ and $g\in G$, $\sigma_g(u)$ is a real unit, since $\sigma_g$ commutes with $J$ in the abelian group $\mathrm{Gal}(L/\mathbb Q)$. Its sign vector is $x\mapsto\operatorname{sgn}_e(u)(gx)$. Translates of generators are therefore generators, and the generated subgroup is translation-stable. Finally $-1$ is a real unit, negative at every embedding.

(ii) The image under $\varphi$ of a primitive $M$-th root of unity in $L$ is a primitive $M$-th root of unity in $\mathbb C$, so $e^{2\pi i/M}$ is a power of it. The corresponding power of the root in $L$ has the stated image and is again primitive (`exists_zeta`). The root $\zeta$ is a unit. The sum $1+\zeta+\cdots+\zeta^{c-1}=(\zeta^c-1)/(\zeta-1)$ is a unit because $c$ is prime to $M$ (`IsPrimitiveRoot.geom_sum_isUnit`). Since $\zeta^{k(M-1)}=\zeta^{-k}$, $u_c$ is a unit. With $\theta=\pi a/M$ and $w=e^{2i\theta}=e_t(\zeta)$,
$$
w^{-k}\sum_{j=0}^{2k}w^j=\frac{e^{i(2k+1)\theta}-e^{-i(2k+1)\theta}}{e^{i\theta}-e^{-i\theta}}=\frac{\sin((2k+1)\theta)}{\sin\theta}
$$
(`geom_sin`). So every $e_t(u_c)$ is real. The case $t=1$ gives $J(u_c)=u_c$, since $\varphi\circ J=\overline\varphi$ and $\varphi$ is injective. As $0<a<M$, $\sin(\pi a/M)>0$. Also $\sin(\pi ca/M)\neq0$, since $M\nmid ca$ when $ca$ is prime to $M>2$ (`sin_ne`). The sign is that of $\sin(\pi y)$ with $y=ca/M$. Finally $\sin(\pi y)=(-1)^{\lfloor y\rfloor}\sin(\pi(y-\lfloor y\rfloor))$, and the last factor is positive (`sinSign`). $\square$

**Lemma G (the two cyclotomic hypotheses; `unitSurj`, `unrJ`).** [Lean, read for the arithmetic; the inertia order and the cyclotomic inertia groups are [Lean]] Let $M=f2^n$ with $f>1$ odd and $n\ge2$, and let $L=\mathbb Q(\zeta_M)$.

(i) Hypothesis (Q) holds: $1-\zeta$ is a unit, and $(1-\zeta)/J(1-\zeta)=-\zeta$ generates the roots of unity of $L$.

(ii) Hypothesis (U) holds: no finite prime of $L$ ramifies over $L^+$.

**Proof.** (i) The integer $M$ is not a prime power, since a prime power divisible by $2$ is a power of $2$ and has no odd divisor $f>1$. Hence $\Phi_M(1)=1$ (Mathlib's `Polynomial.eval_one_cyclotomic_not_prime_pow`). Writing $\Phi_M=(X-\zeta)q$ and evaluating at $1$ shows that $1-\zeta$ is a unit. Since $\lvert\varphi(\zeta)\rvert=1$, $J(\zeta)=\zeta^{-1}$ and $(1-\zeta)/(1-\zeta^{-1})=-\zeta$. Write $M=4k$. Then $\zeta^{2k}=-1$, so $-\zeta=\zeta^{2k+1}$ is a primitive $M$-th root, because $\gcd(2k+1,4k)=1$. The roots of unity of $L$ form a cyclic group of order $M$ for even $M$ (`IsCyclotomicExtension.Rat.torsionOrder_eq`). Hence every root of unity is $(-\zeta)^j=(1-\zeta)^j/J((1-\zeta)^j)$.

(ii) Let $w$ be a prime of $L$ over the rational prime $p$. The inertia group of $w$ in $\mathrm{Gal}(L/L^+)$ has order equal to the ramification index of $w$ over $L^+$ (`ineCard` [Lean]), and $\mathrm{Gal}(L/L^+)=\{1,J\}$. Suppose $J$ were in the inertia group. Since $J=\sigma_{M-1}$, the description of inertia in cyclotomic fields (`cycIne` [Lean]) would give $M-1\equiv1$ modulo the prime-to-$p$ part $M'_p$ of $M$. In that description, $\sigma_a$ is inertial at $w$ exactly when $a\equiv1\bmod M'_p$. Then $M'_p\mid2$. But $M'_2=f\ge3$ is odd, and $4\mid M'_p$ for odd $p$ (`unrJ_arith`). $\square$

**Corollary H (`sgnCyc` and the $\ell=2$ branch of `cyc`).** [Lean, read; inputs as named] Let $M=f2^n$ with $f>1$ odd and $n\ge2$. Let $c$ be odd and prime to $M$, and let $\gamma\in G$ satisfy $([\gamma]-1)^N\in(\theta_{\mathrm{half}},1+[-1],2)$ in $\mathbb Z[G]$, where $\theta_{\mathrm{half}}$ is `thetaH M c`. Then for $C=\mathrm{Cl}(\mathbb Q(\zeta_M))$,
$$
[C^-:(1-J)C]\le[\mathcal E_J:S\cap\mathcal E_J]\le\bigl(2^{[G:\langle\gamma\rangle]}\bigr)^N.
$$

**Proof.** Lemma F(ii) provides $\varphi$ and the sign vector of $u_c$ in $S$ (`SgnCyc.lean:19`). Lemma F(i) gives the surjectivity of $e$ and places all real sign vectors in $\mathcal E_J$ (`:20`). Lemma G gives (U) and (Q). Theorem E with $V=\mathcal E_J$ is the first inequality (`:21–22`). For the second, Lemma 8(ii) (`sgnAlg`) needs $S$ to be translation-stable, which is Lemma F(i). It also needs the mod $2$ reduction of the coefficient vector of $\theta_{\mathrm{half}}(1+[J])$ in $S$. Translate the sign vector of $u_c$ by $c^{-1}$ and subtract $k$ times the constant vector:
$$
t\longmapsto\Bigl\lfloor\frac{c\operatorname{val}(c^{-1}t)}{M}\Bigr\rfloor-k=g_c(t).
$$
By Lemma 5(i) (`thetaFull`), this is the coefficient of $\theta_{\mathrm{half}}(1+[J])$ at $t$ modulo $2$ (`:29–37`). Finally $J\neq1$ because $-1\neq1$ in $\mathbb Z/M\mathbb Z$ (`:25–28`). $\square$

In `cyc` the corollary is called at `FerreroWashington.lean:56` with $c=2(2f)+1$ and the $\gamma$, $N$ of `memZ`. Line 57 rewrites $[G:\langle\gamma\rangle]=\varphi(4f)$, and `pTwo` (Lemma 8(i)) combines the defect bound with the image bound at `:63–64`. This completes the reading of Lemma 8(iii). The $\ell=2$ case of Theorem 9 now rests, beyond the inputs used for the image bound, only on the cohomological input of Proposition C, since the local norm input of Lemma B is read in §11.4.3.5, and on the inertia inputs of Lemma G.

**Remarks.** [Expository] *Why the odd projection cannot be copied.* For odd $\ell$, the element $(1-J)/2$ is an idempotent on $C[\ell^\infty]$. It splits $C[\ell^\infty]$ into eigenspaces and identifies $C^-[\ell]$ with $(1-J)C\cap C[\ell]$ (Lemma 7). For $\ell=2$ the corresponding group $C^-/(1-J)C$ is killed by $2$ but need not vanish. The same happens for units, as in Example 1, where the unit group is $\mathbb Z/4$ with $J=-1$. The Kummer reflection of §11.4.3.3 does not substitute either. It turns $J$-fixed characters into minus radical classes because $J$ inverts $\mu_\ell$. For $\ell=2$ the group $\mu_2=\{\pm1\}$ is fixed by $J$, so a $J$-fixed quadratic character has a $J$-fixed radical class, and the eigenspaces are not exchanged. The binary route uses instead the places at which $K/K^+$ ramifies in every case, the real places of $K^+$. Under (U), for a generator of a relative norm ideal, those are the only local obstructions to being a relative norm (Lemma B).

*Kernels and cokernels.* The choices in Theorem E do not matter. Replacing $\mathfrak A$ by $\beta\mathfrak A$ multiplies $\alpha$ by the totally positive $\beta J(\beta)$. Changing the real generator multiplies it by a real unit. If $x=z-Jz$ with $z=[\mathfrak C]$, the fractional ideal $\mathfrak C J(\mathfrak C)^{-1}$ represents $x$ and has real generator $1$. So the map is a homomorphism with kernel exactly $(1-J)C$, although the archive needs only the injectivity. In this form Theorem E is an embedding
$$
\widehat H^{-1}(\langle J\rangle,C)=C^-/(1-J)C\hookrightarrow\mathbb F_2^{\{\text{real places of }K^+\}}/\operatorname{sgn}(E^+)\cong P_{K^+}/P^+_{K^+}.
$$
Here $P_{K^+}$ and $P^+_{K^+}$ are the principal and totally positive principal ideals, so the target is the kernel from the narrow to the ordinary class group of $K^+$. The map sends $[\mathfrak A]$ to the narrow class of $N_{K/K^+}(\mathfrak A)=\alpha\mathcal O_{K^+}$. Lemma A is the vanishing of $\widehat H^{-1}$ on ideals. Lemma D uses $W/(1-J)E=0$, which is (Q). Proposition C uses the injectivity of $K^{+\times}/N(K^\times)$ into the product of the local norm residue groups. For a generator of a relative norm ideal, Lemma B removes every finite component under (U), and only the signs at the real places remain. Example 2 shows that the embedding need not be onto. There the target has order $2$, generated by the narrow class of $(\sqrt3)$, and that narrow class contains no relative norm ideal.

*The archive's minus part and the norm minus part.* [Paper] Lemmermeyer defines the minus class group as the kernel of $N_{K/K^+}:\mathrm{Cl}(K)\to\mathrm{Cl}(K^+)$ [Lemmermeyer1995, §1, p. 347](http://matwbn.icm.edu.pl/ksiazki/aa/aa72/aa7245.pdf). The archive's $C^-=\ker(1+J)$ is the kernel of $N$ followed by extension of ideals back to $K$, since $N(\mathfrak A)\mathcal O_K=\mathfrak AJ(\mathfrak A)$. The two agree when no class of $K^+$ capitulates in $K$, which holds when $Q_K=2$ [Lemmermeyer1995, Proposition 1(b), p. 348]. Its proof is the argument of Lemma D. Proposition 1(g) there (Hasse's Satz 27) is Lemma G(i), proved from $(1-\zeta_m)^{1-\sigma}=-\zeta_m$ in the same way. Proposition 1(c) says that $Q_K=1$ whenever $K^+$ has units of every signature. Under (Q) the full sign quotient therefore always has order at least $2$, as in Example 2 [Lemmermeyer1995, Proposition 1, pp. 348–349].

*Comparison with the ambiguous class number formula.* Under (U), the ramified places of $K/K^+$ are the $[K^+:\mathbb Q]$ real places. The units of $K^+$ that are norms of elements are exactly the totally positive units. Lemmermeyer's formula then counts the ambiguous classes of $K/K^+$ as $h(K^+)\,2^{[K^+:\mathbb Q]-1}/[E^+:E^+_{\gg0}]$ [Lemmermeyer2013, Theorem 1](https://arxiv.org/pdf/1309.1071). Since $[E^+:E^+_{\gg0}]$ is the number of sign vectors of real units, the formula reads $\lvert C^{J}\rvert=h(K^+)\,[V:S_e]/2$ with $V$ the full sign space. The sign quotient of Theorem E reappears, now counting the invariant classes $C^J$ rather than the defect $C^-/(1-J)C$. The archive does not use the formula, and the two examples check it only for consistency.

**Reading boundary and source map.** Read in full here [Lean, read]: `hMinus` and its private helpers, `realGen`, `hasse`, `classGroup_div_mem_of_mul_conj_eq`, `locFin` with `ideal_step` and `norm_cm`, `locInf`, `sgnStab`, `sgnUnit` with `geom_sin`, `exists_zeta` and `sin_ne`, `sinSign`, `unitSurj`, `unrJ` with `unrJ_prime`, `unrJ_arith` and `unrJ_conj`, the deduction of the Hasse norm theorem in `HasseNorm.lean`, and the definitions `sgn`, `sgnE`, `UnrFin`, `embT`, `difR`, `minK`, `evenF` and `cE`. With these, `sgnCyc` is read together with all its archive inputs. Named inputs not read here [Lean] (the first is read in §11.4.3.7 down to the Kummer case and the two Herbrand suppliers): `natCard_cycTateNegOne_ideleClassGroup` (with the second inequality behind it), `ineCard`, `cycIne`, `relIncl`, `nonempty_placesOver`, `Qh29.norm_eq_mul_cE`, and the cited Mathlib declarations: the `IsCMField` interface, the torsion criterion for units, `IsDedekindDomain.exists_sup_span_eq`, `Polynomial.eval_one_cyclotomic_not_prime_pow`, `IsPrimitiveRoot.geom_sum_isUnit` and `IsCyclotomicExtension.Rat.torsionOrder_eq`. Inherited from §11.4.3.2: `sgnAlg`, `pTwo`, `thetaFull`, `conjEq`, `memZ` and `cyc`. The odd-prime reflection of §11.4.3.3 is not touched. Section 11.4.3.5 reads `map_integerUnitsOver_eq_of_ramificationIdx_eq_one` and `mem_range_ideleNorm_iff_forall` down to the local-field theorem `normIntegerUnits_surjective`. The reading status of the full Ferrero–Washington dependency cone remains as in §11.4.3.

In the table, `GL/` expands to `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/`, and `GT/` to `src/GroundTheory/GlobalFields/`.

| Source and lines | Role and reading |
|---|---|
| `GL/FerreroWashingtonIndex/HMinus.lean:12–163` | [Lean, read] Real sign vectors, one unit per element of $S_e$, positivity, the kernel step, and the injective map of Theorem E. |
| `GL/FerreroWashingtonIndex/RealGen.lean:6–82` | [Lean, read] Real generator of $\mathfrak AJ(\mathfrak A)$ from (Q) (Lemma D). |
| `GL/FerreroWashingtonIndex/Mk0PrincipalEqOne.lean:10–63` | [Lean, read] `hasse` (Proposition C). |
| `GL/FerreroWashingtonIndex/ClassGroupDivMemOfMulConjEq.lean:6–96` | [Lean, read] Ideal-theoretic Hilbert 90 (Lemma A). |
| `GL/FerreroWashingtonIndex/LocFin.lean:8–92`, `GL/FerreroWashingtonIndex/LocInf.lean:8–62` | [Lean, read] Local norms at finite and infinite places (Lemma B). |
| `GT/HasseNorm.lean:17–62,98–105` | [Lean, read] Deduction of the Hasse norm theorem from the vanishing of $\widehat H^{-1}$ of the idele class group. |
| `GT/SecondInequality/Cyclic.lean:26` | [Lean, read] Cohomological input to the Hasse norm theorem, read in §11.4.3.7. |
| `GT/IdeleGroups/LocalNormsEverywhere.lean:28,58` | [Lean, read] Local norm inputs, read in §11.4.3.5. |
| `GL/FerreroWashingtonIndex/SgnStab.lean:7–51` | [Lean, read] Lemma F(i). |
| `GL/FerreroWashingtonIndex/SgnUnit.lean:7–111`, `GL/FerreroWashingtonIndex/SinSign.lean:5–27` | [Lean, read] Lemma F(ii). |
| `GL/FerreroWashingtonIndex/UnitSurj.lean:6–95` | [Lean, read] Lemma G(i). |
| `GL/FerreroWashingtonIndex/UnrJPrime.lean:8–62` | [Lean, read] Lemma G(ii), with `ineCard` (`GL/ClassFieldRamification/IneCard.lean:8`) and `cycIne` (`GL/ClassFieldRamification/CycIne.lean:8`) [Lean]. |
| `GL/FerreroWashingtonIndex/SgnCyc.lean:13–37`, `GL/FerreroWashingtonIndex/FerreroWashington.lean:56–64` | [Lean, read] Corollary H and its consumption in `cyc`. |
| `GL/FerreroWashingtonIndex/CycRepApply.lean:26–42`, `GL/FerreroWashingtonIndex/TwSingle.lean:62–72`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:64` | [Lean, read] Definitions. |

#### 11.4.3.5 Norms of local units in unramified extensions

**Motivation.** Lemma B of §11.4.3.4 (`locFin`) needs one local fact at every finite place $v$ of the real subfield: if no prime of the CM field $K$ over $v$ ramifies, then every $v$-adic unit is the norm of a local unit of $K$. The archive takes this from `map_integerUnitsOver_eq_of_ramificationIdx_eq_one` (`src/GroundTheory/GlobalFields/IdeleGroups/LocalNormsEverywhere.lean:28`). The same declaration is used a second time on the binary route. The place-by-place description of idelic norms `mem_range_ideleNorm_iff_forall` (`LocalNormsEverywhere.lean:58`), which Proposition C of §11.4.3.4 feeds into the Hasse norm theorem, needs integral preimages at almost all places, and gets them from the same local statement at the places where the extension is unramified. Both uses were left as named inputs in §11.4.3.4. This subsection reads them down to the local-field theorem behind them, `normIntegerUnits_surjective` (`src/GroundTheory/LocalFields/UnramifiedNormSurj.lean:182`). The archive does not prove this by local class field theory. It follows the elementary route: the residue-field norm is onto, the residue-field trace is onto, these two facts lift one filtration step at a time through the principal units, and completeness assembles the steps into a limit. This is the proof in [MilneCFT, Ch. III, §1, Proposition 1.2 with Lemmas 1.3–1.5, pp. 97–98](https://www.jmilne.org/math/CourseNotes/CFT.pdf) [Paper]. The subsection also records, hypothesis by hypothesis, what the local-field axioms, the ramification index, residue separability and the normalization of the valuation each pay for. Source references are to the joined archive with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` and to Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. [Lean, read]

**Example 1 (the residue step in the unramified quadratic extension of $\mathbb Q_3$).** [Expository] Let $K=\mathbb Q_3$ and $L=\mathbb Q_3(i)$ with $i^2=-1$. Since $-1$ is not a square modulo $3$, the polynomial $X^2+1$ is irreducible over $\mathbb F_3$, so $L/K$ is the unramified quadratic extension: $\mathcal O_L=\mathbb Z_3[i]$, the prime $3$ stays prime in $\mathcal O_L$, and the residue extension is $\mathbb F_9=\mathbb F_3(i)$ over $\mathbb F_3$. The norm is $N(a+bi)=a^2+b^2$. On residue fields,
$$
N(1)=1,\qquad N(i)=1,\qquad N(1+i)=2,
$$
so the residue norm $\mathbb F_9^\times\to\mathbb F_3^\times=\{1,2\}$ is onto. Take the unit $u=5\in\mathbb Z_3^\times$, with residue $2$. The residue step chooses $g_0=1+i$, a unit of $\mathcal O_L$ whose residue norm is $2$. Then $N(g_0)=2$ and
$$
\frac{u}{N(g_0)}=\frac52=1+3\cdot\frac12,
$$
which lies in the principal units $U_K^{(1)}=1+3\mathbb Z_3$ and not in $U_K^{(2)}$. The residue step has removed the obstruction visible modulo $3$, and only a principal unit is left. For this particular $u$ an exact preimage can be seen at once, $N(2+i)=5$. The algorithm below does not find it; it converges to a different preimage, and the two differ by an element of norm $1$.

**Example 2 (lifting a principal unit in the same extension).** [Expository] Keep $K=\mathbb Q_3$, $L=\mathbb Q_3(i)$ and the uniformizer $\varpi=3$, which stays a uniformizer in $L$. The trace is $\mathrm{Tr}(x+yi)=2x$, and for $a\in\mathcal O_L$,
$$
N(1+3a)=(1+3x)^2+9y^2=1+3\cdot\mathrm{Tr}(a)+9\,(x^2+y^2),\qquad a=x+yi.
$$
The first-order term is $3\,\mathrm{Tr}(a)$ and the second-order term is divisible by $9$. Take $h=-2=1+3\cdot(-1)\in U_K^{(1)}\setminus U_K^{(2)}$.

*Step $n=1$.* Here $h=1+3c$ with $c=-1$, residue $\bar c=2$. We need $a$ with $\mathrm{Tr}(\bar a)=\bar c$, that is $2x\equiv2$, so $x\equiv1\bmod3$. Take $a=1$, $g_1=1+3=4$, $N(g_1)=16$. Then
$$
\frac{h}{N(g_1)}=-\frac18=1-\frac98,\qquad v_3\!\left(-\tfrac98\right)=2,
$$
so $h/N(g_1)\in U_K^{(2)}$.

*Step $n=2$.* Now $-1/8=1+9c$ with $c=-1/8$. Since $8\equiv2$ and $2\cdot2\equiv1\bmod3$, we get $\bar c=-2=1$, so $2x\equiv1$, $x\equiv2$. Take $g_2=1+9\cdot2=19$, $N(g_2)=361$. Then
$$
\frac{-1/8}{361}=-\frac1{2888}=1-\frac{2889}{2888},\qquad 2889=3^3\cdot107,
$$
so the quotient lies in $U_K^{(3)}$.

*Step $n=3$.* Write $-1/2888=1+27c$ with $c=-107/2888$. Both $107$ and $2888$ have residue $2$, so $\bar c=-1=2$ and $x\equiv1$. Take $g_3=1+27=28$, $N(g_3)=784$, and the quotient $-1/2264192=1-2264193/2264192$ has $v_3(2264193)=4$, so it lies in $U_K^{(4)}$.

The partial products $y_j=g_1g_2\cdots g_j$ satisfy $h/N(y_j)\in U_K^{(j+1)}$ and $y_{j+1}/y_j=g_{j+1}\in U_L^{(j+1)}$, so $(y_j)$ is Cauchy for the filtration of $U_L$. Its limit $y$ has $N(y)=h$. The choice at each step is not unique: at step $1$ the choice $a=1+i$ gives $g=4+3i$, $N(g)=25$ and $-2/25=1-27/25\in U_K^{(3)}$, two steps at once, because the second-order term $9(x^2+y^2)$ happened to help. The proof only uses that this term is divisible by $9$. For comparison, since $p=3$ is odd, $-2\equiv1\bmod3$ is already a square in $\mathbb Z_3$, and $y=\sqrt{-2}=1+3+2\cdot9+\cdots\in\mathbb Z_3\subset L$ has $N(y)=y^2=-2$. Hensel's lemma shortcuts the principal units when $p$ is odd and $[L:K]$ is prime to $p$. The archive's argument does not use this. It works uniformly for every unramified extension, including degree divisible by $p$, where the principal units are not all $[L:K]$-th powers.

**Example 3 (a ramified boundary case).** [Expository] Let $K=\mathbb Q_3$ and $L=\mathbb Q_3(\sqrt3)$, so $e=2$ and the residue field is still $\mathbb F_3$. Here $N(a+b\sqrt3)=a^2-3b^2$. A unit of $\mathcal O_L=\mathbb Z_3[\sqrt3]$ has $a\in\mathbb Z_3^\times$, and then $N(a+b\sqrt3)\equiv a^2\equiv1\bmod3$. So $-1$, $2$ and $5$ are units of $K$ that are not norms of units of $L$, and
$$
N(U_L)=U_K^{(1)}=1+3\mathbb Z_3,\qquad [U_K:N(U_L)]=2=e.
$$
The inclusion $N(U_L)\supseteq U_K^{(1)}$ holds because every element of $1+3\mathbb Z_3$ is a square in $\mathbb Z_3$ and $N(a)=a^2$ for $a\in\mathbb Z_3$. The proof below fails at its first lemma. The residue of a norm is not the residue-field norm: the residue of $N(a+b\sqrt3)$ is $\bar a^2$, the square of the residue norm $N_{\mathbb F_3/\mathbb F_3}(\bar a)=\bar a$. The reason is the dimension count. The basis $1,\sqrt3$ of $\mathcal O_L$ over $\mathcal O_K$ reduces to $1,0$, which is not a basis of $\mathbb F_3$ over $\mathbb F_3$. The valuations are also misaligned: $3=(\sqrt3)^2$ gives $1+3\mathcal O_L=U_L^{(2)}$, so the level-$n$ principal units of $K$ sit at level $2n$ in $L$. The theorem below needs the ramification index to be $1$ in both places.

**Definitions.** [Lean, read] The archive's local fields carry Mathlib's class `IsNonarchimedeanLocalField`. For such a field $K$ with valuation $\mathrm{val}_K$, write $\mathcal O_K$ for the valuation ring, $\mathfrak m_K$ for its maximal ideal and $k_K=\mathcal O_K/\mathfrak m_K$ for the residue field, with residue map $\mathrm{res}$. Three facts about $\mathcal O_K$ are drawn from the local-field class: it is a discrete valuation ring with an irreducible element $\varpi$ (`IsDiscreteValuationRing.exists_irreducible`); its residue field is finite; and it is $\mathfrak m_K$-adically complete (`isAdicComplete_integer`, `src/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean:52`). The *unit filtration* is
$$
U_K^{(n)}=\{u\in\mathcal O_K^\times:\ u-1\in\mathfrak m_K^n\}\qquad(n\ge0),
$$
a decreasing sequence of subgroups with $U_K^{(0)}=\mathcal O_K^\times$ (`unitFiltration`, `src/GroundTheory/LocalFields/UnitsBasic.lean:12–40`). The residue map induces $\mathcal O_K^\times\to k_K^\times$, which is onto with kernel $U_K^{(1)}$ (`unitsToResidue_surjective`, `ker_unitsToResidue`, `UnitsBasic.lean:275–290`). For $x\in K^\times$, $\mathrm{ord}(x)\in\mathbb Z$ is the normalized valuation with $\mathrm{ord}(\varpi)=1$ (`UnitsBasic.lean:144`).

Let $L/K$ be a finite extension of such fields, with $\mathcal O_K\subseteq\mathcal O_L$ (`ValuativeExtension`). The *ramification index* $e(L/K)$ is the exponent with $\mathfrak m_K\mathcal O_L=\mathfrak m_L^{\,e}$, and the *residue degree* $f(L/K)$ is $[k_L:k_K]$; the archive defines them as the ramification index and inertia degree of $\mathfrak m_L$ over $\mathcal O_K$ (`src/GroundTheory/LocalFields/Integers.lean:16,18`) and proves $ef=[L:K]$ (`ramificationIndex_mul_residueDegree`, `Integers.lean:123`) and $\mathfrak m_K\mathcal O_L=\mathfrak m_L^{\,e}$ (`map_maximalIdeal`, `Integers.lean:133`). The extension is *unramified* when $e=1$ (`IsUnramified`, `src/GroundTheory/LocalFields/UnramifiedDefs.lean:11`), equivalently when $f=[L:K]$ (`isUnramified_iff_finrank_residueField`). The *unit norm* is
$$
N=N_{L/K}:\ \mathcal O_L^\times\to\mathcal O_K^\times,
$$
the units map of the algebra norm $\mathrm{Nm}_{\mathcal O_L/\mathcal O_K}$ (`normIntegerUnits`, `src/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean:123`); its value agrees with the field norm $\mathrm{Nm}_{L/K}$ on the underlying elements (`coe_normIntegerUnits`). Finally, for a group $G$ with a decreasing sequence of subgroups $F_n$, a sequence $(x_j)$ is *$F$-Cauchy* if for every $N$ there is $M$ with $x_n/x_m\in F_N$ for all $m,n\ge M$; the filtration is *complete* if every $F$-Cauchy sequence has a limit $y$ in the sense $x_n/y\in F_N$ for $n$ large, and *separated* if $\bigcap_nF_n=\{1\}$ (`src/GroundTheory/LocalFields/FilteredSurj.lean:12–27`).

Throughout the lemmas, $L/K$ is a finite unramified extension of nonarchimedean local fields and $\varpi$ is an irreducible element of $\mathcal O_K$.

**Lemma 1 (residues of norms and traces; `residue_norm`, `residue_trace`).** [Lean, read] For $y\in\mathcal O_L$,
$$
\mathrm{res}\bigl(\mathrm{Nm}_{\mathcal O_L/\mathcal O_K}(y)\bigr)=\mathrm{Nm}_{k_L/k_K}(\mathrm{res}\,y),\qquad
\mathrm{res}\bigl(\mathrm{Tr}_{\mathcal O_L/\mathcal O_K}(y)\bigr)=\mathrm{Tr}_{k_L/k_K}(\mathrm{res}\,y).
$$

**Proof.** The ring $\mathcal O_L$ is a finite free $\mathcal O_K$-module (a finitely generated torsion-free module over a discrete valuation ring). Choose a basis $b_1,\dots,b_m$ (`Module.Free.chooseBasis`), so $m=[L:K]$ (`finrank_integer`, `Integers.lean:88`). Every element of $k_L$ is the residue of some $y=\sum c_ib_i$, and $\mathrm{res}\,y=\sum\mathrm{res}(c_i)\,\mathrm{res}(b_i)$ (`residue_eq_sum_repr`, `UnramifiedNormSurj.lean:37–44`), so the residues $\bar b_i$ span $k_L$ over $k_K$. Since $e=1$, the count $m=[L:K]=f=[k_L:k_K]$ shows that $m$ spanning vectors form a basis (`residueBasis`, `UnramifiedNormSurj.lean:52–61`, through Mathlib's `basisOfTopLeSpanOfCardEqFinrank`). With respect to these two bases the matrix of multiplication by $\mathrm{res}\,y$ on $k_L$ is the entrywise residue of the matrix of multiplication by $y$ on $\mathcal O_L$ (`leftMulMatrix_residueBasis`, `:76–81`). Norm and trace are determinant and trace of this matrix, and the residue map is a ring homomorphism, so it commutes with determinant and trace (`:83–94`). $\square$

The hypothesis $e=1$ is used exactly once, in the dimension count. Example 3 shows what happens without it.

**Lemma 2 (first-order expansion of the norm and alignment of the filtrations; `exists_norm_one_add_smul`, `irreducible_algebraMap_of_isUnramified`, `normIntegerUnits_mem_unitFiltration`).** [Lean, read]

(i) For $r\in\mathcal O_K$ and $a\in\mathcal O_L$ there is $c\in\mathcal O_K$ with
$$
\mathrm{Nm}_{\mathcal O_L/\mathcal O_K}(1+ra)=1+r\,\mathrm{Tr}_{\mathcal O_L/\mathcal O_K}(a)+r^2c.
$$

(ii) The element $\varpi$ remains irreducible in $\mathcal O_L$, so $\mathfrak m_L^{\,n}=\varpi^n\mathcal O_L$ for all $n$.

(iii) $N(U_L^{(n)})\subseteq U_K^{(n)}$ for all $n\ge0$.

**Proof.** (i) Let $A$ be the matrix of multiplication by $a$ in a basis of $\mathcal O_L$ over $\mathcal O_K$. Then $\det(1+XA)\in\mathcal O_K[X]$ has constant term $1$ and linear coefficient $\mathrm{tr}\,A=\mathrm{Tr}(a)$ (Mathlib's `Matrix.det_one_add_smul`). Dividing twice by $X$ (`Polynomial.divX`) leaves a polynomial whose value at $r$ is the required $c$ (`UnramifiedNormSurj.lean:26–35`). (ii) By `map_maximalIdeal`, $\mathfrak m_K\mathcal O_L=\mathfrak m_L^{\,e}=\mathfrak m_L$ when $e=1$, and $\mathfrak m_K=\varpi\mathcal O_K$, so $\varpi\mathcal O_L=\mathfrak m_L$ and $\varpi$ is a uniformizer of $\mathcal O_L$ (`:96–102`). (iii) For $n=0$ there is nothing to prove. For $n\ge1$ and $u\in U_L^{(n)}$, (ii) gives $u=1+\varpi^na$ with $a\in\mathcal O_L$. By (i) with $r=\varpi^n$,
$$
N(u)=1+\varpi^n\bigl(\mathrm{Tr}(a)+\varpi^nc\bigr)\in U_K^{(n)}.\qquad\square
$$

Part (ii) is where the normalization of the valuation pays. Because $\varpi$ is a uniformizer on both sides, the $n$-th filtration step of $L$ maps into the $n$-th step of $K$, and the graded lemma below can be used with the identity reindexing $\varphi(n)=n$. In a ramified extension the correct comparison would be between $U_L^{(en)}$ and $U_K^{(n)}$.

**Lemma 3 (the residue-field inputs; `trace_integer_surjective`).** [Lean, read; the two finite-field facts are Mathlib inputs [Lean]]

(i) The norm $k_L^\times\to k_K^\times$ is onto.

(ii) The trace $k_L\to k_K$ is onto.

(iii) The trace $\mathrm{Tr}_{\mathcal O_L/\mathcal O_K}:\mathcal O_L\to\mathcal O_K$ is onto.

**Proof.** (i) is Mathlib's `FiniteField.unitsMap_norm_surjective` (`Mathlib/FieldTheory/Finite/GaloisField.lean:236` at the pinned commit). It is a counting argument: $k_L^\times$ is cyclic, the norm to $k_K$ is $x\mapsto x^{(|k_L|-1)/(|k_K|-1)}$ (`algebraMap_norm_eq_pow`), so its kernel has at most $(|k_L|-1)/(|k_K|-1)$ elements, and a homomorphism between finite groups whose kernel is at most $|\text{source}|/|\text{target}|$ is onto. This uses that the residue fields are finite. (ii) is Mathlib's `Algebra.trace_surjective` (`Mathlib/RingTheory/Trace/Basic.lean:521`), which needs the extension $k_L/k_K$ to be separable: a nonzero $k_K$-linear map to a field is onto, and the trace of a finite separable extension is nonzero. Finite fields are perfect, so separability is automatic here. This is the only place where residue separability enters. (iii) Choose $t\in k_L$ with $\mathrm{Tr}(t)=1$ and lift it to $a\in\mathcal O_L$. By Lemma 1, $\mathrm{res}\,\mathrm{Tr}(a)=1\neq0$, so $\mathrm{Tr}(a)$ is a unit $\eta$ of $\mathcal O_K$. For $c\in\mathcal O_K$, $\mathrm{Tr}(\eta^{-1}c\,a)=c$ (`UnramifiedNormSurj.lean:104–113`). $\square$

**Lemma 4 (one step at a time; `exists_normIntegerUnits_div_mem_one`, `exists_normIntegerUnits_div_mem_succ`).** [Lean, read]

(i) For every $h\in\mathcal O_K^\times$ there is $g\in\mathcal O_L^\times$ with $h/N(g)\in U_K^{(1)}$.

(ii) For $n\ge1$ and every $h\in U_K^{(n)}$ there is $g\in U_L^{(n)}$ with $h/N(g)\in U_K^{(n+1)}$.

**Proof.** (i) By Lemma 3(i) there is $\zeta\in k_L^\times$ with $\mathrm{Nm}(\zeta)=\mathrm{res}\,h$, and $\zeta$ lifts to $g\in\mathcal O_L^\times$. By Lemma 1, $\mathrm{res}\,N(g)=\mathrm{Nm}(\zeta)=\mathrm{res}\,h$, so $h/N(g)$ is in the kernel of $\mathcal O_K^\times\to k_K^\times$, which is $U_K^{(1)}$ (`UnramifiedNormSurj.lean:131–138`). This is the residue step of Example 1.

(ii) Write $h=1+\varpi^nc$ with $c\in\mathcal O_K$. By Lemma 3(ii) there is $t\in k_L$ with $\mathrm{Tr}(t)=\mathrm{res}\,c$; lift $t$ to $a\in\mathcal O_L$. Set $g=1+\varpi^na$. It is a unit because $\varpi^na\in\mathfrak m_L$ (`isUnit_one_add_mul`, `UnitsBasic.lean:321`), and it lies in $U_L^{(n)}$ by Lemma 2(ii). By Lemma 2(i),
$$
N(g)=1+\varpi^n\,\mathrm{Tr}(a)+\varpi^{2n}d,\qquad d\in\mathcal O_K,
$$
so
$$
h-N(g)=\varpi^n\bigl(c-\mathrm{Tr}(a)\bigr)-\varpi^{2n}d .
$$
By Lemma 1, $\mathrm{res}(c-\mathrm{Tr}(a))=\mathrm{res}\,c-\mathrm{Tr}(t)=0$, so $c-\mathrm{Tr}(a)=\varpi e$ for some $e\in\mathcal O_K$, and $2n\ge n+1$. Hence $h-N(g)=\varpi^{n+1}(e-\varpi^{n-1}d)\in\mathfrak m_K^{n+1}$. For units $x,y$ one has $x/y\in U_K^{(k)}$ if and only if $x-y\in\mathfrak m_K^{k}$ (`div_mem_unitFiltration_iff`, `LocalIndex.lean:25`), which gives $h/N(g)\in U_K^{(n+1)}$ (`UnramifiedNormSurj.lean:140–168`). These are the steps of Example 2. $\square$

**Lemma 5 (graded surjectivity passes to the limit; `map_eq_of_graded_surjective`).** [Lean, read] Let $f:G\to H$ be a homomorphism of groups, $F_n\subseteq G$ and $E_n\subseteq H$ decreasing sequences of subgroups, $F$ complete and $E$ separated. Fix $k\ge0$ and suppose that for all $n\ge k$:

(a) $f(F_n)\subseteq E_n$, and

(b) for every $h\in E_n$ there is $g\in F_n$ with $h/f(g)\in E_{n+1}$.

Then $f(F_k)=E_k$.

**Proof.** The inclusion $f(F_k)\subseteq E_k$ is (a). Let $h\in E_k$. Define $r_0=h$ and, given $r_j\in E_{k+j}$, use (b) at level $k+j$ to choose $D_j\in F_{k+j}$ with $r_{j+1}=r_j/f(D_j)\in E_{k+j+1}$. Let $x_j=D_jD_{j-1}\cdots D_0$. Then $h/f(x_j)=r_{j+1}$ by induction, each $x_j\in F_k$, and $x_{m+d}/x_m\in F_{k+m+1}$ because it is a product of $D_{m+1},\dots,D_{m+d}$, all in $F_{k+m+1}$. So $(x_j)$ is $F$-Cauchy. By completeness it has a limit $y$, and $y\in F_k$ because $x_{M}/y\in F_k$ for large $M$. Finally, for every $m$ and all large $j$,
$$
\frac h{f(y)}=r_{j+1}\cdot f\!\left(\frac{x_j}{y}\right)\in E_{k+j+1}\cdot E_{m}\subseteq E_m,
$$
using (a) for the second factor. Since $E$ is separated, $h=f(y)$ (`FilteredSurj.lean:38–129`). $\square$

The archive states this lemma with a reindexing $\varphi:\mathbb N\to\mathbb N$ tending to infinity, comparing $F_n$ with $E_{\varphi(n)}$. Here $\varphi$ is the identity, which Lemma 2(ii) makes possible.

**Lemma 6 (the unit filtrations are complete and separated; `filtrationComplete_unitFiltration`, `filtrationSeparated_unitFiltration`).** [Lean, read] For a nonarchimedean local field $K$, the filtration $U_K^{(n)}$ of $\mathcal O_K^\times$ is complete and separated.

**Proof.** Separated: if $u-1\in\mathfrak m_K^n$ for all $n$, write $u-1=\varpi^m w$ with $w$ a unit if $u-1\neq0$; then $\varpi^{m+1}\mid\varpi^mw$ forces $\varpi\mid w$, impossible (`eq_zero_of_forall_mem_maximalIdeal_pow`, `LocalIndex.lean:38`). Complete: an $F$-Cauchy sequence of units is, after passing to a monotone choice of indices, a sequence in $\mathcal O_K$ that is Cauchy for the $\mathfrak m_K$-adic topology, since $x/y\in U_K^{(N)}$ means $x-y\in\mathfrak m_K^N$. The ring $\mathcal O_K$ is $\mathfrak m_K$-adically complete, so there is a limit $\Lambda\in\mathcal O_K$. Its residue agrees with that of the terms, which are units, so $\Lambda$ is a unit, and $x_n/\Lambda\in U_K^{(N)}$ for large $n$ (`LocalIndex.lean:57–89`). $\square$

**Theorem A (unit norms are onto in unramified extensions; `normIntegerUnits_surjective`, `map_normIntegerUnits_unitFiltration`).** [Lean, read; the finite-field norm and trace surjectivities are Mathlib inputs [Lean]] Let $L/K$ be a finite unramified extension of nonarchimedean local fields. Then for every $n\ge0$,
$$
N_{L/K}\bigl(U_L^{(n)}\bigr)=U_K^{(n)} .
$$
In particular $N_{L/K}:\mathcal O_L^\times\to\mathcal O_K^\times$ is onto.

**Proof.** Apply Lemma 5 with $G=\mathcal O_L^\times$, $H=\mathcal O_K^\times$, $F_n=U_L^{(n)}$, $E_n=U_K^{(n)}$, $f=N$ and $\varphi=\mathrm{id}$. Both filtrations are decreasing (`unitFiltration_antitone`); $F$ is complete and $E$ is separated by Lemma 6. Condition (a) is Lemma 2(iii). Condition (b) at level $0$ is Lemma 4(i), since $U_L^{(0)}$ is the whole unit group, and at level $n\ge1$ it is Lemma 4(ii) (`UnramifiedNormSurj.lean:170–180`). Taking $k=n$ gives the displayed equality, and $k=0$ with $U^{(0)}=\mathcal O^\times$ gives surjectivity (`:182–190`). $\square$

The archive also records the consequence in the multiplicative groups: the image of $U_L^{(n)}$ in $K^\times$ under the field norm is $U_K^{(n)}$ (`map_normUnits_unitFiltrationUnits`, `:192–198`), so $\mathcal O_K^\times\subseteq\mathrm{Nm}(L^\times)$ (`:200–203`).

**Proposition B (transfer to completions of a number field; `exists_norm_eq_of_ramificationIdx_eq_one`).** [Lean, read] Let $L/K$ be a finite extension of number fields, $v$ a nonzero prime of $\mathcal O_K$ and $w$ a prime of $\mathcal O_L$ over $v$ with ramification index $e(w\mid v)=1$ in the sense of Dedekind domains. Then for every unit $u$ of the valuation ring of the completion $K_v$ there is a unit $y$ of the valuation ring of $L_w$ with $\mathrm{Nm}_{L_w/K_v}(y)=u$.

**Proof.** The ramification index of the completed extension $L_w/K_v$, defined through the maximal ideals of the valuation rings, equals $e(w\mid v)$ (`ramificationIdx_integer`, `src/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean:240–258`). The proof compares, for each $n$, the condition $\mathfrak m_{K_v}\mathcal O_{L_w}\subseteq\mathfrak m_{L_w}^{\,n}$ with $n\le e(w\mid v)$ by evaluating the valuation of a uniformizer of $K_v$ in $L_w$, where the completed valuations restrict to the global ones (`valued_algebraMap_adicCompletion'`, `valued_of_irreducible_integer` [Lean]). So $L_w/K_v$ is unramified in the sense of the definitions above. Mathlib gives both completions the local-field class, and the inclusion of valuation rings is a `ValuativeExtension`. Theorem A applied to $u$, viewed as a unit of the valuation ring of $K_v$, gives a unit $g$ of the valuation ring of $L_w$ with $N(g)=u$; pushing $g$ into $L_w^\times$ (`unitsIncl`) gives $y$ (`LocalNormGroups.lean:122–142`). $\square$

**Proposition C (local units are local norms at an unramified place; `map_integerUnitsOver_eq_of_ramificationIdx_eq_one`).** [Lean, read] With $L/K$, $v$ as in Proposition B, let $\mathrm{Nm}_v:\prod_{w\mid v}L_w^\times\to K_v^\times$ be the product of the local norms (`finiteLocalNorm`, `src/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean:19`) and let $\mathcal U_v=\prod_{w\mid v}\mathcal O_{L_w}^\times$ (`integerUnitsOver`, `:34`). If some prime $w$ over $v$ has $e(w\mid v)=1$, then
$$
\mathrm{Nm}_v(\mathcal U_v)=\mathcal O_{K_v}^\times .
$$

**Proof.** The inclusion $\subseteq$ holds without any hypothesis: the norm of an integral element is integral (`norm_mem_integer`), so the norm of a tuple of integral units and of its inverse are both integral (`finiteLocalNorm_mem_integers`, `map_integerUnitsOver_le`, `LocalNormGroups.lean:86–101`). For $\supseteq$, let $u\in\mathcal O_{K_v}^\times$. Proposition B at the given $w$ gives a unit $y$ of $\mathcal O_{L_w}$ with $\mathrm{Nm}_{L_w/K_v}(y)=u$. Put $y$ at the coordinate $w$ and $1$ at every other prime over $v$ (`Pi.mulSingle`). The tuple lies in $\mathcal U_v$, and the product of local norms collapses to the single factor $\mathrm{Nm}_{L_w/K_v}(y)=u$ (`finiteLocalNorm_mulSingle`, `LocalNormGroups.lean:20–27`; `LocalNormsEverywhere.lean:28–43`). $\square$

One unramified prime above $v$ suffices; the other primes over $v$ may ramify. The consumer `locFin` has every prime over $v$ unramified, since hypothesis (U) of §11.4.3.4 is `UnrFin K`, the statement that $e(w\mid v)=1$ for all $w$.

**Corollary D (almost all places; `eventually_ramificationIdx_eq_one`, `eventually_map_integerUnitsOver_eq`).** [Lean, read; the different-ideal criterion is a Mathlib input [Lean]] For all but finitely many primes $v$ of $\mathcal O_K$, $\mathrm{Nm}_v(\mathcal U_v)=\mathcal O_{K_v}^\times$.

**Proof.** A prime $w$ of $\mathcal O_L$ with $e(w\mid v)>1$ divides the different ideal of $\mathcal O_L/\mathcal O_K$ (Mathlib's `not_dvd_differentIdeal_iff` and `Ideal.ramificationIdx_eq_one`), which is nonzero and so has finitely many prime factors (`LocalNormsEverywhere.lean:18–26`). Hence $e(w\mid v)=1$ for all but finitely many $w$, so for all but finitely many $v$ every $w$ over $v$ is unramified (`eventually_forall_placesOver`, `LocalNorms.lean:95` [Lean]). Each such $v$ has at least one prime above it (`nonempty_placesOver` [Lean]), and Proposition C applies (`LocalNormsEverywhere.lean:47–54`). $\square$

**Wiring to the consumers.** [Lean, read for the two deductions; `mem_range_ideleNorm_iff` is read in §11.4.3.6] The idelic criterion `mem_range_ideleNorm_iff` (`LocalNorms.lean:194`) says that an idele $x$ of $K$ is the norm of an idele of $L$ if and only if three conditions hold: each finite component $x_v$ is in the image of $\mathrm{Nm}_v$; each infinite component is a local norm; and for all but finitely many $v$ the component $x_v$ is in $\mathrm{Nm}_v(\mathcal U_v)$. The third condition is the restricted-product condition. The preimages must be integral units almost everywhere, or they do not form an idele. The archive removes it in `mem_range_ideleNorm_iff_forall` (`LocalNormsEverywhere.lean:58–67`): an idele has unit components at almost all places (`eventually_finiteProj_mem`, `LocalNorms.lean:83` [Lean]), and by Corollary D those components are norms of integral units at almost all places. So the local conditions at all places already imply the idelic one. This is the form used at `HasseNorm.lean:56–62` (and through it at `:98–105`) and hence in Proposition C of §11.4.3.4.

The second consumer is `locFin` (`GL/FerreroWashingtonIndex/LocFin.lean:47–92`, read in §11.4.3.4). After the ideal step, it has a global norm $n=\mathrm{Nm}_{K/K^+}(b)$ and the element $nx^{-1}=t$, which is a $v$-adic unit. The step `h2` rewrites the image of $\mathcal U_v$ under $\mathrm{Nm}_v$ as $\mathcal O_{K^+_v}^\times$ by Proposition C, with the prime $w$ chosen by `nonempty_placesOver` and the hypothesis `hunr w.1`, which is (U) at $w$. Then $t$ is a local norm, so $x=n\,t^{-1}$ is one. This closes the local-norm input named in Lemma B.

**Remarks.** [Expository] *What each hypothesis pays for.* The local-field class supplies a discrete valuation ring with a uniformizer, which is what makes the unit filtration a filtration by the powers of one element and gives the uniform expansion of Lemma 2; a finite residue field, which gives the norm surjectivity of Lemma 3(i) by counting and makes separability automatic in Lemma 3(ii); and completeness of $\mathcal O_L$, used once, in Lemma 6 for the limit of Lemma 5. Separatedness is used on the $K$ side and completeness on the $L$ side. The ramification index $1$ is used twice: in the dimension count of Lemma 1, where it identifies the residue extension with the whole extension, and in Lemma 2(ii), where it keeps one uniformizer for both fields so that the filtrations match level by level. Residue separability enters only through the trace. In a general complete discretely valued field with imperfect residue field, an unramified extension in the sense $e=1$ with inseparable residue extension would have zero trace on residue fields, and Lemma 4(ii) would have nothing to lift with. The archive avoids this case because the residue fields are finite.

*The full norm group.* [Lean] The archive goes on to compute $K^\times/\mathrm{Nm}(L^\times)$ in the unramified case: $\mathrm{ord}(\mathrm{Nm}\,x)=f\cdot\mathrm{ord}(x)$ (`ord_norm`, `ExistsUnitFiltrationUnitsLeRangeNormUnits.lean:195`), so an element is a norm if and only if $[L:K]$ divides its order (`mem_range_normUnits_iff`, `UnramifiedNormSurj.lean:235`), the quotient is cyclic of order $[L:K]$ generated by a uniformizer (`index_range_normUnits`, `isCyclic_quotient_range_normUnits`, `:269–297`). These are the statements that local class field theory recovers from the reciprocity map; here they are proved directly from Theorem A. They are not used by `locFin`, which only needs units.

*Comparison with the cohomological account.* [Paper] Milne proves Proposition 1.2 exactly by the two surjectivities and the iteration, and then uses it to show $\widehat H^0(G,U_L)=0$ and, with Hilbert 90, that all Tate cohomology of $U_L$ vanishes for unramified $L/K$ (Proposition 1.1, p. 97). The archive uses Theorem A only in the two consumers above and does not pass through the cohomology of $U_L$ on this route.

*The ramified case is genuinely different.* Example 3 has $[U_K:N(U_L)]=2$. In general the index of the unit norms in a totally ramified extension of degree $e$ measures ramification, and the Hasse norm route of §11.4.3.4 needs hypothesis (U) precisely so that these local obstructions do not appear at finite places.

**Reading boundary and source map.** Read in full here [Lean, read]: `map_integerUnitsOver_eq_of_ramificationIdx_eq_one`, `eventually_ramificationIdx_eq_one`, `eventually_map_integerUnitsOver_eq`, the deduction `mem_range_ideleNorm_iff_forall` from `mem_range_ideleNorm_iff`; `exists_norm_eq_of_ramificationIdx_eq_one`, `finiteLocalNorm_mulSingle`, `finiteLocalNorm_mem_integers`, `map_integerUnitsOver_le`; `normIntegerUnits_surjective`, `map_normIntegerUnits_unitFiltration`, `exists_normIntegerUnits_div_mem_one`, `exists_normIntegerUnits_div_mem_succ`, `normIntegerUnits_mem_unitFiltration`, `trace_integer_surjective`, `irreducible_algebraMap_of_isUnramified`, `residue_norm`, `residue_trace`, `residueBasis` with `residue_eq_sum_repr` and `leftMulMatrix_residueBasis`, `exists_norm_one_add_smul`; `map_eq_of_graded_surjective`; `filtrationComplete_unitFiltration`, `filtrationSeparated_unitFiltration`, `div_mem_unitFiltration_iff`; `unitFiltration` with `unitFiltration_zero`, `unitFiltration_antitone`, `unitsToResidue_surjective`, `ker_unitsToResidue`, `isUnit_one_add_mul`; `ramificationIdx_integer`; `IsUnramified` with `isUnramified_iff_finrank_residueField`, `ramificationIndex_mul_residueDegree` and `map_maximalIdeal`; and the definitions `finiteLocalNorm`, `integerUnitsOver`, `normIntegerUnits`, `normUnits`, `unitsIncl`. Named inputs not read here [Lean] (the first four are read in §11.4.3.6): `mem_range_ideleNorm_iff`, `eventually_finiteProj_mem`, `eventually_forall_placesOver`, `nonempty_placesOver`, `finrank_integer`, `ord_norm` and the norm-group statements of the second remark, `valued_algebraMap_adicCompletion'`, `valued_of_irreducible_integer`, the instance inputs of `isAdicComplete_integer`, and the Mathlib declarations `FiniteField.unitsMap_norm_surjective` (`Mathlib/FieldTheory/Finite/GaloisField.lean:236`), `Algebra.trace_surjective` (`Mathlib/RingTheory/Trace/Basic.lean:521`), `Matrix.det_one_add_smul`, `basisOfTopLeSpanOfCardEqFinrank`, `Module.Free.chooseBasis`, `not_dvd_differentIdeal_iff`, `Ideal.ramificationIdx_eq_one`, `Ideal.sum_ramification_inertia_eq_finrank` and the `IsNonarchimedeanLocalField` instances on completions. The Hasse norm theorem's cohomological input `natCard_cycTateNegOne_ideleClassGroup` and the cyclotomic inertia inputs of Lemma G in §11.4.3.4 are not touched. The reading status of the rest of the Ferrero–Washington dependency cone remains as in §11.4.3.

| Source and lines | Role and reading |
|---|---|
| `GT/IdeleGroups/LocalNormsEverywhere.lean:18–26,28–43,47–54,58–67` | [Lean, read] Different-ideal finiteness, Proposition C, Corollary D and the idelic deduction. |
| `GT/IdeleGroups/LocalNormGroups.lean:20–27,86–101,122–142` | [Lean, read] Single-coordinate norm, integrality of unit norms, Proposition B. |
| `GT/IdeleGroups/LocalNorms.lean:19–45` | [Lean, read] Definitions of the product local norm and the integral units; `:83,95,194` read in §11.4.3.6. |
| `GT/CompletionAtPlace/Integers.lean:240–258` | [Lean, read] Global and completed ramification indices agree. |
| `LF/UnramifiedNormSurj.lean:22–190` | [Lean, read] Lemmas 1–4 and Theorem A; `:192–203` the multiplicative-group consequences; `:207–297` [Lean] the norm-group remark. |
| `LF/FilteredSurj.lean:12–27,38–129` | [Lean, read] Filtration vocabulary and Lemma 5. |
| `GT/KummerTheory/LocalIndex.lean:25–89` | [Lean, read] Lemma 6 and the quotient criterion. |
| `LF/UnitsBasic.lean:12–40,144,164–165,275–290,321–326` | [Lean, read] Unit filtration, `ord`, `unitsIncl`, residue map, units of the form $1+\varpi^na$. |
| `LF/UnramifiedDefs.lean:11–56`, `LF/Integers.lean:16–18,88,123–146` | [Lean, read] Unramified definition and its equivalents; $ef=[L:K]$; $\mathfrak m_K\mathcal O_L=\mathfrak m_L^{\,e}$. |
| `LF/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean:20–24,123–126` | [Lean, read] Definitions of the field and integral unit norms; `:195` [Lean] named. |
| Mathlib `0df444a`: `Mathlib/FieldTheory/Finite/GaloisField.lean:236`, `Mathlib/RingTheory/Trace/Basic.lean:521` | [Lean] Statements checked against the pinned source; proofs not read. |

Here `GT/` expands to `src/GroundTheory/GlobalFields/` and `LF/` to `src/GroundTheory/LocalFields/`.

#### 11.4.3.6 The idelic norm as a restricted product: from local norms to one idele

**Motivation.** The Hasse norm theorem of §11.4.3.4 (Proposition C there, `HasseNorm.lean:56–62`) and the local-norm lemma `locFin` both speak about the norm of a *single* idele. The place-by-place description `mem_range_ideleNorm_iff_forall` was read in §11.4.3.5 down to the criterion `mem_range_ideleNorm_iff` (`src/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean:194`), which was left as a named input. That criterion is the content of this subsection. It says that an idele $x$ of $K$ is the norm of an idele of $L$ if and only if every finite component is a product of local norms over the primes above it, every infinite component is a product of local norms over the infinite places above it, and, at almost all finite places, the component is the norm of a tuple of local *units*. The third condition is the restricted-product condition. It is the only place where the idele structure, rather than the family of all local norm groups, enters. The proof has a formal half, in which the components of the norm of an idele are computed as products of local norms, and a selection half, in which local preimages are chosen at every place in such a way that they are integral units almost everywhere and are then glued into one idele of $L$. The second half is where the order of the choices matters. The subsection reads `mem_range_ideleNorm_iff` with its producers `mem_range_ideleNorm`, `glue`, `ideleNorm_glue`, `finiteProj_ideleNorm`, `eventually_finiteProj_mem` and `eventually_forall_placesOver`, the component formulas `ideleNorm_snd` and `ideleNorm_fst` with their matrix inputs `norm_map_of_repr` and `norm_pi`, and the restricted-product description of the idele group `prodRestrictedEquiv`. It gives two complete local-to-idelic calculations for $\mathbb Q(i)/\mathbb Q$, one centred at a split odd prime and one at an inert odd prime, and a counter-control showing that an arbitrary coordinatewise choice of preimages need not be an idele. The classical statements are Milne's definition of the idelic norm by local components [MilneCFT, Ch. V, §4, "Norms of idèles", pp. 176–177](https://www.jmilne.org/math/CourseNotes/CFT.pdf) and Neukirch's Proposition (2.2) [Neukirch1999, Ch. VI, §2, pp. 370–371]. The cohomological input of the Hasse norm theorem (`natCard_cycTateNegOne_ideleClassGroup`, the second inequality) is not touched. Source references are to the joined archive with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` and to Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. [Lean, read]

**Example 1 (the place inventory of $\mathbb Q(i)/\mathbb Q$).** [Expository] Let $K=\mathbb Q$ and $L=\mathbb Q(i)$. For an idele $x=(x_v)$ of $\mathbb Q$ the criterion below asks, place by place, whether $x_v$ is a product of local norms, so we first record the local norm groups. Write $\mathrm{Nm}_v$ for the product of the local norms over the primes $w$ of $L$ above $v$, and $\mathcal U_v=\prod_{w\mid v}\mathcal O_{L_w}^\times$.

- *Split odd primes, $p\equiv1\bmod4$.* Two primes $w_1,w_2$ lie over $p$, and $L_{w_j}\cong\mathbb Q_p$ since $X^2+1$ splits over $\mathbb Q_p$. The local norm of $\mathbb Q_p/\mathbb Q_p$ is the identity, so $\mathrm{Nm}_p(y_1,y_2)=y_1y_2$. Every $x_p\in\mathbb Q_p^\times$ is a product of local norms, and $\mathrm{Nm}_p(\mathcal U_p)=\mathbb Z_p^\times$.
- *Inert odd primes, $p\equiv3\bmod4$.* One prime $w=(p)$ lies over $p$, and $L_w=\mathbb Q_p(i)$ is the unramified quadratic extension with $\mathrm{Nm}(a+bi)=a^2+b^2$. By Theorem A of §11.4.3.5 every unit of $\mathbb Z_p$ is the norm of a unit, and $\mathrm{ord}_p(\mathrm{Nm}\,y)=2\,\mathrm{ord}_w(y)$ (`ord_norm`, named in §11.4.3.5). So $x_p$ is a local norm if and only if $\mathrm{ord}_p(x_p)$ is even, and $\mathrm{Nm}_p(\mathcal U_p)=\mathbb Z_p^\times$.
- *The ramified prime $2$.* One prime $(1+i)$ lies over $2$, and $L_w=\mathbb Q_2(i)$ is ramified. An element $a+bi\in\mathbb Z_2[i]$ is a unit exactly when $a+b$ is odd, and then $a^2+b^2\equiv1$ or $5\bmod8$. So $\mathrm{Nm}(\mathcal O_{L_w}^\times)\subseteq1+4\mathbb Z_2$, a subgroup of index $2$ in $\mathbb Z_2^\times$, and $2=\mathrm{Nm}(1+i)$ is a norm. The norm group of $\mathbb Q_2(i)/\mathbb Q_2$ is $\{2^k u:\ u\equiv1\bmod4\}$, since $x$ is a norm from $\mathbb Q_2(\sqrt{-1})$ exactly when the Hilbert symbol $(-1,x)_2$ is $1$, and Serre's formula gives $(-1,2^ku)_2=(-1)^{\varepsilon(u)}$ with $\varepsilon(u)=(u-1)/2\bmod2$ [Paper] [Serre1973, Ch. III, §1.2, Theorem 1, p. 20]. Here $3$, $7$ and $-1$ are not local norms.
- *The infinite place.* Over the real place of $\mathbb Q$ lies the single complex place of $L$, with completion $\mathbb C$ and $\mathrm{Nm}(z)=z\bar z=\lvert z\rvert^2$. So $x_\infty$ is a local norm exactly when $x_\infty>0$.

Theorem A below therefore says: an idele $x$ of $\mathbb Q$ is the norm of an idele of $\mathbb Q(i)$ if and only if $x_\infty>0$, $x_2=2^ku$ with $u\equiv1\bmod4$, and $\mathrm{ord}_p(x_p)$ is even for every $p\equiv3\bmod4$. No condition is imposed at $p\equiv1\bmod4$, and the restricted-product condition is satisfied automatically: at almost all $p$ the component $x_p$ is a unit, and a unit is the norm of a tuple of units at every odd $p$, by the two bullets above. This is the content of Corollary D of §11.4.3.5 in this example.

**Example 2 (a split odd prime: from one local preimage to the idele).** [Expository] Keep $K=\mathbb Q$, $L=\mathbb Q(i)$, and let $x$ be the idele with $x_5=2$ and every other component, finite and infinite, equal to $1$. The primes over $5$ are $w_1=(2+i)$ and $w_2=(2-i)$. In $\mathbb Q_5$ the equation $\iota^2=-1$ has the two solutions $\iota\equiv57$ and $\iota\equiv68\bmod125$ (indeed $57^2=3249=26\cdot125-1$). Since $i\equiv-2\equiv3\bmod w_1$ and $i\equiv2\bmod w_2$, the completions are identified with $\mathbb Q_5$ by $i\mapsto68+O(5^3)$ at $w_1$ and $i\mapsto57+O(5^3)$ at $w_2$. The place-$5$ data of a tuple $(y_{w_1},y_{w_2})\in\mathbb Q_5^\times\times\mathbb Q_5^\times$ has norm $\mathrm{Nm}_5(y)=y_{w_1}y_{w_2}$. The equation $\mathrm{Nm}_5(y)=2$ has many solutions:
$$
(2,1),\qquad(1,2),\qquad\bigl((1+i)_{w_1},(1+i)_{w_2}\bigr)=(69,58)+O(5^3),\qquad(10,\tfrac15).
$$
The first three lie in $\mathcal U_5=\mathbb Z_5^\times\times\mathbb Z_5^\times$, the fourth does not. For the third, $69\cdot58=4002=2+32\cdot125$, which checks $\mathrm{Nm}_5$ of the diagonal image of $1+i$, namely $\prod_{w\mid5}(1+i)_w=\mathrm N_{L/K}(1+i)=2$, place by place. The tuple is the image of the global element $1+i$ under the two embeddings; the conjugate $1-i$ has coordinates $(58,69)$, and mixing one coordinate of each, as in $(69,69)$, gives $11\bmod125$, not $2$. At every other finite $v$ and at the infinite place the component $x_v=1$ has the preimage $1$ at each $w\mid v$. The proof of Theorem A selects, at $v=5$, some tuple in $\mathcal U_5$ with norm $2$, say $(2,1)$, and the tuple $1$ everywhere else; here the "almost all places" set of condition (iii) is all finite places. Lemma 4 glues these into the idele $y$ of $L$ with $y_{w_1}=2$ and $y_w=1$ for all other $w$, finite and infinite. Lemma 1 confirms $\mathrm{Nm}(y)=x$: at $v=5$ the component is $2\cdot1$, elsewhere it is $1$. The idele $x$ is not the diagonal image of a rational number, so no global $\beta$ with $\mathrm{Nm}(\beta)=x$ exists, and none is claimed. Compare the diagonal idele of $2$. By Example 1 it is a norm idele: $2=\mathrm{Nm}(1+i)$ at $v=2$ with the non-unit preimage $1+i$, $\mathrm{ord}_p(2)=0$ at inert $p$, $2>0$ at infinity, and no condition at split $p$. The global preimage $1+i$ supplies a preimage at every place at once, and at $v=5$ it is the third tuple above.

**Example 3 (an inert odd prime: from one local preimage to the idele).** [Expository] Let $x$ be the idele of $\mathbb Q$ with $x_3=-2$, $x_2=5$, $x_\infty=2$ and all other components $1$. At $v=3$ the single prime $w=(3)$ has $L_w=\mathbb Q_3(i)$. The component $-2$ is a unit of $\mathbb Z_3$, so Theorem A of §11.4.3.5 gives a unit $y_w$ with $\mathrm{Nm}(y_w)=-2$; Example 2 of that subsection computed one such limit step by step. Here one can also take the $3$-adic square root $y_w=\sqrt{-2}=22+O(3^5)\in\mathbb Z_3\subset L_w$, since $22^2+2=486=2\cdot3^5$ and $\mathrm{Nm}(y)=y^2$ for $y\in\mathbb Q_3$. At an inert place every preimage of a unit is a unit, because $\mathrm{ord}_3(\mathrm{Nm}\,y)=2\,\mathrm{ord}_w(y)$: the integrality demanded by condition (iii) is forced, not chosen. At $v=2$ the component $5\equiv1\bmod4$ is a norm, $5=\mathrm{Nm}(2+i)$, and $2+i$ is a unit of $\mathbb Z_2[i]$ since $2+1$ is odd. At $v=\infty$ the component $2>0$ is $\lvert1+i\rvert^2=\mathrm{Nm}(1+i)$ with $1+i\in\mathbb C$. Lemma 4 glues $y_{(3)}=\sqrt{-2}$, $y_{(1+i)}=2+i$, $y_\infty=1+i$ and $y_w=1$ elsewhere into an idele $y$ of $\mathbb Q(i)$, and Lemma 1 gives $\mathrm{Nm}(y)=x$ component by component. Now change one component: let $x'$ have $x'_3=-6$ and agree with $x$ elsewhere. Then $\mathrm{ord}_3(x'_3)=1$ is odd, so $x'_3$ is not a local norm, condition (i) of Theorem A fails at $v=3$, and $x'$ is not the norm of any idele. A diagonal idele cannot fail at exactly one place. For a rational $a\neq0$ the number of places at which $a$ is not a norm from $\mathbb Q(i)$ is even, because this number counts the $v$ with Hilbert symbol $(-1,a)_v=-1$ and the product of all these symbols is $1$ [Paper] [Serre1973, Ch. III, §2.1, Theorem 3, p. 23]. Thus $3$ fails at $2$ and at $3$, $7$ fails at $2$ and at $7$, $21$ fails at $3$ and at $7$ but not at $2$ since $21\equiv1\bmod4$, and $-1$ fails at $2$ and at $\infty$. The idele $x'$, which fails at one place only, is far from diagonal.

**Example 4 (a coordinatewise choice that is not an idele).** [Expository] Take $x=1$, the identity idele of $\mathbb Q$. At each split prime $p\equiv1\bmod4$ the tuple $(p,p^{-1})\in\mathbb Q_p^\times\times\mathbb Q_p^\times$ satisfies $\mathrm{Nm}_p(p,p^{-1})=1$, so it is a legitimate preimage of $x_p$ under $\mathrm{Nm}_p$. Choose it at every split prime and the tuple $1$ at every other place. The resulting family $(y_w)_w$ has $y_w\notin\mathcal O_{L_w}$ at one of the two primes over each $p\equiv1\bmod4$, and there are infinitely many such $p$. It is therefore not an element of the restricted product and does not define an idele of $L$, although it solves the norm equation at every place. The identity idele is of course a norm, namely of the identity. The example shows that the restricted-product condition (iii) of Theorem A is a condition on how the preimages are *selected*, and that the selection must prefer integral preimages wherever they exist. At inert places no such care is needed (Example 3), and at a place with several primes above it the valuations of non-unit coordinates can cancel. At a single prime above, a preimage of a unit has valuation zero.

**Definitions.** [Lean, read] Let $L/K$ be a finite extension of number fields. The archive's adele ring $\mathbb A_K$ is Mathlib's: the product of the infinite adele ring $\prod_{v\mid\infty}K_v$ with the finite adele ring $\mathbb A_{K,f}=\prod'_v[K_v,\mathcal O_v]$, the restricted product of the completions $K_v$ at the nonzero primes $v$ of $\mathcal O_K$ (Mathlib's `HeightOneSpectrum`) with respect to the valuation rings $\mathcal O_v$ and the cofinite filter. The *idele group* is $I_K=\mathbb A_K^\times$ (`IdeleGroup`, `src/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean:12`). For a finite place $v$, $\mathrm{pr}_v:I_K\to K_v^\times$ is the units map of the evaluation at $v$ of the finite part (`finiteProj`, `:144–148`), with $\mathrm{pr}_v(x)=x_v$ as elements of $K_v$ (`coe_finiteProj`, `:157–159`); for an infinite place $w$, $\mathrm{pr}_w:I_K\to K_w^\times$ is the analogous evaluation (`infiniteProj`, `:213–216`). The *diagonal* $\Delta:K^\times\to I_K$ is the units map of the algebra map (`diagonal`, `:51–52`), and $\mathrm{pr}_v(\Delta a)$ is the image of $a$ in $K_v$ (`coe_finiteProj_diagonal`, `:181–184`).

The idele group is a restricted product of units. Mathlib's `RestrictedProduct.unitsEquiv` (`Mathlib/Topology/Algebra/RestrictedProduct/Units.lean:84`) identifies the units of $\prod'_v[K_v,\mathcal O_v]$ with $\prod'_v[K_v^\times,\mathcal O_v^\times]$: a unit $x$ of the restricted product has $x$ and $x^{-1}$ integral at almost all $v$, hence $x_v\in\mathcal O_v^\times$ at almost all $v$ (`coeUnits`, `:68`), and conversely a family $(x_v)\in\prod_vK_v^\times$ with $x_v\in\mathcal O_v^\times$ almost everywhere is a unit of the restricted product (`mkUnit`, `:74–79`); the two maps are inverse by reflexivity. Together with `MulEquiv.piUnits` (`Mathlib/Algebra/Group/Pi/Units.lean:25`), which identifies units of a product with the product of the units, and with the identification $(\mathbb A_K)^\times\cong(\prod_{v\mid\infty}K_v)^\times\times(\mathbb A_{K,f})^\times$ (`prodEquiv`, `InfiniteProjInfiniteEmbeddingOfNe.lean:23–29`), the archive obtains
$$
I_K\;\cong\;\Bigl(\prod_{v\mid\infty}K_v\Bigr)^\times\times\prod'_v\bigl[K_v^\times,\ \mathcal O_v^\times\bigr]
$$
as topological groups (`prodRestrictedEquiv`, `src/GroundTheory/GlobalFields/IdeleGroups/Restricted.lean:97–105`; the continuity of `unitsEquiv` on the finite part is `continuous_unitsEquiv`, `:31–59`, read at the statement level). Its two components are the infinite part and the finite components of $x$ (`prodRestrictedEquiv_apply_fst`, `_snd`, `:108–116`).

For a finite place $v$ of $K$ let $P_v=\{w\mid v\}$ be the set of primes of $\mathcal O_L$ lying over $v$ (`PlacesOver`, `src/GroundTheory/GlobalFields/SemilocalAlgebras/ContinuousCompletionMap.lean:15–16`). It is finite, in bijection with the primes of $\mathcal O_L$ over $v\mathcal O_L$ (`placesOverEquiv`, `:23–31`), and nonempty, because the local degrees $[L_w:K_v]$ for $w\in P_v$ sum to $[L:K]>0$ (`nonempty_placesOver`, `src/GroundTheory/GlobalFields/KummerTheory/Splitting.lean:82–87`, with `sum_finrank_eq` named). The map $w\mapsto w\cap\mathcal O_K$ from primes of $L$ to primes of $K$ is `below` (`src/GroundTheory/GlobalFields/Adele/BaseChange/FiniteMap.lean:20–23`), and $\mathrm{below}(w)=v$ exactly when $w$ lies over $v$ (`below_eq_iff`, `:31–37`). For infinite places, $w\mid v$ means that $w$ restricts to $v$ (`InfinitePlace.placesOver`).

The *local norm at $v$* is the homomorphism
$$
\mathrm{Nm}_v:\ \prod_{w\in P_v}L_w^\times\longrightarrow K_v^\times,\qquad \mathrm{Nm}_v(y)=\prod_{w\in P_v}\mathrm{Nm}_{L_w/K_v}(y_w)
$$
(`finiteLocalNorm`, `LocalNorms.lean:19–24`, `coe_finiteLocalNorm`, `:28–32`), and $\mathcal U_v=\prod_{w\in P_v}\mathcal O_{L_w}^\times$ is the subgroup of tuples of integral units (`integerUnitsOver`, `mem_integerUnitsOver`, `:34–45`). At an infinite place $v$ the local norm $\mathrm{Nm}_v:\prod_{w\mid v}L_w^\times\to K_v^\times$ is defined in the same way (`infiniteLocalNorm`, `:49–54`). The *idelic norm* is the units map of the algebra norm of $\mathbb A_L$ over $\mathbb A_K$,
$$
\mathrm{Nm}=\mathrm{Nm}_{L/K}:\ I_L\longrightarrow I_K,\qquad \mathrm{Nm}(y)=\mathrm{Nm}_{\mathbb A_L/\mathbb A_K}(y)
$$
(`ideleNorm`, `src/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean:170–176`). This makes sense because $\mathbb A_L\cong\mathbb A_K\otimes_KL$ is a free $\mathbb A_K$-module with basis the image of any $K$-basis $b$ of $L$ (`adeleBasis`, `:51–52`; the identification `adeleTensorEquiv` is a named input), and the coordinates of $y\in\mathbb A_L$ in this basis are the coordinate functions `coord` (`adeleBasis_repr`, `:60–68`). On diagonal ideles the idelic norm is the diagonal of the field norm (`ideleNorm_diagonal`, `:181–184`, from `norm_adeleRing_algebraMap`, `:109`).

**Lemma 1 (components of the norm of an idele; `ideleNorm_snd`, `ideleNorm_fst`, `finiteProj_ideleNorm`, `infiniteProj_ideleNorm`).** [Lean, read; the semilocal decomposition `tensorEquiv` is a named input] For $y\in I_L$ and a finite place $v$ of $K$,
$$
\mathrm{pr}_v(\mathrm{Nm}\,y)=\mathrm{Nm}_v\bigl((y_w)_{w\in P_v}\bigr)=\prod_{w\in P_v}\mathrm{Nm}_{L_w/K_v}(y_w),
$$
and likewise $\mathrm{pr}_v(\mathrm{Nm}\,y)=\prod_{w\mid v}\mathrm{Nm}_{L_w/K_v}(y_w)$ at an infinite place $v$.

**Proof.** Fix a finite $v$. Evaluation at $v$ is a ring homomorphism $\mathrm{ev}_v:\mathbb A_K\to K_v$ (`finiteEval`, `src/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/CompletionsOverBasisRepr.lean:20–25`), and restriction to the primes over $v$ is a ring homomorphism $\mathrm{res}_v:\mathbb A_L\to C_v:=\prod_{w\in P_v}L_w$ (`finiteRestrict`, `:29–34`). The archive's semilocal theorem $K_v\otimes_KL\cong C_v$ as $K_v$-algebras (`tensorEquiv`, `src/GroundTheory/GlobalFields/SemilocalAlgebras/Finite.lean:82–83`, named) transports the $K_v$-basis $1\otimes b$ to a $K_v$-basis $b_v$ of $C_v$ (`completionsOverBasis`, `:38–40`) whose coordinate functions are the local coordinates `localCoord` (`:43–45`). The two coordinate systems are compatible: the $i$-th coordinate of $\mathrm{res}_v(y)$ in $b_v$ equals $\mathrm{ev}_v$ of the $i$-th coordinate of $y$ in the adelic basis, by unfolding both sides to the same function (`:51–54`, closed by `rfl`). Now the general matrix lemma `norm_map_of_repr` (`IdeleNorms/BaseChange.lean:17–27`) says: if $\varphi:A\to A'$ and $\psi:B\to B'$ are ring homomorphisms between algebras with bases $b,b'$ indexed by the same finite set, and $b'$-coordinates of $\psi(y)$ are $\varphi$ of $b$-coordinates of $y$, then $\mathrm{Nm}_{A'}(\psi y)=\varphi(\mathrm{Nm}_Ay)$. Indeed $\psi(b_j)=b'_j$ follows by comparing coordinates, the matrix of multiplication by $\psi(y)$ in $b'$ is the entrywise image under $\varphi$ of the matrix of multiplication by $y$ in $b$ (`Algebra.leftMulMatrix_eq_repr_mul`), and the determinant commutes with ring homomorphisms (`RingHom.map_det`). Applied with $\varphi=\mathrm{ev}_v$, $\psi=\mathrm{res}_v$, this gives $\mathrm{ev}_v(\mathrm{Nm}_{\mathbb A_L/\mathbb A_K}y)=\mathrm{Nm}_{C_v/K_v}(\mathrm{res}_vy)$ (`finiteEval_norm`, `:47–54`). Finally, for a finite product of finite-dimensional algebras $S_i$ over a field $R$, the norm of $(s_i)$ is $\prod_i\mathrm{Nm}_{S_i/R}(s_i)$: in a product basis the matrix of multiplication by $(s_i)$ is block diagonal with blocks the matrices of the $s_i$ (`leftMulMatrix_pi`, `src/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean:31–40`), and the determinant of a block-diagonal matrix is the product of the determinants of the blocks (`det_blockDiagonal'`, `:12–25`, via Mathlib's block-triangular determinant), which is `norm_pi` (`:42–46`). Hence $(\mathrm{Nm}\,y)_v=\prod_{w\in P_v}\mathrm{Nm}_{L_w/K_v}(y_w)$ (`norm_adeleRing_snd`, `CompletionsOverBasisRepr.lean:56–59`; `ideleNorm_snd`, `:113–116`). Passing to units with `Units.ext` gives the statement for $\mathrm{pr}_v$ (`finiteProj_ideleNorm`, `LocalNorms.lean:68–73`). The infinite case is the same argument with the infinite evaluation and restriction maps and the infinite semilocal decomposition (`infiniteEval_norm`, `norm_adeleRing_fst`, `ideleNorm_fst`, `CompletionsOverBasisRepr.lean:63–105,120–123`; `infiniteProj_ideleNorm`, `LocalNorms.lean:75–81`). $\square$

The lemma is the archive's form of Neukirch's Proposition (2.2) [Neukirch1999, Ch. VI, §2, pp. 370–371], whose proof is the same block-diagonal determinant, and of the definition of the idelic norm in Milne [MilneCFT, Ch. V, §4, p. 176]. Milne *defines* $\mathrm{Nm}$ on ideles by the right-hand side and then checks compatibility with the field norm; the archive defines it as the algebra norm of $\mathbb A_L/\mathbb A_K$ and derives the components.

**Lemma 2 (components of an idele are integral units almost everywhere; `eventually_finiteProj_mem`).** [Lean, read] For $y\in I_L$, $y_w\in\mathcal O_{L_w}^\times$ for all but finitely many primes $w$ of $L$.

**Proof.** Under `prodRestrictedEquiv` the finite part of $y$ is an element of $\prod'_w[L_w^\times,\mathcal O_{L_w}^\times]$, whose defining property is exactly that its $w$-component lies in $\mathcal O_{L_w}^\times$ for almost all $w$. That component is $\mathrm{pr}_w(y)$ (`prodRestrictedEquiv_apply_snd`, `Units.ext`; `LocalNorms.lean:83–90`). Unwinding Mathlib's `unitsEquiv`, the reason is that $y$ and $y^{-1}$ are both integral almost everywhere, and an element of $\mathcal O_{L_w}$ whose inverse is in $\mathcal O_{L_w}$ is a unit there. $\square$

**Lemma 3 (pulling a cofinite condition down to $K$; `eventually_forall_placesOver`, `tendsto_below`).** [Lean, read] Let $P$ be a property of primes of $L$ that holds for all but finitely many $w$. Then for all but finitely many primes $v$ of $K$, $P(w)$ holds for every $w\in P_v$. Moreover, the preimage under `below` of a cofinite set of primes of $K$ is a cofinite set of primes of $L$.

**Proof.** Let $E$ be the finite set of $w$ with $\neg P(w)$. Its image $\mathrm{below}(E)$ is finite. If $v\notin\mathrm{below}(E)$ and $w\in P_v$, then $\mathrm{below}(w)=v$ by `below_eq_iff`, so $w\notin E$ (`LocalNorms.lean:95–102`). For the second statement, the fibre of `below` over $v$ is contained in the image of $P_v$ under $w\mapsto w$, a finite set; a map with finite fibres pulls cofinite sets back to cofinite sets (Mathlib's `Tendsto.cofinite_of_finite_preimage_singleton`; `FiniteMap.lean:39–42`). $\square$

**Lemma 4 (gluing local data into one idele; `glue`, `glue_snd`, `glue_fst`, `ideleNorm_glue`).** [Lean, read] Suppose given, for every finite place $v$ of $K$, a tuple $y^f(v)\in\prod_{w\in P_v}L_w^\times$ such that $y^f(v)\in\mathcal U_v$ for all but finitely many $v$, and for every infinite place $v$ a tuple $y^\infty(v)\in\prod_{w\mid v}L_w^\times$. Then there is an idele $y\in I_L$ with $y_w=y^f(v)_w$ for every finite $w\mid v$ and $y_w=y^\infty(v)_w$ for every infinite $w\mid v$. If moreover $x\in I_K$ satisfies $\mathrm{Nm}_v(y^f(v))=x_v$ for all finite $v$ and $\mathrm{Nm}_v(y^\infty(v))=x_v$ for all infinite $v$, then $\mathrm{Nm}(y)=x$.

**Proof.** Define the finite family $w\mapsto y^f(\mathrm{below}\,w)_w$, where $w$ is viewed in $P_{\mathrm{below}(w)}$ by `liesOver_below`. The set of $v$ with $y^f(v)\in\mathcal U_v$ is cofinite, so by Lemma 3 the set of $w$ with $y^f(\mathrm{below}\,w)\in\mathcal U_{\mathrm{below}(w)}$ is cofinite, and at such $w$ the $w$-component is in $\mathcal O_{L_w}^\times$ (`mem_integerUnitsOver`). Hence the family is an element of $\prod'_w[L_w^\times,\mathcal O_{L_w}^\times]$. The infinite family $w\mapsto y^\infty(w|_K)_w$ is an element of $\prod_{w\mid\infty}L_w^\times$, which `MulEquiv.piUnits.symm` turns into a unit of $\prod_{w\mid\infty}L_w$. Applying the inverse of `prodRestrictedEquiv` gives $y\in I_L$ (`LocalNorms.lean:124–133`). Its components are as prescribed: for finite $w\in P_v$, $\mathrm{below}(w)=v$, and the two ways of indexing the same tuple agree by `placesOver_congr` (`:106–112`, a `subst`), giving `glue_snd` (`:135–142`); the infinite case uses `infinitePlacesOver_congr` and `InfinitePlace.LiesOver.comap_eq` (`glue_fst`, `:144–154`). For the norm, two ideles of $K$ are equal when their underlying adeles agree in every infinite and every finite coordinate (`Units.ext`, `Prod.ext`, `FiniteAdeleRing.ext`). At a finite $v$, Lemma 1 gives $(\mathrm{Nm}\,y)_v=\prod_{w\in P_v}\mathrm{Nm}_{L_w/K_v}(y_w)=\prod_w\mathrm{Nm}_{L_w/K_v}(y^f(v)_w)=\mathrm{Nm}_v(y^f(v))=x_v$ by `glue_snd`, and similarly at infinite $v$ (`ideleNorm_glue`, `:156–169`). $\square$

**Theorem A (the idelic norm criterion; `mem_range_ideleNorm_iff`).** [Lean, read; `tensorEquiv`, `adeleTensorEquiv`, `sum_finrank_eq` and the Mathlib restricted-product interface are named inputs] Let $L/K$ be a finite extension of number fields and $x\in I_K$. Then $x\in\mathrm{Nm}(I_L)$ if and only if

(i) for every finite place $v$, $x_v\in\mathrm{Nm}_v\bigl(\prod_{w\in P_v}L_w^\times\bigr)$;

(ii) for every infinite place $v$, $x_v\in\mathrm{Nm}_v\bigl(\prod_{w\mid v}L_w^\times\bigr)$;

(iii) for all but finitely many finite places $v$, $x_v\in\mathrm{Nm}_v(\mathcal U_v)$.

**Proof.** Suppose $x=\mathrm{Nm}(y)$ with $y\in I_L$. For every finite $v$, Lemma 1 exhibits $x_v=\mathrm{Nm}_v\bigl((y_w)_{w\in P_v}\bigr)$, which is (i), and likewise (ii) at infinite places. For (iii), Lemma 2 says $y_w\in\mathcal O_{L_w}^\times$ for almost all $w$, and Lemma 3 turns this into: for almost all $v$, every $w\in P_v$ has $y_w\in\mathcal O_{L_w}^\times$, that is, $(y_w)_{w\in P_v}\in\mathcal U_v$. At such $v$, Lemma 1 shows $x_v\in\mathrm{Nm}_v(\mathcal U_v)$ (`LocalNorms.lean:200–205`).

Conversely assume (i), (ii), (iii). The choices are made in the following order (`mem_range_ideleNorm`, `:171–192`). First $x$ is fixed and the three hypotheses are in hand. Then, for each finite place $v$ separately, one of two cases is decided: either $x_v\in\mathrm{Nm}_v(\mathcal U_v)$, and then a tuple $y^f(v)\in\mathcal U_v$ with $\mathrm{Nm}_v(y^f(v))=x_v$ is chosen from that fact; or not, and then any tuple $y^f(v)$ with $\mathrm{Nm}_v(y^f(v))=x_v$ is chosen from (i). The case distinction is made by classical decidability of the membership, and both choices use the axiom of choice (`Classical.choice` through `Exists.choose`); no preimage is canonical. The function $v\mapsto y^f(v)$ so defined satisfies $\mathrm{Nm}_v(y^f(v))=x_v$ at every $v$, because each branch was chosen to (`hyf`, `:184–190`), and $y^f(v)\in\mathcal U_v$ wherever the first branch was taken (`hyf_int`, `:181–183`). Hypothesis (iii) says the first branch is taken at all but finitely many $v$, so $y^f$ is integral almost everywhere. At each infinite $v$ choose $y^\infty(v)$ from (ii). Lemma 4 now produces $y\in I_L$ with $\mathrm{Nm}(y)=x$ (`:191–192`). $\square$

Note what hypothesis (iii) does and does not do. It does not say that *every* preimage is integral almost everywhere; Example 4 shows a family of preimages of the identity idele that is integral at no split prime. It says that an integral preimage *exists* almost everywhere, and the proof uses this to prefer the integral preimage wherever one exists. The finitely many places where no integral preimage exists are harmless: a restricted product allows any finite set of exceptions. Two kinds of places can be exceptional. At a place with a single prime $w$ above it, $\mathrm{ord}_v(\mathrm{Nm}\,y)=f_w\,\mathrm{ord}_w(y)$ for every $y\in L_w^\times$, whether or not $w$ ramifies, so a unit $x_v$ has only unit preimages, and $x_v$ fails to have an integral preimage exactly when it is not a unit or when it is a unit outside $\mathrm{Nm}_v(\mathcal U_v)$, which at a ramified place may be a proper subgroup of $\mathcal O_v^\times$ (the place $2$ in Example 1). At a place with several primes above it, a unit can also have non-unit preimages, as $(10,\tfrac15)$ in Example 2; the proof prefers the integral ones. In Example 3 the components $x_2=5$ and $x_\infty=2$ are a $2$-adic unit and a positive real, and both have unit preimages; the restricted-product condition concerns finite places only and is satisfied there without exception.

**Corollary B (the restricted-product condition is automatic; `mem_range_ideleNorm_iff_forall`).** [Lean, read] For $x\in I_K$, $x\in\mathrm{Nm}(I_L)$ if and only if (i) and (ii) hold.

**Proof.** This was read in §11.4.3.5. The components $x_v$ are units for almost all $v$ (Lemma 2 for $K$ in place of $L$), and by Corollary D of §11.4.3.5 every unit of $\mathcal O_v$ lies in $\mathrm{Nm}_v(\mathcal U_v)$ for almost all $v$, which is where the unramified unit-norm theorem enters. The intersection of two cofinite sets is cofinite, so (iii) follows from the hypotheses, and Theorem A applies (`LocalNormsEverywhere.lean:58–67`). $\square$

In Example 1 the corollary reads: an idele of $\mathbb Q$ is a norm from $\mathbb Q(i)$ as soon as the conditions at $\infty$, at $2$ and at the inert primes hold. The condition at the inert primes, that $\mathrm{ord}_p(x_p)$ be even, is a condition (i), not a condition (iii): at an inert place a unit is always the norm of a unit, and it is the non-units with odd valuation that are excluded.

**Wiring to the consumers.** [Lean, read] Corollary B is used at `HasseNorm.lean:62` to rewrite "the diagonal idele of $x\in K^\times$ is a norm idele" as the two local conditions. With the cohomological step `mem_range_norm_of_diagonal_mem_range_ideleNorm` (`HasseNorm.lean:17–47`, read in §11.4.3.4; its input `natCard_cycTateNegOne_ideleClassGroup` is read in §11.4.3.7), this gives the Hasse norm theorem for cyclic extensions in the form used by Proposition C of §11.4.3.4 (`:98–105`). Lemma 1 is also consumed directly: `locFin` (`GL/FerreroWashingtonIndex/LocFin.lean:82`) rewrites $\mathrm{pr}_v(\Delta\,\mathrm{Nm}_{K/K^+}b)$ as $\mathrm{pr}_v(\mathrm{Nm}(\Delta b))$ by `ideleNorm_diagonal` and then as $\mathrm{Nm}_v\bigl((b)_{w\in P_v}\bigr)$ by `finiteProj_ideleNorm`, which is step `h1` of Lemma B of §11.4.3.4: a global norm is a local norm. Step `h2` there is Proposition C of §11.4.3.5. The reading of the local-norm route behind Proposition C of §11.4.3.4 is now complete except for the cohomological input, which §11.4.3.7 reads.

**Remarks.** [Expository] *What is formal and what is not.* Theorem A is a statement about the restricted-product structure and the compatibility of norms with products; it uses no arithmetic beyond the finiteness of $P_v$ and the finiteness of the fibres of `below`. Its hypotheses (i)–(iii) are local. The arithmetic enters in two places only: Corollary B uses the unramified unit-norm theorem of §11.4.3.5 to discard (iii), and the Hasse norm theorem uses $\widehat H^{-1}$ of the idele class group to pass from a norm idele to a norm element. Neukirch obtains Theorem A together with Corollary B in one stroke for cyclic $L/K$ from the decomposition $\widehat H^0(G,I_L)\cong\bigoplus_v\widehat H^0(G_w,L_w^\times)$, which rests on the induced-module description of the local factors and on the vanishing of the Tate groups of the unit groups at unramified places (the unramified unit theorem of §11.4.3.5); the companion statement $\widehat H^{-1}(G,I_L)=1$ is a separate conclusion of the same proposition, obtained from Hilbert 90 [Neukirch1999, Ch. VI, §3, Proposition (3.2) and the remark following it, pp. 374–375]. The archive separates the two: Theorem A has no Galois hypothesis, and the cohomology is used only for the final global step.

*On the order of choices.* The function $y^f$ in the proof of Theorem A is defined by a single `if … then … else` at each $v$, not by first choosing a finite exceptional set $S$ and then treating $v\in S$ and $v\notin S$ differently. The exceptional set is never named; hypothesis (iii) is used only once, to show that the integral branch is taken almost everywhere. This is why the glued object is an idele: Lemma 4 needs a cofinite set of places at which the chosen tuple is integral, and gets it from (iii) through the `mono` of a filter statement, not from an enumeration.

*On the two kinds of places.* In Example 3 the integrality of the chosen preimage at an inert place is forced by the valuation identity $\mathrm{ord}(\mathrm{Nm}\,y)=f\,\mathrm{ord}(y)$. In Example 2 it is not forced, since $\mathrm{Nm}_5(10,1/5)=2$, and in Example 4 the wrong choices at infinitely many split primes destroy the idele. The restricted-product condition is therefore essential exactly for the primes with more than one prime above them, together with the finitely many ramified primes.

*What is not read.* The semilocal decomposition $K_v\otimes_KL\cong\prod_{w\mid v}L_w$ (`tensorEquiv`) and its infinite analogue, the adelic base change $\mathbb A_K\otimes_KL\cong\mathbb A_L$ (`adeleTensorEquiv`), the degree formula $\sum_{w\mid v}[L_w:K_v]=[L:K]$ (`sum_finrank_eq`), and the continuity statements are used as named inputs; their statements were read, their proofs were not. The second inequality `natCard_cycTateNegOne_ideleClassGroup` is read in §11.4.3.7; the inertia inputs of Lemma G in §11.4.3.4 are not touched.

**Reading boundary and source map.** Read in full here [Lean, read]: `mem_range_ideleNorm_iff`, `mem_range_ideleNorm`, `glue`, `glue_snd`, `glue_fst`, `ideleNorm_glue`, `placesOver_congr`, `infinitePlacesOver_congr`, `finiteProj_ideleNorm`, `infiniteProj_ideleNorm`, `eventually_finiteProj_mem`, `eventually_forall_placesOver`, the definitions `finiteLocalNorm`, `coe_finiteLocalNorm`, `integerUnitsOver`, `mem_integerUnitsOver`, `infiniteLocalNorm`, `coe_infiniteLocalNorm`; `ideleNorm_snd`, `ideleNorm_fst`, `norm_adeleRing_snd`, `norm_adeleRing_fst`, `finiteEval_norm`, `infiniteEval_norm`, `finiteEval`, `finiteRestrict`, `infiniteEval`, `infiniteRestrict`, `completionsOverBasis` with `completionsOverBasis_repr`; `norm_map_of_repr`, `adeleBasis`, `adeleBasis_repr`, `ideleNorm`, `coe_ideleNorm`, `ideleNorm_diagonal`; `norm_pi`, `leftMulMatrix_pi`; `prodRestrictedEquiv` with `prodRestrictedEquiv_apply_fst`, `_snd`, `finiteUnitsEquiv`, `isOpen_units_adicCompletionIntegers`, `prodEquiv`; `below`, `liesOver_below`, `below_eq_iff`, `tendsto_below`; `IdeleGroup`, `finiteProj`, `coe_finiteProj`, `coe_finiteProj_diagonal`, `infiniteProj`, `coe_infiniteProj`, `diagonal`; `PlacesOver`, `placesOverEquiv`, `nonempty_placesOver`; the deduction `mem_range_ideleNorm_iff_forall` (inherited from §11.4.3.5); and Mathlib's `RestrictedProduct.unitsEquiv` with `coeUnits` and `mkUnit`, and `MulEquiv.piUnits`, checked in the pinned source. Statement read, proof not read [Lean]: `tensorEquiv`, `tensorMap`, `det_blockDiagonal'`, `continuous_unitsEquiv`, `norm_adeleRing_algebraMap`, `piPlacesOverBasis`, `GroundTheory.Global.Algebra.norm_pi` (infinite version). Named inputs not read [Lean]: `adeleTensorEquiv`, `adeleTensorEquiv_sum_coord`, `coord`, `localCoord`, `sum_finrank_eq`, `InfinitePlace.placesOver`, `InfinitePlace.LiesOver.comap_eq`, `PiPlacesOver`, `tensorPiEquiv`, and the Mathlib declarations `Algebra.leftMulMatrix_eq_repr_mul`, `Algebra.norm_eq_matrix_det`, `RingHom.map_det`, `Matrix.BlockTriangular.det_fintype`, `Filter.Tendsto.cofinite_of_finite_preimage_singleton`, `Homeomorph.prodUnits`, `RestrictedProduct.mapAlong_continuous`, `FiniteAdeleRing.ext`. Inherited: `map_integerUnitsOver_eq_of_ramificationIdx_eq_one` and `eventually_map_integerUnitsOver_eq` (§11.4.3.5), `mem_range_norm_of_diagonal_mem_range_ideleNorm` and `locFin` (§11.4.3.4). Not touched: `natCard_cycTateNegOne_ideleClassGroup`, `ineCard`, `cycIne`.

| Source and lines | Role and reading |
|---|---|
| `GT/IdeleGroups/LocalNorms.lean:19–45,68–90,95–102,106–205` | [Lean, read] Local norm definitions, Lemmas 1 (unit form), 2, 3, 4 and Theorem A. |
| `GT/IdeleGroups/LocalNormsEverywhere.lean:58–67` | [Lean, read] Corollary B (inherited from §11.4.3.5). |
| `GT/IdeleGroups/IdeleNorms/CompletionsOverBasisRepr.lean:20–59,63–105,113–123` | [Lean, read] Evaluation and restriction maps, coordinate compatibility, Lemma 1. |
| `GT/IdeleGroups/IdeleNorms/BaseChange.lean:17–27,51–68,109,170–184` | [Lean, read] `norm_map_of_repr`, adelic basis, `ideleNorm`, `ideleNorm_diagonal`; `:109` statement only. |
| `GT/SemilocalAlgebras/NormTrace.lean:12–46` | [Lean, read] `norm_pi` and `leftMulMatrix_pi`; `det_blockDiagonal'` statement only. |
| `GT/SemilocalAlgebras/Finite.lean:17,82–83`, `GT/SemilocalAlgebras/ContinuousCompletionMap.lean:15–31` | [Lean, read] `CompletionsOver`, `PlacesOver`, `placesOverEquiv`; `tensorEquiv` [Lean] statement only. |
| `GT/IdeleGroups/Restricted.lean:79–116` | [Lean, read] `prodRestrictedEquiv`; `:31–65` continuity, statement only. |
| `GT/Adele/BaseChange/FiniteMap.lean:20–42` | [Lean, read] `below`, `below_eq_iff`, `tendsto_below`. |
| `GT/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean:12,23–29,51–52,144–159,181–184,213–227` | [Lean, read] Idele group, `prodEquiv`, `diagonal`, projections. |
| `GT/KummerTheory/Splitting.lean:82–87` | [Lean, read] `nonempty_placesOver`; `sum_finrank_eq` [Lean] named. |
| `GT/HasseNorm.lean:56–62`, `GL/FerreroWashingtonIndex/LocFin.lean:82,87` | [Lean, read] Consumers (inherited). |
| Mathlib `0df444a`: `Mathlib/Topology/Algebra/RestrictedProduct/Units.lean:66–89`, `Mathlib/Algebra/Group/Pi/Units.lean:25–28` | [Lean, read] `unitsEquiv` with `coeUnits`, `mkUnit`; `piUnits`. Checked against the pinned source. |

Here `GT/` expands to `src/GroundTheory/GlobalFields/` and `GL/` to `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/`.

#### 11.4.3.7 The second inequality for cyclic extensions and the vanishing of the minus-one Tate group of the idele class group

**Motivation.** Proposition C of §11.4.3.4 deduces the Hasse norm theorem for a cyclic extension $L/K$ from one cohomological fact: the Tate group $\widehat H^{-1}(G,C_L)$ of the idele class group $C_L=I_L/L^\times$, $G=\mathrm{Gal}(L/K)$, is trivial (`natCard_cycTateNegOne_ideleClassGroup`, `src/GroundTheory/GlobalFields/SecondInequality/Cyclic.lean:26`). Sections 11.4.3.4–11.4.3.6 read everything else on that route and left this fact as a named input. This subsection reads it. The archive does not attack $\widehat H^{-1}$ directly. It compares two finite groups attached to the same cyclic extension. The group $\widehat H^0(G,C_L)=C_L^G/\mathrm{Nm}\,C_L$ is identified with $C_K/\mathrm{Nm}_{L/K}C_L$, so its order is the norm index $[C_K:\mathrm{Nm}\,C_L]$. The Herbrand quotient $\lvert\widehat H^0\rvert/\lvert\widehat H^{-1}\rvert$ is computed to be $n=[L:K]$ from the $S$-units and $S$-ideles. Hence the norm index is $n\lvert\widehat H^{-1}\rvert\ge n$, the first inequality. The second inequality says the norm index is at most $n$. The two inequalities together force $\lvert\widehat H^{-1}\rvert=1$ and $\lvert\widehat H^0\rvert=n$. The second inequality is proved first for cyclic extensions of prime degree $p$ over a field containing the $p$-th roots of unity, by Kummer theory and the first inequality, and then transported to all cyclic extensions by two reductions, one adjoining roots of unity and one inducting on the degree. The subsection reads the comparison step, the identification of $\widehat H^0$, the two reductions and the final assembly in full, reads the assembly of the Herbrand quotient computation, and names the two Herbrand quotient suppliers and the Kummer case as inputs. Source references are to the joined archive with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` and to Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. [Lean, read]

**Example 1 (the Gaussian field: Tate groups of units and the Herbrand bookkeeping).** [Expository] Let $K=\mathbb Q$, $L=\mathbb Q(i)$, $G=\langle\sigma\rangle$ with $\sigma$ complex conjugation, $n=2$. The computations below are of finitely generated $G$-modules. They are not computations in the idele class group $C_L$, which is neither finite nor finitely generated; what they verify is the bookkeeping by which the archive obtains the Herbrand quotient of $C_L$ from such modules.

*Units.* $E=\mathcal O_L^\times=\mu_4=\{\pm1,\pm i\}$, written additively as $\mathbb Z/4$ with $\sigma=-1$ since $\sigma(i)=i^{-1}$. Fixed points $E^G=\{\pm1\}$; norms $\mathrm{Nm}(u)=u\sigma(u)=uu^{-1}=1$, so $\mathrm{Nm}\,E=\{1\}$; hence $\widehat H^0(G,E)=\{\pm1\}/\{1\}$ has order $2$. Kernel of the norm: all of $\mu_4$; image of $\sigma-1$: $\{u^{-1}/u\}=\{u^{-2}\}=\mu_2$; hence $\widehat H^{-1}(G,E)=\mu_4/\mu_2$ has order $2$. The Herbrand quotient $h(E)=2/2=1$, as it must be for a finite module.

*$S$-units.* Take $S=\{2\}$, the only ramified prime; $\mathbb Q(i)$ has class number $1$, so no further primes are needed for $I_L=L^\times I_{L,T}$ (Lemma 2 below), where $T$ is the set of primes of $L$ over $S$, here $T=\{(1+i)\}$. The $T$-units are $U(T)=\mu_4\times(1+i)^{\mathbb Z}$. Since $\sigma(1+i)=1-i=-i(1+i)$, the quotient $U(T)/\mu_4\cong\mathbb Z$ carries the trivial action. For $\mathbb Z$ with trivial action, $\widehat H^0=\mathbb Z/n\mathbb Z$ has order $n=2$ and $\widehat H^{-1}=\ker(\mathrm{Nm})/0=0$, so $h(\mathbb Z)=2$. Multiplicativity along $0\to\mu_4\to U(T)\to\mathbb Z\to0$ gives $h(U(T))=1\cdot2=2$. The archive's formula (Lemma 2(ii)) gives the same: $(e_2f_2)\cdot(\text{infinite factor})/n=(2\cdot1)\cdot2/2=2$, the infinite factor being $2$ because the real place of $\mathbb Q$ ramifies in $\mathbb Q(i)$.

*$T$-ideles.* $I_{L,T}$ consists of the ideles that are integral units at every finite prime other than $(1+i)$. Its Herbrand quotient is the product of the local degrees over $S$ and over the infinite places (Lemma 2(i)): $[\mathbb Q_2(i):\mathbb Q_2]\cdot[\mathbb C:\mathbb R]=2\cdot2=4$. The local factors are induced modules whose Tate groups are those of the decomposition group; at the unramified primes the unit groups contribute nothing, which is the unramified unit-norm theorem of §11.4.3.5 together with Hilbert 90.

*The idele class group.* From $0\to U(T)\to I_{L,T}\to C_L\to0$ one gets $h(C_L)=h(I_{L,T})/h(U(T))=4/2=2=n$. With Lemma 1, $\lvert\widehat H^0(G,C_L)\rvert=[C_{\mathbb Q}:\mathrm{Nm}\,C_L]=2\lvert\widehat H^{-1}(G,C_L)\rvert$. Theorem A gives $\lvert\widehat H^{-1}\rvert=1$ and norm index $2$. The two statements have concrete meaning. The norm index $2$: the idele $x$ with $x_\infty=-1$ and all other components $1$ is not in $\mathbb Q^\times\mathrm{Nm}(I_L)$. If it were $a\,\mathrm{Nm}(y)$ with $a\in\mathbb Q^\times$, then $a$ would be a local norm at every finite place and negative at $\infty$, so $a$ would fail to be a local norm at exactly one place, contradicting the even number of failures recorded in Example 3 of §11.4.3.6 [Paper] [Serre1973, Ch. III, §2.1, Theorem 3, p. 23]. By Theorem A every idele class of $\mathbb Q$ is either a norm class or this one. The vanishing of $\widehat H^{-1}$: every rational number that is a sum of two squares in every $\mathbb Q_v$ is a sum of two squares in $\mathbb Q$, which is the Hasse norm theorem for $\mathbb Q(i)/\mathbb Q$ (Proposition C of §11.4.3.4).

**Example 2 (a cyclic cubic field: a free unit lattice and the opposite direction of the Herbrand quotient).** [Expository] Let $L=\mathbb Q(\zeta_7)^+=\mathbb Q(\rho_1)$ with $\rho_k=2\cos(2\pi k/7)$, $k=1,2,3$, the roots of $X^3+X^2-2X-1$. It is the cyclic cubic field of smallest discriminant, $49=7^2$, with class number $1$, regulator $0.525454682123$, fundamental units $a^2-2$, $a^2-1$ where $a$ is a root of $X^3-X^2-2X+1$ (so $a=-\rho_k$), and $7$ the only ramified prime [Paper] [LMFDB, number field 3.3.49.1]. The generator $\sigma:\zeta_7\mapsto\zeta_7^2$ of $G=\mathrm{Gal}(L/\mathbb Q)$ permutes $\rho_1\mapsto\rho_2\mapsto\rho_3\mapsto\rho_1$, since $\rho_{2k}=\rho_k^2-2$.

*Units.* The constant term of $X^3+X^2-2X-1$ gives $\rho_1\rho_2\rho_3=1$, so each $\rho_k$ is a unit and $\mathrm{Nm}(\rho_1)=1$. The regulator of $\langle\rho_1,\rho_2\rangle$, computed from the three real embeddings, is $0.5254546821\ldots$, equal to the regulator of $L$; so $\rho_1,\rho_2$ are fundamental units and $E=\mathcal O_L^\times=\{\pm1\}\times\langle\rho_1,\rho_2\rangle$. Modulo torsion, $E/\{\pm1\}$ is generated by $\rho_1$ as a $\mathbb Z[G]$-module with the single relation $\rho_1\sigma(\rho_1)\sigma^2(\rho_1)=1$, so $E/\{\pm1\}\cong\mathbb Z[G]/(\mathrm{Nm})\cong\mathbb Z[\zeta_3]$ with $\sigma$ acting as multiplication by $\zeta_3$. On this module: fixed points are $0$, since $\zeta_3x=x$ forces $x=0$; the norm $1+\zeta_3+\zeta_3^2$ is $0$, so $\ker\mathrm{Nm}$ is everything; and $(1-\zeta_3)\mathbb Z[\zeta_3]$ has index $\lvert\mathrm N(1-\zeta_3)\rvert=3$. Hence $\widehat H^0(G,\mathbb Z[\zeta_3])=0$, $\widehat H^{-1}(G,\mathbb Z[\zeta_3])\cong\mathbb Z/3$, and $h=1/3$. The torsion $\{\pm1\}$ is finite with trivial action and contributes $h=1$. So $h(E)=1/3$: here it is $\widehat H^{-1}$, not $\widehat H^0$, that carries the order $3$. This is the general pattern for units of a totally real cyclic extension of $\mathbb Q$ of degree $n$: the infinite place is unramified, and Lemma 2(ii) gives $h(E)=1/n$ when $S$ is empty.

*$S$-units.* Take $S=\{7\}$. Since $\prod_{j<k}(\rho_j-\rho_k)^2=\mathrm{disc}=49$ and the three differences are conjugate up to sign, $\pi=\rho_1-\rho_2$ has norm $\pm7$ and generates the unique prime of $L$ over $7$, which is totally ramified ($e=3$, $f=1$). The class number is $1$, so $I_L=L^\times I_{L,T}$ with $T=\{(\pi)\}$. The $T$-units are $U(T)=E\times\pi^{\mathbb Z}$ and $U(T)/E\cong\mathbb Z$ with trivial action ($\sigma(\pi)/\pi$ is a unit). So $h(U(T))=h(E)\,h(\mathbb Z)=(1/3)\cdot3=1$. The archive's formula: $(e_7f_7)\cdot(\text{infinite factor})/n=(3\cdot1)\cdot1/3=1$, the infinite factor being $1$ because the real place of $\mathbb Q$ is unramified in the totally real field $L$.

*$T$-ideles and the idele class group.* $h(I_{L,T})=[L_\pi:\mathbb Q_7]\cdot[\mathbb R:\mathbb R]=3\cdot1=3$, and $h(C_L)=3/1=3=n$. Theorem A gives $[C_{\mathbb Q}:\mathrm{Nm}\,C_L]=3$ and $\widehat H^{-1}(G,C_L)=1$. Unlike Example 1, exhibiting the three norm classes needs more than the Hilbert symbol. The prime $2$ is inert in $L$ since $2$ has order $3$ modulo $7$, so the idele $x$ with $x_2=2$ and all other components $1$ is a natural candidate for a generator of $C_{\mathbb Q}/\mathrm{Nm}\,C_L$: its norm residue symbol is the local symbol at $2$, the Frobenius at $2$, which generates $G$ [Paper] [Neukirch1999, Ch. VI, §5, (5.6)–(5.7), pp. 391–393]. This book does not read the reciprocity law; the statement is recorded for orientation only. What the archive proves is the order $3$ and the vanishing of $\widehat H^{-1}$, by the comparison in Theorem A.

**Definitions.** [Lean, read] Let $k$ be a commutative ring, $G$ a finite group, $V$ a $k$-module with a representation $\rho:G\to\mathrm{End}_k(V)$, and $\sigma\in G$. The archive defines (`src/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean:99–185`):
- $\sigma-1$ as the additive endomorphism $v\mapsto\rho(\sigma)v-v$ (`cycSubOne`, `:99–104`), and the norm $\mathrm{Nm}=\sum_{g\in G}\rho(g)$ (`cycNorm`, `:158–162`);
- for additive endomorphisms $f,g$ of an abelian group $A$ with $f\circ g=0$ and $g\circ f=0$, the quotient $\mathrm{KMR}(f,g)=\ker f/\operatorname{im}g$ (`KerModRange`, `src/GroundTheory/TateCohomology/HerbrandAbstract.lean:36–37`), the predicate that both $\mathrm{KMR}(f,g)$ and $\mathrm{KMR}(g,f)$ are finite (`HasHerbrandQuotient`, `:39–40`), and the rational number $\lvert\mathrm{KMR}(f,g)\rvert/\lvert\mathrm{KMR}(g,f)\rvert$ (`herbrandQuotient`, `:42–43`), where the cardinality of an infinite set is the integer $0$;
- $\widehat H^0_\sigma(V)=\mathrm{KMR}(\sigma-1,\mathrm{Nm})=\ker(\sigma-1)/\mathrm{Nm}V$ (`CycTateZero`, `:174–175`), $\widehat H^{-1}_\sigma(V)=\mathrm{KMR}(\mathrm{Nm},\sigma-1)=\ker\mathrm{Nm}/(\sigma-1)V$ (`CycTateNegOne`, `:177–178`), and $h_\sigma(V)=\lvert\widehat H^0_\sigma\rvert/\lvert\widehat H^{-1}_\sigma\rvert$ (`cycHerbrand`, `cycHerbrand_eq`, `:180–185`). The compositions $(\sigma-1)\circ\mathrm{Nm}=0=\mathrm{Nm}\circ(\sigma-1)$ are `cycSubOne_cycNorm` and `cycNorm_cycSubOne` (`:164–172`).

When $\sigma$ generates $G$ (the archive's hypothesis is `∀ g, g ∈ Subgroup.zpowers σ`), $\ker(\sigma-1)=V^G$ (`mem_ker_cycSubOne_iff`, `:118–121`) and $(\sigma-1)V$ is the subgroup generated by all $\rho(g)v-v$ (`range_cycSubOne_eq_closure`, `:146–154`), so $\widehat H^0_\sigma$ and $\widehat H^{-1}_\sigma$ are the Tate groups $\widehat H^0(G,V)$ and $\widehat H^{-1}(G,V)$ of the cyclic group $G$, and $h_\sigma$ is the Herbrand quotient. For a number field extension $L/K$ with $G=\mathrm{Gal}(L/K)$, the module in question is the idele class group $C_L=I_L/\Delta(L^\times)$ (`IdeleClassGroup`, `src/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean:65`) written additively, with $G$ acting through its action on ideles (`Representation.ofMulDistribMulAction`). The norm $\mathrm{Nm}_{L/K}:C_L\to C_K$ is `ideleClassNorm` (`IdeleNorms/BaseChange.lean:207–208`), induced by the idele norm of §11.4.3.6, and the inclusion $C_K\to C_L$ is `ideleClassMap` (`:202–203`), induced by the embedding of ideles. The two are related by $\mathrm{Nm}(\iota c)=c^n$ for $c\in C_K$, $n=[L:K]$ (`ideleClassNorm_ideleClassMap`, `:228`), by $\iota(\mathrm{Nm}\,c)=\prod_{g\in G}g\cdot c$ for $c\in C_L$ (`ideleClassMap_ideleClassNorm`, `GaloisOnAdeles/Action.lean:267–270`), by $\mathrm{Nm}_{L/K}\circ\mathrm{Nm}_{M/L}=\mathrm{Nm}_{M/K}$ for a tower $K\subseteq L\subseteq M$ (`ideleClassNorm_ideleClassNorm`, `IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean:122–125`), and by the injectivity of $\iota$ (`ideleClassMap_injective`, `BaseChange.lean:246`). The archive also records that $\iota(C_K)$ is exactly the set of $G$-fixed idele classes (`forall_smul_eq_iff_mem_range_ideleClassMap`, `Action.lean:272`), which is Lemma 4.1 of [MilneCFT, Ch. VII, §4, p. 210] and rests on Hilbert 90 for $L^\times$. The last five declarations are used here as named inputs; their statements were read, their proofs were not. [Lean]

**Lemma 1 (the zeroth Tate group is the norm index; `natCard_cycTateZero_ideleClassGroup`).** [Lean, read] Let $L/K$ be Galois with $G=\mathrm{Gal}(L/K)$ generated by $\sigma$. The map $c\mapsto[\iota c]$ is a surjective homomorphism $C_K\to\widehat H^0_\sigma(C_L)$ with kernel $\mathrm{Nm}_{L/K}C_L$. Hence $\lvert\widehat H^0(G,C_L)\rvert=[C_K:\mathrm{Nm}_{L/K}C_L]$, the two sides being $0$ together when the index is infinite.

**Proof.** The map is well defined because $\iota c$ is fixed by $\sigma$ (`smul_ideleClassMap`, `Action.lean:252`), so it lies in $\ker(\sigma-1)$ (`ideleClassToCycTateZero`, `src/GroundTheory/GlobalFields/FirstInequality.lean:15–21`). Surjectivity (`:42–54`): a class in $\widehat H^0_\sigma$ is represented by $y\in\ker(\sigma-1)$; since $\sigma$ generates $G$, $y$ is fixed by every $g$ (`mem_ker_cycSubOne_iff`), hence $y=\iota c$ for some $c\in C_K$ by the fixed-point description. Kernel (`:56–69`): $[\iota c]=0$ means $\iota c\in\mathrm{Nm}\,C_L$ in the additive sense, that is $\iota c=\sum_g g\cdot d=\iota(\mathrm{Nm}_{L/K}d)$ for some $d$ (`cycNorm_ideleClassGroup`, `:35–40`, which rewrites the additive norm as $\iota\circ\mathrm{Nm}_{L/K}$); by injectivity of $\iota$ this is $c=\mathrm{Nm}_{L/K}d$. Conversely $\iota(\mathrm{Nm}\,d)$ is in the image of the additive norm by the same identity. The cardinality statement (`:71–76`) is the first isomorphism theorem applied to this surjection, with the archive's convention that the index of a subgroup is the cardinality of the quotient and is $0$ when infinite. $\square$

**Lemma 2 (the Herbrand quotient of the idele class group; `cycHerbrand_ideleClassGroup`).** [Lean, read as an assembly; the two suppliers (i) and (ii) are [Lean]] Let $L/K$ be Galois with $G$ generated by $\sigma$ and $n=[L:K]$. Then $\widehat H^0_\sigma(C_L)$ and $\widehat H^{-1}_\sigma(C_L)$ are finite and $h_\sigma(C_L)=n$. More precisely, let $S$ be a finite set of primes of $K$ containing every prime that ramifies in $L$ and such that $I_L=\Delta(L^\times)\cdot I_{L,T}$, where $T$ is the set of primes of $L$ over $S$ and $I_{L,T}$ is the group of ideles of $L$ that are integral units at every finite prime outside $T$ (`sIdeles`, `IdeleGroups/SIdeleGroups.lean:15–19`). Let $U(T)=L^\times\cap I_{L,T}$ be the $T$-units. Then, with $w$ a chosen prime of $L$ over each $v$:
(i) $h_\sigma(I_{L,T})=\prod_{v\mid\infty}[L_w:K_v]\cdot\prod_{v\in S}[L_w:K_v]$ (`cycHerbrand_sIdeles`, `IdeleGroups/SIdeleHerbrand.lean:68–78`) [Lean];
(ii) $h_\sigma(U(T))=\prod_{v\in S}e_vf_v\cdot\prod_{v\mid\infty}\epsilon_v\,/\,n$, where $e_vf_v=[L_w:K_v]$ and $\epsilon_v=1$ if $v$ is unramified in $L$ and $2$ if it ramifies (`cycHerbrand_sUnitRep`, `HerbrandQuotients/SUnits.lean:50–55`) [Lean];
(iii) $0\to U(T)\to I_{L,T}\to C_L\to0$ is an exact sequence of $G$-modules (`sUnits_sIdeles_placesAbove_exact`, `IdeleGroups/SIdeleGroups/Galois.lean:144–150`) [Lean], and the Herbrand quotient is multiplicative along it (`herbrandQuotient_eq_mul_of_shortExact`, `HerbrandAbstract.lean:387–403`) [Lean, read for the statement and the hexagon count `natCard_kerModRange_hexagon`, `:334–342`].

**Proof of the assembly (`FirstInequality/HerbrandClass.lean:93–180`).** The set $S$ exists (`exists_finset_unramified_sup_sIdeles_eq_top`, `:73–87`): the primes of $L$ with ramification index $>1$ form a finite set (`eventually_ramificationIdx_eq_one`), and `exists_finset_superset_sup_sIdeles_placesAbove_eq_top` (`SIdeleGroups/Galois.lean:131`) [Lean] enlarges the set of their images in $K$ to an $S$ with $\Delta(L^\times)\cdot I_{L,T}=I_L$; this is the finiteness of the class group, as in Lemma 4.2 of [MilneCFT, Ch. VII, §4, p. 210]. The maps $U(T)\to I_{L,T}$ (diagonal) and $I_{L,T}\to C_L$ (class) are $G$-equivariant (`:120–128`, using `smul_diagonal` and `sIdelesToIdeleClassGroup_smul`), so they commute with $\sigma-1$ and with $\mathrm{Nm}$ (`map_cycSubOne`, `map_cycNorm`, `:22–31`, and `:130–136`). $U(T)$ has a Herbrand quotient because it is a finitely generated $\mathbb Z$-module (`hasHerbrandQuotient_sUnitRep`, `SUnits.lean:22–25`, from `hasHerbrandQuotient_cycSubOne_of_finite`) and $I_{L,T}$ has one by (i). The two-out-of-three statement `HasHerbrandQuotient.of_shortExact_left_mid` (`HerbrandAbstract.lean:363–373`) gives finiteness for $C_L$, and (iii) gives $h(I_{L,T})=h(U(T))\,h(C_L)$. Substituting (i) and (ii), after converting the local degrees $[L_w:K_v]$ at finite places to $e_vf_v$ (`finrank_adicCompletion_eq_ramificationIdxIn_mul`, `:59–65`) and at infinite places to $\epsilon_v$ (`finrank_infiniteCompletion_eq_ite`, `:42–55`), the products over $S$ and over the infinite places cancel and `field_simp` leaves $h(C_L)=n$ (`:172–180`). The three nonvanishing facts needed for the cancellation are that the infinite factors are $1$ or $2$, that local degrees are positive, and that $n>0$. $\square$

The suppliers (i) and (ii) are the content of Propositions (3.3) and (3.5) of [Neukirch1999, Ch. VI, §3, pp. 375–378] and of Theorem 4.3 of [MilneCFT, Ch. VII, §4, p. 211], whose proof has the same three lines $C_L\cong I_{L,T}/U(T)$, $h(C_L)=h(I_{L,T})/h(U(T))$, and the two local computations. Supplier (i) decomposes $I_{L,T}$ into induced modules at the places of $S$ and at infinity, where the Tate groups are those of the local extensions ($\widehat H^{-1}=0$ by Hilbert 90 and $\lvert\widehat H^0\rvert=[L_w:K_v]$ by local class field theory, or in the archive by `LocalHerbrand`), and into unit groups at the unramified places outside $S$, where both Tate groups vanish by the unramified unit-norm theorem of §11.4.3.5. Supplier (ii) is the Herbrand quotient of a lattice on which $G$ permutes a basis, computed through the real vector space spanned by the logarithmic embeddings. Neither is read here. Examples 1 and 2 check both formulas on $\mathbb Q(i)/\mathbb Q$ and on $\mathbb Q(\zeta_7)^+/\mathbb Q$.

**Lemma 3 (the first inequality; `index_range_ideleClassNorm`, `finrank_le_index_range_ideleClassNorm`, `firstInequality`).** [Lean, read] Let $L/K$ be Galois with $G$ generated by $\sigma$. Then $\widehat H^{-1}_\sigma(C_L)$ is finite and nonempty, and
$$
[C_K:\mathrm{Nm}_{L/K}C_L]=n\cdot\lvert\widehat H^{-1}_\sigma(C_L)\rvert .
$$
In particular $[C_K:\mathrm{Nm}_{L/K}C_L]$ is finite and at least $n$; in the archive's formulation with extended cardinals, $n\le\lvert C_K/\mathrm{Nm}\,C_L\rvert$ in $\mathbb N\cup\{\infty\}$ (`FirstInequality`, `FirstInequalityStatement.lean:8–11`).

**Proof.** (`FirstInequality.lean:78–110`) By Lemma 2 both Tate groups are finite, so $\lvert\widehat H^{-1}_\sigma\rvert$ is a positive integer (`Nat.card_pos`), and $h_\sigma(C_L)=\lvert\widehat H^0_\sigma\rvert/\lvert\widehat H^{-1}_\sigma\rvert=n$. Replacing $\lvert\widehat H^0_\sigma\rvert$ by the index through Lemma 1 and clearing the denominator gives the displayed identity (`:88–90`). Since $\lvert\widehat H^{-1}_\sigma\rvert\ge1$, the index is at least $n$ and nonzero (`:92–98`). For the extended-cardinal form (`:102–110`), a nonzero index makes the quotient finite (`Subgroup.finite_quotient_of_finiteIndex`), after which the cardinality in $\mathbb N\cup\{\infty\}$ is the natural number just bounded. $\square$

**Lemma 4 (four facts about indices; `Statement.lean:12–55`).** [Lean, read] Let $G,G'$ be groups, $f:G\to G'$ a homomorphism, $H\le G$ and $H'\le G'$ subgroups, with the convention that the index of a subgroup of infinite index is $0$.
(i) $\lvert G/H\rvert\le m$ in $\mathbb N\cup\{\infty\}$ if and only if $[G:H]\ne0$ and $[G:H]\le m$ (`enatCard_quotient_le_iff`).
(ii) If $f^{-1}(H')\le H$ and $[G':H']\ne0$, then $[G:H]\ne0$ and $[G:H]\le[G':H']$ (`index_le_of_comap_le`).
(iii) If $[G:H]\ne0$ and $[G':f(G)]\ne0$, then $[G':f(H)]\ne0$ and $[G':f(H)]\le[G':f(G)]\cdot[G:H]$ (`index_map_le`).
(iv) If $a,b$ are coprime and $x^a,x^b\in H$ then $x\in H$ (`mem_of_pow_mem_of_coprime`); and in a cyclic group all elements commute (`mul_comm_of_isCyclic`).

**Proof.** (i) If $G/H$ is finite, the extended cardinal is the natural cardinal and the index is nonzero; if infinite, the left side is $\infty\le m$, false, and the right side is false because the index is $0$. (ii) The index of $f^{-1}(H')$ equals the relative index of $H'$ in $f(G)$ (`Subgroup.index_comap`), which is at most $[G':H']$ and nonzero when $[G':H']$ is; and $[G:H]$ divides $[G:f^{-1}(H')]$ because $f^{-1}(H')\le H$ (`Subgroup.index_dvd_of_le`). (iii) Mathlib's `Subgroup.index_map` gives $[G':f(H)]=[G:H\ker f]\cdot[G':f(G)]$, and $[G:H\ker f]$ divides $[G:H]$. (iv) Bezout: $1=ua+vb$ in $\mathbb Z$, so $x=(x^a)^u(x^b)^v\in H$. The last statement reads $a,b$ as powers of a generator. $\square$

**Definition (the two forms of the second inequality).** [Lean, read] Fix a universe $u$. `SecondInequality` (`Reduction.lean:10–13`) is the statement that for all number fields $K\subseteq L$ in $u$ with $L/K$ Galois and cyclic, $\lvert C_K/\mathrm{Nm}_{L/K}C_L\rvert\le[L:K]$ in $\mathbb N\cup\{\infty\}$. `SecondInequalityRoots` (`Statement.lean:59–62`) is the same statement restricted to extensions of prime degree $p$ such that $K$ contains a primitive $p$-th root of unity (`HasEnoughRootsOfUnity K p`). By Lemma 4(i) each is equivalent to the finiteness of the norm index together with the bound on it.

**Proposition 5 (adjoining roots of unity; `SecondInequalityRoots.index_le_of_prime`).** [Lean, read] Assume `SecondInequalityRoots` in universe $u$. Let $L/K$ be a Galois extension of number fields in $u$ of prime degree $p$. Then $[C_K:\mathrm{Nm}_{L/K}C_L]$ is nonzero and at most $p$.

**Proof.** (`PrimeDegree.lean:15–99`) Let $E=L(\zeta)$ with $\zeta$ a primitive $p$-th root of unity (`CyclotomicField p L`, `IsCyclotomicExtension.zeta`), and $K'=K(\zeta)\subseteq E$. Since $\zeta$ is a root of the $p$-th cyclotomic polynomial, of degree $p-1$, $m=[K':K]\le p-1<p$, so $m$ is coprime to $p$ (`:25–37`). $K'$ contains a primitive $p$-th root of unity (`:39–42`). $E/K$ is Galois: $L$ is the splitting field over $K$ of a separable polynomial $f$ (`IsGalois.is_separable_splitting_field`), $E$ is the splitting field over $L$ of the cyclotomic polynomial (`IsCyclotomicExtension.splitting_field_cyclotomic`), so $E$ is the splitting field over $K$ of $f\cdot\Phi_p$ (`IsSplittingField.mul`), hence normal, and separable in characteristic $0$ (`:44–52`). Then $E/K'$ is Galois (`:53`). Write $L'$ for the image of $L$ in $E$; the compositum $K'L'$ is $E$ because $E$ is generated over $L$ by $\zeta$ (`:55–67`), and $[L':K]=p$ (`:68–69`). Degrees: $[E:K]\le[K':K]\cdot[L':K]=mp$ by `finrank_sup_le`, so $[E:K']\le p$; and $p=[L:K]$ divides $[E:K]=m[E:K']$, so $p$ divides $[E:K']$ since $\gcd(m,p)=1$; hence $[E:K']=p$ (`:71–84`). A group of prime order is cyclic, so `SecondInequalityRoots` applies to $E/K'$ and, through Lemma 4(i), gives $[C_{K'}:\mathrm{Nm}_{E/K'}C_E]\ne0$ and $\le p$ (`:85–88`).

The comparison step (`:90–97`): if $c\in C_K$ and $\iota_{K'}c=\mathrm{Nm}_{E/K'}y$ with $y\in C_E$, then
$$
c^m=\mathrm{Nm}_{K'/K}(\iota_{K'}c)=\mathrm{Nm}_{K'/K}\mathrm{Nm}_{E/K'}y=\mathrm{Nm}_{E/K}y=\mathrm{Nm}_{L/K}(\mathrm{Nm}_{E/L}y)\in\mathrm{Nm}_{L/K}C_L,
$$
using $\mathrm{Nm}\circ\iota=(\ )^m$ and the tower identity twice; and $c^p=\mathrm{Nm}_{L/K}(\iota_Lc)\in\mathrm{Nm}_{L/K}C_L$ (`pow_finrank_mem_range_ideleClassNorm`, `Statement.lean:68–70`). As $\gcd(m,p)=1$, Lemma 4(iv) gives $c\in\mathrm{Nm}_{L/K}C_L$. So the preimage under $\iota_{K'}$ of $\mathrm{Nm}_{E/K'}C_E$ is contained in $\mathrm{Nm}_{L/K}C_L$, and Lemma 4(ii) gives $[C_K:\mathrm{Nm}_{L/K}C_L]\ne0$ and $\le[C_{K'}:\mathrm{Nm}_{E/K'}C_E]\le p$ (`:98–99`). $\square$

This is Lemma 6.1 of [MilneCFT, Ch. VII, §6, p. 214]. Milne shows that $C_K/\mathrm{Nm}\,C_L\to C_{K'}/\mathrm{Nm}\,C_E\to C_K/\mathrm{Nm}\,C_L$ is multiplication by $m$, an isomorphism because the group is killed by $p$; the archive replaces the isomorphism by the Bezout step on a single class and the index comparison of Lemma 4(ii). Both use only $\gcd(m,p)=1$ and the two norm identities.

**Proposition 6 (induction on the degree; `SecondInequalityRoots.index_le_of_finrank_eq`, `SecondInequalityRoots.secondInequality`).** [Lean, read] Assume `SecondInequalityRoots` in universe $u$. Then for every cyclic Galois extension $L/K$ of number fields in $u$, $[C_K:\mathrm{Nm}_{L/K}C_L]$ is nonzero and at most $[L:K]$. Hence `SecondInequality` holds in $u$.

**Proof.** (`Reduction.lean:15–72`) Strong induction on $n=[L:K]$, the statement being quantified over all $K,L$ in $u$ of degree $n$. If $n=1$, every $c\in C_K$ equals $c^1=\mathrm{Nm}(\iota c)$, so the norm is onto and the index is $1$ (`:23–31`). If $n>1$, choose a prime $q\mid n$ and an element $g\in G$ of order $q$ (`exists_prime_orderOf_dvd_card'`, after $\lvert G\rvert=n$). Let $H=\langle g\rangle$ and $M=L^H$. $H$ is normal because $G$ is abelian (Lemma 4(iv)), $[L:M]=\lvert H\rvert=q$ (`finrank_fixedField_eq_card`), $[M:K]\cdot q=n$, and $[M:K]<n$ (`:32–47`). The extensions $L/M$ and $M/K$ are Galois (`IsGalois.tower_top_of_isGalois`, `IsGalois.of_fixedField_normal_subgroup`) and cyclic: $\mathrm{Gal}(L/M)$ has prime order, and $\mathrm{Gal}(M/K)$ is the image of the cyclic group $G$ under the restriction map, which is onto (`AlgEquiv.restrictNormalHom_surjective`) (`:49–54`). The induction hypothesis applied to $M/K$ gives $[C_K:\mathrm{Nm}_{M/K}C_M]\ne0$, $\le[M:K]$; Proposition 5 applied to $L/M$ gives $[C_M:\mathrm{Nm}_{L/M}C_L]\ne0$, $\le q$ (`:55–56`). Since $\mathrm{Nm}_{L/K}=\mathrm{Nm}_{M/K}\circ\mathrm{Nm}_{L/M}$, the image of $\mathrm{Nm}_{L/K}$ is the image under $\mathrm{Nm}_{M/K}$ of the image of $\mathrm{Nm}_{L/M}$ (`:58–62`), and Lemma 4(iii) with $f=\mathrm{Nm}_{M/K}$, $H=\mathrm{Nm}_{L/M}C_L$ gives
$$
[C_K:\mathrm{Nm}_{L/K}C_L]\le[C_K:\mathrm{Nm}_{M/K}C_M]\cdot[C_M:\mathrm{Nm}_{L/M}C_L]\le[M:K]\cdot q=n,
$$
with the left side nonzero (`:63–67`). The passage to `SecondInequality` is Lemma 4(i) (`:69–72`). $\square$

The archive's induction differs from Milne's reduction in [MilneCFT, Ch. VII, §5, Lemmas 5.3–5.4, pp. 212–213] in two ways. Milne first reduces to $p$-groups by restricting to Sylow subgroups, then inducts using a normal subgroup $H$ of index $p$, so that the bottom step $L^H/K$ has prime degree; the archive stays inside cyclic groups, where every subgroup is normal, and uses a subgroup of prime order $q$, so that the top step $L/M$ has prime degree. The index inequality at the end is the same display as Milne's last line of Lemma 5.4. Milne's Lemma 5.4 also tracks $H^1$ and $H^2$; the archive tracks only the norm index, which is all that Theorem A needs.

**Theorem 7 (the Kummer case; `FirstInequality.secondInequalityRoots`).** [Lean; statement and proof skeleton read, the Kummer index lemma and the local inputs not read] Assume `FirstInequality` in universe $u$. Then `SecondInequalityRoots` holds in $u$: for a cyclic extension $L/K$ of prime degree $p$ with $\zeta_p\in K$, $\lvert C_K/\mathrm{Nm}_{L/K}C_L\rvert\le p$.

**Skeleton of the proof (`PowFinrankMemRangeInfiniteLocalNorm.lean:109–207`).** By Kummer theory $L=K(\alpha)$ with $\alpha^p=a\in K^\times$ (`exists_root_adjoin_eq_top_of_isCyclic`, Mathlib `Mathlib/FieldTheory/KummerExtension.lean`), and $a$ is not a $p$-th power in $K$, else $\alpha\in K$ (`:116–142`). Choose a finite set $S$ of primes of $K$ containing a set $S_0$ with $I_K=\Delta(K^\times)I_{K,S_0}$, all primes above $p$, and all primes where $a$ is not a unit (`:144–160`). The first inequality, in the form `FirstInequality.exists_places_index_map_powerSubgroup` (`KummerTheory/KummerIndexLemma.lean:136–145`) [Lean], produces a finite set $T$ of primes disjoint from $S$ with $\lvert T\rvert+1=\lvert S\rvert+r_\infty$, at which $a$ is a local $p$-th power, such that the subgroup $P(S,T)$ of ideles that are $p$-th powers at the places of $S$ and at the infinite places, arbitrary at $T$, and integral units elsewhere (`powerSubgroup`, `IdeleGroups/LocalConditionIndex.lean:147–149`) has image of index exactly $p$ in $C_K$ (`:162`). Then $P(S,T)\le\mathrm{Nm}(I_L)$ (`:164–189`), by the place-by-place criterion `mem_range_ideleNorm_of_forall` (`LocalNormsEverywhere.lean:69–73`, the direction of Corollary B of §11.4.3.6 that needs no restricted-product condition): at $v\in S$ and at infinite places, $p$-th powers are norms since $[L:K]=p$ (`pow_finrank_mem_range_finiteLocalNorm`, `pow_finrank_mem_range_infiniteLocalNorm`); at $v\in T$, $a$ is a local $p$-th power so $L_w=K_v$ and every element is a norm (`splitsCompletely_of_pow_eq`, `:51`) [Lean]; at $v\notin S\cup T$, the prime is unramified because $v\nmid p$ and $a$ is a $v$-unit (`Kummer.ramificationIdx_eq_one_of_pow_eq`, `KummerTheory/Unramified.lean:112`) [Lean], and the component is a unit, hence the norm of a unit by Proposition C of §11.4.3.5. So the image of $P(S,T)$ in $C_K$ is contained in $\mathrm{Nm}_{L/K}C_L$, the index of $\mathrm{Nm}_{L/K}C_L$ divides $p$ and is nonzero, and Lemma 4(i) concludes (`:194–204`). $\square$

This is the algebraic proof of [MilneCFT, Ch. VII, §6, pp. 214–218], with $r=1$: Milne's $T$ is chosen by the Frobenius density statement 4.7, itself a consequence of the first inequality, and the index of his $C_K(S,T)$ is computed from the unit theorem for $U(S)$; the archive packages both into `exists_places_index_map_powerSubgroup`. It is also Theorem (4.2) of [Neukirch1999, Ch. VI, §4, pp. 380–381]. The reading status of this theorem stays at the level of its statement and skeleton; the proof of the index lemma and the Kummer splitting statement belong to a later subsection if one is written.

**Theorem A (the class field axiom for cyclic extensions; `secondInequality`, `index_range_ideleClassNorm_eq_finrank`, `natCard_cycTateNegOne_ideleClassGroup`, `natCard_cycTateZero_ideleClassGroup_eq_finrank`, `classFieldAxiom_ideleClassGroup`).** [Lean, read; the inputs are Lemma 2(i), (ii) and Theorem 7] Let $L/K$ be a cyclic Galois extension of number fields in a fixed universe, $n=[L:K]$, and let $\sigma$ generate $G=\mathrm{Gal}(L/K)$. Then
(a) $[C_K:\mathrm{Nm}_{L/K}C_L]=n$;
(b) $\widehat H^{-1}_\sigma(C_L)=\ker(\mathrm{Nm})/(\sigma-1)C_L$ has exactly one element;
(c) $\widehat H^0_\sigma(C_L)=C_L^G/\mathrm{Nm}\,C_L$ has exactly $n$ elements.

**Proof.** (`Cyclic.lean:12–48`) `secondInequality` (`:12–13`) is Proposition 6 applied to Theorem 7 applied to Lemma 3's extended-cardinal form. (a) (`:20–24`): Lemma 3 gives $n\le[C_K:\mathrm{Nm}\,C_L]$ and nonzero; `secondInequality` with Lemma 4(i) gives $[C_K:\mathrm{Nm}\,C_L]\le n$; antisymmetry. (b) (`:26–34`): Lemma 3 gives $[C_K:\mathrm{Nm}\,C_L]=n\cdot\lvert\widehat H^{-1}_\sigma\rvert$; substituting (a), $n\cdot1=n\cdot\lvert\widehat H^{-1}_\sigma\rvert$, and cancelling $n>0$ (`Nat.eq_of_mul_eq_mul_left`) gives $\lvert\widehat H^{-1}_\sigma\rvert=1$. (c) (`:36–41`): Lemma 1 and (a). The conjunction (b) and (c) is `classFieldAxiom_ideleClassGroup` (`:43–48`). $\square$

The direction of each inequality should be kept in view. The first inequality, $n\le$ index, comes from the exact value $n$ of the Herbrand quotient and the trivial bound $\lvert\widehat H^{-1}\rvert\ge1$; it is analytic in Milne's Chapter VI and algebraic here, through the $S$-unit lattice. The second inequality, index $\le n$, is proved by exhibiting enough norms: a subgroup of index $p$ inside the norm group, in the Kummer case. The comparison then shows that the trivial bound was sharp. As Neukirch remarks at the opening of his §4 [Neukirch1999, Ch. VI, §4, p. 380], the identity $\widehat H^{-1}(G,C_L)=1$ "is curiously inaccessible by way of direct attack"; one proves $\lvert\widehat H^0\rvert=n$ instead and lets the Herbrand quotient do the rest. The archive follows this exactly. The groups being compared are finite: Lemma 2 establishes finiteness of both Tate groups before any order is computed, and the archive's convention that infinite sets have cardinality $0$ is what makes the nonvanishing clauses of Lemmas 3 and 4 necessary.

**Wiring to the consumer.** [Lean, read] Theorem A(b) is used once on the route of §11.4.3.4, at `HasseNorm.lean:33–35` inside `mem_range_norm_of_diagonal_mem_range_ideleNorm` (read in §11.4.3.4). There, for $x\in K^\times$ whose diagonal idele is $\mathrm{Nm}(j)$, the class $c=[j]\in C_L$ has $\sum_g g\cdot c=\iota(\mathrm{Nm}[j])=\iota[\Delta x]=0$, so $c\in\ker\mathrm{Nm}$; Theorem A(b) makes $\widehat H^{-1}_\sigma(C_L)$ a singleton (`Nat.card_eq_one_iff_unique`), so the class of $c$ is $0$ and $c=(\sigma-1)d$ for some $d$; lifting to ideles, $j=(\sigma e/e)\cdot\Delta a$ with $a\in L^\times$, and applying $\mathrm{Nm}$ gives $\Delta x=\Delta(\mathrm{Nm}\,a)$, hence $x=\mathrm{Nm}\,a$. With Corollary B of §11.4.3.6 this is Proposition C of §11.4.3.4, and through Lemma B there it feeds `hMinus` and the $\ell=2$ branch of `cyc` in §11.4.3.2. The other consumers of Theorem A in the archive, `LevelCyclic.lean:19,25` in the profinite class formation and `NatCardTateOfIsCyclic.lean:35`, lie off the Ferrero–Washington route and are not read.

**Remarks.** [Expository] *Finite modules versus the idele class group.* Examples 1 and 2 compute Tate groups of units, $S$-units and the integers $\mathbb Z$, which are finitely generated, and read the local degrees off the splitting of a few primes. These are the inputs of Lemma 2, not the idele class group. The orders $\lvert\widehat H^0(G,C_L)\rvert=n$ and $\lvert\widehat H^{-1}(G,C_L)\rvert=1$ are outputs of Theorem A and are not computed by hand in either example; what the examples supply is one explicit non-norm class for $\mathbb Q(i)$ (through the Hilbert symbol) and a candidate for $\mathbb Q(\zeta_7)^+$ whose nontriviality the book does not verify.

*Two shapes of the unit Herbrand quotient.* In Example 1 the units are finite and $h(E)=1$; the whole value $h(U(T))=2$ comes from the uniformizer at the ramified prime $2$. In Example 2 the unit lattice is $\mathbb Z[\zeta_3]$ with $h(E)=1/3$, which is cancelled by the uniformizer at $7$ to give $h(U(T))=1$. In both cases $h(C_L)=h(I_{L,T})/h(U(T))$ equals $n$, and in both the division by $n$ in Lemma 2(ii) is what produces it.

*Universes.* `SecondInequality` and `SecondInequalityRoots` are statements about all pairs of number fields in a fixed universe $u$, and Propositions 5 and 6 pass between extensions of different fields inside $u$: Proposition 5 moves from $L/K$ to $E/K'$ with $E=L(\zeta_p)$, and Proposition 6 moves from $L/K$ to $M/K$ and $L/M$ with $M$ an intermediate field. This is why the archive states the inequalities as universe-polymorphic propositions rather than as theorems about a fixed pair, and why the induction in Proposition 6 is over the degree with the fields quantified inside.

*Reading at the level of this subsection.* The Kummer index lemma `exists_places_index_map_powerSubgroup`, which is where the first inequality enters the proof of the second, and the local statements `splitsCompletely_of_pow_eq` and `Kummer.ramificationIdx_eq_one_of_pow_eq`; the two Herbrand suppliers `cycHerbrand_sIdeles` and `cycHerbrand_sUnitRep`, with the local Herbrand quotients and the lattice argument behind them; the fixed-point description `forall_smul_eq_iff_mem_range_ideleClassMap`; and the existence of $S$ with $I_L=\Delta(L^\times)I_{L,T}$. These enter as named inputs here. Section 11.4.3.8 reads both arithmetic suppliers and explains the common choice of places. The inertia inputs `ineCard` and `cycIne` of Lemma G in §11.4.3.4 are not on this route; they live in `GL/ClassFieldRamification/IneCard.lean:8` and `CycIne.lean:8` and remain [Lean].

**Reading boundary and source map.** Read in full here [Lean, read]: `natCard_cycTateNegOne_ideleClassGroup`, `index_range_ideleClassNorm_eq_finrank`, `natCard_cycTateZero_ideleClassGroup_eq_finrank`, `classFieldAxiom_ideleClassGroup`, `secondInequality`; `ideleClassToCycTateZero`, `ideleClassToCycTateZero_surjective`, `ker_ideleClassToCycTateZero`, `cycNorm_ideleClassGroup`, `natCard_cycTateZero_ideleClassGroup`, `index_range_ideleClassNorm`, `finrank_le_index_range_ideleClassNorm`, `firstInequality`; the assembly `cycHerbrand_ideleClassGroup` with `exists_finset_unramified_sup_sIdeles_eq_top`, `finrank_infiniteCompletion_eq_ite`, `finrank_adicCompletion_eq_ramificationIdxIn_mul`, `map_cycSubOne`, `map_cycNorm`; `enatCard_quotient_le_iff`, `index_le_of_comap_le`, `index_map_le`, `mem_of_pow_mem_of_coprime`, `mul_comm_of_isCyclic`, `pow_finrank_mem_range_ideleClassNorm`; `SecondInequalityRoots.index_le_of_prime`; `SecondInequalityRoots.index_le_of_finrank_eq`, `SecondInequalityRoots.secondInequality`; the definitions `cycSubOne`, `cycNorm`, `CycTateZero`, `CycTateNegOne`, `cycHerbrand`, `KerModRange`, `HasHerbrandQuotient`, `herbrandQuotient`, `SecondInequality`, `SecondInequalityRoots`, `FirstInequality`, with `mem_ker_cycSubOne_iff`, `range_cycSubOne_eq_closure`, `cycSubOne_cycNorm`, `cycNorm_cycSubOne`, `KerModRange.mk_eq_zero_iff`, `natCard_kerModRange_hexagon` (statement) and `herbrandQuotient_eq_mul_of_shortExact`. Statement and skeleton read, body not read [Lean]: `FirstInequality.secondInequalityRoots`. Named inputs not read here [Lean]: `cycHerbrand_sIdeles`, `cycHerbrand_sUnitRep`, `hasHerbrandQuotient_sUnitRep`, `sUnits_sIdeles_placesAbove_exact`, `exists_finset_superset_sup_sIdeles_placesAbove_eq_top`, `HasHerbrandQuotient.of_shortExact_left_mid`, `forall_smul_eq_iff_mem_range_ideleClassMap`, `smul_ideleClassMap`, `ideleClassMap_ideleClassNorm`, `ideleClassNorm_ideleClassMap`, `ideleClassNorm_ideleClassNorm`, `ideleClassMap_injective`, `exists_places_index_map_powerSubgroup`, `splitsCompletely_of_pow_eq`, `Kummer.ramificationIdx_eq_one_of_pow_eq`, `exists_finset_sup_sIdeles_eq_top`, and the Mathlib declarations `exists_root_adjoin_eq_top_of_isCyclic`, `Subgroup.index_comap`, `Subgroup.index_map`, `Subgroup.index_dvd_of_le`, `IsGalois.of_fixedField_normal_subgroup`, `AlgEquiv.restrictNormalHom_surjective`, `IsSplittingField.mul`. Inherited: `mem_range_ideleNorm_of_forall` and Corollary B (§§11.4.3.5–11.4.3.6), Proposition C of §11.4.3.5, the deduction in `HasseNorm.lean` (§11.4.3.4). The reading status of the full Ferrero–Washington dependency cone remains as in §11.4.3.

| Source and lines | Role and reading |
|---|---|
| `GT/SecondInequality/Cyclic.lean:12–48` | [Lean, read] Theorem A: `secondInequality`, index $=n$, $\lvert\widehat H^{-1}\rvert=1$, $\lvert\widehat H^0\rvert=n$. |
| `GT/FirstInequality.lean:15–110` | [Lean, read] Lemma 1 (`:15–76`), Lemma 3 (`:78–110`). |
| `GT/FirstInequality/HerbrandClass.lean:22–31,42–65,73–87,93–180` | [Lean, read] Equivariance lemmas, local degree conversions, choice of $S$, assembly of Lemma 2. |
| `GT/HerbrandQuotients/CycTate.lean:99–185` | [Lean, read] Definitions of $\sigma-1$, $\mathrm{Nm}$, the Tate groups and the Herbrand quotient. |
| `src/GroundTheory/TateCohomology/HerbrandAbstract.lean:36–43,50–52,334–342,363–373,387–403` | [Lean, read] `KerModRange`, `HasHerbrandQuotient`, `herbrandQuotient`; hexagon count and multiplicativity, statements read, `:363–373` named. |
| `GT/SecondInequality/Statement.lean:12–70` | [Lean, read] Lemma 4, `SecondInequalityRoots`, `pow_finrank_mem_range_ideleClassNorm`. |
| `GT/SecondInequality/PrimeDegree.lean:15–99` | [Lean, read] Proposition 5. |
| `GT/SecondInequality/Reduction.lean:10–72` | [Lean, read] `SecondInequality`, Proposition 6. |
| `GT/SecondInequality/PowFinrankMemRangeInfiniteLocalNorm.lean:51,109–207` | [Lean] Theorem 7, statement and skeleton read. |
| `GT/FirstInequalityStatement.lean:8–11` | [Lean, read] `FirstInequality`. |
| `GT/IdeleGroups/SIdeleHerbrand.lean:68–78`, `GT/HerbrandQuotients/SUnits.lean:22–25,50–55` | [Lean] Lemma 2(i), (ii), statements read. |
| `GT/IdeleGroups/SIdeleGroups.lean:15–19,81–91`, `GT/IdeleGroups/SIdeleGroups/Galois.lean:75–76,131,144–150` | [Lean] $S$-ideles, $S$-units, places above, exactness; statements read. |
| `GT/IdeleGroups/IdeleNorms/BaseChange.lean:202–208,228,246`, `GT/IdeleGroups/GaloisOnAdeles/Action.lean:252,267–275`, `GT/IdeleGroups/IdeleNorms/InfiniteAdeleRingMapInfiniteAdeleRingMap.lean:122–125` | [Lean] Class maps and norms and their identities; statements read. |
| `GT/KummerTheory/KummerIndexLemma.lean:136–145`, `GT/KummerTheory/Unramified.lean:112`, `GT/IdeleGroups/LocalConditionIndex.lean:66–70,147–149`, `GT/IdeleGroups/LocalNormsEverywhere.lean:69–73` | [Lean] Inputs to Theorem 7; `:69–73` inherited from §11.4.3.5. |
| `GT/HasseNorm.lean:33–35` | [Lean, read] Consumer (inherited from §11.4.3.4). |
| Mathlib `0df444a`: `Mathlib/FieldTheory/KummerExtension.lean` (`exists_root_adjoin_eq_top_of_isCyclic`), `Mathlib/GroupTheory/Index.lean:84,112,309` (`index_comap`, `index_dvd_of_le`, `index_map`) | [Lean] Statements located in the pinned source. |

Here `GT/` expands to `src/GroundTheory/GlobalFields/` and `GL/` to `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/`.

#### 11.4.3.8 The two arithmetic suppliers of the Herbrand quotient

The identity $h_G(C_L)=[L:K]$ comes from using the same places twice. The local degrees appear both in the idele group with prescribed unit coordinates and in the representation of the corresponding global units. The factor that survives division comes from the product formula.

**Examples.** In $\mathbb Q(i)/\mathbb Q$ the finite place $2$ and the real place both have local degree $2$. In $\mathbb Q(\zeta_7)^+/\mathbb Q$ the place $7$ has local degree $3$, and each of the three real completions has degree $1$. The idele quotients are $4$ and $3$ and the unit quotients are $2$ and $1$. The calculations below give the Tate group orders as well.

**Definitions.** Let $L/K$ be a finite cyclic extension of number fields with $G=\langle\sigma\rangle$ and $n=[L:K]$. Let $S$ be a finite set of finite places of $K$, and $T$ all finite places of $L$ above $S$. Infinite places are included separately. Write $I_T$ for the subgroup of $I_L$ with coordinates in $U_w=\mathcal O_{L_w}^{\times}$ at finite $w\notin T$, and $E_T$ for the subgroup of $L^\times$ with valuations zero there. The action on tuples is $(ga)_w=g(a_{g^{-1}w})$, using the induced map of completions. On $E_T$ it is the field action and on $C_L=I_L/L^\times$ it is the quotient action. Choose $w\mid v$ and put $D_w=\operatorname{Stab}_G(w)$ and $d_v=[L_w:K_v]=|D_w|$. Transitivity makes the degree independent of $w$. At finite places $d_v=e_vf_v$. At infinite places $d_v=\epsilon_v$, equal to $2$ for real-to-complex and $1$ otherwise.

In additive notation let $D=\sigma-1$ and $N=\sum_{g\in G}g$. The two Tate groups are $\ker D/\operatorname{im}N$ and $\ker N/\operatorname{im}D$, in degrees $0$ and $-1$. Write $h_G$ for the ratio of their orders when both are finite. For a short exact sequence $0\to A\to B\to C\to0$, the cyclic Tate sequence is an exact hexagon. Finiteness for two modules implies it for the third by exactness. Multiplying alternate orders gives $h_G(B)=h_G(A)h_G(C)$. For a finite module both groups have order $|M|/(|\operatorname{im}D||\operatorname{im}N|)$. For a finitely generated abelian module they are finite because they are finitely generated and killed by $n$, using $n-N\in(\sigma-1)\mathbb Z[G]$. In multiplicative notation $N$ is a product.

**Lemma 1 (the idele supplier).** Suppose every finite $v\notin S$ is unramified in $L$. Both Tate groups of $I_T$ are finite, $\widehat H^{-1}(G,I_T)$ is trivial, and $h_G(I_T)=\prod_{v\mid\infty}d_v\prod_{v\in S}d_v$. [Lean, read] The archive's **cycHerbrand_sIdeles** states finiteness and the quotient, with a choice of a place above each base place.

*Proof.* Split $I_T$ into the product of full completion groups at the infinite places, full completion groups over $S$, and integral unit groups at the remaining places. To assemble an idele, return each coordinate to its place. The tuple and its inverse are integral off the finite set $T$. Conversely zero valuation outside $T$ gives the integral-unit coordinates uniquely. The coordinate action preserves the three families, since each $g$ preserves the underlying $K$-place. This is the equivariant isomorphism **sIdelesEquivProduct**.

For each $v$ the product over $w\mid v$ is coinduced from $D_w$ with fibre $L_w^\times$ or $U_w$. Moving a tuple supported at $w$ transports its support to $gw$, and the stabilizer acts on that coordinate by the completion action. To see both cyclic Tate isomorphisms explicitly, write $r=[G:D_w]$, use $\sigma^j$ to identify each fibre with the first, and put $\tau=\sigma^r$. In additive notation the shift sends $(a_0,\ldots,a_{r-1})$ to $(\tau a_{r-1},a_0,\ldots,a_{r-2})$. Invariants are constant tuples with value fixed by $\tau$. Each norm coordinate is $N_{D_w}(\sum_j a_j)$. Modulo $(\sigma-1)$ a tuple is equivalent to its sum in the first coordinate: generators in consecutive coordinates become equal, and the wraparound identifies $a$ with $\tau a$. Evaluation on invariants and summation on the norm kernel therefore give the two Tate isomorphisms with the fibre. The archive uses these orbit equivalences with support transport and verifies that the stabilizer actions agree by extending the field action to the completion.

At finite $v\in S$, the cyclic local-field Herbrand theorem gives $h_{D_w}(L_w^\times)=d_v$ with finite Tate groups, and Hilbert 90 gives $\widehat H^{-1}=0$. At an infinite place of degree one the stabilizer is trivial. For real-to-complex the invariants of conjugation are $\mathbb R^\times$, the norms are $\mathbb R_{>0}$, and every norm-one element is $\bar z/z$. The two orders are $(2,1)$. For finite $v\notin S$, the norm on $U_w$ is onto the base units by §11.4.3.5. If $u\in U_w$ has norm one, Hilbert 90 gives $u=\tau b/b$. Divide $b$ by a power of a base uniformizer to make it a unit, using $e_v=1$. Both Tate groups of that fibre are trivial.

Kernels commute with arbitrary products, and so do images of the coordinatewise maps, by independent choices of preimages. Thus the entire outside product has trivial Tate groups. The remaining finitely many orders multiply. In Lean, **cycHerbrand_integerUnitsOutside** first proves both subsingleton statements. Positivity of the final product then certifies finiteness under the archive's cardinality convention. $\square$

**Lemma 2 (the unit supplier).** Let $T$ be any finite $G$-stable set of finite places of $L$ and let $S$ be its image in $K$. Then $E_T$ has finite Tate groups and $h_G(E_T)=\prod_{v\in S}e_vf_v\prod_{v\mid\infty}\epsilon_v/n$. Stability and finiteness suffice for this supplier. [Lean, read] **cycHerbrand_sUnitRep** and **hasHerbrandQuotient_sUnitRep**.

*Proof.* Stability and transitivity give entire fibres over $S$. Write $E=\mathcal O_L^\times$. The inclusion and valuation map in $0\to E\to E_T\xrightarrow{\operatorname{ord}_T}\mathbb Z^T$ are equivariant since $\operatorname{ord}_w(ga)=\operatorname{ord}_{g^{-1}w}(a)$. Zero valuations throughout characterize the kernel $E$. Put $b=|\operatorname{Cl}(L)|>0$. For each $w\in T$ the $b$-th power of its prime ideal has a generator, which is a $T$-unit. Taking products and inverse powers gives every vector in $b\mathbb Z^T$ as a valuation vector. The composite using the archive's **placeUnitsMap** gives $-b$ times the vector, which gives the same containment. The cokernel is thus finite and $E_T$ is finitely generated, since the valuation image and $E$ are. Apply the hexagon to the inclusion of the valuation image in $\mathbb Z^T$ and to the surjection onto that image. It follows that $h_G(E_T)=h_G(E)h_G(\mathbb Z^T)$.

On a transitive orbit the permutation lattice has invariants generated by the constant vector. The norm of a coordinate generator is $|D_w|$ times that vector. The norm kernel consists of the vectors of sum zero and is generated by successive coordinate differences. Hence the two Tate orders are $(|D_w|,1)$. This gives $\prod_{v\in S}e_vf_v$ for the finite-place permutation representation.

For ordinary units let $X$ be the infinite places of $L$, one coordinate per real embedding or complex conjugate pair. Use coordinates $\log|w(a)|$ at real places and $2\log|w(a)|$ at complex places with the ordinary absolute value of the representative embedding. The map intertwines the permutation and field actions since $G$ preserves these multiplicities. Its kernel is the finite roots-of-unity group. The product formula places its image $\Lambda$ in the sum-zero hyperplane, and Dirichlet's unit theorem makes $\Lambda$ a full lattice there. Since $X$ is nonempty the constant vector spans a complementary real line, and $(\lambda,k)\mapsto\lambda+k\mathbf 1$ gives a real equivariant isomorphism between the extensions of $\Lambda\oplus\mathbb Z$ and $\mathbb Z^X$.

The comparison of these integral representations requires a finite-index argument. Given two finite-rank free integral representations with equivariantly isomorphic real extensions, the intertwiner equations in bases are rational linear equations. Row reduction gives a rational solution basis that also spans the real solutions. The determinant polynomial in the basis coefficients is nonzero at the given real isomorphism, so it is nonzero at some rational point. Clearing denominators gives an injective integral intertwiner with finite cokernel. The hexagon and the finite-module computation imply equality of Herbrand quotients. This compares the lattices even if their original embeddings in the real space have different rational spans.

The finite logarithmic kernel gives $h_G(E)=h_G(\Lambda)$. The added trivial line contributes $h_G(\mathbb Z)=n$, and the orbit calculation gives $h_G(\mathbb Z^X)=\prod_{v\mid\infty}\epsilon_v$. Dividing by $n$ completes the calculation. $\square$

**Theorem (assembly on the same set).** Choose $S$ containing all finite ramified places and large enough that the classes of the primes in $T$ generate $\operatorname{Cl}(L)$. Then $1\to E_T\to I_T\to C_L\to1$ is an exact sequence of $G$-modules, the Tate groups of $C_L$ are finite, and $h_G(C_L)=n$. [Lean, read]

*Proof.* The finite valuations give an onto map from ideles to fractional ideals. Class generation lets us choose an ideal supported in $T$ in the class of the ideal of any idele. Dividing that idele by a generator of the principal quotient ideal gives a representative in $I_T$. The kernel consists of principal ideles in $I_T$, exactly the diagonal image of $E_T$. Both maps commute with $G$ by the diagonal and quotient actions. Such an $S$ exists by taking the places below finitely many primes generating $\operatorname{Cl}(L)$ and adjoining the ramified places. The class generation condition is equivalent to the join of $I_T$ with the principal ideles being all of $I_L$.

The two lemmas apply to exactly these modules and to the same $\sigma$ and norm. Finiteness for $C_L$ follows from the hexagon. Its quotient is $h_G(I_T)/h_G(E_T)=n$, because the same positive local-degree product occurs twice. This supplies the first inequality in §11.4.3.7. The subsequent Kummer argument uses **exists_places_index_map_powerSubgroup** (KummerTheory/KummerIndexLemma.lean:136–180, prior reading). $\square$

**Example 1 in full.** Take $L=\mathbb Q(i)$, $S=\{2\}$ and $\sigma$ complex conjugation. The Gaussian integers are Euclidean for the squared absolute value, so the class generation condition holds. At $2$, $\pi=1+i$ generates the unique prime and $2=-i\pi^2$. Thus $(e,f)=(2,1)$ and the full fibre is $\mathbb Q_2(i)^\times$ with Tate orders $(2,1)$. At odd $p\equiv1\bmod4$ the two split unit factors have trivial stabilizer. At odd $p\equiv3\bmod4$ the single unit factor is unramified quadratic. Both kinds contribute $(1,1)$. The infinite fibre is $\mathbb C^\times$ over $\mathbb R^\times$ with orders $(2,1)$. Thus $I_T$ has orders $(4,1)$.

The ordinary units are $\mu_4=\langle i\rangle$. On this finite module conjugation inverts, so the norm is trivial, the invariants are $\{\pm1\}$ and the image of $D$ is $\{\pm1\}$. The two orders are $(2,2)$. The actual $T$-unit group is $\mu_4\cdot\pi^{\mathbb Z}$. Its fixed subgroup is $\langle-1,2\rangle$, its norms are $2^{\mathbb Z}$ and its norm kernel is $\mu_4$. Since $\bar\pi/\pi=-i$, the image of $D$ contains all of $\mu_4$. Thus $E_T$ has orders $(2,1)$ and quotient $2$. The finite valuation lattice is trivial as a representation and contributes $2$, and the ordinary-unit quotient is $1$. The generator $-1$ of $\widehat H^0(G,E_T)$ is nontrivial at the infinite coordinate, so the map into $\widehat H^0(G,I_T)$ is injective. The hexagon gives orders $(2,1)$ for $C_L$, and the quotient is $4/2=2$.

**Example 2 in full.** Take $L=\mathbb Q(\zeta_7)^+$, $S=\{7\}$, and the generator induced by $\zeta_7\mapsto\zeta_7^2$. The element $\theta=\zeta_7+\zeta_7^{-1}$ has polynomial $x^3+x^2-2x-1$ of discriminant $49$. The element $\pi=2-\theta$ has polynomial $x^3-7x^2+14x-7$, Eisenstein at $7$, and norm $7$. There is a unique place above $7$ with $(e,f)=(3,1)$ and uniformizer $\pi$. The field discriminant is $49$, since ramification at $7$ rules out index $7$ in the order of discriminant $49$. The totally real cubic Minkowski bound is $3!\sqrt{49}/3^3=14/9<2$, so the class number is one.

At $7$ the full fibre $\mathbb Q_7(\theta)^\times$ has Tate orders $(3,1)$. For $p\ne7$ the Frobenius acts by $p$ in $(\mathbb Z/7)^\times/\{\pm1\}$. For $p\equiv\pm1\bmod7$ there are three split unit factors, and otherwise one unramified cubic unit factor. Both have orders $(1,1)$ as orbit modules. The three real factors form one orbit with trivial stabilizer and contribute $(1,1)$, so $I_T$ has orders $(3,1)$.

Ordinary units have torsion $\{\pm1\}$ and rank two. The norm on the torsion group is the identity and the norm on the free quotient is zero. The free quotient has rational representation with minimal polynomial $x^2+x+1$: its logarithmic real representation is the sum-zero subspace of the three-cycle. Thus $\sigma-1$ has determinant $3$ on the free quotient, with zero invariant subgroup. The two Tate orders for ordinary units are $(1,3)$, including torsion since its Tate groups are trivial. This argument uses the actual integral lattice and requires no choice of fundamental units. The finite valuation lattice at $7$ contributes $3$, so the $T$-unit quotient is $1$. More explicitly, $E_T=E\cdot\pi^{\mathbb Z}$, with invariants $\langle-1,7\rangle$ and norms containing both generators, since $N(-1)=-1$ and $N(\pi)=7$. Its degree-zero Tate group is trivial, so degree $-1$ is trivial by the computed quotient. The hexagon identifies the degree-zero Tate group of $C_L$ with that of $I_T$ and gives a trivial degree $-1$ group. The quotient is $3/1=3$.

A finite test of the cubic operators is $\mathbb F_3$ with trivial action. Both $D$ and $N$ vanish, so the orders are $(3,3)$ and its quotient is $1$. The free rank-two lattice above gives $(1,3)$, since the sum-zero representation has no invariants and its determinant gives the index. The finite calculation by itself gives neither of those lattice orders. The actual modules $E_T$, $I_T$ and $C_L$ in both examples are infinite. For $C_L$, the absolute idele norm descends by the product formula and maps onto $\mathbb R_{>0}$. All displayed pairs are orders of Tate groups of the indicated module.

**Remark (deleting a hypothesis).** Keep the Gaussian example but take $S=\varnothing$. Class generation still holds. At $2$ one must now use integral units. The exact valuation sequence for $\mathbb Q_2(i)^\times$ has trivial-action quotient $\mathbb Z$ with Herbrand quotient $2$, so the integral units contribute $2/2=1$. They have nontrivial degree $-1$ Tate group: $\bar\pi/\pi$ is a unit of norm one, and if it came from a unit by $D$, the two preimages would differ by a base element. Such an element has even valuation upstairs and cannot change valuation one into zero. More precisely the valuation sequence gives degree $-1$ of order $2$, and degree zero then also has order $2$. Thus the outside product has nontrivial Tate groups and the idele orders become $(4,2)$. The quotient still agrees with the empty-set product. In general a ramified omitted fibre has quotient $d_v/|D_w|=1$ by the same valuation computation, but its two Tate groups can be nontrivial. Consequently the missing unramified hypothesis breaks the termwise vanishing and the group-order calculation. Separately, the image of $I_T$ in $C_L$ has cokernel $\operatorname{Cl}(L)/\langle[w]:w\in T\rangle$. Class-group finiteness controls the size of this error, whereas the short exact sequence with target $C_L$ requires it to vanish. For example, take the degree-one cyclic extension $L=K=\mathbb Q(\sqrt{-5})$ and $S=\varnothing$. The prime above $2$ of norm $2$ is nonprincipal, since $a^2+5b^2=2$ has no integral solution. The ideles with unit coordinates at every finite place then miss its class.

**Classical sources and reading boundary.** Milne VII, Proposition 2.7 (p. 206), Proposition 3.1 and Lemmas 3.2, 3.4 and 3.5 (pp. 208–209), Lemma 4.2 and Theorem 4.3 (pp. 210–211) give the local product, lattice comparison and assembly. Milne includes infinite places in his $S$ and uses one logarithmic lattice on all selected places. The archive adds the finite valuations after computing the ordinary-unit lattice. Neukirch VI §3 gives the corresponding local product, lattice and assembly in (3.3)–(3.6), pp. 375–378. [Paper] [Milne](https://www.jmilne.org/math/CourseNotes/CFT.pdf) · [Neukirch](https://web.math.ucsb.edu/~agboola/teaching/2021/fall/225A/neukirch.pdf)

The fixed archive is **lean.tar.gz**, SHA-256 **9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc**. Paths below are relative to **src/GroundTheory/GlobalFields/**. Reading refers to the source proofs.

| Source | Reading and role |
|---|---|
| IdeleGroups/SIdeleHerbrand.lean:21–104 | [Lean, read] Nonempty fibres, outside product, and complete idele calculation. |
| IdeleGroups/SIdeleGroups/Decomposition.lean:25–190 | [Lean, read] Equivariant decomposition and reconstruction. |
| IdeleGroups/SIdeleHerbrand/Places.lean:25–123,153–228 and IdeleGroups/SIdeleHerbrand/Product.lean:143–225 | [Lean, read] Support, stabilizer compatibility, both orbit Tate equivalence wrappers, and product. |
| IdeleGroups/LocalHerbrand.lean:160–190,223–296 and IdeleGroups/LocalHerbrandInfinite.lean:217–267 | [Lean, read] Transport to the local-field and archimedean results. |
| HerbrandQuotients/SUnits.lean:22–70, HerbrandQuotients/SUnitsExact.lean:13–82, HerbrandQuotients/SUnitsRep.lean:19–109, and HerbrandQuotients/SUnitsPerm.lean:17–80,114–157 in the same directory | [Lean, read] Finiteness, valuation exactness up to finite cokernel, and orbit factors. |
| HerbrandQuotients/UnitsHerbrandValue.lean:24–147 and HerbrandQuotients/Lattice.lean:11–34,118–144 | [Lean, read] The constant line, real comparison, and cancellation of the trivial factor. |
| HerbrandQuotients/UnitsHerbrand.lean:21–55,92–110,112–176 and SUnits.lean:116–125 | [Lean, read] Weighted logarithm, finite kernel, and the signed class-number multiple. |
| FirstInequality/HerbrandClass.lean:42–87,93–180 and IdeleGroups/SIdeleGroups/Galois.lean:105–152 | [Lean, read] Common set, equivariance, and cancellation. |
| Also used by name | [Lean] The deeper finite-local theorem **LocalField.cycHerbrand_units_eq_finrank**, local Hilbert 90, the generic orbit-equivalence internals, decomposition-group equivalences, Dirichlet's theorem underlying **unitLattice**, and the rational matrix construction **exists_injective_intertwiner_of_basis**. |
| KummerTheory/KummerIndexLemma.lean:136–180 and §11.4.3.5 | Inherited: Kummer selection and unramified norm on units. |

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

### 11.4.5 From two zero annihilators to a perfect local cup pairing

**Motivation.** The cyclic norm criterion explains how a local cup class vanishes. Its two annihilator consequences tell us that each nonzero class is detected by some class on the other side. A perfect pairing gives a stronger answer. Every character on either side must be evaluation against a class on the other side, and that class must be unique. The proof starts with the finite quotient of field units by powers, uses Kummer theory to bound one cohomology group, and closes a cycle of four inequalities. This is the degree-$(1,1)$ root-of-unity input to the local duality package. [Lean, read] A2, `LocalTateDuality/EqZeroOfForallCupPairingZmodMulEqZeroLeft.lean:38–66,117–149`. [Source ledger](../sources/SOURCES.md#chapter-11-finite-perfect-local-cup-pairing)

**Two examples to keep in view.** Over $\mathbb Q_3$, the square classes are generated by $3$ and $-1$. Two quadratic characters distinguish these coordinates. Over $\mathbb Q_5$, the tenth-power quotient has a valuation coordinate of order $10$, a residue-unit coordinate of order $2$, and a principal-unit coordinate of order $5$. The last coordinate pairs with a wild character. A perfect matrix in the second example tests characters on cyclic groups of different orders.

**The objects.** Let $K$ be a non-archimedean local field, $\Omega$ a chosen separable closure, $G_K=\operatorname{Gal}(\Omega/K)$ with the Krull topology, and $U\le G_K$ any open subgroup. Put $F=\Omega^U$. Galois correspondence and the local-field structure on finite separable extensions make $F$ a non-archimedean local field. Restricting scalars identifies $G_F$ topologically with $U$ inside $G_K$, with its given action on the very same $\Omega$. This works for nonnormal $U$. Let $n$ be a natural number satisfying $(n:K)\ne0$. The injection $K\hookrightarrow F$ gives $(n:F)\ne0$, and $n\ge1$.

For this $U$ set
$$
X=H^1_{\mathrm{cts}}(U,\mathbb Z/n),\qquad
Y=H^1_{\mathrm{cts}}(U,\mu_n(\Omega)),\qquad
Z=H^2_{\mathrm{cts}}(U,\mu_n(\Omega)).
$$
The first action is trivial and the root module carries its restricted Galois action. Cohomology uses discrete coefficients. The coefficient pairing is $(j,\zeta)\mapsto\zeta^j$. It gives the cup product $\beta:X\times Y\to Z$. Here $X=\operatorname{Hom}_{\mathrm{cts}}(U,\mathbb Z/n)$, since for the trivial action the cocycle equation is the homomorphism equation and the degree-one coboundaries are zero. The roots of $T^n-1$ in $\Omega$ form a cyclic group of order $n$, since the polynomial is separable and splits in $\Omega$. The resulting abstract cyclic group identification does not trivialize its action.

Let $t=\operatorname{localInvRootsOfUnity}_{K,\Omega,n,U}:Z\overset{\sim}{\longrightarrow}\mathbb Z/n$, and let $j_n:\mathbb Z/n\hookrightarrow\mathbb Q/\mathbb Z$ send $j$ to $[j/n]$. The defining normalization is $j_n(t(c))=\operatorname{inv}_F(i(c))$, where $i$ is the Kummer degree-two inclusion into $H^2_{\mathrm{cts}}(U,\Omega^\times)$. Indeed, Hilbert 90 makes $i$ injective, exactness identifies its image with the kernel of multiplication by $n$, and the local Brauer invariant identifies this kernel with $(\mathbb Q/\mathbb Z)[n]$. The archive identifies the two ranges and inverts $j_n$ on that common range. The local invariant and Hilbert 90 enter here as named inputs. [Lean, read] `LocalTateDuality/InjectiveCohomologyMapKummerSeqOpenFTwo.lean:82–93,137–219`.

We use the two established annihilator statements for this exact cup. For each $x\in X$, if $\beta(x,y)=0$ for all $y\in Y$, then $x=0$. For each $y\in Y$, if $\beta(x,y)=0$ for all $x\in X$, then $y=0$. They use norm detection and norm separation through the cyclic Kummer cup criterion. Their common field is $F$ and every norm test is in the fixed field of the corresponding character kernel in $\Omega$. [Lean] `LocalTateDuality/EqZeroOfForallCupPairingZmodMulEqZeroLeft.lean:68–115`, with `LocalTateDuality/NormCharacters.lean:38–139` and `LocalTateDuality/KummerCup.lean:225–252`.

**Lemma 1 (the supply of finite power quotients).** Let $F$ be a non-archimedean local field and $(n:F)\ne0$. Write $v$ for the additive valuation with $v(\pi)=1$, $\mathcal O$ for the valuation ring, $\mathfrak m=(\pi)$, $k=\mathcal O/\mathfrak m$, and $q=|k|$. Put $V_0=\mathcal O^\times$ and $V_j=1+\mathfrak m^j$ for $j\ge1$. Then $P=(F^\times)^n$ is open and $F^\times/P$ is finite. Explicitly, with $d=v(n)$ and $N=2d+1$, there is a surjection
$$
\{0,\ldots,n-1\}\times (\mathcal O^\times/V_N)
 \longrightarrow F^\times/P,\qquad (r,\bar u)\longmapsto[\pi^r u],
$$
and $[\mathcal O^\times:V_N]=(q-1)q^{N-1}$.

*Proof.* Reduction $\mathcal O^\times\to k^\times$ is onto, since any lift of a nonzero residue is a unit. Its kernel is $V_1$. At each $j\ge1$, write a member of $V_j$ uniquely as $1+\pi^j a$. The map to $\bar a\in(k,+)$ is additive under multiplication, since the product has coefficient $a+b+\pi^jab$. Its kernel is $V_{j+1}$, and each residue has a lift $a$ for which $1+\pi^j a$ is a unit. Thus the successive indices are $q$. Multiplying indices gives the formula, including $N=1$. These are the residue map, graded coefficient map and finite-index instance of `LocalFields/UnitsBasic.lean:275–293,306–374,376–410`. [Lean, read] [Serre, *Local Fields*, IV §2, Proposition 6, pp. 66–67](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Serre-Local.pdf)

Write $n=\pi^d\epsilon$ in $\mathcal O$ with $\epsilon$ a unit and let $w\in V_N$. For $f(T)=T^n-w$, Taylor expansion at $1$ gives
$$
f(1+\pi^{d+1}T)=\pi^{2d+1}\bigl(c+\epsilon T+\pi T^2 h(T)\bigr),
\qquad c=(1-w)/\pi^{2d+1},\qquad h(T)\in\mathcal O[T].
$$
The linear term has valuation factor $\pi^{2d+1}$ and every term of degree at least two has factor $\pi^{2d+2}$. The polynomial in parentheses, say $g$, has residue root $-\bar c/\bar\epsilon$ with nonzero derivative. To see the completeness step used by the archive, start at any lift $a_0$ of this root. Set $a_{i+1}=a_i-g(a_i)/g'(a_i)$. Inductively $g'(a_i)$ is a unit, $a_{i+1}\equiv a_i\bmod\mathfrak m$, and $g(a_i)\in\mathfrak m^{i+1}$. The polynomial identity for $g(a_i+h)$ cancels the constant and linear terms for this choice of $h$ and makes the new error divisible by $\mathfrak m^{2(i+1)}$. The sequence converges in the complete ring and its limit satisfies $g=0$ since the ring is separated and polynomial evaluation is continuous. Then $1+\pi^{d+1}\lim_i a_i$ is a unit whose $n$-th power is $w$. This proves $V_N\subset P$ including $d>0$. The formal root supplier performs the same rescaling and uses the compatible residues of the Newton sequence. [Lean, read] `LocalFields/UnitsPowers.lean:12–15,28–31,156–182` and `Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsRootOfAdicComplete.lean:7–84,86–130,134–152`. [Milne, *Algebraic Number Theory*, §7, Proposition 7.31 and Theorem 7.32, pp. 119–121](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

The image of $V_N$ in $F^\times$ is the open ball condition $v(x-1)\ge N$. The power image is a union of its cosets, hence open. For finiteness, the map $\mathcal O^\times\to F^\times/P$ kills $V_N$ by the unit root just constructed. Each $x\in F^\times$ has unique coordinates $x=\pi^a u$ with $a\in\mathbb Z$ and $u\in\mathcal O^\times$. Divide $a=r+nb$ with $0\le r<n$, also when $a<0$. The factor $(\pi^b)^n$ disappears, proving the displayed surjectivity. In the code, $\pi^b$ is the explicit power witness in the quotient equality. This argument uses finiteness of the residue field for the index, discreteness for the uniformizer and integer division, completeness for the root, and the nonzero **field** cast for $d$. [Lean, read] `LocalFields/UnitsPowers.lean:195–235`, `LocalFields/UnitsBasic.lean:145–257` and `LocalFields/ExistsUnitFiltrationUnitsLeAndRangePowLe.lean:12–47,49–59,108–125,194–200`. $\square$

**Lemma 2 (finite Kummer cohomology).** For the original $U$ and root module, $Y$ is finite and killed by $n$.

*Proof.* The $n$-th power sequence on $\Omega^\times$ is short exact since every $T^n-a$ with $a\ne0$ is separable and has a root in $\Omega$. On invariants the unit group is $F^\times$. Exactness and $H^1_{\mathrm{cts}}(U,\Omega^\times)=0$ give
$$
F^\times\xrightarrow{(\cdot)^n}F^\times
 \xrightarrow{\kappa_n}Y\longrightarrow0.
$$
For $a\in F^\times$, $\kappa_n(a)$ is the class of $g\mapsto g(A)/A$ for $A^n=a$. Another root changes it by a coboundary, and choosing the product of two lifts proves $\kappa_n(ab)=\kappa_n(a)+\kappa_n(b)$. Thus it factors through $F^\times/P$, where its kernel is trivial by exactness. The proof of finiteness in Lean uses the surjection alone. It packages the map as a homomorphism from units into the multiplicative wrapper of $Y$, using the map from fixed-field units, $(H^0\text{ comparison})^{-1}$ and the connecting map. The image of the power homomorphism lies in its kernel. It descends by the quotient lift and gives a preimage of $y$ by choosing a unit representative for $\kappa_n$. Lemma 1 supplies the finite domain. The quotient is killed by $n$, as is $Y$. [Lean, read] `LocalTateDuality/EqZeroOfForallCupPairingZmodMulEqZeroLeft.lean:23–66` and `LocalTateDuality/KummerCup.lean:109–150,181–189`. $\square$

**Lemma 3 (finite character count).** For $n\ge1$ and a finite abelian group $A$, write $A^\vee_n=\operatorname{Hom}(A,\mathbb Z/n)$. Then $|A^\vee_n|\le |A|$. If $nA=0$, then $|A^\vee_n|=|A|$.

*Proof.* Postcomposition with $j_n$ is injective: $[m/n]=[0]$ exactly when $n\mid m$. Next send $f:A\to\mathbb Q/\mathbb Z$ to the character $a\mapsto\exp(2\pi i f(a))$ into $\mathbb C^\times$. The exponential here is well defined on a rational class and has trivial kernel. Distinct characters $\chi,\psi$ are orthogonal in $\mathbb C^A$. In fact $\lambda=\psi\chi^{-1}$ is a nontrivial character. For a $b$ with $\lambda(b)\ne1$, translation gives $\sum_a\lambda(a)=\lambda(b)\sum_a\lambda(a)$, so the sum is zero. Values have absolute value one by finite order, and each character has squared norm $|A|$ with the unnormalized inner product. Taking the inner product with one character at a time gives linear independence of every finite family, so there can be at most $|A|$ characters. This is the code's inequality, with an intermediate rational-to-real circle embedding and Mathlib's normalized inner product.

For equality on a finite group killed by $n$, one may use the finite abelian group decomposition $A\simeq\bigoplus_i\mathbb Z/d_i$. Each $d_i\mid n$. An image of the generator of $\mathbb Z/d_i$ is an arbitrary element of $(\mathbb Z/n)[d_i]$, precisely a multiple of $n/d_i$. There are $d_i$ choices, independently for all $i$. The empty product gives one for the trivial group. More generally the count by cyclic factors is $\prod_i\gcd(n,d_i)$. Equality under the torsion hypothesis is useful for reading the examples. The archive's perfect-pairing proof uses the upper bound valid for every finite $A$. [Lean, read] `PoincareDuality/Torsion.lean:14–39,90–100`, `TorsionDualFinite.lean:14–59,115–124` and pinned Mathlib, `Analysis/Fourier/FiniteAbelian/Orthogonality.lean:35–86`. $\square$

**Theorem (two finite adjoints, both onto).** For every $K,\Omega,U,n$ as above, $X$ and $Y$ are finite $n$-torsion groups, and $B(x,y)=t(\beta(x,y))$ induces isomorphisms
$$
L:X\longrightarrow Y^\vee_n,\quad x\longmapsto (y\mapsto B(x,y)),
\qquad
R:Y\longrightarrow X^\vee_n,\quad y\longmapsto (x\mapsto B(x,y)).
$$
Equivalently, each character on $Y$ is $B(x,-)$ for exactly one $x$, and each character on $X$ is $B(-,y)$ for exactly one $y$.

*Proof.* The cup and $t$ are additive in the indicated arguments. If $L(x)=0$, evaluation at every $y$ and injectivity of $t$ give $\beta(x,y)=0$ for every $y$. The left annihilator input gives $x=0$, and applying this to differences proves injectivity of $L$. If $R(y)=0$, evaluation at every $x$ gives the right annihilator premise by the same injectivity. It gives $y=0$, so $R$ too is injective. Since $Y$ is finite by Lemma 2, so is $Y^\vee_n$ by Lemma 3, and $L$ makes $X$ finite. The trivial coefficient group already makes $nX=0$.

Now both sides of the following chain are ordinary finite cardinalities:
$$
|X|\le |Y^\vee_n|\le |Y|\le |X^\vee_n|\le |X|.
$$
All four inequalities are equalities. The image of $L$ has $|X|=|Y^\vee_n|$ elements, so it is all of $Y^\vee_n$. The image of $R$ has $|Y|=|X^\vee_n|$ elements, so it is all of $X^\vee_n$. Thus there are two surjections, and the injections give their respective unique preimages. This is `IsPerfectPairing` in the archive. In lines 129–139, `t` is the invariant as an additive homomorphism and `β.flip` exchanges argument order while preserving the given scalar value. In lines 140–149, the first finiteness result is applied to $Y$, the injection gives finiteness of $X$, and the two character bounds give the reverse cardinal inequalities required by the two bijectivity calls. The proof works for $n=1$ with all groups trivial. It includes mixed characteristic with $v(n)>0$ and makes no assumption that $F$ contains a primitive $n$-th root. [Lean, read] `LocalTateDuality/EqZeroOfForallCupPairingZmodMulEqZeroLeft.lean:117–149` and `PoincareDuality/NsmulEqZeroOfNonemptyAddEquiv.lean:115–130,154–182,201–222`. $\square$

**Computing the matrix in the archive's normalization.** We use the positive Kummer cup comparison and the arithmetic Artin evaluation as named inputs. For $x$ a continuous $\mathbb Z/n$-valued character on $U$ and $a\in F^\times$ the comparison takes $x\cup\kappa_n(a)$ to the cyclic class $a\cup\delta(j_n\circ x)$ in the units module after scalar restriction to $G_F$. Its local invariant is $(j_n\circ x)(\operatorname{Art}_F(a))$, with $\operatorname{Art}$ sending a uniformizer to arithmetic Frobenius on unramified layers. The equality defining $t$ and injectivity of $j_n$ therefore give
$$
B(x,\kappa_n(a))=x(\operatorname{Art}_F(a)).
$$
On the right we evaluate in the finite abelian quotient through which $x$ factors. Each computation below takes $K=F$ and $U=G_K$, the top open subgroup, and all finite extensions are inside the same $\Omega$. [Lean] `LocalTateDuality/KummerCup.lean:80–101,193–252`, `LocalClassFormation/CupSymbol.lean:60–163,173–177`. [Milne, *Class Field Theory*, III §3, Proposition 3.6 and Lemma 3.7, pp. 109–110](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

**Example 1 (prime modulus, $F=\mathbb Q_3$, $n=2$).** Every principal unit is a square by Lemma 1 with $d=0$. The unit quotient is therefore $\mathbb F_3^\times/(\mathbb F_3^\times)^2$, generated by $-1$, and valuation gives the independent generator $3$. The classes $y_1=\kappa_2(3)$ and $y_2=\kappa_2(-1)$ generate $Y\simeq(\mathbb Z/2)^2$ by Kummer exactness.

Let $x_1$ be the character of $F(\sqrt{-1})/F$ with value $1$ on the nonidentity element. The polynomial $T^2+1$ has no root in $\mathbb F_3$ and is separable there, so the extension is unramified quadratic. Arithmetic Frobenius is nontrivial and units have zero image there. For $x_2$ use the character of $F(\sqrt{-3})/F$ with value $1$ on the sign change. The polynomial $T^2+3$ is Eisenstein, so the quadratic extension is totally ramified. The norm of $\sqrt{-3}$ is $3$. To rule out $-1$ as a norm, write $a+b\sqrt{-3}$ with $a,b\in F$. Its norm is $a^2+3b^2$. The two terms have valuations of opposite parity whenever both are nonzero, so the valuation of the sum is the smaller one. If the norm has valuation zero, then $a$ is a unit and $b$ is integral. Its residue is $1$, excluding $-1$. The norm criterion, $t$ injective, and the two-element target give $B(x_2,y_1)=0$ and $B(x_2,y_2)=1$. Thus the matrix in the ordered lists $(x_1,x_2)$ and $(y_1,y_2)$ is
$$
M_2=\begin{pmatrix}1&0\\0&1\end{pmatrix}\pmod 2 .
$$
The two characters have order two and the matrix proves their independence. Since $|X|\le |Y^\vee_2|=4$, they give all of $X$. A functional on $Y$ with values $(a,b)$ on the generators is represented by $ax_1+bx_2$, and a functional on $X$ with those values is represented by $ay_1+by_2$. [Paper] [Serre, *Local Fields*, I §6, Proposition 17 and III §5, Theorems 2–3](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Serre-Local.pdf)

**Example 2 (composite modulus with wild ramification, $F=\mathbb Q_5$, $n=10$).** The valuation coordinate is $\mathbb Z/10$. For the units, let $i\in\mathbb Z_5$ be the root of $i^2=-1$ with $i\equiv2\bmod5$, given by the simple residue lift. Its powers map bijectively to $\mathbb F_5^\times$. Every unit factors uniquely as $i^e u$ with $e\bmod4$ and $u\in V_1$. The power $10$ on the order-four factor has the same image as the square, so $[i]$ has order $2$. On $V_1$ the square map is onto $V_1$ by the simple root lift at $1\bmod5$. For $a\in\mathbb Z_5$,
$$
(1+5a)^5=1+25a+125h(a),\qquad h(a)\in\mathbb Z_5.
$$
The fifth powers lie in $V_2$ and their images fill $V_2/V_3$ by the displayed congruence. Moreover, the rescaled root argument of Lemma 1 applied with exponent $5$ and $d=1$ gives fifth roots of $V_3$ in $1+25\mathbb Z_5\subset V_1$. Given $w\in V_2$, choose $a$ to match its coefficient modulo $V_3$ and correct the remaining factor by such a fifth root. Hence $V_1^5=V_2$ and also $V_1^{10}=V_2$. Since $6=1+5$ maps to $1$ under the coefficient map $V_1/V_2\to(\mathbb F_5,+)$, the ordered Kummer generators
$$
(y_\pi,y_t,y_w)=\bigl(\kappa_{10}(5),\kappa_{10}(i),\kappa_{10}(6)\bigr)
$$
have orders $10,2,5$ and generate the direct product of those cyclic groups. In particular $|Y|=100$. The field $F$ itself has no primitive fifth root, as $\Phi_5(1+T)$ is Eisenstein at $5$.

For the rows take the following continuous characters.

- $x_\pi$ factors through the unramified extension of degree $10$ and sends arithmetic Frobenius to $1\in\mathbb Z/10$. Its values on the Artin images of $5,i,6$ are $(1,0,0)$.
- $x_t$ factors through $F(\sqrt5)/F$ and assigns $5\in\mathbb Z/10$ to the sign change. The root has norm $-5$ and $-1=i^2$ is a norm (of the scalar $i$), so $5$ is a norm. For the norm $a^2-5b^2$ to have valuation zero, the same parity test as above forces $a$ to be a unit and $b$ integral. Its residue is a square, which excludes $i$ of residue $2$. The scalar simple residue lift gives a square root of $6$ in $F$, so $6$ is a norm. The row is $(0,5,0)$.
- Let $E=F(\zeta_{25})$. The polynomial $\Phi_{25}(1+T)$ is Eisenstein. Its reduction is $T^{20}$, by reducing $\sum_{j=0}^4(1+T)^{5j}$ modulo $5$, and its constant term is $5$. Thus $E/F$ is totally ramified of degree $20$. The automorphism $\zeta_{25}\mapsto\zeta_{25}^b$ identifies its Galois group with $(\mathbb Z/25)^\times$. This group is the direct product of the order-four subgroup lifting $\mathbb F_5^\times$ and the order-five kernel of reduction. The latter is generated by $6\bmod25$, since $6^j\equiv1+5j\bmod25$. Use the character $x_w$ of this Galois group that assigns $2\in\mathbb Z/10$ to $6$ and kills the order-four subgroup. Its fixed kernel field is a totally ramified extension of degree $5$. This is an actual wild character because the residue characteristic is $5$. For arithmetic Artin the action of $5^a u$ on $\zeta_{25}$ has exponent $u^{-1}\bmod25$. The values on the three chosen classes are $(0,0,-2)=(0,0,8)$: $5$ acts trivially, $i\bmod25$ has order four, and $6$ acts by $6^{-1}$. [Paper] [Milne, *Class Field Theory*, I §3, Examples 3.8 and 3.13, pp. 40 and 44](https://www.jmilne.org/math/CourseNotes/CFT.pdf)

In the given row and column orders the pairing matrix is
$$
M_{10}=\begin{pmatrix}1&0&0\\0&5&0\\0&0&8\end{pmatrix}\pmod{10}.
$$
Here the diagonal entries generate the allowed image subgroups of orders $10,2,5$ in $\mathbb Z/10$. If a linear combination of the three characters is zero, evaluating on the three columns forces its coefficients to vanish modulo $10,2,5$ respectively. They generate a subgroup of order $100$, and $|X|\le |Y^\vee_{10}|=100$ gives all of $X$. To exhibit both actual surjections in these coordinates, the possible characters on either group have generator values $(a,5b,2c)$ with $a\bmod10$, $b\bmod2$ and $c\bmod5$. On $Y$ these values are represented by $a x_\pi+b x_t+(4c)x_w$, since $8\cdot4c=2c\bmod10$. On $X$ they are represented by $a y_\pi+b y_t+(4c)y_w$. Both formulas give unique representatives in the listed cyclic coordinates.

**What the hypotheses control.** Fix $n\ge2$. Remove finiteness and let $X=Y=\bigoplus_{j\ge1}\mathbb Z/n$ with the pairing $B(x,y)=\sum_j x_jy_j\bmod n$. The sum is finite and testing against the vector supported at coordinate $j$ with value $1$ detects $x_j$ or $y_j$. Thus both annihilators vanish, and both sides are still killed by $n$. Every functional is specified by its values on those single-coordinate vectors, so the dual is $\prod_{j\ge1}\mathbb Z/n$. Each adjoint has image exactly the finite-support sequences. The functional sending every vector of the indicated basis to $1$ is missed on both sides. This uses ordinary additive duals of discrete groups, exactly as in the finite pairing. In the finite argument one finite side suffices, since an injection into its finite dual already supplies finiteness of the other side.

For the same target $\mathbb Z/n$, deleting an explicit $n$-torsion hypothesis while retaining bilinearity and the two zero annihilators cannot produce a counterexample among finite abelian groups. For any $x,y$ one has $B(nx,y)=n B(x,y)=0=B(x,ny)$. Hence the zero annihilators imply $nx=0$ and $ny=0$ for every $x,y$. Indeed, the counting proof applies to arbitrary finite abelian groups even before this consequence is observed. This closes the proposed deletion route with that target. The role of $n$-torsion before currying is different: the formula $(j,\zeta)\mapsto\zeta^j$ on a coefficient group requires $n$ to kill that group for independence of the integer representative of $j$. For example the representatives $0$ and $2$ of $0\bmod2$ act differently on a generator of $\mathbb Z/4$.

The field-cast hypothesis has its own obstruction. If $F=\mathbb F_p((T))$ and $n=p$, taking $p$-th powers yields exactly $\mathbb F_p((T^p))^\times$. For distinct positive integers $a<b$ prime to $p$, the quotient $(1+T^a)/(1+T^b)$ has first nonconstant term $T^a$, so the classes $[1+T^a]$ give infinitely many distinct cosets. Also $T^{1/p}$ is purely inseparable of degree $p$, so the $p$-power map on $F^{\mathrm{sep},\times}$ fails surjectivity. The Galois root group is trivial in this case. This pinpoints the failed power and Kummer steps of the stated theorem.

**Remark on precedence and use.** The finiteness and cup-duality conclusion is the classical specialization of Tate's local theorem at the trivial finite module $\mathbb Z/n$ in complementary degrees $(1,1)$. Its Cartier dual is $\mu_n(\Omega)$ by evaluation at $1$. The conclusion over $G_F$ transports to $U$. A rational-valued character on a group killed by $n$ has values in $(\mathbb Q/\mathbb Z)[n]$, which is identified with $\mathbb Z/n$ by $j_n$. Tate's formulation and Milne's proof specify invertibility in the field, so the wild mixed-characteristic example belongs to the specialization. [Paper] [Tate, *Duality theorems in Galois cohomology over number fields*, §1 and Theorem 2.1, pp. 288–289](https://math.stanford.edu/~conrad/BSDseminar/refs/TateICM.pdf) · [Milne, *Arithmetic Duality Theorems*, 2nd ed., I §2, Theorem 2.1, Corollary 2.3 and Remark 2.5(b), pp. 26–29](https://www.jmilne.org/math/Books/ADTnot.pdf)

**Actual consumer.** `LocalTateDuality/MainDefs.lean:88–95` installs the theorem at the field `isPerfectPairing` of `localDualityHypotheses`, for every open subgroup and this same invariant. `PoincareDuality/Devissage.lean:99–112` uses the corresponding hypothesis at the chosen open subgroup $W$ when checking degree-one duality for coinduced trivial cyclic coefficients. The broader bundle uses its own cohomological finiteness, degree-three vanishing and invariant corestriction inputs. The readings here are author-level local R3 for the named production bodies and immediate field assignment. [Lean] retains the named class-formation, general coefficient local duality and global Poitou–Tate suppliers. [Open] marks the proof-reading boundary at their deeper bodies. New Lean kernel replay, exported Main proof-term reachability and independent review remain pending for this section. [Source ledger](../sources/SOURCES.md#chapter-11-finite-perfect-local-cup-pairing)


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
