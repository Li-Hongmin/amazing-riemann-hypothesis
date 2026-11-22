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
by splitting the left-hand side (`vvle_of_parts`, `LengthEqAddEigen.lean:127`) [Lean, read] into
**three pieces**, each controlled by a distinct pillar of modern algebraic number theory:

1. **The $\ell = 2$ tower and finitely many bad odd primes (`ThmBab`, `PrimeSetBoundDataOfPrimitiveChar.lean:49`):**
   Bounded by $\exp(x^{4\varepsilon / 5})$ on a pigeonholed window $[Y, Y^2]$ using **Iwasawa theory**
   in the cyclotomic $\mathbb Z_\ell$-tower `[Iwasawa1959]`, `[Iwasawa1973]`, an in-archive proof of
   the **Ferrero–Washington theorem ($\mu = 0$)** `[FerreroWashington1979]` via Sinnott's rational-function
   method `[Sinnott1984]` (`FW.ferreroWashington`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:104`), and a Soulé-type
   $K$-theoretic torsion bound `[Soule1979]` (`LemmaK`, `LemmaK.lean:13`) on the few exceptional twists
   near Iwasawa roots.
2. **The odd-$\ell$ minus eigenspace of complex conjugation (`ShaMinus`, `ThmBcFree`, `PrimeSetBoundDataOfPrimitiveChar.lean:64`):**
   Bounded polynomially in $([E : \mathbb Q], \operatorname{cond}(E), t)$ — hence by
   $K \exp(8 x^{\varepsilon/4})$ — via the **cyclotomic Euler system** of Gauss/Jacobi sums and
   Stickelberger elements, mirroring the upper-bound half of the **Mazur–Wiles / Kolyvagin–Rubin**
   theory `[MazurWiles1984]`, `[Rubin2000]`.
3. **The odd-$\ell$ plus ("Vandiver") eigenspace of complex conjugation (`ShaPlus`, `ThmHV`, `PrimeSetBoundDataOfPrimitiveChar.lean:79`):**
   Bounded by $(\operatorname{cond}(E)\cdot t)^C + C \exp(x^{4\varepsilon/5})$ by constructing a
   **nonzero rational integer annihilator `NN`** (`PropGK`, `KatoUse.lean:36`) out of Frobenius trace
   differences on $U(3)$ and $\mathrm{GSp}_4$ Galois representations, combining **Kato's $\mathrm{GL}_2$
   Euler system** `[Kato2004]` (`KatoUse`, `:13`) with a **residually reducible ordinary modularity-lifting
   machine** built on **Taylor–Wiles patching** `[TaylorWiles1995]`, `[ClozelHarrisTaylor2008]`,
   `[Thorne2015]` (`PfromAut`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/TaylorWilesObstructionBound.lean:150`).

Once those three bounds are assembled, an elementary exponent comparison (`error_terms_le_sqrt_exp_rpow`,
`ErrorTermsLeSqrtExpRpow.lean:6`, read in full) squeezes their sum below $\exp(x^\varepsilon / 2)$
because $\frac{\varepsilon}{4} < \frac{4\varepsilon}{5} < \varepsilon$ — closing Part II!

---

## 11.1 Motivation

### 11.1.1 Why a subexponential bound $\exp(x^\varepsilon / 2)$ suffices to beat prime-window growth

At first glance, a number theorist opening `ExistsPageN.lean:41–49` might be startled by the target
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
   - In Chapter 6 (`phi_bound`, `WeightedMeanData.lean:81`) and Chapter 9 (`SlopeIneq`), the concave
     logarithmic penalty $u_F \log(1 + \mathrm{HH}/u_F)$ from Bost's near-orthogonal frame inequality
     was linearized via $u \log(1 + H/u) \le \log(1 + X)(U + b)$ at $\mathrm{HH} \le x^{c_{\mathrm{HH}}} b$
     with $X = x^{c_{\mathrm{HH}}}$, costing only $O(\varepsilon (\log x)\,b) \ll b\,x^\varepsilon$
     because $\log(1 + x^{c_{\mathrm{HH}}})$ grows logarithmically!
   - In Chapter 10 (`vvRecord` and `divinN_of_hypV`, `DivinNOfHypV.lean:17,117`) [Lean, read], the
     total congruence denominator loss across the $m$ lifts had the shape $O\bigl(f m b (\log x)^2 + m B\bigr)$,
     where $B$ bounds $\sum_\ell \log \ell \sum_{1 \le e < R.t} \mathrm{shaLen}(E, \ell, e)$. Setting
     $B = \sqrt{b} = \exp(x^\varepsilon / 2) \le b = \exp(x^\varepsilon)$ absorbs $m\sqrt{b}$ cleanly
     into the per-step budget $B_0 = f m b x^\varepsilon$, which in Chapter 5's `SZ.T3`
     (`LipschitzWeightAndMinimum.lean:53`) is divided by the archimedean weight $a \asymp x^{1 + O(\varepsilon)} b$ —
     **cancelling the factor $b = \exp(x^\varepsilon)$ completely** and leaving $m \cdot x^{-1 + O(\varepsilon)} \ll x^{1/2 + O(\varepsilon)}$!
2. **Why $\exp(x^\varepsilon / 2)$ is large enough to swallow both polynomial conductor bounds and $4\varepsilon/5$ Iwasawa bounds:**
   Look at the conductor $\operatorname{cond}(E)$ of our CM host field $E \subset \mathbb Q(\zeta_N)$
   (`conductor_bounds_of_isChiField`, `ConductorBoundsOfIsChiField.lean:77`) [Lean, read]:
   $$\operatorname{cond}(E) \le 2^{e(x) + 2} \cdot \psi.N \cdot q \cdot d.$$
   Remember from Chapter 4 (`WinPair`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:27–37`) that $2^{e(x)} \asymp x^{2 + 8\varepsilon}$,
   while the auxiliary primes $(q, d)$ were chosen at the subexponential scale $\log q \le Y^{\varepsilon/5}$
   and $\log d \le Y^{\varepsilon/5}(\log Y)^2$! Consequently, for $x \ge Y$,
   $$\log\bigl(\operatorname{cond}(E) \cdot \lfloor x^{401} \rfloor\bigr)
   \le (403 + 8\varepsilon)\log x + \log(8\,\psi.N) + x^{\varepsilon/4}
   \le 2\,x^{\varepsilon/4}$$
   for all large $x$ (`log_conductor_mul_height_le_of_pageN`,
   `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/LogConductorMulHeightLeOfPageN.lean:6`,
   invoked at `…/CMFieldExponentialBounds/AdmissibleOfPageN.lean:49` and proved line by line in **Chapter 17**, Theorem 17.4(3)) [Lean, read]!
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
(`ShaPlus` with eigenvalue $(-1)^e$ and `ShaMinus` with eigenvalue $(-1)^{e+1}$, `LengthEqAddEigen.lean:68–72`):

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
     (`length_eq_add_eigen` and `shaLen_eq_add`, `LengthEqAddEigen.lean:10,88` [Lean, read])!
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
     minus bound `minusBound` (`StmtFields.lean:69`) and the $U(3)$ trace-difference integer `NN` in
     `PropGK` (`KatoUse.lean:36`)!

### 11.2.2 Toy Iwasawa root-avoidance pigeonhole on $[Y, Y^2]$ and the $\frac{\varepsilon}{4} < \frac{4\varepsilon}{5} < \varepsilon$ squeeze

Why does `VWinAt` (`ExistsPageN.lean:44–47`) assert that **inside every super-window $[X^{1/J}, X]$ there
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
   - Now apply `LemmaK` (`LemmaK.lean:13`) at that single resonant integer $e_{\mathrm{bad}}$! If
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
     (`BConst.J`, `PrimeSetBoundDataOfPrimitiveChar.lean:20–21` [Lean, read]) guarantees by the
     **pigeonhole principle** at least one clean window $[Y, Y^2] \subset [X^{1/J}, X]$ on which both
     `BaAt` ($\ell = 2$) and `BbAt` ($l \in B_\chi(\psi)$) stay below $\exp(x^{4\varepsilon/5})$!

3. **Numerical check of the final subexponential squeeze (`error_terms_le_sqrt_exp_rpow`):**
   Take $\varepsilon = 1/60 < 1/52$ and compare the three exponents in
   `ErrorTermsLeSqrtExpRpow.lean:6–9` [Lean, read]:
   - Minus-part / conductor exponent: $\frac{\varepsilon}{4} = \frac{1}{240} \approx 0.00417$;
   - $\ell = 2$ and bad-prime window exponent: $\frac{4\varepsilon}{5} = \frac{1}{75} \approx 0.01333$;
   - Target `HypV` exponent: $\varepsilon = \frac{1}{60} \approx 0.01667$, where $\sqrt{\exp(x^\varepsilon)} = \exp\bigl(\frac{1}{2} x^{1/60}\bigr)$.
   Because $x^{1/60} = x^{1/75} \cdot x^{1/300}$ (`hc : x ^ eps = b * s` at
   `ErrorTermsLeSqrtExpRpow.lean:33`, where $b = x^{4\varepsilon/5}$ and $s = x^{\varepsilon/5}$!), as
   soon as $s = x^{\varepsilon/5} \ge 2(D + \log N + 1)$, multiplying $b$ by $s/2$ dominates $D b + \log N$:
   $$N\,\exp\bigl(D\,x^{4\varepsilon/5}\bigr) \le \exp\Bigl(\frac{1}{2}\,x^\varepsilon\Bigr) = \sqrt{\exp(x^\varepsilon)}!$$

---

## 11.3 Definitions

We now record the exact Lean declarations of node **P12**, separating the small-cone `R3`-verified
statement and assembly files from the deep modularity/Kato/K-theory interface definitions.

### 11.3.1 Host fields, conductor, and the master target `VWin` (`ExistsPageN.lean`, `StmtFields.lean`)

**Definition 11.1 (`VVle`, `IsChiField`, `PageN`, `VAt`, `VWinAt`, `VWin`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean:12,19,39,41,44,49`, and `condF`, `Bchi`, `minusBound`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean:44,66,69`).** [Lean, read]

1. **Bounded $\log \ell$-weighted $Ш^1$ sum (`VVle`, `ExistsPageN.lean:12–17`):** For a number field $E$,
   a twist cutoff $t \in \mathbb N$, and a real bound $B \in \mathbb R$, `VVle E t B : Prop` asserts that
   for every algebraic closure $\Omega / E$ and every family of prime-level cohomological packages
   `ld : ∀ p [Fact p.Prime], LData E Ω p`,
   - *(finiteness)* for every prime $p$ and every $0 < e < t$, $\mathrm{shaLen}(\mathrm{ld}\,p, e) \neq \top$; and
   - *(uniform partial-sum bound)* for every finite set $S$ of primes,
     $$\sum_{\ell \in S} \log \ell \sum_{1 \le e < t} \bigl(\mathrm{shaLen}(\mathrm{ld}\,\ell, e).\mathrm{toNat} : \mathbb R\bigr) \le B.$$
2. **Cyclotomic CM host characterization (`IsChiField`, `ExistsPageN.lean:19–25`; generalized to subgroup data `AbF` as `IsCompField`, `StmtFields.lean:36–42`):**
   Given a primitive Dirichlet character $\psi : \mathrm{PChar}$ of conductor $\psi.N$, a $2$-adic exponent
   $e \in \mathbb N$, and auxiliary primes $q, d \in \mathbb N$, `IsChiField ψ e q d E` asserts that $E$
   embeds via $j : E \hookrightarrow \mathbb Q(\zeta_N)$ ($2^{e+2} \mid N$, $\psi.N \mid N$, $q \mid N$, $d \mid N$)
   as the exact fixed field of all $\tau_a : \zeta_N \mapsto \zeta_N^a$ satisfying
   $$\bigl(a \equiv \pm 1 \pmod{2^{e+2}}\bigr) \ \wedge\ \psi(a) = 1 \ \wedge\ \Bigl(\frac{a}{q}\Bigr) = 1 \ \wedge\ \Bigl(\frac{a}{d}\Bigr) = 1.$$
   Its minimal cyclotomic conductor is `condF E := sInf {N | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)}` (`StmtFields.lean:44`).
3. **Scale page, pointwise bound, window bound, and `VWin` (`PageN`, `VAt`, `VWinAt`, `VWin`, `ExistsPageN.lean:39–49`):**
   - `PageN eps x e` (`:39`): $x^{2 + 8\varepsilon} \le 2^e \le 2\,x^{2 + 8\varepsilon}$ (inhabited for all $\varepsilon > 0$ by `exists_pageN`, `:67`);
   - `VAt ψ eps Ct q d e x` (`:41`): for every number field $E$ satisfying `IsChiField ψ e q d E`,
     `VVle E ⌊x ^ Ct⌋₊ (Real.sqrt (Real.exp (x ^ eps)))`;
   - `VWinAt ψ Ct` (`:44`): for every $0 < \varepsilon < 1/52$ and every page function $e : \mathbb R \to \mathbb N$
     satisfying `∀ x ≥ 1, PageN eps x (e x)`, there exist $J \ge 1$ and $X_0$ such that for all $X \ge X_0$
     and all $(q, d)$ satisfying `WinPair eps (X ^ (1 / J)) q d`, there exists $Y$ with
     $X^{1/J} \le Y$ and $Y^2 \le X$ such that `VAt ψ eps Ct q d (e x) x` holds for **all $x \in [Y, Y^2]$**;
   - `VWin : Prop` (`:49`): `∀ ψ : PChar, VWinAt ψ 401`.
4. **Auxiliary bad-prime set and explicit minus-part bound (`Bchi`, `minusBound`, `StmtFields.lean:57–71`):**
   For $\psi : \mathrm{PChar}$ of multiplicative order $o = \mathrm{ordC}\,\psi$, let $p_K(\psi)$ be the
   least prime $p \equiv 3 \pmod 4$ with $p \ge 7$ and $\gcd(p, \psi.N) = 1$, let $h^{\ast}(\psi) = h(\mathbb Q(\sqrt{-p_K(\psi)}))$,
   and let $p_1(\psi)$ be the least prime $p \equiv 1 \pmod{o_{\mathrm{odd}}}$ coprime to $2\,\psi.N\,p_K(\psi)$. Then
   $$B_\chi(\psi) := \{3\} \cup \bigl\{\text{odd prime factors of } o \cdot \psi.N \cdot p_K(\psi) \cdot h^{\ast}(\psi) \cdot p_1(\psi)\bigr\},$$
   and for real constant $C$ and natural numbers $(o, n, N, t)$,
   $$\mathrm{minusBound}(C, o, n, N, t) := 3 n t^2 \log(t N) + C \sum_{\substack{\ell \mid o \\ \ell \text{ odd prime}}} \ell\,n^2 t^2 \bigl(\log(t \ell N)\bigr)^2.$$

### 11.3.2 Three-way parity decomposition and window propositions (`LengthEqAddEigen.lean`, `PrimeSetBoundDataOfPrimitiveChar.lean`)

**Definition 11.2 (`ShaPlus`, `ShaMinus`, `BoundedHeightTwoPlaceCondition`, `VVminusLe`, `VVplusLe`, `ThmBab`, `ThmBcFree`, `ThmHV`, `JointWin`, `src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean:68,71,107,111,113,120` and `…/PrimeSetBoundDataOfPrimitiveChar.lean:49,64,75,79,88`).** [Lean, read]

1. **Plus and minus submodules (`LengthEqAddEigen.lean:64–76`):** Over a CM field $E$ with complex
   conjugation `cE E : E ≃+* E` acting on $H^1(G_{E, S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e))$ via
   `cAct D e`, define
   $$\mathrm{ShaPlus}(D, e) := \mathrm{Sha}(D, e) \cap \ker\bigl(\mathrm{cAct}(D, e) - (-1)^e\bigr),
   \quad
   \mathrm{ShaMinus}(D, e) := \mathrm{Sha}(D, e) \cap \ker\bigl(\mathrm{cAct}(D, e) - (-1)^{e+1}\bigr),$$
   with $\mathbb Z_\ell$-lengths `plusLen D e` and `minusLen D e`.
2. **The three prime/parity predicates (`LengthEqAddEigen.lean:107–125`):**
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

1. *(`length_eq_add_eigen`, `LengthEqAddEigen.lean:10–55`)* *Let $R$ be a commutative ring in which
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
   $E$ is an abelian CM field (`isCMField_of_isChiField`, `IsCMFieldOfIsChiField.lean:7`) and its
   cyclotomic conductor satisfies*
   $$1 \le \operatorname{cond}(E) \le 2^{e + 2}\,\psi.N\,q\,d \qquad\text{and}\qquad [E : \mathbb Q] \le \operatorname{cond}(E)$$
   *(`conductor_bounds_of_isChiField`, `ConductorBoundsOfIsChiField.lean:77`).*
2. *(Assembling `VVplusLe` from bad-prime layers and generic counts: `thmHV_of_counts`, `JointWinOfCounts.lean:20`)*
   *Assume `PoitouTateDuality` (`[Lean]` / `[Open]`), `LocalFinitenessK`, `LocalTateDualityK`,
   `LemmaK CK`, and the five character-level plus-part count packages `CountI`, `CountII`, `CountIII`,
   `CountV`, and `CountZ`. Then `ThmHV K Ct` holds for every $C_t > 0$.*
3. *(Subexponential squeeze to `VWin`: `vwin_of_joint` and `vwin_of_counts`, `AdmissibleOfPageN.lean:131`, `JointWinOfCounts.lean:30`)*
   *Combining `ThmBab K 401`, `ThmBcFree`, and `ThmHV K 401` proves `VWin`!*

*Proof.*
(1) Inside $\mathbb Q(\zeta_N)$ ($q \mid N$), the primitive $q$-th root $\zeta_q := \zeta_N^{N/q}$ builds
the quadratic Gauss sum $G$ with $G^2 = -q$ (`exists_gauss` for $q \equiv 3 \pmod 4$,
`IsCMFieldOfIsChiField.lean:19`) on which $\tau_a(\zeta_N) = \zeta_N^a$ acts by the Legendre/Jacobi
symbol $\bigl(\frac{a}{q}\bigr)$. Every $\tau_a$ fixing $j(E)$ satisfies $\bigl(\frac{a}{q}\bigr) = 1$
by `IsChiField` (`:26`), hence fixes $G$, so Galois theory places $G \in j(E)$, producing $x \in E$
with **$x^2 = -q < 0$** (`:42–46`)! No complex embedding $\sigma : E \hookrightarrow \mathbb C$ can be
real (if $\Im\sigma(x) = 0$, then $(\Re\sigma(x))^2 = -q < 0$, impossible!, `:47–59`), so $E$ is
totally complex and abelian over $\mathbb Q$, hence a CM field (`IsCMField.of_isAbelianGalois E`, `:60`).
Similarly (`ConductorBoundsOfIsChiField.lean:86–119`), setting $L := \operatorname{lcm}(2^{e+2}, \psi.N, q, d) \mid N$,
every $\tau_a$ with $a \equiv 1 \pmod L$ satisfies $a \equiv 1 \pmod{2^{e+2}}$, $\psi(a) = 1$,
$\bigl(\frac{a}{q}\bigr) = 1$, and $\bigl(\frac{a}{d}\bigr) = 1$, so $j(E) \subseteq \mathbb Q(\zeta_L)$
(`descend`, `:11–64`), giving $\operatorname{cond}(E) \le L \le 2^{e+2}\,\psi.N\,q\,d$ and
$[E : \mathbb Q] \le \varphi(\operatorname{cond}(E)) \le \operatorname{cond}(E)$ (`finrank_le`, `:66–75`).

(2) Look at how `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/JointWinOfCounts.lean:16–23` splits the odd primes $\ell \neq 2$ in `VVplusLe` into
two regimes (`PointArith.lean:36–92`):
- **Outside the fixed bad set ($\ell \notin B_\chi(\psi)$, `sumOut` in `SumOut.lean:50–231`):** At each
  twist $1 \le e < t$, filter $S$ by `CaseI l e` ($\ell \notin B_\chi$ and $(\ell - 1) \nmid 2e$, `:171`).
  On `CaseI`, `CountI` (derived from `PropGK`!) bounds the **entire sum over $\ell$ at once** by $M^{C_1}$
  where $M := h.N \cdot t$ (`:176`)! On $\neg\mathrm{CaseI}$, $(\ell - 1) \mid 2e$ forces
  $\ell \le 2e + 1 \le 2t$ (`card_small`, `:19, 192`: **at most $2t$ such primes exist!**), and
  `CountZ`, `CountII`, `CountIII` bound each character summand by $(\ell \cdot h.N \cdot e)^K \le M^{3K}$
  (`:73–118`). Summing over $1 \le e < t$ gives $\le t(M^{C_1} + 2 M^{3K+1}) \le M^{C_1 + 3K + 4}$
  (`final_le`, `:31–47, 231`)!
- **Inside the fixed finite bad set ($\ell \in B_\chi(\psi)$, `sumIn` in `FinalLe.lean:86–263`):**
  First, `countVs` (`CountVs.lean:86–171`) handles large-$R_1$ bad-prime twists at $e = 1$ by cutting out
  a cyclic extension $L / \mathbb Q$ of bounded degree $[L : \mathbb Q] \le n_0(\psi)$ (`vsField`, `:112`),
  using Poitou–Tate duality (`shaLeV`, `:123`) and `LemmaK` (`klen`, `:124`) to bound the length by
  $(\ell \cdot h.N)^{C_6}$. Then `sumIn` splits the characters $\psi' \in h.X(c, e)$ into at most $h.q = \psi.N$
  odd-order characters `Oset` (`hOcard`, `:175`, bounded across $1 \le e < t$ by $B + M^{C_4}$ via `CountIV`
  from the Iwasawa layer hypothesis `BbAt`!) and the remaining characters (bounded pointwise by
  $(M^2)^{C_m}$ via `CountII`, `CountV`, `CountVs`), combining them via `sum_split` (`:14–54`) and
  `final_le` (`:56–84`) into $\le M^C + C \cdot B$.
- Summing `sumOut` with the $\lvert B_\chi(\psi) \rvert$ bad primes of `sumIn` (`point_arith`,
  `PointArith.lean:5–34`) and substituting $B = \exp(x^{4\varepsilon/5})$ and $h.N = \operatorname{cond}(E)$
  (`hostCond`, `ThmHV.lean:39`) yields `HVAt`:
  $$\mathrm{VVplusLe}\Bigl(E,\ t(x),\ \bigl(\operatorname{cond}(E)\cdot t(x)\bigr)^C + C\,\exp\bigl(x^{4\varepsilon/5}\bigr)\Bigr)!$$

(3) Finally, follow `vwinAt_of_joint` (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean:41–129`):
- `jointWin_of` (`PrimeSetBoundDataOfPrimitiveChar.lean:145–156`) intersects the threshold of `ThmBab`
  and `ThmHV` to obtain a window $[Y, Y^2] \subset [X^{1/J}, X]$ on which both `BaAt`
  ($B_2 = \exp(x^{4\varepsilon/5})$) and `HVAt` ($B_p = u^C + C\exp(x^{4\varepsilon/5})$ with
  $u := \operatorname{cond}(E)\cdot t(x)$) hold for all $x \in [Y, Y^2]$;
- `ThmBcFree` (`thmBc_iff`, `:112`) supplies `VVminusLe E (t x) (minusBound Cb ...)`. Since
  $[E : \mathbb Q] \le \operatorname{cond}(E)$ and $\log u = \log(\operatorname{cond}(E)\cdot \lfloor x^{401} \rfloor) \le 2 x^{\varepsilon/4}$
  (`hxN`, `AdmissibleOfPageN.lean:120`), `minusBound_le_exp_of_log_le` (`minusle.lean:6–75`) bounds
  $u^4 \le \exp(8 x^{\varepsilon/4})$ and gives $B_m \le K \exp(8 x^{\varepsilon/4})$;
- Proposition 11.1(2) (`vvle_of_parts`, `AdmissibleOfPageN.lean:123`) combines $B_2, B_m, B_p$ into
  $$\mathrm{VVle}\Bigl(E,\ \lfloor x^{401} \rfloor,\ \exp\bigl(x^{4\varepsilon/5}\bigr)\log 2 + K\exp\bigl(8 x^{\varepsilon/4}\bigr) + \bigl(u^C + C\exp(x^{4\varepsilon/5})\bigr)\Bigr);$$
- and for $x \ge x_T$ (`error_terms_le_sqrt_exp_rpow`, `ErrorTermsLeSqrtExpRpow.lean:6–88`), writing
  $a = x^{\varepsilon/4} \le b = x^{4\varepsilon/5}$ and $x^\varepsilon = b \cdot x^{\varepsilon/5}$,
  every term is bounded by $N \exp(D b) \le \exp(x^\varepsilon / 2) = \sqrt{\exp(x^\varepsilon)}$,
  so `VVle.mono` (`ExistsPageN.lean:51`) concludes `VAt ψ eps 401 q d (e x) x`! $\square$

### 11.4.3 Sinnott's proof of Ferrero–Washington ($\mu = 0$) and Iwasawa $\ell$-rank bounds (`src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`)

Remarkably, `FerreroWashington` is **not** left in the unreviewed `GlobalTheory.Published` pool: we read
the entire 119-line file `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`
(import cone **809** modules) and the 104-line bridge `ExistsIwasawaRankBoundOfFerreroWashington.lean`
(cone **2,033**) line by line (`R3` / `[Lean, read]` for both files; `R2` `[Lean]` for their imported
Stickelberger/Sinnott sub-modules)!

**Proposition 11.3 (In-archive deduction of `FerreroWashington` and Iwasawa rank stabilization).**
*For every prime $\ell$ (including $\ell = 2$!) and every abelian number field $K / \mathbb Q$ containing
$\mu_4$ ($\ell = 2$) or $\mu_\ell$ ($\ell \neq 2$), the $\ell$-cotorsion rank of $\mathrm{Cl}(\mathcal O_{K_n})$
is uniformly bounded along the cyclotomic $\mathbb Z_\ell$-tower $K_n = K(\mu_{\ell^n})$:*
$$\exists r \in \mathbb N,\ \forall n \in \mathbb N,\quad \bigl\lvert \mathrm{Cl}(\mathcal O_{K_n}) / \mathrm{Cl}(\mathcal O_{K_n})^\ell \bigr\rvert \le \ell^r,$$
*and for odd $\ell$ this bounds the dual Iwasawa module rank `XRk l 1 (levU l U n) r` uniformly in $n$.*
*(Lean: `UpperTheory.V.FW.cyc` and `UpperTheory.V.FW.ferreroWashington`,
`…/FerreroWashingtonIndex/FerreroWashington.lean:18,104`;
`exists_iwasawaRank_bound_of_ferreroWashington`,
`…/RealPlaceConjugation/ExistsIwasawaRankBoundOfFerreroWashington.lean:23`.)* [Lean, read]

*Proof.* Look at the two-step proof in `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean`:

1. **Full cyclotomic towers $\mathbb Q(\zeta_{f \ell^n})$ (`FW.cyc`, `:18–103`):** Let $f > 1$ be
   coprime to $\ell$, and set $c := 2 f \ell + 1$ (odd, $> 1$, coprime to $f\ell$, `:25–28`).
   - *Minus part via Stickelberger + Sinnott (`[FerreroWashington1979]`, `[Sinnott1984]`):* The imported
     Sinnott independence lemma `memZ` (`:29` `[Lean]`) produces $N, n_0 \in \mathbb N$ and, for each
     $n \ge n_0$, a Galois element $\gamma \in (\mathbb Z / f \ell^n \mathbb Z)^\times$ whose Stickelberger
     projection is nontrivial mod $\ell$, while `stickH` (`:50, 86` `[Lean]`) shows that the smoothed
     Stickelberger element `thetaH (f * l^n) (2*f*l + 1)` annihilates the minus class group! Combined
     with the uniform genus/ambiguous-ideal bound `ambCyc` (`B`, `:30` `[Lean]`), `core` (`:47, 83` `[Lean]`)
     bounds the minus $\ell$-torsion subgroup by $\lvert \mathrm{difR}(-1) \cap \mathrm{Cl}(L)[\ell] \rvert \le B^N$ (`:52, 88`)!
   - *Plus part via Kummer/Leopoldt reflection (`:54–64` for $\ell = 2$; `:90–102` for $\ell \ge 3$):*
     Because $L = \mathbb Q(\zeta_{f \ell^n})$ ($n \ge n_0 \ge 2$) contains $\mu_\ell$ (and $\mu_4$ when
     $\ell = 2$), **Kummer / Leopoldt reflection** (`reflOdd` and `pOdd` at `:99–102` for odd $\ell$,
     `sgnCyc` and `pTwo` at `:56–64` for $\ell = 2$ `[Lean]`) bounds the total $\ell$-rank index
     `[Cl(L) : Cl(L)^l]` by $\ell \cdot (B^N)^2$ (for $\ell \ge 3$) or $\bigl(2^{\varphi(f \cdot 2^{\mathrm{ee}\,2}) N} B^N\bigr)^2$
     (for $\ell = 2$), **completely independent of $n \ge n_0$**!
2. **Descent from $\mathbb Q(\zeta_{f \ell^m})$ to general abelian $K_n / K$ (`FW.ferreroWashington`, `:104–119`):**
   By Kronecker–Weber (`embed l K`, `:107` `[Lean]`), $K$ embeds into $\mathbb Q(\zeta_{f \ell^{m_0}})$
   with $f > 1$ coprime to $\ell$ and bounded relative degree $D$, embedding each $K_n$ into
   $L = \mathbb Q(\zeta_{f \ell^m})$ ($m \ge n_0$) of relative degree $[L : K_n] \le D \ell^{n_0}$ (`:111`).
   Norm/transfer descent on class groups (`desc`, `:113` `[Lean]`) gives
   $$\bigl[\mathrm{Cl}(K_n) : \mathrm{Cl}(K_n)^\ell\bigr] \le [L : K_n] \cdot \bigl[\mathrm{Cl}(L) : \mathrm{Cl}(L)^\ell\bigr]
   \le D \ell^{n_0} B < \ell^{D \ell^{n_0} B}$$
   (using $k < \ell^k$ for $\ell \ge 2$, `Nat.lt_pow_self`, `:119`), proving `FerreroWashington` with
   $r := D \ell^{n_0} B$! In `ExistsIwasawaRankBoundOfFerreroWashington.lean:73–104`, Kummer duality
   between unramified $\mathbb Z/\ell\mathbb Z$-extensions and $\mathrm{Hom}(\mathrm{Cl}(K_n), \mathbb Z/\ell\mathbb Z)$
   (`cardClDual` and `pullOnto`, `:99–103` `[Lean]`) immediately transfers $\le \ell^r$ to the Iwasawa
   cotorsion module `XDual`! $\square$

### 11.4.4 Top-level modularity-to-`VWin` wiring (`vwin_of_row`) and honest map of the 157,603-module cone

Finally, we read the three top-level P12 assembly files `VwinOfRow.lean`, `TopMainZj.lean`, and
`WindowBoundOfLiteratureLevel.lean` in full (`R3` / `[Lean, read]` for these three files; `R2` / `R1`
for their deep sub-trees):

**Theorem 11.4 (From CM automorphic Galois representations `Row0b` to `VWin`: `vwin_of_row`).**
*Assume `h : UpperTheory.GalStar.Row0b (fun h rc => UpperTheory.Zero.LLC.IsRecT h rc)` (node `P14` + `P15`,
Chapter 12). Then `UpperTheory.Top.VWin` holds.*
*(Lean: `UpperTheory.One.vwin_of_row`,
`src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean:4`;
`automorphic_window_of_inputs`, `…/DenseThresholdCases/TopMainZj.lean:71`;
`v_window_of_literal_automorphy_n` and `vwin_of_hypotheses_H_E_alt`,
`…/DenseThresholdCases/WindowBoundOfLiteratureLevel.lean:25,33`.)* [Lean, read]

*Proof (top-level wiring in Lean, with reading-level boundaries marked explicitly).*

1. **Packaging `OpenImageCondition` and four literature bundles (`VwinOfRow.lean:4–5`, `TopMainZj.lean:18–74` `[Lean, read]`):**
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
2. **Discharging `LemmaK`, Kato's Euler system, and residually reducible modularity (`WindowBoundOfLiteratureLevel.lean:25–34` `[Lean, read]`):**
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
| `FerreroWashingtonIndex/FerreroWashington.lean` | **809** | `R3` (`[Lean, read]` top proof; `R2` `[Lean]` Sinnott sub-lemmas) | Proves `FW.ferreroWashington` via Sinnott's independence lemma, Stickelberger annihilation, and Kummer reflection. |
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
   in `KatoUse` (`KatoUse.lean:15–17`), twisting a weight-$(2e + 1)$ newform ($e \ge 1$) by $\chi_{\mathrm{cyc}}^{-e}$
   evaluates Kato's Euler system at $s = 2e + 1 - e = e + 1$ in classical normalization (analytic
   $s = 1$, strictly to the right of the critical center $s = 1/2$ and at the edge of Euler-product
   non-vanishing!), where $L$-values of $\mathrm{GL}_2$ cusp forms never vanish `[Kato2004]` [Community]
   (see **Chapter 18**, Lemma 18.2(1), for the line-by-line `R3` verification of `Published.Kato` and `2 * r ≠ k` `[Lean, read]`)!
3. **What happened to Behrend's set (`remark.pdf` p. 4, item 19 vs. `P12` and `HostOfField`):** In `remark.pdf`
   (p. 4, item 19 and fn. 7), Alpöge listed an October step tuning the choice of the Iwasawa tower via
   Behrend sets while noting *"This is the sort of trick that intuitively to me is
   obviously going to be unnecessary"* [Paper; remark p. 4]. Indeed, on the **P12 `VWin`** branch (`LUMI doc 06`
   [Community]), the Iwasawa root-avoidance window uses the elementary pigeonhole count `BConst.J`
   (`PrimeSetBoundDataOfPrimitiveChar.lean:20`), while the 14-file folder `src/Formalism/BehrendSets/`
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
| `isCMField_of_isChiField`; `conductor_bounds_of_isChiField`; `minusBound_le_exp_of_log_le`; `error_terms_le_sqrt_exp_rpow`; `admissible_of_pageN`, `vwinAt_of_joint`, `vwin_of_joint` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/IsCMFieldOfIsChiField.lean:7`; `…/ConductorBoundsOfIsChiField.lean:77`; `…/minusle.lean:6`; `…/ErrorTermsLeSqrtExpRpow.lean:6`; `…/AdmissibleOfPageN.lean:24,41,131` | Proposition 11.2(1,3): proves $\sqrt{-q} \in E \implies \mathrm{IsCMField}\,E$, $\operatorname{cond}(E) \le 2^{e+2}\psi.N q d$, and squeezes $B_2\log 2 + B_m + B_p \le \sqrt{\exp(x^\varepsilon)}$ (cones 21–38). | [Lean, read] |
| `countVs`; `sumIn`; `sumOut`; `point`; `thmHV`; `pointHV_of_counts`, `thmHV_of_counts`, `jointWin_of_counts`, `vwin_of_counts` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/CountVs.lean:86`; `…/FinalLe.lean:86`; `…/SumOut.lean:50`; `…/PointArith.lean:36`; `…/ThmHV.lean:6`; `…/JointWinOfCounts.lean:16,20,25,30` | Proposition 11.2(2–3): combines `LemmaK`, `CountI`–`CountV`, `CountZ`, `ThmBab`, and `ThmBcFree` into `VWin` (cone 1,144). | [Lean, read] |
| `UpperTheory.V.Published.FerreroWashington`; `UpperTheory.V.FW.cyc`, `ferreroWashington`; `exists_iwasawaRank_bound_of_ferreroWashington` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PublishedTheorems/FerreroWashington.lean:7`; `…/GaloisLibrary/FerreroWashingtonIndex/FerreroWashington.lean:18,104`; `…/WeakShimuraTheory/RealPlaceConjugation/ExistsIwasawaRankBoundOfFerreroWashington.lean:23` | Definition 11.3(1) & Proposition 11.3: Sinnott-route proof of $\mu = 0$ bounded $\ell$-rank for all primes $\ell$ (including $\ell = 2$) and Iwasawa cotorsion rank stabilization (cones 0, 809, 2,033). | [Lean, read] |
| `HasMuQ`, `kBound`, `UpperTheory.V.LemmaK` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/GeneratorCountTuples/LemmaK.lean:9,11,13` | Definition 11.3(2): Soulé-type bound $\log\lvert H^2(\mathbb Z_\ell(e+1)) \rvert \le \exp((2e[L:\mathbb Q])^{C_K}\log(2\lvert d_L \rvert))$ (statement `R3`, cone 9; proof in `KTheoryStability/` `[Open]`). | [Lean, read] |
| `KatoUse`, `CohInp`, `Inp`, `PropGK`, `CorGK`, `OneChar` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/KatoUse.lean:13,19,26,36,44,54` | Definition 11.3(3): Kato $\mathrm{GL}_2$ Selmer vanishing and the $U(3)$ Frobenius-trace integer annihilator `NN` bounding generic `ShaPlus` across all $\ell \neq p$ (statement `R3`, cone 1,713; proof cone `[Open]`). | [Lean, read] |
| `TWPl`, `LocCFT`, `ArPl`, `FirstOrderDualArithmeticBound`, `TaylorWilesObstructionBound`, `HasAut`, `PfromAut` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/PatchingModules/TaylorWilesObstructionBound.lean:88,115,119,126,136,147,150` | Definition 11.3(4): Taylor–Wiles prime systems and patching theorem `PfromAut` on universal ordinary determinant rings (statement `R3`, cone 1,711; 50k-line `PatchingModules/` proof cone `[Open]`). | [Lean, read] |
| `vwin_of_hypotheses_H_E_alt`, `v_window_of_literal_automorphy_n`; `local_inputs_from_literature`, `automorphic_inputs_from_literature`, `cm_abelian_inputs_from_literature`, `automorphic_window_of_inputs`; `UpperTheory.One.vwin_of_row` | `src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/WindowBoundOfLiteratureLevel.lean:25,33`; `…/TopMainZj.lean:18,38,59,71`; `…/VwinOfRow.lean:4` | Theorem 11.4: top-level deduction of `VWin` from `Row0b` and `OpenImageCondition` (top files `R3`; 157,603-module internal proof cone `[Lean]` / `[Open]`). | [Lean, read] |

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
