# Chapter 5. The square-root barrier as bookkeeping: `core_gm`

With Chapters 2, 3, and 4 in hand, only one link of **Part I: The analytic endgame** remains open.
In Chapter 3 (`zeroFreeAll_of_topG`, Theorem 3.7) we saw that `ZeroFreeAll` follows from three
inputs for each primitive character $\psi$ [Lean, read]:

1. the Landau-window criterion `formB` (proved in full in Chapter 3, Theorem 3.6);
2. the window host supply `supplyChi` on $[Z, Z^{3/2}]$, delivering at each window point $x$ a CM
   host field `H : HostAx φ` and coset sample `TT` satisfying `EAtH (Level.cyc ψ) H.toHostRaw TT x eps 4`
   together with the Tate–Shafarevich bound `VVle H.E R.t (sqrt s.b)` (proved in Chapter 4, Theorem 4.9,
   assuming `VWin`); and
3. the **window Chebyshev upper bound** `level_gm_le_on_family_scales` (`LevelGmLeOnFamilyScales.lean:28`),
   which turns host data `EAtH` and chain data `CoreAtH` at scale $x$ into the one-sided inequality
   $$\Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}.$$

That inequality is proved by `UpperTheory.Comparison₂.core_gm`
(`src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12`, node `P6` of
`notes/proof-map.md`). Every Lean file in the proof of `core_gm` — `CoreGm.lean`, `CoreAtH.lean`,
`charsA.lean`, `GmAEq.lean`, `SigALe.lean`, `hostFactsS.lean`, `TopsSum.lean`, `PrimRead.lean`,
`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean`, `ChTop.lean`, `ChBalance.lean`, `SplitInertia.lean`,
`LipschitzWeightAndMinimum.lean`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean`, `WindowInequalityOfArtinInputs.lean`,
and `LevelGmLeOnFamilyScales.lean` — has been read line by line by us (`R3` / `[Lean, read]`).

The title of this chapter is deliberate. The theorem `core_gm` sits in a tiny import cone of just
**114 archive modules** (`notes/proof-map.md`), containing zero automorphic forms, zero Shimura
varieties, and zero Galois cohomology! Why? Because `core_gm` is pure **finite harmonic analysis on
the host's character group plus elementary exponent bookkeeping**: it takes the arithmetic output
of Part II packaged inside the proposition `CoreAtH`, projects from prime divisibility at inert
primes to characters via finite Fourier orthogonality, balances $x/m + m$ at chain length
$m \approx x^{1/2}$, and hands the resulting exponent $1/2 + (e_D + e_L + 7)\varepsilon$ back to
Chapter 3. Reading `core_gm` in full shows both *exactly where the exponent $1/2$ enters* and
*exactly what Part II (Chapters 6–11) has to prove to inhabit its hypotheses*.

---

## 5.1 Motivation

### 5.1.1 From prime divisibility of a chain to Dirichlet $L$-functions

Suppose Part II hands us, at a large scale $x$, a CM host field $E = F(\sqrt{-d})$ of degree
$4n$ ($n = \lvert \varphi.A \rvert = \varphi.\mathrm{ord} \asymp x^{2 + 8\varepsilon}$, with
$[F : \mathbb Q] = 2n$) and a chain of $m$ theta lifts whose Arakelov/Hermitian slope inequality
produces an upper bound on a weighted sum over **primes $p$ that are inert in $K = \mathbb Q(\sqrt{-d})$**:
$$\mathrm{ASK} - \Re\,\mathrm{MAIN} \le \mathcal E_{\mathrm{chain}}.$$
Here $\mathrm{ASK}$ counts prime powers $p^r$ ($p$ inert in $K$, weighted by Riesz ramps
$(a_t / (w(\rho) p^r) - 1)_+$ in prescribed Frobenius classes of $\operatorname{Gal}(E/\mathbb Q)$),
$\mathrm{MAIN}$ records the expected main term from $\zeta(s)$ and $L'(1, \chi_{-d})/L(1, \chi_{-d})$,
and $\mathcal E_{\mathrm{chain}}$ is the total error accumulated across all $m$ steps of the chain
(archimedean norms, word-count losses, Selmer/Tate–Shafarevich congruence losses, and $2$-adic level
losses).

Three questions immediately confront an analytic number theorist looking at $\mathrm{ASK} - \Re\,\mathrm{MAIN} \le \mathcal E_{\mathrm{chain}}$:

1. **How does a sum restricted to *inert* primes recover the full Riesz prime sum $G_\chi(x)$ of a
   target character $\chi \in \Lambda.\mathrm{KEPT}$, which sums over *all* primes?**
   Watch the mechanism of the colour subgroup $\Phi \subset E_0 \times H$ (`ChBalance.lean:200`)!
   Model $\operatorname{Gal}(E/\mathbb Q)$ additively as $E_0 \times H$, where
   $E_0 = \mathbb Z/2\mathbb Z \times \mathbb Z/2\mathbb Z$ tracks the two quadratic signs and
   $\Phi = \{g \in E_0 \times H : g_{1,1} = 0\}$ (`InPhi g ↔ g.1.1 = 0`) tracks splitting in
   $K = \mathbb Q(\sqrt{-d})$. Every prime $p$ that **splits** in $K$ (including $2$, $q$, and
   every prime dividing $\psi.N$, by Lemma 4.1(2)!) has Frobenius in $\Phi$, whereas every prime
   **inert** in $K$ has Frobenius **outside $\Phi$**! When we expand $\mathbf{1}_{g = r\,\mathrm{frob}(p)}$
   by characters $\psi \in \widehat{E_0 \times H}$ and sum over $g \notin \Phi$:
   - for **split** primes, $g - r\,\mathrm{frob}(p)$ never hits the inertia subgroup inside $\Phi$,
     so their character sum over $g \notin \Phi$ vanishes identically (`lsplit`, `ChBalance.lean:77`)!
   - for **each kept character** $\chi \in \Lambda.\mathrm{KEPT}$, $\chi$ appears *twice* in
     $\widehat{E_0 \times H}$: once on the plus-side ($\psi$ trivial on the $K$-factor) and once
     twisted by $\chi_{-d}$ ($\psi + \mathrm{ch}_C$)! On $g \notin \Phi$, $\mathrm{ch}_C(g) = -1$,
     so summing over $g \notin \Phi$ pairs $\psi$ (which gets weight $+1$, supported on all primes!)
     with $\psi + \mathrm{ch}_C$ (which is a `Bounded` twist ramified at $d$, bounded by $x^{1/2+\varepsilon}$
     from Chapter 4!)! In short: **inert primes = $\frac{1}{2}(\text{all primes} - \chi_{-d}\text{-twisted primes})$**,
     and Chapter 4 already proved square-root cancellation for the $\chi_{-d}$-twisted primes!
2. **How do we eliminate the $4n - 4o \approx 4 x^{2+8\varepsilon}$ unwanted characters of $E$ that
   depend nontrivially on the $2$-power tower $A_0 \le H$?**
   By **averaging the chain inequality over translations $u_0 \in A_0$** (`sum_Th`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:56`)!
   Exact orthogonality of characters on the finite subgroup $\{0\} \times A_0$ annihilates every
   character $\psi \notin \Psi_A(A_0) := \{\psi : \psi\rvert_{\{0\}\times A_0} = 1\}$ with **zero
   analytic error** — leaving only the $4\,\Lambda.o$ characters trivial on $A_0$! Then summing
   over the Frobenius shift set $TT \subset H$, whose coset distribution across $H / A_0$ has weights
   $\frac{4}{3o + 1}$ on $A_0$ and $\frac{3}{3o + 1}$ on each non-identity coset (`Frame.lam`,
   `ExplicitFormulaErrorOfHostConditions.lean:135`), gives Fourier transform $+1$ on the trivial
   coset character ($\zeta$) and $+\frac{1}{3o + 1} > 0$ on **every** nontrivial character of $H/A_0$
   (`tops_sum`, `TopsSum.lean:75`) — matching $\Lambda.\mathrm{Gm}(x)$ term for term (`gmA_eq`,
   `GmAEq.lean:61`)!
3. **Where does the exponent $1/2$ come from?**
   After dividing the chain gap by the signal prefactor $\lvert TT \rvert \cdot m \cdot b$ (each of
   the $m$ lifts contributes one unit of Riesz prime-sum signal of scale $b$), the archimedean top
   weight $n_T a_E \asymp n_T x b$ divides down to $\frac{x}{m}$, while the per-lift Selmer/congruence
   charge $m \cdot B_0 \asymp m \cdot (n m b x^\varepsilon)$ divides down to $m\,x^{O(\varepsilon)}$.
   Balancing
   $$\frac{x}{m} + m\,x^{O(\varepsilon)} \quad\text{at}\quad x^{1/2 - \varepsilon} \le m \le x^{1/2 + \varepsilon/2}$$
   gives $x^{1/2 + O(\varepsilon)}$!

---

## 5.2 Small examples

We illustrate the two mechanisms of `core_gm` — finite Fourier isolation on $E_0 \times H$ and the
$x/m + m$ vs. $x/m + m^2$ chain balance — in miniature.

### 5.2.1 Toy finite Fourier projection on $E_0 \times H$

Take $o = \Lambda.o = 3$ (say $\psi$ is a cubic character of conductor $7$), and collapse $A_0 = \{0\}$
so $H = \mathbb Z/3\mathbb Z$ (`o = 3`). Then $E_0 \times H = (\mathbb Z/2\mathbb Z \times \mathbb Z/2\mathbb Z) \times \mathbb Z/3\mathbb Z$
has $12$ elements, and the split subset (`PhiSet`) is
$$\Phi = \bigl\{((0, e_2), h) : e_2 \in \mathbb Z/2\mathbb Z,\ h \in \mathbb Z/3\mathbb Z\bigr\}$$
of size $\lvert \Phi \rvert = 6$, with complement $\Phi^c = \{((1, e_2), h)\}$ also of size $6$ [Expository].

1. **Summing over $g \in \Phi^c$ (`colour_sum`).** Write any character of $E_0 \times H$ as
   $\psi_{\alpha, \beta, k}((e_1, e_2), h) = (-1)^{\alpha e_1 + \beta e_2} \omega^{kh}$
   ($\alpha, \beta \in \{0, 1\}$, $k \in \{0, 1, 2\}$, $\omega = e^{2\pi i/3}$). Notice that
   $\mathrm{ch}_C = \psi_{1, 0, 0}$ (`FirstPrimeNeSecondPrime.lean:21`) takes value $+1$ on $\Phi$
   ($e_1 = 0$) and $-1$ on $\Phi^c$ ($e_1 = 1$). Therefore, summing $\overline{\psi_{\alpha,\beta,k}(g)}$
   over $g \in \Phi^c$ ($e_1 = 1$, $e_2 \in \{0,1\}$, $h \in \{0,1,2\}$) gives
   $$\frac{1}{6}\sum_{g \in \Phi^c} \overline{\psi_{\alpha,\beta,k}(g)}
   = (-1)^\alpha \Bigl(\frac{1 + (-1)^\beta}{2}\Bigr)\Bigl(\frac{1 + \omega^{-k} + \omega^{-2k}}{3}\Bigr)
   = \begin{cases}
   +1 & \text{if }(\alpha, \beta, k) = (0, 0, 0)\ \ (\psi = 0),\\
   -1 & \text{if }(\alpha, \beta, k) = (1, 0, 0)\ \ (\psi = \mathrm{ch}_C),\\
   0 & \text{for all } 10 \text{ other characters!}
   \end{cases}$$
   That two-line calculation is why `MAIN` (`FirstPrimeNeSecondPrime.lean:89`) has **only** two
   terms: the $\zeta(s)$ main term from $\psi = 0$ (with $+1$) and the $-\frac{L'}{L}(1, \chi_{-d})$
   counterterm from $\psi = \mathrm{ch}_C$ (with $-1$), while all $10$ remaining characters have
   their $s = 1$ counterterms embedded straight into $G_\psi$ with zero leftover!
2. **Summing over $t \in TT$ with the $(4, 3)/(3o + 1)$ coset law (`tops_sum`).** Suppose $TT$ has
   $10N$ elements distributed across $H = \mathbb Z/3\mathbb Z$ with $4N$ elements in $0 \bmod 3$,
   $3N$ elements in $1 \bmod 3$, and $3N$ elements in $2 \bmod 3$ — the exact ratios
   $\mathrm{lam}(0) = \frac{4}{10}$ and $\mathrm{lam}(1) = \mathrm{lam}(2) = \frac{3}{10}$ of
   `Frame.lam` (`ExplicitFormulaErrorOfHostConditions.lean:135` at $o = 3$, $3o + 1 = 10$)! Compute
   $\frac{1}{\lvert TT \rvert}\sum_{t \in TT} \omega^{kt}$ for each $k \in \{0, 1, 2\}$:
   - for $k = 0$: $\frac{4N + 3N + 3N}{10N} = 1$;
   - for $k = 1$ or $k = 2$:
     $$\frac{4N \cdot 1 + 3N \cdot \omega^k + 3N \cdot \omega^{2k}}{10N}
     = \frac{1 + 3(1 + \omega^k + \omega^{2k})}{10} = \frac{1 + 0}{10} = \frac{1}{10} = \frac{1}{3o + 1} > 0!$$
   Look why the archive gave the identity coset $A_0$ weight $4/(3o+1)$ and every other coset weight
   $3/(3o+1)$: writing $(4, 3, \dots, 3) = (3, 3, \dots, 3) + (1, 0, \dots, 0)$ decomposes the
   measure as $\frac{3o}{3o+1}$ times **uniform measure** (whose Fourier transform vanishes on every
   $k \neq 0$!) plus $\frac{1}{3o+1}$ times a **Dirac delta at $0$** (whose Fourier transform is
   identically $+1$ on *every* character $k$)! Thus every kept character $\psi^k$ ($k \neq 0$)
   receives the exact positive weight $(3o + 1)^{-1}$ of Chapter 3's `Level.Gm` (`ExplicitFormulaErrorOfHostConditions.lean:36–38`)!

### 5.2.2 Toy optimization: $x/m + m$ at $1/2$ versus $x/m + m^2$ at $2/3$

Suppose an inequality of Stepanov/Arakelov type produces $m$ units of prime-sum signal $m \cdot G(x)$
against a fixed archimedean degree cost $x$ plus a congruence/Selmer error from the $m$ lifts
[Expository]:

- **Compounding per-lift cost (the $2/3$ trap):** Look at `errorBracketSizeWindows`
  (`ErrorFormsWeakWindowsFalse.lean:133`, `SZ.T3` at `LipschitzWeightAndMinimum.lean:53`): in the
  actual chain, **even a single lift** has Hodge–Tate/Selmer rank proportional to $m$ (so
  $B_0 \asymp n m b x^\varepsilon$ already carries **one** factor of $m$), and summing a fixed
  per-lift charge $B_0$ across all $m$ lifts (`m * B_0`) already produces **$m^2$** in the
  numerator before dividing by the signal prefactor $m \cdot n b$:
  $$\frac{m \cdot B_0}{m \cdot n b} \asymp \frac{m \cdot (n m b x^\varepsilon)}{m \cdot n b} = m\,x^\varepsilon.$$
  Had lift $j \in \{1, \dots, m\}$ compounded across the $j$ lifts below it (paying $j \cdot B_0$
  at step $j$), the numerator would have been $\sum_{j=1}^m j \cdot B_0 \asymp m^2 B_0 \asymp n m^3 b x^\varepsilon$,
  which after dividing by $m \cdot n b$ leaves
  $$\frac{x}{m} + m^2\,x^\varepsilon, \qquad \min_{m \ge 1}\Bigl(\frac{x}{m} + m^2\Bigr) = \frac{3}{2^{2/3}}\,x^{2/3} \quad\text{at } m \asymp x^{1/3}!$$
  That is the a priori $2/3$ barrier recorded in Alpöge's timeline ("11/15/26: precise computation
  of the 'cost' of each lift, showing that one would stop at $2/3$ a priori, attempt to get a main
  term and transfer constant to a function field or kill via twisting, need for 'division'",
  `remark.pdf` p. 4, item 14) [Paper; remark p. 4] and traced in community guides [Community].
- **Non-compounding per-lift cost (`SZ.T1`–`SZ.T4`):** Because `CoreAtH` / `SizeData₂` charges only
  $m \cdot B_0$ (one factor of $m$ times $B_0 \asymp n m b x^\varepsilon$), dividing by the signal
  prefactor $Q \asymp n_T m b$ leaves
  $$G(x) \lesssim \underbrace{\frac{x}{m}}_{\text{archimedean }\mathrm{T1}}
  + \underbrace{\frac{x m}{k}}_{\text{word ratio }\mathrm{T2}}
  + \underbrace{m\,x^{9\varepsilon/8}}_{\text{Selmer/Ш }\mathrm{T3}}
  + \underbrace{\frac{k}{n^2}\,x^{17\varepsilon/8}}_{2\text{-adic level }\mathrm{T4}}.$$
  Choosing $m \in [x^{1/2 - \varepsilon}, x^{1/2 + \varepsilon/2}]$, $n \asymp x^{2 + 8\varepsilon}$,
  and $k \asymp x^{9/2 + 10\varepsilon}$ (note $xm \approx x \cdot x^{1/2} = x^{3/2} \ll x^{9/2+10\varepsilon} = k \le n^2 x^{1/2-\varepsilon} \approx x^{4+16\varepsilon} \cdot x^{1/2-\varepsilon} = x^{9/2+15\varepsilon}$!)
  makes $\mathrm{T1} \le 2 x^{1/2+\varepsilon}$, $\mathrm{T2} \le 2$, $\mathrm{T3} \le 4 x^{1/2+13\varepsilon/8}$,
  and $\mathrm{T4} \le 2 x^{1/2+9\varepsilon/8}$ — hitting exponent **$1/2 + O(\varepsilon)$** on
  every single term!

---

## 5.3 Definitions

We now state the exact Lean definitions used in `ChBalance`, `ChCore`, `ChTop`, and `CoreGm`.

### 5.3.1 Finite group arithmetic data, `ASK`, `MAIN`, and `De`

Let $E_0 := \mathbb Z/2\mathbb Z \times \mathbb Z/2\mathbb Z$ (`E0`, additive group of order $4$)
with distinguished elements $\mathrm{sg} = (0, 1)$, $\mathrm{sgc}_0 = (1, 0)$, complex-conjugation
element $\mathrm{cconj} = (1, 1)$ (viewed in $E_0 \times H$ via $(e, 0)$), and character
$\mathrm{ch}_C((e_1, e_2), h) = (-1)^{e_1}$, and let $\Phi := \{g \in E_0 \times H : g_{1,1} = 0\}$
(`InPhi`, `PhiSet` of cardinality $f_{\mathrm{Pl}}(H) = 2\lvert H \rvert$, where $H$ is a finite
abelian group, instantiated as $H = \varphi.A$) [Lean, read]
(`src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:15–25`). For $t \in H$ and
$g \in E_0 \times H$, define the **partner map** (`partner`, `:19`)
$$\mathrm{partner}_t(g) := \mathrm{cconj} + g + \mathrm{topPl}(t) = \bigl((g_{1,1} + 1, g_{1,2} + 1),\,g_2 + t\bigr).$$
Because $\mathrm{cconj}$ flips the first coordinate $g_{1,1}$, for every $g \notin \Phi$ ($g_{1,1} = 1$)
the element $\mathrm{partner}_t(g)$ has first coordinate $1 + 1 = 0$, landing **inside $\Phi$**
(`partner_inPhi : g ∉ PhiSet H → partner t g ∈ PhiSet H`, `LipschitzWeightAndMinimum.lean:214`)
bijectively as a map $\Phi^c \xrightarrow{\sim} \Phi$ (`PartnerBij`, `:127`) [Lean, read]. Thus a
place-weight function $w : \Phi \to \mathbb R$ (assigning positive weights to the $2\lvert H \rvert$
CM-type places of $E$) evaluates at $\mathrm{partner}_t(g) \in \Phi$ for every $g \notin \Phi$.

**Definition 5.1 (`ArithData`, `GPsi`, `ASK`, `MAIN`, and `De`, `src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:38,65,68,72,84,89,93`).**

1. **Arithmetic host record (`ArithData H`, `:38`).** Packages the four fields `q1`, `d`
   ($q_1 = H.q$, $d = H.d$), inertia subgroup $\mathrm{inertia} : \mathbb N \to \mathrm{AddSubgroup}(E_0 \times H)$,
   and Frobenius representative $\mathrm{frob} : \mathbb N \to E_0 \times H$. By `HostFactsS D S₀`
   (`src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean:14`), at unramified
   primes $p \notin S_0 \cup \{d\}$ we have $\mathrm{inertia}(p) = \{0\}$; at split primes
   $p \in S_0 = \{2, q_1\} \cup \mathrm{small}$ ($d \notin S_0$), both $\mathrm{frob}(p)$ and
   $\mathrm{inertia}(p)$ lie inside $\Phi$; and at $d$, $\mathrm{inertia}(d) = \{0, \mathrm{sgc}_0\}$,
   whose first bit $(1, 0)$ guarantees that every coset $i\,\mathrm{frob}(d) + \mathrm{inertia}(d)$
   meets $\Phi^c$ in a unique element (`DCosetSingle`, `:130`) [Lean, read].
2. **Primitive character values and Riesz sums (`primVal` and `GPsi`, `:65, 68`).** For an additive
   character $\psi \in \widehat{E_0 \times H}$ and $n = p_1^{a_1}\cdots p_k^{a_k} \ge 1$,
   `primVal D ψ n` (`:65`) multiplies over $p^a \parallel n$ the inertia-averaged Frobenius values
   $\frac{1}{\lvert I_p \rvert}\sum_{u \in I_p} \psi(a\,\mathrm{frob}(p) + u)$ (which by
   `prim_read`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/PrimRead.lean:48`, equals
   $\chi_\psi^\ast(n)$ for the primitive Dirichlet character $\chi_\psi^\ast$ attached to $\psi$!) [Lean, read].
   Given $\ell : \widehat{E_0 \times H} \to \mathbb C$ with $\ell(\psi) = \frac{L'}{L}(1, \chi_\psi^\ast)$
   for $\psi \neq 0$ (`HostAddCharCompatible`, `CoreAtH.lean:18`), `GPsi D ell ψ y` (`:68`) equals
   `Gz y` when $\psi = 0$ and $\sum_{1 \le n \le \lfloor y \rfloor} \Lambda(n)\,\mathrm{primVal}(D,\psi,n)(y/n - 1) + y\,\ell(\psi) = \mathrm{An.gChi}\,\chi_\psi^\ast\,y$
   when $\psi \neq 0$ (`prim_read`, `:51`) [Lean, read].
3. **Inert prime sum, main term, and character-side discrepancy (`ASK`, `MAIN`, `De`, `:72–96`).**
   A prime $p \neq 2, q_1, d$ is **inert** (`IsInert D p`, `:72`) if $\mathrm{frob}(p) \notin \Phi$.
   For truncation $N \in \mathbb N$, top parameter $a > 0$, shift $t \in H$, and place weights
   $w : E_0 \times H \to \mathbb R$ [Lean, read]:
   $$\mathrm{ASK}(D, N, a, t, w) := \sum_{\substack{p \le N \\ \mathrm{IsInert}\,D\,p}} 2\log p
   \sum_{\substack{1 \le i \le N \\ i\cdot\mathrm{frob}(p) \notin \Phi}}
   \max\Bigl(\frac{a}{p^i} - w\bigl(\mathrm{partner}_t(i\,\mathrm{frob}(p))\bigr),\ 0\Bigr)
   + \log d \cdot \mathrm{askD}(D, N, a, t, w),$$
   where $\mathrm{askD}$ (`:79`) sums $\max(a/d^i - w(\mathrm{partner}_t(g)), 0)$ over $1 \le i \le N$
   and $g \in (i\,\mathrm{frob}(d) + \mathrm{inertia}(d)) \cap \Phi^c$ (vanishing identically
   whenever $N < d$, `ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime`, `ChBalance.lean:18`!);
   $$\mathrm{MAIN}(\ell, a, w) := a\Bigl(\log a - 1 - \gamma + \ell(\mathrm{ch}_C)
   - \frac{1}{\lvert\Phi\rvert}\sum_{\rho \in \Phi} \log w(\rho)\Bigr)
   = \frac{1}{\lvert\Phi\rvert}\sum_{\rho \in \Phi}
   \Bigl[a\log\Bigl(\frac{a}{w(\rho)}\Bigr) - (1 + \gamma)a + a\,\ell(\mathrm{ch}_C)\Bigr];$$
   $$\mathrm{De}(D, \ell, a, t, w) := \frac{1}{\lvert\Phi\rvert}\sum_{g \in \Phi^c}
   \sum_{\psi \in \widehat{E_0 \times H}} \overline{\psi(g)}\,w(\mathrm{partner}_t(g))\,
   \mathrm{GPsi}\Bigl(D, \ell, \psi, \frac{a}{w(\mathrm{partner}_t(g))}\Bigr).$$

### 5.3.2 Subgroup projection (`PsiA`, `GmA`, `SigA`) and the two hypothesis packages (`EAtH`, `CoreAtH`)

**Definition 5.2 (`PsiA`, `GmA`, and `SigA`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean:26,30,34,39`).**
Let $A_0 \le H$ be a subgroup, let $\mathrm{Kept}_A \subseteq \widehat{E_0 \times H}$ be a finite
subset (`keptA Λ H`, `CoreAtH.lean:24`), and let $c_{\mathrm{top}} \in \mathbb R$ (instantiated as
$c_{\mathrm{top}} = (3\,\Lambda.o + 1)^{-1}$) [Lean, read]:

1. $\Psi_A(A_0) := \bigl\{\psi \in \widehat{E_0 \times H} : \forall s \in A_0,\ \psi(0, s) = 1\bigr\}$;
2. for $\psi \in \widehat{E_0 \times H}$, $\mathrm{wt}_A(c_{\mathrm{top}}, \psi) := 1$ if
   $\psi(0, h) = 1$ for all $h \in H$, and $c_{\mathrm{top}}$ otherwise;
3. the **projected signal** and **parasitic remainder** at scale $x$ are
   $$\mathrm{Gm}_A(x) := \sum_{\psi \in \mathrm{Kept}_A} \mathrm{wt}_A(c_{\mathrm{top}}, \psi)\,\Re\,\mathrm{GPsi}(D, \ell, \psi, x),
   \qquad
   \mathrm{Sig}_A(x) := \sum_{\psi \in \Psi_A(A_0) \setminus \mathrm{Kept}_A} \bigl\lVert \mathrm{GPsi}(D, \ell, \psi, x) \bigr\rVert.$$

**Definition 5.3 (Host conditions `EAtH` and chain conditions `CoreAtH`).**

1. **Host analytic/equidistribution bundle (`Formalism.HC.EAtH`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:144`).**
   For a character level $\Lambda$, `H : HostRaw φ`, $TT \subseteq \varphi.A$, and reals $x, \varepsilon, C$,
   `EAtH Λ H TT x eps C` asserts six conditions [Lean, read]:
   - `kept`: every $p \in \Lambda.\mathrm{KEPT}$ is the primitive character of some $\theta \in \varphi.Xp$ (`KeptInXp`);
   - `exc`: the exceptional quadratic character slot `Λ.psK` is respected (`ExceptionalCharacterKept`);
   - `o_eq`: $\varphi.o = \Lambda.o$ (i.e. $[\varphi.A : \varphi.A_0] = \Lambda.o$);
   - `bdG`: for every $\theta \in H.\mathrm{Bounded}(\Lambda.\mathrm{KEPT})$, its primitive character
     $\chi$ satisfies $\lVert \mathrm{An.gChi}\,\chi\,x \rVert \le x^{1/2 + \varepsilon}$ (`BoundedCharsPointwise`);
   - `bdL`: for every $\theta \in H.\mathrm{Bounded}(\Lambda.\mathrm{KEPT})$, its primitive character
     $\chi$ satisfies $\lVert \frac{L'}{L}(1, \chi) \rVert \le C \log x$;
   - `shares`: for every $g \in \varphi.A$,
     $$\Bigl\lvert \#\{t \in TT : t - g \in \varphi.A_0\} - \varphi.\mathrm{lam}(g)\,\lvert TT \rvert \Bigr\rvert
     \le x^{-1 + \varepsilon}\,\lvert TT \rvert,$$
     where $\varphi.\mathrm{lam}(g) = \frac{4}{3\varphi.o + 1}$ if $g \in \varphi.A_0$ and $\frac{3}{3\varphi.o + 1}$
     if $g \notin \varphi.A_0$ (`Frame.lam`, `:135`; `Frame.Shares`, `:139`).
2. **Chain existence bundle (`UpperTheory.Comparison₂.CoreAtH`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean:29`).**
   At `H : HostRaw φ`, $TT \subseteq \varphi.A$, constants $(e_D, e_L, K, c_{HH}, e_K)$, $\varepsilon$,
   and scale $x$, `CoreAtH` asserts the existence of a finite index set $U_0$ surjecting onto
   $\varphi.A_0$ via $\mathrm{tr} : U_0 \to \varphi.A$, word families $W(u_0)$, chain length
   $m \in \mathbb N$, $f = 2\lvert \varphi.A \rvert$, chain datum `Dd : SizeData₂` (`src/Formalism/SizeWindowBrackets/SChain.lean:17`)
   at `(Dd.x, Dd.ε) = (x, eps)` with constants `(eDiv, eLoss, cHH) ≤ (eD, eL, cHH)`, thick place-set
   $T_2 \subseteq \Phi$ of density $\delta_2 = \lvert T_2 \rvert / \lvert \varphi.A \rvert \ge x^{-\varepsilon}$,
   top scales $a_t = x b + O(b)$ ($t \in TT$), place weights $w_{u_0, j} : \Phi \to \mathbb R$
   ($0 \le j < m$), and error parameters $(\eta, X', \theta)$ satisfying [Lean, read]:
   - **Algebraic & Arakelov chain clauses (`IdentU`, `ErrWindows`, `BNBoundsU`, plus the host-character
     bridge `ReadsKept`, `SplitInertia.lean:67,74,81`, `CoreAtH.lean:29`, and
     `ErrorFormsWeakWindowsFalse.lean:43`):** the $11$-clause Hermitian/Hida divisibility-and-slope
     package `SizeData₂` (`src/Formalism/SizeWindowBrackets/SChain.lean:17`, opened in Part II, Chapters 6–10) whose weighted-mean
     gap is bounded by $x^{\mathrm{CErr}(C_c)\varepsilon}\,\mathcal E_{\mathrm{win}}$ (paired with
     `ReadsKept` on `CoreAtH` matching `keptA` to the host characters), where
     $\mathrm{CErr}(C_c) = e_{\mathrm{Div}} + e_{\mathrm{Loss}} + 3 \le e_D + e_L + 3$
     (`ErrorFormsWeakWindowsFalse.lean:19`) and
     $$\mathcal E_{\mathrm{win}}(x, \varepsilon, n, n_T, n_{T_2}, m, b, k, a_E)
     := n_T a_E + n_T a_E \frac{m^2}{k} + m\,(2 n m b\,x^\varepsilon) + m\,\frac{n_{T_2} k b\,x^{2\varepsilon}}{n^2}$$
     (`errorBracketSizeWindows`, `ErrorFormsWeakWindowsFalse.lean:133`);
   - **Scale windows (`SizesA`, `ThinScales`, `CostWindows`, `RestSize`, `SplitInertia.lean:42` and
     `src/Formalism/SizeWindowBrackets/SChain.lean:50,53`):** in particular,
     $$x^{1/2 - \varepsilon} \le m \le x^{1/2 + \varepsilon/2}, \qquad
     x m \le k \le n^2\,x^{1/2 - \varepsilon}, \qquad
     n \le 2\,n_T\,x^{\varepsilon/8}, \qquad
     a_E \le 2 x b,$$
     thick weights $w_{u_0, j}(\rho) \in [b, b + \eta + 1]$ on $\rho \in T_2 + (0, u_0)$, thin
     weights $A / w \ge X'/3$ with unconditional zero-free decay $\theta$ satisfying
     $2 f (x + 1)\theta \le 1/x$, and Lipschitz window step $6 f (x + 1)(\eta + 1) \le b/x$
     (`CostWindows`, `src/Formalism/SizeWindowBrackets/SChain.lean:50`, where $f = 2\lvert\varphi.A\rvert$).

---

## 5.4 Lemmas and proofs

We now prove `core_gm` from end to end in five clean steps, following the exact proof terms of
`ChBalance.lean`, `LipschitzWeightAndMinimum.lean`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean`, `ChTop.lean`, `GmAEq.lean`,
`SigALe.lean`, and `CoreGm.lean`.

### 5.4.1 Prime-to-character Fourier identity on $E_0 \times H$ (`ch_balance`)

**Theorem 5.1 (Inert prime sum minus main term equals character-side discrepancy: `ch_balance`).**
*Let $H$ be a finite abelian group, let $D : \mathrm{ArithData}\,H$ satisfy `HostFactsS D S₀` for a
finite prime set $S_0$ with $d \notin S_0$, let $\ell : \widehat{E_0 \times H} \to \mathbb C$, and
let $N \in \mathbb N$, $a > 0$, $t \in H$, and $w : E_0 \times H \to \mathbb R$ satisfy $w(\rho) > 0$
and $a / w(\rho) \le N$ for all $\rho \in \Phi$. Then*
$$\mathrm{ASK}(D, N, a, t, w) - \mathrm{MAIN}(\ell, a, w) = \mathrm{De}(D, \ell, a, t, w).$$
*(Lean: `Deduction.CH.ch_balance`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean:200`.)* [Lean, read]

*Proof.* Start from the right-hand side $\mathrm{De}(D, \ell, a, t, w)$. Fix $g \in \Phi^c$, set
$\rho := \mathrm{partner}_t(g) \in \Phi$, and set $y_\rho := a / w(\rho) \le N$. Recall from
`FirstPrimeNeSecondPrime.lean:68` and `src/Formalism/StatementOC.lean:13` how
$\mathrm{GPsi}(D, \ell, \psi, y_\rho)$ splits between $\psi = 0$ and $\psi \neq 0$ (note that
$\ell(0)$ is never evaluated!):

- For $\psi = 0$, $\mathrm{primVal}(D, 0, n) = 1$, and $\mathrm{GPsi}(D, \ell, 0, y_\rho) = \mathrm{Gz}(y_\rho) = \sum_{1 \le n \le \lfloor y_\rho \rfloor} \Lambda(n)(y_\rho/n - 1) - y_\rho\log y_\rho + (1 + \gamma)y_\rho$.
- For $\psi \neq 0$, $\mathrm{GPsi}(D, \ell, \psi, y_\rho) = \sum_{1 \le n \le \lfloor y_\rho \rfloor} \Lambda(n)\,\mathrm{primVal}(D, \psi, n)(y_\rho/n - 1) + y_\rho\,\ell(\psi)$.

Multiply by $\overline{\psi(g)}\,w(\rho)$ (note $w(\rho) y_\rho = a$) and sum over all
$\psi \in \widehat{E_0 \times H}$ and $g \in \Phi^c$, dividing by $\lvert\Phi\rvert = \frac{1}{2}\lvert E_0 \times H \rvert = 2\lvert H \rvert$:

1. **The main-term pieces cancel to $-\mathrm{MAIN}(\ell, a, w)$ (`colour_sum`, `ChBalance.lean:212–235`).**
   First, at $\psi = 0$ ($\overline{0(g)} = 1$), the counterterm $w(\rho)\bigl(-y_\rho\log y_\rho + (1+\gamma)y_\rho\bigr) = -a\log(a/w(\rho)) + (1+\gamma)a$
   averages over $g \in \Phi^c$ (as $\rho = \mathrm{partner}_t(g)$ runs bijectively over the
   $\lvert\Phi\rvert$ elements of $\Phi$) to
   $-\frac{1}{\lvert\Phi\rvert}\sum_{\rho \in \Phi}\bigl[a\log(a/w(\rho)) - (1+\gamma)a\bigr]$.
   Second, for the linear $\ell(\psi)$ counterterms ($\psi \neq 0$, where $w(\rho) y_\rho\,\ell(\psi) = a\,\ell(\psi)$
   is independent of $g$), summing $\overline{\psi(g)}$ over $g \in \Phi^c = \{((1, e_2), h)\}$
   annihilates every character $\psi \neq 0$ **except** $\psi = \mathrm{ch}_C$, where
   $\mathrm{ch}_C(g) = -1$ for all $\lvert\Phi\rvert$ elements $g \in \Phi^c$, giving
   $\frac{1}{\lvert\Phi\rvert}\sum_{g \in \Phi^c} (-1)\,a\,\ell(\mathrm{ch}_C) = -a\,\ell(\mathrm{ch}_C)$.
   Combining the two pieces produces $-\mathrm{MAIN}(\ell, a, w)$ on the nose.
2. **The prime-power sum collapses to $\mathrm{ASK}(D, N, a, t, w)$ (`askExp`, `lunram`, `lsplit`, `ld`,
   `ChBalance.lean:55–196`).** For each prime power $n = p^i \le y_\rho \le N$ ($i \ge 1$), character
   orthogonality on the finite abelian group $E_0 \times H$ of order $2\lvert\Phi\rvert$ gives, upon
   dividing by $\lvert\Phi\rvert$ instead of $2\lvert\Phi\rvert$,
   $$\frac{1}{\lvert\Phi\rvert}\sum_{\psi \in \widehat{E_0 \times H}} \overline{\psi(g)}\,\mathrm{primVal}(D, \psi, p^i)
   = \frac{2}{\lvert I_p \rvert}\,\mathbf{1}_{\,g - i\,\mathrm{frob}(p) \in I_p}.$$
   Examine the three types of primes $p$ for $g \in \Phi^c$ ($g_{1,1} = 1$):
   - **Split primes $p \in S_0$ (`lsplit`, `:77`):** Both $\mathrm{frob}(p)$ and every $u \in I_p$
     lie in $\Phi$ (first bit $0$). Hence $i\,\mathrm{frob}(p) + u \in \Phi$ can **never** equal
     $g \in \Phi^c$: every prime in $S_0$ (including $2$, $q_1$, and all prime divisors of $\psi.N$)
     contributes **identically $0$**.
   - **Unramified primes $p \notin S_0 \cup \{d\}$ (`lunram`, `:55`):** Here $\lvert I_p \rvert = 1$,
     so the prefactor $\frac{2}{\lvert I_p \rvert} = 2$! Because the first coordinate of $E_0$ lives
     in $\mathbb Z/2\mathbb Z$, $i\,\mathrm{frob}(p) \notin \Phi$ holds if and only if
     **$\mathrm{frob}(p) \notin \Phi$ ($p$ is inert) and $i$ is odd**. When both hold, the unique
     $g = i\,\mathrm{frob}(p) \in \Phi^c$ contributes
     $2\log p \cdot \max\bigl(a/p^i - w(\mathrm{partner}_t(i\,\mathrm{frob}(p))),\ 0\bigr)$,
     matching $2\log p \cdot \mathrm{askP}(p)$ (`FirstPrimeNeSecondPrime.lean:75, 86`).
   - **The ramified prime $p = d$ (`ld`, `:99`):** Here $\lvert I_d \rvert = 2$, so
     $\frac{2}{\lvert I_d \rvert} = 1$, and $i\,\mathrm{frob}(d) + I_d$ meets $\Phi^c$ in a unique
     element $g$, reproducing $\log d \cdot \mathrm{askD}$.

Thus $\mathrm{De} = \mathrm{ASK} - \mathrm{MAIN}$. $\square$

### 5.4.2 Thick/thin smoothing, $A_0$-averaging, and $TT$-equidistribution (`ChCore` & `tops_sum`)

Theorem 5.1 still evaluates $\mathrm{GPsi}(D, \ell, \psi, a_t / w_{u_0, j}(\rho))$ at the
place-dependent argument $a_t / w_{u_0, j}(\rho)$ rather than at the single target scale $x$. How
does `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean` replace $a_t / w_{u_0, j}(\rho)$ by $x$ and isolate $\Psi_A(A_0)$?

**Lemma 5.2 (Subgroup orthogonality, thick/thin replacement, and coset equidistribution).**

1. **Subgroup averaging (`sum_A` and `sum_Th`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:28,56`).**
   *Because the thick indicator $\mathbf{1}_{\rho \in T_2 + (0, u_0)}$ is invariant under simultaneous
   translation $(\rho, u_0) \mapsto (\rho + (0, s), u_0 + s)$ for $s \in A_0$, averaging over
   $u_0 \in A_0$ kills every character $\psi \notin \Psi_A(A_0)$, while on $\psi \in \Psi_A(A_0)$
   each $(t, j)$ contributes $\lvert A_0 \rvert \cdot \frac{\lvert T_2 \rvert}{\lvert \Phi \rvert} = \lvert A_0 \rvert\,\frac{\delta_2}{2}$
   copies of $b\,\psi(\mathrm{e}_1(t))\,\mathrm{GPsi}(\psi, a_t/b)$, where
   $\mathrm{e}_1(t) := ((1, 0), t) \in E_0 \times H$ (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:16, 59`).* [Lean, read]
2. **Thick Lipschitz + thin zero-free error (`th_le`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:75`, and `move`, `:154`).**
   *On thick places ($\rho \in T_2 + (0, u_0)$), $w_{u_0, j}(\rho) \in [b, b + \eta + 1]$, and the
   Lipschitz bound `LipW` (`LipschitzWeightAndMinimum.lean:957`) bounds the replacement of
   $w\,\mathrm{GPsi}(\psi, a_t/w)$ by $b\,\mathrm{GPsi}(\psi, a_t/b)$ within $O(x\eta) \le b/x$
   (`CostWindows`). On thin places ($\rho \notin T_2 + (0, u_0)$), $a_t / w_{u_0, j}(\rho) \ge X'/3$,
   where the unconditional de la Vallée Poussin decay parameter $\theta$ (`ThinScales`, $(x + 1)\theta \le 1/x$)
   bounds $\lvert w\,\mathrm{GPsi}(\psi, a_t/w) \rvert \le (x+1) b \theta \le b/x$. Finally, shifting
   $a_t / b = x + O(1)$ to $x$ (`move`, `:154`) changes $\mathrm{GPsi}(\psi, a_t/b)$ by at most
   $O(\log x + \lvert \ell(\psi) \rvert)$.* [Lean, read]
3. **Coset equidistribution over $TT$ (`UpperTheory.Comparison₂.tops_sum`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/TopsSum.lean:75`).**
   *If `φ.Shares TT δ` holds, then for every $\psi \in \Psi_A(\varphi.A_0)$:*
   - *if $\psi(0, h) = 1$ for all $h \in \varphi.A$, then $\sum_{t \in TT} \overline{\psi(0, t)} = \lvert TT \rvert$;*
   - *if $\psi$ is nontrivial on $\{0\} \times \varphi.A$, then*
     $$\Bigl\lVert \sum_{t \in TT} \overline{\psi(0, t)} - \frac{1}{3\,\varphi.o + 1}\,\lvert TT \rvert \Bigr\rVert
     \le \varphi.o\,\delta\,\lvert TT \rvert.$$
   *(At $\delta = x^{-1 + \varepsilon}$, pairing against the elementary a priori bound
   $\lvert \mathrm{GPsi}(\psi, x) \rvert \le 3x + x\lvert\ell(\psi)\rvert \ll x\log x$ in `vv`,
   `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:183`, gives error $O(\varphi.o\,x^\varepsilon \log x) \ll x^{1/2}$.)* [Lean, read]

*Proof.* Items (1) and (2) are direct applications of finite character orthogonality
$\sum_{u_0 \in A_0} \psi(0, u_0) = \lvert A_0 \rvert\,\mathbf{1}_{\psi \in \Psi_A(A_0)}$, the
piecewise-linear Lipschitz property of $w \mapsto w(a/w/n - 1)_+ = (a/n - w)_+$ (which is $1$-Lipschitz
in $w$ at every $n$!), and `ThinScales`. For item (3) (`TopsSum.lean:26–103`), let $\theta(h) := \psi(0, h)$
(or its conjugate, which is also in $\Psi_A(A_0)$ and nontrivial on $\varphi.A$). Because $\theta$ is
constant on cosets of $A_0$ in $\varphi.A$ and $[\varphi.A : A_0] = \varphi.o$, choose coset
representatives $g_1, \dots, g_o$ ($g_1 \in A_0$). Writing $N_r := \#\{t \in TT : t - g_r \in A_0\}$,
`Shares TT δ` says $N_r = \varphi.\mathrm{lam}(g_r)\lvert TT \rvert + e_r$ with $\lvert e_r \rvert \le \delta\lvert TT \rvert$.
Since $\theta$ induces a nontrivial character of the quotient group $\varphi.A / A_0$, we have
$\sum_{r=1}^o \theta(g_r) = 0$, and $\theta(g_1) = 1$ (since $g_1 \in A_0$). Therefore
$$\begin{aligned}
\sum_{t \in TT} \theta(t)
&= \sum_{r=1}^o N_r\,\theta(g_r) \\
&= \frac{3\lvert TT \rvert}{3\varphi.o + 1}\sum_{r=1}^o \theta(g_r)
   + \frac{\lvert TT \rvert}{3\varphi.o + 1}\,\theta(g_1)
   + \sum_{r=1}^o e_r\,\theta(g_r)
= \frac{\lvert TT \rvert}{3\varphi.o + 1} + \sum_{r=1}^o e_r\,\theta(g_r).
\end{aligned}$$
Since $\lvert \theta(g_r) \rvert = 1$ and $\lvert e_r \rvert \le \delta\lvert TT \rvert$ for each of
the $\varphi.o$ cosets, the error has norm at most $\varphi.o\,\delta\,\lvert TT \rvert$. $\square$

### 5.4.3 Balancing $x/m + m$: the size bound (`SZ.T1`–`SZ.T4` and `proposition_size_bound`)

We now prove the exact inequality where the exponent **$1/2$** is born!

**Proposition 5.3 (From the four-term chain error bracket to exponent $1/2$: `proposition_size_bound`).**
*Let $\varepsilon > 0$ and $C \ge 0$, and suppose $x \ge 1$ is large enough that $26 \le x^{3\varepsilon/8}$
(and $1/x \le x^{1/2+\varepsilon}$). Suppose positive parameters $(n, n_T, n_{T_2}, m, b, k, a_E, \delta_2)$
satisfy `SizeWindows` (`GrowthBoundGivesRiemannHypothesis.lean:109`):*
$$x^{1/2 - \varepsilon} \le m \le x^{1/2 + \varepsilon/2}, \qquad
x m \le k \le n^2\,x^{1/2 - \varepsilon}, \qquad
n \le 2\,n_T\,x^{\varepsilon/8}, \qquad
n_{T_2} \le n, \qquad
a_E \le 2 x b, \qquad
\delta_2 \ge x^{-\varepsilon}.$$
*If a real number $G_x$ satisfies the core Fourier inequality*
$$n_T\,m\,b\,\frac{\delta_2}{2}\,\bigl(G_x - 4\,x^{1/2 + \varepsilon}\bigr)
\le x^{C\varepsilon}\,\mathcal E_{\mathrm{win}}(x, \varepsilon, n, n_T, n_{T_2}, m, b, k, a_E)
+ \frac{2\,n_T\,m\,b}{x},$$
*then*
$$G_x \le x^{1/2 + (C + 3)\varepsilon}.$$
*(Lean: `SZ.T1`, `SZ.T2`, `SZ.T3`, `SZ.T4` and `proposition_size_bound`,
`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:31,41,53,77,507`.)* [Lean, read]

*Proof.* Set $Q := n_T\,m\,b > 0$ and bound each of the four summands of
$\mathcal E_{\mathrm{win}} / Q$ one by one (`LipschitzWeightAndMinimum.lean:31–113`):

1. **Term `T1` (archimedean top weight $n_T a_E$):** Using $a_E \le 2xb$ and $m \ge x^{1/2 - \varepsilon}$,
   $$\frac{n_T\,a_E}{n_T\,m\,b} = \frac{a_E}{m\,b} \le \frac{2xb}{m\,b} = \frac{2x}{m}
   \le \frac{2x}{x^{1/2 - \varepsilon}} = 2\,x^{1/2 + \varepsilon}
   \le 2\,x^{1/2 + 13\varepsilon/8}.$$
2. **Term `T2` (word-count ratio $n_T a_E m^2 / k$):** Using $a_E \le 2xb$ and $k \ge xm$,
   $$\frac{n_T\,a_E\,(m^2 / k)}{n_T\,m\,b} = \frac{a_E\,m}{b\,k} \le \frac{2xb\,m}{b\,(xm)} = 2
   \le 2\,x^{1/2 + 13\varepsilon/8}.$$
3. **Term `T3` (per-lift Selmer / congruence charge $m \cdot (2 n m b\,x^\varepsilon)$):** Using
   $n \le 2 n_T x^{\varepsilon/8}$ and **$m \le x^{1/2 + \varepsilon/2}$**,
   $$\frac{2\,n\,m^2\,b\,x^\varepsilon}{n_T\,m\,b}
   = \frac{2n}{n_T}\,m\,x^\varepsilon
   \le 4\,x^{\varepsilon/8} \cdot x^{1/2 + \varepsilon/2} \cdot x^\varepsilon
   = 4\,x^{1/2 + 13\varepsilon/8}!$$
4. **Term `T4` ($2$-adic level / congruence term $m \cdot n_{T_2} k b\,x^{2\varepsilon} / n^2$):**
   Using $n_{T_2} \le n$, $n \le 2 n_T x^{\varepsilon/8}$, and $k \le n^2 x^{1/2 - \varepsilon}$,
   $$\frac{m\,n_{T_2}\,k\,b\,x^{2\varepsilon} / n^2}{n_T\,m\,b}
   \le \frac{n}{n_T} \cdot \frac{k}{n^2}\,x^{2\varepsilon}
   \le 2\,x^{\varepsilon/8} \cdot x^{1/2 - \varepsilon} \cdot x^{2\varepsilon}
   = 2\,x^{1/2 + 9\varepsilon/8}
   \le 2\,x^{1/2 + 13\varepsilon/8}!$$

Adding the four bounds gives $\mathcal E_{\mathrm{win}} / Q \le (2 + 2 + 4 + 2)\,x^{1/2 + 13\varepsilon/8} = 10\,x^{1/2 + 13\varepsilon/8}$!
Now divide the core Fourier inequality by $Q\,\frac{\delta_2}{2} > 0$, using $\frac{2}{\delta_2} \le 2\,x^\varepsilon$:
$$\begin{aligned}
G_x &\le 4\,x^{1/2 + \varepsilon}
   + \frac{2}{\delta_2}\,x^{C\varepsilon}\,\frac{\mathcal E_{\mathrm{win}}}{Q}
   + \frac{2}{\delta_2}\,\frac{2}{x} \\
&\le 4\,x^{1/2 + \varepsilon}
   + 20\,x^{1/2 + (C + 1 + 13/8)\varepsilon}
   + 4\,x^{-1 + \varepsilon} \\
&\le (4 + 20 + 2)\,x^{1/2 + (C + 21/8)\varepsilon}
= 26\,x^{1/2 + (C + 21/8)\varepsilon}.
\end{aligned}$$
Since $26 \le x^{3\varepsilon/8}$ and $\frac{21}{8} + \frac{3}{8} = \frac{24}{8} = 3$, the right-hand
side is at most $x^{1/2 + (C + 3)\varepsilon}$! $\square$

### 5.4.4 Matching `GmA` to `Λ.Gm`, bounding `SigA`, and proving `core_gm`

Two short identification lemmas connect `GmA` and `SigA` on $E_0 \times \varphi.A$ to the Dirichlet
character level $\Lambda$, after which `core_gm` closes in ten lines of algebra!

**Lemma 5.4 (Identification of `GmA` with `Λ.Gm` and bound on `SigA`).** *Assume
`EAtH Λ H.toHostRaw TT x eps C` and `HostAddCharCompatible H.toHostRaw ell` (`x > 0`). Then:*

1. **(`UpperTheory.Comparison₂.gmA_eq`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean:61`.)**
   *For every real $y$,*
   $$\mathrm{Gm}_A\bigl(\mathrm{arith}\,H, \ell, \mathrm{keptA}\,\Lambda\,H, (3\,\Lambda.o + 1)^{-1}, y\bigr) = \Lambda.\mathrm{Gm}(y).$$
   [Lean, read]
2. **(`UpperTheory.Comparison₂.sigA_le`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean:38`.)**
   $$\mathrm{Sig}_A\bigl(\mathrm{arith}\,H, \ell, \varphi.A_0, \mathrm{keptA}\,\Lambda\,H, x\bigr)
   \le 4\,\Lambda.o\,x^{1/2 + \varepsilon}.$$
   [Lean, read]

*Proof.*

1. By `EAtH.kept`, every $p \in \Lambda.\mathrm{KEPT}$ arises as the primitive character of a unique
   $\theta \in \varphi.Xp$ (`prim_inj`, `GmAEq.lean:68`), corresponding under `chr_bij` to a unique
   $\psi \in \mathrm{keptA}(\Lambda, H) \subseteq \Psi_A(\varphi.A_0)$ with $\theta(\mathrm{iod}) = +1$.
   Why does each $p \in \Lambda.\mathrm{KEPT}$ appear once rather than twice in $\mathrm{keptA}$
   (at $\theta$ versus $\theta \cdot \mathrm{ps}_C$, where $\mathrm{ps}_C$ is the $(\frac{\cdot}{q})$
   sign character)? In `keptA` (`CoreAtH.lean:24`) and `HostRaw.Kept` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:127`), a
   character $\theta$ is in `Kept` if and only if $\theta \in \varphi.Xp$ **and** its primitive
   character lies in $\Lambda.\mathrm{KEPT}$. Since $q = H.q$ is coprime to every conductor in
   $\Lambda.\mathrm{KEPT}$ ($\gcd(\psi.N, qd) = 1$), multiplying by $(\frac{\cdot}{q})$ multiplies
   the conductor by $q$, throwing $\theta \cdot \mathrm{ps}_C$ **out** of $\Lambda.\mathrm{KEPT}$
   (`gmA_eq_triv`, `GmAEq.lean:16–59`). Moreover, for $\psi \in \mathrm{keptA}$:
   - $\psi$ is trivial on $\{0\} \times \varphi.A$ if and only if $\theta = 1$ (since $\theta \cdot \mathrm{ps}_C$
     is ramified at $q$, hence not in $\Lambda.\mathrm{KEPT}$), which corresponds to $p = \mathrm{PChar.one}$,
     receiving weight $\mathrm{wt}_A = 1 = \Lambda.\mathrm{wt}(\mathrm{PChar.one})$;
   - for $p \in \Lambda.\mathrm{Nt}$ ($p \neq \mathrm{PChar.one}$), $\psi$ is nontrivial on
     $\{0\} \times \varphi.A$, receiving weight $\mathrm{wt}_A = (3\,\Lambda.o + 1)^{-1} = \Lambda.\mathrm{wt}(p)$!
   And by `prim_read` (`PrimRead.lean:51`), $\mathrm{GPsi}(\psi, y) = \mathrm{An.gChi}(p.\chi, y)$,
   so $\mathrm{Gm}_A(y) = \Lambda.\mathrm{Gm}(y)$ term by term!
2. Every $\psi \in \Psi_A(\varphi.A_0) \setminus \mathrm{keptA}(\Lambda, H)$ maps under `chr` to
   `H.Bounded Λ.KEPT` (`chr_bounded`, `SigALe.lean:18`: if $\theta(\mathrm{iod}) = +1$ then
   $\theta \in X_p \setminus \mathrm{Kept}$, and if $\theta(\mathrm{iod}) = -1$ then $\theta \in X_m$).
   By `prim_read` and `EAtH.bdG`, $\lVert \mathrm{GPsi}(\psi, x) \rVert \le x^{1/2 + \varepsilon}$
   for every such $\psi$. Since $\lvert \Psi_A(\varphi.A_0) \setminus \mathrm{keptA} \rvert \le \lvert \Psi_A(\varphi.A_0) \rvert = \lvert E_0 \rvert \cdot [\varphi.A : \varphi.A_0] = 4\,\varphi.o = 4\,\Lambda.o$
   (`card_PsiA` and `EAtH.o_eq`), summing over $\psi$ gives $\mathrm{Sig}_A(x) \le 4\,\Lambda.o\,x^{1/2 + \varepsilon}$. $\square$

**Theorem 5.5 (The square-root Chebyshev bound from host and chain inputs: `core_gm`).** *Let
$\Lambda$ be a `Level`, let $e_D, e_L, K, c_{HH}, e_K, C \in \mathbb R$, and let $\varepsilon > 0$.
There exists $x_1 \in \mathbb R$ such that for every $x \ge x_1$, every frame $\varphi$, every host
`H : HostAx φ`, and every $TT \subseteq \varphi.A$,*
$$\mathrm{EAtH}\,\Lambda\,H.\mathrm{toHostRaw}\,TT\,x\,\varepsilon\,C
\ \land\ \mathrm{CoreAtH}\,H.\mathrm{toHostRaw}\,TT\,e_D\,e_L\,K\,c_{HH}\,e_K\,\varepsilon\,x
\implies \Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}.$$
*(Lean: `UpperTheory.Comparison₂.core_gm`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12`,
combining `Deduction.ch_top` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean:37`),
`Deduction.ch_core` (`…/LandauTheorems/ChCore.lean:343`), `charsA` (`…/PrimitiveCosets/charsA.lean:80`), `gmA_eq`, and `sigA_le`.)* [Lean, read]

*Proof.* Watch every single multiple of $\varepsilon$ in the exponent $(e_D + e_L + 7)\varepsilon$
(`CoreGm.lean:16–74`):

1. **Unpack the chain gap (`ch_top`, `ChTop.lean:37`, + `e_D + e_L + 3`):** Given `CoreAtH` at
   $x \ge x_1$, `each_unit_bound_statement` (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`, unpacked by `ch_top`) and
   surjectivity of $\mathrm{tr} : U_0 \twoheadrightarrow \varphi.A_0$ give, for every $u_0 \in \varphi.A_0$,
   $$\mathrm{gap}_A(u_0) := \sum_{t \in TT} \sum_{j=0}^{m-1}
   \bigl(\mathrm{ASK}(a_t, t, w_{u_0, j}) - \Re\,\mathrm{MAIN}(\ell, a_t, w_{u_0, j})\bigr)
   \le x^{(e_D + e_L + 3)\varepsilon}\,\mathcal E_{\mathrm{win}},$$
   since `CErr Cc = Cc.eDiv + Cc.eLoss + 3 ≤ e_D + e_L + 3` (`CoreGm.lean:51–54`, with $e_D + e_L \ge 0$).
2. **Apply finite Fourier projection and the size lemma (`ch_core`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:343`, adding $+3\varepsilon$):**
   By Theorem 5.1 (`ch_balance`), $\mathrm{ASK} - \Re\,\mathrm{MAIN} = \Re\,\mathrm{De}$ at every
   $(t, j, u_0)$. Averaging $u_0 \in \varphi.A_0$, smoothing thick/thin weights, and summing
   $t \in TT$ via Lemma 5.2 (`charsA`, `charsA.lean:80`, supplies `CharsA` with $c_{\mathrm{top}} = (3\Lambda.o + 1)^{-1}$,
   $\lvert \Psi_A \rvert \le 4\Lambda.o$, and $\lvert \ell(\psi) \rvert \le C\log x$ from `EAtH.bdL`)
   yields the core Fourier inequality of Proposition 5.3 for
   $$G_x := \mathrm{Gm}_A(x) - \mathrm{Sig}_A(x)$$
   with exponent parameter $C_{\mathrm{chain}} := e_D + e_L + 3$ (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:283–442`). Applying
   Proposition 5.3 (`proposition_size_bound`) gives
   $$\mathrm{Gm}_A(x) - \mathrm{Sig}_A(x) \le x^{1/2 + (C_{\mathrm{chain}} + 3)\varepsilon}
   = x^{1/2 + (e_D + e_L + 6)\varepsilon}.$$
3. **Absorb the parasitic characters (`gmA_eq`, `sigA_le`, adding the final $+1\varepsilon$):**
   Substitute $\mathrm{Gm}_A(x) = \Lambda.\mathrm{Gm}(x)$ (Lemma 5.4(1)) and
   $\mathrm{Sig}_A(x) \le 4\,\Lambda.o\,x^{1/2 + \varepsilon}$ (Lemma 5.4(2)). Since $e_D + e_L \ge 0$
   and $x \ge 1$, we have $x^{1/2 + \varepsilon} \le x^{1/2 + (e_D + e_L + 6)\varepsilon}$. Choosing
   $x_1$ large enough that
   $$1 + 4\,\Lambda.o \le x^\varepsilon \qquad \forall x \ge x_1$$
   (`hx₃`, `CoreGm.lean:24–25`), we conclude (`CoreGm.lean:61–74`):
   $$\begin{aligned}
   \Lambda.\mathrm{Gm}(x)
   &\le x^{1/2 + (e_D + e_L + 6)\varepsilon} + 4\,\Lambda.o\,x^{1/2 + \varepsilon} \\
   &\le (1 + 4\,\Lambda.o)\,x^{1/2 + (e_D + e_L + 6)\varepsilon} \\
   &\le x^\varepsilon \cdot x^{1/2 + (e_D + e_L + 6)\varepsilon}
   = x^{1/2 + (e_D + e_L + 7)\varepsilon}. \quad \square
   \end{aligned}$$

### 5.4.5 Closing Part I: `level_gm_le_on_family_scales`

Finally, two short glue files (`WindowInequalityOfArtinInputs.lean` and `LevelGmLeOnFamilyScales.lean`,
75 lines combined, read in full) package `core_gm` into the exact `ChebyshevInequalityOnWindows`
predicate invoked by `zeroFreeAll_of_topG` in Chapter 3 (Section 3.4.5, Theorem 3.7)!

**Corollary 5.6 (Window Chebyshev inequality on family scales, closing Part I).** *For every
character level $\Lambda$, `level_gm_le_on_family_scales Λ` holds: given $\varepsilon > 0$, a
chain family `Fm : FamP eps` whose uniform constant bounds are `(eD, eL, K, cHH, eK, CL)`, there
exists $X_0$ such that at every scale $x \ge X_0$ where both `ChainTied Fm eD eL K cHH eK CL x` and
a family index $i_0$ satisfying `EAtH Λ (Fm.D x i0).host.toHostRaw (Fm.D x i0).host.TT x eps C`
exist, we have*
$$\Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}.$$
*Combining Corollary 5.6 (`level_gm_le_on_family_scales`), Theorem 4.9 (`supplyChi`), Theorem 3.6
(`formB`), Theorem 3.7 (`zeroFreeAll_of_topG`), Proposition 2.2 (`imprimitive`), and Theorems 2.6–2.7
reduces all five theorems of `src/Main.lean` to the three arithmetic inputs `TopG`, `VWin`, and
`PairEx` — and since `PairEx` was already proved in Theorem 4.7(2), **solely to `TopG` and `VWin`**!*
*(Lean: `UpperTheory.Comparison₂.windowInequality_of_artinInputs`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean:17`;
`tiedCore_of_chainTied` and `level_gm_le_on_family_scales`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean:13,28`.)* [Lean, read]

*Proof.* `tiedCore_of_chainTied` (`LevelGmLeOnFamilyScales.lean:13–26`) unpacks the existential
tuple of `ChainTied Fm eD eL K cHH eK CL x` (`TieGlobal.lean:97` [Lean]), verifies that the sample
set $TT$ coincides with `(Fm.D x i0).host.TT` via injectivity of `Frame.A.val`, checks that every
digit shift lands inside the cyclic subgroup $\varphi.A_0$ (`Frame.digit_mem_cyclic_subgroup`), and
assembles `FamCoreConstantBounds`, which evaluates directly to `CoreAtH` at index $i_0$. Applying
Theorem 5.5 (`core_gm`) at index $i_0$ gives $\Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}$
(`WindowInequalityOfArtinInputs.lean:17–25`). $\square$

---

## 5.5 Remarks

### 5.5.1 Accounting for every $\varepsilon$ in $1/2 + (e_D + e_L + 7)\varepsilon$

One virtue of reading `CoreGm.lean`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean`, `LipschitzWeightAndMinimum.lean`, and
`ErrorFormsWeakWindowsFalse.lean` line by line is that the coefficient $e_D + e_L + 7$ is no longer
a mysterious constant — every single $+1$ in $+7$ has an explicit origin [Lean, read]:

| Piece of $(e_D + e_L + 7)\varepsilon$ | Lean location | Where it comes from |
|---|---|---|
| $(e_D + e_L + 3)\varepsilon$ | `ErrorFormsWeakWindowsFalse.lean:19`, `CoreGm.lean:51` | `CErr Cc = eDiv + eLoss + 3`: chain divisibility exponent $e_{\mathrm{Div}} \le e_D$, word-loss exponent $e_{\mathrm{Loss}} \le e_L$, plus $+3\varepsilon$ slack converting `SizeData₂` clauses into `ErrWindows`. |
| $+1\,\varepsilon$ | `LipschitzWeightAndMinimum.lean:556` | Dividing by the thick-place density $\delta_2 / 2 \ge \frac{1}{2} x^{-\varepsilon}$. |
| $+2\,\varepsilon$ ($\frac{13}{8} + \frac{3}{8}$) | `LipschitzWeightAndMinimum.lean:53,585`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean:130` | Term `SZ.T3` gives $x^{1/2 + 13\varepsilon/8}$ (from $n/n_T \le 2x^{\varepsilon/8}$, $m \le x^{1/2+\varepsilon/2}$, and $x^\varepsilon$ in $B_0$), plus $26 \le x^{3\varepsilon/8}$. |
| $+1\,\varepsilon$ | `CoreGm.lean:25,65` | Absorbing the parasitic-character prefactor $1 + 4\,\Lambda.o \le x^\varepsilon$ from `sigA_le`. |

Notice again why the exact numbers $3$, $1$, $2$, $1$ do not matter once they are independent of
$\varepsilon$: in Chapter 3 (`zeroFreeOn_of_tiedWin`, Theorem 3.7), for fixed $(e_D, e_L)$ one sets
$\varepsilon := \frac{\delta}{2(e_D + e_L + 7)}$ and lets $\delta \to 0^+$, pushing
$\frac{1}{2} + (e_D + e_L + 7)\varepsilon = \frac{1}{2} + \frac{\delta}{2}$ arbitrarily close to
$\frac{1}{2}$! What *is* essential is that $(e_D, e_L)$ are **uniform across all window scales $x$**
for a given level $\Lambda$ (`TopG`, Chapter 7).

### 5.5.2 Why all the arithmetic difficulty lives inside `CoreAtH` (preview of Part II)

Pause at the end of Part I to take stock of what we have and have not seen [Expository]. Every step
proved in Chapters 1–5 is completely transparent classical mathematics:

- functional equations and Euler factors (Chapters 1–2);
- Laplace transforms and Landau's positivity lemma on windows (Chapter 3);
- large-sieve zero density, $L^2$ Jacobi sums, and Siegel–Walfisz on auxiliary primes (Chapter 4);
- finite abelian Fourier orthogonality and $x/m + m$ balancing (Chapter 5).

Why, then, does RH not fall to a ten-page classical paper? Because **producing an object inhabiting
`CoreAtH` (`SizeData₂` at chain length $m \asymp \sqrt{x}$ with $B_0 \le 2 n m b x^\varepsilon$ and
$N_c \le n_{T_2} k b x^{2\varepsilon}/n^2$) is extraordinarily hard**! Look at what Part II
(Chapters 6–11) must construct to inhabit `TopG` and `VWin` (`notes/proof-map.md`, nodes `P7`–`P12`,
`P17`):

1. **Why `ASK` appears on the left of a slope inequality (Chapters 6–9, `P7`–`P10`, `P17`):**
   Building $m \approx \sqrt{x}$ iterated theta lifts between definite unitary groups over $E/F$ so
   that (a) at primes inert in $K = \mathbb Q(\sqrt{-d})$, supersingular/local theta kernels vanish
   to high $p$-adic order (`Conclusion1`, Chapter 8), supplying `ASK`; (b) Chowla–Selberg periods
   and Rallis inner-product formulas supply `MAIN` and near-orthogonality of chain words (`LinkG`,
   `LinkS`, Chapter 9); and (c) Bost's Arakelov slope inequality (`SlopeIneq`, Chapter 9) turns
   local $p$-adic divisibility plus archimedean norm bounds into a global numerical inequality!
2. **Why the Selmer/congruence budget $B_0$ does not blow up (Chapters 10–11, `P11`–`P12`):**
   Each lift can lose divisibility through congruences measured by a Fitting ideal / congruence
   module (`CutCoreUnit.main`, Chapter 10), bounded by Bloch–Kato Selmer and Tate–Shafarevich
   lengths $\sum_{\ell} \log \ell \sum_{e < R.t} \operatorname{len}_{\mathbb Z_\ell}Ш^1(G_{E,S_\ell}, \mathbb Q_\ell/\mathbb Z_\ell(-e))$.
   Keeping $B_0$ at $O(n m b x^\varepsilon)$ requires bounding that $Ш^1$ sum by
   $\sqrt{b} = \exp(x^\varepsilon / 2)$ across windows — which is `VWin` (`P12`, Chapter 11, 90% of
   the entire archive by import weight!).

Separating `core_gm` cleanly from `TopG` and `VWin` means that **Part I is now 100% closed at `R3`**
(modulo the classical analytic sub-packages marked `[Lean]` in Chapter 4), and Part II can focus
single-mindedly on the arithmetic engine.

### 5.5.3 Note on unused parallel variants in `SizeWindowBrackets/`

While reading `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean`, `src/Formalism/SizeWindowBrackets/SChain.lean`, `GrowthBoundGivesRiemannHypothesis.lean`, and
`ErrorFormsWeakWindowsFalse.lean` (`R3`), we observed roughly twenty standalone "model" or
"reduced-hypothesis" propositions (such as `GrowthBoundGivesRiemannHypothesis`,
`ChainGivesRiemannHypothesis`, and `exists_data_completion`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean:306`) that record
self-contained size-layer blueprints [Lean, read]. On the actual `src/Main.lean` call path, only the
definitions `SizeData₂`, `CostWindows`, `RestSize`, `errorBracketSizeWindows`, `CErr`, `KBig`, and
the theorems `each_unit_bound_statement`, `errX5at_le`, `large_x_eventually`, `le_rpow_26`, and
`proposition_size_bound` (via `ch_top` and `ch_core`) are invoked [Lean, read] (consistent with the
declaration-reachability counts reported by LUMI and Dixit [Community]). Notice one telling file name: `ErrorFormsWeakWindowsFalse.lean` (containing only `def` declarations
and zero theorems; `:60` defines `ErrorFormsWeakWindowsFalse : Prop` with `ErrWindowsWeak`, `:47`,
where `etaBar ≤ 1 ∧ eBar ≤ 1` replaces the decaying trace condition of `ErrWindows`, `:43`), fossil
evidence of why exponential near-orthogonality decay in `LinkS` (Chapter 9) is indispensable
[Lean, read].

### 5.5.4 Masullo's counterpart

Masullo's draft has **no counterpart** to `core_gm`, chain lengths $m \approx \sqrt{x}$, or
Chebyshev-type prime-sum bounds [Expository]. Instead, in **Chapter 1, Section 1.2.1 ("Orbital
Schauder bases and the Fundamental Divisor Exact Sequence", pp. 12–15)**, the number **$1/2$** is
built directly into the functional-analytic normalization on **page 13** [Paper; Masullo pp. 12–15]:

- For each unitary character $\chi\rvert_{C_F^1}$ of the norm-$1$ idele class group $C_F^1$, Masullo
  introduces on page 13 the "Fundamental Divisor Exact Sequence"
  $$0 \longrightarrow \lvert \cdot \rvert_F^{1/2}\,H_{0,\mathrm{cont}}\bigl(\chi\rvert_{C_F^1}, \mathcal S_0(\mathbb A_F)\bigr)
  \longrightarrow \mathcal S\mathcal E(C_F)\bigl(\chi\rvert_{C_F^1}\bigr)
  \longrightarrow \mathcal H_F\bigl(\chi\rvert_{C_F^1}\bigr) \longrightarrow 0$$
  [Paper; Masullo p. 13].
- Because the left-hand kernel carries the multiplicative factor $\lvert \cdot \rvert_F^{1/2}$ (where
  $\lvert \cdot \rvert_F : C_F \to \mathbb R_{>0}$ is the global idele norm), applying the global
  Mellin transform shifts the complex variable by $+1/2$, sending the first term isomorphically onto
  multiples of **$L(s + 1/2, \chi)$** so that a zero $\rho$ of $L(w, \chi)$ corresponds to spectral
  parameter $s = \rho - 1/2$ ($\Re s = 0 \iff \Re \rho = 1/2$, pp. 13–15; compare eq. (B.4.4.16) on
  p. 623 and eq. (B.4.4.20) on p. 625) [Paper; Masullo pp. 13–15, 623, 625].

Put simply: in Masullo's framework, $1/2$ is put in at the beginning as the unitary $L^2$-scaling
exponent $\lvert g \rvert_F^{1/2}$ of Tate–Weil harmonic analysis, and the burden is to prove a
spectral-equals-geometric trace identity on strips around $\Re s = 0$; in the Lean archive, $1/2$ is
*not* put into $G_\chi(x)$ at all — it emerges at the end of `core_gm` as $\min_m (x/m + m) \asymp x^{1/2}$!

---

## 5.6 Lean counterpart for this chapter

Every Lean declaration in the table below (except the upstream Part II chain predicate `ChainTied`
and family structure `FamP` cited at the boundary of `tiedCore_of_chainTied`, which belong to
Chapter 7 and are tagged `[Lean]`) has been read in full, proof body included (`R3` / `[Lean, read]`).

### 5.6.1 Finite Fourier balance, chain size bounds, and `core_gm` (node P6)

| Declaration | File:line | Mathematical content / role in Section 5.4 | Tag |
|---|---|---|---|
| `sg`, `sgc0`, `partner`, `chC`, `ArithData`, `primVal`, `GPsi`, `IsInert`, `askP`, `askD`, `ASK`, `MAIN`, `De` | `src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:15,17,19,21,38,65,68,72,75,79,84,89,93` | Definition 5.1: group $E_0 \times H$, colour subset $\Phi$, partner bijection $\Phi^c \to \Phi$, inert prime sum `ASK`, `MAIN`, and character sum `De`. | [Lean, read] |
| `Deduction.CH.HostFactsS`, `PsiA`, `wtA`, `GmA`, `SigA`, `SizesA`, `gapA`, `CharsA`, `IdentU`, `BNBoundsU`, `ReadsKept` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean:14,26,30,34,39,42,50,56,67,74,81` | Definitions 5.1–5.3: splitting/inertia axioms on $S_0$, subgroup dual $\Psi_A(A_0)$, projected signal `GmA`, parasitic sum `SigA`, and chain interfaces. | [Lean, read] |
| `Deduction.CH.ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime`, `lunram`, `lsplit`, `ld`, `askExp`, `ch_balance` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean:18,55,77,99,122,200` | Theorem 5.1: exact finite Fourier identity $\mathrm{ASK} - \mathrm{MAIN} = \mathrm{De}$; split primes in $S_0$ cancel identically. | [Lean, read] |
| `Deduction.ch_top_main_eq`, `Deduction.ch_top` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean:11,37` | Theorem 5.5 (Step 1): unpacks `each_unit_bound_statement` and `errX5at_le` to bound $\mathrm{gap}_A(\mathrm{tr}\,v) \le x^{\mathrm{CErr}(C)\varepsilon}\,\mathcal E_{\mathrm{win}}$. | [Lean, read] |
| `each_unit_bound_statement` | `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175` | Converts `SizeData₂` weighted-mean slope/divisibility clauses into a per-unit bound on `ASK - Re MAIN`. | [Lean, read] |
| `CErr`, `KBig`, `ErrWindows`, `LargeX`, `errorBracketSizeWindows` | `src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:19,21,43,52,133` | Definition 5.3(2): error exponent $e_{\mathrm{Div}} + e_{\mathrm{Loss}} + 3$ and the four-term chain error bracket $\mathcal E_{\mathrm{win}}$. | [Lean, read] |
| `SizeData₂`, `CostWindows`, `RestSize` | `src/Formalism/SizeWindowBrackets/SChain.lean:17,50,53` | Definition 5.3(2): the $11$-clause chain datum (opened in Chapter 7) and thick/thin cost inequalities. | [Lean, read] |
| `SZ.T1`, `SZ.T2`, `SZ.T3`, `SZ.T4`, `proposition_finite_group`, `proposition_size_bound`, `lipschitz_weight_all` | `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:31,41,53,77,373,507,957` | Proposition 5.3: bounds the four normalized chain error terms (`x/m`, `xm/k`, `m x^{9ε/8}`, `(k/n^2) x^{17ε/8}`) to prove $G_x \le x^{1/2+(C+3)\varepsilon}$. | [Lean, read] |
| `le_rpow_26`, `errX5at_le` | `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean:130,613` | Eventual bound $26 \le x^{3\varepsilon/8}$ and conversion of `ErrText` to `x^{CErr*ε} * errorBracketSizeWindows`. | [Lean, read] |
| `Deduction.sum_A`, `sum_Th`, `th_le`, `move`, `one_char`, `core`, `Deduction.ch_core` | `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:28,56,75,154,202,283,343` | Lemma 5.2 and Theorem 5.5 (Step 2): $A_0$-averaging, thick Lipschitz + thin zero-free smoothing, and deduction of $\mathrm{Gm}_A(x) - \mathrm{Sig}_A(x) \le x^{1/2+(C+3)\varepsilon}$. | [Lean, read] |
| `Formalism.HC.Frame.lam`, `Frame.Shares`, `Formalism.HC.EAtH` | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:135,139,144` | Definition 5.3(1): the $(4, 3)/(3o+1)$ coset weights, coset equidistribution `Shares`, and the six-field host bundle `EAtH`. | [Lean, read] |
| `UpperTheory.Comparison₂.chr`, `HostAddCharCompatible`, `keptA`, `koOf`, `CoreAtH` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean:14,18,24,27,29` | Definition 5.3(2): character bridge $E_0 \times \varphi.A \leftrightarrow \varphi.\mathrm{GG}$, `keptA`, and the chain bundle `CoreAtH`. | [Lean, read] |
| `UpperTheory.Comparison₂.hostFactsS` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/hostFactsS.lean:127` | Verifies `HostFactsS` on $S_0 = \{q\} \cup \mathrm{small}$ for any `HostAx φ`. | [Lean, read] |
| `UpperTheory.Comparison₂.prim_read` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/PrimRead.lean:48` | Identifies $\ell(\psi) = \frac{L'}{L}(1, \chi_\psi^*)$ ($\psi \neq 0$) and $\mathrm{GPsi}(\psi, y) = \mathrm{An.gChi}(\chi_\psi^*, y)$. | [Lean, read] |
| `UpperTheory.Comparison₂.tops_sum` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/TopsSum.lean:75` | Lemma 5.2(3): $(4, 3)/(3o+1)$ coset equidistribution implies $\sum_{t \in TT} \psi(0, t) = (3o+1)^{-1}\lvert TT \rvert + O(o\delta\lvert TT \rvert)$. | [Lean, read] |
| `UpperTheory.Comparison₂.charsA` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/charsA.lean:80` | Assembles `CharsA` from `EAtH`, `tops_sum`, and `prim_read`. | [Lean, read] |
| `UpperTheory.Comparison₂.gmA_eq` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean:61` | Lemma 5.4(1): exact equality $\mathrm{Gm}_A(y) = \Lambda.\mathrm{Gm}(y)$. | [Lean, read] |
| `UpperTheory.Comparison₂.sigA_le` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean:38` | Lemma 5.4(2): bounds $\mathrm{Sig}_A(x) \le 4\,\Lambda.o\,x^{1/2+\varepsilon}$ using `EAtH.bdG`. | [Lean, read] |
| `UpperTheory.Comparison₂.core_gm` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:12` | Theorem 5.5: proves $\Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}$ from `EAtH` and `CoreAtH`. | [Lean, read] |
| `FamCoreConstantBounds`, `windowInequality_of_artinInputs` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean:11,17` | Corollary 5.6: lifts `core_gm` to `ChebyshevInequalityOnWindows` for any abstract family. | [Lean, read] |
| `tiedCore_of_chainTied`, `level_gm_le_on_family_scales` | `src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean:13,28` | Corollary 5.6: unpacks `ChainTied` into `CoreAtH` and proves `level_gm_le_on_family_scales Λ`, closing Part I. | [Lean, read] |
| `Formalism.MainNotions.FamP`, `Formalism.MainNotions.ChainTied` | `src/Formalism/SharpRestriction/ParConsts.lean:31`; `src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97` | Upstream Part II family type and tied-chain proposition (proved in Chapter 7 from `TopG`). | [Lean] |

**Summary of the chapter (and of Part I).** On the abelian Galois group $E_0 \times \varphi.A$ of a
CM host field $E$, exact finite Fourier orthogonality equates the inert-prime Riesz sum minus its
main term (`ASK - MAIN`) to a character sum `De` in which all split primes — including $2$, $q$, and
every prime dividing $\psi.N$ — vanish identically (Theorem 5.1) [Lean, read]. Averaging over the
$2$-power tower subgroup $A_0$ kills all characters outside the $4\,\Lambda.o$-element dual
$\Psi_A(A_0)$, and summing over $TT$ with coset weights $(4, 3)/(3\Lambda.o + 1)$ gives positive
weight $1$ to $\zeta$ and $(3\Lambda.o + 1)^{-1}$ to every nontrivial target character in $\Lambda$
(Lemmas 5.2 and 5.4) [Lean, read]. Dividing the four-term chain error bracket by the $m$-lift signal
prefactor balances $x/m$ against $m\,x^{O(\varepsilon)}$ at chain length
$x^{1/2-\varepsilon} \le m \le x^{1/2+\varepsilon/2}$ (Proposition 5.3), and absorbing the
$4\,\Lambda.o$ parasitic twists bounded in Chapter 4 yields
$\Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}$ (`core_gm`, Theorem 5.5) [Lean, read].
Part I is now complete: the entire Riemann Hypothesis and Dirichlet GRH of `src/Main.lean` have been
reduced, by fully checked classical arguments, to constructing the theta-lift chains (`TopG`) and
proving the Tate–Shafarevich window bound (`VWin`) — the subject of **Part II**.
