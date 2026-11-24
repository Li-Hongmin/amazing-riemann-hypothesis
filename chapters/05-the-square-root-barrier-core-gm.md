# Chapter 5. The square-root barrier as bookkeeping: `core_gm`

With Chapters 2, 3, and 4 in hand, only one link of **Part I: The analytic endgame** remains open.
In Chapter 3 (`zeroFreeAll_of_topG`, Theorem 3.7) we saw that `ZeroFreeAll` follows from three
inputs for each primitive character $\psi$ [Lean, read]:

1. the Landau-window criterion `formB` (proved in full in Chapter 3, Theorem 3.6);
2. the window host supply `supplyChi` on $[Z, Z^{3/2}]$, delivering at each window point $x$ a CM
   host field `H : HostAx φ` and coset sample `TT` satisfying `EAtH (Level.cyc ψ) H.toHostRaw TT x eps 4`
   together with the Tate–Shafarevich bound `VVle H.E R.t (sqrt s.b)` (proved in Chapter 4, Theorem 4.9,
   assuming `VWin`); and
3. the **window Chebyshev upper bound** `level_gm_le_on_family_scales` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean:28`),
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
   Watch the mechanism of the colour subgroup $\Phi \subset E_0 \times H$ (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean:200`)!
   Model $\operatorname{Gal}(E/\mathbb Q)$ additively as $E_0 \times H$, where
   $E_0 = \mathbb Z/2\mathbb Z \times \mathbb Z/2\mathbb Z$ tracks the two quadratic signs and
   $\Phi = \{g \in E_0 \times H : g_{1,1} = 0\}$ (`InPhi g ↔ g.1.1 = 0`) tracks splitting in
   $K = \mathbb Q(\sqrt{-d})$. Every prime $p$ that **splits** in $K$ (including $2$, $q$, and
   every prime dividing $\psi.N$, by Lemma 4.1(2)!) has Frobenius in $\Phi$, whereas every prime
   **inert** in $K$ has Frobenius **outside $\Phi$**! When we expand $\mathbf{1}_{g = r\,\mathrm{frob}(p)}$
   by characters $\psi \in \widehat{E_0 \times H}$ and sum over $g \notin \Phi$:
   - for **split** primes, $g - r\,\mathrm{frob}(p)$ never hits the inertia subgroup inside $\Phi$,
     so their character sum over $g \notin \Phi$ vanishes identically (`lsplit`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean:77`)!
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
   `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:135`), gives Fourier transform $+1$ on the trivial
   coset character ($\zeta$) and $+\frac{1}{3o + 1} > 0$ on **every** nontrivial character of $H/A_0$
   (`tops_sum`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/TopsSum.lean:75`) — matching $\Lambda.\mathrm{Gm}(x)$ term for term (`gmA_eq`,
   `src/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean:61`)!
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
   $\mathrm{ch}_C = \psi_{1, 0, 0}$ (`src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:21`) takes value $+1$ on $\Phi$
   ($e_1 = 0$) and $-1$ on $\Phi^c$ ($e_1 = 1$). Therefore, summing $\overline{\psi_{\alpha,\beta,k}(g)}$
   over $g \in \Phi^c$ ($e_1 = 1$, $e_2 \in \{0,1\}$, $h \in \{0,1,2\}$) gives
   $$\frac{1}{6}\sum_{g \in \Phi^c} \overline{\psi_{\alpha,\beta,k}(g)}
   = (-1)^\alpha \Bigl(\frac{1 + (-1)^\beta}{2}\Bigr)\Bigl(\frac{1 + \omega^{-k} + \omega^{-2k}}{3}\Bigr)
   = \begin{cases}
   +1 & \text{if }(\alpha, \beta, k) = (0, 0, 0)\ \ (\psi = 0),\\
   -1 & \text{if }(\alpha, \beta, k) = (1, 0, 0)\ \ (\psi = \mathrm{ch}_C),\\
   0 & \text{for all } 10 \text{ other characters!}
   \end{cases}$$
   That two-line calculation is why `MAIN` (`src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:89`) has **only** two
   terms: the $\zeta(s)$ main term from $\psi = 0$ (with $+1$) and the $-\frac{L'}{L}(1, \chi_{-d})$
   counterterm from $\psi = \mathrm{ch}_C$ (with $-1$), while all $10$ remaining characters have
   their $s = 1$ counterterms embedded straight into $G_\psi$ with zero leftover!
2. **Summing over $t \in TT$ with the $(4, 3)/(3o + 1)$ coset law (`tops_sum`).** Suppose $TT$ has
   $10N$ elements distributed across $H = \mathbb Z/3\mathbb Z$ with $4N$ elements in $0 \bmod 3$,
   $3N$ elements in $1 \bmod 3$, and $3N$ elements in $2 \bmod 3$ — the exact ratios
   $\mathrm{lam}(0) = \frac{4}{10}$ and $\mathrm{lam}(1) = \mathrm{lam}(2) = \frac{3}{10}$ of
   `Frame.lam` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:135` at $o = 3$, $3o + 1 = 10$)! Compute
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
   receives the exact positive weight $(3o + 1)^{-1}$ of Chapter 3's `Level.Gm` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:36–38`)!

### 5.2.2 Toy optimization: $x/m + m$ at $1/2$ versus $x/m + m^2$ at $2/3$

Suppose an inequality of Stepanov/Arakelov type produces $m$ units of prime-sum signal $m \cdot G(x)$
against a fixed archimedean degree cost $x$ plus a congruence/Selmer error from the $m$ lifts
[Expository]:

- **Compounding per-lift cost (the $2/3$ trap):** Look at `errorBracketSizeWindows`
  (`src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:133`, `SZ.T3` at `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:53`): in the
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
(`partner_inPhi : g ∉ PhiSet H → partner t g ∈ PhiSet H`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:214`)
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
   for $\psi \neq 0$ (`HostAddCharCompatible`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean:18`), `GPsi D ell ψ y` (`:68`) equals
   `Gz y` when $\psi = 0$ and $\sum_{1 \le n \le \lfloor y \rfloor} \Lambda(n)\,\mathrm{primVal}(D,\psi,n)(y/n - 1) + y\,\ell(\psi) = \mathrm{An.gChi}\,\chi_\psi^\ast\,y$
   when $\psi \neq 0$ (`prim_read`, `:51`) [Lean, read]. Section 5.3.1.1 proves the coefficient identity
   and the finite-sum substitution.
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
   whenever $N < d$, `ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean:18`!);
   $$\mathrm{MAIN}(\ell, a, w) := a\Bigl(\log a - 1 - \gamma + \ell(\mathrm{ch}_C)
   - \frac{1}{\lvert\Phi\rvert}\sum_{\rho \in \Phi} \log w(\rho)\Bigr)
   = \frac{1}{\lvert\Phi\rvert}\sum_{\rho \in \Phi}
   \Bigl[a\log\Bigl(\frac{a}{w(\rho)}\Bigr) - (1 + \gamma)a + a\,\ell(\mathrm{ch}_C)\Bigr];$$
   $$\mathrm{De}(D, \ell, a, t, w) := \frac{1}{\lvert\Phi\rvert}\sum_{g \in \Phi^c}
   \sum_{\psi \in \widehat{E_0 \times H}} \overline{\psi(g)}\,w(\mathrm{partner}_t(g))\,
   \mathrm{GPsi}\Bigl(D, \ell, \psi, \frac{a}{w(\mathrm{partner}_t(g))}\Bigr).$$

### 5.3.1.1 Why inertia averaging recovers the primitive character

**Motivation.** A character pulled back from the host group to units modulo $N$ is
extended by zero at the nonunits. A prime dividing $N$ can be coprime to the conductor,
so the primitive character may have a nonzero value there. Inertia averaging
recovers that value and also accounts for the zero when the prime divides the conductor.

**Example [Expository].** At cyclotomic level $20$, write a unit by its residues
$((-1)^\epsilon,2^j)$ modulo $4$ and $5$. Send it to $g^{j+2\epsilon}$ in the
cyclic group $G=\langle g\rangle$ of order four. This is the Galois group of the
subfield of $\mathbb Q(\zeta_{20})$ fixed by the kernel of the map. At $p=2$,
the units equal to $1$ modulo $5$ have image $I_2=\{1,g^2\}$. The unit $17$,
equal to $1$ modulo $4$ and $2$ modulo $5$, gives the Frobenius lift $g$.
The other lift is $g^3$.

Put $\psi_j(g)=i^j$ for $j=0,1,2,3$, where $i^2=-1$. The two summands
at $2^a$ come from $g^a$ and $g^{a+2}$. The last column gives the primitive
values for the first four positive exponents.

| $j$ | $\psi_j(g^2)$ | Two summands at $2^a$ | Average | Values at $2,4,8,16$ |
|---|---|---|---|---|
| 0 | $1$ | $1,\ 1$ | $1$ | $1,1,1,1$ |
| 1 | $-1$ | $i^a,\ -i^a$ | $0$ | $0,0,0,0$ |
| 2 | $1$ | $(-1)^a,\ (-1)^a$ | $(-1)^a$ | $-1,1,-1,1$ |
| 3 | $-1$ | $(-i)^a,\ -(-i)^a$ | $0$ | $0,0,0,0$ |

For $j=2$, the pullback ignores the component modulo $4$ and sends $2$ modulo
$5$ to $-1$. Its conductor is $5$, so its value at $2$ modulo $20$ is zero
while the primitive value at $2$ modulo $5$ is $-1$. For odd $j$, the pullback
is nontrivial on both components. The component modulo $4$ requires the full
modulus $4$ since the units modulo $2$ are trivial, and the component modulo
$5$ requires $5$. Hence the conductor is $20$, and the primitive values at
all positive powers of $2$ are zero. For $j=0$ the conductor is $1$.

**Definitions.** In a finite abelian Galois extension $E/K$ of number fields,
fix a prime $\mathfrak P$ over a finite prime $\mathfrak p$. Its decomposition
group $D_{\mathfrak P}$ is the stabilizer of $\mathfrak P$. Reduction gives a
surjection from $D_{\mathfrak P}$ onto the residue-field Galois group, with
kernel the inertia group $I_{\mathfrak P}$. Arithmetic Frobenius is the
$\lvert k(\mathfrak p)\rvert$-power map on the residue field above
$\mathfrak p$. Its lifts form one coset of $I_{\mathfrak P}$. Changing the
prime above $\mathfrak p$ conjugates these data, which leaves them identical
in an abelian group. Write $I_p$ and $F_p$ for the inertia group and a lift
over a rational prime $p$ when $K=\mathbb Q$. Lean writes the host group
additively, so $F_p^a I_p$ becomes $a\,\mathrm{frob}(p)+I_p$.

**Orthogonality lemma [Lean, read].** For a one-dimensional complex character $\psi$ of a finite
abelian group $G$, a subgroup $I$, and $h\in G$, put
$$A_I(h)=\frac{1}{\lvert I\rvert}\sum_{u\in I}\psi(hu).$$
Then $A_I(h)=\psi(h)$ if $\psi$ is trivial on $I$, and $A_I(h)=0$ otherwise.
In particular $A_I(F^a)$ depends only on the coset $FI$ for $a\ge1$.

**Proof.** In the trivial case every term equals $\psi(h)$ and the denominator
is positive since $1\in I$. Otherwise choose $v\in I$ with $\psi(v)\ne1$.
The map $u\mapsto vu$ permutes $I$, with inverse multiplication by $v^{-1}$.
Thus $S=\sum_{u\in I}\psi(hu)$ also equals $\sum_{u\in I}\psi(hvu)=\psi(v)S$.
Since $1-\psi(v)\ne0$ in $\mathbb C$, we get $S=0$. For independence, if
$F'=Fv$ with $v\in I$, then $(F')^a=F^av^a$ by commutativity and $v^a\in I$.
Multiplication by $v^a$ permutes the summands in either branch.

**Primitive-value identity [Lean, read].** In the archive's cyclotomic model
let $U_N=(\mathbb Z/N\mathbb Z)^\times$ and $r:U_N\to G$ be the map to the
host group, with $N\ge1$. Define $\chi(u)=\psi(r(u))$ on units and extend by
zero modulo $N$. Write $c=\operatorname{cond}(\chi)$ and let $\chi^\ast$
be the inducing primitive character modulo $c$. For $n\ge1$,
$$\mathrm{primVal}(n)=\prod_{p^a\parallel n} A_{I_p}(F_p^a)=\chi^\ast(n).$$

**Proof.** Fix $p$, write $N=p^b M$ with $p\nmid M$, and set
$K_p=\ker(U_N\to U_M)$. The model defines $I_p=r(K_p)$ and $F_p=r(w_p)$,
where $w_p$ is congruent to $1$ modulo $p^b$ and to $p$ modulo $M$.
Both residues are units, so the Chinese remainder theorem gives a unique
$w_p$. Any unit congruent to $p$ modulo $M$ differs from $w_p$ by a factor
in $K_p$. The archive's host congruence theorems identify these images
with inertia and the arithmetic Frobenius coset [Lean].

Triviality on $I_p$ is equivalent to triviality of $\chi$ on $K_p$.
Reduction to $U_M$ is surjective by the Chinese remainder theorem. If $\chi$
is trivial on the kernel, it descends by assigning to each residue the value
at any lift. Conversely a descended character takes value $1$ on the kernel.
The conductor criterion for divisors of $N$ says that descent through $U_M$
is equivalent to $c\mid M$. Since $c\mid N$, this is equivalent to $p\nmid c$.

In the trivial-on-inertia branch, $c\mid M$ gives $w_p\equiv p\pmod c$.
On units modulo $N$, $\chi$ is the pullback of $\chi^\ast$ from modulo $c$.
By orthogonality,
$$A_{I_p}(F_p^a)=\psi(F_p)^a=\chi(w_p)^a=\chi^\ast(p)^a=\chi^\ast(p^a).$$
In the other branch, $p\mid c$. Then $p$ is a nonunit modulo $c$, so
$\chi^\ast(p)=0$ and $\chi^\ast(p^a)=0$ for $a\ge1$. The average also
vanishes by orthogonality. This proves equality factor by factor. The
factorization of $n>0$ and complete multiplicativity of $\chi^\ast$,
including at nonunits, give the product identity. At $n=1$ the empty
product is $1$.

**The finite sum [Lean, read].** In the host, take $N$ to be its cyclotomic level.
Then $r$ is `recH`, the Artin
map followed by the change of group coordinates `toE`. The host Dirichlet
character agrees with $\chi$ on units, which determines it everywhere.
The host record uses the inertia and Frobenius data of this same map $r$.
For $\psi\ne0$, applying `HostAddCharCompatible` to the primitive character
and the product identity gives
$\ell(\psi)=\mathrm{An.logDerivativeAtOne}(\chi^\ast)$, the logarithmic
derivative at $1$. Here $\psi=0$ denotes the trivial additive character
with constant value $1$. The host axioms supply surjectivity of the Artin map. Both sign coordinates
of `toE` are attained independently using $1,-1$, while the remaining
coordinate ranges over the whole cyclic factor, so $r$ is surjective. By induction
from the conductor, $\chi^\ast$ is trivial exactly when $\chi$ is trivial
on units, hence exactly when $\psi=0$.

Let $J_y=\{1,\ldots,\max(0,\lfloor y\rfloor)\}$, empty for $y<1$.
For $n\in J_y$, we have $0<n\le y$, so $\max(y/n-1,0)=y/n-1$.
When $\psi\ne0$, substitution gives
$$
\begin{aligned}
\mathrm{GPsi}(\psi,y)
 &=\sum_{n\in J_y}\Lambda(n)\,\mathrm{primVal}(n)(y/n-1)+y\ell(\psi)\\
 &=\sum_{n\in J_y}\Lambda(n)\,\chi^\ast(n)\max(y/n-1,0)
      +y\,\mathrm{An.logDerivativeAtOne}(\chi^\ast)\\
 &=\mathrm{An.gChi}(\chi^\ast,y).
\end{aligned}
$$
When $\psi=0$, both definitions choose the zeta branch. The same weight
equality identifies the finite sums, and both subtract
$y(\log y-1-\gamma)$, where $\gamma$ is Euler's constant.

**Reading note.** A prime can ramify in $E$ while the character is trivial on
its inertia subgroup, as the $j=2$ row illustrates. The zero criterion
involves the conductor of the individual character. The exponent $a$ acts on
the Frobenius lift before averaging over the full inertia group. In the
odd-$j$ rows, even $g^4=1$ leaves the two summands at $a=4$ equal to $1,-1$.

Locations below refer to the Alpöge–Claude archive, joined SHA-256
`9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.
[Archive record](../sources/SOURCES.md)

| Step in the text | Archive declaration and location | Tag |
|---|---|---|
| Average, product and finite sum | `cosetMean`, `primVal`, `GPsi`, `src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:61,65,68` | [Lean, read] |
| Cyclotomic model and CRT lift | `localUnits`, `IsFrobUnit`, `frobUnit`, `cftData`, `dirChar`, `PrimValPrimitive`, `src/Formalism/SizeWindowBrackets/GaloisToProductIsIso.lean:12,14,18,25,31,95` and `frobenius_unit_spec`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean:64` | [Lean, read] |
| Host inertia and Frobenius congruences | `inertia`, `frob_any`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean:191,261` | [Lean] |
| Orthogonality and conductor criterion | `cosetMean_of_trivial`, `cosetMean_of_nontrivial`, `trivial_on_inertia_iff`, `inertia_conductor`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean:155,167,129,145` | [Lean, read] |
| Two prime-power branches and the product identity | `cosetMean_eq_primitive`, `primitive_value_primitive`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean:209,233` | [Lean, read] |
| Host pullback, compatibility and finite sum | `recH`, `arith`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/RecH.lean:21,23` and `HostAddCharCompatible`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean:18` and `prim_read`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/PrimRead.lean:48` (value supplier at :56–61, finite sum at :84–97) | [Lean, read] |
| Host Artin surjectivity input | `HostDer.art_surj`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:87` | [Lean] |
| Riesz and zeta branches | `G`, `sumLamChi`, `gChi`, `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:14,18,23` and `Sz`, `Gz`, `src/Formalism/StatementOC.lean:11,13` | [Lean, read] |

### 5.3.1.2 Frobenius and inertia in the cyclotomic host

**Motivation.** The same host data serve two arguments in this chapter. The primitive-character identity in §5.3.1.1 reads the local coefficients. The Fourier balance uses a list of constraints on the inertia groups and Frobenius representatives. Both start with a unit group, and both carry its elements to the host Galois group. To see why these elements encode the arithmetic at $p$, we first compute the order of a cyclotomic root after reduction at $p$.

**Example.** Let $L=\mathbb Q(\zeta_8)$, with $\mathcal O_L=\mathbb Z[\zeta_8]$ and minimal polynomial $X^4+1$. Label the four automorphisms by $1,3,5,7$ modulo $8$, with $u$ acting by $\zeta_8\mapsto\zeta_8^u$. For $p=3$ the factorization is
$(X^2+X+2)(X^2-X+2)$. Each discriminant is $2$ in $\mathbb F_3$, a nonsquare. For $p=5$ the factorization is $(X^2+2)(X^2+3)$, and their roots would have to square to $3$ and $2$ respectively, both nonsquares. The two factors are distinct in each case, so there are two primes, each of residue degree two and ramification index one. Frobenius on the integral generator is the third power at $3$ and the fifth power at $5$. For $p=2$ the polynomial is $(X+1)^4$ modulo $2$. The quotient by $2$ has one maximal ideal, giving the unique prime $(2,\zeta_8-1)$ and residue field $\mathbb F_2$. Its ramification index is four. Thus the group calculation gives

| $p$ | Decomposition group | Inertia group | Residue degree |
|---|---|---|---|
| $3$ | $\{1,3\}$ | $\{1\}$ | $2$ |
| $5$ | $\{1,5\}$ | $\{1\}$ | $2$ |
| $2$ | $\{1,3,5,7\}$ | $\{1,3,5,7\}$ | $1$ |

For the odd primes the Frobenius elements have order two since $3^2\equiv5^2\equiv 1\pmod 8$. At $2$ every automorphism induces the identity on $\mathbb F_2$. The CRT convention below selects $1$ as a lift. The table illustrates the ambient cyclotomic calculation. The chapter's actual host has the extra $q,d$ data specified by the archive. [Expository]

**Definitions.** Write $N=p^a M$ with $p\nmid M$, $U_N=(\mathbb Z/N\mathbb Z)^\times$, and $\pi:U_N\to U_M$ for reduction, with $U_1$ trivial. For a prime $P$ of a Galois number field $E/\mathbb Q$ above $p$, its decomposition group $D_P$ stabilizes $P$. Its inertia $I_P$ consists of the automorphisms satisfying $\sigma x-x\in P$ for every $x\in\mathcal O_E$. An arithmetic Frobenius lift satisfies $\sigma x-x^p\in P$ for every such $x$. The latter condition implies stabilization since $\bar x^p=0$ exactly when $\bar x=0$. The induced Frobenius generates the cyclic residue-field Galois group $D_P/I_P$.

**Identification theorem.** Use the archive's `HostRaw φ` hypotheses. In particular $N=QS\,q\,d>0$, the host $E$ is Galois over $\mathbb Q$, and its specified embedding $\iota:E\hookrightarrow L=\mathbb Q(\zeta_N)$ comes with a primitive $N$th root and `art_spec`. Write $\gamma$ for the given group isomorphism `H.gal` and $A$ for `H.art`. The compatibility `art_spec` says that $\tau_u$ acting by the $u$th power on the chosen root restricts along $\iota$ to $\gamma^{-1}(A(u))$. For every prime $p$ and prime $P$ above $p$,
$\gamma(I_P)=A(\ker\pi)$, the images of all Frobenius lifts are $A(\pi^{-1}(p))$, and $\gamma(D_P)=A(\pi^{-1}(\langle p\bmod M\rangle))$. More precisely, the elements acting on the residue field by $x\mapsto x^{p^k}$ have images $A(\pi^{-1}(p^k))$ for $k\ge0$. The representative used in the chapter is $w$ with $w\equiv1\pmod{p^a}$ and $w\equiv p\pmod M$. [Lean, read]

**Proof.** First work in $L$ at a prime $Q$ above $p$, using the integral primitive root $z$ of `RootEqOfSubMem.lean`. The residue characteristic is $p$ by contraction to $(p)$, and $\lvert\mathbb Z/(Q\cap\mathbb Z)\rvert=p$. We will show that $\bar z$ has order exactly $M$.

For the prime-to-$p$ step, suppose $x,y$ are $m$th roots of unity in a domain with a prime ideal in whose quotient $m$ has nonzero image, and $x-y$ lies in that ideal. The identity $x^m-y^m=(x-y)\sum_{i=0}^{m-1}x^iy^{m-1-i}$ has zero left side. If $x\ne y$, the sum vanishes in the domain. Its reduction is $m\bar y^{m-1}$, which is nonzero because $m$ has nonzero image and $\bar y^m=1$. Therefore $x=y$. This is `root_eq_of_sub_mem`.

The reduction of $z^{Mc}$ is $1$ for every $c\ge0$. Indeed, $(\overline{z^{Mc}}-1)^{p^a}=\overline{z^{Nc}}-1=0$ in the residue field. Conversely, if $\bar z^b=\bar z^c$, raise both sides to $p^a$ and apply the previous lemma with $m=M$ to $(z^{p^a})^b$ and $(z^{p^a})^c$. They are equal in $L$. Since $z^{p^a}$ has order $M$, this is equivalent to $b\equiv c\pmod M$. For the reverse implication reduce the difference of the two exponents by writing the larger as the smaller plus a nonnegative multiple of $M$. This proves `zO_sub_mem_iff`.

The power description of $\tau_u$ follows by applying the inverse of the rational cyclotomic Galois equivalence to $u$. On the integral root it gives $\tau_u z=z^u$. The ring of integers is generated over $\mathbb Z$ by $z$, so two ring maps out of it agreeing on $z$ agree on all integral elements by closure under addition and multiplication. Comparing reduction after $\tau_u$ with reduction itself now identifies inertia with $\pi(u)=1$. Comparing reduction after $\tau_u$ with reduction followed by the $p$-power homomorphism gives Frobenius for every $u$ with $\pi(u)=p$. The comparison on $z$ also gives the converse in $L$. These are the generator comparisons in `tauN_inertia_iff` and `tauN_frob`.

For descent to $E$, choose $Q$ over $P$ by lying over. The compatibility on roots gives $\gamma(\sigma)=A(u)$ if and only if $\iota\sigma=\tau_u\iota$. In the forward direction substitute the specified Galois coordinate; in the reverse direction use injectivity of $\iota$ and the Galois coordinate isomorphism. Restriction of an inertia element preserves the congruence by contraction. For surjectivity on inertia, lift $\sigma\in I_P$ to $\tau_0\in\operatorname{Gal}(L/\mathbb Q)$ by normality. Then $\tau_0^{-1}Q$ lies above $P$. Choose $\rho\in\operatorname{Gal}(L/E)$ carrying $Q$ to $\tau_0^{-1}Q$. Thus $\tau_1=\tau_0\rho$ fixes $Q$ and still lifts $\sigma$. Its residue automorphism fixes the residue field at $P$. Lift that residue automorphism to $r$ in the relative decomposition group for $L/E$, using surjectivity of the decomposition-to-residue map. The element $\tau_1 r^{-1}$ then lifts $\sigma$ and acts trivially on the residue field at $Q$. Expressing this element as $\tau_u$ gives $\pi(u)=1$. Conversely any such $u$ restricts to inertia. This gives the two directions of `Der.inertia`.

For Frobenius, the quotient map on residue rings is injective in the direction from $P$ to $Q$. More explicitly, to descend the congruence, embed the integral elements of $E$, carry $\sigma x-x^p$ to $\tau_u\iota(x)-\iota(x)^p$, and contract $Q$ to $P$. In the source, `lift_lemma'` obtains that contraction from integrality of $\mathcal O_L$ over $\mathcal O_E$ and lying over, then uses transitivity of contraction to $\mathbb Z$. The cardinalities of both base residue rings are $p$. This proves `frob_of_modEq`. Reduction on units is surjective, so a unit $w$ above $p\bmod M$ exists. The CRT selects the stated $w$, uniquely, and $F=\gamma^{-1}(A(w))$ is a lift. The set of lifts is $I_P F$: comparing the congruences of $\sigma$ and $F$ at $F^{-1}x$ gives the inertia congruence for $\sigma F^{-1}$, and adding the two congruences at $Fx$ and $x$ gives the converse. If $\sigma F^{-1}$ is represented by $v$ over $1\bmod M$, then $\sigma$ is represented by $vw$ over $p\bmod M$. This proves `frob_any`.

Finally $F^k$ induces $x\mapsto x^{p^k}$ by induction, starting with the identity and composing with the $p$-power map. Any automorphism fixing $P$ induces a power of that map by the cyclic Galois theory of finite fields. Consequently it is $\rho F^k$ with $\rho\in I_P$. If $\rho$ is represented by $v$, then $vw^k$ represents $\rho F^k$ and reduces to $p^k\bmod M$. Conversely, for a representative $u$ over $p^k\bmod M$, $u(w^k)^{-1}$ reduces to $1$ and represents $\sigma(F^k)^{-1}$, which is inertia. Multiplying back by $F^k$ yields the claimed element of $D_P$. This is `Der.decomp` with its `Decomp.stab_eq_inertia_mul` supplier. In particular the residue degree of the host is the order of $A(w)$ modulo $A(\ker\pi)$.

**Remarks on the two moduli and the host group.** At $p\nmid N$ we have $M=N$, inertia is trivial, and $w=p\bmod N$. At $p\mid N$ the integer $p$ is a nonunit modulo $N$. Its class modulo $M$ is a unit, so the arithmetic is expressed by a coset of $\ker\pi$ with representative $w$. The image of $\ker\pi$ in the host can be smaller than the ambient cyclotomic inertia. In particular divisibility of the ambient modulus alone does not decide ramification in a quotient. For a character of the host, its Dirichlet conductor is a divisor $c$ of $N$ determined by that character. The test $p\nmid c$ concerns the value of the primitive character, with the proof given in §5.3.1.1. The two quotients at this step are the cyclotomic quotient by $\ker A$ and the local decomposition quotient by inertia.

**The exact use in P6.** The arithmetic producer is `Formalism.HC.Der`: `hostCore` assigns `frob_any`, `inertia`, and `decomp`; `HostRaw.der` carries them into `HostDer`; `HostAx.ofRaw` packages the result. The `fieldChi` construction uses this package. Its raw host comes from `CharData.toHostRaw`. There the map `res` composes the cyclotomic exponent equivalence with the explicit character map `art`. The field is the fixed field of its kernel. The quotient isomorphism sends the restriction of $\tau$ to `res τ`. The action of $\tau$ on the primitive root determines its exponent by injectivity of the powers in the standard residue range. Substituting this exponent into the quotient isomorphism gives `art_spec`. Those fields identify the arithmetic meaning of the data. In the finite-group proof, `recH = toE.comp H.art` and `arith = cftData H.q H.d (recH H)`. Here `toE` is a bijective change of coordinates, and `cftData` forms the image of $\ker\pi$ and the image of $w$. The Jacobi symbol of the second sign coordinate in `H.der.art_ch` tests membership in $\Phi$ after `toE`.

The `hostFactsS_pf` proof takes $S_0$ to be the prime divisors of $QS\,q$. Its first four fields follow from the host's primality, $2\mid QS$, and $d\nmid QS\,q$. Outside $S_0\cup\{d\}$, $p\nmid N$, so the local kernel is trivial by `unramified_spec`. Inside $S_0$, $d\mid M$. An inertia representative is $1\bmod d$, so its Jacobi symbol is $1$. The selected Frobenius representative is $p\bmod d$, whose Jacobi symbol is $1$ by the supplementary law $(2/d)=1$ when $d\equiv7\pmod 8$, or by $(-d/p)=(p/d)$ for odd $p$ and the host splitting hypotheses for the odd divisors of $QS$ and for $q$. Hence both images lie in $\Phi$. At $d$, the prime-to-$d$ part is $QS\,q$. The input `art_d` puts the image of its kernel in $\{1,\varphi.\mathrm{iod}\}$. CRT provides a unit $1\bmod QS\,q$ and $-1\bmod d$. Since $d\equiv3\pmod4$, its Jacobi symbol modulo $d$ is $-1$, so its image is $\varphi.\mathrm{iod}$. The identity supplies the other element, and `toE` sends the two to $0$ and $\mathrm{sgc}_0=((1,0),0)$. Factoring $QS\,q$ identifies the prime set with `insert H.q H.small`. This proves the advertised `HostFactsS` for the actual `arith`.

The single application of `hostFactsS φ H` inside `core_gm` is the argument to `ch_core` following `keptA Λ H.toHostRaw`. Its data argument is `arith H.toHostRaw`, with the prime set inferred from the proof's type. `PrimRead` has no `HostFactsS` argument. At its coefficient call it passes `R.condN R.q R.d (recH R) ψ n` to `primitive_value_primitive`, for `R = H.toHostRaw`. This is the same `cftData`, by definition. Its use of `HostDer.art_surj` is a separate step at line 72. [Lean, read]

**Source and reading boundary.** The following references use the archive SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The mathematics in the proof above follows the named bodies. The ring-of-integers generation theorem, cyclotomic Galois equivalence, residue-map surjectivity and finite-field Galois theorem are imported inputs. The proof also retains the `HostRaw` compatibility and the specialized sign inputs. The argument uses cyclotomic restriction via `art_spec`. General Artin reciprocity is outside this chain. In the concrete `AnyGrp` instance, `art_d` follows by reducing a unit $1\bmod QS\,q$ modulo $q$ and $QS$. The first sign and the $QS$-component are then trivial, as is the correction to the latter coming from the first sign. The second sign is $1$ or $-1$. The imported square-root action used for the derived sign formula remains [Lean] at the source boundary.

| Archive source | Role | Status |
|---|---|---|
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:12–46,54–56,87–125,174–175` | Host assumptions and derived interfaces | [Lean] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean:17–21,35–41,69–93` | Normal lift, power action, restriction compatibility and surjectivity | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycLift.lean:17–44,46–87,91–116` | Contraction, inertia lift, prime choice and Frobenius coset | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean:12–56,62–185,191–299` | Reduction lemma and host inertia, Frobenius and decomposition proofs | [Lean, read] |
| `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean:18–96` | Powers of Frobenius and generation modulo inertia | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycAll.lean:90–106` | Host core field assignments | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfRawToHostRaw.lean:9–44` | Derived host package | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/AnyLevel.lean:119–123` | Raw host on the character route | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean:38–82,113–139` | Cyclotomic fixed field and the construction of restriction compatibility | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/AnyFrame.lean:235–237,252–276,313–348` | Concrete unit map and its restriction at $d$ | [Lean, read] for the unit map and the cited restriction steps |
| `src/Development/AutomorphicArithmetic/CharacterBoxes/FieldChi.lean:20–59` | Construction of the host package used by the character route | [Lean, read] |
| `src/Development/AutomorphicArithmetic/PrimitiveCosets/RecH.lean:10–23`; `src/Development/AutomorphicArithmetic/PrimitiveCosets/ToEBij.lean:5–84` | Shared data and coordinate change | [Lean, read] |
| `src/Formalism/SizeWindowBrackets/GaloisToProductIsIso.lean:12–32`; `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean:17–108,123–127` | CRT representative and image of the local kernel | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean:15–28,34–105` | Reciprocity signs and modulus divisibility | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean:165–175` | Sign coordinate from the square-root action and cancellation | [Lean, read] |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSym.lean:62` | Square-root action used by the sign argument (proved in §5.3.1.3) | [Lean, read] |
| `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean:254–261,290–295,792` | Prime parts, supplementary law, and sign coordinate | [Lean, read] |
| `src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean:14–22` | The eight fields supplied to the Fourier argument | [Lean] |
| `src/Development/AutomorphicArithmetic/PrimitiveCosets/hostFactsS.lean:7–136` | Finite-group host facts, conditional on the host inputs | [Lean, read] |
| `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:21–22,55–60`; `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:343–348` | Actual P6 argument | [Lean, read] |
| `src/Development/AutomorphicArithmetic/PrimitiveCosets/PrimRead.lean:48–61,64–80` | Shared-data consumer and separate surjectivity call | [Lean, read] |

For a classical comparison, Milne proves the prime-power ring-of-integers and ramification statements in Proposition 6.2 (pp. 96–98), explains the decomposition and inertia calculation in Remark 8.12 (p. 140), and computes the unramified cyclotomic power action in Example 8.18 (p. 143). The order-of-reduction argument above covers the lifts at primes dividing the ambient modulus and is transcribed from the Lean proof cited here. The worked table and the mapping between the two P6 consumers are this book's exposition. [Milne, *Algebraic Number Theory*, v3.08](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

### 5.3.1.3 The second host sign from a quadratic Gauss sum

**Motivation.** The preceding subsection describes which cyclotomic units represent inertia and Frobenius. The Fourier argument also needs to know which of those representatives fix the quadratic part of the host singled out by $d$. The host comes with a specified element $b$ satisfying $b^2=-d$. Any rational automorphism carries $b$ to $b$ or $-b$. A finite sum in the ambient cyclotomic field gives a root of the same equation and makes the sign computable. The coefficients of the sum are rational integers, so the automorphism acts only on the roots of unity in its terms.

Throughout, the host hypotheses are that $q,d$ are primes, $q\equiv3\pmod8$, $d\equiv7\pmod{16}$, and $\left(\frac{-d}{q}\right)=1$. These primes are distinct by their classes modulo $8$. On the character route the ambient modulus is $N=Q_S qd$ with $Q_S>0$, $\gcd(Q_S,qd)=1$, and $2^{e+2}\mid Q_S$ for the frame exponent $e\ge2$. The `fieldChi` route also assumes $q\ne3$. Every odd prime $\ell\mid Q_S$ satisfies $\left(\frac{-d}{\ell}\right)=1$. In particular the modulus is even. We use $A(u)$ for the host map called `art`, and $s_d$ for projection to its second sign, Lean's `.1.2`. The second sign is in $\{1,-1\}$ and is separate from the frame coordinate.

**Example 1 ($d=7$).** Take $q=11$. We have $-7\equiv4\pmod{11}$, so the host condition holds. For $x$ a primitive seventh root, the nonzero squares modulo $7$ are $1,2,4$. The signed sum is $G=(x+x^2+x^4)-(x^3+x^5+x^6)$. The exponent $5$ carries $\{1,2,4\}$ to $\{5,3,6\}$ and carries its complement back to the squares. Thus a cyclotomic unit represented by $5$ sends $G$ to $-G$. The exponents $2$ and $11\equiv4\pmod7$ preserve the square set, giving the positive second sign for the Frobenius representatives at $2$ and $11$. Here those representatives have the stated exponents **modulo $7$**. The integer $2$ is a nonunit modulo $N$.

**Example 2 ($d=23$).** Take $q=59$. Then $-23\equiv36=6^2\pmod{59}$. Squaring $1,\ldots,11$ modulo $23$ gives, in order, $1,4,9,16,2,13,3,18,12,8,6$. In particular $2=5^2$ and $59\equiv13=6^2\pmod{23}$ as residue identities. The exponent $5$ is absent from the square list and interchanges the square and nonsquare cosets, so it negates the sum with these coefficients. The exponents $2$ and $59$ preserve each coset. For these two examples one can take $Q_S=16$ in the congruence calculations, so $5$ represents a unit modulo each $N$. As a check at $d$, the units represented by $881=1+5(16\cdot11)$ and $19825=1+21(16\cdot59)$ are $1$ modulo $Q_Sq$ and $-1$ modulo $7$ and $23$, respectively. They negate the respective quadratic sums since $-1$ is outside each square list. The general proof below identifies these sums with square roots.

**Definition (The algebraic normalization).** Let $N>0$, let $p\mid N$ be prime with $p\equiv3\pmod4$, and fix the archive's primitive root $z$ of order $N$ in $L=\mathbb Q(\zeta_N)$. Then $x=z^{N/p}$ has order $p$ because $N\mid (N/p)j$ exactly when $p\mid j$. Let $\chi_p(0)=0$ and let $\chi_p(a)$ be $1$ on nonzero squares and $-1$ on nonsquares in $\mathbb F_p$. Define $\psi_x(a)=x^a$ using any integer representative of $a$, and put $G_x=\sum_{a\in\mathbb F_p}\chi_p(a)\psi_x(a)$. We use the additive character with positive exponent and the unscaled sum. The character $\psi_x$ is primitive since $x$ has order $p$. The definition uses the chosen algebraic root of unity. The host element `sqd` is specified by its square and its action, with no choice of sign in a complex embedding required. In particular this calculation uses the algebraic square of $G_x$.

**Lemma (Square-root action, `D7.sqrt_act`) [Lean, read].** Let $u\in(\mathbb Z/N\mathbb Z)^\times$, with least nonnegative representative $v$, and let $\tau_u$ act by $w\mapsto w^v$ on $N$th roots of unity. If $y\in L$ satisfies $y^2=-p$, then $\tau_u(y)=\left(\frac{v}{p}\right)y$. The symbol on the right is the Jacobi symbol with prime denominator, hence the Legendre symbol. On units it takes values in $\{1,-1\}$.

**Proof.** First, the finite-field square identity used by `Cond.gs_sq` is $G_x^2=\chi_p(-1)p$. To see the product calculation behind the identity, write $\psi=\psi_x$ and let $\psi^{-1}$ be its pointwise inverse. In the product of the two sums for $(\chi_p,\psi)$ and $(\chi_p^{-1},\psi^{-1})$, the second summation variable $b$ is nonzero in every contributing term. Here the inverse multiplicative character is extended by zero at zero. Put $a=bc$ in the first sum. The product is then $\sum_c\chi_p(c)\sum_{b\ne0}\psi(b(c-1))$. Since $\chi_p$ is nontrivial, $\sum_c\chi_p(c)=0$, so we may restore the term $b=0$ in each inner sum. The complete inner sum is $p$ for $c=1$ and zero otherwise by the finite geometric sum for a primitive root. The product is $p$. Now $\chi_p^{-1}=\chi_p$, and replacing $\psi(a)$ by $\psi(-a)$ multiplies the sum by $\chi_p(-1)$. As $p\equiv3\pmod4$, the supplementary law gives $\chi_p(-1)=-1$. Thus $G_x^2=-p$ and $G_x\ne0$. This is the specialization of the finite-field product and square identities used in the production proof.

Next, $x^N=1$ and $\tau_u(x)=x^v$. The automorphism fixes all the coefficients $\chi_p(a)$, so $\tau_u(G_x)=\sum_a\chi_p(a)\psi_x(va)$. The reduction of $v$ modulo $p$ is invertible since $p\mid N$ and $u$ is a unit. Replacing $va$ by $c$ turns the coefficient into $\chi_p(v)^{-1}\chi_p(c)$, including the zero term. The inverse of this sign equals the sign itself, so $\tau_u(G_x)=\chi_p(v)G_x$. This is the shift used in `D7.gs_act`. The map `sgnN` first reduces the unit modulo $p$ and then applies the quadratic character. By `sgnN_val` its value is $\left(\frac{v}{p}\right)$.

Finally, $(y-G_x)(y+G_x)=0$ in a field. In either case $y=\pm G_x$ the same action formula holds, since $\tau_u$ fixes the rational sign in front of $G_x$. This last step permits the use of any specified root with the given square. $\square$

**The root in the fixed field [Lean, read].** On the character route `AnyFrame.art` defines $s_p(A(u))=\left(\frac{v}{p}\right)$ for the two coordinates $p=q,d$, using `sgnN`. Its second-coordinate computation is stored in `CharData.art_ch`. The host field $E$ in `OfChar` is the fixed field of the kernel of $\tau_u\mapsto A(u)$, and the restriction of $\tau_u$ has coordinate $A(u)$ under the Galois identification $\gamma$. The proof `exists_root` takes the root supplied by `Cond.sqrt_exists`, which is the Gauss sum constructed above. The lemma shows that each member of this kernel acts on that root by $s_d(1)=1$. Hence it belongs to $E$. For $\sigma\in\operatorname{Gal}(E/\mathbb Q)$, lift $\gamma(\sigma)$ through the surjective map $\tau_u\mapsto A(u)$. Restricting the action on the root proves $\sigma b=s_d(\gamma(\sigma))b$ in $E$. The specialization `exists_sqd` uses $p=d$ and stores the root, its square, and its action as `sqd`, `sqd_sq`, and `gal_sqd` in `toHostRaw`.

**Recovering the second sign from the raw host [Lean, read].** The downstream theorem `Der.art_ch` is formulated for a raw host with these three fields and the cyclotomic restriction compatibility. Write $\iota:E\hookrightarrow L$ for its embedding and $\sigma_u=\gamma^{-1}(A(u))$. The restriction compatibility gives $\iota(\sigma_u b)=\tau_u(\iota b)$. Using the specified host action on the left and the lemma on the right gives $s_d(A(u))\,\iota b=\left(\frac{v}{d}\right)\iota b$. Since $(\iota b)^2=-d\ne0$, cancellation yields $s_d(A(u))=\left(\frac{v}{d}\right)$. This is the `art_ch` field of `Der.hostCore` and then of `HostRaw.der`. The character constructor uses the sign to produce the raw host. The derived theorem recovers the sign using the raw host's root and its compatibility.

**The negative discriminant and the prime $2$.** Since $d$ is prime and $-d\equiv1\pmod4$, the quadratic field $\mathbb Q(b)$ has discriminant $-d$, with integral basis $1,(1+b)/2$. For example the latter generator has polynomial $X^2-X+(1+d)/4$ of discriminant $-d$, which is squarefree. The discriminant of $X^2+d$ itself is $-4d$. For positive odd $k$, quadratic reciprocity and the supplementary law for $-1$ give $\left(\frac{-d}{k}\right)=\left(\frac{-1}{k}\right)\left(\frac{d}{k}\right)=\left(\frac{k}{d}\right)$. When $k\equiv1\pmod4$ the two factors contribute no sign, and when $k\equiv3\pmod4$ their minus signs cancel. This is the calculation in `jacobi_neg_recip`. In particular the hypothesis at $q$ gives $\left(\frac{q}{d}\right)=1$. At $2$ the proof uses `jac_two_d` to obtain $\left(\frac{2}{d}\right)=(-1)^{(d^2-1)/8}=1$ since $d\equiv7\pmod8$. Equivalently the Kronecker symbol $\left(\frac{-d}{2}\right)$ is $1$ since $-d\equiv1\pmod8$. This agrees with the polynomial $X^2-X+(1+d)/4$, which has two distinct roots modulo $2$. For example $(1+d)/4$ is $2$ at $d=7$ and $6$ at $d=23$. The first sign at a Frobenius representative for $2$ is $\left(\frac{2}{q}\right)=-1$ by $q\equiv3\pmod8$. The original host condition $d\equiv7\pmod{16}$ is retained. The action itself used $d\equiv3\pmod4$ and the supplement used $d\equiv7\pmod8$.

**Where the sign enters `HostFactsS` [Lean, read].** Set $S_0=\{q\}\cup\mathrm{small}$, the prime divisors of $Q_Sq$. In the additive coordinates of the preceding subsection, membership in $\Phi$ is equivalent to having second sign $+1$. For $\ell\in S_0$ the prime-to-$\ell$ part of $N$ still contains $d$. The already identified inertia representatives are $1$ modulo $d$, so their second signs are $+1$. The Frobenius representatives are $\ell$ modulo $d$. Their signs are $+1$ by `jac_two_d` at $2$, the host assumption at $q$ and reciprocity, or the splitting condition for odd $\ell\mid Q_S$ and reciprocity. These are the `split_inertia` and `split_frob` fields. The splitting asserted by the sign is in the quadratic part selected by $d$. At $d$, a CRT unit equal to $1$ modulo $Q_Sq$ and $-1$ modulo $d$ belongs to the local inertia kernel. Its sign is $\left(\frac{-1}{d}\right)=-1$. The `art_d` restriction leaves only the identity or the element with this one sign changed and trivial frame coordinate. Thus the CRT witness realizes the latter and gives the additive inertia set $\{0,\mathrm{sgc0}\}$. The resulting `hostFactsS` is passed to `ch_core` with the same arithmetic data as in §5.3.1.2.

**Source map and reading boundary.** Paths below are relative to the `lean/` directory of the joined archive A2, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The local R3 reading concerns the displayed proof bodies and assignments. [Archive source](../sources/SOURCES.md#alpöge)

| Archive path and lines | Role |
| --- | --- |
| `src/Formalism/FrobeniusOrbits/Statement.lean:13–14` | Original `HostHyp`. |
| `src/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean:19–51,95–104,143–149` | Algebraic sum, square, primitive root and existence. |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSym.lean:15–23,31–77,157–165` | Unit sign, Gauss shift and action on either root. |
| `src/Development/AutomorphicArithmetic/CharacterBoxes/FieldChi.lean:20–59`; `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/AnyLevel.lean:119–123` | P6 host entry. |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/AnyFrame.lean:235–250,313–348`; `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfChar.lean:38–139` | Sign in the character constructor, fixed-field descent and the selected raw root. |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ConjEMemHostFIff.lean:202–207`; `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycBasic.lean:35–39,72–76,165–175` | Restriction, square-root action and cancellation. |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/CycAll.lean:90–106`; `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/OfRawToHostRaw.lean:9–42` | Packaging in the derived host. |
| `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean:15–28`; `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean:290–294` | Actual reciprocal identity and supplement used by the consumer. |
| `src/Development/AutomorphicArithmetic/PrimitiveCosets/hostFactsS.lean:7–136`; `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:55–60` | Sign-dependent host fields and the Fourier consumer. |

The finite-field product and shift can be compared directly with Mathlib's pinned `Mathlib/NumberTheory/GaussSum.lean:71–86,166–201,222–228`. The imported proofs below those identities, including `sum_mulShift`, `MulChar.sum_eq_zero_of_ne_one`, and `AddChar.zmodChar_primitive_of_primitive_root`, remain [Lean]. Section 5.3.1.4 reads the imported quadratic-character and Jacobi reciprocity proofs. The cyclotomic equivalence `IsCyclotomicExtension.Rat.galEquivZMod` and the fixed-field quotient theorem `IsGalois.normalAutEquivQuotient` remain [Lean] inputs. The residue-field surjectivity and cyclotomic integer-ring inputs from §5.3.1.2 remain at their stated reading levels. [Pinned Mathlib source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/GaussSum.lean#L71-L86)

Milne identifies the unique quadratic subfield of the prime cyclotomic field and computes its unramified signs through Frobenius and reciprocity (Example 8.19 and pp. 143–144). His discussion of class numbers gives the case of $\mathbb Q(\sqrt{-23})$ and the splitting of $2$ (p. 101). Here the archive obtains the action on the specified root directly from the algebraic Gauss sum. [Milne, *Algebraic Number Theory*, v3.08](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

### 5.3.1.4 Quadratic reciprocity and the host splitting signs

**Motivation.** The second host sign from §5.3.1.3 is evaluated on the exponent modulo $d$. For an odd prime $p$ dividing $Q_Sq$, the input instead describes $-d$ modulo $p$. Reciprocity exchanges these two arguments. The minus sign in the discriminant absorbs the reciprocity sign when $dequiv3pmod4$. At $p=2$ the input comes from a separate supplementary law.

**Examples.** For $d=7$, the squares modulo $7$ are $1,2,4$ among nonzero residues. With $q=11$, the two sides of the odd-prime identity are positive since $-7equiv2^2pmod{11}$ and $11equiv2^2pmod7$. For $d=23$, take $q=59$. Here $-23equiv6^2pmod{59}$ and $59equiv13equiv6^2pmod{23}$. In both cases $2$ is a square modulo $d$, represented by $3^2$ modulo $7$ and $5^2$ modulo $23$. The odd $Q_S$ branch can also be seen in these examples. For $d=7$, take $Q_S=16\cdot29$ and use $-7\equiv14^2\pmod{29}$ and $29\equiv1\pmod7$. For $d=23$, take $Q_S=16\cdot13$ and use $-23\equiv4^2\pmod{13}$ and $13\equiv6^2\pmod{23}$. At $p=d$ the relevant residue is zero.

For a composite denominator, take $d=7$ and $n=15$. The residues of $-7$ modulo $3$ and $5$ are $2$ and $3$, both nonsquares. The Jacobi value is $(-1)(-1)=1$, agreeing with $15equiv1pmod7$. This positive value can coexist with two inert prime factors. At $n=21$ the factor at $7$ is zero, so the product is zero, as is the symbol of $21$ modulo $7$. At $n=1$ the empty product is $1$. Even a repeated factor matters: at $n=9$ the factor $-1$ at $3$ occurs twice, giving $1$, in agreement with $9equiv2pmod7$.

**Definition.** For an odd prime $p$, let $L_p(a)$ be the Legendre symbol of an integer $a$, with value $0$ on the zero residue and values $1,-1$ on nonzero squares and nonsquares. For a positive odd integer $n$, write $n=prod_i p_i$, listing primes with multiplicity. Define $J(a,n)=prod_i L_{p_i}(a)$. The empty product convention gives $J(a,1)=1$ for every $a$. The definition gives multiplicativity in the denominator by concatenation and in the numerator by multiplicativity of each $L_p$. Reduction of $a$ modulo $n$ preserves each residue modulo $p_i$. A factor vanishes exactly when $p_i$ divides $a$, so $J(a,n)=0$ exactly when $gcd(|a|,n)>1$.

**Lemma (prime reciprocity and supplements) [Lean, read].** For all odd primes $p,ell$, with $h(t)=(t-1)/2$ on positive odd integers,
$L_p(ell)=(-1)^{h(p)h(ell)}L_ell(p)$.
Also $L_p(-1)=(-1)^{h(p)}$, and $L_p(2)=chi_8(p)$, where $chi_8$ is $1$ on $1,7$ and $-1$ on $3,5$ modulo $8$ and is zero on even integers.

**Proof.** In an odd prime field, Euler's criterion identifies the reduction of $L_p(a)$ with $a^{h(p)}$. The two unit signs have distinct reductions. Taking $a=-1$ gives the first supplement. For distinct $p,ell$, choose a primitive $p$th root $x$ in an algebraic closure of $mathbb F_ell$. Such a root exists because $X^p-1$ has $p$ distinct roots there. The product proof of the square identity in §5.3.1.3 uses only the primitive root and finite geometric sums, so it applies here for either residue class of $p$ modulo $4$. For $G=sum_{ainmathbb F_p}L_p(a)x^a$ it gives $G^2=L_p(-1)p$. This is nonzero in characteristic $ell$. The $ell$th power map preserves the coefficients and sends $x^a$ to $x^{ell a}$. Multiplication by $ell$ permutes the residues modulo $p$, so $G^ell=L_p(ell)G$. Dividing by $G$ yields $(L_p(-1)p)^{h(ell)}=L_p(ell)$ in characteristic $ell$. Euler's criterion and distinctness of the two signs now give $L_p(ell)=L_ell(L_p(-1)p)=(-1)^{h(p)h(ell)}L_ell(p)$ over the integers. For $p=ell$, both sides are zero. This equality form is the prime input to the composite proof.

For the supplement at $2$, work in characteristic $p$ and choose a primitive eighth root $t$ in the algebraic closure. The Gauss sum on $mathbb Z/8mathbb Z$ with coefficients $chi_8$ is $T=t-t^3-t^5+t^7=2(t-t^3)$ since $t^4=-1$. Squaring gives $T^2=8$, using $t^6=-t^2$. The unit group modulo $8$ has generators $3,7$ of order two, and their product is $5$. The displayed signs thus define a multiplicative character on units, extended by zero on even residues. The $p$th-power map and substitution $amapsto pa$ in this eight-term sum give $T^p=chi_8(p)T$. As $T
e0$, it follows that $8^{h(p)}=chi_8(p)$ in characteristic $p$. Since $2^{p-1}=1$, this power of $8$ equals $2^{h(p)}$. Euler's criterion again recovers the integer sign. The pinned proof performs these same power-and-cancellation steps for arbitrary finite fields of odd characteristic. [Prime specialization](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean#L105-L129) · [Finite-field Gauss-sum proof](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/GaussSum.lean#L283-L402)

**Theorem (Jacobi reciprocity and the negative argument) [Lean, read].** For positive odd $r,n$,
$J(r,n)=(-1)^{h(r)h(n)}J(n,r)$,
$J(-1,n)=(-1)^{h(n)}$, and $J(2,n)=chi_8(n)$. If $requiv3pmod4$, then $J(-r,n)=J(n,r)$. These identities allow common prime factors and include denominator $1$.

**Proof.** For odd positive $u,v$ the identity $h(uv)=h(u)+h(v)+2h(u)h(v)$ gives additivity modulo $2$. The two supplements therefore extend by multiplying the prime formulas, using also multiplicativity of $chi_8$. Now write $r=prod_i r_i$ and $n=prod_j p_j$. Expanding both arguments gives
$J(r,n)=prod_{i,j} L_{p_j}(r_i)$.
Replace each factor by $(-1)^{h(r_i)h(p_j)}L_{r_i}(p_j)$ using the equality form of prime reciprocity. The resulting sign exponent is $(sum_i h(r_i))(sum_j h(p_j))$, congruent to $h(r)h(n)$ modulo $2$. The remaining product is $J(n,r)$. If a prime occurs in both lists, a zero factor occurs on each side. This multiplication uses no cancellation of a symbol and works for empty lists. Mathlib implements the two expansions by applying `value_at` twice, with the sign packaged as the bimultiplicative `qrSign`.

Finally $J(-r,n)=J(-1,n)J(r,n)=(-1)^{(1+h(r))h(n)}J(n,r)$. For $requiv3pmod4$ the exponent is even. In `jacobi_neg_recip`, the branch $nequiv1pmod4$ has both signs positive and the branch $nequiv3pmod4$ has two minus signs. [Pinned Jacobi proof](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean#L299-L448)

**Corollary (the three host branches) [Lean, read].** Use the host hypotheses of §5.3.1.3 and let $p$ be a prime dividing $Q_Sq$. Then $J(p,d)=1$.

**Proof.** The divisibility alternative in `dvd_QSq_iff` gives $pmid Q_S$ or $p=q$. In the former case with $p=2$, the hypothesis $dequiv7pmod{16}$ implies $dequiv7pmod8$, so `jac_two_d` gives $J(2,d)=chi_8(d)=1$. For odd $pmid Q_S$, apply the theorem with $(r,n)=(d,p)$ to `QS_split`, which supplies $J(-d,p)=1$. In the remaining branch $p=q$, oddness follows from $qequiv3pmod8$ and the same theorem with $(r,n)=(d,q)$ converts the last clause of `HostHyp`, namely $J(-d,q)=1$. The three branches are exactly those of `jac_of_dvd`.

**Remarks.** For the quadratic field $mathbb Q(sqrt{-d})$, the integral basis from §5.3.1.3 gives discriminant $-d$. At an odd prime $p$, the reduced integral polynomial has two simple roots when $J(-d,p)=1$, is irreducible when the symbol is $-1$, and has a double root at $p=d$. These give the split, inert and ramified cases for the quadratic field. At $2$, the integral polynomial $X^2-X+(1+d)/4$ reduces to $X(X-1)$ since $dequiv7pmod8$. This gives the split case, equivalently Kronecker value $1$ at $2$. The host proof uses $J(2,d)$, with $2$ in the numerator. The prime $q$ has $J(2,q)=-1$ by its residue modulo $8$, a different sign coordinate. [Milne, *Algebraic Number Theory*, v3.08, pp. 101, 143–144](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

In `hostFactsS_pf`, the condition $pmid Q_Sq$ ensures $p
e d$, so $d$ divides the prime-to-$p$ part of $N=Q_Sqd$. The inertia exponents reduce to $1$ modulo $d$, giving $J(1,d)=1$. The Frobenius exponent reduces to $p$ modulo $d$, giving the corollary's value through `inPhi_of_jac`. These are the `split_inertia` and `split_frob` fields for the second sign. At $2$ only the reduction of the Frobenius representative modulo $d$ is $2$; the representative is a unit modulo $N$. At $d$, the CRT witness instead has exponent $-1$ modulo $d$, so $J(-1,d)=-1$. The zero $J(d,d)$ concerns the ramified prime and cannot be the sign of a unit. The inertia witness and its use of `art_d` are described in the preceding subsections.

The archive consumers are `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/HostFacts.lean:15–28,41–46,104–105`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/GaloisMapComplexConjugation.lean:290–300`, and `src/Development/AutomorphicArithmetic/PrimitiveCosets/hostFactsS.lean:7–38,71–82,106–125` (archive A2, SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`). The deeper Mathlib inputs `quadraticChar_eq_pow_of_char_ne_two'`, `FiniteField.primitiveChar`, `primitiveZModChar` and `AddChar.IsPrimitive.zmod_char_eq_one_iff` remain [Lean] inputs to the formal reading. The preceding sections give the host action and local unit inputs.

### 5.3.1.5 Euler's criterion over a finite field

The reciprocity argument in §5.3.1.4 produces an identity of powers in a
field of positive characteristic. To read its sign as an integer-valued
quadratic character, we need to know exactly which field elements the
half-order power sends to $1$, to $-1$, and to $0$. The cardinality of the
field controls the exponent. The characteristic controls whether the two
signs are distinct.

**Two examples.** In $\mathbb F_7$, the exponent is $3$. For the square
column, the inputs pair as $1,6$, $2,5$, and $3,4$, with respective outputs
$1,4,2$. For the cube column, $1^3=1$, $2^3=8\equiv1$, and
$3^3=27\equiv-1$. The cubes of the other three units follow by negation.
The character column is determined by membership in $\{1,2,4\}$ for
nonzero inputs.

| $a$ | $a^2$ | $a^3$ | $\chi(a)$ in $\mathbb Z$ |
|---|---|---|---|
| $0$ | $0$ | $0$ | $0$ |
| $1$ | $1$ | $1$ | $1$ |
| $2$ | $4$ | $1$ | $1$ |
| $3$ | $2$ | $-1$ | $-1$ |
| $4$ | $2$ | $1$ | $1$ |
| $5$ | $4$ | $-1$ | $-1$ |
| $6$ | $1$ | $-1$ | $-1$ |

For $\mathbb F_9$, use $\mathbb F_3[t]/(t^2+1)$, writing $t$ also for
its residue class. The three squares of $0,1,-1$ in $\mathbb F_3$ are
$0,1,1$, so the defining quadratic has no root and is irreducible.
There are nine elements, uniquely $a+bt$ with $a,b\in\mathbb F_3$.
Here the exponent is $4$. Using $t^2=-1$ and $2=-1$, we get
$(1+t)^2=-t$ and $(1-t)^2=t$. Changing an input's sign leaves its
square unchanged. Thus the unit squares are exactly $1,-1,t,-t$.
Squaring the square column gives the fourth powers.

| $x$ | $x^2$ | $x^4$ | $\chi(x)$ in $\mathbb Z$ |
|---|---|---|---|
| $0$ | $0$ | $0$ | $0$ |
| $1$ | $1$ | $1$ | $1$ |
| $-1$ | $1$ | $1$ | $1$ |
| $t$ | $-1$ | $1$ | $1$ |
| $-t$ | $-1$ | $1$ | $1$ |
| $1+t$ | $-t$ | $-1$ | $-1$ |
| $-1-t$ | $-t$ | $-1$ | $-1$ |
| $1-t$ | $t$ | $-1$ | $-1$ |
| $-1+t$ | $t$ | $-1$ | $-1$ |

In particular $-1$ is a nonsquare in the prime field $\mathbb F_3$
and a square in its quadratic extension. Using the characteristic $3$
in place of the cardinality $9$ would give exponent $1$, which sends
the square $t$ to $t$. [Expository]

**Definition.** Let $F$ be a finite field of cardinality $Q$ and let
$G=F^\times$. Define $\chi_F:F\to\mathbb Z$ by taking $\chi_F(0)=0$,
$\chi_F(a)=1$ for $a\in G^2$, and $\chi_F(a)=-1$ for $a\in G\setminus
G^2$. This is the piecewise function underlying Mathlib's
`quadraticChar`. In the following proof write $s:G\to G$ for $s(x)=x^2$.

**Lemma (squares and the half-order kernel).** Assume
$\operatorname{char}F\ne2$. Then $m=(Q-1)/2=\lfloor Q/2\rfloor$ is a
positive integer. The square map has kernel $\{1,-1\}$ and image
of size $m$. The image equals $\{a\in G:a^m=1\}$.

**Proof.** The field has order $p^f$ for prime characteristic $p$ and
$f\ge1$. Hence $Q$ is odd and at least $3$. Commutativity makes $s$ a
homomorphism. If $x^2=1$, then $(x-1)(x+1)=0$, so $x=1$ or $x=-1$.
Both solutions occur and are distinct. Each nonempty fiber of $s$ is
a coset of this two-element kernel. Indeed $x^2=y^2$ for units exactly
when $(xy^{-1})^2=1$. Counting fibers gives $\lvert G^2\rvert=m$.
By Lagrange's theorem $y^{Q-1}=1$ for every $y\in G$, so
$(y^2)^m=1$. Thus the $m$ squares already supply $m$ distinct roots
of the nonzero polynomial $X^m-1$. The degree bound on distinct roots
gives the reverse inclusion. This proof uses finite-group order and
fiber counting together with the polynomial root bound.

**Theorem (Euler's criterion and identification).** Under the same
hypotheses, the following statements hold.

- For $a\ne0$, the integer $\chi_F(a)$ is $1$ if $a^m=1$ in $F$ and
  $-1$ otherwise.
- For every $a\in F$, the image of $\chi_F(a)$ under $\mathbb Z\to F$
  is $a^m$.
- On $G$, $\chi_F$ is the unique nontrivial homomorphism to
  $\{1,-1\}$ under multiplication. Its extension by zero is
  multiplicative on $F$.

**Proof.** The lemma identifies the $+1$ case. For $a\ne0$, Lagrange
also gives $(a^m)^2=1$, so $a^m$ is one of the two distinct signs.
For $a=0$, positivity of $m$ gives $0^m=0$, which agrees with the
cast of $\chi_F(0)$. Distinctness of the signs gives a multiplicative
identification of the two integer signs with their images in $F$.
Since $(ab)^m=a^mb^m$, the character is multiplicative on units.
An argument equal to zero gives zero on both sides of
$\chi_F(ab)=\chi_F(a)\chi_F(b)$. The quotient $G/G^2$ has size two.
Every homomorphism to the signs kills $G^2$, because either sign
squares to $1$. A nontrivial homomorphism on the two-element quotient
must send the other coset to $-1$. This proves uniqueness.

**How Mathlib proves the criterion.** The library's converse in
`FiniteField.unit_isSquare_iff` uses cyclicity. Choose a generator
$g$ of $F^\times$ and write a unit as $g^n$ with $n\ge0$.
Mathlib passes from integer powers to natural powers in the finite
group. The generator has order $\lvert G\rvert=Q-1=2m$. If
$(g^n)^m=1$, then $2m\mid nm$ by the order divisibility lemma.
Since $m>0$, cancellation in this divisibility relation gives
$2\mid n$. Writing $n=2j$ gives the square root $g^j$.
The forward direction is again $(y^2)^m=y^{Q-1}=1$.
`FiniteField.pow_card_sub_one_eq_one` lifts a nonzero element to a
unit, uses $\lvert F^\times\rvert=Q-1$ and the finite-group theorem
`pow_card_eq_one`, and then takes the value of the unit. The parity
input is `odd_card_of_char_ne_two`, obtained from the prime-power
cardinality and the characterization of even field cardinality.
The passage to `FiniteField.isSquare_iff` uses that a square root
of a nonzero field element is itself nonzero, so it can be lifted
back to a unit. Separately, `pow_dichotomy` rewrites the group-order
power as a square and uses the two field roots of $X^2-1$.

The unprimed `quadraticChar_eq_pow_of_char_ne_two` is the integer
formula on nonzero inputs. Its helper unfolds the piecewise
definition and rewrites the square test. The primed
`quadraticChar_eq_pow_of_char_ne_two'` has an integer cast into $F$
on the left and permits every input. The proof handles zero using
$Q\ge2$ and positivity of $\lfloor Q/2\rfloor$, then uses the
unprimed version and `pow_dichotomy` for the two nonzero cases.
In the library's construction of the multiplicative character,
`quadraticCharFun_mul` handles zero factors first. Its
odd-characteristic branch multiplies the two half-order powers
and checks their two possible signs, and its characteristic-two
branch uses the fact that every nonzero element is a square.
[Lean, read] [Pinned finite-field implementation](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Basic.lean#L781-L837)
[Quadratic character implementation](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean#L69-L196)

**The additive character interface.** For a commutative monoid $C$,
an additive character $\psi:\mathbb Z/n\mathbb Z\to C$ sends sums
to products and zero to $1$. Assume $n>0$. Define the shift by $a$
as the character $b\mapsto\psi(ab)$. Primitivity requires every
shift by $a\ne0$ to be nontrivial. Every class $b$ is $b_0$ times
the additive generator $1$, for $0\le b_0<n$. The shifted
character consequently takes the value $\psi(a)^{b_0}$ on $b$.
Thus it is trivial exactly when $\psi(a)=1$: evaluate at $1$ for
one implication and use the power formula for the other. By
primitivity this gives $\psi(a)=1$ if and only if $a=0$. This is
`AddChar.IsPrimitive.zmod_char_eq_one_iff`. Conversely, if that
equivalence holds for every $a$, a trivial shift evaluated at
$1$ forces $a=0$.

Given an element $\zeta$ of order $n$ in $C^\times$, the formula
$\psi([b])=\zeta^b$ defines such a primitive character.
Independence of the representative follows from $\zeta^n=1$,
as does the homomorphism law after reducing sums modulo $n$.
The order identity gives $\zeta^b=1$ exactly when $n\mid b$, so
the preceding converse applies. In `primitiveZModChar`, the
arguments are a positive integer $n$, a field $B$, and
$(n:B)\ne0$. The character takes values in the $n$th cyclotomic
extension of $B$, where the construction supplies the primitive
root. For the call in `FiniteField.primitiveChar`, put
$p=\operatorname{char}F$ and take $n=p$ and $B=F'$.
The assumed different field characteristics ensure $(p:F')\ne0$.
The resulting character on $\mathbb Z/p\mathbb Z$ is composed
with $\operatorname{Tr}_{F/\mathbb F_p}$. In the kernel interface,
the argument $a$ is now the trace of a field element selected to
have nonzero trace, using trace nondegeneracy with first argument
$1$. Its character value differs from $1$, so the composition
is nontrivial. A shift by a nonzero element of a field is a
bijection, giving primitivity of the composition. When $[F:\mathbb
F_p]>1$, the trace has a nontrivial kernel and the composition
can take value $1$ on nonzero inputs. The cyclic additive-domain
hypothesis of the kernel interface matters. [Lean, read]
[Pinned additive character implementation](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean#L128-L230)

**Conditional specialization to the host.** Retain the hypotheses
of §5.3.1.2. Let $Q_0$ be a prime above $\ell$ in the ambient
cyclotomic field, let $k$ be its residue field, and let
$M=\operatorname{ordCompl}_{\ell}(N)$ be the prime-to-$\ell$ part
of $N$. Write $\eta$ for the reduction of the integral
primitive $N$th root. The already established comparison
`zO_sub_mem_iff` gives $\eta^b=\eta^c$ exactly when $b\equiv
c\pmod M$ for nonnegative exponents $b,c$. In particular $\eta$
has order $M$, including order one when $M=1$.

To instantiate `zmod_char_eq_one_iff`, use $n=M$ with $M>0$,
$C=(k,\cdot,1)$, and $\psi=\operatorname{zmodChar}(M,\eta^M=1)$.
Primitivity is supplied by the order of $\eta$ via
`zmodChar_primitive_of_primitive_root`. At the argument
$a=[b-c]\in\mathbb Z/M\mathbb Z$, we have $\psi(a)=\eta^b(\eta^c)^{-1}$.
Thus $\psi(a)=1$ if and only if $a=0$, recovering the exponent
comparison. In the inertia comparison the exponents are $b=u_0$,
$c=1$, where $u_0$ is the natural representative of the cyclotomic
unit. In the Frobenius comparison they are $b=u_0$, $c=\ell$.
The archive obtains the exponent comparison directly by reduction,
then uses it on the integral generator. The additive character
formulation here is a conditional reformulation of that step.

For odd $\ell$, the Euler theorem can also be applied in this
same residue field. If $\lvert k\rvert=\ell^f$, substitute
$F=k$, $m=(\ell^f-1)/2$, and $a=\eta^b$ in the primed formula.
The input is a unit and its power is $\eta^{bm}$.
Consequently the quadratic sign is $+1$ precisely when
$M\mid bm$. This is an application of the additive kernel
interface at the class $[bm]$. The order of $\eta$ divides
$\ell^f-1=2m$, so $\eta^{bm}$ is a sign. For $\ell=2$ the
order comparison and additive interface still apply. This
formulation concerns the residue field at $Q_0$. The host
coordinate $\operatorname{sgnN}$ instead uses a prime field
$\mathbb Z/d\mathbb Z$ after reducing a unit modulo $d$. In that
call, the unit is nonzero, $d$ is odd, and the exponent is
$(d-1)/2$. The integer output agrees with the Jacobi symbol of
the chosen representative modulo $d$ by prime specialization.
[Expository]

**Where the two interfaces are consumed.** The two power formulas
supply different steps of the Mathlib reciprocity path.
`quadraticChar_neg_one` applies the unprimed formula at $-1$,
with the nonzero proof for $-1$, and expresses the answer as the
character modulo four. In `quadraticChar_card_card`, the primed
formula is instantiated in the **second** field $F'$ on the
image of the integer $\chi_F(-1)\lvert F\rvert$. The coefficient
character of the Gauss sum is $\chi_F$ cast into $F'$ and the
auxiliary additive character comes from
`FiniteField.primitiveChar F F'`. The resulting power in $F'$
is replaced by the cast of $\chi_{F'}$ at that argument. Equality
of the cast values lifts to equality of integer signs using
`MulChar.IsQuadratic.eq_of_eq_coe`.

For the supplement at two, the primed formula takes $a=2$ in
$F$. In the power supplier `FiniteField.two_pow_card`, take
$n=8$, $B=F$, and $(8:F)\ne0$, which follows from odd
characteristic. The target is $F(\zeta_8)$ and $\tau=\psi(1)$.
By additivity $\tau^8=\psi([8])=1$. At the argument $[4]$ the
kernel theorem gives $\tau^4\ne1$. The two-root factorization
in the extension gives $\tau^4=-1$. At the end of that proof,
the factor $4=2^2$ in $8=4\cdot2$ has half-order power $1$, by
`FiniteField.isSquare_iff` in $F$ with the explicit square
witness $2$. These are the additive and multiplicative inputs
to the supplement already used in §5.3.1.4.

**Limits of the hypotheses.** In characteristic two the square
map is injective since $x^2=y^2$ implies $(x-y)^2=0$. Finiteness
makes it surjective, and the integer-valued quadratic character
is $1$ on every unit. Also $1=-1$ in $F$ and $Q-1$ is odd,
so the half-order argument has lost its two distinct signs and
its even group order. For instance, in $\mathbb F_4$ take
$u^2+u+1=0$. Then $u$ is a square since $(u^2)^2=u$, but
$u^{\lfloor4/2\rfloor}=u^2\ne1$. In a ring with zero divisors,
field elements away from zero need not be units and even the
unit-group argument can fail. In $\mathbb Z/15\mathbb Z$ the
four distinct units $1,4,11,14$ square to $1$. In this ring
$(4-1)(4+1)=0$ with both factors nonzero. The unit $4$ is a square, with square root $2$. Yet $4^7=4$ since $4^2=1$,
so the naive exponent $\lfloor15/2\rfloor=7$ fails even on
a unit square. Here $\lvert(\mathbb Z/15\mathbb Z)^\times\rvert=8$,
and changing the exponent to $4$ also fails: every unit has
fourth power $1$ because the unit residues modulo $3$ and $5$
have orders dividing $2$ and $4$ respectively, while $2$ is a
nonsquare already modulo $3$. [Expository]

The mathematical results are classical. Conrad's notes give the
prime-power cardinality and cyclicity arguments and the same
polynomial model for the nine-element field. The two full
quadratic-character tables, the generator-free proof alongside
the production proof, and the conditional substitution into the
host residue calculation are the exposition here. [Conrad,
*Finite Fields*, pp. 1–2](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf)

The archive SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. The local reading ends at the finite-group order and cyclicity lemmas, finite-field trace nondegeneracy and cyclotomic root supply, integer-sign recovery, and the inherited host and Gauss-sum inputs. These imported inputs retain [Lean].

The residue comparison used here is
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/RootEqOfSubMem.lean:87–185`.
The separate prime-field sign comes from
`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ArtinMapSecondEqJacobiSym.lean:15–35`.
The production substitutions in the two Gauss-sum branches are at
[Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean:36–40,77–90](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean#L77-L90)
and
[Mathlib/NumberTheory/GaussSum.lean:303–319,346–402](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/GaussSum.lean#L346-L402).

### 5.3.1.6 Cyclic multiplicative groups of finite fields

The reverse implication of the unit square test in §5.3.1.5 writes an arbitrary unit as $g^n$. To use this expression one needs a single $g$ whose powers exhaust the units, and one needs to know the first positive exponent at which $g$ returns to $1$. A polynomial root bound supplies both facts.

**Example 1. Combining orders two and three in $\mathbb F_7$.** The element $-1=6$ has order two. The element $2$ has order three since $2^2=4$ and $2^3=8\equiv1\pmod7$. Their product is $g=5$. Successively multiplying by $5$ and reducing modulo $7$ gives

| $j$ | $0$ | $1$ | $2$ | $3$ | $4$ | $5$ | $6$ |
|---|---|---|---|---|---|---|---|
| $g^j$ | $1$ | $5$ | $4$ | $6$ | $2$ | $3$ | $1$ |

The first six entries exhaust the units. The nonzero squares are $1,4,2$, the even powers. By the character formula of §5.3.1.5 the quadratic character of $g$ is $-1$, whose image in the field agrees with $g^3=6$.

**Example 2. A primitive element in $\mathbb F_{16}$.** Let $f(T)=T^4+T+1$ over $\mathbb F_2$. Neither $0$ nor $1$ is a root. A reducible quartic with no linear factor has an irreducible quadratic factor. The only monic irreducible quadratic over $\mathbb F_2$ is $T^2+T+1$: the constant term must be $1$ to avoid the root $0$, and the linear coefficient must be $1$ to avoid the root $1$. Modulo this quadratic we have $T^3=1$ and $T^4=T$, so $f$ has remainder $1$. Thus $f$ is irreducible. Write $t$ for the class of $T$ in the field $\mathbb F_2[T]/(f)$. Its elements have unique representatives of degree at most three, giving sixteen elements.

Multiplication by $t$ shifts all terms up by one degree and replaces $t^4$ by $t+1$. For example $t(t^3+t^2)=t^4+t^3=t^3+t+1$, and the next product reduces to $t^2+1$.

| $j$ | $t^j$ | $j$ | $t^j$ |
|---|---|---|---|
| $0$ | $1$ | $8$ | $t^2+1$ |
| $1$ | $t$ | $9$ | $t^3+t$ |
| $2$ | $t^2$ | $10$ | $t^2+t+1$ |
| $3$ | $t^3$ | $11$ | $t^3+t^2+t$ |
| $4$ | $t+1$ | $12$ | $t^3+t^2+t+1$ |
| $5$ | $t^2+t$ | $13$ | $t^3+t^2+1$ |
| $6$ | $t^3+t^2$ | $14$ | $t^3+1$ |
| $7$ | $t^3+t+1$ | $15$ | $1$ |

The entries at indices $0$ through $14$ exhaust the nonzero representatives. The table also gives an order-three element $t^5$, an order-five element $t^3$, and their product $t^8=t^2+1$. The coprime-order argument below shows that this product is primitive too. Cyclicity holds here in characteristic two, while the power formulas in §5.3.1.5 require odd characteristic.

**Definitions.** In a finite group the order $\operatorname{ord}(x)$ of $x$ is its least positive period under exponentiation, that is, the least positive $d$ with $x^d=1$. The exponent of the group is the least positive $e$ with $x^e=1$ for every $x$. A primitive element of a finite field is a generator of its multiplicative group.

**Lemma 1 (orders and powers).** If $x$ has order $d$, then $x^n=1$ exactly when $d\mid n$. The subgroup $\langle x\rangle$ has $d$ elements. The order of $x^r$ for $r\geq 0$ is $d/\gcd(d,r)$.

**Proof.** Write $n=ad+b$ with $0\leq b<d$. Then $x^n=x^b$, which is $1$ exactly when $b=0$, by minimality. Allowing negative $a$ accounts for all integer powers. The powers with exponents from $0$ through $d-1$ are distinct since equality of two would give a positive period smaller than $d$. The cosets of $\langle x\rangle$ partition any finite ambient group $G$ into sets of size $d$, giving $d\mid |G|$. Finally $(x^r)^s=1$ is equivalent to $d\mid rs$. Dividing $d$ and $r$ by their greatest common divisor leaves coprime integers, so the least positive $s$ is $d/\gcd(d,r)$.

**Lemma 2 (attaining the exponent).** In a finite abelian group some element has order equal to the exponent.

**Proof.** Let commuting elements $x,y$ have coprime orders $a,b$. Then $(xy)^{ab}=1$. If $(xy)^s=1$, raising that equation to the $b$th power gives $x^{sb}=1$, so $a\mid s$. Raising it to the $a$th power gives $b\mid s$. Therefore $ab\mid s$, and $xy$ has order $ab$.

By Lemma 1 the exponent $e$ is the least common multiple of the element orders and divides $|G|$. For each maximal prime power $\ell^v$ dividing $e$, some element has order $\ell^v d$ with $\ell\nmid d$, by the definition of least common multiple of a finite list. Its $d$th power has order $\ell^v$. Multiply the resulting elements, one for each prime. At each stage the order accumulated so far is coprime to the next order, so the product has order $e$. For $e=1$ the empty product is $1$. [Conrad, *Finite Fields*, Appendix A, Theorems A.1–A.2 and Corollary A.4](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf)

**Proposition (finite multiplicative subgroups).** If $R$ is a commutative integral domain and $G$ a finite subgroup of $R^\times$, then $G$ is cyclic and its exponent is $|G|$.

**Proof.** If a nonzero polynomial $P$ has a root $a$, division by the monic polynomial $X-a$ gives $P=(X-a)Q$. Any other root $b$ is a root of $Q$, since $b-a$ is nonzero and $R$ has no zero divisors. Induction on degree, starting with a nonzero constant, bounds the number of distinct roots by the degree. All $|G|$ elements are roots of the monic polynomial $X^e-1$ of degree $e$. Thus $|G|\leq e$. Lemma 2 gives $e\mid |G|$ and an element of order $e$, so $e=|G|$ and that element generates $G$. [Conrad, *Finite Fields*, Lemma 1.6](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf)

**Primitive elements and roots of unity.** Every finite field $\mathbb F_q$ with $q=p^f$, $p$ prime and $f\geq 1$, has a primitive element. This includes $1$ in $\mathbb F_2$. If $g$ generates $\mathbb F_q^\times$, the primitive elements are $g^j$ for $0\leq j<q-1$ with $\gcd(j,q-1)=1$. Their number is $\varphi(q-1)$, including $\varphi(1)=1$. More generally, exact order $m>0$ occurs precisely when $m\mid q-1$. Necessity is Lemma 1, and sufficiency follows by taking $g^{(q-1)/m}$. In particular an order divisible by the characteristic cannot occur. Every multiplicative generator generates the field over its prime field because all nonzero elements are its powers. The converse can fail. In Example 2, $t^3$ has order five and generates the field over $\mathbb F_2$: a proper subfield would have degree one or two over $\mathbb F_2$ by the tower law, and hence a unit group of order one or three.

**Why the domain condition matters.** The units modulo $15$ are $1,2,4,7,8,11,13,14$, with squares $1,4,1,4,4,1,4,1$ in that order. Every fourth power is $1$ and $2$ has order four. The exponent is four although the group has eight elements. The polynomial $X^2-1$ has four distinct roots $1,4,11,14$. At $X=4$ the factors $X-1$ and $X+1$ have nonzero values $3$ and $5$ with product zero. The step that passes from a second root of $P$ to a root of its quotient by a linear factor fails in this ring.

**The pinned Mathlib proof [Lean, read].** The instance for $R^\times$ uses the injective multiplicative map `Units.coeHom R`. The instance for a finite subgroup composes inclusion with the same map. `card_nthRoots_subgroup_units` injects the solutions of $x^n=g_0$ in the group into the distinct roots of $X^n-f(g_0)$ in $R$, where $f$ is the injective map. The cardinality of the distinct roots is at most the multiset cardinality, bounded by $n$ via `Polynomial.card_nthRoots`. The cyclicity argument takes $g_0=1$ for every positive $n$. [Mathlib/RingTheory/IntegralDomain.lean:118–154](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/IntegralDomain.lean#L118-L154)

Mathlib then counts by exact order. Put $c=|G|$ and let $N(d)$ count the elements of order $d$. For an attained $d$, the $d$ powers of an element of order $d$ fill the set of solutions of $x^d=1$. Each divisor $m$ of $d$ is attained by a power of that element. Partition the solutions by order and use $\sum_{m\mid d}\varphi(m)=d$. Induction subtracts the proper-divisor terms to give $N(d)=\varphi(d)$ whenever $d$ is attained. Now $c=\sum_{d\mid c}N(d)$ because each order divides $c$. If some divisor of $c$ were missing, the sum of the corresponding positive totients over the remaining divisors would be strictly less than $c$. Hence $N(c)=\varphi(c)>0$, and `isCyclic_of_orderOf_eq_card` turns a witness into cyclicity. This counting proof works for any finite group satisfying the given solution bounds. [Mathlib/GroupTheory/SpecificGroups/Cyclic.lean:59–149](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/GroupTheory/SpecificGroups/Cyclic.lean#L59-L149)

**The generator in the quadratic-character arguments [Lean, read].** For a finite field $F$ of odd characteristic let $q=|F|$ and $m=\lfloor q/2\rfloor>0$, so $2m=q-1$. `FiniteField.unit_isSquare_iff` obtains `IsCyclic.exists_generator` at the type $F^\times$. Integer powers are converted to natural powers by taking remainders modulo the generator's order. For the given unit $a=g^n$ the reverse implication assumes $a^m=1$, so $g^{nm}=1$. `orderOf_eq_card_of_forall_mem_zpowers` uses equality of the subgroup of powers with the full group, and `Nat.card_units` counts all field elements except zero. `orderOf_dvd_of_pow_eq_one` applies at $g$ and the exponent $nm$: it uses divisibility by the minimal period of multiplication by $g$ at $1$. Thus $2m\mid nm$, and cancellation of $m>0$ gives $n=2j$, with $g^j$ the square root. [Mathlib/FieldTheory/Finite/Basic.lean:801–834](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Basic.lean#L801-L834)

`FiniteField.isSquare_iff` passes `Units.mk0 a ha` to the unit test, where `ha` proves that $a$ is nonzero. This yields the test in `quadraticCharFun_eq_pow_of_char_ne_two` and thus its unprimed integer-valued wrapper `quadraticChar_eq_pow_of_char_ne_two`. In `quadraticChar_neg_one` that wrapper receives $a=-1$ and the proof `neg_ne_zero.mpr one_ne_zero`. The primed wrapper casts the character value into its own field and allows zero. In `quadraticChar_card_card` it receives the second field $F'$, the odd-characteristic proof `hF'`, and $a=\chi_F(-1)\cdot |F|$ cast into $F'$. In `quadraticChar_two` the same primed formula receives $a=2$ in $F$. The existing archive reader `Cond.chi_neg_one` applies the minus-one result in $F=\mathbb Z/p\mathbb Z$ before casting the integer value into the characteristic-zero coefficient field. The surrounding Gauss-sum and Jacobi reciprocity results are those of §§5.3.1.3–5.3.1.5. [Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean:87–91,181–195,257–265](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean#L181-L195) · [Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean:77–90](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean#L77-L90)

The cyclotomic integer-ring and host residue-field constructions retain their earlier reading boundaries. The [source ledger](../sources/SOURCES.md#chapter-5-cyclic-multiplicative-groups) records the pinned archive and the precise scope of the proof reading.

### 5.3.1.7 Trace pairings and the additive input to Gauss sums

**Motivation.** The quadratic Gauss sum of §5.3.1.3 couples two characters. The multiplicative character detects squares. The additive character provides cancellation after every nonzero dilation. On the prime field it is easy to obtain such a character by exponentiating a primitive root of unity. On an extension field, the trace supplies an exponent in the prime field. Varying the trace functional gives every additive character.

**Examples [Expository].** Use the [finite-field trace formula](#5318-why-the-finite-field-trace-is-a-frobenius-sum) $T(x)=\sum_{j=0}^{f-1}x^{p^j}$ on $\mathbb F_{p^f}$. In a basis $(e_i)$ the trace matrix has entries $T(e_i e_j)$. The dual basis $(d_j)$ satisfies $T(e_i d_j)=\delta_{ij}$.

1. In $\mathbb F_9=\mathbb F_3[i]$ with $i^2=-1$, the defining polynomial $X^2+1$ has no root in $\mathbb F_3$. Cubing sends $i$ to $-i$, so $T(u+vi)=2u$. The traces of $1,i,i^2$ are $2,0,1$. In the basis $(1,i)$ the trace matrix is $\begin{pmatrix}2&0\\0&1\end{pmatrix}$, its own inverse over $\mathbb F_3$. The dual basis is $(2,i)$. For $b=r+si$, the trace exponent at $x=u+vi$ is $T(bx)=2ru+sv$. For $b=0$ the character kernel has size nine. For $r\ne0$ choose any of the three values of $v$ and solve $u=-sv/(2r)$. For $r=0$ and $s\ne0$ take $v=0$ with $u$ arbitrary. Thus all eight nontrivial characters have kernels of size three. In particular, $i\ne 0$ has trace zero.

2. In $\mathbb F_{16}=\mathbb F_2[t]$ take $t^4=t+1$. The polynomial $X^4+X+1$ has no root in $\mathbb F_2$, and division by the sole monic irreducible quadratic $X^2+X+1$ leaves remainder $1$. Thus it is irreducible. For $T(x)=x+x^2+x^4+x^8$ we obtain $T(1)=0$ and $T(t)=0$, using $t^4=t+1$ and $t^8=t^2+1$. Squaring preserves trace by $x^{16}=x$. The successive squares of $t^3$ are $t^6=t^3+t^2$, $t^{12}=t^3+t^2+t+1$ and $t^{24}=t^3+t$. Adding these to $t^3$ gives $1$. Also $t^5=t^2+t$, so the traces of $1,t,\ldots,t^6$ are $0,0,0,1,0,0,1$. Consequently

   $$
   M=\begin{pmatrix}0&0&0&1\\0&0&1&0\\0&1&0&0\\1&0&0&1\end{pmatrix},
   \qquad M^{-1}=\begin{pmatrix}1&0&0&1\\0&0&1&0\\0&1&0&0\\1&0&0&0\end{pmatrix}.
   $$

   Multiplying the displayed matrices gives the identity over $\mathbb F_2$. The inverse columns give the dual basis $(1+t^3,t^2,t,1)$. For $b=r+st+ut^2+vt^3$ and $x=x_0+x_1t+x_2t^2+x_3t^3$ the exponent is $v x_0+u x_1+s x_2+(r+v)x_3$. If $b=0$ the kernel has size sixteen. Otherwise the coefficient vector is nonzero. Solving for the first coordinate with coefficient $1$ leaves three freely chosen bits, hence size eight for each of the fifteen nontrivial characters. Here the characteristic divides the degree and the trace vanishes on the prime field, yet $T(t^3)=1$.

**Definitions.** Let $F=\mathbb F_{p^f}$ and let $T=\operatorname{Tr}_{F/\mathbb F_p}$. The trace of $x$ is the linear-algebra trace of multiplication by $x$. The trace pairing is the symmetric $\mathbb F_p$-bilinear form $B(b,x)=T(bx)$. Fix a field $C$ containing $\zeta$ of order $p$, for example $\exp(2\pi i/p)$ in $\mathbb C$. Write $\lambda(t)=\zeta^k$ for an integer representative $k$ of $t\in\mathbb F_p$. Its kernel is zero since $\zeta$ has order $p$. An additive character is a homomorphism $(F,+)\to C^\times$. Its multiplicative shift by $a$ sends $x$ to $\psi(ax)$. Mathlib calls a character primitive when every shift by $a\ne0$ is nontrivial. Over a field this is equivalent to nontriviality, since nonzero dilations are bijections.

**Lemma (trace duality and additive characters) [Expository].** The form $B$ is nondegenerate. With $\zeta$ fixed, every additive character has a unique expression $\psi_b(x)=\lambda(T(bx))$ with $b\in F$. Addition of parameters corresponds to multiplication of characters. The kernel for $b=0$ is $F$. For $b\ne0$ it is the hyperplane $b^{-1}\ker T$ of size $p^{f-1}$. Two nonzero parameters have the same kernel exactly when they are nonzero prime-field multiples of one another. The intersection of all kernels is $\{0\}$.

**Proof.** The sum-of-conjugates formula gives the trace polynomial above. It is monic of degree $p^{f-1}<p^f$, so it cannot vanish at every element of $F$. Choose $w$ of nonzero trace. For $b\ne0$, the test point $x=w/b$ gives $B(b,x)=T(w)\ne0$. Hence $b\mapsto B(b,-)$ injects $F$ into its linear dual and is an isomorphism by equality of dimensions. In particular the inverse images of the coordinate functionals of $(e_j)$ form the trace-dual basis $(d_j)$.

For any additive character $\psi$, the relation $px=0$ gives $\psi(x)^p=1$. The $p$ distinct powers of $\zeta$ exhaust the roots of $X^p-1$ in $C$. Thus $\lambda^{-1}\psi$ is an additive map to $\mathbb F_p$, and repeated addition makes it $\mathbb F_p$-linear. Duality gives its unique trace representative. Explicitly, if $\psi(e_j)=\lambda(c_j)$, then $b=\sum_j c_j d_j$. Bilinearity gives $\psi_{b+b'}=\psi_b\psi_{b'}$.

Since $\lambda$ has kernel zero, $\psi_b(x)=1$ exactly when $B(b,x)=0$. For $b\ne0$ this functional is onto the one-dimensional prime field, so its kernel has dimension $f-1$. Two nonzero linear functionals with the same kernel both induce isomorphisms from the same one-dimensional quotient to $\mathbb F_p$, so one is a nonzero scalar multiple of the other. Conversely a nonzero scalar preserves the kernel. Trace duality transfers this criterion to the parameters. For $x\ne0$, take $b=w/x$ to see that some character detects $x$. On scalars $T(c)=fc$, so $p\mid f$ kills the restriction to scalars while the polynomial argument still gives surjectivity on $F$. For $f>1$ the trace kernel contains nonzero elements. [Conrad, *Finite Fields*, Theorem 4.6, pp. 9–10](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf) · [Stacks Project, Tag 0BIL](https://stacks.math.columbia.edu/tag/0BIL)

**Gauss-sum input [Expository].** Extend a multiplicative character $\chi$ by zero at $0$ and write $G(\chi,\psi_b)=\sum_{x\in F}\chi(x)\psi_b(x)$. For $b\ne0$, translation by a point where $\psi_b$ differs from $1$ multiplies the additive sum by a scalar unequal to $1$ and preserves the sum. Thus $\sum_x\psi_b(x)=0$. For $b=0$ and nontrivial $\chi$, the Gauss sum is zero by multiplicative translation on $F^\times$. For $b\ne0$, the substitution $y=bx$ gives $G(\chi,\psi_b)=\chi(b)^{-1}G(\chi,\psi_1)$.

To apply the product identity from §5.3.1.3, expand $G(\chi,\psi_b)G(\chi^{-1},\psi_{-b})$ with nontrivial $\chi$ and $b\ne0$. Put $x=ty$ for the two summation variables $x,y\ne0$. For $t=1$ the inner sum $\sum_{y\ne0}\psi_b((t-1)y)$ is $|F|-1$, and for $t\ne1$ it is $-1$ by additive cancellation. Since $\sum_{t\in F^\times}\chi(t)=0$, the product equals $|F|$. This is nonzero in $C$ because in characteristic $p$ the polynomial $X^p-1=(X-1)^p$ could have no root of order $p$. For nontrivial quadratic $\chi$ the shift by $-1$ gives $G(\chi,\psi_b)^2=\chi(-1)|F|$.

For a numerical check in $\mathbb F_9$, the nonzero squares are $1,-1,-i,i$, obtained respectively from the four pairs $\pm1,\pm i,\pm(1+i),\pm(1-i)$. For real coordinates $u=0,1,2$ respectively, the sum of the quadratic sign over the three imaginary coordinates is $2,-1,-1$. At $b=1$ the exponent is $2u$, giving $2-\zeta^2-\zeta=3$ in $\mathbb C$. Every $b\ne0$ then gives $3\chi(b)$ by the shift formula.

**How Mathlib supplies the input [Lean, read].** `FiniteField.trace_to_zmod_nondegenerate` installs primality of the characteristic so `ZMod` is a field. It rewrites the abstract trace form as $T(ab)$ and uses nondegeneracy to contradict $a\ne0$ if all pairings vanish. `traceForm_nondegenerate` applies the determinant criterion. The determinant proof changes basis from a separable power basis. After scalar extension the trace matrix there is the embedding Vandermonde matrix times its transpose. Distinct embeddings have distinct values on the generator, making the Vandermonde determinant nonzero. The finite-field polynomial proof above reaches the same conclusion. [Mathlib/FieldTheory/Finite/Trace.lean:37–56](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Trace.lean#L37-L56) · [Mathlib/RingTheory/Trace/Basic.lean:460–507](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L460-L507)

The cyclotomic extension instance transports nonvanishing of the order to the splitting field, extracts a root from the split positive-degree polynomial and applies the cyclotomic-root criterion. The root supplies the existence field at the singleton index. The splitting-field generation identity supplies the other field of the instance. `zeta` takes the witness from `exists_isPrimitiveRoot`, `zeta_spec` takes its choice specification, and `zeta_pow` projects the power identity. `primitiveZModChar` exponentiates this same root by the residue representative. Its proof of primitivity uses injectivity of the powers on representatives in range. In `FiniteField.primitiveChar`, distinct characteristics imply that $p$ is nonzero in the coefficient field, whether its characteristic is zero or another prime. The proof composes the cyclic character at order $p$ with $T$. At $a=1$ the nondegeneracy lemma gives a point of nonzero trace. The cyclic character's kernel criterion makes the composite nontrivial there. `IsPrimitive.of_ne_one` then uses inverse dilation. The construction gives $\psi_1$ for the chosen root. The classification and hyperplane counts are the textbook deductions above. [Mathlib/NumberTheory/Cyclotomic/Basic.lean:649–687](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Cyclotomic/Basic.lean#L649-L687) · [Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean:85–107](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean#L85-L107) · [Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean:138–230](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean#L138-L230)

**Actual consumers [Lean, read].** In `Char.card_pow_card` the finite fields $F,F'$ have distinct characteristics and $F'$ has odd characteristic. The nontrivial quadratic character into $F'$ is transported injectively into `CyclotomicField ψ.n F'`. The proof takes `ψ.char` from `FiniteField.primitiveChar F F' hch₁` and supplies `ψ.prim` to `gaussSum_sq`. The resulting square identity is the input to `Char.card_pow_char_pow`. The quadratic-character cardinality comparison uses this route on the way to the prime Legendre calculation and then Jacobi reciprocity in §5.3.1.4. The supplement at $2$ takes `primitiveZModChar 8 F` directly on $\mathbb Z/8\mathbb Z$. Its proof uses the cyclic kernel test to derive $\tau^4=-1$ for $\tau=\psi_8(1)$. [Mathlib/NumberTheory/GaussSum.lean:283–319,340–401](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/GaussSum.lean#L283-L401) · [Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean:77–99](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean#L77-L99)

**Host archive and conditional restatement.** In archive A2, `Cond.gs` and `Cond.gs_sq` use a supplied $p$th root of unity in the characteristic-zero field $K$, source $\mathbb Z/p\mathbb Z$, and the integer quadratic character cast to $K$. Only `Cond.gs_sq` requires the root to be primitive. The actual primitive proof is `AddChar.zmodChar_primitive_of_primitive_root`. On this source the trace is the identity, so the formula for $\psi_1$ agrees for the supplied root. [Host Gauss-sum proof](#5313-the-second-host-sign-from-a-quadratic-gauss-sum)

Separately [Expository], given the reduced root $\eta$ of order $M$ from §5.3.1.2, the character `zmodChar` on $\mathbb Z/M\mathbb Z$ with root $\eta$ has kernel zero by `zmod_char_eq_one_iff`. The archive itself makes its reduction comparison by `zO_sub_mem_iff`. [Host root reduction](#5312-frobenius-and-inertia-in-the-cyclotomic-host)

**Reading boundary.** Archive A2 SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` fix the readings. The source map lists local R3 bodies and named inputs retained at interface level. Multiplicative cyclicity, Euler's criterion and Jacobi reciprocity are used through the preceding sections. [Source map](../sources/SOURCES.md#trace-pairings-and-additive-characters-5317)

### 5.3.2 Subgroup projection (`PsiA`, `GmA`, `SigA`) and the two hypothesis packages (`EAtH`, `CoreAtH`)

**Definition 5.2 (`PsiA`, `GmA`, and `SigA`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean:26,30,34,39`).**
Let $A_0 \le H$ be a subgroup, let $\mathrm{Kept}_A \subseteq \widehat{E_0 \times H}$ be a finite
subset (`keptA Λ H`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean:24`), and let $c_{\mathrm{top}} \in \mathbb R$ (instantiated as
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
     bridge `ReadsKept`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean:67,74,81`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean:29`, and
     `src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:43`):** the $11$-clause Hermitian/Hida divisibility-and-slope
     package `SizeData₂` (`src/Formalism/SizeWindowBrackets/SChain.lean:17`, opened in Part II, Chapters 6–10) whose weighted-mean
     gap is bounded by $x^{\mathrm{CErr}(C_c)\varepsilon}\,\mathcal E_{\mathrm{win}}$ (paired with
     `ReadsKept` on `CoreAtH` matching `keptA` to the host characters), where
     $\mathrm{CErr}(C_c) = e_{\mathrm{Div}} + e_{\mathrm{Loss}} + 3 \le e_D + e_L + 3$
     (`src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:19`) and
     $$\mathcal E_{\mathrm{win}}(x, \varepsilon, n, n_T, n_{T_2}, m, b, k, a_E)
     := n_T a_E + n_T a_E \frac{m^2}{k} + m\,(2 n m b\,x^\varepsilon) + m\,\frac{n_{T_2} k b\,x^{2\varepsilon}}{n^2}$$
     (`errorBracketSizeWindows`, `src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:133`);
   - **Scale windows (`SizesA`, `ThinScales`, `CostWindows`, `RestSize`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean:42` and
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

### 5.3.1.8 Why the finite-field trace is a Frobenius sum

**Motivation.** The preceding subsection evaluates a trace to obtain the exponent of an additive character. The trace starts as the matrix trace of multiplication. Changing from coefficient coordinates to values under embeddings explains why powers of Frobenius can compute the same number.

**Examples [Expository].** Use column vectors throughout.

1. The polynomial $X^2+X+1$ has value $1$ at both elements of $\mathbb F_2$, so it defines $\mathbb F_4=\mathbb F_2[a]$ with $a^2=a+1$. In the basis $(1,a)$, the products for $x=u+va$ are $x$ and $xa=v+(u+v)a$. Thus

   $$
   M_x=\begin{pmatrix}u&v\\v&u+v\end{pmatrix},
   \qquad \operatorname{tr}M_x=v.
   $$

   Squaring gives $x^2=(u+v)+va$, so $x+x^2=v$. The evaluation rows $(1,a)$ and $(1,a+1)$ have determinant $1$ and give the diagonal entries $x,x^2$ over $\mathbb F_4$. In particular $\operatorname{Tr}(1)=0$ and $\operatorname{Tr}(a)=1$.

2. The cubic $X^3-X-1$ takes value $-1$ everywhere on $\mathbb F_3$, so it is irreducible. Write $\mathbb F_{27}=\mathbb F_3[b]$ with $b^3=b+1$ and $b^4=b^2+b$. For $x=u+vb+wb^2$, the products are $x$, $xb=w+(u+w)b+vb^2$ and $xb^2=v+(v+w)b+(u+w)b^2$. In $(1,b,b^2)$,

   $$
   M_x=\begin{pmatrix}u&w&v\\v&u+w&v+w\\w&v&u+w\end{pmatrix},
   \qquad \operatorname{tr}M_x=3u+2w=2w.
   $$

   Cubing sends $b$ to $b+1$. Cubing again gives $b^9=(b+1)^3=b+2$. The three evaluations give

   $$
   \begin{aligned}
   x &= u+vb+wb^2,\\
   x^3 &= (u+v+w)+(v+2w)b+wb^2,\\
   x^9 &= (u+2v+w)+(v+w)b+wb^2.
   \end{aligned}
   $$

   Their sum is $2w$. The evaluation rows $(1,b+j,(b+j)^2)$ for $j=0,1,2$ have Vandermonde determinant $(1)(2)(1)=2$. In these coordinates over $\mathbb F_{27}$ the diagonal entries are $x,x^3,x^9$. Here $\operatorname{Tr}(1)=\operatorname{Tr}(b)=0$ and $\operatorname{Tr}(b^2)=2$.

**Definitions.** For a finite extension $L/K$, let $m_x$ be the $K$-linear map $y\mapsto xy$ and let $\operatorname{Tr}_{L/K}(x)=\operatorname{tr}(m_x)$. An embedding over $K$ is a field map agreeing with the given inclusion of $K$. A simple extension $K(a)/K$ of degree $n$ has power basis $(1,a,\ldots,a^{n-1})$. For finite $K$ of cardinality $q$, the relative Frobenius is $\Phi(y)=y^q$.

**Lemma (diagonalization in a split separable power basis) [Expository].** Suppose $L=K(a)$ and the minimal polynomial of $a$ splits into $n=[L:K]$ distinct roots $a_i$ in a field $E$ over $K$. Write $\sigma_i$ for the embedding defined by $a\mapsto a_i$. Over $E$, the matrix of $m_x$ is similar to the diagonal matrix with entries $\sigma_i(x)$.

**Proof.** The presentation $K[T]/(f)$ for the minimal polynomial $f$ identifies embeddings with roots. Send a coefficient column to its evaluations at the $a_i$. The matrix $V$ has entries $a_i^j$, with $0\le j<n$. A column in the kernel gives a polynomial of degree less than $n$ vanishing at $n$ distinct points. Thus $V$ is invertible. Multiplicativity on the power basis gives $VM_x=\operatorname{diag}(\sigma_i(x))V$. Taking the diagonal sum yields the trace after including $K$ into $E$.

**Theorem (embeddings and the finite-field trace) [Lean, read].** Let $L/K$ be finite separable and let $E$ be an algebraically closed field over $K$. For each $x\in L$, the image of $\operatorname{Tr}_{L/K}(x)$ in $E$ is the sum of $\sigma(x)$ over all embeddings $\sigma:L\to E$ over $K$. If $L/K$ is also normal, the trace in $L$ is the sum over $\operatorname{Gal}(L/K)$. For finite fields $K\subset L$, with $q=|K|$ and $n=[L:K]$, this last sum is

$$
\sum_{i=0}^{n-1}x^{q^i}.
$$

**Proof.** Put $F=K(x)$ and $r=[L:F]$. Choosing an $F$-basis of $L$ writes $m_x$ over $K$ as $r$ identical blocks on copies of $F$. Consequently $\operatorname{Tr}_{L/K}(x)=r\operatorname{Tr}_{F/K}(x)$. The lemma computes the latter trace on the simple extension with generator $x$. Each embedding $F\to E$ extends to exactly $r$ embeddings of $L$. To count these, adjoin a finite list of generators of $L/F$ one at a time. At every simple step the transported minimal polynomial splits into distinct roots, one for each possible extension of the preceding embedding. The product of the degrees is $r$. Grouping the sum over $L$ by restriction to $F$ therefore gives the same weighted sum. In particular, the block decomposition and evaluation lemma diagonalize $m_x$ over $E$ even for a proper $K(x)$, with each block's diagonal repeated $r$ times.

For a normal extension take $E$ to be an algebraic closure containing $L$. Every image of $y\in L$ is a root of its minimal polynomial, and all these roots lie in $L$. Thus each embedding takes values in $L$ and is onto by finite dimension. Conversely each automorphism gives an embedding by inclusion. Injectivity of $L\to E$ gives the identity in $L$.

For finite fields, $L$ has $q^n$ elements, all roots of $T^{q^n}-T$ by Lagrange's theorem on $L^\times$ and the identity at zero. This polynomial has derivative $-1$ and splitting field $L$ over $K$, which gives normality and separability. Since $q$ is a power of the characteristic, the binomial identity makes $\Phi$ additive. It is multiplicative and fixes $K$, since $c^q=c$ in $K$. Injectivity and finiteness make it an automorphism. Its $n$th power is the identity. If its $m$th power were the identity for $0<m<n$, then $T^{q^m}-T$, of degree $q^m$, would have $q^n$ distinct roots. Hence the first $n$ powers are distinct. The embedding count with $F=K$ shows that they exhaust the embeddings. Substituting $\Phi^i(x)=x^{q^i}$ gives the stated sum. An individual $x$ may have a shorter orbit of length $d$ dividing $n$. In that case each orbit value appears $n/d$ times. For the prime field $q=p$, this is the trace formula used for the exponent in §5.3.1.7.

**The proof in Mathlib [Lean, read].** `trace_eq_sum_embeddings` uses the power basis of the simple adjoin of $x$. Trace transitivity and the trace of a scalar supply the factor $[L:K(x)]$. On the simple adjoin, `trace_eq_sum_embeddings_gen` uses the negative next coefficient of the characteristic polynomial of multiplication by the generator. That polynomial is its minimal polynomial. Splitting converts the coefficient to a root sum and separability makes the roots distinct, so the root-to-embedding correspondence reindexes the sum. The evaluation lemma gives the diagonalization behind this coefficient calculation. `sum_embeddings_eq_finrank_mul` groups the embeddings into fibers of restriction and counts each fiber by `AlgHom.card`. `trace_eq_sum_automorphisms` reindexes via normality in an algebraic closure and uses injectivity to descend. [Mathlib/RingTheory/Trace/Basic.lean:218–272](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L218-L272)

Mathlib proves the order of the Frobenius endomorphism by the polynomial root bound. `bijective_frobeniusAlgHom_pow` uses that order for injectivity and the bound `card_algHom_le_finrank` for surjectivity. `bijective_frobeniusAlgEquivOfAlgebraic_pow` transfers the bijection to automorphisms using the equivalence for algebraic extensions, which respects powers. `algebraMap_trace_eq_sum_pow` changes the summation index from automorphisms to integers in range and evaluates each iterate. The preceding subsection uses this identity in its textbook proof of trace duality. The library's trace-form proof also consumes the embedding sum when it factors the trace matrix. [Mathlib/FieldTheory/Finite/Basic.lean:327–406](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Basic.lean#L327-L406) · [Mathlib/FieldTheory/Finite/Trace.lean:37–56](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Trace.lean#L37-L56) · [Mathlib/RingTheory/Trace/Basic.lean:444–446](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L444-L446)

**Remarks [Expository].** For $c\in K$, multiplication by $c$ is $cI$, so the trace is $nc$. When the characteristic divides $n$, this vanishes on all scalars. The two examples exhibit nonzero traces on nonscalars. In general, the Frobenius-sum polynomial is monic of degree $q^{n-1}<q^n$, so it takes a nonzero value somewhere in $L$. The trace is then onto by $K$-linearity. [Keith Conrad, *Finite Fields*, Theorems 4.1, 4.6, 5.6 and 5.7, pp. 8–11](https://kconrad.math.uconn.edu/blurbs/galoistheory/finitefields.pdf)

For an inseparable model take $K=\mathbb F_p(t)$ and $L=K(a)$ with $a^p=t$. The polynomial $T^p-t$ is Eisenstein at $t$ over $\mathbb F_p[t]$. In the power basis, multiplication by $a^j$ for $1\le j<p$ sends column $i$ to row $i+j$ modulo $p$, with coefficient $1$ if $i+j<p$ and $t$ otherwise. Every diagonal entry is zero. Multiplication by $1$ has trace $p=0$, so the trace vanishes on the entire basis. In an algebraic closure $T^p-t=(T-a)^p$, giving just one embedding and an unweighted embedding sum of $1$ at $x=1$. Counting all $p$ roots with multiplicity produces identical evaluation rows, so the change of coordinates is singular. In $E[T]/((T-a)^p)$, multiplication by $a$ after scalar extension is multiplication by the residue of $T$. Subtracting the scalar $aI$ gives a nonzero nilpotent operator, which precludes diagonalization. Separability supplies the distinct roots for evaluation, and normality supplies the identification of embeddings with automorphisms. [Stacks Project, Lemma 9.20.7](https://stacks.math.columbia.edu/tag/0BIL)

The general separable power-basis existence theorem used in the trace-pairing determinant proof remains an imported input. Its pinned proof is read in [§5.3.1.9](#5319-primitive-elements-and-power-bases-for-separable-extensions). [Source ledger](../sources/SOURCES.md#finite-field-trace-by-embeddings-5318)

### 5.3.1.9 Primitive elements and power bases for separable extensions

**Motivation.** Two pinned proofs used above take a finite separable extension $E/F$ and silently ask for a single generator. The trace-form determinant in §5.3.1.7 changes basis to the powers $1,\alpha,\ldots,\alpha^{n-1}$ of one element $\alpha$ so that, after extending scalars, the trace matrix becomes a Vandermonde matrix times its transpose. The embedding count in §5.3.1.8 counts the embeddings $E\to L$ over $F$ as roots of the minimal polynomial of that same $\alpha$. In both places Mathlib calls `Field.powerBasisOfFiniteOfSeparable`. The textbook proof of §5.3.1.8 avoided this by adjoining generators one at a time. The library does not avoid it. This subsection reads the pinned proof that such an $\alpha$ exists. The argument has two genuinely different branches. Over an infinite base field one combines two generators as $\alpha+c\beta$ after excluding finitely many bad scalars $c$. Over a finite base field one takes a generator of the cyclic multiplicative group from §5.3.1.6. [Stacks Project, Lemma 9.19.1](https://stacks.math.columbia.edu/tag/030N) · [Stacks Project, Section 9.18](https://stacks.math.columbia.edu/tag/09HY) · [Milne, *Fields and Galois Theory*, v5.10, Theorem 5.1 and Proposition 4.19, pp. 61–62 and 53](https://www.jmilne.org/math/CourseNotes/FT.pdf)

**Examples [Expository].**

1. *The biquadratic field.* Let $E=\mathbb Q(\sqrt2,\sqrt3)$. First, $[E:\mathbb Q]=4$. If $\sqrt3=a+b\sqrt2$ with $a,b\in\mathbb Q$, then $3=a^2+2b^2+2ab\sqrt2$ forces $ab=0$. The case $b=0$ makes $\sqrt3$ rational, and the case $a=0$ gives $3q^2=2p^2$ for coprime integers $p,q$, which is impossible by parity. Thus $\sqrt3\notin\mathbb Q(\sqrt2)$ and the basis $B=(1,\sqrt2,\sqrt3,\sqrt6)$ has four elements.

   Take $\alpha=\sqrt2$, $\beta=\sqrt3$ and the scalar $c=1$, so $\gamma=\sqrt2+\sqrt3$. The powers are
   $$
   \gamma^2=5+2\sqrt6,\qquad
   \gamma^3=(\sqrt2+\sqrt3)(5+2\sqrt6)=5\sqrt2+5\sqrt3+4\sqrt3+6\sqrt2=11\sqrt2+9\sqrt3 .
   $$
   Hence $\gamma^3-9\gamma=2\sqrt2$ and $11\gamma-\gamma^3=2\sqrt3$, so both square roots lie in $\mathbb Q(\gamma)$ and $E=\mathbb Q(\gamma)$. Squaring $\gamma^2-5=2\sqrt6$ gives the minimal polynomial $X^4-10X^2+1$, which has degree $4=[E:\mathbb Q]$ and is therefore irreducible. The four conjugates $\pm\sqrt2\pm\sqrt3$ are distinct, as the separability of the extension requires.

   Writing the power basis $P=(1,\gamma,\gamma^2,\gamma^3)$ in the coordinates of $B$ gives the change-of-basis matrix with columns $1\mapsto(1,0,0,0)$, $\gamma\mapsto(0,1,1,0)$, $\gamma^2\mapsto(5,0,0,2)$ and $\gamma^3\mapsto(0,11,9,0)$:
   $$
   M=\begin{pmatrix}1&0&5&0\\0&1&0&11\\0&1&0&9\\0&0&2&0\end{pmatrix},\qquad
   \det M=1\cdot\bigl(1\cdot(0-18)-0+11\cdot(2-0)\bigr)=4 .
   $$
   The determinant is nonzero, so $P$ is a basis. The inverse change is read off from the identities above, $\sqrt2=\tfrac12(\gamma^3-9\gamma)$, $\sqrt3=\tfrac12(11\gamma-\gamma^3)$ and $\sqrt6=\tfrac12(\gamma^2-5)$:
   $$
   M^{-1}=\begin{pmatrix}1&0&0&-\tfrac52\\[2pt]0&-\tfrac92&\tfrac{11}2&0\\[2pt]0&0&0&\tfrac12\\[2pt]0&\tfrac12&-\tfrac12&0\end{pmatrix}.
   $$
   For instance the $\sqrt2$ column gives $M\,(0,-\tfrac92,0,\tfrac12)^{T}=(0,\,-\tfrac92+\tfrac{11}2,\,-\tfrac92+\tfrac92,\,0)^{T}=(0,1,0,0)^{T}$.

   The bad scalars of the proof below are the quotients $-(\alpha'-\alpha)/(\beta'-\beta)$ over the conjugates $\alpha'=\pm\sqrt2$ and $\beta'=\pm\sqrt3$. With $\beta'=-\sqrt3$ they are $0$ for $\alpha'=\sqrt2$ and $-\sqrt{2/3}$ for $\alpha'=-\sqrt2$. Only $c=0$ is a rational bad scalar, and indeed $\gamma=\alpha+0\cdot\beta=\sqrt2$ generates a proper subfield. Every nonzero rational $c$ works, and $c=1$ is Milne's choice.

2. *A finite field of degree three.* Let $E=\mathbb F_8=\mathbb F_2[t]$ with $t^3=t+1$. The cubic $X^3+X+1$ has no root in $\mathbb F_2$, so it is irreducible. The multiplicative group has order $7$, a prime, so every element other than $0$ and $1$ generates it. For $t$ itself,
   $$
   t^3=t+1,\quad t^4=t^2+t,\quad t^5=t^2+t+1,\quad t^6=t^2+1,\quad t^7=1 .
   $$
   The seven powers exhaust $E^\times$, and $E=\mathbb F_2(t)$ with power basis $(1,t,t^2)$. This is the finite-base branch of the proof: the generator of the cyclic group is the primitive element.

   The same branch applies to the generator $u=t^6=t^2+1$. Its Frobenius conjugates are $u^2=t^{12}=t^5=t^2+t+1$ and $u^4=t^{24}=t^3=t+1$. The elementary symmetric functions are $u+u^2+u^4=1$, $u\cdot u^2+u\cdot u^4+u^2\cdot u^4=t^{4}+t^{2}+t=(t^2+t)+t^2+t=0$ and $u\cdot u^2\cdot u^4=t^{14}=1$, so the minimal polynomial of $u$ is $X^3+X^2+1$, the other irreducible cubic over $\mathbb F_2$. In the coordinates of $(1,t,t^2)$ the power basis $(1,u,u^2)$ has columns $(1,0,0)$, $(1,0,1)$ and $(1,1,1)$:
   $$
   N=\begin{pmatrix}1&1&1\\0&0&1\\0&1&1\end{pmatrix},\qquad \det N=1\cdot(0-1)=1\ \text{in}\ \mathbb F_2,
   \qquad
   N^{-1}=\begin{pmatrix}1&0&1\\0&1&1\\0&1&0\end{pmatrix},
   $$
   since $t=u+u^2$ and $t^2=1+u$. A direct check gives $N\,(0,1,1)^{T}=(0,1,0)^{T}$ and $N\,(1,1,0)^{T}=(0,0,1)^{T}$. Here the base field has only two scalars, so the infinite-base argument of excluding finitely many $c$ is unavailable, and the cyclic argument is what the pinned proof uses.

3. *An inseparable failure.* Let $K=\mathbb F_p(s,t)$ with independent indeterminates and $L=K(\alpha,\beta)$ with $\alpha^p=s$ and $\beta^p=t$. The polynomial $X^p-s$ is Eisenstein at the prime $s$ of $\mathbb F_p(t)[s]$, so $[K(\alpha):K]=p$ by Gauss's lemma. Next, $K(\alpha)=\mathbb F_p(\alpha,t)$ is the fraction field of $\mathbb F_p(\alpha)[t]$, in which $t$ is prime, and $X^p-t$ is Eisenstein at $t$ there; hence $[L:K(\alpha)]=p$ and $[L:K]=p^2$. Every $\gamma\in L$ satisfies $\gamma^p\in K$. Indeed, write $\gamma=\sum_{i,j<p}a_{ij}\alpha^i\beta^j$ with $a_{ij}\in K$; the $p$th power map is additive and multiplicative in characteristic $p$ and maps $K$ into itself, so $\gamma^p=\sum_{i,j}a_{ij}^p s^it^j\in K$. Hence $[K(\gamma):K]\le p<p^2$ and no primitive element exists. The remarks below locate the exact step of the proof that fails.

**Definitions.** Let $E/F$ be a field extension. For $\alpha\in E$, $F(\alpha)$ denotes the smallest intermediate field containing $\alpha$, written $F\langle\alpha\rangle$ in Mathlib and realized there as an `IntermediateField F E`. The extension is *simple*, and $\alpha$ is a *primitive element*, if $F(\alpha)=E$; Mathlib writes this as $F\langle\alpha\rangle=\top$. For $\alpha,\beta\in E$ the field $F(\alpha,\beta)$ is $F\langle\alpha\rangle\langle\beta\rangle$ with scalars restricted back to $F$, which Mathlib proves equal to $F\langle\alpha,\beta\rangle$ (`adjoin_simple_adjoin_simple`). A *power basis* of $E$ over $F$ consists of a generator $g$ and a dimension $d$ such that $1,g,\ldots,g^{d-1}$ is an $F$-basis of $E$; this is the structure `PowerBasis F E` with fields `gen`, `dim` and `basis`. An extension is *separable* if the minimal polynomial of every element has distinct roots in a splitting field; `Algebra.IsSeparable F E` is this condition for all elements at once. Throughout, $E/F$ is finite-dimensional. [Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:578–579](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean#L578-L579)

**Lemma A (finite base field; `Field.exists_primitive_element_of_finite_top`, `_of_finite_bot`) [Lean, read].** If $E$ is a finite field, then for any subfield $F$ there is $\alpha\in E$ with $F(\alpha)=E$. In particular, if $F$ is finite and $E/F$ is finite-dimensional, then $E/F$ is simple.

*Proof.* By §5.3.1.6 the group $E^\times$ is cyclic; the pinned proof takes a generator $\alpha$ from `IsCyclic.exists_generator`. Let $x\in E$. If $x=0$ it lies in $F(\alpha)$ as in every subfield. Otherwise $x$ is a unit, hence $x=\alpha^n$ for some integer $n$, and integer powers of $\alpha$ stay in the field $F(\alpha)$ (`zpow_mem`). Thus $E\subseteq F(\alpha)$. The second statement follows because a finite-dimensional space over a finite field is finite (`Module.finite_of_finite`). $\square$ [Mathlib/FieldTheory/PrimitiveElement.lean:54–72](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L54-L72)

**Lemma B (excluding the bad scalars; `primitive_element_inf_aux_exists_c`) [Lean, read].** Let $F$ be an infinite field, $\varphi:F\to E'$ a ring map into a field, $\alpha,\beta\in E'$ and $f,g\in F[X]$. There is $c\in F$ such that
$$
-\frac{\alpha'-\alpha}{\beta'-\beta}\ne\varphi(c)
\quad\text{for every root }\alpha'\text{ of }f^{\varphi}\text{ and every root }\beta'\text{ of }g^{\varphi}\text{ in }E'.
$$

*Proof.* The roots of $f^\varphi$ and of $g^\varphi$ in $E'$ form two finite multisets. The displayed quotients, one for each pair, form a finite set $S\subseteq E'$. Since $\varphi$ is injective, its preimage $\varphi^{-1}(S)$ is a finite subset of $F$. An infinite set is not contained in a finite one, so some $c\in F$ lies outside it (`Infinite.exists_notMem_finset`). $\square$

The quantifiers matter here. The scalar $c$ is chosen once, after $f,g,\alpha,\beta$ and the target field $E'$ are fixed, and it then works for all pairs of roots simultaneously. In Lean division by zero is zero, so the pairs with $\beta'=\beta$ contribute the value $0$ to $S$; this only enlarges the finite set. [Mathlib/FieldTheory/PrimitiveElement.lean:83–95](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L83-L95)

**Lemma C (two generators over an infinite field; `primitive_element_inf_aux`) [Lean, read].** Let $F$ be infinite, let $E/F$ be separable, and let $\alpha,\beta\in E$. Then there is $\gamma\in E$ with $F(\alpha,\beta)=F(\gamma)$. Only the separability of $\beta$ and the integrality of $\alpha$ are used.

*Proof.* Let $f$ and $g$ be the minimal polynomials of $\alpha$ and $\beta$ over $F$. Let $E'$ be a splitting field of $g$ over $E$, with inclusion $\iota:E\to E'$. Apply Lemma B to the composite $F\to E\to E'$, the points $\iota\alpha,\iota\beta$ and the polynomials $f,g$, and let $c$ be the resulting scalar. Put $\gamma=\alpha+c\beta$. It suffices to show $\beta\in F(\gamma)$: then $\alpha=\gamma-c\beta\in F(\gamma)$, so $F(\alpha,\beta)\subseteq F(\gamma)$, and the reverse inclusion holds because $\gamma\in F(\alpha,\beta)$.

Consider the two polynomials $f(\gamma-cX)$ and $g(X)$. Both have coefficients in $F(\gamma)$, and both vanish at $\beta$, since $f(\gamma-c\beta)=f(\alpha)=0$. Let $h\in E[X]$ be their greatest common divisor computed over $E$, and $p\in F(\gamma)[X]$ the greatest common divisor computed over $F(\gamma)$. The Euclidean algorithm commutes with field extension (`gcd_map`, read in §5.3.1.11), so $p$ maps to $h$ under $F(\gamma)\to E$. We claim $h$ is linear.

First, $h\ne0$ because $g\ne0$. Second, $h$ divides $g$, and $g$ is separable because $\beta$ is; a divisor of a separable polynomial is separable (`separable_gcd_right`). Third, $h(\beta)=0$ since both polynomials vanish at $\beta$ (`eval_gcd_eq_zero`). Fourth, $h$ splits over $E'$ because $g$ does and $h$ divides $g$. Fifth, every root $x\in E'$ of $h$ equals $\iota\beta$. Indeed, $x$ is a root of $g$, so $x=\beta'$ for one of the conjugates of $\beta$, and $\gamma-cx$ is a root of $f$, so $\gamma-cx=\alpha'$ for one of the conjugates of $\alpha$. If $x\ne\iota\beta$, then from $\alpha+c\beta-c\beta'=\alpha'$ we solve
$$
\varphi(c)=\frac{\alpha'-\alpha}{\beta-\beta'}=-\frac{\alpha'-\alpha}{\beta'-\beta},
$$
contradicting the choice of $c$ in Lemma B. A separable polynomial that splits, vanishes at $\beta$, and has no root other than $\beta$ is a constant times $X-\beta$ (`eq_X_sub_C_of_separable_of_root_eq`). Thus $h=\lambda(X-\beta)$ with $\lambda\ne0$ its leading coefficient.

Transporting back, $p$ has degree one with coefficients $p_0,p_1\in F(\gamma)$ and $p_1\beta+p_0=0$ in $E$, so $\beta=-p_0/p_1$ lies in $F(\gamma)$. $\square$ [Mathlib/FieldTheory/PrimitiveElement.lean:100–167](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L100-L167) · [Mathlib/FieldTheory/Separable.lean:477–495](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Separable.lean#L477-L495)

The field tower in this proof is $F\subseteq F(\gamma)\subseteq F(\alpha,\beta)\subseteq E\subseteq E'$. The greatest common divisor is formed over $F(\gamma)$, its roots are examined over $E'$, and the conclusion is read off over $E$. Separability is required of $\beta$ alone: it makes $h$ separable, so that the single root $\beta$ has multiplicity one and $h$ is linear rather than a higher power of $X-\beta$. [§5.3.1.11](#53111-the-separable-greatest-common-divisor-in-the-primitive-element-proof) opens these steps: the Euclidean algorithm under field maps, the Bézout identities behind separability and the simple-root argument, with every coefficient map of this tower named.

**Theorem (primitive element theorem; `Field.exists_primitive_element`) [Lean, read].** Let $E/F$ be a finite-dimensional separable extension of fields. Then there exists $\alpha\in E$ with $F(\alpha)=E$. Explicitly: there is one $\alpha\in E$ such that every $x\in E$ lies in $F(\alpha)$.

*Proof.* The pinned proof splits on whether $F$ is finite.

If $F$ is finite, Lemma A applies directly, since $E$ is finite-dimensional over $F$.

If $F$ is infinite, consider the predicate $P(K)$ on intermediate fields $F\subseteq K\subseteq E$: "there is $\alpha\in E$ with $F(\alpha)=K$". The bottom field $F$ satisfies $P$ with $\alpha=0$ (`adjoin_zero`). If $P(K)$ holds with witness $\alpha$ and $x\in E$, then $K(x)=F(\alpha)(x)=F(\alpha,x)$ by `adjoin_simple_adjoin_simple`, and Lemma C applied to $\alpha$ and $\beta=x$ gives $\gamma$ with $F(\alpha,x)=F(\gamma)$, so $P(K(x))$ holds. Since $E/F$ is finite-dimensional, every intermediate field is finitely generated, so it is reached from $F$ by finitely many simple adjunctions (`induction_on_adjoin`, which reduces to a `Finset` induction in `induction_on_adjoin_finset`). Hence $P(E)$ holds. $\square$ [Mathlib/FieldTheory/PrimitiveElement.lean:206–221](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L206-L221) · [Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:301–305](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean#L301-L305) · [Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:686–699](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean#L686-L699)

The two branches are not interchangeable. The infinite branch needs a scalar outside a finite subset of $F$ at each step, which a finite field cannot always supply; the finite branch needs a cyclic multiplicative group, which an infinite field never has. The separability hypothesis on $E/F$ is consumed only in the infinite branch, element by element, through Lemma C.

**Corollary (power basis; `Field.powerBasisOfFiniteOfSeparable`) [Lean, read].** A finite-dimensional separable extension $E/F$ has a power basis: for the primitive element $\alpha$ of the theorem, $1,\alpha,\ldots,\alpha^{n-1}$ is an $F$-basis of $E$, where $n$ is the degree of the minimal polynomial of $\alpha$, and $n=[E:F]$.

*Proof.* Choose $\alpha$ by the theorem. Since $\alpha$ is integral, the simple extension $F(\alpha)$ has the power basis `adjoin.powerBasis`, whose generator is $\alpha$, whose dimension is the degree of the minimal polynomial, and whose basis vectors are the powers of $\alpha$; Mathlib transports it from the polynomial quotient presentation `AdjoinRoot.powerBasis` along the isomorphism $F[X]/(\mathrm{minpoly})\cong F(\alpha)$. Finally the equality $F(\alpha)=\top$ gives an $F$-algebra isomorphism $F(\alpha)\cong E$ (`equivOfEq` followed by `topEquiv`), and `PowerBasis.map` carries the power basis across. Comparing dimensions gives $n=[E:F]$ (`adjoin.finrank`). $\square$ [Mathlib/FieldTheory/PrimitiveElement.lean:223–231](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L223-L231) · [Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:440–470](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean#L440-L470)

**Where the trace proofs call it [Lean, read].** Three pinned declarations consume the corollary.

1. *Embedding count.* `AlgHom.natCard_of_splits` and `AlgHom.card` prove that a finite separable $E/F$ has exactly $[E:F]$ embeddings over $F$ into a field $L$ in which all minimal polynomials split, in particular into an algebraic closure. The proof applies `AlgHom.natCard_of_powerBasis` to the power basis of the corollary: embeddings of a simple extension correspond to roots of the minimal polynomial of the generator, and separability makes these roots distinct, so there are exactly `pb.dim` of them. This count is the input `AlgHom.card L F E` in `sum_embeddings_eq_finrank_mul`, which gives the fiber size $[L:K(x)]$ in the proof of `trace_eq_sum_embeddings` in §5.3.1.8. There the power basis of $K(x)$ itself comes from `adjoin.powerBasis` and needs no primitive element; the primitive element is needed for the top extension over $K(x)$. [Mathlib/FieldTheory/PrimitiveElement.lean:346–362](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L346-L362) · [Mathlib/FieldTheory/Separable.lean:767–779](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Separable.lean#L767-L779) · [Mathlib/RingTheory/Trace/Basic.lean:235–262](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L235-L262)

2. *Trace-form determinant.* `det_traceForm_ne_zero` takes an arbitrary basis $b$ of $E$ over $F$ and sets `pb := Field.powerBasisOfFiniteOfSeparable`. It rewrites the matrix of the trace form in $b$ as $C^{T}\,T\,C$ with $C$ the change-of-basis matrix between $b$ and the power basis and $T$ the trace matrix of the power basis. The determinant of $C$ is a unit, as in the matrices $M$ and $N$ of the examples, so it suffices that $\det T\ne0$. That is `det_traceMatrix_ne_zero'`, which extends scalars to an algebraic closure, indexes the embeddings by `Fin pb.dim` using `AlgHom.card` a second time, and writes $T$ as a Vandermonde matrix in the values $\sigma(\alpha)$ times its transpose. Distinct embeddings take distinct values on the generator, so the Vandermonde determinant is nonzero. [Mathlib/RingTheory/Trace/Basic.lean:462–507](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L462-L507)

3. *Nondegeneracy and the additive character.* `traceForm_nondegenerate` applies the determinant criterion to the standard basis, and §5.3.1.7 recorded how `FiniteField.trace_to_zmod_nondegenerate` and `FiniteField.primitiveChar` consume it on the way to the quadratic Gauss sum. For these finite-field consumers only the finite branch of the theorem, Lemma A, is ever exercised, although the declaration is stated and proved for all finite separable extensions.

**Remarks [Expository].**

1. *Which hypothesis the inseparable example violates.* In Example 3 the hypothesis `Algebra.IsSeparable F E` fails: the minimal polynomial $X^p-s$ of $\alpha$ has derivative zero and the single root $\alpha$ with multiplicity $p$. The proof of Lemma C breaks at its second step. With $\gamma=\alpha+c\beta$ and $c\in K$ one computes
   $$
   f(\gamma-cX)=(\gamma-cX)^p-s=\gamma^p-c^pX^p-s=(s+c^pt)-c^pX^p-s=-c^p\,g(X),
   $$
   so the greatest common divisor is $g=X^p-t=(X-\beta)^p$ itself, of degree $p$, and the separability input to `eq_X_sub_C_of_separable_of_root_eq` is unavailable. The conclusion of Lemma C also fails: $\gamma^p=s+c^pt\in K$, so $[K(\gamma):K]\le p$ while $[K(\alpha,\beta):K]=p^2$. The fields $K(\alpha+c\beta)$ for distinct $c\in K$ are pairwise distinct, since a common field would contain $(c-c')\beta$ and hence $\alpha$ and $\beta$. So there are infinitely many intermediate fields, in accordance with Steinitz's criterion `exists_primitive_element_iff_finite_intermediateField`, which is proved in the same pinned file but not used by the trace consumers. In the same example the trace form is identically zero, as §5.3.1.8 showed for the degree-$p$ case, so the determinant criterion has nothing to work with.

2. *Hypotheses in the classical statements.* Milne's Theorem 5.1 requires only that all generators after the first be separable, and the pinned Lemma C uses exactly that much at each step, although the pinned theorem is stated under the global hypothesis on $E/F$. The Stacks Project proves the infinite case by choosing a vector outside finitely many proper subspaces, namely the kernels of $\sigma_i-\sigma_j$ for distinct embeddings into an algebraic closure. The pinned proof chooses a scalar outside a finite set of root quotients instead. Both rest on the same fact that an infinite field cannot be covered by finitely many excluded values. The finite case is credited by both sources and by the pinned `@[stacks 09HY]` and `@[stacks 030N]` attributes to the cyclicity of the multiplicative group. [Stacks Project, Lemma 9.19.1](https://stacks.math.columbia.edu/tag/030N) · [Stacks Project, Section 9.18](https://stacks.math.columbia.edu/tag/09HY) · [Milne, *Fields and Galois Theory*, v5.10, pp. 53 and 61–62](https://www.jmilne.org/math/CourseNotes/FT.pdf)

3. *Nonconstructive choice.* The corollary uses `Classical.choose` on the existence statement. The resulting basis is therefore not computable from the data, which is why the examples above exhibit a primitive element and its change-of-basis matrix by hand rather than by evaluating the Lean term.

**Reading boundary.** Archive A2 SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` pins Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The bodies of Lemmas A, B and C, the theorem, the corollary, the two embedding-count wrappers, `eq_X_sub_C_of_separable_of_root_eq`, `AlgHom.natCard_of_powerBasis`, `induction_on_adjoin` and `induction_on_adjoin_finset` were read against the source. Cyclicity of $E^\times$ is inherited from §5.3.1.6, and the trace consumers from §5.3.1.7 and §5.3.1.8. The declarations `gcd_map`, `separable_gcd_right` and `Infinite.exists_notMem_finset` are read in [§5.3.1.11](#53111-the-separable-greatest-common-divisor-in-the-primitive-element-proof); `Module.finite_of_finite` and `IsNoetherian.iff_fg` are used at interface level. The quotient construction behind the corollary, `AdjoinRoot.powerBasis`, `adjoinRootEquivAdjoin` and `PowerBasis.map`, is read in [§5.3.1.10](#53110-power-bases-from-the-quotient-ring-remainders-multiplication-matrices-and-transport). No Lean kernel replay or full dependency closure was performed. [Source map](../sources/SOURCES.md#primitive-elements-and-power-bases-5319)

### 5.3.1.10 Power bases from the quotient ring: remainders, multiplication matrices and transport

**Motivation.** The corollary of §5.3.1.9 produced the separable power basis in two quoted steps. In the polynomial quotient $F[X]/(m)$ by the minimal polynomial of the primitive element, the classes of $1,X,\ldots,X^{n-1}$ form a basis, and this basis is carried to $F(\alpha)$ and then to $E$. Every trace computation of §§5.3.1.7–5.3.1.9 takes place in that basis. The matrix whose determinant `det_traceMatrix_ne_zero'` declares nonzero is the matrix of the numbers $\operatorname{Tr}(\alpha^{i+j})$, and §5.3.1.8 read traces of generators off characteristic polynomials of multiplication matrices. This subsection opens the two quoted steps. It reads the pinned proof that every class of $F[X]/(f)$ has exactly one representative of degree less than $\deg f$, identifies multiplication by the class of $X$ with a companion matrix, and follows the algebra isomorphism and the transport of bases that end in `Field.powerBasisOfFiniteOfSeparable`. The outcome is a clean division of labor: the quotient power basis needs only $f\ne0$, and separability is spent on the trace determinant and nowhere in the quotient. [Stacks Project, Example 9.7.6](https://stacks.math.columbia.edu/tag/09G7) · [Stacks Project, Lemma 9.6.8](https://stacks.math.columbia.edu/tag/09G1)

**Examples [Expository].** In each example $A=K[X]/(f)$, $\rho$ is the class of $X$, and matrices act on coordinate columns in the basis $(1,\rho,\ldots,\rho^{n-1})$.

1. *The pure cubic $\mathbb Q[X]/(X^3-2)$.* Put $f=X^3-2$. Division by the monic $f$ replaces $X^3$ by $2$, so $X^3\equiv2$, $X^4\equiv2X$ and $X^5\equiv2X^2$. For instance
   $$
   X^5+X^4-1=(X^3-2)(X^2+X)+(2X^2+2X-1),
   $$
   so the class of $X^5+X^4-1$ is $2\rho^2+2\rho-1$. No other polynomial of degree at most two represents this class: two such representatives differ by a multiple of $f$ of degree at most two, which is zero.

   For $x=u+v\rho+w\rho^2$ with $u,v,w\in\mathbb Q$, the products $x$, $x\rho=2w+u\rho+v\rho^2$ and $x\rho^2=2v+2w\rho+u\rho^2$ are the columns of
   $$
   M_x=\begin{pmatrix}u&2w&2v\\v&u&2w\\w&v&u\end{pmatrix},\qquad
   C=M_\rho=\begin{pmatrix}0&0&2\\1&0&0\\0&1&0\end{pmatrix}.
   $$
   The matrix $C$ is the companion matrix of $f$: ones below the diagonal and the coordinates $(2,0,0)$ of $\rho^3$ in the last column. Expanding along the first row gives $\det(XI-C)=X\cdot X^2+(-2)\cdot1=X^3-2$. One checks $M_x=uI+vC+wC^2$, so $\operatorname{Tr}(x)=3u$, and $\det C=2$ is the norm of $\rho$.

   Since $\rho^3=2$ and $\rho^4=2\rho$, the traces of $\rho^k$ for $k=0,1,2,3,4$ are $3,0,0,6,0$. The trace matrix of the power basis is the Hankel matrix
   $$
   T=\bigl(\operatorname{Tr}(\rho^{i+j})\bigr)_{0\le i,j\le2}=\begin{pmatrix}3&0&0\\0&0&6\\0&6&0\end{pmatrix}.
   $$
   Expanding along the first row gives $\det T=3\cdot(0\cdot0-6\cdot6)=-108=-2^2\cdot3^3$. The columns of
   $$
   T^{-1}=\begin{pmatrix}1/3&0&0\\0&0&1/6\\0&1/6&0\end{pmatrix}
   $$
   are the coordinates of the dual basis $(1/3,\ \rho^2/6,\ \rho/6)$ for the pairing $(x,y)\mapsto\operatorname{Tr}(xy)$. For example $\operatorname{Tr}(\rho\cdot\rho^2/6)=\operatorname{Tr}(1/3)=1$ and $\operatorname{Tr}(\rho\cdot\rho/6)=\operatorname{Tr}(\rho^2)/6=0$. Euler's formula gives the same basis. Here $f/(X-\rho)=X^2+\rho X+\rho^2$ and $f'(\rho)=3\rho^2$, and dividing the coefficients $\rho^2,\rho,1$ by $3\rho^2$ gives $1/3$, $\rho^2/6$ and $\rho/6$ because $\rho^3=2$. In Mathlib this is `Module.Basis.traceDual_powerBasis_eq`, stated for a separable field with a power basis. [Mathlib/RingTheory/Trace/Basic.lean:606–627](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L606-L627)

   Three independent computations give the same determinant. Over $\mathbb C$ we have $f=\prod_{k=0}^{2}(X-r_k)$ with $r_k=\sqrt[3]{2}\,\omega^k$ and $\omega=e^{2\pi i/3}$. The power sums $\sum_k r_k^m$ equal $3\cdot2^{m/3}$ when $3\mid m$ and vanish otherwise, because $1+\omega^m+\omega^{2m}=0$ for $3\nmid m$; they reproduce the traces. The Vandermonde product is $(r_1-r_0)(r_2-r_0)(r_2-r_1)=2(\omega-1)(\omega^2-1)(\omega^2-\omega)=2\cdot3\cdot(-\sqrt{-3})$, whose square is $-108$. Next, $f'(\rho)=3\rho^2$ has norm $\det(3C^2)=27\cdot2^2=108$, and $(-1)^{3\cdot2/2}\cdot108=-108$. Finally, the classical formula $\operatorname{disc}(X^3+aX+b)=-4a^3-27b^2$ at $a=0$, $b=-2$ gives $-108$.

   The polynomial $f$ is Eisenstein at $2$, hence irreducible, and it is the minimal polynomial both of $\sqrt[3]{2}\in\mathbb R$ and of $\omega\sqrt[3]{2}\in\mathbb C$. The isomorphisms of $A$ with $\mathbb Q(\sqrt[3]{2})$ and with $\mathbb Q(\omega\sqrt[3]{2})$ send $\rho$ to these roots and $(1,\rho,\rho^2)$ to the power bases $(1,\sqrt[3]{2},\sqrt[3]{4})$ and $(1,\omega\sqrt[3]{2},\omega^2\sqrt[3]{4})$ of two different subfields of $\mathbb C$. Both have trace matrix $T$, because an algebra isomorphism preserves traces. Conrad computes the same multiplication matrix, trace and norm. [Conrad, *Trace and Norm*, Example 2.4, pp. 2–3](https://kconrad.math.uconn.edu/blurbs/galoistheory/tracenorm.pdf) · [Milne, *Algebraic Number Theory*, v3.08, Proposition 2.34 and Example 2.35, pp. 37–38](https://www.jmilne.org/math/CourseNotes/ANT.pdf). Milne proves Proposition 2.34 under the standing assumption, made on p. 37 at the head of *Finding the ring of integers*, that the base field has characteristic zero; this example is over $\mathbb Q$.

2. *The field of four elements as $\mathbb F_2[X]/(X^2+X+1)$.* The polynomial $X^2+X+1$ takes the value $1$ at both elements of $\mathbb F_2$, so it is irreducible and $A$ is a field. Its four elements are the classes of the four polynomials $0,1,X,X+1$ of degree less than two. Reduction uses $X^2\equiv X+1$; for instance $X^3=(X^2+X+1)(X+1)+1$, so $\rho^3=1$ and $A^\times=\{1,\rho,\rho+1\}$ is cyclic of order three, as in §5.3.1.6. For $x=u+v\rho$,
   $$
   M_x=\begin{pmatrix}u&v\\v&u+v\end{pmatrix},\qquad
   C=M_\rho=\begin{pmatrix}0&1\\1&1\end{pmatrix},
   $$
   which is the matrix of §5.3.1.8, Example 1. The last column of $C$ holds the coordinates $(1,1)$ of $\rho^2=1+\rho$, and $\det(XI-C)=X^2-X-1=X^2+X+1$ in characteristic two. The traces are $\operatorname{Tr}(1)=0$, $\operatorname{Tr}(\rho)=1$ and $\operatorname{Tr}(\rho^2)=\operatorname{Tr}(1+\rho)=1$, so
   $$
   T=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad \det T=-1=1,\qquad
   T^{-1}=\begin{pmatrix}1&1\\1&0\end{pmatrix}.
   $$
   The dual basis is $(1+\rho,\ 1)$: indeed $\operatorname{Tr}(1+\rho)=1$, $\operatorname{Tr}(\rho(1+\rho))=\operatorname{Tr}(1)=0$, $\operatorname{Tr}(1)=0$ and $\operatorname{Tr}(\rho)=1$. Euler's formula agrees: $f/(X-\rho)=X+(\rho+1)$ and $f'(\rho)=2\rho+1=1$. The roots of $X^2+X+1$ in $A$ are $\rho$ and $\rho^2=\rho+1$, with Vandermonde determinant $\rho^2-\rho=1$. The Frobenius formula of §5.3.1.8 gives $\operatorname{Tr}(x)=x+x^2=v$, and the classical discriminant $1-4=-3$ reduces to $1$ modulo two.

   The same basis sits inside a larger field. In $\mathbb F_{16}=\mathbb F_2[s]/(s^4+s+1)$, the field of §5.3.1.7, Example 2, written there with $t$, the element $a=s^5=s^2+s$ satisfies $a^2+a+1=s^4+s+1=0$ and $a\notin\mathbb F_2$. Its minimal polynomial is therefore $X^2+X+1$, and $\rho\mapsto a$ is an isomorphism of $A$ onto $\mathbb F_2(a)=\{0,1,s^2+s,s^2+s+1\}$. The other root $a^2=s^{10}=s^2+s+1$ gives a second isomorphism, which differs from the first by Frobenius. The transported power basis $(1,s^2+s)$ again has trace matrix $T$ for the trace of $\mathbb F_2(a)$ over $\mathbb F_2$. The trace of $\mathbb F_{16}$ over $\mathbb F_2$ is a different function: $\operatorname{Tr}_{\mathbb F_{16}/\mathbb F_2}(a)=[\mathbb F_{16}:\mathbb F_2(a)]\cdot\operatorname{Tr}_{\mathbb F_2(a)/\mathbb F_2}(a)=2\cdot1=0$, in agreement with the vanishing trace of $t^5$ in the table of §5.3.1.7. The factor $[\mathbb F_{16}:\mathbb F_2(a)]$ is the factor $[L:K(x)]$ in the proof of §5.3.1.8, stated in Mathlib as `trace_eq_trace_adjoin`.

3. *A power basis with a degenerate trace form.* Let $K=\mathbb F_3(t)$, $f=X^3-t$ and $L=K[X]/(f)$. The polynomial $f$ is Eisenstein at the prime $t$ of $\mathbb F_3[t]$, hence irreducible over $K$ by Gauss's lemma, so $L$ is a field of degree three with power basis $(1,\rho,\rho^2)$. The computation of Example 1 goes through with $2$ replaced by $t$:
   $$
   M_x=\begin{pmatrix}u&tw&tv\\v&u&tw\\w&v&u\end{pmatrix},\qquad
   \operatorname{Tr}(x)=3u=0,\qquad
   T=\begin{pmatrix}3&0&0\\0&0&3t\\0&3t&0\end{pmatrix}=0 .
   $$
   Every element has trace zero, the trace form vanishes identically, and the discriminant $-27t^2$ is $0$ in $K$. The reason is visible in a splitting field: $(X-\rho)^3=X^3-\rho^3=f$ in characteristic three, so $f$ has the single root $\rho$ with multiplicity three. Counting roots with multiplicity gives $\operatorname{Tr}(g(\rho))=3g(\rho)=0$, and the Vandermonde matrix in the roots has three equal rows. The extension is not separable, since $f'=3X^2=0$, and $L$ has exactly one $K$-embedding into an algebraic closure instead of three. The inseparable model $\mathbb F_p(t)(a)$ with $a^p=t$ at the end of §5.3.1.8 behaves in the same way. By contrast, Example 3 of §5.3.1.9 is an inseparable extension of degree $p^2$ without a primitive element, so it has no power basis at all.

**Definitions.** Let $R$ be a commutative ring and $f\in R[X]$. Mathlib's `AdjoinRoot f` is the quotient ring $R[X]/(f)$, with quotient map `mk f`, constants `of f` and the class `root f` of $X$, written $\rho$ here. For monic $g$, the quotient and remainder of $p$ (`p /ₘ g` and `p %ₘ g`) are produced by `divModByMonicAux`, which subtracts $g\cdot\mathrm{lc}(p)X^{\deg p-\deg g}$ from $p$ as long as $p\ne0$ and $\deg g\le\deg p$. A power basis is the structure `PowerBasis R S` of §5.3.1.9. For a basis $b$ of an $R$-algebra $S$, the multiplication matrix `leftMulMatrix b x` is the matrix of $y\mapsto xy$; its $(i,j)$ entry is the $i$th coordinate of $x\,b_j$, and $x\mapsto$ `leftMulMatrix b x` is a homomorphism of $R$-algebras into matrices. When $S$ is free of finite rank over $R$, the trace $\operatorname{Tr}_{S/R}(x)$ is the trace of this matrix in any basis. For a monic $m=X^n+c_{n-1}X^{n-1}+\cdots+c_0$, the companion matrix $C(m)$ has ones in the positions $(i+1,i)$, the column $(-c_0,\ldots,-c_{n-1})^{T}$ in the last place, and zeros elsewhere. For a finite family $b=(b_i)$ the trace matrix `traceMatrix R b` has entries $\operatorname{Tr}(b_ib_j)$, and the discriminant `Algebra.discr R b` is its determinant. A linear equivalence $e$ carries a basis $b$ to the basis `b.map e` with vectors $e(b_i)$; the coordinates of $y$ in it are those of $e^{-1}(y)$ in $b$. For an algebra isomorphism $e$, `PowerBasis.map pb e` performs this transport and takes $e$ of the old generator as the new one. [Mathlib/RingTheory/AdjoinRoot.lean:60–165](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AdjoinRoot.lean#L60-L165) · [Mathlib/Algebra/Polynomial/Div.lean:119–139](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean#L119-L139) · [Mathlib/LinearAlgebra/Matrix/ToLin.lean:947–975](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/ToLin.lean#L947-L975) · [Mathlib/RingTheory/Trace/Defs.lean:68–89](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Defs.lean#L68-L89) · [Mathlib/RingTheory/Trace/Basic.lean:339–347](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L339-L347) · [Mathlib/RingTheory/Discriminant.lean:66–71](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Discriminant.lean#L66-L71) · [Mathlib/LinearAlgebra/Basis/Defs.lean:162–176](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Basis/Defs.lean#L162-L176)

**Lemma A (division by a monic polynomial) [Lean, read].** Let $R$ be a nontrivial commutative ring and $g\in R[X]$ monic. Every $p\in R[X]$ can be written $p=gq+r$ with $\deg r<\deg g$, and the pair $(q,r)$ is unique. The remainder vanishes if and only if $g\mid p$, and it equals $p$ if and only if $\deg p<\deg g$.

*Proof.* Write $q_0$ and $r_0$ for the outputs of the recursion. If $p\ne0$ and $\deg g\le\deg p$, subtracting $g\cdot\mathrm{lc}(p)X^{\deg p-\deg g}$ cancels the leading term of $p$, because $g$ is monic, so the degree drops (`div_wf_lemma`). Well-founded recursion on the degree therefore ends with $\deg r_0<\deg g$ (`degree_modByMonic_lt`), and unwinding it gives $p=gq_0+r_0$ (`modByMonic_eq_sub_mul_div`, `modByMonic_add_div`). For uniqueness (`div_modByMonic_unique`), let $p=gq+r$ with $\deg r<\deg g$. Then $r-r_0=-g\,(q-q_0)$. The left side has degree less than $\deg g$. If $q\ne q_0$, the right side has degree at least $\deg g$, since the leading coefficient $1$ of $g$ cannot cancel the leading coefficient of $q-q_0$. Hence $q=q_0$ and $r=r_0$. The same comparison shows that a multiple of $g$ of degree less than $\deg g$ is zero, which gives the divisibility criterion (`modByMonic_eq_zero_iff_dvd`), and the recursion stops at once when $\deg p<\deg g$ (`modByMonic_eq_self_iff`). $\square$ [Mathlib/Algebra/Polynomial/Div.lean:106–260,349–413](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean#L106-L413)

**Lemma B (unique representatives in $R[X]/(g)$; `AdjoinRoot.powerBasis'`) [Lean, read].** Let $g\in R[X]$ be monic of degree $n$ over a commutative ring $R$. Every class in $R[X]/(g)$ is the class of exactly one polynomial of degree less than $n$, namely the remainder of any representative. Consequently $1,\rho,\ldots,\rho^{n-1}$ is an $R$-basis of $R[X]/(g)$, and the coordinates of the class of $p$ are the coefficients of $X^0,\ldots,X^{n-1}$ in the remainder of $p$.

*Proof.* Two polynomials have the same class exactly when $g$ divides their difference (`mk_eq_mk`). The remainder is constant on classes: if $g\mid p-p'$, the two remainders differ by a multiple of $g$ of degree less than $n$, which is zero by Lemma A. Mathlib packages this as the $R$-linear map `AdjoinRoot.modByMonicHom`, obtained by factoring the remainder map through the quotient; the factorization exists because the kernel of the remainder map consists of the multiples of $g$ (`mem_ker_modByMonic`). The remainder of $p$ has the class of $p$, since $p$ minus its remainder is $gq_0$ (`mk_leftInverse`). A polynomial of degree less than $n$ is its own remainder (Lemma A), which is the uniqueness. `powerBasisAux'` builds the basis from the coordinate isomorphism that sends a class to the first $n$ coefficients of its remainder, with inverse $c\mapsto$ the class of $\sum_{i<n}c_iX^i$; the two composites are the identity by `sum_modByMonic_coeff` and `modByMonic_eq_self_iff`. `powerBasis'` takes $\rho$ as generator and $n$ as dimension. $\square$ [Mathlib/RingTheory/AdjoinRoot.lean:208–214,569–646](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AdjoinRoot.lean#L569-L646) · [Mathlib/Algebra/Polynomial/RingDivision.lean:64–83](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/RingDivision.lean#L64-L83) · [Mathlib/Algebra/Polynomial/Div.lean:439–444](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean#L439-L444)

**Lemma C (the minimal polynomial of the root; `AdjoinRoot.minpoly_root`) [Lean, read].** Let $K$ be a field, $f\in K[X]$ nonzero and $f_1=f\cdot\mathrm{lc}(f)^{-1}$ its monic multiple. In $K[X]/(f)$ a polynomial $h$ satisfies $h(\rho)=0$ if and only if $f\mid h$, no nonzero polynomial of degree less than $\deg f$ vanishes at $\rho$, and the minimal polynomial of $\rho$ is $f_1$.

*Proof.* Evaluation at $\rho$ is the quotient map (`aeval_eq`), and a class vanishes exactly when $f$ divides the representative (`mk_eq_zero`). This gives the first two statements. In particular $f_1$, a monic multiple of $f$, vanishes at $\rho$, and every monic $q$ with $q(\rho)=0$ is divisible by $f$, so $\deg q\ge\deg f$. The pinned proof reaches $f\mid q$ by factoring `mk f` through `mk q` with `lift`, which is possible because $q(\rho)=0$, and then applies `mk_eq_zero` and `natDegree_le_of_dvd`. The minimal polynomial is defined as a monic polynomial of least degree vanishing at $\rho$ (`minpoly`, `minpoly.min`). `minpoly.unique` identifies $f_1$ with it: two monic polynomials of the same least degree vanishing at $\rho$ differ by a polynomial of smaller degree vanishing at $\rho$, and such a polynomial is zero by `minpoly.degree_le_of_ne_zero`, which applies minimality to the monic multiple of a nonzero polynomial. No irreducibility of $f$ is used. $\square$ [Mathlib/RingTheory/AdjoinRoot.lean:246–248,664–686](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AdjoinRoot.lean#L664-L686) · [Mathlib/FieldTheory/Minpoly/Basic.lean:40–42,132–163](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Minpoly/Basic.lean#L132-L163) · [Mathlib/FieldTheory/Minpoly/Field.lean:34–77](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Minpoly/Field.lean#L34-L77)

**Theorem 1 (the quotient power basis; `AdjoinRoot.powerBasis`) [Lean, read].** Let $K$ be a field and $f\in K[X]$ nonzero of degree $n$. Then $1,\rho,\ldots,\rho^{n-1}$ is a $K$-basis of $A=K[X]/(f)$; equivalently, every element of $A$ is the class of exactly one polynomial of degree less than $n$. The pinned `AdjoinRoot.powerBasis hf` is this basis with generator $\rho$ and dimension $n$. Its only hypothesis is $f\ne0$: irreducibility, monicity and separability of $f$ are not used. The docstrings of `powerBasisAux` and `powerBasis` speak of an irreducible polynomial, but the hypothesis in the code is `hf : f ≠ 0`.

*Proof.* By Lemma C the minimal polynomial of $\rho$ is $f_1$, of degree $n$. *Independence* (`linearIndependent_pow`): if $\sum_{i<n}g_i\rho^i=0$, then $h=\sum_{i<n}g_iX^i$ has degree less than $n$ and vanishes at $\rho$, so $h=0$ by `minpoly.degree_le_of_ne_zero`, and every $g_i$ is zero. *Spanning* (`IsIntegral.mem_span_pow`): every element is $p(\rho)$ for some $p$; Lemma A with the monic $f_1$ writes $p=f_1q+r$ with $\deg r<n$, and $p(\rho)=r(\rho)$ because $f_1(\rho)=0$. By `mem_span_pow'` the span of $1,\rho,\ldots,\rho^{n-1}$ consists of the values $r(\rho)$ with $\deg r<n$. `Basis.mk` assembles the basis from the two facts (`powerBasisAux`), and `basis_eq_pow` holds because `Basis.mk` returns the given vectors. Independence is the uniqueness of the representative and spanning is its existence. $\square$ [Mathlib/RingTheory/AdjoinRoot.lean:688–714](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AdjoinRoot.lean#L688-L714) · [Mathlib/RingTheory/PowerBasis.lean:95–116,412–436](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/PowerBasis.lean#L412-L436) · [Mathlib/LinearAlgebra/Basis/Basic.lean:107–126](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Basis/Basic.lean#L107-L126)

For monic $f$ the bases of Lemma B and Theorem 1 have the same vectors. The field version is the one called by `IntermediateField.powerBasisAux`, so it is the one on the trace path of §§5.3.1.7–5.3.1.9.

**Lemma D (multiplication by the generator is a companion matrix; `PowerBasis.leftMulMatrix`) [Lean, read].** Let $S$ be an algebra over a commutative ring $A$ with a power basis of dimension $n$ and generator $\gamma$, and let $m=X^n+c_{n-1}X^{n-1}+\cdots+c_0$ be the minimal polynomial of $\gamma$. In this basis multiplication by $\gamma$ has matrix $C(m)$, and multiplication by $h(\gamma)$ has matrix $h(C(m))$ for every $h\in A[X]$. For $K[X]/(f)$ with the basis of Theorem 1, the matrix of $\rho$ is $C(f_1)$.

*Proof.* Column $k$ of the matrix holds the coordinates of $\gamma\cdot\gamma^k=\gamma^{k+1}$. For $k+1<n$ this is the basis vector of index $k+1$, a single $1$ below the diagonal. For $k=n-1$ it is $\gamma^n$. Its coordinates define `minpolyGen`, the polynomial $X^n$ minus $\sum_{i<n}$ (coordinate $i$ of $\gamma^n$) $X^i$, which kills $\gamma$ (`aeval_minpolyGen`). No nonzero polynomial of degree less than $n$ kills $\gamma$, by linear independence of the basis (`dim_le_degree_of_root`). From these two facts `minpolyGen_eq` identifies `minpolyGen` with $m$ through `minpoly.unique'`, so the last column is $(-c_0,\ldots,-c_{n-1})^{T}$. Since `leftMulMatrix` is an algebra homomorphism, $h(\gamma)$ is sent to $h(C(m))$. For $K[X]/(f)$, Lemma C gives $m=f_1$. $\square$ The characteristic polynomial of $C(m)$ is $m$ (`charpoly_leftMulMatrix`). It is monic of degree $n$, it kills $\gamma$ by the Cayley–Hamilton theorem transported through the injective map `leftMulMatrix`, and `minpoly.unique'` applies with the same degree bound `dim_le_degree_of_root`. [Mathlib/RingTheory/PowerBasis.lean:162–241](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/PowerBasis.lean#L162-L241) · [Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean:70–84](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/LinearAlgebra/Matrix/Charpoly/Minpoly.lean#L70-L84)

**Lemma E (from the quotient to $F(\alpha)$ and beyond) [Lean, read].** Let $F\subseteq E$ be fields and let $\alpha\in E$ be algebraic over $F$ with minimal polynomial $m$ of degree $n$.

1. (`adjoinRootEquivAdjoin`) The $F$-algebra map $F[X]/(m)\to F(\alpha)$ sending the class of $p$ to $p(\alpha)$ is an isomorphism.
2. (`IntermediateField.powerBasisAux`, `adjoin.powerBasis`) It carries the basis of Theorem 1 to $1,\alpha,\ldots,\alpha^{n-1}$, a power basis of $F(\alpha)$ with generator $\alpha$.
3. (`PowerBasis.map`) An $F$-algebra isomorphism $\varphi:S\to S'$ carries a power basis of $S$ with generator $\gamma$ to the power basis of $S'$ with generator $\varphi(\gamma)$, of the same dimension and with the same minimal polynomial.
4. (`Algebra.trace_eq_of_algEquiv`, `discr_eq_discr_of_algEquiv`) $\operatorname{Tr}_{S'/F}(\varphi(y))=\operatorname{Tr}_{S/F}(y)$ for every $y\in S$. Hence a family and its image under $\varphi$ have the same trace matrix and the same discriminant.

*Proof.* (1) The map is `AdjoinRoot.liftAlgHom` at the generator of $F(\alpha)$; it is well defined because $m(\alpha)=0$ (`aeval_gen_minpoly`). The minimal polynomial of an algebraic element of a field is irreducible (`minpoly.irreducible`): in a factorization into two monic factors of smaller degree one factor would vanish at $\alpha$, contradicting the minimality of the degree. Hence $(m)$ is a maximal ideal and $F[X]/(m)$ is a field (`AdjoinRoot.instField`). A ring homomorphism from a field to a nonzero ring is injective (`RingHom.injective`, read in §6.4.15). For surjectivity, $F(\alpha)$ is the subfield generated by the image of $F$ and $\alpha$, and the image of the map is a subfield containing the constants (`lift_of`) and $\alpha$ (`lift_root`). (2) `IntermediateField.powerBasisAux` maps the basis of Theorem 1 along the linear equivalence underlying (1) and reindexes trivially by `finCongr rfl`. The $i$th vector is the image of $\rho^i$, which is $\alpha^i$ by multiplicativity and `adjoinRootEquivAdjoin_apply_root`. (3) `PowerBasis.map` applies `Basis.map` along $\varphi$; the identity $\varphi(\gamma^i)=\varphi(\gamma)^i$ gives `basis_eq_pow`, and `minpolyGen_map` gives the minimal polynomial. (4) Multiplication by $\varphi(y)$ on $S'$ is $\varphi$ composed with multiplication by $y$ composed with $\varphi^{-1}$, and the trace of a linear map is invariant under conjugation (`LinearMap.trace_conj'`). Applying this to the products $b_ib_j$ gives the statement about trace matrices. $\square$ [Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:384–457](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean#L384-L457) · [Mathlib/RingTheory/PowerBasis.lean:444–468](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/PowerBasis.lean#L444-L468) · [Mathlib/RingTheory/Trace/Basic.lean:174–178](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L174-L178) · [Mathlib/RingTheory/Discriminant.lean:73–78](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Discriminant.lean#L73-L78) · [Mathlib/FieldTheory/Minpoly/Basic.lean:268–278](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Minpoly/Basic.lean#L268-L278) · [Stacks Project, Lemma 9.9.2](https://stacks.math.columbia.edu/tag/09GN)

**Theorem 2 (the trace matrix of a quotient presentation) [Expository].** Let $K$ be a field, $f\in K[X]$ monic of degree $n\ge1$, and $A=K[X]/(f)$ with the power basis of Theorem 1. Write $f=\prod_{i=1}^{n}(X-r_i)$ in a splitting field $L$, with roots repeated according to multiplicity.

1. For every $g\in K[X]$, $\operatorname{Tr}_{A/K}(g(\rho))=\sum_{i=1}^{n}g(r_i)$ in $L$. In particular $\operatorname{Tr}(\rho^k)=\sum_i r_i^k$.
2. The trace matrix $T=\bigl(\operatorname{Tr}(\rho^{j+k})\bigr)_{0\le j,k<n}$ equals $V^{T}V$, where $V=(r_i^{\,j})$ has rows indexed by the roots and columns by the powers. Hence $\det T=\prod_{i<j}(r_j-r_i)^2$.
3. The trace form $(x,y)\mapsto\operatorname{Tr}(xy)$ of $A$ is nondegenerate if and only if $f$ has $n$ distinct roots in $L$, that is, if and only if $f$ is separable.
4. If $f$ is the minimal polynomial of $\alpha$ over $K$, then $T$ is also the trace matrix of the power basis $1,\alpha,\ldots,\alpha^{n-1}$ of $K(\alpha)$ and of every power basis obtained from it by `PowerBasis.map`.

*Proof.* (1) By Lemma D, multiplication by $g(\rho)$ has matrix $g(C)$ with $C=C(f)$, and $\det(XI-C)=f$. Over $L$ the matrix $C$ is triangularizable. More generally, a square matrix over $L$ whose characteristic polynomial splits as $\prod_i(X-r_i)$ is similar to an upper triangular matrix with diagonal entries $r_1,\ldots,r_n$ in some order. Indeed $\det(r_1I-C)=f(r_1)=0$, so $C$ has an eigenvector for $r_1$. In a basis of $L^n$ that begins with this eigenvector, $C$ becomes block upper triangular with corner entry $r_1$ and a lower block whose characteristic polynomial is $f/(X-r_1)$, which again splits; induction on the size applies to the lower block. This gives an invertible $P$ over $L$ such that $P^{-1}CP$ is upper triangular with diagonal entries $r_1,\ldots,r_n$. Then $P^{-1}g(C)P=g(P^{-1}CP)$ is upper triangular with diagonal entries $g(r_i)$, and similar matrices have the same trace. (2) By (1), $T_{jk}=\sum_i r_i^{\,j+k}=\sum_i V_{ij}V_{ik}=(V^{T}V)_{jk}$. Thus $\det T=(\det V)^2$, and the Vandermonde determinant is $\det V=\prod_{i<j}(r_j-r_i)$. (3) A bilinear form on a finite-dimensional space is nondegenerate exactly when its matrix in a basis has nonzero determinant. By (2) this happens exactly when no two $r_i$ coincide. For a polynomial over a field, having no repeated root in a splitting field is separability, equivalently coprimality with $f'$. (4) is Lemma E (2)–(4). $\square$ [Stacks Project, Lemma 9.20.7](https://stacks.math.columbia.edu/tag/0BIL) · [Milne, *Algebraic Number Theory*, v3.08, Proposition 2.26, Remark 2.28 and Proposition 2.34, pp. 34 and 37](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

The classical sources cover part of this theorem only. Milne's Proposition 2.26 and Remark 2.28 concern a finite separable, respectively inseparable, field extension with no condition on the characteristic. His Proposition 2.34, the product formula $\prod_{i<j}(\beta_i-\beta_j)^2$ of part (2), is proved under the standing assumption, stated on p. 37 at the head of *Finding the ring of integers*, that the base field has characteristic zero. In positive characteristic, as in Examples 2 and 3 and Remark 2, and for quotients that are not fields, Theorem 2 rests on the proof given here. Its field cases in every characteristic are the pinned Mathlib declarations `det_traceMatrix_ne_zero'`, `discr_powerBasis_eq_prod` and `trace_eq_zero_of_not_isSeparable` described below, which carry no hypothesis on the characteristic.

Part (1) contains the trace formulas of §5.3.1.8. At $g=X$ it is the negative of the next coefficient of $f$ (`trace_gen_eq_nextCoeff_minpoly`). For a finite field with $q$ elements and $f$ the minimal polynomial of $x$, the roots are $x,x^q,x^{q^2},\ldots$, and (1) becomes the Frobenius sum. Mathlib proves (2) and (3) for fields only, in the direction from separability to a nonzero determinant together with the inseparable vanishing described below. The form with multiplicities given here also covers quotients that are not fields, such as $K[X]/(X^2)$.

**How the pinned proofs spend separability on $T$ [Lean, read].** `Algebra.traceForm_toMatrix_powerBasis` records that in any power basis the matrix of the trace form has the Hankel entries $\operatorname{Tr}(\gamma^{i+j})$. The theorem `det_traceMatrix_ne_zero'` takes a power basis `pb` of a field $L$ over $K$ together with `Algebra.IsSeparable K L`. It maps $\det T$ to an algebraic closure and enumerates the $K$-embeddings $\sigma_1,\ldots,\sigma_n$ by `Fin pb.dim` through `AlgHom.card`; this is the first use of separability, which supplies exactly $n=[L:K]$ embeddings. It then factors $T$ as $EE^{T}$ by `traceMatrix_eq_embeddingsMatrixReindex_mul_trans`, the second use, through `trace_eq_sum_embeddings`. Finally it recognizes $E$ as the transposed Vandermonde matrix in the values $\sigma_i(\gamma)$ (`embeddingsMatrixReindex_eq_vandermonde`) and concludes because distinct embeddings differ on the generator (`pb.algHom_ext`). This is part (2) of Theorem 2 with $r_i=\sigma_i(\gamma)$. Nothing about how `pb` was constructed enters. `det_traceForm_ne_zero` needs one power basis to compare with an arbitrary basis $b$. It takes `Field.powerBasisOfFiniteOfSeparable`, which by §5.3.1.9 is `(adjoin.powerBasis _).map ((equivOfEq e).trans topEquiv)`, that is, Lemma E applied to the quotient basis of Theorem 1, and a change of basis multiplies the determinant by the square of a unit. Separability is consumed in this proof in the choice of the primitive element and inside `det_traceMatrix_ne_zero'`; `powerBasisOfFiniteOfSeparable` also reads the integrality of $\alpha$ off the separability instance (`Algebra.IsSeparable.isIntegral`), although finite dimension alone would give it. It is never consumed in `AdjoinRoot.powerBasis`, `adjoinRootEquivAdjoin`, `adjoin.powerBasis` or `PowerBasis.map`. `traceForm_nondegenerate` and its finite-field consumers of §5.3.1.7 follow. [Mathlib/RingTheory/Trace/Basic.lean:67–69,409–507](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L409-L507) · [Mathlib/FieldTheory/PrimitiveElement.lean:223–231](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L223-L231) · [Mathlib/FieldTheory/Finite/Trace.lean:36–44](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Finite/Trace.lean#L36-L44)

On the discriminant side, `Algebra.discr` is by definition the determinant of the trace matrix (`discr_def`), and `discr_eq_discr_of_algEquiv` is Lemma E (4). A change of basis by a matrix $P$ multiplies it by $\det(P)^2$ (`discr_of_matrix_vecMul`). For separable $L/K$, `discr_powerBasis_eq_prod` states part (2) in the form $\prod_{i<j}(\sigma_j\gamma-\sigma_i\gamma)^2$, `discr_powerBasis_eq_norm` gives $(-1)^{n(n-1)/2}N(m'(\gamma))$, and `discr_not_zero_of_basis` gives a nonzero discriminant for every basis by way of `traceForm_nondegenerate`. The converse direction is also pinned. `Algebra.trace_eq_zero_of_not_isSeparable` shows that the trace of a field extension $L/K$ that is not separable vanishes identically. When $L/K$ is finite, its characteristic is a prime $p$ and the proof has two cases. A separable element $x$ lies in the separable closure $L_s$ of $K$ in $L$, so $\operatorname{Tr}_{L/K}(x)=\operatorname{Tr}_{L_s/K}([L:L_s]\,x)$, and $[L:L_s]$ is a positive power of $p$. An inseparable element has minimal polynomial $g(X^{p^k})$ with $k\ge1$, whose next coefficient vanishes, and `trace_eq_finrank_mul_minpoly_nextCoeff` applies. `traceForm_nondegenerate_tfae` packages separability, the nonvanishing of the trace and nondegeneracy as equivalent conditions. Example 3 instantiates the second case at $x=\rho$, where $f=g(X^3)$ with $g=X-t$, and the first case at $x=1$, where $[L:K]=3$. [Mathlib/RingTheory/Discriminant.lean:66–239](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Discriminant.lean#L66-L239) · [Mathlib/RingTheory/Trace/Basic.lean:276–326,509–515](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L276-L326)

**Return to §5.3.1.9 and to the trace formula.** The corollary of §5.3.1.9 is Lemma E (2)–(3) applied to the primitive element chosen there; the choice, the excluded scalars and the two branches are those of §5.3.1.9 and are not repeated. In §5.3.1.8, `trace_eq_sum_embeddings` uses `adjoin.powerBasis` for $K(x)$, which is Lemma E (2) applied to the basis of Theorem 1. `trace_eq_sum_embeddings_gen` then turns the root sum of Theorem 2 (1) at $g=X$ into an embedding sum through `liftEquiv'` (read in §6.4.15) and the separability of the generator. Example 2 displays the finite-field case, in which the matrix trace $v$, the Frobenius sum $x+x^2$ and the root sum coincide. The dual bases over $\mathbb F_9$ and $\mathbb F_{16}$ in §5.3.1.7 are computed from trace matrices of the same kind. [Mathlib/RingTheory/Trace/Basic.lean:78–95,127–142,218–261](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Trace/Basic.lean#L218-L261)

**Remarks [Expository].**

1. *Which hypothesis each step uses.* The table lists the pinned declarations along the path from the quotient to the trace determinant.

   | Step | Pinned declaration | Hypothesis used |
   |---|---|---|
   | Unique remainder | `divModByMonicAux`, `div_modByMonic_unique` | monic divisor |
   | Basis of $R[X]/(g)$ | `powerBasisAux'`, `powerBasis'` | $g$ monic over a commutative ring |
   | Basis of $K[X]/(f)$ | `minpoly_root`, `powerBasisAux`, `AdjoinRoot.powerBasis` | $f\ne0$ over a field |
   | Multiplication matrix | `PowerBasis.leftMulMatrix`, `minpolyGen_eq` | a power basis |
   | Quotient and $F(\alpha)$ | `adjoinRootEquivAdjoin` | $\alpha$ algebraic; irreducibility of its minimal polynomial is automatic |
   | Transport | `Basis.map`, `adjoin.powerBasis`, `PowerBasis.map` | an algebra isomorphism |
   | Invariance of $T$ | `trace_eq_of_algEquiv`, `discr_eq_discr_of_algEquiv` | none |
   | Existence of a primitive element | `exists_primitive_element` (§5.3.1.9) | separability, in the infinite branch |
   | $\det T\ne0$ | `det_traceMatrix_ne_zero'` | separability: $n$ embeddings and a Vandermonde determinant |

   Examples 1 and 2 are separable and have $\det T\ne0$. Example 3 has a power basis and $T=0$. Example 3 of §5.3.1.9 has no power basis at all. Separability is therefore not what makes a quotient free with a power basis; on a power basis it is exactly what makes the trace pairing nondegenerate.

2. *Reduction of Example 1.* Since $X^3-2$ is monic over $\mathbb Z$, Lemma B gives the $\mathbb Z$-basis $1,\rho,\rho^2$ of $\mathbb Z[X]/(X^3-2)$. The matrices $M_x$ have integer entries and reduce modulo a prime $p$ to the multiplication matrices of $\mathbb F_p[X]/(X^3-2)$ in its own power basis. Modulo $3$ we have $X^3-2=(X+1)^3$ and $T\equiv0$. Modulo $2$ we have $X^3-2=X^3$ and $T\equiv\operatorname{diag}(1,0,0)$, of rank one. The power bases survive both reductions, and the trace forms degenerate exactly at the primes dividing $\det T=-108$. These two quotients are not fields; Example 3 shows the same phenomenon in a field.

**Reading boundary.** Archive A2 SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` pins Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Read against the source at local R3 in this subsection: the division recursion with `div_wf_lemma`, `degree_modByMonic_lt`, `modByMonic_eq_sub_mul_div`, `div_modByMonic_unique`, `modByMonic_eq_zero_iff_dvd` and `sum_modByMonic_coeff`; `Polynomial.modByMonicHom` and `mem_ker_modByMonic`; in `AdjoinRoot.lean` the bodies of `modByMonicHom`, `mk_leftInverse`, `powerBasisAux'`, `powerBasis'`, `minpoly_root`, `powerBasisAux` and `powerBasis`, together with `aeval_eq`, `mk_eq_mk`, `mk_eq_zero`, `lift` and the field instance; `linearIndependent_pow`, `IsIntegral.mem_span_pow`, `mem_span_pow'`, `minpolyGen` through `minpolyGen_eq`, `PowerBasis.leftMulMatrix`, `PowerBasis.map` and `minpolyGen_map`; `charpoly_leftMulMatrix` (first read in §5.3.1.8); the minimal-polynomial lemmas `min`, `unique'`, `irreducible`, `degree_le_of_ne_zero`, `unique` and `dvd`; `adjoinRootEquivAdjoin` with `aeval_gen_minpoly` and `adjoinRootEquivAdjoin_apply_root`; `Basis.map`, `Basis.ofEquivFun`, `Basis.mk` and `leftMulMatrix`; and on the consumer side `Algebra.trace`, `trace_eq_matrix_trace`, `traceForm_toMatrix_powerBasis`, `trace_gen_eq_nextCoeff_minpoly`, `trace_gen_eq_sum_roots`, `trace_eq_trace_adjoin`, `trace_eq_finrank_mul_minpoly_nextCoeff`, `trace_eq_of_algEquiv`, `trace_eq_zero_of_not_isSeparable`, `traceMatrix_of_matrix_vecMul`, `embeddingsMatrixReindex_eq_vandermonde`, `traceMatrix_eq_embeddingsMatrixReindex_mul_trans`, `traceForm_nondegenerate_tfae`, `traceDual_powerBasis_eq`, and the discriminant declarations `discr`, `discr_eq_discr_of_algEquiv`, `discr_of_matrix_vecMul`, `discr_not_zero_of_basis`, `discr_powerBasis_eq_prod` and `discr_powerBasis_eq_norm`. Reread at their call sites: `IntermediateField.powerBasisAux` and `adjoin.powerBasis` (§§5.3.1.8–5.3.1.9), `powerBasisOfFiniteOfSeparable` (§5.3.1.9), `trace_eq_sum_embeddings_gen` and `trace_eq_sum_embeddings` (§5.3.1.8), and `det_traceMatrix_ne_zero'`, `det_traceForm_ne_zero`, `traceForm_nondegenerate` and `FiniteField.trace_to_zmod_nondegenerate` (§5.3.1.7). Inherited without rereading: `exists_primitive_element` and `AlgHom.card` (§5.3.1.9), `sum_embeddings_eq_finrank_mul` (§5.3.1.8), and `RingHom.injective` and `liftEquiv'` (§6.4.15). Used at interface level: `PrincipalIdealRing.isMaximal_of_irreducible`, `Ideal.Quotient.lift`, `Submodule.liftQ`, `Subfield.closure_le`, `AlgEquiv.ofBijective`, `LinearMap.trace_conj'`, `Matrix.det_vandermonde`, `Matrix.aeval_self_charpoly`, `trace_eq_neg_charpoly_coeff`, `trace_trace`, `separableClosure`, `IsPurelyInseparable.finrank_eq_pow`, `Irreducible.hasSeparableContraction`, `minpolyDiv`, `sum_smul_minpolyDiv_eq_X_pow`, `Algebra.norm_eq_prod_embeddings`, `Splits.eval_root_derivative` and `BilinForm.nondegenerate_iff_det_ne_zero`. Theorem 2 is a textbook proof; Mathlib proves its field cases as described. The hand calculations were rechecked by exact arithmetic in the run directory. No Lean kernel replay or full dependency closure was performed. [Source map](../sources/SOURCES.md#power-bases-from-the-quotient-ring-53110)

### 5.3.1.11 The separable greatest common divisor in the primitive element proof

**Motivation.** In Lemma C of §5.3.1.9 the scalar $c$ is chosen, $\gamma=\alpha+c\beta$ is formed, and everything after that happens inside one greatest common divisor, that of $f(\gamma-cX)$ and $g(X)$, where $f$ and $g$ are the minimal polynomials of $\alpha$ and $\beta$. Three facts about this divisor were quoted there. It is the same polynomial whether it is computed over the small field $F(\gamma)$ or over $E$ (`gcd_map`). It inherits separability from $g$ (`separable_gcd_right`). And a separable split polynomial whose only root is $\beta$ is a constant times $X-\beta$ (`eq_X_sub_C_of_separable_of_root_eq`). Together the three facts turn the choice of $c$ into the membership $\beta\in F(\gamma)$, and hence into $F(\alpha+c\beta)=F(\alpha,\beta)$. This subsection opens them down to their producers in the pinned library: the Euclidean algorithm with its Bézout coefficients, separability as a Bézout identity between $g$ and $g'$, and the computation that makes a square factor of a separable polynomial a unit. It then follows the pinned proof along the tower $F\subseteq F(\gamma)\subseteq E\subseteq E'$ with every coefficient map named, writes out the elimination that defines the finitely many excluded scalars, and records what is returned to the adjoin induction of §5.3.1.9. Two complete calculations, one over $\mathbb Q$ and one over $\mathbb F_2(t)$, follow each step, and a purely inseparable example isolates the one step that needs separability. The classical argument is Milne's proof of the primitive element theorem, which transfers the divisor from $L[X]$ to $F[\gamma][X]$ by the invariance of greatest common divisors under field extension. [Milne, *Fields and Galois Theory*, v5.10, Theorem 5.1 and Proposition 2.17, pp. 61–62 and 31](https://www.jmilne.org/math/CourseNotes/FT.pdf)

**Examples [Expository].** In each example $f$ and $g$ are the minimal polynomials of $\alpha$ and $\beta$ over $F$, $\gamma=\alpha+c\beta$, and $a=f(\gamma-cX)$. The greatest common divisor is computed by the recursion of the definitions below: $\gcd(0,b)=b$, and $\gcd(a,b)=\gcd(b\bmod a,\,a)$ for $a\ne0$, where $b\bmod a$ is the remainder of $b$ on division by the monic multiple $a\cdot\mathrm{lc}(a)^{-1}$ of $a$.

1. *The biquadratic field over $\mathbb Q$.* Let $E=\mathbb Q(\sqrt2,\sqrt3)$, $\alpha=\sqrt2$, $\beta=\sqrt3$, so $f=X^2-2$ and $g=X^2-3$, with roots $\pm\sqrt2$ and $\pm\sqrt3$ in $E$ (§5.3.1.9, Example 1). Here $g$ already splits over $E$, so $E'=E$ serves as the field in which the roots are examined.

   (a) *A legal scalar, $c=1$.* Then $\gamma=\sqrt2+\sqrt3$, $\gamma^2=5+2\sqrt6$, and
   $$
   a=f(\gamma-X)=X^2-2\gamma X+(\gamma^2-2),\qquad b=g=X^2-3 .
   $$
   Both polynomials have coefficients in $\mathbb Q(\gamma)$. In the first step $a$ is monic, so $b\bmod a=b-a=2\gamma X-(\gamma^2+1)=:r$. In the second step the monic multiple of $r$ is $X-\frac{\gamma^2+1}{2\gamma}$, and $\frac{\gamma^2+1}{2\gamma}=\sqrt3$ because $\gamma^2+1=6+2\sqrt6=2\sqrt3\,(\sqrt3+\sqrt2)=2\sqrt3\,\gamma$. The remainder of $a$ on division by $X-\sqrt3$ is the constant $a(\sqrt3)=(\gamma-\sqrt3)^2-2=0$. In the third step $\gcd(0,r)=r$. Hence
   $$
   h=\gcd(a,b)=2\gamma X-(\gamma^2+1)=2\gamma\,(X-\sqrt3),
   $$
   with leading coefficient $2\gamma$, and the extended algorithm returns the Bézout identity $h=(-1)\cdot a+1\cdot b$. Reading off the root, $\beta=-p_0/p_1=\frac{\gamma^2+1}{2\gamma}$. Since $\gamma^4-10\gamma^2+1=0$, we have $\gamma^{-1}=10\gamma-\gamma^3$, so $\beta=\frac12(\gamma+\gamma^{-1})=\frac12(11\gamma-\gamma^3)$ and $\alpha=\gamma-\beta=\frac12(\gamma^3-9\gamma)$. These are the formulas of §5.3.1.9, now produced by the algorithm.

   The separability input is visible as well. From $g'=2X$ one gets $u\,g+v\,g'=1$ with $u=-\frac13$ and $v=\frac X6$, which is what "$g$ is separable" means. Write $g=h\,q$ with $q=(X+\sqrt3)/(2\gamma)$. Lemma D below transports the identity to the divisor $h$ as $(uq+vq')\,h+(vq)\,h'=1$, and here
   $$
   (uq+vq')\,h=-\tfrac16\,(X+2\sqrt3)(X-\sqrt3),\qquad (vq)\,h'=\tfrac16\,X(X+\sqrt3),
   $$
   whose sum is $\frac16\bigl(-X^2-\sqrt3X+6+X^2+\sqrt3X\bigr)=1$.

   The excluded values are the quotients $-(\alpha'-\alpha)/(\beta'-\beta)$ over the four root pairs, with $x/0=0$. The two pairs with $\beta'=\sqrt3$ give $0$, the pair $(\sqrt2,-\sqrt3)$ gives $0$, and the pair $(-\sqrt2,-\sqrt3)$ gives $-(-2\sqrt2)/(-2\sqrt3)=-\sqrt6/3$. So $S=\{0,-\sqrt6/3\}$, and the only rational value in $S$ is $0$. Every nonzero rational $c$ is legal.

   (b) *A bad scalar, $c=0$.* Now $\gamma=\sqrt2$ and $a=f(\sqrt2-0\cdot X)$ is the zero polynomial, so the recursion stops at once with $\gcd(0,g)=g=X^2-3$, of degree two. Both roots of $g$ are common roots. For the second one, $x=-\sqrt3$, the corresponding root of $f$ is $\alpha'=\gamma-0\cdot x=\sqrt2=\alpha$, and the elimination returns $c=-(\alpha'-\alpha)/(\beta'-\beta)=0$, a value in $S$. Over $\mathbb Q(\sqrt2)$ the polynomial $X^2-3$ has no root (§5.3.1.9, Example 1), so the divisor computed over $F(\gamma)$ is not linear and $\beta\notin\mathbb Q(\gamma)$.

   (c) *A bad scalar that is not rational.* Take the base field $F=\mathbb Q(\sqrt6)$ instead. Neither $\sqrt2$ nor $\sqrt3$ lies in $F$: from $\sqrt2=x+y\sqrt6$ with $x,y\in\mathbb Q$, squaring forces $xy=0$, and then $\sqrt2=x$ is rational or $6y^2=2$, both impossible; the same argument with $6y^2=3$ applies to $\sqrt3$. So $f$ and $g$ are still the minimal polynomials and $[E:F]=2$, but now both elements of $S$ are scalars. For $c=-\sqrt6/3$ one finds $\gamma=\sqrt2-\frac{\sqrt6}{3}\sqrt3=\sqrt2-\sqrt2=0$. Then $a=f(-cX)=c^2X^2-2=\frac23\,(X^2-3)$, whose monic multiple is $g$ itself, so the first step gives $b\bmod a=0$ and $\gcd(a,b)=a=\frac23\,(X^2-3)$. The common root $x=-\sqrt3$ corresponds to $\alpha'=\gamma-cx=c\sqrt3=-\sqrt2$, and indeed $-(\alpha'-\alpha)/(x-\beta)=-(-2\sqrt2)/(-2\sqrt3)=-\sqrt6/3=c$. The same element of $S$ is harmless over $\mathbb Q$, where it is not a scalar. The legal scalar $c=1$ works over $\mathbb Q(\sqrt6)$ by the computation of (a), word for word.

2. *A separable tower in characteristic two.* Let $F=\mathbb F_2(t)$, the field of rational functions over $\mathbb F_2$, which is infinite. Let $\alpha$ be a root of $f=X^2+X+t$ and $\beta$ a root of $g=X^2+X+(t+1)$, and $E=F(\alpha,\beta)$.

   *Degrees.* For $r\in F$ let $v(r)$ be the order of $r$ at infinity, $v(n/d)=\deg d-\deg n$ for polynomials $n,d$. If $v(r)<0$ then $v(r^2+r)=2v(r)$ is even, and if $v(r)\ge0$ then $v(r^2+r)\ge0$. Since $v(t)=v(t+1)=-1$, neither $r^2+r=t$ nor $r^2+r=t+1$ has a solution in $F$, so $f$ and $g$ are irreducible and $[F(\alpha):F]=2$. Next, let $y=x+w\alpha$ with $x,w\in F$. Using $\alpha^2=\alpha+t$,
   $$
   y^2+y=(x^2+x+w^2t)+(w^2+w)\,\alpha .
   $$
   If $y^2+y=t+1$, the coefficient of $\alpha$ forces $w\in\{0,1\}$. For $w=0$ we would need $x^2+x=t+1$, excluded above. For $w=1$ we would need $x^2+x=1$; at a pole of $x$ of order $m\ge1$, at a finite place or at infinity, the left side has a pole of order $2m$, so $x$ has no poles, hence is a constant in $\mathbb F_2$, and $0^2+0=1^2+1=0\ne1$. So $g$ has no root in $F(\alpha)$, $[E:F(\alpha)]=2$ and $[E:F]=4$.

   *Separability.* In characteristic two $f'=g'=2X+1=1$, so $0\cdot f+1\cdot f'=1$ and $0\cdot g+1\cdot g'=1$: both $f$ and $g$ are separable, and $E/F$ is separable because it is generated by separable elements [Milne, *Fields and Galois Theory*, v5.10, Remark 3.15, p. 39](https://www.jmilne.org/math/CourseNotes/FT.pdf). Since $(y+1)^2+(y+1)=y^2+y$, the roots of $f$ are $\alpha,\alpha+1$ and those of $g$ are $\beta,\beta+1$, all in $E$; again $E'=E$.

   *Excluded values.* The pairs with $\beta'=\beta$ give $0$, the pair $(\alpha,\beta+1)$ gives $-0/1=0$, and the pair $(\alpha+1,\beta+1)$ gives $-1/1=-1=1$. So $S=\{0,1\}=\mathbb F_2$: the excluded scalars are exactly the prime field.

   (a) *The bad scalar $c=1$.* Here $\gamma=\alpha+\beta$ and $\gamma^2+\gamma=(\alpha^2+\alpha)+(\beta^2+\beta)=t+(t+1)=1$, so $\gamma$ is a root of $X^2+X+1$, which has no root in $F$ by the last argument. Thus $F(\gamma)=\mathbb F_4(t)$ is a quadratic subfield and $F(\gamma)\ne E$. In the algorithm, $(\gamma-X)^2=\gamma^2+X^2$ and $-X=X$ in characteristic two, so
   $$
   a=f(\gamma-X)=X^2+X+(\gamma^2+\gamma+t)=X^2+X+(t+1)=g .
   $$
   The first step gives $g\bmod g=0$ and $\gcd(a,b)=g$, of degree two. The second root $x=\beta+1$ of $g$ corresponds to $\alpha'=\gamma-x=\alpha+1$, and the elimination returns $-(\alpha'-\alpha)/(x-\beta)=-1/1=1=c$. For $c=0$ one has $a=f(\alpha)=0$ and $\gcd(0,g)=g$ again.

   (b) *The legal scalar $c=t$.* Now $\gamma=\alpha+t\beta$ and
   $$
   a=f(\gamma-tX)=t^2X^2+tX+(\gamma^2+\gamma+t),\qquad b=g=X^2+X+(t+1).
   $$
   The monic multiple of $a$ is $X^2+t^{-1}X+e$ with $e=(\gamma^2+\gamma+t)/t^2$, and one subtraction gives
   $$
   r=b\bmod a=\frac{t+1}{t}\,X+\Bigl((t+1)+\frac{\gamma^2+\gamma+t}{t^2}\Bigr),
   $$
   whose coefficients lie in $F(\gamma)$. To locate its root, expand with $\alpha^2=\alpha+t$ and $\beta^2=\beta+t+1$: $\gamma^2+\gamma=(\alpha^2+\alpha)+t^2\beta^2+t\beta=t+t^2(\beta+t+1)+t\beta$, so $\gamma^2+\gamma+t=(t^2+t)\beta+t^3+t^2$ and $e=\frac{t+1}{t}\beta+(t+1)$. Hence $r=\frac{t+1}{t}(X+\beta)=\frac{t+1}{t}(X-\beta)$. In the second step the remainder of $a$ on division by $X-\beta$ is $a(\beta)=f(\gamma-t\beta)=f(\alpha)=0$, and the third step returns $r$. So
   $$
   h=\frac{t+1}{t}\,(X-\beta),\qquad
   \beta=-\frac{p_0}{p_1}=t+\frac{\gamma^2+\gamma+t}{t^2+t}\in F(\gamma),\qquad
   \alpha=\gamma+t\beta ,
   $$
   and $E=F(\alpha+t\beta)$. The extended algorithm returns $h=t^{-2}\,a+1\cdot b$. The transported Bézout identity is equally explicit: $g=h\,q$ with $q=\frac{t}{t+1}(X+\beta+1)$, and from $u=0$, $v=1$ one gets $(uq+vq')\,h+(vq)\,h'=(X+\beta)+(X+\beta+1)=1$.

3. *A purely inseparable failure.* Let $K=\mathbb F_2(s,t)$ and $L=K(\alpha,\beta)$ with $\alpha^2=s$ and $\beta^2=t$. This is the case $p=2$ of §5.3.1.9, Example 3: $[L:K]=4$, and $\gamma^2\in K$ for every $\gamma\in L$, so $L/K$ is purely inseparable. Here $f=X^2+s$ and $g=X^2+t$, both with derivative $2X=0$. For $c\in K$ and $\gamma=\alpha+c\beta$ we have $\gamma^2=s+c^2t$, hence
   $$
   a=f(\gamma-cX)=\gamma^2+c^2X^2+s=c^2X^2+c^2t=c^2\,g(X).
   $$
   For $c\ne0$ the monic multiple of $a$ is $g$, so the first step gives $b\bmod a=0$ and $\gcd(a,b)=a=c^2(X-\beta)^2$, because $X^2+t=(X-\beta)^2$ in $L[X]$. For $c=0$ the divisor is $g$. The roots of $f$ and $g$ in $L$ are $\alpha$ and $\beta$, each twice, so every quotient is $-0/0=0$ and $S=\{0\}$: every $c\ne0$ passes the exclusion. The divisor vanishes at $\beta$, splits over $L$, and has no root other than $\beta$. What fails is separability. A Bézout identity $u\,g+v\,g'=1$ would read $u\,g=1$, which is impossible, so `separable_gcd_right` has no input, and the root $\beta$ of the divisor has multiplicity two. Theorem G below locates the failure in its Steps 1 and 4.

**Definitions.** Let $K$ be a field.

- *Division in $K[X]$.* For $q\ne0$ Mathlib divides by the monic multiple $q\cdot\mathrm{lc}(q)^{-1}$ with the monic division of §5.3.1.10, Lemma A, and rescales the quotient:
  $$
  p\bmod q=p\mathbin{\mathrm{mod}_m}\bigl(q\cdot\mathrm{lc}(q)^{-1}\bigr),\qquad
  p\mathbin{\mathrm{div}}q=\mathrm{lc}(q)^{-1}\cdot\bigl(p\mathbin{\mathrm{div}_m}(q\cdot\mathrm{lc}(q)^{-1})\bigr),
  $$
  written `p % q` and `p / q`. Since $\mathrm{lc}(0)^{-1}=0$, the same formulas give $p\bmod0=p$ and $p\mathbin{\mathrm{div}}0=0$. With degree as the well-founded measure this makes $K[X]$ a Euclidean domain (`Polynomial.instEuclideanDomain`).
- *Euclidean greatest common divisor.* `EuclideanDomain.gcd a b` is defined by recursion on $a$: $\gcd(0,b)=b$ and $\gcd(a,b)=\gcd(b\bmod a,\,a)$ for $a\ne0$. It is one specific polynomial, in general not monic.
- *Extended algorithm.* `xgcdAux` updates two triples $(r,\sigma,\tau)$ and $(r',\sigma',\tau')$ to $(r'\bmod r,\ \sigma'-q\sigma,\ \tau'-q\tau)$ and $(r,\sigma,\tau)$ with $q=r'\mathbin{\mathrm{div}}r$, stopping when $r=0$; started from $(a,1,0)$ and $(b,0,1)$ it returns the coefficients `gcdA a b` and `gcdB a b`.
- *Greatest common divisors up to units.* A polynomial $d$ is a greatest common divisor of $a$ and $b$ if $d\mid a$, $d\mid b$, and every common divisor of $a$ and $b$ divides $d$. The units of $K[X]$ are the nonzero constants. If $a$ or $b$ is nonzero, exactly one greatest common divisor is monic; we call it the monic gcd.
- *Coprimality and separability.* `IsCoprime x y` means $ux+vy=1$ for some $u,v$. A polynomial $f$ is separable (`Polynomial.Separable`) if `IsCoprime f f'`, that is, if $u\,f+v\,f'=1$ for some polynomials $u,v$. This is the condition $\gcd(f,f')=1$ of Milne's Definition 2.22, stated for every polynomial, and for irreducible $f$ it is the Stacks Project's Definition 9.12.2. An algebraic element is separable if its minimal polynomial is.
- *Roots and multiplicities.* Over a domain, `p.roots` is the multiset of roots of $p\ne0$, each repeated according to its multiplicity, and for $p\ne0$ `rootMultiplicity x p` is the largest $m$ with $(X-x)^m\mid p$. The number of times $x$ occurs in `p.roots` is `rootMultiplicity x p` (`count_roots`).
- *Splitting.* At the pinned commit `Splits p` is a predicate on $p$ itself: $p$ is a product of constants and monic linear polynomials. Over a domain this means $p=\mathrm{lc}(p)\prod_{x}(X-x)$, the product over `p.roots` (`Splits.eq_prod_roots`).
- *Maps.* For a ring homomorphism $\varphi:K\to L$, $p^\varphi$ (`p.map φ`) applies $\varphi$ to the coefficients. A homomorphism of fields is injective, so $\deg p^\varphi=\deg p$ and $\mathrm{lc}(p^\varphi)=\varphi(\mathrm{lc}\,p)$ (`degree_map`, `leadingCoeff_map`).

[Mathlib/Algebra/Polynomial/FieldDivision.lean:273–286,310–367](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/FieldDivision.lean#L273-L367) · [Mathlib/Algebra/EuclideanDomain/Defs.lean:164–235](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/EuclideanDomain/Defs.lean#L164-L235) · [Mathlib/RingTheory/Coprime/Basic.lean:41–46](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Coprime/Basic.lean#L41-L46) · [Mathlib/FieldTheory/Separable.lean:42–58](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Separable.lean#L42-L58) · [Mathlib/Algebra/Polynomial/Splits.lean:36](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Splits.lean#L36) · [Milne, *Fields and Galois Theory*, v5.10, Definition 2.22, p. 33](https://www.jmilne.org/math/CourseNotes/FT.pdf) · [Stacks Project, Definition 9.12.2](https://stacks.math.columbia.edu/tag/09H1)

**Lemma A (division commutes with ring maps; `map_mod_divByMonic`, `map_div`, `map_mod`) [Lean, read].** Let $\varphi:R\to S$ be a homomorphism of rings and let $q\in R[X]$ be monic. Then for every $p\in R[X]$,
$$
(p\mathbin{\mathrm{div}_m} q)^\varphi=p^\varphi\mathbin{\mathrm{div}_m} q^\varphi,\qquad (p\mathbin{\mathrm{mod}_m} q)^\varphi=p^\varphi\mathbin{\mathrm{mod}_m} q^\varphi .
$$
If $\varphi:K\to L$ is a homomorphism of fields, then $(p\mathbin{\mathrm{div}}q)^\varphi=p^\varphi\mathbin{\mathrm{div}}q^\varphi$ and $(p\bmod q)^\varphi=p^\varphi\bmod q^\varphi$ for all $p,q\in K[X]$.

*Proof.* Write $p=q\,d+r$ with $d=p\mathbin{\mathrm{div}_m} q$, $r=p\mathbin{\mathrm{mod}_m} q$ and $\deg r<\deg q$ (§5.3.1.10, Lemma A). Applying $\varphi$ to coefficients is a ring homomorphism $R[X]\to S[X]$, so $p^\varphi=q^\varphi d^\varphi+r^\varphi$. If $S$ is the zero ring there is nothing to prove. Otherwise $q^\varphi$ is monic of degree $\deg q$, because its leading coefficient is $\varphi(1)=1\ne0$, and $\deg r^\varphi\le\deg r<\deg q=\deg q^\varphi$ (`degree_map_le`, `degree_map_eq_of_leadingCoeff_ne_zero`). By the uniqueness of quotient and remainder for the monic divisor $q^\varphi$ (`div_modByMonic_unique`), $d^\varphi$ and $r^\varphi$ are the quotient and the remainder of $p^\varphi$. Now let $\varphi$ be a homomorphism of fields. For $q=0$ both sides are given by the conventions. For $q\ne0$, injectivity gives $\mathrm{lc}(q^\varphi)=\varphi(\mathrm{lc}\,q)$ (`leadingCoeff_map`), and $\varphi$ preserves inverses (`map_inv₀`), so $\bigl(q\cdot\mathrm{lc}(q)^{-1}\bigr)^\varphi=q^\varphi\cdot\mathrm{lc}(q^\varphi)^{-1}$. The monic case applied to this monic multiple gives the statement for the remainder, and for the quotient after multiplying by $\varphi(\mathrm{lc}(q)^{-1})=\mathrm{lc}(q^\varphi)^{-1}$. $\square$ [Mathlib/Algebra/Polynomial/Div.lean:373–395](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Div.lean#L373-L395) · [Mathlib/Algebra/Polynomial/FieldDivision.lean:411–421](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/FieldDivision.lean#L411-L421)

Injectivity enters only through the leading coefficient: the monic statement holds for every ring map, while the normalization $q\cdot\mathrm{lc}(q)^{-1}$ commutes with $\varphi$ because a field homomorphism cannot kill $\mathrm{lc}(q)$.

**Lemma B (the Euclidean gcd commutes with field homomorphisms; `Polynomial.gcd_map`) [Lean, read].** Let $\varphi:K\to L$ be a homomorphism of fields. For all $a,b\in K[X]$,
$$
\gcd\bigl(a^\varphi,b^\varphi\bigr)=\gcd(a,b)^\varphi
$$
in $L[X]$, as an equality of polynomials and not only up to a unit.

*Proof.* The pinned proof is an induction along the recursion that defines $\gcd$ (`EuclideanDomain.GCD.induction`): it suffices to treat $a=0$, and, for $a\ne0$, to deduce the claim for $(a,b)$ from the claim for $(b\bmod a,\,a)$. The recursion terminates because $\deg(b\bmod a)<\deg a$. For $a=0$ both sides equal $b^\varphi$ (`gcd_zero_left`). For $a\ne0$,
$$
\begin{aligned}
\gcd(a^\varphi,b^\varphi)&=\gcd\bigl(b^\varphi\bmod a^\varphi,\ a^\varphi\bigr)\\
&=\gcd\bigl((b\bmod a)^\varphi,\ a^\varphi\bigr)\\
&=\gcd(b\bmod a,\ a)^\varphi=\gcd(a,b)^\varphi .
\end{aligned}
$$
The first and last equalities are `gcd_val`, the identity $\gcd(x,y)=\gcd(y\bmod x,\,x)$, which holds for all $x$ because $y\bmod0=y$ and $\gcd(y,0)=y$ (`gcd_zero_right`); so no case distinction on $a^\varphi$ is needed in $L[X]$. The second is Lemma A and the third is the induction hypothesis. $\square$ [Mathlib/Algebra/Polynomial/FieldDivision.lean:457–460](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/FieldDivision.lean#L457-L460) · [Mathlib/Algebra/EuclideanDomain/Defs.lean:164–193](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/EuclideanDomain/Defs.lean#L164-L193) · [Mathlib/Algebra/EuclideanDomain/Basic.lean:127–134](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/EuclideanDomain/Basic.lean#L127-L134)

Thus the algorithm over $F(\gamma)$ performs exactly the divisions it performs over $E$; every remainder of Example 1(a) and Example 2(b) visibly has coefficients in $F(\gamma)$.

**Proposition C (Bézout, common roots and units).** Let $K$ be a field, $a,b\in K[X]$ and $d=\gcd(a,b)$.

1. (`gcd_eq_gcd_ab`) $d=a\cdot\mathrm{gcdA}(a,b)+b\cdot\mathrm{gcdB}(a,b)$. [Lean, read]
2. (`gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`, `gcd_eq_zero_iff`) $d$ divides $a$ and $b$, every common divisor of $a$ and $b$ divides $d$, and $d=0$ only if $a=b=0$. [Lean, read]
3. (`eval₂_gcd_eq_zero`, `root_left_of_root_gcd`, `root_right_of_root_gcd`) For a ring homomorphism $\psi:K\to R$ into a commutative ring and $x\in R$, $d^\psi(x)=0$ if and only if $a^\psi(x)=0$ and $b^\psi(x)=0$. [Lean, read]
4. For a homomorphism of fields $\varphi:K\to L$, every greatest common divisor of $a^\varphi$ and $b^\varphi$ in $L[X]$ is $\lambda\,d^\varphi$ for some $\lambda\in L^\times$. If $a$ or $b$ is nonzero, the monic gcd of $a^\varphi$ and $b^\varphi$ is the image $\bigl(d\cdot\mathrm{lc}(d)^{-1}\bigr)^\varphi$ of the monic gcd of $a$ and $b$. [Expository]

*Proof.* (1) The two triples of the extended algorithm satisfy $r=a\sigma+b\tau$ and $r'=a\sigma'+b\tau'$ at the start, for $(a,1,0)$ and $(b,0,1)$. The update keeps both identities, because $r'\bmod r=r'-r\,(r'\mathbin{\mathrm{div}}r)$ (`mod_eq_sub_mul_div`) gives $r'\bmod r=a(\sigma'-q\sigma)+b(\tau'-q\tau)$ for $q=r'\mathbin{\mathrm{div}}r$ (`xgcdAux_P`). The first components follow the recursion of $\gcd$ (`xgcdAux_fst`), so the algorithm ends with $r'=d$ and coefficients $\mathrm{gcdA}$ and $\mathrm{gcdB}$ (`xgcdAux_val`). (2) By the same induction: $\gcd(0,b)=b$ divides $0$ and $b$; and if $\gcd(b\bmod a,a)$ divides $b\bmod a$ and $a$, it divides $b=a\,(b\mathbin{\mathrm{div}}a)+b\bmod a$ (`dvd_mod_iff`). In the same way a common divisor of $a$ and $b$ divides $b\bmod a$, hence $\gcd(b\bmod a,a)$. If $d=0$, then $a$ and $b$ are multiples of $0$. (3) If $a^\psi(x)=b^\psi(x)=0$, evaluate (1): evaluation at $x$ after $\psi$ is a ring homomorphism $K[X]\to R$, so $d^\psi(x)=a^\psi(x)\,\mathrm{gcdA}^\psi(x)+b^\psi(x)\,\mathrm{gcdB}^\psi(x)=0$. Conversely $a=d\,a_1$ gives $a^\psi(x)=d^\psi(x)\,a_1^\psi(x)=0$, and likewise for $b$. (4) By Lemma B and (2) over $L$, $d^\varphi$ is a greatest common divisor of $a^\varphi$ and $b^\varphi$. Two greatest common divisors $e,e'$ divide each other; if $e'=e\,\lambda$ and $e=e'\,\mu$ with $e\ne0$, then $\lambda\mu=1$, so $\lambda$ and $\mu$ are nonzero constants. If $a$ or $b$ is nonzero then $d\ne0$, the monic gcd of $a,b$ is $d\cdot\mathrm{lc}(d)^{-1}$, and its image is monic because $\varphi(\mathrm{lc}(d)^{-1})=\mathrm{lc}(d^\varphi)^{-1}$. Without Lemma B one argues as Milne does: $d^\varphi$ divides $a^\varphi$ and $b^\varphi$, hence every greatest common divisor $e$ of them, and $e$ divides $a^\varphi\,\mathrm{gcdA}(a,b)^\varphi+b^\varphi\,\mathrm{gcdB}(a,b)^\varphi=d^\varphi$ by (1), so $e$ and $d^\varphi$ are associates. $\square$ [Mathlib/Algebra/EuclideanDomain/Basic.lean:44–68,136–210](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/EuclideanDomain/Basic.lean#L136-L210) · [Mathlib/Algebra/Polynomial/FieldDivision.lean:464–491](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/FieldDivision.lean#L464-L491) · [Milne, *Fields and Galois Theory*, v5.10, 1.8 and Proposition 2.17, pp. 10–11 and 31](https://www.jmilne.org/math/CourseNotes/FT.pdf)

This is the precise sense in which a greatest common divisor survives a field embedding: any two choices of it in $L[X]$ differ by a nonzero constant, the monic one is the image of the monic one over $K$, and the Euclidean one is the image of the Euclidean one over $K$. For the primitive element proof the constant never matters, since the root $-p_0/p_1$ of a linear polynomial does not change when the polynomial is multiplied by a unit. In Example 1(a) the Euclidean divisor $2\gamma(X-\sqrt3)$ is not monic, and its leading coefficient $2\gamma$ is the constant `C h.leadingCoeff` of the pinned proof.

**Lemma D (separability is a Bézout identity and passes to divisors; `Separable.of_mul_left`, `Separable.of_dvd`, `separable_gcd_right`, `Separable.map`) [Lean, read].** Let $R$ be a commutative ring.

1. If $fg$ is separable, so is $f$. Explicitly, $u\,(fg)+v\,(fg)'=1$ implies $(ug+vg')\,f+(vg)\,f'=1$.
2. If $f$ is separable and $h\mid f$, then $h$ is separable. In particular, over a field $K$, $\gcd(a,g)$ is separable for every $a$ whenever $g$ is separable.
3. If $f$ is separable and $\varphi:R\to S$ is a ring homomorphism, then $f^\varphi$ is separable: $u\,f+v\,f'=1$ implies $u^\varphi f^\varphi+v^\varphi\,(f^\varphi)'=1$.

*Proof.* (1) By the product rule $(fg)'=f'g+fg'$ (`derivative_mul`), so $1=ufg+vf'g+vfg'=(ug+vg')\,f+(vg)\,f'$. The pinned proof performs this in three steps on `IsCoprime`: it drops the factor $g$ from the first argument (`IsCoprime.of_mul_left_left`, which replaces $u$ by $ug$), drops the multiple $f\cdot g'$ of the first argument from the second (`IsCoprime.of_add_mul_left_right`), and drops the factor $g$ from the remaining $f'g$ (`IsCoprime.of_mul_right_left`). (2) Write $f=hk$ and apply (1) to $h\cdot k$. For the greatest common divisor, $\gcd(a,g)\mid g$ by Proposition C (2). (3) Apply $\varphi$ to the identity and use $(f^\varphi)'=(f')^\varphi$ (`derivative_map`). $\square$ [Mathlib/FieldTheory/Separable.lean:79–99,117–121](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Separable.lean#L79-L121) · [Mathlib/RingTheory/Coprime/Basic.lean:132–146,185–201](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Coprime/Basic.lean#L132-L201)

No property of $a$ enters (2): the divisor inherits separability from its second argument alone. In the primitive element proof this is the only place where the separability of $\beta$ is used.

**Lemma E (a separable polynomial has only simple roots; `isUnit_of_self_mul_dvd_separable` through `nodup_roots`) [Lean, read].** Let $R$ be a commutative ring and $p\in R[X]$ separable.

1. If $q\cdot q\mid p$, then $q$ is a unit.
2. If $R$ is nontrivial, then `rootMultiplicity x p` $\le1$ for every $x\in R$.
3. If $R$ is a domain, then the multiset `p.roots` has no repeated element.

*Proof.* (1) Write $p=q\cdot(q\cdot r)$. Two applications of the product rule give $p'=q\,(q'r+q'r+qr')$, so $p$ and $p'$ are both multiples of $q$. From $u\,p+v\,p'=1$ we get $q\cdot\bigl(uqr+v\,(2q'r+qr')\bigr)=1$, and $q$ is a unit. The pinned proof writes $p'$ in exactly this form by `derivative_mul` and `ring`, drops factors as in Lemma D to reach `IsCoprime q q`, and concludes with `isCoprime_self`. (2) A separable polynomial over a nontrivial ring is nonzero (`not_separable_zero`: $u\cdot0+v\cdot0'=0\ne1$). For $p\ne0$ the root multiplicity is the multiplicity of $X-x$ in $p$, which is finite. If it were at least two, then $(X-x)^2\mid p$ and $X-x$ would be a unit by (1), which it is not (`not_isUnit_X_sub_C`). (3) The number of occurrences of $x$ in `p.roots` is `rootMultiplicity x p` (`count_roots`), at most one by (2), and a multiset in which every element occurs at most once has no repetition. $\square$ [Mathlib/FieldTheory/Separable.lean:151–178,269–291](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Separable.lean#L151-L291) · [Milne, *Fields and Galois Theory*, v5.10, Lemma 2.19 and Proposition 2.21, pp. 32–33](https://www.jmilne.org/math/CourseNotes/FT.pdf) · [Stacks Project, Lemma 9.12.4](https://stacks.math.columbia.edu/tag/09H3)

Part (1) is the repeated-root half of Milne's Proposition 2.21 and of the Stacks Project's Lemma 9.12.4, stated without a splitting field: a square factor of a separable polynomial is a unit. The converse, that a split polynomial with distinct roots is separable, is `nodup_roots_iff_of_splits` and is not used here.

**Lemma F (separable, split, with one root; `eq_X_sub_C_of_separable_of_root_eq`) [Lean, read].** Let $i:K\to L$ be a homomorphism of fields, $x\in K$, and $h\in K[X]$ separable with $h(x)=0$. If $h^i$ splits over $L$ and every root of $h^i$ in $L$ equals $i(x)$, then $h=\mathrm{lc}(h)\,(X-x)$.

*Proof.* $h\ne0$, since the zero polynomial is not separable (`not_separable_zero`). The multiset of roots of $h^i$ contains $i(x)$, because $h^i(i(x))=i(h(x))=0$; it has no repetition by Lemma D (3) and Lemma E (3); and all its elements equal $i(x)$. Hence it is the singleton $\{i(x)\}$. A split polynomial over a domain is its leading coefficient times the product of $X-y$ over its roots (`Splits.eq_prod_roots`), so $h^i=\mathrm{lc}(h^i)\,(X-i(x))=\bigl(\mathrm{lc}(h)\,(X-x)\bigr)^i$ (`Splits.eq_X_sub_C_of_single_root`). Applying $i$ to coefficients is injective, so $h=\mathrm{lc}(h)\,(X-x)$. $\square$ [Mathlib/FieldTheory/Separable.lean:477–494](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/Separable.lean#L477-L494) · [Mathlib/Algebra/Polynomial/Splits.lean:299–305,357–360](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Splits.lean#L299-L360)

**Theorem G (the linear divisor and $F(\alpha+c\beta)=F(\alpha,\beta)$; `primitive_element_inf_aux`) [Lean, read].** Let $E/F$ be an extension of fields with structure map $\iota:F\to E$. Let $\alpha,\beta\in E$ be algebraic over $F$ with minimal polynomials $f$ and $g$, and assume that $\beta$ is separable over $F$. Let $\kappa:E\to E'$ be a homomorphism of fields such that $g^{\kappa\iota}$ splits over $E'$. Let $c\in F$ satisfy the exclusion condition

(†) $\kappa\iota(c)\ne-(\alpha'-\kappa\alpha)/(\beta'-\kappa\beta)$ for every root $\alpha'$ of $f^{\kappa\iota}$ and every root $\beta'$ of $g^{\kappa\iota}$ in $E'$, with $y/0=0$.

Put $\gamma=\alpha+c\beta$, let $j:F(\gamma)\to E$ be the inclusion, and form
$$
h=\gcd\bigl(f^{\iota}(\gamma-cX),\ g^{\iota}\bigr)\in E[X],\qquad
p=\gcd\bigl(f^{F(\gamma)}(\gamma-cX),\ g^{F(\gamma)}\bigr)\in F(\gamma)[X],
$$
where $f^{F(\gamma)}$ and $g^{F(\gamma)}$ have their coefficients in $F(\gamma)$, and $c$ inside each polynomial stands for its image in $E$, respectively in $F(\gamma)$. Then:

1. $h$ is separable, $h(\beta)=0$, every root of $h^\kappa$ in $E'$ equals $\kappa\beta$, and $h=\mathrm{lc}(h)\,(X-\beta)$ with $\mathrm{lc}(h)\ne0$.
2. $p^j=h$. Hence $p=p_1X+p_0$ with $p_1\ne0$, and $\beta=-p_0/p_1\in F(\gamma)$.
3. $F(\alpha,\beta)=F(\gamma)$.

The pinned proof takes $E'$ to be a splitting field of $g^\iota$ over $E$ with its structure map as $\kappa$, chooses $c$ by Lemma B of §5.3.1.9, which needs $F$ infinite, and states only the existence of $\gamma$. Its hypothesis `Algebra.IsSeparable F E` is used for the integrality of $\alpha$ and $\beta$ and for the separability of $\beta$, and the lines after the choice of $c$ use nothing about $c$ beyond condition (†).

*Proof.* Write $a_E=f^\iota(\gamma-cX)$.

*Step 0 (common root).* Both $a_E$ and $g^\iota$ vanish at $\beta$: $g(\beta)=0$, and $a_E(\beta)=f^\iota(\gamma-c\beta)=f^\iota(\alpha)=0$ because $\gamma-c\beta=\alpha$. Since $g\ne0$, also $g^\iota\ne0$ and $h\ne0$ (Proposition C (2)), so $\mathrm{lc}(h)\ne0$. By Proposition C (3) with $\psi$ the identity, $h(\beta)=0$ (`h_root`, by `eval_gcd_eq_zero`, that is, by the Bézout identity).

*Step 1 (separability).* $g^\iota$ is separable by Lemma D (3), and $h\mid g^\iota$, so $h$ is separable by Lemma D (2) (`h_sep`, by `separable_gcd_right`).

*Step 2 (splitting).* By Lemma B for $\kappa$, $h^\kappa=\gcd\bigl(a_E^\kappa,\ g^{\kappa\iota}\bigr)$, which divides the nonzero split polynomial $g^{\kappa\iota}$. A divisor of a nonzero split polynomial splits (`Splits.of_dvd`, from `splits_mul`: if a nonzero product splits, peel off a root of the product, which divides one of the factors since $X-y$ is prime, and induct on the degree). This is `h_splits`. Mapping the divisibility $h\mid g^\iota$ directly would serve equally; the pinned proof uses `gcd_map` here a first time.

*Step 3 (elimination).* Let $x\in E'$ be a root of $h^\kappa$. By Proposition C (3) for $\psi=\kappa$, $x$ is a root of $g^{\kappa\iota}$, and $\alpha'=\kappa\gamma-\kappa\iota(c)\,x$ is a root of $f^{\kappa\iota}$, since $a_E^\kappa(x)=f^{\kappa\iota}(\kappa\gamma-\kappa\iota(c)\,x)$. Suppose $x\ne\kappa\beta$. Since $\kappa\gamma=\kappa\alpha+\kappa\iota(c)\,\kappa\beta$,
$$
\alpha'-\kappa\alpha=\kappa\iota(c)\,(\kappa\beta-x),\qquad\text{hence}\qquad -\frac{\alpha'-\kappa\alpha}{x-\kappa\beta}=\kappa\iota(c),
$$
which contradicts (†) at the pair $(\alpha',x)$. So every root of $h^\kappa$ is $\kappa\beta$ (`h_roots`).

*Step 4 (linear).* Lemma F with $i=\kappa$ and Steps 0–3 give $h=\mathrm{lc}(h)\,(X-\beta)$. This proves (1).

*Step 5 (descent to $F(\gamma)$).* The structure map of $E$ factors as $\iota=j\circ\iota_{F(\gamma)}$ (`IsScalarTower.algebraMap_eq`), so $(f^{F(\gamma)})^j=f^\iota$ and $(g^{F(\gamma)})^j=g^\iota$ (`Polynomial.map_map`). The element $\gamma$ of $F(\gamma)$ maps to $\gamma$ (`AdjoinSimple.algebraMap_gen`), and mapping coefficients commutes with substituting $\gamma-cX$ (`map_comp`, `map_sub`, `map_C`, `map_mul`, `map_X`). Lemma B for $j$ therefore gives $p^j=h$, the second use of `gcd_map`. Comparing coefficients in $p^j=\mathrm{lc}(h)\,(X-\beta)$ gives $j(p_1)=\mathrm{lc}(h)\ne0$, $j(p_0)=-\mathrm{lc}(h)\,\beta$ and $p_k=0$ for $k\ge2$, so $\beta=j(-p_0/p_1)$ (`finale`, by `coeff_map`, `map_div₀` and `mul_div_cancel_left₀`). This proves (2).

*Step 6 (the two fields).* Since $\beta\in F(\gamma)$, also $\alpha=\gamma-c\beta\in F(\gamma)$, so $F(\alpha,\beta)\subseteq F(\gamma)$ (`adjoin_le_iff`). Conversely $\gamma=\alpha+c\beta\in F(\alpha,\beta)$ gives $F(\gamma)\subseteq F(\alpha,\beta)$ (`adjoin_simple_le_iff`). This proves (3). $\square$ [Mathlib/FieldTheory/PrimitiveElement.lean:100–167](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L100-L167) · [Mathlib/Algebra/Polynomial/FieldDivision.lean:497–499](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/FieldDivision.lean#L497-L499) · [Mathlib/Algebra/Polynomial/Splits.lean:436–478](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Polynomial/Splits.lean#L436-L478)

The tower and its maps, as they occur in the pinned proof, are
$$
F\xrightarrow{\ \iota_{F(\gamma)}\ }F(\gamma)\xrightarrow{\ j\ }E\xrightarrow{\ \kappa\ }E'=\mathrm{SplittingField}\bigl(g^\iota\bigr),\qquad \iota=j\circ\iota_{F(\gamma)} .
$$
The divisor $p$ is formed with $\iota_{F(\gamma)}$ (`algebraMap F F⟮γ⟯`), the divisor $h$ with $\iota$ (`ιFE`), the roots are examined with $\kappa$ (`ιEE'`), and the excluded values of Lemma B of §5.3.1.9 are computed for the composite $\kappa\iota$ (`ιEE'.comp ιFE`). The lemma `gcd_map` is applied once along $\kappa$ (Step 2) and once along $j$ (Step 5).

**The excluded scalars.** Step 3 is the whole reason for condition (†). A common root $x=\beta'$ of $g$ and of $f(\gamma-cX)$ produces the root $\alpha'=\gamma-c\beta'$ of $f$, that is, a second way of writing $\gamma=\alpha+c\beta=\alpha'+c\beta'$. Eliminating $\gamma$ leaves the linear equation
$$
(\alpha'-\alpha)+c\,(\beta'-\beta)=0,
$$
which for $\beta'\ne\beta$ has the single solution $c=-(\alpha'-\alpha)/(\beta'-\beta)$. The bad values therefore form the finite set
$$
S=\Bigl\{-\frac{\alpha'-\kappa\alpha}{\beta'-\kappa\beta}\ :\ f^{\kappa\iota}(\alpha')=0,\ g^{\kappa\iota}(\beta')=0\Bigr\}\subseteq E',
$$
with at most $\deg f\cdot\deg g$ elements, the pairs with $\beta'=\kappa\beta$ contributing $0$. The scalars to avoid are $(\kappa\iota)^{-1}(S)\subseteq F$, of at most the same size because $\kappa\iota$ is injective. Lemma B of §5.3.1.9 (`primitive_element_inf_aux_exists_c`) assembles $S$ as a `Finset` from the two root multisets, pulls it back along $\kappa\iota$, and takes $c$ outside the preimage by `Infinite.exists_notMem_finset`: if every element of an infinite type lay in one finite set, the type would be finite (`Fintype.false`). Condition (†) is sufficient, not necessary. It always excludes $c=0$, through the pairs with $\beta'=\kappa\beta$, even when $\beta\in F(\alpha)$ and $c=0$ would work, and it excludes an element of $S$ only when that element is a scalar, as Example 1(c) shows. Only $g$ has to split over $E'$: the roots $\alpha'$ that matter are produced in Step 3 as roots of $f^{\kappa\iota}$ in $E'$, whether or not $f$ splits there. [Mathlib/FieldTheory/PrimitiveElement.lean:83–95](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L83-L95) · [Mathlib/Data/Fintype/EquivFin.lean:450–451](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Fintype/EquivFin.lean#L450-L451)

**What is returned, and to whom [Lean, read].** Inside Lemma C of §5.3.1.9 the chain of returns is `p_linear` (Step 4 and the first half of Step 5), then `finale` ($\beta=j(-p_0/p_1)$), then the membership $\beta\in F(\gamma)$ that the opening `suffices` asks for, and finally the equality of Step 6. The equality is returned to `Field.exists_primitive_element`. In its infinite branch the predicate $P(K)$, "$K=F(\alpha)$ for some $\alpha$", is carried through `induction_on_adjoin`. The step from $K=F(\alpha)$ to $K(\beta)$ rewrites $K(\beta)=F(\alpha)(\beta)=F(\alpha,\beta)$ by `adjoin_simple_adjoin_simple`, calls `primitive_element_inf_aux F α β`, that is, Theorem G with the current primitive element as $\alpha$ and the adjoined element as $\beta$, and returns $\langle\gamma,\,\text{the equality read backwards}\rangle$. Only the existence of $\gamma$ leaves the lemma; the scalar $c$ and the divisor $p$ are discarded. `powerBasisOfFiniteOfSeparable` then picks the final generator by `Classical.choose` (§5.3.1.9) and transports `adjoin.powerBasis` along $F(\alpha)=E$ (§5.3.1.10). On the trace path of §§5.3.1.7–5.3.1.8 the base field is finite and the proof takes the finite branch, Lemma A of §5.3.1.9; the chain of this subsection is the infinite-base half of the same declaration. [Mathlib/FieldTheory/PrimitiveElement.lean:206–231](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L206-L231)

**Remarks [Expository].**

1. *Which hypothesis each step uses.*

   | Step | Pinned declarations | Hypothesis used |
   |---|---|---|
   | Choice of $c$ | `primitive_element_inf_aux_exists_c`, `Infinite.exists_notMem_finset` | $F$ infinite |
   | Remainders and maps | `map_mod_divByMonic`, `map_mod` | monic divisor; for fields, injectivity on leading coefficients |
   | Divisor and maps | `gcd_map` | a homomorphism of fields |
   | $h(\beta)=0$ | `eval₂_gcd_eq_zero`, `gcd_eq_gcd_ab` | $f(\alpha)=0$, $g(\beta)=0$ |
   | $h$ separable | `Separable.map`, `separable_gcd_right`, `Separable.of_mul_left` | $\beta$ separable |
   | $h^\kappa$ splits | `gcd_map`, `Splits.of_dvd` | $g$ splits over $E'$ |
   | Only root $\kappa\beta$ | `root_left_of_root_gcd`, `root_right_of_root_gcd`, `mem_roots_map` | condition (†); $f\ne0$, i.e. $\alpha$ algebraic |
   | $h$ linear | `eq_X_sub_C_of_separable_of_root_eq`, `nodup_roots`, `isUnit_of_self_mul_dvd_separable` | separability of $h$ |
   | $\beta\in F(\gamma)$ | `gcd_map`, `finale` | injectivity of $j$ |
   | $F(\alpha,\beta)=F(\gamma)$ | `adjoin_le_iff`, `adjoin_simple_le_iff` | none |

   No step refers to the characteristic. Example 2 runs in characteristic two, where the excluded scalars are the prime field itself, and Example 3 shows that the characteristic matters only through separability.

2. *Comparison with Milne.* Milne infers $\gcd(g(X),f(\gamma-cX))=X-\beta$ in $L[X]$ from the fact that $\beta$ is the only common root and moves the divisor to $F[\gamma][X]$ by Proposition 2.17. The first inference uses that the divisor has no repeated root: it divides $g$, which has only simple roots because $\beta$ is separable. Lemmas D–F make that use explicit, and Proposition C (4) is Proposition 2.17 for the monic divisor, while Lemma B is its exact form for Mathlib's Euclidean divisor. Milne requires only the generators after the first to be separable, and Theorem G uses exactly this of $\alpha$ and $\beta$. [Milne, *Fields and Galois Theory*, v5.10, Theorem 5.1, pp. 61–62](https://www.jmilne.org/math/CourseNotes/FT.pdf)

3. *Roots versus multiplicities.* In Example 3, Steps 0, 2 and 3 and the first half of Step 5 hold verbatim: (†) holds for every $c\ne0$, the divisor vanishes at $\beta$, it splits, its only root is $\beta$, and $p$ maps to $h$, since Lemma B needs no hypothesis. Steps 1 and 4 fail, and with them the comparison of coefficients in Step 5, and the divisor is $c^2(X-\beta)^2$. The conclusion of Step 3 determines the set of roots of $h$ but says nothing about their multiplicities; separability is what converts "only the root $\beta$" into "degree one". The conclusion of the theorem fails as well, since $[K(\gamma):K]\le2<4=[L:K]$.

4. *Exact equality versus associates.* Since $-p_0/p_1$ is unchanged when $p$ is scaled by a unit, the argument would also run with greatest common divisors known only up to units, as in Proposition C (4). Mathlib's statements are equalities because its divisor is a function of $(a,b)$, computed by the same divisions in $F(\gamma)[X]$ and in $E[X]$.

**Reading boundary.** Archive A2 SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc` pins Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Read against the source at local R3 in this subsection: `map_mod_divByMonic`, `map_divByMonic`, `map_modByMonic`; the polynomial `div`, `mod`, `div_def`, `mod_def`, the Euclidean-domain instance with its two private lemmas, `map_ne_zero`, `degree_map`, `leadingCoeff_map`, `map_div`, `map_mod`, `gcd_map`, `eval₂_gcd_eq_zero`, `eval_gcd_eq_zero`, `root_left_of_root_gcd`, `root_right_of_root_gcd`, `root_gcd_iff_root_left_right`, `isCoprime_map` and `mem_roots_map`; in `EuclideanDomain` the class, `GCD.induction`, `gcd`, `gcd_zero_left`, `xgcdAux`, `xgcdAux_rec`, `xgcd`, `gcdA`, `gcdB`, `mod_eq_sub_mul_div`, `dvd_mod_iff`, `gcd_zero_right`, `gcd_val`, `gcd_dvd`, `gcd_dvd_left`, `gcd_dvd_right`, `gcd_eq_zero_iff`, `dvd_gcd`, `xgcdAux_fst`, `xgcdAux_val`, `xgcdAux_P` and `gcd_eq_gcd_ab`; `IsCoprime`, `isCoprime_self`, `IsCoprime.map` and the four dropping lemmas; `Separable`, `separable_def'`, `not_separable_zero`, `Separable.of_mul_left`, `Separable.of_dvd`, `separable_gcd_left`, `separable_gcd_right`, `Separable.map`, `isUnit_of_self_mul_dvd_separable`, `emultiplicity_le_one_of_separable`, `Separable.squarefree`, `rootMultiplicity_le_one_of_separable`, `count_roots_le_one` and `nodup_roots`; `Splits`, `splits_iff_exists_multiset`, `Splits.exists_eval_eq_zero`, `Splits.eq_prod_roots`, `Splits.eq_X_sub_C_of_single_root`, `splits_mul` and `Splits.of_dvd`; and `Infinite.exists_notMem_finset`. Reread at their call sites: `primitive_element_inf_aux`, `primitive_element_inf_aux_exists_c`, `exists_primitive_element` and `eq_X_sub_C_of_separable_of_root_eq` (§5.3.1.9). Inherited without rereading: `div_modByMonic_unique`, `modByMonic_add_div`, `degree_modByMonic_lt` and the minimal-polynomial lemmas (§5.3.1.10), `induction_on_adjoin` and `adjoin_simple_adjoin_simple` (§5.3.1.9), and `RingHom.injective` (§6.4.15). Used at interface level: `derivative_mul`, `derivative_map`, `count_roots`, `mem_roots`, `rootMultiplicity_eq_multiplicity`, `finiteMultiplicity_X_sub_C`, `not_isUnit_X_sub_C`, `pow_dvd_of_le_emultiplicity`, `Multiset.nodup_iff_count_le_one`, `roots_C_mul`, `roots_multiset_prod_X_sub_C`, `splits_iff_exists_multiset'`, `splits_X_sub_C_mul_iff`, `leadingCoeff_map_of_injective`, `degree_map_le`, `degree_map_eq_of_leadingCoeff_ne_zero`, `monic_mul_leadingCoeff_inv`, `map_injective`, `SplittingField.splits`, `IsScalarTower.algebraMap_eq`, `AdjoinSimple.algebraMap_gen`, `Polynomial.map_map`, `map_comp`, `Algebra.IsSeparable.isSeparable`, `Algebra.IsSeparable.isIntegral` and `Fintype.false`. The finiteness inputs `Module.finite_of_finite` and `IsNoetherian.iff_fg` of §5.3.1.9 are not on this path and remain at interface level. The hand calculations were rechecked by exact arithmetic in the run directory. No Lean kernel replay or full dependency closure was performed. [Source map](../sources/SOURCES.md#separable-greatest-common-divisors-53111)

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
`src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:68` and `src/Formalism/StatementOC.lean:13` how
$\mathrm{GPsi}(D, \ell, \psi, y_\rho)$ splits between $\psi = 0$ and $\psi \neq 0$ (note that
$\ell(0)$ is never evaluated!):

- For $\psi = 0$, $\mathrm{primVal}(D, 0, n) = 1$, and $\mathrm{GPsi}(D, \ell, 0, y_\rho) = \mathrm{Gz}(y_\rho) = \sum_{1 \le n \le \lfloor y_\rho \rfloor} \Lambda(n)(y_\rho/n - 1) - y_\rho\log y_\rho + (1 + \gamma)y_\rho$.
- For $\psi \neq 0$, $\mathrm{GPsi}(D, \ell, \psi, y_\rho) = \sum_{1 \le n \le \lfloor y_\rho \rfloor} \Lambda(n)\,\mathrm{primVal}(D, \psi, n)(y_\rho/n - 1) + y_\rho\,\ell(\psi)$.

Multiply by $\overline{\psi(g)}\,w(\rho)$ (note $w(\rho) y_\rho = a$) and sum over all
$\psi \in \widehat{E_0 \times H}$ and $g \in \Phi^c$, dividing by $\lvert\Phi\rvert = \frac{1}{2}\lvert E_0 \times H \rvert = 2\lvert H \rvert$:

1. **The main-term pieces cancel to $-\mathrm{MAIN}(\ell, a, w)$ (`colour_sum`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean:212–235`).**
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
   `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChBalance.lean:55–196`).** For each prime power $n = p^i \le y_\rho \le N$ ($i \ge 1$), character
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
     matching $2\log p \cdot \mathrm{askP}(p)$ (`src/Formalism/SizeWindowBrackets/FirstPrimeNeSecondPrime.lean:75, 86`).
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
   Lipschitz bound `LipW` (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:957`) bounds the replacement of
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
in $w$ at every $n$!), and `ThinScales`. For item (3) (`src/Development/AutomorphicArithmetic/PrimitiveCosets/TopsSum.lean:26–103`), let $\theta(h) := \psi(0, h)$
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
satisfy `SizeWindows` (`src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:109`):*
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
$\mathcal E_{\mathrm{win}} / Q$ one by one (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:31–113`):

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
   $\theta \in \varphi.Xp$ (`prim_inj`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean:68`), corresponding under `chr_bij` to a unique
   $\psi \in \mathrm{keptA}(\Lambda, H) \subseteq \Psi_A(\varphi.A_0)$ with $\theta(\mathrm{iod}) = +1$.
   Why does each $p \in \Lambda.\mathrm{KEPT}$ appear once rather than twice in $\mathrm{keptA}$
   (at $\theta$ versus $\theta \cdot \mathrm{ps}_C$, where $\mathrm{ps}_C$ is the $(\frac{\cdot}{q})$
   sign character)? In `keptA` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean:24`) and `HostRaw.Kept` (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Analytic.lean:127`), a
   character $\theta$ is in `Kept` if and only if $\theta \in \varphi.Xp$ **and** its primitive
   character lies in $\Lambda.\mathrm{KEPT}$. Since $q = H.q$ is coprime to every conductor in
   $\Lambda.\mathrm{KEPT}$ ($\gcd(\psi.N, qd) = 1$), multiplying by $(\frac{\cdot}{q})$ multiplies
   the conductor by $q$, throwing $\theta \cdot \mathrm{ps}_C$ **out** of $\Lambda.\mathrm{KEPT}$
   (`gmA_eq_triv`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/GmAEq.lean:16–59`). Moreover, for $\psi \in \mathrm{keptA}$:
   - $\psi$ is trivial on $\{0\} \times \varphi.A$ if and only if $\theta = 1$ (since $\theta \cdot \mathrm{ps}_C$
     is ramified at $q$, hence not in $\Lambda.\mathrm{KEPT}$), which corresponds to $p = \mathrm{PChar.one}$,
     receiving weight $\mathrm{wt}_A = 1 = \Lambda.\mathrm{wt}(\mathrm{PChar.one})$;
   - for $p \in \Lambda.\mathrm{Nt}$ ($p \neq \mathrm{PChar.one}$), $\psi$ is nontrivial on
     $\{0\} \times \varphi.A$, receiving weight $\mathrm{wt}_A = (3\,\Lambda.o + 1)^{-1} = \Lambda.\mathrm{wt}(p)$!
   And by `prim_read` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/PrimRead.lean:51`), $\mathrm{GPsi}(\psi, y) = \mathrm{An.gChi}(p.\chi, y)$,
   so $\mathrm{Gm}_A(y) = \Lambda.\mathrm{Gm}(y)$ term by term!
2. Every $\psi \in \Psi_A(\varphi.A_0) \setminus \mathrm{keptA}(\Lambda, H)$ maps under `chr` to
   `H.Bounded Λ.KEPT` (`chr_bounded`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/SigALe.lean:18`: if $\theta(\mathrm{iod}) = +1$ then
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
`Deduction.ch_core` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:343`), `charsA` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/charsA.lean:80`), `gmA_eq`, and `sigA_le`.)* [Lean, read]

*Proof.* Watch every single multiple of $\varepsilon$ in the exponent $(e_D + e_L + 7)\varepsilon$
(`src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:16–74`):

1. **Unpack the chain gap (`ch_top`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean:37`, + `e_D + e_L + 3`):** Given `CoreAtH` at
   $x \ge x_1$, `each_unit_bound_statement` (`src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`, unpacked by `ch_top`) and
   surjectivity of $\mathrm{tr} : U_0 \twoheadrightarrow \varphi.A_0$ give, for every $u_0 \in \varphi.A_0$,
   $$\mathrm{gap}_A(u_0) := \sum_{t \in TT} \sum_{j=0}^{m-1}
   \bigl(\mathrm{ASK}(a_t, t, w_{u_0, j}) - \Re\,\mathrm{MAIN}(\ell, a_t, w_{u_0, j})\bigr)
   \le x^{(e_D + e_L + 3)\varepsilon}\,\mathcal E_{\mathrm{win}},$$
   since `CErr Cc = Cc.eDiv + Cc.eLoss + 3 ≤ e_D + e_L + 3` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:51–54`, with $e_D + e_L \ge 0$).
2. **Apply finite Fourier projection and the size lemma (`ch_core`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:343`, adding $+3\varepsilon$):**
   By Theorem 5.1 (`ch_balance`), $\mathrm{ASK} - \Re\,\mathrm{MAIN} = \Re\,\mathrm{De}$ at every
   $(t, j, u_0)$. Averaging $u_0 \in \varphi.A_0$, smoothing thick/thin weights, and summing
   $t \in TT$ via Lemma 5.2 (`charsA`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/charsA.lean:80`, supplies `CharsA` with $c_{\mathrm{top}} = (3\Lambda.o + 1)^{-1}$,
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
   (`hx₃`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:24–25`), we conclude (`src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:61–74`):
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

*Proof.* `tiedCore_of_chainTied` (`src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean:13–26`) unpacks the existential
tuple of `ChainTied Fm eD eL K cHH eK CL x` (`src/Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean:97` [Lean]), verifies that the sample
set $TT$ coincides with `(Fm.D x i0).host.TT` via injectivity of `Frame.A.val`, checks that every
digit shift lands inside the cyclic subgroup $\varphi.A_0$ (`Frame.digit_mem_cyclic_subgroup`), and
assembles `FamCoreConstantBounds`, which evaluates directly to `CoreAtH` at index $i_0$. Applying
Theorem 5.5 (`core_gm`) at index $i_0$ gives $\Lambda.\mathrm{Gm}(x) \le x^{1/2 + (e_D + e_L + 7)\varepsilon}$
(`src/Development/AutomorphicArithmetic/PrimitiveCosets/WindowInequalityOfArtinInputs.lean:17–25`). $\square$

---

## 5.5 Remarks

### 5.5.1 Accounting for every $\varepsilon$ in $1/2 + (e_D + e_L + 7)\varepsilon$

One virtue of reading `CoreGm.lean`, `src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean`, `LipschitzWeightAndMinimum.lean`, and
`ErrorFormsWeakWindowsFalse.lean` line by line is that the coefficient $e_D + e_L + 7$ is no longer
a mysterious constant — every single $+1$ in $+7$ has an explicit origin [Lean, read]:

| Piece of $(e_D + e_L + 7)\varepsilon$ | Lean location | Where it comes from |
|---|---|---|
| $(e_D + e_L + 3)\varepsilon$ | `src/Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean:19`, `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:51` | `CErr Cc = eDiv + eLoss + 3`: chain divisibility exponent $e_{\mathrm{Div}} \le e_D$, word-loss exponent $e_{\mathrm{Loss}} \le e_L$, plus $+3\varepsilon$ slack converting `SizeData₂` clauses into `ErrWindows`. |
| $+1\,\varepsilon$ | `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:556` | Dividing by the thick-place density $\delta_2 / 2 \ge \frac{1}{2} x^{-\varepsilon}$. |
| $+2\,\varepsilon$ ($\frac{13}{8} + \frac{3}{8}$) | `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:53,585`, `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/PChain.lean:130` | Term `SZ.T3` gives $x^{1/2 + 13\varepsilon/8}$ (from $n/n_T \le 2x^{\varepsilon/8}$, $m \le x^{1/2+\varepsilon/2}$, and $x^\varepsilon$ in $B_0$), plus $26 \le x^{3\varepsilon/8}$. |
| $+1\,\varepsilon$ | `src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean:25,65` | Absorbing the parasitic-character prefactor $1 + 4\,\Lambda.o \le x^\varepsilon$ from `sigA_le`. |

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
