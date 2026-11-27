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

[Real-place tensor norms in the Hermitian descent prerequisite](#53118-the-same-tensor-norm-witness-at-a-real-place)

[Cyclic Hasse norm assembly](#53119-from-prime-degree-norms-to-the-cyclic-hasse-norm-principle)

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

**From the separable gcd to tensor norms.** [Root multiplicities](#53112-root-multisets-and-separable-root-counting) give the split singleton step. [Splitting fields](#53114-constructing-splitting-fields-and-extending-embeddings) supply the common extension $E'$. [Finite étale tensor decomposition](#53116-product-decomposition-and-tensor-splitting-of-finite-étale-algebras) supplies the common cyclic factor in the [real-place](#53118-the-same-tensor-norm-witness-at-a-real-place) and [cyclic norm](#53119-from-prime-degree-norms-to-the-cyclic-hasse-norm-principle) arguments.

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

### 5.3.1.12 Root multisets and separable root counting

#### Motivation

In §5.3.1.11, the divisor $h$ has a known root $\beta$ in $E$. In the splitting extension $E'$, every root of $h$ lies at the image of $\beta$. To turn that statement into a linear polynomial, we need to count occurrences as well as distinct values. We also need to account for the full degree. The root multiset does the counting, separability bounds each count by one, and splitting accounts for the degree. [Previous subsection](#53111-the-separable-greatest-common-divisor-in-the-primitive-element-proof)

#### Two worked examples

**Example 1 (a separable cubic over $\mathbb Q$).** Let $f=X^3-2$ and let $\alpha$ be the positive real cube root of $2$. A rational root of this monic polynomial would be an integer dividing $2$. None of $1,-1,2,-2$ cubes to $2$, so the cubic is irreducible and its rational root multiset is empty. Set $K=\mathbb Q(\alpha)$ and $L=K(\zeta)$, where $\zeta^2+\zeta+1=0$ and $\zeta$ is nonreal. We have $[K:\mathbb Q]=3$, and $[L:K]=2$ since $K$ is real. In $K[X]$,

$$
f=(X-\alpha)(X^2+\alpha X+\alpha^2).
$$

The second factor has discriminant $-3\alpha^2<0$ in the chosen real embedding, so only $\alpha$ occurs over $K$. In $L[X]$ the second factor is $(X-\zeta\alpha)(X-\zeta^2\alpha)$ because $\zeta+\zeta^2=-1$ and $\zeta^3=1$. These three roots are distinct since $\zeta$ has order three and $\alpha\ne0$. The derivative is $3X^2$, whose value at each root is nonzero. Over the base there is even an explicit separability identity, $(-1/2)f+(X/6)f'=1$. The multiset sizes along the tower are $0,1,3$, and the count of $\alpha$ stays one from $K$ to $L$. [Milne, *Fields and Galois Theory*, Example 3.8(a), p. 37](https://www.jmilne.org/math/CourseNotes/FT.pdf)

**Example 2 (a purely inseparable extension).** For a prime $p$ let $k=\mathbb F_p(t)$ and $f=X^p-t$. The valuation at $t=0$ takes the value $1$ on $t$, while the value on any nonzero $p$th power is a multiple of $p$. Hence there are no roots in $k$. Embed $k$ in $L=\mathbb F_p(u)$ by $t\mapsto u^p$ with $u$ transcendental. The elements $1,u,\dots,u^{p-1}$ are linearly independent over $k$. Indeed, clearing denominators of a relation gives $\sum_{j=0}^{p-1}u^j A_j(u^p)=0$ with $A_j\in\mathbb F_p[T]$, and each summand has exponents in a different residue class modulo $p$. As $u$ satisfies $X^p-t$, this gives $[L:k]=p$ and proves irreducibility. Every element $A(u)/B(u)$ of $L$ has $p$th power $A(t)/B(t)$, so the extension is purely inseparable. In $L[X]$ the binomial theorem gives $f_L=(X-u)^p$. Its quotient after removing $p$ linear factors is $1$, and a factor of degree $p+1$ cannot divide a polynomial of degree $p$. The root multiset has $p$ copies of $u$, its support has one element, and $f'_L=0$. [Milne, Example 2.18 and Definition 3.6, pp. 32, 37](https://www.jmilne.org/math/CourseNotes/FT.pdf) · [Stacks Project, §9.14](https://stacks.math.columbia.edu/tag/09HD)

#### Definitions

Write $L_a=X-a$, with the scalar $a$ identified with its constant polynomial, and write $f^\iota$ for coefficient transport along a field embedding $\iota:K\hookrightarrow L$. For $f\ne0$ in a domain $R[X]$, let $m_a(f)$ be the largest $n\ge0$ for which $L_a^n\mid f$. Mathlib writes this as $m_a(f)=\operatorname{rootMultiplicity}(a,f)$ and sets $m_a(0)=0$. It also sets $\operatorname{roots}(0)=\varnothing$. This convention allows a finite multiset even over an infinite field. Evaluation of the zero polynomial still vanishes at every point. A nonzero polynomial is split over its coefficient domain if it is a nonzero constant times a finite product of monic linear factors. Mathlib's `Splits` is defined by the multiplicative closure of the constants and monic linear factors, so it includes zero. Over a field, `Separable` means there are $U,V$ with $Uf+Vf'=1$. This identity forces $f\ne0$. [Fixed source map](../sources/SOURCES.md#root-multisets-and-separable-root-counting-53112)

#### Lemma 1. The finite division order [Lean, read]

For nonzero $f\in R[X]$ over an integral domain, there is a unique integer $m\ge0$ such that $f=L_a^m q$ and $q(a)\ne0$ for a polynomial $q$. It satisfies $n\le m$ exactly when $L_a^n\mid f$. For nonzero $f,g$, $m_a(fg)=m_a(f)+m_a(g)$.

*Proof.* Monic division by $L_a$ leaves the constant remainder $f(a)$, by evaluating the division identity at $a$. Thus $L_a\mid f$ exactly when $f(a)=0$. Since $\deg L_a^n=n$, every dividing exponent is at most $\deg f$. The dividing exponents include zero and are downward closed. The first $n$ such that $L_a^{n+1}$ fails to divide $f$ is therefore the maximum dividing exponent. A quotient by this maximal power has nonzero evaluation at $a$, since otherwise one more division succeeds. Conversely, if $f=L_a^m q$ with $q(a)\ne0$, cancellation in the domain rules out $L_a^{m+1}\mid f$. For a product, multiply the two decompositions. The residual quotient has value $q_f(a)q_g(a)\ne0$, which gives the sum.

The source defines `rootMultiplicity` using `Nat.find` on the first failed division. In `rootMultiplicity_eq_multiplicity`, unfolding the generic extended multiplicity gives a finite natural number cast into $\mathbb N\cup\{\infty\}$ by the same least-witness construction. The generic natural-valued multiplicity takes `untopD 1`, which returns that natural number in the finite case and defaults to one at infinity. The proof handles $f=0$ by the explicit zero branch, independently of that generic default, and identifies the least-witness terms in the nonzero branch. For $f=0$, every power divides, so the equivalence with $n\le m_a(f)$ requires the nonzero hypothesis. The pinned product proof uses the generic addition law for the prime $L_a$. The residual-quotient argument above proves the specialization directly. [Fixed source map](../sources/SOURCES.md#root-multisets-and-separable-root-counting-53112)

#### Lemma 2. Producing and counting the roots [Lean, read]

For every nonzero $f\in R[X]$ over an integral domain there is a unique multiset $S$ of elements of $R$ whose count at each $a$ equals $m_a(f)$. Its cardinality is at most $\deg f$. With the empty multiset assigned to zero, the count identity holds for every polynomial.

*Proof.* The existence and bound are proved together by induction on degree. If there is no root, Lemma 1 gives zero count everywhere, and the empty multiset has cardinality at most the nonnegative degree. Otherwise pick a root $x$ and form the monic quotient $g=f/L_x$. Its remainder is zero. Since $f=L_xg\ne0$, we have $g\ne0$ and $\deg g=\deg f-1$. Apply induction to $g$ and adjoin one copy of $x$ to its multiset. The cardinality increases by one, so it is at most $\deg f$. At any $a$, $m_a(L_x)$ is one if $a=x$ and zero otherwise, by degree and evaluation. Lemma 1 then shows the count increases by exactly $m_a(L_x)$. This proves both outputs of `exists_multiset_roots`, where the nonzero quotient allows the strict degree decrease to serve as a decrease of `natDegree`. Count equality implies multiset equality, proving uniqueness. In `count_roots` the zero branch simplifies by the two conventions. The other branch unfolds `roots` and takes the second component of the specification of the chosen witness, evaluated at $a$. Its first component gives the degree bound. In particular, membership means $f\ne0$ and $f(a)=0$. [Fixed source map](../sources/SOURCES.md#root-multisets-and-separable-root-counting-53112)

#### Lemma 3. Split products and field maps [Lean, read]

Over an integral domain, taking the roots of $\prod_{a\in S}L_a$ recovers $S$ with its repetitions. Every split $f$ satisfies

$$
f=\operatorname{lc}(f)\prod_{a\in\operatorname{roots}(f)}L_a.
$$

For nonzero split $f$, the cardinality of the multiset equals $\deg f$. Under a field embedding $\iota$, the count at $\iota(a)$ in $\operatorname{roots}(f^\iota)$ is the count at $a$ in $\operatorname{roots}(f)$. If $f$ splits over $K$, the entire multiset over $L$ is the image multiset.

*Proof.* For a product of two nonzero polynomials, Lemmas 1 and 2 give addition of multisets by equality of counts. The source first iterates this argument over lists, starting with the empty list, whose product is $1$ with empty roots. It passes to multisets since the product and the sum of root multisets are invariant under permutations. In `roots_multiset_prod_X_sub_C`, all factors are nonzero since they have degree one. The multiset sum of the singleton $\{a\}$ for each occurrence of $a$ is exactly $S$.

For `splits_iff_exists_multiset'`, in a commutative semiring the constants already form a multiplicative submonoid. A product from the closure of the union can be written as one constant times a product from the closure of the $X+c$ factors by collecting the constants. Membership in the latter closure gives a finite product of generators. Choosing a coefficient $c$ for each generator gives a multiset of coefficients, and the product of the monic factors is monic, including for the empty product. Thus the constant multiplier is the leading coefficient. Conversely, the constant and all linear factors belong to the defining closure, so their product belongs. Over a ring change $c$ to $-c$ throughout to obtain the subtraction version. For $f\ne0$, the leading coefficient is nonzero and a nonzero scalar contributes zero occurrences at every point. Thus the multiset in any split representation is the actual root multiset, and taking degrees gives the cardinality equality. For $f=0$ the displayed identity reads $0=0\cdot1$.

For $f\ne0$ use $f=L_a^m q$ from Lemma 1. Coefficient transport sends this to $f^\iota=L_{\iota(a)}^m q^\iota$ with $q^\iota(\iota(a))=\iota(q(a))\ne0$. Hence the count is preserved. The pinned proof of `eq_rootMultiplicity_map` instead transports divisibility forward and reflects it using preservation of the monic-division remainder under the injective map. For $f=0$ the counts both vanish. If $f$ splits, transport its displayed factorization and recover the entire image multiset by the product calculation, or use the empty multiset when $f=0$. Example 1 shows that roots outside the image can appear when the original polynomial does not split. [Fixed source map](../sources/SOURCES.md#root-multisets-and-separable-root-counting-53112)

#### Lemma 4. Derivatives and the characteristic boundary [Expository]

Let $f\ne0$ over a field and suppose $a$ is a root, in the coefficient field or after coefficient transport. Use $m=m_a(f)$ in that field. Then $m=1$ if and only if $f'(a)\ne0$, and $m\ge2$ if and only if $f'(a)=0$. If $m$ is nonzero in the field then $m_a(f')=m-1$. If $m$ vanishes in the field then $f'$ is divisible by $L_a^m$, and its order is at least $m$ provided $f'\ne0$.

*Proof.* By Lemma 1 write $f=L_a^m q$ with $m\ge1$ and $q(a)\ne0$. The product rule and induction on the power give

$$
f'=L_a^{m-1}\bigl(mq+L_a q'\bigr).
$$

When $m=1$, evaluation gives $f'(a)=q(a)$. When $m\ge2$, the visible factor forces $f'(a)=0$ in every characteristic. If $m$ is nonzero in the field, the parenthesized factor evaluates to $m q(a)\ne0$, so $f'$ is nonzero and has order exactly $m-1$. If $m$ vanishes, the formula is $f'=L_a^m q'$. For $f'\ne0$ it gives the more precise $m_a(f')=m+m_a(q')$. For $f'=0$ every power divides and the totalized count is zero. In characteristic $p>0$ the second branch occurs precisely when $p\mid m$. Example 2 realizes the zero derivative. The polynomial $L_a^p(1+L_a)$ realizes the case of a positive-characteristic jump with $f'=L_a^p$. More generally $f'=0$ in characteristic $p$ exactly when $f\in K[X^p]$, since the coefficient of $X^{j-1}$ in $f'$ is $j$ times the coefficient of $X^j$ in $f$. Example 2 shows why this need not give a $p$th power in $K[X]$. The order statements are textbook deductions from the displayed formula, using the pinned differentiation rules. [Milne, Lemma 2.19 and Proposition 2.20, p. 32](https://www.jmilne.org/math/CourseNotes/FT.pdf) · [Stacks Project, Lemma 9.12.4, irreducible case](https://stacks.math.columbia.edu/tag/09H3) · [Fixed source map](../sources/SOURCES.md#root-multisets-and-separable-root-counting-53112)

#### Theorem. Separable root counting and the linear conclusion

**Root counting [Expository].** Let $\iota:K\hookrightarrow L$ be a field embedding and $0\ne f\in K[X]$. If $f^\iota$ splits, its number of distinct roots in $L$ equals $\deg f$ exactly when $f$ is separable.

*Proof.* Derivatives commute with coefficient transport by the coefficient formula. If $Uf+Vf'=1$, transporting the identity and evaluating at a root shows $V^\iota(a)(f^\iota)'(a)=1$. Lemma 4 gives multiplicity one, and Lemma 3 gives the total degree, which is preserved by injectivity. Conversely, distinct-root cardinality is at most multiset cardinality, with equality exactly when each occurring count is one. If the distinct roots fill the degree, Lemma 3 and Lemma 4 give a nonzero derivative at every root. If $f,f'$ were not coprime over $K$, their common divisor of positive degree would still have positive degree over $L$. It divides the split $f^\iota$ and therefore has a linear factor there, by unique factorization over a field. This would give a common root, a contradiction. Coprimality supplies the Bézout identity in $K[X]$. The split nonzero case corresponds to `nodup_aroots_iff_of_splits` and `card_rootSet_eq_natDegree_iff_of_splits`. The argument above gives the field-embedding formulation. [Milne, Proposition 2.21 and Definition 2.22, pp. 32–33](https://www.jmilne.org/math/CourseNotes/FT.pdf) · [Fixed source map](../sources/SOURCES.md#root-multisets-and-separable-root-counting-53112)

**Linear conclusion [Lean, read].** Let $h\in K[X]$ be separable, let $x\in K$ satisfy $h(x)=0$, and suppose $h^\iota$ splits and every element of its root multiset equals $\iota(x)$. Then $h=\operatorname{lc}(h)(X-x)$.

*Proof.* Separability makes $h\ne0$, so the transported evaluation places $\iota(x)$ in the multiset. The transported separability identity makes the multiplicity one. By the hypothesis on every multiset element, the multiset is the singleton with that one copy. In the source, `nodup_roots` allows the finite-set singleton criterion to identify precisely this multiset. Apply `Splits.eq_X_sub_C_of_single_root`, the singleton case of Lemma 3, and descend by injectivity on coefficients, which also preserves the leading coefficient. This is exactly `eq_X_sub_C_of_separable_of_root_eq`. [Fixed source map](../sources/SOURCES.md#root-multisets-and-separable-root-counting-53112)

#### Remarks

**The return to §5.3.1.11.** At the call to `eq_X_sub_C_of_separable_of_root_eq`, take $K=E$, $L=E'$, $\iota=\kappa:E\hookrightarrow E'$ and $x=\beta$. The inputs are `h_sep` for $h$, `h_root` for $\beta$, `h_splits` for the image of $h$, and `h_roots` for all occurrences in that image's multiset. The result is the equality for $h$ over $E$, including its original leading coefficient. Since the image of the polynomial $p$ of §5.3.1.11 in $E[X]$ equals $h$, this fills `p_linear`, the equality used by `finale` at the coefficient-reading step. The root may be tested over $E'$ while the returned equality is over $E$. [Previous subsection](#53111-the-separable-greatest-common-divisor-in-the-primitive-element-proof) · [Fixed source map](../sources/SOURCES.md#root-multisets-and-separable-root-counting-53112)

**Testing the hypotheses.** Over $\mathbb Q$, $b=(X-1)^2(X^2+1)$ has degree four and root multiset $[1,1]$. The residual factor evaluates to $2$ at $1$ and is irreducible over $\mathbb Q$, so the count at $1$ is exactly two and there are no other rational roots. The repeated root is detected by $b'(1)=0$. Over $\mathbb Q(i)$ the multiset is $[1,1,i,-i]$. This example exhibits both a repeated root and missing degree over the base. To test splitting alone in the linear conclusion, use $c=(X-1)(X^2+1)$ over $\mathbb Q$ with the identity embedding. Over $\mathbb Q(i)$ it has the three distinct factors $X-1,X-i,X+i$, so it is separable by the root-counting theorem. Over $\mathbb Q$ the only root is $1$ and its multiset is $[1]$, yet $\deg c=3$. To test separability alone, use $X^2$ with $x=0$ in any field. It splits with one distinct root and its multiset has two copies. To test the existence of the designated root, use $1$, whose multiset is empty and whose universal condition on roots is vacuous. To test uniqueness, use $X(X-1)$. It is separable, splits and vanishes at $0$, with the additional root $1$. Finally, in the count-to-evaluation step the nonzero premise is essential because $0$ has empty multiset and vanishes at every point. In the linear conclusion this premise follows already from separability. For the converse from absence of repeated roots to separability it must be present separately, since zero splits and its empty multiset has no repetitions.

**Reading boundary.** The fixed source map records the proof bodies read for this subsection, the five findings inherited from the predecessor audit, and deeper inputs retained by name. The reading is local R3 and the characteristic-dependent order formula is an expository deduction. [Fixed source map](../sources/SOURCES.md#root-multisets-and-separable-root-counting-53112)

### 5.3.1.14 Constructing splitting fields and extending embeddings

#### Motivation

The primitive element argument in §5.3.1.11 needs an extension of the working field in which one specified polynomial splits. A quotient by an irreducible factor gives one root. Dividing out the corresponding linear factor gives a smaller problem even when the root occurs several times.

#### Two worked examples [Expository]

**A rational cubic.** The only possible rational roots of $X^3-2$ are $1,-1,2,-2$, none of which cubes to $2$. Thus it is irreducible. Take its positive real root $a$ and let $K_1=\mathbb Q(a)$. The first quotient is $X^2+aX+a^2$, since multiplying by $X-a$ gives $X^3-a^3$. Completing the square gives $(X+a/2)^2+3a^2/4$, so the quadratic is irreducible over the real subfield $K_1$. Adjoin a root $b$ by taking the quotient by this quadratic, and set $c=-a-b$. Then $b+c=-a$ and $bc=-ab-b^2=a^2$. The next residual is $X-c$, and the last residual is $1$. The field degrees in the three steps are $3,2,1$, so the resulting splitting field $S=K_1(b)$ has degree six.

Put $\zeta=b/a$. The quadratic equation yields $\zeta^2+\zeta+1=0$, hence $\zeta^3=1$ and $\zeta\ne1$. The roots are $a,a\zeta,a\zeta^2$. For an embedding into $S$ there are three choices $r$ for the image of $a$. Once $r$ is chosen, the transported quadratic is $(X^3-2)/(X-r)$ and has the other two roots. Evaluation on the two successive quotients gives one embedding for each ordered choice. Each image contains the third root by the negative-sum formula and therefore contains $S$. This gives six automorphisms.

**An inseparable cubic.** Let $K=\mathbb F_3(t)$ and $f=X^3-t$. The order at $t$ of a nonzero rational function is the exponent of $t$ in its numerator minus that in its denominator. Cubing triples this integer, whereas $t$ has order one. This excludes roots in $K$ and proves irreducibility by the cubic degree. In $S=K[X]/(f)$, write $a=[X]$. Then $a^3=t$ and $f=(X-a)^3$. The residuals are $(X-a)^2$, $X-a$ and $1$, with field degrees $3,1,1$. The basis $1,a,a^2$ gives $[S:K]=3$. Over any field containing $S$, a root $b$ satisfies $(b-a)^3=0$, hence $b=a$. Evaluation gives exactly one $K$-embedding into such a field. Here the same root supplies three linear factors and only one possible image for the generator.

#### Definitions

Write $f^j$ for coefficient transport along a field embedding $j$. A nonzero polynomial splits over a field if its transported polynomial is its leading coefficient times a product of linear factors, with repetition allowed. A splitting field is a field in which the polynomial splits and which is generated by the roots. Nonzero constants use the empty product and empty root set. Mathlib declares zero split and uses the empty root set for zero as well, so both degree-zero cases have the base field as splitting field.

#### Lemma 1. Adjoining one root [Lean, read]

If $q\in A[X]$ is irreducible over a field $A$, then $A_q=A[X]/(q)$ is a field generated as an algebra by $u=[X]$, with $q(u)=0$. Given $j:A\hookrightarrow M$ and a root $v$ of $q^j$ in a field $M$, there is a unique embedding $A_q\hookrightarrow M$ extending $j$ and sending $u$ to $v$.

*Proof.* The ideal $(q)$ is maximal in the principal ideal domain $A[X]$. The quotient kills $q$ and every residue class is a polynomial in $u$. Evaluation $g\mapsto g^j(v)$ kills all multiples of $q$, hence descends to a unital homomorphism of fields and is injective. Generation proves uniqueness. Conversely a homomorphism extending $j$ sends $u$ to a root of $q^j$. For an algebraic element already in an extension, taking its minimal polynomial and evaluating at the element identifies the quotient with the simple field it generates. The degree of this field over $A$ is $\deg q$ by §5.3.1.10. [Mathlib, AdjoinRoot](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AdjoinRoot.lean#L247-L326)

#### Theorem 2. Existence by a finite tower [Lean, read]

For every field $K$ and every $f\in K[X]$ there is a finite splitting field over $K$. For nonzero $f$ of degree $n$, the following construction takes exactly $n$ linear divisions.

*Proof.* Start with $K_0=K$ and $f_0=f$. If $i<n$ and $\deg f_i=n-i$, choose an irreducible divisor $q_i$ of $f_i$ and form $K_{i+1}=K_i[X]/(q_i)$. Let $\iota_i:K_i\hookrightarrow K_{i+1}$ be the structure map and $a_i=[X]$. The transported $f_i$ vanishes at $a_i$ because its divisor does. Monic linear division (§5.3.1.12) gives
$$
f_i^{\iota_i}=(X-a_i)f_{i+1},\qquad \deg f_{i+1}=n-i-1.
$$
Degree is preserved by the coefficient embedding and drops by one on division. Inductively, the image of $f$ in $K_i[X]$ is the product of the first $i$ removed linear factors times $f_i$, with all earlier roots carried along the tower maps. At $i=n$, the residual is a nonzero constant, so $f$ splits. The transported $a_i$ are roots of $f$ in $K_n$, and they generate $K_n$ as a $K$-algebra by Lemma 1 at each stage. Thus adjoining the entire root set also generates $K_n$. Each step has finite degree by Lemma 1, and the tower law gives finiteness. For zero take $K$ under the stated convention.

**The fixed construction.** Mathlib's `factor` chooses an irreducible divisor when available, with $X$ as fallback. Positive natural degree ensures divisibility. The operation `removeFactor` transports to `AdjoinRoot` and takes the monic quotient. `SplittingFieldAuxAux` recurses on a natural counter with the coefficient field varying, composing structure maps in the successor step. The equality `natDegree_removeFactor'` preserves the invariant that the counter equals the residual degree. The splitting induction multiplies the split images of the peeled factor and the residual. The generation induction takes the union of the singleton peeled root and the residual root set, then uses generation by that first root and generation over the larger field by the remaining roots. [Mathlib, Construction:49–207](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/SplittingField/Construction.lean#L49-L207)

The public `SplittingField` is a quotient of the multivariate polynomial algebra over $K$ with one variable for each element of the auxiliary field. Evaluation sends each variable to the element indexing it. This is onto, so the quotient by the kernel is algebra-isomorphic to the auxiliary field. Mathlib transports inversion through that equivalence and transfers splitting and generation through `IsSplittingField.of_algEquiv`. `SplittingField.splits` and `SplittingField.adjoin_rootSet` then project the two fields of the predicate. The public quotient gives the desired algebra instances for scalar towers. [Mathlib, Construction:211–283](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/SplittingField/Construction.lean#L211-L283)

#### Theorem 3. Extension and the image of any embedding

Let $K$ be a field, $f\in K[X]$, and $S$ a splitting field of $f$ over $K$. For any intermediate field $K\subseteq A\subseteq S$, any $K$-field $M$ splitting $f$, and any $K$-embedding $j:A\hookrightarrow M$, there exists a $K$-embedding $S\hookrightarrow M$ extending $j$. The image of every $K$-embedding $S\hookrightarrow M$ is the field generated over $K$ by the roots in $M$. If $M$ is itself a splitting field, every such embedding is an isomorphism.

*Proof.* The case $f=0$ reduces to $S=A=K$. Otherwise enumerate the finitely many distinct roots $a_1,\ldots,a_m$ of $f$ in $S$. Starting from $A_0=A$, set $A_i=A_{i-1}(a_i)$. Given an extension $j_{i-1}:A_{i-1}\hookrightarrow M$ of $j$, the minimal polynomial $q_i$ of $a_i$ over $A_{i-1}$ divides the image of $f$ over that field. Transport along $j_{i-1}$, which fixes the specified images of $K$. The transported $q_i$ divides the nonzero split image of $f$ in $M[X]$. Its positive degree and its splitting as a divisor yield a root, so Lemma 1 extends $j_{i-1}$ to $A_i$. Generation gives $A_m=S$, including the empty-list case.

For $f\ne0$ and any $K$-embedding from $S$ to $M$, transport the complete factorization. Its leading coefficient stays nonzero. A product in a field vanishes precisely when a factor vanishes, so the roots in $M$ are exactly the images of roots in $S$. Generation in $S$ gives the range statement, and generation in $M$ gives surjectivity.

**The fixed lift [Lean, read].** `IsSplittingField.lift` uses the base-restriction case $A=K$. In the nonzero branch it applies `Polynomial.lift_of_splits` to the finite root set. Each root is integral and its minimal polynomial over $K$ divides $f$. The induction first embeds the algebra generated by the old set. That algebra is finite dimensional over $K$: successively reduce powers of each generator by a monic annihilating polynomial. It is a domain, so multiplication by any nonzero element is an injective linear endomorphism and hits $1$ by finite dimensionality. This gives the field instance for the old algebra. The next minimal polynomial over it divides the transported original minimal polynomial, so the proof chooses a root in the target. `Algebra.adjoin.liftSingleton` extends the embedding via the quotient evaluation `AdjoinRoot.liftAlgHom`. The zero branch uses the bottom subalgebra. The range assertion is expressed by `IsSplittingField.adjoin_rootSet_eq_range`. The exported `IsSplittingField.algEquiv` uses lifts in both directions and finite-dimensionality for bijectivity. [Mathlib, lift and range](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/SplittingField/IsSplittingField.lean#L109-L149)

#### Remarks

**Counting extensions.** At each step of Theorem 3, the extensions correspond bijectively to the distinct roots of the transported minimal polynomial. If $f\ne0$ is separable, every such divisor has distinct roots, so the number of choices is its degree. Multiplying the successive counts gives exactly $[S:A]$ extensions of the given $j$. In general there are between one and $[S:A]$ extensions. The characteristic-three example gives strict inequality. Repetition in $f$ alone need not decrease the count: $(X-a)^2$ for $a\in K$ gives a degree-one field and one embedding. Target generation is essential for surjectivity: for $f=X$, the splitting field $K$ embeds in $K(t)$, which splits $X$, with proper image.

**The common extension in the primitive element proof.** In [§5.3.1.11](#53111-the-separable-greatest-common-divisor-in-the-primitive-element-proof) let $f,g$ be the minimal polynomials over $F$ of $\alpha,\beta\in E$, and let $\iota:F\hookrightarrow E$. The actual proof uses $E'=\mathrm{SplittingField}(g^\iota)$ over $E$. The structure embedding $\kappa:E\hookrightarrow E'$ places $\alpha,\beta$ and the roots of $g^{\kappa\circ\iota}$ in one field. The scalar exclusion argument considers whatever roots of $f$ lie there and requires no splitting of $f$. The gcd over $E$, transported to $E'$, divides the split polynomial $g^{\kappa\circ\iota}$ and therefore splits there. Separability of $\beta$ is used separately to make the gcd separable, so its unique root forces a linear polynomial by [§5.3.1.12](#53112-root-multisets-and-separable-root-counting). The finite-field trace account in §5.3.1.8 uses the identification of its finite extension as a splitting field and the distinct-root embedding count. [Mathlib, PrimitiveElement:102–159](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/PrimitiveElement.lean#L102-L159)

**Classical sources and reading scope.** Milne treats simple-extension lifting, finite existence, the embedding count and uniqueness in Propositions 2.4, 2.7, 2.12 and Corollary 2.13. Stacks Project Lemma 9.16.1 gives existence and uniqueness for nonconstant polynomials by choosing an algebraic closure. Theorem 3 gives the intermediate-field version and deduces surjectivity directly from generation. The declaration-level reading of the Mathlib construction and lift is local. [Source ledger](../sources/SOURCES.md#splitting-fields-53114)

### 5.3.1.16 Product decomposition and tensor splitting of finite étale algebras

#### Motivation

When a field extension $E/F$ is base-changed along another field extension $K/F$, the tensor product $K\otimes_F E$ preserves dimension ($\dim_K(K\otimes_F E)=[E:F]$) and commutativity, and may acquire zero divisors when a polynomial irreducible over $F$ factors over $K$. In the archive's Hermitian descent for the Hasse norm principle (`HasseEt.lean`), a cyclic Galois extension $E/F$ of number fields is base-changed to arbitrary residue fields $K=A/\mathfrak m$ of a finite reduced $F$-algebra $A$. To transfer local norms between $E/F$ and a single field extension $L/K$, the proof must know two structural facts without assuming that $K$ splits $E$ into linear factors: first, that $K\otimes_F E$ decomposes canonically as a finite product of finite separable field extensions $A_i/K$; second, that when $E/F$ is normal (and cyclic Galois), every factor $A_i$ is a splitting field over $K$ of the same transported polynomial, so two calls to the splitting-field equivalence from [the mutual-embedding manuscript (§5.3.1.15)](../sources/SOURCES.md#chapter-5-unpublished-algebra-and-finite-place-supplies) identify all factors with one selected factor $L=A_{i_0}$ while over a full splitting extension $L/F$ the algebra splits completely into embedding-indexed coordinates $L^{\operatorname{Hom}_{F\text{-alg}}(A,L)}$.

Mathlib proves the product decomposition not only for $K\otimes_F E$, but as an equivalence characterizing all essentially-of-finite-type formally étale (and all finite étale) commutative algebras over a field: infinitesimal unique lifting across square-zero ideals forces finite dimension via a diagonal separability idempotent, eliminates nilpotents after base change to an algebraic closure, turns the Artinian maximal-spectrum Chinese remainder map into an isomorphism, and forces each residue field to be separable.

#### Two worked examples [Expository]

**Example 1: A reducible separable cubic algebra and its tensor splitting over $\mathbb Q(i)$.** Let
$$
f(X)=(X-1)(X^2+1)=X^3-X^2+X-1\in\mathbb Q[X],\qquad A=\mathbb Q[X]/(f(X))=\mathbb Q[x],
$$
where $x=[X]$ satisfies $x^3=x^2-x+1$. By monic division (§5.3.1.10), $\{1,x,x^2\}$ is a $\mathbb Q$-basis of $A$, and $(X+1)f(X)=X^4-1$ gives $x^4=1$ in $A$. Differentiating gives $f'(X)=3X^2-2X+1$; two Euclidean divisions
$$
f(X)=\Bigl(\frac{1}{3}X-\frac{1}{9}\Bigr)f'(X)+\Bigl(\frac{4}{9}X-\frac{8}{9}\Bigr),\qquad f'(X)=\Bigl(\frac{27}{4}X+9\Bigr)\Bigl(\frac{4}{9}X-\frac{8}{9}\Bigr)+9
$$
show $\gcd(f,f')=1$, so $f$ is separable.

Over $\mathbb Q$, the irreducible factors $X-1$ and $X^2+1$ cut out the two maximal ideals $\mathfrak m_1=(x-1)$ and $\mathfrak m_2=(x^2+1)$ of $A$, with separable residue fields $A/\mathfrak m_1\cong\mathbb Q$ ($x\mapsto 1$, degree $1$) and $A/\mathfrak m_2\cong\mathbb Q(i)$ ($x\mapsto i$, degree $2$). From the Bézout identity
$$
\frac{1}{2}(X^2+1)-\frac{1}{2}(X+1)(X-1)=1\quad\text{in }\mathbb Q[X],
$$
passing to $A$ yields two elements in the power basis $\{1,x,x^2\}$:
$$
e_1=\frac{1}{2}(1+x^2),\qquad e_2=\frac{1}{2}(1-x^2).
$$
Using $x^4=1$, one checks directly in $A$ that $e_1+e_2=1$, $e_1e_2=\frac{1}{4}(1-x^4)=0$, $e_1^2=e_1(1-e_2)=e_1$, and $e_2^2=e_2$. Moreover, $xe_1=\frac{1}{2}(x+x^3)=\frac{1}{2}(x+x^2-x+1)=e_1$, while $xe_2=-\frac{1}{2}+x-\frac{1}{2}x^2$ satisfies $(xe_2)^2=x^2e_2=\frac{1}{2}(x^2-x^4)=-e_2$. Thus $\{e_1,e_2\}$ is the complete family of primitive orthogonal idempotents of $A$, giving the explicit $\mathbb Q$-algebra isomorphism $\Phi_{\mathbb Q}:A\xrightarrow{\sim}\mathbb Q\times\mathbb Q(i)$ and its inverse:
$$
\Phi_{\mathbb Q}(c_0+c_1x+c_2x^2)=\bigl(c_0+c_1+c_2,\ (c_0-c_2)+c_1i\bigr),\qquad \Phi_{\mathbb Q}^{-1}(r,\ u+vi)=re_1+(u+vx)e_2=\frac{r+u-v}{2}+vx+\frac{r-u-v}{2}x^2.
$$

Now base-change $A$ to the splitting field $L=\mathbb Q(i)$ of $f$. In $L[X]$, $f(X)=(X-1)(X-i)(X+i)$ splits into three distinct linear factors, corresponding to the three $\mathbb Q$-algebra homomorphisms $\sigma_1,\sigma_2,\sigma_3\in\operatorname{Hom}_{\mathbb Q\text{-alg}}(A,L)$ determined by $\sigma_1(x)=1$, $\sigma_2(x)=i$, and $\sigma_3(x)=-i$. In the $L$-basis $\{1\otimes 1,1\otimes x,1\otimes x^2\}$ of $L\otimes_{\mathbb Q}A$, the evaluation map $\Psi_L:L\otimes_{\mathbb Q}A\to L^3$, $c\otimes a\mapsto(c\sigma_1(a),c\sigma_2(a),c\sigma_3(a))$, and its inverse have matrices
$$
M=\begin{pmatrix}1&1&1\\ 1&i&-1\\ 1&-i&-1\end{pmatrix},\qquad \det M=-4i\ne 0,\qquad M^{-1}=\begin{pmatrix}\frac{1}{2}&\frac{1+i}{4}&\frac{1-i}{4}\\[3pt] 0&-\frac{i}{2}&\frac{i}{2}\\[3pt] \frac{1}{2}&-\frac{1-i}{4}&-\frac{1+i}{4}\end{pmatrix}.
$$
The three columns of $M^{-1}$ give the primitive orthogonal idempotents of $L\otimes_{\mathbb Q}A$:
$$
E_1=1\otimes e_1=\frac{1}{2}(1\otimes 1+1\otimes x^2),\qquad E_2=\frac{1+i}{4}(1\otimes 1)-\frac{i}{2}(1\otimes x)-\frac{1-i}{4}(1\otimes x^2),\qquad E_3=\frac{1-i}{4}(1\otimes 1)+\frac{i}{2}(1\otimes x)-\frac{1+i}{4}(1\otimes x^2).
$$
Here $1\otimes e_1=E_1$ stays primitive because $\mathbb Q$ was already degree $1$, whereas $1\otimes e_2=E_2+E_3$ splits across the two conjugate embeddings of $\mathbb Q(i)$ into $L$.

**Example 2: A nonnormal separable cubic field across three base changes.** Let $\alpha=\sqrt[3]{2}\in\mathbb R$ and $E=\mathbb Q(\alpha)\cong\mathbb Q[X]/(X^3-2)$. The polynomial $g(X)=X^3-2$ is Eisenstein at $2$ and satisfies $\gcd(X^3-2,3X^2)=1$, so $E/\mathbb Q$ is finite separable of degree $3$, but nonnormal because the complex roots $\omega\alpha,\omega^2\alpha$ ($\omega=(-1+\sqrt{-3})/2$, $\omega^2+\omega+1=0$) lie outside $E\subset\mathbb R$. For any field extension $K/\mathbb Q$, $K\otimes_{\mathbb Q}E\cong K[Y]/(Y^3-2)$ with $Y\leftrightarrow 1\otimes\alpha$. Three choices of $K$ display the three factor patterns $(3)$, $(1,2)$, and $(1,1,1)$:

1. *Inert quadratic base change $K_1=\mathbb Q(\omega)$.* Since $[K_1(\alpha):\mathbb Q]=\operatorname{lcm}(2,3)=6$, $[K_1(\alpha):K_1]=3$ and $Y^3-2$ remains irreducible in $K_1[Y]$. Thus $K_1\otimes_{\mathbb Q}E\cong\mathbb Q(\alpha,\omega)$ has a single maximal ideal $(0)$ and sole nonzero idempotent $1\otimes 1$.
2. *Self-tensor base change $K_2=E=\mathbb Q(\alpha)$.* In $E[Y]$, $Y^3-2=(Y-\alpha)(Y^2+\alpha Y+\alpha^2)$, where $Y^2+\alpha Y+\alpha^2$ has negative discriminant $-3\alpha^2<0$ in $E\subset\mathbb R$ and is therefore irreducible over $E$. Hence
   $$
   E\otimes_{\mathbb Q}E\xrightarrow{\sim} E\times E[Y]/(Y^2+\alpha Y+\alpha^2)\cong E\times\mathbb Q(\alpha,\omega)
   $$
   splits into two separable field extensions of $E$ of **unequal** degrees $1$ and $2$ ($1+2=3$). Because $A_1=E$ and $A_2\cong E(\omega)$ have different degrees over $E$, $A_1\not\simeq_E A_2$: without normality of $E/\mathbb Q$, the coordinate factors of $K\otimes_{\mathbb Q}E$ need not be isomorphic. From $(Y^2+\alpha Y+\alpha^2)-(Y+2\alpha)(Y-\alpha)=3\alpha^2$ and $\alpha^{-1}=\frac{1}{2}\alpha^2$, $\alpha^{-2}=\frac{1}{2}\alpha$, the primitive orthogonal idempotents in $E\otimes_{\mathbb Q}E$ are
   $$
   e_{\mathrm{diag}}=\frac{1}{3}\Bigl(1\otimes 1+\frac{\alpha^2}{2}\otimes\alpha+\frac{\alpha}{2}\otimes\alpha^2\Bigr),\qquad e_{\mathrm{off}}=1\otimes 1-e_{\mathrm{diag}}=\frac{2}{3}(1\otimes 1)-\frac{\alpha^2}{6}\otimes\alpha-\frac{\alpha}{6}\otimes\alpha^2.
   $$
   Under the multiplication map $\mu:E\otimes_{\mathbb Q}E\to E$, $\mu(e_{\mathrm{diag}})=\frac{1}{3}(1+1+1)=1$ and $(1\otimes\alpha-\alpha\otimes 1)e_{\mathrm{diag}}=\frac{1}{3}(1\otimes\alpha+\frac{\alpha^2}{2}\otimes\alpha^2+\alpha\otimes 1-\alpha\otimes 1-1\otimes\alpha-\frac{\alpha^2}{2}\otimes\alpha^2)=0$, so $e_{\mathrm{diag}}$ is simultaneously the Chinese-remainder idempotent of $\ker\mu$ and the concrete separability idempotent (`FormallyUnramified.elem`) of $E/\mathbb Q$.
3. *Splitting-field base change $L=\mathbb Q(\alpha,\omega)$.* Over $L$, $Y^3-2=(Y-\alpha)(Y-\omega\alpha)(Y-\omega^2\alpha)$ splits completely, indexed by the three $\mathbb Q$-embeddings $\sigma_k:E\hookrightarrow L$, $\sigma_k(\alpha)=\omega^k\alpha$ ($k=0,1,2$). In the $L$-basis $\{1\otimes 1,1\otimes\alpha,1\otimes\alpha^2\}$, the evaluation isomorphism $\Psi_L:L\otimes_{\mathbb Q}E\xrightarrow{\sim}L^3$ has Vandermonde matrix $W$ and inverse $W^{-1}$:
   $$
   W=\begin{pmatrix}1&\alpha&\alpha^2\\ 1&\omega\alpha&\omega^2\alpha^2\\ 1&\omega^2\alpha&\omega\alpha^2\end{pmatrix},\qquad W^{-1}=\frac{1}{3}\begin{pmatrix}1&1&1\\[3pt] \frac{\alpha^2}{2}&\omega^2\frac{\alpha^2}{2}&\omega\frac{\alpha^2}{2}\\[3pt] \frac{\alpha}{2}&\omega\frac{\alpha}{2}&\omega^2\frac{\alpha}{2}\end{pmatrix},
   $$
   with $\det W=\alpha^3(\omega-1)(\omega^2-1)(\omega^2-\omega)=2(-3-6\omega)=-6-12\omega\in L^\times$ and $(\det W)^2=-108=\operatorname{disc}(X^3-2)$. The $k$-th column of $W^{-1}$ gives the primitive idempotent $e_{\sigma_k}=\frac{1}{3}(1\otimes 1+\omega^{2k}\frac{\alpha^2}{2}\otimes\alpha+\omega^k\frac{\alpha}{2}\otimes\alpha^2)$, satisfying $e_{\sigma_0}=1_L\otimes_E e_{\mathrm{diag}}$ and $e_{\sigma_1}+e_{\sigma_2}=1_L\otimes_E e_{\mathrm{off}}$. (By contrast, for the cyclic Galois cubic $E_{\mathrm{cyc}}=\mathbb Q[X]/(X^3-3X+1)$ of discriminant $81=9^2$, the roots $\beta,\beta^2-2,-\beta^2-\beta+2$ all lie in $E_{\mathrm{cyc}}$, so $E_{\mathrm{cyc}}\otimes_{\mathbb Q}E_{\mathrm{cyc}}\simeq E_{\mathrm{cyc}}^3$ already splits into three isomorphic degree-$1$ factors.)

#### Definitions

Let $R$ be a commutative ring (with $1$) and $A$ a commutative $R$-algebra.

1. **Square-zero lifting properties.** For a commutative $R$-algebra $B$ and an ideal $J\triangleleft B$ satisfying $J^2=0$, write $\pi_{B,J}:B\to B/J$ for the quotient $R$-algebra map and $\pi_{B,J}^*\colon\operatorname{Hom}_{R\text{-alg}}(A,B)\to\operatorname{Hom}_{R\text{-alg}}(A,B/J)$ for post-composition $g\mapsto\pi_{B,J}\circ g$. One calls $A$ **formally unramified** (resp. **formally smooth**, **formally étale**) over $R$ if for every commutative $R$-algebra $B$ and every ideal $J\triangleleft B$ with $J^2=0$, the map $\pi_{B,J}^*$ is injective (resp. surjective, bijective). In Mathlib (`Unramified/Basic.lean:58–122`, `Smooth/Basic.lean:70–85,371–382`, `Etale/Basic.lean:47–98`), the criteria `iff_comp_injective`, `iff_comp_surjective`, and `iff_comp_bijective` quantify over commutative $R$-algebras $B$.
2. **Finiteness conditions and finite étale algebras.** An $R$-algebra $A$ is of **finite type** (`Algebra.FiniteType R A`) if $A=R[x_1,\dots,x_m]$ is finitely generated as an $R$-algebra, of **finite presentation** (`Algebra.FinitePresentation R A`) if $A\cong R[X_1,\dots,X_m]/(g_1,\dots,g_r)$, and **essentially of finite type** (`Algebra.EssFiniteType R A`, `EssentialFiniteness.lean:40–99`) if $A$ is the localization $S^{-1}A_0$ of a finite-type $R$-subalgebra $A_0\subseteq A$. Every finite-dimensional algebra over a field $F$ is of finite type (`Module.Finite.finiteType`, `FiniteType.lean:55–57`), hence essentially of finite type (`EssFiniteType.of_finiteType`, `:95`) and finitely presented (since $F[X_1,\dots,X_m]$ is Noetherian). One calls $A$ **étale** over $R$ (`Algebra.Etale R A`, `Etale/Basic.lean:206–209`) if $A$ is formally étale and of finite presentation over $R$; over a field $F$, Theorem 3 shows that every étale $F$-algebra is automatically finite-dimensional over $F$ ("finite étale").
3. **Artinian rings, maximal spectrum, and reducedness.** A commutative ring $A$ is **Artinian** (`IsArtinianRing A`) if every descending chain $I_0\supseteq I_1\supseteq I_2\supseteq\cdots$ of ideals of $A$ stabilizes (`Artinian/Defs.lean:43–69`). Its **maximal spectrum** $\operatorname{MaxSpec}(A)$ (`MaximalSpectrum A`, `Spectrum/Maximal/Defs.lean:27–30`) is the set of maximal ideals $\mathfrak m\triangleleft A$, its **nilradical** is $\operatorname{nilradical}(A)=\{a\in A:\exists n\ge 1,\ a^n=0\}$, and $A$ is **reduced** (`IsReduced A`) if $\operatorname{nilradical}(A)=\{0\}$.
4. **Complete orthogonal and primitive idempotents.** A family $(e_i)_{i\in I}$ in $A$ indexed by a finite set $I$ is a **complete family of orthogonal idempotents** (`CompleteOrthogonalIdempotents`, `Idempotents.lean:52–67,129–140`) if $e_i^2=e_i$ for all $i$, $e_ie_j=0$ for $i\ne j$, and $\sum_{i\in I}e_i=1_A$. A nonzero idempotent $e\in A$ is **primitive** if it cannot be written as $e=e'+e''$ with nonzero orthogonal idempotents $e',e''\in A$, equivalently if the corner ring $Ae$ (with multiplicative identity $e$) is connected (has only $0$ and $e$ as idempotents).
5. **Zero-algebra and empty-product convention.** We allow the zero $F$-algebra $A=\{0\}$ (where $0_A=1_A$ and $\dim_F A=0$). Its maximal spectrum $\operatorname{MaxSpec}(\{0\})=\emptyset$ is empty because maximal ideals are proper ($1\notin\mathfrak m$). Over $I=\emptyset$, the empty product $\prod_{i\in\emptyset}A_i$ is the one-element zero $F$-algebra, the empty sum of idempotents is $0=1_{\{0\}}$, and universal quantifiers $\forall i\in\emptyset,\ \dots$ hold vacuously; thus $\{0\}$ is étale over $F$ and satisfies Theorem 3 with $I=\emptyset$ and $\dim_F\{0\}=0=\sum_{i\in\emptyset}[A_i:F]$. Conversely, if $F$, $E$, and $K$ are fields ($1\ne 0$), then $\dim_F E\ge 1$ and $\dim_K(K\otimes_F E)=\dim_F E\ge 1$, so $1\otimes 1\ne 0$ in $K\otimes_F E$ and its factor index set $I$ is necessarily nonempty.

#### Lemma 1. Maximal-spectrum product decomposition of reduced Artinian algebras [Lean, read]

For every field $F$ and every finite-dimensional commutative $F$-algebra $A$:

1. $A$ is an Artinian ring, $\operatorname{MaxSpec}(A)$ is finite, every prime ideal of $A$ is maximal, and $\operatorname{nilradical}(A)=\bigcap_{\mathfrak m\in\operatorname{MaxSpec}(A)}\mathfrak m$.
2. The canonical $F$-algebra homomorphism
   $$
   \Phi_A:A\longrightarrow\prod_{\mathfrak m\in\operatorname{MaxSpec}(A)}A/\mathfrak m,\qquad \Phi_A(a)=(a\bmod\mathfrak m)_{\mathfrak m\in\operatorname{MaxSpec}(A)},
   $$
   is surjective with $\ker\Phi_A=\operatorname{nilradical}(A)$.
3. Consequently, $A$ is reduced if and only if $\Phi_A$ is an $F$-algebra isomorphism. When $A$ is reduced, setting $e_{\mathfrak m}=\Phi_A^{-1}(\delta_{\mathfrak m})$ (where $\delta_{\mathfrak m}$ has $1$ in coordinate $\mathfrak m$ and $0$ elsewhere) gives the unique family of primitive pairwise orthogonal idempotents of $A$ with $\sum_{\mathfrak m\in\operatorname{MaxSpec}(A)}e_{\mathfrak m}=1_A$; each corner ring $Ae_{\mathfrak m}$ is a field isomorphic to $A/\mathfrak m$ via $ae_{\mathfrak m}\mapsto a\bmod\mathfrak m$, and $\mathfrak m=A(1-e_{\mathfrak m})$.

*Proof.* (1) Every ideal of $A$ is an $F$-linear subspace. Since $\dim_F A<\infty$, any descending chain of subspaces has strictly decreasing dimensions at at most $\dim_F A$ steps and therefore stabilizes, so $A$ is Artinian. Let $\mathfrak p\triangleleft A$ be a prime ideal; then $D=A/\mathfrak p$ is an Artinian integral domain. For any $0\ne d\in D$, the descending chain $(d)\supseteq(d^2)\supseteq\cdots$ stabilizes: $d^n=d^{n+1}u$ for some $n\ge 1$ and $u\in D$, so $d^n(1-du)=0$ in the domain $D$, forcing $du=1$. Hence $D$ is a field and $\mathfrak p$ is maximal.

Suppose for contradiction that $\operatorname{MaxSpec}(A)$ were infinite. Consider the nonempty collection $\mathcal F$ of all finite intersections $\mathfrak m_1\cap\cdots\cap\mathfrak m_r$ of maximal ideals of $A$. Because $A$ is Artinian, $\mathcal F$ contains a minimal element $J=\mathfrak m_1\cap\cdots\cap\mathfrak m_r$ (if no member were minimal, one could choose a strictly descending infinite sequence in $\mathcal F$). For any $\mathfrak m\in\operatorname{MaxSpec}(A)$, $J\cap\mathfrak m\in\mathcal F$ and $J\cap\mathfrak m\subseteq J$, so minimality gives $J\subseteq\mathfrak m$. Since $\mathfrak m_1\cdots\mathfrak m_r\subseteq J\subseteq\mathfrak m$ and $\mathfrak m$ is prime, $\mathfrak m_k\subseteq\mathfrak m$ for some $1\le k\le r$, whence $\mathfrak m_k=\mathfrak m$ by maximality of $\mathfrak m_k$. Thus $\operatorname{MaxSpec}(A)\subseteq\{\mathfrak m_1,\dots,\mathfrak m_r\}$, proving $\operatorname{MaxSpec}(A)$ finite.

If $a\in\operatorname{nilradical}(A)$, say $a^n=0$, then $a^n\in\mathfrak m$ implies $a\in\mathfrak m$ for every prime (hence every maximal) ideal $\mathfrak m$. Conversely, if $a\in A$ is not nilpotent, the multiplicative set $S=\{1,a,a^2,\dots\}$ does not contain $0$, so by Zorn's lemma the poset of ideals of $A$ disjoint from $S$ (ordered by inclusion, closed under nonempty chains because $1$ and $a^n$ lie in a union only if they lie in one member) has a maximal element $\mathfrak p$. Standard avoidance shows $\mathfrak p$ is prime: if $bc\in\mathfrak p$ with $b,c\notin\mathfrak p$, both $\mathfrak p+(b)$ and $\mathfrak p+(c)$ meet $S$, giving $a^m\in\mathfrak p+(b)$ and $a^k\in\mathfrak p+(c)$, hence $a^{m+k}\in\mathfrak p+(bc)=\mathfrak p$, impossible. By the previous paragraph $\mathfrak p$ is maximal in $A$, and $a\notin\mathfrak p$. Thus $\operatorname{nilradical}(A)=\bigcap_{\mathfrak m\in\operatorname{MaxSpec}(A)}\mathfrak m$.

(2) Clearly $\ker\Phi_A=\bigcap_{\mathfrak m\in\operatorname{MaxSpec}(A)}\mathfrak m=\operatorname{nilradical}(A)$, and $\Phi_A$ is $F$-linear because each quotient map $A\to A/\mathfrak m$ is an $F$-algebra homomorphism. Write the finite set $\operatorname{MaxSpec}(A)$ as $\{\mathfrak m_1,\dots,\mathfrak m_r\}$ (if $r=0$, $1\in\bigcap_{\emptyset}\mathfrak m=A$ makes $A=\{0\}$ and $\Phi_A:\{0\}\to\prod_{\emptyset}$ is trivially bijective). For $j\ne i$, $\mathfrak m_i\ne\mathfrak m_j$ and maximality imply $\mathfrak m_i+\mathfrak m_j=A$, so $u_{i,j}+v_{i,j}=1$ for some $u_{i,j}\in\mathfrak m_i$ and $v_{i,j}\in\mathfrak m_j$. The product $c_i=\prod_{j\ne i}v_{i,j}\in A$ satisfies $c_i\equiv\prod_{j\ne i}(1-u_{i,j})\equiv 1\pmod{\mathfrak m_i}$ while $c_i\in\mathfrak m_j$ for every $j\ne i$. Given any target tuple $(a_i\bmod\mathfrak m_i)_{i=1}^r$, the element $a=\sum_{i=1}^r a_ic_i\in A$ satisfies $a\equiv a_i\pmod{\mathfrak m_i}$ for all $i$, proving $\Phi_A$ surjective.

(3) Since $\Phi_A$ is surjective with kernel $\operatorname{nilradical}(A)$, $\Phi_A$ is bijective if and only if $\operatorname{nilradical}(A)=\{0\}$ (note that any product of fields has no nonzero nilpotents). When $\Phi_A$ is an isomorphism, transporting the canonical complete orthogonal idempotents $(\delta_{\mathfrak m})_{\mathfrak m}$ of $\prod_{\mathfrak m}A/\mathfrak m$ along $\Phi_A^{-1}$ produces pairwise orthogonal idempotents $e_{\mathfrak m}=\Phi_A^{-1}(\delta_{\mathfrak m})$ summing to $1_A$, with $Ae_{\mathfrak m}\cong(A/\mathfrak m)\delta_{\mathfrak m}\cong A/\mathfrak m$ a field (hence connected, making each $e_{\mathfrak m}$ nonzero and primitive) and $\mathfrak m=\ker(\mathrm{eval}_{\mathfrak m}\circ\Phi_A)=A(1-e_{\mathfrak m})$. Conversely, in any decomposition $1_A=\sum_{k\in K}f_k$ into nonzero primitive orthogonal idempotents, $\Phi_A(f_k)$ is a nonzero primitive idempotent in $\prod_{\mathfrak m}A/\mathfrak m$, hence equals $\delta_{\mathfrak m}$ for a unique $\mathfrak m$, proving uniqueness up to indexing. $\square$

**The fixed proof.** Mathlib derives `IsArtinianRing A` from `Module.Finite F A` via `isArtinian_of_tower F inferInstance` or `IsArtinianRing.of_finite F A` (`Artinian/Module.lean:369–375,394–405`, using `DivisionSemiring.instIsArtinianRing`). Every Artinian domain is a field by `surjective_of_injective_endomorphism` on left multiplication (`:163–171,536–547`), whence `isMaximal_of_isPrime` and `primeSpectrumEquivMaximalSpectrum` (`:550–565`). Finiteness of `MaximalSpectrum A` is `setOfPred_isMaximal_finite` (`:517–527`, extracting a minimal finite infimum via `IsArtinianRing.set_has_minimal` and `Finset.exists_inf_le` plus `Ideal.IsPrime.inf_le'`), and `nilradical_eq_iInf` (`:590–591`) rewrites `nilradical A = sInf {J | J.IsPrime}` using `isPrime_iff_isMaximal`. Pairwise coprimality `MaximalSpectrum.isCoprime_of_ne` (`Spectrum/Maximal/Basic.lean:50–51`) feeds the Chinese remainder equivalence `Ideal.quotientInfRingEquivPiQuotient` (`Ideal/Quotient/Operations.lean:202–252`) inside `IsArtinianRing.quotNilradicalEquivPi` (`Artinian/Module.lean:613–621`); specializing `nilradical A = ⊥` under `[IsReduced A]` via `AlgEquiv.quotientBot` yields `IsArtinianRing.equivPi` (`:633–639`). [Mathlib, Artinian/Module:517–639](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Artinian/Module.lean#L517-L639) · [Ideal/Quotient/Operations:202–252](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Ideal/Quotient/Operations.lean#L202-L252)

#### Lemma 2. Infinitesimal lifting, finite products, and the unramified field supply [Lean, read]

Let $F$ be a field.

1. (*Separable field extensions are formally étale.*) For every separable algebraic field extension $L/F$, $L$ is formally étale over $F$.
2. (*Finite product transfer.*) For every finite index set $I$ and family $(A_i)_{i\in I}$ of commutative $F$-algebras, $\prod_{i\in I}A_i$ is formally unramified (resp. formally smooth, formally étale) over $F$ if and only if each $A_i$ is.
3. (*Finiteness, reducedness, and separability from formal unramifiedness.*) Every essentially-of-finite-type formally unramified commutative $F$-algebra $A$ satisfies $\dim_F A<\infty$ and is reduced. If moreover $A=L$ is a field, then $L/F$ is algebraic and separable.

*Proof.* (1) First assume $[L:F]<\infty$. By the primitive element theorem (§5.3.1.9), $L=F(\alpha)\cong F[X]/(p(X))$ where $p=\operatorname{minpoly}_F(\alpha)$ is separable, so $p'(\alpha)\ne 0$ in the field $L$. Let $B$ be a commutative $F$-algebra, $J\triangleleft B$ an ideal with $J^2=0$, and $\bar f:L\to B/J$ an $F$-algebra homomorphism. Put $\bar x=\bar f(\alpha)\in B/J$. Because $\bar f$ is an $F$-algebra map out of the field $L$, $p(\bar x)=\bar f(p(\alpha))=0$ and $p'(\bar x)=\bar f(p'(\alpha))$ is a unit in $B/J$ with inverse $\bar f(p'(\alpha)^{-1})$. Choose any preimage $x\in B$ of $\bar x$ and any preimage $u\in B$ of $-p'(\bar x)^{-1}\in B/J$; then $p(x)\in J$ and $1+u\,p'(x)\in J$. For every $\delta\in J$, $\delta^2=0$ expands $(x+\delta)^k=x^k+kx^{k-1}\delta$ in $B$, giving the exact first-order Taylor identity
$$
p(x+\delta)=p(x)+\delta\,p'(x).
$$
Taking $\delta=u\,p(x)\in J$ gives
$$
p(x+u\,p(x))=p(x)+u\,p(x)\,p'(x)=\bigl(1+u\,p'(x)\bigr)p(x)\in J^2=\{0\},
$$
so the quotient property (§5.3.1.10) defines an $F$-algebra lift $g:L\to B$ sending $\alpha\mapsto x+u\,p(x)$ and reducing to $\bar f$ modulo $J$. For uniqueness, if $g_1,g_2:L\to B$ both lift $\bar f$, then $\eta=g_1(\alpha)-g_2(\alpha)\in J$ satisfies $\eta^2=0$, whence $0=p(g_1(\alpha))-p(g_2(\alpha))=\eta\,p'(g_2(\alpha))$. Since $1+u\,p'(g_2(\alpha))=z\in J$ has $z^2=0$, $(-u)(1+z)p'(g_2(\alpha))=1-z^2=1$, so $p'(g_2(\alpha))\in B^\times$ and $\eta=0$, proving $g_1=g_2$.

For an arbitrary separable algebraic extension $L/F$, every $k\in L$ generates a finite separable subextension $F(k)/F$, which therefore admits a unique lift $g_k:F(k)\to B$ of $\bar f|_{F(k)}$. Given $x,y\in L$, $F(x,y)/F$ is finite separable and so $F(x,y)=F(\gamma)$ for some $\gamma\in L$ (§5.3.1.9). By uniqueness on $F(x)$ and $F(y)$, $g_\gamma|_{F(x)}=g_x$ and $g_\gamma|_{F(y)}=g_y$, so $g(x):=g_x(x)$ preserves $1,0,+,\cdot$ and $F$-scalars and is the unique $F$-algebra lift $L\to B$ of $\bar f$.

(2) Write $P=\prod_{i\in I}A_i$ with complete orthogonal idempotents $(\delta_i)_{i\in I}$. For any $i\in I$ and test data $(B,J)$ with $J^2=0$, extending maps $A_i\to B$ or $A_i\to B/J$ along the projection $\mathrm{eval}_i:P\to A_i$ shows immediately that if $P$ is formally unramified or formally smooth (using a zero-outside-$i$ section on the corner component when lifting; see the fixed proof below), then $A_i$ inherits the same property. Conversely, suppose every $A_i$ is formally unramified and $g_1,g_2:P\to B$ satisfy $\pi_{B,J}\circ g_1=\pi_{B,J}\circ g_2$. For each $i\in I$, $e_i=g_1(\delta_i)$ and $e_i'=g_2(\delta_i)$ are commuting idempotents in $B$ with $e_i-e_i'\in J$; expanding the cube gives
$$
(e_i-e_i')^3=e_i^3-3e_i^2e_i'+3e_ie_i'^2-e_i'^3=e_i-3e_ie_i'+3e_ie_i'-e_i'=e_i-e_i',
$$
and since $(e_i-e_i')^2\in J^2=\{0\}$ we obtain $e_i=e_i'$. Restricting $g_1$ and $g_2$ to $A_i\cong P\delta_i\to Be_i$ gives two $F$-algebra maps into the corner $F$-algebra $Be_i$ that agree modulo the square-zero ideal $Je_i\triangleleft Be_i$; unramifiedness of $A_i$ yields $g_1|_{P\delta_i}=g_2|_{P\delta_i}$, and summing over finite $I$ gives $g_1(x)=\sum_{i\in I}g_1(x\delta_i)=\sum_{i\in I}g_2(x\delta_i)=g_2(x)$.

Next suppose every $A_i$ is formally smooth and $\bar f:P\to B/J$ is given. The elements $\bar e_i=\bar f(\delta_i)$ form a complete orthogonal family of idempotents in $B/J$. Choose arbitrary preimages $y_i\in B$ of $\bar e_i$. Because $y_i^2-y_i\in J$ and $J^2=0$, setting $z_i=3y_i^2-2y_i^3=y_i+(y_i^2-y_i)(1-2y_i)\equiv y_i\pmod J$ gives exact idempotents $z_i^2-z_i=(y_i^2-y_i)^2(4y_i^2-4y_i-3)\in J^2=\{0\}$. Enumerating $I=\{i_1,\dots,i_r\}$ (if $r=0$, $1_{B/J}=\bar f(0)=0$ forces $1_B\in J$, hence $1_B=1_B^2=0$ and $B=\{0\}$), define recursively $u_{i_k}=z_{i_k}\bigl(1-\sum_{m<k}u_{i_m}\bigr)$ for $1\le k<r$ and $u_{i_r}=1-\sum_{m<r}u_{i_m}$ (inductively, $u_{i_m}\equiv\bar e_{i_m}\pmod J$ and pairwise orthogonality $\bar e_{i_k}\bar e_{i_m}=0$ in $B/J$ give $z_{i_k}u_{i_m}\in J$, hence $(z_{i_k}u_{i_m})^2\in J^2=\{0\}$; since $z_{i_k}u_{i_m}$ is also idempotent in commutative $B$, $z_{i_k}u_{i_m}=0$, making $u_{i_k}$ idempotent and orthogonal to earlier $u_{i_m}$, while $u_{i_r}^2-u_{i_r}=0$ follows from orthogonality of $u_{i_1},\dots,u_{i_{r-1}}$). Then $(u_i)_{i\in I}$ is a complete orthogonal family of idempotents in $B$ lifting $(\bar e_i)_{i\in I}$, decomposing $B\xrightarrow{\sim}\prod_{i\in I}Bu_i$ with square-zero ideals $Ju_i\triangleleft Bu_i$. Formal smoothness of $A_i$ lifts $\bar f|_{A_i}:A_i\to(B/J)\bar e_i\cong(Bu_i)/(Ju_i)$ to $g_i:A_i\to Bu_i$, and $g((a_i)_{i\in I})=\sum_{i\in I}g_i(a_i)\in B$ lifts $\bar f$. Combining both halves gives the formally étale product equivalence.

(3) Let $A$ be essentially of finite type and formally unramified over $F$, say $A=S^{-1}A_0$ with $A_0=F[x_1,\dots,x_m]$, and let $\mu:A\otimes_F A\to A$, $u\otimes v\mapsto uv$, be multiplication with kernel $K_\Delta=\ker\mu$. Every element of $A_0\otimes_F A_0$ congruently reduces modulo $\sum_{r=1}^m(A_0\otimes_F A_0)(1\otimes x_r-x_r\otimes 1)$ to $A_0\otimes 1$, and localizing by $S\otimes S$ shows that $K_\Delta$ is finitely generated as an ideal of $A\otimes_F A$ by $\{1\otimes x_r-x_r\otimes 1:1\le r\le m\}$. Consider $B=(A\otimes_F A)/K_\Delta^2$ with square-zero ideal $J=K_\Delta/K_\Delta^2$, so $B/J\cong(A\otimes_F A)/K_\Delta\cong A$ via $\mu$. The two $F$-algebra homomorphisms $a\mapsto(1\otimes a)+K_\Delta^2$ and $a\mapsto(a\otimes 1)+K_\Delta^2$ from $A$ to $B$ both compose with $B\to B/J\cong A$ to $\mathrm{id}_A$. By formal unramifiedness of $A/F$, they are equal, so $1\otimes a-a\otimes 1\in K_\Delta^2$ for all $a\in A$, forcing $K_\Delta=K_\Delta^2$. Because $K_\Delta$ is a finitely generated ideal of $A\otimes_F A$ with $K_\Delta=K_\Delta^2$, Nakayama's determinant/Cramer trick on generators $w_1,\dots,w_m$ of $K_\Delta$ produces $e\in K_\Delta$ with $(1-e)K_\Delta=0$, hence $e^2=e$ and $K_\Delta=(e)$. Put $t=1\otimes 1-e\in A\otimes_F A$. Then $\mu(t)=1-\mu(e)=1$, while for every $x\in A$, $1\otimes x-x\otimes 1\in K_\Delta=(e)$ satisfies $(1\otimes x-x\otimes 1)t=(1\otimes x-x\otimes 1)(1-e)=0$, i.e.,
$$
(x\otimes 1)t=(1\otimes x)t\qquad(\forall x\in A).
$$
Choose an $F$-vector-space basis $(b_\lambda)_{\lambda\in\Lambda}$ of $A$, and write $t=\sum_{\lambda\in S_0}f_\lambda\otimes b_\lambda$ for a finite subset $S_0\subseteq\Lambda$ and elements $f_\lambda\in A$, so $\sum_{\lambda\in S_0}f_\lambda b_\lambda=\mu(t)=1$. For any $x\in A$, write $b_\lambda x=\sum_{\nu\in\Lambda}a_{\lambda,\nu}b_\nu$ ($a_{\lambda,\nu}\in F$). Then in $A\otimes_F A$,
$$
\sum_{\nu\in S_0}(xf_\nu)\otimes b_\nu=(x\otimes 1)t=(1\otimes x)t=\sum_{\lambda\in S_0}f_\lambda\otimes(b_\lambda x)=\sum_{\nu\in\Lambda}\Bigl(\sum_{\lambda\in S_0}a_{\lambda,\nu}f_\lambda\Bigr)\otimes b_\nu.
$$
Because $(\cdot\otimes b_\nu)_{\nu\in\Lambda}$ is an $A$-basis of $A\otimes_F A$, equating coefficients for $\nu\in S_0$ gives $xf_\nu=\sum_{\lambda\in S_0}a_{\lambda,\nu}f_\lambda$. Multiplying by $b_\nu$ and summing over $\nu\in S_0$ gives
$$
x=x\sum_{\nu\in S_0}f_\nu b_\nu=\sum_{\lambda,\nu\in S_0}a_{\lambda,\nu}(f_\lambda b_\nu),
$$
so the finite set $\{f_\lambda b_\nu:\lambda,\nu\in S_0\}$ spans $A$ over $F$, proving $\dim_F A<\infty$.

To prove $A$ is reduced, choose an algebraic closure $\overline F$ of $F$ (`[Lean]` interface). Because $F$ is a field, $1\in\overline F$ extends to an $F$-basis of $\overline F$, so $A\hookrightarrow\overline F\otimes_F A$, $a\mapsto 1\otimes a$, is injective. Base change preserves essential finite type (`EssFiniteType.baseChange`) and formal unramifiedness: any test diagram $(\overline F\otimes_F A\to B/J,\ B\to B/J)$ of $\overline F$-algebras pulls back along $A\to\overline F\otimes_F A$ to $F$-algebra maps $A\to B$ whose uniqueness on $A$ together with fixed $\overline F$-scalars gives uniqueness on $\overline F\otimes_F A$. By the previous paragraph, $C=\overline F\otimes_F A$ has $\dim_{\overline F}C<\infty$, hence is Artinian by Lemma 1(1). Suppose $C$ had a nonzero nilpotent element; by Lemma 1(2) and localization, at some maximal ideal $\mathfrak M\in\operatorname{MaxSpec}(C)$ the localization $R=C_{\mathfrak M}$ is a local Artinian $\overline F$-algebra whose maximal ideal $\mathfrak m_R$ is nilpotent ($\mathfrak m_R^N=0$). Since $\dim_{\overline F}(R/\mathfrak m_R)\le\dim_{\overline F}C<\infty$ and $\overline F$ is algebraically closed, the structure map $\overline F\to R/\mathfrak m_R$ is an isomorphism; let $\rho:R\to R/\mathfrak m_R\cong\overline F$ be the inverse-composed residue $\overline F$-algebra map. Because $R=C_{\mathfrak M}$ is a localization of formally unramified $C/\overline F$, $R/\overline F$ is formally unramified: if $g_1,g_2:C\to B$ agree modulo $J$ ($J^2=0$) and map $C\setminus\mathfrak M$ to units (which is automatic since $(B/J)^\times$ pulls back to $B^\times$ across $J^2=0$), universal localization extends uniqueness from $C$ to $R$. Now pass to $B=R/\mathfrak m_R^2$ with square-zero ideal $J=\mathfrak m_R/\mathfrak m_R^2$: both the quotient map $q:R\to R/\mathfrak m_R^2$ and the scalar composite $\eta\circ\rho:R\to\overline F\to R/\mathfrak m_R^2$ reduce modulo $J$ to $\rho:R\to R/\mathfrak m_R$, so formal unramifiedness of $R/\overline F$ forces $q=\eta\circ\rho$. That means every element of $\mathfrak m_R=\ker\rho$ vanishes in $R/\mathfrak m_R^2$, i.e., $\mathfrak m_R=\mathfrak m_R^2$. Inducting gives $\mathfrak m_R=\mathfrak m_R^N=\{0\}$, so $R\cong\overline F$ is reduced. Since an element of $C$ vanishing in $C_{\mathfrak M}$ for all $\mathfrak M\in\operatorname{MaxSpec}(C)$ has annihilator ideal contained in no maximal ideal and hence equal to $C$, $C=\overline F\otimes_F A$ is reduced, and its subring $A$ is reduced.

Finally, suppose $A=L$ is a field. Then $[L:F]=\dim_F L<\infty$, so $L/F$ is algebraic. Let $L_{\mathrm{sep}}=\{x\in L:\operatorname{minpoly}_F(x)\text{ is separable}\}$ be the separable closure of $F$ in $L$. Any square-zero lifting problem for $L$ over $L_{\mathrm{sep}}$ restricts scalars to a square-zero lifting problem over $F$, so $L$ remains formally unramified and finite-dimensional over $L_{\mathrm{sep}}$. By base change and the reducedness result just proved over the field $L_{\mathrm{sep}}$ (applied to the base change $L\otimes_{L_{\mathrm{sep}}}L$ over $L$), the commutative ring $L\otimes_{L_{\mathrm{sep}}}L$ is reduced. On the other hand, $L/L_{\mathrm{sep}}$ is purely inseparable: if $\operatorname{char}F=0$, every irreducible polynomial over $F$ is separable so $L=L_{\mathrm{sep}}$ immediately; if $\operatorname{char}F=p>0$, every $x\in L$ has minimal polynomial over $L_{\mathrm{sep}}$ of the form $X^{p^n}-c$ ($c\in L_{\mathrm{sep}}$, $n\ge 0$), since factoring out the highest $p$-power $P(X)=Q(X^{p^n})$ with $Q'\ne 0$ makes $x^{p^n}$ separable over $L_{\mathrm{sep}}$ and hence already in $L_{\mathrm{sep}}$. Thus $x^{p^n}\in L_{\mathrm{sep}}$ commutes across $\otimes_{L_{\mathrm{sep}}}$, giving in characteristic $p$:
$$
(1\otimes x-x\otimes 1)^{p^n}=1\otimes x^{p^n}-x^{p^n}\otimes 1=0\quad\text{in }L\otimes_{L_{\mathrm{sep}}}L.
$$
Because $L\otimes_{L_{\mathrm{sep}}}L$ is reduced, $1\otimes x-x\otimes 1=0$. If $x\notin L_{\mathrm{sep}}$, $\{1,x\}$ would be $L_{\mathrm{sep}}$-linearly independent in $L$, making $\{1\otimes 1,1\otimes x,x\otimes 1,x\otimes x\}$ $L_{\mathrm{sep}}$-linearly independent in $L\otimes_{L_{\mathrm{sep}}}L$ and contradicting $1\otimes x=x\otimes 1$. Hence $x\in L_{\mathrm{sep}}$ for all $x\in L$, proving $L/F$ separable. $\square$

**The fixed proof.** Part (1) is `FormallyEtale.of_isSeparable_aux` (`Etale/Field.lean:56–96`, following Iversen Corollary II.5.3 with `Field.powerBasisOfFiniteOfSeparable` and `Polynomial.eval_add_of_sq_eq_zero`, paired with `FormallyUnramified.of_isSeparable` at `Unramified/Field.lean:44–56`) and the directed-subfield gluing `FormallyEtale.of_isSeparable` (`Etale/Field.lean:98–156`, calling `Field.exists_primitive_element` on $K(x,y)$). Part (2) is `FormallyEtale.pi_iff` (`Etale/Pi.lean:31–35`), combining `FormallyUnramified.pi_iff` (`Unramified/Pi.lean:28–98`, which treats commutative target rings $B$ by localizing away `Pi.single x 1` and forming the corner ring of $e=f_1(\delta_x)$) and `FormallySmooth.pi_iff` (`Smooth/Pi.lean:50–120`, lifting `CompleteOrthogonalIdempotents.single` across `I^2 = ⊥` via `CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker` in `Idempotents.lean:325–332` and decomposing $B$ via `bijective_pi` at `:424–438`). In Part (3), the diagonal idempotent `elem` and spanning set $\{f_ib_j:i,j\in s\}$ are `iff_exists_tensorProduct`, `elem`, and `finite_of_free` (`Unramified/Finite.lean:51–232`); reducedness over a field is `FormallyUnramified.isReduced_of_field` (`Unramified/Field.lean:61–153`, which in `bijective_of_isAlgClosed_of_isLocalRing` applies the retraction `sec` of `Unramified/Finite.lean:238–273` to show $1-f(1)$ is both idempotent and in the nilpotent maximal ideal of the localized $\overline K\otimes_K A$, hence $0$); and separability via `separableClosure` and $(1\otimes x-x\otimes 1)^{q^n}=0$ is `range_eq_top_of_isPurelyInseparable` and `FormallyUnramified.isSeparable` (`Unramified/Field.lean:161–215`, using `PurelyInseparable/Basic.lean:224–227,481–489`). [Mathlib, Etale/Field:56–160](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Etale/Field.lean#L56-L160) · [Unramified/Finite:51–232](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Unramified/Finite.lean#L51-L232) · [Unramified/Field:44–220](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Unramified/Field.lean#L44-L220)

#### Theorem 3. Product-of-fields equivalence for formally étale and finite étale algebras [Lean, read]

Let $F$ be a field and $A$ a commutative $F$-algebra.

1. (*Essentially-of-finite-type formally étale equivalence.*) Assume $A$ is essentially of finite type over $F$. Then the following are equivalent:
   - (a) $A$ is formally étale over $F$;
   - (b) $A$ is formally unramified over $F$;
   - (c) there exist a finite index set $I$, a family $(A_i)_{i\in I}$ of separable algebraic field extensions of $F$, and an $F$-algebra isomorphism $e:A\xrightarrow{\sim}\prod_{i\in I}A_i$.
   Moreover, when (a)–(c) hold, $\dim_F A<\infty$, every $A_i$ satisfies $[A_i:F]<\infty$ with $\dim_F A=\sum_{i\in I}[A_i:F]$, and one may take canonically $I=\operatorname{MaxSpec}(A)$, $A_{\mathfrak m}=A/\mathfrak m$, and $e=\Phi_A$ from Lemma 1.
2. (*Unconditional finite étale equivalence.*) Without assuming essential finite type in advance, $A$ is étale over $F$ if and only if there exist a finite index set $I$, a family $(A_i)_{i\in I}$ of **finite** separable field extensions of $F$, and an $F$-algebra isomorphism $e:A\xrightarrow{\sim}\prod_{i\in I}A_i$.

*Proof.* (1) Clearly (a) $\Rightarrow$ (b) by definition of formal étaleness. Assume (b): $A$ is essentially of finite type and formally unramified over $F$. By Lemma 2(3), $\dim_F A<\infty$ and $A$ is reduced. By Lemma 1, $\operatorname{MaxSpec}(A)$ is finite and $\Phi_A:A\xrightarrow{\sim}\prod_{\mathfrak m\in\operatorname{MaxSpec}(A)}A/\mathfrak m$ is an $F$-algebra isomorphism onto a finite product of fields $A/\mathfrak m$. Transporting formal unramifiedness across $\Phi_A$ and applying Lemma 2(2) shows that each residue field $A/\mathfrak m$ is formally unramified over $F$ (and finite-dimensional over $F$, since $A\twoheadrightarrow A/\mathfrak m$ is $F$-linear and surjective, hence essentially of finite type). Lemma 2(3) applied to the field $L=A/\mathfrak m$ shows that $A/\mathfrak m$ is separable over $F$, giving (c) with $I=\operatorname{MaxSpec}(A)$ and $\dim_F A=\sum_{\mathfrak m\in\operatorname{MaxSpec}(A)}[A/\mathfrak m:F]$. Finally, assume (c): $e:A\xrightarrow{\sim}\prod_{i\in I}A_i$ with $I$ finite and each $A_i/F$ separable (since $A$ is essentially of finite type and projects onto $A_i$ once Lemma 2(1)–(2) gives formal unramifiedness, Lemma 2(1) does not even require finiteness of $[A_i:F]$!). Lemma 2(1) shows each $A_i$ is formally étale over $F$, Lemma 2(2) shows $\prod_{i\in I}A_i$ is formally étale over $F$, and transporting along $e^{-1}$ gives (a).

(2) If $A$ is étale over $F$, then $A$ is formally étale and finitely presented (hence of finite type, hence essentially of finite type) over $F$. Part (1) supplies $e:A\xrightarrow{\sim}\prod_{i\in I}A_i$ with $I$ finite, $\dim_F A<\infty$, and each $A_i/F$ separable; surjectivity of $\mathrm{eval}_i\circ e:A\twoheadrightarrow A_i$ gives $[A_i:F]\le\dim_F A<\infty$. Conversely, if $e:A\xrightarrow{\sim}\prod_{i\in I}A_i$ with $I$ finite and each $[A_i:F]<\infty$ and $A_i/F$ separable, then $\dim_F(\prod_{i\in I}A_i)=\sum_{i\in I}[A_i:F]<\infty$, so $\dim_F A<\infty$. As a finite-dimensional $F$-algebra, $A=F[x_1,\dots,x_n]\cong F[X_1,\dots,X_n]/\ker\mathrm{ev}$ is finitely presented over the Noetherian polynomial ring $F[X_1,\dots,X_n]$, while Lemma 2(1)–(2) transported along $e^{-1}$ makes $A$ formally étale over $F$; hence $A$ is étale over $F$. $\square$

**The fixed proof.** In `Mathlib/RingTheory/Etale/Field.lean`, (a) $\Leftrightarrow$ (b) is `Algebra.FormallyEtale.iff_formallyUnramified_of_field` (`:175–187`), and (a) $\Leftrightarrow$ (c) is `Algebra.FormallyEtale.iff_exists_algEquiv_prod` (`:194–213`). In the forward branch (`:201–209`), given `H : FormallyEtale K A`, lines 202–204 deduce `FormallyUnramified.finite_of_free K A`, `FormallyUnramified.isReduced_of_field K A`, and `IsArtinianRing A := isArtinian_of_tower K inferInstance` (line 205 also notes the idempotents `v i := (IsArtinianRing.equivPi A).symm (Pi.single i 1)`). Lines 206–209 rewrite `H` across `(IsArtinianRing.equivPi A).restrictScalars K` via `FormallyEtale.iff_of_equiv` (`Etale/Basic.lean:104–105`) and `FormallyEtale.pi_iff` (`Etale/Pi.lean:31–35`), then apply `(iff_isSeparable _ _).mp` (`Etale/Field.lean:158–160`) to each quotient `A ⧸ m.asIdeal` (equipped with `IsArtinianRing.fieldOfSubtypeIsMaximal` at `:189`). The reverse branch (`:210–212`) rewrites along `e` and `pi_iff` and discharges each coordinate by `of_isSeparable K (Ai I)`. Part (2) is `Algebra.Etale.iff_exists_algEquiv_prod` (`:271–286`), obtaining `Module.Finite K (Ai i)` via `Module.Finite.of_surjective ((LinearMap.proj i).comp e.toLinearMap)` and the reverse finite presentation via `FinitePresentation.of_finiteType` over the Noetherian field `K`. [Mathlib, Etale/Field:175–286](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Etale/Field.lean#L175-L286)

#### Theorem 4. Base change, coordinate tensor splitting, and cyclic Galois factors [Lean, read]

Let $F$ be a field.

1. (*Base change stability.*) For every étale $F$-algebra $A$ and every field extension $K/F$, the tensor product $K\otimes_F A$ is an étale $K$-algebra of $K$-dimension $\dim_F A$, hence isomorphic as a $K$-algebra to $\prod_{\mathfrak M\in\operatorname{MaxSpec}(K\otimes_F A)}(K\otimes_F A)/\mathfrak M$, a finite product of finite separable field extensions of $K$.
2. (*Embedding-indexed coordinate splitting.*) Let $A$ be an étale $F$-algebra with $A\simeq_F\prod_{j=1}^m E_j$ ($E_j/F$ finite separable field extensions), and let $L/F$ be a field extension in which the minimal polynomial over $F$ of every element of every $E_j$ splits into linear factors in $L[X]$ (for example, a splitting field over $F$ of $\prod_{j=1}^m\operatorname{minpoly}_F(\alpha_j)$ where $E_j=F(\alpha_j)$, or any separably closed extension $L/F$). Put $\Sigma=\operatorname{Hom}_{F\text{-alg}}(A,L)$. Then $\Sigma$ is finite with $\lvert\Sigma\rvert=\dim_F A$, and the $L$-algebra evaluation map
   $$
   \Psi_L:L\otimes_F A\xrightarrow{\;\sim\;}\prod_{\sigma\in\Sigma}L,\qquad c\otimes a\longmapsto\bigl(c\,\sigma(a)\bigr)_{\sigma\in\Sigma},
   $$
   is an isomorphism of $L$-algebras. Under $\Psi_L$, $\sigma\mapsto\ker(c\otimes a\mapsto c\,\sigma(a))$ is a bijection $\Sigma\xrightarrow{\sim}\operatorname{MaxSpec}(L\otimes_F A)$, and the primitive orthogonal idempotents $e_\sigma=\Psi_L^{-1}(\delta_\sigma)\in L\otimes_F A$ satisfy $(1\otimes a)e_\sigma=(\sigma(a)\otimes 1)e_\sigma$ for all $a\in A$.
3. (*General field base change of a finite cyclic Galois extension — the archive theorem.*) For every finite cyclic Galois field extension $E/F$ and **every** field extension $K/F$, there exist a finite cyclic Galois field extension $L/K$, a nonempty finite index set $I$, and a $K$-algebra isomorphism
   $$
   K\otimes_F E\xrightarrow{\;\sim\;}\prod_{i\in I}L,
   $$
   satisfying $\lvert I\rvert\cdot[L:K]=[E:F]$.

*Proof.* (1) Any $K$-algebra lifting diagram $(K\otimes_F A\to B/J,\ B\to B/J)$ with $J^2=0$ corresponds by the universal property of tensor products to an $F$-algebra map $A\to B/J$ (since $B$ is a $K$-algebra, the pair $(K\to B,\ A\to B)$ glues uniquely to $K\otimes_F A\to B$). Bijectivity of $\pi_{B,J}^*$ for $A/F$ therefore implies bijectivity of $\pi_{B,J}^*$ for $(K\otimes_F A)/K$. Moreover, an $F$-basis of $A$ maps via $1\otimes\cdot$ to a $K$-basis of $K\otimes_F A$, so $\dim_K(K\otimes_F A)=\dim_F A<\infty$, making $K\otimes_F A$ étale over $K$. Theorem 3(2) gives the product decomposition over $\operatorname{MaxSpec}(K\otimes_F A)$.

(2) First observe how $\Sigma=\operatorname{Hom}_{F\text{-alg}}(A,L)$ decomposes across $A\simeq_F\prod_{j=1}^m E_j$. Let $(u_j)_{j=1}^m$ be the complete orthogonal idempotents of $\prod_{j=1}^m E_j$. For any $\sigma\in\Sigma$, the elements $\sigma(u_j)\in L$ are pairwise orthogonal idempotents summing to $1_L$ in the field $L$. Since the only idempotents in a field are $0$ and $1$, there cannot be $m=0$ terms ($0\ne 1_L$), and for $m\ge 1$ exactly one index $j_0\in\{1,\dots,m\}$ has $\sigma(u_{j_0})=1_L$ while $\sigma(u_j)=0$ for $j\ne j_0$ (if $A=\{0\}$, i.e. $m=0$, then $\Sigma=\emptyset$, $L\otimes_F\{0\}=\{0\}$, and $\Psi_L:\{0\}\xrightarrow{\sim}\prod_{\emptyset}L$ holds vacuously with $\lvert\emptyset\rvert=0=\dim_F\{0\}$). Thus $\sigma$ factors uniquely through the projection onto $E_{j_0}$, giving a natural bijection $\Sigma\cong\bigsqcup_{j=1}^m\operatorname{Hom}_{F\text{-alg}}(E_j,L)$ compatible with $L\otimes_F\bigl(\prod_{j=1}^m E_j\bigr)\xrightarrow{\sim}\prod_{j=1}^m(L\otimes_F E_j)$.

This reduces (2) to a single finite separable field extension $E/F$. By §5.3.1.9, write $E=F(\alpha)\cong F[X]/(p(X))$ where $p=\operatorname{minpoly}_F(\alpha)$ is monic separable of degree $d=[E:F]$. Over $L$, the hypothesis makes $p(X)$ split in $L[X]$; because $p$ is separable over $F$, its image in $L[X]$ remains separable (§5.3.1.11) and therefore factors as $p(X)=\prod_{r\in R_L(p)}(X-r)$ over the set $R_L(p)\subseteq L$ of $\lvert R_L(p)\rvert=d$ distinct roots ([§5.3.1.12](#53112-root-multisets-and-separable-root-counting)). By the quotient universal property (§5.3.1.10), evaluation at $\alpha$ gives a bijection $\operatorname{Hom}_{F\text{-alg}}(E,L)\xrightarrow{\sim}R_L(p)$, $\sigma\mapsto\sigma(\alpha)$. Under the canonical $L$-algebra identification $L\otimes_F(F[X]/(p(X)))\xrightarrow{\sim}L[X]/(p(X))$ sending $c\otimes[Q(X)]\mapsto c[Q(X)]$, the distinct monic linear polynomials $(X-\sigma(\alpha))_{\sigma\in\operatorname{Hom}_{F\text{-alg}}(E,L)}$ generate the maximal ideals of $L[X]/(p(X))$, and the Chinese remainder map of Lemma 1 sends $[Q(X)]\mapsto\bigl(Q(\sigma(\alpha))\bigr)_\sigma$. Composing with $c\otimes a\mapsto c[Q_a(X)]$ recovers $c\otimes a\mapsto(c\,\sigma(a))_\sigma=\Psi_L(c\otimes a)$, proving $\Psi_L$ an $L$-algebra isomorphism with $\lvert\Sigma\rvert=\sum_{j=1}^m[E_j:F]=\dim_F A$. Finally, in $\prod_{\sigma\in\Sigma}L$, $\Psi_L(1\otimes a)=(\sigma(a))_\sigma$ and $\Psi_L(\sigma_0(a)\otimes 1)=(\sigma_0(a))_\sigma$ agree in the $\sigma_0$-coordinate, so multiplying by $\delta_{\sigma_0}=\Psi_L(e_{\sigma_0})$ and applying $\Psi_L^{-1}$ gives $(1\otimes a)e_{\sigma_0}=(\sigma_0(a)\otimes 1)e_{\sigma_0}$.

(3) Let $E/F$ be finite cyclic Galois and $K/F$ an arbitrary field extension. Since $E/F$ is finite and normal, choose an $F$-basis $b_1,\dots,b_d$ of $E$ and put $p(X)=\prod_{k=1}^d\operatorname{minpoly}_F(b_k)\in F[X]$. Every factor $\operatorname{minpoly}_F(b_k)$ splits in $E[X]$ by normality, and the roots of $p$ in $E$ include $b_1,\dots,b_d$ and hence generate $E$ over $F$; thus $E$ is a splitting field of $p$ over $F$.

Because $E/F$ is Galois, $E/F$ is separable, so $E$ is étale over $F$ by Theorem 3(2), and $K\otimes_F E$ is étale over $K$ by Part (1). Applying Theorem 3(1) to $K\otimes_F E$ produces a finite index set $I$, a family $(A_i)_{i\in I}$ of separable field extensions of $K$, and a $K$-algebra isomorphism
$$
e:K\otimes_F E\xrightarrow{\;\sim\;}\prod_{i\in I}A_i.
$$
As noted in Definition 5, $\dim_K(K\otimes_F E)=[E:F]\ge 1$, so $1\otimes 1\ne 0$ in $K\otimes_F E$; if $I$ were empty, $\prod_{i\in\emptyset}A_i$ would be subsingleton, contradicting $1\otimes 1\ne 0$. Hence $I$ is nonempty; fix an index $i_0\in I$.

For each $i\in I$, let $f_i=\mathrm{eval}_i\circ e:K\otimes_F E\to A_i$ be the $i$-th coordinate $K$-algebra homomorphism. Because $e$ is bijective and coordinate evaluation $\prod_{j\in I}A_j\to A_i$ is surjective, $f_i$ is surjective. Composing $f_i$ (as a ring homomorphism) with the right tensor inclusion $\mathrm{inc}_R:E\to K\otimes_F E$, $y\mapsto 1\otimes y$, yields a field embedding $\iota_i:E\hookrightarrow A_i$. For every scalar $c\in F$, $(1_K)\otimes(c\cdot 1_E)=(c\cdot 1_K)\otimes 1_E$ in $K\otimes_F E$, so $K$-linearity of $f_i$ gives the scalar compatibility
$$
\iota_i(\mathrm{algebraMap}_{F,E}(c))=f_i\bigl(\mathrm{algebraMap}_{K,K\otimes_F E}(\mathrm{algebraMap}_{F,K}(c))\bigr)=\mathrm{algebraMap}_{K,A_i}(\mathrm{algebraMap}_{F,K}(c)).
$$
Put $q=p.\mathrm{map}(\mathrm{algebraMap}_{F,K})\in K[X]$, the polynomial over $K$ obtained by applying $F\to K$ to the coefficients of $p$. We claim every factor $A_i$ ($i\in I$) is a splitting field of **this same** polynomial $q$ over $K$:

- *Splitting of $q$ in $A_i$.* Because $p$ splits in $E[X]$, transporting the linear factorization of $p.\mathrm{map}(\mathrm{algebraMap}_{F,E})$ along $\iota_i:E\to A_i$ splits $p.\mathrm{map}(\iota_i\circ\mathrm{algebraMap}_{F,E})=p.\mathrm{map}(\mathrm{algebraMap}_{K,A_i}\circ\mathrm{algebraMap}_{F,K})=q.\mathrm{map}(\mathrm{algebraMap}_{K,A_i})$ in $A_i[X]$.
- *Generation of $A_i$ over $K$ by $R_{A_i}(q)$.* Because $E=F[R_E(p)]$ as an $F$-algebra, every pure tensor $c\otimes y\in K\otimes_F E$ ($c\in K$, $y\in E$) is a $K$-linear combination of products of elements $1\otimes r$ ($r\in R_E(p)$), so $K\otimes_F E=K\bigl[\{1\otimes r:r\in R_E(p)\}\bigr]$ as a $K$-algebra. Since $f_i:K\otimes_F E\twoheadrightarrow A_i$ is a surjective $K$-algebra homomorphism, $A_i=f_i(K\otimes_F E)=K\bigl[\{\iota_i(r):r\in R_E(p)\}\bigr]$. For each $r\in R_E(p)$, $p\ne 0$ implies $q\ne 0$ (as $F\hookrightarrow K$ is injective) and $q(\iota_i(r))=\iota_i(p(r))=0$ by the scalar compatibility identity, so $\iota_i(r)\in R_{A_i}(q)$. Thus $K\bigl[R_{A_i}(q)\bigr]=A_i$.

Now let $S=q.\mathrm{SplittingField}$ be the public splitting field of $q$ over $K$ ([§5.3.1.14](#53114-constructing-splitting-fields-and-extending-embeddings)). Applying the splitting-field equivalence `IsSplittingField.algEquiv` from [the mutual-embedding manuscript (§5.3.1.15)](../sources/SOURCES.md#chapter-5-unpublished-algebra-and-finite-place-supplies) **twice** to the same polynomial $q\in K[X]$—once in the forward direction on $A_i$, giving $\psi_i:A_i\xrightarrow{\sim}S$, and once in the symmetrized direction on the fixed reference factor $A_{i_0}$, giving $\psi_{i_0}^{-1}:S\xrightarrow{\sim}A_{i_0}$—produces for each $i\in I$ a $K$-algebra isomorphism
$$
\theta_i=\psi_{i_0}^{-1}\circ\psi_i:A_i\xrightarrow{\;\sim\;}L:=A_{i_0}.
$$
Applying $\theta_i$ coordinatewise (`AlgEquiv.piCongrRight`) and composing with $e$ yields the $K$-algebra isomorphism
$$
K\otimes_F E\xrightarrow{\;e\;}\prod_{i\in I}A_i\xrightarrow{\;(\theta_i)_{i\in I}\;}\prod_{i\in I}L,
$$
whence $[E:F]=\dim_K(K\otimes_F E)=\lvert I\rvert\cdot[L:K]$. Moreover, $L=A_{i_0}$ is finite-dimensional over $K$ as a splitting field of $q$ ([§5.3.1.14](#53114-constructing-splitting-fields-and-extending-embeddings)), separable over $K$ from Theorem 3(1), and normal over $K$ because every splitting field is normal (for any $x\in L=K[R_L(q)]$, every embedding of $L$ into an algebraic closure permutes $R_L(q)$ and hence maps $L$ into $L$, splitting $\operatorname{minpoly}_K(x)$ over $L$); thus $L/K$ is finite Galois.

Finally, to see that $\operatorname{Gal}(L/K)$ is cyclic, equip $L$ with the $F$-algebra structure $F\to K\to L$ and the $E$-algebra structure $\iota_{i_0}:E\hookrightarrow L$; the scalar compatibility identity makes $F\to E\xrightarrow{\iota_{i_0}}L$ agree with $F\to K\to L$. Every $\tau\in\operatorname{Gal}(L/K)$ restricts scalars to an $F$-automorphism of $L$. Since $E/F$ is normal, $\tau(\iota_{i_0}(E))=\iota_{i_0}(E)$ (for each $y\in E$, $\tau(\iota_{i_0}(y))$ is a root in $L$ of $\operatorname{minpoly}_F(y)$, which already has all $\deg\operatorname{minpoly}_F(y)$ distinct roots inside $\iota_{i_0}(E)$), defining a group homomorphism $\varphi:\operatorname{Gal}(L/K)\to\operatorname{Gal}(E/F)$ satisfying $\iota_{i_0}(\varphi(\tau)(y))=\tau(\iota_{i_0}(y))$ for all $y\in E$. If $\tau\in\ker\varphi$, then $\tau(\iota_{i_0}(y))=\iota_{i_0}(y)$ for all $y\in E$. Then the two $K$-algebra homomorphisms $\tau\circ f_{i_0}$ and $f_{i_0}:K\otimes_F E\to L$ agree on $K\otimes 1$ (by $K$-linearity of $\tau$) and on $1\otimes E$ (since $\tau(f_{i_0}(1\otimes y))=\tau(\iota_{i_0}(y))=\iota_{i_0}(y)=f_{i_0}(1\otimes y)$), hence agree on all of $K\otimes_F E$. Because $f_{i_0}:K\otimes_F E\twoheadrightarrow L$ is surjective, every $z\in L$ has the form $z=f_{i_0}(w)$, giving $\tau(z)=\tau(f_{i_0}(w))=f_{i_0}(w)=z$. Thus $\varphi$ is injective, embedding $\operatorname{Gal}(L/K)$ as a subgroup of the cyclic group $\operatorname{Gal}(E/F)$; every subgroup of a cyclic group is cyclic, so $\operatorname{Gal}(L/K)$ is cyclic. $\square$

**The fixed proof.** Base change of formal étaleness and étaleness in Mathlib is `FormallyEtale`'s base-change instance (`Etale/Basic.lean:145–146`, combining `FormallyUnramified.base_change` at `Unramified/Basic.lean:276–284` and `FormallySmooth`'s base-change instance at `Smooth/Basic.lean:459–470`) and `Algebra.Etale.baseChange` (`Etale/Basic.lean:242`). Over a separably closed base field `K`, Mathlib packages the coordinate splitting directly as `Algebra.FormallyEtale.equivPiOfIsSepClosed` (`Etale/Field.lean:217–227`), composing `(IsArtinianRing.equivPi A).restrictScalars K` with `AlgEquiv.piCongrRight` of `(AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m.asIdeal)) (IsSepClosed.algebraMap_bijective _ _)).symm` and `AlgEquiv.piCongrLeft` (`Algebra/Algebra/Pi.lean:171–239`) along `IsArtinianRing.primeSpectrumEquivMaximalSpectrum`. Part (3) is `UpperTheory.exists_cyclic_galois_tensor_algEquiv_pi` in A2's `ExistsCyclicGaloisTensorAlgEquivPi.lean:67–93`, built over the three private lemmas `comp_eq` (`:5–18`), `splitting` (`:19–39`, calling `Algebra.TensorProduct.adjoin_one_tmul_image_eq_top` from `TensorProduct/Basic.lean:549–556`), and `cyclic` (`:41–66`, calling `AlgEquiv.restrictNormalHom` from `Normal/Basic.lean:233–236` and `Algebra.TensorProduct.ext` from `TensorProduct/Basic.lean:353–360`). [Mathlib, Etale/Field:217–227](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Etale/Field.lean#L217-L227) · [Algebra/Pi:171–239](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Algebra/Pi.lean#L171-L239) · [A2, ExistsCyclicGaloisTensorAlgEquivPi.lean:5–93](../sources/SOURCES.md#product-decomposition-and-tensor-splitting-of-finite-etale-algebras-53116)

#### Remarks

**Failure after deleting separability: dual numbers and purely inseparable field extensions.** Finite dimension and commutativity over $F$ can fail étaleness in two distinct ways—already over $F$ by nilpotents, or only after base change by inseparability:

1. *Non-reduced Artinian algebra (dual numbers).* Let $A_{\mathrm{dual}}=F[\varepsilon]/(\varepsilon^2)$ ($\dim_F A_{\mathrm{dual}}=2$). Its sole prime and maximal ideal is $(\varepsilon)$, with separable residue field $A_{\mathrm{dual}}/(\varepsilon)\cong F$, yet $\operatorname{nilradical}(A_{\mathrm{dual}})=(\varepsilon)\ne\{0\}$: in Lemma 1(2), $\Phi_{A_{\mathrm{dual}}}:A_{\mathrm{dual}}\to F$ is surjective with nonzero kernel $(\varepsilon)$. For any $a+b\varepsilon\in A_{\mathrm{dual}}$, $(a+b\varepsilon)^2=a^2+2ab\varepsilon=a+b\varepsilon$ requires $a^2=a$ (so $a\in\{0,1\}$) and $(2a-1)b=0$; since $2a-1=\pm 1\in F^\times$ in every characteristic (including $\operatorname{char}F=2$, where $-1=1$), $b=0$. Thus $A_{\mathrm{dual}}$ has only the trivial idempotents $0,1$, and for every extension $L/F$ the base change $L\otimes_F A_{\mathrm{dual}}\cong L[\varepsilon]/(\varepsilon^2)$ remains non-reduced and therefore cannot be isomorphic to any product of fields. Infinitesimal lifting fails on $B=A_{\mathrm{dual}}$, $J=(\varepsilon)$ ($J^2=0$): both $\varepsilon\mapsto 0$ and $\varepsilon\mapsto\varepsilon$ lift $A_{\mathrm{dual}}\twoheadrightarrow A_{\mathrm{dual}}/(\varepsilon)$, violating formal unramifiedness.
2. *Reduced field extension that acquires nilpotents after base change (purely inseparable cubic).* Let $F=\mathbb F_3(t)$ and $E_{\mathrm{insep}}=F[X]/(X^3-t)=F(a)$ with $a^3=t$ ($[E_{\mathrm{insep}}:F]=3$). Because $X^3-t$ is Eisenstein at the prime $(t)$ of $\mathbb F_3[t]$ (equivalently, for $(c_0,c_1,c_2)\ne(0,0,0)$ in $F^3$, $(c_0+c_1a+c_2a^2)^3=c_0^3+tc_1^3+t^2c_2^3\in F^\times$ has $t$-adic valuations in distinct residue classes $0,1,2\bmod 3$ and hence cannot vanish, giving the explicit inverse $(c_0+c_1a+c_2a^2)^{-1}=(c_0+c_1a+c_2a^2)^2/(c_0^3+tc_1^3+t^2c_2^3)$), $E_{\mathrm{insep}}$ is itself a **field**—hence reduced, Artinian, and trivially a $1$-factor product $\prod_{\mathfrak m\in\{(0)\}}E_{\mathrm{insep}}/\mathfrak m$ failing only the separability clause of Theorem 3! Upon base-changing to $K=E_{\mathrm{insep}}$, however, $Y^3-t=Y^3-a^3=(Y-a)^3$ in $E_{\mathrm{insep}}[Y]$, so
   $$
   E_{\mathrm{insep}}\otimes_F E_{\mathrm{insep}}\cong E_{\mathrm{insep}}[Y]/\bigl((Y-a)^3\bigr)=E_{\mathrm{insep}}[\delta]/(\delta^3),\qquad \delta=1\otimes a-a\otimes 1\ne 0,\quad \delta^3=0.
   $$
   Every $z=c_0+c_1\delta+c_2\delta^2\in E_{\mathrm{insep}}[\delta]/(\delta^3)$ satisfies $z^3=c_0^3$, so $z^2=z$ implies $z=z^3=c_0^3\in E_{\mathrm{insep}}$, forcing $c_1=c_2=0$ and $c_0\in\{0,1\}$. Thus $E_{\mathrm{insep}}\otimes_F E_{\mathrm{insep}}$ is a connected local Artinian ring with $2$-dimensional nilradical $E_{\mathrm{insep}}\delta\oplus E_{\mathrm{insep}}\delta^2\ne\{0\}$, $\operatorname{Hom}_{F\text{-alg}}(E_{\mathrm{insep}},L)$ has cardinality $1<3=\dim_L(L\otimes_F E_{\mathrm{insep}})$ for every field $L/E_{\mathrm{insep}}$ (since $\sigma(a)^3=t=a^3\implies(\sigma(a)-a)^3=0\implies\sigma(a)=a$), and square-zero lifting fails on $B=E_{\mathrm{insep}}[\delta]/(\delta^2)$ with $J=(\delta)$ ($J^2=0$), where $a\mapsto a$ and $a\mapsto a+\delta$ both satisfy $(a+\delta)^3=a^3+\delta^3=t$ in characteristic $3$ and lift $\mathrm{id}_{E_{\mathrm{insep}}}$.

**Hypotheses and outcomes across commutative $F$-algebras ($\dim_F A<\infty$).** The four structural regimes partition all finite-dimensional commutative $F$-algebras into pairwise disjoint cases:

| Regime on $A/F$ ($\dim_F A<\infty$) | Nilradical of $A$ | Residue fields $A/\mathfrak m$ | Base change $L\otimes_F A$ over splitting/algebraic closure $L/F$ |
|---|---|---|---|
| Zero algebra $A=\{0\}$ ($\dim_F A=0$) | $\{0\}$ | Empty family ($\operatorname{MaxSpec}(A)=\emptyset$) | $L\otimes_F\{0\}=\{0\}\simeq\prod_{\emptyset}L$ ($0$ embeddings, étale) |
| Nontrivial étale $F$-algebra ($\dim_F A\ge 1$) | $\{0\}$ | Nonempty finite family, all separable over $F$ | Splits as $\prod_{\sigma\in\operatorname{Hom}_{F\text{-alg}}(A,L)}L$ with $\lvert\Sigma\rvert=\dim_F A\ge 1$ |
| Reduced non-étale $F$-algebra (e.g. $E_{\mathrm{insep}}$) | $\{0\}$ | Nonempty finite family, at least one inseparable over $F$ | Acquires nonzero nilradical ($\lvert\operatorname{Hom}_{F\text{-alg}}(A,L)\rvert<\dim_F A$) |
| Non-reduced $F$-algebra (e.g. $F[\varepsilon]/(\varepsilon^2)$) | $\ne\{0\}$ | Nonempty finite family ($\operatorname{MaxSpec}(A)\ne\emptyset$ since $1\ne 0$); $\Phi_A$ has nonzero kernel $\operatorname{nilradical}(A)$ | Remains non-reduced under every field extension $L/F$ |

**Downstream archive consumers: `ExistsCyclicGaloisTensorAlgEquivPi` and `HasseEt` [Lean, read].** Theorem 4(3), with the dimension identity recorded in the exposition, follows `UpperTheory.exists_cyclic_galois_tensor_algEquiv_pi` (`ExistsCyclicGaloisTensorAlgEquivPi.lean:67–93`), which calls `Algebra.FormallyEtale.iff_exists_algEquiv_prod` and supplies the algebraic decomposition to `UpperTheory.ConvolutionTheory.D.hasseEt` (`HasseEt.lean:93–129`):

1. Inside `ExistsCyclicGaloisTensorAlgEquivPi.lean`, `Normal.exists_isSplittingField F E` (`:70`), `FormallyEtale.of_isSeparable F E` (`:71`), base-change inference `FormallyEtale K (K ⊗[F] E)` (`:72`), and `(Algebra.FormallyEtale.iff_exists_algEquiv_prod K (K ⊗[F] E)).1 inferInstance` (`:73–74`) produce the coordinate fields `Ai i`. Lines 75–80 discharge `Nonempty I` from `Nontrivial (K ⊗[F] E)` and select `i0`. Lines 81–85 build `fi i` and call `splitting` (`:19–39`) to establish `IsSplittingField K (Ai i) (p.map (algebraMap F K))` for all `i`. Lines 86–88 make the **two real calls to `IsSplittingField.algEquiv`** ([the mutual-embedding manuscript (§5.3.1.15)](../sources/SOURCES.md#chapter-5-unpublished-algebra-and-finite-place-supplies)) on the same polynomial `p.map (algebraMap F K)`, routing `Ai i ≃ₐ[K] (p.map _).SplittingField ≃ₐ[K] Ai i0` without requiring choice-free lifts between `Ai i` and `Ai i0` to be mutual inverses. Lines 89–93 assemble `FiniteDimensional`, `IsGalois`, `cyclic (fi i0) (hfi i0)` (`:41–66`), and `e.trans (AlgEquiv.piCongrRight eqv)`.
2. The finite-place transport is recorded in the [completion manuscript (§5.3.1.17)](../sources/SOURCES.md#chapter-5-unpublished-algebra-and-finite-place-supplies). The [real-place transport](#53118-the-same-tensor-norm-witness-at-a-real-place) and the [cyclic field norm theorem](#53119-from-prime-degree-norms-to-the-cyclic-hasse-norm-principle) are described below. In `HasseEt.lean`, `field_case` (`:69–89`) invokes `exists_cyclic_galois_tensor_algEquiv_pi F E K` at line 76 for a residue number field $K=A/\mathfrak m$. At each matched finite or real place, `local_step` first uses `transfer` to carry the supplied witness into $T\otimes_F E$ for the target field $T$. The scalar extension of $e:K\otimes_F E\simeq_K(I\to L)$ then gives the product coordinates for `norm_down` (`:21–32`), which multiplies the coordinates and uses `norm_pi'` (`:11–19`). The resulting witnesses feed the field-level cyclic Hasse norm theorem `hasseNormPrinciple_of_isCyclic K L` (`:78`), and lift a global norm witness $y\in L$ back to $K\otimes_F E$ via `norm_up` (`:34–48`, placing $y$ in the single selected coordinate $i_0\in I$ via `Pi.mulSingle i0 y` and $1$ elsewhere!). Then `hasseEt` itself (`:93–129`) applies Lemma 1 (`IsArtinianRing.of_finite F A` at `:97` and `(IsArtinianRing.equivPi A).symm` / `.injective` at `:109–118`) a second time to glue the fiberwise norm witnesses $y_{\mathfrak m}\in(A/\mathfrak m)\otimes_F E$ across all $\mathfrak m\in\operatorname{MaxSpec}(A)$ into a global norm witness in $A\otimes_F E$. [A2, HasseEt.lean:11–129](../sources/SOURCES.md#product-decomposition-and-tensor-splitting-of-finite-etale-algebras-53116)

**Sources and reading scope.** Milne defines étaleness by diagonalizability after a field extension, proves the equivalence with geometric reducedness and finite products of separable field extensions, and gives the coordinate splitting $\Omega\otimes_F A\xrightarrow{\sim}\Omega^{\mathcal F(A)}$. The Stacks Project proves finiteness of maximal ideals and product decomposition for Artinian rings in Tags `00J7` (Lemma 10.53.3) and `00JA` (Lemma 10.53.5), and the equivalence between étale $k$-algebras and finite products of finite separable extensions in Tag `00U3` (Lemma 10.143.4); Mathlib credits Iversen (*Generic Local Structure of the Morphisms in Commutative Algebra*, Springer LNM 310, 1973, Corollary II.5.3 and Proposition I.2.8) for the square-zero Taylor lift and free-module finiteness. [Milne, *Fields and Galois Theory*, v5.10, pp. 105–110](https://www.jmilne.org/math/CourseNotes/FT.pdf#page=105) All `[Lean, read]` claims here record local source-body reading against the pinned archive and Mathlib commit; neither source reading nor `mdbook build` constitutes Lean kernel replay or full dependency-closure verification. [Source ledger](../sources/SOURCES.md#product-decomposition-and-tensor-splitting-of-finite-etale-algebras-53116)

### 5.3.1.18 The same tensor norm witness at a real place

**Motivation.** A norm from $\mathbb C$ to $\mathbb R$ is positive on units. A norm from $\mathbb R\times\mathbb R$ can have either sign. In Hermitian descent the difference matters at a particular real embedding of a particular residue field of the coefficient algebra. The proof has already been given a norm witness over a completion of the base field. It finds the completion that matches the prescribed real structure and sends that very witness through the tensor maps.

**Two examples.** Fix the usual embedding of $\mathbb Q$ in $\mathbb R$. Its completion is $\mathbb R$, since the rationals are dense. For either $E=\mathbb Q(i)$ or $E=\mathbb Q(\sqrt5)$ let $u=1\otimes\theta$, with $\theta=i$ or $\theta=\sqrt5$ respectively. The rational basis $(1,\theta)$ gives the real basis $(1,u)$ of $\mathbb R\otimes_{\mathbb Q}E$. Write $d=\theta^2$ and $z=b+cu$. Both $z\cdot1=1\cdot z=b+cu$ and $z\cdot u=u\cdot z=dc+bu$ hold. Thus left and right multiplication, with images recorded in columns, both have matrix
$$M_d(b,c)=\begin{pmatrix} b&dc\\c&b\end{pmatrix},
\qquad \det M_d(b,c)=b^2-dc^2.$$

For $\mathbb Q(i)$, evaluation $u\mapsto i$ gives $\mathbb R[X]/(X^2+1)\simeq\mathbb C$. Its inverse sends $b+ci$ to $b+cu$, so the basis becomes $(1,i)$ and the matrix is $\begin{pmatrix}b&-c\\c&b\end{pmatrix}$. The determinant $b^2+c^2$ equals $(b+ci)(b-ci)$. Every $a>0$ has witness $\sqrt a+0u$. For example $1+2u$ represents $5$ and has inverse $(1-2u)/5$. Every $a<0$ is impossible because a sum of two real squares is nonnegative.

For $\mathbb Q(\sqrt5)$ put $t=\sqrt5>0$. The distinct roots $t,-t$ give the evaluation isomorphism
$$b+cu\longmapsto(b+ct,b-ct),\qquad
(p,q)\longmapsto (p+q)/2+((p-q)/(2t))u.$$
In the product basis $(1,0),(0,1)$ both multiplication matrices are diagonal with entries $b+ct,b-ct$. The change of coordinates from $(1,u)$ is $P=\begin{pmatrix}1&t\\1&-t\end{pmatrix}$ with determinant $-2t$. Direct multiplication gives $PM_5(b,c)=\operatorname{diag}(b+ct,b-ct)P$. The two determinants are $b^2-5c^2=(b+ct)(b-ct)$. Each nonzero $a$ has the product witness $(a,1)$, whose preimage is $(a+1)/2+((a-1)/(2t))u$. In particular $2$ has norm $4$ and $u$ has norm $-5$ with inverse $u/5$. These two witnesses already come from $E$, as does the witness for $5$ in the first example.

**Definitions.** In `HasseEt`, $E/F$ is a cyclic Galois extension of number fields and $A$ is a finite reduced commutative $F$-algebra. Since $F$ has characteristic zero, the finite reduced algebra is a product of finite separable field extensions and hence finite étale. The input is a unit $x\in A^\times$ and a tensor norm witness at each finite and each infinite place of $F$. For any commutative $F$-algebra $B$ write $N_B$ for the determinant over $B$ of multiplication on $B\otimes_F E$. At an infinite place $v$ with completion $F_v$ the hypothesis `hi v` supplies $z_v\in (F_v\otimes_F A)\otimes_F E$ with $N_{F_v\otimes_F A}(z_v)=1\otimes x$.

Fix a maximal ideal of $A$, let $K$ be its residue field and let $\pi:A\to K$ be the quotient. Put $a=\pi(x)\ne0$. For a specified $K$-algebra structure on $\mathbb R$, write $\tau:K\to\mathbb R$ for its structure map, $\iota:F\to K$ for the inclusion of scalars, and $\sigma=\tau\circ\iota$. The real tensor algebra in the transfer step is $D=\mathbb R\otimes_{F,\sigma}E$. The subsequent target is $D_0=\mathbb R\otimes_{K,\tau}L$, where the [cyclic tensor splitting of §5.3.1.16](#53116-product-decomposition-and-tensor-splitting-of-finite-étale-algebras) gives a cyclic extension $L/K$ and a $K$-algebra isomorphism $e:K\otimes_F E\simeq\prod_{i\in I}L$ with $I$ finite and nonempty. The norm in each real algebra here is the determinant over $\mathbb R$. [A2 declarations and inherited inputs](../sources/SOURCES.md#the-same-tensor-norm-witness-at-a-real-place-53118)

**Lemma (real determinant norm) [Expository].** Let $D$ be any finite étale commutative real algebra. In a decomposition $D\simeq\mathbb R^r\times\mathbb C^s$ its determinant norm sends $(u_i,b_j+ic_j)$ to
$$\prod_{i=1}^r u_i\prod_{j=1}^s(b_j^2+c_j^2).$$
An element is a unit exactly when that determinant is nonzero. The norm image on units is $\mathbb R^\times$ for $r>0$, $\mathbb R_{>0}$ for $r=0<s$, and $\{1\}$ for $r=s=0$ if the zero algebra is admitted.

**Proof.** The finite étale product decomposition gives finite field extensions of $\mathbb R$. Every irreducible real polynomial has degree one or two by the fundamental theorem of algebra and complex conjugation. If a finite field extension contains an element outside $\mathbb R$, completing the square in its irreducible quadratic exhibits a square root of $-1$ there. The extension is then algebraic over a copy of $\mathbb C$ and equals that copy. This proves the asserted form. In the product basis multiplication is block diagonal. A real coordinate gives a one-by-one block and each complex coordinate gives $M_{-1}(b_j,c_j)$. Their determinants give the formula. Nonzero determinant means that every coordinate is nonzero, which gives an inverse coordinatewise. If $r>0$, choose the first real coordinate to be the desired nonzero value and all others to be $1$. If $r=0<s$, positivity is forced and the square root of a desired positive value can be placed in the first complex coordinate. The empty product has determinant $1$. For nonzero $D$ the norm on all elements adds $0$ to the indicated unit image, since the zero element has zero multiplication determinant. In the application $\dim_{\mathbb R}D=[E:F]>0$. [Stacks, Lemma 10.143.4](https://stacks.math.columbia.edu/tag/00U3) · [Milne, *Algebraic Number Theory*, pp. 31, 135–136](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

**Lemma (the prescribed real scalar square) [Lean, read].** For the composite $\sigma$ there is a real infinite place $v$ of $F$ with a map $\psi_v:F_v\to\mathbb R$ satisfying $\psi_v j_v=\tau\iota$, where $j_v:F\to F_v$ is the original scalar map.

**Proof.** Postcompose $\sigma$ with $\mathbb R\hookrightarrow\mathbb C$. The resulting complex embedding is fixed by conjugation, so the infinite place it defines is real. In Mathlib, `InfinitePlace.mk` takes the absolute value of the complex embedding. The chosen `embedding` of this place is the given complex embedding or its conjugate. The two agree here, by `embedding_mk_eq_of_isReal`. The real-valued embedding `embedding_of_isReal` includes into $\mathbb C$ as that chosen embedding. Injectivity of the inclusion gives equality with $\sigma$. This is the proof in `exists_isReal_embedding_eq_hom`.

Since $v(b)=|\sigma(b)|$, the real embedding is an isometry for the absolute value of $v$. On the underlying `WithAbs` field it is the composite with `WithAbs.equiv`. The extension sends the class of a Cauchy sequence $(b_n)$ to $\lim_n\sigma(b_n)$, which exists in $\mathbb R$. Isometry makes this independent of the sequence, and the laws of a ring map pass to limits of sums and products. In the pinned body `extensionEmbeddingOfIsReal` first unwraps the place completion with `Completion.equiv`, then applies `Isometry.extensionHom`. The latter uses the ring extension on the dense image. Its value on an original point is given by `extensionEmbeddingOfIsReal_coe`. For $b\in F$ this lemma is applied to `((WithAbs.equiv v.1).symm b)`. That point coerces to $j_v(b)$ and the equivalence cancels on the right. Rewriting the real embedding by its equality with $\sigma$ gives $\psi_v(j_v(b))=\tau(\iota(b))$. The extension is isometric. Its image contains the dense rational subfield of $\mathbb R$ and is closed by completeness, so $\psi_v$ identifies $F_v$ with $\mathbb R$ under this particular scalar square. [A2 real embedding proof and pinned Mathlib bodies](../sources/SOURCES.md#the-same-tensor-norm-witness-at-a-real-place-53118) · [Milne, Theorem 7.23 and Remark 7.24](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

**The same witness in the real consumer.** The square makes
$$\Phi:F_v\otimes_F A\longrightarrow\mathbb R,\qquad
c\otimes b\longmapsto\psi_v(c)\tau(\pi(b))$$
an $F$-algebra map for the structure $\sigma$ on $\mathbb R$. The $F$-scalar moves between $c$ and $b$ with the same factor $\sigma$ on either side. The formula is multiplicative and sends $1$ to $1$. Use the tensor map with identity on $E$. By the inherited determinant base-change identity,
$$z_{\mathbb R}=(\Phi\otimes\operatorname{id}_E)(z_v),
\qquad N_{D/\mathbb R}(z_{\mathbb R})=\Phi(1\otimes x)=\tau(a).$$
The element $z_{\mathbb R}$ is a unit by the lemma. If its algebra has only complex factors, then $\tau(a)>0$. A real factor permits either sign at this place. Equivalently, the obstruction disappears exactly when $\sigma$ extends to a real embedding of $E$, since an $\mathbb R$-algebra map $D	o\mathbb R$ must project onto a real factor and restricts to such an embedding. This sign test describes solvability over the real scalar algebra. The actual proof uses the image of $z_v$.

Continuing through $e$ gives $D\simeq\prod_{i\in I}D_0$. Write $(z_i)_{i\in I}$ for the image of $z_{\mathbb R}$. In `norm_down` the returned witness is $y_\tau=\prod_{i\in I}z_i\in D_0$. Each $z_i$ is a unit and block determinants and multiplicativity give $N_{D_0/\mathbb R}(y_\tau)=\prod_i N_{D_0/\mathbb R}(z_i)=\tau(a)$. Since $I$ is nonempty, $D$ has a real factor exactly when $D_0$ does. The operation on a witness uses all of its coordinates. Inserting a witness in a single coordinate with the others set to $1$ gives the reverse inclusion of norm images.

| Site in `HasseEt.lean` | What the real branch supplies |
|---|---|
| 78, 81 | For every `a : Algebra K ℝ` in `LocNorm`, `letI := a` installs the prescribed $\tau$. The fixed field element is $\pi(x)$. |
| 82–83 | Apply `exists_isReal_embedding_eq_hom` to `((algebraMap K ℝ).comp (algebraMap F K))`. Obtain $v$, its realness, and equality of the chosen real embedding with $\sigma$. |
| 84–88 | Pass `hi v`, $\psi_v$, and the proof of $\psi_v j_v=\tau\iota$ to `local_step`. The proof uses the wrapped original point and rewrites by `hσ`. |
| 64–67, 53–56 | Install the composite $F$-algebra structure and scalar tower. The square provides `commutes'`. Use `productMap` for $\Phi$ and map the element unpacked from `hi v` with identity on $E$. |
| 21–32 | Take the product of the projected witnesses in $D_0$. Its determinant is $\tau(\pi(x))$, the right-hand side of this instance of `TNorm K L ℝ`. |
| 78, 98–105 | The named cyclic principle takes $\pi(x)\ne0$ and both complete local families. The residue-field call obtains nonzeroness by mapping the original unit. An inherited global norm witness is inserted by `norm_up` and the residue witnesses are then assembled. |

Here is the transport in the two examples with a coefficient algebra and a residue map. Take $F=\mathbb Q$, $A=\mathbb Q\times E$, $K=\mathbb Q$, and let $\pi$ project to the first factor. For each of the rational values $a=5$ in the imaginary example and $a=4,-5$ in the real example, put $x=(a,1)$. The element with components $(g,1\otimes1)$ in $(\mathbb Q\otimes_{\mathbb Q}E)\times(E\otimes_{\mathbb Q}E)$, where $g=1+2i,2,\sqrt5$ respectively, has norm $x$. This follows from the displayed matrices in the first coordinate and the identity matrix in the second. Its image under scalar extension gives the input at every finite and infinite place, by the inherited norm identity. At the real place, $\Phi$ selects the first coefficient coordinate. It sends the source witness to exactly $1+2u$, $2$, or $u$, respectively. Here $L=E$ and $I$ is a singleton, so `norm_down` returns that same element.

A further coefficient algebra illustrates the real quantifier. For $A=\mathbb Q(i)\times\mathbb Q$, $E=\mathbb Q(\sqrt2)$ and $x=(6i,-1)$, the residue $\mathbb Q(i)$ has no real algebra structure, since the image of $i$ would square to $-1$. For the residue $\mathbb Q$, the source witness from the global tensor with coefficients $(1+i,1)$ and $(1-i,1)$ maps to $1+u$, $u^2=2$. The real evaluations are $1+\sqrt2$ and $1-\sqrt2$, with product $-1=\tau(\pi(x))$. The same $x$ and the same source witness thus give the signed value at the only real residue structure.

A two-coordinate instance makes the product step visible. Use $F=\mathbb Q$, $E=K=\mathbb Q(t)$ with $t^2=5$, and take $A=K$, $\pi=\operatorname{id}$. For the structure $\tau(t)=\sqrt5$, the splitting $e$ sends $1\otimes t$ to $(t,-t)$, with $L=K$. Take the original tensor $z=(2+t)\otimes1+1\otimes t$, whose two coordinates are $(2+2t,2)$. Its norm is $x=4+4t$, a unit, so its scalar images give the entire local family. The image of the chosen real witness has coordinates $(2+2\sqrt5,2)$ and their product is $\tau(x)$. More generally, in this same algebra a source $\lambda\otimes1+\mu\otimes t$ yields the two coordinates $\tau(\lambda)\pm\sqrt5\,\tau(\mu)$ and `norm_down` multiplies them.

**The original coefficient algebra.** At a fixed real place $v$ the original ring-valued input also has a componentwise sign criterion. Set $B=F_v\otimes_F A$ and identify $F_v$ with $\mathbb R$ by $\psi_v$. From the inherited étale product decomposition, each factor of $B$ is real or complex. Real factors correspond to the maps $\tau$ from the residue fields extending the embedding $\sigma$ of $F$, by the universal property and the idempotent argument. The norm on $B\otimes_F E$ has as coordinates the norms after projection to each respective factor, by the inherited norm identity. A complex factor of $B$ imposes no condition on its nonzero target, because tensoring the finite separable extension $E/F$ with that complex factor yields a product of $[E:F]$ copies of $\mathbb C$ and the coordinate product is surjective on units. At a real factor the corresponding $\tau(a)$ must be positive precisely in the purely complex case of the real determinant lemma. Prescribing the resulting witnesses in all factors gives an element of $B\otimes_F E$ by the inherited finite-product tensor isomorphism. This equivalence concerns existence at this particular real place. The transport above follows the input witness already chosen there. An empty $B$ has its unique unit as the target and its unique element as witness.

**Why the chosen embedding and the unit matter.** Let $F=\mathbb Q(t)$ with $t=\sqrt5$, $E=F(\theta)$ with $\theta^2=t$, and $A=K=F$ with the identity quotient. The element $t$ is nonsquare in $F$ because its negative real embedding sends it to $-\sqrt5$. Thus $E/F$ is cyclic quadratic. Take the original unit $x=-t$ and global witness $\theta$, whose norm is $-t$. Its scalar images give all local inputs. For the prescribed embedding $\sigma_+$ with $t\mapsto\sqrt5$, the real tensor algebra splits. The transported witness has evaluations $\sqrt{\sqrt5},-\sqrt{\sqrt5}$, with product $-\sqrt5$. The other embedding $\sigma_-$ sends $t$ to $-\sqrt5$. Over that real place the algebra is complex, and the same global witness has local norm $+\sqrt5$. No unital ring map $F_{v_-}\to\mathbb R$ can make the required square for $\sigma_+$. The image of $t$ in $F_{v_-}$ is the negative of a nonzero square, and a unital map from a field preserves squares and their nonzeroness. It therefore cannot send that image to $+\sqrt5$. This counterexample keeps the original element and all local hypotheses, and changes the selected place only.

For $E=\mathbb Q(i)$, the scalar $a=0$ has witness $0$ but has no unit witness and fails the strict positivity test. The ring-valued local equation and its transport still make sense. At the coefficient-algebra level, $x=(5,0)$ in $A=\mathbb Q\times\mathbb Q$ is nonzero. The tensor with components $(1+2i,0)$ has norm $x$ and supplies all its local witnesses by scalar extension. In the second residue field the value is zero and every local norm witness for that value is a nonunit. This exhibits why a nonzero element of $A$ cannot replace a unit in the proof of the residue-field hypothesis $\pi(x)\ne0$.

The direct caller `nmHasse` makes the coefficient algebra concrete. It takes the algebra obtained by adjoining a root of the characteristic polynomial of an invertible matrix $\gamma$. Separability makes this algebra reduced. The nonzero constant coefficient makes the distinguished root a unit. At lines 34–36 the local `nmAlg` implications supply the two hypotheses of `hasseEt`, and the global `nmAlg` implication consumes its result. Thus the real step concerns the image of that same distinguished root in each residue field. [A2, NmHasse.lean:9–36](../sources/SOURCES.md#the-same-tensor-norm-witness-at-a-real-place-53118)

**Reading scope.** The real embedding production proof, the indicated real completion declarations and the real branch are read locally at R3. The real norm-image lemma and hand calculations are expository proofs of classical facts. The finite-place transport, general determinant base change, étale decomposition and cyclic tensor splitting retain their existing proofs and scope. The global theorem `GlobalTheory.T.hasseNormPrinciple_of_isCyclic` is a named [Lean] input here. Local source reading, kernel replay, declaration reachability from `Main`, and peer review are distinct checks. This section provides the local source reading and the mathematical reconstruction of the real input. [Source ledger](../sources/SOURCES.md#the-same-tensor-norm-witness-at-a-real-place-53118)

### 5.3.1.19 From prime-degree norms to the cyclic Hasse norm principle

**Motivation.** The finite and real arguments supply local witnesses for one element of a residue field. Hermitian descent needs a field element whose global norm is that same value. To see how the cyclic Hasse norm theorem supplies it, put an intermediate field $M$ between $F$ and $E$. Norm transitivity can combine two global norm equations once their targets match. The work is to produce those equations from the local data, using the cyclic action to correct the target for the lower extension.

**Two towers [Expository].** Start with $\mathbb Q\subset\mathbb Q(\sqrt5)\subset\mathbb Q(\zeta_5)$, with top degree $2$ and bottom degree $2$. A nonzero norm to $\mathbb R$ from the full extension is positive because the real tensor algebra has two complex factors. In $\mathbb Q\subset\mathbb Q(\sqrt{-7})\subset\mathbb Q(\zeta_7)$ the top degree is $3$ and the bottom degree is $2$. The intermediate field has no real embedding, although the original real input over $\mathbb Q$ still imposes positivity. We will calculate witnesses in both towers after deriving the norm equations they must satisfy.

#### The field-level statement

For a finite field extension $E/F$ and a field $K$ with a specified map $j:F\to K$, write $N_{E/F}$ for the field norm and $N_{K\otimes_F E/K}$ for the determinant of multiplication over $K$. The tensor algebra may have several factors. The original definitions in A2 are
$$
\begin{aligned}
\operatorname{TNorm}(F,E,K,x)&\iff
  \exists z\in K\otimes_F E,\quad N_{K\otimes_F E/K}(z)=j(x),\\
\operatorname{LocNorm}(F,E,x)&\iff
  \bigl(\forall v\text{ finite in }F,\ \operatorname{TNorm}(F,E,F_v,x)\bigr)\\
&\qquad{}\land
  \bigl(\forall (j:F\hookrightarrow\mathbb R),\ \operatorname{TNorm}(F,E,\mathbb R_j,x)\bigr),\\
\operatorname{NP}(F,E)&\iff
  \forall x\in F,\quad x\ne 0\ \Longrightarrow\
    \bigl(\operatorname{LocNorm}(F,E,x)\Longrightarrow
             \exists y\in E,\ N_{E/F}(y)=x\bigr).
\end{aligned}
$$
The finite index is the height-one spectrum of $\mathcal O_F$. In the real family each Lean parameter $a:\mathrm{Algebra}\ F\ \mathbb R$ installs its own scalar map. The number $x$ is fixed before the two local families are supplied. Each field or scalar structure has its own existential witness. The determinant equation for $x\ne0$ makes that witness a unit, since multiplication by it is invertible and the inverse image of $1$ is its inverse. At a complex completion the finite separable tensor algebra is a product of copies of $\mathbb C$ and any nonzero scalar is a coordinate product. Thus the original $\operatorname{LocNorm}$ has all the content of the usual all-place condition. For a totally imaginary $F$ the real family is empty. [A2 definitions](../sources/SOURCES.md#the-cyclic-hasse-norm-assembly-53119) · [Milne, *Algebraic Number Theory*, Propositions 8.1–8.2 and Corollary 8.4](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

**Prime-degree input [Lean].** The quadratic supply gives $\operatorname{NP}(F,E)$ for number fields with $[E:F]=2$. Its interface needs no Galois argument, since a quadratic extension of number fields is Galois. The odd-prime supply requires number fields, a Galois extension, a prime $p\ne2$ and $[E:F]=p$. The body of `np_of_finrank_prime` tests $p=2$ and dispatches to these two inputs. The quadratic proof remains a named input. [§5.3.1.21](#53121-descending-an-odd-prime-degree-norm-after-adjoining-roots-of-unity) proves the odd-prime descent from the case with the primitive root in the base. [A2, `HasseNormPrincipleOfIsCyclic.lean:18–23` and the two prime-degree interfaces](../sources/SOURCES.md#the-cyclic-hasse-norm-assembly-53119)

#### The cyclic tower lemma [Lean, read]

Let $F\subseteq M\subseteq E$ be a tower of number fields with $E/F$ finite Galois and cyclic. Put $d=[M:F]$ and $r=[E:M]$. Given $\operatorname{NP}(M,E)$ and $\operatorname{NP}(F,M)$, we prove $\operatorname{NP}(F,E)$. The proof uses two tensor lemmas at their named interfaces.

The first, `TNorm.of_tower`, takes a compatible tower $F\subseteq M\to K$ of fields and sends a witness over $K\otimes_F E$ for $x$ to one over $K\otimes_M E$ for the image of $x$ in $M$. In the cyclic case, let $\tau$ generate $\operatorname{Gal}(E/F)$ and let $q:K\otimes_F E\to K\otimes_M E$ impose the $M$-balancing relation. For a witness $z$ the construction is $q(\prod_{i=0}^{d-1}\tau^i(z))$, with $\tau$ acting on the right tensor factor. Its upper norm is the product over $\langle\tau^d\rangle$ of these $d$ factors. They exhaust the full group as $\tau^{dj+i}$, so the norm is the same scalar. The archive uses coset representatives in the full Galois statement.

The second, `tnorm_of_tnorm_pow`, applies to any field $K$ with an $F$-algebra structure, with no choice of $M$-structure on $K$. For $b\in F^\times$, it gives
$$
\operatorname{TNorm}(F,E,K,b^r)\ \Longrightarrow\
\operatorname{TNorm}(F,M,K,b).
$$
Its hypotheses are a compatible finite Galois cyclic tower over a field $F$ of characteristic zero. Its proof is a named input here. The inference concerns a change of norm algebra and uses cyclicity. The lower witness cannot be obtained just by taking an $r$th root of a determinant. [A2, `OfIntermediateFieldTower.lean:32–35` and `IsNormFromBaseChangeOfPowFinrankCyclic.lean:114`](../sources/SOURCES.md#the-cyclic-hasse-norm-assembly-53119)

**Proof of the tower lemma.** Fix $x\in F^\times$ with both local families.

1. For a finite place $w$ of $M$, contract it to the finite place $v$ of $F$. The compatible map $F_v\to M_w$ takes the original witness to $M_w\otimes_F E$ by tensoring with the identity. Determinant base change gives the image of $x$ as its norm. Apply the first tensor lemma with $K=M_w$. For any real embedding $a:M\to\mathbb R$, use the original real witness indexed by $a|_F$ and the same tensor lemma for $\mathbb R$ with that compatible tower. This produces $\operatorname{LocNorm}(M,E,x_M)$ for $x_M$ the image of $x$ in $M$. Since the scalar map is injective, $x_M\ne0$. The upper input gives $e_0\in E^\times$ with $N_{E/M}(e_0)=x_M$. [A2, `HasseNormPrincipleOfCyclicTower.lean:163–183`](../sources/SOURCES.md#the-cyclic-hasse-norm-assembly-53119)

2. Write $G=\langle\tau\rangle$ of order $dr$. The subgroup fixing $M$ has order $r$ and is generated by $g=\tau^d$. We identify scalars with their images when calculating inside $E$. Since $G$ is abelian, $\tau$ commutes with the conjugates in $N_{E/M}$. Therefore $N_{E/M}(\tau(e_0)/e_0)=1$, because $\tau$ fixes $x$. Multiplicative Hilbert 90 for $E/M$ gives $u\in E^\times$ with
   $$\frac{\tau(e_0)}{e_0}=\frac{u}{g(u)}.$$
   Set $P=\prod_{i=0}^{d-1}\tau^i(u)$. Shifting the factors gives $\tau(P)/P=g(u)/u$, so $\tau(e_0P)=e_0P$. Since $\tau$ generates $G$, $e_0P$ is the image of a unique $b\in F^\times$. Furthermore,
   $$
   N_{E/M}(P)=\prod_{j=0}^{r-1}\prod_{i=0}^{d-1}\tau^{dj+i}(u)
             =N_{E/F}(u).
   $$
   Here the last scalar is embedded in $M$. Taking $N_{E/M}$ of $e_0P=b$ gives $b^r=xN_{E/F}(u)$ in $F$ by scalar injectivity. With $c=u^{-1}$ we obtain $x=b^rN_{E/F}(c)$. The production proof lifts $g$ to an $M$-automorphism, proves the two product identities and returns the inverse of the Hilbert 90 unit. [A2, `HasseNormPrincipleOfCyclicTower.lean:14–155`](../sources/SOURCES.md#the-cyclic-hasse-norm-assembly-53119) · [Milne, *Fields and Galois Theory*, Corollary 5.25](https://www.jmilne.org/math/CourseNotes/FT.pdf)

3. Return to each original scalar field $K=F_v$ or $K=\mathbb R_a$ of $F$. Let $z$ be the originally supplied witness for $x$. The tensor $1\otimes c$ has norm $j(N_{E/F}(c))\ne0$. The witness $z(1\otimes c^{-1})$ therefore has norm $j(b)^r$. The second tensor lemma produces a witness for $b$ in $K\otimes_F M$. This proves $\operatorname{LocNorm}(F,M,b)$ for the same $b$ at every place, so $\operatorname{NP}(F,M)$ yields $m\in M$ with $N_{M/F}(m)=b$. Finally the witness in $E$ is $mc$, where $m$ is mapped along $M\to E$. Scalar norms and norm transitivity give
   $$N_{E/F}(mc)=N_{M/F}(m^r)N_{E/F}(c)=b^rN_{E/F}(c)=x.$$
   This completes the implication for the original $x$. [A2, `HasseNormPrincipleOfCyclicTower.lean:184–198`](../sources/SOURCES.md#the-cyclic-hasse-norm-assembly-53119) · [Milne, *Fields and Galois Theory*, Proposition 5.48](https://www.jmilne.org/math/CourseNotes/FT.pdf)

#### Assembly in every finite cyclic degree [Lean, read]

**Theorem.** For a finite cyclic Galois extension $E/F$ of number fields, the two prime-degree inputs and the tower lemma give $\operatorname{NP}(F,E)$.

**Proof.** Use strong induction on $n=[E:F]$, with the claim ranging over every pair of number fields of degree $n$. Finiteness over $\mathbb Q$ gives finiteness over $F$, so $n>0$. In degree $1$ the scalar image of $x$ itself has norm $x^1=x$. If $n>1$, choose a prime divisor $p$ of $n$. Since $|G|=n$, a generator $\tau$ gives the order-$p$ subgroup $H=\langle\tau^{n/p}\rangle$. The archive obtains an element of order $p$ and takes the subgroup it generates. The subgroup is normal since $G$ is abelian. Its fixed field $M=E^H$ is a number field, with $[E:M]=|H|=p$. By the Galois correspondence $M/F$ is Galois and its group is a quotient of $G$ by restriction, hence cyclic. The tower formula is $n=[M:F]p$, and $[M:F]>0$ and $p>1$ give $[M:F]<n$. The prime-degree input applies upstairs to $E/M$, which is Galois, and the induction hypothesis applies downstairs to $M/F$. The tower lemma consumes the upper principle first and the lower one second. For prime $n$ this proof permits $M=F$, so the recursive use is the degree-one case. The wrapper `np_cyclic` instantiates the induction at the actual finrank. [A2, `HasseNormPrincipleOfIsCyclic.lean:12–68`](../sources/SOURCES.md#the-cyclic-hasse-norm-assembly-53119) · [Milne, *Fields and Galois Theory*, Theorem 3.17](https://www.jmilne.org/math/CourseNotes/FT.pdf)

#### The two towers worked out [Expository]

Use $E=\mathbb Q(\zeta_\ell)$ with $\ell=5$ or $7$ and put $a=1-\zeta_\ell$. The polynomial $\Phi_\ell(X)=1+X+\cdots+X^{\ell-1}$ is irreducible by Eisenstein after shifting $X$ by $1$. The Galois group acts by the nonzero exponents modulo $\ell$. In each example choose the indicated $H$ fixing $M$, write $h=N_{E/M}(a)$, and choose $y=ha\in E$. We have $N_{E/\mathbb Q}(a)=\Phi_\ell(1)=\ell$, $N_{M/\mathbb Q}(h)=\ell$ and $N_{E/\mathbb Q}(y)=\ell^{r+1}$. To supply *all* original places, take $z=1\otimes y$ in each original tensor. The multiplication matrix in the scalar extension of the rational basis has the original coefficients mapped to the completion, so each is an exact witness. For the choices of $e_0,u,b,c$ below, the corrected local witness is $z(1\otimes a^{-1})=1\otimes h$ in the full tensor. Since $h\in M$, its lower realization is $1\otimes h$ in $K\otimes_F M$, with norm $b$. Thus the examples exhibit the actual norm equations on both levels. [Milne, *Fields and Galois Theory*, Lemmas 1.42 and 5.9](https://www.jmilne.org/math/CourseNotes/FT.pdf)

**Degree four and the positive real target.** Let $\ell=5$, take $\tau:\zeta_5\mapsto\zeta_5^2$ and $H=\{1,\tau^2\}$. Put $t=\zeta_5+\zeta_5^{-1}$. The primitive roots sum to $-1$, so $t^2+t-1=0$ and $\tau(t)=-1-t$. Thus $M=\mathbb Q(t)=\mathbb Q(\sqrt5)$. Direct multiplication gives
$$
h=(1-\zeta_5)(1-\zeta_5^{-1})=2-t,\qquad
h'=\tau(h)=3+t,\qquad hh'=5.
$$
Here $r=d=2$ and $x=125$. The product of the two coset representatives applied to $y$ is $e_0=y\tau(y)=5a\tau(a)$. Its upper norm is $25hh'=125$. In the Hilbert 90 step we can take $u=a^{-1}$, since $\tau(e_0)/e_0=\tau^2(a)/a=u/\tau^2(u)$. It gives $b=5$, $c=a$. The lower witness is $m=h$, with norm $5$, and the final witness is $ha$. At the real place the two coordinates of $z$ are $h_j(1-\zeta_5^j)$ for $j=1,2$ in the two complex factors, where $h_1=h$ and $h_2=h'$ under the chosen complex embedding. Their squared absolute values are $h^3,(h')^3$, with product $125$. In each real structure of $M$ the upper tensor is complex and $e_0$ has squared absolute value $25hh'=125$. The lower real tensor has the witness $(h,h')$ with product $5$. In the original tensor a target of $-125$ has no real witness by the same block determinants.

For a finite calculation use $11$. The residue $3$ has order $5$ in $\mathbb F_{11}^\times$. Simple-root lifting for $X^5-1$ gives a primitive root $\lambda\in\mathbb Q_{11}$ reducing to $3$. The original coordinates, ordered by exponents $j=1,2,4,3$, are $(2-\lambda^j-\lambda^{-j})(1-\lambda^j)$. Galois products evaluated at $\lambda$ give the exact norm $125$. Modulo $11$ the paired $h$ values are $6,10,6,10$ and the $a$ values are $9,3,8,7$, giving witness coordinates $10,8,4,4$. Each upper tensor at a place of $M$ above $11$ groups indices $j,-j$ and the coordinates of $e_0$ are $5(1-\lambda^j)(1-\lambda^{2j})$. The product within either pair is $25hh'=125$. The lower coordinates are the two values of $h$, with product $5$. [Milne, *Algebraic Number Theory*, Proposition 7.31](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

**Degree six and an odd top step.** Let $\ell=7$, take $\tau:\zeta_7\mapsto\zeta_7^3$ and $H=\langle\tau^2\rangle$, acting by exponents $\{1,2,4\}$. Set $s=\zeta_7+\zeta_7^2+\zeta_7^4$ and $s'=\zeta_7^3+\zeta_7^5+\zeta_7^6$. The sum $s+s'=-1$. In the nine terms of $ss'$ the exponents modulo $7$ are $0$ three times and each nonzero exponent once, so $ss'=2$. The polynomial $X^2+X+2$ now gives $M=\mathbb Q(s)=\mathbb Q(\sqrt{-7})$. Multiplying the three factors of $h$ gives
$$
h=1-s+s'-1=s'-s,\qquad
h'=\tau(h)=-h,\qquad hh'=7.
$$
With $r=3,d=2$ we have $x=2401$. Again $e_0=y\tau(y)=7a\tau(a)$, with upper norm $7^3hh'=2401$. The identity $\tau(e_0)/e_0=\tau^2(a)/a$ gives the choice $u=a^{-1}$, hence $b=7$ and $c=a$. The lower witness $m=h$ has norm $7$. The real tensor of $E/\mathbb Q$ has three complex factors represented by exponents $1,2,4$. In each factor $|h|^2=7$, and the product of the three squared absolute values of $1-\zeta_7^j$ is $hh'=7$. Hence the local norm of the same $y$ is $7^3\cdot7$. The upper real family is empty since $M$ is imaginary. Downstairs the real tensor of $M/\mathbb Q$ is complex and $h$ has squared absolute value $7$.

For $29$, the residue $16$ has order $7$ and lifts to a primitive seventh root $\lambda$ by the same simple-root criterion. In exponent order $1,3,2,6,4,5$, evaluate $a$ at $\lambda^j$ and use $h$ defined by the three factors with exponents $j,2j,4j$. Modulo $29$ those $h$ values alternate $14,15$ and the $a$ values are $14,23,6,10,5,7$. Thus $z$ has residues $22,26,26,5,12,18$. The upper coordinates of $e_0$ are $7(1-\lambda^j)(1-\lambda^{3j})$. Within each of the two three-element orbits their product is $7^3hh'=2401$. The lower witness has the two evaluations of $h$, with product $7$. These are exact evaluations via the lifted root. The residues are a check on coordinates and do not supply the all-place quantifier. [Milne, *Algebraic Number Theory*, Proposition 7.31](https://www.jmilne.org/math/CourseNotes/ANT.pdf)

#### Where the cyclic hypothesis is used

In the splitting field $E=\mathbb Q(\sqrt[3]{2},\zeta_3)$ the group is $S_3$: the cubic is Eisenstein, its real root field has degree three, and adjoining the nonreal $\zeta_3$ adds degree two. Complex conjugation generates an order-two subgroup $H$ with fixed field $\mathbb Q(\sqrt[3]{2})$. Conjugating this transposition by a three-cycle produces a different transposition. The fixed field is consequently nonnormal over $\mathbb Q$, so the lower induction hypothesis requiring a Galois cyclic extension is unavailable even though its degree has decreased. Choosing the normal order-three subgroup instead gives a cyclic lower extension, but the whole group still has no cyclic generator for the tower lemma.

The power-norm interface can itself fail upon dropping cyclicity. Take $E=\mathbb Q(\sqrt2,\sqrt5)$, $M=\mathbb Q(\sqrt2)$, $K=\mathbb Q_3$, and $b=3$. The distinct quadratic subfields give the sign-change group $C_2\times C_2$, and $r=2$. A simple root of $X^2-10$ modulo $3$ lifts to a unit $v\in K$ with $v^2=10$. In $D=K(\sqrt2)$ the two possible images of $\sqrt5$ are $\pm v/\sqrt2$. Thus $K\otimes_\mathbb Q E\simeq D\times D$ and $(3,1)$ has determinant norm $9=b^2$. But $3$ is no norm from $D=K\otimes_\mathbb Q M$. For $\alpha+\beta\sqrt2\ne0$ divide both coefficients by $3^{\min(\operatorname{ord}_3\alpha,\operatorname{ord}_3\beta)}$. The resulting integral pair has at least one unit and its norm $\alpha_0^2-2\beta_0^2$ is nonzero modulo $3$. The original norm therefore has even valuation. This refutes the power-norm implication for one specified scalar field and value after deleting cyclicity. It gives no all-place claim about the Hasse norm principle for $E/\mathbb Q$.

#### Return to Hermitian descent

In `HasseEt` the input is a unit $x_A\in A^\times$ of a finite reduced commutative $F$-algebra. For a maximal ideal take $K=A/\mathfrak m$ and $x_K=\pi(x_A)\ne0$. By the [cyclic tensor splitting of §5.3.1.16](#53116-product-decomposition-and-tensor-splitting-of-finite-étale-algebras), we have $K\otimes_F E\simeq\prod_{i\in I}L$ into a finite nonempty family with a common cyclic Galois field $L/K$. The theorem just proved applies to $L/K$. In particular the end fields of the tower proof here are $K$ and $L$.

| Original call site | Types and witness |
|---|---|
| `HasseEt.lean:49–67,79–88` | For a target finite completion of $K$, or a prescribed real $K$-structure, write $T$ for the target field and $F'$ for the prescribed source completion of $F$. The square makes $\psi:F'\to T$ and $\rho:A\to K\to T$ compatible over $F$. The witness in $(F'\otimes_F A)\otimes_F E$ for $1\otimes x_A$ is sent by `transfer` to $T\otimes_F E$ with norm $\rho(x_A)$. The base of the determinant changes from the coefficient ring $F'\otimes_F A$ to the field $T$. |
| `HasseEt.lean:21–32,66–67,78` | The compatible tower $F\to K\to T$ gives $T\otimes_F E\simeq\prod_{i\in I}(T\otimes_K L)$. `norm_down` multiplies the transported coordinates in $T\otimes_K L$ to preserve the determinant value. The result is `TNorm K L T` for $x_K$. Both complete families are supplied to the cyclic theorem. |
| `HasseEt.lean:34–47,76–78,98–129` | The field witness in $L$ has norm $x_K$. Put it in one coordinate and $1$ elsewhere via `norm_up`, giving the witness in $K\otimes_F E$. Lift the basis coordinates of these witnesses simultaneously across all residue fields and use determinant base change and injectivity into their product to obtain a norm $x_A$ in $A\otimes_F E$. |
| `NmHasse.lean:9–36` | For invertible $\gamma$ with separable characteristic polynomial, $A=F[X]/(\operatorname{cp}(\gamma))$ is finite reduced and its root $x_A$ is a unit by the nonzero constant term. The local `nmAlg` equivalences send both families of characteristic-polynomial witnesses into the ring-valued norm equations. The reverse global implication consumes the resulting equation for that root and returns a matrix norm witness commuting with the scalar extension of $\gamma$. |

The finite-place transport fixes the contracted place, and §5.3.1.18 identifies the required real structure. The all-degree assembly now explains the field-level call there. The direct source calls have local R3 status for the tower and degree assembly. The quadratic proof and the upper tensor lemma remain named [Lean] inputs. [§5.3.1.21](#53121-descending-an-odd-prime-degree-norm-after-adjoining-roots-of-unity) treats the odd-prime branch. [§5.3.1.20](#53120-cancelling-a-power-in-a-local-tensor-norm) reads the lower tensor power cancellation. Kernel replay, a declaration-level path from `Main`, independent review of this exposition, and peer review are separate records. Hasse’s 1931 paper already proves the all-degree norm theorem by induction from prime degree. His intermediate field has prime degree **over the base**, and he corrects a lower norm preimage using norm-residue symbols and class field theory. Here the intermediate field has prime index **in the top field**. The calculation follows the archive’s upper-first argument with tensor norms. [Hasse, 1931, §1, pp. 64–68](https://gdz.sub.uni-goettingen.de/download/pdf/PPN252457811_1931/PPN252457811_1931.pdf#page=69) · [Source ledger](../sources/SOURCES.md#the-cyclic-hasse-norm-assembly-53119)

### 5.3.1.20 Cancelling a power in a local tensor norm

In §5.3.1.19 the cyclic tower correction gives $x=b^r N_{E/F}(c)$ with $r=[E:M]$. At an original place of $F$, dividing the supplied tensor witness by $1\otimes c$ leaves a witness of norm $b^r$. To use the lower Hasse norm input we need a witness of norm $b$ in the smaller tensor algebra. The construction changes the witness by a quotient of conjugates. This makes it invariant under the subgroup fixing $M$, so it comes from the smaller algebra.

#### Two forms of the tensor algebra

Use the tower $\mathbb Q\subset \mathbb Q(\zeta+\zeta^{-1})\subset \mathbb Q(\zeta)$ of §5.3.1.19, with $\zeta$ a primitive fifth root of unity and $\sigma(\zeta)=\zeta^2$. Both steps have degree two. At $11$, a fifth root of order five in $\mathbb Q_{11}$ gives four scalar coordinates. At the real place the four embeddings occur in two complex-conjugate pairs, so the large tensor algebra is $\mathbb C\times\mathbb C$ over $\mathbb R$. In both algebras a witness of norm $25$ will give one of norm $5$. The permutation of four coordinates and the combination of swapping and conjugating two complex coordinates are instances of the same action.

#### The tensor norm and the cancellation lemma

Let $F$ be a field of characteristic zero, let $F\to M\to E$ be a compatible tower of fields with $E/F$ finite Galois and cyclic, and let $j:F\to K$ give a field $K$ its $F$-algebra structure. Write
$$
A=K\otimes_F E,\qquad B=K\otimes_F M,\qquad
\iota=1\otimes(M\to E):B\longrightarrow A,
\qquad d=[M:F],\quad r=[E:M].
$$
The norm $N_{A/K}(y)$ is the determinant of $K$-linear multiplication by $y$. Likewise for $B$. Scalars in either tensor algebra enter as $k\otimes 1$. The tensor spaces are finite free of ranks $dr$ and $d$, by extending bases over $F$. All maps into $K$ in this construction come from $j$.

**Lemma (cancellation of the top degree) [Lean, read].** For each $b\in F^\times$ and each $y\in A$ with $N_{A/K}(y)=j(b)^r$, there is $z\in B$ with $N_{B/K}(z)=j(b)$. This gives the original implication $\operatorname{TNorm}(F,E,K,b^r)\Rightarrow\operatorname{TNorm}(F,M,K,b)$ of `CNorm.tnorm_of_tnorm_pow`. [A2, `IsNormFromBaseChangeOfPowFinrankCyclic.lean:114–188`](../sources/SOURCES.md#local-tensor-power-norm-cancellation-53120)

**The determinant as a product of conjugates.** For any finite Galois field extension $L/F$, let $C=K\otimes_F L$ and $J=\operatorname{Gal}(L/F)$. The action of $g\in J$ on $C$ is $1\otimes g$. In $C$ we have
$$
N_{C/K}(v)\otimes 1=\prod_{g\in J}(1\otimes g)(v).
$$
Here the matrix argument also works with any commutative $F$-algebra $K$. Choose an $F$-basis $(e_j)$ of $L$ of size $|J|$ and form the square matrix $Q=(g(e_j))_{g,j}$ over $L$. If a row relation holds on that basis, $F$-linearity extends it to all of $L$. The independence of distinct field embeddings forces its coefficients to vanish, so $\det Q\ne0$. Write $Q_C$ for the image of $Q$ under $e\mapsto1\otimes e$, and $D$ for the multiplication matrix of $v$ in the extended basis. Applying $1\otimes g$ to the multiplication equations yields
$$
\operatorname{diag}\bigl((1\otimes g)(v)\bigr)Q_C
   =Q_C(D\otimes1),
$$
where $D\otimes1$ means the entrywise scalar map. On taking determinants, $\det Q_C$ is a unit because it is the image of the nonzero field element $\det Q$. Cancelling that unit gives the formula even when $C$ has zero divisors. We will use this identity first for $L=E$ and finally for $L=M$. [A2, `AlgebraMapNormTensorEqProdConjugates.lean:11–69`](../sources/SOURCES.md#local-tensor-power-norm-cancellation-53120) · [Milne, *Fields and Galois Theory*, Corollaries 5.15–5.16 and Remark 5.47](https://www.jmilne.org/math/CourseNotes/FT.pdf)

**Hilbert 90 after scalar extension.** Suppose $\tau$ is an $F$-automorphism of $E$ of order $r$ and $U=1\otimes\tau$ on $A$. If $u\in A$ satisfies $\prod_{i=0}^{r-1}U^i(u)=1$, we claim that some $h\in A^\times$ satisfies $uU(h)=h$. Set $q_0=1$, $q_i=\prod_{j=0}^{i-1}U^j(u)$, and define the $K$-linear map
$$
\Theta(v)=\sum_{i=0}^{r-1} q_i U^i(v).
$$
We have $uU(q_i)=q_{i+1}$, $q_r=q_0=1$ and $U^r=1$ as an operator. Shifting the sum gives $uU(\Theta(v))=\Theta(v)$ for every $v$.

To get a *unit* in its image, work modulo each maximal ideal $\mathfrak m$ of $A$. The composite $E\to A\to A/\mathfrak m$ is a unital map of fields, hence injective. Composing it with $\tau^0,\ldots,\tau^{r-1}$ gives distinct embeddings into $A/\mathfrak m$. If $\Theta(A)\subseteq\mathfrak m$, then evaluating on $1\otimes e$ for every $e\in E$ gives a linear relation among these embeddings, with the coefficient of the identity embedding equal to $1$. The independence used here and for $Q$ follows by taking a nonzero relation of minimal support among distinct embeddings $f_i$. For two embeddings in its support, choose $a$ on which they differ. Subtract $f_1(a)$ times the relation at $e$ from the relation at $ae$. The $f_1$ coefficient is killed and a second coefficient survives, contradicting minimality. A one-term relation is impossible by evaluation at $1$. This calculation evaluates each term in the quotient and requires no action of $U$ on that quotient.

Consequently each $\Theta^{-1}(\mathfrak m)$ is a proper $K$-subspace. The finite-dimensional $K$-algebra $A$ is Artinian, so it has finitely many maximal ideals. The field $K$ is infinite by characteristic zero. A finite union of proper subspaces cannot exhaust a finite-dimensional vector space over an infinite field. Indeed, choose a nonzero linear form vanishing on each subspace and take their product. This nonzero polynomial has a nonzero value somewhere over an infinite field, by induction on the number of variables using the univariate root bound. Choose $v$ outside the union. Then $h=\Theta(v)$ avoids every maximal ideal and is a unit. This proves the claim including the product-algebra case. [A2, `Hilbert90BaseChange.lean:8–28,30–98`](../sources/SOURCES.md#local-tensor-power-norm-cancellation-53120) · [Hilbert, *Zahlbericht*, Satz 90](https://gdz.sub.uni-goettingen.de/download/pdf/PPN237821559/LOG_0023.pdf)

**Proof of cancellation.** Choose a generator $\sigma$ of $\operatorname{Gal}(E/F)$ and let $T=1\otimes\sigma$ on $A$. The tower law gives $|\sigma|=dr$. The subgroup fixing $M$ has order $r$ and equals $\langle\sigma^d\rangle$, the unique subgroup of that order. In particular $M/F$ is Galois, and $\bar\sigma=\sigma|_M$ generates its group of order $d$. Let $s=j(b)\otimes1\in A^\times$. The determinant formula gives $\prod_{i=0}^{dr-1}T^i(y)=s^r$. Set $U=T^d$ and
$$
P(v)=\prod_{j=0}^{d-1}T^j(v),\qquad u=P(y)s^{-1}.
$$
The identity $i=dk+j$, with $0\le k<r$ and $0\le j<d$, enumerates the full product exactly once. The scalar $s$ is fixed by $T$. It follows that
$$
\prod_{k=0}^{r-1}U^k(u)
 =\left(\prod_{i=0}^{dr-1}T^i(y)\right)s^{-r}=1.
$$
Apply the preceding Hilbert 90 construction with $\tau=\sigma^d$ to get a unit $h$ with $uU(h)=h$. Put $w=yT(h)h^{-1}$. The product telescopes to
$$
P(w)=P(y)\frac{U(h)}{h}=s.
$$
For every $v$, shifting the $d$ factors gives $P(Tv)v=P(v)U(v)$. Here $P(Tw)=T(P(w))=s$, so $sw=sU(w)$. Cancelling the scalar unit $s$ gives $U(w)=w$. Every element of $\operatorname{Gal}(E/M)$ is a power of $\sigma^d$. Thus $w$ is fixed by its entire action on $A$. This is the calculation in `LocStep.core`, followed by the subgroup check at the call site. [A2, `IsNormFromBaseChangeOfPowFinrankCyclic.lean:11–107,115–160`](../sources/SOURCES.md#local-tensor-power-norm-cancellation-53120)

**Descending the fixed tensor.** Over the original base $F$, apply the $F$-linear trace map $\operatorname{Tr}_{E/M}:E\to M$ on the right tensor factor. For a pure tensor $k\otimes e$, the image of $k\otimes\operatorname{Tr}_{E/M}(e)$ under $\iota$ is the sum of its $E/M$ conjugates, by the Galois trace formula. Both operations are additive, so this holds for any tensor. Applied to $w$ this sum is $rw$. Since $r$ is invertible in $F$, the tensor
$$
z=r^{-1}(1\otimes\operatorname{Tr}_{E/M})(w)\in B
$$
has $\iota(z)=w$. This proof uses a commutative $F$-algebra $K$ and the Galois top step. The factor $r^{-1}$ acts through the original base $F$. [A2, `TensorExistsOfGaloisFixed.lean:8–35`](../sources/SOURCES.md#local-tensor-power-norm-cancellation-53120)

**Reading the determinant in the smaller algebra.** Put $T_M=1\otimes\bar\sigma$ on $B$. Restriction of automorphisms gives $\iota T_M=T\iota$ on pure tensors and hence on all of $B$. The lower determinant formula and this identity give
$$
\iota\bigl(N_{B/K}(z)\otimes1\bigr)
 =\iota\left(\prod_{j=0}^{d-1} T_M^j(z)\right)
 =\prod_{j=0}^{d-1}T^j(w)=s.
$$
Tensoring the injective $F$-linear map $M\to E$ by the $F$-vector space $K$ preserves injectivity. One can see this by extending an $F$-basis of $M$ to one of $E$. Also $K\to B$ is injective, as a basis of $M$ over $F$ can begin with $1$. These are the two injections in the final Lean step. They give $N_{B/K}(z)=j(b)$ in $K$. [A2, `IsNormFromBaseChangeOfPowFinrankCyclic.lean:161–188`](../sources/SOURCES.md#local-tensor-power-norm-cancellation-53120)

#### Calculating the corrected witness

Continue with the fifth-root tower above. The values $b=5$ and $c=1-\zeta$ belong to the $x=125$ example of §5.3.1.19. The input to cancellation has norm $25$. In each calculation one can take the original local witness for $125$ to be $y(1\otimes c)$ for the displayed $y$, since $N_{E/\mathbb Q}(c)=\Phi_5(1)=5$. In particular these examples allow local choices that are not preimages from the lower tensor before correction.

**Split at $11$.** In $K=\mathbb Q_{11}$ the residue $3$ satisfies $3^5=1\pmod{11}$ and $3\ne1\pmod{11}$, and $5\cdot3^4$ is a unit modulo $11$. Simple-root lifting gives a primitive fifth root $\lambda$ reducing to $3$. Evaluating at $\lambda,\lambda^2,\lambda^4,\lambda^3$ gives $A=K^4$, with $T$ the left shift and $U=T^2$. The fixed subalgebra $B=K^2$ embeds as $(a,b,a,b)$, since opposite indices correspond to the same root of the quadratic polynomial for $\zeta+\zeta^{-1}$. Take $y=(25,1,1,1)$. Multiplication is diagonal, with determinant $25$. The construction gives
$$
\begin{aligned}
P(y)&=(25,1,1,25), &u&=(5,1/5,1/5,5),\
v&=(5,0,0,5), &h=v+uU(v)&=(5,1,1,5),\
T(h)&=(1,1,5,5), &w=yT(h)h^{-1}&=(5,1,5,1).
\end{aligned}
$$
Here $uU(u)=(1,1,1,1)$ and $uU(h)=h$. The average of $w$ and $U(w)$ is $w$, which descends to $(5,1)$. Multiplication on $B$ is diagonal with entries $5,1$, hence determinant $5$. All displayed coordinates are exact in $K$.

**Non-split at the real place.** Evaluate at $\zeta$ and $\zeta^2$ in $\mathbb C$, with $\zeta=\exp(2\pi i/5)$. The other two roots are their conjugates. The Chinese remainder isomorphism gives $A=\mathbb C\times\mathbb C$ with $T(a,b)=(b,\overline a)$ and $U(a,b)=(\overline a,\overline b)$. The real subalgebra $B=\mathbb R\times\mathbb R$ is the fixed algebra of $U$. For $y=(5i,1)$, the two real multiplication matrices in the basis $(1,i)$ are
$$
\begin{pmatrix}0&-5\\5&0\end{pmatrix},\qquad
\begin{pmatrix}1&0\\0&1\end{pmatrix}.
$$
The determinant of their direct sum is $25$. Now
$$
\begin{aligned}
P(y)&=(5i,-5i), &u&=(i,-i),\
v&=(1,1), &h=v+uU(v)&=(1+i,1-i),\
T(h)&=(1-i,1-i), &w=yT(h)h^{-1}&=(5,1).
\end{aligned}
$$
Indeed $uU(u)=(1,1)$, $uU(h)=h$, and $i(1-i)=1+i$. The average fixes $w$ and gives the lower real pair $(5,1)$, whose multiplication determinant is $5$. This time conjugation within each factor matters to the correction.

**A connected non-split case at $2$.** The same tower also gives a field tensor at $K=\mathbb Q_2$. Modulo $2$, $\Phi_5$ has no linear factor. The only monic irreducible quadratic is $X^2+X+1$, and the remainder of $\Phi_5$ on division by it is $X+1$. Hence $\Phi_5$ is irreducible modulo $2$ and over $K$, so $A=K[X]/(\Phi_5)$ is a field. Denote its root by $\lambda$ and put $t=\lambda+\lambda^{-1}$. Then $t^2+t-1=0$, and this polynomial is irreducible modulo $2$. Thus $B=K(t)$. For $m=2-t$ we have $T(m)=3+t$ and $mT(m)=5$. Multiplication by $m$ on the basis $(1,t)$ has columns $(2,-1)$ and $(-1,3)$, hence determinant $5$. In a $B$-basis of $A$, multiplication by $m$ is the scalar matrix of size two. Over $K$ this has two copies of the lower matrix, so its determinant is $25$. Multiplication by $\lambda^{-1}$ has determinant $1$, since the characteristic polynomial of multiplication by $\lambda$ is $\Phi_5$ with constant coefficient $1$. Thus $y=m\lambda^{-1}$ has determinant $25$. Here
$$
P(y)=5\lambda^2,\qquad u=\lambda^2,\qquad
v=\lambda/2,\qquad h=v+uU(v)=\lambda,\qquad
w=yT(h)h^{-1}=m.
$$
Indeed $U(\lambda)=\lambda^{-1}$, $uU(u)=1$ and $uU(h)=h$. The fixed tensor averages to itself and descends to $m\in B$ with determinant $5$.

#### Hypotheses and the return to the tower

**Cyclicity matters.** Take $F=\mathbb Q$, $M=\mathbb Q(i)$, $E=\mathbb Q(i,\sqrt2)$, $K=\mathbb R$ and $b=-1$. The upper degree is two and the full Galois group is $C_2\times C_2$, given by the independent signs of $i$ and $\sqrt2$. The upper tensor is $\mathbb C\times\mathbb C$ and its identity has norm $1=b^2$. Every lower tensor element is $a+bi$ with real coordinates, and its determinant is the sum of their squares, so the target $-1$ is excluded. This deletes only cyclicity from the cancellation lemma. Even *within* the fifth-root cyclic tower, $(-1)^2$ has the identity as a witness at every place. Yet $-1$ cannot be an $E/\mathbb Q$ norm, since a nonzero real tensor norm is a product of positive squared moduli. The conclusion concerns the lower extension and the specified scalar. The exponent must match the upper degree. In the cyclic seventh-root tower of §5.3.1.19, take $M=\mathbb Q(\sqrt{-7})$, $K=\mathbb R$ and $b=-1$. The upper degree is three. Replacing it by two would make the upper equation true with the identity witness, while the lower target $-1$ is excluded by the complex multiplication determinant. This example also has no real algebra structure extending the map through $M$.

**Use of the hypotheses.** The compatible tower supplies the map $B\to A$ and the Galois restriction. The finite Galois degree supplies two full conjugate products and finite multiplication matrices. Cyclicity orders the full product and identifies the subgroup and quotient generators. The field structure on $K$ makes $j(b)$ a unit and supplies vector spaces for the unit selection. The characteristic-zero assumption makes $K$ infinite and $r$ invertible in $F$. These are uses in this proof. The determinant identity works already over a commutative scalar algebra, while the unit selection here uses the field. The archive proves the implication for $b\ne0$. For the omitted scalar $0$ the zero tensor witnesses norm zero, since both ranks are positive.

**The same $b$ at every original place.** Fix the original $x$ and the one pair $b,c$ produced in §5.3.1.19, with $x=b^rN_{E/F}(c)$ and $b,c\ne0$. For every finite $v$ of $F$ take $K=F_v$ and the original witness $z_v\in K\otimes_F E$ for $x$. For every real $F$-algebra structure $a$ take $K=\mathbb R_a$ and the original witness $z_a$ for that very structure. In each case the inherited tensor norm identities give $y=z_v(1\otimes c^{-1})$ or $y=z_a(1\otimes c^{-1})$ with norm $j(b)^r$. The lemma uses only the specified $F$-algebra of each $K$, including real structures that do not extend to $M$. The resulting two families for $b$ are exactly the input to $\operatorname{NP}(F,M)$. Its output $m\in M$ has norm $b$, and the original tower consumer takes $mc$ in $E$. The finite-place transport is recorded in the [completion manuscript (§5.3.1.17)](../sources/SOURCES.md#chapter-5-unpublished-algebra-and-finite-place-supplies). The [real-place transport](#53118-the-same-tensor-norm-witness-at-a-real-place), the tower correction producing $b,c$ and the [full-degree induction](#53119-from-prime-degree-norms-to-the-cyclic-hasse-norm-principle) are given above. [A2, `HasseNormPrincipleOfCyclicTower.lean:184–198`](../sources/SOURCES.md#local-tensor-power-norm-cancellation-53120) · [§5.3.1.19](#53119-from-prime-degree-norms-to-the-cyclic-hasse-norm-principle)

**Attribution and reading scope.** The cyclic norm theorem for number fields is due to Hasse, with the prime-degree antecedent credited there to Hilbert and Furtwängler. The algebraic power implication is also a consequence of the classical cyclic-algebra norm criterion and the additivity of the cyclic character under multiplication by the top degree. The witness proof here follows the A2 bodies of `LocStep.core`, `hilbert90_baseChange`, `tensor_exists_of_galois_fixed` and `algebraMap_norm_tensor_eq_prod_conjugates`, and their return through the lower determinant. These bodies have local author-level R3 [Lean, read]. The odd-prime input is taken up in [§5.3.1.21](#53121-descending-an-odd-prime-degree-norm-after-adjoining-roots-of-unity). Lean kernel replay, declaration-level reachability from `Main`, and peer review have separate records. [Source ledger](../sources/SOURCES.md#local-tensor-power-norm-cancellation-53120)

### 5.3.1.21 Descending an odd prime-degree norm after adjoining roots of unity

**Motivation.** In [§5.3.1.19](#53119-from-prime-degree-norms-to-the-cyclic-hasse-norm-principle), the odd-prime branch needs a norm witness in the original extension $E/F$. Adjoining a primitive $p$th root lets us use a theorem over a larger base $F'$. The solution there produces a norm of $x^{[F':F]}$ back in $E/F$. A scalar in $E$ gives a second norm, $x^p$. Bézout's identity combines these two equations.

**Two examples.** Fix $\eta=\exp(2\pi i/7)$ and the real cubic field $C=\mathbb Q(\eta+\eta^{-1})$. We will use $C/\mathbb Q$ and $\mathbb Q(\sqrt5)C/\mathbb Q(\sqrt5)$. In each case $p=3$, adjoining $\zeta=\exp(2\pi i/3)$ raises the base degree by two, and the original norm comes from a quotient of the cubic and square norm witnesses.

#### The local data and the supplied theorem

For a specified map $j:F\to K$ of fields, a tensor witness for $x\in F$ is an element $z\in K\otimes_F E$ with multiplication determinant $N_{K\otimes_F E/K}(z)=j(x)$. This is the predicate $\operatorname{TNorm}(F,E,K,x)$ of §5.3.1.19. Its algebra can be a product. The predicate $\operatorname{LocNorm}(F,E,x)$ requires such a witness at every finite place $v$ of $F$ in $F_v\otimes_F E$ and for every real embedding $j:F\to\mathbb R$ in $\mathbb R_j\otimes_F E$. At a complex completion the finite separable tensor is a product of copies of $\mathbb C$ whose coordinate product represents each nonzero scalar. The predicate $\operatorname{NP}(F,E)$ says that for every nonzero $x$ with the two local families there exists $y\in E$ with $N_{E/F}(y)=x$. [A2 definitions](../sources/SOURCES.md#odd-prime-cyclotomic-norm-descent-53121)

**Supplied theorem [Lean].** Let $D/B$ be a Galois extension of number fields of prime degree $p$. If $B$ is totally imaginary and has a specified primitive $p$th root $\zeta$, then $\operatorname{NP}(B,D)$ holds. This is the named input `np_of_finrank_prime_of_isPrimitiveRoot`. [A2 declaration](../sources/SOURCES.md#odd-prime-cyclotomic-norm-descent-53121)

**Lemma (combining two power norms).** Let $E/F$ be a finite field extension and let $x\in F^\times$. If $N_{E/F}(A)=x^m$ and $N_{E/F}(B)=x^n$ for relatively prime positive integers $m,n$, then $x$ is the norm of $A^rB^s$ for any integers $r,s$ with $rm+sn=1$.

**Proof.** The two values are nonzero, so $A,B$ are units. Multiplicativity makes the norm a homomorphism on units, in particular it sends inverses to inverses. Thus $N_{E/F}(A^rB^s)=x^{rm+sn}=x$. The Lean proof obtains $r,s$ from `Nat.gcdA` and `Nat.gcdB` and uses the norm identity for integer powers.

#### Cyclotomic descent [Lean, read]

**Theorem.** Let $E/F$ be a Galois extension of number fields of degree $p$, where $p$ is an odd prime. Its Galois group is cyclic because its order is prime. Fix $x\in F^\times$ with $\operatorname{LocNorm}(F,E,x)$. The supplied theorem implies that $x$ is a norm from $E$, with a witness constructed below.

**Proof.** Embed $E$ in an algebraic closure of $F$. Choose a primitive $p$th root $\zeta$ there and put $F'=F(\zeta)$ and $E'=EF'$. The minimal polynomial of $\zeta$ over $F$ divides $\Phi_p(T)=1+T+\cdots+T^{p-1}$. Hence $m=[F':F]$ lies between $1$ and $p-1$ and $\gcd(m,p)=1$. The tower laws give $p\mid [E':F]$ and $[E':F]=m[E':F']$, so $p\mid [E':F']$. The multiplication map $F'\otimes_F E\to E'$ has image a finite-dimensional domain over $F'$. Multiplication by any nonzero element of that domain is injective and hence surjective, so the image is a field. It contains both $F'$ and $E$, so it is $E'$. Its source has dimension $p$ over $F'$ by extension of a basis. Therefore $[E':F']=p$, the map is an isomorphism, and $[E':E]=m$. The degree of $E\cap F'$ over $F$ divides both $p$ and $m$, so the intersection is $F$. The $p$ distinct automorphisms of $E/F$ extend by the identity on the left tensor factor and remain distinct on $1\otimes E$. Thus $E'/F'$ is Galois. The archive obtains the tensor field by linear disjointness and then counts those automorphisms. [A2, `ExistsPushoutPrimitiveRoot.lean:9–72`](../sources/SOURCES.md#odd-prime-cyclotomic-norm-descent-53121)

A real embedding of $F'$ would send $\zeta$ to a real root of unity of order $p$. The only real roots of unity are $1$ and $-1$, so $F'$ is totally imaginary and its real witness family is empty. The statement keeps the original real family over $F$. [A2, `NpOfOddPrimeDegree.lean:48–57`](../sources/SOURCES.md#odd-prime-cyclotomic-norm-descent-53121)

For each finite place $w$ of $F'$, contract it to the finite place $v$ of $F$. The normalized valuation at $w$ restricts to a positive ramification multiple of the valuation at $v$. The inclusion of valued fields thus extends to a ring map $\phi_w:F_v\to F'_w$. If $j_v:F\to F_v$, $j'_w:F'\to F'_w$ and $i:F\to F'$ are the scalar maps, agreement on original points gives the commutative square
$$
\begin{array}{ccc}
 F & \xrightarrow{i} & F' \\
 \big\downarrow{j_v} && \big\downarrow{j'_w} \\
 F_v & \xrightarrow{\phi_w} & F'_w
\end{array}
\qquad \phi_w\circ j_v=j'_w\circ i.
$$
The archive constructs this map using the two equivalences between adic completions and completions of valuation models, then evaluates the map of completions on each original $x$. [A2, `ExistsRingHomAdicCompletionUnder.lean:7–22`](../sources/SOURCES.md#odd-prime-cyclotomic-norm-descent-53121)

Starting with the original witness $z_v\in F_v\otimes_F E$, apply $\phi_w\otimes1$ and then
$$
F'_w\otimes_F E \simeq F'_w\otimes_{F'}(F'\otimes_F E)
 \simeq F'_w\otimes_{F'} E'.
$$
In the first isomorphism the inverse sends $k\otimes(a\otimes e)$ to $k j'_w(a)\otimes e$. Thus the full composite sends $k\otimes e$ from the original tensor to $\phi_w(k)\otimes i_E(e)$ with $i_E:E\to E'$ the pushout inclusion. For a fixed $F$-basis of $E$, the scalar-extended basis gives multiplication columns for $z_v$. The corresponding columns for its image under $\phi_w\otimes1$ are their entrywise images under $\phi_w$, by multiplicativity and the coordinate expansion. Applying the determinant commutes with $\phi_w$, and the final isomorphism preserves the determinant by conjugation. The image of $z_v$ therefore has norm $\phi_w(j_v(x))=j'_w(i(x))$. The same $z_v$ can serve for every $w$ above $v$. This gives the whole finite family. [A2, `NpOfOddPrimeDegree.lean:13–31` and `IsNormFromBaseChangeBaseChangeProperties.lean:11–38`](../sources/SOURCES.md#odd-prime-cyclotomic-norm-descent-53121)

Since $i$ is injective, $i(x)\ne0$. Apply the supplied theorem to the fields $F',E'$, the same $p$ and the chosen $\zeta$. It gives $b\in E'$ with $N_{E'/F'}(b)=i(x)$. Set $A=N_{E'/E}(b)$ and let $B$ be the image of $x$ in $E$. Transitivity in the two towers and the scalar multiplication determinant give
$$
\begin{aligned}
N_{E/F}(A)&=N_{E'/F}(b)
 =N_{F'/F}(N_{E'/F'}(b))=N_{F'/F}(i(x))=x^m,\\
N_{E/F}(B)&=x^p.
\end{aligned}
$$
Apply the lemma with $n=p$. For any $r,s$ with $rm+sp=1$, the witness in the original $E$ is
$$
y=A^rB^s=N_{E'/E}(b)^r\,\bigl(\operatorname{algebraMap}_{F,E}(x)\bigr)^s,
\qquad N_{E/F}(y)=x^{rm+sp}=x.
$$
The archive supplies the two norm equations as `h1` and `h3`. [A2, `NpOfOddPrimeDegree.lean:33–64`](../sources/SOURCES.md#odd-prime-cyclotomic-norm-descent-53121)

#### Two calculations in the original cubic fields

Write $t=\eta+\eta^{-1}$. The polynomial $\Phi_7$ is irreducible by Eisenstein after shifting by $1$. Complex conjugation in its Galois group acts by exponent $-1$. Its fixed field has degree three and is generated by $t$, since $\eta$ is a nonreal root of $X^2-tX+1$. The quotient is generated by the class of $2$. The three images of $t$ are $t_j=\eta^j+\eta^{-j}$ for $j=1,2,4$. Grouping the seventh roots into inverse pairs gives $1+t+(t^2-2)+(t^3-3t)=0$, so $f(T)=T^3+T^2-2T-1$ is the minimal polynomial of $t$.

**Over $\mathbb Q$.** Inside the fixed complex embedding take $F=\mathbb Q$, $E=C$, $F'=\mathbb Q(\zeta)$ and $E'=C(\zeta)$. The intersection $F'\cap E$ is $\mathbb Q$ by degrees two and three. Put $u=t-2$ and $x=-f(2)=-7$. At the real place, the three real coordinates of $1\otimes u$ are $t_j-2$, with product $-7$. For each finite $v$ take the same pure tensor $1\otimes u$ over $F_v$. Its determinant is given by the first matrix below with $S=2$.

**Over $\mathbb Q(\sqrt5)$.** Take $\rho=\sqrt5>0$ in the fixed embedding and put $F=\mathbb Q(\rho)$, $E=F(t)$. Since $F\cap C=\mathbb Q$ by degrees, and the cubic and quadratic degrees are coprime, the degree argument above gives $[E:F]=3$. The automorphism on $C$ from exponent $2$ extends by fixing $\rho$. With $F'=F(\zeta)$ and $E'=E(\zeta)$ the two root adjunctions have degree two since $F,E$ are real and $\zeta$ is nonreal quadratic. Again $F'\cap E=F$ by the coprime degrees over $F$. Choose $u=t-\rho$ and $x=-4-3\rho$. For each real structure $\rho\mapsto e\sqrt5$ with $e=1,-1$, the three coordinates are $t_j-e\sqrt5$. Their product is $-f(e\sqrt5)=-4-3e\sqrt5$. The original finite witnesses are $1\otimes u$ for all finite $v$, now using $S=\rho$ in the first matrix.

**Multiplication matrices and descent.** With $S=2$ or $S=\rho$ and $u=t-S$, reduction by $t^3=1+2t-t^2$ gives the matrices in the basis $(1,t,t^2)$
$$
M(u)=\begin{pmatrix}-S&0&1\\1&-S&2\\0&1&-1-S\end{pmatrix},
\qquad
M(u^2)=\begin{pmatrix}
 S^2&1&-1-2S\\
 -2S&S^2+2&-1-4S\\
 1&-1-2S&S^2+3+2S
\end{pmatrix}.
$$
The first has determinant $-S^3-S^2+2S+1$, giving the targets above. At each $w$, the finite scalar square carries $1\otimes u$ to $1\otimes i_E(u)$ with this first matrix mapped into $F'_w$. There are no real structures on $F'$.

Use the explicit upper solution $b=u\zeta$. Over $F'$ its multiplication matrix is $\zeta M(u)$, with determinant $x$ since $\zeta^3=1$. Over $E$, the basis $(1,\zeta)$ and $\zeta^2=-1-\zeta$ give
$$
M_{E'/E}(b)=\begin{pmatrix}0&-u\\u&-u\end{pmatrix},
\qquad \det M_{E'/E}(b)=u^2.
$$
The first power witness is $A=u^2$, whose matrix is $M(u)^2$ as displayed. Its determinant is $49$ over $\mathbb Q$ and $61+24\rho$ over $\mathbb Q(\rho)$. The second witness is $B=x$ with matrix $xI_3$ and determinant $-343$ over $\mathbb Q$ and $-604-279\rho$ over $\mathbb Q(\rho)$. The identity $2(-1)+3(1)=1$ gives $y=B/A=x/u^2$. Its norm is $-343/49=-7$ in the first calculation. In the second, $(-4-3\rho)(61+24\rho)=-604-279\rho$, so the norm is $-4-3\rho$. The denominator determinants are nonzero since they are $x^2$ with $x\ne0$. One can also compute the inverse explicitly. Division gives $f(T)-f(S)=(T-S)(T^2+(S+1)T+S^2+S-2)$, so $y=(t^2+(S+1)t+S^2+S-2)^2/x$ in both fields. In both cases $u^2$ has coefficient $1$ on $t^2$, so the first power witness genuinely lies outside the base field.

#### Hypotheses and the return to Hermitian descent

**Degree two.** The primitive second root is $-1\in F$, so adjoining it leaves $F$ itself, which may have real places. For $\mathbb Q(i)/\mathbb Q$ the real tensor is $\mathbb C$ and its norm is $a^2+b^2$ on $a+bi$. The positivity condition for nonzero norms survives. Coprimality still holds with $m=1$, and the separate quadratic input in §5.3.1.19 handles the real family.

**Coprimality.** Keep the first cyclic cubic and take $x=2$ with both exponents equal to $3$. Both powers are norms of the scalar $2$ in $E$. Yet $2$ is no norm from $E$. Modulo $2$, $f$ becomes $T^3+T^2+1$, which has no root and hence is irreducible. For nonzero $y$ in the scalar extension to $\mathbb Q_2$, factor $2^k$ out of its basis coefficients, where $k$ is their minimum valuation. The remaining coefficients are integral with at least one unit. They reduce to a nonzero element of the residue cubic field, so its multiplication determinant is nonzero modulo $2$. The norm of $y$ has valuation $3k$, whereas $2$ has valuation one. This refutes the inference from the two power equations alone. The example fails the original local condition at $2$, and cyclotomic adjunction cannot produce $m=3$ here.

**Nonzeroness.** If $x=0$ and $A=B=0$ in the first cubic with exponents $2,3$, both power equations hold, but every integer Bézout pair has a negative exponent. There is no inverse of the corresponding zero witness in the multiplicative group. The zero target itself has witness $0$ because the norm is a positive-rank determinant. This tests the formula on units.

**Use in A2.** The wrapper `GlobalTheory.T.np_of_odd_prime_degree'` exports the result. The prime-degree dispatcher selects it for $p\ne2$. The full cyclic-degree assembly of §5.3.1.19 uses the dispatcher for the prime-degree top step and strong induction below. Its separate tensor power-norm cancellation is the inherited input of §5.3.1.20. In `HasseEt` the all-degree theorem applies to the common cyclic field factor $L$ over the residue field $K=A/\mathfrak m$, with target the nonzero image in $K$ of the original coefficient-algebra unit. The inherited finite and real transports give the two witness families for that same image, and the resulting field norm witness is lifted through the product and assembled over the residue fields. [A2 source ledger](../sources/SOURCES.md#odd-prime-cyclotomic-norm-descent-53121)

**Attribution and reading scope.** The result specializes Hasse's cyclic norm theorem for number fields (1931, §1, pp. 64–68). Hasse credits Hilbert and Furtwängler for the prime-degree antecedent on p. 64. This explanation follows A2's cyclotomic descent and its direct suppliers at author-level local R3. The theorem over a base containing the primitive root remains a named [Lean] input. [Source ledger](../sources/SOURCES.md#odd-prime-cyclotomic-norm-descent-53121)

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
