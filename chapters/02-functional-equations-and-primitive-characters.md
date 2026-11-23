# Chapter 2. One half-plane implies everything: functional equations and primitive characters

> Sources as of 2026-11-21. Pinned archive sha256 `9631b4f0…9c7fc`; Mathlib at commit
> `0df444a` (tag `v4.33.1`); Masullo's draft sha256 `e039d3f6…97bf5`. See `sources/SOURCES.md`.

Chapter 1 showed that the archive's five headline theorems in `src/Main.lean` rest on a single
proposition, `UpperTheory.EveryCharacter`: no Dirichlet $L$-function vanishes on the open right
half-plane $\Re s > 1/2$, apart from the simple pole of the trivial character at $s = 1$
[Lean, read] (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13`).
Inside the archive, `EveryCharacter` itself is derived from a narrower statement,
`Formalism.HC.ZeroFreeAll`, which asserts the same non-vanishing on $\Re s > 1/2$ only for
*primitive* Dirichlet characters [Lean, read]
(`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:18`;
`src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5`).

This chapter opens Part I by teaching that entire outer shell from first principles. Everything
here is classical analytic number theory — Euler products at bad primes, conductors, Gamma
factors, and the functional equations of $\zeta(s)$ and of primitive $L(s,\chi)$ — and every line
of the corresponding Lean code imports Mathlib alone (or, on the side of `ZeroFreeAll`, thin
bookkeeping definitions over Mathlib). A graduate student can check every step by hand, and we
do so in full, following the order promised in the README: motivation, small examples,
definitions, lemmas and proofs, remarks (including Masullo's counterpart), and a complete
declaration-by-declaration Lean concordance.

---

## 2.1 Motivation

At first sight, the generalized Riemann hypothesis is a statement about a *line*: every nontrivial
zero of $L(s,\chi)$ in the critical strip $0 < \Re s < 1$ lies on $\Re s = 1/2$. Why does the
proof never aim at the critical line directly, and instead spend all its effort proving that a
*half-plane* $\Re s > 1/2$ is free of zeros for *primitive* characters?

Two basic asymmetries of multiplicative number theory dictate this reformulation [Expository].

1. **Primes live on the right.** The Dirichlet series $L(s,\chi) = \sum_{n \ge 1} \chi(n) n^{-s}$
   and the Euler product $\prod_p (1 - \chi(p) p^{-s})^{-1}$ converge absolutely on $\Re s > 1$.
   When one translates bounds on prime sums $\sum_{n \le x} \Lambda(n)\chi(n)$ into analytic
   information via Mellin or Laplace transforms (as Chapter 3 will do), the integral converges on
   a right half-plane $\Re s > \theta$ and shows that $-\frac{L'}{L}(s,\chi)$ has no poles to the
   right of $\Re s = \theta$. Prime-sum estimates are naturally blind to the distinction between a
   zero on $\Re s = 1/2$ and a zero on $\Re s = 1/4$: any zero at $\rho_0$ contributes an
   oscillation of size $x^{\Re\rho_0}$, which is masked by zeros on $\Re s = 1/2$ whenever
   $\Re\rho_0 < 1/2$. Thus an upper bound of exponent $1/2 + \varepsilon$ on prime sums can only
   forbid zeros with $\Re s > 1/2$.
2. **Reflection supplies the left half-plane — provided the character is primitive.** Once one
   knows $L(s,\chi) \neq 0$ on $\Re s > 1/2$ for *every* primitive character $\chi$, the
   functional equation relates $L(s,\chi)$ to $L(1 - s, \bar\chi)$. If $0 < \Re s < 1/2$, then
   $\Re(1 - s) > 1/2$. A zero of $L(s,\chi)$ in the left half of the critical strip would
   therefore become a zero of $L(1 - s, \bar\chi)$ in the right half, provided two potential
   obstructions do not interfere:
   - the archimedean Gamma factor $\gamma_\chi(s)$ relating $L(s,\chi)$ to the completed
     function $\Lambda(s,\chi)$ must have neither zeros nor poles that mask the zero at $s$ or
     absorb the zero at $1 - s$;
   - the functional equation in its clean form holds *only* for primitive characters.

An imprimitive character $\chi \bmod N$ is obtained from a unique primitive character
$\chi^* \bmod d$ (where $d \mid N$ is the conductor of $\chi$) by setting $\chi(n) = 0$ whenever
$\gcd(n, N) > 1$. On the level of $L$-functions, zeroing out primes $p \mid N$ simply multiplies
$L(s,\chi^*)$ by finitely many local Euler factors:
$$L(s,\chi) = L(s,\chi^*) \prod_{p \mid N} \bigl(1 - \chi^*(p)\,p^{-s}\bigr).$$
Each extra factor $1 - \chi^*(p) p^{-s}$ vanishes infinitely often when $p \nmid d$, namely along
a periodic lattice of points on the imaginary axis $\Re s = 0$. Those extra zeros spoil both the
naive functional equation for $\chi$ and any naive claim that all zeros of $L(s,\chi)$ in the
*closed* strip $0 \le \Re s \le 1$ lie on $\Re s = 1/2$. Yet in the open right half-plane
$\Re s > 0$, we have $\lvert \chi^*(p) p^{-s} \rvert \le p^{-\Re s} < 1$, so none of the extra
Euler factors can ever vanish on $\Re s > 0$. Stripping bad primes before applying the functional
equation, and restoring them afterwards, costs only a five-line inequality [Expository].

The logical architecture of the chapter mirrors that of the archive [Lean, read]:

$$\text{ZeroFreeAll (primitive }\chi,\ \Re s > \tfrac12\text{)}
\;\xrightarrow{\text{Prop. 2.2}}\;
\text{EveryCharacter (all }\chi,\ \Re s > \tfrac12\text{)}
\;\xrightarrow{\text{Thms. 2.5, 2.6}}\;
\text{all five theorems of }\texttt{src/Main.lean:4}.$$

---

## 2.2 Small examples

Before stating general definitions, we work through two concrete examples by hand [Expository].
They exhibit every phenomenon that the formal proofs have to handle: bad Euler factors on the
imaginary axis, parity of characters, the poles of $\Gamma(s/2)$, and the special status of
$s = 0$ and $s = 1$ for $\zeta(s)$.

### 2.2.1 Moduli $4$ and $12$: where imprimitive zeros sit

Let $\chi_4$ be the nontrivial Dirichlet character modulo $4$:
$$\chi_4(n) = \begin{cases}
1 & \text{if } n \equiv 1 \pmod 4,\\
-1 & \text{if } n \equiv 3 \pmod 4,\\
0 & \text{if } 2 \mid n.
\end{cases}$$
Because $\chi_4$ does not factor through $(\mathbb Z / 1\mathbb Z)^\times$ or
$(\mathbb Z / 2\mathbb Z)^\times$, its conductor is $4$ and $\chi_4$ is primitive. Since
$\chi_4(-1) = \chi_4(3) = -1$, it is an *odd* real character ($\chi_4^{-1} = \chi_4$), with
Dirichlet series
$$L(s,\chi_4) = 1 - \frac{1}{3^s} + \frac{1}{5^s} - \frac{1}{7^s} + \dots \qquad (\Re s > 0),$$
whose evaluation at $s = 1$ is Leibniz's series $L(1,\chi_4) = \pi/4 \neq 0$.

Now view $\chi_4$ modulo $12$ by defining $\chi_{12} : \mathbb Z/12\mathbb Z \to \mathbb C$ to be
the induced character: $\chi_{12}(n) = \chi_4(n)$ if $\gcd(n,12) = 1$, and $\chi_{12}(n) = 0$ if
$2 \mid n$ or $3 \mid n$. The prime divisors of $12$ are $2$ and $3$. At $p = 2$ we already had
$\chi_4(2) = 0$, so $1 - \chi_4(2) 2^{-s} = 1$. At $p = 3$, however, $\chi_4(3) = -1$, and
dropping multiples of $3$ removes the Euler factor $(1 - \chi_4(3) 3^{-s})^{-1} = (1 + 3^{-s})^{-1}$:
$$L(s,\chi_{12}) = L(s,\chi_4)\bigl(1 - \chi_4(2)2^{-s}\bigr)\bigl(1 - \chi_4(3)3^{-s}\bigr)
= L(s,\chi_4)\bigl(1 + 3^{-s}\bigr).$$
Look at the zeros of the extra factor $1 + 3^{-s}$:
$$1 + 3^{-s} = 0 \iff e^{-s \log 3} = -1 \iff s = \frac{(2k + 1)\pi i}{\log 3} \quad (k \in \mathbb Z).$$
Every one of these zeros lies on the imaginary axis $\Re s = 0$. Three lessons can be read off
immediately:

1. $L(s,\chi_{12})$ has infinitely many zeros on the boundary $\Re s = 0$ of the critical strip,
   even though $L(s,\chi_4)$ has none there. That is why `DirichletLZerosOnLine` in
   `src/Statements.lean:10` restricts to the *open* strip $0 < \Re s < 1$ [Lean, read].
2. For any $s$ with $\Re s > 0$, the triangle inequality gives
   $\lvert 1 + 3^{-s} \rvert \ge 1 - 3^{-\Re s} > 0$. Inside $\Re s > 0$, $L(s,\chi_{12})$ and
   $L(s,\chi_4)$ have the *exact same* zeros, with the same multiplicities.
3. If $L(s,\chi_{12})$ vanished at some point $s_0 = \frac{1}{4} + 14i$, then dividing by
   $1 + 3^{-s_0} \neq 0$ would give $L(s_0,\chi_4) = 0$. We could *not* apply the primitive
   functional equation directly to $\chi_{12}$ (note that $L(1 - s, \chi_{12})$ vanishes at
   $s = 1 - \frac{(2k+1)\pi i}{\log 3}$ on $\Re s = 1$, where $L(s,\chi_{12})$ has no zeros at
   all!), so passing from $\chi_{12}$ to $\chi_4$ before reflecting $s_0 \mapsto 1 - s_0$ is
   genuinely necessary.

### 2.2.2 Parity, Gamma poles, and why $\zeta(0) \neq 0$

Write $\Gamma_{\mathbb R}(s) = \pi^{-s/2}\Gamma(s/2)$. Because $\Gamma(w)$ never vanishes on
$\mathbb C$ and has simple poles at $w = 0, -1, -2, \dots$, the factor $\Gamma_{\mathbb R}(s)$ has
no zeros anywhere in $\mathbb C$ (except under Mathlib's total-function convention at its poles,
explained in Section 2.3.2 below) and classical simple poles at $s = 0, -2, -4, \dots$.

Compare three primitive characters under reflection $s \mapsto 1 - s$:

- **Odd primitive character ($\chi_4 \bmod 4$).** Here $\chi_4(-1) = -1$, so the completed
  $L$-function is $\Lambda(s,\chi_4) = \Gamma_{\mathbb R}(s + 1) L(s,\chi_4)$, which is entire and
  satisfies $\Lambda(1 - s, \chi_4) = 4^{s - 1/2}\,\varepsilon(\chi_4)\,\Lambda(s,\chi_4)$ (where
  the root number is $\varepsilon(\chi_4) = \tau(\chi_4)/(2i) = 2i/(2i) = 1$). At $s = 1$,
  $L(1,\chi_4) = \pi/4 \neq 0$ and $\Gamma_{\mathbb R}(2) = \pi^{-1}\Gamma(1) = \pi^{-1}$, so
  $\Lambda(1,\chi_4) = 1/4 \neq 0$. By the functional equation, $\Lambda(0,\chi_4) = 1/2 \neq 0$;
  since $\Gamma_{\mathbb R}(0 + 1) = \pi^{-1/2}\Gamma(1/2) = 1$ has no pole at $s = 0$, we get
  $L(0,\chi_4) = 1/2 \neq 0$. At $s = -1, -3, -5, \dots$, $\Lambda(s,\chi_4)$ is finite and
  nonzero (by $L(1 - s, \chi_4) \neq 0$ on $\Re(1 - s) \ge 2$), while $\Gamma_{\mathbb R}(s + 1)$
  has simple poles; thus $L(s,\chi_4)$ has simple *trivial zeros* at $-1, -3, -5, \dots$.
- **Even nontrivial primitive character ($\chi_8 \bmod 8$, with $\chi_8(\pm 1) = 1$, $\chi_8(\pm 3) = -1$).**
  Here $\chi_8(-1) = 1$, so $\Lambda(s,\chi_8) = \Gamma_{\mathbb R}(s) L(s,\chi_8)$ is entire.
  Because $L(1,\chi_8) = \frac{\log(1 + \sqrt 2)}{\sqrt 2} \neq 0$, $\Lambda(0,\chi_8) \neq 0$;
  now $\Gamma_{\mathbb R}(s)$ *already* has a simple pole at $s = 0$ as well as at
  $-2, -4, \dots$, forcing $L(s,\chi_8) = 0$ at $s = 0, -2, -4, \dots$ (including $s = 0$!).
- **The Riemann zeta function ($N = 1$, $\chi = 1$).** Here $\Lambda_\zeta(s) = \Gamma_{\mathbb R}(s)\zeta(s)$
  satisfies $\Lambda_\zeta(1 - s) = \Lambda_\zeta(s)$, *but* $\zeta(s)$ has a simple pole at
  $s = 1$, so $\Lambda_\zeta(s)$ has simple poles at both $s = 1$ and $s = 0$. At $s = 0$, the
  simple pole of $\Lambda_\zeta(s)$ cancels the simple pole of $\Gamma_{\mathbb R}(s)$, leaving
  $\zeta(0) = -1/2 \neq 0$; the trivial zeros of $\zeta(s)$ sit only at $-2, -4, -6, \dots$.

Now watch what happens if $\zeta(s)$ has a hypothetical zero at $s_0$ with $\Re s_0 < 1/2$ and
$s_0 \notin \{-2, -4, -6, \dots\}$. Put $w = 1 - s_0$, so $\Re w > 1/2$. Could $w = 1$? Only if
$s_0 = 0$, which is impossible because $\zeta(0) = -1/2 \neq 0$. Thus $w \neq 1$ and $\Re w > 1/2$,
where our half-plane hypothesis says $\zeta(w) \neq 0$. In the asymmetric functional equation
$$\zeta(s_0) = \zeta(1 - w) = 2(2\pi)^{-w}\Gamma(w)\cos\Bigl(\frac{\pi w}{2}\Bigr)\zeta(w),$$
the factors $2(2\pi)^{-w}$, $\Gamma(w)$ (since $\Re w > 1/2 > 0$), and $\zeta(w)$ are all nonzero.
Hence $\cos(\pi w / 2) = 0$, so $w = 2k + 1$ for some $k \in \mathbb Z$, meaning $s_0 = -2k$. Then
$-2k = \Re s_0 < 1/2$ forces $k \ge 0$; $k = 0$ gives $s_0 = 0$ (impossible), and $k \ge 1$ gives
$s_0 = -2k \in \{-2, -4, \dots\}$, contradicting the assumption that $s_0$ is not a trivial zero.
That twelve-line calculation *is* the proof of `Formalism.VW.rh_of_right` (`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5`) [Lean, read].

---

## 2.3 Definitions

We fix the exact mathematical definitions and match them against Mathlib (at commit `0df444a`) and
the archive's character-box modules.

### 2.3.1 Conductors, level change, and bundled primitive characters

Let $N \ge 1$ be an integer. A **Dirichlet character modulo $N$** is a multiplicative homomorphism
$(\mathbb Z/N\mathbb Z)^\times \to \mathbb C^\times$, extended to $\mathbb Z/N\mathbb Z$ (and hence
to $\mathbb Z$ and $\mathbb N$) by mapping every residue class not coprime to $N$ to $0$. In
Mathlib this is `DirichletCharacter ℂ N`, defined as `MulChar (ZMod N) ℂ` [Lean]
(`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:40`), with the positivity condition $N \ge 1$
carried by the typeclass `[NeZero N]`. Because every unit of $\mathbb Z/N\mathbb Z$ has finite
order, every value $\chi(n)$ is either $0$ or a root of unity; in particular $\lvert \chi(n) \rvert \le 1$,
and the pointwise inverse character $\chi^{-1}$ satisfies $\chi^{-1}(n) = \overline{\chi(n)}$ for
all $n$.

**Definition 2.1 (Level change, conductor, and primitive character).** Let $d \mid N$ with
$d, N \ge 1$, and let $\pi_{N,d} : (\mathbb Z/N\mathbb Z)^\times \twoheadrightarrow (\mathbb Z/d\mathbb Z)^\times$
be reduction modulo $d$.

1. Given $\psi \bmod d$, the **induced character** (or **level change**) modulo $N$, written
   `DirichletCharacter.changeLevel` for $d \mid N$ [Lean]
   (`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:66`), is the character modulo $N$ whose
   restriction to $(\mathbb Z/N\mathbb Z)^\times$ is $\psi \circ \pi_{N,d}$. On integers $a$ with
   $\gcd(a, N) = 1$ it equals $\psi(a)$; on integers sharing a prime factor with $N$ it equals $0$.
2. A character $\chi \bmod N$ **factors through $d$** (`FactorsThrough χ d`) if $d \mid N$ and
   $\chi = \operatorname{changeLevel}_{d \mid N}(\psi)$ for some $\psi \bmod d$. The **conductor**
   of $\chi$, denoted $\operatorname{cond}(\chi)$ (`χ.conductor`,
   `Mathlib/NumberTheory/DirichletCharacter/Basic.lean:246`), is the least natural number $d$
   through which $\chi$ factors [Lean]. Since $N \ge 1$, we have $\operatorname{cond}(\chi) \ge 1$
   and $\operatorname{cond}(\chi) \mid N$ (`conductor_ne_zero`, `:255`; `conductor_dvd_level`, `:251`) [Lean].
3. We say $\chi \bmod N$ is **primitive** (`χ.IsPrimitive`, `:292`) if $\operatorname{cond}(\chi) = N$ [Lean].
   Every $\chi \bmod N$ is induced from a unique primitive character $\chi^*$ modulo
   $d = \operatorname{cond}(\chi)$ (`χ.primitiveCharacter`, `:307`;
   `changeLevel_primitiveCharacter`, `:310`; `primitiveCharacter_isPrimitive`, `:314`) [Lean].
   For the trivial character $1 \bmod N$, the conductor is $1$ (`conductor_one`, `:259`), and its
   primitive character is the unique character $1 \bmod 1$ (`level_one`, `:202`) [Lean]. Moreover,
   taking inverses preserves conductors: $\operatorname{cond}(\chi^{-1}) = \operatorname{cond}(\chi)$
   (`conductor_inv`, `:405`) [Lean].

Inside the analytic endgame and the arithmetic engine, the archive packages a primitive character
together with its modulus into a single dependent record [Lean, read]
(`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean:7`, `:19`, `:21`, `:32`):

```lean
structure PChar where
  N : ℕ
  [ne : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive
```

Here `PChar.one` (`:19`) is the trivial character modulo $1$, `ψ.inv` (`:21`) is the primitive
character $(N, \chi^{-1})$, and `PChar.of χ` (`:32`) sends any character $\chi \bmod N$ to the
bundled triple $(\operatorname{cond}(\chi), \chi^*, \text{proof of primitivity})$ [Lean, read].

### 2.3.2 Archimedean Gamma factors and completed $L$-functions

A character $\chi \bmod N$ is **even** (`χ.Even`) if $\chi(-1) = 1$, and **odd** (`χ.Odd`) if
$\chi(-1) = -1$ [Lean] (`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:536`, `:533`). Since
$(-1)^2 = 1$ in $\mathbb Z/N\mathbb Z$ and $\chi(1) = 1$ (even for $N = 1$, where $-1 \equiv 1 \pmod 1$
makes the unique character modulo $1$ even), every complex-valued Dirichlet character is either
even or odd (`even_or_odd`, `:538`) [Lean].

**Definition 2.2 (Gamma factors and completed $L$-functions).** Define
$\Gamma_{\mathbb R}(s) = \pi^{-s/2}\Gamma(s/2)$ (`Complex.Gammaℝ`). For $\chi \bmod N$ with
$N \ge 1$:

1. The **archimedean Gamma factor** of $\chi$ is
   $$\gamma_\chi(s) := \begin{cases}
   \Gamma_{\mathbb R}(s) & \text{if }\chi\text{ is even},\\
   \Gamma_{\mathbb R}(s + 1) & \text{if }\chi\text{ is odd}
   \end{cases}$$
   (`DirichletCharacter.gammaFactor`, `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:207`) [Lean].
2. Mathlib constructs the **completed Riemann zeta function** $\Lambda_\zeta(s)$
   (`completedRiemannZeta`) and the **completed Dirichlet $L$-function** $\Lambda(s,\chi)$
   (`DirichletCharacter.completedLFunction`, `:224`) directly by theta-function Mellin transforms,
   and defines $L(s,\chi)$ so that the division identity
   $$L(s,\chi) = \frac{\Lambda(s,\chi)}{\gamma_\chi(s)}$$
   holds for all $s \in \mathbb C$ whenever $s \neq 0$ or $N \neq 1$
   (`LFunction_eq_completed_div_gammaFactor`, `:259`), and similarly
   $\zeta(s) = \Lambda_\zeta(s) / \Gamma_{\mathbb R}(s)$ for all $s \neq 0$
   (`riemannZeta_def_of_ne_zero`, `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:154`) [Lean].

One Mathlib convention deserves explicit notice so that the formal proofs in Section 2.4 read
naturally [Expository]. In Lean, total functions must assign a value at poles: `Complex.Gamma`
returns $0$ at its poles $0, -1, -2, \dots$, and complex division satisfies $z / 0 = 0$. As a
consequence, Mathlib's `Gammaℝ s` takes the value $0$ precisely at the classical *poles*
$s = -2n$ ($n \in \mathbb N$) of $\pi^{-s/2}\Gamma(s/2)$ (`Complex.Gammaℝ_eq_zero_iff`), and is
nonzero everywhere else — in particular on the entire right half-plane $\Re s > 0$
(`Gammaℝ_ne_zero_of_re_pos`). That is why Mathlib writes $L(s,\chi) = \Lambda(s,\chi)/\gamma_\chi(s)$
rather than $\Lambda = \gamma_\chi L$: at a trivial zero $s = -2k$ ($k \ge 1$) of an even
character, $\gamma_\chi(-2k) = 0$ in Lean, so $\Lambda(-2k,\chi)/0 = 0 = L(-2k,\chi)$ holds
without exception! Only at $s = 0$ for $N = 1$, where $\zeta(0) = -1/2 \neq 0$ despite
$\Gamma_{\mathbb R}(0) = 0$, must $s = 0$ be excluded [Expository].

### 2.3.3 The half-plane and critical-strip propositions

We record in mathematical notation the exact propositions linked in this chapter.

**Definition 2.3 (Target and intermediate propositions).**

1. **Primitive right half-plane (`Formalism.HC.ZeroFreeAll`).** For every bundled primitive
   character $\psi = (N, \chi, \text{prim})$ and every $s \in \mathbb C$ with $\Re s > 1/2$, we
   have $L(s, \psi.\chi) \neq 0$ [Lean, read]
   (`src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:11`, `:14`, `:18`):
   ```lean
   def PChar.ZeroFreeAbove (ψ : PChar) (θ : ℝ) : Prop :=
     ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction ψ.χ s ≠ 0

   def ZeroFreeOn (Q : PChar → Prop) : Prop := ∀ ψ : PChar, Q ψ → ψ.ZeroFreeAbove (1 / 2)

   def ZeroFreeAll : Prop := ZeroFreeOn fun _ => True
   ```
   Notice that `PChar.ZeroFreeAbove ψ (1 / 2)` requires $L(s, \psi.\chi) \neq 0$ for *every*
   $s$ with $\Re s > 1/2$, **without** excluding $s = 1$ even when $\psi = \mathrm{PChar.one}$!
   Why is that true rather than false at $(\psi, s) = (\mathrm{PChar.one}, 1)$? Because, as we saw
   in Chapter 1 (Section 1.2.2), for $N = 1$ we have `LFunction 1 1 = riemannZeta 1 = (γ - log 4π)/2 ≠ 0`
   (`riemannZeta_ne_zero_of_one_le_re`, `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:411`) [Lean, read]!
   Mathlib's nonzero junk value at the pole $s = 1$ of $\zeta$ allows the internal predicate
   `ZeroFreeAll` to omit the exception $(\psi, s) = (1, 1)$, whereas the public statement
   `EveryCharacter` prudently restores the hypothesis $(\chi \neq 1 \lor s \neq 1)$ so that
   nothing in the final theorem statements depends on any junk value at $s = 1$ [Expository].
2. **All-character right half-plane (`UpperTheory.EveryCharacter` / `Claim.HalfPlane` / `DirichletLNonvanishingRightOfHalf`).**
   For every $N \ge 1$, every $\chi \bmod N$, and every $s \in \mathbb C$ with $\Re s > 1/2$, if
   $\chi \neq 1$ or $s \neq 1$, then $L(s,\chi) \neq 0$ [Lean, read]
   (`src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13`;
   `src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean:3`; `src/Statements.lean:6`).
3. **Critical-strip targets (`PrimitiveDirichletLZerosOnLine`, `DirichletLZerosOnLine` / `Claim.Strip`)
   and global RH (`RiemannHypothesis` / `RiemannZetaZerosOnLine` / `Claim.Zeta`).** As stated in
   Chapter 1, Sections 1.2.1 and 1.3.1 [Lean, read] (`src/Statements.lean:3,10,14`;
   `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`).

---

## 2.4 Lemmas and proofs

We now prove every implication in the chain from `ZeroFreeAll` to the five theorems of
`src/Main.lean`. Each proof is self-contained and follows the exact mathematical reasoning checked by
Lean.

### 2.4.1 Bad Euler factors and passage from primitive to all characters

**Lemma 2.1 (Non-vanishing of single Euler factors on $\Re s > 0$).** *Let $M \ge 1$, let
$\psi$ be a Dirichlet character modulo $M$, let $p$ be a prime number, and let $s \in \mathbb C$
satisfy $\Re s > 0$. Then*
$$1 - \psi(p)\,p^{-s} \neq 0.$$
*(Lean: `Claim.factor_ne_zero`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:7`,
and inline inside `UpperTheory.Top.imprimitive`, `src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:21`.)* [Lean, read]

*Proof.* Suppose for a contradiction that $1 - \psi(p) p^{-s} = 0$, so $\psi(p) p^{-s} = 1$. Since
$p$ is prime, $p > 1$; since $-\Re s < 0$, we have
$$\lvert p^{-s} \rvert = p^{-\Re s} < 1.$$
Every value of a Dirichlet character lies in $\{0\} \cup \{z \in \mathbb C : \lvert z \rvert = 1\}$,
so $\lvert \psi(p) \rvert \le 1$. Multiplying gives
$$1 = \lvert \psi(p)\,p^{-s} \rvert = \lvert \psi(p) \rvert \cdot \lvert p^{-s} \rvert
\le 1 \cdot p^{-\Re s} < 1,$$
a contradiction. $\square$

To relate $L(s,\chi)$ to $L(s,\chi^*)$ across the whole complex plane (away from the pole at
$s = 1$), Mathlib provides the level-change identity (`LFunction_changeLevel`,
`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:150`) [Lean]: if $d \mid N$ ($d, N \ge 1$)
and $\psi \bmod d$, then for every $s \in \mathbb C$ satisfying $\psi \neq 1 \lor s \neq 1$,
$$L\bigl(s, \operatorname{changeLevel}_{d \mid N}(\psi)\bigr)
= L(s,\psi) \prod_{p \mid N} \bigl(1 - \psi(p)\,p^{-s}\bigr),$$
where the product runs over the distinct prime divisors of $N$. (Notice that if a prime $p \mid N$
also divides $d$, then $\psi(p) = 0$ when $d > 1$, so the factor $1 - \psi(p) p^{-s}$ is simply
$1$; only primes dividing $N$ and coprime to $d$ contribute nontrivial factors. On $\Re s > 1$ the
identity is immediate by comparing Euler products, and Mathlib extends it to $\mathbb C \setminus \{1\}$
— and to $s = 1$ when $\psi \neq 1$ — by continuity on the dense open set $\mathbb C \setminus \{1\}$.)

**Proposition 2.2 (Primitive characters imply all characters on $\Re s > 1/2$).** *Assume
`ZeroFreeAll`: for every primitive Dirichlet character $\psi$ and every $s \in \mathbb C$ with
$\Re s > 1/2$, we have $L(s,\psi) \neq 0$. Then `EveryCharacter` holds: for every $N \ge 1$, every
Dirichlet character $\chi \bmod N$, and every $s \in \mathbb C$ with $\Re s > 1/2$ and
$(\chi \neq 1 \lor s \neq 1)$, we have $L(s,\chi) \neq 0$.*
*(Lean: `UpperTheory.Top.imprimitive`, `src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5`.)* [Lean, read]

*Proof.* Fix $N \ge 1$, $\chi \bmod N$, and $s \in \mathbb C$ with $\Re s > 1/2$ and
$(\chi \neq 1 \lor s \neq 1)$. Let $d = \operatorname{cond}(\chi) \ge 1$, so $d \mid N$, and let
$\chi^* \bmod d$ be the primitive character inducing $\chi$, so that
$\chi = \operatorname{changeLevel}_{d \mid N}(\chi^*)$.

First, applying `ZeroFreeAll` to the bundled primitive character $\mathrm{PChar.of}(\chi) = (d, \chi^*)$
gives $L(s, \chi^*) \neq 0$.

Second, we verify the hypothesis $(\chi^* \neq 1 \lor s \neq 1)$ needed to invoke the level-change
identity. If $s \neq 1$, the second disjunct holds immediately. If $\chi \neq 1$, then we must
have $\chi^* \neq 1$: indeed, if $\chi^* = 1 \bmod d$, then inducing the trivial character from
level $d$ to level $N$ yields the trivial character $1 \bmod N$ (`changeLevel_one`,
`Mathlib/NumberTheory/DirichletCharacter/Basic.lean:220`), contradicting $\chi \neq 1$.

Therefore the level-change formula applies at $s$ and gives
$$L(s,\chi) = L(s,\chi^*) \prod_{p \mid N} \bigl(1 - \chi^*(p)\,p^{-s}\bigr).$$
Here $L(s,\chi^*) \neq 0$, and since $\Re s > 1/2 > 0$, Lemma 2.1 shows that every factor
$1 - \chi^*(p) p^{-s}$ in the finite product is nonzero. A product of nonzero complex numbers is
nonzero, so $L(s,\chi) \neq 0$. $\square$

*(Remark on the proof.)* Notice that even if one weakened `ZeroFreeAll` to exclude the pole
$(\psi, s) = (\mathrm{PChar.one}, 1)$, the proof above would still go through word for word: when
$(\chi \neq 1 \lor s \neq 1)$ holds, we just checked that $(\chi^* \neq 1 \lor s \neq 1)$ holds,
and if $\chi^* = 1$ with $d = 1$ that forces $s \neq 1$ [Expository].

### 2.4.2 Functional-equation reflection in the critical strip

We turn to the deduction of the critical-line theorems from `EveryCharacter`. First we check that
the archimedean Gamma factors never vanish in the open right half-plane $\Re s > 0$.

**Lemma 2.3 (Non-vanishing of Gamma factors on $\Re s > 0$).** *For any modulus $M \ge 1$, any
Dirichlet character $\varphi \bmod M$, and any $t \in \mathbb C$ with $\Re t > 0$, we have
$\gamma_\varphi(t) \neq 0$.*
*(Lean: `Formalism.VW.gammaFactor_ne_zero`, `src/Formalism/GammaFactorNonvanishing/CritLine.lean:6`,
and `Claim.gamma_ne_zero`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:35`.)* [Lean, read]

*Proof.* For $\Re w > 0$, both $\pi^{-w/2} = \exp(-\frac{w}{2}\log\pi)$ and $\Gamma(w/2)$ (since
$\Re(w/2) > 0$) are nonzero, so $\Gamma_{\mathbb R}(w) \neq 0$ (`Gammaℝ_ne_zero_of_re_pos`). Now
$\varphi$ is either even or odd. If $\varphi$ is even, $\gamma_\varphi(t) = \Gamma_{\mathbb R}(t)$,
which is nonzero since $\Re t > 0$. If $\varphi$ is odd, $\gamma_\varphi(t) = \Gamma_{\mathbb R}(t + 1)$,
which is nonzero since $\Re(t + 1) = \Re t + 1 > 1 > 0$. $\square$

Next we prove that zeros of a primitive $L$-function in the open strip $0 < \Re s < 1$ reflect
cleanly under $(s, \psi) \mapsto (1 - s, \psi^{-1})$. For a primitive character $\chi \bmod M$,
Mathlib proves the global functional equation (`IsPrimitive.completedLFunction_one_sub`,
`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:284`) [Lean]: for every $s \in \mathbb C$,
$$\Lambda(1 - s, \chi) = M^{s - 1/2}\,\varepsilon(\chi)\,\Lambda(s, \chi^{-1}),$$
where $\varepsilon(\chi) = \tau(\chi) / (i^{\mathfrak a} M^{1/2})$ is the root number (`rootNumber`,
`:272`, with $\mathfrak a = 0$ for $\chi$ even and $\mathfrak a = 1$ for $\chi$ odd). Watch how
applying this equation to $\chi = \psi^{-1}$ rather than to $\psi$ spares us from proving
anything at all about the Gauss sum $\tau(\psi)$ or the root number $\varepsilon(\psi)$!

**Lemma 2.4 (Reflection of zeros for primitive characters).** *Let $M \ge 1$, let $\psi \bmod M$
be a primitive Dirichlet character, and let $s \in \mathbb C$ satisfy $0 < \Re s < 1$. If
$L(s,\psi) = 0$, then $L(1 - s, \psi^{-1}) = 0$.*
*(Lean: `Claim.prim_reflect`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:42`,
and inline inside `Formalism.VW.critLine`, `src/Formalism/GammaFactorNonvanishing/CritLine.lean:17–26`.)* [Lean, read]

*Proof.* Since $0 < \Re s < 1$, we have $\Re(1 - s) = 1 - \Re s > 0$; in particular $s \neq 0$ and
$1 - s \neq 0$.

1. Because $s \neq 0$, Definition 2.2(2) gives $L(s,\psi) = \Lambda(s,\psi) / \gamma_\psi(s)$.
   By Lemma 2.3 applied at $t = s$ ($\Re s > 0$), the denominator $\gamma_\psi(s)$ is nonzero.
   Since $L(s,\psi) = 0$, it follows that $\Lambda(s,\psi) = 0$.
2. Because $\psi \bmod M$ is primitive, we have $\operatorname{cond}(\psi^{-1}) = \operatorname{cond}(\psi) = M$,
   so $\psi^{-1} \bmod M$ is also primitive. Applying the functional equation of $\psi^{-1}$ at
   $s$, and using $(\psi^{-1})^{-1} = \psi$, we obtain
   $$\Lambda(1 - s, \psi^{-1}) = M^{s - 1/2}\,\varepsilon(\psi^{-1})\,\Lambda(s, (\psi^{-1})^{-1})
   = M^{s - 1/2}\,\varepsilon(\psi^{-1})\,\Lambda(s,\psi) = 0.$$
3. Because $1 - s \neq 0$, Definition 2.2(2) applied to $\psi^{-1}$ at $1 - s$ gives
   $$L(1 - s, \psi^{-1}) = \frac{\Lambda(1 - s, \psi^{-1})}{\gamma_{\psi^{-1}}(1 - s)}
   = \frac{0}{\gamma_{\psi^{-1}}(1 - s)} = 0.$$
   (Even without checking $\gamma_{\psi^{-1}}(1 - s) \neq 0$, $0 / z = 0$ holds unconditionally; of
   course Lemma 2.3 also shows $\gamma_{\psi^{-1}}(1 - s) \neq 0$ since $\Re(1 - s) > 0$.) $\square$

We also record the converse direction of Proposition 2.2 inside the critical strip: any zero of an
imprimitive $L(s,\chi)$ in $0 < \Re s < 1$ is already a zero of its underlying primitive
$L$-function $L(s,\chi^*)$.

**Lemma 2.5 (Stripping bad Euler factors at a strip zero).** *Let $N \ge 1$, let $\chi \bmod N$ be
any Dirichlet character with primitive character $\chi^* \bmod d$ ($d = \operatorname{cond}(\chi)$),
and let $s \in \mathbb C$ satisfy $0 < \Re s < 1$. If $L(s,\chi) = 0$, then $L(s,\chi^*) = 0$.*
*(Lean: `Claim.prim_zero`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:23`.)* [Lean, read]

*Proof.* Since $\Re s < 1$, we have $s \neq 1$. Hence the level-change formula applies to $\chi^*$
for $d \mid N$ and gives
$$0 = L(s,\chi) = L(s,\chi^*) \prod_{p \mid N} \bigl(1 - \chi^*(p)\,p^{-s}\bigr).$$
Because $\Re s > 0$, Lemma 2.1 implies that $1 - \chi^*(p) p^{-s} \neq 0$ for every prime $p \mid N$.
Dividing by the nonzero finite product yields $L(s,\chi^*) = 0$. $\square$

Combining Lemmas 2.4 and 2.5 immediately yields both critical-strip theorems of `src/Main.lean`.

**Theorem 2.6 (Critical-line theorems for primitive and general Dirichlet $L$-functions).** *Assume
`EveryCharacter`. Let $N \ge 1$, let $\chi \bmod N$ be a Dirichlet character, and let $s \in \mathbb C$
satisfy $0 < \Re s < 1$ and $L(s,\chi) = 0$. Then $\Re s = 1/2$. In particular, both
`PrimitiveDirichletLZerosOnLine` and `DirichletLZerosOnLine` hold.*
*(Lean: `Formalism.VW.critLine`, `src/Formalism/GammaFactorNonvanishing/CritLine.lean:11`;
`Claim.strip`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:59`;
`critAll` and `claimAll`, `src/Supplements/Kernels/MainTheorems.lean:11,15`.)* [Lean, read]

*Proof.* Since $0 < \Re s < 1$, we have $s \neq 0$ and $s \neq 1$. Compare $\Re s$ with $1/2$ by
trichotomy:

- **Case $\Re s > 1/2$.** Since $s \neq 1$, the hypothesis $(\chi \neq 1 \lor s \neq 1)$ holds, so
  `EveryCharacter` applied directly to $(N, \chi, s)$ gives $L(s,\chi) \neq 0$, contradicting
  $L(s,\chi) = 0$.
- **Case $\Re s < 1/2$.** Let $d = \operatorname{cond}(\chi) \ge 1$ and let $\chi^* \bmod d$ be
  the primitive character inducing $\chi$ (if $\chi$ is already primitive, $d = N$ and $\chi^* = \chi$).
  By Lemma 2.5, $L(s, \chi^*) = 0$. Since $\chi^*$ is primitive and $0 < \Re s < 1$, Lemma 2.4
  gives $L(1 - s, (\chi^*)^{-1}) = 0$. Now $\Re(1 - s) = 1 - \Re s > 1 - 1/2 = 1/2$, and
  $1 - s \neq 1$ because $s \neq 0$. Applying `EveryCharacter` to $(d, (\chi^*)^{-1}, 1 - s)$
  yields $L(1 - s, (\chi^*)^{-1}) \neq 0$, again a contradiction.
- **Case $\Re s = 1/2$.** This is the only remaining possibility. $\square$

### 2.4.3 Two derivations of the global Riemann Hypothesis

Mathlib's `RiemannHypothesis` (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185`) asks for more
than the critical strip $0 < \Re s < 1$: it states that for *every* $s \in \mathbb C$ with
$\zeta(s) = 0$, if $s$ is not of the form $-2(n + 1)$ ($n \in \mathbb N$) and $s \neq 1$, then
$\Re s = 1/2$ [Lean, read]. The archive contains *two* complete proofs of this global statement
from `EveryCharacter`:

1. `Formalism.VW.rh_of_every` (`src/Formalism/GammaFactorNonvanishing/CritLine.lean:29`) + `Formalism.VW.rh_of_right` (`src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5`),
   which is the proof term `rhOfAll` actually used by the first two theorems of `src/Main.lean:4,6`
   [Lean, read];
2. `Claim.zeta` (`src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:75`), which sits inside `claimAll` (`src/Supplements/Kernels/MainTheorems.lean:15`) and
   uses the symmetric completed zeta function instead of the cosine-Gamma functional equation
   [Lean, read].

Both proofs are short and instructive, so we give both.

**Theorem 2.7 (Global Riemann Hypothesis from `EveryCharacter`).** *Assume `EveryCharacter`. Then
Mathlib's `RiemannHypothesis` (and definitionally `RiemannZetaZerosOnLine` and `Claim.Zeta`) holds:
for every $s \in \mathbb C$, if $\zeta(s) = 0$, $s \notin \{-2(n + 1) : n \in \mathbb N\}$, and
$s \neq 1$, then $\Re s = 1/2$.*
*(Lean: `Formalism.VW.rh_of_every`, `src/Formalism/GammaFactorNonvanishing/CritLine.lean:29`;
`Formalism.VW.rh_of_right`, `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5`;
`Claim.zeta`, `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:75`.)* [Lean, read]

*First proof (via the asymmetric functional equation, mirroring `rh_of_every` and `rh_of_right`).*
First specialize `EveryCharacter` to $N = 1$ and the unique character $1 \bmod 1$. Since
`LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta` (`LFunction_modOne_eq`,
`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:67`), we obtain the right half-plane
non-vanishing property for $\zeta$:
$$\forall w \in \mathbb C,\quad \Re w > \tfrac12 \ \text{and}\ w \neq 1 \implies \zeta(w) \neq 0.$$

Now let $s \in \mathbb C$ satisfy $\zeta(s) = 0$, $s \notin \{-2(n + 1) : n \in \mathbb N\}$, and
$s \neq 1$. First note that $s \neq 0$, because $\zeta(0) = -1/2 \neq 0$ (`riemannZeta_zero`,
`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:151`). By trichotomy on $\Re s$ relative to $1/2$:

- If $\Re s > 1/2$, then since $s \neq 1$, the half-plane property immediately gives
  $\zeta(s) \neq 0$, contradicting $\zeta(s) = 0$.
- If $\Re s = 1/2$, we are done.
- Suppose $\Re s < 1/2$, and set $w = 1 - s$. Then $\Re w = 1 - \Re s > 1/2$. Furthermore:
  - $w \neq 1$, because $1 - s = 1$ would give $s = 0$;
  - $w \neq -n$ for every $n \in \mathbb N$, because $\Re w > 1/2 > 0 \ge -n = \Re(-n)$.
  Mathlib's asymmetric functional equation `riemannZeta_one_sub`
  (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean:178`) states that whenever $w \neq 1$ and
  $w \neq -n$ for all $n \in \mathbb N$,
  $$\zeta(1 - w) = 2\,(2\pi)^{-w}\,\Gamma(w)\,\cos\Bigl(\frac{\pi w}{2}\Bigr)\,\zeta(w).$$
  Since $1 - w = s$ and $\zeta(s) = 0$, the left-hand side is $0$. On the right-hand side:
  - $2(2\pi)^{-w} \neq 0$ since $2\pi > 0$;
  - $\Gamma(w) \neq 0$ since $\Re w > 1/2 > 0$ (`Complex.Gamma_ne_zero_of_re_pos`);
  - $\zeta(w) \neq 0$ by the right half-plane property applied to $w$ ($\Re w > 1/2$, $w \neq 1$).
  Hence the remaining factor $\cos(\pi w / 2)$ must vanish. In $\mathbb C$, $\cos z = 0$ if and
  only if $z = (2k + 1)\pi / 2$ for some integer $k \in \mathbb Z$ (`Complex.cos_eq_zero_iff`).
  Cancelling $\pi / 2 \neq 0$ gives $1 - s = w = 2k + 1$, that is, $s = -2k$ with $k \in \mathbb Z$.
  Taking real parts gives $-2k = \Re s < 1/2$, which for an integer $k$ forces $k \ge 0$:
  - if $k \le -1$, then $-2k \ge 2 > 1/2$, impossible;
  - if $k = 0$, then $s = 0$, contradicting $s \neq 0$;
  - if $k \ge 1$, then $m := k - 1 \in \mathbb N$ satisfies $s = -2k = -2(m + 1)$, contradicting
    the hypothesis that $s$ is not a trivial zero!
  Every branch of $\Re s < 1/2$ is impossible, so $\Re s = 1/2$. $\square$

*Second proof (via the completed zeta function, mirroring `Claim.zeta`).*
Let $\zeta(s) = 0$ with $s \notin \{-2(n + 1) : n \in \mathbb N\}$ and $s \neq 1$. Again $s \neq 0$
since $\zeta(0) = -1/2$. Split into three regions according to $\Re s$:

1. **The open strip $0 < \Re s < 1$.** Rewriting $\zeta(s) = L(s, 1 \bmod 1)$ and applying
   Theorem 2.6 (`Claim.strip` at $N = 1$) gives $\Re s = 1/2$.
2. **The closed half-plane $\Re s \ge 1$.** Mathlib's classical non-vanishing theorem
   `riemannZeta_ne_zero_of_one_le_re` (`Mathlib/NumberTheory/LSeries/Nonvanishing.lean:411`)
   gives $\zeta(s) \neq 0$, contradicting $\zeta(s) = 0$. (Notice that `EveryCharacter` itself
   would also rule out $\Re s \ge 1$ since $s \neq 1$; `Claim.zeta` simply invokes Mathlib's
   unconditional lemma here.)
3. **The closed left half-plane $\Re s \le 0$.** First check that $\Gamma_{\mathbb R}(s) \neq 0$
   (under Mathlib's convention where $\Gamma_{\mathbb R}$ vanishes precisely at its classical poles
   $0, -2, -4, \dots$): if $\Gamma_{\mathbb R}(s) = 0$, then $s = -2m$ for some $m \in \mathbb N$
   (`Gammaℝ_eq_zero_iff`); $m = 0$ gives $s = 0$ (impossible), and $m = n + 1$ gives
   $s = -2(n + 1)$ (excluded as a trivial zero). Since $s \neq 0$, the identity
   $\zeta(s) = \Lambda_\zeta(s) / \Gamma_{\mathbb R}(s)$ together with $\zeta(s) = 0$ and
   $\Gamma_{\mathbb R}(s) \neq 0$ forces $\Lambda_\zeta(s) = 0$. By the symmetric functional
   equation $\Lambda_\zeta(1 - s) = \Lambda_\zeta(s)$ (`completedRiemannZeta_one_sub`,
   `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:106`), we get $\Lambda_\zeta(1 - s) = 0$.
   Because $\Re s \le 0$, we have $\Re(1 - s) = 1 - \Re s \ge 1$; in particular $1 - s \neq 0$,
   so $\zeta(1 - s) = \Lambda_\zeta(1 - s) / \Gamma_{\mathbb R}(1 - s) = 0$. That contradicts
   $\zeta \neq 0$ on $\Re(1 - s) \ge 1$ (`riemannZeta_ne_zero_of_one_le_re`). $\square$

---

## 2.5 Remarks

### 2.5.1 Why two parallel sets of reductions exist in the archive

A reader browsing the archive will notice redundancy in this layer [Lean, read]:

- `CritLine.lean` and `RhOfRight.lean` supply `rhOfAll` (`src/Main.lean:4,6`) and `critAll`
  (`src/Main.lean:12`), while `ClaimStrip.lean` supplies `Claim.strip` (`src/Main.lean:10`) as well as a
  second proof `Claim.zeta` of RH inside `claimAll` (`src/Supplements/Kernels/MainTheorems.lean:15`).
- As noted in `notes/proof-map.md` (P2), there is even a third derivation of RH from
  `EveryCharacter`, `UpperTheory.riemannHypothesis_of_everyCharacter`
  (`src/Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean:215`),
  which `src/Main.lean` never imports [Lean].

In an AI-assisted codebase of 175,187 modules, small glue files were evidently written more than
once as target statements were tidied up into `src/Statements.lean` [Expository]. From a verification
standpoint the duplication is benign — and in fact helpful: `RhOfRight.lean` (`62` lines) and
`ClaimStrip.lean` (`104` lines, via `HalfPlane.lean`) import **only Mathlib**, with zero archive
dependencies, so one can read and type-check the passage from `Claim.HalfPlane` to all five
final theorem shapes against stock Mathlib in seconds [Lean, read].

### 2.5.2 What Dirichlet GRH does and does not imply for Dedekind zeta functions

Once `EveryCharacter` (and hence GRH for all primitive Dirichlet $L$-functions) is established,
what follows automatically for number fields $K / \mathbb Q$ by classical algebraic number theory,
even without formalizing Dedekind zeta functions? The answer splits sharply along abelian versus
non-abelian Galois groups [Expository]:

1. **Abelian number fields: RH for $\zeta_K(s)$ follows.** By the Kronecker–Weber theorem, every
   finite abelian extension $K / \mathbb Q$ lies inside some cyclotomic field $\mathbb Q(\zeta_N)$.
   Viewing $\operatorname{Gal}(\mathbb Q(\zeta_N)/\mathbb Q) \cong (\mathbb Z/N\mathbb Z)^\times$,
   the character group $X(K)$ of $\operatorname{Gal}(K/\mathbb Q)$ identifies with a subgroup of
   Dirichlet characters modulo $N$, and class field theory (see Washington, *Introduction to
   Cyclotomic Fields*, 2nd ed., Springer, 1997, Theorem 4.3, or Davenport, *Multiplicative Number
   Theory*, 3rd ed., Springer, 2000, Chapter 4) gives the exact factorization
   $$\zeta_K(s) = \prod_{\chi \in X(K)} L(s, \chi^*),$$
   where $\chi^*$ is the primitive Dirichlet character attached to $\chi$. Because this is a
   *honest product with positive integer exponents* (exponent $1$ for each $\chi \in X(K)$), no
   factor is in the denominator: for $\chi = 1$ we get $\zeta(s)$ (whose single pole at $s = 1$
   supplies the simple pole of $\zeta_K(s)$ at $s = 1$), and for $\chi \neq 1$ the factor
   $L(s,\chi^*)$ is entire. Therefore the zeros of $\zeta_K(s)$ in $0 < \Re s < 1$ are simply the
   union of the zeros of $L(s,\chi^*)$ ($\chi \in X(K)$), all of which lie on $\Re s = 1/2$ by
   Theorem 2.6. (In particular, for the abelian CM "host" fields $E \subset \mathbb Q(\zeta_N)$
   that appear in Chapters 4, 5, and 11, $\zeta_E(s)$ factors into primitive Dirichlet
   $L$-functions — a fact that is central to why finite Fourier analysis on the character group of
   $E$ works in Chapter 5, though of course Chapters 4–11 never assume GRH when proving it!)
2. **Non-abelian number fields: ERH does *not* follow from Dirichlet GRH.** For an arbitrary
   Galois extension $K / \mathbb Q$, Artin's decomposition writes $\zeta_K(s)$ as a product of
   Artin $L$-functions of irreducible representations of $\operatorname{Gal}(K/\mathbb Q)$, and
   Brauer's induction theorem expresses each Artin $L$-function as an alternating product
   $\prod_i L(s, \psi_i)^{n_i}$ of **Hecke $L$-functions of intermediate subfields $F_i \subset K$**
   with $n_i \in \mathbb Z$. Two obstructions block any deduction from `EveryCharacter`: first,
   the base fields $F_i$ are in general nontrivial extensions of $\mathbb Q$, so $L(s,\psi_i)$ is
   a Hecke (or principal Dirichlet) $L$-function over $F_i$, not over $\mathbb Q$; second, even if
   one knew non-vanishing on $\Re s > 1/2$ for some factors, negative exponents $n_i < 0$ mean a
   zero of one factor could in principle cancel against another unless Artin's holomorphy
   conjecture or zero-freeness of *all* factors on $\Re s > 1/2$ is known first. Thus the
   Extended Riemann Hypothesis (ERH) genuinely lies outside the scope of the five theorems of
   `src/Main.lean`, matching Alpöge's remark that he expects ERH only "with more time"
   [Paper; remark p. 1].

### 2.5.3 Masullo's counterpart

In Masullo's draft *The Music of the Primes*, the mathematical counterpart of this chapter sits in
**Chapter 3 ("Idelic Zeta Functions", pp. 117–154)** and in the overview of the intended endgame
in **Section 1.8.5.1 (p. 55)**, pointing toward the unfinished **Chapter 13 (pp. 521–522)**
[Paper; Masullo pp. 55, 117–154, 521–522].

- **Tate's thesis instead of Hurwitz zeta functions.** Where Mathlib defines $L(s,\chi)$ over
  $\mathbb Q$ as a linear combination of Hurwitz zeta functions and proves the functional equation
  via finite Fourier transforms on $\mathbb Z/N\mathbb Z$ (`ZMod.completedLFunction_one_sub_even` /
  `_odd`), Masullo works over an arbitrary number field $F$ following J. T. Tate's 1950 thesis
  ("Fourier analysis in number fields, and Hecke's zeta-functions", published in J. W. S. Cassels
  and A. Fröhlich, eds., *Algebraic Number Theory*, Academic Press, London, 1967, pp. 305–347) and
  D. Ramakrishnan and R. J. Valenza, *Fourier Analysis on Number Fields* (Springer, 1999) [Paper;
  Masullo p. 11, §1.1.1, and p. 123, Prop. 3.2.1.3]. By working directly with continuous
  characters $\chi$ of the idele class group $C_F = \mathrm{GL}_1(\mathbb A_F)/F^\times$, every
  character is automatically primitive (its ramification at each finite place $v$ determines the
  exact local Euler factor of the completed Hecke $L$-function $L(s,\chi)$, Definition 3.2.1.2,
  p. 123, and of the finite Hecke $L$-function $L_f(s,\chi)$, Definition 3.2.1.4, pp. 123–124),
  and the global idelic Mellin transform of an adelic theta function yields meromorphic
  continuation and the functional equation in one stroke (Theorem 3.2.2.1, p. 124) [Paper; Masullo
  pp. 123–124].
- **Same half-plane-to-strip logic, shifted by $1/2$.** Masullo normalizes his spectral variable so
  that the critical line sits at $\Re s = 0$, writing $L_f(s + 1/2, \chi)$. In the sketch from his
  letter to Sarnak (§1.8.5.1, equation (1.8.5.1), p. 55), the intended output of his trace formula
  is that for every unitary character $\chi$ of $C_F$, the logarithmic derivative
  $$\frac{L_f'(s + 1/2, \chi)}{L_f(s + 1/2, \chi)} - \delta\Bigl(\frac{1}{s + 1/2} + \frac{1}{s - 1/2}\Bigr)$$
  is holomorphic on the open right half-plane $\Re s > 0$ (which is $\Re(s + 1/2) > 1/2$ in
  classical coordinates!), so $L_f(w,\chi)$ has neither zeros nor uncancelled poles on $\Re w > 1/2$
  [Paper; Masullo p. 55]. Passing from $\Re w > 1/2$ to all of $0 < \Re w < 1$ is then the exact
  same classical functional-equation reflection $w \mapsto 1 - w$ (i.e. $s \mapsto -s$ after
  accounting for archimedean Gamma factors). As recorded in Chapter 1 (Section 1.8), Chapter 13 of
  the draft currently stops at restating the trace formula (Theorem 13.3.1.1, p. 522) and has not
  yet written out this final deduction [Paper; Masullo pp. 521–522].

---

## 2.6 Lean counterpart for this chapter

Every Lean file from the archive listed below has been read line by line by us (`R3` in
`notes/proof-map.md`, nodes `P1` and `P3`), so every archive entry carries `[Lean, read]`.
Mathlib declarations are cited at the pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`
(`v4.33.1`).

### 2.6.1 Archive declarations (nodes P1 and P3)

| Declaration | File:line | Mathematical content / role in Section 2.4 | Tag |
|---|---|---|---|
| `UpperTheory.EveryCharacter` | `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:13` | $L(s,\chi) \neq 0$ for all $N \ge 1$, all $\chi \bmod N$, and all $\Re s > 1/2$ with $(\chi \neq 1 \lor s \neq 1)$. | [Lean, read] |
| `UpperTheory.Top.plugWin`, `UpperTheory.Top.plugAll` | `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean:8,16` | Side assembly route (not imported by `src/Main.lean`) pairing `zeroFreeAll_of_topG` with `imprimitive`. | [Lean, read] |
| `Formalism.HC.PChar`, `PChar.one`, `PChar.inv`, `PChar.of` | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean:7,19,21,32` | Bundled primitive Dirichlet characters $(N, \chi, \text{prim})$, trivial bundle, inverse, and extraction of $( \operatorname{cond}\chi, \chi^* )$. | [Lean, read] |
| `Formalism.HC.PChar.ZeroFreeAbove`, `ZeroFreeOn`, `ZeroFreeAll` | `src/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:11,14,18` | Zero-freeness of $L(s,\psi.\chi)$ on $\Re s > \theta$ and on $\Re s > 1/2$ for all primitive $\psi$. | [Lean, read] |
| `UpperTheory.Top.imprimitive` | `src/Development/AutomorphicArithmetic/CharacterBoxes/Imprimitive.lean:5` | Proposition 2.2: `ZeroFreeAll` $\implies$ `EveryCharacter` via `LFunction_changeLevel` and Euler-factor bounds. | [Lean, read] |
| `Claim.HalfPlane`, `Claim.Strip`, `Claim.Zeta` | `src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean:3,6,9` | Standalone Mathlib-only copies of `EveryCharacter`, `DirichletLZerosOnLine`, and `RiemannHypothesis`. | [Lean, read] |
| `Claim.factor_ne_zero` | `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:7` | Lemma 2.1: $1 - \psi(p)p^{-s} \neq 0$ for prime $p$ and $\Re s > 0$. | [Lean, read] |
| `Claim.prim_zero` | `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:23` | Lemma 2.5: $L(s,\chi) = 0$ on $0 < \Re s < 1$ implies $L(s,\chi^*) = 0$. | [Lean, read] |
| `Claim.gamma_ne_zero` | `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:35` | Lemma 2.3: $\gamma_\varphi(t) \neq 0$ for $\Re t > 0$. | [Lean, read] |
| `Claim.prim_reflect` | `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:42` | Lemma 2.4: for primitive $\psi$ and $0 < \Re s < 1$, $L(s,\psi) = 0 \implies L(1-s,\psi^{-1}) = 0$. | [Lean, read] |
| `Claim.strip` | `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:59` | Theorem 2.6: `Claim.HalfPlane` $\implies$ `Claim.Strip` for all moduli and characters. | [Lean, read] |
| `Claim.zeta`, `Claim.zeta_iff` | `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean:75,102` | Theorem 2.7 (second proof): `Claim.HalfPlane` $\implies$ `Claim.Zeta`, and definitional equality `Zeta ↔ RiemannHypothesis`. | [Lean, read] |
| `Formalism.VW.gammaFactor_ne_zero` | `src/Formalism/GammaFactorNonvanishing/CritLine.lean:6` | Lemma 2.3 (second copy, without `[NeZero N]`): $\gamma_\chi(s) \neq 0$ for $\Re s > 0$. | [Lean, read] |
| `Formalism.VW.critLine` | `src/Formalism/GammaFactorNonvanishing/CritLine.lean:11` | Theorem 2.6 (primitive case): `EveryCharacter` implies zeros of primitive $L(s,\chi)$ in $0 < \Re s < 1$ satisfy $\Re s = 1/2$. | [Lean, read] |
| `Formalism.VW.rh_of_every` | `src/Formalism/GammaFactorNonvanishing/CritLine.lean:29` | Specializes `EveryCharacter` at $N = 1$ and invokes `rh_of_right`. | [Lean, read] |
| `Formalism.VW.rh_of_right` | `src/Formalism/GammaFactorNonvanishing/RhOfRight.lean:5` | Theorem 2.7 (first proof): $\zeta(s) \neq 0$ on $\{\Re s > 1/2,\ s \neq 1\}$ implies `RiemannHypothesis` via `riemannZeta_one_sub`. | [Lean, read] |
| `allChi`, `rhOfAll`, `critAll`, `claimAll` | `src/Supplements/Kernels/MainTheorems.lean:7,9,11,15` | Top-level assembly feeding the five theorems of `src/Main.lean:4,6,8,10,12`. | [Lean, read] |

### 2.6.2 Mathlib declarations used by these proofs

| Declaration | File:line (Mathlib `0df444a`) | Mathematical content | Tag |
|---|---|---|---|
| `RiemannHypothesis`, `riemannZeta_zero`, `riemannZeta_def_of_ne_zero`, `completedRiemannZeta_one_sub`, `riemannZeta_one_sub` | `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185,151,154,106,178` | Global RH statement, $\zeta(0) = -1/2$, $\zeta(s) = \Lambda_\zeta(s)/\Gamma_{\mathbb R}(s)$ ($s \neq 0$), and symmetric/asymmetric functional equations of $\zeta$. | [Lean] |
| `riemannZeta_ne_zero_of_one_le_re`, `LFunction_ne_zero_of_one_le_re` | `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:411,398` | Classical non-vanishing on $\Re s \ge 1$ for $\zeta$ and Dirichlet $L$-functions. | [Lean] |
| `DirichletCharacter`, `changeLevel`, `level_one`, `changeLevel_one`, `conductor`, `conductor_dvd_level`, `conductor_ne_zero`, `conductor_one`, `IsPrimitive`, `primitiveCharacter`, `changeLevel_primitiveCharacter`, `primitiveCharacter_isPrimitive`, `conductor_inv`, `Odd`, `Even`, `even_or_odd` | `Mathlib/NumberTheory/DirichletCharacter/Basic.lean:40,66,202,220,246,251,255,259,292,307,310,314,405,533,536,538` | Dirichlet characters, conductors, primitive characters, level changes, inverse conductors, and parity. | [Lean] |
| `LFunction_modOne_eq`, `LFunction_changeLevel`, `gammaFactor`, `completedLFunction`, `LFunction_eq_completed_div_gammaFactor`, `IsPrimitive.completedLFunction_one_sub` | `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:67,150,207,224,259,284` | Identification $L(s, 1 \bmod 1) = \zeta(s)$, Euler-factor product under level change, $\gamma_\chi(s)$, $\Lambda(s,\chi)$, and the primitive functional equation. | [Lean] |

**Summary of the chapter.** Every Dirichlet $L$-function differs from its primitive $L$-function
only by finitely many Euler factors $1 - \chi^*(p) p^{-s}$, none of which vanishes on $\Re s > 0$
(Lemma 2.1) [Lean, read]. Hence non-vanishing of primitive $L$-functions on $\Re s > 1/2$
(`ZeroFreeAll`) implies non-vanishing of all Dirichlet $L$-functions on $\Re s > 1/2$
(`EveryCharacter`, Proposition 2.2) [Lean, read], and reflecting across $\Re s = 1/2$ via the
functional equations of $\Lambda(s,\chi^*)$ and of $\zeta(s)$ immediately yields all five theorems
of `src/Main.lean` (Theorems 2.6 and 2.7) [Lean, read]. The entire remainder of the book is therefore
devoted to proving `ZeroFreeAll`.
