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

A character modulo $N$ may require only a small table. If its values on the units
depend only on their images modulo a divisor $d$, we can store one value for each
unit modulo $d$ and recover all the other values by reduction and extension by zero.

For example, modulo $8$ the sign character from modulus $4$ gives equal values
at $1$ and $5$, and at $3$ and $7$. A character that distinguishes $1$ from $5$
needs modulus $8$. Modulo $12$, the sign characters from $3$ and $4$ are distinct,
and their product requires modulus $12$. We compute their tables below.

**Definition 2.1 (Level change, conductor, and primitive character).** For $N>0$
write $U_N=(\mathbb Z/N\mathbb Z)^\times$. A character modulo $N$ is a homomorphism
$U_N\to\mathbb C^\times$ extended by zero at nonunits. For $d\mid N$, reduction sends
a unit and its inverse to a unit and its inverse, giving $\pi_{N,d}:U_N\to U_d$.
The level change $\operatorname{changeLevel}_{d\mid N}(\psi)$ of a character modulo
$d$ is the composition $\psi\circ\pi_{N,d}$ on $U_N$, extended by zero at the
nonunits modulo $N$. In a commutative monoid a product is a unit exactly when both
factors are units, so extension by zero preserves multiplicativity. Two characters
agree everywhere as soon as they agree on units. Mathlib uses this construction
for any commutative monoid with zero as coefficient type, with unit values in its
group of units. [Lean, read] ([DirichletCharacter/Basic.lean:38–40, 64–77][cond-basic];
[MulChar/Basic.lean:134–192][cond-mulchar].)

We say $\chi$ *factors through* $d$ if $d\mid N$ and some character $\psi$ modulo
$d$ satisfies $\chi=\operatorname{changeLevel}_{d\mid N}(\psi)$. Let $S(\chi)$
be the set of all such $d$. The conductor $c=\operatorname{cond}(\chi)$ is the
minimum of $S(\chi)$ in the natural-number order. A character is *primitive* if
its conductor equals its modulus. [Lean, read] ([DirichletCharacter/Basic.lean:113–116, 233–246, 291–292][cond-basic].)

**Lemma (Lifting units and descending characters).** For $d\mid N$ and $N>0$,
$\pi_{N,d}$ is surjective. There is exactly one character inducing $\chi$ at each
admissible level $d$. A divisor $d$ is admissible exactly when $\chi$ equals $1$
on $\ker\pi_{N,d}$. [Lean, read] ([ZMod/Units.lean:23–71][cond-units];
[DirichletCharacter/Basic.lean:79–86, 136–158][cond-basic].)

*Proof.* Take a nonnegative representative $x$ of a unit modulo $d$, so
$\gcd(x,d)=1$. Let $k$ be the product of the primes dividing $N$ that do not divide
$x$, with empty product $1$. Then $y=x+kd$ lifts the given unit. For $p\mid N$,
if $p\nmid x$ then $p\mid k$ and $y\equiv x\pmod p$ is nonzero. If $p\mid x$,
then $p$ divides neither $d$ (by coprimality) nor $k$ (by construction), and
$y\equiv kd\pmod p$ is again nonzero. Hence $\gcd(y,N)=1$. This includes $d=1$.
Mathlib allows level $0$, with $\mathbb Z/0\mathbb Z=\mathbb Z$, but surjectivity
can fail there. Its units $1,-1$ miss two units under reduction to $U_5$.

An inducing character sends the identity to $1$, so $\chi$ must equal $1$ on the
kernel. Conversely, under that condition define $\psi(v)=\chi(u)$ for any lift
$u$ of $v\in U_d$. Two lifts differ by a kernel element, giving the same value.
Products of lifts lift products, so $\psi$ is multiplicative. Its extension by
zero induces $\chi$. Surjectivity forces these values for any inducing character
modulo $d$, giving uniqueness. $\square$

**Theorem (Existence, recovery, and primitivity).** The set $S(\chi)$ contains
$N$ and consists of positive divisors of $N$. There is a unique character
$\chi^*$ modulo $c=\operatorname{cond}(\chi)$ with
$\operatorname{changeLevel}_{c\mid N}(\chi^*)=\chi$, and $\chi^*$ is primitive.
[Lean, read] ([DirichletCharacter/Basic.lean:93–102, 142–143, 233–256, 273–319][cond-basic].)

*Proof.* Reduction to the same level is the identity. Taking $\chi$ itself as
witness puts $N$ in $S(\chi)$. By well-ordering of $\mathbb N$, the infimum in
Lean is attained. Membership supplies $c\mid N$, which implies $c>0$ for $N>0$.
It also supplies a character $\psi$ at level $c$ and an equation
$\chi=\operatorname{changeLevel}_{c\mid N}(\psi)$. Lean extracts divisibility and
chooses the character from this same existential witness. This choice defines
$\chi^*$. Reading the witness equation in reverse proves recovery, and the lifting
lemma gives uniqueness at the fixed level $c$.

Put $e=\operatorname{cond}(\chi^*)$. The same membership argument gives $e\mid c$
and a character at level $e$ inducing $\chi^*$. Reductions compose along
$e\mid c\mid N$. Hence two successive level changes agree with one, and the
character at level $e$ induces $\chi$, so $e\in S(\chi)$. Minimality gives
$c\le e$, and divisibility of the positive $c$ gives $e\le c$. Thus $e=c$.
The recovery equation in Lean needs no positivity. In the separate branch
$c=0$ of the primitivity proof, the conductor of $\chi^*$ is $0$ since its own
level $0$ belongs to its conductor set. $\square$

**Lemma (Divisibility minimum).** For $N>0$ and $d\mid N$, one has
$d\in S(\chi)$ if and only if $c\mid d$. Moreover, if a primitive character
modulo any $d\mid N$ induces $\chi$, then $d=c$ and that character is $\chi^*$
after identifying the two moduli. The divisibility statement follows the cited
Lean proof. The last assertion combines it with fixed-level uniqueness.
[Lean, read] ([DirichletCharacter/Basic.lean:100–107, 150–196, 333–360][cond-basic].)

*Proof.* Consider characters $\alpha$ modulo $a$ and $\beta$ modulo $b$, where
$a,b>0$, whose level changes to $ab$ agree. Put $g=\gcd(a,b)$. If $u\in U_a$
reduces to $1$ modulo $g$, the generalized Chinese remainder theorem supplies
$z\equiv u\pmod a$ and $z\equiv1\pmod b$, since $u\equiv1\pmod g$. Both
congruences ensure that $z$ is a unit modulo $ab$. Evaluating the common
character there gives $\alpha(u)=\beta(1)=1$, so $\alpha$ descends to $g$
by the kernel criterion.

Now take $d\in S(\chi)$ and an inducing character $\alpha$ modulo $d$. Compare
it with $\chi^*$ modulo $c$. Their lifts to $dc$ agree because both lift to the
character induced by $\chi$ at level $dcN$, and level change from $dc$ to the
positive level $dcN$ is injective by surjectivity on units. Applying the preceding
paragraph with $a=d$, $b=c$ makes $\alpha$ descend to $\gcd(d,c)$. Composing
that descent witness with the change from $d$ to $N$ shows
$\gcd(d,c)\in S(\chi)$. Thus $c\le\gcd(d,c)\le c$, so $c\mid d$.

Conversely, for $c\mid d\mid N$, every unit congruent to $1$ modulo $d$ also
reduces to $1$ modulo $c$. The kernel criterion gives descent to $d$ since
$\chi$ already descends to $c$. If $\alpha$ modulo $d$ induces $\chi$, then
injectivity of change from $d$ to $N$ identifies $\alpha$ with the lift of
$\chi^*$ to $d$: after further change, both give $\chi$. If $\alpha$ is
primitive, its descent to $c$ gives $d\le c$, and $c\mid d$ gives $c\le d$.
So $d=c$ and $\alpha=\chi^*$. $\square$

**Worked conductor table.** Both $U_8$ and $U_{12}$ have two independent
generators of order two. Use $3,5$ at level $8$ with product $7$, and
$5,7$ at level $12$ with product $11$. Each generator can take either sign.
Their product takes the product of the signs. [Expository]

| $N$ | Ordered units | Values in order | $S(\chi)$ | Conductor |
|---|---|---|---|---:|
| 8 | $1,3,5,7$ | $1,1,1,1$ | $\{1,2,4,8\}$ | 1 |
| 8 | $1,3,5,7$ | $1,-1,1,-1$ | $\{4,8\}$ | 4 |
| 8 | $1,3,5,7$ | $1,1,-1,-1$ | $\{8\}$ | 8 |
| 8 | $1,3,5,7$ | $1,-1,-1,1$ | $\{8\}$ | 8 |
| 12 | $1,5,7,11$ | $1,1,1,1$ | $\{1,2,3,4,6,12\}$ | 1 |
| 12 | $1,5,7,11$ | $1,-1,1,-1$ | $\{3,6,12\}$ | 3 |
| 12 | $1,5,7,11$ | $1,1,-1,-1$ | $\{4,12\}$ | 4 |
| 12 | $1,5,7,11$ | $1,-1,-1,1$ | $\{12\}$ | 12 |

A row descends just when its values are constant on the reduction fibers.
For both moduli, reduction to $1$ or $2$ has one fiber. Reduction from $8$
to $4$ pairs $1$ with $5$ and $3$ with $7$. Reduction from $12$ to either
$3$ or $6$ pairs $1$ with $7$ and $5$ with $11$. Reduction from $12$ to $4$
pairs $1$ with $5$ and $7$ with $11$. These tests exhaust the proper divisors.
For the conductor-$4$ row at level $12$, the inducing character takes $-1$
at the integer $3$ and its lift takes $0$ there. Recovery compares characters
at level $N$. Before level change their integer values agree on integers
coprime to $N$. [Expository]

**Notes.** On $U_N$, finiteness forces each character value to be a root of unity.
Thus its modulus is at most $1$ everywhere, and the inverse character agrees with
complex conjugation on units and extends by zero elsewhere. Numerical minimality alone cannot prove divisibility minimality,
even for a set of divisors closed upwards among divisors of $N$. At $N=12$ the
set $\{3,4,6,12\}$ has minimum $3$, which does not divide $4$. The common-lift
argument supplies the missing fact for $S(\chi)$ by putting $\gcd(d,c)$ back in
the set. The principal character at positive level descends to the unique
character of $U_1$ and so has conductor $1$. Inversion preserves the conductor
by a separate Mathlib result [Lean] ([DirichletCharacter/Basic.lean:405][cond-basic]).

[cond-basic]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/DirichletCharacter/Basic.lean
[cond-units]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/ZMod/Units.lean#L23-L71
[cond-mulchar]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/MulChar/Basic.lean#L134-L192

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

#### 2.3.2.1 Why Gamma has no zeros in the right half-plane

The integral for $\Gamma(z)$ has a strictly positive integrand when $z$ is positive real. When $z$ is nonreal, $x^{z-1}$ has a varying phase, so the integral calls for a different argument. Even Euler's limit of nonzero finite quotients could in principle be zero. The fixed Mathlib proof pairs two Euler quotients, at $z$ and $1-z$. Their denominator becomes a finite sine product, whose limit is known explicitly. The right-half-plane result is then a specialization of the resulting zero exclusion away from the poles. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:374–457`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L374-L457)

**Examples.** For positive $x$ we use $x^z=\exp(z\log x)$ with the real logarithm of $x$. At $z=1$, the integral gives $\int_0^\infty e^{-x}\,dx=1$. At $z=2$, integration by parts gives $\int_0^\infty xe^{-x}\,dx=1$. At $z=1/2$, substituting $x=u^2$ gives $\Gamma(1/2)=2\int_0^\infty e^{-u^2}\,du$. The square of this positive quantity is the integral of $e^{-(u^2+v^2)}$ on the plane. In polar coordinates this is $2\pi \int_0^\infty re^{-r^2}\,dr=\pi$, so $\Gamma(1/2)=\sqrt{\pi}$. Consequently $\Gamma_{\mathbb R}(1)=1$ and $\Gamma_{\mathbb R}(2)=1/\pi$. At the argument $1/2$ of the archimedean factor, the definition instead gives $\Gamma_{\mathbb R}(1/2)=\pi^{-1/4}\Gamma(1/4)$. The factor uses Gamma at half its argument. [DLMF 5.2.1](https://dlmf.nist.gov/5.2.E1) · [DLMF 5.4.6](https://dlmf.nist.gov/5.4.E6) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:307–325`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean#L307-L325)

**Definition.** For integers $n\ge 1$ set
$$
G_n(z)=\frac{n^z n!}{\prod_{j=0}^n(z+j)},\qquad
P_n(z)=\prod_{k=1}^n\left(1-\frac{z^2}{k^2}\right).
$$
Use $P_0(z)=1$. For the classical quotients we omit points with vanishing denominators. In Mathlib, `Complex.GammaSeq` is a total quotient. The book uses the same symbol $\Gamma$ for the classical function on its regular locus and explicitly specifies the Lean value when discussing poles. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:228–247`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L228-L247)

**Lemma (Gamma nonvanishing).** Let $\Gamma$ be given on $\Re z>0$ by Euler's integral
$$
\Gamma(z)=\int_0^\infty e^{-x}x^{z-1}\,dx
$$
and elsewhere off $0,-1,-2,\ldots$ by the recurrence $\Gamma(z+1)=z\Gamma(z)$. Then $\Gamma(z)\ne 0$ at every regular point. In particular, for every $s\in\mathbb C$ with $\Re s>0$, $\pi^{-s/2}\Gamma(s/2)\ne 0$. [Lean, read] for the local proof bodies identified below. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:427–457`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L427-L457) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean:39–45,66–74`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L66-L74)

**Proof.** First recover the Euler quotient from an integral. For $\Re u,\Re v>0$ put $B(u,v)=\int_0^1 t^{u-1}(1-t)^{v-1}\,dt$. The endpoint bounds come from the real exponents $\Re u-1$ and $\Re v-1$. Integrating the derivative of $t^u(1-t)^v$, whose endpoint values are zero, gives $u B(u,v+1)=v B(u+1,v)$. Also $B(u,1)=1/u$ by the primitive $t^u/u$. Induction on $n$ now gives $B(z,n+1)=n!/\prod_{j=0}^n(z+j)$ for $\Re z>0$. In the induction step the recurrence divides by $z$ and shifts to $z+1$. Substituting $x=nt$ gives
$$
G_n(z)=\int_0^n (1-x/n)^n x^{z-1}\,dx .
$$
The Jacobian and the scaling of $t^{z-1}$ together give $n^{-z}$, exactly cancelling $n^z$ in the quotient. The beta recurrence here follows directly from a derivative and uses no division by Gamma. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:60–101,141–215,228–269`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L141-L215)

Extend the integrand by zero outside $(0,n]$. For fixed $x>0$, its scalar weight tends to $e^{-x}$. On $(0,n]$ the bound $0\le (1-x/n)^n\le e^{-x}$ follows from $1-y\le e^{-y}$ for $0\le y\le 1$. Thus its modulus is dominated on $(0,\infty)$ by the integrable function $e^{-x}x^{\Re z-1}$. Dominated convergence gives $G_n(z)\to\Gamma(z)$. There is also an explicit error bound on this half-plane. For $0\le y\le 1/2$, integration of $t/(1-t)$ from $0$ to $y$ gives $0\le -\log(1-y)-y\le y^2$. For $0<x\le n/2$, taking $y=x/n$ and using $1-e^{-v}\le v$ for $v\ge0$ bounds the error in the scalar weight by $e^{-x}x^2/n$. For $x>n/2$ the error is at most $e^{-x}\le 4x^2e^{-x}/n$ for $n\ge1$. With $\sigma=\Re z>0$ this yields
$$
|G_n(z)-\Gamma(z)|\le \frac{4\Gamma(\sigma+2)}{n}.
$$
This bound makes the domination explicit. The Lean limit uses dominated convergence directly. For the examples above the finite quotients even give $G_n(1)=n/(n+1)$ and $G_n(2)=n^2/((n+1)(n+2))$. At $z=1/2$, the denominator is the product of the first $n+1$ odd integers divided by $2^{n+1}$. Thus $G_n(1/2)=2^{2n+2}\sqrt n\,n!(n+1)!/(2n+2)!$, tending to $\sqrt{\pi}$ by the same integral limit. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:271–343`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L271-L343) · [DLMF 5.8.1](https://dlmf.nist.gov/5.8.E1)

For a regular point $z$ outside the right half-plane, the quotient identity
$$
\frac{G_n(z+1)}{z}=\frac{n}{n+1+z}G_n(z)
$$
propagates convergence one step to the left, since the scalar on the right tends to $1$ and $\Gamma(z+1)/z=\Gamma(z)$. An integer number of steps reaches every such point from the right half-plane. Lean organizes these steps by induction on the truncated natural floor of $1-\Re z$. It handles $z=0$ separately, with the zero denominator in every quotient giving $G_n(0)=0$, and then the same induction also supplies the totalized limits at the negative integers. This shift is needed because even when $\Re z>0$, the reflected argument $1-z$ can lie outside the domain of the integral. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:237–247,334–361`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L334-L361)

We next prove the sine-product limit used in the pairing. Write $b=\pi/2$, and let
$$
I_m(z)=\int_0^b\cos(2zx)\cos^m x\,dx,\qquad C_m=I_m(0)>0.
$$
For $m\ge 2$ and $z\ne 0$, put $J=\int_0^b\sin(2zx)\sin x\cos^{m-1}x\,dx$. Integration by parts first gives $I_m(z)=mJ/(2z)$, with the boundary terms vanishing by $\sin 0=0$ and $\cos b=0$. Integrating $J$ by parts with the antiderivative $-\cos(2zx)/(2z)$ gives
$$
2zJ=m I_m(z)-(m-1)I_{m-2}(z).
$$
Here the derivative of $\sin x\cos^{m-1}x$ is $m\cos^m x-(m-1)\cos^{m-2}x$ and again the boundary terms vanish. Hence $(1-4z^2/m^2)I_m(z)=(m-1)I_{m-2}(z)/m$. The same recurrence at $z=0$ follows by continuity, or by integration by parts for $C_m$. Since $I_0(z)=\sin(\pi z)/(2z)$ and $C_0=\pi/2$, iteration over even $m$ gives
$$
\sin(\pi z)=\pi z P_n(z)\frac{I_{2n}(z)}{C_{2n}} .
$$
The product form uses multiplication by $1-z^2/k^2$ at each step, so the identity also holds where one of these factors vanishes. At $z=0$ both sides are zero. Lean uses the Wallis recurrence for $C_m$ in this induction. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean:41–238`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean#L41-L238)

For $0<\delta<b$, the proportion of the mass of $\cos^m x\,dx$ on $[\delta,b]$ is at most
$$
\frac{2b}{\delta}\left(\frac{\cos \delta}{\cos(\delta/2)}\right)^m .
$$
Indeed the numerator is at most $b\cos^m\delta$, and the denominator is at least $(\delta/2)\cos^m(\delta/2)$. For $f(x)=\cos(2zx)$ put $M=\max_{[0,b]}|f(x)-1|$. The error $|I_m(z)/C_m-1|$ is at most $\sup_{0\le x\le \delta}|f(x)-1|$ plus $M$ times the displayed mass bound. First choose $\delta$ by continuity at $0$, then let $m$ increase. The ratio tends to $1$. This proves the concrete concentration step that Lean supplies using a general theorem on powers of a continuous function with a unique maximum. Dividing by the ratio for sufficiently large $n$ gives $\pi z P_n(z)\to\sin(\pi z)$. The factor $\pi z$ comes from the initial integrals. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean:251–292`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Trigonometric/EulerSineProd.lean#L251-L292) · [DLMF 4.22.1](https://dlmf.nist.gov/4.22.E1)

For $z\notin \mathbb Z$, pair the factors $z+k$ and $k-z$ for $1\le k\le n$. Their product is $k^2(1-z^2/k^2)$, so the product of the $k^2$ cancels $(n!)^2$. The endpoint factors are $z$ and $n+1-z$, while $n^z n^{1-z}=n$. Therefore
$$
G_n(z)G_n(1-z)=\frac{n}{n+1-z}\frac{1}{zP_n(z)}
\longrightarrow\frac{\pi}{\sin(\pi z)} .
$$
The reciprocal limit is legitimate because $zP_n(z)\to\sin(\pi z)/\pi$, which is nonzero for $z\notin \mathbb Z$. For instance $\sin(\pi z)=0$ forces $e^{2\pi iz}=1$, which by taking absolute values forces $\Im z=0$, and then $z\in \mathbb Z$. The two Euler limits identify the left-hand limit as $\Gamma(z)\Gamma(1-z)$, proving the reflection formula. Lean treats integer $z$ separately: one of the two totalized Gamma values is zero and the right-hand side divides by zero, so the totalized equality holds there too. For $z=1/2$ the reflection formula gives $\Gamma(1/2)^2=\pi$, with positivity fixing the same square root as the integral calculation. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:374–423`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L374-L423) · [DLMF 5.5.3](https://dlmf.nist.gov/5.5.E3)

For nonreal $z$, reflection shows $\Gamma(z)\Gamma(1-z)\ne 0$, so $\Gamma(z)\ne 0$. For positive real $z$ the integral is strictly positive. For real $z$ outside the positive axis and off the excluded integers, shift to positive real part and use the recurrence with nonzero factors. This is the split in `Complex.Gamma_ne_zero`, whose real branch uses `Complex.Gamma_ofReal` and `Real.Gamma_ne_zero`. The right-half-plane hypothesis excludes all $-m$ for $m\ge0$. Finally $\Re(s/2)=\Re s/2>0$ and $\exp((-s/2)\log\pi)\ne 0$. Their product with $\Gamma(s/2)$ in the definition gives the stated result. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:425–457`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L425-L457) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:419–420,443–455,490–520`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L490-L520) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean:66–71`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L66-L71)

**The excluded argument $0$.** Classically $\Gamma(z)=\Gamma(1+z)/z$ near $0$ with $\Gamma(1)=1$. The numerator is holomorphic there by local domination of the differentiated integral, using $x^{-1/2}|\log x|$ near zero and $e^{-x}x^{1/2}\log x$ at infinity on $|\Re z|<1/2$. Thus there is a simple pole of residue $1$. The factor $\pi^{-s/2}$ is regular with value $1$ at $0$, so $\Gamma_{\mathbb R}(s)$ has residue $2$ there. In Lean the defining shifted quotient at $z=0$ is $\Gamma(1)/0=0$, hence $\Gamma_{\mathbb R}(0)=0$. The assigned point value says nothing about the limit through the punctured neighborhood. In particular the analytic reciprocal extends with a zero at the pole, whereas the totalized Gamma itself is assigned zero at that same point. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:286–288,338–354`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L338-L354) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean:43–45,73–74`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean#L73-L74) · [DLMF §5.2(i)](https://dlmf.nist.gov/5.2#i)

**Use in the chapter.** In archive A2, `Formalism.VW.gammaFactor_ne_zero` applies `Complex.Gammaℝ_ne_zero_of_re_pos` at $s$ in even parity and at $s+1$ in odd parity. This supplies the nonzero denominator for passing from a zero of the uncompleted function to a zero of the completed function. The consumer is `src/Formalism/GammaFactorNonvanishing/CritLine.lean:6–9`, with the division step on lines 19–21. The archive SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

**Reading boundary.** All Mathlib links are fixed at `0df444a360eaa60ab8c11dca51a86af692955474`, the revision in A2's `lean/lake-manifest.json:5–14`. The [Lean, read] Gamma increment covers the beta recurrence and finite integral evaluation, the dominated-convergence step and shift of the Euler limit, the sine recurrence and its limit wrapper, the pairing and reflection, the real and nonreal zero exclusions, and the final Deligne factor. The explicit integral error and the concrete mass estimate are textbook derivations. The general concentration machinery beneath the sine limit, the Gamma integral foundations, and complex power and logarithm infrastructure remain [Lean]. DLMF records the Weierstrass product for $1/\Gamma$ as a separate classical formula. [Mathlib, `Mathlib/MeasureTheory/Integral/PeakFunction.lean:371`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/PeakFunction.lean#L371) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:66,87`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L66-L106) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean:35–39`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean#L35-L39) · [DLMF 5.8.2](https://dlmf.nist.gov/5.8.E2)

#### 2.3.2.2 The Beta integral and the Gamma product: total scale and proportion coordinates

Section 2.3.2.1 proved that $\Gamma$ has no zeros, and on the way it evaluated the Beta integral $B(z,n+1)$ at integer second arguments by a recurrence. It deliberately avoided the classical quotient $B(a,b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)$, because that quotient needs the nonvanishing of $\Gamma(a+b)$ as an input. Now that nonvanishing is available, we prove the quotient. The real content is a change of variables in the positive quadrant: a pair $(y,z)$ of positive numbers is recorded as a total scale $x=y+z$ and a proportion $t=y/(y+z)$. The product of two Euler integrals separates in these coordinates into a Gamma integral in $x$ and a Beta integral in $t$. The fixed Mathlib proof performs this change of variables in two steps, a shear with Jacobian $1$ and a dilation with Jacobian $x$, and this subsection follows that decomposition. The archive uses the resulting identity at integer parameters, where it evaluates polynomial moments on $[0,1]$. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:103–139`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L103-L139) · [Mathlib, `Mathlib/Analysis/Convolution.lean:944–998`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convolution.lean#L944-L998) · [DLMF 5.12.1](https://dlmf.nist.gov/5.12.E1)

**Examples.** Take $a=b=1/2$. The Beta integral is $\int_0^1 t^{-1/2}(1-t)^{-1/2}\,dt$. Substituting $t=\sin^2\theta$ with $0<\theta<\pi/2$ gives $dt=2\sin\theta\cos\theta\,d\theta$, and the integrand becomes $1/(\sin\theta\cos\theta)$. The integral is therefore $\int_0^{\pi/2}2\,d\theta=\pi$. On the Gamma side, $\Gamma(1/2)^2/\Gamma(1)=\pi$ by the value $\Gamma(1/2)=\sqrt\pi$ computed in Section 2.3.2.1. The identity proved below gives a second route to that value: $B(1/2,1/2)=\pi$ and positivity force $\Gamma(1/2)=\sqrt{\pi}$. Here the exponent $a+b-1$ equals $0$, so the scaled form of the Beta integral says that $\int_0^x y^{-1/2}(x-y)^{-1/2}\,dy=\pi$ for every $x>0$. Indeed $y=xt$ turns this into the unscaled integral, with the two factors $x^{-1/2}$ cancelling the Jacobian $x$. Next take $a=1$ and $b=2$. Then $B(1,2)=\int_0^1(1-t)\,dt=1/2$, while $\Gamma(1)\Gamma(2)/\Gamma(3)=1\cdot 1/2=1/2$. The scaled form reads $\int_0^x(x-y)\,dy=x^2/2$, and the exponent $a+b-1=2$ is visible. Integrating the scaled form against $e^{-x}$ over $(0,\infty)$ gives $\Gamma(3)/2=1=\Gamma(1)\Gamma(2)$, which is the identity in the shape the Lean proof produces first. [DLMF 5.12.2](https://dlmf.nist.gov/5.12.E2)

**Definition.** For $a,b\in\mathbb C$ with $\Re a>0$ and $\Re b>0$, the Beta integral is
$$
B(a,b)=\int_0^1 t^{a-1}(1-t)^{b-1}\,dt ,
$$
with $t^{a-1}=\exp((a-1)\log t)$ for the real logarithm of $t\in(0,1)$, and likewise for $(1-t)^{b-1}$. For $x>0$ the scaled Beta integral is $\int_0^x y^{a-1}(x-y)^{b-1}\,dy$. In Mathlib, `Complex.betaIntegral u v` is the totalized interval integral $\int_0^1 (t:\mathbb C)^{u-1}(1-t)^{v-1}\,dt$ for all complex $u,v$; outside the convergence region the Bochner integral of a non-integrable function is defined to be $0$, and every statement below carries the hypotheses $\Re u>0$ and $\Re v>0$. The forward convolution of two functions $f,g$ on $(0,\infty)$ is the function on $\mathbb R$ equal to $\int_0^x f(t)g(x-t)\,dt$ for $x>0$ and to $0$ for $x\le0$. Mathlib's `MeasureTheory.posConvolution f g L` is this function for a general continuous bilinear map $L$; we only use $L(u)(v)=uv$ on $\mathbb C$. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:60–61`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L60-L61) · [Mathlib, `Mathlib/Analysis/Convolution.lean:944–946`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convolution.lean#L944-L946)

**Lemma (dilation of the Beta integrand).** Let $a,b\in\mathbb C$ and $x>0$. Then
$$
\int_0^x y^{a-1}(x-y)^{b-1}\,dy = x^{a+b-1}\,B(a,b),
$$
where for $\Re a,\Re b>0$ both sides are absolutely convergent integrals, and in Mathlib the identity holds for the totalized integrals without any hypothesis on $a,b$. [Lean, read] [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:103–122`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L103-L122)

*Proof.* Substitute $y=xt$, so $dy=x\,dt$ and $t$ runs over $(0,1)$. For positive reals $x$ and $t$ and any complex exponent $c$, $(xt)^c=x^ct^c$, because both sides equal $\exp(c(\log x+\log t))$ with real logarithms. Hence $y^{a-1}=x^{a-1}t^{a-1}$ and $(x-y)^{b-1}=(x(1-t))^{b-1}=x^{b-1}(1-t)^{b-1}$. Collecting the powers of $x$ gives $x\cdot x^{a-1}x^{b-1}=x^{1+(a-1)+(b-1)}=x^{a+b-1}$, again by the addition rule for powers of the positive real $x$. The remaining integral in $t$ is $B(a,b)$. Absolute convergence for $\Re a,\Re b>0$ is the endpoint comparison of Section 2.3.2.1, transported along the dilation. Mathlib's proof rewrites $x^{a+b-1}$ as $x\cdot x^{a-1}x^{b-1}$, applies the change of variables lemma for interval integrals under division by $x$, and then matches the integrands pointwise on $(0,x]$ with the product rule for complex powers of nonnegative reals; the interval-integral substitution lemma is an identity of totalized integrals, which is why no convergence hypothesis appears. $\square$

**Lemma (shear and Fubini for the forward convolution).** Let $f,g:(0,\infty)\to\mathbb C$ be Bochner integrable. Then the function $H(x,y)=f(y)g(x-y)$ on $\{0<y<x\}$, extended by $0$ to the plane, is integrable on $\mathbb R^2$, the forward convolution $x\mapsto\int_0^x f(y)g(x-y)\,dy$ is integrable on $(0,\infty)$, and
$$
\int_0^\infty\!\!\left(\int_0^x f(y)\,g(x-y)\,dy\right)dx=\left(\int_0^\infty f\right)\left(\int_0^\infty g\right).
$$
[Lean, read] [Mathlib, `Mathlib/Analysis/Convolution.lean:948–998`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convolution.lean#L948-L998) · [Mathlib, `Mathlib/Analysis/Convolution.lean:272–289,845–850`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convolution.lean#L845-L850)

*Proof.* Extend $f$ and $g$ by zero to all of $\mathbb R$; call the extensions $f_+$ and $g_+$. For every real $x$, the integrand $f_+(y)g_+(x-y)$ vanishes unless $y>0$ and $x-y>0$, that is unless $0<y<x$. So for $x>0$ the two-sided convolution $\int_{\mathbb R}f_+(y)g_+(x-y)\,dy$ equals $\int_0^x f(y)g(x-y)\,dy$, the endpoints $y=0$ and $y=x$ being null, and for $x\le0$ it equals $0$. Thus the forward convolution of $f,g$ is the ordinary convolution of $f_+,g_+$, and the displayed identity is the statement that the integral of a convolution is the product of the integrals.

For that statement we need the integrability of $(x,y)\mapsto f_+(y)g_+(x-y)$ on the plane. This is the shear $(y,z)\mapsto(y+z,y)$ applied to the product function $f_+(y)g_+(z)$; the shear has Jacobian determinant $1$, so one expects the plane integral of the modulus to equal $\int|f|\int|g|$. The Mathlib argument reaches this through the slice criterion for product measures. The integrand is measurable because $(x,y)\mapsto x-y$ is measurable and preserves null sets in the required sense. For fixed $y$, the slice $x\mapsto f_+(y)g_+(x-y)$ is integrable with $\int|f_+(y)g_+(x-y)|\,dx=|f_+(y)|\int|g_+|$ by translation invariance of Lebesgue measure. The function $y\mapsto|f_+(y)|\int|g_+|$ is integrable since $f_+$ is. Hence the integrand is integrable on the product, and in particular the inner integral exists for almost every $x$ and defines an integrable function of $x$. Fubini's theorem now permits exchanging the order:
$$
\int_{\mathbb R}\int_{\mathbb R}f_+(y)g_+(x-y)\,dy\,dx=\int_{\mathbb R}f_+(y)\left(\int_{\mathbb R}g_+(x-y)\,dx\right)dy=\int_{\mathbb R}f_+(y)\,dy\int_{\mathbb R}g_+ ,
$$
using translation invariance once more in the inner integral and then pulling the constant out. Restricting the extended integrals to $(0,\infty)$ gives the claim. In Lean, `posConvolution_eq_convolution_indicator` performs the case analysis $y\le0$, $0<y<x$, $x\le y$ and the null endpoint, `Integrable.convolution_integrand` is the slice argument with the operator norm bound $\|L(u)(v)\|\le\|L\|\,\|u\|\,\|v\|$, `integral_convolution` is the exchange and translation step, and `integral_posConvolution` assembles them. $\square$

**Theorem (Beta–Gamma identity on the right half-plane).** Let $a,b\in\mathbb C$ with $\Re a>0$ and $\Re b>0$. Then $B(a,b)$ converges absolutely and
$$
\Gamma(a)\Gamma(b)=\Gamma(a+b)\,B(a,b),\qquad B(a,b)=\frac{\Gamma(a)\Gamma(b)}{\Gamma(a+b)} .
$$
[Lean, read] for the proof bodies identified below. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:124–139`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L124-L139) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:537–540`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L537-L540) · [DLMF 5.12.1](https://dlmf.nist.gov/5.12.E1)

*Proof.* Absolute convergence of $B(a,b)$ is the endpoint estimate of Section 2.3.2.1: the modulus of the integrand is $t^{\Re a-1}(1-t)^{\Re b-1}$, which is integrable near $0$ because $\Re a-1>-1$ and near $1$ because $\Re b-1>-1$. Set $f(y)=e^{-y}y^{a-1}$ and $g(z)=e^{-z}z^{b-1}$ on $(0,\infty)$. Each is Bochner integrable. The modulus of $f$ is $e^{-y}y^{\Re a-1}$, which is integrable on $(0,1]$ by the power comparison and on $(1,\infty)$ because $e^{-y}y^{\Re a-1}=o(e^{-y/2})$; the function is continuous on $(0,\infty)$, hence measurable. By definition of the Euler integral, $\int_0^\infty f=\Gamma(a)$ and $\int_0^\infty g=\Gamma(b)$, and also $\Gamma(a+b)=\int_0^\infty e^{-x}x^{a+b-1}\,dx$ since $\Re(a+b)>0$.

Apply the shear lemma to $f$ and $g$. For $0<y<x$ we have $f(y)g(x-y)=e^{-y}e^{-(x-y)}y^{a-1}(x-y)^{b-1}=e^{-x}y^{a-1}(x-y)^{b-1}$, because the exponential turns the sum $y+(x-y)=x$ into a product. Therefore
$$
\Gamma(a)\Gamma(b)=\int_0^\infty e^{-x}\left(\int_0^x y^{a-1}(x-y)^{b-1}\,dy\right)dx .
$$
By the dilation lemma the inner integral is $x^{a+b-1}B(a,b)$ for every $x>0$. The constant $B(a,b)$ comes out of the outer integral, leaving $\int_0^\infty e^{-x}x^{a+b-1}\,dx=\Gamma(a+b)$. This proves the product form. Since $\Re(a+b)>0$, Section 2.3.2.1 gives $\Gamma(a+b)\ne0$, and dividing yields the quotient form. In Lean, `Gamma_mul_Gamma_eq_betaIntegral` rewrites the three Gamma values as integrals, applies `integral_posConvolution` with the multiplication map, and then matches the integrands pointwise on $(0,\infty)$ using `betaIntegral_scaled` and the addition law of the exponential; `betaIntegral_eq_Gamma_mul_div` cancels $\Gamma(a+b)$ with `Gamma_ne_zero_of_re_pos`. The order of the files reflects the logical order: the product form is proved before any zero-freeness, and the quotient only afterwards. $\square$

**Remark (the composite change of variables).** The two lemmas compose to the single map $\Phi(x,t)=(xt,\,x(1-t))$ from $(0,\infty)\times(0,1)$ onto the open quadrant, with inverse $(y,z)\mapsto(y+z,\,y/(y+z))$. Its Jacobian matrix has rows $(t,\,x)$ and $(1-t,\,-x)$, with determinant $-xt-x(1-t)=-x$, so the area element is $dy\,dz=x\,dx\,dt$. The shear $(y,z)\mapsto(y+z,y)$ contributes the factor $1$ and the fibrewise dilation $y=xt$ contributes the factor $x$, which is how the factor $x$ in $x^{a+b-1}=x\cdot x^{a-1}x^{b-1}$ arises in the dilation lemma. In these coordinates the integrand $e^{-(y+z)}y^{a-1}z^{b-1}$ becomes $e^{-x}x^{a+b-1}\,t^{a-1}(1-t)^{b-1}$, a product of a function of $x$ and a function of $t$, and Fubini's theorem for this nonnegative-modulus integrand gives the identity in one stroke. The fixed Mathlib proof does not invoke a two-dimensional change of variables theorem; it uses translation invariance for the shear and a one-dimensional substitution for the dilation, and the Fubini step is applied to the sheared integrand. The textbook and the formal proof are the same computation organized differently. [Expository]

**Remark (the endpoint condition is sharp).** The hypotheses $\Re a>0$, $\Re b>0$ cannot be weakened to conditional convergence. Take $a=i$ and $b=1$. The integrand $t^{i-1}$ has modulus $t^{-1}$ on $(0,1)$, so it is not Bochner integrable, and the identity $\Gamma(i)\Gamma(1)=\Gamma(1+i)B(i,1)$ has no integral meaning on the right; Mathlib's totalized `betaIntegral i 1` is $0$ by the convention for non-integrable functions, while $\Gamma(i)\ne0$ by Section 2.3.2.1, so the equation is false there and the hypothesis of `Gamma_mul_Gamma_eq_betaIntegral` is doing real work. Even the improper integral does not help: for $0<\varepsilon<1$, $\int_\varepsilon^1 t^{i-1}\,dt=(1-\varepsilon^{\,i})/i=(1-e^{i\log\varepsilon})/i$, whose modulus oscillates between $0$ and $2$ as $\varepsilon\to0$ and has no limit. More generally, if $\Re a\le0$ then $|t^{a-1}(1-t)^{b-1}|\ge 2^{1-\Re b}\,t^{-1}$ on $(0,1/2]$ when $\Re b\ge1$, and $\ge t^{-1}$ there when $\Re b<1$, so the modulus is never integrable. The dilation lemma, by contrast, is an identity between two totalized integrals and survives, but it then relates two zeros. [Expository]

**Use in the archive.** Both archive consumers specialize the theorem to integer parameters and read off polynomial moments. In `src/Development/AbelianVarietyTheory/Definitions/Divisors/ChernFormSecondChernClass.lean:62–72`, the lemma `beta j` takes $a=b=j+1$ and obtains $\int_0^1(t(1-t))^j\,dt=(j!)^2/(2j+1)!$ from $\Gamma(j+1)=j!$ and $\Gamma(2j+2)=(2j+1)!$; it feeds the evaluation `aeval_pm` on lines 74–90 and, through it, `FlagBundleRegularBaseFirst.lean:52`. For $j=0$ the integral is $1=(0!)^2/1!$, and for $j=1$ it is $\int_0^1(t-t^2)\,dt=1/2-1/3=1/6=(1!)^2/3!$. In `src/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PBetaSum.lean:9–47`, `BetaSum.proof` takes $a=i+1$ and $b=D-i+1$ for $0\le i\le D$, converts the complex Beta integral to the real moment $\int_0^1 t^i(1-t)^{D-i}\,dt=i!\,(D-i)!/(D+1)!$, and multiplies by the binomial coefficient to get $\int_0^1\binom Di t^i(1-t)^{D-i}\,dt=1/(D+1)$, exported as `BetaSum.full` in `AssemblyBase.lean:273`. For $D=2$, $i=1$ the integrand is $2t(1-t)$ with integral $1/3$. Both consumers call `Complex.Gamma_mul_Gamma_eq_betaIntegral` directly, rather than the integer recurrence of Section 2.3.2.1, so the convolution route is the one actually on their chain. Whether these two files lie in the dependency closure of the main theorem is recorded in the chapters on heights and host geometry and is not re-derived here. The archive SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

**Reading boundary.** All Mathlib links are fixed at `0df444a360eaa60ab8c11dca51a86af692955474`. The [Lean, read] increment of this subsection covers `betaIntegral_scaled`, `Gamma_mul_Gamma_eq_betaIntegral` and `betaIntegral_eq_Gamma_mul_div` in `Beta.lean`, the forward-convolution block `posConvolution`, `posConvolution_eq_convolution_indicator`, `integrable_posConvolution` and `integral_posConvolution`, the exchange step `integral_convolution`, and the slice argument `Integrable.convolution_integrand` in `Convolution.lean`, together with the convergence proofs `Real.GammaIntegral_convergent` and `Complex.GammaIntegral_convergent` in `Basic.lean`. Named inputs retained at [Lean]: the product-measure criteria `integrable_prod_iff'` and `integral_integral_swap`, the translation lemma `integral_sub_right_eq_self`, the measurability transfer `quasiMeasurePreserving_sub_of_right_invariant`, the commutation `ContinuousLinearMap.integral_comp_comm`, the interval substitution `intervalIntegral.integral_comp_div`, the power laws `mul_cpow_ofReal_nonneg` and `cpow_add`, the representation `Gamma_eq_integral`, and the exponential-decay comparison `integrable_of_isBigO_exp_neg`. The composite Jacobian and the sharpness example are textbook derivations. This subsection does not develop the derivative of $\Gamma$ or the duplication formula, which Mathlib proves from the quotient form by analytic continuation in the same file. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:66–105,319`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L66-L105) · [Mathlib, `Mathlib/Analysis/Convolution.lean:264–289`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convolution.lean#L264-L289) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:545–595`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L545-L595)

#### 2.3.2.3 Euler's integral for Gamma: convergence at both ends and what `Gamma_eq_integral` actually proves

Sections 2.3.2.1 and 2.3.2.2 both start from the sentence "for $\Re s>0$, $\Gamma(s)=\int_0^\infty e^{-x}x^{s-1}\,dx$, an absolutely convergent integral." In §2.3.2.2 this sentence carried real weight: the proof of $\Gamma(a)\Gamma(b)=\Gamma(a+b)B(a,b)$ needed the two integrands $e^{-y}y^{a-1}$ and $e^{-z}z^{b-1}$ to be Bochner integrable on $(0,\infty)$ before the shear and Fubini lemma could be applied, and it needed each of the three Gamma values to be literally equal to its Euler integral. In the pinned Mathlib these are two separate theorems, `Complex.GammaIntegral_convergent` and `Complex.Gamma_eq_integral`, and the second is not a definition: Mathlib's `Complex.Gamma` is defined for every complex number by a recurrence from the integral, and the statement that the recursive definition agrees with the integral on the half-plane of convergence has a proof. This subsection reads those two proofs. The integral has two dangerous ends. Near $x=0$ the power $x^{\Re s-1}$ is unbounded when $\Re s<1$, and the exponent $\Re s-1>-1$ is exactly what makes it integrable. Near $x=\infty$ the power may grow, and the exponential $e^{-x}$ must beat it; the formal proof does this by comparing with $e^{-x/2}$. The complex power $x^{s-1}$ for positive real $x$ has modulus $x^{\Re s-1}$, which reduces the complex question to the real one. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:54–105`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L54-L105) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:248–319`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L248-L319) · [DLMF 5.2.1](https://dlmf.nist.gov/5.2.E1)

**Examples.** For $s=1$ the integrand is $e^{-x}$, bounded near $0$ and with $\int_0^\infty e^{-x}\,dx=1$; nothing is dangerous. For $s=1/2$ the integrand is $e^{-x}x^{-1/2}$, which blows up at $0$ like $x^{-1/2}$. Since $\int_0^1 x^{-1/2}\,dx=2x^{1/2}\big|_0^1=2$ is finite, the blow-up is harmless, and $e^{-x}\le1$ gives $\int_0^1 e^{-x}x^{-1/2}\,dx\le2$. For $x\ge1$ we have $x^{-1/2}\le1$, so $\int_1^\infty e^{-x}x^{-1/2}\,dx\le e^{-1}$. The two pieces are $\sqrt\pi\,\mathrm{erf}(1)\approx1.4936$ and $\sqrt\pi\,\mathrm{erfc}(1)\approx0.2788$, summing to $\sqrt\pi$ as computed in §2.3.2.1. For $s=3$ the integrand $e^{-x}x^2$ is bounded near $0$ but the power grows; here $x^2\le 2^2\cdot2!\,e^{x/2}$ for $x\ge0$, because $e^{x/2}\ge(x/2)^2/2!$, so $e^{-x}x^2\le8e^{-x/2}$, whose integral over $(1,\infty)$ is $16e^{-1/2}$. The value is $\Gamma(3)=2!=2$. Finally for $s=1+i$ the complex power enters: $x^{i}=e^{i\log x}$ lies on the unit circle for every $x>0$, so the integrand $e^{-x}x^{i}$ has modulus exactly $e^{-x}$, and the integral converges absolutely with $\int_0^\infty|e^{-x}x^i|\,dx=1$ even though the integrand spins infinitely often as $x\to0$. [DLMF 5.2.1](https://dlmf.nist.gov/5.2.E1) · [DLMF 5.4.1](https://dlmf.nist.gov/5.4.E1)

**Definition (Euler integral, complex powers of positive reals, and Mathlib's Gamma).** For $x>0$ and $c\in\mathbb C$ write $x^c=\exp(c\log x)$ with the real logarithm; for real $c$ this is the real power. For $s\in\mathbb C$ the *Euler integral* is
$$
\mathrm{G}(s)=\int_0^\infty e^{-x}x^{s-1}\,dx ,
$$
understood as a Bochner integral over $(0,\infty)$ with Lebesgue measure. In Mathlib, `Complex.GammaIntegral s` is this totalized integral `∫ x in Ioi 0, ↑(-x).exp * ↑x ^ (s - 1)`, defined for every $s$ and equal to $0$ when the integrand is not integrable; the exponential is written as the coercion of the real $e^{-x}$ and the power is the complex power `cpow` of the coercion of $x$, a choice the source records in a technical note because the three natural spellings of $e^{-x}$ are equal but not definitionally so. The function `Complex.Gamma` is *not* defined as $\mathrm{G}$. Mathlib first sets $\Gamma_0=\mathrm{G}$ and $\Gamma_{n+1}(s)=\Gamma_n(s+1)/s$ (`GammaAux`), and then defines
$$
\Gamma(s)=\Gamma_{N(s)}(s),\qquad N(s)=\lfloor 1-\Re s\rfloor_+ ,
$$
where $\lfloor\cdot\rfloor_+$ is the natural-number floor, equal to $0$ for nonpositive arguments. The index $N(s)$ is the number of unit shifts needed to move $s$ into the half-plane $\Re s>0$ where the integral converges, and division by $s$ at each shift is the recurrence $\Gamma(s)=\Gamma(s+1)/s$ run backwards; at $s=0,-1,-2,\dots$ one of the divisions is by $0$ and Lean's convention $z/0=0$ assigns the value $0$. The definition is marked irreducible, so even for $\Re s>0$, where $N(s)=0$, the equation $\Gamma(s)=\mathrm{G}(s)$ is a theorem (`Gamma_eq_integral`) and not an unfolding. The real Gamma function `Real.Gamma s` is the real part of $\Gamma(s)$. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:80–111`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L80-L111) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:248–290`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L248-L290) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:402–408`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L402-L408)

**Lemma (the zero end: integrable powers).** Let $r>-1$ and $c>0$. Then $x\mapsto x^r$ is integrable on $(0,c]$ with $\int_0^c x^r\,dx=c^{r+1}/(r+1)$, and for every $s\in\mathbb C$ with $\sigma=\Re s>0$ the function $e^{-x}x^{\sigma-1}$ is integrable on $(0,1]$ with $\int_0^1 e^{-x}x^{\sigma-1}\,dx\le1/\sigma$. [Lean, read] [Mathlib, `Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean:45–63`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean#L45-L63) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:66–71`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L66-L71)

*Proof.* On $(0,c)$ the function $F(x)=x^{r+1}/(r+1)$ has derivative $x^r$, since $r+1\neq0$, and $F$ is continuous on $[0,c]$ because $r+1>0$ makes $x^{r+1}\to0$ as $x\to0^+$; we set $F(0)=0$. The integrand $x^r$ is nonnegative. A nonnegative function on an open interval that is the derivative of a function continuous on the closed interval is integrable there, with integral equal to the difference of the boundary values (§2.3.2.4, Lemma B). Here one can see this through the monotone convergence of $\int_\varepsilon^c x^r\,dx=F(c)-F(\varepsilon)\to F(c)$ as $\varepsilon\to0^+$, the increasing limit of the truncated integrals being finite (§2.3.2.6, Theorem N(2) at the zero end); the formal criterion takes no such limit and instead bounds the integral of every simple function below $x^r$ by $F(c)-F(0)$. Hence $\int_0^c x^r\,dx=c^{r+1}/(r+1)$. For the second claim take $r=\sigma-1>-1$ and $c=1$; the factor $e^{-x}$ is continuous on $[0,1]$ with $0<e^{-x}\le1$, so the product $e^{-x}x^{\sigma-1}$ is measurable and dominated by the integrable $x^{\sigma-1}$, giving integrability and the bound $1/\sigma$. Mathlib's `intervalIntegrable_rpow'` is exactly the derivative argument through `integrableOn_deriv_of_nonneg` with the primitive $x^{r+1}/(r+1)$ supplied by `Real.hasDerivAt_rpow_const`; its hypothesis is the strict inequality $-1<r$, and the lemma is stated for arbitrary endpoints by splitting at $0$. `Real.GammaIntegral_convergent` then multiplies by the continuous $e^{-x}$ on $[0,1]$ (`ContinuousOn.mul`, with `continuousOn_id.neg.rexp`) and passes from the closed to the half-open interval, whose difference is the null set $\{0\}$. $\square$

**Lemma (the infinite end: exponential decay beats powers).** Let $r\in\mathbb R$. Then $e^{-x}x^{r}=o(e^{-x/2})$ as $x\to\infty$, and $x\mapsto e^{-x}x^{r}$ is integrable on $(1,\infty)$. More generally, if $f:\mathbb R\to\mathbb R$ is continuous on $[a,\infty)$ and $f(x)=O(e^{-bx})$ as $x\to\infty$ for some $b>0$, then $f$ is integrable on $(a,\infty)$. [Lean, read] [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:54–75`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L54-L75) · [Mathlib, `Mathlib/MeasureTheory/Integral/ExpDecay.lean:31–46`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/ExpDecay.lean#L31-L46) · [Mathlib, `Mathlib/MeasureTheory/Integral/Asymptotics.lean:136–140`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Asymptotics.lean#L136-L140)

*Proof.* The ratio of $e^{-x}x^{r}$ to $e^{-x/2}$ is $e^{-x/2}x^{r}$, the reciprocal of $e^{x/2}/x^{r}$. The quotient $e^{bx}/x^{r}$ tends to $+\infty$ for every $b>0$: writing $e^{bx}/x^{r}=\big(e^{x}/x^{r/b}\big)^{b}$ for $x>0$ reduces it to the case $b=1$, where $e^x/x^{r}\to\infty$ is the statement that the exponential outgrows every power. Its reciprocal tends to $0$, which is the little-o claim; in Mathlib this is `Gamma_integrand_isLittleO`, proved by `isLittleO_of_tendsto` from `tendsto_exp_mul_div_rpow_atTop` with $b=1/2$, after a `field` simplification of the ratio.

For the general statement, let $g(x)=e^{-bx}$. Then $g$ is integrable on $(a,\infty)$ for $a\in\mathbb R$: the function $-e^{-bx}/b$ has derivative $e^{-bx}\ge0$ and tends to $0$ as $x\to\infty$, so the half-line criterion of §2.3.2.4 (Theorem D), which does pass the truncated integrals to their monotone limit, gives integrability with $\int_a^\infty e^{-bx}\,dx=e^{-ba}/b$ (`exp_neg_integrableOn_Ioi`, through `integrableOn_Ioi_deriv_of_nonneg'`). Now $f$ is continuous on $[a,\infty)$, hence locally integrable there, and $|f(x)|\le Cg(x)$ for $x\ge X_0$. Integrability on $[a,\infty)$ is equivalent to local integrability together with integrability near the filter at infinity, and the latter is inherited from $g$ through the big-O bound (`IsBigO.integrableAtFilter`): on $[X_0,\infty)$ the modulus of $f$ is dominated by the integrable $Cg$, and on the compact $[a,X_0]$ local integrability suffices. This is `LocallyIntegrableOn.integrableOn_of_isBigO_atTop`, and `integrable_of_isBigO_exp_neg` specializes it to $g=e^{-bx}$ and finally drops the null endpoint $a$. Applied with $a=1$, $b=1/2$ and $f(x)=e^{-x}x^{r}$, which is continuous on $[1,\infty)$ because $x\ne0$ there, this gives the integrability of the Gamma integrand on $(1,\infty)$; this is the second half of `Real.GammaIntegral_convergent`. $\square$

*Remark (an explicit domination constant).* The big-O argument hides the constant. For the Gamma integrand one can make it explicit: choose an integer $n\ge\max(r,0)$; then for $x\ge1$ we have $x^{r}\le x^{n}$ and $e^{x/2}\ge(x/2)^n/n!$, hence $x^{r}\le2^nn!\,e^{x/2}$ and
$$
e^{-x}x^{r}\le2^nn!\,e^{-x/2}\quad(x\ge1),\qquad\int_1^\infty e^{-x}x^{r}\,dx\le2^{n+1}n!\,e^{-1/2}.
$$
For $r\le0$ take $n=0$ and the bound is $2e^{-1/2}\approx1.213$, consistent with the value $0.2788$ at $r=-1/2$ and $e^{-1}$ at $r=0$. This explicit bound is a textbook addition; the formal proof uses only the existence of the constant. [Expository]

**Lemma (complex powers of positive reals).** For $x>0$ and $c\in\mathbb C$, $|x^{c}|=x^{\Re c}$, and $x\mapsto x^{c}$ is continuous on $(0,\infty)$ as a map into $\mathbb C$. Consequently, for $s\in\mathbb C$,
$$
|e^{-x}x^{s-1}|=e^{-x}x^{\Re s-1}\qquad(x>0),
$$
and the complex integrand is measurable on $(0,\infty)$. [Lean, read] [Mathlib, `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:337–339`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L337-L339) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:87–105`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L87-L105)

*Proof.* Since $x>0$, its complex logarithm is the real $\log x$, with argument $0$. So $x^{c}=\exp(c\log x)$ and $|x^{c}|=\exp(\Re(c\log x))=\exp(\Re c\cdot\log x)=x^{\Re c}$. There is no branch ambiguity: the general formula $|z^{c}|=|z|^{\Re c}e^{-\arg z\cdot\Im c}$ (`norm_cpow_of_ne_zero`) has $\arg z=0$ here, which is how `norm_cpow_eq_rpow_re_of_pos` is proved. Continuity: the complex power $z\mapsto z^{c}$ is continuous at every $z$ off the closed negative real axis (the slit plane), in particular at every positive real, and composing with the continuous coercion $\mathbb R\to\mathbb C$ gives continuity of $x\mapsto x^{c}$ on $(0,\infty)$ (`continuousAt_cpow_const` with `ofReal_mem_slitPlane`). The factor $e^{-x}$ is continuous, so the product is continuous on $(0,\infty)$, hence strongly measurable on this measurable set. The modulus formula follows from $|e^{-x}|=e^{-x}$ and multiplicativity. $\square$

**Theorem (Euler's integral for Gamma).** Let $s\in\mathbb C$ with $\Re s>0$. Then $e^{-x}x^{s-1}$ is Bochner integrable on $(0,\infty)$, and Mathlib's recursively defined $\Gamma$ satisfies
$$
\Gamma(s)=\int_0^\infty e^{-x}x^{s-1}\,dx ,\qquad\text{so that}\qquad|\Gamma(s)|\le\int_0^\infty e^{-x}x^{\Re s-1}\,dx=\Gamma(\Re s).
$$
For real $s>0$ the same integral is the real Gamma function, and it is strictly positive. [Lean, read] for the proof bodies identified below. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:87–105`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L87-L105) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:146–238`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L146-L238) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:248–319`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L248-L319) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:402–408,443–455`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L402-L455) · [DLMF 5.2.1](https://dlmf.nist.gov/5.2.E1)

*Proof.* Put $\sigma=\Re s>0$. *Integrability.* By the lemma on complex powers, the integrand is measurable on $(0,\infty)$ and its modulus is the real function $e^{-x}x^{\sigma-1}$. Split $(0,\infty)=(0,1]\cup(1,\infty)$. On $(0,1]$ the zero-end lemma applies with $r=\sigma-1>-1$. On $(1,\infty)$ the infinite-end lemma applies with the same $r$. So the real function is integrable on $(0,\infty)$ (`Real.GammaIntegral_convergent`, which performs exactly this split with `Ioc_union_Ioi_eq_Ioi` and `integrableOn_union`). A measurable complex function whose modulus is integrable is Bochner integrable, which is `Complex.GammaIntegral_convergent`: it proves measurability from continuity as above, then rewrites finiteness of the integral of the norm (`hasFiniteIntegral_norm_iff`) and transfers it from the real case by the almost-everywhere identity of the two moduli on $(0,\infty)$ (`norm_cpow_eq_rpow_re_of_pos`). Thus $\mathrm{G}(s)$ is an honest integral.

*The recurrence for the integral.* For $X\ge0$ let $\mathrm{G}_X(s)=\int_0^X e^{-x}x^{s-1}\,dx$ (`partialGamma`). On $(0,X)$ the function $e^{-x}x^{s}$ has derivative $-e^{-x}x^{s}+s\,e^{-x}x^{s-1}$, using the derivative $s\,x^{s-1}$ of the complex power on the slit plane and the chain rule through the coercion; this function is continuous on $[0,X]$ since $\Re s>0$ gives $x^{s}\to0$ at $0$, and both terms of the derivative are integrable on $(0,X)$ by the integrability just proved at $s+1$ and at $s$. The fundamental theorem of calculus therefore gives
$$
\mathrm{G}_X(s+1)=s\,\mathrm{G}_X(s)-e^{-X}X^{s},
$$
the boundary term at $0$ vanishing because $0^{s}=0$ for $s\neq0$ (`partialGamma_add_one`). As $X\to\infty$, $\mathrm{G}_X(s)\to\mathrm{G}(s)$ and $\mathrm{G}_X(s+1)\to\mathrm{G}(s+1)$ because both integrands are integrable on $(0,\infty)$ (`tendsto_partialGamma`), while $|e^{-X}X^{s}|=e^{-X}X^{\sigma}\to0$ by the infinite-end lemma. Hence $\mathrm{G}(s+1)=s\,\mathrm{G}(s)$ for $\Re s>0$ (`GammaIntegral_add_one`).

*Agreement of the recursive definition with the integral.* Recall $\Gamma_0=\mathrm{G}$ and $\Gamma_{n+1}(s)=\Gamma_n(s+1)/s$. We claim: if $n$ is a natural number with $n>-\Re s$, then $\Gamma_n(s)=\Gamma_{n+1}(s)$. For $n=0$ the hypothesis is $\Re s>0$, and the claim $\mathrm{G}(s)=\mathrm{G}(s+1)/s$ is the recurrence just proved, divided by $s\neq0$. For the step from $n$ to $n+1$, the hypothesis $n+1>-\Re s$ gives $n>-\Re(s+1)$, so by induction $\Gamma_n(s+1)=\Gamma_{n+1}(s+1)$, and dividing both sides by $s$ gives $\Gamma_{n+1}(s)=\Gamma_{n+2}(s)$ (`GammaAux_recurrence2`, which runs the induction through the companion identity `GammaAux_recurrence1`: $\Gamma_n(s)=\Gamma_n(s+1)/s$ for $n>-\Re s$). Iterating the claim, $\Gamma_n(s)=\Gamma_m(s)$ whenever $m\ge n>-\Re s$: the value does not depend on the index once the index is large enough to shift $s$ into the half-plane of convergence. Mathlib's definition uses $N(s)=\lfloor1-\Re s\rfloor_+$, which satisfies $N(s)>-\Re s$ because $\lfloor y\rfloor_+>y-1$ for every real $y$. So for any $n>-\Re s$, $\Gamma(s)=\Gamma_{N(s)}(s)=\Gamma_{\max(n,N(s))}(s)=\Gamma_n(s)$ (`Gamma_eq_GammaAux`). Taking $n=0$, which is allowed precisely when $\Re s>0$, gives $\Gamma(s)=\Gamma_0(s)=\mathrm{G}(s)$. This is the entire proof of `Gamma_eq_integral`: one line applying `Gamma_eq_GammaAux s 0` to the hypothesis $0>-\Re s$. For $\Re s>0$ one has in fact $N(s)=0$, so no shift is performed; the content of the theorem is that the recursive definition is well posed, and that content is the integration by parts above.

*Modulus bound and the real case.* The inequality $|\int f|\le\int|f|$ for Bochner integrals together with the modulus lemma gives $|\Gamma(s)|\le\int_0^\infty e^{-x}x^{\sigma-1}\,dx$. For real $s>0$, the complex integrand is the coercion of the real one, so $\mathrm{G}(s)$ is real and equals the real integral (`GammaIntegral_ofReal`); hence `Real.Gamma s`, the real part of $\Gamma(s)$, equals the real Euler integral (`Real.Gamma_eq_integral`), which is the right-hand side above. Finally the real integrand is strictly positive on $(0,\infty)$, a set of positive measure, so the real integral is strictly positive (`Real.Gamma_pos_of_pos`). $\square$

**Hand calculation 1: $s=1/2$.** Here $\sigma-1=-1/2>-1$. Zero end: $\int_0^1 x^{-1/2}\,dx=2$ by the primitive $2x^{1/2}$, so $\int_0^1 e^{-x}x^{-1/2}\,dx\le2$. Infinite end: $x^{-1/2}\le1$ for $x\ge1$ gives $\int_1^\infty e^{-x}x^{-1/2}\,dx\le e^{-1}\approx0.368$, and the explicit constant with $n=0$ gives the weaker $2e^{-1/2}\approx1.213$. The little-o statement is visible: $e^{-x}x^{-1/2}/e^{-x/2}=e^{-x/2}x^{-1/2}\to0$. Since $N(1/2)=\lfloor1/2\rfloor_+=0$, Mathlib's $\Gamma(1/2)$ is the integral with no shift. The substitution $x=u^2$ of §2.3.2.1 evaluates it to $\sqrt\pi\approx1.7725$; numerically the two pieces are $\int_0^1\approx1.4936\le2$ and $\int_1^\infty\approx0.2788\le0.368$, as the bounds require. The recurrence check: $\Gamma(3/2)=\tfrac12\Gamma(1/2)=\sqrt\pi/2$, and indeed $\int_0^\infty e^{-x}x^{1/2}\,dx$ is, by $x=u^2$, $2\int_0^\infty u^2e^{-u^2}\,du=\sqrt\pi/2$ by one integration by parts. [DLMF 5.4.6](https://dlmf.nist.gov/5.4.E6)

**Hand calculation 2: $s=1+i$.** Here $\sigma-1=0$, so the modulus of the integrand is $e^{-x}x^{0}=e^{-x}$: the zero end is bounded (the lemma applies with $r=0$, giving $\int_0^1 e^{-x}\,dx=1-e^{-1}$) and the infinite end is dominated by $e^{-x}\le e^{-x/2}$ with constant $1$. So $\int_0^\infty|e^{-x}x^{i}|\,dx=1$ and the integral converges absolutely, although the integrand $e^{-x}(\cos\log x+i\sin\log x)$ oscillates without limit as $x\to0^+$; its modulus, not its phase, controls convergence. Since $N(1+i)=\lfloor0\rfloor_+=0$, $\Gamma(1+i)=\mathrm{G}(1+i)$ with no shift. The modulus bound of the theorem gives $|\Gamma(1+i)|\le\Gamma(1)=1$. The exact modulus follows from the pieces already read: the conjugation identity $\mathrm{G}(\bar s)=\overline{\mathrm{G}(s)}$ (`GammaIntegral_conj`, from $\overline{x^{s-1}}=x^{\bar s-1}$ for $x>0$) gives $\Gamma(1-i)=\overline{\Gamma(1+i)}$; the recurrence gives $\Gamma(1+i)=i\,\Gamma(i)$; and the reflection formula of §2.3.2.1 gives $\Gamma(i)\Gamma(1-i)=\pi/\sin(\pi i)=\pi/(i\sinh\pi)$. Multiplying, $|\Gamma(1+i)|^2=\Gamma(1+i)\Gamma(1-i)=i\,\Gamma(i)\Gamma(1-i)=\pi/\sinh\pi\approx0.2720$, so $|\Gamma(1+i)|\approx0.5216<1$. Numerically $\Gamma(1+i)\approx0.4980-0.1549\,i$, that is $\int_0^\infty e^{-x}\cos(\log x)\,dx\approx0.4980$ and $\int_0^\infty e^{-x}\sin(\log x)\,dx\approx-0.1549$. [DLMF 5.4.3](https://dlmf.nist.gov/5.4.E3) · [DLMF 5.5.3](https://dlmf.nist.gov/5.5.E3)

**Remark (the hypothesis $\Re s>0$ is sharp).** Let $s=it$ with $t\in\mathbb R$, so $\Re s=0$. The modulus of the integrand is $e^{-x}x^{-1}\ge e^{-1}x^{-1}$ on $(0,1]$, and $\int_\varepsilon^1 x^{-1}\,dx=-\log\varepsilon\to\infty$, so the integrand is not Bochner integrable and $\mathrm{G}(it)$ is the convention value $0$. The zero-end lemma fails exactly here: $r=-1$ is excluded by the strict hypothesis $-1<r$, and the primitive $x^{r+1}/(r+1)$ degenerates. Conditional convergence does not rescue the integral either. For $t\ne0$ write $\int_\varepsilon^1 e^{-x}x^{it-1}\,dx=\int_\varepsilon^1 x^{it-1}\,dx+\int_\varepsilon^1(e^{-x}-1)x^{it-1}\,dx$; the second integral converges absolutely as $\varepsilon\to0$ because $|e^{-x}-1|\le x$ cancels the $x^{-1}$, while the first equals $(1-\varepsilon^{it})/(it)=(1-e^{it\log\varepsilon})/(it)$, whose modulus oscillates between $0$ and $2/|t|$ and has no limit: at $\varepsilon=e^{-2\pi k/|t|}$ it is $0$ and at $\varepsilon=e^{-(2k+1)\pi/|t|}$ it is $2/|t|$. On the Lean side the contrast is stark: $\Gamma(it)\ne0$ for $t\ne0$ by the nonvanishing theorem of §2.3.2.1 (for instance $|\Gamma(i)|=|\Gamma(1+i)|\approx0.5216$), while `GammaIntegral (it)` is $0$, so `Gamma_eq_integral` is false at $s=it$ and its hypothesis is doing real work. At $s=0$ both sides happen to be $0$, the left by the convention at the pole and the right by the convention for non-integrable functions, a coincidence of two conventions rather than an identity of integrals. The recurrence `GammaIntegral_add_one` carries the same hypothesis for the same reason. [Expository]

**Remark (where this feeds §2.3.2.2).** The Beta–Gamma theorem of §2.3.2.2 consumed exactly two facts about Gamma: the Bochner integrability of $e^{-y}y^{a-1}$ and $e^{-z}z^{b-1}$ on $(0,\infty)$, which is the hypothesis of the shear and Fubini lemma, and the equalities $\Gamma(a)=\mathrm{G}(a)$, $\Gamma(b)=\mathrm{G}(b)$, $\Gamma(a+b)=\mathrm{G}(a+b)$. In the pinned proof of `Gamma_mul_Gamma_eq_betaIntegral` these appear as the two `GammaIntegral_convergent` arguments passed to `integral_posConvolution` and the three rewrites by `Gamma_eq_integral`. Both are now [Lean, read]. The proofs of the shear lemma, the dilation lemma, the Beta identity and the reflection and nonvanishing of §2.3.2.1 are cited and not re-read here. [Expository] [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:124–139`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L124-L139)

**Use in the archive.** Archive A2 calls `Complex.Gamma_eq_integral` directly in `src/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean:9–19`, where `PI.EF.norm_Gamma_le` proves $|\Gamma(w)|\le\Gamma(\Re w)$ for $\Re w>0$: it rewrites both sides as Euler integrals (`Complex.Gamma_eq_integral`, `Real.Gamma_eq_integral`), applies $|\int f|\le\int|f|$ (`norm_integral_le_integral_norm`), and matches the integrands with `norm_cpow_eq_rpow_re_of_pos`, which is the modulus bound of the theorem above. This lemma is read at `LGrowthGamma.lean:201`, `src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormInvGammaLeReflect.lean:27`, `src/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean:75,157` and `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCompletedHeckeLCMOneLePhragmenLindelof.lean:47`, where vertical-strip growth bounds for Gamma factors are assembled. Hand check at $w=1+i$: $|\Gamma(1+i)|\approx0.5216\le\Gamma(1)=1$; at $w=1/2$ the bound is an equality. Whether these files lie in the dependency closure of the main theorem is not re-derived here. The archive SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

**Reading boundary.** All Mathlib links are fixed at `0df444a360eaa60ab8c11dca51a86af692955474`, the revision in A2's `lean/lake-manifest.json:10`. The [Lean, read] increment of this subsection covers, in `Gamma/Basic.lean`, `Real.Gamma_integrand_isLittleO`, `Real.GammaIntegral_convergent`, `Complex.GammaIntegral_convergent`, `GammaIntegral`, `GammaIntegral_conj`, `GammaIntegral_ofReal`, `partialGamma`, `tendsto_partialGamma`, the two private integrability lemmas, `partialGamma_add_one`, `GammaIntegral_add_one`, `GammaAux`, `GammaAux_recurrence1`, `GammaAux_recurrence2`, `Gamma`, `Gamma_eq_GammaAux`, `Gamma_eq_integral`, `Real.Gamma`, `Real.Gamma_eq_integral` and `Real.Gamma_pos_of_pos`; in `ExpDecay.lean`, `exp_neg_integrableOn_Ioi` and `integrable_of_isBigO_exp_neg`; in `Integrability/Basic.lean`, `intervalIntegrable_rpow'`; in `Integral/Asymptotics.lean`, `LocallyIntegrableOn.integrableOn_of_isBigO_atTop`; in `Pow/Real.lean`, `norm_cpow_eq_rpow_re_of_pos`; and in `Pow/Asymptotics.lean`, `tendsto_exp_mul_div_rpow_atTop` and `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`. The derivative-of-nonnegative integrability criteria `integrableOn_deriv_of_nonneg` and `integrableOn_Ioi_deriv_of_nonneg'`, the improper-integral limit `intervalIntegral_tendsto_integral_Ioi` and the fundamental theorem `integral_eq_sub_of_hasDerivAt_of_le` are read in §2.3.2.4. Named inputs retained at [Lean]: the filter characterization `integrableOn_Ici_iff_integrableAtFilter_atTop` and `IsBigO.integrableAtFilter`, `ContinuousOn.locallyIntegrableOn`, the growth input `tendsto_exp_div_rpow_atTop`, the complex-power facts `continuousAt_cpow_const`, `norm_cpow_of_ne_zero`, `HasDerivAt.cpow_const` and `Real.hasDerivAt_rpow_const`, and the floor inequality `Nat.sub_one_lt_floor`. `Complex.Gamma_add_one` for general $s\ne0$ and the pole values are cited from §2.3.2.1. The explicit domination constant and the two hand calculations are textbook derivations; the numerical values were checked by a composite Simpson rule after the substitution $x=e^{u}$. This subsection does not develop the derivative of $\Gamma$ or the Bohr–Mollerup characterization, which Chapter 1 treats. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:54–105,146–238,248–319,402–408,443–455`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L54-L105) · [Mathlib, `Mathlib/MeasureTheory/Integral/ExpDecay.lean:31–46`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/ExpDecay.lean#L31-L46) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean:45–63`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean#L45-L63) · [Mathlib, `Mathlib/MeasureTheory/Integral/Asymptotics.lean:136–140`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Asymptotics.lean#L136-L140) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:337–339`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L337-L339) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:133–144`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L133-L144)

#### 2.3.2.4 Nonnegative derivatives and improper integrals: the integrability criteria behind both ends of Euler's integral

Section 2.3.2.3 reduced the convergence of Euler's integral to two model facts: for $r>-1$ the power $x^r$ is integrable on $(0,c]$, and for $b>0$ the exponential $e^{-bx}$ is integrable on $(a,\infty)$. Both functions are explicit derivatives, of $x^{r+1}/(r+1)$ and of $-e^{-bx}/b$, so the familiar calculation is the improper one: integrate over a truncated interval, subtract two values of the primitive, and move the truncation point to the end. In Mathlib, however, an integral over $(0,c]$ or over $(a,\infty)$ is a Bochner integral, defined without any limit and meaningful only when the integrand is integrable, that is when $\int\lvert f\rvert<\infty$. The two notions differ, and the file `IntegralEqImproper.lean` opens with the standard example $\sin x/x$ on $[1,\infty)$, whose truncated integrals converge although the function is not integrable. So §2.3.2.3 needed more than primitives. It needed a theorem turning a primitive into integrability, and it used two: `integrableOn_deriv_of_nonneg` on a bounded interval and `integrableOn_Ioi_deriv_of_nonneg'` on a half-line. This subsection reads them. Their content is that a nonnegative derivative is integrable as soon as its primitive is finite at the ends: continuous on the closed bounded interval, or convergent at infinity. Neither hypothesis can be dropped, and nonnegativity is not necessary for integrability. The two proofs also differ in kind. On a bounded interval the formal proof takes no limit at all: it bounds the integral of every simple function below the derivative by the difference of the boundary values, through a one-sided fundamental theorem of calculus that follows the proof of Theorem 7.21 in Rudin's *Real and Complex Analysis*. On a half-line the proof does let the truncated integrals converge, by monotone convergence along the filter $x\to\infty$. [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:13–76`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L13-L76) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:943–962`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L943-L962)

**Examples.** (1) On $(0,1]$ take $g(x)=2\sqrt x$. Then $g'(x)=x^{-1/2}\ge0$, the primitive extends continuously to $[0,1]$ with $g(0)=0$, and the truncated integrals $\int_\varepsilon^1x^{-1/2}\,dx=2-2\sqrt\varepsilon$ increase to $2=g(1)-g(0)$. (2) On $(0,1]$ take $g(x)=\log x$. Again $g'(x)=1/x\ge0$, but $g(x)\to-\infty$ as $x\to0^+$ and $\int_\varepsilon^1dx/x=-\log\varepsilon\to\infty$, so the derivative is not integrable: nonnegativity alone is not enough, the primitive must have a finite value at the end. (3) On $[0,1]$ take $g(x)=x^2\sin(x^{-2})$ with $g(0)=0$. This $g$ is continuous on $[0,1]$ and differentiable at every point, and $\int_\varepsilon^1g'=g(1)-g(\varepsilon)\to\sin1$; but $g'$ changes sign infinitely often near $0$ and $\int_0^1\lvert g'\rvert=\infty$, as computed in the remark on failures below. A finite primitive alone is not enough either; the sign matters. (4) On $(1/2,\infty)$ take $g(x)=-2e^{-x/2}$. Then $g'(x)=e^{-x/2}>0$, $g(x)\to0$, and the truncated integrals $2e^{-1/4}-2e^{-x/2}$ increase to $2e^{-1/4}$. Examples (1) and (4) are, before the factor $e^{-x}$ is attached, the two instances that the Gamma integral of §2.3.2.3 uses at $s=1/2$; the hand calculations below run them through the formal proofs.

**Definition (integrability, lower integrals, interval integrals, right derivatives, covers).** Let $\mu$ be Lebesgue measure on $\mathbb R$ and $S\subseteq\mathbb R$ a measurable set. For a function $h\ge0$ the *lower integral* $\int_Sh\,d\mu\in[0,\infty]$ is the supremum of $\int_S\varphi\,d\mu$ over simple functions $0\le\varphi\le h$ (`lintegral`). A function $f$ with values in a normed space is *integrable on $S$* (`IntegrableOn f S`) if it is almost everywhere strongly measurable on $S$ and $\int_S\lvert f\rvert\,d\mu<\infty$; the Bochner integral $\int_Sf$ is defined for integrable $f$ and set to $0$ otherwise. For real $a,b$ the interval integral is $\int_a^bf=\int_{(a,b]}f-\int_{(b,a]}f$, and $f$ is *interval integrable* on $a,b$ if it is integrable on $(a,b]$ and on $(b,a]$; for $a\le b$ the second set is empty. A real function $g$ has *right derivative* $g'(x)$ at $x$ if $(g(u)-g(x))/(u-x)\to g'(x)$ as $u\to x^+$ (`HasDerivWithinAt g (g' x) (Ioi x) x`); an ordinary derivative is in particular a right derivative. Finally, for a measure $\nu$ and a filter $l$ on an index set, a family of measurable sets $\varphi_i$ is an *a.e. cover* along $l$ (`AECover ν l φ`) if $\nu$-almost every point lies in $\varphi_i$ for all $i$ eventually along $l$. The only cover used below has $\nu$ equal to Lebesgue measure restricted to $(a,\infty)$, $l$ the filter `atTop` of the limit $x\to+\infty$ in $\mathbb R$, and $\varphi_x=(-\infty,x]$: every point $y$ lies in $\varphi_x$ as soon as $x\ge y$. The filter `atTop` on $\mathbb R$ is countably generated, by the sets $[n,\infty)$ with $n\in\mathbb N$. [Mathlib, `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:47–49`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L47-L49) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:89–99,152–157`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L89-L157)

**Lemma A (the one-sided fundamental theorem of calculus).** Let $a\le b$, let $g:\mathbb R\to\mathbb R$ be continuous on $[a,b]$ with a right derivative $g'(x)$ at every $x\in(a,b)$, and let $\varphi$ be integrable on $[a,b]$.

1. If $g'\le\varphi$ on $(a,b)$, then $g(b)-g(a)\le\int_a^b\varphi$.
2. If $\varphi\le g'$ on $(a,b)$, then $\int_a^b\varphi\le g(b)-g(a)$.
3. If $g'$ is integrable on $(a,b]$, then $\int_a^bg'=g(b)-g(a)$. The same holds for $g$ with values in a Banach space.

In parts 1 and 2 nothing is assumed about the integrability, or even the measurability, of $g'$; only the comparison function $\varphi$ is integrated. [Lean, read] [Mathlib, `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:968–1144`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L968-L1144)

*Proof.* Part 1 is first proved under the stronger assumption that the right derivative exists on $[a,b)$, including at $a$. Fix $\varepsilon>0$. By the Vitali–Carathéodory theorem there is a lower semicontinuous $G:\mathbb R\to(-\infty,\infty]$ with $\varphi<G$ everywhere, $G<\infty$ almost everywhere, $G$ integrable on $[a,b]$ and $\int_a^bG<\int_a^b\varphi+\varepsilon$ (`exists_lt_lowerSemicontinuous_integral_lt`, Theorem J of §2.3.2.5). Let $s$ be the set of $t\in[a,b]$ with $g(t)-g(a)\le\int_a^tG$. It is closed, because $t\mapsto g(t)-g(a)$ is continuous on $[a,b]$ by hypothesis and $t\mapsto\int_a^tG$ is continuous because $G$ is integrable. It contains $a$. Let $t\in s$ with $t<b$. Since $g'(t)\le\varphi(t)<G(t)$, choose a real $y$ with $g'(t)<y<G(t)$. Lower semicontinuity gives $G>y$ near $t$, hence $\int_t^uG\ge(u-t)y$ for $u>t$ close to $t$. The right derivative gives $(g(u)-g(t))/(u-t)<y$ for $u>t$ close to $t$, hence $g(u)-g(t)\le(u-t)y$. For such $u$,
$$g(u)-g(a)=\bigl(g(t)-g(a)\bigr)+\bigl(g(u)-g(t)\bigr)\le\int_a^tG+\int_t^uG=\int_a^uG ,$$
so $s$ contains points arbitrarily close to $t$ on its right. The real induction principle for closed sets (`IsClosed.Icc_subset_of_forall_exists_gt`) gives $s=[a,b]$, and at $t=b$ we get $g(b)-g(a)\le\int_a^bG<\int_a^b\varphi+\varepsilon$; now let $\varepsilon\to0$ (`sub_le_integral_of_hasDeriv_right_of_le_Ico`).

If the right derivative is given only on $(a,b)$ and $a<b$, apply the previous case on $[t,b]$ for each $t\in(a,b]$. The set of $t\in[a,b]$ with $g(b)-g(t)\le\int_t^b\varphi$ then contains $(a,b]$, and it is closed because $g$ is continuous on $[a,b]$ and $t\mapsto\int_t^b\varphi$ is continuous, so it contains the closure $[a,b]$, in particular $a$ (`sub_le_integral_of_hasDeriv_right_of_le`). This closure step is the only use of continuity at the left endpoint: no derivative is available at $a$, and the value $g(a)$ is reached as the limit of $g(t)$ for $t\to a^+$. Part 2 is part 1 for $-g$, $-g'$ and $-\varphi$ (`integral_le_sub_of_hasDeriv_right_of_le`). For part 3 apply parts 1 and 2 with $\varphi=g'$ (`integral_eq_sub_of_hasDeriv_right_of_le_real`). For vector-valued $g$, apply the real case to $L\circ g$ for every continuous linear functional $L$, which commutes with the integral, and conclude because such functionals separate points (`integral_eq_sub_of_hasDeriv_right_of_le`, through `SeparatingDual.eq_iff_forall_dual_eq`). The two-sided form `integral_eq_sub_of_hasDerivAt_of_le` restricts ordinary derivatives to right derivatives. $\square$

Rudin's proof of Theorem 7.21 has the same structure. It keeps a parameter $\eta>0$ where Lean chooses the intermediate value $y$, and it takes the last zero of $\int_a^xG-g(x)+g(a)+\eta(x-a)$ where Lean uses real induction. Rudin assumes differentiability at every point of $[a,b]$ and integrability of the derivative; the Lean form needs only right derivatives inside, continuity on the closed interval, and an integrable comparison function. [W. Rudin, *Real and Complex Analysis*, 3rd ed. (1987), Theorem 7.21, pp. 149–150, and Theorem 2.25, p. 56] [Expository]

**Lemma B (nonnegative derivatives on a bounded interval).** Let $a<b$, and let $g$ be continuous on $[a,b]$ with a right derivative $g'(x)\ge0$ at every $x\in(a,b)$. Then $g'$ is integrable on $(a,b]$, with
$$\int_{(a,b)}\lvert g'\rvert\,d\mu\le g(b)-g(a)\qquad\text{and}\qquad\int_a^bg'=g(b)-g(a).$$
The same holds when $g$ has an ordinary derivative at every point of $(a,b)$; if $a\ge b$ the set $(a,b]$ is empty and there is nothing to prove. [Lean, read] [Mathlib, `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1216–1272`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L1216-L1272)

*Proof.* The endpoint $b$ is a null set, so it suffices to prove integrability on $(a,b)$ (`integrableOn_Ioc_iff_integrableOn_Ioo`). *Measurability.* For an arbitrary function $g$, the function that assigns to $x$ the right derivative of $g$ at $x$ where it exists, and $0$ elsewhere, is Borel measurable (`aemeasurable_derivWithin_Ioi`, a named input). On $(a,b)$ it agrees with $g'$, because a right derivative is unique. Hence $g'$ is almost everywhere measurable on $(a,b)$. *The bound.* Suppose $\int_{(a,b)}\lvert g'\rvert>g(b)-g(a)$. Since the left side is a supremum over simple functions, there is a simple function $\varphi\ge0$ with $\varphi\le\lvert g'\rvert$ everywhere, $\int_{(a,b)}\varphi<\infty$ and $\int_{(a,b)}\varphi>g(b)-g(a)$; the finiteness of $\int\varphi$ is part of the statement and uses that the restricted measure is $\sigma$-finite (`exists_lt_lintegral_simpleFunc_of_lt_lintegral`, a named input). A simple function with finite integral is integrable, so $\varphi$ is integrable on $(a,b)$ and hence on $[a,b]$. Here the sign hypothesis is used, and only here: on $(a,b)$ we have $\lvert g'\rvert=g'$, so $\varphi\le g'$ there, and Lemma A(2) gives $\int_a^b\varphi\le g(b)-g(a)$, a contradiction. Therefore $\int_{(a,b)}\lvert g'\rvert\le g(b)-g(a)<\infty$, which together with measurability is integrability. The value is Lemma A(3). The version with ordinary derivatives (`integrableOn_deriv_of_nonneg`) restricts each derivative to a right derivative, and `intervalIntegrable_deriv_of_nonneg` allows either order of $a$ and $b$. $\square$

The proof contains no limit of truncated integrals. Each hypothesis enters at one identifiable place: continuity of $g$ on $[a,b]$ through Lemma A, the derivative through Lemma A and the measurability step, and the sign through $\lvert g'\rvert=g'$, which is what allows the simple functions below $\lvert g'\rvert$ to be compared with $g'$.

**Lemma C (from truncated integrals to integrability on a half-line).** Let $a\in\mathbb R$, and let $f:\mathbb R\to E$, with $E$ a normed space, be integrable on $(a,x]$ for every $x\in\mathbb R$. If $\int_a^x\lvert f\rvert\to I\in\mathbb R$ as $x\to\infty$, then $f$ is integrable on $(a,\infty)$, and $\int_{(a,\infty)}\lvert f\rvert=I$. [Lean, read] for integrability; the equality is the same limit read twice. [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:316–453,554–576`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L316-L576)

*Proof, followed through the formal chain on the actual filter.* Let $\nu$ be Lebesgue measure restricted to $(a,\infty)$ and $\varphi_x=(-\infty,x]$. (i) *The cover.* Each $\varphi_x$ is closed, hence measurable, and every $y$ lies in $\varphi_x$ for all $x\ge y$, so $(\varphi_x)$ is an a.e. cover for $\nu$ along `atTop` (`aecover_Iic` applied to the identity map, the order dual of `aecover_Ici`). Integrating against $\nu$ over $\varphi_x$ is integrating against $\mu$ over $(a,x]$, and for $x\ge a$ this is the interval integral $\int_a^x$ (`Measure.restrict_restrict`, `intervalIntegral.integral_of_le`); this is how `integrableOn_Ioi_of_intervalIntegral_norm_bounded` transports both hypotheses to the cover. (ii) *A bound.* A convergent function is eventually bounded, so $\int_a^x\lvert f\rvert\le I'$ for some $I'$ and all large $x$ (`integrableOn_Ioi_of_intervalIntegral_norm_tendsto` passes to this bound and uses nothing else about $I$). (iii) *Measurability.* Since `atTop` is countably generated there is a sequence $u_n\to\infty$; $f$ is almost everywhere strongly measurable on each $(a,u_n]$, and these countably many sets cover $\nu$-almost every point, so $f$ is $\nu$-almost everywhere strongly measurable (`AECover.aestronglyMeasurable`). (iv) *Monotone convergence.* The core claim is that $\int_{\varphi_x}\lvert f\rvert\,d\nu\to\int\lvert f\rvert\,d\nu$ in $[0,\infty]$ as $x\to\infty$ (`AECover.lintegral_tendsto_of_countably_generated`). For a countably generated filter it suffices to check the limit along every sequence $u_n\to\infty$ (`tendsto_of_seq_tendsto`). A given sequence need not increase, so Lean squeezes $\varphi_{u_n}$ between the increasing sets
$$\bigcap_{k\ge n}\varphi_{u_k}=\Bigl(-\infty,\inf_{k\ge n}u_k\Bigr]\qquad\text{and}\qquad\bigcup_{k\le n}\varphi_{u_k}=\Bigl(-\infty,\max_{k\le n}u_k\Bigr],$$
both again a.e. covers (`biInter_Ici_aecover`, `biUnion_Iic_aecover`). For an increasing cover $\psi_n$ the functions $1_{\psi_n}\lvert f\rvert$ increase with $n$ and converge $\nu$-almost everywhere to $\lvert f\rvert$, for these covers at every point (`ae_tendsto_indicator`), and the monotone convergence theorem gives $\int1_{\psi_n}\lvert f\rvert\,d\nu\to\int\lvert f\rvert\,d\nu$ (the private `lintegral_tendsto_of_monotone_of_nat`, which calls `lintegral_tendsto_of_tendsto_of_monotone`, read in §2.3.2.6). The sandwich then gives the limit along $u_n$ (`AECover.lintegral_tendsto_of_nat`). For the natural choice $u_n=n$ both envelopes equal $(-\infty,n]$, and the whole step is the monotone convergence theorem for $1_{(a,n]}\lvert f\rvert$. (v) *Conclusion.* By (ii) and (iv), $\int\lvert f\rvert\,d\nu$ is the limit of quantities eventually at most $I'$, so it is at most $I'<\infty$ (`AECover.integrable_of_lintegral_enorm_bounded`, reached from the Bochner form through `AECover.integrable_of_integral_norm_bounded`, which rewrites each $\int_{\varphi_x}\lvert f\rvert$ as a lower integral by `integral_eq_lintegral_of_nonneg_ae`). With (iii) this is integrability. Since for $x\ge a$ the quantity $\int_{\varphi_x}\lvert f\rvert\,d\nu=\int_a^x\lvert f\rvert$ tends both to $\int\lvert f\rvert\,d\nu$ and to $I$, the two are equal. $\square$

**Theorem D (nonnegative derivatives on a half-line).** Let $a,l\in\mathbb R$, and let $g:\mathbb R\to\mathbb R$ be continuous at $a$ from the right, differentiable at every $x>a$ with $g'(x)\ge0$, and such that $g(x)\to l$ as $x\to\infty$. Then $g'$ is integrable on $(a,\infty)$ and
$$\int_{(a,\infty)}g'\,d\mu=l-g(a).$$
If $g$ is differentiable at every $x\ge a$, the continuity hypothesis holds automatically. Conversely, and without any sign condition, if $f$ takes values in a Banach space, is differentiable at every $x>a$, and $f'$ is integrable on $(a,\infty)$, then $f(x)$ converges as $x\to\infty$. Consequently, for $g$ as in the first sentence but without the assumption on its limit, the following are equivalent: $g'$ is integrable on $(a,\infty)$; $g$ has a finite limit at $\infty$; $g$ is bounded above on $(a,\infty)$. [Lean, read] for the direct statement, the value and the converse; the equivalence combines them with the monotonicity of $g$ [Expository]. [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:709–752,780–886`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L709-L886)

*Proof.* *Continuity on $[a,\infty)$.* At $a$ it is a hypothesis, and at each $x>a$ it follows from differentiability. *Each truncation.* For every $x$, $g$ is continuous on $[a,x]$ with derivative $g'\ge0$ on $(a,x)$, so Lemma B makes $g'$ integrable on $(a,x]$; for $x\le a$ the set is empty. This is the hypothesis "integrable on $(a,x]$ for every $x$" of Lemma C. *The truncated integrals.* For $x>a$, Lemma A(3) on $[a,x]$ and the sign give
$$\int_a^x\lvert g'\rvert=\int_a^xg'=g(x)-g(a)\longrightarrow l-g(a).$$
*Integrability.* Apply Lemma C with $f=g'$ and $I=l-g(a)$. In the source this is the single call `integrableOn_Ioi_of_intervalIntegral_norm_tendsto (l - g a) a _ tendsto_id _`, whose two arguments are the two previous steps, and step (iv) of Lemma C is where the truncations are passed to the limit. *Value.* Along the same cover, dominated convergence with dominating function $\lvert g'\rvert$ shows that $\int_a^xg'\to\int_{(a,\infty)}g'$ (`intervalIntegral_tendsto_integral_Ioi`, through `AECover.integral_tendsto_of_countably_generated` and the named input `tendsto_integral_filter_of_dominated_convergence`; for truncations §2.3.2.6 derives the same limit from monotone convergence and one subtraction, Theorem N(3)). The same quantities equal $g(x)-g(a)\to l-g(a)$, and limits are unique (`integral_Ioi_of_hasDerivAt_of_tendsto`, `integral_Ioi_of_hasDerivAt_of_nonneg`). So integrability comes from monotone convergence and the value from dominated convergence. The primed versions obtain continuity at $a$ from differentiability at $a$ (`integrableOn_Ioi_deriv_of_nonneg'`, `integral_Ioi_of_hasDerivAt_of_nonneg'`).

*The converse.* Let $\varepsilon>0$. The tails $\int_{[n,\infty)}\lvert f'\rvert$, $n\in\mathbb N$, decrease to the integral over $\bigcap_n[n,\infty)=\varnothing$, which is $0$ (`tendsto_setIntegral_of_antitone`, a named input). Choose an integer $N>a$ with tail below $\varepsilon$. For $x\ge N$, Lemma A(3) on $[N,x]$ gives $\lvert f(x)-f(N)\rvert=\bigl\lvert\int_{(N,x]}f'\bigr\rvert\le\int_{[N,\infty)}\lvert f'\rvert<\varepsilon$. So $f$ is Cauchy at infinity, and it converges because the target is complete (`tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`). For the equivalence, $g$ is nondecreasing on $[a,\infty)$ by the mean value theorem, so it converges in $(-\infty,\infty]$, with a finite limit exactly when it is bounded above. A finite limit gives integrability by the first part, and integrability gives a finite limit by the converse. $\square$

**Corollary E (the two model integrals of §2.3.2.3).**

1. Let $r>-1$ and $c\ge0$. Then $x^r$ is integrable on $(0,c]$ and $\int_0^cx^r\,dx=c^{r+1}/(r+1)$. Mathlib's `intervalIntegrable_rpow'` states more: $x^r$ is interval integrable on every $[a,b]$, where for $x<0$ the real power is $x^r=e^{r\log\lvert x\rvert}\cos(r\pi)$.
2. Let $b>0$ and $a\in\mathbb R$. Then $e^{-bx}$ is integrable on $(a,\infty)$ and $\int_a^\infty e^{-bx}\,dx=e^{-ab}/b$ (`exp_neg_integrableOn_Ioi`).

[Lean, read] for the two integrability statements; the two values follow from Lemma A(3) and Theorem D applied to the same primitives [Expository]. [Mathlib, `Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean:45–67`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean#L45-L67) · [Mathlib, `Mathlib/MeasureTheory/Integral/ExpDecay.lean:30–46`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/ExpDecay.lean#L30-L46) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:66–75`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L66-L75)

*Proof, with the exact interfaces.* (1) Let $0\le c$ and apply Lemma B on $[0,c]$ to $g(x)=x^{r+1}/(r+1)$; if $c=0$ there is nothing to prove. *Continuity on $[0,c]$:* Lean uses `ContinuousOn.rpow_const`, whose side condition at each point is "$x\ne0$ or $0\le r+1$", and discharges the second alternative from $-1<r$. *Derivative on $(0,c)$:* `Real.hasDerivAt_rpow_const`, applicable because $x\ne0$, gives the derivative $(r+1)x^r$ of $x^{r+1}$, and after division by $r+1$ the simplification to $x^r$ uses $r+1\ne0$. *Sign:* $x^r\ge0$ for $x\ge0$ (`rpow_nonneg`). So the proof consumes exactly two facts about $r$, namely $0\le r+1$ and $r+1\ne0$, which together say $r>-1$. The value $g(c)-g(0)=c^{r+1}/(r+1)$ is Lemma A(3). For $c<0$ Lean reflects: on $(0,-c]$ one has $(-x)^r=\cos(r\pi)\,x^r$ (`Real.rpow_def_of_neg` with $\log(-x)=\log x$), so interval integrability on $[c,0]$ is the case $[0,-c]$ multiplied by the constant $\cos(r\pi)$ (`IntervalIntegrable.iff_comp_neg`), and a general $[a,b]$ is joined through $0$ (`IntervalIntegrable.trans`). In §2.3.2.3, `Real.GammaIntegral_convergent` calls this at $r=s-1$, which exceeds $-1$ because $s>0$, on $[0,1]$; it multiplies by the continuous $e^{-x}$ (`IntervalIntegrable.continuousOn_mul`) and passes from $[0,1]$ to $(0,1]$.

(2) Apply the primed form of Theorem D to $g(x)=-e^{-bx}/b$, which is differentiable everywhere with $g'(x)=e^{-bx}>0$. Lean builds the derivative by the chain rule (identity, multiplication by $b$, negation, exponential, negation, division by $b$) and simplifies $-\bigl(e^{-bx}\cdot(-b)\bigr)/b$ to $e^{-bx}$ using $b\ne0$. For the limit, $-bx\to-\infty$ because $-b<0$, so $e^{-bx}\to0$ and $g(x)\to-0/b=0$. Hence $l=0$ and $\int_{(a,\infty)}e^{-bx}=0-g(a)=e^{-ab}/b$. In §2.3.2.3 the consumer is `integrable_of_isBigO_exp_neg`, which uses the pair consisting of the set $(b,\infty)$ and `exp_neg_integrableOn_Ioi b h0` as its witness that $e^{-bx}$ is integrable at the filter `atTop`; the left endpoint of that set is the decay rate $b$ itself. `Real.GammaIntegral_convergent` calls it with $b=1/2$, so the instance on the Gamma chain is $e^{-x/2}$ on $(1/2,\infty)$. $\square$

**Hand calculation 1: $x^{-1/2}$ at the zero end.** This is the instance $r=-1/2$, $c=1$ that §2.3.2.3 uses at $s=1/2$. The primitive is $g(x)=x^{1/2}/(1/2)=2\sqrt x$. Lean's two side conditions read $r+1=1/2\ge0$, so $g$ is continuous at $0$ with $g(0)=0$, and $r+1=1/2\ne0$, so the derivative $\tfrac12x^{-1/2}$ of $x^{1/2}$, divided by $1/2$, is $x^{-1/2}$. Lemma B asserts $\int_{(0,1)}x^{-1/2}\le g(1)-g(0)=2$, and its proof tests this against simple functions below $x^{-1/2}$. For $0<q<1$ and $n\ge1$ consider the staircase
$$\varphi_{q,n}=\sum_{k=1}^nq^{-(k-1)/2}\,1_{(q^k,\,q^{k-1}]} .$$
It lies below $x^{-1/2}$, because $x\le q^{k-1}$ on the $k$-th step. Its integral is
$$\sum_{k=1}^nq^{-(k-1)/2}\bigl(q^{k-1}-q^k\bigr)=(1-q)\sum_{k=1}^nq^{(k-1)/2}=(1+\sqrt q)\bigl(1-q^{n/2}\bigr),$$
by $(1-q)/(1-\sqrt q)=1+\sqrt q$. Every such value is below $2$, as Lemma A(2) requires for a simple function below the derivative. Letting $n\to\infty$ gives $1+\sqrt q$, which is $1.7071$, $1.9487$, $1.9950$ and $1.9995$ for $q=1/2$, $0.9$, $0.99$ and $0.999$, and letting $q\to1$ gives $2$. So the lower integral of $x^{-1/2}$ over $(0,1)$ is exactly $2$, in agreement with Lemma A(3): $\int_0^1x^{-1/2}\,dx=g(1)-g(0)=2$. The route of §2.3.2.3 reaches the same number through truncations, $\int_\varepsilon^1x^{-1/2}\,dx=2-2\sqrt\varepsilon$, which equals $1.8$, $1.98$ and $1.998$ at $\varepsilon=10^{-2}$, $10^{-4}$ and $10^{-6}$; Lemma B never forms these. In the Gamma integrand at $s=1/2$, multiplying by the continuous factor $e^{-x}\in(0,1]$ gives $\int_0^1e^{-x}x^{-1/2}\,dx\le2$, with actual value $\sqrt\pi\,\mathrm{erf}(1)\approx1.4936$. One detail of the formal statement is worth seeing once: on the negative axis Mathlib's $x^{-1/2}$ equals $e^{-\frac12\log\lvert x\rvert}\cos(-\pi/2)=0$, so at $r=-1/2$ the reflected half of `intervalIntegrable_rpow'` integrates the zero function.

**Hand calculation 2: the exponential tail $e^{-x/2}$ on $(1/2,\infty)$.** This is the instance `exp_neg_integrableOn_Ioi (1/2) one_half_pos` on the Gamma chain. The primitive is $g(x)=-e^{-x/2}/(1/2)=-2e^{-x/2}$, with $g'(x)=e^{-x/2}>0$ at every $x$ and $g(x)\to0=l$. For $x>1/2$ the truncated integrals are
$$\int_{1/2}^xe^{-t/2}\,dt=g(x)-g(1/2)=2e^{-1/4}-2e^{-x/2},$$
nondecreasing in $x$ and bounded by $l-g(1/2)=2e^{-1/4}\approx1.557602$, so in step (ii) of Lemma C one may take $I'=2e^{-1/4}$ itself. Along $u_n=n$ the cover sets are $(-\infty,n]\cap(1/2,\infty)=(1/2,n]$, the functions $1_{(1/2,n]}e^{-t/2}$ increase to $e^{-t/2}$ on $(1/2,\infty)$, and monotone convergence gives $\int_{(1/2,\infty)}e^{-t/2}=\lim_n\bigl(2e^{-1/4}-2e^{-n/2}\bigr)$. The terms at $n=1,2,4,8,16,32$ are $0.344540$, $0.821843$, $1.286931$, $1.520970$, $1.556931$ and $1.557601$. Theorem D gives the value $l-g(1/2)=2e^{-1/4}$. Back in §2.3.2.3, `integrable_of_isBigO_exp_neg` uses the set $(1/2,\infty)$ with this integrability as its witness at infinity and combines it with $e^{-x}x^{s-1}=O(e^{-x/2})$. At $s=1/2$ the comparison is explicit on $[1,\infty)$: $e^{-x}x^{-1/2}/e^{-x/2}=e^{-x/2}x^{-1/2}\le e^{-1/2}<1$, so $\int_1^\infty e^{-x}x^{-1/2}\,dx\le\int_1^\infty e^{-x/2}\,dx=2e^{-1/2}\approx1.2131$, the explicit constant of §2.3.2.3, against the actual value $\sqrt\pi\,\mathrm{erfc}(1)\approx0.2788$.

**Remark (what fails when a hypothesis is removed).** [Expository]

1. *A finite end without a finite value of the primitive.* For $r<-1$ the function $g(x)=x^{r+1}/(r+1)$ still has $g'(x)=x^r>0$ on $(0,c)$, and $r+1\ne0$, but $g(x)\to-\infty$ as $x\to0^+$. No continuous extension to $[0,c]$ exists, and Lean's side condition "$x\ne0$ or $0\le r+1$" fails at $x=0$. The derivative is not integrable: at $r=-3/2$, $\int_\varepsilon^1x^{-3/2}\,dx=2\varepsilon^{-1/2}-2$, which is $18$, $198$ and $19998$ at $\varepsilon=10^{-2}$, $10^{-4}$ and $10^{-8}$. At $r=-1$ the other side condition fails instead. In Lean the formula $x^0/0$ is the constant $1/0=0$, continuous on $[0,c]$ but with derivative $0\ne x^{-1}$; the true primitive $\log x$ tends to $-\infty$, and $\int_\varepsilon^1dx/x=-\log\varepsilon$. This is the failure behind the sharpness remark at $\Re s=0$ in §2.3.2.3.
2. *An infinite end without a finite limit.* For $b=0$ the derivative $1$ of $x$ is nonnegative and $\int_a^x1=x-a\to\infty$. For $b<0$ the primitive $-e^{-bx}/b$ tends to $+\infty$. In Lean, $0<b$ is what makes $-bx\to-\infty$, and $b\ne0$ is what makes the derivative of $-e^{-bx}/b$ equal to $e^{-bx}$; at $b=0$ the formula is again the constant $0$.
3. *A finite but discontinuous end.* Let $g(0)=0$ and $g=1$ on $(0,\infty)$. Then $g'=0$ on $(0,\infty)$ is integrable, while $g(1)-g(0)=1$ and $l-g(0)=1$: both value formulas fail, and so does Lemma A(1) with $\varphi=0$. Integrability itself survives a jump. For a nonnegative derivative, what integrability needs is that the primitive be bounded near the end: if $g$ is differentiable on $(a,b)$ with $g'\ge0$ and continuous at $b$, Lemma B on $[a+\varepsilon,b]$ gives $\int_{(a+\varepsilon,b]}g'=g(b)-g(a+\varepsilon)$, and monotone convergence as $\varepsilon\to0^+$ gives $\int_{(a,b]}g'=g(b)-\lim_{t\to a^+}g(t)$. The value formulas, by contrast, need continuity at the end, which is why `integral_Ioi_of_hasDerivAt_of_tendsto` carries the hypothesis `ContinuousWithinAt g (Ici a) a`.
4. *The sign removed on a bounded interval.* For $g(x)=x^2\sin(x^{-2})$ with $g(0)=0$, every hypothesis of Lemma B except the sign holds: $g$ is continuous on $[0,1]$ and differentiable at every point, with $g'(0)=0$ and $g'(x)=2x\sin(x^{-2})-2x^{-1}\cos(x^{-2})$ for $x\ne0$. The truncated integrals converge, $\int_\varepsilon^1g'=\sin1-\varepsilon^2\sin(\varepsilon^{-2})\to\sin1\approx0.8415$. But $g'$ is not integrable. The first term of $g'$ is bounded by $2$, and the substitution $u=x^{-2}$ turns the second into
$$\int_{U^{-1/2}}^1\frac{2\lvert\cos(x^{-2})\rvert}{x}\,dx=\int_1^U\frac{\lvert\cos u\rvert}{u}\,du\ge\sum_{k=1}^{m-1}\frac{2}{(k+1)\pi},$$
where $m=\lfloor U/\pi\rfloor$: on each $[k\pi,(k+1)\pi]\subseteq[1,U]$ the factor $1/u$ is at least $1/((k+1)\pi)$ and $\int_{k\pi}^{(k+1)\pi}\lvert\cos u\rvert\,du=2$. The sum diverges like $(2/\pi)\log U$; numerically the left side is $2.7434$, $4.2111$ and $5.6768$ for $U=10^2$, $10^3$ and $10^4$. Since $\lvert g'\rvert\ge2x^{-1}\lvert\cos(x^{-2})\rvert-2$, it follows that $\int_0^1\lvert g'\rvert=\infty$. Here the Lebesgue integral $\int_0^1g'$ does not exist, so Lemma A(3) does not apply, while the limit of truncations does. The example is classical. Tao's 245A Notes 5 states the variant $x^2\sin(x^{-3})$ on $[-1,1]$ as Exercise 94, with the same conclusion, and notes in Remark 96 that its derivative is Henstock–Kurzweil integrable although it is not Lebesgue integrable; the computation above is our verification of the square version. Gordon's 2016 article, whose title announces a bounded derivative that is not Riemann integrable, concerns the opposite phenomenon (a derivative that is Lebesgue integrable but not Riemann integrable, in the line of Volterra's 1881 construction cited in its bibliography); we could verify only its title and reference list, not its text, and do not attribute the present example to it.
5. *The sign removed on a half-line.* Let $g(x)=\int_1^x\frac{\sin t}{t}\,dt$, the example at the head of `IntegralEqImproper.lean`. Then $g'(x)=\sin x/x$ and $g(x)\to\pi/2-\mathrm{Si}(1)\approx0.624713$, where $\mathrm{Si}(1)\approx0.946083$. But $\int_1^{(m+1)\pi}\lvert\sin x\rvert/x\,dx\ge\sum_{k=1}^m2/((k+1)\pi)\to\infty$; numerically $3.8337$ and $5.2938$ for $m=100$ and $1000$, while the signed integrals are $0.627865$ and $0.625031$. Theorem D's converse is consistent with this: it only says that an integrable derivative forces a limit, not the other way round.
6. *Nonnegativity is not necessary.* The derivative $\cos x$ of $\sin x$ is integrable on $(0,2\pi)$ although it changes sign, and $e^{-x}\cos x$ is integrable on $(0,\infty)$ although it changes sign infinitely often. So "$g'\ge0$" is neither necessary for integrability nor, by items 1 and 2, sufficient. The correct statement is the equivalence in Theorem D: for a nonnegative derivative, integrability on a half-line is equivalent to a finite limit of the primitive, and on a bounded interval (item 3) to boundedness of the primitive near the ends.

**Remark (where truncation limits enter).** [Expository] The zero-end lemma of §2.3.2.3 describes the integrability of $x^r$ through the truncations $\int_\varepsilon^cx^r\,dx=F(c)-F(\varepsilon)$. That is a correct textbook proof: on $[\varepsilon,c]$ the integrand is continuous, Lemma A(3) gives the truncated values, and monotone convergence as $\varepsilon\to0^+$ gives $\int_{(0,c]}x^r=F(c)-\lim F(\varepsilon)=F(c)$. It is not, however, the formal proof. Lemma B never lets $\varepsilon\to0$: the boundary value $F(0)=0$ enters as a hypothesis, continuity of $F$ on $[0,c]$, and is used once, in the closure step of Lemma A at the left endpoint. In the formal chain, truncated integrals and monotone convergence appear only at the infinite end, in Lemma C, along the filter $x\to\infty$. The theorems agree; the proofs put the limit in different places. The truncation route at the zero end is also formalized, in the same file, as `integrableOn_Ioc_of_intervalIntegral_norm_bounded_left` through the cover `aecover_Ioc_of_Ioc` (§2.3.2.6, Theorem N(2)); the zero end of the Gamma chain does not use it. The gauge-integral proof of the same fundamental theorem in Tao's notes (Proposition 92) uses Cousin's lemma of Chapter 3 instead of Vitali–Carathéodory.

**Use in the archive.** Archive A2 calls these interfaces directly in 57 source files (65 call sites): the bounded-interval criterion in 3, the half-line criterion in 10, its value form in 11, `exp_neg_integrableOn_Ioi` in 22 and `intervalIntegrable_rpow'` in 18. Two of them sit in files read elsewhere in this book. In Chapter 4's `MeanSquareBounds/`, the lemma `dom_integrableOn` (`src/Development/AutomorphicArithmetic/MeanSquareBounds/GIntegral.lean:21–42`) proves that $1/(t\log^2t)$ is integrable on $(a,\infty)$ for $a>1$ by `integrableOn_Ioi_deriv_of_nonneg` with $g(t)=-1/\log t$ and $l=0$. It supplies continuity at $a$ from continuity of $\log$ at $a\ne0$ and $\log a\ne0$, the derivative by the chain rule, the sign by positivity, and the limit from $\log t\to\infty$. Hand check at $a=e$: $\int_e^\infty dt/(t\log^2t)=0-g(e)=1$; at $a=e^2$ the value is $1/2$. In Chapter 3, `poleData_integrable` (`src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/poleData.lean:91–112`, cited there for part (3) of Proposition 3.1) bounds $\lvert G_\chi(e^u)e^{-su}\rvert$ on $(0,\infty)$ by $\max(C,0)\,e^{-(\Re s-2)u}$ and takes integrability from `exp_neg_integrableOn_Ioi 0` with $b=\Re s-2>0$; at $s=3$ the majorant integral is $\max(C,0)\cdot1$. Whether the remaining call sites lie in the dependency closure of the main theorem is not re-derived here. The archive SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

**Reading boundary.** All Mathlib links are fixed at `0df444a360eaa60ab8c11dca51a86af692955474`. The [Lean, read] increment of this subsection covers, in `IntervalIntegral/FundThmCalculus.lean`, `sub_le_integral_of_hasDeriv_right_of_le_Ico`, `sub_le_integral_of_hasDeriv_right_of_le`, `integral_le_sub_of_hasDeriv_right_of_le`, `integral_eq_sub_of_hasDeriv_right_of_le_real`, `integral_eq_sub_of_hasDeriv_right_of_le`, `integral_eq_sub_of_hasDeriv_right`, `integral_eq_sub_of_hasDerivAt_of_le`, `integral_eq_sub_of_hasDerivAt`, `integrableOn_deriv_right_of_nonneg`, `integrableOn_deriv_of_nonneg` and `intervalIntegrable_deriv_of_nonneg`. In `IntegralEqImproper.lean` it covers the structure `AECover` with `aecover_Ici`, `aecover_Iic`, `ae_tendsto_indicator`, `AECover.aestronglyMeasurable`, `comp_tendsto`, `biUnion_Iic_aecover` and `biInter_Ici_aecover`; the private `lintegral_tendsto_of_monotone_of_nat` with `lintegral_tendsto_of_nat` and `lintegral_tendsto_of_countably_generated`; `integrable_of_lintegral_enorm_bounded` and `integrable_of_integral_norm_bounded`; `integral_tendsto_of_countably_generated`; `integrableOn_Ioi_of_intervalIntegral_norm_bounded` and `_tendsto`; `intervalIntegral_tendsto_integral_Ioi`; `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`; `integral_Ioi_of_hasDerivAt_of_tendsto` and its primed form; and `integrableOn_Ioi_deriv_of_nonneg`, `integral_Ioi_of_hasDerivAt_of_nonneg` and their primed forms. It also covers the two consumers `intervalIntegral.intervalIntegrable_rpow'` and `exp_neg_integrableOn_Ioi` as interfaces. The Vitali–Carathéodory theorem `exists_lt_lowerSemicontinuous_integral_lt` (`Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean:422`) is read in §2.3.2.5, and the monotone convergence theorem `lintegral_tendsto_of_tendsto_of_monotone` with `lintegral_iSup'` (`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:113,96`) in §2.3.2.6. Named inputs retained at [Lean]: the simple-function approximation `exists_lt_lintegral_simpleFunc_of_lt_lintegral` (`Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean:342`); measurability of right derivatives `aemeasurable_derivWithin_Ioi` (`Mathlib/Analysis/Calculus/FDeriv/Measurable.lean:764`); real induction `IsClosed.Icc_subset_of_forall_exists_gt` (`Mathlib/Topology/Order/IntermediateValue.lean:332`); the slope bound `HasDerivWithinAt.limsup_slope_le'` (`Mathlib/Analysis/Calculus/Deriv/Slope.lean:232`); continuity of primitives `continuousOn_primitive_interval` and `continuousOn_primitive_interval_left` and dominated convergence along a filter `tendsto_integral_filter_of_dominated_convergence` (`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:469,473,67`); `tendsto_setIntegral_of_antitone` (`Mathlib/MeasureTheory/Integral/Bochner/Set.lean:299`); `lintegral_coe_eq_integral`, `integral_eq_lintegral_of_nonneg_ae` and `norm_integral_le_integral_norm` (`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:694,483,934`); `SeparatingDual.eq_iff_forall_dual_eq`; and the real-power facts `Real.hasDerivAt_rpow_const`, `ContinuousOn.rpow_const` and `Real.rpow_def_of_neg` (`Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:435`, `Pow/Continuity.lean:278`, `Pow/Real.lean:95`). The staircase functions, the equivalences in Theorem D and in remark item 3, the two hand calculations, the failure examples and the archive hand checks are textbook derivations; their numerical values are floating-point checks with the standard library, not interval certificates. Classical sources: W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Theorem 1.26 (p. 21), Theorem 2.25 (p. 56) and Theorem 7.21 (pp. 149–150); R. A. Gordon, "A bounded derivative that is not Riemann integrable", *Math. Mag.* 89 (2016), 364–370, doi:10.4169/math.mag.89.5.364 (title and reference list verified through its Crossref record, text not consulted; cited in item 4 of the first remark for contrast, not as a source for the example); T. Tao, [245A Notes 5: Differentiation theorems](https://terrytao.wordpress.com/2010/10/16/245a-notes-5-differentiation-theorems/) (2010), Proposition 92 and Exercise 94. [Mathlib, `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:968–1272`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L968-L1272) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:89–886`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L89-L886) · [Mathlib, `Mathlib/MeasureTheory/Integral/ExpDecay.lean:30–46`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/ExpDecay.lean#L30-L46)

#### 2.3.2.5 The Vitali–Carathéodory majorant: lower semicontinuous upper bounds for integrable functions and what the one-sided fundamental theorem takes from them

The proof of Lemma A in §2.3.2.4 began with one sentence that was not proved there: for an integrable $\varphi$ on $[a,b]$ and $\varepsilon>0$ there is a lower semicontinuous $G$ with $\varphi<G$ at every point, $G<\infty$ almost everywhere, $G$ integrable, and $\int_a^bG<\int_a^b\varphi+\varepsilon$. Everything else in Lemma A was elementary: a closed set, a real induction, a slope bound. The sentence is the Vitali–Carathéodory theorem, `exists_lt_lowerSemicontinuous_integral_lt`, and this subsection reads its proof in the pinned Mathlib file `Bochner/VitaliCaratheodory.lean` (Sébastien Gouëzel, 2021) and explains why each of its five conclusions, and each of its hypotheses, is shaped the way the fundamental theorem needs. The question behind it is simple. An integrable function on $[0,1]$ can be discontinuous at every point. A continuous function cannot sit strictly above it with nearly the same integral (we show this below), and an inequality that holds only almost everywhere is useless at the one point where the real induction of Lemma A is stuck. Lower semicontinuity is the weakest regularity that survives both demands: it is preserved by sums and by series with nonnegative terms, indicators of open sets have it, and it is exactly the property "if $G(t)>y$ then $G>y$ near $t$" that the induction step uses. The price is that $G$ may take the value $+\infty$, on a null set, and that the measure must be $\sigma$-finite and regular.

On the Gamma chain the input to this theorem is concrete. Lemma B of §2.3.2.4 argued by contradiction with a nonnegative simple function $\varphi\le\lvert g'\rvert$ and fed $-\varphi$ into Lemma A(1) through Lemma A(2). So at $s=1/2$ the function handed to Vitali–Carathéodory is the negative of a staircase below $x^{-1/2}$, such as the $\varphi_{q,n}$ of §2.3.2.4, on the measure $\mu=\mathrm{vol}\mid_{[0,1]}$. Hand calculation 3 below follows that instance through the proof.

**Examples.** (1) Let $f=1_{\mathbb Q\cap[0,1]}$ on $[0,1]$. It is integrable with $\int f=0$ and discontinuous at every point of $[0,1]$. Any continuous $G>f$ satisfies $G>1$ on the dense set $\mathbb Q\cap[0,1]$, hence $G\ge1$ everywhere, hence $\int_0^1G\ge1$: the continuous majorants miss the integral by at least $1$. A lower semicontinuous majorant can do with an arbitrarily small error, as Hand calculation 1 shows, because an open set containing all rationals of $[0,1]$ can have measure as small as one likes. (2) Let $U\subset(0,1)$ be the open set removed in the construction of the Smith–Volterra–Cantor set, so $U$ is dense in $[0,1]$ and $\mu(U)=1/2$, and let $f=1_U$. Again every continuous $G>f$ has $\int_0^1G\ge1=\int f+\tfrac12$, while $f$ itself is lower semicontinuous (Hand calculation 2). (3) Let $f=1_K$ with $K=[0,1]\setminus U$ closed. Here continuous majorants with small excess exist, but a lower semicontinuous $v\le f$ must be $\le0$: the set $\{v>0\}$ is open and inside $K$, which has empty interior (Rudin, Exercise 2.6). Lower semicontinuity works from above and fails from below; for lower bounds the theorem uses upper semicontinuity. (4) Let $f(x)=\sum_n2^{-n}\lvert x-q_n\rvert^{-1/2}$ on $[0,1]$, where $(q_n)$ enumerates $\mathbb Q\cap[0,1]$, set to $0$ where the series diverges. Then $\int_0^1f\le2\sqrt2$, but every lower semicontinuous $g\ge f$ equals $+\infty$ on a dense $G_\delta$ set, by the Baire category theorem (Remark, item 3). This is why the theorem's $G$ takes values in $(-\infty,\infty]$ and is finite only almost everywhere.

**Definition (semicontinuity, regularity, lower integrals).** Let $X$ be a topological space with its Borel $\sigma$-algebra and $\mu$ a measure on it. A function $G:X\to L$ into a preorder is *lower semicontinuous* if for every $x$ and every $y<G(x)$ one has $G>y$ on a neighbourhood of $x$ (`LowerSemicontinuous`, `Mathlib/Topology/Semicontinuity/Defs.lean:293`); for $L\in\{\mathbb R,[0,\infty],[-\infty,\infty]\}$ this is the condition $\liminf_{x'\to x}G(x')\ge G(x)$, equivalently that $\{G>y\}$ is open for every $y$. *Upper semicontinuous* is the same with the order reversed. Indicators of open sets are lower semicontinuous, indicators of closed sets upper semicontinuous, both are preserved by finite sums, and a series $\sum_ig_i$ of lower semicontinuous functions with values in $[0,\infty]$ is lower semicontinuous (`lowerSemicontinuous_tsum`, `Semicontinuity/Basic.lean:720`). The measure $\mu$ is *outer regular* if every measurable $A$ and every $r>\mu(A)$ admit an open $U\supseteq A$ with $\mu(U)<r$ (`OuterRegular`, `Mathlib/MeasureTheory/Measure/Regular.lean:308`), and *weakly regular* if in addition every open $V$ and every $r<\mu(V)$ admit a closed $F\subseteq V$ with $\mu(F)>r$ (`WeaklyRegular`, `Regular.lean:324`); the second condition then holds for every measurable set of finite measure (`MeasurableSet.exists_isClosed_lt_add`, `Regular.lean:1031`). Lebesgue measure on $\mathbb R$ and its restrictions to intervals are weakly regular by the general instances for finite, or locally finite and second countable, Borel measures on metrizable spaces (`Regular.lean:1072,1081`). The measure is *$\sigma$-finite* if $X$ is a countable union of sets of finite measure. For $h:X\to[0,\infty]$ the *lower integral* $\int h\,d\mu$ is the supremum of $\int\varphi\,d\mu$ over simple functions $\varphi\le h$ (`lintegral`, `Lebesgue/Basic.lean:48`), and it suffices to use simple functions with finite values (`lintegral_eq_nnreal`, `Lebesgue/Basic.lean:158`). A real function is *integrable* if it is almost everywhere strongly measurable with $\int\lvert f\rvert<\infty$, and for a nonnegative integrable $f$ the Bochner integral is the real number $\bigl(\int f\,d\mu\bigr)$ with the lower integral on the right (`integral_eq_lintegral_of_nonneg_ae`, `Bochner/Basic.lean:483`).

Throughout, $\mu$ is a weakly regular Borel measure on $X$; where $\sigma$-finiteness is needed it is stated.

**Lemma F (open supersets for simple functions).** Let $\varphi:X\to[0,\infty)$ be a simple function and $\varepsilon\in(0,\infty]$. There is a lower semicontinuous $g:X\to[0,\infty)$ with $\varphi\le g$ everywhere and $\int g\,d\mu\le\int\varphi\,d\mu+\varepsilon$. [Lean, read] [Mathlib, `Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean:92–150`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean#L92-L150)

*Proof.* By the induction principle for simple functions (`SimpleFunc.induction`, `Function/SimpleFunc.lean:1260`) it suffices to treat $\varphi=c\,1_s$ with $s$ measurable and $c\ge0$, and to show that the property passes to sums. *The indicator case.* If $\int\varphi=\infty$, the constant $g=c$ works. If $c=0$, take $g=0$. Otherwise $\int\varphi=c\,\mu(s)<\infty$ forces $\mu(s)<\infty$, hence $\mu(s)<\mu(s)+\varepsilon/c$, and outer regularity gives an open $u\supseteq s$ with $\mu(u)<\mu(s)+\varepsilon/c$ (`Set.exists_isOpen_lt_of_lt`, `Regular.lean:359`). Put $g=c\,1_u$. It is lower semicontinuous because $u$ is open (`IsOpen.lowerSemicontinuous_indicator`), it dominates $\varphi$ because $u\supseteq s$, and $\int g=c\,\mu(u)\le c\,\mu(s)+\varepsilon$. *Sums.* If $g_1,g_2$ serve for $\varphi_1,\varphi_2$ with error $\varepsilon/2$ each, then $g_1+g_2$ is lower semicontinuous, dominates $\varphi_1+\varphi_2$, and $\int(g_1+g_2)\le\int\varphi_1+\int\varphi_2+\varepsilon$; the additivity of the lower integral uses measurability of $g_1$ (`lintegral_add_left`), which lower semicontinuous functions have. $\square$

**Lemma G (measurable functions, non-strict).** Let $f:X\to[0,\infty]$ be measurable and $\varepsilon\in(0,\infty]$. There is a lower semicontinuous $g:X\to[0,\infty]$ with $f\le g$ everywhere and $\int g\,d\mu\le\int f\,d\mu+\varepsilon$. [Lean, read] [Mathlib, `VitaliCaratheodory.lean:157–188`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean#L157-L188)

*Proof.* Write $f=\sum_{n\ge0}t_n$ pointwise, where $t_n=s_{n+1}-s_n$ are the increments of the standard increasing simple approximations $s_n\uparrow f$ (`eapproxDiff`, `tsum_eapproxDiff`, `Function/SimpleFunc.lean:925,942`); each $t_n$ is a simple function with finite values. Choose $\delta_n>0$ with $\sum_n\delta_n<\varepsilon$ (`ENNReal.exists_pos_sum_of_countable'`) and apply Lemma F to $t_n$ with error $\delta_n$, obtaining lower semicontinuous $g_n\ge t_n$. Put $g=\sum_ng_n$. Then $g\ge\sum_nt_n=f$; $g$ is lower semicontinuous as a series of lower semicontinuous nonnegative functions (`lowerSemicontinuous_tsum`); and, integrating the series termwise (`lintegral_tsum`, `Lebesgue/Add.lean:360`, which needs only almost everywhere measurability of the terms),
$$\int g=\sum_n\int g_n\le\sum_n\Bigl(\int t_n+\delta_n\Bigr)=\int f+\sum_n\delta_n\le\int f+\varepsilon. \qquad\square$$

This is Rudin's construction: his $f=\sum c_i\chi_{E_i}$ with $E_i\subseteq V_i$ open is the series of the $t_n$ with each step covered by an open set. The strict inequality and the measurable-only hypothesis are what the next two lemmas add.

**Lemma H (strict majorants; $\sigma$-finite measures).** Assume $\mu$ is $\sigma$-finite and let $\varepsilon\in(0,\infty]$.

1. If $f:X\to[0,\infty)$ is measurable, there is a lower semicontinuous $g:X\to[0,\infty]$ with $f<g$ at every point and $\int g\le\int f+\varepsilon$.
2. The same holds if $f$ is only almost everywhere measurable.
3. If $f:X\to[0,\infty)$ is integrable and $\varepsilon\in(0,\infty)$, the $g$ of part 2 can be taken with $g<\infty$ almost everywhere, with $x\mapsto g(x)$ (read as a real number where finite, $0$ elsewhere) integrable, and with $\int g\,d\mu<\int f\,d\mu+\varepsilon$ as Bochner integrals.

[Lean, read] [Mathlib, `VitaliCaratheodory.lean:194–298`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean#L194-L298)

*Proof.* (1) Since $\mu$ is $\sigma$-finite there is a measurable $w:X\to(0,\infty)$, positive at every point, with $\int w<\varepsilon/2$ (`exists_pos_lintegral_lt_of_sigmaFinite`, `Lebesgue/Countable.lean:227`: take disjoint measurable sets $s_n$ of finite measure covering $X$ and put $w=\delta_n$ on $s_n$ with $\sum_n\mu(s_n)\delta_n<\varepsilon/2$). Apply Lemma G to $f+w$ with error $\varepsilon/2$ to get $g\ge f+w>f$ everywhere, and $\int g\le\int f+\int w+\varepsilon/2\le\int f+\varepsilon$. This is the only place where $\sigma$-finiteness enters, and it enters only for the strict inequality: Lemma G needs no such hypothesis. (2) Let $f_0$ be a measurable function equal to $f$ almost everywhere, and $s$ a measurable null set containing $\{f\ne f_0\}$ (`exists_measurable_superset_of_null`). Part 1 gives $g_0>f_0$ with $\int g_0\le\int f_0+\varepsilon/2=\int f+\varepsilon/2$. Lemma G applied to the measurable function $\infty\cdot1_s$, whose lower integral is $\infty\cdot\mu(s)=0$, gives a lower semicontinuous $g_1\ge\infty\cdot1_s$ with $\int g_1\le\varepsilon/2$. Put $g=g_0+g_1$. Off $s$ we have $g\ge g_0>f_0=f$; on $s$ we have $g_1=\infty$, so $g=\infty>f$. And $\int g\le\int f+\varepsilon$. (3) Integrability of $f$ gives $\int f<\infty$ and almost everywhere measurability (`Integrable.aestronglyMeasurable`). Pick $\delta\in(0,\varepsilon)$ and apply part 2 with error $\delta$. Then $\int g\le\int f+\delta<\infty$, so $g<\infty$ almost everywhere (`ae_lt_top`), the real-valued reading of $g$ is measurable with finite integral, hence integrable, and its Bochner integral is $\bigl(\int g\bigr)\le\int f+\delta<\int f+\varepsilon$, the inequality now between real numbers (`ENNReal.toReal_mono`, `ENNReal.toReal_add`). $\square$

**Lemma I (upper semicontinuous minorants).** Let $f:X\to[0,\infty)$ with $\int f\,d\mu<\infty$ and $\varepsilon\in(0,\infty]$. There is an upper semicontinuous $g:X\to[0,\infty)$ with $g\le f$ everywhere and $\int f\le\int g+\varepsilon$. If moreover $f$ is integrable and $\varepsilon<\infty$, then $g$ is integrable and $\int f-\varepsilon\le\int g$ as Bochner integrals. No $\sigma$-finiteness is needed. [Lean, read] [Mathlib, `VitaliCaratheodory.lean:307–414`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean#L307-L414)

*Proof.* *Simple functions.* Let $\varphi=c\,1_s$ with $\int\varphi<\infty$ and $c\ne0$, so $\mu(s)<\infty$. Weak regularity gives a closed $F\subseteq s$ with $\mu(s)<\mu(F)+\varepsilon/c$ (`MeasurableSet.exists_isClosed_lt_add`), and $g=c\,1_F$ is upper semicontinuous (`IsClosed.upperSemicontinuous_indicator`), lies below $\varphi$, and $\int\varphi=c\,\mu(s)\le c\,\mu(F)+\varepsilon=\int g+\varepsilon$. For $c=0$ take $g=0$. Sums are handled as in Lemma F, with the finiteness hypothesis split between the two summands. *General $f$.* Since the lower integral is the supremum over finite-valued simple functions $\varphi\le f$ (`lintegral_eq_nnreal`) and $\int f<\infty$, there is such a $\varphi$ with $\int f\le\int\varphi+\varepsilon/2$; this is where the finiteness is used, and it is why the lower bound keeps only finitely many terms of Rudin's series where the upper bound keeps all of them. The simple case with error $\varepsilon/2$ gives $g\le\varphi\le f$ with $\int\varphi\le\int g+\varepsilon/2$, so $\int f\le\int g+\varepsilon$. *Bochner form.* If $f$ is integrable, $g\le f$ is integrable by domination, and the lower-integral inequality converts to the Bochner one because both lower integrals are finite. $\square$

**Theorem J (Vitali–Carathéodory, strict form).** Let $\mu$ be a weakly regular $\sigma$-finite Borel measure on $X$, let $f:X\to\mathbb R$ be integrable, and let $\varepsilon>0$. There is a function $G:X\to[-\infty,\infty]$ such that

1. $f(x)<G(x)$ for every $x\in X$;
2. $G$ is lower semicontinuous;
3. the real-valued reading of $G$ (its value where finite, $0$ elsewhere) is integrable;
4. $G<\infty$ almost everywhere;
5. $\int G\,d\mu<\int f\,d\mu+\varepsilon$, the left side being the integral of the function in item 3.

Symmetrically there is an upper semicontinuous $H<f$ everywhere with $H>-\infty$ almost everywhere, integrable reading, and $\int f<\int H+\varepsilon$. [Lean, read] [Mathlib, `VitaliCaratheodory.lean:422–518`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean#L422-L518)

*Proof.* Let $\delta=\varepsilon/2$ and split $f=f^+-f^-$ with $f^\pm=\max(\pm f,0)$, both nonnegative and integrable (`Integrable.real_toNNReal`). Lemma H(3) gives a lower semicontinuous $g_p:X\to[0,\infty]$ with $f^+<g_p$ everywhere, $g_p<\infty$ almost everywhere, integrable reading, and $\int g_p<\int f^++\delta$. Lemma I gives an upper semicontinuous $g_m:X\to[0,\infty)$ with $g_m\le f^-$ everywhere, integrable, and $\int f^--\delta\le\int g_m$. Define $G=g_p-g_m$ in $[-\infty,\infty]$; since $g_m$ is finite, $G=+\infty$ exactly where $g_p=+\infty$, and $G$ never equals $-\infty$.

*(1)* At each $x$, $f(x)=f^+(x)-f^-(x)<g_p(x)-g_m(x)$ because $f^+(x)<g_p(x)$ and $g_m(x)\le f^-(x)$; the subtraction is legitimate in $[-\infty,\infty]$ because neither term is $-\infty$ and the second is finite (`EReal.sub_lt_sub_of_lt_of_le`). *(2)* The map $[0,\infty]\to[-\infty,\infty]$ is continuous and monotone, so $g_p$ stays lower semicontinuous, and $-g_m$ is lower semicontinuous because $g_m$ is upper semicontinuous and negation reverses the order. Their sum is lower semicontinuous because addition on $[-\infty,\infty]$ is continuous at every pair of points except $(+\infty,-\infty)$ and $(-\infty,+\infty)$ (`LowerSemicontinuous.add'` with `EReal.continuousAt_add`, `Mathlib/Topology/Instances/EReal/Lemmas.lean:430–444`, whose two hypotheses $p_1\ne+\infty\lor p_2\ne-\infty$ and $p_1\ne-\infty\lor p_2\ne+\infty$ exclude exactly these two pairs). Both exclusions are needed: $(-n,n)$ and $(-n,2n)$ both tend to $(-\infty,+\infty)$ while their sums are $0$ and $n\to+\infty$, and $(n,-n)$ and $(2n,-n)$ do the same at $(+\infty,-\infty)$. This is the one place where the extended-real arithmetic needs care, and both hypotheses are met because the second coordinate $-g_m(x)$ is a real number at every $x$ (`EReal.continuousAt_add (by simp) (by simp)`, `VitaliCaratheodory.lean:494`). *(3) and (5)* Almost everywhere $g_p<\infty$, and there the reading of $G$ is the real number $g_p-g_m$ (`EReal.toReal_sub`). So the reading of $G$ is almost everywhere equal to the difference of two integrable functions, hence integrable, with
$$\int G=\int g_p-\int g_m<\Bigl(\int f^++\delta\Bigr)-\Bigl(\int f^--\delta\Bigr)=\int f+2\delta=\int f+\varepsilon,$$
using $\int f=\int f^+-\int f^-$ (`integral_eq_integral_pos_part_sub_integral_neg_part`, `Bochner/Basic.lean:559`). *(4)* $G<\infty$ wherever $g_p<\infty$, which is almost everywhere. For the symmetric statement apply the theorem to $-f$ and negate (`exists_upperSemicontinuous_lt_integral_gt`). $\square$

**How Lemma A consumes the five conclusions.** The call in `sub_le_integral_of_hasDeriv_right_of_le_Ico` (`FundThmCalculus.lean:974–975`) is `exists_lt_lowerSemicontinuous_integral_lt φ φint εpos` with the measure $\mu=\mathrm{vol}\mid_{[a,b]}$, since `IntegrableOn φ (Icc a b)` means integrability for that restricted measure. This measure is $\sigma$-finite and weakly regular: the restriction of the weakly regular Lebesgue measure to the finite-measure set $[a,b]$ is weakly regular (`WeaklyRegular.restrict_of_measure_ne_top`, `Regular.lean:1061`), and so is any finite Borel measure on a metrizable space (`Regular.lean:1072`); which of these routes the elaborator takes to discharge the instance we did not check. The conclusions are then used, each once, at identifiable lines. *Strictness everywhere* (1): at the induction point $t\in s$, $t<b$, the proof needs a real $y$ with $g'(t)<y<G(t)$, which it obtains from $g'(t)\le\varphi(t)<G(t)$ (`:989–990`); $t$ is an arbitrary point of $[a,b)$, so an inequality valid only almost everywhere would not do. *Lower semicontinuity* (2): from $y<G(t)$ it gives an interval $(m,M)\ni t$ on which $G>y$ (`:993–994`), hence $\int_t^uG\ge(u-t)y$ for $u\in(t,\min(M,b))$ (`:996–1014`). *Integrability of the reading* (3): it makes $t\mapsto\int_a^tG$ continuous (`continuousOn_primitive_interval`, `:979–984`), so that $s$ is closed, and it justifies $\int_a^tG+\int_t^uG=\int_a^uG$ (`integral_add_adjacent_intervals`, `:1033–1040`). *Finiteness almost everywhere* (4): inside the estimate $\int_t^uG\ge(u-t)y$ the integrand is the real reading of $G$, and the inequality $y\le G(x)$ in $[-\infty,\infty]$ is transferred to its reading only at points where $G(x)<\infty$, which is almost all of them (`EReal.coe_toReal`, `:1003–1013`). *The integral bound* (5): at the end, $g(b)-g(a)\le\int_a^bG<\int_a^b\varphi+\varepsilon$ (`:1052–1057`), and $\varepsilon\to0$. The interval integral $\int_a^b$ is the integral over $(a,b]$, while $\mu$ lives on $[a,b]$; the two differ by the null set $\{a\}$ (`integral_Icc_eq_integral_Ioc'`, `Real.volume_singleton`, `:1056–1057`). [Lean, read]

**Hand calculation 1: the rationals, a null set with dense discontinuities.** Take $X=[0,1]$ with $\mu$ Lebesgue measure, $f=1_{\mathbb Q\cap[0,1]}$ and $\varepsilon=0.1$. Here $f\ge0$, so $f^-=0$ and only Lemma H is active; $f$ is itself the simple function $c\,1_s$ with $c=1$ and $s=\mathbb Q\cap[0,1]$, $\mu(s)=0$, $\int f=0$. We follow the proof with the explicit choices it leaves open. *Lemma H(1), the positive function.* On the finite measure space $[0,1]$ one may take $w$ constant, $w=\varepsilon/4=0.025$, with $\int w=0.025<\varepsilon/2$; this is the choice Rudin makes in the proof of his Theorem 7.21 ("add a small constant"). *Lemma G for $f+w$.* The increments of $f+w$ are the two simple functions $w$ and $1_s$, up to the dyadic bookkeeping of `eapproxDiff`, and we treat them directly with Lemma F: for $w$ the constant itself is lower semicontinuous with no loss; for $1_s$, enumerate $\mathbb Q\cap[0,1]=\{q_1,q_2,\dots\}$ and put
$$U=\bigcup_{n\ge1}\bigl(q_n-\varepsilon2^{-n-2},\,q_n+\varepsilon2^{-n-2}\bigr),\qquad \mu(U)\le\sum_{n\ge1}\varepsilon2^{-n-1}=\varepsilon/2=0.05 .$$
Then $G=1_U+w$ is lower semicontinuous, $G\ge1+w>1=f$ on $U\supseteq s$ and $G=w>0=f$ off $U$, so $f<G$ everywhere, and $\int_0^1G\le0.05+0.025=0.075<0+\varepsilon$. (For the enumeration by increasing denominator, the first $1069$ intervals already have a union of measure $0.0500$ to four places; the later ones add less than $10^{-320}$.) The set where $G$ exceeds $f$ by at least $1$ is the dense open set $U$ of measure at most $0.05$, and the set where $G$ exceeds $f$ by at least $w$ is all of $[0,1]$. Compare: an inequality required only almost everywhere would allow $G=w$ with $\int G=0.025$, the price of "everywhere" on a null set is the open cover, $0.05$ here and as small as one likes; while a continuous $G>f$ has $\int_0^1G\ge1$, as in Example (1), so continuity costs at least $1$.

**Hand calculation 2: a dense open set of measure $1/2$.** At stage $n\ge1$ of the Smith–Volterra–Cantor construction remove from each of the $2^{n-1}$ closed intervals remaining in $[0,1]$ an open middle interval of length $4^{-n}$. The removed set $U$ is open and dense in $[0,1]$, with
$$\mu(U)=\sum_{n\ge1}2^{n-1}4^{-n}=\tfrac14+\tfrac18+\tfrac1{16}+\cdots=\tfrac12,$$
the partial sums after $1,2,3,5,10$ stages being $0.25$, $0.375$, $0.4375$, $0.484375$ and $0.499512$. The complement $K=[0,1]\setminus U$ is closed with empty interior and $\mu(K)=1/2$. Let $f=1_U$, which is continuous exactly on $U$ and discontinuous on $K$, a set of measure $1/2$; $\int f=1/2$. Lemma F for $f=1\cdot1_U$ asks for an open set containing $U$ of measure below $\mu(U)+\varepsilon$, and $U$ itself qualifies, so $g=1_U$ with no loss; indeed $1_U$ is already lower semicontinuous. Lemma H adds $w=\varepsilon/4$: $G=1_U+\varepsilon/4$, with $f<G$ everywhere and
$$\int_0^1G=\tfrac12+\tfrac\varepsilon4,\qquad\text{that is }0.525\text{ at }\varepsilon=0.1\text{ and }0.5025\text{ at }\varepsilon=0.01 .$$
A continuous $G>f$, by contrast, is $>1$ on the dense set $U$, hence $\ge1$ on $[0,1]$, so $\int_0^1G\ge1=\int f+\tfrac12$ whatever $\varepsilon$ is: here no continuous majorant comes within $1/2$ of the integral, while the lower semicontinuous one comes within $\varepsilon/4$. The obstruction is not the positive measure of the discontinuity set but its density. For the closed set, $f=1_K$, a continuous majorant does work: with $d(x)=\operatorname{dist}(x,K)$ and $\eta>0$ put $G=\tfrac\varepsilon4+\bigl(1+\tfrac\varepsilon4\bigr)\max\bigl(0,1-d(x)/\eta\bigr)$; then $G>1$ on $K$, $G>0$ everywhere, and $\int_0^1G\le\tfrac\varepsilon4+\bigl(1+\tfrac\varepsilon4\bigr)\mu(K_\eta)$ with $K_\eta=\{d<\eta\}$, where $\mu(K_\eta)\le\tfrac12+\sum_{n\ge1}2^{n-1}\min(4^{-n},2\eta)$, which is at most $0.5204$ for $\eta=10^{-4}$ and $0.5020$ for $\eta=10^{-6}$. What fails for $1_K$ is the other direction, as Example (3) shows.

**Hand calculation 3: the staircase on the Gamma chain.** In Lemma B of §2.3.2.4 at $r=-1/2$, the contradiction hypothesis produces a nonnegative simple $\varphi\le x^{-1/2}$ on $(0,1)$ with $\int\varphi>2$; the proof then applies Lemma A(2), which is Lemma A(1) for $-g$, $-g'$, $-\varphi$, and Lemma A(1) calls Theorem J with $f=-\varphi$ on $\mu=\mathrm{vol}\mid_{[0,1]}$. No such $\varphi$ exists, but the staircase $\varphi=\varphi_{1/2,3}=1\cdot1_{(1/2,1]}+\sqrt2\cdot1_{(1/4,1/2]}+2\cdot1_{(1/8,1/4]}$, with $\int\varphi=\tfrac12+\tfrac{\sqrt2}4+\tfrac14=1.10355$, shows what the theorem does with such an input. Here $f=-\varphi\le0$, so $f^+=0$ and $f^-=\varphi$. *Upper branch, Lemma H(3) for $f^+=0$:* $g_p=w=\varepsilon/4$. *Lower branch, Lemma I for $f^-=\varphi$:* for each step $(q^k,q^{k-1}]$ with height $c_k$ choose the closed subinterval $F_k=[q^k+\eta_k,\,q^{k-1}]$ with $c_k\eta_k=\varepsilon/(2n)$, so that $\int\varphi-\int g_m=\sum_kc_k\eta_k=\varepsilon/2$ for $g_m=\sum_kc_k1_{F_k}$; at $\varepsilon=0.1$, $n=3$ the three $\eta_k$ are $0.016667$, $0.011785$ and $0.008333$. Then $G=g_p-g_m=\tfrac\varepsilon4-\sum_kc_k1_{F_k}$ is lower semicontinuous, $G>-\varphi$ everywhere ($\tfrac\varepsilon4-c_k>-c_k$ on $F_k$, $\tfrac\varepsilon4>-\varphi$ elsewhere), and
$$\int_0^1G=\tfrac\varepsilon4-\int g_m=\tfrac\varepsilon4-\int\varphi+\tfrac\varepsilon2=\int f+\tfrac{3\varepsilon}4<\int f+\varepsilon .$$
In fact this $\varphi$ is upper semicontinuous at every point except the bottom point $q^3=1/8$: at the interior jumps $q^1,q^2$ its value is the larger of the two neighbouring heights, while at $1/8$ its value $0$ lies below the limit $2$ from the right. So only the lowest step needs shaving, and $g_m=\varphi\,1_{[1/8+\eta,1]}$ with $2\eta=\varepsilon/2$ would have done with the same total error $3\varepsilon/4$; the proof shaves every step regardless. The function Lemma A(1) then integrates is $G$, and the set $s$ of its real induction is $\{t:\ -g(t)+g(0)\le\int_0^tG\}$ with $g=2\sqrt x$.

**Remark (what fails when a hypothesis is removed).** [Expository]

1. *$\sigma$-finiteness.* Let $X$ be an uncountable set with the discrete topology and $\mu$ the counting measure. Every subset is open and closed, so $\mu$ is weakly regular, and the Borel $\sigma$-algebra is the full power set; but $\mu$ is not $\sigma$-finite. Take $f=0$, integrable with $\int f=0$. A function $G>0$ at every point has $\{G>1/k\}$ uncountable for some $k$, so $\int G=\infty$: no strict majorant with finite integral exists, and Theorem J fails. Lemma G, the non-strict version, holds trivially with $g=f$. This is the price the file's docstring announces for the strict inequality, and it is the only use of $\sigma$-finiteness in the proof (Lemma H(1)).
2. *Regularity.* Outer regularity enters once, in Lemma F, and inner regularity by closed sets once, in Lemma I. The counting measure on $\mathbb R$ with its usual topology is neither $\sigma$-finite nor outer regular ($\mu(\{0\})=1$ while every open neighbourhood of $0$ has infinite measure), and for it $f=1_{\{0\}}$ has no lower semicontinuous majorant with finite integral; we did not pursue an example that fails regularity alone.
3. *Real values.* Let $f=\sum_n2^{-n}\lvert x-q_n\rvert^{-1/2}$ on $[0,1]$ as in Example (4), set to $0$ where the series diverges. Since $\int_0^1\lvert x-q\rvert^{-1/2}dx=2\sqrt q+2\sqrt{1-q}\le2\sqrt2$, we get $\int_0^1f\le2\sqrt2\approx2.83$ (the first sixty terms give $2.20$), so $f$ is integrable and finite almost everywhere. Near each $q_n$ the points where $f$ is finite are dense and $f\ge2^{-n}\lvert x-q_n\rvert^{-1/2}$ there, so $f$ is unbounded on every nonempty open subset of $[0,1]$. If $g\ge f$ is lower semicontinuous, each $\{g>k\}$ is open and dense, so $\bigcap_k\{g>k\}$ is a dense $G_\delta$ by Baire's theorem, and $g=+\infty$ on it. Hence no real-valued lower semicontinuous majorant exists at all, and conclusion (4) of Theorem J cannot be strengthened to "everywhere". The set where $g=\infty$ is a null set because $\int g<\infty$.
4. *Strictness only almost everywhere.* Hand calculation 1 measures the cost of "everywhere" on a null set: the open cover $U$. In Lemma A the strict inequality is used at the induction point $t$, which can be any point of $[a,b)$; an almost-everywhere version would stall at the first $t$ in the exceptional set.
5. *Lower semicontinuity from below.* For $f=1_K$ with $K$ the Smith–Volterra–Cantor set, every lower semicontinuous $v\le f$ satisfies $v\le0$, since $\{v>0\}$ is an open subset of $K$ and $K$ has empty interior; so $\int v\le0<\tfrac12=\int f$ for all of them (Rudin, Exercise 2.6). This is why the lower bound in Theorem J is upper semicontinuous, and why Lemma I approximates from inside by closed sets where Lemma F approximates from outside by open sets.
6. *Continuity.* Hand calculations 1 and 2 show that continuous majorants can be forced to miss the integral by $1$ or by $1/2$. In general, for bounded $f$ a continuous $G>f$ dominates the upper envelope $f^\ast(x)=\limsup_{x'\to x}f(x')$, so $\inf\int G\ge\int f^\ast$ over continuous majorants. For $f=1_U$ the envelope is $f^\ast=1$ on all of $[0,1]$ and the gap is $1/2$; for $f=1_K$ the envelope is $f$ itself, which is why $1_K$ does admit continuous majorants with small excess although it is discontinuous on a set of measure $1/2$. The theorem avoids the envelope by asking only for lower semicontinuity, which $1_U$ and every open-set series already have.
7. *Integrability.* For $f=1/x$ on $(0,1]$ with $f(0)=0$ one has $\int f=\infty$, and no $G\ge f$ has finite integral; the theorem is about integrable $f$ and says nothing here.

**Remark (Rudin's version and the formal one).** [Expository] Rudin's Theorem 2.25 states, for $f\in L^1(\mu)$ real-valued and $\varepsilon>0$, with $\mu$ the measure of his Riesz representation theorem on a locally compact Hausdorff space, that there are $u\le f\le v$ with $u$ upper semicontinuous and bounded above, $v$ lower semicontinuous and bounded below, and $\int(v-u)<\varepsilon$; the inequalities are not strict, and in the proof of Theorem 7.21 he obtains $g>f'$ by adding a small constant to $g\ge f'$, "since $m([a,b])<\infty$". Mathlib's statement builds the strictness in and pays with $\sigma$-finiteness (Lemma H), replaces compact inner approximation by closed sets so that weak regularity suffices, and states the upper and lower bounds separately. The construction is otherwise Rudin's: his $v=\sum_ic_i\chi_{V_i}$ over open $V_i\supseteq E_i$ is Lemma G, and his $u=\sum_{i\le N}c_i\chi_{K_i}$ over compact $K_i\subseteq E_i$ is Lemma I with closed sets. The file's header cites "Theorem 2.24"; in the third edition the Vitali–Carathéodory theorem is Theorem 2.25 on page 56 and Theorem 2.24 is Lusin's theorem. Rudin's notes to Chapter 2 refer, for Section 2.25, to Saks's *Theory of the Integral*, page 75. Tao's Proposition 92, cited in §2.3.2.4, proves the same fundamental theorem for everywhere differentiable functions by a different route (Lebesgue points and a covering of the exceptional set) and does not use semicontinuous approximation.

**Reading boundary.** All Mathlib links are fixed at `0df444a360eaa60ab8c11dca51a86af692955474`. The [Lean, read] increment of this subsection is the whole of `Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean` (520 lines): `SimpleFunc.exists_le_lowerSemicontinuous_lintegral_ge`, `exists_le_lowerSemicontinuous_lintegral_ge`, `exists_lt_lowerSemicontinuous_lintegral_ge`, `exists_lt_lowerSemicontinuous_lintegral_ge_of_aemeasurable`, `exists_lt_lowerSemicontinuous_integral_gt_nnreal`, `SimpleFunc.exists_upperSemicontinuous_le_lintegral_le`, `exists_upperSemicontinuous_le_lintegral_le`, `exists_upperSemicontinuous_le_integral_le`, `exists_lt_lowerSemicontinuous_integral_lt` and `exists_upperSemicontinuous_lt_integral_gt`, together with the consumer lines `FundThmCalculus.lean:974–1057` re-read for the five uses. Read as statements, with their proofs retained at [Lean]: `Set.exists_isOpen_lt_of_lt` and `MeasurableSet.exists_isClosed_lt_add` (`Mathlib/MeasureTheory/Measure/Regular.lean:359,1031`), the regularity classes and instances (`Regular.lean:308,324,1072,1081`), `exists_pos_lintegral_lt_of_sigmaFinite` (`Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean:227`), `lintegral_eq_nnreal` and the definition `lintegral` (`Lebesgue/Basic.lean:158,48`), `lintegral_tsum` and `lintegral_add_left` (`Lebesgue/Add.lean:360,314`), `eapproxDiff`, `tsum_eapproxDiff` and `SimpleFunc.induction` (`Mathlib/MeasureTheory/Function/SimpleFunc.lean:925,942,1260`), `lowerSemicontinuous_tsum`, `IsOpen.lowerSemicontinuous_indicator`, `IsClosed.upperSemicontinuous_indicator` and `LowerSemicontinuous.add'` (`Mathlib/Topology/Semicontinuity/Basic.lean:720,125,771,505`), `integral_eq_lintegral_of_nonneg_ae` and `integral_eq_integral_pos_part_sub_integral_neg_part` (`Bochner/Basic.lean:483,559`), and the `EReal` arithmetic lemmas `EReal.lt_iff_exists_real_btwn`, `EReal.sub_lt_sub_of_lt_of_le`, `EReal.toReal_sub` and `EReal.continuousAt_add`. Nothing was compiled or kernel-checked: source reading against the pinned revision, with file hashes recorded in the source ledger, is not kernel verification. The three hand calculations, the Baire argument in item 3, the envelope remark in item 6 and the two counting-measure examples are textbook derivations; their numerical values are floating-point checks with the standard library. Classical sources: W. Rudin, *Real and Complex Analysis*, 3rd ed. (McGraw-Hill, 1987), Theorem 2.25 (p. 56), Exercise 2.6 (p. 58), Theorem 7.21 (pp. 149–150) and the notes to Chapter 2; S. Saks, *Theory of the Integral*, 2nd ed. (Warsaw, 1937), cited through Rudin and not consulted. [Mathlib, `Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean:92–518`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean#L92-L518) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:968–1060`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L968-L1060) · [Mathlib, `Mathlib/MeasureTheory/Measure/Regular.lean:308–359,1031–1088`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Regular.lean#L308-L359)

#### 2.3.2.6 Monotone convergence on truncation domains: the lower-integral theorem behind Lemma C and the signed limits at both ends of Euler's integral

Two limits in §2.3.2.4 were used without proof. Step (iv) of Lemma C passed the truncated integrals $\int_{(a,n]}\lvert f\rvert$ to $\int_{(a,\infty)}\lvert f\rvert$ by the monotone convergence theorem `lintegral_tendsto_of_tendsto_of_monotone`. Theorem D obtained the signed value $\int_a^xg'\to\int_{(a,\infty)}g'$ from dominated convergence, and the same signed limit is used in §2.3.2.3, where `tendsto_partialGamma` lets $\int_0^Xe^{-x}x^{s-1}\,dx$ tend to $\Gamma(s)$ in the proof of the recurrence $\Gamma(s+1)=s\Gamma(s)$. This subsection reads the first theorem in the pinned file `Lebesgue/Add.lean` (Mario Carneiro and Johannes Hölzl, 2018), down to the definition of the lower integral. It then shows that for truncations the second limit follows from the first by a single subtraction, and that the subtraction is legitimate exactly when $\int\lvert f\rvert$ is finite.

One distinction runs through everything below. The theorem concerns a monotone family of functions $n\mapsto F_n$. In every use on the Gamma chain that family is $F_n=1_{\psi_n}\lvert f\rvert$ for an increasing family of truncation domains $\psi_n$. It is monotone because the domains grow and $\lvert f\rvert\ge0$, not because $f$ is a monotone function of $x$. The kernel $e^{-x}x^2$ rises and then falls, and $e^{-x}\cos x$ changes sign infinitely often; the truncation families of their absolute values are monotone all the same. For a signed $f$, on the other hand, the family $1_{\psi_n}f$ is not monotone at all, and what carries its integrals to the limit is a domination hypothesis. Each end of Euler's integral needs its own such hypothesis. [Mathlib, `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:1–125`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean#L1-L125) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:364–407`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L364-L407) · [Mathlib, `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:146–151`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L146-L151)

**Examples.**

1. *$x^{-1/2}$ on $(0,\infty)$.* As $\varepsilon\downarrow0$, $\int_{(\varepsilon,1]}x^{-1/2}\,dx=2-2\sqrt\varepsilon\uparrow2$. As $X\uparrow\infty$, $\int_{(1,X]}x^{-1/2}\,dx=2\sqrt X-2\uparrow\infty$. Monotone convergence holds at both ends, with limits $2$ and $\infty$. Only at the zero end is the limit finite, and only there does the tail $\int_{(0,\varepsilon]}x^{-1/2}\,dx=2\sqrt\varepsilon$ tend to $0$; at infinity every tail $\int_{(X,\infty)}x^{-1/2}\,dx$ equals $+\infty$. For $x^{-2}$ the roles are exchanged. The two ends are independent.
2. *$e^{-x}\cos x$ on $(0,\infty)$.* Here $\int_0^Xe^{-x}\cos x\,dx=\tfrac12+\tfrac12e^{-X}(\sin X-\cos X)$, which is $0.603940$, $0.521607$, $0.495508$ and $0.499066$ at $X=\pi/2,\pi,3\pi/2,2\pi$, so it is not monotone in $X$. The absolute truncations $\int_0^Xe^{-x}\lvert\cos x\rvert\,dx$ are $0.603940$, $0.686273$, $0.712371$ and $0.715929$, and they increase to $\bigl(\tfrac12+e^{-\pi/2}-\tfrac12e^{-\pi}\bigr)/(1-e^{-\pi})\approx0.717269$. Since $\lvert e^{-x}\cos x\rvert\le e^{-x}$, one integrable function dominates every truncation, and the signed truncations converge to $\tfrac12$.
3. *$e^{-x}x^2$ on $(0,\infty)$.* This kernel increases on $(0,2)$ and decreases afterwards. Its truncations $\int_{(\varepsilon,X]}e^{-x}x^2\,dx$ nevertheless increase as $\varepsilon$ decreases and as $X$ increases. Hand calculation 1 computes both tails exactly.
4. *$\sin x/x$ on $[1,\infty)$.* Remark item 5 of §2.3.2.4 showed that signed truncations can converge without any integrable dominating function. Failure example 2 below shows that the limit then depends on how the domain is exhausted.

**Definition (simple-function integral, lower integral, a.e. representatives, truncation families, tails).** Let $\mu$ be a measure on a measurable space $X$.

- A *simple function* $s:X\to[0,\infty]$ has finitely many values and measurable level sets $s^{-1}\{p\}$ (`SimpleFunc`). Its integral is $\sum_pp\,\mu(s^{-1}\{p\})$ over its values, with the convention $0\cdot\infty=0$ (`SimpleFunc.lintegral`). Rudin's nonnegative simple functions take values in $[0,\infty)$; his Definition 1.16 explicitly excludes $\infty$. Mathlib's may take the value $\infty$. The difference is removed by `lintegral_eq_nnreal` below.
- For any $f:X\to[0,\infty]$, measurable or not, the *lower integral* is $\int f\,d\mu=\sup\{\int s:\ s\text{ simple},\ s\le f\}$ (`lintegral`). For a simple $f$ it is the simple integral (`SimpleFunc.lintegral_eq_lintegral`), and it is monotone in $f$ (`lintegral_mono`). The supremum may be restricted to simple functions with finite values (`lintegral_eq_nnreal`): if a simple $s\le f$ equals $\infty$ on a set $B$ of positive measure, then $f=\infty$ on $B$, and the simple functions $m\,1_B\le f$ have integrals $m\,\mu(B)\to\infty$.
- $f$ is *a.e.-measurable* (`AEMeasurable f μ`) if it agrees almost everywhere with a measurable function, its *representative* (`AEMeasurable.mk`).
- A family $(F_n)_{n\in\mathbb N}$ of functions $X\to[0,\infty]$ is *monotone* if $F_m\le F_n$ at every point whenever $m\le n$ (`Monotone`). It is *a.e. monotone* if for almost every $x$ the sequence $n\mapsto F_n(x)$ is nondecreasing.
- Given $h:X\to[0,\infty]$ and an increasing family of measurable sets $\psi_n$, the *truncation family* of $h$ is $F_n=1_{\psi_n}h$. Because $h\ge0$, it is monotone whatever the shape of $h$. Its integrals are $\int_{\psi_n}h$; the identity $\int1_\psi h\,d\mu=\int_\psi h\,d\mu$ (`lintegral_indicator`) requires $\psi$ to be measurable.
- Let $f$ be a function on $(0,\infty)$ that is integrable on every $[\varepsilon,X]$ with $0<\varepsilon<X$. Write $A(\varepsilon,X)=\int_{(\varepsilon,X]}f$. Call $T_0(\varepsilon)=\int_{(0,\varepsilon]}f$ the *zero-end tail* and $T_\infty(X)=\int_{(X,\infty)}f$ the *infinite-end tail*, whenever these are defined. When $f$ is integrable on $(0,\infty)$ and $\varepsilon<X$,
$$\int_{(0,\infty)}f-A(\varepsilon,X)=T_0(\varepsilon)+T_\infty(X).$$

[Mathlib, `Mathlib/MeasureTheory/Function/SimpleFunc.lean:45–49,955–957`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/SimpleFunc.lean#L45-L49) · [Mathlib, `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:47–200`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L47-L200) · [Mathlib, `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:496–503`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L496-L503)

**Lemma K (monotone convergence for measurable functions).** Let $F_n:X\to[0,\infty]$, $n\in\mathbb N$, be measurable, with $F_m\le F_n$ everywhere for $m\le n$. Then
$$\int\sup_nF_n\,d\mu=\sup_n\int F_n\,d\mu .$$
[Lean, read] [Mathlib, `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:33–93`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean#L33-L93)

*Proof.* Put $F=\sup_nF_n$. Since $F_n\le F$, monotonicity of the integral gives $\sup_n\int F_n\le\int F$ (`iSup_lintegral_le`). For the reverse inequality three reductions are made:

- by `lintegral_eq_nnreal`, it suffices to show $\int s\le\sup_n\int F_n$ for every simple $s\le F$ with finite values;
- since $\int s=\sup_{r<1}r\int s$ (`ENNReal.le_of_forall_lt_one_mul_le`), it suffices to show $r\int s\le\sup_n\int F_n$ for each real $r\in[0,1)$;
- fix such $s$ and $r$, let $t=rs$, and for each value $p$ of $t$ and each $n$ put $A_{p,n}=t^{-1}\{p\}\cap\{x:\ p\le F_n(x)\}$.

(a) *The sets $A_{p,n}$ increase with $n$*, because $F_n(x)$ does.

(b) *Their union is $t^{-1}\{p\}$.* If $p=0$, every $x$ with $t(x)=0$ satisfies $0\le F_n(x)$. If $p=t(x)\ne0$, then $s(x)\ne0$. Because $s(x)<\infty$ and $r<1$, we have $t(x)=rs(x)<s(x)\le F(x)=\sup_nF_n(x)$, so $t(x)<F_n(x)$ for some $n$.

(c) *Continuity from below.* By (a) and (b), $\mu(A_{p,n})\uparrow\mu(t^{-1}\{p\})$ (`Monotone.measure_iUnion`, which holds for arbitrary sets). Multiplication by $p$ commutes with the supremum (`ENNReal.mul_iSup`). For a finite sum of nondecreasing sequences, the supremum of the sums is the sum of the suprema (`ENNReal.finsetSum_iSup_of_monotone`). Hence
$$r\int s=\int t=\sum_pp\,\mu\bigl(t^{-1}\{p\}\bigr)=\sup_n\sum_pp\,\mu(A_{p,n}).$$

(d) *Comparison with $F_n$.* The set $E_n=\{x:\ t(x)\le F_n(x)\}$ is measurable because $t$ and $F_n$ are (`measurableSet_le`). So $t\,1_{E_n}$ is a simple function, and its integral is $\sum_pp\,\mu(t^{-1}\{p\}\cap E_n)=\sum_pp\,\mu(A_{p,n})$ (`restrict_lintegral`). Since $t\,1_{E_n}\le F_n$, this is at most $\int F_n$. Combined with (c), this gives $r\int s\le\sup_n\int F_n$. $\square$

Each hypothesis is used once.

- *Measurability of $F_n$* is used only in (d). `SimpleFunc.restrict` returns the zero function on a non-measurable set, so without it the comparison collapses.
- *Monotonicity* is used only in (a).
- *Nonnegativity* is built into the codomain $[0,\infty]$. It makes the lower integral a supremum over simple functions below, and in (b) it handles the value $p=0$.
- *The finite values of $s$ and the factor $r<1$* are used together in (b), to make $t(x)<F(x)$ strict. They come from `lintegral_eq_nnreal` and `ENNReal.le_of_forall_lt_one_mul_le` respectively. Remark item 5 shows that the argument needs both.

This is the proof of Theorem 1.26 in Rudin's *Real and Complex Analysis* (pp. 21–22). His sets $E_n=\{f_n\ge cs\}$ with $0<c<1$ are the $E_n$ above with $r=c$. Rudin then uses the measure $E\mapsto\int_Es$ (Proposition 1.25) and its continuity from below (Theorem 1.19(d)); the Lean proof unrolls that step over the level sets of $t$.

**Lemma L (almost-everywhere hypotheses, and the limit form).** Let $F_n:X\to[0,\infty]$ be a.e.-measurable, with $n\mapsto F_n(x)$ nondecreasing for almost every $x$. Then $\int\sup_nF_n=\sup_n\int F_n$. If moreover $F_n(x)\to G(x)$ for almost every $x$, then $\int F_n\to\int G$ in $[0,\infty]$. [Lean, read] [Mathlib, `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:95–147`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean#L95-L147) · [Mathlib, `Mathlib/MeasureTheory/Function/AEMeasurableSequence.lean:32–117`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/AEMeasurableSequence.lean#L32-L117)

*Proof.* *Representatives.* Choose measurable $H_n$ with $H_n=F_n$ almost everywhere (`AEMeasurable.mk`). Let $B_0$ be the set of $x$ at which $F_n(x)\ne H_n(x)$ for some $n$ or $n\mapsto F_n(x)$ fails to be monotone. It is a countable union of null sets, hence null (`ae_all_iff`, which uses that $\mathbb N$ is countable). Enlarge it to a measurable null set $B$ (`toMeasurable`). Put $R_n=H_n$ off $B$ and $R_n=c_0$ on $B$ (`aeSeq`). Here $c_0$ is a single value. In the source it is `(⟨f i x⟩ : Nonempty β).some`, the element chosen from a proof that $[0,\infty]$ is nonempty; all proofs of a proposition are equal, so the value depends neither on $n$ nor on $x$. Then:

- each $R_n$ is measurable (`aeSeq.measurable`);
- the family $(R_n)$ is monotone at every point, off $B$ because $R_n=F_n$ there and on $B$ because $R_n$ does not depend on $n$;
- $R_n=F_n$ and $\sup_nR_n=\sup_nF_n$ almost everywhere (`aeSeq.aeSeq_n_eq_fun_n_ae`, `aeSeq.iSup`).

Lemma K and the invariance of integrals under a.e. equality (`lintegral_congr_ae`) give $\int\sup F_n=\int\sup R_n=\sup\int R_n=\sup\int F_n$ (`lintegral_iSup'`).

*Limit form.* The integrals $\int F_n$ are nondecreasing (`lintegral_mono_ae`), so they converge to their supremum (`tendsto_atTop_iSup`). At almost every $x$ the sequence $F_n(x)$ is nondecreasing, so it converges to $\sup_nF_n(x)$; it also converges to $G(x)$. Limits in $[0,\infty]$ are unique, so $G=\sup_nF_n$ almost everywhere, and $\int G=\sup_n\int F_n$ (`lintegral_tendsto_of_tendsto_of_monotone`). $\square$

Mathlib also proves the almost-everywhere form a second way, for measurable $F_n$ with $F_n\le F_{n+1}$ almost everywhere (`lintegral_iSup_ae`): it sets every $F_n$ to $0$ on one measurable null set containing all the exceptions (`exists_measurable_superset_of_null`). In both versions the exceptions of countably many functions are collected into a single null set. A family indexed by a real parameter is therefore first reduced to sequences.

**Lemma M (decreasing families need one finite integral).** Let $F_n:X\to[0,\infty]$ be measurable, with $F_{n+1}\le F_n$ almost everywhere for every $n$ and $\int F_0<\infty$. Then $\int\inf_nF_n=\inf_n\int F_n$, and the same holds in the limit form. The finiteness hypothesis cannot be dropped. [Lean, read] [Mathlib, `Mathlib/MeasureTheory/Integral/Lebesgue/Sub.lean:26–84,133–146`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/Sub.lean#L26-L146)

*Proof.* The measurable functions $F_0-F_n$ increase almost everywhere, so the a.e. form of Lemma K gives $\int\sup_n(F_0-F_n)=\sup_n\int(F_0-F_n)$ (`lintegral_iSup_ae`). Subtraction of integrals is allowed in one case: if $g$ is measurable, $g\le f$ almost everywhere and $\int g<\infty$, then $\int(f-g)=\int f-\int g$. This follows from additivity, $\int g+\int(f-g)=\int f$, and the finiteness of $\int g$ (`lintegral_sub`). Each $F_n$, and also $\inf_nF_n$, lies below $F_0$ almost everywhere and has finite integral. With $\sup_n(F_0-F_n)=F_0-\inf_nF_n$ (`ENNReal.sub_iInf`) this gives
$$\int F_0-\int\inf_nF_n=\sup_n\Bigl(\int F_0-\int F_n\Bigr)=\int F_0-\inf_n\int F_n .$$
Since $\int F_0$ is finite, it cancels (`ENNReal.sub_right_inj`, `lintegral_iInf_ae`). The limit form `lintegral_tendsto_of_tendsto_of_antitone` carries the same hypothesis. For the necessity, take $F_n=1_{(n,\infty)}$ on $(0,\infty)$: it decreases to $0$, while $\int F_n=\infty$ for every $n$. $\square$

**How measurability, representatives, the simple-function supremum and nonnegativity pay for Lemma C.** [Lean, read] Return to step (iv) of Lemma C in §2.3.2.4. The private lemma `lintegral_tendsto_of_monotone_of_nat` applies Lemma L to $F_n=1_{\varphi_n}f$, where $(\varphi_n)$ is an increasing a.e. cover of a measure $\nu$ and $f:X\to[0,\infty]$ is a.e.-measurable; in Lemma C, $f$ is the extended norm of the integrand. Its three hypotheses are paid as follows.

1. *Measurability* (`key₁`). The function $1_{\varphi_n}f$ is a.e.-measurable because $f$ is and $\varphi_n$ is measurable; measurability of $\varphi_n$ is the second field of `AECover`. The final rewriting $\int1_{\varphi_n}f\,d\nu=\int_{\varphi_n}f\,d\nu$ (`lintegral_indicator`) needs the measurability of $\varphi_n$ again. In Lemma C the a.e.-measurability of $f$ comes from the pieces: the integrand is a.e. strongly measurable on each $(a,u_n]$, and countably many of these cover almost every point (`AECover.aestronglyMeasurable`).
2. *Monotonicity comes from the domains* (`key₂`). For $m\le n$ we have $\varphi_m\subseteq\varphi_n$, hence $1_{\varphi_m}f\le1_{\varphi_n}f$ at every point. This inequality between indicators holds because $f\ge0$, and it is the only place where the growth of the domains is used. It holds everywhere, not just almost everywhere (`ae_of_all`).
3. *Convergence comes from the cover* (`key₃`). Almost every $x$ lies in $\varphi_n$ for all large $n$, so $1_{\varphi_n}f(x)=f(x)$ eventually (`ae_tendsto_indicator`).
4. *Representatives and the simple-function supremum* are paid inside Lemmas L and K. `aeSeq` replaces the a.e.-measurable functions $1_{\varphi_n}f$ by measurable functions that are monotone at every point. Lemma K then compares each finite-valued simple $s\le f$ with $1_{\varphi_n}f$ through the sets $\{rs\le1_{\varphi_n}f\}$.

A sequence $u_n\to\infty$ need not increase. For such a sequence, `lintegral_tendsto_of_nat` applies the private lemma twice, to the lower envelope $\bigcap_{k\ge n}\varphi_{u_k}$, an infimum of domains, and to the upper envelope $\bigcup_{k\le n}\varphi_{u_k}$. Both envelopes increase and both are a.e. covers. It then squeezes $\int_{\varphi_{u_n}}f$ between them by monotonicity in the domain (`lintegral_mono_set`), which is another consequence of $f\ge0$. For a countably generated filter it suffices to test sequences (`lintegral_tendsto_of_countably_generated`).

In the half-line criterion `integrableOn_Ioi_of_intervalIntegral_norm_bounded`, the cover is $\varphi_i=(-\infty,b_i]$ of $\nu=\mu\mid_{(a,\infty)}$ along a filter $l$ with $b_i\to\infty$ (`aecover_Iic`). `Measure.restrict_restrict` with `inter_comm` turns $\int_{\varphi_i}\cdot\,d\nu$ into $\int_{(a,b_i]}\cdot\,d\mu$, and `intervalIntegral.integral_of_le` turns that into $\int_a^{b_i}$ once $b_i\ge a$. The hypothesis is a bound on Bochner integrals of $\lVert f\rVert$. `integrable_of_integral_norm_bounded` converts it into a bound on lower integrals by `integral_eq_lintegral_of_nonneg_ae`, which uses the nonnegativity of the norm once more. `integrable_of_lintegral_enorm_bounded` then passes the bound to the limit (`le_of_tendsto`). The version with a convergence hypothesis only extracts a bound (`isBoundedUnder_le`). The limit is the same number $\int\lVert f\rVert\,d\nu$ for every such $b$ and every such $l$, so it does not depend on how the half-line is exhausted. In Theorem D, $l$ is `atTop` on $\mathbb R$ and $b$ is the identity, so $\varphi_x=(-\infty,x]$. [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:316–392`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L316-L392) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:413–453`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L413-L453) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:554–576`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L554-L576)

**Remark (truncation domains do not need measurable integrands).** [Expository, from two read statements] For domains, as opposed to functions, monotone convergence is a statement about the measure alone. For any $h:X\to[0,\infty]$ and any countable directed family of sets $\psi_i$, measurable or not,
$$\int_{\bigcup_i\psi_i}h\,d\mu=\sup_i\int_{\psi_i}h\,d\mu$$
(`setLIntegral_iUnion_of_directed`). The proof uses only simple functions. For a simple $s$, continuity from below gives $\mu\mid_{\bigcup\psi_i}(s^{-1}\{p\})=\sup_i\mu\mid_{\psi_i}(s^{-1}\{p\})$ (`SimpleFunc.lintegral_restrict_iUnion_of_directed`), and two suprema commute. Applied to an increasing a.e. cover, whose union has full measure so that restricting to it changes nothing (`Measure.restrict_eq_self_of_ae_mem`), this gives the conclusion of `lintegral_tendsto_of_monotone_of_nat` without its hypothesis that $f$ be a.e.-measurable. The private lemma goes through Lemma L, which does need that hypothesis. In Lemma C nothing is lost, because a.e. strong measurability is needed anyway for the conclusion "integrable". The two forms differ when the domains are not measurable. Then $\int_\psi h\,d\mu$, the integral against the restricted measure, and $\int1_\psi h\,d\mu$, the lower integral of the truncated function, can be different numbers, and only the second is the integral of a truncation family (Remark, item 4). [Mathlib, `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:646–650`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L646-L650) · [Mathlib, `Mathlib/MeasureTheory/Function/SimpleFunc.lean:1067–1073`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Function/SimpleFunc.lean#L1067-L1073)

**Theorem N (truncation at the two ends).** Let $E$ be a Banach space and let $f:(0,\infty)\to E$ be integrable on every interval $[\varepsilon,X]$ with $0<\varepsilon<X$. For $0<c<\infty$:

1. *Nonnegative convergence, no finiteness needed.* As $\varepsilon\to0^+$, $\int_{(\varepsilon,c]}\lVert f\rVert\uparrow\int_{(0,c]}\lVert f\rVert$. As $X\to\infty$, $\int_{(c,X]}\lVert f\rVert\uparrow\int_{(c,\infty)}\lVert f\rVert$. Jointly, $\int_{(\varepsilon,X]}\lVert f\rVert\to\int_{(0,\infty)}\lVert f\rVert$. All limits are taken in $[0,\infty]$.
2. *The two tails.* $\int_{(0,\varepsilon]}\lVert f\rVert\to0$ as $\varepsilon\to0^+$ if and only if $\int_{(0,c]}\lVert f\rVert<\infty$ for some, equivalently every, $c>0$. Likewise $\int_{(X,\infty)}\lVert f\rVert\to0$ as $X\to\infty$ if and only if $\int_{(c,\infty)}\lVert f\rVert<\infty$ for some, equivalently every, $c$. Neither condition implies the other. If the truncated integrals $\int_{(a_i,b]}\lVert f\rVert$ or $\int_{(c,b_i]}\lVert f\rVert$ stay bounded along a nontrivial countably generated filter with $a_i\to0$ or $b_i\to\infty$, then $f$ is integrable on $(0,b]$, respectively on $(c,\infty)$.
3. *Signed transport under a common integrable dominating function.* If both conditions hold, that is, if $f$ is integrable on $(0,\infty)$, then
$$\Bigl\lVert\int_{(0,\infty)}f-\int_{(\varepsilon,X]}f\Bigr\rVert\le\int_{(0,\varepsilon]}\lVert f\rVert+\int_{(X,\infty)}\lVert f\rVert\longrightarrow0\qquad(\varepsilon\to0^+,\ X\to\infty).$$
The same inequality with one tail holds at one end under that end's condition alone. For example, if $f$ is integrable on $(c,\infty)$, then $\int_{(c,X]}f\to\int_{(c,\infty)}f$.
4. *Without the conditions.* If $\int_{(c,\infty)}\lVert f\rVert=\infty$, the signed truncations $\int_{(c,X]}f$ may fail to converge. They may also converge to a number that is not the Bochner integral, which is then $0$ by convention, and limits along different increasing exhaustions may differ. The same holds at the zero end.

[Lean, read] for the formal counterparts:

- (1) is `AECover.lintegral_tendsto_of_countably_generated`, with the cover $(-\infty,X]$ of $\mu\mid_{(c,\infty)}$ (`aecover_Iic`) at infinity and the cover $(a_i,b_i]$ of $\mu\mid_{(a_0,b_0]}$ (`aecover_Ioc_of_Ioc`) at the zero end;
- the integrability statements in (2) are `integrableOn_Ioi_of_intervalIntegral_norm_bounded` and `integrableOn_Ioc_of_intervalIntegral_norm_bounded_left`;
- (3) is `AECover.integral_tendsto_of_countably_generated`, in the form `intervalIntegral_tendsto_integral_Ioi` at the infinite end, and the tail form is `tendsto_integral_Ioi_zero`.

All of these were read down to Lemma L, with one exception: the Lean proof of the Bochner limit in (3) calls the dominated convergence theorem `tendsto_integral_filter_of_dominated_convergence` with the bound $\lVert f\rVert$. That theorem is a named input, proved in `DominatedConvergence.lean` through the $L^1$ extension `setToFun` and not read here. The proof of (3) below is a textbook proof from Lemma L. [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:197–260`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L197-L260) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:481–489`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L481-L489) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:578–600`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L578-L600) · [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:658–679`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L658-L679) · [Mathlib, `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:57–74`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean#L57-L74)

*Proof.* (1) Let $\varepsilon_n\downarrow0$ and $X_n\uparrow\infty$. The domains $(\varepsilon_n,X_n]$ increase to $(0,\infty)$, and $1_{(\varepsilon_n,X_n]}\lVert f\rVert$ is their truncation family. The function $\lVert f\rVert$ is a.e.-measurable on $(0,\infty)$, because $f$ is a.e. strongly measurable on each $[\varepsilon_n,X_n]$ and these countably many sets cover $(0,\infty)$. Lemma L gives the convergence along these sequences. Arbitrary sequences reduce to monotone ones through the two envelopes, and arbitrary approach reduces to sequences, exactly as in Lemma C. The one-ended statements use the domains $(\varepsilon_n,c]$ and $(c,X_n]$.

(2) Suppose $\int_{(0,c]}\lVert f\rVert<\infty$. For $\varepsilon<c$, additivity over $(0,\varepsilon]\cup(\varepsilon,c]$ and the finiteness give $\int_{(0,\varepsilon]}\lVert f\rVert=\int_{(0,c]}\lVert f\rVert-\int_{(\varepsilon,c]}\lVert f\rVert$, and this tends to $0$ by (1). Equivalently, apply Lemma M to $1_{(0,\varepsilon_n]}\lVert f\rVert$, which decreases to $0$ at every point. Conversely, if the zero-end tails tend to $0$, one of them is finite, and adding $\int_{(\varepsilon,c]}\lVert f\rVert<\infty$ gives $\int_{(0,c]}\lVert f\rVert<\infty$. "Some" and "every" agree because $f$ is integrable on the compact pieces in between. The infinite end is the same with $(X,\infty)$. The functions $x^{-1/2}$ and $x^{-2}$ of Example 1 show that the two conditions are independent. If the truncated integrals stay bounded, (1) bounds the limit, and the a.e. measurability from (1) completes integrability; this is the argument of Lemma C, applied to the respective cover.

(3) The function $\lVert f\rVert$ is integrable on $(0,\infty)$, and $f$ is a.e. strongly measurable, so $f$ is integrable. Its Bochner integrals over $(0,\varepsilon]$, $(\varepsilon,X]$ and $(X,\infty)$ exist and add up, so the error $\int_{(0,\infty)}f-\int_{(\varepsilon,X]}f$ equals $T_0(\varepsilon)+T_\infty(X)$. Moreover $\lVert T_0(\varepsilon)\rVert\le\int_{(0,\varepsilon]}\lVert f\rVert$ and $\lVert T_\infty(X)\rVert\le\int_{(X,\infty)}\lVert f\rVert$ (`norm_integral_le_integral_norm`). Both bounds tend to $0$ by (2). The dominating function is $\lVert f\rVert$ itself: $\lVert1_{(\varepsilon,X]}f\rVert\le\lVert f\rVert$ for every truncation, and $\lVert f\rVert$ is integrable. That is the common integrable domination, and its finiteness is used at exactly one place, the subtraction in (2). The one-ended statements use one tail.

(4) is shown by Failure examples 2 and 3 below. $\square$

For truncation families, then, domination reduces to monotone convergence plus one subtraction. Dominated convergence proper is needed for families that are not truncations, such as the translates $f(x+1/n)$. Rudin's proof of it (Theorem 1.34, pp. 26–27) applies Fatou's lemma to $2g-\lvert f_n-f\rvert$ and cancels $\int2g$, which spends the same finiteness.

**Remark (the tail lemma and the convention value $0$).** `tendsto_integral_Ioi_zero` states that $\int_{(b_i,\infty)}f\to0$ whenever $b_i\to\infty$, and it has no hypothesis on $f$. Its proof splits into two cases.

- If $f$ is integrable on some $(a,\infty)$, the tail eventually equals $\int_{(a,\infty)}f-\int_a^{b_i}f$ and tends to $0$ by (3).
- If $f$ is integrable on no $(a,\infty)$, every tail is the convention value $0$ of a non-integrable Bochner integral (`integral_undef`).

For $f(x)=x^{-1/2}$ the lemma therefore asserts $0\to0$, while the true tails are all $+\infty$ (Example 1). The lemma describes the error term only in the first case. [Mathlib, `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:669–679`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean#L669-L679)

**Corollary O (the Gamma kernel at both ends).** For $\sigma>0$ let $k_\sigma(x)=e^{-x}x^{\sigma-1}$ on $(0,\infty)$, and let $n\ge\max(\sigma-1,0)$ be an integer. For $0<\varepsilon\le1\le X$,
$$e^{-\varepsilon}\,\frac{\varepsilon^\sigma}{\sigma}\le\int_{(0,\varepsilon]}k_\sigma\le\frac{\varepsilon^\sigma}{\sigma},\qquad\int_{(X,\infty)}k_\sigma\le2^{n+1}n!\,e^{-X/2},$$
and for every $s\in\mathbb C$ with $\Re s=\sigma$,
$$\Bigl\lvert\Gamma(s)-\int_\varepsilon^Xe^{-x}x^{s-1}\,dx\Bigr\rvert\le\int_{(0,\varepsilon]}k_\sigma+\int_{(X,\infty)}k_\sigma .$$
The zero-end bound uses $\sigma>0$ and nothing about infinity. The infinite-end bound uses the exponential decay and nothing about the sign of $\sigma$. [Expository] for the explicit constants. The case in which only the infinite end is truncated is `tendsto_partialGamma` [Lean, read].

*Proof.* On $(0,\varepsilon]$ we have $e^{-\varepsilon}\le e^{-x}\le1$, and $\int_0^\varepsilon x^{\sigma-1}\,dx=\varepsilon^\sigma/\sigma$. On $[1,\infty)$, $e^{-x}x^{\sigma-1}\le2^nn!\,e^{-x/2}$ by the explicit domination constant of §2.3.2.3 with $r=\sigma-1$, and $\int_X^\infty e^{-x/2}\,dx=2e^{-X/2}$. For the complex statement, $\lvert e^{-x}x^{s-1}\rvert=k_\sigma(x)$ (§2.3.2.3), $k_\sigma$ is integrable on $(0,\infty)$ (`Real.GammaIntegral_convergent`), and $\Gamma(s)=\int_0^\infty e^{-x}x^{s-1}\,dx$ (`Gamma_eq_integral`). Theorem N(3) then applies with the dominating function $k_\sigma$. In the pinned proof of the recurrence, `tendsto_partialGamma` is exactly `intervalIntegral_tendsto_integral_Ioi 0 (GammaIntegral_convergent hs) tendsto_id`. It uses the cover $(-\infty,X]$ of Lebesgue measure on $(0,\infty)$, under the single hypothesis of integrability on $(0,\infty)$, which packages both ends. The zero end is never truncated in the formal chain, since $(-\infty,X]\cap(0,\infty)=(0,X]$. $\square$

**Hand calculation 1: exact tails of the positive Gamma kernel.**

*(a) $\sigma=1/2$, the instance on the Gamma chain.* Substituting $x=u^2$ gives $\int_a^be^{-x}x^{-1/2}\,dx=2\int_{\sqrt a}^{\sqrt b}e^{-u^2}\,du$, so
$$T_0(\varepsilon)=\sqrt\pi\,\mathrm{erf}\bigl(\sqrt\varepsilon\bigr)=2\sqrt\varepsilon\Bigl(1-\frac\varepsilon3+\frac{\varepsilon^2}{10}-\cdots\Bigr),\qquad T_\infty(X)=\sqrt\pi\,\mathrm{erfc}\bigl(\sqrt X\bigr).$$
The series comes from integrating $e^{-x}=\sum_m(-x)^m/m!$ termwise against $x^{-1/2}$; its general term is $2\sqrt\varepsilon\,(-\varepsilon)^m/(m!\,(2m+1))$. The values of $T_0$ are $0.1993353$, $0.0199993$ and $0.0020000$ at $\varepsilon=10^{-2},10^{-4},10^{-6}$. They lie between the bounds $2\sqrt\varepsilon\,e^{-\varepsilon}$ and $2\sqrt\varepsilon$ of Corollary O, which at $\varepsilon=10^{-2}$ are $0.1980100$ and $0.2$.

At infinity, $x^{-1/2}\le X^{-1/2}$ on $(X,\infty)$ gives $T_\infty(X)\le X^{-1/2}e^{-X}$, and restricting to $(X,X+1]$ gives $T_\infty(X)\ge(X+1)^{-1/2}e^{-X}(1-e^{-1})$. The exact values and the upper bounds are:

| $X$ | $T_\infty(X)$ | $X^{-1/2}e^{-X}$ |
|---|---|---|
| $1$ | $2.788056\cdot10^{-1}$ | $3.678794\cdot10^{-1}$ |
| $4$ | $8.291069\cdot10^{-3}$ | $9.157819\cdot10^{-3}$ |
| $9$ | $3.915439\cdot10^{-5}$ | $4.113660\cdot10^{-5}$ |
| $16$ | $2.732638\cdot10^{-8}$ | $2.813379\cdot10^{-8}$ |

The bound $2e^{-X/2}$ of Corollary O ($n=0$) is $1.213061$ at $X=1$ and $6.709253\cdot10^{-4}$ at $X=16$: correct, but far from sharp.

The truncation error is $T_0(\varepsilon)+T_\infty(X)$. For $\varepsilon=10^{-4}$ and $X=9$ it is $0.0200385$, and $\int_{10^{-4}}^9e^{-x}x^{-1/2}\,dx=\sqrt\pi-0.0200385=1.7524154$. Both tails decrease as their domains shrink, and here the kernel itself is decreasing as well. The monotonicity that the proofs use, however, is that of the domains.

For complex $s=\tfrac12+i$, Corollary O bounds $\bigl\lvert\Gamma(\tfrac12+i)-\int_{10^{-4}}^9e^{-x}x^{-1/2+i}\,dx\bigr\rvert$ by the same $0.0200385$. With $\Gamma(\tfrac12+i)\approx0.300695-0.424968\,i$, the actual error is $0.008983$. The rotating phase $x^{i}=e^{i\log x}$ makes the signed error smaller, but only the tails of the positive kernel control it.

*(b) $\sigma=3$.* The kernel $e^{-x}x^2$ is bounded at $0$ and not monotone: it increases on $(0,2)$ to $4e^{-2}\approx0.5413$ and then decreases. Two integrations by parts give $\int e^{-x}x^2\,dx=-e^{-x}(x^2+2x+2)$, so
$$T_0(\varepsilon)=2-e^{-\varepsilon}\bigl(\varepsilon^2+2\varepsilon+2\bigr)=\frac{\varepsilon^3}3-\frac{\varepsilon^4}4+\frac{\varepsilon^5}{10}-\cdots,\qquad T_\infty(X)=e^{-X}\bigl(X^2+2X+2\bigr).$$
At $\varepsilon=0.1$, $T_0=3.093061\cdot10^{-4}$, against the bound $\varepsilon^3/3=3.333333\cdot10^{-4}$. At $X=10$, $T_\infty=122e^{-10}=5.538791\cdot10^{-3}$, against the bound $16e^{-5}\approx0.1078$ with $n=2$. Hence $\int_{0.1}^{10}e^{-x}x^2\,dx=2-0.0003093-0.0055388=1.9941519$.

For $s=3+i$, the recurrence gives $\Gamma(3+i)=(2+i)(1+i)\Gamma(1+i)=(1+3i)\,\Gamma(1+i)$, and with $\Gamma(1+i)\approx0.4980157-0.1549498\,i$ (§2.3.2.3, Hand calculation 2, to four digits) this is $\approx0.962865+1.339097\,i$. At $\varepsilon=0.1$ and $X=10$ the signed truncation error is $0.005614$, below the positive-kernel bound $0.005848$. The truncation family $1_{(\varepsilon,X]}e^{-x}x^2$ is monotone in each parameter although the kernel rises and falls. This is the distinction between monotone truncation domains and monotone functions, seen on Euler's own integrand.

**Hand calculation 2: a sign-changing integrable step kernel.** The dyadic intervals $D_k=(2^k,2^{k+1}]$, $k\in\mathbb Z$, partition $(0,\infty)$. Let
$$h=(-1)^k\,2^{-k}\bigl(\tfrac34\bigr)^{\lvert k\rvert}\quad\text{on }D_k .$$
Since $D_k$ has length $2^k$, $\int_{D_k}h=(-1)^k(3/4)^{\lvert k\rvert}$ and $\int_{D_k}\lvert h\rvert=(3/4)^{\lvert k\rvert}$. The heights are:

- $1$ on $(1,2]$, $-3/8$ on $(2,4]$, $9/64$ on $(4,8]$;
- $-3/2$ on $(1/2,1]$, $9/4$ on $(1/4,1/2]$, $-27/8$ on $(1/8,1/4]$.

So $h$ is unbounded at the zero end, roughly like $x^{-\log_2(3/2)}\approx x^{-0.585}$, decays at infinity like $x^{-\log_2(8/3)}\approx x^{-1.415}$, and changes sign from step to step.

*Domination.* $\int_{(0,\infty)}\lvert h\rvert=1+2\sum_{m\ge1}(3/4)^m=7$. So $h$ is integrable, and $\lvert h\rvert$ is a common integrable dominating function for all its truncations.

*Values.* $\int_{(0,\infty)}h=1+2\sum_{m\ge1}(-3/4)^m=1-\tfrac67=\tfrac17$. The positive and negative parts have $\int h^+=\sum_{k\text{ even}}(3/4)^{\lvert k\rvert}=\tfrac{25}7$ and $\int h^-=\tfrac{24}7$. Applying Lemma L to $h^+$ and $h^-$ separately and subtracting two finite numbers gives the same $\tfrac17$.

*The two tails at dyadic points.* For $n,N\ge0$,
$$T_0(2^{-n})=\sum_{m>n}(-1)^m\bigl(\tfrac34\bigr)^m=(-1)^{n+1}\tfrac37\bigl(\tfrac34\bigr)^n,\qquad T_\infty(2^N)=\sum_{k\ge N}(-1)^k\bigl(\tfrac34\bigr)^k=(-1)^N\tfrac47\bigl(\tfrac34\bigr)^N .$$
The dominating tails are $\int_{(0,2^{-n}]}\lvert h\rvert=3(3/4)^n$ and $\int_{(2^N,\infty)}\lvert h\rvert=4(3/4)^N$, exactly seven times larger in absolute value. For instance, $T_0(1)=\int_{(0,1]}h=-\tfrac37$ and $T_\infty(1)=\int_{(1,\infty)}h=\tfrac47$ add up to $\tfrac17$.

*Symmetric truncations.* On $(2^{-n},2^n]$,
$$\int_{(2^{-n},2^n]}h=\tfrac17\Bigl(1-\bigl(-\tfrac34\bigr)^n\Bigr).$$
For $n=1,2,3,4$ this is $\tfrac14,\tfrac1{16},\tfrac{13}{64},\tfrac{25}{256}$, alternately above and below $\tfrac17\approx0.142857$, with error $\tfrac17\bigl(-\tfrac34\bigr)^n$. Meanwhile $\int_{(2^{-n},2^n]}\lvert h\rvert=7-7(3/4)^n$, namely $\tfrac74,\tfrac{49}{16},\tfrac{259}{64},\tfrac{1225}{256}$, increases.

*Asymmetric truncations.* Off the diagonal the signed truncations are no more orderly. For $N=1,2,3,4$, $\int_{(1,2^N]}h$ is $1,\tfrac14,\tfrac{13}{16},\tfrac{25}{64}$, and $\int_{(1/2,2^N]}h$ is $\tfrac14,-\tfrac12,\tfrac1{16},-\tfrac{23}{64}$.

So the truncation family of $h$ is not monotone, and Lemma L does not apply to it. The truncation family of $\lvert h\rvert$ is monotone, and Theorem N(3) bounds every error by the two dominating tails:
$$\Bigl\lvert\tfrac17-\int_{(2^{-n},2^N]}h\Bigr\rvert\le3\bigl(\tfrac34\bigr)^n+4\bigl(\tfrac34\bigr)^N .$$
Each end has its own condition here. The zero-end tail is controlled by $\sum_{m\ge1}(3/4)^m<\infty$, although $h$ is unbounded there, and the infinite-end tail by $\sum_{k\ge0}(3/4)^k<\infty$. Replace $3/4$ by $1$ at one end only, that is, use heights $\pm2^{-k}$ there. Then every step integral at that end has modulus $1$, that end's dominating tail is infinite, and the signed truncations at that end oscillate between two values; the other end is unaffected.

**Remark (what fails when a hypothesis is removed).** [Expository]

1. *Nonnegativity in Lemma L.* On $(0,\infty)$ let $F_n=-1_{(n,\infty)}$. Then $F_n\le F_{n+1}$ and $F_n\to0$ at every point. But the negative part of each $F_n$ has integral $\infty$, so in the extended sense $\int F_n=0-\infty=-\infty$ for every $n$, while the limit has integral $0$. Bochner integration does not rescue the statement. Each $F_n$ is non-integrable and has the convention integral $0$, so "$\int F_n\to\int\lim F_n$" holds as $0\to0$ for no mathematical reason. The signed form of monotone convergence needs a common integrable lower bound $F_n\ge-g$; it then reduces to Lemma L applied to $F_n+g$, followed by the subtraction of the finite number $\int g$. For truncation families, nonnegativity is what makes larger domains give larger functions (`key₂`). For the signed kernel $h$ of Hand calculation 2 the truncations oscillate.
2. *Integrable domination in the signed transport.* Let $g=(-1)^{k+1}/k$ on $(k-1,k]$, $k\ge1$.
   - The truncations $\int_{(0,N]}g=\sum_{k\le N}(-1)^{k+1}/k$ are $0.645635$, $0.688172$ and $0.692647$ for $N=10,100,1000$, and they converge to $\log2\approx0.693147$. Since $\lvert g\rvert\le1/k\to0$ on the last partial step, $\int_{(0,x]}g\to\log2$ along every $x\to\infty$.
   - But $\int_{(0,N]}\lvert g\rvert=H_N$, which is $2.928968$, $5.187378$, $7.485471$, tends to $\infty$. Monotone convergence applied to $\lvert g\rvert$ certifies that $g$ is not integrable. Its Bochner integral is the convention value $0$, and the limit $\log2$ is not the integral of anything.
   - Worse, the limit depends on the exhaustion. Let $E_n$ consist of the first $2n$ positive steps $(2j-2,2j-1]$ and the first $n$ negative steps $(2j-1,2j]$. The sets $E_n$ increase and exhaust $(0,\infty)$, so they form an a.e. cover along `atTop`. Yet $\int_{E_n}g=\sum_{j\le2n}\frac1{2j-1}-\sum_{j\le n}\frac1{2j}=H_{4n}-\tfrac12H_{2n}-\tfrac12H_n$, which is $1.015189$, $1.037225$, $1.039471$ for $n=10,100,1000$ and tends to $\tfrac32\log2\approx1.039721$, because $H_m=\log m+\gamma+o(1)$.

   With an integrable dominating function, every a.e. cover gives the same limit $\int g$; for this reason `AECover.integral_tendsto_of_countably_generated` requires `Integrable f μ`, and Theorem N(3) proves the statement. Without such a function, "the" improper integral is a property of the chosen family of domains. This is the step-function form of Riemann's rearrangement theorem, and the $\sin x/x$ example of §2.3.2.4 behaves the same way.
3. *Finiteness for the tails.* For $f=x^{-1/2}$ on $(0,\infty)$, the infinite-end truncations $1_{(X,\infty)}f$ decrease to $0$ at every point, while $\int_{(X,\infty)}f=\infty$ for every $X$. So Lemma M fails without $\int F_0<\infty$, and so does the infinite-end tail statement of Theorem N(2), although at the zero end the same function has tails $2\sqrt\varepsilon\to0$. For $f=1/x$ on $(0,1]$ the zero-end tails are all infinite. For the Gamma kernel the zero-end condition is $\sigma>0$. At $\sigma=0$, $\int_{(0,\varepsilon]}e^{-x}x^{-1}\,dx\ge e^{-\varepsilon}\int_0^\varepsilon dx/x=\infty$, while the infinite-end tail $\int_{(X,\infty)}e^{-x}x^{-1}\,dx\le e^{-X}/X$ is as small as before. Each end's tail has its own finiteness hypothesis, and neither implies the other. In Lean the conventions hide this: for $x^{-1/2}$, `tendsto_integral_Ioi_zero` holds as the statement $0\to0$.
4. *Measurability in Lemma K.* Let $V\subset[0,1]$ be a Vitali set, with one point from each coset of $\mathbb Q$ that meets $[0,1]$. Let $(q_j)$ enumerate $\mathbb Q\cap[-1,1]$, and put $A_n=[0,1]\cap\bigcup_{j\le n}(V+q_j)$. The sets $A_n$ increase to $[0,1]$.
   - *Every measurable subset $M$ of $A_n$ is null.* Choose rationals $\rho_1,\rho_2,\dots$ in $[0,1]$ such that the finite sets $\{q_j+\rho_i:\ j\le n\}$ are pairwise disjoint for different $i$. Then the translates $M+\rho_i$ are pairwise disjoint, because they lie in disjoint unions of translates of $V$. They all lie in $[0,2]$ and have the same measure, so that measure is $0$.
   - *Consequence for the lower integral.* Every simple function below $1_{A_n}$ has integral $0$, so $\int1_{A_n}=0$ for all $n$, while $\sup_n1_{A_n}=1_{[0,1]}$ has integral $1$. The proof of Lemma K fails at step (d): the set $\{t\le1_{A_n}\}=A_n\cup[0,1]^c$ is not measurable for large $n$, since a measurable $A_n$ would be null while $\mu(A_n)\to1$.
   - *The domain form gives the other answer.* By the previous remark, $\int_{A_n}1\,d\mu=\mu(A_n)\to1$, because $\mu(A_n)$ is the outer measure and continuity from below holds for arbitrary sets.

   So for non-measurable domains $\int_Ah\,d\mu$ and $\int1_Ah\,d\mu$ differ. This is why `lintegral_indicator` and the definition of `AECover` require measurable sets.
5. *The two devices inside Lemma K.* Step (b) needs both the factor $r<1$ and the finite values of $s$.
   - Take $F_n=(1-\tfrac1n)1_{[0,1]}$ and $s=1_{[0,1]}$. The sets $\{s\le F_n\}\cap[0,1]$ are empty for every $n$, although $\sup_nF_n=s$. With $r<1$, the sets $\{rs\le F_n\}$ contain $[0,1]$ as soon as $1-\tfrac1n\ge r$.
   - Take $F_n=n\,1_{[0,1]}$ and the simple function $s=\infty\cdot1_{[0,1]}\le\sup_nF_n$. The sets $\{rs\le F_n\}\cap[0,1]$ are empty for every $r>0$ and every $n$, since $r\cdot\infty=\infty$. `lintegral_eq_nnreal` replaces such an $s$ by the finite-valued $m\,1_{[0,1]}$, whose integrals $m$ already exhaust $\int\sup_nF_n=\infty$.

**Remark (Levi's lemma, Rudin's proof and the formal one).** [Expository] The file's docstring calls the theorem the "Beppo Levi lemma". In B. Levi, "Sopra l'integrazione delle serie", *Rendiconti del R. Istituto Lombardo* (2) 39 (1906), 775–780, §2 states it in the form that Lemma C uses: if a nondecreasing sequence of nonnegative (in Levi's wording, positive) integrable functions has integrals with a finite limit, then its limit function is integrable, with integral equal to that limit. Levi's proof (pp. 776–778) is itself a truncation-domain argument. It restricts to the sets where the limit function is at most $l_i$, applies Lebesgue's bounded convergence theorem on each of them, and exchanges two limits that are both nondecreasing. In §1 Levi recalls that the integral of an unbounded function can be defined as a limit over such truncations, and that for Riemann–Cauchy integrals this limit agrees with the ordinary definition only for absolutely integrable functions; that distinction opened §2.3.2.4. Rudin's Theorem 1.26 (pp. 21–22) is the measurable form, with the proof of Lemma K. Mathlib's Fatou lemma (`lintegral_liminf_le'`) is derived from Lemma L, while its Bochner dominated convergence theorem goes through the $L^1$ machinery instead. [Mathlib, `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:201–234`](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean#L201-L234)

**Use in the archive.** Archive A2 calls the theorems of this subsection directly at 49 source lines in 34 files: `lintegral_iSup` at 23 lines, `lintegral_iSup'` at 3, `lintegral_tendsto_of_tendsto_of_monotone` at 6, `lintegral_iSup_directed` at 1, `lintegral_iInf` at 1, `setLIntegral_iUnion_of_directed` at 5, `intervalIntegral_tendsto_integral_Ioi` at 8 and `integrableOn_Ioi_of_intervalIntegral_norm_bounded` at 2.

One of these calls sits in a file this book reads elsewhere: `src/Development/AutomorphicArithmetic/MeanSquareBounds/GIntegral.lean`, whose lemma `dom_integrableOn` is read in §2.3.2.4. There the lemma `psi_zero_div_sq_integrable` (lines 93–166) proves that $u\mapsto\psi_0(\chi,u)/u^2$ is integrable on $(y,\infty)$ for $y\ge1$. Here $\psi_0(\chi,u)=\sum_{n\le u}\Lambda(n)\chi(n)$, minus $u$ when $\chi$ is principal. The proof splits at $X_1=\max(x_1,y)$.

- On $(y,X_1]$ the function is bounded by a constant.
- On $(X_1,\infty)$ it is dominated by $K/(u\log^2u)$, that is, by $K$ times the function `dom` of §2.3.2.4. This uses a Siegel–Walfisz bound $\lvert\psi_0(\chi,t)\rvert\le Ct\,e^{-c\sqrt{\log t}}\le\frac{24C}{c^4}\,\frac{t}{\log^2t}$ (`psi0_bound`, lines 66–91), whose second inequality is $e^z\ge z^4/24$.

The lemma `l21a` (lines 195–226) then calls `intervalIntegral_tendsto_integral_Ioi y hint tendsto_id`. By uniqueness of limits it identifies the Bochner integral with a limit of truncated integrals that a separate summation formula provides. This is Theorem N(3) at the infinite end, with the common dominating function $\lvert\psi_0\rvert/u^2\le K\cdot\mathrm{dom}$ beyond $X_1$. Since $\int_U^\infty du/(u\log^2u)=1/\log U$, the tail is at most $K/\log U$ for $U\ge X_1$; the transport needs the existence of $K$, not its size.

Whether `GIntegral.lean` and the other call sites lie in the dependency closure of the main theorem is not re-derived here. The archive SHA-256 is `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`.

**Reading boundary.** All Mathlib links are fixed at `0df444a360eaa60ab8c11dca51a86af692955474`.

- *[Lean, read] increment.*
  - In `Lebesgue/Add.lean`: `lintegral_iSup`, `lintegral_iSup'`, `lintegral_tendsto_of_tendsto_of_monotone`, `lintegral_iSup_ae`, and the reduction of Fatou's lemma to them (`lintegral_liminf_nat_le'`).
  - In `Function/AEMeasurableSequence.lean`: the whole file, that is, `aeSeqSet`, `aeSeq` and its lemmas.
  - In `Lebesgue/Sub.lean`: `lintegral_sub'`, `lintegral_sub`, `lintegral_iInf_ae`, `lintegral_iInf`, `lintegral_iInf'` and `lintegral_tendsto_of_tendsto_of_antitone`.
  - In `Lebesgue/Basic.lean`: the definition `lintegral`, `SimpleFunc.lintegral_eq_lintegral`, `lintegral_eq_nnreal`, `iSup_lintegral_le`, `lintegral_indicator` and `setLIntegral_iUnion_of_directed`, with `SimpleFunc.lintegral_restrict_iUnion_of_directed`, `SimpleFunc.restrict` and `restrict_lintegral` in `Function/SimpleFunc.lean`.
  - In `IntegralEqImproper.lean`, in addition to what §2.3.2.4 read (including `intervalIntegral_tendsto_integral_Ioi` and `AECover.integral_tendsto_of_countably_generated`): the zero-end covers `aecover_Ioi_of_Ioi`, `aecover_Ioo_of_Ioo` and `aecover_Ioc_of_Ioc`, `integrableOn_Ioc_of_intervalIntegral_norm_bounded` and its `_left` form, and `tendsto_integral_Ioi_zero`.
  - In `Gamma/Basic.lean`: `tendsto_partialGamma`.
  - Continuity from below for arbitrary sets: `Directed.measure_iUnion` and `Monotone.measure_iUnion` (`Mathlib/MeasureTheory/Measure/MeasureSpace.lean:485,520`), and `Measure.restrict_iUnion_apply_eq_iSup` and `Measure.restrict_eq_self_of_ae_mem` (`Mathlib/MeasureTheory/Measure/Restrict.lean:314,337`).
- *Read as statements, proofs retained at [Lean].*
  - `lintegral_add_compl` and `lintegral_mono_ae` (`Lebesgue/Basic.lean:630,217`).
  - The dominated convergence theorems `tendsto_integral_of_dominated_convergence` and `tendsto_integral_filter_of_dominated_convergence` (`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:57,67`), whose `setToFun` proofs were not read.
  - `norm_integral_le_integral_norm` and `integral_undef` (`Bochner/Basic.lean:934,202`).
  - `EReal.continuousAt_add` (`Mathlib/Topology/Instances/EReal/Lemmas.lean:432`).
- *Named inputs retained at [Lean].* The `ENNReal` order and arithmetic lemmas `ENNReal.le_of_forall_lt_one_mul_le`, `ENNReal.lt_iff_exists_coe`, `ENNReal.mul_iSup`, `ENNReal.finsetSum_iSup_of_monotone`, `ENNReal.sub_iInf` and `ENNReal.sub_right_inj`, as well as `measurableSet_le`, `toMeasurable`, `ae_all_iff`, `tendsto_atTop_iSup`, and the inputs `measure_iUnion_toMeasurable`, `measure_biUnion_finset`, `exists_seq_monotone_tendsto_atTop_atTop` and `Measure.restrict_congr_set` of the continuity lemmas.
- *Textbook material.* The truncation remark, the proof of Theorem N(3) by subtraction, the explicit constants of Corollary O, the two hand calculations and the five failure examples are textbook derivations. Their numerical values are floating-point checks with the standard library, not interval certificates.
- *Classical sources.* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Definitions 1.16 (p. 15) and 1.23 (p. 19), Theorems 1.26 (pp. 21–22) and 1.34 (pp. 26–27); B. Levi, "Sopra l'integrazione delle serie", *Rend. R. Ist. Lombardo* (2) 39 (1906), 775–780, read in the archive.org scan of the volume.

Nothing was compiled or kernel-checked. Reading the source and matching hashes is not kernel verification.

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
| `changeLevel`, `changeLevel_injective`, `FactorsThrough.existsUnique`, `factorsThrough_iff_ker_unitsMap` | `Mathlib/NumberTheory/DirichletCharacter/Basic.lean:66,80,137,150` | Level change, descent and fixed-level uniqueness. | [Lean, read] |
| `conductor`, `conductor_dvd_level`, `primitiveCharacter`, `changeLevel_primitiveCharacter`, `primitiveCharacter_isPrimitive`, `mem_conductorSet_iff_conductor_dvd` | `Mathlib/NumberTheory/DirichletCharacter/Basic.lean:246,251,307,310,314,358` | Minimum, witness, recovery, primitivity, and divisibility minimum. | [Lean, read] |
| `level_one`, `changeLevel_one`, `conductor_one`, `conductor_inv`, `Odd`, `Even`, `even_or_odd` | `Mathlib/NumberTheory/DirichletCharacter/Basic.lean:202,220,259,405,533,536,538` | Principal character, inversion and parity. | [Lean] |
| `LFunction_modOne_eq`, `LFunction_changeLevel`, `gammaFactor`, `completedLFunction`, `LFunction_eq_completed_div_gammaFactor`, `IsPrimitive.completedLFunction_one_sub` | `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:67,150,207,224,259,284` | Identification $L(s, 1 \bmod 1) = \zeta(s)$, Euler-factor product under level change, $\gamma_\chi(s)$, $\Lambda(s,\chi)$, and the primitive functional equation. | [Lean] |
| `betaIntegral`, `betaIntegral_scaled`, `Gamma_mul_Gamma_eq_betaIntegral`, `betaIntegral_eq_Gamma_mul_div`; `posConvolution`, `integral_posConvolution`, `Integrable.convolution_integrand` | `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean:60,103,124,537`; `Mathlib/Analysis/Convolution.lean:944,986,272` | Beta integral, its dilation to $(0,x)$, the product form $\Gamma(a)\Gamma(b)=\Gamma(a+b)B(a,b)$ and the quotient on $\Re a,\Re b>0$; forward convolution, its Fubini and translation step (§2.3.2.2). | [Lean, read] |
| `Real.GammaIntegral_convergent`, `Complex.GammaIntegral_convergent`, `GammaIntegral`, `GammaIntegral_add_one`, `Gamma`, `Gamma_eq_integral`, `Real.Gamma_eq_integral`; `integrable_of_isBigO_exp_neg`; `intervalIntegrable_rpow'`; `norm_cpow_eq_rpow_re_of_pos` | `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:66,87,110,217,287,319,405`; `Mathlib/MeasureTheory/Integral/ExpDecay.lean:41`; `Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean:45`; `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:337` | Absolute convergence of the Euler integral on $\Re s>0$ (power comparison at $0$, exponential-decay comparison at $\infty$, modulus $|x^{s-1}|=x^{\Re s-1}$), the integral recurrence by parts, the recursive definition of $\Gamma$ and its agreement with the integral (§2.3.2.3). | [Lean, read] |
| `integral_le_sub_of_hasDeriv_right_of_le`, `integral_eq_sub_of_hasDerivAt_of_le`, `integrableOn_deriv_right_of_nonneg`, `integrableOn_deriv_of_nonneg`; `integrableOn_Ioi_of_intervalIntegral_norm_tendsto`, `integrableOn_Ioi_deriv_of_nonneg`, `integral_Ioi_of_hasDerivAt_of_nonneg`, `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`; `exp_neg_integrableOn_Ioi` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1094,1140,1221,1256`; `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:572,833,874,711`; `Mathlib/MeasureTheory/Integral/ExpDecay.lean:31` | One-sided fundamental theorem of calculus; a nonnegative derivative is integrable when the primitive is continuous on a closed bounded interval or converges at infinity, with the boundary difference as value, and an integrable derivative forces a limit; the zero-end power and exponential-tail integrability consumed in §2.3.2.3 (§2.3.2.4). | [Lean, read] |
| `exists_lt_lowerSemicontinuous_integral_lt`, `exists_upperSemicontinuous_lt_integral_gt`; `exists_lt_lowerSemicontinuous_lintegral_ge`, `exists_upperSemicontinuous_le_lintegral_le`; `Set.exists_isOpen_lt_of_lt`, `MeasurableSet.exists_isClosed_lt_add` | `Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean:422,499,194,356`; `Mathlib/MeasureTheory/Measure/Regular.lean:359,1031` | Vitali–Carathéodory: for an integrable real function on a $\sigma$-finite weakly regular Borel measure space, a lower semicontinuous strict majorant and an upper semicontinuous strict minorant, finite almost everywhere, with integrals within $\varepsilon$; the open-set and closed-set regularity steps it rests on. Input of the one-sided fundamental theorem (§2.3.2.5). | [Lean, read] for the Vitali–Carathéodory file; the regularity lemmas [Lean] |
| `lintegral_iSup`, `lintegral_iSup'`, `lintegral_tendsto_of_tendsto_of_monotone`, `lintegral_iSup_ae`; `aeSeq`; `lintegral_iInf_ae`, `lintegral_tendsto_of_tendsto_of_antitone`; `setLIntegral_iUnion_of_directed`; `integrableOn_Ioc_of_intervalIntegral_norm_bounded_left`, `tendsto_integral_Ioi_zero`; `tendsto_partialGamma` | `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean:34,96,113,128`; `Mathlib/MeasureTheory/Function/AEMeasurableSequence.lean:41`; `Mathlib/MeasureTheory/Integral/Lebesgue/Sub.lean:51,133`; `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:646`; `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:592,669`; `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:149` | Monotone convergence for measurable and for a.e.-measurable functions with values in $[0,\infty]$, the a.e. representatives behind it, its decreasing form under one finite integral, monotone convergence over truncation domains without measurability, the zero-end integrability criterion, and the signed improper limits at both ends under the common dominating function $\lVert f\rVert$ (§2.3.2.6). | [Lean, read] |

**Summary of the chapter.** Every Dirichlet $L$-function differs from its primitive $L$-function
only by finitely many Euler factors $1 - \chi^*(p) p^{-s}$, none of which vanishes on $\Re s > 0$
(Lemma 2.1) [Lean, read]. Hence non-vanishing of primitive $L$-functions on $\Re s > 1/2$
(`ZeroFreeAll`) implies non-vanishing of all Dirichlet $L$-functions on $\Re s > 1/2$
(`EveryCharacter`, Proposition 2.2) [Lean, read], and reflecting across $\Re s = 1/2$ via the
functional equations of $\Lambda(s,\chi^*)$ and of $\zeta(s)$ immediately yields all five theorems
of `src/Main.lean` (Theorems 2.6 and 2.7) [Lean, read]. The entire remainder of the book is therefore
devoted to proving `ZeroFreeAll`.
