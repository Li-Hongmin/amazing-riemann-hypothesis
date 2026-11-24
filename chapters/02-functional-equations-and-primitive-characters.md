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

**Summary of the chapter.** Every Dirichlet $L$-function differs from its primitive $L$-function
only by finitely many Euler factors $1 - \chi^*(p) p^{-s}$, none of which vanishes on $\Re s > 0$
(Lemma 2.1) [Lean, read]. Hence non-vanishing of primitive $L$-functions on $\Re s > 1/2$
(`ZeroFreeAll`) implies non-vanishing of all Dirichlet $L$-functions on $\Re s > 1/2$
(`EveryCharacter`, Proposition 2.2) [Lean, read], and reflecting across $\Re s = 1/2$ via the
functional equations of $\Lambda(s,\chi^*)$ and of $\zeta(s)$ immediately yields all five theorems
of `src/Main.lean` (Theorems 2.6 and 2.7) [Lean, read]. The entire remainder of the book is therefore
devoted to proving `ZeroFreeAll`.
